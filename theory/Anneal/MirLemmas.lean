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
import Anneal.StepResult
import Anneal.Lowering

/-!
# MIR Meta-Theorems, Compositional Crate Verifier, and Adequacy Canaries

This module proves:
1. Structural non-vacuity properties (`TotalStep`, `InhabitedDemonic`) of
   `Trusted.MirMachine` and admissibility of `defaultAdtInv` and
   `nonZeroAdtInv`.
2. Symbolic small-step execution helpers (`ExecNormal`, `ExecUnwind`,
   `ExecFail`, `execNormal_verified`, `execNormal_fnVerifiedAndRetInv`,
   `monoAdmitted_of_simple`).
3. Verification lemmas for `pub fn id(x: usize) -> usize { x }`, a concrete
   size-checked `transmute_copy` (a post-monomorphization error, PME), and the
   `NonZeroUsize` library contract over the flat `BodyId`-indexed `Crate.bodies`
   table.
4. Positive and negative adequacy canaries, including partial-move
   deinitialization (`MirVal.uninit`), `Stmt.placeMention`,
   `Terminator.assert`, and demand-driven `.unsupported` bodies.
5. Fuel-free AST boolean equality (`beqMirBody`) and the compositional
   per-ADT and per-function crate verifier (`proveCrateOpt`, `checkCrate`,
   `proveCrate`).
-/

namespace Anneal

open Trusted

/-- Shorthand for a bare-local `Place` with no projections. -/
abbrev locPlace (idx : Nat) : Place :=
  { loc := ⟨idx⟩, projection := [] }

/-!
## 1. Structural Machine Meta-Theorems (`TotalStep`, `InhabitedDemonic`)
-/

/-- `MirMachine adts bodies` is total: every `(body, s)` pair steps to
`(evalMirStep adts bodies body s).toStepResult`. -/
theorem mirMachine_total (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) :
    TotalStep (MirMachine adts bodies) :=
  fun body s => ⟨(evalMirStep adts bodies body s).toStepResult, rfl⟩

/-- `MirMachine adts bodies` has no empty choice nodes (`evalMirStep` only
emits `.silent` choices via `RawStep.toStepResult`, which are uniquely
inhabited). -/
theorem mirMachine_inhabited (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) :
    InhabitedDemonic (MirMachine adts bodies) :=
  fun _ _ _ hstep => RawStep.toStepResult_choice_inhabited hstep

/-- Postcondition `EnsuresEqArg argLocal adts bodies` refines
`wellFormed (MirLang adts bodies)`. -/
theorem ensuresEqArg_le_wellFormed (argLocal : Nat)
    (adts : List AdtDecl := []) (bodies : List BodyDecl := []) :
    EnsuresEqArg argLocal adts bodies ≤ wellFormed (MirLang adts bodies) :=
  spec_le_wellFormed _

/-- `defaultAdtInv` is admissible for an empty list of ADT declarations. -/
theorem defaultAdtInv_admissible :
    AdmissibleAdtInv [] defaultAdtInv :=
  ⟨True.intro, fun _ h => by cases h⟩

/-!
## 2. Symbolic Small-Step Execution Helpers
-/

/-- Construct `initEntryState adts body s` by discharging structural fields via
default `rfl`/`decide` arguments and taking only the argument condition. -/
theorem mkInitEntryState {adts : List AdtDecl} {body : MirBody} {s : MirState}
    (hargs : argsMatchInv adts defaultAdtInv body.localCount s body.argTys)
    (hb : s.block = 0 := by rfl)
    (hstmt : s.stmtIdx = 0 := by rfl)
    (hcur : s.curBody = none := by rfl)
    (hstack : s.stack = [] := by rfl)
    (hfid : s.frameId = 0 := by rfl)
    (hnfid : s.nextFrameId = 1 := by rfl)
    (hlg : s.localGens = (fun _ => 0) := by rfl)
    (hloc0 : s.locals 0 = none := by rfl)
    (hcount : 1 + body.argTys.length ≤ body.localCount := by decide)
    (hargWf : body.argTys.all (MirTy.wfInAdts adts) = true := by rfl)
    (hretWf : body.retTy.wfInAdts adts = true := by rfl) :
    initEntryState adts body s :=
  ⟨hb, hstmt, hcur, hstack, hfid, hnfid, hlg, hloc0,
   hcount, hargWf, hretWf, hargs⟩

theorem initEntryState_argsMatch {adts : List AdtDecl} {body : MirBody}
    {s : MirState} (h : initEntryState adts body s) :
    argsMatchInv adts defaultAdtInv body.localCount s body.argTys :=
  h.2.2.2.2.2.2.2.2.2.2.2

theorem updateLocal_one_gt_one {v1 : Option MirVal} (j : Nat)
    (hj : 2 ≤ j) :
    updateLocal (fun _ => none) 1 v1 j = none := by
  cases j with
  | zero => cases hj
  | succ k =>
    cases k with
    | zero =>
      cases hj with
      | step hle => cases hle
    | succ _ => rfl

theorem toStepResult_of_silent {s' : MirState}
    {r : RawStep MirState MirReturn} (h : r = .silent s') :
    r.toStepResult (Obs := Empty) = StepResult.silent s' :=
  congrArg RawStep.toStepResult h

theorem toStepResult_of_terminated {term : TerminationKind MirReturn}
    {r : RawStep MirState MirReturn} (h : r = .terminated term) :
    r.toStepResult (Obs := Empty) = StepResult.terminated term :=
  congrArg RawStep.toStepResult h

theorem toStepResult_of_failed {r : RawStep MirState MirReturn}
    (h : r = .failed) :
    r.toStepResult (Obs := Empty) = StepResult.failed :=
  congrArg RawStep.toStepResult h

theorem reachesPrefix_of_step
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s s' : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn}
    (hstep : evalMirStep adts bodies body s = .silent s')
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out) :
    out = .running s ∨
      ∃ n' tr', ReachesPrefix (MirStep adts bodies) body n' s' tr' out := by
  have hstepR := toStepResult_of_silent hstep
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice n' _ s₂ branches _ _ h1 hbr hr =>
    have h1' :
        StepResult.choice branches =
          (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    subst hbr
    exact Or.inr ⟨n', tr, hr⟩
  | emptyChoice _ _ branches h1 hemp =>
    have h1' :
        StepResult.choice branches =
          (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    exact False.elim (hemp ⟨s', rfl⟩)
  | terminated _ _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstepR.symm⟩)

theorem reachesPrefix_of_terminated
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn}
    {term : TerminationKind MirReturn}
    (hstep : evalMirStep adts bodies body s = .terminated term)
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out) :
    out = .running s ∨ out = .terminated term := by
  have hstepR := toStepResult_of_terminated hstep
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' :
        StepResult.terminated t =
          (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'
    injection h1' with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstepR.symm⟩)

/-- Combined prefix-safety, normal-return postcondition, and
compile-time-error-freedom predicate. -/
def SafeAndEnsures (P : MirReturn → Prop)
    (out : PrefixOutcome MirState MirReturn) : Prop :=
  out.isSafe ∧
  (∀ ret, out = .terminated (.normal ret) → P ret) ∧
  out ≠ .terminated .compileTimeError

theorem reachesPrefix_safeAndEnsures_of_step
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s s' : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn} {P : MirReturn → Prop}
    (hstep : evalMirStep adts bodies body s = .silent s')
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out)
    (hnext : ∀ n' tr',
      ReachesPrefix (MirStep adts bodies) body n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_safeAndEnsures_of_normal
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s : MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn}
    {P : MirReturn → Prop} {v : MirReturn}
    (hstep : evalMirStep adts bodies body s = .terminated (.normal v))
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
  | inr hterm =>
    subst hterm
    refine ⟨True.intro, ?_, (fun h => by cases h)⟩
    intro ret hret
    injection hret with h1
    injection h1 with h2
    subst h2
    exact hPv

theorem reachesPrefix_not_normal_of_step
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s s' : MirState} {n : Nat} {tr : List Empty} {v : MirReturn}
    (hstep : evalMirStep adts bodies body s = .silent s')
    (hreach :
      ReachesPrefix (MirStep adts bodies) body n s tr (.terminated (.normal v)))
    (hnext : ∀ n' tr',
      ReachesPrefix (MirStep adts bodies) body n' s' tr'
        (.terminated (.normal v)) → False) :
    False := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => cases hrun
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_not_normal_of_unwind
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s : MirState} {n : Nat} {tr : List Empty} {v : MirReturn}
    (hstep : evalMirStep adts bodies body s = .terminated .unwind)
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr
      (.terminated (.normal v))) :
    False := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => cases hrun
  | inr hunw => cases hunw

theorem reachesPrefix_not_normal_of_failed
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s : MirState} {n : Nat} {tr : List Empty} {v : MirReturn}
    (hstep : evalMirStep adts bodies body s = .failed)
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr
      (.terminated (.normal v))) :
    False := by
  have hstepR := toStepResult_of_failed hstep
  cases hreach with
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'

/-- Inductive unwind-termination symbolic execution relation for a `MirBody`. -/
inductive ExecUnwind (adts : List AdtDecl := []) (bodies : List BodyDecl := [])
    (body : MirBody) : MirState → Prop where
  | step {s s' : MirState} :
      evalMirStep adts bodies body s = .silent s' →
      ExecUnwind adts bodies body s' →
      ExecUnwind adts bodies body s
  | unwind {s : MirState} :
      evalMirStep adts bodies body s = .terminated .unwind →
      ExecUnwind adts bodies body s

/-- `ExecUnwind adts bodies body s` implies the existence of a finite prefix
reaching `.terminated .unwind`. -/
theorem execUnwind_reaches {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} (hexec : ExecUnwind adts bodies body s) :
    ∃ n,
      ReachesPrefix (MirStep adts bodies) body n s [] (.terminated .unwind) := by
  induction hexec with
  | step hstep _ ih =>
    cases ih with
    | intro n hr =>
      exact ⟨n + 1,
        .choice n _ _ _ [] (.terminated .unwind)
          (toStepResult_of_silent hstep).symm rfl hr⟩
  | unwind hterm =>
    exact ⟨1, .terminated 0 _ .unwind (toStepResult_of_terminated hterm).symm⟩

/-- No prefix from an `ExecUnwind` state can terminate normally. -/
theorem execUnwind_not_normal {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} (hexec : ExecUnwind adts bodies body s) :
    ∀ {n : Nat} {tr : List Empty} {v : MirReturn},
      ReachesPrefix (MirStep adts bodies) body n s tr
        (.terminated (.normal v)) → False := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr v hreach
    exact reachesPrefix_not_normal_of_step hstep hreach (fun _ _ hr => ih hr)
  | unwind hterm =>
    intro n tr v hreach
    exact reachesPrefix_not_normal_of_unwind hterm hreach

/-- Inductive compile-time-error symbolic execution relation for a `MirBody`. -/
inductive ExecCompileTimeError (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) (body : MirBody) : MirState → Prop where
  | step {s s' : MirState} :
      evalMirStep adts bodies body s = .silent s' →
      ExecCompileTimeError adts bodies body s' →
      ExecCompileTimeError adts bodies body s
  | compileTimeError {s : MirState} :
      evalMirStep adts bodies body s = .terminated .compileTimeError →
      ExecCompileTimeError adts bodies body s

theorem execCompileTimeError_reaches {adts : List AdtDecl}
    {bodies : List BodyDecl} {body : MirBody} {s : MirState}
    (hexec : ExecCompileTimeError adts bodies body s) :
    ∃ n,
      ReachesPrefix (MirStep adts bodies) body n s []
        (.terminated .compileTimeError) := by
  induction hexec with
  | step hstep _ ih =>
    cases ih with
    | intro n hr =>
      exact ⟨n + 1,
        .choice n _ _ _ [] (.terminated .compileTimeError)
          (toStepResult_of_silent hstep).symm rfl hr⟩
  | compileTimeError hterm =>
    exact ⟨1,
      .terminated 0 _ .compileTimeError
        (toStepResult_of_terminated hterm).symm⟩

theorem execCompileTimeError_safe_and_not_normal {adts : List AdtDecl}
    {bodies : List BodyDecl} {body : MirBody} {s : MirState}
    (hexec : ExecCompileTimeError adts bodies body s) :
    ∀ {n : Nat} {tr : List Empty} {out : PrefixOutcome MirState MirReturn},
      ReachesPrefix (MirStep adts bodies) body n s tr out →
      out.isSafe ∧ ∀ ret, out ≠ .terminated (.normal ret) := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr out hreach
    cases reachesPrefix_of_step hstep hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, fun _ h => by cases h⟩
    | inr hex =>
      cases hex with
      | intro n' htr =>
        cases htr with
        | intro tr' hr' => exact ih hr'
  | compileTimeError hterm =>
    intro n tr out hreach
    cases reachesPrefix_of_terminated hterm hreach with
    | inl hrun =>
      subst hrun
      exact ⟨True.intro, fun _ h => by cases h⟩
    | inr herr =>
      subst herr
      exact ⟨True.intro, fun _ h => by cases h⟩

/-- Every prefix reachable from a state satisfying
`ExecNormal adts bodies body s P` is safe, satisfies `P` on normal
termination, and never terminates with `.compileTimeError`. -/
theorem execNormal_safeAndEnsures {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} {P : MirReturn → Prop}
    (hexec : ExecNormal adts bodies body s P) :
    ∀ {n : Nat} {tr : List Empty} {out : PrefixOutcome MirState MirReturn},
      ReachesPrefix (MirStep adts bodies) body n s tr out →
      SafeAndEnsures P out := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_step hstep hreach
      (fun _ _ hr => ih hr)
  | normal hterm hp =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_normal hterm hreach hp

/-- `ExecNormal adts bodies body s P` implies the existence of a finite prefix
reaching `.terminated (.normal v)` with `P v`. -/
theorem execNormal_reaches {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} {P : MirReturn → Prop}
    (hexec : ExecNormal adts bodies body s P) :
    ∃ n v,
      ReachesPrefix (MirStep adts bodies) body n s []
        (.terminated (.normal v)) ∧ P v := by
  induction hexec with
  | step hstep _ ih =>
    cases ih with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        exact ⟨n + 1, v,
          .choice n _ _ _ [] (.terminated (.normal v))
            (toStepResult_of_silent hstep).symm rfl hv.1,
          hv.2⟩
  | normal hterm hp =>
    exact ⟨1, _,
      .terminated 0 _ (.normal _) (toStepResult_of_terminated hterm).symm, hp⟩

/-- `ExecNormal` implies conditional specification refinement `SpecOn`. -/
theorem execNormal_specOn {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {pre : MirState → Prop} {P : MirState → MirReturn → Prop}
    (h_exec : ∀ s, initMirState adts bodies body s → pre s →
      ExecNormal adts bodies body s (P s)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) := by
  refine eventualBehaviorOf_le_normalSpecOn (M := MirMachine adts bodies) ?_
  intro init _ _ out hpre hpfx
  have hsafe := execNormal_safeAndEnsures (h_exec init hpfx.1 hpre) hpfx.2
  exact ⟨hsafe.1, hsafe.2.1⟩

/-- `ExecNormal` implies unconditional specification refinement `Spec`. -/
theorem execNormal_spec {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {P : MirState → MirReturn → Prop}
    (h_exec : ∀ s, initMirState adts bodies body s →
      ExecNormal adts bodies body s (P s)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).Spec (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) :=
  execNormal_specOn (fun s hinit _ => h_exec s hinit)

/-- `ExecNormal` on `pre` implies refinement of a specification restricted
to `pre`. -/
theorem execNormal_spec_on_pre {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {pre : MirState → Prop} {P : MirState → MirReturn → Prop}
    (h_exec : ∀ s, pre s → ExecNormal adts bodies body s (P s)) :
    MirSem adts bodies body ≤
      (fun q => ⟨pre q ∧ True,
        fun _ out =>
          ∀ tr ret, out = .terminated tr (.normal ret) → P q ret⟩) :=
  execNormal_specOn (fun s _ h => h_exec s h.1)

/-- `ExecNormal` on `pre` discharges `EnsuresRetLibInv` for any
`allowCompileTimeGuard` flag. -/
theorem execNormal_ensuresRetLibInv {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} {body : MirBody}
    {pre : MirState → Prop} {allowGuard : Bool}
    (h_exec : ∀ s, pre s →
      ExecNormal adts bodies body s (fun r =>
        r.value.valid adts adtInv r.state body.localCount body.retTy)) :
    let retSpec := EnsuresRetLibInv adts bodies adtInv body pre allowGuard
    MirSem adts bodies body ≤
      (fun q => ⟨pre q ∧ (retSpec q).defined,
        fun h o => (retSpec q).val h.2 o⟩) := by
  intro retSpec s ⟨hpre, _⟩
  refine ⟨fun _ n tr oc hreach =>
    (execNormal_safeAndEnsures (h_exec s hpre) hreach).1, ?_⟩
  intro out hval
  refine ⟨?_, ?_⟩
  · intro tr ret hout
    subst hout
    cases hval.2 with
    | intro n hreach =>
      exact (execNormal_safeAndEnsures (h_exec s hpre) hreach).2.1 ret rfl
  · have hnoErr : ∀ tr, out ≠ .terminated tr .compileTimeError := by
      intro tr hout
      subst hout
      cases hval.2 with
      | intro n hreach =>
        exact (execNormal_safeAndEnsures (h_exec s hpre) hreach).2.2 rfl
    cases allowGuard with
    | false => exact hnoErr
    | true => exact fun _ => hnoErr

/-- Lift `NonVacuousOn dom pre` to `NonVacuousOn dom (fun q => pre q ∧ defP q)`
when `pre` implies `defP`. -/
theorem nonVacuousOn_and_defined {Query : Type} {dom pre defP : Query → Prop}
    (h : NonVacuousOn dom pre) (himp : ∀ q, pre q → defP q) :
    NonVacuousOn dom (fun q => pre q ∧ defP q) :=
  match h with
  | ⟨q, hdom, hpre⟩ => ⟨q, hdom, hpre, himp q hpre⟩

/-- Discharge `(MirLang adts bodies).Verified pre (fun _ _ => True) body` from
`ExecNormal`, with non-vacuity witnessed by `h_inh`. -/
theorem execNormal_verified {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {pre : MirState → Prop} {P : MirState → MirReturn → Prop}
    (h_pre_init : ∀ s, pre s → initMirState adts bodies body s)
    (h_inh : ∃ s₀, pre s₀)
    (h_exec : ∀ s, pre s → ExecNormal adts bodies body s (P s)) :
    (MirLang adts bodies).Verified pre (fun _ _ => True) body := by
  have h_wf : MirSem adts bodies body ≤ wellFormedOn (MirLang adts bodies) pre := by
    refine
      (eventualBehaviorOf_le_wellFormedOn_iff (M := MirMachine adts bodies)).mpr ?_
    intro s n tr out hpre _ hreach
    exact (execNormal_safeAndEnsures (h_exec s hpre) hreach).1
  have h_nonvac : NonVacuousOn (initMirState adts bodies body) pre :=
    match h_inh with
    | ⟨s₀, hs₀⟩ => ⟨s₀, h_pre_init s₀ hs₀, hs₀⟩
  refine ⟨h_nonvac, ?_, ?_⟩
  · intro s hpre
    have hinit : initMirState adts bodies body s := h_pre_init s hpre
    have hdef : (MirSem adts bodies body s).defined := (h_wf s hpre).1
    cases execNormal_reaches (h_exec s hpre) with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        exact ⟨hdef, .terminated [] (.normal v), hinit, n, hv.1⟩
  · intro s hpre
    refine ⟨(h_wf s hpre).1, fun _ _ => True.intro⟩

/-- Combined per-function verification and return-invariant obligation for a
public `CapturedFn`, including the per-specification `NonVacuousOn` conjunct
for `EnsuresRetLibInv`. -/
abbrev FnVerifiedAndRetInv (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) (adtInv : AdtInv) (fn : CapturedFn)
    (tcb : List TCBItem := []) : Prop :=
  let body := fn.resolveBody bodies
  let pre := fun s => fn.effectivePre adts bodies adtInv s tcb
  let retSpec :=
    EnsuresRetLibInv adts bodies adtInv body pre
      (hasCompileTimeGuardWaiver fn tcb)
  (MirLang adts bodies).Verified pre (fun _ _ => True) body ∧
  NonVacuousOn (initMirState adts bodies body)
    (fun s => pre s ∧ (retSpec s).defined) ∧
  MirSem adts bodies body ≤ (fun q => ⟨pre q ∧ (retSpec q).defined,
    fun h o => (retSpec q).val h.2 o⟩)

/-- Discharge `FnVerifiedAndRetInv` directly from `h_inh` and `ExecNormal`. The
return predicate reads the returned value in the terminal state. -/
theorem execNormal_fnVerifiedAndRetInv {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    {tcb : List TCBItem}
    (h_inh : ∃ s₀, fn.effectivePre adts bodies adtInv s₀ tcb)
    (h_exec : ∀ s, fn.effectivePre adts bodies adtInv s tcb →
      ExecNormal adts bodies (fn.resolveBody bodies) s (fun r =>
        r.value.valid adts adtInv r.state (fn.resolveBody bodies).localCount
          (fn.resolveBody bodies).retTy)) :
    FnVerifiedAndRetInv adts bodies adtInv fn tcb := by
  have h_ver := execNormal_verified (fun _ h => h.1) h_inh h_exec
  exact ⟨h_ver,
    nonVacuousOn_and_defined h_ver.1 (fun _ hpre => hpre),
    execNormal_ensuresRetLibInv h_exec⟩

/-- Discharge `FnVerifiedAndRetInv` when `hasCompileTimeGuardWaiver fn tcb = true`,
given that execution from any state in `effectivePre` either returns a valid
result (`ExecNormal`) or terminates with `.compileTimeError`
(`ExecCompileTimeError`), and returns normally in the zero-extra-padding world
(`s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8)`). -/
theorem execNormalOrGuard_fnVerifiedAndRetInv {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    {tcb : List TCBItem}
    (hguard : hasCompileTimeGuardWaiver fn tcb = true)
    (h_inh : ∃ s₀, fn.effectivePre adts bodies adtInv s₀ tcb)
    (h_exec : ∀ s, fn.effectivePre adts bodies adtInv s tcb →
      (s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8) →
        ExecNormal adts bodies (fn.resolveBody bodies) s (fun r =>
          r.value.valid adts adtInv r.state (fn.resolveBody bodies).localCount
            (fn.resolveBody bodies).retTy)) ∧
      (ExecNormal adts bodies (fn.resolveBody bodies) s (fun r =>
          r.value.valid adts adtInv r.state (fn.resolveBody bodies).localCount
            (fn.resolveBody bodies).retTy) ∨
       ExecCompileTimeError adts bodies (fn.resolveBody bodies) s)) :
    FnVerifiedAndRetInv adts bodies adtInv fn tcb := by
  let body := fn.resolveBody bodies
  let pre := fun s => fn.effectivePre adts bodies adtInv s tcb
  have h_wf : MirSem adts bodies body ≤ wellFormedOn (MirLang adts bodies) pre := by
    refine
      (eventualBehaviorOf_le_wellFormedOn_iff (M := MirMachine adts bodies)).mpr ?_
    intro s n tr out hpre _ hreach
    cases (h_exec s hpre).2 with
    | inl hnorm => exact (execNormal_safeAndEnsures hnorm hreach).1
    | inr hcte => exact (execCompileTimeError_safe_and_not_normal hcte hreach).1
  have h_nonvac : NonVacuousOn (initMirState adts bodies body) pre :=
    match h_inh with
    | ⟨s₀, hs₀⟩ => ⟨s₀, hs₀.1, hs₀⟩
  have h_ver : (MirLang adts bodies).Verified pre (fun _ _ => True) body := by
    refine ⟨h_nonvac, ?_, ?_⟩
    · intro s hpre
      have hdef : (MirSem adts bodies body s).defined := (h_wf s hpre).1
      cases (h_exec s hpre).2 with
      | inl hnorm =>
        cases execNormal_reaches hnorm with
        | intro n hn =>
          cases hn with
          | intro v hv =>
            exact ⟨hdef, .terminated [] (.normal v), hpre.1, n, hv.1⟩
      | inr hcte =>
        cases execCompileTimeError_reaches hcte with
        | intro n hr =>
          exact ⟨hdef, .terminated [] .compileTimeError, hpre.1, n, hr⟩
    · intro s hpre
      exact ⟨(h_wf s hpre).1, fun _ _ => True.intro⟩
  refine ⟨h_ver, nonVacuousOn_and_defined h_ver.1 (fun _ hpre => hpre), ?_⟩
  intro s ⟨hpre, _⟩
  refine ⟨(h_wf s hpre).1, ?_⟩
  intro out hval
  refine ⟨?_, ?_⟩
  · intro tr ret hout
    subst hout
    cases hval.2 with
    | intro n hreach =>
      cases (h_exec s hpre).2 with
      | inl hnorm =>
        exact (execNormal_safeAndEnsures hnorm hreach).2.1 ret rfl
      | inr hcte =>
        exact False.elim
          ((execCompileTimeError_safe_and_not_normal hcte hreach).2 ret rfl)
  · rw [if_true_eq hguard]
    intro h0 tr hout
    subst hout
    cases hval.2 with
    | intro n hreach =>
      have hnorm := (h_exec s hpre).1 h0
      exact (execNormal_safeAndEnsures hnorm hreach).2.2 rfl

/-- Equivalence of `fn.effectivePre` across in-place lowering `lowerBody` when
`lowerBody (fn.resolveBody bodies) = target` and `hasPinnedCoupledWaiver fn tcb = false`. -/
theorem effectivePre_of_lowerBody_eq {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} {fn : CapturedFn}
    {target : MirBody} {s : MirState} {tcb : List TCBItem}
    (hres : lowerBody (fn.resolveBody bodies) = target)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    fn.effectivePre adts bodies adtInv s tcb ↔
      initMirState adts bodies target s ∧
      argsMatchInv adts adtInv target.localCount s target.argTys ∧
      denoteRequires fn.requires s := by
  have hlc : (fn.resolveBody bodies).localCount = target.localCount := by
    rw [← lowerBody_localCount (fn.resolveBody bodies), hres]
  have hargs : (fn.resolveBody bodies).argTys = target.argTys := by
    rw [← lowerBody_argTys (fn.resolveBody bodies), hres]
  have hret : (fn.resolveBody bodies).retTy = target.retTy := by
    rw [← lowerBody_retTy (fn.resolveBody bodies), hres]
  dsimp [CapturedFn.effectivePre, CapturedFn.safetyPre, initMirState,
    initEntryState]
  rw [hpin, hlc, hargs, hret]
  exact Iff.rfl

/-- Discharge `FnVerifiedAndRetInv` for `fn` from an `ExecNormal` proof on its
normalized body `target = lowerBody (fn.resolveBody bodies)`. -/
theorem execNormal_fnVerifiedAndRetInv_of_lowerBody {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    (target : MirBody) {tcb : List TCBItem}
    (hres : lowerBody (fn.resolveBody bodies) = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl)
    (h_inh : ∃ s₀,
      initMirState adts bodies target s₀ ∧
      argsMatchInv adts adtInv target.localCount s₀ target.argTys ∧
      denoteRequires fn.requires s₀)
    (h_exec : ∀ s,
      initMirState adts bodies target s →
      argsMatchInv adts adtInv target.localCount s target.argTys →
      denoteRequires fn.requires s →
      ExecNormal adts bodies target s (fun r =>
        r.value.valid adts adtInv r.state target.localCount target.retTy)) :
    FnVerifiedAndRetInv adts bodies adtInv fn tcb := by
  have hcallsOrig :
      (fn.resolveBody bodies).blocks.all
        (fun bb => !isCall1 bb.terminator) = true := by
    rw [← noCall_lowerBody (fn.resolveBody bodies), hres]
    exact hcalls
  have hlc : (fn.resolveBody bodies).localCount = target.localCount := by
    rw [← lowerBody_localCount (fn.resolveBody bodies), hres]
  have hret : (fn.resolveBody bodies).retTy = target.retTy := by
    rw [← lowerBody_retTy (fn.resolveBody bodies), hres]
  cases h_inh with
  | intro s₀ hs₀ =>
    refine execNormal_fnVerifiedAndRetInv fn
      ⟨s₀, (effectivePre_of_lowerBody_eq hres hpin).mpr hs₀⟩ ?_
    intro s hpre
    have ⟨hinitT, hargsT, hreqT⟩ :=
      (effectivePre_of_lowerBody_eq hres hpin).mp hpre
    rw [hlc, hret]
    have hexecLow :
        ExecNormal adts bodies (lowerBody (fn.resolveBody bodies)) s
          (fun r =>
            r.value.valid adts adtInv r.state target.localCount target.retTy) := by
      rw [hres]
      exact h_exec s hinitT hargsT hreqT
    exact lowerBody_simulates hcallsOrig
      (stmtIdxInvariant_valid adts adtInv target.localCount target.retTy)
      hinitT.2.1 hinitT.2.2.1 hinitT.2.2.2.1 hexecLow

/-- Inductive failure symbolic execution relation for negative canaries. -/
inductive ExecFail (adts : List AdtDecl := []) (bodies : List BodyDecl := [])
    (body : MirBody) : MirState → Prop where
  | step {s s' : MirState} :
      evalMirStep adts bodies body s = .silent s' →
      ExecFail adts bodies body s' →
      ExecFail adts bodies body s
  | fail {s : MirState} :
      evalMirStep adts bodies body s = .failed →
      ExecFail adts bodies body s

theorem execFail_reaches {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} (hexec : ExecFail adts bodies body s) :
    ∃ n, ReachesPrefix (MirStep adts bodies) body n s [] .failed := by
  induction hexec with
  | step hstep _ ih =>
    cases ih with
    | intro n hr =>
      exact ⟨n + 1,
        .choice n _ _ _ [] .failed (toStepResult_of_silent hstep).symm rfl hr⟩
  | fail hfail =>
    exact ⟨1, .failed 0 _ (toStepResult_of_failed hfail).symm⟩

/-- No prefix from an `ExecFail` state can terminate normally. -/
theorem execFail_not_normal {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} (hexec : ExecFail adts bodies body s) :
    ∀ {n : Nat} {tr : List Empty} {v : MirReturn},
      ReachesPrefix (MirStep adts bodies) body n s tr
        (.terminated (.normal v)) → False := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr v hreach
    exact reachesPrefix_not_normal_of_step hstep hreach (fun _ _ hr => ih hr)
  | fail hfail =>
    intro n tr v hreach
    exact reachesPrefix_not_normal_of_failed hfail hreach

theorem reachesPrefix_not_unwind_of_step
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s s' : MirState} {n : Nat} {tr : List Empty}
    (hstep : evalMirStep adts bodies body s = .silent s')
    (hreach :
      ReachesPrefix (MirStep adts bodies) body n s tr (.terminated .unwind))
    (hnext : ∀ n' tr',
      ReachesPrefix (MirStep adts bodies) body n' s' tr'
        (.terminated .unwind) → False) :
    False := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => cases hrun
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_not_unwind_of_failed
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s : MirState} {n : Nat} {tr : List Empty}
    (hstep : evalMirStep adts bodies body s = .failed)
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr
      (.terminated .unwind)) :
    False := by
  have hstepR := toStepResult_of_failed hstep
  cases hreach with
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'

/-- No prefix from an `ExecFail` state can unwind. -/
theorem execFail_not_unwind {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} (hexec : ExecFail adts bodies body s) :
    ∀ {n : Nat} {tr : List Empty},
      ReachesPrefix (MirStep adts bodies) body n s tr
        (.terminated .unwind) → False := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr hreach
    exact reachesPrefix_not_unwind_of_step hstep hreach (fun _ _ hr => ih hr)
  | fail hfail =>
    intro n tr hreach
    exact reachesPrefix_not_unwind_of_failed hfail hreach

/-- Two `rustcLowering` and `fnVerified` identifiers are always distinct. -/
theorem tcbItem_rustcLowering_ne_fnVerified {n1 n2 : String}
    {b1 b2 : BodyId}
    (h : TCBItem.rustcLowering n1 b1 = TCBItem.fnVerified n2 b2) : False :=
  TCBItem.noConfusion h

theorem tcbItem_rustcLowering_ne_of_ne {n1 n2 : String} {b1 b2 : BodyId}
    (hne : n1 ≠ n2)
    (h : TCBItem.rustcLowering n1 b1 = TCBItem.rustcLowering n2 b2) : False :=
  TCBItem.noConfusion h (fun hn _ => hne hn)

theorem mem_cons_eq_or_mem {α : Type} {x y : α} {ys : List α}
    (h : x ∈ y :: ys) : x = y ∨ x ∈ ys := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ hm => exact Or.inr hm

/-- The never-waivable verification obligation of the only function of a
single-function crate, extracted from `CrateTheorem`. -/
theorem crateTheorem_single_fnVerified {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn}
    (hdeps : calledTransparentDeps bodies fn.name (fn.resolveBody bodies) = [] := by rfl)
    (h : CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := [TCBItem.rustcLowering fn.name fn.bodyId] }) :
    (Obligation.wellFormedAndSpecsOn (TCBItem.fnVerified fn.name fn.bodyId)
      (MirLang adts bodies)
      (fun s => fn.effectivePre adts bodies (denoteAdtInv adts) s
        [TCBItem.rustcLowering fn.name fn.bodyId])
      (fn.effectiveSpecs adts bodies (denoteAdtInv adts)
        [TCBItem.rustcLowering fn.name fn.bodyId])
      (fn.resolveBody bodies)).prop := by
  have h1 := h.2.2.2.2.1
  dsimp [CapturedFn.obligations] at h1
  rw [hdeps] at h1
  cases h1.2.2.2.2.2.1 with
  | inl hIn =>
    cases mem_cons_eq_or_mem hIn with
    | inl hEq =>
      exact False.elim (tcbItem_rustcLowering_ne_fnVerified hEq.symm)
    | inr hNil => cases hNil
  | inr hVer => exact hVer

/-- A function that fails from some state satisfying its effective
precondition makes a single-function crate unverifiable. -/
theorem crateTheorem_single_rejects_of_fail {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} (s0 : MirState)
    (hpre : fn.effectivePre adts bodies (denoteAdtInv adts) s0
      [TCBItem.rustcLowering fn.name fn.bodyId])
    (hfail : ExecFail adts bodies (fn.resolveBody bodies) s0)
    (hdeps : calledTransparentDeps bodies fn.name (fn.resolveBody bodies) = [] := by rfl) :
    ¬ CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := [TCBItem.rustcLowering fn.name fn.bodyId] } := by
  intro hCrate
  have hWF := (crateTheorem_single_fnVerified hdeps hCrate).1.2.2
  cases execFail_reaches hfail with
  | intro n hr => exact (hWF s0 hpre).1 hpre.1 n [] .failed hr

/-- A function with no initial state makes a single-function crate
unverifiable (model limits at entry fail closed). -/
theorem crateTheorem_single_rejects_of_empty_dom {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn}
    (hempty : ∀ s, ¬ initMirState adts bodies (fn.resolveBody bodies) s)
    (hdeps : calledTransparentDeps bodies fn.name (fn.resolveBody bodies) = [] := by rfl) :
    ¬ CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := [TCBItem.rustcLowering fn.name fn.bodyId] } := by
  intro hCrate
  exact verified_rejects_empty_dom (L := MirLang adts bodies)
    (fn.resolveBody bodies) _ _ hempty
    (crateTheorem_single_fnVerified hdeps hCrate).1

/-- Generic single-function `CrateTheorem` discharge for a function with
specifications `specs`, given `NoDupIds` for `bodies`, its per-function
verification `h_ver`, and a proof of every user specification on
`fn.effectivePre`. -/
theorem verify_single_fn_crate_gen {adts : List AdtDecl}
    {bodies : List BodyDecl} (fn : CapturedFn)
    (h_bodies_nodup : NoDupIds (bodies.map (fun d => d.id.index)))
    (h_adm : AdmissibleAdtInv adts (denoteAdtInv adts))
    (h_ver : FnVerifiedAndRetInv adts bodies (denoteAdtInv adts) fn
      [TCBItem.rustcLowering fn.name fn.bodyId])
    (h_specs : AllHold ((fn.specs.map (denotePostSpec adts bodies)).map
      (fun spec =>
        NonVacuousOn ((MirLang adts bodies).dom (fn.resolveBody bodies))
          (fun q =>
            fn.effectivePre adts bodies (denoteAdtInv adts) q
              [TCBItem.rustcLowering fn.name fn.bodyId] ∧
              (spec q).defined) ∧
        (MirLang adts bodies).sem (fn.resolveBody bodies) ≤ (fun q =>
          ⟨fn.effectivePre adts bodies (denoteAdtInv adts) q
            [TCBItem.rustcLowering fn.name fn.bodyId] ∧ (spec q).defined,
            fun h o => (spec q).val h.2 o⟩))))
    (hdeps : calledTransparentDeps bodies fn.name (fn.resolveBody bodies) = [] := by rfl) :
    CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := [TCBItem.rustcLowering fn.name fn.bodyId]
    } := by
  refine ⟨(by intro h; cases h), h_bodies_nodup, ⟨True.intro, True.intro⟩,
    h_adm, ?_, True.intro⟩
  dsimp [CapturedFn.obligations]
  rw [hdeps]
  exact ⟨(by intro h; cases h),
    ⟨⟨tcbItem_rustcLowering_ne_fnVerified, True.intro⟩, True.intro, True.intro⟩,
    ⟨True.intro, True.intro⟩,
    ⟨True.intro, True.intro⟩,
    ⟨Or.inl (.head _),
     Or.inr ⟨h_ver.1, ⟨h_ver.2.1, h_ver.2.2⟩, h_specs⟩,
     True.intro⟩⟩

/-!
## 3. `pub fn id(x: usize) -> usize { x }` Verification Lemmas
-/

/-- Canonical `Runtime(PostCleanup)` MIR body for
`pub fn id(x: usize) -> usize { x }` using `Operand.copy`. -/
def idCopyBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign (locPlace 0) (.use (.copy (locPlace 1)))]
      terminator := .return_ }
  ]

/-- Canonical `Runtime(PostCleanup)` MIR body for
`pub fn id(x: usize) -> usize { x }` using `Operand.move`. -/
def idMoveBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign (locPlace 0) (.use (.move (locPlace 1)))]
      terminator := .return_ }
  ]

/-- Canonical entry state for a single-`usize`-argument function (`_1 = 0`). -/
def singleArgUsizeInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.usize 0))
  block := 0
  stmtIdx := 0

/-- `idCopyBody` executes to normal termination returning the initial `_1`
under any `bodies` table. -/
theorem idCopyBody_execNormal {bodies : List BodyDecl} (s : MirState)
    (hinit : initMirState [] bodies idCopyBody s) :
    ExecNormal [] bodies idCopyBody s (fun r =>
      s.locals 1 = some r.value ∧
      r.value.valid [] defaultAdtInv r.state 2 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | fieldCons _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        apply ExecNormal.step
        · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
            List.foldr, Option.getD, evalMirStmt, evalOperand, evalPlace,
            assignPlace, locPlace, idCopyBody]
          rw [hv1]
          rfl
        · exact .normal rfl ⟨hv1, True.intro⟩

/-- `idCopyBody` satisfies `EnsuresEqArg 1` under any `bodies`. -/
theorem idCopyBody_satisfies_ensures {bodies : List BodyDecl} :
    MirSem [] bodies idCopyBody ≤ EnsuresEqArg 1 [] bodies :=
  execNormal_spec (fun s hinit =>
    (idCopyBody_execNormal s hinit).map (fun _ h => h.1))

/-- `idCopyBody` satisfies `wellFormed (MirLang [] bodies)`. -/
theorem idCopyBody_satisfies_wellFormed {bodies : List BodyDecl} :
    MirSem [] bodies idCopyBody ≤ wellFormed (MirLang [] bodies) :=
  Preorder.le_trans idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idCopyBody` satisfies `FnVerifiedAndRetInv` for any `fn` whose lowered
body resolves to `idCopyBody`. -/
theorem idCopyBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (hres : lowerBody (fn.resolveBody bodies) = idCopyBody)
    (hreq : fn.requires = none)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb := by
  have hargs : argsMatchInv [] defaultAdtInv 2 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies idCopyBody singleArgUsizeInitState :=
    mkInitEntryState hargs
  have hreq0 : denoteRequires fn.requires singleArgUsizeInitState := by
    rw [hreq]; exact True.intro
  exact execNormal_fnVerifiedAndRetInv_of_lowerBody fn idCopyBody hres rfl hpin
    ⟨singleArgUsizeInitState, hinit, hargs, hreq0⟩
    (fun s hinitS _ _ => (idCopyBody_execNormal s hinitS).map (fun _ h => h.2))

/-- `idMoveBody` executes to normal termination returning the initial `_1`
under any `bodies` table. -/
theorem idMoveBody_execNormal {bodies : List BodyDecl} (s : MirState)
    (hinit : initMirState [] bodies idMoveBody s) :
    ExecNormal [] bodies idMoveBody s (fun r =>
      s.locals 1 = some r.value ∧
      r.value.valid [] defaultAdtInv r.state 2 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | fieldCons _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        apply ExecNormal.step
        · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
            List.foldr, Option.getD, evalMirStmt, evalOperand, evalPlace,
            deinitPlace, assignPlace, locPlace, idMoveBody]
          rw [hv1]
          rfl
        · exact .normal rfl ⟨hv1, True.intro⟩

/-- `idMoveBody` satisfies `EnsuresEqArg 1` under any `bodies`. -/
theorem idMoveBody_satisfies_ensures {bodies : List BodyDecl} :
    MirSem [] bodies idMoveBody ≤ EnsuresEqArg 1 [] bodies :=
  execNormal_spec (fun s hinit =>
    (idMoveBody_execNormal s hinit).map (fun _ h => h.1))

/-- `idMoveBody` satisfies `FnVerifiedAndRetInv` for any `fn` whose lowered
body resolves to `idMoveBody`. -/
theorem idMoveBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (hres : lowerBody (fn.resolveBody bodies) = idMoveBody)
    (hreq : fn.requires = none)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb := by
  have hargs : argsMatchInv [] defaultAdtInv 2 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies idMoveBody singleArgUsizeInitState :=
    mkInitEntryState hargs
  have hreq0 : denoteRequires fn.requires singleArgUsizeInitState := by
    rw [hreq]; exact True.intro
  exact execNormal_fnVerifiedAndRetInv_of_lowerBody fn idMoveBody hres rfl hpin
    ⟨singleArgUsizeInitState, hinit, hargs, hreq0⟩
    (fun s hinitS _ _ => (idMoveBody_execNormal s hinitS).map (fun _ h => h.2))

/-!
## 4. Post-Monomorphization Error (PME) Size-Checked Transmute

A generic `transmute_checked<Src, Dst>` guarded by a `size_of` equality
constant is *not* verifiable as a root function: its `transmute_copy` into
`Dst` is undefined behavior in the model (`canary_generic_transmute_checked_
rejected`). The preserved archetype is a concrete instantiation: a caller that
calls `transmute_checked::<usize, usize>` is verified end to end
(`prove_pme_concrete_transmute_crate`), and an instantiation with mismatched
sizes steps to `.terminated .compileTimeError` at `.evalConst` and is rejected
(`canary_concrete_mismatched_pme_rejected`).
-/

/-- Shorthand for a dereferenced local place `*_idx`. -/
abbrev derefPlace (idx : Nat) : Place :=
  { loc := ⟨idx⟩, projection := [.deref] }

/-- Shorthand for field `0` of local `_idx` (`_idx.0`). -/
abbrev field0Place (idx : Nat) : Place :=
  { loc := ⟨idx⟩, projection := [.field 0] }

/-- Constant body for `assert!(size_of::<T0>() == size_of::<T1>())`, exactly as
`anneal-rustc-capture` emits it from `rustc`'s `Runtime(PostCleanup)` MIR. -/
def sizeEqConstBodyAt (t0 t1 : MirTy) : MirBody where
  argTys := []
  retTy := .unit
  localCount := 5
  blocks := [
    { stmts := [.storageLive ⟨1⟩, .storageLive ⟨2⟩]
      terminator := .callSizeOf (locPlace 2) t0 ⟨1⟩ },
    { stmts := [.storageLive ⟨3⟩]
      terminator := .callSizeOf (locPlace 3) t1 ⟨2⟩ },
    { stmts := [
        .assign (locPlace 1)
          (.binaryOp .eq (.move (locPlace 2)) (.move (locPlace 3)))
      ]
      terminator := .switchInt (.move (locPlace 1)) ⟨4⟩ ⟨3⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .storageDead ⟨2⟩,
        .assign (locPlace 0) (.use (.constVal .unit)),
        .storageDead ⟨1⟩
      ]
      terminator := .return_ },
    { stmts := [.storageDead ⟨3⟩, .storageDead ⟨2⟩, .storageLive ⟨4⟩]
      terminator := .panic }
  ]

/-- The generic size-equality constant (`T0 := Src`, `T1 := Dst`). -/
def sizeEqConstBody : MirBody := sizeEqConstBodyAt (.param 0) (.param 1)

/-- Body of `transmute_checked::<src, dst>(x)` referencing `constId` in
`Crate.bodies`:
`let () = const { assert!(size_of::<Src>() == size_of::<Dst>()) };
unsafe { core::mem::transmute_copy(&x) }`. -/
def transmuteCheckedBodyAt (constId : BodyId) (src dst : MirTy) : MirBody where
  argTys := [src]
  retTy := dst
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .evalConst (locPlace 2) constId [src, dst],
        .storageDead ⟨2⟩,
        .storageLive ⟨3⟩,
        .storageLive ⟨4⟩,
        .assign (locPlace 4) (.ref (locPlace 1)),
        .assign (locPlace 3) (.ref (derefPlace 4))
      ]
      terminator :=
        .callTransmuteCopy (locPlace 0) src dst (.move (locPlace 3)) ⟨1⟩ },
    { stmts := [.storageDead ⟨4⟩, .storageDead ⟨3⟩]
      terminator := .return_ }
  ]

/-- The generic `pub fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst`
referencing `constId`. -/
def transmuteCheckedBody (constId : BodyId := ⟨0⟩) : MirBody :=
  transmuteCheckedBodyAt constId (.param 0) (.param 1)

/-- `transmute_checked` without its PME assertion. -/
def transmuteUncheckedBody : MirBody where
  argTys := [.param 0]
  retTy := .param 1
  localCount := 4
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign (locPlace 3) (.ref (locPlace 1)),
        .assign (locPlace 2) (.ref (derefPlace 3))
      ]
      terminator :=
        .callTransmuteCopy (locPlace 0) (.param 0) (.param 1)
          (.move (locPlace 2)) ⟨1⟩ },
    { stmts := [.storageDead ⟨3⟩, .storageDead ⟨2⟩]
      terminator := .return_ }
  ]

/-- Canonical PME entry state (`_1 = .bytes 8 0`, every parameter 8 bytes). -/
def pmeInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.bytes 8 0))
  block := 0
  stmtIdx := 0
  tySizes := fun _ => 8

/-- Canary (C-2/F2): the generic `transmute_checked<Src, Dst>` is rejected.
Its size check passes when `Src` and `Dst` have equal sizes, but a generic
function is verified for every instantiation, including `Dst := bool` or a
reference, so the transmute into `.param 1` is undefined behavior in the
model. -/
theorem canary_generic_transmute_checked_rejected (fnName : String) :
    let bodies : List BodyDecl := [
      { id := ⟨0⟩, body := sizeEqConstBody },
      { id := ⟨1⟩, body := (transmuteCheckedBody ⟨0⟩) }
    ]
    ¬ CrateTheorem {
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨1⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨1⟩]
    } := by
  intro bodies
  have hargs : argsMatchInv [] defaultAdtInv 5 pmeInitState [.param 0] :=
    ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies (transmuteCheckedBody ⟨0⟩) pmeInitState :=
    mkInitEntryState hargs
  have hfail : ExecFail [] bodies (transmuteCheckedBody ⟨0⟩) pmeInitState := by
    refine .step rfl ?_
    apply ExecFail.step
    · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
        List.foldr, Option.getD, evalMirStmt, transmuteCheckedBody,
        transmuteCheckedBodyAt, findBody, List.find?, Option.map, Option.bind,
        MirBody.subst, BasicBlock.subst, Stmt.subst, Rvalue.subst,
        Terminator.subst, LayoutQuery.subst, MirTy.subst, mapAll,
        sizeEqConstBody, sizeEqConstBodyAt]
      rfl
    · dsimp only [updateLocal, bumpGen]
      exact .step rfl (.step rfl (.step rfl (.step rfl (.step rfl (.fail rfl)))))
  exact crateTheorem_single_rejects_of_fail
    (bodies := bodies) (fn := { name := fnName, bodyId := ⟨1⟩ })
    pmeInitState ⟨hinit, hargs, True.intro⟩ hfail

/-- Canary: removing the PME assertion (`transmuteUncheckedBody`) is likewise
rejected. -/
theorem canary_transmuteUnchecked_rejected (fnName : String) :
    let bodies : List BodyDecl := [
      { id := ⟨0⟩, body := transmuteUncheckedBody }
    ]
    ¬ CrateTheorem {
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨0⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
    } := by
  intro bodies
  have hargs : argsMatchInv [] defaultAdtInv 4 pmeInitState [.param 0] :=
    ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies transmuteUncheckedBody pmeInitState :=
    mkInitEntryState hargs
  exact crateTheorem_single_rejects_of_fail
    (bodies := bodies) (fn := { name := fnName, bodyId := ⟨0⟩ })
    pmeInitState ⟨hinit, hargs, True.intro⟩
    (.step rfl (.step rfl (.step rfl (.step rfl (.fail rfl)))))

/-- Concrete caller `pub fn f(x: usize) -> dstTy { transmute_checked::<usize,
dstTy>(x) }` calling `calleeId` in `Crate.bodies`. -/
def concreteTransmuteCallerBody (calleeId : BodyId) (dstTy : MirTy) :
    MirBody where
  localCount := 3
  argTys := [.usize]
  retTy := dstTy
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign (locPlace 2) (.use (.copy (locPlace 1)))
      ]
      terminator :=
        .call1 (locPlace 0) calleeId (.move (locPlace 2)) ⟨1⟩ [.usize, dstTy] },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]

/-- The concrete caller returns its argument, transmuted to `usize`, from every
initial state. -/
theorem concreteTransmuteCaller_execNormal {bodies : List BodyDecl}
    {calleeId constId : BodyId}
    (hcallee : findBody bodies calleeId = some (transmuteCheckedBody constId))
    (hconst : findBody bodies constId = some sizeEqConstBody)
    (s : MirState)
    (hinit :
      initMirState [] bodies (concreteTransmuteCallerBody calleeId .usize) s) :
    ExecNormal [] bodies (concreteTransmuteCallerBody calleeId .usize) s
      (fun r => r.value.valid [] defaultAdtInv r.state 3 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | fieldCons _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        have hL : locals0 = updateLocal locals0 1 (some (.usize n)) := by
          funext i
          cases i with
          | zero => rfl
          | succ k =>
            cases k with
            | zero => exact hv1
            | succ _ => rfl
        rw [hL]
        refine .step rfl (.step rfl ?_)
        apply ExecNormal.step
        · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
            List.foldr, Option.getD, List.length, evalMirTerminator,
            concreteTransmuteCallerBody]
          rw [hcallee]
          rfl
        · refine .step rfl ?_
          apply ExecNormal.step
          · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
              lookupAt, List.foldr, Option.getD, evalMirStmt,
              transmuteCheckedBody, transmuteCheckedBodyAt, MirBody.subst,
              BasicBlock.subst, Stmt.subst, Rvalue.subst, Terminator.subst,
              MirTy.subst, mapAll, Option.bind, Option.map]
            rw [hconst]
            rfl
          · refine .step rfl ?_
            dsimp only [updateLocal, bumpGen]
            refine .step rfl (.step rfl (.step rfl (.step rfl (.step rfl ?_))))
            dsimp only [updateLocal, bumpGen]
            refine .step rfl (.step rfl (.step rfl (.step rfl ?_)))
            dsimp only [updateLocal, bumpGen]
            exact .normal rfl True.intro

/-- `concreteTransmuteCallerBody calleeId .usize` satisfies
`FnVerifiedAndRetInv` for any `fn` resolving to it when `calleeId` and `constId`
resolve in `bodies`. -/
theorem concreteTransmuteCaller_verified_of_resolve {bodies : List BodyDecl}
    {calleeId constId : BodyId} {tcb : List TCBItem} (fn : CapturedFn)
    (hres : fn.resolveBody bodies = concreteTransmuteCallerBody calleeId .usize)
    (hreq : fn.requires = none)
    (hcallee : findBody bodies calleeId = some (transmuteCheckedBody constId))
    (hconst : findBody bodies constId = some sizeEqConstBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb := by
  have hargs : argsMatchInv [] defaultAdtInv 3 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hcount :
      1 + (concreteTransmuteCallerBody calleeId .usize).argTys.length ≤
        (concreteTransmuteCallerBody calleeId .usize).localCount :=
    Nat.le_succ_of_le (Nat.le_refl 2)
  have hinit :
      initMirState [] bodies (concreteTransmuteCallerBody calleeId .usize)
        singleArgUsizeInitState :=
    mkInitEntryState hargs (hcount := hcount)
  have hpre0 :
      fn.effectivePre [] bodies defaultAdtInv singleArgUsizeInitState tcb := by
    dsimp [CapturedFn.effectivePre, CapturedFn.safetyPre]
    rw [hres, hreq, hpin]
    exact ⟨hinit, hargs, True.intro⟩
  refine execNormal_fnVerifiedAndRetInv fn ⟨singleArgUsizeInitState, hpre0⟩ ?_
  intro s hpre
  have hinitS :
      initMirState [] bodies (concreteTransmuteCallerBody calleeId .usize) s := by
    have h1 := hpre.1
    rw [hres] at h1
    exact h1
  rw [hres]
  exact concreteTransmuteCaller_execNormal hcallee hconst s hinitS

/-- Canary: instantiating `transmute_checked` at `[.usize, .bool]` (8 vs 1
bytes) steps to `.terminated .compileTimeError` at `.evalConst` and refutes
`CrateTheorem`. -/
theorem canary_concrete_mismatched_pme_rejected (fnName : String) :
    let bodies : List BodyDecl := [
      { id := ⟨0⟩, body := sizeEqConstBody },
      { id := ⟨1⟩, body := (transmuteCheckedBody ⟨0⟩) },
      { id := ⟨2⟩, body := (concreteTransmuteCallerBody ⟨1⟩ .bool) }
    ]
    ExecCompileTimeError [] bodies (concreteTransmuteCallerBody ⟨1⟩ .bool)
      singleArgUsizeInitState ∧
    ¬ CrateTheorem {
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨2⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨2⟩]
    } := by
  intro bodies
  have hexec :
      ExecCompileTimeError [] bodies (concreteTransmuteCallerBody ⟨1⟩ .bool)
        singleArgUsizeInitState := by
    refine .step rfl (.step rfl ?_)
    apply ExecCompileTimeError.step
    · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
        List.foldr, Option.getD, List.length, evalMirTerminator,
        concreteTransmuteCallerBody, findBody, List.find?, Option.map,
        Option.bind, Option.elim, MirBody.subst, BasicBlock.subst, Stmt.subst,
        Rvalue.subst, Terminator.subst, LayoutQuery.subst, MirTy.subst, mapAll,
        transmuteCheckedBody, transmuteCheckedBodyAt]
      rfl
    · refine .step rfl ?_
      apply ExecCompileTimeError.compileTimeError
      dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
        List.foldr, Option.getD, evalMirStmt, findBody, List.find?, Option.map,
        Option.bind, MirBody.subst, BasicBlock.subst, Stmt.subst, Rvalue.subst,
        Terminator.subst, LayoutQuery.subst, MirTy.subst, mapAll,
        sizeEqConstBody, sizeEqConstBodyAt]
      rfl
  refine ⟨hexec, ?_⟩
  intro hCrate
  have hRetInv := (crateTheorem_single_fnVerified rfl hCrate).2.1.2
  have hargs : argsMatchInv [] defaultAdtInv 3 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit :
      initMirState [] bodies (concreteTransmuteCallerBody ⟨1⟩ .bool)
        singleArgUsizeInitState :=
    mkInitEntryState hargs
  have hpre :
      CapturedFn.effectivePre [] bodies defaultAdtInv
        { name := fnName, bodyId := ⟨2⟩ } singleArgUsizeInitState
        [TCBItem.rustcLowering fnName ⟨2⟩] :=
    ⟨hinit, hargs, True.intro⟩
  cases hRetInv singleArgUsizeInitState ⟨hpre, hpre⟩ with
  | intro hdef hval =>
    cases execCompileTimeError_reaches hexec with
    | intro n hr =>
      have hpfx :
          (MirSem [] bodies (concreteTransmuteCallerBody ⟨1⟩ .bool)
            singleArgUsizeInitState).val hdef
            (.terminated [] .compileTimeError) :=
        ⟨hinit, n, hr⟩
      exact (hval _ hpfx).2 [] rfl

/-!
## 5. `NonZeroUsize` Library Verification Contract Lemmas and Canaries
-/

/-- Captured ADT declaration for `pub struct NonZeroUsize { val: usize }` with a
private field (`FieldAccess.priv`) and `/// anneal:invariant val != 0`. -/
def nonZeroAdtDecl (adtId : Nat := 0) (repr : AdtRepr := .rust) : AdtDecl where
  id := adtId
  repr := repr
  fields := [{ ty := .usize, access := .priv }]
  invariant := some { ne := 0 }

/-- Captured ADT declaration for `pub struct NonZeroUsize { pub val: usize }`
with a public safe field (`FieldAccess.pubSafe`) and
`/// anneal:invariant val != 0`. -/
def pubSafeNonZeroAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .pubSafe }]
  invariant := some { ne := 0 }

/-- Standard ADT representation invariant for `NonZeroUsize` (`adtId = 0`),
denoted from `[nonZeroAdtDecl 0 repr]`. -/
abbrev nonZeroAdtInv (repr : AdtRepr := .rust) : AdtInv :=
  denoteAdtInv [nonZeroAdtDecl 0 repr]

/-- Standard `# Safety` precondition (`/// anneal:requires x != 0`) for
`pub unsafe fn new_unchecked`. -/
abbrev newUncheckedRequires : Option RequiresSpec :=
  some { argLocal := 1, ne := 0 }

abbrev newUncheckedSafetyPre (s : MirState) : Prop :=
  denoteRequires newUncheckedRequires s

/-- `nonZeroAdtInv repr` is admissible for `[nonZeroAdtDecl 0 repr]`. -/
theorem nonZeroAdtInv_admissible {repr : AdtRepr} :
    AdmissibleAdtInv [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr) := by
  refine ⟨⟨True.intro, True.intro⟩, ?_⟩
  intro decl hmem hPub
  cases hmem with
  | head => cases hPub
  | tail _ hnil => cases hnil

/-- Canary: if `NonZeroUsize`'s field `val` is made `pub`
(`pubSafeNonZeroAdtDecl`), then `nonZeroAdtInv` violates `AdmissibleAdtInv`. -/
theorem canary_pub_safe_fields_reject_nonzero_inv :
    ¬ AdmissibleAdtInv [pubSafeNonZeroAdtDecl] nonZeroAdtInv := by
  intro hAdm
  exact hAdm.2 pubSafeNonZeroAdtDecl (.head _) rfl
    (constEntryState (fun _ => 0)) (.usize 0) True.intro rfl

/-- Canonical `rustc` MIR body for `pub fn make_nonzero(x: usize) -> NonZeroUsize`
parameterized by `adtId`. -/
def makeNonZeroBodyAt (adtId : Nat := 0) : MirBody where
  argTys := [.usize]
  retTy := .adt adtId
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign (locPlace 3) (.use (.copy (locPlace 1))),
        .assign (locPlace 2)
          (.binaryOp .eq (.move (locPlace 3)) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move (locPlace 2)) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign (locPlace 0) (.aggregate adtId (.constVal (.usize 1)))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .storageLive ⟨4⟩,
        .assign (locPlace 4) (.use (.copy (locPlace 1))),
        .assign (locPlace 0) (.aggregate adtId (.move (locPlace 4))),
        .storageDead ⟨4⟩
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]

abbrev makeNonZeroBody : MirBody := makeNonZeroBodyAt 0

/-- Canonical `rustc` MIR body for
`pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize` parameterized by
`adtId`. -/
def newUncheckedBodyAt (adtId : Nat := 0) : MirBody where
  argTys := [.usize]
  retTy := .adt adtId
  localCount := 3
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign (locPlace 2) (.use (.copy (locPlace 1))),
        .assign (locPlace 0) (.aggregate adtId (.move (locPlace 2))),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

abbrev newUncheckedBody : MirBody := newUncheckedBodyAt 0

/-- Canonical `rustc` MIR body for
`pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize` parameterized by
`adtId` and whether the final read in block 2 is `.copy` or `.move`. -/
def getUncheckedNonZeroBodyAt (adtId : Nat := 0)
    (moveFinal : Bool := false) : MirBody where
  argTys := [.adt adtId]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign (locPlace 3) (.use (.copy (field0Place 1))),
        .assign (locPlace 2)
          (.binaryOp .eq (.move (locPlace 3)) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move (locPlace 2)) ⟨2⟩ ⟨1⟩ },
    { stmts := [.storageDead ⟨3⟩, .storageLive ⟨4⟩]
      terminator := .unreachable },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign (locPlace 0)
          (.use (if moveFinal then .move (field0Place 1)
                 else .copy (field0Place 1))),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

abbrev getUncheckedNonZeroBody : MirBody := getUncheckedNonZeroBodyAt 0 false

/-- Canonical `rustc` MIR body for a buggy safe constructor returning `0`. -/
def buggyZeroBody : MirBody where
  argTys := [.usize]
  retTy := .adt 0
  localCount := 2
  blocks := [
    { stmts := [.assign (locPlace 0) (.aggregate 0 (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Canonical entry state with `_1 = .usize 1`. -/
def singleArgNonZeroUsizeInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.usize 1))
  block := 0
  stmtIdx := 0

/-- Canonical entry state with `_1 = .adt adtId (.usize 1)`. -/
def singleArgAdtNonZeroInitState (adtId : Nat := 0) : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.adt adtId (.usize 1)))
  block := 0
  stmtIdx := 0

theorem nat_beq_refl (n : Nat) : (n == n) = true :=
  beq_iff_eq.mpr rfl

/-- `makeNonZeroBody` executes to normal completion returning a valid
`NonZeroUsize` from any `initMirState`. -/
theorem makeNonZeroBody_execNormal {bodies : List BodyDecl} {repr : AdtRepr}
    (s : MirState)
    (hinit : initMirState [nonZeroAdtDecl 0 repr] bodies makeNonZeroBody s)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    ExecNormal [nonZeroAdtDecl 0 repr] bodies makeNonZeroBody s
      (fun r =>
        r.value.valid [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr) r.state 5
          (.adt 0)) := by
  cases hrepr with
  | inl hrepr | inr hrepr =>
    subst hrepr
    cases s with
    | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
      have hb : block0 = 0 := hinit.1
      have hs : stmtIdx0 = 0 := hinit.2.1
      have hc : curBody0 = none := hinit.2.2.1
      have hst : stack0 = [] := hinit.2.2.2.1
      have hfid : frameId0 = 0 := hinit.2.2.2.2.1
      have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
      have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
      subst hb hs hc hst hfid hnfid hlg
      cases (initEntryState_argsMatch hinit).1 with
      | intro v hv =>
        have hv1 : locals0 1 = some v := hv.1
        have hvty := hv.2
        cases v with
        | uninit => cases hvty
        | bool _ => cases hvty
        | unit => cases hvty
        | adt _ _ => cases hvty
        | fieldCons _ _ => cases hvty
        | bytes _ _ => cases hvty
        | ref _ _ _ => cases hvty
        | usize n =>
          refine .step rfl (.step rfl ?_)
          apply ExecNormal.step
          · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
              List.foldr, Option.getD, evalMirStmt, evalOperand, evalPlace,
              assignPlace, locPlace, makeNonZeroBody, makeNonZeroBodyAt,
              updateLocal]
            rw [hv1]
            rfl
          · refine .step rfl ?_
            cases n with
            | zero =>
              refine .step rfl (.step rfl (.step rfl (.step rfl
                (.step rfl (.normal rfl ⟨rfl, Nat.succ_ne_zero 0, True.intro⟩)))))
            | succ k =>
              refine .step rfl (.step rfl (.step rfl ?_))
              apply ExecNormal.step
              · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
                  lookupAt, List.foldr, Option.getD, evalMirStmt, evalOperand,
                  evalPlace, assignPlace, locPlace, makeNonZeroBody,
                  makeNonZeroBodyAt, updateLocal]
                rw [hv1]
                rfl
              · exact .step rfl (.step rfl (.step rfl (.step rfl
                  (.normal rfl ⟨rfl, Nat.succ_ne_zero k, True.intro⟩))))

/-- `makeNonZeroBody` satisfies `FnVerifiedAndRetInv` for any `fn` whose lowered
body resolves to `makeNonZeroBody`. -/
theorem makeNonZeroBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem} {repr : AdtRepr}
    (fn : CapturedFn)
    (hres : lowerBody (fn.resolveBody bodies) = makeNonZeroBody)
    (hreq : fn.requires = none)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    FnVerifiedAndRetInv [nonZeroAdtDecl 0 repr] bodies (nonZeroAdtInv repr) fn
      tcb := by
  have hargs :
      argsMatchInv [nonZeroAdtDecl 0 repr] defaultAdtInv 5
        singleArgNonZeroUsizeInitState [.usize] :=
    ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hargsInv :
      argsMatchInv [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr) 5
        singleArgNonZeroUsizeInitState [.usize] :=
    ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hretWf :
      MirTy.wfInAdts [nonZeroAdtDecl 0 repr] makeNonZeroBody.retTy = true := by
    cases hrepr with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hinit :
      initMirState [nonZeroAdtDecl 0 repr] bodies makeNonZeroBody
        singleArgNonZeroUsizeInitState :=
    mkInitEntryState hargs (hretWf := hretWf)
  have hreq0 : denoteRequires fn.requires singleArgNonZeroUsizeInitState := by
    rw [hreq]; exact True.intro
  exact execNormal_fnVerifiedAndRetInv_of_lowerBody fn makeNonZeroBody hres rfl
    hpin ⟨singleArgNonZeroUsizeInitState, hinit, hargsInv, hreq0⟩
    (fun s hinitS _ _ => makeNonZeroBody_execNormal s hinitS hrepr)

/-- `newUncheckedBody` executes to normal completion returning a valid
`NonZeroUsize` from any state satisfying its `effectivePre`. -/
theorem newUncheckedBody_execNormal {bodies : List BodyDecl} {repr : AdtRepr}
    (s : MirState)
    (hinit : initMirState [nonZeroAdtDecl 0 repr] bodies newUncheckedBody s)
    (hsafety : newUncheckedSafetyPre s)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    ExecNormal [nonZeroAdtDecl 0 repr] bodies newUncheckedBody s
      (fun r =>
        r.value.valid [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr) r.state 3
          (.adt 0)) := by
  cases hrepr with
  | inl hrepr | inr hrepr =>
    subst hrepr
    cases s with
    | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
      have hb : block0 = 0 := hinit.1
      have hs : stmtIdx0 = 0 := hinit.2.1
      have hc : curBody0 = none := hinit.2.2.1
      have hst : stack0 = [] := hinit.2.2.2.1
      have hfid : frameId0 = 0 := hinit.2.2.2.2.1
      have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
      have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
      subst hb hs hc hst hfid hnfid hlg
      cases (initEntryState_argsMatch hinit).1 with
      | intro v hv =>
        have hv1 : locals0 1 = some v := hv.1
        have hvty := hv.2
        cases v with
        | uninit => cases hvty
        | bool _ => cases hvty
        | unit => cases hvty
        | adt _ _ => cases hvty
        | fieldCons _ _ => cases hvty
        | bytes _ _ => cases hvty
        | ref _ _ _ => cases hvty
        | usize n =>
          have hne0 : n ≠ 0 := hsafety n hv1
          refine .step rfl ?_
          apply ExecNormal.step
          · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
              List.foldr, Option.getD, evalMirStmt, evalOperand, evalPlace,
              assignPlace, locPlace, newUncheckedBody, newUncheckedBodyAt,
              updateLocal]
            rw [hv1]
            rfl
          · exact .step rfl (.step rfl (.normal rfl ⟨rfl, hne0, True.intro⟩))

/-- `newUncheckedBody` satisfies `FnVerifiedAndRetInv` for any `fn` whose
lowered body is `newUncheckedBody` with `requires = newUncheckedRequires`. -/
theorem newUncheckedBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem} {repr : AdtRepr}
    (fn : CapturedFn)
    (hres : lowerBody (fn.resolveBody bodies) = newUncheckedBody)
    (hreq : fn.requires = newUncheckedRequires)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    FnVerifiedAndRetInv [nonZeroAdtDecl 0 repr] bodies (nonZeroAdtInv repr) fn
      tcb := by
  have hargs :
      argsMatchInv [nonZeroAdtDecl 0 repr] defaultAdtInv 3
        singleArgNonZeroUsizeInitState [.usize] :=
    ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hretWf :
      MirTy.wfInAdts [nonZeroAdtDecl 0 repr] newUncheckedBody.retTy = true := by
    cases hrepr with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hinit :
      initMirState [nonZeroAdtDecl 0 repr] bodies newUncheckedBody
        singleArgNonZeroUsizeInitState :=
    mkInitEntryState hargs (hretWf := hretWf)
  have hsafety0 : newUncheckedSafetyPre singleArgNonZeroUsizeInitState := by
    intro n hn
    injection hn with hv
    injection hv with h1
    subst h1
    exact Nat.succ_ne_zero 0
  have hreq0 : denoteRequires fn.requires singleArgNonZeroUsizeInitState := by
    rw [hreq]
    exact hsafety0
  refine execNormal_fnVerifiedAndRetInv_of_lowerBody fn newUncheckedBody hres rfl
    hpin ⟨singleArgNonZeroUsizeInitState, hinit,
      ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩,
      hreq0⟩ ?_
  intro s hinitS _ hreqS
  have hsafetyS : newUncheckedSafetyPre s := by
    rw [hreq] at hreqS
    exact hreqS
  exact newUncheckedBody_execNormal s hinitS hsafetyS hrepr

/-- `getUncheckedNonZeroBodyAt 0 moveFinal` executes to normal completion
from any state satisfying its `effectivePre`. -/
theorem getUncheckedNonZeroBody_execNormal {bodies : List BodyDecl}
    {repr : AdtRepr} (moveFinal : Bool) (s : MirState)
    (hinit : initMirState [nonZeroAdtDecl 0 repr] bodies
      (getUncheckedNonZeroBodyAt 0 moveFinal) s)
    (hargs :
      argsMatchInv [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr) 5 s [.adt 0])
    (hrepr : repr = .rust ∨ repr = .transparent) :
    ExecNormal [nonZeroAdtDecl 0 repr] bodies
      (getUncheckedNonZeroBodyAt 0 moveFinal) s (fun r =>
        r.value.valid [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr) r.state 5
          .usize) := by
  cases hrepr with
  | inl hrepr | inr hrepr =>
    subst hrepr
    cases s with
    | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
      have hb : block0 = 0 := hinit.1
      have hs : stmtIdx0 = 0 := hinit.2.1
      have hc : curBody0 = none := hinit.2.2.1
      have hst : stack0 = [] := hinit.2.2.2.1
      have hfid : frameId0 = 0 := hinit.2.2.2.2.1
      have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
      have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
      subst hb hs hc hst hfid hnfid hlg
      cases hargs.1 with
      | intro v hv =>
        have hv1 : locals0 1 = some v := hv.1
        have hvinv := hv.2
        cases v with
        | uninit => cases hvinv
        | usize _ => cases hvinv
        | bool _ => cases hvinv
        | unit => cases hvinv
        | fieldCons _ _ => cases hvinv
        | bytes _ _ => cases hvinv
        | ref _ _ _ => cases hvinv
        | adt vAdtId inner =>
          have hveq : vAdtId = 0 := hvinv.1
          subst hveq
          cases inner with
          | uninit => cases hvinv.2.2
          | bool _ => cases hvinv.2.2
          | unit => cases hvinv.2.2
          | adt _ _ => cases hvinv.2.2
          | fieldCons _ _ => cases hvinv.2.2
          | bytes _ _ => cases hvinv.2.2
          | ref _ _ _ => cases hvinv.2.2
          | usize n =>
            cases n with
            | zero => exact False.elim (hvinv.2.1 rfl)
            | succ k =>
              refine .step rfl (.step rfl ?_)
              apply ExecNormal.step
              · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
                  lookupAt, List.foldr, Option.getD, evalMirStmt, evalOperand,
                  evalPlace, evalProj, getFieldVal, MirVal.isFullyInit,
                  assignPlace, locPlace, field0Place, getUncheckedNonZeroBodyAt,
                  updateLocal]
                rw [hv1]
                rfl
              · refine .step rfl (.step rfl (.step rfl ?_))
                cases moveFinal with
                | false =>
                  apply ExecNormal.step
                  · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
                      lookupAt, List.foldr, Option.getD,
                      getUncheckedNonZeroBodyAt]
                    rw [if_false_eq (by intro h; cases h)]
                    dsimp only [evalMirStmt, evalOperand, evalPlace, evalProj,
                      getFieldVal, MirVal.isFullyInit, assignPlace, locPlace,
                      field0Place, updateLocal]
                    rw [hv1]
                    rfl
                  · exact .step rfl (.normal rfl True.intro)
                | true =>
                  apply ExecNormal.step
                  · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
                      lookupAt, List.foldr, Option.getD,
                      getUncheckedNonZeroBodyAt]
                    rw [if_true_eq rfl]
                    dsimp only [evalMirStmt, evalOperand, evalPlace, evalProj,
                      getFieldVal, setFieldVal, deinitPlace, updateProj,
                      MirVal.isFullyInit, assignPlace, locPlace, field0Place,
                      updateLocal]
                    rw [hv1]
                    rfl
                  · exact .step rfl (.normal rfl True.intro)

/-- `getUncheckedNonZeroBodyAt 0 moveFinal` satisfies `FnVerifiedAndRetInv`
for any `fn` whose lowered body is `getUncheckedNonZeroBodyAt 0 moveFinal`. -/
theorem getUncheckedNonZeroBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem} {repr : AdtRepr}
    (moveFinal : Bool) (fn : CapturedFn)
    (hres :
      lowerBody (fn.resolveBody bodies) =
        getUncheckedNonZeroBodyAt 0 moveFinal)
    (hreq : fn.requires = none)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    FnVerifiedAndRetInv [nonZeroAdtDecl 0 repr] bodies (nonZeroAdtInv repr) fn
      tcb := by
  have hcount :
      1 + (getUncheckedNonZeroBodyAt 0 moveFinal).argTys.length ≤
        (getUncheckedNonZeroBodyAt 0 moveFinal).localCount :=
    Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2)))
  have hvalDef :
      validAdtDecl
        (MirVal.validFuel [nonZeroAdtDecl 0 repr] defaultAdtInv
          (singleArgAdtNonZeroInitState 0) 5 1)
        (nonZeroAdtDecl 0 repr) (.usize 1) := by
    cases hrepr with
    | inl h => subst h; exact True.intro
    | inr h => subst h; exact True.intro
  have hvalInv :
      validAdtDecl
        (MirVal.validFuel [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr)
          (singleArgAdtNonZeroInitState 0) 5 1)
        (nonZeroAdtDecl 0 repr) (.usize 1) := by
    cases hrepr with
    | inl h => subst h; exact True.intro
    | inr h => subst h; exact True.intro
  have hargWf :
      (getUncheckedNonZeroBodyAt 0 moveFinal).argTys.all
        (MirTy.wfInAdts [nonZeroAdtDecl 0 repr]) = true := by
    cases hrepr with
    | inl h => subst h; rfl
    | inr h => subst h; rfl
  have hargsDef :
      argsMatchInv [nonZeroAdtDecl 0 repr] defaultAdtInv 5
        (singleArgAdtNonZeroInitState 0) [.adt 0] :=
    ⟨⟨.adt 0 (.usize 1), rfl, rfl, True.intro, hvalDef⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hargsInv :
      argsMatchInv [nonZeroAdtDecl 0 repr] (nonZeroAdtInv repr) 5
        (singleArgAdtNonZeroInitState 0) [.adt 0] :=
    ⟨⟨.adt 0 (.usize 1), rfl, rfl, Nat.succ_ne_zero 0, hvalInv⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit :
      initMirState [nonZeroAdtDecl 0 repr] bodies
        (getUncheckedNonZeroBodyAt 0 moveFinal)
        (singleArgAdtNonZeroInitState 0) :=
    mkInitEntryState hargsDef (hcount := hcount) (hargWf := hargWf)
  have hreq0 :
      denoteRequires fn.requires (singleArgAdtNonZeroInitState 0) := by
    rw [hreq]
    exact True.intro
  refine execNormal_fnVerifiedAndRetInv_of_lowerBody fn
    (getUncheckedNonZeroBodyAt 0 moveFinal) hres (by cases moveFinal <;> rfl)
    hpin ⟨singleArgAdtNonZeroInitState 0, hinit, hargsInv, hreq0⟩ ?_
  intro s hinitS hargsS _
  exact getUncheckedNonZeroBody_execNormal moveFinal s hinitS hargsS hrepr

/-- Canary: a safe function `buggy_zero` that returns
`NonZeroUsize { val: 0 }` violates `EnsuresRetLibInv` and refutes
`CrateTheorem`. -/
theorem canary_buggy_zero_rejected (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := buggyZeroBody }]
    ¬ CrateTheorem {
      adts := [nonZeroAdtDecl 0]
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨0⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
    } := by
  intro bodies hCrate
  have hRetInv := (crateTheorem_single_fnVerified rfl hCrate).2.1.2
  let s0 : MirState := singleArgUsizeInitState
  have hargs : argsMatchInv [nonZeroAdtDecl 0] defaultAdtInv 2 s0 [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [nonZeroAdtDecl 0] bodies buggyZeroBody s0 :=
    mkInitEntryState hargs
  have hexec :
      ExecNormal [nonZeroAdtDecl 0] bodies buggyZeroBody s0
        (fun r => r.value = .adt 0 (.usize 0)) :=
    .step rfl (.normal rfl rfl)
  have hpre :
      CapturedFn.effectivePre [nonZeroAdtDecl 0] bodies nonZeroAdtInv
        { name := fnName, bodyId := ⟨0⟩ } s0
        [TCBItem.rustcLowering fnName ⟨0⟩] :=
    ⟨hinit,
     ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩,
     True.intro⟩
  cases hRetInv s0 ⟨hpre, hpre⟩ with
  | intro hdef hval =>
    cases execNormal_reaches hexec with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        have hpfx :
            (MirSem [nonZeroAdtDecl 0] bodies buggyZeroBody s0).val hdef
              (.terminated [] (.normal v)) :=
          ⟨hinit, n, hv.1⟩
        have hinv := (hval _ hpfx).1 [] v rfl
        have hv_eq : v.value = .adt 0 (.usize 0) := hv.2
        rw [hv_eq] at hinv
        exact hinv.2.1 rfl


/-!
## 6. Baseline Positive and Negative Rust Adequacy Canaries
-/

/-- Pure infinite loop MIR body (`bb0: { goto -> bb0; }`). -/
def loopBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 1
  blocks := [{ stmts := [], terminator := .goto ⟨0⟩ }]

theorem loopBody_reaches_running {bodies : List BodyDecl} (n : Nat) :
    ∀ (s : MirState) (tr : List Empty) (out : PrefixOutcome MirState MirReturn),
      s.block = 0 → s.stmtIdx = 0 → s.curBody = none →
      ReachesPrefix (MirStep [] bodies) loopBody n s tr out →
      ∃ s', out = .running s' := by
  induction n with
  | zero =>
    intro s _ out _ _ _ hreach
    cases hreach with
    | zero => exact ⟨s, rfl⟩
  | succ k ih =>
    intro s tr out hb hs hc hreach
    have hstep0 :
        (evalMirStep [] bodies loopBody s).toStepResult (Obs := Empty) =
          StepResult.silent { s with block := 0, stmtIdx := 0 } := by
      cases s with
      | mk locals localGens block stmtIdx tySizes curBody stack frameId nextFrameId adtPad ubChecks =>
        dsimp at hb hs hc
        subst hb hs hc
        rfl
    cases hreach with
    | step _ _ _ obs _ _ _ _ => nomatch obs
    | choice _ _ s' branches _ _ h1 hbr h2 =>
      have h1' :
          StepResult.choice branches =
            (evalMirStep [] bodies loopBody s).toStepResult := h1
      rw [hstep0] at h1'
      injection h1' with hbr_eq
      subst hbr_eq
      subst hbr
      exact ih { s with block := 0, stmtIdx := 0 } tr out rfl rfl hc h2
    | emptyChoice _ _ branches h1 hemp =>
      have h1' :
          StepResult.choice branches =
            (evalMirStep [] bodies loopBody s).toStepResult := h1
      rw [hstep0] at h1'
      injection h1' with hbr_eq
      subst hbr_eq
      exact False.elim (hemp ⟨{ s with block := 0, stmtIdx := 0 }, rfl⟩)
    | terminated _ _ _ h1 =>
      have h1' : _ = (evalMirStep [] bodies loopBody s).toStepResult := h1
      rw [hstep0] at h1'
      cases h1'
    | failed _ _ h1 =>
      have h1' : _ = (evalMirStep [] bodies loopBody s).toStepResult := h1
      rw [hstep0] at h1'
      cases h1'
    | noStep _ _ hnostep =>
      exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- Positive canary: a pure infinite loop (`loop {}`) is well formed. -/
theorem canary_safe_infinite_loop :
    MirSem [] [] loopBody ≤ wellFormed (MirLang [] []) := by
  refine (eventualBehaviorOf_le_wellFormed_iff (M := MirMachine [] [])).mpr ?_
  intro init steps tr out hinit hreach
  cases loopBody_reaches_running steps init tr out
    hinit.1 hinit.2.1 hinit.2.2.1 hreach with
  | intro s' hout =>
    rw [hout]
    exact True.intro

/-- MIR body that returns immediately without initializing `_0`. -/
def uninitReturnBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .return_ }]

/-- Negative canary: returning an uninitialized `_0` fails at step `1`. -/
theorem canary_uninit_return_violates_wellFormed :
    ¬ (MirSem [] [] uninitReturnBody ≤ wellFormed (MirLang [] [])) := by
  intro hWF
  let s0 : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hinit : initMirState [] [] uninitReturnBody s0 :=
    mkInitEntryState (fun _ _ _ => rfl)
  have hfail :
      ReachesPrefix (MirStep [] []) uninitReturnBody 1 s0 []
        PrefixOutcome.failed :=
    ReachesPrefix.failed 0 s0 rfl
  exact (eventualBehaviorOf_le_wellFormed_iff (M := MirMachine [] [])).mp
    hWF s0 1 [] .failed hinit hfail

/-- MIR body for `pub fn id(x: usize) -> usize { 0 }`. -/
def wrongReturnZeroBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign (locPlace 0) (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Negative canary: returning constant `0` instead of `_1` violates
`EnsuresEqArg 1` when `_1 = MirVal.usize 1`. -/
theorem canary_wrong_id_violates_ensures :
    ¬ (MirSem [] [] wrongReturnZeroBody ≤ EnsuresEqArg 1 [] []) := by
  intro hEns
  let s0 : MirState := singleArgNonZeroUsizeInitState
  have hargs : argsMatchInv [] defaultAdtInv 2 s0 [.usize] :=
    ⟨⟨MirVal.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] [] wrongReturnZeroBody s0 :=
    mkInitEntryState hargs
  have hexec :
      ExecNormal [] [] wrongReturnZeroBody s0 (fun r => r.value = .usize 0) :=
    .step rfl (.normal rfl rfl)
  cases hEns s0 True.intro with
  | intro hdef hval =>
    cases execNormal_reaches hexec with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        have hpfx :
            (MirSem [] [] wrongReturnZeroBody s0).val hdef
              (.terminated [] (.normal v)) :=
          ⟨hinit, n, hv.1⟩
        have hpost := hval _ hpfx [] v rfl
        have hv_eq : v.value = .usize 0 := hv.2
        rw [hv_eq] at hpost
        have h1 : s0.locals 1 = some (MirVal.usize 1) := rfl
        rw [h1] at hpost
        injection hpost with hval'
        injection hval' with hnum
        cases hnum

/-!
## 7. Reference, Frame-ID, Type-Substitution, and ADT Canaries
-/

/-- Returning a reference to a root frame-local variable `_2` (`< localCount`)
is rejected at `Terminator.return_` by `MirVal.returnRefsOk`. -/
def rootLocalEscapeBody : MirBody where
  localCount := 3
  argTys := [.usize]
  retTy := .ref .usize
  blocks := [{
    stmts := [
      .assign (locPlace 2) (.use (.copy (locPlace 1))),
      .assign (locPlace 0) (.ref (locPlace 2))
    ]
    terminator := .return_
  }]

theorem holdout_A5_part1_root_local_escape_fails :
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.usize 42) else none
      block := 0
      stmtIdx := 0
    }
    ∃ s1 s2,
      evalMirStep [] [] rootLocalEscapeBody s0 = .silent s1 ∧
      evalMirStep [] [] rootLocalEscapeBody s1 = .silent s2 ∧
      evalMirStep [] [] rootLocalEscapeBody s2 = .failed :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- Root reference-forwarding body `pub fn id_ref(r: &usize) -> &usize { r }`
whose caller referent resides at slot `2 = body.localCount`. -/
def idRefBody : MirBody where
  localCount := 2
  argTys := [.ref .usize]
  retTy := .ref .usize
  blocks := [{
    stmts := [.assign (locPlace 0) (.use (.copy (locPlace 1)))]
    terminator := .return_
  }]

def idRefCallerState : MirState where
  locals := fun
    | 1 => some (.ref 0 0 ⟨2⟩)
    | 2 => some (.usize 42)
    | _ => none
  block := 0
  stmtIdx := 0

/-- Positive canary: `id_ref` has a non-vacuous entry state with a caller-owned
referent and returns the reference. -/
theorem holdout_A5_part1_id_ref_nonvacuous_and_succeeds :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := idRefBody }]
    let fn : CapturedFn := { name := "id_ref", bodyId := ⟨0⟩ }
    fn.effectivePre [] bodies defaultAdtInv idRefCallerState [] ∧
    ∃ s1,
      evalMirStep [] bodies idRefBody idRefCallerState = .silent s1 ∧
      evalMirStep [] bodies idRefBody s1 =
        .terminated (.normal ⟨.ref 0 0 ⟨2⟩, s1⟩) := by
  intro bodies fn
  have hrest : ∀ j, 2 ≤ j → j < 2 → idRefCallerState.locals j = none :=
    fun _ hge hlt => False.elim (Nat.not_le_of_gt hlt hge)
  have hargs : argsMatchInv [] defaultAdtInv 2 idRefCallerState [.ref .usize] :=
    ⟨⟨.ref 0 0 ⟨2⟩, rfl, rfl, Nat.le_refl 2, True.intro⟩, hrest⟩
  exact ⟨⟨mkInitEntryState hargs, hargs, True.intro⟩, _, rfl, rfl⟩

/-- `Stmt.storageLive` increments `localGens`, invalidating stale references to
a reborn local even without an intervening `Stmt.storageDead`. -/
def useAfterStorageLiveRebirthBody : MirBody where
  localCount := 4
  argTys := [.usize]
  retTy := .usize
  blocks := [{
    stmts := [
      .assign (locPlace 2) (.use (.copy (locPlace 1))),
      .assign (locPlace 3) (.ref (locPlace 2)),
      .storageLive ⟨2⟩,
      .assign (locPlace 2) (.use (.constVal (.usize 77))),
      .assign (locPlace 0) (.use (.copy (derefPlace 3)))
    ]
    terminator := .return_
  }]

theorem holdout_A5_part1_storageLive_rebirth_fails :
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.usize 42) else none
      block := 0
      stmtIdx := 0
    }
    ∃ s1 s2 s3 s4,
      evalMirStep [] [] useAfterStorageLiveRebirthBody s0 = .silent s1 ∧
      evalMirStep [] [] useAfterStorageLiveRebirthBody s1 = .silent s2 ∧
      evalMirStep [] [] useAfterStorageLiveRebirthBody s2 = .silent s3 ∧
      evalMirStep [] [] useAfterStorageLiveRebirthBody s3 = .silent s4 ∧
      evalMirStep [] [] useAfterStorageLiveRebirthBody s4 = .failed :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩

/-- Reborrowing a dead reference fails at `Rvalue.ref (derefPlace _)`, and a
reference into a frame newer than the root (`frameId 1`) does not survive a
root return. -/
def reborrowDeadLocalBody : MirBody where
  localCount := 4
  argTys := [.usize]
  retTy := .usize
  blocks := [{
    stmts := [
      .assign (locPlace 2) (.use (.copy (locPlace 1))),
      .assign (locPlace 3) (.ref (locPlace 2)),
      .storageDead ⟨2⟩,
      .assign (locPlace 0) (.ref (derefPlace 3))
    ]
    terminator := .return_
  }]

theorem fc2_5_reborrow_dead_local_fails_and_dangling_depth_escapes :
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.usize 42) else none
      block := 0
      stmtIdx := 0
    }
    (∃ s1 s2 s3,
      evalMirStep [] [] reborrowDeadLocalBody s0 = .silent s1 ∧
      evalMirStep [] [] reborrowDeadLocalBody s1 = .silent s2 ∧
      evalMirStep [] [] reborrowDeadLocalBody s2 = .silent s3 ∧
      evalMirStep [] [] reborrowDeadLocalBody s3 = .failed) ∧
    (MirVal.ref 1 0 ⟨99⟩).returnRefsOk s0 2 = false :=
  ⟨⟨_, _, _, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- Cross-frame reference forwarding: the caller borrows its `_1` and passes the
reference to a callee, which resolves it against the caller frame and
transmutes the referent. The callee is instantiated at `[usize, usize]`. -/
def transmuteViaRefBody : MirBody where
  localCount := 3
  argTys := [.ref (.param 0)]
  retTy := .param 1
  blocks := [
    { stmts := [.assign (locPlace 2) (.ref (derefPlace 1))]
      terminator :=
        .callTransmuteCopy (locPlace 0) (.param 0) (.param 1)
          (.copy (locPlace 2)) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

def outerViaRefTransmuteBody (calleeId : BodyId := ⟨0⟩) : MirBody where
  localCount := 3
  argTys := [.usize]
  retTy := .usize
  blocks := [
    { stmts := [.assign (locPlace 2) (.ref (locPlace 1))]
      terminator :=
        .call1 (locPlace 0) calleeId (.move (locPlace 2)) ⟨1⟩
          [.usize, .usize] },
    { stmts := []
      terminator := .return_ }
  ]

theorem holdout_A6_part1_cross_frame_ref_1_to_1_succeeds :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := transmuteViaRefBody }]
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.usize 42) else none
      block := 0
      stmtIdx := 0
    }
    ExecNormal [] bodies (outerViaRefTransmuteBody ⟨0⟩) s0
      (fun r => r.value = .usize 42) := by
  intro bodies s0
  repeat (first | exact ExecNormal.normal rfl rfl | refine ExecNormal.step rfl ?_)

/-- Canary: fresh monotonic frame IDs ensure that a second `.call1` activation
receives `frameId = 2` (rather than reusing `frameId = 1` from a returned
sibling activation), so a stale reference targeting `frameId = 1` fails to
resolve inside the second callee. -/
def noopCalleeBody : MirBody where
  localCount := 2
  argTys := [.usize]
  retTy := .usize
  blocks := [{
    stmts := [.assign (locPlace 0) (.use (.copy (locPlace 1)))]
    terminator := .return_
  }]

def derefArgCalleeBody : MirBody where
  localCount := 3
  argTys := [.ref .usize]
  retTy := .usize
  blocks := [{
    stmts := [
      .assign (locPlace 2) (.use (.constVal (.usize 99))),
      .assign (locPlace 0) (.use (.copy (derefPlace 1)))
    ]
    terminator := .return_
  }]

def twoSiblingCallsBody : MirBody where
  localCount := 3
  argTys := [.ref .usize]
  retTy := .usize
  blocks := [
    { stmts := []
      terminator :=
        .call1 (locPlace 2) ⟨0⟩ (.constVal (.usize 7)) ⟨1⟩ },
    { stmts := []
      terminator :=
        .call1 (locPlace 0) ⟨1⟩ (.copy (locPlace 1)) ⟨2⟩ },
    { stmts := []
      terminator := .return_ }
  ]

theorem canary_sibling_call_frame_id_isolation :
    let bodies : List BodyDecl := [
      { id := ⟨0⟩, body := noopCalleeBody },
      { id := ⟨1⟩, body := derefArgCalleeBody }
    ]
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.ref 1 0 ⟨2⟩) else none
      block := 0
      stmtIdx := 0
    }
    ∃ s1 s2 s3 s4 s5,
      evalMirStep [] bodies twoSiblingCallsBody s0 = .silent s1 ∧
      s1.frameId = 1 ∧
      evalMirStep [] bodies twoSiblingCallsBody s1 = .silent s2 ∧
      evalMirStep [] bodies twoSiblingCallsBody s2 = .silent s3 ∧
      s3.frameId = 0 ∧ s3.nextFrameId = 2 ∧
      evalMirStep [] bodies twoSiblingCallsBody s3 = .silent s4 ∧
      s4.frameId = 2 ∧
      evalMirStep [] bodies twoSiblingCallsBody s4 = .silent s5 ∧
      evalMirStep [] bodies twoSiblingCallsBody s5 = .failed :=
  ⟨_, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary: `evalTyByteSize` and `MirTy.wfInAdts` validate reference pointee
types, rejecting `.ref (.adt 99)` when ADT `99` is undeclared while accepting
`.ref .usize`. -/
theorem canary_ref_undeclared_adt_rejected_by_wf :
    MirTy.wfInAdts [] (.ref (.adt 99)) = false ∧
    evalTyByteSize [] (fun _ => 8) (.ref (.adt 99)) = none ∧
    MirTy.wfInAdts [] (.ref .usize) = true ∧
    evalTyByteSize [] (fun _ => 8) (.ref .usize) = some 8 :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Canary:
1. `MirVal.returnRefsOk` looks through nested struct payloads and rejects a
   reference into the root's own locals,
2. it rejects a reference that does not resolve (dangling), and
3. `argsMatchInv` requires entry references to point at caller-owned referents
   (`localCount ≤ index`), so a caller reference cannot alias the callee's own
   locals. -/
theorem canary_deep_escape_dangling_and_entry_ref_guard :
    let sDead : MirState := {
      locals := fun _ => none
      block := 0
      stmtIdx := 0
    }
    let sCallerAlias : MirState := {
      locals := fun
        | 1 => some (.ref 0 0 ⟨1⟩)
        | _ => none
      block := 0
      stmtIdx := 0
    }
    (MirVal.adt 0 (.adt 1 (.ref 0 0 ⟨1⟩))).returnRefsOk sDead 2 = false ∧
    (MirVal.adt 0 (.ref 0 0 ⟨5⟩)).returnRefsOk sDead 2 = false ∧
    ¬ argsMatchInv [] defaultAdtInv 2 sCallerAlias [.ref .usize] := by
  refine ⟨rfl, rfl, ?_⟩
  intro ⟨⟨v, hv1, hinv⟩, _⟩
  injection hv1 with hv
  subst hv
  exact Nat.not_succ_le_self 1 hinv.2.1

/-- Canary: `transmute_copy` looks through nested struct payloads, accepting a
destination of nested public wrappers and rejecting a public wrapper around a
struct with a private field (`Wrapper<NonZeroUsize>`). -/
theorem canary_nested_adt_transmute_copy :
    let privInner : AdtDecl := {
      id := 0
      fields := [{ ty := .usize, access := .priv }]
    }
    let pubOuterOfPriv : AdtDecl := {
      id := 1
      fields := [{ ty := .adt 0, access := .pubSafe }]
    }
    let pubInner : AdtDecl := {
      id := 2
      fields := [{ ty := .usize, access := .pubSafe }]
    }
    let pubOuterOfPub : AdtDecl := {
      id := 3
      fields := [{ ty := .adt 2, access := .pubSafe }]
    }
    let adts := [privInner, pubOuterOfPriv, pubInner, pubOuterOfPub]
    let s : MirState := {
      locals := fun i => if i == 1 then some (.usize 42) else none
      block := 0
      stmtIdx := 0
    }
    evalTransmuteCopy adts s .usize (.adt 1) (.ref 0 0 ⟨1⟩) = none ∧
    evalTransmuteCopy adts s .usize (.adt 3) (.ref 0 0 ⟨1⟩) =
      some (.adt 3 (.adt 2 (.usize 42))) :=
  ⟨rfl, rfl⟩

/-- Canary: `transmute_copy` from a single-field struct to `usize` succeeds,
while transmuting `usize` into the private-field `NonZeroUsize` is blocked. -/
theorem fc2_7_transmute_from_adt_to_usize_and_priv_adt_blocked :
    let s : MirState := {
      locals := fun
        | 1 => some (.adt 0 (.usize 42))
        | 2 => some (.usize 0)
        | _ => none
      block := 0
      stmtIdx := 0
    }
    evalTransmuteCopy [nonZeroAdtDecl 0] s (.adt 0) .usize (.ref 0 0 ⟨1⟩) =
      some (.usize 42) ∧
    evalTransmuteCopy [nonZeroAdtDecl 0] s .usize (.adt 0) (.ref 0 0 ⟨2⟩) =
      none :=
  ⟨rfl, rfl⟩

/-- Canary:
1. `RefWrap` (`fields := [{ ty := .ref .usize, access := .pubSafe }]`) has a
   valid value when its inner reference resolves to a live `.usize`,
2. an ill-typed struct value missing its second field has no transmutation bit
   pattern, and
3. returning an outer reference whose pointee reference was killed by
   `Stmt.storageDead` fails at `Terminator.return_`. -/
def killTargetOfNestedRefBody : MirBody where
  localCount := 3
  argTys := [.ref (.ref .usize), .usize]
  retTy := .ref (.ref .usize)
  blocks := [{
    stmts := [
      .storageDead ⟨2⟩,
      .assign (locPlace 0) (.use (.copy (locPlace 1)))
    ]
    terminator := .return_
  }]

theorem canary_ref_adt_multi_field_and_nested_ref_return :
    let refWrapDecl : AdtDecl := {
      id := 0
      fields := [{ ty := .ref .usize, access := .pubSafe }]
    }
    let twoFieldDecl : AdtDecl := {
      id := 1
      fields := [
        { ty := .usize, access := .pubSafe },
        { ty := .bool, access := .pubSafe }
      ]
    }
    let sRefWrap : MirState := {
      locals := fun i => if i == 2 then some (.usize 42) else none
      block := 0
      stmtIdx := 0
    }
    let sNestedKill : MirState := {
      locals := fun
        | 1 => some (.ref 0 0 ⟨3⟩)
        | 2 => some (.usize 42)
        | 3 => some (.ref 0 0 ⟨2⟩)
        | _ => none
      block := 0
      stmtIdx := 0
    }
    (MirVal.adt 0 (.ref 0 0 ⟨2⟩)).valid
      [refWrapDecl] defaultAdtInv sRefWrap 0 (.adt 0) ∧
    extractTransmuteBits [twoFieldDecl] (.adt 1 (.usize 42)) = none ∧
    (∃ s1 s2,
      evalMirStep [] [] killTargetOfNestedRefBody sNestedKill = .silent s1 ∧
      evalMirStep [] [] killTargetOfNestedRefBody s1 = .silent s2 ∧
      evalMirStep [] [] killTargetOfNestedRefBody s2 = .failed) :=
  ⟨⟨rfl, True.intro, rfl, Nat.zero_le 2, True.intro⟩, rfl,
   ⟨_, _, rfl, rfl, rfl⟩⟩

/-- Single-field public `bool` struct and an invariant that rejects `false`. -/
def pubBoolAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .bool, access := .pubSafe }]

def restrictedPubBoolInv : AdtInv
  | 0, .usize _ => True
  | 0, .bool b => b = true
  | _, _ => True

/-- Canary: an invariant on a struct that safe code can build must accept every
valid payload; rejecting `false` is inadmissible. -/
theorem holdout_A5_part2_pub_bool_restricted_inv_refuted :
    ¬ AdmissibleAdtInv [pubBoolAdtDecl] restrictedPubBoolInv := by
  intro hAdm
  have hfalse : restrictedPubBoolInv 0 (.bool false) :=
    hAdm.2 pubBoolAdtDecl (.head _) rfl (constEntryState (fun _ => 8))
      (.bool false) True.intro
  cases hfalse

/-- A constant body with an argument fails `.evalConst` because
`evalMirStmt` requires `cBody.argTys.isEmpty`. -/
def branchingArgConstBody : MirBody where
  localCount := 2
  argTys := [.bool]
  retTy := .unit
  blocks := [
    { stmts := []
      terminator := .switchInt (.copy (locPlace 1)) ⟨0⟩ ⟨1⟩ },
    { stmts := [.assign (locPlace 0) (.use (.constVal .unit))]
      terminator := .return_ }
  ]

def evalBranchingArgConstBody : MirBody where
  localCount := 2
  argTys := []
  retTy := .unit
  blocks := [{
    stmts := [.evalConst (locPlace 0) ⟨0⟩ []]
    terminator := .return_
  }]

theorem holdout_B3_part1_branching_arg_const_rejected :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := branchingArgConstBody }]
    evalMirStep [] bodies evalBranchingArgConstBody
      (constEntryState (fun _ => 8)) = .failed :=
  rfl

/-!
## 8. Candidate 003 and Three-Stage Pipeline Canaries
-/

/-! ### C-1: references inside structs, and empty domains -/

/-- `pub struct Holder { pub r: &'static usize }`. -/
def holderAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .ref .usize, access := .pubSafe }]

/-- `pub fn bad(h: Holder) -> usize { unsafe { unreachable_unchecked() } }`. -/
def holderUnreachableBody : MirBody where
  argTys := [.adt 0]
  retTy := .usize
  localCount := 2
  blocks := [{ stmts := [], terminator := .unreachable }]

/-- Canary (C-1): a struct whose field is a reference is well formed, so the
size model no longer empties the domain of functions that take it. -/
theorem canary_c1_holder_wf :
    MirTy.wfInAdts [holderAdtDecl] (.adt 0) = true ∧
    evalTyByteSize [holderAdtDecl] (fun _ => 0) (.adt 0) = some 8 :=
  ⟨rfl, rfl⟩

/-- Entry state for `bad`: `_1 = Holder { r: &_2 }` with caller referent
`_2 = 0`. -/
def holderInitState : MirState where
  locals := fun i =>
    if i == 1 then some (.adt 0 (.ref 0 0 ⟨2⟩))
    else if i == 2 then some (.usize 0)
    else none
  block := 0
  stmtIdx := 0

/-- Canary (C-1 exploit `x1-dead-domain`): the crate whose only function takes
a `Holder` and executes `unreachable` is rejected. -/
theorem canary_c1_holder_unreachable_rejected (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := holderUnreachableBody }]
    ¬ CrateTheorem {
      adts := [holderAdtDecl]
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨0⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
    } := by
  intro bodies
  have hargs :
      argsMatchInv [holderAdtDecl] defaultAdtInv 2 holderInitState [.adt 0] :=
    ⟨⟨.adt 0 (.ref 0 0 ⟨2⟩), rfl, rfl, True.intro, rfl, Nat.le_refl 2,
       True.intro⟩,
     fun _ hge hlt => False.elim (Nat.not_le_of_gt hlt hge)⟩
  have hinit :
      initMirState [holderAdtDecl] bodies holderUnreachableBody
        holderInitState :=
    mkInitEntryState hargs
  exact crateTheorem_single_rejects_of_fail
    (bodies := bodies) (fn := { name := fnName, bodyId := ⟨0⟩ })
    holderInitState ⟨hinit, hargs, True.intro⟩ (.fail rfl)

/-! ### F1: an inline constant the model cannot evaluate -/

/-- `impl Make for () { const ONE: NonZeroUsize =
{ let x: usize = 1; unsafe { core::mem::transmute_copy(&x) } }; }`. `rustc`
evaluates this constant; the model refuses to transmute into a struct with a
private field. -/
def oneConstBody : MirBody where
  argTys := []
  retTy := .adt 0
  localCount := 3
  blocks := [
    { stmts := [
        .storageLive ⟨1⟩,
        .assign (locPlace 1) (.use (.constVal (.usize 1))),
        .storageLive ⟨2⟩,
        .assign (locPlace 2) (.ref (locPlace 1))
      ]
      terminator :=
        .callTransmuteCopy (locPlace 0) .usize (.adt 0)
          (.move (locPlace 2)) ⟨1⟩ },
    { stmts := [.storageDead ⟨2⟩, .storageDead ⟨1⟩]
      terminator := .return_ }
  ]

/-- `pub fn boom() -> usize { let _one = const { ... };
unsafe { core::hint::unreachable_unchecked() } }`. -/
def boomBody (constId : BodyId := ⟨0⟩) : MirBody where
  argTys := []
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [
        .storageLive ⟨1⟩,
        .evalConst (locPlace 1) constId [],
        .storageDead ⟨1⟩
      ]
      terminator := .unreachable }
  ]

/-- Canary (F1 exploit `/tmp/fc002/a`): a function whose `.evalConst` constant
the model cannot evaluate steps to `.failed` at `.evalConst`, and the crate is
rejected rather than vacuously accepted. -/
theorem canary_f1_unevaluable_const_rejected (fnName : String) :
    let bodies : List BodyDecl := [
      { id := ⟨0⟩, body := oneConstBody },
      { id := ⟨1⟩, body := (boomBody ⟨0⟩) }
    ]
    ¬ CrateTheorem {
      adts := [nonZeroAdtDecl 0]
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨1⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨1⟩]
    } := by
  intro bodies
  let s0 : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hargs : argsMatchInv [nonZeroAdtDecl 0] defaultAdtInv 2 s0 [] :=
    fun _ _ _ => rfl
  have hargsInv : argsMatchInv [nonZeroAdtDecl 0] nonZeroAdtInv 2 s0 [] :=
    fun _ _ _ => rfl
  have hinit : initMirState [nonZeroAdtDecl 0] bodies (boomBody ⟨0⟩) s0 :=
    mkInitEntryState hargs
  exact crateTheorem_single_rejects_of_fail
    (bodies := bodies) (fn := { name := fnName, bodyId := ⟨1⟩ })
    s0 ⟨hinit, hargsInv, True.intro⟩ (.step rfl (.fail rfl))

/-! ### Pass 3: parameterized `.evalConst` must succeed across all `tySizes` -/

/-- A constant that branches on `size_of::<T0>() == 1`: when
`tySizes 0 ≠ 1` it returns `()` normally, and when `tySizes 0 = 1` it executes
`unreachable` (stepping to `.failed`). -/
def branchingFailConstBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 3
  blocks := [
    { stmts := [.storageLive ⟨1⟩, .storageLive ⟨2⟩]
      terminator := .callSizeOf (locPlace 2) (.param 0) ⟨1⟩ },
    { stmts := [
        .assign (locPlace 1)
          (.binaryOp .eq (.move (locPlace 2)) (.constVal (.usize 1)))
      ]
      terminator := .switchInt (.move (locPlace 1)) ⟨2⟩ ⟨3⟩ },
    { stmts := [
        .storageDead ⟨2⟩,
        .assign (locPlace 0) (.use (.constVal .unit)),
        .storageDead ⟨1⟩
      ]
      terminator := .return_ },
    { stmts := []
      terminator := .unreachable }
  ]

/-- Generic function gated on `branchingFailConstBody` via `.evalConst`. -/
def branchingFailConstFnBody (constId : BodyId := ⟨0⟩) : MirBody where
  argTys := [.param 0]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [
        .evalConst (locPlace 2) constId [.param 0],
        .assign (locPlace 0) (.use (.constVal (.usize 0)))
      ]
      terminator := .return_ }
  ]

/-- Negative adequacy canary: a generic function whose `.evalConst` succeeds on
`tySizes 0 = 8` (`≠ 1`) but steps to `.failed` on `tySizes 0 = 1` fails from a
valid entry state and refutes `CrateTheorem`. -/
theorem canary_branching_const_fail_rejects_crate (fnName : String) :
    let bodies : List BodyDecl := [
      { id := ⟨0⟩, body := branchingFailConstBody },
      { id := ⟨1⟩, body := (branchingFailConstFnBody ⟨0⟩) }
    ]
    let s1 : MirState := {
      locals := updateLocal (fun _ => none) 1 (some (.bytes 1 0))
      block := 0
      stmtIdx := 0
      tySizes := fun _ => 1
    }
    ExecNormal [] bodies (branchingFailConstFnBody ⟨0⟩) pmeInitState
      (fun r => r.value = .usize 0) ∧
    ExecFail [] bodies (branchingFailConstFnBody ⟨0⟩) s1 ∧
    ¬ CrateTheorem {
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨1⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨1⟩]
    } := by
  intro bodies s1
  have hsuc8 :
      ExecNormal [] bodies (branchingFailConstFnBody ⟨0⟩) pmeInitState
        (fun r => r.value = .usize 0) :=
    .step rfl (.step rfl (.normal rfl rfl))
  have hfail1 : ExecFail [] bodies (branchingFailConstFnBody ⟨0⟩) s1 :=
    .fail rfl
  refine ⟨hsuc8, hfail1, ?_⟩
  have hargs : argsMatchInv [] defaultAdtInv 3 s1 [.param 0] :=
    ⟨⟨.bytes 1 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies (branchingFailConstFnBody ⟨0⟩) s1 :=
    mkInitEntryState hargs
  exact crateTheorem_single_rejects_of_fail
    (bodies := bodies) (fn := { name := fnName, bodyId := ⟨1⟩ })
    s1 ⟨hinit, hargs, True.intro⟩ hfail1

/-! ### Pass 3 (`P3-M1`): user specifications restricted to `effectivePre` -/

/-- `pub unsafe fn id_nonzero_unchecked(x: usize) -> usize`: branches on
`x == 0` to `unreachable` and returns `x` when `x ≠ 0`. -/
def idNonZeroUncheckedBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign (locPlace 3) (.use (.copy (locPlace 1))),
        .assign (locPlace 2)
          (.binaryOp .eq (.move (locPlace 3)) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move (locPlace 2)) ⟨2⟩ ⟨1⟩ },
    { stmts := [.storageDead ⟨3⟩]
      terminator := .unreachable },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign (locPlace 0) (.use (.copy (locPlace 1))),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

theorem idNonZeroUnchecked_execNormal {bodies : List BodyDecl} (s : MirState)
    (hinit : initMirState [] bodies idNonZeroUncheckedBody s)
    (hsafety : newUncheckedSafetyPre s) :
    ExecNormal [] bodies idNonZeroUncheckedBody s (fun r =>
      s.locals 1 = some r.value ∧
      r.value.valid [] defaultAdtInv r.state 4 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | fieldCons _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        cases n with
        | zero => exact False.elim (hsafety 0 hv1 rfl)
        | succ k =>
          have hL :
              locals0 = updateLocal locals0 1 (some (.usize (k + 1))) := by
            funext i
            cases i with
            | zero => rfl
            | succ m =>
              cases m with
              | zero => exact hv1
              | succ _ => rfl
          rw [hL]
          refine .step rfl (.step rfl (.step rfl (.step rfl (.step rfl ?_))))
          dsimp only [updateLocal, bumpGen]
          exact .step rfl (.step rfl (.step rfl (.normal rfl ⟨rfl, True.intro⟩)))

/-- Positive canary (`P3-M1`): a function with a non-trivial `safetyPre`
(`newUncheckedSafetyPre`, which fails at `x = 0`) and a user specification
`specs := [.ensuresEqArg 1]` satisfies `CrateTheorem` because
`Obligation.wellFormedAndSpecsOn` restricts each specification in `specs` to
`pre`. -/
theorem canary_p3_m1_safetyPre_with_ensuresEqArg_crate (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := idNonZeroUncheckedBody }]
    CrateTheorem {
      bodies := bodies
      functions := [{
        name := fnName
        bodyId := ⟨0⟩
        requires := newUncheckedRequires
        specs := [.ensuresEqArg 1]
      }]
      tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
    } := by
  intro bodies
  let fn : CapturedFn := {
    name := fnName
    bodyId := ⟨0⟩
    requires := newUncheckedRequires
    specs := [.ensuresEqArg 1]
  }
  have hargs :
      argsMatchInv [] defaultAdtInv 4 singleArgNonZeroUsizeInitState [.usize] :=
    ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit :
      initMirState [] bodies idNonZeroUncheckedBody
        singleArgNonZeroUsizeInitState :=
    mkInitEntryState hargs
  have hsafety : newUncheckedSafetyPre singleArgNonZeroUsizeInitState := by
    intro n hn
    injection hn with hv
    injection hv with h1
    subst h1
    exact Nat.succ_ne_zero 0
  have h_ver :
      FnVerifiedAndRetInv [] bodies defaultAdtInv fn
        [TCBItem.rustcLowering fnName ⟨0⟩] :=
    execNormal_fnVerifiedAndRetInv fn
      ⟨singleArgNonZeroUsizeInitState, hinit, hargs, hsafety⟩
      (fun s hpre =>
        (idNonZeroUnchecked_execNormal s hpre.1 hpre.2.2).map
          (fun _ h => h.2))
  exact verify_single_fn_crate_gen fn ⟨True.intro, True.intro⟩
    defaultAdtInv_admissible h_ver
    ⟨⟨nonVacuousOn_and_defined h_ver.1.1 (fun _ _ => True.intro),
      execNormal_spec_on_pre (fun s hpre =>
        (idNonZeroUnchecked_execNormal s hpre.1 hpre.2.2).map
          (fun _ h => h.1))⟩,
     True.intro⟩

/-! ### C-3: the return invariant reads the terminal state -/

/-- Canary (C-3/F6): `EnsuresRetLibInv` evaluates the returned value in the
terminal state carried by the outcome. Here a returned reference to caller
referent `_2` is valid in the terminal state (where `_2` holds a value) but
would be invalid in the entry state (where `_2` is uninitialized), and the
postcondition accepts the outcome. -/
theorem canary_c3_ret_inv_reads_terminal_state :
    let entry : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
    let final : MirState := {
      locals := fun i => if i == 2 then some (.usize 1) else none
      block := 0
      stmtIdx := 0
    }
    let r : MirReturn := ⟨.ref 0 0 ⟨2⟩, final⟩
    (∀ h, (EnsuresRetLibInv [] [] defaultAdtInv idRefBody (fun _ => True) false
      entry).val h (.terminated [] (.normal r))) ∧
    ¬ r.value.valid [] defaultAdtInv entry idRefBody.localCount idRefBody.retTy := by
  intro entry final r
  refine ⟨?_, fun h => h.2.2⟩
  intro _
  refine ⟨?_, fun _ h => by cases h⟩
  intro tr r' hout
  injection hout with _ hterm
  injection hterm with hr
  subst hr
  exact ⟨rfl, Nat.le_refl 2, True.intro⟩

/-! ### C-4: constants carry no references -/

/-- `_0 = const &_1`: a constant reference that would forge provenance to the
root's local `_1`. -/
def constRefBody : MirBody where
  argTys := [.usize]
  retTy := .ref .usize
  localCount := 2
  blocks := [{
    stmts := [.assign (locPlace 0) (.use (.constVal (.ref 0 0 ⟨1⟩)))]
    terminator := .return_
  }]

/-- Canary (C-4): a constant operand is admitted only if it is a
reference-free scalar; a constant reference makes the step undefined
behavior, and constant structs and opaque bytes are rejected too. -/
theorem canary_c4_const_ref_rejected :
    evalMirStep [] [] constRefBody singleArgUsizeInitState = .failed ∧
    (MirVal.ref 0 0 ⟨1⟩).isConstScalar = false ∧
    (MirVal.adt 0 (.usize 1)).isConstScalar = false ∧
    (MirVal.bytes 8 0).isConstScalar = false ∧
    (MirVal.usize 3).isConstScalar = true :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ### C-5: one parameter space -/

/-- A generic identity callee `fn gid<T>(x: T) -> T { x }`. -/
def genericIdBody : MirBody where
  localCount := 2
  argTys := [.param 0]
  retTy := .param 0
  blocks := [{
    stmts := [.assign (locPlace 0) (.use (.copy (locPlace 1)))]
    terminator := .return_
  }]

/-- A caller that calls `gid` without supplying its type argument. -/
def callerMissingTypeArgBody : MirBody where
  localCount := 2
  argTys := [.usize]
  retTy := .usize
  blocks := [
    { stmts := []
      terminator := .call1 (locPlace 0) ⟨0⟩ (.copy (locPlace 1)) ⟨1⟩ [] },
    { stmts := [], terminator := .return_ }
  ]

/-- Canary (C-5/F11): substitution maps a callee parameter to the caller's type
argument, which stays in the caller's parameter space (`.param 1` inside a
reference is not reinterpreted), and a parameter with no type argument makes
substitution, and hence the call, fail. -/
theorem canary_c5_single_parameter_space :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := genericIdBody }]
    MirTy.subst [.ref (.param 1)] (.ref (.param 0)) =
      some (.ref (.ref (.param 1))) ∧
    MirTy.subst [] (.param 0) = none ∧
    evalMirStep [] bodies callerMissingTypeArgBody singleArgUsizeInitState =
      .failed :=
  ⟨rfl, rfl, rfl⟩

/-- A constant that can never succeed: it transmutes a non-reference operand. -/
def checkParam0Size8ConstBody : MirBody where
  localCount := 2
  argTys := []
  retTy := .unit
  blocks := [{
    stmts := [.assign (locPlace 1) (.use (.constVal (.usize 0)))]
    terminator :=
      .callTransmuteCopy (locPlace 0) (.param 0) .usize
        (.copy (locPlace 1)) ⟨0⟩
  }]

def innerPmeBody (constId : BodyId := ⟨0⟩) : MirBody where
  localCount := 3
  argTys := [.param 0]
  retTy := .param 0
  blocks := [{
    stmts := [
      .evalConst (locPlace 2) constId [.param 0],
      .assign (locPlace 0) (.use (.copy (locPlace 1)))
    ]
    terminator := .return_
  }]

/-- `innerPmeBody` instantiated at `[.param 1, .param 0]`. -/
def innerPmeSwappedInst (constId : BodyId := ⟨0⟩) : MirBody where
  localCount := 3
  argTys := [.param 1]
  retTy := .param 1
  blocks := [{
    stmts := [
      .evalConst (locPlace 2) constId [.param 1],
      .assign (locPlace 0) (.use (.copy (locPlace 1)))
    ]
    terminator := .return_
  }]

/-- `checkParam0Size8ConstBody` instantiated at `[.param 1]`. -/
def checkParam1Inst : MirBody where
  localCount := 2
  argTys := []
  retTy := .unit
  blocks := [{
    stmts := [.assign (locPlace 1) (.use (.constVal (.usize 0)))]
    terminator :=
      .callTransmuteCopy (locPlace 0) (.param 1) .usize
        (.copy (locPlace 1)) ⟨0⟩
  }]

def outerSwappedGenericBody (calleeId : BodyId := ⟨1⟩) : MirBody where
  localCount := 2
  argTys := [.param 0]
  retTy := .param 1
  blocks := [
    { stmts := []
      terminator :=
        .call1 (locPlace 0) calleeId (.copy (locPlace 1)) ⟨1⟩
          [.param 1, .param 0] },
    { stmts := []
      terminator := .return_ }
  ]

/-- Canary (ported `holdout_B3_part2`, rephrased for inline `.evalConst`): a
swapped generic call carries the callee's `.evalConst` type arguments into the
caller's parameter space (`.param 0` becomes the caller's `.param 1`), and a
constant that fails there makes the caller step to `.failed`. -/
theorem holdout_B3_part2_swapped_generic_call1_rejected :
    let bodies : List BodyDecl := [
      { id := ⟨0⟩, body := checkParam0Size8ConstBody },
      { id := ⟨1⟩, body := (innerPmeBody ⟨0⟩) }
    ]
    checkParam0Size8ConstBody.subst [.param 1] = some checkParam1Inst ∧
    (innerPmeBody ⟨0⟩).subst [.param 1, .param 0] =
      some (innerPmeSwappedInst ⟨0⟩) ∧
    ExecFail [] bodies (outerSwappedGenericBody ⟨1⟩) pmeInitState :=
  ⟨rfl, rfl, .step rfl (.fail rfl)⟩

/-! ### R-2: unsupported struct shapes are local -/

/-- `struct UnmodeledWrap { f: Unmodeled }` (contains an unmodeled field). -/
def unmodeledFieldAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .unmodeled, access := .pubSafe }]

/-- `struct Node { next: &'static Node }` (a declaration cycle through a
reference). -/
def nodeAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .ref (.adt 0), access := .pubSafe }]

/-- Canary (R-2/F8): an unsupported struct is ill formed, so any function that
mentions it fails closed at entry, but merely declaring it does not block the
crate-level `AdmissibleAdtInv` conjunct. A cyclic declaration is likewise ill
formed rather than looping. -/
theorem canary_r2_unsupported_struct_is_local :
    MirTy.wfInAdts [unmodeledFieldAdtDecl] (.adt 0) = false ∧
    AdmissibleAdtInv [unmodeledFieldAdtDecl] defaultAdtInv ∧
    MirTy.wfInAdts [nodeAdtDecl] (.adt 0) = false :=
  ⟨rfl, ⟨⟨True.intro, True.intro⟩, fun _ _ _ _ _ _ => True.intro⟩, rfl⟩

/-! ### Three-stage pipeline canaries: partial moves, `placeMention`, `assert` -/

/-- Moving field 0 out of `_1` leaves `_1 = some (.adt 0 .uninit)`, so reading
`_1.0` a second time or returning `_1` as a whole struct steps to `.failed`. -/
def useAfterPartialMoveField0Body : MirBody where
  localCount := 3
  argTys := [.adt 0]
  retTy := .usize
  blocks := [{
    stmts := [
      .assign (locPlace 2) (.use (.move (field0Place 1))),
      .assign (locPlace 0) (.use (.copy (field0Place 1)))
    ]
    terminator := .return_
  }]

theorem canary_partial_move_field0_leaves_adt_uninit :
    let s0 : MirState := singleArgAdtNonZeroInitState 0
    ∃ s1,
      evalMirStep [nonZeroAdtDecl 0] [] useAfterPartialMoveField0Body s0 =
        .silent s1 ∧
      s1.locals 1 = some (.adt 0 .uninit) ∧
      evalMirStep [nonZeroAdtDecl 0] [] useAfterPartialMoveField0Body s1 =
        .failed :=
  ⟨_, rfl, rfl, rfl⟩

/-- `Stmt.placeMention` on a bare local succeeds even when the local is
uninitialized, whereas `Stmt.placeMention` on a projected place (`*_1`) fails
when `_1` is uninitialized or dangling. -/
def placeMentionBareAndProjectedBody : MirBody where
  localCount := 3
  argTys := [.ref .usize]
  retTy := .usize
  blocks := [{
    stmts := [
      .placeMention (locPlace 2),
      .placeMention (derefPlace 1)
    ]
    terminator := .return_
  }]

theorem canary_placeMention_validates_projected_place :
    let sDangling : MirState := {
      locals := fun i => if i == 1 then some (.ref 0 0 ⟨2⟩) else none
      block := 0
      stmtIdx := 0
    }
    ∃ s1,
      evalMirStep [] [] placeMentionBareAndProjectedBody sDangling =
        .silent s1 ∧
      evalMirStep [] [] placeMentionBareAndProjectedBody s1 = .failed :=
  ⟨_, rfl, rfl⟩

/-- `Terminator.assert` steps to `target` when `cond` evaluates to
`.bool expected` and unwinds when `cond` evaluates to `.bool (!expected)`. -/
def assertTrueBody : MirBody where
  localCount := 2
  argTys := [.bool]
  retTy := .usize
  blocks := [
    { stmts := []
      terminator := .assert (.copy (locPlace 1)) true ⟨1⟩ },
    { stmts := [.assign (locPlace 0) (.use (.constVal (.usize 1)))]
      terminator := .return_ }
  ]

theorem canary_assert_terminator_branches_or_unwinds :
    let sTrue : MirState := {
      locals := fun i => if i == 1 then some (.bool true) else none
      block := 0
      stmtIdx := 0
    }
    let sFalse : MirState := {
      locals := fun i => if i == 1 then some (.bool false) else none
      block := 0
      stmtIdx := 0
    }
    (∃ s1, evalMirStep [] [] assertTrueBody sTrue = .silent s1 ∧ s1.block = 1) ∧
    evalMirStep [] [] assertTrueBody sFalse = .terminated .unwind :=
  ⟨⟨_, rfl, rfl⟩, rfl⟩

/-! ### Forward-compatible MIR layout, padding, and TCB waiver canaries -/

/-- `#[repr(C)] pub struct PairU32 { pub a: u32, pub b: u32 }` (`size = 8`,
`align = 4`, `offset_of!(PairU32, a) = 0`, `offset_of!(PairU32, b) = 4`). -/
def pairU32AdtDecl : AdtDecl where
  id := 0
  repr := .c
  fields := [
    { ty := .uint 32, access := .pubSafe },
    { ty := .uint 32, access := .pubSafe }
  ]

/-- `#[repr(C)] pub struct PaddedReprC { pub a: u8, pub b: u32 }` (`size = 8`
due to 3 bytes of internal alignment padding between `a` and `b`). -/
def paddedReprCAdtDecl : AdtDecl where
  id := 0
  repr := .c
  fields := [
    { ty := .uint 8, access := .pubSafe },
    { ty := .uint 32, access := .pubSafe }
  ]

/-- Canary: `#[repr(C)]` layout queries (`sizeOf`, `alignOf`, `offsetOf`)
compute exact C layout, padding-free `PairU32` transmutes to `[u8; 8]`, and
padded `PaddedReprC` (`size = 8 > 1 + 4`) is rejected by
`extractTransmuteBits`. -/
theorem canary_repr_c_layout_and_padding_guard :
    let s : MirState := {
      locals := fun i =>
        if i == 1 then some (.adt 0 (.fieldCons (.usize 1) (.usize 2)))
        else none
      block := 0
      stmtIdx := 0
    }
    evalLayoutQuery [pairU32AdtDecl] (fun _ => 8) (.sizeOf (.adt 0)) =
      some 8 ∧
    evalLayoutQuery [pairU32AdtDecl] (fun _ => 8) (.alignOf (.adt 0)) =
      some 4 ∧
    evalLayoutQuery [pairU32AdtDecl] (fun _ => 8) (.offsetOf (.adt 0) 0 0) =
      some 0 ∧
    evalLayoutQuery [pairU32AdtDecl] (fun _ => 8) (.offsetOf (.adt 0) 0 1) =
      some 4 ∧
    evalTransmuteCopy [pairU32AdtDecl] s (.adt 0) (.array (.uint 8) 8)
      (.ref 0 0 ⟨1⟩) = some (.bytes 8 (1 + 2 * (2 ^ 32))) ∧
    evalLayoutQuery [paddedReprCAdtDecl] (fun _ => 8) (.sizeOf (.adt 0)) =
      some 8 ∧
    evalTransmuteCopy [paddedReprCAdtDecl] s (.adt 0) (.array (.uint 8) 8)
      (.ref 0 0 ⟨1⟩) = none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Single-field public wrapper `pub struct Wrap(pub usize)` parameterized by
`repr`. -/
def pubWrapAdtDecl (repr : AdtRepr) : AdtDecl where
  id := 0
  repr := repr
  fields := [{ ty := .usize, access := .pubSafe }]

theorem pubWrapAdtInv_admissible {repr : AdtRepr} :
    AdmissibleAdtInv [pubWrapAdtDecl repr]
      (denoteAdtInv [pubWrapAdtDecl repr]) := by
  refine ⟨⟨True.intro, True.intro⟩, ?_⟩
  intro decl hmem _ _ _ _
  cases hmem with
  | head => exact True.intro
  | tail _ hnil => cases hnil

/-- `#[repr(Rust)] pub struct RustWrap(pub usize)` with unspecified layout
padding `s.adtPad 0`. -/
abbrev reprRustWrapAdtDecl : AdtDecl := pubWrapAdtDecl .rust

/-- Unguarded `unsafe { core::mem::transmute::<RustWrap, usize>(x) }`. -/
def reprRustUnguardedTransmuteBody : MirBody where
  argTys := [.adt 0]
  retTy := .usize
  localCount := 2
  blocks := [{
    stmts := [
      .assign (locPlace 0)
        (.cast (.transmute (.adt 0)) (.move (locPlace 1)) .usize)
    ]
    terminator := .return_
  }]

/-- Const-guarded `const { assert!(size_of::<RustWrap>() == size_of::<usize>()) };
unsafe { core::mem::transmute::<RustWrap, usize>(x) }`. -/
def reprRustGuardedTransmuteBody (constId : BodyId := ⟨0⟩) : MirBody where
  argTys := [.adt 0]
  retTy := .usize
  localCount := 3
  blocks := [{
    stmts := [
      .evalConst (locPlace 2) constId [],
      .assign (locPlace 0)
        (.cast (.transmute (.adt 0)) (.move (locPlace 1)) .usize)
    ]
    terminator := .return_
  }]

/-- Canary:
1. Unguarded `transmute` on a `#[repr(Rust)]` struct steps to `.failed` when the
   compiler inserts padding (`s.adtPad 0 = 4`), refuting `CrateTheorem`.
2. Adding a compile-time size assertion (`const { assert!(size_of::<RustWrap>()
   == size_of::<usize>()) }`) converts the `s.adtPad 0 = 4` execution from UB
   (`.failed`) into `.terminated .compileTimeError`, which is still rejected by
   `CrateTheorem` unless `TCBItem.compileTimeGuard` is recorded in `c.tcb`. -/
theorem canary_repr_rust_transmute_and_compile_time_guard (fnName : String) :
    let sPadded : MirState := {
      locals := updateLocal (fun _ => none) 1 (some (.adt 0 (.usize 7)))
      block := 0
      stmtIdx := 0
      adtPad := fun _ => 4
    }
    let bodiesGuarded : List BodyDecl := [
      { id := ⟨0⟩, body := (sizeEqConstBodyAt (.adt 0) .usize) },
      { id := ⟨1⟩, body := (reprRustGuardedTransmuteBody ⟨0⟩) }
    ]
    evalMirStep [reprRustWrapAdtDecl] [] reprRustUnguardedTransmuteBody
      sPadded = .failed ∧
    ¬ CrateTheorem {
      adts := [reprRustWrapAdtDecl]
      bodies := [{ id := ⟨0⟩, body := reprRustUnguardedTransmuteBody }]
      functions := [{ name := fnName, bodyId := ⟨0⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
    } ∧
    ExecCompileTimeError [reprRustWrapAdtDecl] bodiesGuarded
      (reprRustGuardedTransmuteBody ⟨0⟩) sPadded ∧
    ¬ CrateTheorem {
      adts := [reprRustWrapAdtDecl]
      bodies := bodiesGuarded
      functions := [{ name := fnName, bodyId := ⟨1⟩ }]
      tcb := [TCBItem.rustcLowering fnName ⟨1⟩]
    } := by
  intro sPadded bodiesGuarded
  have hargsU :
      argsMatchInv [reprRustWrapAdtDecl] defaultAdtInv 2 sPadded [.adt 0] :=
    ⟨⟨.adt 0 (.usize 7), rfl, rfl, True.intro, True.intro⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinitU :
      initMirState [reprRustWrapAdtDecl]
        [{ id := ⟨0⟩, body := reprRustUnguardedTransmuteBody }]
        reprRustUnguardedTransmuteBody sPadded :=
    mkInitEntryState hargsU
  have hRejU :
      ¬ CrateTheorem {
        adts := [reprRustWrapAdtDecl]
        bodies := [{ id := ⟨0⟩, body := reprRustUnguardedTransmuteBody }]
        functions := [{ name := fnName, bodyId := ⟨0⟩ }]
        tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
      } :=
    crateTheorem_single_rejects_of_fail
      (adts := [reprRustWrapAdtDecl])
      (bodies := [{ id := ⟨0⟩, body := reprRustUnguardedTransmuteBody }])
      (fn := { name := fnName, bodyId := ⟨0⟩ })
      sPadded ⟨hinitU, hargsU, True.intro⟩ (.fail rfl)
  have hexecCte :
      ExecCompileTimeError [reprRustWrapAdtDecl] bodiesGuarded
        (reprRustGuardedTransmuteBody ⟨0⟩) sPadded :=
    .compileTimeError rfl
  refine ⟨rfl, hRejU, hexecCte, ?_⟩
  intro hCrate
  have hRetInv := (crateTheorem_single_fnVerified rfl hCrate).2.1.2
  have hargsG :
      argsMatchInv [reprRustWrapAdtDecl] defaultAdtInv 3 sPadded [.adt 0] :=
    ⟨⟨.adt 0 (.usize 7), rfl, rfl, True.intro, True.intro⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinitG :
      initMirState [reprRustWrapAdtDecl] bodiesGuarded
        (reprRustGuardedTransmuteBody ⟨0⟩) sPadded :=
    mkInitEntryState hargsG
  have hpreG :
      CapturedFn.effectivePre [reprRustWrapAdtDecl] bodiesGuarded defaultAdtInv
        { name := fnName, bodyId := ⟨1⟩ } sPadded
        [TCBItem.rustcLowering fnName ⟨1⟩] :=
    ⟨hinitG, hargsG, True.intro⟩
  cases hRetInv sPadded ⟨hpreG, hpreG⟩ with
  | intro hdef hval =>
    cases execCompileTimeError_reaches hexecCte with
    | intro n hr =>
      have hpfx :
          (MirSem [reprRustWrapAdtDecl] bodiesGuarded
            (reprRustGuardedTransmuteBody ⟨0⟩) sPadded).val hdef
            (.terminated [] .compileTimeError) :=
        ⟨hinitG, n, hr⟩
      exact (hval _ hpfx).2 [] rfl

/-- `#[repr(transparent)] pub struct TransWrap { pub val: usize }`. -/
abbrev reprTransparentWrapAdtDecl : AdtDecl := pubWrapAdtDecl .transparent

abbrev reprTransparentWrapAdtInv_admissible :=
  @pubWrapAdtInv_admissible .transparent

abbrev reprRustWrapAdtInv_admissible :=
  @pubWrapAdtInv_admissible .rust

/-- Captured `Runtime(PostCleanup)` MIR body for
`pub fn f(x: Wrap) -> usize { unsafe { core::mem::transmute::<Wrap, usize>(x) } }`. -/
def adtTransmuteBody (adtId : Nat := 0) : MirBody where
  argTys := [.adt adtId]
  retTy := .usize
  localCount := 3
  blocks := [{
    stmts := [
      .storageLive ⟨2⟩,
      .assign (locPlace 2) (.use (.move (locPlace 1))),
      .assign (locPlace 0)
        (.cast (.transmute (.adt adtId)) (.move (locPlace 2)) .usize),
      .storageDead ⟨2⟩
    ]
    terminator := .return_
  }]

/-- Captured `Runtime(PostCleanup)` MIR body for
`pub fn f(x: RustWrap) -> usize {
  let () = const { assert!(size_of::<RustWrap>() == size_of::<usize>()) };
  unsafe { core::mem::transmute::<RustWrap, usize>(x) }
}`. -/
def capturedGuardedAdtTransmuteBody (constId : BodyId := ⟨0⟩)
    (adtId : Nat := 0) : MirBody where
  argTys := [.adt adtId]
  retTy := .usize
  localCount := 4
  blocks := [{
    stmts := [
      .storageLive ⟨2⟩,
      .evalConst (locPlace 2) constId [],
      .storageDead ⟨2⟩,
      .storageLive ⟨3⟩,
      .assign (locPlace 3) (.use (.move (locPlace 1))),
      .assign (locPlace 0)
        (.cast (.transmute (.adt adtId)) (.move (locPlace 3)) .usize),
      .storageDead ⟨3⟩
    ]
    terminator := .return_
  }]

theorem adtTransmuteBody_transparent_execNormal {bodies : List BodyDecl}
    (s : MirState)
    (hinit : initMirState [reprTransparentWrapAdtDecl] bodies
      (adtTransmuteBody 0) s) :
    ExecNormal [reprTransparentWrapAdtDecl] bodies (adtTransmuteBody 0) s
      (fun r =>
        r.value.valid [reprTransparentWrapAdtDecl]
          (denoteAdtInv [reprTransparentWrapAdtDecl]) r.state 3 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit | usize _ | bool _ | unit | fieldCons _ _ | bytes _ _ | ref _ _ _ =>
        cases hvty
      | adt vAdtId inner =>
        have hveq : vAdtId = 0 := hvty.1
        subst hveq
        cases inner with
        | uninit | bool _ | unit | adt _ _ | fieldCons _ _ | bytes _ _ | ref _ _ _ =>
          cases hvty.2.2
        | usize n =>
          have hL : locals0 = updateLocal locals0 1 (some (.adt 0 (.usize n))) := by
            funext i
            cases i with
            | zero => rfl
            | succ k =>
              cases k with
              | zero => exact hv1
              | succ _ => rfl
          rw [hL]
          exact .step rfl (.step rfl (.step rfl (.step rfl (.normal rfl True.intro))))

theorem adtTransmuteBody_transparent_verified_of_resolve
    {bodies : List BodyDecl} {tcb : List TCBItem}
    (fn : CapturedFn)
    (hres : lowerBody (fn.resolveBody bodies) = adtTransmuteBody 0)
    (hreq : fn.requires = none)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnVerifiedAndRetInv [reprTransparentWrapAdtDecl] bodies
      (denoteAdtInv [reprTransparentWrapAdtDecl]) fn tcb := by
  have hcount :
      1 + (adtTransmuteBody 0).argTys.length ≤ (adtTransmuteBody 0).localCount :=
    Nat.le_succ_of_le (Nat.le_refl 2)
  have hargs :
      argsMatchInv [reprTransparentWrapAdtDecl] defaultAdtInv 3
        (singleArgAdtNonZeroInitState 0) [.adt 0] :=
    ⟨⟨.adt 0 (.usize 1), rfl, rfl, True.intro, True.intro⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit0 :
      initMirState [reprTransparentWrapAdtDecl] bodies (adtTransmuteBody 0)
        (singleArgAdtNonZeroInitState 0) :=
    mkInitEntryState hargs (hcount := hcount)
  have hreq0 : denoteRequires fn.requires (singleArgAdtNonZeroInitState 0) := by
    rw [hreq]; exact True.intro
  exact execNormal_fnVerifiedAndRetInv_of_lowerBody fn (adtTransmuteBody 0)
    hres rfl hpin ⟨singleArgAdtNonZeroInitState 0, hinit0, hargs, hreq0⟩
    (fun s hinitS _ _ => adtTransmuteBody_transparent_execNormal s hinitS)

theorem adtTransmuteBody_rustPinned_execNormal {bodies : List BodyDecl}
    (s : MirState)
    (hinit : initMirState [reprRustWrapAdtDecl] bodies (adtTransmuteBody 0) s)
    (hpad : s.adtPad = (fun _ => 0)) :
    ExecNormal [reprRustWrapAdtDecl] bodies (adtTransmuteBody 0) s
      (fun r =>
        r.value.valid [reprRustWrapAdtDecl]
          (denoteAdtInv [reprRustWrapAdtDecl]) r.state 3 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    dsimp at hpad
    subst hb hs hc hst hfid hnfid hlg hpad
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit | usize _ | bool _ | unit | fieldCons _ _ | bytes _ _ | ref _ _ _ =>
        cases hvty
      | adt vAdtId inner =>
        have hveq : vAdtId = 0 := hvty.1
        subst hveq
        cases inner with
        | uninit | bool _ | unit | adt _ _ | fieldCons _ _ | bytes _ _ | ref _ _ _ =>
          cases hvty.2.2
        | usize n =>
          have hL : locals0 = updateLocal locals0 1 (some (.adt 0 (.usize n))) := by
            funext i
            cases i with
            | zero => rfl
            | succ k =>
              cases k with
              | zero => exact hv1
              | succ _ => rfl
          rw [hL]
          exact .step rfl (.step rfl (.step rfl (.step rfl (.normal rfl True.intro))))

theorem adtTransmuteBody_rustPinned_verified_of_resolve
    {bodies : List BodyDecl} {tcb : List TCBItem}
    (fn : CapturedFn)
    (hres : fn.resolveBody bodies = adtTransmuteBody 0)
    (hreq : fn.requires = none)
    (hpin : hasPinnedCoupledWaiver fn tcb = true) :
    FnVerifiedAndRetInv [reprRustWrapAdtDecl] bodies
      (denoteAdtInv [reprRustWrapAdtDecl]) fn tcb := by
  have hcount :
      1 + (adtTransmuteBody 0).argTys.length ≤ (adtTransmuteBody 0).localCount :=
    Nat.le_succ_of_le (Nat.le_refl 2)
  have hargs :
      argsMatchInv [reprRustWrapAdtDecl] defaultAdtInv 3
        (singleArgAdtNonZeroInitState 0) [.adt 0] :=
    ⟨⟨.adt 0 (.usize 1), rfl, rfl, True.intro, True.intro⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit0 :
      initMirState [reprRustWrapAdtDecl] bodies (adtTransmuteBody 0)
        (singleArgAdtNonZeroInitState 0) :=
    mkInitEntryState hargs (hcount := hcount)
  have hpre0 :
      fn.effectivePre [reprRustWrapAdtDecl] bodies
        (denoteAdtInv [reprRustWrapAdtDecl])
        (singleArgAdtNonZeroInitState 0) tcb := by
    dsimp [CapturedFn.effectivePre, CapturedFn.safetyPre]
    rw [hres, hpin, hreq]
    exact ⟨hinit0, hargs, rfl, True.intro⟩
  refine execNormal_fnVerifiedAndRetInv fn
    ⟨singleArgAdtNonZeroInitState 0, hpre0⟩ ?_
  intro s hpre
  dsimp [CapturedFn.effectivePre] at hpre
  rw [hres, hpin] at hpre
  rw [hres]
  exact adtTransmuteBody_rustPinned_execNormal s hpre.1 hpre.2.2.1

/-- Overrides `adtPad 0` with `val` while delegating all other ADT indices to
`fallback`. -/
def padAtZero (val : Nat) (fallback : Nat → Nat) (i : Nat) : Nat :=
  if i == 0 then val else fallback i

theorem capturedGuardedAdtTransmuteBody_exec_zero {bodies : List BodyDecl}
    {constId : BodyId}
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt (.adt 0) .usize))
    (locals0 : Nat → Option MirVal) (tySizes0 : Nat → Nat)
    (adtPad0 : Nat → Nat) (ubChecks0 : Bool) (n : Nat) :
    ExecNormal [reprRustWrapAdtDecl] bodies
      (capturedGuardedAdtTransmuteBody constId 0)
      { locals := updateLocal locals0 1 (some (.adt 0 (.usize n)))
        localGens := fun _ => 0
        block := 0
        stmtIdx := 0
        tySizes := tySizes0
        curBody := none
        stack := []
        frameId := 0
        nextFrameId := 1
        adtPad := padAtZero 0 adtPad0
        ubChecks := ubChecks0 }
      (fun r =>
        r.value.valid [reprRustWrapAdtDecl]
          (denoteAdtInv [reprRustWrapAdtDecl]) r.state 4 .usize) := by
  refine .step rfl ?_
  apply ExecNormal.step
  · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
      lookupAt, List.foldr, Option.getD, evalMirStmt,
      capturedGuardedAdtTransmuteBody]
    rw [hconst]
    rfl
  · exact .step rfl (.step rfl (.step rfl (.step rfl
      (.step rfl (.normal rfl True.intro)))))

theorem capturedGuardedAdtTransmuteBody_exec_succ {bodies : List BodyDecl}
    {constId : BodyId}
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt (.adt 0) .usize))
    (locals0 : Nat → Option MirVal) (tySizes0 : Nat → Nat)
    (adtPad0 : Nat → Nat) (ubChecks0 : Bool) (n k : Nat) :
    ExecCompileTimeError [reprRustWrapAdtDecl] bodies
      (capturedGuardedAdtTransmuteBody constId 0)
      { locals := updateLocal locals0 1 (some (.adt 0 (.usize n)))
        localGens := fun _ => 0
        block := 0
        stmtIdx := 0
        tySizes := tySizes0
        curBody := none
        stack := []
        frameId := 0
        nextFrameId := 1
        adtPad := padAtZero (Nat.succ k) adtPad0
        ubChecks := ubChecks0 } := by
  refine .step rfl (.compileTimeError ?_)
  dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
    lookupAt, List.foldr, Option.getD, evalMirStmt,
    capturedGuardedAdtTransmuteBody]
  rw [hconst]
  rfl

theorem capturedGuardedAdtTransmuteBody_rustGuarded_exec
    {bodies : List BodyDecl} {constId : BodyId}
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt (.adt 0) .usize))
    (s : MirState)
    (hinit : initMirState [reprRustWrapAdtDecl] bodies
      (capturedGuardedAdtTransmuteBody constId 0) s) :
    (s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8) →
      ExecNormal [reprRustWrapAdtDecl] bodies
        (capturedGuardedAdtTransmuteBody constId 0) s (fun r =>
          r.value.valid [reprRustWrapAdtDecl]
            (denoteAdtInv [reprRustWrapAdtDecl]) r.state 4 .usize)) ∧
    (ExecNormal [reprRustWrapAdtDecl] bodies
        (capturedGuardedAdtTransmuteBody constId 0) s (fun r =>
          r.value.valid [reprRustWrapAdtDecl]
            (denoteAdtInv [reprRustWrapAdtDecl]) r.state 4 .usize) ∨
     ExecCompileTimeError [reprRustWrapAdtDecl] bodies
        (capturedGuardedAdtTransmuteBody constId 0) s) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit | usize _ | bool _ | unit | fieldCons _ _ | bytes _ _ | ref _ _ _ =>
        cases hvty
      | adt vAdtId inner =>
        have hveq : vAdtId = 0 := hvty.1
        subst hveq
        cases inner with
        | uninit | bool _ | unit | adt _ _ | fieldCons _ _ | bytes _ _ | ref _ _ _ =>
          cases hvty.2.2
        | usize n =>
          have hL : locals0 = updateLocal locals0 1 (some (.adt 0 (.usize n))) := by
            funext i
            cases i with
            | zero => rfl
            | succ k =>
              cases k with
              | zero => exact hv1
              | succ _ => rfl
          have hPad : adtPad0 = padAtZero (adtPad0 0) adtPad0 := by
            funext i
            cases i with
            | zero => rfl
            | succ _ => rfl
          refine ⟨fun h0 => ?_, ?_⟩
          · have hp0 : adtPad0 0 = 0 := congrFun h0.1 0
            rw [hL, hPad, hp0]
            exact capturedGuardedAdtTransmuteBody_exec_zero hconst locals0
              tySizes0 adtPad0 ubChecks0 n
          · rw [hL, hPad]
            cases adtPad0 0 with
            | zero =>
              exact Or.inl (capturedGuardedAdtTransmuteBody_exec_zero hconst
                locals0 tySizes0 adtPad0 ubChecks0 n)
            | succ k =>
              exact Or.inr (capturedGuardedAdtTransmuteBody_exec_succ hconst
                locals0 tySizes0 adtPad0 ubChecks0 n k)

theorem capturedGuardedAdtTransmuteBody_rustGuarded_verified_of_resolve
    {bodies : List BodyDecl} {constId : BodyId} {tcb : List TCBItem}
    (fn : CapturedFn)
    (hres : fn.resolveBody bodies = capturedGuardedAdtTransmuteBody constId 0)
    (hreq : fn.requires = none)
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt (.adt 0) .usize))
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hguard : hasCompileTimeGuardWaiver fn tcb = true) :
    FnVerifiedAndRetInv [reprRustWrapAdtDecl] bodies
      (denoteAdtInv [reprRustWrapAdtDecl]) fn tcb := by
  have hcount :
      1 + (capturedGuardedAdtTransmuteBody constId 0).argTys.length ≤
        (capturedGuardedAdtTransmuteBody constId 0).localCount :=
    Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2))
  have hargs :
      argsMatchInv [reprRustWrapAdtDecl] defaultAdtInv 4
        (singleArgAdtNonZeroInitState 0) [.adt 0] :=
    ⟨⟨.adt 0 (.usize 1), rfl, rfl, True.intro, True.intro⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit0 :
      initMirState [reprRustWrapAdtDecl] bodies
        (capturedGuardedAdtTransmuteBody constId 0)
        (singleArgAdtNonZeroInitState 0) :=
    mkInitEntryState hargs (hcount := hcount)
  have hpre0 :
      fn.effectivePre [reprRustWrapAdtDecl] bodies
        (denoteAdtInv [reprRustWrapAdtDecl])
        (singleArgAdtNonZeroInitState 0) tcb := by
    dsimp [CapturedFn.effectivePre, CapturedFn.safetyPre]
    rw [hres, hpin, hreq]
    exact ⟨hinit0, hargs, True.intro⟩
  refine execNormalOrGuard_fnVerifiedAndRetInv fn hguard
    ⟨singleArgAdtNonZeroInitState 0, hpre0⟩ ?_
  intro s hpre
  dsimp [CapturedFn.effectivePre] at hpre
  rw [hres, hpin] at hpre
  rw [hres]
  exact capturedGuardedAdtTransmuteBody_rustGuarded_exec hconst s hpre.1

/-- `rustc`-inserted UB check (`Operand.runtimeChecks .ubChecks` +
`Terminator.assert ... .ub`) steps to `.failed` (UB) when `s.ubChecks = true`
and the condition fails. -/
def ubCheckAssertBody : MirBody where
  argTys := [.bool]
  retTy := .unit
  localCount := 3
  blocks := [
    { stmts := [
        .assign (locPlace 2) (.use (.runtimeChecks .ubChecks))
      ]
      terminator := .switchInt (.move (locPlace 2)) ⟨2⟩ ⟨1⟩ },
    { stmts := []
      terminator := .assert (.copy (locPlace 1)) true ⟨2⟩ .ub },
    { stmts := [.assign (locPlace 0) (.use (.constVal .unit))]
      terminator := .return_ }
  ]

theorem canary_ub_check_assert_fails_when_ubChecks_enabled :
    let sFail : MirState := {
      locals := updateLocal (fun _ => none) 1 (some (.bool false))
      block := 0
      stmtIdx := 0
      ubChecks := true
    }
    ExecFail [] [] ubCheckAssertBody sFail :=
  .step rfl (.step rfl (.fail rfl))

/-!
## 9. Captured Fixtures (`alloc_passthrough` and `inline_const_transmute`)
-/

/-- `pub fn alloc_passthrough(x: usize) -> usize { let r = &x; *r }`. -/
def allocPassthroughBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 3
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign (locPlace 2) (.ref (locPlace 1)),
        .assign (locPlace 0) (.use (.copy (derefPlace 2))),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

/-- `alloc_passthrough` returns its argument through a local borrow. -/
theorem allocPassthroughBody_execNormal {bodies : List BodyDecl} (s : MirState)
    (hinit : initMirState [] bodies allocPassthroughBody s) :
    ExecNormal [] bodies allocPassthroughBody s (fun r =>
      s.locals 1 = some r.value ∧
      r.value.valid [] defaultAdtInv r.state 3 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | fieldCons _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        have hL : locals0 = updateLocal locals0 1 (some (.usize n)) := by
          funext i
          cases i with
          | zero => rfl
          | succ k =>
            cases k with
            | zero => exact hv1
            | succ _ => rfl
        rw [hL]
        refine ExecNormal.step rfl ?_
        refine ExecNormal.step rfl ?_
        refine ExecNormal.step rfl ?_
        refine ExecNormal.step rfl ?_
        exact ExecNormal.normal rfl ⟨rfl, True.intro⟩

/-- `alloc_passthrough` satisfies `FnVerifiedAndRetInv` for any `fn` whose
lowered body is `allocPassthroughBody` with `fn.requires = none`. -/
theorem allocPassthroughBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn)
    (hres : lowerBody (fn.resolveBody bodies) = allocPassthroughBody)
    (hreq : fn.requires = none)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb := by
  have hargs : argsMatchInv [] defaultAdtInv 3 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies allocPassthroughBody singleArgUsizeInitState :=
    mkInitEntryState hargs
  have hreq0 : denoteRequires fn.requires singleArgUsizeInitState := by
    rw [hreq]; exact True.intro
  exact execNormal_fnVerifiedAndRetInv_of_lowerBody fn allocPassthroughBody hres rfl
    hpin ⟨singleArgUsizeInitState, hinit, hargs, hreq0⟩
    (fun s hinitS _ _ => (allocPassthroughBody_execNormal s hinitS).map (fun _ h => h.2))

/-- `pub fn inline_const_transmute(x: usize) -> usize`:
`let () = const { assert!(size_of::<usize>() == size_of::<usize>()) };
unsafe { core::mem::transmute_copy(&x) }`. -/
def inlineConstTransmuteBody (constId : BodyId := ⟨0⟩) : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .evalConst (locPlace 2) constId [],
        .storageDead ⟨2⟩,
        .storageLive ⟨3⟩,
        .storageLive ⟨4⟩,
        .assign (locPlace 4) (.ref (locPlace 1)),
        .assign (locPlace 3) (.ref (derefPlace 4))
      ]
      terminator :=
        .callTransmuteCopy (locPlace 0) .usize .usize
          (.move (locPlace 3)) ⟨1⟩ },
    { stmts := [.storageDead ⟨4⟩, .storageDead ⟨3⟩]
      terminator := .return_ }
  ]

/-- `inline_const_transmute` returns its argument from every initial state when
`constId` resolves to `sizeEqConstBodyAt .usize .usize`. -/
theorem inlineConstTransmute_execNormal {bodies : List BodyDecl}
    {constId : BodyId}
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt .usize .usize))
    (s : MirState)
    (hinit : initMirState [] bodies (inlineConstTransmuteBody constId) s) :
    ExecNormal [] bodies (inlineConstTransmuteBody constId) s (fun r =>
      r.value.valid [] defaultAdtInv r.state 5 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hb : block0 = 0 := hinit.1
    have hs : stmtIdx0 = 0 := hinit.2.1
    have hc : curBody0 = none := hinit.2.2.1
    have hst : stack0 = [] := hinit.2.2.2.1
    have hfid : frameId0 = 0 := hinit.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hinit.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hinit.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hinit).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | fieldCons _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        have hL : locals0 = updateLocal locals0 1 (some (.usize n)) := by
          funext i
          cases i with
          | zero => rfl
          | succ k =>
            cases k with
            | zero => exact hv1
            | succ _ => rfl
        rw [hL]
        refine .step rfl ?_
        apply ExecNormal.step
        · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith, lookupAt,
            List.foldr, Option.getD, evalMirStmt, inlineConstTransmuteBody]
          rw [hconst]
          rfl
        · refine .step rfl (.step rfl (.step rfl ?_))
          dsimp only [updateLocal, bumpGen]
          repeat (first | exact ExecNormal.normal rfl True.intro |
            refine ExecNormal.step rfl ?_)

/-- `inlineConstTransmuteBody constId` satisfies `FnVerifiedAndRetInv` for any
`fn` whose lowered body is `inlineConstTransmuteBody constId` when `constId`
resolves to `sizeEqConstBodyAt .usize .usize`. -/
theorem inlineConstTransmute_verified_of_resolve {bodies : List BodyDecl}
    {constId : BodyId} {tcb : List TCBItem} (fn : CapturedFn)
    (hres : lowerBody (fn.resolveBody bodies) = inlineConstTransmuteBody constId)
    (hreq : fn.requires = none)
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt .usize .usize))
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb := by
  have hargs : argsMatchInv [] defaultAdtInv 5 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hcount :
      1 + (inlineConstTransmuteBody constId).argTys.length ≤
        (inlineConstTransmuteBody constId).localCount :=
    Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2)))
  have hinit :
      initMirState [] bodies (inlineConstTransmuteBody constId)
        singleArgUsizeInitState :=
    mkInitEntryState hargs (hcount := hcount)
  have hreq0 : denoteRequires fn.requires singleArgUsizeInitState := by
    rw [hreq]; exact True.intro
  exact execNormal_fnVerifiedAndRetInv_of_lowerBody fn
    (inlineConstTransmuteBody constId) hres rfl hpin
    ⟨singleArgUsizeInitState, hinit, hargs, hreq0⟩
    (fun s hinitS _ _ => inlineConstTransmute_execNormal hconst s hinitS)

/-!
## 10. Fuel-Free AST Boolean Equality and Compositional Crate Proof Dispatcher
-/

def listBeq {α : Type} (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => eq x y && listBeq eq xs ys
  | _, _ => false

theorem listEq_of_beq {α : Type} {eq : α → α → Bool}
    (heq : ∀ {x y : α}, eq x y = true → x = y) :
    ∀ {xs ys : List α}, listBeq eq xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp [listBeq] at h
    rw [heq h.1, listEq_of_beq heq h.2]

def optBeq {α : Type} (eq : α → α → Bool) : Option α → Option α → Bool
  | none, none => true
  | some x, some y => eq x y
  | _, _ => false

theorem optEq_of_beq {α : Type} {eq : α → α → Bool}
    (heq : ∀ {x y : α}, eq x y = true → x = y) :
    ∀ {x y : Option α}, optBeq eq x y = true → x = y
  | none, none, _ => rfl
  | some _, some _, h => congrArg some (heq h)

def beqLocalId (a b : LocalId) : Bool := a.index == b.index

theorem eq_of_beqLocalId {a b : LocalId} (h : beqLocalId a b = true) : a = b := by
  cases a; cases b; simp [beqLocalId] at h; subst h; rfl

def beqBlockId (a b : BlockId) : Bool := a.index == b.index

theorem eq_of_beqBlockId {a b : BlockId} (h : beqBlockId a b = true) : a = b := by
  cases a; cases b; simp [beqBlockId] at h; subst h; rfl

def beqBodyId (a b : BodyId) : Bool := a.index == b.index

theorem eq_of_beqBodyId {a b : BodyId} (h : beqBodyId a b = true) : a = b := by
  cases a; cases b; simp [beqBodyId] at h; subst h; rfl

def beqPlaceElem (a b : PlaceElem) : Bool :=
  match a with
  | .deref => match b with | .deref => true | _ => false
  | .field a1 => match b with | .field b1 => a1 == b1 | _ => false
  | _ => false

theorem eq_of_beqPlaceElem {a b : PlaceElem} (h : beqPlaceElem a b = true) :
    a = b := by
  cases a with
  | deref => cases b <;> first | rfl | cases h
  | field a1 =>
    cases b with
    | field b1 => simp [beqPlaceElem] at h; exact congrArg PlaceElem.field h
    | _ => cases h
  | _ => cases h

def beqPlace (a b : Place) : Bool :=
  beqLocalId a.loc b.loc &&
  listBeq beqPlaceElem a.projection b.projection

theorem eq_of_beqPlace {a b : Place} (h : beqPlace a b = true) : a = b := by
  cases a; cases b; simp [beqPlace] at h
  rw [eq_of_beqLocalId h.1, listEq_of_beq eq_of_beqPlaceElem h.2]

def beqFieldAccess : FieldAccess → FieldAccess → Bool
  | .pubSafe, .pubSafe => true
  | .priv, .priv => true
  | _, _ => false

theorem eq_of_beqFieldAccess {a b : FieldAccess}
    (h : beqFieldAccess a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

def beqMirTy : MirTy → MirTy → Bool
  | .usize => fun b => match b with | .usize => true | _ => false
  | .bool => fun b => match b with | .bool => true | _ => false
  | .unit => fun b => match b with | .unit => true | _ => false
  | .adt i => fun b => match b with | .adt j => i == j | _ => false
  | .param i => fun b => match b with | .param j => i == j | _ => false
  | .ref a => fun b => match b with | .ref b1 => beqMirTy a b1 | _ => false
  | _ => fun _ => false

theorem eq_of_beqMirTy : ∀ {a b : MirTy}, beqMirTy a b = true → a = b
  | .usize, b, h => by cases b <;> first | rfl | cases h
  | .bool, b, h => by cases b <;> first | rfl | cases h
  | .unit, b, h => by cases b <;> first | rfl | cases h
  | .adt _, b, h => by
    cases b with
    | adt _ => simp [beqMirTy] at h; exact congrArg MirTy.adt h
    | _ => cases h
  | .param _, b, h => by
    cases b with
    | param _ => simp [beqMirTy] at h; exact congrArg MirTy.param h
    | _ => cases h
  | .ref _, b, h => by
    cases b with
    | ref _ => exact congrArg MirTy.ref (eq_of_beqMirTy h)
    | _ => cases h
  | .isize, _, h | .uint _, _, h | .int _, _, h | .float _, _, h
  | .char, _, h | .str, _, h | .never, _, h | .refMut _, _, h
  | .rawPtr _ _, _, h | .array _ _, _, h | .slice _, _, h
  | .tuple _, _, h | .fnDef _, _, h | .fnPtr, _, h
  | .unmodeled, _, h => by cases h

def beqFieldDecl (a b : FieldDecl) : Bool :=
  beqMirTy a.ty b.ty && beqFieldAccess a.access b.access

theorem eq_of_beqFieldDecl {a b : FieldDecl}
    (h : beqFieldDecl a b = true) : a = b := by
  cases a; cases b; simp [beqFieldDecl] at h
  rw [eq_of_beqMirTy h.1, eq_of_beqFieldAccess h.2]

def beqInvariantSpec (a b : InvariantSpec) : Bool := a.ne == b.ne

theorem eq_of_beqInvariantSpec {a b : InvariantSpec}
    (h : beqInvariantSpec a b = true) : a = b := by
  cases a; cases b; simp [beqInvariantSpec] at h; subst h; rfl

def beqAdtRepr : AdtRepr → AdtRepr → Bool
  | .rust, .rust => true
  | .c, .c => true
  | .transparent, .transparent => true
  | _, _ => false

theorem eq_of_beqAdtRepr {a b : AdtRepr} (h : beqAdtRepr a b = true) :
    a = b := by
  cases a <;> cases b <;> first | rfl | cases h

def beqAdtDecl (a b : AdtDecl) : Bool :=
  a.id == b.id &&
  beqAdtRepr a.repr b.repr &&
  listBeq beqFieldDecl a.fields b.fields &&
  optBeq beqInvariantSpec a.invariant b.invariant

theorem eq_of_beqAdtDecl {a b : AdtDecl} (h : beqAdtDecl a b = true) : a = b := by
  cases a; cases b; simp [beqAdtDecl] at h
  rw [h.1.1.1, eq_of_beqAdtRepr h.1.1.2, listEq_of_beq eq_of_beqFieldDecl h.1.2,
    optEq_of_beq eq_of_beqInvariantSpec h.2]

def beqMirVal : MirVal → MirVal → Bool
  | .uninit, .uninit => true
  | .usize a, .usize b => a == b
  | .bool a, .bool b => a == b
  | .unit, .unit => true
  | .adt i a, .adt j b => i == j && beqMirVal a b
  | .fieldCons a1 a2, .fieldCons b1 b2 => beqMirVal a1 b1 && beqMirVal a2 b2
  | .bytes s1 b1, .bytes s2 b2 => s1 == s2 && b1 == b2
  | .ref d1 g1 l1, .ref d2 g2 l2 => d1 == d2 && g1 == g2 && beqLocalId l1 l2
  | _, _ => false

theorem eq_of_beqMirVal : ∀ {a b : MirVal}, beqMirVal a b = true → a = b
  | .uninit, .uninit, _ => rfl
  | .usize _, .usize _, h => by
    simp [beqMirVal] at h; exact congrArg MirVal.usize h
  | .bool _, .bool _, h => by
    simp [beqMirVal] at h; exact congrArg MirVal.bool h
  | .unit, .unit, _ => rfl
  | .adt _ _, .adt _ _, h => by
    simp [beqMirVal] at h
    rw [h.1, eq_of_beqMirVal h.2]
  | .fieldCons _ _, .fieldCons _ _, h => by
    simp [beqMirVal] at h
    rw [eq_of_beqMirVal h.1, eq_of_beqMirVal h.2]
  | .bytes _ _, .bytes _ _, h => by
    simp [beqMirVal] at h
    rw [h.1, h.2]
  | .ref _ _ _, .ref _ _ _, h => by
    simp [beqMirVal] at h
    rw [h.1.1, h.1.2, eq_of_beqLocalId h.2]

def beqOperand (a b : Operand) : Bool :=
  match a with
  | .copy a1 => match b with | .copy b1 => beqPlace a1 b1 | _ => false
  | .move a1 => match b with | .move b1 => beqPlace a1 b1 | _ => false
  | .constVal a1 => match b with | .constVal b1 => beqMirVal a1 b1 | _ => false
  | _ => false

theorem eq_of_beqOperand {a b : Operand} (h : beqOperand a b = true) : a = b := by
  cases a with
  | copy a1 =>
    cases b with
    | copy b1 => exact congrArg Operand.copy (eq_of_beqPlace h)
    | _ => cases h
  | move a1 =>
    cases b with
    | move b1 => exact congrArg Operand.move (eq_of_beqPlace h)
    | _ => cases h
  | constVal a1 =>
    cases b with
    | constVal b1 => exact congrArg Operand.constVal (eq_of_beqMirVal h)
    | _ => cases h
  | _ => cases h

def beqCastKind : CastKind → CastKind → Bool
  | .transmute s1, .transmute s2 => beqMirTy s1 s2
  | .intToInt, .intToInt => true
  | .subtype, .subtype => true
  | _, _ => false

theorem eq_of_beqCastKind :
    ∀ {a b : CastKind}, beqCastKind a b = true → a = b
  | .transmute _, .transmute _, h =>
    congrArg (fun t => CastKind.transmute t) (eq_of_beqMirTy h)
  | .intToInt, .intToInt, _ => rfl
  | .subtype, .subtype, _ => rfl

def beqBinOp (a b : BinOp) : Bool :=
  match a with
  | .eq => match b with | .eq => true | _ => false
  | _ => false

theorem eq_of_beqBinOp {a b : BinOp} (h : beqBinOp a b = true) : a = b := by
  cases a <;> first | cases h | (cases b <;> first | rfl | cases h)

def beqRvalue (a b : Rvalue) : Bool :=
  match a with
  | .use a1 => match b with | .use b1 => beqOperand a1 b1 | _ => false
  | .cast k1 o1 t1 =>
    match b with
    | .cast k2 o2 t2 =>
      beqCastKind k1 k2 && beqOperand o1 o2 && beqMirTy t1 t2
    | _ => false
  | .binaryOp op1 l1 r1 =>
    match b with
    | .binaryOp op2 l2 r2 =>
      beqBinOp op1 op2 && beqOperand l1 l2 && beqOperand r1 r2
    | _ => false
  | .aggregate i1 a1 =>
    match b with
    | .aggregate i2 a2 => i1 == i2 && beqOperand a1 a2
    | _ => false
  | .aggregateFields ops1 i1 =>
    match b with
    | .aggregateFields ops2 i2 =>
      listBeq beqOperand ops1 ops2 && optBeq (fun x y => x == y) i1 i2
    | _ => false
  | .ref a1 => match b with | .ref b1 => beqPlace a1 b1 | _ => false
  | _ => false

theorem eq_of_beqRvalue {a b : Rvalue} (h : beqRvalue a b = true) : a = b := by
  cases a with
  | use a1 =>
    cases b with
    | use b1 => exact congrArg Rvalue.use (eq_of_beqOperand h)
    | _ => cases h
  | cast k1 o1 t1 =>
    cases b with
    | cast k2 o2 t2 =>
      simp [beqRvalue] at h
      rw [eq_of_beqCastKind h.1.1, eq_of_beqOperand h.1.2, eq_of_beqMirTy h.2]
    | _ => cases h
  | binaryOp op1 l1 r1 =>
    cases b with
    | binaryOp op2 l2 r2 =>
      simp [beqRvalue] at h
      rw [eq_of_beqBinOp h.1.1, eq_of_beqOperand h.1.2, eq_of_beqOperand h.2]
    | _ => cases h
  | aggregate i1 a1 =>
    cases b with
    | aggregate i2 a2 =>
      simp [beqRvalue] at h
      rw [h.1, eq_of_beqOperand h.2]
    | _ => cases h
  | aggregateFields ops1 i1 =>
    cases b with
    | aggregateFields ops2 i2 =>
      simp [beqRvalue] at h
      rw [listEq_of_beq eq_of_beqOperand h.1,
        optEq_of_beq (fun hxy => beq_iff_eq.mp hxy) h.2]
    | _ => cases h
  | ref a1 =>
    cases b with
    | ref b1 => exact congrArg Rvalue.ref (eq_of_beqPlace h)
    | _ => cases h
  | _ => cases h

def beqStmt (a b : Stmt) : Bool :=
  match a with
  | .assign d1 r1 =>
    match b with
    | .assign d2 r2 => beqPlace d1 d2 && beqRvalue r1 r2
    | _ => false
  | .evalConst d1 c1 tys1 =>
    match b with
    | .evalConst d2 c2 tys2 =>
      beqPlace d1 d2 && beqBodyId c1 c2 && listBeq beqMirTy tys1 tys2
    | _ => false
  | .placeMention a1 =>
    match b with | .placeMention b1 => beqPlace a1 b1 | _ => false
  | .storageLive a1 =>
    match b with | .storageLive b1 => beqLocalId a1 b1 | _ => false
  | .storageDead a1 =>
    match b with | .storageDead b1 => beqLocalId a1 b1 | _ => false
  | .constEvalCounter => match b with | .constEvalCounter => true | _ => false
  | .nop => match b with | .nop => true | _ => false
  | _ => false

theorem eq_of_beqStmt {a b : Stmt} (h : beqStmt a b = true) : a = b := by
  cases a with
  | assign d1 r1 =>
    cases b with
    | assign d2 r2 =>
      simp [beqStmt] at h
      rw [eq_of_beqPlace h.1, eq_of_beqRvalue h.2]
    | _ => cases h
  | evalConst d1 c1 tys1 =>
    cases b with
    | evalConst d2 c2 tys2 =>
      simp [beqStmt] at h
      rw [eq_of_beqPlace h.1.1, eq_of_beqBodyId h.1.2,
        listEq_of_beq eq_of_beqMirTy h.2]
    | _ => cases h
  | placeMention a1 =>
    cases b with
    | placeMention b1 => exact congrArg Stmt.placeMention (eq_of_beqPlace h)
    | _ => cases h
  | storageLive a1 =>
    cases b with
    | storageLive b1 => exact congrArg Stmt.storageLive (eq_of_beqLocalId h)
    | _ => cases h
  | storageDead a1 =>
    cases b with
    | storageDead b1 => exact congrArg Stmt.storageDead (eq_of_beqLocalId h)
    | _ => cases h
  | constEvalCounter =>
    cases b with
    | constEvalCounter => rfl
    | _ => cases h
  | nop =>
    cases b with
    | nop => rfl
    | _ => cases h
  | _ => cases h

def beqLayoutQuery : LayoutQuery → LayoutQuery → Bool
  | .sizeOf t1, .sizeOf t2 => beqMirTy t1 t2
  | .alignOf t1, .alignOf t2 => beqMirTy t1 t2
  | .offsetOf t1 v1 f1, .offsetOf t2 v2 f2 =>
    beqMirTy t1 t2 && v1 == v2 && f1 == f2
  | _, _ => false

theorem eq_of_beqLayoutQuery :
    ∀ {a b : LayoutQuery}, beqLayoutQuery a b = true → a = b
  | .sizeOf _, .sizeOf _, h => congrArg LayoutQuery.sizeOf (eq_of_beqMirTy h)
  | .alignOf _, .alignOf _, h => congrArg LayoutQuery.alignOf (eq_of_beqMirTy h)
  | .offsetOf _ _ _, .offsetOf _ _ _, h => by
    simp [beqLayoutQuery] at h
    rw [eq_of_beqMirTy h.1.1, h.1.2, h.2]

def beqAssertFailKind : AssertFailKind → AssertFailKind → Bool
  | .unwind, .unwind => true
  | .ub, .ub => true
  | .abort, .abort => true
  | _, _ => false

theorem eq_of_beqAssertFailKind :
    ∀ {a b : AssertFailKind}, beqAssertFailKind a b = true → a = b
  | .unwind, .unwind, _ => rfl
  | .ub, .ub, _ => rfl
  | .abort, .abort, _ => rfl

def beqTerminator (a b : Terminator) : Bool :=
  match a with
  | .return_ => match b with | .return_ => true | _ => false
  | .goto a1 => match b with | .goto b1 => beqBlockId a1 b1 | _ => false
  | .unreachable => match b with | .unreachable => true | _ => false
  | .panic => match b with | .panic => true | _ => false
  | .assert c1 e1 t1 k1 =>
    match b with
    | .assert c2 e2 t2 k2 =>
      beqOperand c1 c2 && e1 == e2 && beqBlockId t1 t2 &&
      beqAssertFailKind k1 k2
    | _ => false
  | .switchInt d1 f1 t1 =>
    match b with
    | .switchInt d2 f2 t2 =>
      beqOperand d1 d2 && beqBlockId f1 f2 && beqBlockId t1 t2
    | _ => false
  | .callLayout d1 q1 t1 =>
    match b with
    | .callLayout d2 q2 t2 =>
      beqPlace d1 d2 && beqLayoutQuery q1 q2 && beqBlockId t1 t2
    | _ => false
  | .callTransmuteCopy d1 s1 dt1 o1 t1 =>
    match b with
    | .callTransmuteCopy d2 s2 dt2 o2 t2 =>
      beqPlace d1 d2 && beqMirTy s1 s2 && beqMirTy dt1 dt2 &&
      beqOperand o1 o2 && beqBlockId t1 t2
    | _ => false
  | .call1 d1 c1 a1 t1 tys1 =>
    match b with
    | .call1 d2 c2 a2 t2 tys2 =>
      beqPlace d1 d2 && beqBodyId c1 c2 && beqOperand a1 a2 &&
      beqBlockId t1 t2 && listBeq beqMirTy tys1 tys2
    | _ => false
  | _ => false

theorem eq_of_beqTerminator {a b : Terminator} (h : beqTerminator a b = true) :
    a = b := by
  cases a with
  | return_ => cases b <;> first | rfl | cases h
  | goto a1 =>
    cases b with
    | goto b1 => exact congrArg Terminator.goto (eq_of_beqBlockId h)
    | _ => cases h
  | unreachable => cases b <;> first | rfl | cases h
  | panic => cases b <;> first | rfl | cases h
  | assert c1 e1 t1 k1 =>
    cases b with
    | assert c2 e2 t2 k2 =>
      simp [beqTerminator] at h
      rw [eq_of_beqOperand h.1.1.1, h.1.1.2, eq_of_beqBlockId h.1.2,
        eq_of_beqAssertFailKind h.2]
    | _ => cases h
  | switchInt d1 f1 t1 =>
    cases b with
    | switchInt d2 f2 t2 =>
      simp [beqTerminator] at h
      rw [eq_of_beqOperand h.1.1, eq_of_beqBlockId h.1.2, eq_of_beqBlockId h.2]
    | _ => cases h
  | callLayout d1 q1 t1 =>
    cases b with
    | callLayout d2 q2 t2 =>
      simp [beqTerminator] at h
      rw [eq_of_beqPlace h.1.1, eq_of_beqLayoutQuery h.1.2,
        eq_of_beqBlockId h.2]
    | _ => cases h
  | callTransmuteCopy d1 s1 dt1 o1 t1 =>
    cases b with
    | callTransmuteCopy d2 s2 dt2 o2 t2 =>
      simp [beqTerminator] at h
      rw [eq_of_beqPlace h.1.1.1.1, eq_of_beqMirTy h.1.1.1.2,
        eq_of_beqMirTy h.1.1.2, eq_of_beqOperand h.1.2, eq_of_beqBlockId h.2]
    | _ => cases h
  | call1 d1 c1 a1 t1 tys1 =>
    cases b with
    | call1 d2 c2 a2 t2 tys2 =>
      simp [beqTerminator] at h
      rw [eq_of_beqPlace h.1.1.1.1, eq_of_beqBodyId h.1.1.1.2,
        eq_of_beqOperand h.1.1.2, eq_of_beqBlockId h.1.2,
        listEq_of_beq eq_of_beqMirTy h.2]
    | _ => cases h
  | _ => cases h

def beqBasicBlock (a b : BasicBlock) : Bool :=
  listBeq beqStmt a.stmts b.stmts &&
  beqTerminator a.terminator b.terminator

theorem eq_of_beqBasicBlock {a b : BasicBlock}
    (h : beqBasicBlock a b = true) : a = b := by
  cases a; cases b; simp [beqBasicBlock] at h
  rw [listEq_of_beq eq_of_beqStmt h.1, eq_of_beqTerminator h.2]

/-- Fuel-free structural equality on `MirBody`, enabled by flat `BodyId`
indirection in `Crate.bodies`. -/
def beqMirBody (a b : MirBody) : Bool :=
  listBeq beqMirTy a.argTys b.argTys &&
  beqMirTy a.retTy b.retTy &&
  a.localCount == b.localCount &&
  listBeq beqBasicBlock a.blocks b.blocks

theorem eq_of_beqMirBody {a b : MirBody} (h : beqMirBody a b = true) : a = b := by
  cases a; cases b; simp [beqMirBody] at h
  rw [listEq_of_beq eq_of_beqMirTy h.1.1.1,
    eq_of_beqMirTy h.1.1.2,
    h.1.2,
    listEq_of_beq eq_of_beqBasicBlock h.2]

def beqRequiresSpec (a b : RequiresSpec) : Bool :=
  a.argLocal == b.argLocal && a.ne == b.ne

theorem eq_of_beqRequiresSpec {a b : RequiresSpec}
    (h : beqRequiresSpec a b = true) : a = b := by
  cases a; cases b; simp [beqRequiresSpec] at h; rw [h.1, h.2]

def beqPostSpec : PostSpec → PostSpec → Bool
  | .ensuresEqArg a, .ensuresEqArg b => a == b

theorem eq_of_beqPostSpec : ∀ {a b : PostSpec}, beqPostSpec a b = true → a = b
  | .ensuresEqArg _, .ensuresEqArg _, h => by
    simp [beqPostSpec] at h; exact congrArg PostSpec.ensuresEqArg h

def beqTCBItem : TCBItem → TCBItem → Bool
  | .rustcLowering n1 b1, .rustcLowering n2 b2 =>
    decide (n1 = n2) && decide (b1.index = b2.index)
  | .fnVerified n1 b1, .fnVerified n2 b2 =>
    decide (n1 = n2) && decide (b1.index = b2.index)
  | .compileTimeGuard n1 b1, .compileTimeGuard n2 b2 =>
    decide (n1 = n2) && decide (b1.index = b2.index)
  | .transparentDepBody n1 b1, .transparentDepBody n2 b2 =>
    decide (n1 = n2) && decide (b1.index = b2.index)
  | .documentedIntent n1 b1 d1, .documentedIntent n2 b2 d2 =>
    decide (n1 = n2) && decide (b1.index = b2.index) && decide (d1 = d2)
  | .pinnedCompilerCoupled n1 b1 r1, .pinnedCompilerCoupled n2 b2 r2 =>
    decide (n1 = n2) && decide (b1.index = b2.index) && decide (r1 = r2)
  | _, _ => false

theorem eq_of_beqTCBItem : ∀ {a b : TCBItem}, beqTCBItem a b = true → a = b
  | .rustcLowering _ b1, .rustcLowering _ b2, h => by
    cases b1; cases b2; simp [beqTCBItem] at h; rw [h.1, h.2]
  | .fnVerified _ b1, .fnVerified _ b2, h => by
    cases b1; cases b2; simp [beqTCBItem] at h; rw [h.1, h.2]
  | .compileTimeGuard _ b1, .compileTimeGuard _ b2, h => by
    cases b1; cases b2; simp [beqTCBItem] at h; rw [h.1, h.2]
  | .transparentDepBody _ b1, .transparentDepBody _ b2, h => by
    cases b1; cases b2; simp [beqTCBItem] at h; rw [h.1, h.2]
  | .documentedIntent _ b1 _, .documentedIntent _ b2 _, h => by
    cases b1; cases b2; simp [beqTCBItem] at h; rw [h.1.1, h.1.2, h.2]
  | .pinnedCompilerCoupled _ b1 _, .pinnedCompilerCoupled _ b2 _, h => by
    cases b1; cases b2; simp [beqTCBItem] at h; rw [h.1.1, h.1.2, h.2]

theorem beqTCBItem_refl (a : TCBItem) : beqTCBItem a a = true := by
  cases a <;> (
    dsimp [beqTCBItem]
    repeat rw [decide_eq_true rfl]
    rfl)

theorem ne_of_beqTCBItem_false {a b : TCBItem}
    (h : beqTCBItem a b = false) : a ≠ b := by
  intro heq
  subst heq
  rw [beqTCBItem_refl] at h
  cases h

/-! ### Generic `NoDupIds` and `TCBItem` inventory checkers -/

def checkNotMem {α : Type} (beq : α → α → Bool) (x : α) :
    List α → Bool
  | [] => true
  | y :: ys => !beq x y && checkNotMem beq x ys

theorem allHold_ne_of_checkNotMem {α : Type} {beq : α → α → Bool}
    (hne : ∀ {x y : α}, beq x y = false → x ≠ y) {x : α} :
    ∀ {ys : List α},
      checkNotMem beq x ys = true →
      AllHold (ys.map (fun y => x ≠ y))
  | [], _ => True.intro
  | y :: ys, h => by
    have h' : (!beq x y && checkNotMem beq x ys) = true := h
    cases hxy : beq x y with
    | true => rw [hxy] at h'; cases h'
    | false =>
      rw [hxy] at h'
      exact ⟨hne hxy, allHold_ne_of_checkNotMem hne h'⟩

def checkNoDupFoldr {α : Type} (beq : α → α → Bool) :
    List α → Bool × List α
  | [] => (true, [])
  | x :: xs =>
    let r := checkNoDupFoldr beq xs
    (checkNotMem beq x r.2 && r.1, x :: r.2)

theorem noDupIds_of_checkNoDupFoldr {α : Type} {beq : α → α → Bool}
    (hne : ∀ {x y : α}, beq x y = false → x ≠ y) :
    ∀ {xs : List α},
      (checkNoDupFoldr beq xs).1 = true →
      NoDupIds xs ∧
      (checkNoDupFoldr beq xs).2 =
        (xs.foldr
          (fun id (acc : Prop × List α) =>
            (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1,
             id :: acc.2))
          (True, [])).2
  | [], _ => ⟨True.intro, rfl⟩
  | x :: xs, h => by
    have h' :
        (checkNotMem beq x (checkNoDupFoldr beq xs).2 &&
          (checkNoDupFoldr beq xs).1) = true := h
    cases h1 : checkNotMem beq x (checkNoDupFoldr beq xs).2 with
    | false => rw [h1] at h'; cases h'
    | true =>
      rw [h1] at h'
      have ih := noDupIds_of_checkNoDupFoldr hne (xs := xs) h'
      have hall := allHold_ne_of_checkNotMem hne h1
      rw [ih.2] at hall
      exact ⟨⟨hall, ih.1⟩, congrArg (List.cons x) ih.2⟩

def checkNoDupIds {α : Type} (beq : α → α → Bool)
    (xs : List α) : Bool :=
  (checkNoDupFoldr beq xs).1

theorem noDupIds_of_check {α : Type} {beq : α → α → Bool}
    (hne : ∀ {x y : α}, beq x y = false → x ≠ y) {xs : List α}
    (h : checkNoDupIds beq xs = true) : NoDupIds xs :=
  (noDupIds_of_checkNoDupFoldr hne h).1

def checkMemTCB (x : TCBItem) : List TCBItem → Bool
  | [] => false
  | y :: ys => beqTCBItem x y || checkMemTCB x ys

theorem mem_of_checkMemTCB {x : TCBItem} :
    ∀ {ys : List TCBItem}, checkMemTCB x ys = true → x ∈ ys
  | [], h => by cases h
  | y :: ys, h => by
    have h' : (beqTCBItem x y || checkMemTCB x ys) = true := h
    cases hxy : beqTCBItem x y with
    | true =>
      rw [eq_of_beqTCBItem hxy]
      exact .head _
    | false =>
      rw [hxy] at h'
      exact .tail _ (mem_of_checkMemTCB h')

def isAllowedTCB : TCBItem → Bool
  | .fnVerified _ _ => false
  | _ => true

def checkAllowedTCB : List TCBItem → Bool
  | [] => true
  | x :: xs => isAllowedTCB x && checkAllowedTCB xs

theorem allHold_allowed_of_checkAllowedTCB :
    ∀ {xs : List TCBItem},
      checkAllowedTCB xs = true →
      AllHold (xs.map defaultTrustPolicy.isAllowed)
  | [], _ => True.intro
  | x :: xs, h => by
    cases x with
    | fnVerified _ _ => cases h
    | rustcLowering _ _ =>
      exact ⟨True.intro, allHold_allowed_of_checkAllowedTCB h⟩
    | compileTimeGuard _ _ =>
      exact ⟨True.intro, allHold_allowed_of_checkAllowedTCB h⟩
    | transparentDepBody _ _ =>
      exact ⟨True.intro, allHold_allowed_of_checkAllowedTCB h⟩
    | documentedIntent _ _ _ =>
      exact ⟨True.intro, allHold_allowed_of_checkAllowedTCB h⟩
    | pinnedCompilerCoupled _ _ _ =>
      exact ⟨True.intro, allHold_allowed_of_checkAllowedTCB h⟩

/-! ### Compositional per-function and per-crate verification -/

abbrev UserSpecsHold (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (tcb : List TCBItem := []) : Prop :=
  AllHold ((fn.specs.map (denotePostSpec adts bodies)).map
    (fun spec =>
      NonVacuousOn ((MirLang adts bodies).dom (fn.resolveBody bodies))
        (fun q =>
          fn.effectivePre adts bodies adtInv q tcb ∧ (spec q).defined) ∧
      (MirLang adts bodies).sem (fn.resolveBody bodies) ≤ (fun q =>
        ⟨fn.effectivePre adts bodies adtInv q tcb ∧ (spec q).defined,
          fun h o => (spec q).val h.2 o⟩)))

theorem userSpecsHold_nil {adts : List AdtDecl} {bodies : List BodyDecl}
    {adtInv : AdtInv} {fn : CapturedFn} {tcb : List TCBItem}
    (h : fn.specs = []) :
    UserSpecsHold adts bodies adtInv fn tcb := by
  unfold UserSpecsHold
  rw [h]
  exact True.intro

theorem userSpecs_ensuresEqArg1_of_lowerBody {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (target : MirBody)
    (hres : lowerBody (fn.resolveBody bodies) = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hver : FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb)
    (hspecs : fn.specs = [.ensuresEqArg 1])
    (h_exec : ∀ s, initMirState [] bodies target s →
      ExecNormal [] bodies target s (fun r => s.locals 1 = some r.value)) :
    UserSpecsHold [] bodies defaultAdtInv fn tcb := by
  unfold UserSpecsHold
  rw [hspecs]
  dsimp [List.map, denotePostSpec]
  refine ⟨⟨nonVacuousOn_and_defined hver.1.1 (fun _ _ => True.intro), ?_⟩,
    True.intro⟩
  exact execNormal_spec_on_pre (fun s hpre => by
    have ⟨hinitT, _, _⟩ :=
      (effectivePre_of_lowerBody_eq hres hpin).mp hpre
    have hcallsOrig :
        (fn.resolveBody bodies).blocks.all
          (fun bb => !isCall1 bb.terminator) = true := by
      rw [← noCall_lowerBody (fn.resolveBody bodies), hres]
      exact hcalls
    have hexecLow :
        ExecNormal [] bodies (lowerBody (fn.resolveBody bodies)) s
          (fun r => s.locals 1 = some r.value) := by
      rw [hres]
      exact h_exec s hinitT
    exact lowerBody_simulates hcallsOrig (fun _ _ _ h => h)
      hinitT.2.1 hinitT.2.2.1 hinitT.2.2.2.1 hexecLow)

/-- Structured diagnostic returned when `proveCrateOpt` cannot discharge a
function or crate obligation. -/
structure ProofError where
  message : String
  scope : String

/-- Discharge either `fn.specs = []` or `fn.specs = [.ensuresEqArg 1]` for an
identity-like intra-procedural body `target`. -/
def dispatchIdLikeSpecs {bodies : List BodyDecl} {tcb : List TCBItem}
    (fn : CapturedFn)
    (target : MirBody)
    (hres : lowerBody (fn.resolveBody bodies) = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hver : FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb)
    (h_exec : ∀ s, initMirState [] bodies target s →
      ExecNormal [] bodies target s (fun r => s.locals 1 = some r.value))
    (errMsg : String) :
    Except ProofError
      (PLift
        (FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb ∧
         UserSpecsHold [] bodies defaultAdtInv fn tcb)) :=
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    .ok (.up ⟨hver, userSpecsHold_nil (listEq_of_beq eq_of_beqPostSpec hs0)⟩)
  else if hs1 : listBeq beqPostSpec fn.specs [.ensuresEqArg 1] = true then
    .ok (.up ⟨hver,
      userSpecs_ensuresEqArg1_of_lowerBody fn target hres hcalls hpin hver
        (listEq_of_beq eq_of_beqPostSpec hs1) h_exec⟩)
  else
    .error ⟨errMsg, fn.name⟩

theorem fnObligations_verified {c : Crate} {fn : CapturedFn}
    (h_nodup_tcb : NoDupIds c.tcb)
    (h_allowed_tcb : AllHold (c.tcb.map defaultTrustPolicy.isAllowed))
    (h_mem_tcb : TCBItem.rustcLowering fn.name fn.bodyId ∈ c.tcb)
    (h_deps : calledTransparentDeps c.bodies fn.name (fn.resolveBody c.bodies) = [])
    (h_ver : FnVerifiedAndRetInv c.adts c.bodies c.adtInv fn c.tcb)
    (h_specs : UserSpecsHold c.adts c.bodies c.adtInv fn c.tcb) :
    VerificationResult defaultTrustPolicy c.tcb
      (fn.obligations c.adts c.bodies c.adtInv c.tcb) := by
  dsimp [CapturedFn.obligations]
  rw [h_deps]
  exact ⟨(by intro h; cases h),
    ⟨⟨tcbItem_rustcLowering_ne_fnVerified, True.intro⟩, True.intro, True.intro⟩,
    h_nodup_tcb,
    h_allowed_tcb,
    ⟨Or.inl h_mem_tcb,
     Or.inr ⟨h_ver.1, ⟨h_ver.2.1, h_ver.2.2⟩, h_specs⟩,
     True.intro⟩⟩

/-- Extract the first `.call1` callee `BodyId` from a body's blocks, if any. -/
def firstCalleeId (b : MirBody) : BodyId :=
  match b.blocks with
  | bb :: _ =>
    match bb.terminator with
    | .call1 _ calleeId _ _ _ => calleeId
    | _ => ⟨0⟩
  | _ => ⟨0⟩

/-- Extract the first `.evalConst` constant `BodyId` from a statement list. -/
def firstEvalConstInStmts : List Stmt → Option BodyId
  | [] => none
  | .evalConst _ constId _ :: _ => some constId
  | _ :: rest => firstEvalConstInStmts rest

/-- Extract the first `.evalConst` constant `BodyId` from a body, if any. -/
def firstRequiredConstId (b : MirBody) : BodyId :=
  match b.blocks with
  | bb :: _ => (firstEvalConstInStmts bb.stmts).getD ⟨0⟩
  | _ => ⟨0⟩

/-- Per-function proof dispatcher for crates without ADTs (`adts = []`).
Normalizes intra-procedural bodies with `lowerBody` before matching so that
functions containing `Stmt.nop` or forwarding `goto` chains reduce to the
same canonical verification theorems. -/
def proveFnNoAdtOpt (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) (hpin : hasPinnedCoupledWaiver fn tcb = false) :
    Except ProofError
      (PLift
        (FnVerifiedAndRetInv [] bodies defaultAdtInv fn tcb ∧
         UserSpecsHold [] bodies defaultAdtInv fn tcb)) :=
  let b := fn.resolveBody bodies
  let lb := lowerBody b
  if hreq : optBeq beqRequiresSpec fn.requires none = true then
    have hreqEq : fn.requires = none := optEq_of_beq eq_of_beqRequiresSpec hreq
    if hb : beqMirBody lb idCopyBody = true then
      have hres : lowerBody (fn.resolveBody bodies) = idCopyBody :=
        eq_of_beqMirBody hb
      dispatchIdLikeSpecs fn idCopyBody hres rfl hpin
        (idCopyBody_verified_of_resolve fn hres hreqEq hpin)
        (fun s hinit => (idCopyBody_execNormal s hinit).map (fun _ h => h.1))
        "unsupported specs on id (copy)"
    else if hb : beqMirBody lb idMoveBody = true then
      have hres : lowerBody (fn.resolveBody bodies) = idMoveBody :=
        eq_of_beqMirBody hb
      dispatchIdLikeSpecs fn idMoveBody hres rfl hpin
        (idMoveBody_verified_of_resolve fn hres hreqEq hpin)
        (fun s hinit => (idMoveBody_execNormal s hinit).map (fun _ h => h.1))
        "unsupported specs on id (move)"
    else if hb : beqMirBody lb allocPassthroughBody = true then
      have hres : lowerBody (fn.resolveBody bodies) = allocPassthroughBody :=
        eq_of_beqMirBody hb
      dispatchIdLikeSpecs fn allocPassthroughBody hres rfl hpin
        (allocPassthroughBody_verified_of_resolve fn hres hreqEq hpin)
        (fun s hinit =>
          (allocPassthroughBody_execNormal s hinit).map (fun _ h => h.1))
        "unsupported specs on alloc_passthrough"
    else
      let constId := firstRequiredConstId lb
      if hb : beqMirBody lb (inlineConstTransmuteBody constId) = true then
        have hres :
            lowerBody (fn.resolveBody bodies) =
              inlineConstTransmuteBody constId :=
          eq_of_beqMirBody hb
        if hconst :
            optBeq beqMirBody (findBody bodies constId)
              (some (sizeEqConstBodyAt .usize .usize)) = true then
          if hs0 : listBeq beqPostSpec fn.specs [] = true then
            .ok (.up ⟨inlineConstTransmute_verified_of_resolve fn hres hreqEq
                (optEq_of_beq eq_of_beqMirBody hconst) hpin,
              userSpecsHold_nil (listEq_of_beq eq_of_beqPostSpec hs0)⟩)
          else
            .error ⟨"unsupported specs on inline_const_transmute", fn.name⟩
        else
          .error ⟨"unproved required const", fn.name⟩
      else
        let calleeId := firstCalleeId b
        if hb : beqMirBody b (concreteTransmuteCallerBody calleeId .usize) = true then
          have hres :
              fn.resolveBody bodies =
                concreteTransmuteCallerBody calleeId .usize :=
            eq_of_beqMirBody hb
          match hcalleeOpt : findBody bodies calleeId with
          | none => .error ⟨"missing callee body", fn.name⟩
          | some calleeBody =>
            let cId := firstRequiredConstId calleeBody
            if hcallee :
                beqMirBody calleeBody (transmuteCheckedBody cId) = true then
              if hconst :
                   optBeq beqMirBody (findBody bodies cId)
                     (some sizeEqConstBody) = true then
                if hs0 : listBeq beqPostSpec fn.specs [] = true then
                  have hcalleeEq :
                      findBody bodies calleeId =
                        some (transmuteCheckedBody cId) := by
                    rw [hcalleeOpt, eq_of_beqMirBody hcallee]
                  .ok (.up ⟨concreteTransmuteCaller_verified_of_resolve fn
                      hres hreqEq hcalleeEq
                      (optEq_of_beq eq_of_beqMirBody hconst) hpin,
                    userSpecsHold_nil (listEq_of_beq eq_of_beqPostSpec hs0)⟩)
                else
                  .error ⟨"unsupported specs on concrete transmute caller", fn.name⟩
              else
                .error ⟨"unproved required const on callee", fn.name⟩
            else
              .error ⟨"unproved callee body", fn.name⟩
        else
          .error ⟨"unproved function body", fn.name⟩
  else
    .error ⟨"unexpected requires clause", fn.name⟩

/-- Per-function proof dispatcher for crates with `[nonZeroAdtDecl 0 repr]`. -/
def proveFnNonZeroOpt (repr : AdtRepr)
    (hrepr : repr = .rust ∨ repr = .transparent)
    (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) (hpin : hasPinnedCoupledWaiver fn tcb = false) :
    Except ProofError
      (PLift
        (FnVerifiedAndRetInv [nonZeroAdtDecl 0 repr] bodies
           (nonZeroAdtInv repr) fn tcb ∧
         UserSpecsHold [nonZeroAdtDecl 0 repr] bodies
           (nonZeroAdtInv repr) fn tcb)) :=
  let lb := lowerBody (fn.resolveBody bodies)
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    have hspecs :
        UserSpecsHold [nonZeroAdtDecl 0 repr] bodies (nonZeroAdtInv repr) fn
          tcb :=
      userSpecsHold_nil (listEq_of_beq eq_of_beqPostSpec hs0)
    if hreq : optBeq beqRequiresSpec fn.requires none = true then
      have hreqEq : fn.requires = none :=
        optEq_of_beq eq_of_beqRequiresSpec hreq
      if hb : beqMirBody lb makeNonZeroBody = true then
        .ok (.up ⟨makeNonZeroBody_verified_of_resolve fn
            (eq_of_beqMirBody hb) hreqEq hpin hrepr,
          hspecs⟩)
      else if hb : beqMirBody lb (getUncheckedNonZeroBodyAt 0 false) = true then
        .ok (.up ⟨getUncheckedNonZeroBody_verified_of_resolve false fn
            (eq_of_beqMirBody hb) hreqEq hpin hrepr,
          hspecs⟩)
      else if hb : beqMirBody lb (getUncheckedNonZeroBodyAt 0 true) = true then
        .ok (.up ⟨getUncheckedNonZeroBody_verified_of_resolve true fn
            (eq_of_beqMirBody hb) hreqEq hpin hrepr,
          hspecs⟩)
      else
        .error ⟨"unproved safe NonZeroUsize function", fn.name⟩
    else if hreq :
        optBeq beqRequiresSpec fn.requires newUncheckedRequires = true then
      have hreqEq : fn.requires = newUncheckedRequires :=
        optEq_of_beq eq_of_beqRequiresSpec hreq
      if hb : beqMirBody lb newUncheckedBody = true then
        .ok (.up ⟨newUncheckedBody_verified_of_resolve fn
            (eq_of_beqMirBody hb) hreqEq hpin hrepr,
          hspecs⟩)
      else
        .error ⟨"unproved unsafe NonZeroUsize function", fn.name⟩
    else
      .error ⟨"unsupported requires clause", fn.name⟩
  else
    .error ⟨"unsupported specs on NonZeroUsize function", fn.name⟩

/-- Per-function proof dispatcher for `[reprTransparentWrapAdtDecl]`. -/
def proveFnTransWrapOpt (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) (hpin : hasPinnedCoupledWaiver fn tcb = false) :
    Except ProofError
      (PLift
        (FnVerifiedAndRetInv [reprTransparentWrapAdtDecl] bodies
           (denoteAdtInv [reprTransparentWrapAdtDecl]) fn tcb ∧
         UserSpecsHold [reprTransparentWrapAdtDecl] bodies
           (denoteAdtInv [reprTransparentWrapAdtDecl]) fn tcb)) :=
  let lb := lowerBody (fn.resolveBody bodies)
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    have hspecs :
        UserSpecsHold [reprTransparentWrapAdtDecl] bodies
          (denoteAdtInv [reprTransparentWrapAdtDecl]) fn tcb :=
      userSpecsHold_nil (listEq_of_beq eq_of_beqPostSpec hs0)
    if hreq : optBeq beqRequiresSpec fn.requires none = true then
      have hreqEq : fn.requires = none :=
        optEq_of_beq eq_of_beqRequiresSpec hreq
      if hb : beqMirBody lb (adtTransmuteBody 0) = true then
        .ok (.up ⟨adtTransmuteBody_transparent_verified_of_resolve fn
            (eq_of_beqMirBody hb) hreqEq hpin,
          hspecs⟩)
      else
        .error ⟨"unproved #[repr(transparent)] function", fn.name⟩
    else
      .error ⟨"unsupported requires clause on #[repr(transparent)] function", fn.name⟩
  else
    .error ⟨"unsupported specs on #[repr(transparent)] function", fn.name⟩

/-- Per-function proof dispatcher for `[reprRustWrapAdtDecl]`:
- Unguarded `adtTransmuteBody 0` requires `TCBItem.pinnedCompilerCoupled`.
- Const-guarded `capturedGuardedAdtTransmuteBody constId 0` requires
  `TCBItem.compileTimeGuard`. -/
def proveFnRustWrapOpt (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) :
    Except ProofError
      (PLift
        (FnVerifiedAndRetInv [reprRustWrapAdtDecl] bodies
           (denoteAdtInv [reprRustWrapAdtDecl]) fn tcb ∧
         UserSpecsHold [reprRustWrapAdtDecl] bodies
           (denoteAdtInv [reprRustWrapAdtDecl]) fn tcb)) :=
  let b := fn.resolveBody bodies
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    have hspecs :
        UserSpecsHold [reprRustWrapAdtDecl] bodies
          (denoteAdtInv [reprRustWrapAdtDecl]) fn tcb :=
      userSpecsHold_nil (listEq_of_beq eq_of_beqPostSpec hs0)
    if hreq : optBeq beqRequiresSpec fn.requires none = true then
      have hreqEq : fn.requires = none :=
        optEq_of_beq eq_of_beqRequiresSpec hreq
      if hb : beqMirBody b (adtTransmuteBody 0) = true then
        if hpin : decide (hasPinnedCoupledWaiver fn tcb = true) = true then
          .ok (.up ⟨adtTransmuteBody_rustPinned_verified_of_resolve fn
              (eq_of_beqMirBody hb) hreqEq (of_decide_eq_true hpin),
            hspecs⟩)
        else
          .error ⟨"missing TCBItem.pinnedCompilerCoupled waiver for unguarded #[repr(Rust)] transmute", fn.name⟩
      else
        let constId := firstRequiredConstId b
        if hb : beqMirBody b (capturedGuardedAdtTransmuteBody constId 0) = true then
          if hconst :
              optBeq beqMirBody (findBody bodies constId)
                (some (sizeEqConstBodyAt (.adt 0) .usize)) = true then
            if hpin : decide (hasPinnedCoupledWaiver fn tcb = false) = true then
              if hguard : decide (hasCompileTimeGuardWaiver fn tcb = true) = true then
                .ok (.up ⟨capturedGuardedAdtTransmuteBody_rustGuarded_verified_of_resolve
                    fn (eq_of_beqMirBody hb) hreqEq
                    (optEq_of_beq eq_of_beqMirBody hconst)
                    (of_decide_eq_true hpin) (of_decide_eq_true hguard),
                  hspecs⟩)
              else
                .error ⟨"missing TCBItem.compileTimeGuard waiver for const-guarded #[repr(Rust)] transmute", fn.name⟩
            else
              .error ⟨"unexpected TCBItem.pinnedCompilerCoupled waiver on const-guarded function", fn.name⟩
          else
            .error ⟨"unproved required const on #[repr(Rust)] transmute", fn.name⟩
        else
          .error ⟨"unproved #[repr(Rust)] function", fn.name⟩
    else
      .error ⟨"unsupported requires clause on #[repr(Rust)] function", fn.name⟩
  else
    .error ⟨"unsupported specs on #[repr(Rust)] function", fn.name⟩

/-- Compositionally discharge `AllHold` of `VerificationResult` across any list
of `CapturedFn`s using a per-function prover `proveFn`. -/
def proveFnsLoop (c : Crate)
    (h_nodup_tcb : NoDupIds c.tcb)
    (h_allowed_tcb : AllHold (c.tcb.map defaultTrustPolicy.isAllowed))
    (proveFn :
      ∀ (fn : CapturedFn),
        Except ProofError
          (PLift
            (FnVerifiedAndRetInv c.adts c.bodies c.adtInv fn c.tcb ∧
             UserSpecsHold c.adts c.bodies c.adtInv fn c.tcb))) :
    ∀ (fns : List CapturedFn),
      Except ProofError
        (PLift
          (AllHold (fns.map (fun fn =>
            VerificationResult defaultTrustPolicy c.tcb
              (fn.obligations c.adts c.bodies c.adtInv c.tcb)))))
  | [] => .ok (.up True.intro)
  | fn :: rest =>
    if hmem : checkMemTCB (TCBItem.rustcLowering fn.name fn.bodyId) c.tcb = true then
      if hdeps :
          decide
            (calledTransparentDeps c.bodies fn.name (fn.resolveBody c.bodies) =
              []) = true then
        match proveFn fn with
        | .error err => .error err
        | .ok pFn =>
          match proveFnsLoop c h_nodup_tcb h_allowed_tcb proveFn rest with
          | .error err => .error err
          | .ok pRest =>
            .ok (.up
              ⟨fnObligations_verified h_nodup_tcb h_allowed_tcb
                (mem_of_checkMemTCB hmem) (of_decide_eq_true hdeps)
                pFn.down.1 pFn.down.2,
               pRest.down⟩)
      else
        .error ⟨"unsupported transparentDepBody call", fn.name⟩
    else
      .error ⟨"missing TCBItem.rustcLowering waiver", fn.name⟩

/-- Compositional Lean proof dispatcher: validates crate-level structural
invariants (`c.functions ≠ []`, `NoDupIds` on bodies, functions, and TCB items,
`AdmissibleAdtInv`, and `defaultTrustPolicy`) and then verifies each function
in `c.functions` independently via `proveFnsLoop`. -/
def proveCrateOpt (c : Crate) :
    Except ProofError (PLift (CrateTheorem c)) :=
  if hne : decide (c.functions = []) = false then
    if hbnodup :
        checkNoDupIds (fun a b => decide (a = b))
          (c.bodies.map (fun d => d.id.index)) = true then
      if hfnodup :
          checkNoDupIds (fun a b => decide (a = b))
            (c.functions.map CapturedFn.name) = true then
        if htnodup : checkNoDupIds beqTCBItem c.tcb = true then
          if htallow : checkAllowedTCB c.tcb = true then
            have h_fns_ne : c.functions ≠ [] := of_decide_eq_false hne
            have h_bodies_nodup :
                NoDupIds (c.bodies.map (fun d => d.id.index)) :=
              noDupIds_of_check (fun h => of_decide_eq_false h) hbnodup
            have h_fns_nodup : NoDupIds (c.functions.map CapturedFn.name) :=
              noDupIds_of_check (fun h => of_decide_eq_false h) hfnodup
            have h_tcb_nodup : NoDupIds c.tcb :=
              noDupIds_of_check ne_of_beqTCBItem_false htnodup
            have h_tcb_allow :
                AllHold (c.tcb.map defaultTrustPolicy.isAllowed) :=
              allHold_allowed_of_checkAllowedTCB htallow
            let finish (hadm : AdmissibleAdtInv c.adts c.adtInv)
                (proveFn : (fn : CapturedFn) →
                  Except ProofError
                    (PLift
                      (FnVerifiedAndRetInv c.adts c.bodies c.adtInv fn c.tcb ∧
                       UserSpecsHold c.adts c.bodies c.adtInv fn c.tcb))) :
                Except ProofError (PLift (CrateTheorem c)) :=
              match proveFnsLoop c h_tcb_nodup h_tcb_allow proveFn c.functions with
              | .ok pFns =>
                .ok (.up ⟨h_fns_ne, h_bodies_nodup, h_fns_nodup, hadm, pFns.down⟩)
              | .error err => .error err
            let finishNoPin (hadm : AdmissibleAdtInv c.adts c.adtInv)
                (proveFn : (fn : CapturedFn) → hasPinnedCoupledWaiver fn c.tcb = false →
                  Except ProofError
                    (PLift
                      (FnVerifiedAndRetInv c.adts c.bodies c.adtInv fn c.tcb ∧
                       UserSpecsHold c.adts c.bodies c.adtInv fn c.tcb))) :
                Except ProofError (PLift (CrateTheorem c)) :=
              finish hadm (fun fn =>
                if hpin : decide (hasPinnedCoupledWaiver fn c.tcb = false) = true then
                  proveFn fn (of_decide_eq_true hpin)
                else
                  .error ⟨"unsupported pinnedCompilerCoupled waiver", fn.name⟩)
            if hadts0 : listBeq beqAdtDecl c.adts [] = true then
              have hadtsEq : c.adts = [] :=
                listEq_of_beq eq_of_beqAdtDecl hadts0
              have hadm : AdmissibleAdtInv c.adts c.adtInv := by
                unfold Crate.adtInv; rw [hadtsEq]; exact defaultAdtInv_admissible
              finishNoPin hadm (fun fn hpin => by
                unfold Crate.adtInv; rw [hadtsEq]
                exact proveFnNoAdtOpt c.bodies c.tcb fn hpin)
            else if hadt1 :
                listBeq beqAdtDecl c.adts [nonZeroAdtDecl 0 .rust] = true then
              have hadtsEq : c.adts = [nonZeroAdtDecl 0 .rust] :=
                listEq_of_beq eq_of_beqAdtDecl hadt1
              have hadm : AdmissibleAdtInv c.adts c.adtInv := by
                unfold Crate.adtInv; rw [hadtsEq]; exact nonZeroAdtInv_admissible
              finishNoPin hadm (fun fn hpin => by
                unfold Crate.adtInv; rw [hadtsEq]
                exact proveFnNonZeroOpt .rust (Or.inl rfl) c.bodies c.tcb fn hpin)
            else if hadt2 :
                listBeq beqAdtDecl c.adts [nonZeroAdtDecl 0 .transparent] = true then
              have hadtsEq : c.adts = [nonZeroAdtDecl 0 .transparent] :=
                listEq_of_beq eq_of_beqAdtDecl hadt2
              have hadm : AdmissibleAdtInv c.adts c.adtInv := by
                unfold Crate.adtInv; rw [hadtsEq]; exact nonZeroAdtInv_admissible
              finishNoPin hadm (fun fn hpin => by
                unfold Crate.adtInv; rw [hadtsEq]
                exact proveFnNonZeroOpt .transparent (Or.inr rfl) c.bodies c.tcb fn hpin)
            else if hadt3 :
                listBeq beqAdtDecl c.adts [reprTransparentWrapAdtDecl] = true then
              have hadtsEq : c.adts = [reprTransparentWrapAdtDecl] :=
                listEq_of_beq eq_of_beqAdtDecl hadt3
              have hadm : AdmissibleAdtInv c.adts c.adtInv := by
                unfold Crate.adtInv; rw [hadtsEq]; exact reprTransparentWrapAdtInv_admissible
              finishNoPin hadm (fun fn hpin => by
                unfold Crate.adtInv; rw [hadtsEq]
                exact proveFnTransWrapOpt c.bodies c.tcb fn hpin)
            else if hadt4 :
                listBeq beqAdtDecl c.adts [reprRustWrapAdtDecl] = true then
              have hadtsEq : c.adts = [reprRustWrapAdtDecl] :=
                listEq_of_beq eq_of_beqAdtDecl hadt4
              have hadm : AdmissibleAdtInv c.adts c.adtInv := by
                unfold Crate.adtInv; rw [hadtsEq]; exact reprRustWrapAdtInv_admissible
              finish hadm (fun fn => by
                unfold Crate.adtInv; rw [hadtsEq]
                exact proveFnRustWrapOpt c.bodies c.tcb fn)
            else
              .error ⟨"unsupported ADT inventory", "crate"⟩
          else
            .error ⟨"disallowed fnVerified TCB waiver", "crate"⟩
        else
          .error ⟨"duplicate TCB waiver IDs", "crate"⟩
      else
        .error ⟨"duplicate function names", "crate"⟩
    else
      .error ⟨"duplicate body IDs", "crate"⟩
  else
    .error ⟨"crate defines no public functions", "crate"⟩

/-- Computable check returning `[]` iff `proveCrateOpt c` succeeds. -/
def checkCrate (c : Crate) : List String :=
  match proveCrateOpt c with
  | .ok _ => []
  | .error err => [err.message, err.scope]

/-- Universal crate verification entrypoint: when `checkCrate c = []` holds by
`rfl`, extracts the kernel-checked `CrateTheorem c` proof from
`proveCrateOpt c`. -/
theorem proveCrate (c : Crate) (h : checkCrate c = []) : CrateTheorem c := by
  unfold checkCrate at h
  cases hp : proveCrateOpt c with
  | ok p => exact p.down
  | error err => simp [hp] at h

/-! ### Archetype crates and `proveCrate` canaries -/

/-- Expected `Crate` for `id` (`Operand.copy`, `specs := [.ensuresEqArg 1]`). -/
def idCopyEnsuresCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := idCopyBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [.ensuresEqArg 1] }]
  tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
}

/-- Expected `Crate` for unannotated `id` (`Operand.copy`, `specs := []`). -/
def idCopyWfCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := idCopyBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [] }]
  tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
}

/-- Expected `Crate` for `id` (`Operand.move`, `specs := [.ensuresEqArg 1]`). -/
def idMoveEnsuresCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := idMoveBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [.ensuresEqArg 1] }]
  tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
}

/-- Expected `Crate` for unannotated `id` (`Operand.move`, `specs := []`). -/
def idMoveWfCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := idMoveBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [] }]
  tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
}

/-- Expected `Crate` for `alloc_passthrough` (`specs := [.ensuresEqArg 1]`). -/
def allocPassthroughCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := allocPassthroughBody }]
  functions := [{
    name := fnName
    bodyId := ⟨0⟩
    specs := [.ensuresEqArg 1]
  }]
  tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
}

/-- Expected `Crate` for unannotated `alloc_passthrough` (`specs := []`). -/
def allocPassthroughWfCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := allocPassthroughBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [] }]
  tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
}

/-- Expected `Crate` for concrete PME caller `f`. -/
def pmeConcreteTransmuteCrate (fnName : String) : Crate := {
  bodies := [
    { id := ⟨0⟩, body := sizeEqConstBody },
    { id := ⟨1⟩, body := (transmuteCheckedBody ⟨0⟩) },
    { id := ⟨2⟩, body := (concreteTransmuteCallerBody ⟨1⟩ .usize) }
  ]
  functions := [{ name := fnName, bodyId := ⟨2⟩ }]
  tcb := [TCBItem.rustcLowering fnName ⟨2⟩]
}

/-- Expected `Crate` for inline-const PME `inline_const_transmute`. -/
def inlineConstPmeCrate (fnName : String) : Crate := {
  bodies := [
    { id := ⟨0⟩, body := (sizeEqConstBodyAt .usize .usize) },
    { id := ⟨1⟩, body := (inlineConstTransmuteBody ⟨0⟩) }
  ]
  functions := [{ name := fnName, bodyId := ⟨1⟩ }]
  tcb := [TCBItem.rustcLowering fnName ⟨1⟩]
}

/-- Expected `Crate` for the 3-function `NonZeroUsize` library crate. -/
def nonzeroLibraryCrate (fn1Name fn2Name fn3Name : String) : Crate := {
  adts := [nonZeroAdtDecl 0 .transparent]
  bodies := [
    { id := ⟨0⟩, body := (makeNonZeroBodyAt 0) },
    { id := ⟨1⟩, body := (newUncheckedBodyAt 0) },
    { id := ⟨2⟩, body := (getUncheckedNonZeroBodyAt 0 false) }
  ]
  functions := [
    { name := fn1Name, bodyId := ⟨0⟩ },
    { name := fn2Name
      bodyId := ⟨1⟩
      requires := newUncheckedRequires },
    { name := fn3Name, bodyId := ⟨2⟩ }
  ]
  tcb := [
    TCBItem.rustcLowering fn1Name ⟨0⟩,
    TCBItem.rustcLowering fn2Name ⟨1⟩,
    TCBItem.rustcLowering fn3Name ⟨2⟩
  ]
}

/-- Expected `Crate` for `#[repr(transparent)]` struct transmute. -/
def transWrapTransmuteCrate (fnName : String) : Crate := {
  adts := [reprTransparentWrapAdtDecl]
  bodies := [{ id := ⟨0⟩, body := (adtTransmuteBody 0) }]
  functions := [{ name := fnName, bodyId := ⟨0⟩ }]
  tcb := [TCBItem.rustcLowering fnName ⟨0⟩]
}

/-- Expected `Crate` for `#[repr(Rust)]` struct transmute with
`TCBItem.pinnedCompilerCoupled` waiver. -/
def rustWrapPinnedCrate (fnName : String) : Crate := {
  adts := [reprRustWrapAdtDecl]
  bodies := [{ id := ⟨0⟩, body := (adtTransmuteBody 0) }]
  functions := [{ name := fnName, bodyId := ⟨0⟩ }]
  tcb := [
    TCBItem.rustcLowering fnName ⟨0⟩,
    TCBItem.pinnedCompilerCoupled fnName ⟨0⟩ "test"
  ]
}

/-- Expected `Crate` for `#[repr(Rust)]` struct transmute with a compile-time
size guard and `TCBItem.compileTimeGuard` waiver. -/
def rustWrapGuardedCrate (fnName : String) : Crate := {
  adts := [reprRustWrapAdtDecl]
  bodies := [
    { id := ⟨0⟩, body := (sizeEqConstBodyAt (.adt 0) .usize) },
    { id := ⟨1⟩, body := (capturedGuardedAdtTransmuteBody ⟨0⟩ 0) }
  ]
  functions := [{ name := fnName, bodyId := ⟨1⟩ }]
  tcb := [
    TCBItem.rustcLowering fnName ⟨1⟩,
    TCBItem.compileTimeGuard fnName ⟨1⟩
  ]
}

/-- Canary confirming that `proveCrate` discharges all twelve verified crate
archetypes via `rfl` kernel reduction. -/
theorem canary_proveCrate_dispatches_all_archetypes :
    CrateTheorem (idCopyEnsuresCrate "id") ∧
    CrateTheorem (idCopyWfCrate "id") ∧
    CrateTheorem (idMoveEnsuresCrate "id") ∧
    CrateTheorem (idMoveWfCrate "id") ∧
    CrateTheorem (allocPassthroughCrate "alloc_passthrough") ∧
    CrateTheorem (allocPassthroughWfCrate "alloc_passthrough") ∧
    CrateTheorem (pmeConcreteTransmuteCrate "f") ∧
    CrateTheorem (inlineConstPmeCrate "inline_const_transmute") ∧
    CrateTheorem (nonzeroLibraryCrate
      "make_nonzero" "new_unchecked" "get_unchecked") ∧
    CrateTheorem (transWrapTransmuteCrate "transparent_transmute") ∧
    CrateTheorem (rustWrapPinnedCrate "unguarded_transmute") ∧
    CrateTheorem (rustWrapGuardedCrate "guarded_transmute") :=
  ⟨proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl⟩

/-- Canary: demand-driven body lookup in `Crate.bodies` allows `proveCrate` to
verify a crate whose `bodies` table also contains an unreferenced helper body
with unmodeled types, statements, and terminators. -/
def unsupportedHelperBody : MirBody where
  argTys := [.unmodeled]
  retTy := .unmodeled
  localCount := 2
  blocks := [{
    stmts := [.coverage]
    terminator := .inlineAsm
  }]

def crateWithUncalledUnsupportedBody : Crate := {
  bodies := [
    { id := ⟨10⟩, body := idCopyBody },
    { id := ⟨99⟩, body := unsupportedHelperBody }
  ]
  functions := [{ name := "id", bodyId := ⟨10⟩, specs := [.ensuresEqArg 1] }]
  tcb := [TCBItem.rustcLowering "id" ⟨10⟩]
}

theorem canary_proveCrate_ignores_uncalled_unsupported_body :
    CrateTheorem crateWithUncalledUnsupportedBody :=
  proveCrate _ rfl

/-- Canary: `proveCrate` normalizes `Stmt.nop` and multi-hop forwarding `goto`
chains via `lowerBody` before discharging `CrateTheorem`. -/
def idCopyWithNopBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [{
    stmts := [.nop, .assign (locPlace 0) (.use (.copy (locPlace 1))), .nop]
    terminator := .return_
  }]

def crateWithNopInIdBody : Crate := {
  bodies := [{ id := ⟨0⟩, body := idCopyWithNopBody }]
  functions := [{ name := "id", bodyId := ⟨0⟩, specs := [.ensuresEqArg 1] }]
  tcb := [TCBItem.rustcLowering "id" ⟨0⟩]
}

theorem canary_proveCrate_lowers_nop_in_id :
    CrateTheorem crateWithNopInIdBody :=
  proveCrate _ rfl

end Anneal
