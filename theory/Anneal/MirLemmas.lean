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

/-!
# MIR Meta-Theorems, PME & Library Verification Lemmas, and Adequacy Canaries

This module proves:
1. Structural non-vacuity properties (`TotalStep`, `InhabitedDemonic`) of
   `Trusted.MirMachine` and admissibility of `defaultAdtInv` and
   `nonZeroAdtInv`.
2. Symbolic small-step execution helpers (`reachesPrefix_of_step`,
   `reachesPrefix_of_terminated`, `ExecNormal`, `ExecFail`,
   `retLibInv_of_ensuresEqArg1`).
3. Verification lemmas for the `pub fn id(x: usize) -> usize { x }` vertical
   slice discharging `Trusted.CrateTheorem`.
4. Verification lemmas for Post-Monomorphization Error (PME) size-checked
   transmutation (`sizeEqConstBody`, `transmuteCheckedBody`,
   `outerTransmuteBody`, `swappedOuterTransmuteBody`), unconditional
   `MirLang.WellFormed` for PME-gated functions, and the negative adequacy
   canary proving that removing the PME (`transmuteUncheckedBody`) is rejected
   (`¬ CrateTheorem`).
5. Verification lemmas for the `NonZeroUsize` library verification contract
   (`makeNonZeroBody`, `newUncheckedBody`, `getUncheckedNonZeroBody`) and
   negative adequacy canaries (`buggyZeroBody`, public-safe field rejection).
6. Surface 3 adequacy canaries covering reference lifetime/depth tracking,
   multi-field ADTs, cross-frame reference forwarding, and `Terminator.call1`
   arity/escape checks.
-/

namespace Anneal

open Trusted

/-!
## 1. Structural Machine Meta-Theorems (`TotalStep`, `InhabitedDemonic`)
-/

/-- `MirMachine adts` is total: every `(body, s)` pair steps to
    `evalMirStep adts body s`. -/
theorem mirMachine_total (adts : List AdtDecl := []) :
    TotalStep (MirMachine adts) :=
  fun body s => ⟨evalMirStep adts body s, rfl⟩

theorem silent_choice_inhabited {s' : MirState} {branches : MirState → Prop}
    (h : StepResult.choice (Obs := Empty) (Val := MirVal) branches =
      .silent s') :
    ∃ s₂, branches s₂ := by
  injection h with hbr
  subst hbr
  exact ⟨s', rfl⟩

theorem choice_inhabited_of_if_failed {P : Prop} [Decidable P]
    {a : StepResult MirState Empty MirVal} {branches : MirState → Prop}
    (ha : StepResult.choice branches = a → ∃ s', branches s') :
    StepResult.choice branches = (if P then a else .failed) →
    ∃ s', branches s' := by
  cases ‹Decidable P› with
  | isFalse _ => intro h; cases h
  | isTrue _ => exact ha

theorem choice_inhabited_of_if_failed_left {P : Prop} [Decidable P]
    {b : StepResult MirState Empty MirVal} {branches : MirState → Prop}
    (hb : StepResult.choice branches = b → ∃ s', branches s') :
    StepResult.choice branches = (if P then .failed else b) →
    ∃ s', branches s' := by
  cases ‹Decidable P› with
  | isFalse _ => exact hb
  | isTrue _ => intro h; cases h

theorem evalMirStmt_choice_inhabited (active : MirBody) (s : MirState)
    (stmt : Stmt) (branches : MirState → Prop) :
    StepResult.choice branches = evalMirStmt active s stmt →
    ∃ s', branches s' := by
  cases stmt with
  | assign dst rv =>
    cases rv with
    | use op =>
      dsimp [evalMirStmt]
      refine choice_inhabited_of_if_failed ?_
      cases evalOperand active.localCount s.locals op with
      | none => intro h; cases h
      | some _ => intro h; exact silent_choice_inhabited h
    | binaryOp op lhs rhs =>
      dsimp [evalMirStmt]
      refine choice_inhabited_of_if_failed ?_
      cases evalOperand active.localCount s.locals lhs with
      | none => intro h; cases h
      | some p1 =>
        dsimp
        cases evalOperand active.localCount p1.2 rhs with
        | none => intro h; cases h
        | some p2 =>
          dsimp
          cases evalBinOp op p1.1 p2.1 with
          | none => intro h; cases h
          | some _ => intro h; exact silent_choice_inhabited h
    | aggregate adtId op =>
      dsimp [evalMirStmt]
      refine choice_inhabited_of_if_failed ?_
      cases evalOperand active.localCount s.locals op with
      | none => intro h; cases h
      | some _ => intro h; exact silent_choice_inhabited h
    | field0 src =>
      dsimp [evalMirStmt]
      refine choice_inhabited_of_if_failed ?_
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v with
        | adt _ _ => intro h; exact silent_choice_inhabited h
        | _ => intro h; cases h
    | ref src =>
      dsimp [evalMirStmt]
      refine choice_inhabited_of_if_failed ?_
      cases s.locals src.index with
      | none => intro h; cases h
      | some _ => intro h; exact silent_choice_inhabited h
    | reborrow src =>
      dsimp [evalMirStmt]
      refine choice_inhabited_of_if_failed ?_
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v with
        | ref depth gen target =>
          dsimp
          cases resolveRef s depth gen target with
          | none => intro h; cases h
          | some _ => intro h; exact silent_choice_inhabited h
        | _ => intro h; cases h
    | copyDeref src =>
      dsimp [evalMirStmt]
      refine choice_inhabited_of_if_failed ?_
      cases s.locals src.index with
      | none => intro h; cases h
      | some v =>
        cases v with
        | ref depth gen target =>
          dsimp
          cases resolveRef s depth gen target with
          | none => intro h; cases h
          | some _ => intro h; exact silent_choice_inhabited h
        | _ => intro h; cases h
  | storageLive _ =>
    dsimp [evalMirStmt]
    exact choice_inhabited_of_if_failed silent_choice_inhabited
  | storageDead _ =>
    dsimp [evalMirStmt]
    exact choice_inhabited_of_if_failed silent_choice_inhabited
  | nop => intro h; exact silent_choice_inhabited h

theorem evalMirTerminator_choice_inhabited (adts : List AdtDecl)
    (active : MirBody) (s : MirState) (term : Terminator)
    (branches : MirState → Prop) :
    StepResult.choice branches = evalMirTerminator adts active s term →
    ∃ s', branches s' := by
  cases term with
  | return_ =>
    dsimp [evalMirTerminator]
    refine choice_inhabited_of_if_failed ?_
    cases s.locals 0 with
    | none => intro h; cases h
    | some retVal =>
      dsimp
      refine choice_inhabited_of_if_failed_left ?_
      cases s.stack with
      | nil => intro h; cases h
      | cons _ _ =>
        dsimp
        exact choice_inhabited_of_if_failed silent_choice_inhabited
  | goto _ =>
    dsimp [evalMirTerminator]
    exact choice_inhabited_of_if_failed silent_choice_inhabited
  | unreachable => intro h; cases h
  | panic => intro h; cases h
  | switchInt discr _ _ =>
    dsimp [evalMirTerminator]
    cases evalOperand active.localCount s.locals discr with
    | none => intro h; cases h
    | some p =>
      cases p with
      | mk v _ =>
        cases v with
        | bool b =>
          cases b <;>
            (dsimp; exact choice_inhabited_of_if_failed silent_choice_inhabited)
        | _ => intro h; cases h
  | callSizeOf _ ty _ =>
    dsimp [evalMirTerminator]
    refine choice_inhabited_of_if_failed ?_
    cases evalTyByteSize adts s.tySizes ty with
    | none => intro h; cases h
    | some _ => intro h; exact silent_choice_inhabited h
  | callTransmuteCopy _ srcTy dstTy op _ =>
    dsimp [evalMirTerminator]
    refine choice_inhabited_of_if_failed ?_
    cases evalOperand active.localCount s.locals op with
    | none => intro h; cases h
    | some p =>
      dsimp
      cases evalTransmuteCopy adts { s with locals := p.2 }
          srcTy dstTy p.1 with
      | none => intro h; cases h
      | some _ => intro h; exact silent_choice_inhabited h
  | call1 _ _ arg _ _ =>
    dsimp [evalMirTerminator]
    refine choice_inhabited_of_if_failed ?_
    cases evalOperand active.localCount s.locals arg with
    | none => intro h; cases h
    | some _ => intro h; exact silent_choice_inhabited h

/-- `MirMachine adts` has no empty choice nodes (`evalMirStep` only emits
    `.silent` choices, which are uniquely inhabited). -/
theorem mirMachine_inhabited (adts : List AdtDecl := []) :
    InhabitedDemonic (MirMachine adts) := by
  intro body s branches hstep
  have h : StepResult.choice branches = evalMirStep adts body s := hstep
  dsimp [evalMirStep] at h
  revert h
  cases lookupAt (s.curBody.getD body).blocks s.block with
  | none => intro h; cases h
  | some bb =>
    intro h
    dsimp at h
    revert h
    cases lookupAt bb.stmts s.stmtIdx with
    | none =>
      exact choice_inhabited_of_if_failed
        (evalMirTerminator_choice_inhabited adts (s.curBody.getD body) s
          bb.terminator branches)
    | some stmt =>
      exact evalMirStmt_choice_inhabited (s.curBody.getD body) s stmt
        branches

/-- Unconditional `L.Spec post` refines `L.SpecOn pre post` for any
    precondition `pre`. -/
theorem spec_le_specOn {SemObs : Type} {L : Language SemObs}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ L.SpecOn pre post :=
  specOn_mono_pre post (fun _ _ => True.intro)

/-- Postcondition `EnsuresEqArg argLocal adts` refines
    `(MirLang adts).WellFormed`. -/
theorem ensuresEqArg_le_wellFormed (argLocal : Nat)
    (adts : List AdtDecl := []) :
    EnsuresEqArg argLocal adts ≤ (MirLang adts).WellFormed :=
  spec_le_wellFormed _

/-- Postcondition `EnsuresEqArg argLocal adts` refines
    `(MirLang adts).WellFormedOn pre` for any precondition `pre`. -/
theorem ensuresEqArg_le_wellFormedOn (argLocal : Nat)
    (adts : List AdtDecl := []) (pre : MirState → Prop) :
    EnsuresEqArg argLocal adts ≤ (MirLang adts).WellFormedOn pre :=
  Preorder.le_trans (ensuresEqArg_le_wellFormed argLocal adts)
    (wellFormed_le_wellFormedOn (L := MirLang adts) pre)

/-- Postcondition `EnsuresRetLibInv adts adtInv retTy pre` refines
    `(MirLang adts).WellFormedOn pre`. -/
theorem ensuresRetLibInv_le_wellFormedOn (adts : List AdtDecl := [])
    (adtInv : AdtInv) (retTy : MirTy) (pre : MirState → Prop) :
    EnsuresRetLibInv adts adtInv retTy pre ≤ (MirLang adts).WellFormedOn pre :=
  specOn_le_wellFormedOn (L := MirLang adts) pre _

/-- `defaultAdtInv` is admissible for an empty list of ADT declarations. -/
theorem defaultAdtInv_admissible :
    AdmissibleAdtInv [] defaultAdtInv :=
  ⟨True.intro, True.intro, fun _ h => by cases h⟩

/-!
## 2. Symbolic Small-Step Execution Helpers
-/

theorem initEntryState_argsMatch {adts : List AdtDecl} {body : MirBody}
    {s : MirState} (h : initEntryState adts body s) :
    argsMatchLocals adts body.localCount s body.argTys :=
  h.2.2.2.2.2.2.2.2.2

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

theorem reachesPrefix_of_step
    {adts : List AdtDecl} {body : MirBody} {s s' : MirState} {n : Nat}
    {tr : List Empty} {out : PrefixOutcome MirState MirVal}
    (hstep : evalMirStep adts body s = .silent s')
    (hreach : ReachesPrefix (MirStep adts) body n s tr out) :
    out = .running s ∨
      ∃ n' tr', ReachesPrefix (MirStep adts) body n' s' tr' out := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice n' _ s₂ branches _ _ h1 hbr hr =>
    have h1' : StepResult.choice branches = evalMirStep adts body s := h1
    rw [hstep] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    subst hbr
    exact Or.inr ⟨n', tr, hr⟩
  | emptyChoice _ _ branches h1 hemp =>
    have h1' : StepResult.choice branches = evalMirStep adts body s := h1
    rw [hstep] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    exact False.elim (hemp ⟨s', rfl⟩)
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep adts body s := h1
    rw [hstep] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : _ = evalMirStep adts body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

theorem reachesPrefix_of_terminated
    {adts : List AdtDecl} {body : MirBody} {s : MirState} {n : Nat}
    {tr : List Empty} {out : PrefixOutcome MirState MirVal}
    {term : TerminationKind MirVal}
    (hstep : evalMirStep adts body s = .terminated term)
    (hreach : ReachesPrefix (MirStep adts) body n s tr out) :
    out = .running s ∨ out = .terminated term := by
  cases hreach with
  | zero => exact Or.inl rfl
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep adts body s := h1
    rw [hstep] at h1'; cases h1'
  | emptyChoice _ _ _ h1 _ =>
    have h1' : _ = evalMirStep adts body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ t h1 =>
    have h1' : StepResult.terminated t = evalMirStep adts body s := h1
    rw [hstep] at h1'
    injection h1' with ht
    subst ht
    exact Or.inr rfl
  | failed _ _ h1 =>
    have h1' : _ = evalMirStep adts body s := h1
    rw [hstep] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstep.symm⟩)

/-- Combined prefix-safety and normal-return postcondition predicate on a
    `PrefixOutcome`. -/
def SafeAndEnsures (P : MirVal → Prop)
    (out : PrefixOutcome MirState MirVal) : Prop :=
  out.isSafe ∧ ∀ ret, out = .terminated (.normal ret) → P ret

theorem reachesPrefix_safeAndEnsures_of_step
    {adts : List AdtDecl} {body : MirBody} {s s' : MirState} {n : Nat}
    {tr : List Empty} {out : PrefixOutcome MirState MirVal} {P : MirVal → Prop}
    (hstep : evalMirStep adts body s = .silent s')
    (hreach : ReachesPrefix (MirStep adts) body n s tr out)
    (hnext : ∀ n' tr', ReachesPrefix (MirStep adts) body n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_safeAndEnsures_of_normal
    {adts : List AdtDecl} {body : MirBody} {s : MirState} {n : Nat}
    {tr : List Empty} {out : PrefixOutcome MirState MirVal} {P : MirVal → Prop}
    {v : MirVal}
    (hstep : evalMirStep adts body s = .terminated (.normal v))
    (hreach : ReachesPrefix (MirStep adts) body n s tr out)
    (hPv : P v) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, fun _ h => by cases h⟩
  | inr hterm =>
    subst hterm
    refine ⟨True.intro, ?_⟩
    intro ret hret
    injection hret with h1
    injection h1 with h2
    subst h2
    exact hPv

theorem reachesPrefix_not_normal_of_step
    {adts : List AdtDecl} {body : MirBody} {s s' : MirState} {n : Nat}
    {tr : List Empty} {v : MirVal}
    (hstep : evalMirStep adts body s = .silent s')
    (hreach :
      ReachesPrefix (MirStep adts) body n s tr (.terminated (.normal v)))
    (hnext : ∀ n' tr',
      ReachesPrefix (MirStep adts) body n' s' tr' (.terminated (.normal v)) →
      False) :
    False := by
  cases reachesPrefix_of_step hstep hreach with
  | inl hrun => cases hrun
  | inr hex =>
    cases hex with
    | intro n' htr =>
      cases htr with
      | intro tr' hr' => exact hnext n' tr' hr'

theorem reachesPrefix_not_normal_of_unwind
    {adts : List AdtDecl} {body : MirBody} {s : MirState} {n : Nat}
    {tr : List Empty} {v : MirVal}
    (hstep : evalMirStep adts body s = .terminated .unwind)
    (hreach : ReachesPrefix (MirStep adts) body n s tr
      (.terminated (.normal v))) :
    False := by
  cases reachesPrefix_of_terminated hstep hreach with
  | inl hrun => cases hrun
  | inr hunw => cases hunw

theorem reachesPrefix_not_normal_of_failed
    {adts : List AdtDecl} {body : MirBody} {s : MirState} {n : Nat}
    {tr : List Empty} {v : MirVal}
    (hstep : evalMirStep adts body s = .failed)
    (hreach : ReachesPrefix (MirStep adts) body n s tr
      (.terminated (.normal v))) :
    False := by
  cases hreach with
  | step _ _ _ obs _ _ _ _ => nomatch obs
  | choice _ _ _ _ _ _ h1 _ _ =>
    have h1' : _ = evalMirStep adts body s := h1
    rw [hstep] at h1'; cases h1'
  | terminated _ _ _ h1 =>
    have h1' : _ = evalMirStep adts body s := h1
    rw [hstep] at h1'; cases h1'

/-- Inductive normal-termination symbolic execution relation for a `MirBody`:
    witnesses a finite sequence of `.silent` transitions ending in
    `.terminated (.normal v)` with `P v`. -/
inductive ExecNormal (adts : List AdtDecl := []) (body : MirBody) :
    MirState → (MirVal → Prop) → Prop where
  | step {s s' : MirState} {P : MirVal → Prop} :
      evalMirStep adts body s = .silent s' →
      ExecNormal adts body s' P →
      ExecNormal adts body s P
  | normal {s : MirState} {v : MirVal} {P : MirVal → Prop} :
      evalMirStep adts body s = .terminated (.normal v) →
      P v →
      ExecNormal adts body s P

/-- Weaken the return-value predicate `P` of `ExecNormal`. -/
theorem ExecNormal.map {adts : List AdtDecl} {body : MirBody}
    {s : MirState} {P Q : MirVal → Prop} (himp : ∀ v, P v → Q v)
    (hexec : ExecNormal adts body s P) :
    ExecNormal adts body s Q := by
  induction hexec with
  | step hstep _ ih => exact .step hstep (ih himp)
  | normal hterm hp => exact .normal hterm (himp _ hp)

/-- Inductive unwind-termination symbolic execution relation for a `MirBody`:
    witnesses a finite sequence of `.silent` transitions ending in
    `.terminated .unwind`. -/
inductive ExecUnwind (adts : List AdtDecl := []) (body : MirBody) :
    MirState → Prop where
  | step {s s' : MirState} :
      evalMirStep adts body s = .silent s' →
      ExecUnwind adts body s' →
      ExecUnwind adts body s
  | unwind {s : MirState} :
      evalMirStep adts body s = .terminated .unwind →
      ExecUnwind adts body s

/-- No prefix from an `ExecUnwind` state can terminate normally. -/
theorem execUnwind_not_normal {adts : List AdtDecl} {body : MirBody}
    {s : MirState} (hexec : ExecUnwind adts body s) :
    ∀ {n : Nat} {tr : List Empty} {v : MirVal},
      ReachesPrefix (MirStep adts) body n s tr (.terminated (.normal v)) →
      False := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr v hreach
    exact reachesPrefix_not_normal_of_step hstep hreach (fun _ _ hr => ih hr)
  | unwind hterm =>
    intro n tr v hreach
    exact reachesPrefix_not_normal_of_unwind hterm hreach

/-- Every prefix reachable from a state satisfying `ExecNormal adts body s P`
    is safe and satisfies `P` on normal termination. -/
theorem execNormal_safeAndEnsures {adts : List AdtDecl} {body : MirBody}
    {s : MirState} {P : MirVal → Prop}
    (hexec : ExecNormal adts body s P) :
    ∀ {n : Nat} {tr : List Empty} {out : PrefixOutcome MirState MirVal},
      ReachesPrefix (MirStep adts) body n s tr out →
      SafeAndEnsures P out := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_step hstep hreach
      (fun _ _ hr => ih hr)
  | normal hterm hp =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_normal hterm hreach hp

/-- `ExecNormal adts body s P` implies the existence of a finite prefix reaching
    `.terminated (.normal v)` with `P v`. -/
theorem execNormal_reaches {adts : List AdtDecl} {body : MirBody}
    {s : MirState} {P : MirVal → Prop}
    (hexec : ExecNormal adts body s P) :
    ∃ n v,
      ReachesPrefix (MirStep adts) body n s [] (.terminated (.normal v)) ∧
      P v := by
  induction hexec with
  | step hstep _ ih =>
    cases ih with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        exact ⟨n + 1, v,
          .choice n _ _ _ [] (.terminated (.normal v)) hstep.symm rfl hv.1,
          hv.2⟩
  | normal hterm hp =>
    exact ⟨1, _, .terminated 0 _ (.normal _) hterm.symm, hp⟩

/-- `ExecNormal` implies conditional specification refinement `SpecOn`. -/
theorem execNormal_specOn {adts : List AdtDecl} {body : MirBody}
    {pre : MirState → Prop} {P : MirState → MirVal → Prop}
    (h_exec : ∀ s, initMirState adts body s → pre s →
      ExecNormal adts body s (P s)) :
    MirSem adts body ≤
      (MirLang adts).SpecOn pre (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) := by
  refine eventualBehaviorOf_le_normalSpecOn (M := MirMachine adts) ?_
  intro init _ _ out hpre hpfx
  have hsafe := execNormal_safeAndEnsures (h_exec init hpfx.1 hpre) hpfx.2
  exact ⟨hsafe.1, hsafe.2⟩

/-- `ExecNormal` implies unconditional specification refinement `Spec`. -/
theorem execNormal_spec {adts : List AdtDecl} {body : MirBody}
    {P : MirState → MirVal → Prop}
    (h_exec : ∀ s, initMirState adts body s →
      ExecNormal adts body s (P s)) :
    MirSem adts body ≤
      (MirLang adts).Spec (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) :=
  execNormal_specOn (fun s hinit _ => h_exec s hinit)

/-- Discharge the baseline `(MirLang adts).Verified pre (fun _ _ => True) body`
    obligation from `ExecNormal`. -/
theorem execNormal_verified {adts : List AdtDecl} {body : MirBody}
    {pre : MirState → Prop} {P : MirState → MirVal → Prop}
    (h_pre_init : ∀ s, pre s → initMirState adts body s)
    (h_inh : ∃ s₀, pre s₀)
    (h_exec : ∀ s, pre s → ExecNormal adts body s (P s)) :
    (MirLang adts).Verified pre (fun _ _ => True) body := by
  have h_wf : MirSem adts body ≤ (MirLang adts).WellFormedOn pre := by
    refine
      (eventualBehaviorOf_le_wellFormedOn_iff (M := MirMachine adts)).mpr ?_
    intro s n tr out hpre _ hreach
    exact (execNormal_safeAndEnsures (h_exec s hpre) hreach).1
  refine ⟨Or.inl h_inh, ?_, ?_⟩
  · intro s hpre
    have hinit : initMirState adts body s := h_pre_init s hpre
    have hdef : (MirSem adts body s).defined := (h_wf s hpre).1
    cases execNormal_reaches (h_exec s hpre) with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        exact ⟨hdef, .terminated [] (.normal v), hinit, n, hv.1⟩
  · intro s hpre
    refine ⟨(h_wf s hpre).1, fun _ _ => True.intro⟩

/-- Combined per-function verification and return-invariant obligation for a
    public `CapturedFn`. -/
abbrev FnVerifiedAndRetInv (adts : List AdtDecl := []) (adtInv : AdtInv)
    (fn : CapturedFn) : Prop :=
  (MirLang adts).Verified (fn.effectivePre adts adtInv) (fun _ _ => True)
    fn.prog ∧
  MirSem adts fn.prog ≤
    EnsuresRetLibInv adts adtInv fn.prog.retTy (fn.effectivePre adts adtInv)

/-- Discharge `FnVerifiedAndRetInv` directly from `h_inh` and `ExecNormal`. -/
theorem execNormal_fnVerifiedAndRetInv {adts : List AdtDecl} {adtInv : AdtInv}
    (fn : CapturedFn)
    (h_inh : ∃ s₀, fn.effectivePre adts adtInv s₀)
    (h_exec : ∀ s, fn.effectivePre adts adtInv s →
      ExecNormal adts fn.prog s (fun ret =>
        ret.satisfiesInv adts adtInv s fn.prog.retTy)) :
    FnVerifiedAndRetInv adts adtInv fn :=
  ⟨execNormal_verified (fun _ h => h.1) h_inh h_exec,
   execNormal_specOn (fun s _ h => h_exec s h)⟩

/-- Inductive failure symbolic execution relation for negative canaries:
    witnesses a finite sequence of `.silent` transitions ending in `.failed`. -/
inductive ExecFail (adts : List AdtDecl := []) (body : MirBody) :
    MirState → Prop where
  | step {s s' : MirState} :
      evalMirStep adts body s = .silent s' →
      ExecFail adts body s' →
      ExecFail adts body s
  | fail {s : MirState} :
      evalMirStep adts body s = .failed →
      ExecFail adts body s

theorem execFail_reaches {adts : List AdtDecl} {body : MirBody}
    {s : MirState} (hexec : ExecFail adts body s) :
    ∃ n, ReachesPrefix (MirStep adts) body n s [] .failed := by
  induction hexec with
  | step hstep _ ih =>
    cases ih with
    | intro n hr =>
      exact ⟨n + 1, .choice n _ _ _ [] .failed hstep.symm rfl hr⟩
  | fail hfail =>
    exact ⟨1, .failed 0 _ hfail.symm⟩

/-- Any single-argument function (`body.argTys = [ty]`) that satisfies
    `EnsuresEqArg 1 adts` automatically satisfies
    `EnsuresRetLibInv adts defaultAdtInv ty pre` for any precondition `pre`,
    without repeating symbolic execution. -/
theorem retLibInv_of_ensuresEqArg1
    {adts : List AdtDecl} {body : MirBody} {ty : MirTy}
    (hArgs : body.argTys = [ty])
    (hEns : MirSem adts body ≤ EnsuresEqArg 1 adts)
    (pre : MirState → Prop) :
    MirSem adts body ≤ EnsuresRetLibInv adts defaultAdtInv ty pre := by
  intro s _
  cases hEns s True.intro with
  | intro hdef hval =>
    refine ⟨hdef, fun out hpfx tr ret hret => ?_⟩
    have hloc1 : s.locals 1 = some ret := hval out hpfx tr ret hret
    have hargs := initEntryState_argsMatch hpfx.1.1
    rw [hArgs] at hargs
    cases hargs.1 with
    | intro v hv =>
      have heq : some v = some ret := hv.1.symm.trans hloc1
      injection heq with hvret
      subst hvret
      exact hv.2

/-!
## 3. `pub fn id(x: usize) -> usize { x }` Verification Lemmas
-/

/-- Canonical `Runtime(PostCleanup)` MIR body for
    `pub fn id(x: usize) -> usize { x }` using `Operand.copy`:
    ```text
    bb0: {
        _0 = copy _1;
        return;
    }
    ``` -/
def idCopyBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
      terminator := .return_ }
  ]

/-- Canonical `Runtime(PostCleanup)` MIR body for
    `pub fn id(x: usize) -> usize { x }` using `Operand.move`:
    ```text
    bb0: {
        _0 = move _1;
        return;
    }
    ``` -/
def idMoveBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.move ⟨1⟩))]
      terminator := .return_ }
  ]

/-- Canonical entry state for a single-`usize`-argument function (`_1 = 0`). -/
def singleArgUsizeInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.usize 0))
  block := 0
  stmtIdx := 0

/-- `idCopyBody` executes to normal termination returning the initial `_1`. -/
theorem idCopyBody_execNormal (s : MirState)
    (hinit : initMirState [] idCopyBody s) :
    ExecNormal [] idCopyBody s (fun ret =>
      s.locals 1 = some ret ∧
      ret.satisfiesInv [] defaultAdtInv s .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.satisfiesInv [] defaultAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        .usize := hv.2
      cases v with
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        apply ExecNormal.step
        · change evalMirStmt idCopyBody _ (.assign ⟨0⟩ (.use (.copy ⟨1⟩))) = _
          dsimp only [evalMirStmt, evalOperand, idCopyBody]
          rw [hv1]
          rfl
        · exact .normal rfl ⟨hv1, True.intro⟩

/-- `idCopyBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idCopyBody_satisfies_ensures :
    MirSem [] idCopyBody ≤ EnsuresEqArg 1 :=
  execNormal_spec (fun s hinit =>
    (idCopyBody_execNormal s hinit).map (fun _ h => h.1))

/-- `idCopyBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idCopyBody_satisfies_wellFormed :
    MirSem [] idCopyBody ≤ (MirLang []).WellFormed :=
  Preorder.le_trans idCopyBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idCopyBody` satisfies `EnsuresRetLibInv [] defaultAdtInv .usize pre` for
    any precondition `pre`. -/
theorem idCopyBody_satisfies_retLibInv (pre : MirState → Prop) :
    MirSem [] idCopyBody ≤ EnsuresRetLibInv [] defaultAdtInv .usize pre :=
  retLibInv_of_ensuresEqArg1 rfl idCopyBody_satisfies_ensures pre

/-- `idCopyBody` satisfies `FnVerifiedAndRetInv` for any `specs`. -/
theorem idCopyBody_verified (fnName : String)
    (specs : List (MirLang []).Behavior := []) :
    FnVerifiedAndRetInv [] defaultAdtInv
      { name := fnName, prog := idCopyBody, specs := specs } := by
  have hmono : MonoAdmitted [] (fun _ => 0) idCopyBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState [] idCopyBody singleArgUsizeInitState :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 2, rfl, rfl,
      ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩,
     hmono⟩
  exact execNormal_fnVerifiedAndRetInv
    { name := fnName, prog := idCopyBody, specs := specs }
    ⟨singleArgUsizeInitState, hinit, True.intro,
     ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    (fun s hpre => (idCopyBody_execNormal s hpre.1).map (fun _ h => h.2))

/-- `idMoveBody` executes to normal termination returning the initial `_1`. -/
theorem idMoveBody_execNormal (s : MirState)
    (hinit : initMirState [] idMoveBody s) :
    ExecNormal [] idMoveBody s (fun ret =>
      s.locals 1 = some ret ∧
      ret.satisfiesInv [] defaultAdtInv s .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.satisfiesInv [] defaultAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        .usize := hv.2
      cases v with
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        apply ExecNormal.step
        · change evalMirStmt idMoveBody _ (.assign ⟨0⟩ (.use (.move ⟨1⟩))) = _
          dsimp only [evalMirStmt, evalOperand, idMoveBody]
          rw [hv1]
          rfl
        · exact .normal rfl ⟨hv1, True.intro⟩

/-- `idMoveBody` satisfies `EnsuresEqArg 1`: every reachable prefix is safe and
    any normal return value equals the initial value of `_1`. -/
theorem idMoveBody_satisfies_ensures :
    MirSem [] idMoveBody ≤ EnsuresEqArg 1 :=
  execNormal_spec (fun s hinit =>
    (idMoveBody_execNormal s hinit).map (fun _ h => h.1))

/-- `idMoveBody` satisfies baseline `MirLang.WellFormed`. -/
theorem idMoveBody_satisfies_wellFormed :
    MirSem [] idMoveBody ≤ (MirLang []).WellFormed :=
  Preorder.le_trans idMoveBody_satisfies_ensures (ensuresEqArg_le_wellFormed 1)

/-- `idMoveBody` satisfies `EnsuresRetLibInv [] defaultAdtInv .usize pre` for
    any precondition `pre`. -/
theorem idMoveBody_satisfies_retLibInv (pre : MirState → Prop) :
    MirSem [] idMoveBody ≤ EnsuresRetLibInv [] defaultAdtInv .usize pre :=
  retLibInv_of_ensuresEqArg1 rfl idMoveBody_satisfies_ensures pre

/-- `idMoveBody` satisfies `FnVerifiedAndRetInv` for any `specs`. -/
theorem idMoveBody_verified (fnName : String)
    (specs : List (MirLang []).Behavior := []) :
    FnVerifiedAndRetInv [] defaultAdtInv
      { name := fnName, prog := idMoveBody, specs := specs } := by
  have hmono : MonoAdmitted [] (fun _ => 0) idMoveBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState [] idMoveBody singleArgUsizeInitState :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 2, rfl, rfl,
      ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩,
     hmono⟩
  exact execNormal_fnVerifiedAndRetInv
    { name := fnName, prog := idMoveBody, specs := specs }
    ⟨singleArgUsizeInitState, hinit, True.intro,
     ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    (fun s hpre => (idMoveBody_execNormal s hpre.1).map (fun _ h => h.2))

/-- Generic single-function `CrateTheorem` discharge for an unannotated safe
    function (`specs := []`, `kind := .pubSafe True`). -/
theorem verify_single_fn_wf_crate
    (fnName : String) (body : MirBody)
    {src : String}
    (h_ver : FnVerifiedAndRetInv [] defaultAdtInv
      { name := fnName, prog := body, specs := [] }) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName body]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } :=
  ⟨(by intro h; cases h),
   ⟨True.intro, True.intro⟩,
   defaultAdtInv_admissible,
   True.intro,
   ⟨{ path := "src/lib.rs", contents := src, expected := src }, .head _, rfl⟩,
   ⟨rfl, True.intro⟩,
   ⟨(by intro h; cases h),
    ⟨⟨(by intro h; cases h), True.intro⟩, True.intro, True.intro⟩,
    ⟨True.intro, True.intro⟩,
    ⟨True.intro, True.intro⟩,
    ⟨Or.inl (.head _),
     Or.inr ⟨h_ver.1, h_ver.2, True.intro⟩,
     True.intro⟩⟩,
   True.intro⟩

/-- Generic single-function `CrateTheorem` discharge for a safe function with an
    explicit functional specification `spec`. -/
theorem verify_single_fn_crate
    (fnName : String) (body : MirBody)
    (spec : (MirLang []).Behavior)
    {src : String}
    (h_ver : FnVerifiedAndRetInv [] defaultAdtInv
      { name := fnName, prog := body, specs := [spec] })
    (h_proof : MirSem [] body ≤ spec) :
    CrateTheorem {
      functions := [{ name := fnName, prog := body, specs := [spec] }]
      tcb := [TCBItem.rustcLowering fnName body]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } :=
  ⟨(by intro h; cases h),
   ⟨True.intro, True.intro⟩,
   defaultAdtInv_admissible,
   True.intro,
   ⟨{ path := "src/lib.rs", contents := src, expected := src }, .head _, rfl⟩,
   ⟨rfl, True.intro⟩,
   ⟨(by intro h; cases h),
    ⟨⟨(by intro h; cases h), True.intro⟩, True.intro, True.intro⟩,
    ⟨True.intro, True.intro⟩,
    ⟨True.intro, True.intro⟩,
    ⟨Or.inl (.head _),
     Or.inr ⟨h_ver.1, h_ver.2, h_proof, True.intro⟩,
     True.intro⟩⟩,
   True.intro⟩

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.copy`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_copy_ensures_crate (fnName : String) {src : String} :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := idCopyBody
        specs := [EnsuresEqArg 1]
      }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } :=
  verify_single_fn_crate fnName idCopyBody (EnsuresEqArg 1) (src := src)
    (idCopyBody_verified fnName [EnsuresEqArg 1])
    idCopyBody_satisfies_ensures

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.copy`, `specs := []`). -/
theorem prove_id_copy_wf_crate (fnName : String) {src : String} :
    CrateTheorem {
      functions := [{ name := fnName, prog := idCopyBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idCopyBody]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } :=
  verify_single_fn_wf_crate fnName idCopyBody (src := src)
    (idCopyBody_verified fnName [])

/-- Ready-to-apply `CrateTheorem` witness for `pub fn id` (`Operand.move`,
    `specs := [EnsuresEqArg 1]`). -/
theorem prove_id_move_ensures_crate (fnName : String) {src : String} :
    CrateTheorem {
      functions := [{
        name := fnName
        prog := idMoveBody
        specs := [EnsuresEqArg 1]
      }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } :=
  verify_single_fn_crate fnName idMoveBody (EnsuresEqArg 1) (src := src)
    (idMoveBody_verified fnName [EnsuresEqArg 1])
    idMoveBody_satisfies_ensures

/-- Ready-to-apply `CrateTheorem` witness for unannotated `pub fn id`
    (`Operand.move`, `specs := []`). -/
theorem prove_id_move_wf_crate (fnName : String) {src : String} :
    CrateTheorem {
      functions := [{ name := fnName, prog := idMoveBody, specs := [] }]
      tcb := [TCBItem.rustcLowering fnName idMoveBody]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } :=
  verify_single_fn_wf_crate fnName idMoveBody (src := src)
    (idMoveBody_verified fnName [])

/-!
## 4. Post-Monomorphization Error (PME) Size-Checked Transmute Lemmas
-/

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` constant body for
    `assert!(core::mem::size_of::<Src>() == core::mem::size_of::<Dst>())`
    (shared by both `const ASSERT: () = assert!(...)` and inline
    `const { assert!(...) }`):
    ```text
    bb0: {
        StorageLive(_1);
        StorageLive(_2);
        ConstEvalCounter;
        _2 = std::mem::size_of::<Src>() -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageLive(_3);
        ConstEvalCounter;
        _3 = std::mem::size_of::<Dst>() -> [return: bb2, unwind continue];
    }
    bb2: {
        _1 = Eq(move _2, move _3);
        switchInt(move _1) -> [0: bb4, otherwise: bb3];
    }
    bb3: {
        StorageDead(_3);
        StorageDead(_2);
        _0 = const ();
        StorageDead(_1);
        return;
    }
    bb4: {
        StorageDead(_3);
        StorageDead(_2);
        StorageLive(_4);
        ConstEvalCounter;
        _4 = panic(...) -> unwind continue;
    }
    ``` -/
def sizeEqConstBody : MirBody where
  argTys := []
  retTy := .unit
  localCount := 5
  blocks := [
    { stmts := [.storageLive ⟨1⟩, .storageLive ⟨2⟩, .nop]
      terminator := .callSizeOf ⟨2⟩ (.param 0) ⟨1⟩ },
    { stmts := [.storageLive ⟨3⟩, .nop]
      terminator := .callSizeOf ⟨3⟩ (.param 1) ⟨2⟩ },
    { stmts := [.assign ⟨1⟩ (.binaryOp .eq (.move ⟨2⟩) (.move ⟨3⟩))]
      terminator := .switchInt (.move ⟨1⟩) ⟨4⟩ ⟨3⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .storageDead ⟨2⟩,
        .assign ⟨0⟩ (.use (.constVal .unit)),
        .storageDead ⟨1⟩
      ]
      terminator := .return_ },
    { stmts := [.storageDead ⟨3⟩, .storageDead ⟨2⟩, .storageLive ⟨4⟩, .nop]
      terminator := .panic }
  ]
  requiredConsts := []

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn transmute_checked<Src: Copy, Dst: Copy>(x: Src) -> Dst`:
    ```text
    bb0: {
        StorageLive(_2);
        _2 = const <() as SizeEq<Src, Dst>>::ASSERT;
        StorageDead(_2);
        StorageLive(_3);
        StorageLive(_4);
        _4 = &_1;
        _3 = &(*_4);
        _0 = transmute_copy::<Src, Dst>(move _3) -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageDead(_4);
        StorageDead(_3);
        return;
    }
    ``` -/
def transmuteCheckedBody : MirBody where
  argTys := [.param 0]
  retTy := .param 1
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign ⟨2⟩ (.use (.constVal .unit)),
        .storageDead ⟨2⟩,
        .storageLive ⟨3⟩,
        .storageLive ⟨4⟩,
        .assign ⟨4⟩ (.ref ⟨1⟩),
        .assign ⟨3⟩ (.reborrow ⟨4⟩)
      ]
      terminator :=
        .callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.move ⟨3⟩) ⟨1⟩ },
    { stmts := [.storageDead ⟨4⟩, .storageDead ⟨3⟩]
      terminator := .return_ }
  ]
  requiredConsts := [(sizeEqConstBody, [.param 0, .param 1])]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn outer_transmute<Src: Copy, Dst: Copy>(x: Src) -> Dst` calling
    `transmute_checked::<Src, Dst>(x)`:
    ```text
    bb0: {
        StorageLive(_2);
        _2 = copy _1;
        _0 = transmute_checked::<Src, Dst>(move _2) -> [return: bb1, unwind continue];
    }
    bb1: {
        StorageDead(_2);
        return;
    }
    ``` -/
def outerTransmuteBody : MirBody where
  argTys := [.param 0]
  retTy := .param 1
  localCount := 3
  blocks := [
    { stmts := [.storageLive ⟨2⟩, .assign ⟨2⟩ (.use (.copy ⟨1⟩))]
      terminator :=
        .call1 ⟨0⟩ transmuteCheckedBody (.move ⟨2⟩) ⟨1⟩ [.param 0, .param 1] },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- Generic wrapper body `pub fn swapped_outer<A: Copy, B: Copy>(x: B) -> A`
    calling `transmute_checked::<B, A>(x)` with non-identity type arguments
    `typeArgs := [.param 1, .param 0]`. -/
def swappedOuterTransmuteBody : MirBody where
  argTys := [.param 1]
  retTy := .param 0
  localCount := 3
  blocks := [
    { stmts := [.storageLive ⟨2⟩, .assign ⟨2⟩ (.use (.copy ⟨1⟩))]
      terminator :=
        .call1 ⟨0⟩ transmuteCheckedBody (.move ⟨2⟩) ⟨1⟩ [.param 1, .param 0] },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for an unchecked
    `pub fn transmute_unchecked<Src: Copy, Dst: Copy>(x: Src) -> Dst` that omits
    the PME assertion (`requiredConsts = []`). -/
def transmuteUncheckedBody : MirBody where
  argTys := [.param 0]
  retTy := .param 1
  localCount := 4
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign ⟨3⟩ (.ref ⟨1⟩),
        .assign ⟨2⟩ (.reborrow ⟨3⟩)
      ]
      terminator :=
        .callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.move ⟨2⟩) ⟨1⟩ },
    { stmts := [.storageDead ⟨3⟩, .storageDead ⟨2⟩]
      terminator := .return_ }
  ]
  requiredConsts := []

/-- Constructive CTFE success of `sizeEqConstBody` whenever
    `tySizes 0 = tySizes 1`. -/
theorem sizeEqConstBody_constSucceeds_of_eq (tySizes : Nat → Nat)
    (heq : tySizes 0 = tySizes 1) :
    ConstSucceeds [] tySizes sizeEqConstBody := by
  refine ⟨rfl, ?_⟩
  have hdec : decide (tySizes 0 = tySizes 1) = true := decide_eq_true heq
  have hexec : ExecNormal [] sizeEqConstBody (constEntryState tySizes)
      (fun v => v = .unit) := by
    refine .step rfl (.step rfl (.step rfl (.step rfl
      (.step rfl (.step rfl (.step rfl ?_))))))
    dsimp only [constEntryState, updateLocal, bumpGen]
    refine .step rfl ?_
    apply ExecNormal.step
    · dsimp only [evalMirStep, lookupAt, Option.getD, List.length,
        evalMirTerminator, evalOperand, sizeEqConstBody, updateLocal]
      rw [hdec]
      rfl
    · exact .step rfl (.step rfl (.step rfl (.step rfl (.normal rfl rfl))))
  cases execNormal_reaches hexec with
  | intro n hn =>
    cases hn with
    | intro v hv => exact ⟨n, v, hv.1⟩

/-- Special case: `sizeEqConstBody` succeeds under `fun _ => 8`. -/
theorem sizeEqConstBody_constSucceeds_eight :
    ConstSucceeds [] (fun _ => 8) sizeEqConstBody :=
  sizeEqConstBody_constSucceeds_of_eq (fun _ => 8) rfl

/-- Key PME soundness lemma: if CTFE of `sizeEqConstBody` succeeds under
    `tySizes` (`ConstSucceeds [] tySizes sizeEqConstBody`), then `Src` and `Dst`
    have equal byte size (`tySizes 0 = tySizes 1`). -/
theorem constSucceeds_sizeEqConstBody_imp_eq (tySizes : Nat → Nat)
    (h : ConstSucceeds [] tySizes sizeEqConstBody) :
    tySizes 0 = tySizes 1 := by
  cases h.2 with
  | intro n hn =>
    cases hn with
    | intro v hreach =>
      cases hdec : decide (tySizes 0 = tySizes 1) with
      | true => exact of_decide_eq_true hdec
      | false =>
        have hunw :
            ExecUnwind [] sizeEqConstBody (constEntryState tySizes) := by
          refine .step rfl (.step rfl (.step rfl (.step rfl
            (.step rfl (.step rfl (.step rfl ?_))))))
          dsimp only [constEntryState, updateLocal, bumpGen]
          refine .step rfl ?_
          apply ExecUnwind.step
          · dsimp only [evalMirStep, lookupAt, Option.getD, List.length,
              evalMirTerminator, evalOperand, sizeEqConstBody, updateLocal]
            rw [hdec]
            rfl
          · exact .step rfl (.step rfl (.step rfl (.step rfl (.unwind rfl))))
        exact False.elim (execUnwind_not_normal hunw hreach)

/-- No constant is required by `sizeEqConstBody`. -/
theorem not_requiresConst_sizeEqConstBody {tySizes tySizes' : Nat → Nat}
    {c : MirBody} (h : RequiresConst [] tySizes sizeEqConstBody tySizes' c) :
    False := by
  cases h with
  | direct hmem => cases hmem
  | nested hmem _ => cases hmem
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ h1 =>
      cases h1 with
      | head => cases hterm
      | tail _ h2 =>
        cases h2 with
        | head => cases hterm
        | tail _ h3 =>
          cases h3 with
          | head => cases hterm
          | tail _ h4 =>
            cases h4 with
            | head => cases hterm
            | tail _ hnil => cases hnil

/-- `transmuteCheckedBody` is monomorphization-admitted under any `tySizes`
    with `tySizes 0 = tySizes 1`. -/
theorem transmuteCheckedBody_monoAdmitted {tySizes : Nat → Nat}
    (heq : tySizes 0 = tySizes 1) :
    MonoAdmitted [] tySizes transmuteCheckedBody := by
  intro tySizes' c hreq
  cases hreq with
  | direct hmem =>
    cases hmem with
    | head =>
      exact sizeEqConstBody_constSucceeds_of_eq
        (substTySizes [] tySizes [.param 0, .param 1]) heq
    | tail _ hnil => cases hnil
  | nested hmem hreq' =>
    cases hmem with
    | head => exact False.elim (not_requiresConst_sizeEqConstBody hreq')
    | tail _ hnil => cases hnil
  | call1 hbb hterm _ =>
    cases hbb with
    | head => cases hterm
    | tail _ h1 =>
      cases h1 with
      | head => cases hterm
      | tail _ hnil => cases hnil

/-- Canonical inhabited PME entry state (`_1 = .bytes 8 0`, `tySizes = 8`). -/
def pmeInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.bytes 8 0))
  block := 0
  stmtIdx := 0
  tySizes := fun _ => 8

/-- `transmuteCheckedBody` executes to normal completion returning a valid
    `Dst` byte value from any `initMirState`. -/
theorem transmuteCheckedBody_execNormal (s : MirState)
    (hinit : initMirState [] transmuteCheckedBody s) :
    ExecNormal [] transmuteCheckedBody s (fun ret =>
      ret.satisfiesInv [] defaultAdtInv s (.param 1)) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hinit.1
    have hmono := hinit.2
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    have hconst :
        ConstSucceeds []
          (substTySizes [] tySizes0 [.param 0, .param 1]) sizeEqConstBody :=
      hmono _ sizeEqConstBody (.direct (.head _))
    have heq : tySizes0 0 = tySizes0 1 :=
      constSucceeds_sizeEqConstBody_imp_eq
        (substTySizes [] tySizes0 [.param 0, .param 1]) hconst
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.satisfiesInv [] defaultAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        (.param 0) := hv.2
      cases v with
      | usize _ => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | bytes vSz bits =>
        have hvSz : vSz = tySizes0 0 := hvty
        subst hvSz
        refine .step rfl (.step rfl (.step rfl (.step rfl (.step rfl ?_))))
        apply ExecNormal.step
        · dsimp [evalMirStep, lookupAt, evalMirStmt, transmuteCheckedBody,
            updateLocal]
          rw [hv1]
        · apply ExecNormal.step
          · dsimp [evalMirStep, lookupAt, evalMirStmt, transmuteCheckedBody,
              resolveRef, updateLocal, bumpGen]
            rw [hv1]
          · apply ExecNormal.step
            · have hdec_eq : decide (tySizes0 0 = tySizes0 1) = true :=
                decide_eq_true heq
              have hdec_refl : decide (tySizes0 0 = tySizes0 0) = true :=
                decide_eq_true rfl
              dsimp [evalMirStep, lookupAt, evalMirTerminator, evalOperand,
                evalTransmuteCopy, evalTyByteSize, evalTyByteSizeFuel,
                transmuteCheckedBody, resolveRef, extractTransmuteBits,
                updateLocal, bumpGen]
              rw [hdec_eq, hv1]
              dsimp [extractTransmuteBits]
              rw [hdec_refl]
              rfl
            · exact .step rfl (.step rfl (.normal rfl rfl))

/-- Because `MonoAdmitted` is part of `initMirState` (`MirMachine.initState`),
    `transmuteCheckedBody` satisfies the unconditional specification
    `EnsuresRetLibInv [] defaultAdtInv (.param 1) (fun _ => True)`: rejected
    monomorphizations (`tySizes 0 ≠ tySizes 1`) have `initMirState = False`
    (`⊥`), while admitted monomorphizations (`tySizes 0 = tySizes 1`) execute
    `transmute_copy` without UB and return a valid `Dst` byte value. -/
theorem transmuteCheckedBody_satisfies_retSpec :
    MirSem [] transmuteCheckedBody ≤
      EnsuresRetLibInv [] defaultAdtInv (.param 1) (fun _ => True) :=
  execNormal_spec transmuteCheckedBody_execNormal

/-- `transmuteCheckedBody` satisfies unconditional `MirLang.WellFormed`. -/
theorem transmuteCheckedBody_satisfies_wellFormed :
    MirSem [] transmuteCheckedBody ≤ (MirLang []).WellFormed :=
  Preorder.le_trans transmuteCheckedBody_satisfies_retSpec
    (spec_le_wellFormed (L := MirLang []) _)

/-- `transmuteCheckedBody` satisfies `FnVerifiedAndRetInv` on its canonical
    `effectivePre`. -/
theorem transmuteCheckedBody_verified (fnName : String) :
    FnVerifiedAndRetInv [] defaultAdtInv
      { name := fnName, prog := transmuteCheckedBody } := by
  have hinit : initMirState [] transmuteCheckedBody pmeInitState :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩,
     transmuteCheckedBody_monoAdmitted rfl⟩
  exact execNormal_fnVerifiedAndRetInv
    { name := fnName, prog := transmuteCheckedBody }
    ⟨pmeInitState, hinit, True.intro,
     ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    (fun s hpre => transmuteCheckedBody_execNormal s hpre.1)

/-- `outerTransmuteBody` executes to normal completion returning a valid `Dst`
    byte value from any `initMirState`. -/
theorem outerTransmuteBody_execNormal (s : MirState)
    (hinit : initMirState [] outerTransmuteBody s) :
    ExecNormal [] outerTransmuteBody s (fun ret =>
      ret.satisfiesInv [] defaultAdtInv s (.param 1)) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hinit.1
    have hmono := hinit.2
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    let subSz := substTySizes [] tySizes0 [.param 0, .param 1]
    have hreq :
        RequiresConst [] tySizes0 outerTransmuteBody
          (substTySizes [] subSz [.param 0, .param 1]) sizeEqConstBody :=
      .call1 (.head _) rfl (.direct (.head _))
    have hconst :
        ConstSucceeds []
          (substTySizes [] subSz [.param 0, .param 1]) sizeEqConstBody :=
      hmono _ sizeEqConstBody hreq
    have heq : tySizes0 0 = tySizes0 1 :=
      constSucceeds_sizeEqConstBody_imp_eq
        (substTySizes [] subSz [.param 0, .param 1]) hconst
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.satisfiesInv [] defaultAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        (.param 0) := hv.2
      cases v with
      | usize _ => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | bytes vSz bits =>
        have hvSz : vSz = tySizes0 0 := hvty
        subst hvSz
        refine .step rfl ?_
        apply ExecNormal.step
        · dsimp [evalMirStep, lookupAt, evalMirStmt, evalOperand,
            outerTransmuteBody, updateLocal]
          rw [hv1]
        · refine .step rfl (.step rfl (.step rfl (.step rfl
            (.step rfl (.step rfl (.step rfl ?_))))))
          dsimp only [updateLocal, bumpGen]
          refine .step rfl ?_
          apply ExecNormal.step
          · have hdec_eq : decide (tySizes0 0 = tySizes0 1) = true :=
              decide_eq_true heq
            have hdec_refl : decide (tySizes0 0 = tySizes0 0) = true :=
              decide_eq_true rfl
            dsimp [evalMirStep, lookupAt, evalMirTerminator, evalOperand,
              evalTransmuteCopy, evalTyByteSize, evalTyByteSizeFuel,
              transmuteCheckedBody, substTySizes, resolveRef,
              extractTransmuteBits, updateLocal, bumpGen]
            rw [hdec_eq, hdec_refl]
            rfl
          · exact .step rfl (.step rfl (.step rfl (.step rfl
              (.normal rfl rfl))))

/-- `outerTransmuteBody` (whose own `requiredConsts` is `[]`, but which calls
    `transmuteCheckedBody` via `Terminator.call1`) satisfies unconditional
    `EnsuresRetLibInv [] defaultAdtInv (.param 1) (fun _ => True)` because
    `RequiresConst` transitively collects `sizeEqConstBody` from
    `transmuteCheckedBody`. -/
theorem outerTransmuteBody_satisfies_retSpec :
    MirSem [] outerTransmuteBody ≤
      EnsuresRetLibInv [] defaultAdtInv (.param 1) (fun _ => True) :=
  execNormal_spec outerTransmuteBody_execNormal

/-- `outerTransmuteBody` satisfies `FnVerifiedAndRetInv` on its canonical
    `effectivePre`. -/
theorem outerTransmuteBody_verified (fnName : String) :
    FnVerifiedAndRetInv [] defaultAdtInv
      { name := fnName, prog := outerTransmuteBody } := by
  have hmono : MonoAdmitted [] (fun _ => 8) outerTransmuteBody := by
    intro tySizes' c hreq
    cases hreq with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm hreq' =>
      cases hbb with
      | head =>
        injection hterm with _ hcallee _ _ htyargs
        subst hcallee htyargs
        exact transmuteCheckedBody_monoAdmitted rfl tySizes' c hreq'
      | tail _ h1 =>
        cases h1 with
        | head => cases hterm
        | tail _ hnil => cases hnil
  have hinit : initMirState [] outerTransmuteBody pmeInitState :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩,
     hmono⟩
  exact execNormal_fnVerifiedAndRetInv
    { name := fnName, prog := outerTransmuteBody }
    ⟨pmeInitState, hinit, True.intro,
     ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    (fun s hpre => outerTransmuteBody_execNormal s hpre.1)

/-- `swappedOuterTransmuteBody` (calling `transmuteCheckedBody` with swapped
    type arguments `typeArgs := [.param 1, .param 0]`) executes to normal
    completion returning a valid `.param 0` byte value from any
    `initMirState`. -/
theorem swappedOuterTransmuteBody_execNormal (s : MirState)
    (hinit : initMirState [] swappedOuterTransmuteBody s) :
    ExecNormal [] swappedOuterTransmuteBody s (fun ret =>
      ret.satisfiesInv [] defaultAdtInv s (.param 0)) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hinit.1
    have hmono := hinit.2
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    let subSz := substTySizes [] tySizes0 [.param 1, .param 0]
    have hreq :
        RequiresConst [] tySizes0 swappedOuterTransmuteBody
          (substTySizes [] subSz [.param 0, .param 1]) sizeEqConstBody :=
      .call1 (.head _) rfl (.direct (.head _))
    have hconst :
        ConstSucceeds []
          (substTySizes [] subSz [.param 0, .param 1]) sizeEqConstBody :=
      hmono _ sizeEqConstBody hreq
    have heq : tySizes0 1 = tySizes0 0 :=
      constSucceeds_sizeEqConstBody_imp_eq
        (substTySizes [] subSz [.param 0, .param 1]) hconst
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.satisfiesInv [] defaultAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        (.param 1) := hv.2
      cases v with
      | usize _ => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | bytes vSz bits =>
        have hvSz : vSz = tySizes0 1 := hvty
        subst hvSz
        refine .step rfl ?_
        apply ExecNormal.step
        · dsimp [evalMirStep, lookupAt, evalMirStmt, evalOperand,
            swappedOuterTransmuteBody, updateLocal]
          rw [hv1]
        · refine .step rfl (.step rfl (.step rfl (.step rfl
            (.step rfl (.step rfl (.step rfl ?_))))))
          dsimp only [updateLocal, bumpGen]
          refine .step rfl ?_
          apply ExecNormal.step
          · have hdec_eq : decide (tySizes0 1 = tySizes0 0) = true :=
              decide_eq_true heq
            have hdec_refl : decide (tySizes0 1 = tySizes0 1) = true :=
              decide_eq_true rfl
            dsimp [evalMirStep, lookupAt, evalMirTerminator, evalOperand,
              evalTransmuteCopy, evalTyByteSize, evalTyByteSizeFuel,
              transmuteCheckedBody, subSz, substTySizes, resolveRef,
              extractTransmuteBits, updateLocal, bumpGen]
            rw [hdec_eq, hdec_refl]
            rfl
          · exact .step rfl (.step rfl (.step rfl (.step rfl
              (.normal rfl rfl))))

/-- `swappedOuterTransmuteBody` satisfies unconditional
    `EnsuresRetLibInv [] defaultAdtInv (.param 0) (fun _ => True)`. -/
theorem swappedOuterTransmuteBody_satisfies_retSpec :
    MirSem [] swappedOuterTransmuteBody ≤
      EnsuresRetLibInv [] defaultAdtInv (.param 0) (fun _ => True) :=
  execNormal_spec swappedOuterTransmuteBody_execNormal

/-- Ready-to-apply `CrateTheorem` witness for a single-function PME library
    crate containing `transmute_checked` (either via associated const `ASSERT`
    or inline `const { assert!(...) }`). -/
theorem prove_pme_transmute_single_crate (fnName : String) {src : String} :
    CrateTheorem {
      functions := [{ name := fnName, prog := transmuteCheckedBody }]
      tcb := [TCBItem.rustcLowering fnName transmuteCheckedBody]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } :=
  verify_single_fn_wf_crate fnName transmuteCheckedBody (src := src)
    (transmuteCheckedBody_verified fnName)

/-- Ready-to-apply `CrateTheorem` witness for a two-function PME library crate
    containing `transmute_checked` and its generic wrapper `outer_transmute`. -/
theorem prove_pme_transmute_crate (fn1Name fn2Name : String) {src : String}
    (h12 : decide (fn1Name = fn2Name) = false := by rfl) :
    CrateTheorem {
      functions := [
        { name := fn1Name, prog := transmuteCheckedBody },
        { name := fn2Name, prog := outerTransmuteBody }
      ]
      tcb := [
        TCBItem.rustcLowering fn1Name transmuteCheckedBody,
        TCBItem.rustcLowering fn2Name outerTransmuteBody
      ]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } := by
  have h1 := transmuteCheckedBody_verified fn1Name
  have h2 := outerTransmuteBody_verified fn2Name
  have hne12 : fn1Name ≠ fn2Name := of_decide_eq_false h12
  have hnodupTcb :
      NoDupIds [
        TCBItem.rustcLowering fn1Name transmuteCheckedBody,
        TCBItem.rustcLowering fn2Name outerTransmuteBody
      ] :=
    ⟨⟨fun h => by injection h with h' _; exact hne12 h', True.intro⟩,
     True.intro, True.intro⟩
  exact ⟨(by intro h; cases h),
    ⟨⟨hne12, True.intro⟩, True.intro, True.intro⟩,
    defaultAdtInv_admissible,
    True.intro,
    ⟨{ path := "src/lib.rs", contents := src, expected := src }, .head _, rfl⟩,
    ⟨rfl, True.intro⟩,
    ⟨⟨(by intro h; cases h),
      ⟨⟨(by intro h; cases h), True.intro⟩, True.intro, True.intro⟩,
      hnodupTcb,
      ⟨True.intro, True.intro, True.intro⟩,
      ⟨Or.inl (.head _),
       Or.inr ⟨h1.1, h1.2, True.intro⟩,
       True.intro⟩⟩,
     ⟨(by intro h; cases h),
      ⟨⟨(by intro h; cases h), True.intro⟩, True.intro, True.intro⟩,
      hnodupTcb,
      ⟨True.intro, True.intro, True.intro⟩,
      ⟨Or.inl (.tail _ (.head _)),
       Or.inr ⟨h2.1, h2.2, True.intro⟩,
       True.intro⟩⟩,
     True.intro⟩⟩

/-- Negative PME adequacy canary: removing the PME assertion from
    `transmute_checked` (`transmuteUncheckedBody`, where `requiredConsts = []`)
    makes `MonoAdmitted` vacuously true on mismatched type sizes
    (`tySizes 0 = 8`, `tySizes 1 = 4`), causing `transmute_copy` to fail with
    `.failed` and refuting `CrateTheorem` without needing any assumption about
    `rustc`. -/
theorem canary_transmuteUnchecked_rejected (fnName : String) {src : String} :
    ¬ CrateTheorem {
      functions := [{ name := fnName, prog := transmuteUncheckedBody }]
      tcb := [TCBItem.rustcLowering fnName transmuteUncheckedBody]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } := by
  intro hCrate
  have hOb2 := hCrate.2.2.2.2.2.2.1.2.2.2.2.2.1
  cases hOb2 with
  | inl hIn =>
    cases hIn with
    | tail _ hNil => cases hNil
  | inr hVer =>
    have hWF := hVer.1.2.2
    let tySizesBad : Nat → Nat := fun idx => if idx == 0 then 8 else 4
    let locals0 : Nat → Option MirVal :=
      updateLocal (fun _ => none) 1 (some (.bytes 8 42))
    let s0 : MirState := {
      locals := locals0
      block := 0
      stmtIdx := 0
      tySizes := tySizesBad
    }
    have hentry : initEntryState [] transmuteUncheckedBody s0 :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        ⟨⟨.bytes 8 42, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    have hmono : MonoAdmitted [] tySizesBad transmuteUncheckedBody := by
      intro _ _ hc
      cases hc with
      | direct hmem => cases hmem
      | nested hmem _ => cases hmem
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ hbb1 =>
          cases hbb1 with
          | head => cases hterm
          | tail _ hnil => cases hnil
    have hinit : initMirState [] transmuteUncheckedBody s0 := ⟨hentry, hmono⟩
    have hpre :
        CapturedFn.effectivePre [] defaultAdtInv
          { name := fnName, prog := transmuteUncheckedBody } s0 :=
      ⟨hinit, True.intro,
       ⟨⟨.bytes 8 42, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    have hfail : ExecFail [] transmuteUncheckedBody s0 :=
      .step rfl (.step rfl (.step rfl (.step rfl (.fail rfl))))
    cases execFail_reaches hfail with
    | intro n hr =>
      exact (hWF s0 hpre).1 hinit n [] .failed hr

/-!
## 5. `NonZeroUsize` Library Verification Contract Lemmas and Canaries
-/

/-- Standard ADT representation invariant for a crate whose ADT `0`
    (`NonZeroUsize`) encapsulates a private non-zero `usize` field
    (`val != 0`). -/
abbrev nonZeroAdtInv : AdtInv :=
  fun id v =>
    match id, v with
    | 0, .usize n => n ≠ 0
    | _, _ => False

/-- Standard `# Safety` precondition for `pub unsafe fn new_unchecked(x: usize)
    -> NonZeroUsize`: the caller guarantees that argument `_1` is non-zero. -/
abbrev newUncheckedSafetyPre (s : MirState) : Prop :=
  ∀ n, s.locals 1 = some (.usize n) → n ≠ 0

/-- Captured ADT declaration for `pub struct NonZeroUsize { val: usize }` with a
    private field (`FieldAccess.priv`). -/
def nonZeroAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .priv }]

/-- Captured ADT declaration for `pub struct NonZeroUsize { pub val: usize }`
    with a public safe field (`FieldAccess.pubSafe`). -/
def pubSafeNonZeroAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .usize, access := .pubSafe }]

/-- `nonZeroAdtInv` is admissible for `[nonZeroAdtDecl]` because
    `NonZeroUsize`'s field is private (`allFieldsPubSafe = false`) and
    `.adt 0 (.usize 1)` inhabits `NonZeroUsize`. -/
theorem nonZeroAdtInv_admissible :
    AdmissibleAdtInv [nonZeroAdtDecl] nonZeroAdtInv := by
  refine ⟨⟨True.intro, True.intro⟩,
    ⟨⟨constEntryState (fun _ => 0), .adt 0 (.usize 1),
      rfl, Nat.succ_ne_zero 0, True.intro⟩, True.intro⟩,
    ?_⟩
  intro decl hmem hPub
  cases hmem with
  | head => cases hPub
  | tail _ hnil => cases hnil

/-- Negative adequacy canary: if `NonZeroUsize`'s field `val` is made `pub`
    (`pubSafeNonZeroAdtDecl`), then `nonZeroAdtInv` violates `AdmissibleAdtInv`
    because safe downstream callers can construct `NonZeroUsize { val: 0 }`! -/
theorem canary_pub_safe_fields_reject_nonzero_inv :
    ¬ AdmissibleAdtInv [pubSafeNonZeroAdtDecl] nonZeroAdtInv := by
  intro hAdm
  exact hAdm.2.2 pubSafeNonZeroAdtDecl (.head _) rfl (fun _ => 0) (.usize 0)
    (Or.inr ⟨{ ty := .usize, access := .pubSafe }, .head _, True.intro⟩) rfl

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn make_nonzero(x: usize) -> NonZeroUsize`. -/
def makeNonZeroBody : MirBody where
  argTys := [.usize]
  retTy := .adt 0
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign ⟨3⟩ (.use (.copy ⟨1⟩)),
        .assign ⟨2⟩ (.binaryOp .eq (.move ⟨3⟩) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign ⟨0⟩ (.aggregate 0 (.constVal (.usize 1)))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .storageLive ⟨4⟩,
        .assign ⟨4⟩ (.use (.copy ⟨1⟩)),
        .assign ⟨0⟩ (.aggregate 0 (.move ⟨4⟩)),
        .storageDead ⟨4⟩
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [.storageDead ⟨2⟩]
      terminator := .return_ }
  ]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub unsafe fn new_unchecked(x: usize) -> NonZeroUsize`. -/
def newUncheckedBody : MirBody where
  argTys := [.usize]
  retTy := .adt 0
  localCount := 3
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign ⟨2⟩ (.use (.copy ⟨1⟩)),
        .assign ⟨0⟩ (.aggregate 0 (.move ⟨2⟩)),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for
    `pub fn get_unchecked_nonzero(x: NonZeroUsize) -> usize`. -/
def getUncheckedNonZeroBody : MirBody where
  argTys := [.adt 0]
  retTy := .usize
  localCount := 5
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .storageLive ⟨3⟩,
        .assign ⟨3⟩ (.field0 ⟨1⟩),
        .assign ⟨2⟩ (.binaryOp .eq (.move ⟨3⟩) (.constVal (.usize 0)))
      ]
      terminator := .switchInt (.move ⟨2⟩) ⟨2⟩ ⟨1⟩ },
    { stmts := [.storageDead ⟨3⟩, .storageLive ⟨4⟩]
      terminator := .unreachable },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign ⟨0⟩ (.field0 ⟨1⟩),
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

/-- Canonical `rustc -Z mir-opt-level=0 --emit=mir` body for a buggy safe
    constructor `pub fn buggy_zero(_x: usize) -> NonZeroUsize { NonZeroUsize {
    val: 0 } }`. -/
def buggyZeroBody : MirBody where
  argTys := [.usize]
  retTy := .adt 0
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.aggregate 0 (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Canonical entry state with `_1 = .usize 1` for `makeNonZeroBody` and
    `newUncheckedBody`. -/
def singleArgNonZeroUsizeInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.usize 1))
  block := 0
  stmtIdx := 0

/-- Canonical entry state with `_1 = .adt 0 (.usize 1)` for
    `getUncheckedNonZeroBody`. -/
def singleArgAdtNonZeroInitState : MirState where
  locals := updateLocal (fun _ => none) 1 (some (.adt 0 (.usize 1)))
  block := 0
  stmtIdx := 0

/-- `makeNonZeroBody` executes to normal completion returning a valid
    `NonZeroUsize` from any `initMirState`. -/
theorem makeNonZeroBody_execNormal (s : MirState)
    (hinit : initMirState [nonZeroAdtDecl] makeNonZeroBody s) :
    ExecNormal [nonZeroAdtDecl] makeNonZeroBody s (fun ret =>
      ret.satisfiesInv [nonZeroAdtDecl] nonZeroAdtInv s (.adt 0)) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.satisfiesInv [nonZeroAdtDecl] defaultAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        .usize := hv.2
      cases v with
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        refine .step rfl (.step rfl ?_)
        apply ExecNormal.step
        · change evalMirStmt makeNonZeroBody _
            (.assign ⟨3⟩ (.use (.copy ⟨1⟩))) = _
          dsimp only [evalMirStmt, evalOperand, makeNonZeroBody, updateLocal]
          rw [hv1]
          rfl
        · refine .step rfl ?_
          cases n with
          | zero =>
            exact .step rfl (.step rfl (.step rfl (.step rfl
              (.step rfl (.normal rfl ⟨rfl, Nat.succ_ne_zero 0, True.intro⟩)))))
          | succ k =>
            refine .step rfl (.step rfl (.step rfl ?_))
            apply ExecNormal.step
            · change evalMirStmt makeNonZeroBody _
                (.assign ⟨4⟩ (.use (.copy ⟨1⟩))) = _
              dsimp only [evalMirStmt, evalOperand, makeNonZeroBody,
                updateLocal]
              rw [hv1]
              rfl
            · exact .step rfl (.step rfl (.step rfl (.step rfl
                (.normal rfl ⟨rfl, Nat.succ_ne_zero k, True.intro⟩))))

/-- `makeNonZeroBody` satisfies `FnVerifiedAndRetInv`. -/
theorem makeNonZeroBody_verified (fnName : String) :
    FnVerifiedAndRetInv [nonZeroAdtDecl] nonZeroAdtInv
      { name := fnName, prog := makeNonZeroBody, kind := .pubSafe True } := by
  have hmono : MonoAdmitted [nonZeroAdtDecl] (fun _ => 0) makeNonZeroBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ h1 =>
        cases h1 with
        | head => cases hterm
        | tail _ h2 =>
          cases h2 with
          | head => cases hterm
          | tail _ h3 =>
            cases h3 with
            | head => cases hterm
            | tail _ hnil => cases hnil
  have hinit :
      initMirState [nonZeroAdtDecl] makeNonZeroBody
        singleArgNonZeroUsizeInitState :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩,
     hmono⟩
  exact execNormal_fnVerifiedAndRetInv
    { name := fnName, prog := makeNonZeroBody, kind := .pubSafe True }
    ⟨singleArgNonZeroUsizeInitState, hinit, True.intro,
     ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    (fun s hpre => makeNonZeroBody_execNormal s hpre.1)

/-- `newUncheckedBody` executes to normal completion returning a valid
    `NonZeroUsize` from any state satisfying its `effectivePre`. -/
theorem newUncheckedBody_execNormal (fnName : String) (s : MirState)
    (hpre :
      CapturedFn.effectivePre [nonZeroAdtDecl] nonZeroAdtInv
        { name := fnName
          prog := newUncheckedBody
          kind := .pubUnsafe True newUncheckedSafetyPre } s) :
    ExecNormal [nonZeroAdtDecl] newUncheckedBody s (fun ret =>
      ret.satisfiesInv [nonZeroAdtDecl] nonZeroAdtInv s (.adt 0)) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hpre.1.1
    have hsafety := hpre.2.2.2
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty : v.satisfiesInv [nonZeroAdtDecl] defaultAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        .usize := hv.2
      cases v with
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ => cases hvty
      | usize n =>
        have hne0 : n ≠ 0 := hsafety n hv1
        refine .step rfl ?_
        apply ExecNormal.step
        · change evalMirStmt newUncheckedBody _
            (.assign ⟨2⟩ (.use (.copy ⟨1⟩))) = _
          dsimp only [evalMirStmt, evalOperand, newUncheckedBody, updateLocal]
          rw [hv1]
          rfl
        · exact .step rfl (.step rfl (.normal rfl ⟨rfl, hne0, True.intro⟩))

/-- `newUncheckedBody` satisfies `FnVerifiedAndRetInv` under
    `FnKind.pubUnsafe True newUncheckedSafetyPre`. -/
theorem newUncheckedBody_verified (fnName : String) :
    FnVerifiedAndRetInv [nonZeroAdtDecl] nonZeroAdtInv {
      name := fnName
      prog := newUncheckedBody
      kind := .pubUnsafe True newUncheckedSafetyPre
    } := by
  have hmono : MonoAdmitted [nonZeroAdtDecl] (fun _ => 0) newUncheckedBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit :
      initMirState [nonZeroAdtDecl] newUncheckedBody
        singleArgNonZeroUsizeInitState :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩,
     hmono⟩
  have hsafety : newUncheckedSafetyPre singleArgNonZeroUsizeInitState := by
    intro n hn
    injection hn with hv
    injection hv with h1
    subst h1
    exact Nat.succ_ne_zero 0
  exact execNormal_fnVerifiedAndRetInv
    { name := fnName
      prog := newUncheckedBody
      kind := .pubUnsafe True newUncheckedSafetyPre }
    ⟨singleArgNonZeroUsizeInitState, hinit, True.intro,
     ⟨⟨.usize 1, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩,
     hsafety⟩
    (newUncheckedBody_execNormal fnName)

/-- `getUncheckedNonZeroBody` executes to normal completion from any state
    satisfying its `effectivePre`: because `_1` satisfies `nonZeroAdtInv`, its
    inner `usize` is `k + 1 ≠ 0`, so `switchInt` never branches to `bb1`
    (`unreachable_unchecked()`) and always returns `k + 1` via `bb2`. -/
theorem getUncheckedNonZeroBody_execNormal (fnName : String) (s : MirState)
    (hpre :
      CapturedFn.effectivePre [nonZeroAdtDecl] nonZeroAdtInv
        { name := fnName
          prog := getUncheckedNonZeroBody
          kind := .pubSafe True } s) :
    ExecNormal [nonZeroAdtDecl] getUncheckedNonZeroBody s (fun ret =>
      ret.satisfiesInv [nonZeroAdtDecl] nonZeroAdtInv s .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 =>
    have hentry := hpre.1.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.1
    subst hb hs hc hst hlg
    cases hpre.2.2.1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvinv : v.satisfiesInv [nonZeroAdtDecl] nonZeroAdtInv
        { locals := locals0, block := 0, stmtIdx := 0, tySizes := tySizes0 }
        (.adt 0) := hv.2
      cases v with
      | usize _ => cases hvinv
      | bool _ => cases hvinv
      | unit => cases hvinv
      | bytes _ _ => cases hvinv
      | ref _ _ _ => cases hvinv
      | adt adtId inner =>
        cases adtId with
        | succ _ => cases hvinv.1
        | zero =>
          cases inner with
          | bool _ => cases hvinv.2.1
          | unit => cases hvinv.2.1
          | adt _ _ => cases hvinv.2.1
          | bytes _ _ => cases hvinv.2.1
          | ref _ _ _ => cases hvinv.2.1
          | usize n =>
            cases n with
            | zero => exact False.elim (hvinv.2.1 rfl)
            | succ k =>
              refine .step rfl (.step rfl ?_)
              apply ExecNormal.step
              · change evalMirStmt getUncheckedNonZeroBody _
                  (.assign ⟨3⟩ (.field0 ⟨1⟩)) = _
                dsimp only [evalMirStmt, getUncheckedNonZeroBody, updateLocal]
                rw [hv1]
                rfl
              · refine .step rfl (.step rfl (.step rfl ?_))
                apply ExecNormal.step
                · change evalMirStmt getUncheckedNonZeroBody _
                    (.assign ⟨0⟩ (.field0 ⟨1⟩)) = _
                  dsimp only [evalMirStmt, getUncheckedNonZeroBody, updateLocal]
                  rw [hv1]
                  rfl
                · exact .step rfl (.normal rfl True.intro)

/-- `getUncheckedNonZeroBody` satisfies `FnVerifiedAndRetInv`. -/
theorem getUncheckedNonZeroBody_verified (fnName : String) :
    FnVerifiedAndRetInv [nonZeroAdtDecl] nonZeroAdtInv {
      name := fnName
      prog := getUncheckedNonZeroBody
      kind := .pubSafe True
    } := by
  have hmono :
      MonoAdmitted [nonZeroAdtDecl] (fun _ => 0) getUncheckedNonZeroBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ h1 =>
        cases h1 with
        | head => cases hterm
        | tail _ h2 =>
          cases h2 with
          | head => cases hterm
          | tail _ hnil => cases hnil
  have hinit :
      initMirState [nonZeroAdtDecl] getUncheckedNonZeroBody
        singleArgAdtNonZeroInitState :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
      ⟨⟨.adt 0 (.usize 1), rfl, rfl, True.intro, True.intro⟩,
       fun j hj _ => updateLocal_one_gt_one j hj⟩⟩,
     hmono⟩
  exact execNormal_fnVerifiedAndRetInv
    { name := fnName, prog := getUncheckedNonZeroBody, kind := .pubSafe True }
    ⟨singleArgAdtNonZeroInitState, hinit, True.intro,
     ⟨⟨.adt 0 (.usize 1), rfl, rfl, Nat.succ_ne_zero 0, True.intro⟩,
      fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    (getUncheckedNonZeroBody_execNormal fnName)

/-- Ready-to-apply `CrateTheorem` witness for the 3-function `NonZeroUsize`
    library crate (`make_nonzero`, `new_unchecked`, `get_unchecked_nonzero`). -/
theorem prove_nonzero_library_crate (fn1Name fn2Name fn3Name : String)
    {src : String}
    (h12 : decide (fn1Name = fn2Name) = false := by rfl)
    (h13 : decide (fn1Name = fn3Name) = false := by rfl)
    (h23 : decide (fn2Name = fn3Name) = false := by rfl) :
    CrateTheorem {
      adts := [nonZeroAdtDecl]
      adtInv := nonZeroAdtInv
      functions := [
        { name := fn1Name, prog := makeNonZeroBody, kind := .pubSafe True },
        { name := fn2Name
          prog := newUncheckedBody
          kind := .pubUnsafe True newUncheckedSafetyPre },
        { name := fn3Name
          prog := getUncheckedNonZeroBody
          kind := .pubSafe True }
      ]
      tcb := [
        TCBItem.rustcLowering fn1Name makeNonZeroBody,
        TCBItem.rustcLowering fn2Name newUncheckedBody,
        TCBItem.rustcLowering fn3Name getUncheckedNonZeroBody
      ]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } := by
  have h1 := makeNonZeroBody_verified fn1Name
  have h2 := newUncheckedBody_verified fn2Name
  have h3 := getUncheckedNonZeroBody_verified fn3Name
  have hne12 : fn1Name ≠ fn2Name := of_decide_eq_false h12
  have hne13 : fn1Name ≠ fn3Name := of_decide_eq_false h13
  have hne23 : fn2Name ≠ fn3Name := of_decide_eq_false h23
  have hnodupTcb :
      NoDupIds [
        TCBItem.rustcLowering fn1Name makeNonZeroBody,
        TCBItem.rustcLowering fn2Name newUncheckedBody,
        TCBItem.rustcLowering fn3Name getUncheckedNonZeroBody
      ] :=
    ⟨⟨fun h => by injection h with h' _; exact hne12 h',
      fun h => by injection h with h' _; exact hne13 h',
      True.intro⟩,
     ⟨fun h => by injection h with h' _; exact hne23 h', True.intro⟩,
     True.intro,
     True.intro⟩
  exact ⟨(by intro h; cases h),
    ⟨⟨hne12, hne13, True.intro⟩, ⟨hne23, True.intro⟩,
     True.intro, True.intro⟩,
    nonZeroAdtInv_admissible,
    True.intro,
    ⟨{ path := "src/lib.rs", contents := src, expected := src }, .head _, rfl⟩,
    ⟨rfl, True.intro⟩,
    ⟨⟨(by intro h; cases h),
      ⟨⟨(by intro h; cases h), True.intro⟩, True.intro, True.intro⟩,
      hnodupTcb,
      ⟨True.intro, True.intro, True.intro, True.intro⟩,
      ⟨Or.inl (.head _),
       Or.inr ⟨h1.1, h1.2, True.intro⟩,
       True.intro⟩⟩,
     ⟨(by intro h; cases h),
      ⟨⟨(by intro h; cases h), True.intro⟩, True.intro, True.intro⟩,
      hnodupTcb,
      ⟨True.intro, True.intro, True.intro, True.intro⟩,
      ⟨Or.inl (.tail _ (.head _)),
       Or.inr ⟨h2.1, h2.2, True.intro⟩,
       True.intro⟩⟩,
     ⟨(by intro h; cases h),
      ⟨⟨(by intro h; cases h), True.intro⟩, True.intro, True.intro⟩,
      hnodupTcb,
      ⟨True.intro, True.intro, True.intro, True.intro⟩,
      ⟨Or.inl (.tail _ (.tail _ (.head _))),
       Or.inr ⟨h3.1, h3.2, True.intro⟩,
       True.intro⟩⟩,
     True.intro⟩⟩

/-- Negative library adequacy canary: a safe function `buggy_zero` that returns
    `NonZeroUsize { val: 0 }` violates
    `EnsuresRetLibInv [nonZeroAdtDecl] nonZeroAdtInv (.adt 0)` and refutes
    `CrateTheorem` without needing any assumption about `rustc`. -/
theorem canary_buggy_zero_rejected (fnName : String) {src : String} :
    ¬ CrateTheorem {
      adts := [nonZeroAdtDecl]
      adtInv := nonZeroAdtInv
      functions := [
        { name := fnName, prog := buggyZeroBody, kind := .pubSafe True }
      ]
      tcb := [TCBItem.rustcLowering fnName buggyZeroBody]
      artifacts := [{ path := "src/lib.rs", contents := src, expected := src }]
    } := by
  intro hCrate
  have hOb2 := hCrate.2.2.2.2.2.2.1.2.2.2.2.2.1
  cases hOb2 with
  | inl hIn =>
    cases hIn with
    | tail _ hNil => cases hNil
  | inr hVer =>
    have hRetInv := hVer.2.1
    let s0 : MirState := singleArgUsizeInitState
    have hentry : initEntryState [nonZeroAdtDecl] buggyZeroBody s0 :=
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, by decide, rfl, rfl,
        ⟨⟨.usize 0, rfl, True.intro⟩,
         fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    have hmono : MonoAdmitted [nonZeroAdtDecl] (fun _ => 0) buggyZeroBody := by
      intro _ _ hc
      cases hc with
      | direct hmem => cases hmem
      | nested hmem _ => cases hmem
      | call1 hbb hterm _ =>
        cases hbb with
        | head => cases hterm
        | tail _ hnil => cases hnil
    have hinit : initMirState [nonZeroAdtDecl] buggyZeroBody s0 :=
      ⟨hentry, hmono⟩
    have hexec :
        ExecNormal [nonZeroAdtDecl] buggyZeroBody s0
          (fun v => v = .adt 0 (.usize 0)) :=
      .step rfl (.normal rfl rfl)
    have hpre :
        CapturedFn.effectivePre [nonZeroAdtDecl] nonZeroAdtInv
          { name := fnName, prog := buggyZeroBody, kind := .pubSafe True } s0 :=
      ⟨hinit, True.intro,
       ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
    cases hRetInv s0 hpre with
    | intro hdef hval =>
      cases execNormal_reaches hexec with
      | intro n hn =>
        cases hn with
        | intro v hv =>
          have hv_eq : v = .adt 0 (.usize 0) := hv.2
          subst hv_eq
          let out : EventualOut Empty MirVal :=
            .terminated [] (.normal (.adt 0 (.usize 0)))
          have hpfx : (MirSem [nonZeroAdtDecl] buggyZeroBody s0).val hdef out :=
            ⟨hinit, n, hv.1⟩
          have hinv :
              (MirVal.adt 0 (.usize 0)).satisfiesInv
                [nonZeroAdtDecl] nonZeroAdtInv s0 (.adt 0) :=
            hval out hpfx [] (.adt 0 (.usize 0)) rfl
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

theorem loopBody_reaches_running (n : Nat) :
    ∀ (s : MirState) (tr : List Empty) (out : PrefixOutcome MirState MirVal),
      s.block = 0 → s.stmtIdx = 0 → s.curBody = none →
      ReachesPrefix (MirStep []) loopBody n s tr out →
      ∃ s', out = .running s' := by
  induction n with
  | zero =>
    intro s _ out _ _ _ hreach
    cases hreach with
    | zero => exact ⟨s, rfl⟩
  | succ k ih =>
    intro s tr out hb hs hc hreach
    have hstep0 :
        evalMirStep [] loopBody s =
          StepResult.silent { s with block := 0, stmtIdx := 0 } := by
      cases s with
      | mk locals localGens block stmtIdx tySizes curBody stack =>
        dsimp at hb hs hc
        subst hb hs hc
        rfl
    cases hreach with
    | step _ _ _ obs _ _ _ _ => nomatch obs
    | choice _ _ s' branches _ _ h1 hbr h2 =>
      have h1' : StepResult.choice branches = evalMirStep [] loopBody s := h1
      rw [hstep0] at h1'
      injection h1' with hbr_eq
      subst hbr_eq
      subst hbr
      exact ih { s with block := 0, stmtIdx := 0 } tr out rfl rfl hc h2
    | emptyChoice _ _ branches h1 hemp =>
      have h1' : StepResult.choice branches = evalMirStep [] loopBody s := h1
      rw [hstep0] at h1'
      injection h1' with hbr_eq
      subst hbr_eq
      exact False.elim (hemp ⟨{ s with block := 0, stmtIdx := 0 }, rfl⟩)
    | terminated _ _ _ h1 =>
      have h1' : _ = evalMirStep [] loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | failed _ _ h1 =>
      have h1' : _ = evalMirStep [] loopBody s := h1
      rw [hstep0] at h1'
      cases h1'
    | noStep _ _ hnostep =>
      exact False.elim (hnostep ⟨_, hstep0.symm⟩)

/-- Positive adequacy canary: a pure infinite loop (`loop {}`)
    never triggers `.failed` or `.stuck` at any prefix depth and therefore
    satisfies `MirLang.WellFormed`. -/
theorem canary_safe_infinite_loop :
    MirSem [] loopBody ≤ (MirLang []).WellFormed := by
  refine (eventualBehaviorOf_le_wellFormed_iff (M := MirMachine [])).mpr ?_
  intro init steps tr out hinit hreach
  cases loopBody_reaches_running steps init tr out
    hinit.1.1 hinit.1.2.1 hinit.1.2.2.1 hreach with
  | intro s' hout =>
    rw [hout]
    exact True.intro

/-- MIR body that returns immediately without initializing `_0`. -/
def uninitReturnBody : MirBody where
  argTys := []
  retTy := .usize
  localCount := 1
  blocks := [{ stmts := [], terminator := .return_ }]

/-- Negative adequacy canary: returning an uninitialized `_0`
    triggers `.failed` at step `1` and therefore refutes
    `MirLang.WellFormed`. -/
theorem canary_uninit_return_violates_wellFormed :
    ¬ (MirSem [] uninitReturnBody ≤ (MirLang []).WellFormed) := by
  intro hWF
  let s0 : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hentry : initEntryState [] uninitReturnBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 1, rfl, rfl, fun _ _ _ => rfl⟩
  have hmono : MonoAdmitted [] (fun _ => 0) uninitReturnBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState [] uninitReturnBody s0 := ⟨hentry, hmono⟩
  have hfail :
      ReachesPrefix (MirStep []) uninitReturnBody 1 s0 []
        PrefixOutcome.failed :=
    ReachesPrefix.failed 0 s0 rfl
  exact (eventualBehaviorOf_le_wellFormed_iff (M := MirMachine [])).mp
    hWF s0 1 [] .failed hinit hfail

/-- MIR body for `pub fn id(x: usize) -> usize { 0 }` (assigns constant `0` to
    `_0` instead of `x`). -/
def wrongReturnZeroBody : MirBody where
  argTys := [.usize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign ⟨0⟩ (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Negative adequacy canary: returning constant `0` instead of `_1`
    violates `EnsuresEqArg 1` when `_1 = MirVal.usize 1`. -/
theorem canary_wrong_id_violates_ensures :
    ¬ (MirSem [] wrongReturnZeroBody ≤ EnsuresEqArg 1) := by
  intro hEns
  let s0 : MirState := singleArgNonZeroUsizeInitState
  have hentry : initEntryState [] wrongReturnZeroBody s0 :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 2, rfl, rfl,
      ⟨⟨MirVal.usize 1, rfl, True.intro⟩,
       fun j hj _ => updateLocal_one_gt_one j hj⟩⟩
  have hmono : MonoAdmitted [] (fun _ => 0) wrongReturnZeroBody := by
    intro _ _ hc
    cases hc with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hinit : initMirState [] wrongReturnZeroBody s0 := ⟨hentry, hmono⟩
  have hexec :
      ExecNormal [] wrongReturnZeroBody s0 (fun v => v = .usize 0) :=
    .step rfl (.normal rfl rfl)
  cases hEns s0 True.intro with
  | intro hdef hval =>
    cases execNormal_reaches hexec with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        have hv_eq : v = .usize 0 := hv.2
        subst hv_eq
        let out : EventualOut Empty MirVal :=
          .terminated [] (TerminationKind.normal (MirVal.usize 0))
        have hpfx : (MirSem [] wrongReturnZeroBody s0).val hdef out :=
          ⟨hinit, n, hv.1⟩
        have hpost := hval out hpfx [] (MirVal.usize 0) rfl
        have h1 : s0.locals 1 = some (MirVal.usize 1) := rfl
        rw [h1] at hpost
        injection hpost with hval'
        injection hval' with hnum
        cases hnum

/-!
## 7. Surface 3 Reference, Multi-Field ADT, and Call-Frame Canaries
-/

/-- Returning a reference to a root frame-local variable `_2` (`< localCount`)
    is rejected at `Terminator.return_` via `MirVal.hasEscapingRef`. -/
def rootLocalEscapeBody : MirBody where
  localCount := 3
  argTys := [.usize]
  retTy := .ref .usize
  blocks := [{
    stmts := [
      .assign ⟨2⟩ (.use (.copy ⟨1⟩)),
      .assign ⟨0⟩ (.ref ⟨2⟩)
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
      evalMirStep [] rootLocalEscapeBody s0 = .silent s1 ∧
      evalMirStep [] rootLocalEscapeBody s1 = .silent s2 ∧
      evalMirStep [] rootLocalEscapeBody s2 = .failed :=
  ⟨_, _, rfl, rfl, rfl⟩

/-- Root reference-forwarding body `pub fn id_ref(r: &usize) -> &usize { r }`
    whose caller referent resides at slot `2 = body.localCount`. -/
def idRefBody : MirBody where
  localCount := 2
  argTys := [.ref .usize]
  retTy := .ref .usize
  blocks := [{
    stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
    terminator := .return_
  }]

def idRefCallerState : MirState where
  locals := fun
    | 1 => some (.ref 0 0 ⟨2⟩)
    | 2 => some (.usize 42)
    | _ => none
  block := 0
  stmtIdx := 0

theorem holdout_A5_part1_id_ref_nonvacuous_and_succeeds :
    let fn : CapturedFn := {
      name := "id_ref"
      prog := idRefBody
      kind := .pubSafe True
    }
    fn.effectivePre [] defaultAdtInv idRefCallerState ∧
    ∃ s1,
      evalMirStep [] idRefBody idRefCallerState = .silent s1 ∧
      evalMirStep [] idRefBody s1 =
        .terminated (.normal (.ref 0 0 ⟨2⟩)) := by
  intro fn
  have hmono : MonoAdmitted [] (fun _ => 0) idRefBody := by
    intro _ _ hreq
    cases hreq with
    | direct hmem => cases hmem
    | nested hmem _ => cases hmem
    | call1 hbb hterm _ =>
      cases hbb with
      | head => cases hterm
      | tail _ hnil => cases hnil
  have hrest : ∀ j, 2 ≤ j → j < 2 → idRefCallerState.locals j = none :=
    fun _ hge hlt => False.elim (Nat.not_le_of_gt hlt hge)
  exact ⟨⟨⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl 2, rfl, rfl,
    ⟨⟨.ref 0 0 ⟨2⟩, rfl, True.intro⟩, hrest⟩⟩, hmono⟩,
    True.intro, ⟨⟨.ref 0 0 ⟨2⟩, rfl, True.intro⟩, hrest⟩⟩,
    _, rfl, rfl⟩

/-- `Stmt.storageLive` increments `localGens`, invalidating stale references to
    a reborn local even without an intervening `Stmt.storageDead`. -/
def useAfterStorageLiveRebirthBody : MirBody where
  localCount := 4
  argTys := [.usize]
  retTy := .usize
  blocks := [{
    stmts := [
      .assign ⟨2⟩ (.use (.copy ⟨1⟩)),
      .assign ⟨3⟩ (.ref ⟨2⟩),
      .storageLive ⟨2⟩,
      .assign ⟨2⟩ (.use (.constVal (.usize 77))),
      .assign ⟨0⟩ (.copyDeref ⟨3⟩)
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
      evalMirStep [] useAfterStorageLiveRebirthBody s0 = .silent s1 ∧
      evalMirStep [] useAfterStorageLiveRebirthBody s1 = .silent s2 ∧
      evalMirStep [] useAfterStorageLiveRebirthBody s2 = .silent s3 ∧
      evalMirStep [] useAfterStorageLiveRebirthBody s3 = .silent s4 ∧
      evalMirStep [] useAfterStorageLiveRebirthBody s4 = .failed :=
  ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩

/-- Reborrowing a dead reference fails at `Rvalue.reborrow`, and returning
    `.ref d _ loc` with `0 < d` at root depth `0` is flagged by
    `MirVal.hasEscapingRef`. -/
def reborrowDeadLocalBody : MirBody where
  localCount := 4
  argTys := [.usize]
  retTy := .usize
  blocks := [{
    stmts := [
      .assign ⟨2⟩ (.use (.copy ⟨1⟩)),
      .assign ⟨3⟩ (.ref ⟨2⟩),
      .storageDead ⟨2⟩,
      .assign ⟨0⟩ (.reborrow ⟨3⟩)
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
      evalMirStep [] reborrowDeadLocalBody s0 = .silent s1 ∧
      evalMirStep [] reborrowDeadLocalBody s1 = .silent s2 ∧
      evalMirStep [] reborrowDeadLocalBody s2 = .silent s3 ∧
      evalMirStep [] reborrowDeadLocalBody s3 = .failed) ∧
    (MirVal.ref 1 0 ⟨99⟩).hasEscapingRef 0 2 = true :=
  ⟨⟨_, _, _, rfl, rfl, rfl, rfl⟩, rfl⟩

/-- `TCBItem.compileId` reduces by `rfl` to `.rustcLowering` when `c.tcb`
    starts with `.rustcLowering`, and to `.fnCompiles` when `c.tcb = []`. -/
theorem fc2_2_tcb_compileId_rfl :
    TCBItem.compileId "id_ref" idRefBody [.rustcLowering "id_ref" idRefBody] =
      .rustcLowering "id_ref" idRefBody ∧
    TCBItem.compileId "id_ref" idRefBody [] =
      .fnCompiles "id_ref" idRefBody :=
  ⟨rfl, rfl⟩

/-- `extractTransmuteBits` and `evalTransmuteCopy` allow transmuting from a
    single-field `.adt 0 (.usize 42)` to `.usize` while blocking transmuting
    from `.usize` into a private-field `NonZeroUsize` (`.adt 0`). -/
theorem fc2_7_transmute_from_adt_to_usize_and_priv_adt_blocked :
    let s : MirState := {
      locals := fun
        | 1 => some (.adt 0 (.usize 42))
        | 2 => some (.usize 0)
        | _ => none
      block := 0
      stmtIdx := 0
    }
    evalTransmuteCopy [nonZeroAdtDecl] s (.adt 0) .usize (.ref 0 0 ⟨1⟩) =
      some (.usize 42) ∧
    evalTransmuteCopy [nonZeroAdtDecl] s .usize (.adt 0) (.ref 0 0 ⟨2⟩) =
      none :=
  ⟨rfl, rfl⟩

/-- Multi-field ADT declaration (`usize` + `bool` = 9 bytes) and single-field
    public `bool` ADT declaration. -/
def twoFieldAdtDecl : AdtDecl where
  id := 0
  fields := [
    { ty := .usize, access := .pubSafe },
    { ty := .bool, access := .pubSafe }
  ]

theorem holdout_A5_part2_multifield_size_is_nine :
    evalTyByteSize [twoFieldAdtDecl] (fun _ => 8) (.adt 0) = some 9 := rfl

theorem holdout_A5_part2_multifield_admissible_holds :
    AdmissibleAdtInv [twoFieldAdtDecl] defaultAdtInv := by
  refine ⟨⟨True.intro, True.intro⟩, ⟨?_, True.intro⟩, ?_⟩
  · refine ⟨constEntryState (fun _ => 8), .adt 0 (.usize 0), ?_⟩
    exact ⟨rfl, True.intro, by decide, True.intro⟩
  · intro _ _ _ _ _ _
    exact True.intro

def pubBoolAdtDecl : AdtDecl where
  id := 0
  fields := [{ ty := .bool, access := .pubSafe }]

def restrictedPubBoolInv : AdtInv
  | 0, .usize _ => True
  | 0, .bool b => b = true
  | _, _ => True

theorem holdout_A5_part2_pub_bool_restricted_inv_refuted :
    ¬ AdmissibleAdtInv [pubBoolAdtDecl] restrictedPubBoolInv := by
  intro hAdm
  have hfalse : restrictedPubBoolInv 0 (.bool false) :=
    hAdm.2.2 pubBoolAdtDecl (.head _) rfl (fun _ => 8) (.bool false)
      (Or.inr ⟨{ ty := .bool, access := .pubSafe }, .head _, True.intro⟩)
  cases hfalse

/-- Cross-frame reference forwarding (`_1` in caller borrowed and passed to
    `_1` in callee) resolves against the caller frame (`depth = 0`) and
    succeeds even though the callee also has a local `_1`. -/
def transmuteViaRefBody : MirBody where
  localCount := 3
  argTys := [.ref (.param 0)]
  retTy := .param 1
  blocks := [
    { stmts := [.assign ⟨2⟩ (.reborrow ⟨1⟩)]
      terminator :=
        .callTransmuteCopy ⟨0⟩ (.param 0) (.param 1) (.copy ⟨2⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

def outerViaRefTransmuteBody : MirBody where
  localCount := 3
  argTys := [.param 0]
  retTy := .param 1
  blocks := [
    { stmts := [.assign ⟨2⟩ (.ref ⟨1⟩)]
      terminator :=
        .call1 ⟨0⟩ transmuteViaRefBody (.move ⟨2⟩) ⟨1⟩ [.param 0, .param 1] },
    { stmts := []
      terminator := .return_ }
  ]

theorem holdout_A6_part1_cross_frame_ref_1_to_1_succeeds :
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.bytes 8 42) else none
      block := 0
      stmtIdx := 0
      tySizes := fun _ => 8
    }
    ExecNormal [] outerViaRefTransmuteBody s0 (fun v => v = .bytes 8 42) :=
  .step rfl (.step rfl (.step rfl (.step rfl (.step rfl (.normal rfl rfl)))))

/-- Parameterized `ConstSucceeds` canary (`argTys = [.bool]` is rejected) and
    swapped generic `Terminator.call1` PME canary. -/
def branchingArgConstBody : MirBody where
  localCount := 2
  argTys := [.bool]
  retTy := .unit
  blocks := [
    { stmts := []
      terminator := .switchInt (.copy ⟨1⟩) ⟨0⟩ ⟨1⟩ },
    { stmts := [.assign ⟨0⟩ (.use (.constVal .unit))]
      terminator := .return_ }
  ]

theorem holdout_B3_part1_branching_arg_const_rejected :
    ∀ tySizes, ¬ ConstSucceeds [] tySizes branchingArgConstBody := by
  intro _ h
  cases h.1

def checkParam0Size8ConstBody : MirBody where
  localCount := 2
  argTys := []
  retTy := .unit
  blocks := [{
    stmts := [.assign ⟨1⟩ (.use (.constVal (.usize 0)))]
    terminator := .callTransmuteCopy ⟨0⟩ (.param 0) .usize (.copy ⟨1⟩) ⟨0⟩
  }]

def innerPmeBody : MirBody where
  localCount := 2
  argTys := [.param 0]
  retTy := .param 0
  requiredConsts := [(checkParam0Size8ConstBody, [.param 0])]
  blocks := [{
    stmts := [.assign ⟨0⟩ (.use (.copy ⟨1⟩))]
    terminator := .return_
  }]

def outerSwappedGenericBody : MirBody where
  localCount := 2
  argTys := [.param 0]
  retTy := .param 1
  blocks := [
    { stmts := []
      terminator :=
        .call1 ⟨0⟩ innerPmeBody (.copy ⟨1⟩) ⟨1⟩ [.param 1, .param 0] },
    { stmts := []
      terminator := .return_ }
  ]

theorem checkParam0Size8_never_terminates (tySizes : Nat → Nat) :
    ¬ ConstSucceeds [] tySizes checkParam0Size8ConstBody := by
  intro h
  cases h.2 with
  | intro n hn =>
    cases hn with
    | intro v hr =>
      refine reachesPrefix_not_normal_of_step rfl hr (fun _ _ hr1 => ?_)
      exact reachesPrefix_not_normal_of_failed rfl hr1

theorem holdout_B3_part2_swapped_generic_call1_rejected :
    let tySizes : Nat → Nat := fun i => if i == 0 then 8 else 1
    substTySizes [] tySizes [.param 1, .param 0] 0 = 1 ∧
    ¬ MonoAdmitted [] tySizes outerSwappedGenericBody := by
  intro tySizes
  refine ⟨rfl, ?_⟩
  intro hmono
  have hreq : RequiresConst [] tySizes outerSwappedGenericBody
      (substTySizes [] (substTySizes [] tySizes [.param 1, .param 0])
        [.param 0])
      checkParam0Size8ConstBody :=
    .call1 (.head _) rfl (.direct (.head _))
  exact checkParam0Size8_never_terminates _ (hmono _ _ hreq)

/-- `Terminator.call1` arity check (rejecting arity 0 or 2) and callee-local
    reference escape check. -/
def calleeArityTwoBody : MirBody where
  localCount := 3
  argTys := [.usize, .usize]
  retTy := .usize
  blocks := [{ stmts := [], terminator := .return_ }]

def calleeArityZeroBody : MirBody where
  localCount := 2
  argTys := []
  retTy := .usize
  blocks := [{ stmts := [], terminator := .return_ }]

def callerBadArityTwoBody : MirBody where
  localCount := 2
  argTys := [.usize]
  retTy := .usize
  blocks := [
    { stmts := []
      terminator := .call1 ⟨0⟩ calleeArityTwoBody (.copy ⟨1⟩) ⟨1⟩ },
    { stmts := [], terminator := .return_ }
  ]

def callerBadArityZeroBody : MirBody where
  localCount := 2
  argTys := [.usize]
  retTy := .usize
  blocks := [
    { stmts := []
      terminator := .call1 ⟨0⟩ calleeArityZeroBody (.copy ⟨1⟩) ⟨1⟩ },
    { stmts := [], terminator := .return_ }
  ]

theorem holdout_B4_part1_call1_arity_mismatch_fails :
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.usize 5) else none
      block := 0
      stmtIdx := 0
    }
    evalMirStep [] callerBadArityTwoBody s0 = .failed ∧
    evalMirStep [] callerBadArityZeroBody s0 = .failed :=
  ⟨rfl, rfl⟩

def calleeReturnLocalRefBody : MirBody where
  localCount := 3
  argTys := [.usize]
  retTy := .ref .usize
  blocks := [{
    stmts := [
      .storageLive ⟨2⟩,
      .assign ⟨2⟩ (.use (.constVal (.usize 5))),
      .assign ⟨0⟩ (.ref ⟨2⟩)
    ]
    terminator := .return_
  }]

def callerForwardCalleeRefBody : MirBody where
  localCount := 2
  argTys := [.usize]
  retTy := .ref .usize
  blocks := [
    { stmts := []
      terminator := .call1 ⟨0⟩ calleeReturnLocalRefBody (.copy ⟨1⟩) ⟨1⟩ },
    { stmts := []
      terminator := .return_ }
  ]

theorem holdout_B4_part2_dangling_callee_ref_fails :
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.usize 5) else none
      block := 0
      stmtIdx := 0
    }
    (∃ s1 s2 s3 s4,
      evalMirStep [] callerForwardCalleeRefBody s0 = .silent s1 ∧
      evalMirStep [] callerForwardCalleeRefBody s1 = .silent s2 ∧
      evalMirStep [] callerForwardCalleeRefBody s2 = .silent s3 ∧
      evalMirStep [] callerForwardCalleeRefBody s3 = .silent s4 ∧
      evalMirStep [] callerForwardCalleeRefBody s4 = .failed) ∧
    ¬ (MirVal.ref 1 0 ⟨2⟩).satisfiesInv [] defaultAdtInv s0 (.ref .usize) :=
  ⟨⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl⟩, fun hinv => hinv⟩

end Anneal
