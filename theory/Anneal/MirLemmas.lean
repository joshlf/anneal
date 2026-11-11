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

/-- Postcondition `EnsuresAtomicLoad argLocal adts bodies` refines
`wellFormed (MirLang adts bodies)`. -/
theorem ensuresAtomicLoad_le_wellFormed (argLocal : Nat)
    (adts : List AdtDecl := []) (bodies : List BodyDecl := []) :
    EnsuresAtomicLoad argLocal adts bodies ≤ wellFormed (MirLang adts bodies) :=
  spec_le_wellFormed _

/-- `defaultAdtInv` is admissible for an empty list of ADT declarations. -/
theorem defaultAdtInv_admissible :
    AdmissibleAdtInv [] defaultAdtInv :=
  ⟨True.intro, fun _ h => by cases h⟩

/-!
## 1b. View Partial Order and Non-Atomic Ownership Helpers (`OwnLoc`)
-/

/-- When `a ≤ b`, `max a b = b`. -/
theorem nat_max_eq_right {a b : Nat} (h : a ≤ b) : max a b = b :=
  if_true_eq h b a

/-- When `¬ a ≤ b`, `max a b = a`. -/
theorem nat_max_eq_left {a b : Nat} (h : ¬ a ≤ b) : max a b = a :=
  if_false_eq h b a

/-- Left upper-bound property of `max` on `Nat` (`a ≤ max a b`). -/
theorem nat_le_max_left (a b : Nat) : a ≤ max a b := by
  cases (inferInstance : Decidable (a ≤ b)) with
  | isFalse h =>
    rw [nat_max_eq_left h]
    exact Nat.le_refl a
  | isTrue h =>
    rw [nat_max_eq_right h]
    exact h

/-- Right upper-bound property of `max` on `Nat` (`b ≤ max a b`). -/
theorem nat_le_max_right (a b : Nat) : b ≤ max a b := by
  cases (inferInstance : Decidable (a ≤ b)) with
  | isFalse h =>
    rw [nat_max_eq_left h]
    exact Nat.le_of_not_le h
  | isTrue h =>
    rw [nat_max_eq_right h]
    exact Nat.le_refl b

/-- Bumping a coherence view at `(loc, ts)` is inflationary in `Preorder View`
(`v ≤ View.bump v loc ts`). -/
theorem View.le_bump (v : View) (loc : Nat) (ts : Timestamp) :
    v ≤ View.bump v loc ts := by
  intro l
  unfold View.bump
  cases l == loc with
  | false => exact Nat.le_refl _
  | true => exact nat_le_max_left (v l) ts

/-- Left upper-bound property of `View.join` in `Preorder View`
(`v₁ ≤ View.join v₁ v₂`). -/
theorem View.le_join_left (v₁ v₂ : View) :
    v₁ ≤ View.join v₁ v₂ :=
  fun l => nat_le_max_left (v₁ l) (v₂ l)

/-- Right upper-bound property of `View.join` in `Preorder View`
(`v₂ ≤ View.join v₁ v₂`). -/
theorem View.le_join_right (v₁ v₂ : View) :
    v₂ ≤ View.join v₁ v₂ :=
  fun l => nat_le_max_right (v₁ l) (v₂ l)

/-- Any atomic load (`.relaxed` or `.acquire`) monotonically advances the active
thread's coherence view in `Preorder View`
(`m.curView ≤ (m.applyAtomicLoad ord msg).curView`). -/
theorem applyAtomicLoad_curView_mono (m : MemState) (ord : AtomicOrdering)
    (msg : AtomicMsg) :
    m.curView ≤ (m.applyAtomicLoad ord msg).curView := by
  cases ord with
  | relaxed =>
    exact View.le_bump m.curView msg.loc msg.ts
  | acquire =>
    exact Preorder.le_trans
      (View.le_bump m.curView msg.loc msg.ts)
      (View.le_join_left (View.bump m.curView msg.loc msg.ts) msg.relView)

/-- Single-threaded / lock-synchronized non-atomic ownership predicate:
non-atomic location `loc` holds initialized value `v`, and its last write and
read timestamps are both visible in the active thread's `curView`. -/
def OwnLoc (m : MemState) (loc : Nat) (v : MirVal) : Prop :=
  m.naVal loc = some v ∧
  m.naWriteTs loc ≤ m.curView loc ∧
  m.naReadTs loc ≤ m.curView loc

/-- Under `OwnLoc m loc v`, a non-atomic read at `loc` is completely
deterministic, never triggers a data-race failure, and returns `v`. -/
theorem OwnLoc.readNA_eq {m : MemState} {loc : Nat} {v : MirVal}
    (hOwn : OwnLoc m loc v) :
    m.readNA loc =
      some (v, { m with naReadTs := View.bump m.naReadTs loc (m.curView loc) }) := by
  unfold MemState.readNA
  have hdec : decide (m.naWriteTs loc ≤ m.curView loc) = true :=
    decide_eq_true hOwn.2.1
  rw [hdec, hOwn.1]
  rfl

/-- `OwnLoc` is preserved whenever the thread's coherence view advances in
`Preorder View` (`m.curView ≤ v'`) without concurrent modification to `loc`. -/
theorem OwnLoc.mono_view {m : MemState} {loc : Nat} {v : MirVal} {v' : View}
    (hOwn : OwnLoc m loc v) (hle : m.curView ≤ v') :
    OwnLoc { m with curView := v' } loc v :=
  ⟨hOwn.1, Nat.le_trans hOwn.2.1 (hle loc), Nat.le_trans hOwn.2.2 (hle loc)⟩

/-- Any atomic load preserves `OwnLoc` on non-atomic locations. -/
theorem OwnLoc.preserved_by_atomic_load {m : MemState} {loc : Nat} {v : MirVal}
    (ord : AtomicOrdering) (msg : AtomicMsg) (hOwn : OwnLoc m loc v) :
    OwnLoc (m.applyAtomicLoad ord msg) loc v := by
  have hmono := applyAtomicLoad_curView_mono m ord msg
  cases ord with
  | relaxed => exact OwnLoc.mono_view hOwn hmono
  | acquire => exact OwnLoc.mono_view hOwn hmono

/-- Release-Acquire ownership transfer (for example, across a `Mutex`
unlock/lock): if a `Release` message `msg` captured a view `msg.relView` that
dominates `loc`'s non-atomic write/read timestamps, performing an `Acquire` load
of `msg` establishes `OwnLoc` in the acquiring thread. -/
theorem OwnLoc.transfer_acquire {m : MemState} {loc : Nat} {v : MirVal}
    (msg : AtomicMsg)
    (hVal : m.naVal loc = some v)
    (hWrite : m.naWriteTs loc ≤ msg.relView loc)
    (hRead : m.naReadTs loc ≤ msg.relView loc) :
    OwnLoc (m.applyAtomicLoad .acquire msg) loc v := by
  have hjoin :=
    View.le_join_right (View.bump m.curView msg.loc msg.ts) msg.relView loc
  exact ⟨hVal, Nat.le_trans hWrite hjoin, Nat.le_trans hRead hjoin⟩

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
    (hretWf : LocalLayoutsAdmitted adts body s.tySizes = true := by rfl) :
    initEntryState adts body s :=
  ⟨hb, hstmt, hcur, hstack, hfid, hnfid, hlg, hloc0,
   hcount, hargWf, hretWf, hargs⟩

/-- Construct `StaticBodyWf adts body` by default `decide`/`rfl` arguments. -/
theorem mkStaticBodyWf {adts : List AdtDecl} {body : MirBody}
    (hcount : 1 + body.argTys.length ≤ body.localCount := by decide)
    (hblocks : 0 < body.blocks.length := by decide)
    (hl0 : LocalLayoutsAdmitted adts body (fun _ => 0) = true := by rfl)
    (hl1 : LocalLayoutsAdmitted adts body (fun _ => 1) = true := by rfl) :
    StaticBodyWf adts body :=
  ⟨hcount, hblocks, hl0, hl1⟩

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

/-- A body with no required constants and no calls requires no constant. -/
theorem noRequires_of_simple {bodies : List BodyDecl} {body : MirBody}
    {c : Option MirBody}
    (hrc : body.requiredConsts = [])
    (hcalls : body.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hc : RequiresConst bodies (some body) c) : False := by
  cases hc with
  | direct hmem => rw [hrc] at hmem; cases hmem
  | viaConst hmem _ => rw [hrc] at hmem; cases hmem
  | viaCall hbb hterm _ =>
    have h := noCall_of_all hcalls hbb
    rw [hterm] at h
    cases h

/-- A body with no required constants and no calls has total required
constants across all valid `tySizes`. -/
theorem constsTotal_of_simple {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody}
    (hrc : body.requiredConsts = [])
    (hcalls : body.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    ConstsTotal adts bodies body :=
  fun _ _ _ hc => False.elim (noRequires_of_simple hrc hcalls hc)

/-- A body with no required constants and no calls is admitted under every
`tySizes`. -/
theorem monoAdmitted_of_simple {adts : List AdtDecl} {bodies : List BodyDecl}
    {tySizes : Nat → Nat} {body : MirBody}
    (hrc : body.requiredConsts = [])
    (hcalls : body.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    MonoAdmitted adts bodies tySizes body :=
  fun _ hc => False.elim (noRequires_of_simple hrc hcalls hc)

/-- A body with no required constants and no calls satisfies both
`ConstsTotal` and `MonoAdmitted`. -/
theorem constsTotal_and_monoAdmitted_of_simple {adts : List AdtDecl}
    {bodies : List BodyDecl} {tySizes : Nat → Nat} {body : MirBody}
    (hrc : body.requiredConsts = [])
    (hcalls : body.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    ConstsTotal adts bodies body ∧ MonoAdmitted adts bodies tySizes body :=
  ⟨constsTotal_of_simple hrc hcalls, monoAdmitted_of_simple hrc hcalls⟩

theorem one_le_isizeMaxBytes : 1 ≤ isizeMaxBytes := by decide

theorem validTySizes_one : ValidTySizes (fun _ => 1) :=
  fun _ => one_le_isizeMaxBytes

/-- If `body` satisfies `StaticBodyWf adts body` and `MonoAdmitted` under every
`tySizes`, then it satisfies `MonoConstsWf adts bodies fn body` whether `fn` is
contracted or uncontracted. -/
theorem monoConstsWf_of_all_monoAdmitted {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {body : MirBody}
    (hwf : StaticBodyWf adts body)
    (hmono : ∀ tySizes, MonoAdmitted adts bodies tySizes body) :
    MonoConstsWf adts bodies fn body := by
  unfold MonoConstsWf
  cases fn.requires.isSome || !fn.specs.isEmpty with
  | true => exact fun tySizes _ _ => hmono tySizes
  | false =>
    exact ⟨fun _ => 1, validTySizes_one, hwf.2.2.2, hmono _⟩

/-- A body with `StaticBodyWf`, no required constants, and no calls satisfies
`ContractWellFormed adts bodies fn body` for any `fn`. -/
theorem contractWellFormed_of_simple {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {body : MirBody}
    (hwf : StaticBodyWf adts body)
    (hrc : body.requiredConsts = [])
    (hcalls : body.blocks.all (fun bb => !isCall1 bb.terminator) = true) :
    ContractWellFormed adts bodies fn body :=
  ⟨hwf, constsTotal_of_simple hrc hcalls,
   monoConstsWf_of_all_monoAdmitted hwf
     (fun _ => monoAdmitted_of_simple hrc hcalls)⟩

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
      (MirLang adts bodies).SpecOn pre (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) :=
  execNormal_specOn (fun s _ h => h_exec s h)

/-- Discharge `SpecOn pre (ContractPost adts bodies fn)` when `fn.specs = []`
from any `SpecOn` proof on a weaker or equal precondition `pre0`. -/
theorem specOn_contractPost_nil {adts : List AdtDecl} {bodies : List BodyDecl}
    {fn : CapturedFn} {body : MirBody} {pre0 pre : MirState → Prop}
    {allowGuard : Bool}
    (himp : ∀ s, pre s → pre0 s)
    (h0 :
      MirSem adts bodies body ≤
        (MirLang adts bodies).SpecOn pre0
          (fun s out =>
            SafetyPost adts (denoteAdtInv adts) body s out allowGuard))
    (hspecs : fn.specs = [] := by rfl) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre (ContractPost adts bodies fn) := by
  intro s hpre
  have hs := h0 s (himp s hpre)
  refine ⟨hs.1, fun out _ => ?_⟩
  unfold ContractPost
  rw [hspecs]
  exact True.intro

/-- Discharge `SpecOn pre (ContractPost adts bodies fn)` when
`fn.specs = [.ensuresEqArg 1]` from `ExecNormal`. -/
theorem specOn_contractPost_ensuresEqArg1 {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {body : MirBody}
    {pre : MirState → Prop}
    (hspecs : fn.specs = [.ensuresEqArg 1] := by rfl)
    (h_exec : ∀ s, pre s →
      ExecNormal adts bodies body s (fun r => s.locals 1 = some r.value)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre (ContractPost adts bodies fn) := by
  have hsingle := execNormal_spec_on_pre h_exec
  intro s hpre
  have hs := hsingle s hpre
  refine ⟨hs.1, fun out hpfx => ?_⟩
  unfold ContractPost
  rw [hspecs]
  exact ⟨hs.2 out hpfx, True.intro⟩

/-- Non-vacuity witness on a domain `dom` and precondition `pre` (retained as a
theorem-layer helper for adequacy canaries). -/
def NonVacuousOn {Query : Type u} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

/-- Return-value library-invariant postcondition behavior on `pre`. -/
def EnsuresRetLibInv (adts : List AdtDecl) (bodies : List BodyDecl := [])
    (adtInv : AdtInv) (body : MirBody) (pre : MirState → Prop)
    (allowCompileTimeGuard : Bool := false) :
    (MirLang adts bodies).Behavior :=
  (MirLang adts bodies).SpecOn pre
    (fun s out => SafetyPost adts adtInv body s out allowCompileTimeGuard)

/-- Effective precondition (`initMirState ∧ argsMatchInv ∧ fn.safetyPre`) on
`fn.resolveBody bodies`. -/
def fnEffectivePre (adts : List AdtDecl)
    (bodies : List BodyDecl := []) (adtInv : AdtInv) (fn : CapturedFn)
    (s : MirState) : Prop :=
  initMirState adts bodies (fn.resolveBody bodies) s ∧
  argsMatchInv adts adtInv (fn.resolveBody bodies).localCount s
    (fn.resolveBody bodies).argTys ∧
  fn.safetyPre s

/-- Lift `NonVacuousOn dom pre` to `NonVacuousOn dom (fun q => pre q ∧ defP q)`
when `pre` implies `defP`. -/
theorem nonVacuousOn_and_defined {Query : Type} {dom pre defP : Query → Prop}
    (h : NonVacuousOn dom pre) (himp : ∀ q, pre q → defP q) :
    NonVacuousOn dom (fun q => pre q ∧ defP q) :=
  match h with
  | ⟨q, hdom, hpre⟩ => ⟨q, hdom, hpre, himp q hpre⟩

/-- Discharge `(MirLang adts bodies).Verified pre ... body` from
`StaticBodyWf` and `ExecNormal`. -/
theorem execNormal_verified {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {pre : MirState → Prop} {P : MirState → MirReturn → Prop}
    (hwf : StaticBodyWf adts body)
    (h_pre_init : ∀ s, pre s → initMirState adts bodies body s)
    (h_exec : ∀ s, pre s → ExecNormal adts bodies body s (P s)) :
    (MirLang adts bodies).Verified pre
      (fun s out => ∀ tr ret, out = .terminated tr (.normal ret) → P s ret)
      body := by
  have h_spec :
      MirSem adts bodies body ≤
        (MirLang adts bodies).SpecOn pre
          (fun s out =>
            ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) :=
    execNormal_specOn (fun s _ hpre => h_exec s hpre)
  refine ⟨hwf, ?_, h_spec⟩
  intro s hpre
  have hinit : initMirState adts bodies body s := h_pre_init s hpre
  have hdef : (MirSem adts bodies body s).defined := (h_spec s hpre).1
  cases execNormal_reaches (h_exec s hpre) with
  | intro n hn =>
    cases hn with
    | intro v hv =>
      exact ⟨hdef, .terminated [] (.normal v), hinit, n, hv.1⟩

/-- `ExecNormal` on `pre` discharges `SpecOn pre (SafetyPost ...)` for any
`allowCompileTimeGuard` flag. -/
theorem execNormal_safetyPost {adts : List AdtDecl} {bodies : List BodyDecl}
    {adtInv : AdtInv} {body : MirBody} {pre : MirState → Prop}
    {allowGuard : Bool}
    (h_exec : ∀ s, pre s →
      ExecNormal adts bodies body s (fun r =>
        r.value.valid adts adtInv r.state body.localCount body.retTy)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre
        (fun s out => SafetyPost adts adtInv body s out allowGuard) := by
  intro s hpre
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

/-- Discharge `(MirLang adts bodies).Verified pre (SafetyPost ...) body` from
`StaticBodyWf` and `ExecNormal`. -/
theorem execNormal_safetyVerified {adts : List AdtDecl} {bodies : List BodyDecl}
    {adtInv : AdtInv} {body : MirBody} {pre : MirState → Prop}
    {allowGuard : Bool}
    (hwf : StaticBodyWf adts body)
    (h_pre_init : ∀ s, pre s → initMirState adts bodies body s)
    (h_exec : ∀ s, pre s →
      ExecNormal adts bodies body s (fun r =>
        r.value.valid adts adtInv r.state body.localCount body.retTy)) :
    (MirLang adts bodies).Verified pre
      (fun s out => SafetyPost adts adtInv body s out allowGuard)
      body := by
  have h_spec := execNormal_safetyPost (allowGuard := allowGuard) h_exec
  refine ⟨hwf, ?_, h_spec⟩
  intro s hpre
  have hinit : initMirState adts bodies body s := h_pre_init s hpre
  have hdef : (MirSem adts bodies body s).defined := (h_spec s hpre).1
  cases execNormal_reaches (h_exec s hpre) with
  | intro n hn =>
    cases hn with
    | intro v hv =>
      exact ⟨hdef, .terminated [] (.normal v), hinit, n, hv.1⟩

/-- Combined per-body contract well-formedness (`ContractWellFormed`) and
baseline safety verification (`(MirLang adts bodies).Verified (SafetyPre ...)
(SafetyPost ...)`). -/
abbrev FnBodySafetyVerified (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) (adtInv : AdtInv) (fn : CapturedFn)
    (body : MirBody) (tcb : List TCBItem := []) : Prop :=
  ContractWellFormed adts bodies fn body ∧
  (MirLang adts bodies).Verified
    (fun s => SafetyPre adts bodies adtInv fn body s tcb)
    (fun s out =>
      SafetyPost adts adtInv body s out (hasCompileTimeGuardWaiver fn tcb))
    body

/-- Combined per-function contract well-formedness and baseline safety
verification for `fn.resolveBody bodies`. -/
abbrev FnVerifiedAndRetInv (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) (adtInv : AdtInv) (fn : CapturedFn)
    (tcb : List TCBItem := []) : Prop :=
  FnBodySafetyVerified adts bodies adtInv fn (fn.resolveBody bodies) tcb

/-- Discharge `FnBodySafetyVerified` directly from `ContractWellFormed` and
`ExecNormal`. -/
theorem execNormal_fnBodySafetyVerified {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    (body : MirBody) {tcb : List TCBItem}
    (hcwf : ContractWellFormed adts bodies fn body)
    (h_exec : ∀ s, SafetyPre adts bodies adtInv fn body s tcb →
      ExecNormal adts bodies body s (fun r =>
        r.value.valid adts adtInv r.state body.localCount body.retTy)) :
    FnBodySafetyVerified adts bodies adtInv fn body tcb :=
  ⟨hcwf, execNormal_safetyVerified hcwf.1 (fun _ h => h.1) h_exec⟩

/-- Discharge `FnVerifiedAndRetInv` directly from `ContractWellFormed` and
`ExecNormal`. -/
theorem execNormal_fnVerifiedAndRetInv {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    {tcb : List TCBItem}
    (hcwf : ContractWellFormed adts bodies fn (fn.resolveBody bodies))
    (h_exec : ∀ s,
      SafetyPre adts bodies adtInv fn (fn.resolveBody bodies) s tcb →
      ExecNormal adts bodies (fn.resolveBody bodies) s (fun r =>
        r.value.valid adts adtInv r.state (fn.resolveBody bodies).localCount
          (fn.resolveBody bodies).retTy)) :
    FnVerifiedAndRetInv adts bodies adtInv fn tcb :=
  execNormal_fnBodySafetyVerified fn (fn.resolveBody bodies) hcwf h_exec

theorem toStepResult_of_choiceList {head : MirState} {tail : List MirState}
    {r : RawStep MirState MirReturn} (h : r = .choiceList head tail) :
    r.toStepResult (Obs := Empty) =
      StepResult.choice (fun s' => s' ∈ head :: tail) :=
  congrArg RawStep.toStepResult h

theorem reachesPrefix_of_choiceList
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s head : MirState} {tail : List MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn}
    (hstep : evalMirStep adts bodies body s = .choiceList head tail)
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out) :
    out = .running s ∨
      ∃ s', s' ∈ head :: tail ∧ ∃ n' tr',
        ReachesPrefix (MirStep adts bodies) body n' s' tr' out := by
  have hstepR := toStepResult_of_choiceList hstep
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
    exact Or.inr ⟨s₂, hbr, n', tr, hr⟩
  | emptyChoice _ _ branches h1 hemp =>
    have h1' :
        StepResult.choice branches =
          (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'
    injection h1' with hbr_eq
    subst hbr_eq
    exact False.elim (hemp ⟨head, .head tail⟩)
  | terminated _ _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | failed _ _ h1 =>
    have h1' : _ = (evalMirStep adts bodies body s).toStepResult := h1
    rw [hstepR] at h1'; cases h1'
  | noStep _ _ hno =>
    exact False.elim (hno ⟨_, hstepR.symm⟩)

theorem reachesPrefix_safeAndEnsures_of_choiceList
    {adts : List AdtDecl} {bodies : List BodyDecl} {body : MirBody}
    {s head : MirState} {tail : List MirState} {n : Nat} {tr : List Empty}
    {out : PrefixOutcome MirState MirReturn} {P : MirReturn → Prop}
    (hstep : evalMirStep adts bodies body s = .choiceList head tail)
    (hreach : ReachesPrefix (MirStep adts bodies) body n s tr out)
    (hnext : ∀ s', s' ∈ head :: tail → ∀ n' tr',
      ReachesPrefix (MirStep adts bodies) body n' s' tr' out →
      SafeAndEnsures P out) :
    SafeAndEnsures P out := by
  cases reachesPrefix_of_choiceList hstep hreach with
  | inl hrun =>
    subst hrun
    exact ⟨True.intro, (fun _ h => by cases h), (fun h => by cases h)⟩
  | inr hex =>
    cases hex with
    | intro s' hs' =>
      cases hs'.2 with
      | intro n' htr =>
        cases htr with
        | intro tr' hr' => exact hnext s' hs'.1 n' tr' hr'

/-- Inductive normal-termination symbolic execution relation supporting both
deterministic `.silent` steps and demonic `.choiceList` transitions. -/
inductive ExecChoiceNormal (adts : List AdtDecl := [])
    (bodies : List BodyDecl := []) (body : MirBody) :
    MirState → (MirReturn → Prop) → Prop where
  | step {s s' : MirState} {P : MirReturn → Prop} :
      evalMirStep adts bodies body s = .silent s' →
      ExecChoiceNormal adts bodies body s' P →
      ExecChoiceNormal adts bodies body s P
  | choice {s head : MirState} {tail : List MirState} {P : MirReturn → Prop} :
      evalMirStep adts bodies body s = .choiceList head tail →
      (∀ s', s' ∈ head :: tail → ExecChoiceNormal adts bodies body s' P) →
      ExecChoiceNormal adts bodies body s P
  | normal {s : MirState} {v : MirReturn} {P : MirReturn → Prop} :
      evalMirStep adts bodies body s = .terminated (.normal v) →
      P v →
      ExecChoiceNormal adts bodies body s P

/-- Weaken the return predicate `P` of `ExecChoiceNormal`. -/
theorem ExecChoiceNormal.map {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {s : MirState} {P Q : MirReturn → Prop}
    (himp : ∀ v, P v → Q v)
    (hexec : ExecChoiceNormal adts bodies body s P) :
    ExecChoiceNormal adts bodies body s Q := by
  induction hexec with
  | step hstep _ ih => exact .step hstep (ih himp)
  | choice hstep _ ih => exact .choice hstep (fun s' hm => ih s' hm himp)
  | normal hterm hp => exact .normal hterm (himp _ hp)

theorem execChoiceNormal_safeAndEnsures {adts : List AdtDecl}
    {bodies : List BodyDecl} {body : MirBody} {s : MirState}
    {P : MirReturn → Prop}
    (hexec : ExecChoiceNormal adts bodies body s P) :
    ∀ {n : Nat} {tr : List Empty} {out : PrefixOutcome MirState MirReturn},
      ReachesPrefix (MirStep adts bodies) body n s tr out →
      SafeAndEnsures P out := by
  induction hexec with
  | step hstep _ ih =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_step hstep hreach
      (fun _ _ hr => ih hr)
  | choice hstep _ ih =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_choiceList hstep hreach
      (fun s' hm _ _ hr => ih s' hm hr)
  | normal hterm hp =>
    intro n tr out hreach
    exact reachesPrefix_safeAndEnsures_of_normal hterm hreach hp

theorem execChoiceNormal_reaches {adts : List AdtDecl}
    {bodies : List BodyDecl} {body : MirBody} {s : MirState}
    {P : MirReturn → Prop}
    (hexec : ExecChoiceNormal adts bodies body s P) :
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
  | @choice _ head tail _ hstep _ ih =>
    cases ih head (.head tail) with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        exact ⟨n + 1, v,
          .choice n _ head _ [] (.terminated (.normal v))
            (toStepResult_of_choiceList hstep).symm (.head tail) hv.1,
          hv.2⟩
  | normal hterm hp =>
    exact ⟨1, _,
      .terminated 0 _ (.normal _) (toStepResult_of_terminated hterm).symm, hp⟩

theorem execChoiceNormal_specOn {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {pre : MirState → Prop} {P : MirState → MirReturn → Prop}
    (h_exec : ∀ s, initMirState adts bodies body s → pre s →
      ExecChoiceNormal adts bodies body s (P s)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) := by
  refine eventualBehaviorOf_le_normalSpecOn (M := MirMachine adts bodies) ?_
  intro init _ _ out hpre hpfx
  have hsafe := execChoiceNormal_safeAndEnsures (h_exec init hpfx.1 hpre) hpfx.2
  exact ⟨hsafe.1, hsafe.2.1⟩

theorem execChoiceNormal_spec {adts : List AdtDecl} {bodies : List BodyDecl}
    {body : MirBody} {P : MirState → MirReturn → Prop}
    (h_exec : ∀ s, initMirState adts bodies body s →
      ExecChoiceNormal adts bodies body s (P s)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).Spec (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) :=
  execChoiceNormal_specOn (fun s hinit _ => h_exec s hinit)

theorem execChoiceNormal_spec_on_pre {adts : List AdtDecl}
    {bodies : List BodyDecl} {body : MirBody} {pre : MirState → Prop}
    {P : MirState → MirReturn → Prop}
    (h_exec : ∀ s, pre s → ExecChoiceNormal adts bodies body s (P s)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre (fun s out =>
        ∀ tr ret, out = .terminated tr (.normal ret) → P s ret) :=
  execChoiceNormal_specOn (fun s _ h => h_exec s h)

theorem execChoiceNormal_safetyPost {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} {body : MirBody}
    {pre : MirState → Prop} {allowGuard : Bool}
    (h_exec : ∀ s, pre s →
      ExecChoiceNormal adts bodies body s (fun r =>
        r.value.valid adts adtInv r.state body.localCount body.retTy)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre
        (fun s out => SafetyPost adts adtInv body s out allowGuard) := by
  intro s hpre
  refine ⟨fun _ n tr oc hreach =>
    (execChoiceNormal_safeAndEnsures (h_exec s hpre) hreach).1, ?_⟩
  intro out hval
  refine ⟨?_, ?_⟩
  · intro tr ret hout
    subst hout
    cases hval.2 with
    | intro n hreach =>
      exact (execChoiceNormal_safeAndEnsures (h_exec s hpre) hreach).2.1 ret rfl
  · have hnoErr : ∀ tr, out ≠ .terminated tr .compileTimeError := by
      intro tr hout
      subst hout
      cases hval.2 with
      | intro n hreach =>
        exact (execChoiceNormal_safeAndEnsures (h_exec s hpre) hreach).2.2 rfl
    cases allowGuard with
    | false => exact hnoErr
    | true => exact fun _ => hnoErr

theorem execChoiceNormal_safetyVerified {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} {body : MirBody}
    {pre : MirState → Prop} {allowGuard : Bool}
    (hwf : StaticBodyWf adts body)
    (h_pre_init : ∀ s, pre s → initMirState adts bodies body s)
    (h_exec : ∀ s, pre s →
      ExecChoiceNormal adts bodies body s (fun r =>
        r.value.valid adts adtInv r.state body.localCount body.retTy)) :
    (MirLang adts bodies).Verified pre
      (fun s out => SafetyPost adts adtInv body s out allowGuard)
      body := by
  have h_spec := execChoiceNormal_safetyPost (allowGuard := allowGuard) h_exec
  refine ⟨hwf, ?_, h_spec⟩
  intro s hpre
  have hinit : initMirState adts bodies body s := h_pre_init s hpre
  have hdef : (MirSem adts bodies body s).defined := (h_spec s hpre).1
  cases execChoiceNormal_reaches (h_exec s hpre) with
  | intro n hn =>
    cases hn with
    | intro v hv =>
      exact ⟨hdef, .terminated [] (.normal v), hinit, n, hv.1⟩

theorem execChoiceNormal_fnBodySafetyVerified {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    (body : MirBody) {tcb : List TCBItem}
    (hcwf : ContractWellFormed adts bodies fn body)
    (h_exec : ∀ s, SafetyPre adts bodies adtInv fn body s tcb →
      ExecChoiceNormal adts bodies body s (fun r =>
        r.value.valid adts adtInv r.state body.localCount body.retTy)) :
    FnBodySafetyVerified adts bodies adtInv fn body tcb :=
  ⟨hcwf, execChoiceNormal_safetyVerified hcwf.1 (fun _ h => h.1) h_exec⟩

theorem specOn_contractPost_ensuresAtomicLoad1 {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {body : MirBody}
    {pre : MirState → Prop}
    (hspecs : fn.specs = [.ensuresAtomicLoad 1] := by rfl)
    (h_exec : ∀ s, pre s →
      ExecChoiceNormal adts bodies body s (fun r =>
        ∃ loc msg,
          s.locals 1 = some (.atomicLoc loc) ∧
          msg ∈ s.mem.visibleAtomicMsgs loc ∧
          r.value = .usize msg.bits)) :
    MirSem adts bodies body ≤
      (MirLang adts bodies).SpecOn pre (ContractPost adts bodies fn) := by
  have hsingle := execChoiceNormal_spec_on_pre h_exec
  intro s hpre
  have hs := hsingle s hpre
  refine ⟨hs.1, fun out hpfx => ?_⟩
  unfold ContractPost
  rw [hspecs]
  exact ⟨hs.2 out hpfx, True.intro⟩

theorem mem_cons_map {α β : Type} (f : α → β) (head : α) :
    ∀ (tail : List α) {y : β},
      y ∈ f head :: tail.map f → ∃ x, x ∈ head :: tail ∧ y = f x
  | _, _, .head _ => ⟨head, .head _, rfl⟩
  | _ :: tail, _, .tail _ hm =>
    match mem_cons_map f _ tail hm with
    | ⟨x, hx, hy⟩ => ⟨x, .tail _ hx, hy⟩

/-- Discharge `FnBodySafetyVerified` when
`hasCompileTimeGuardWaiver fn tcb = true`, given that execution from any state
in `SafetyPre` either returns a valid result (`ExecNormal`) or terminates with
`.compileTimeError` (`ExecCompileTimeError`), and returns normally in the
zero-extra-padding world
(`s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8)`). -/
theorem execNormalOrGuard_fnBodySafetyVerified {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    (body : MirBody) {tcb : List TCBItem}
    (hguard : hasCompileTimeGuardWaiver fn tcb = true)
    (hcwf : ContractWellFormed adts bodies fn body)
    (h_exec : ∀ s, SafetyPre adts bodies adtInv fn body s tcb →
      (s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8) →
        ExecNormal adts bodies body s (fun r =>
          r.value.valid adts adtInv r.state body.localCount body.retTy)) ∧
      (ExecNormal adts bodies body s (fun r =>
          r.value.valid adts adtInv r.state body.localCount body.retTy) ∨
       ExecCompileTimeError adts bodies body s)) :
    FnBodySafetyVerified adts bodies adtInv fn body tcb := by
  let pre := fun s => SafetyPre adts bodies adtInv fn body s tcb
  have h_wf : MirSem adts bodies body ≤ wellFormedOn (MirLang adts bodies) pre := by
    refine
      (eventualBehaviorOf_le_wellFormedOn_iff (M := MirMachine adts bodies)).mpr ?_
    intro s n tr out hpre _ hreach
    cases (h_exec s hpre).2 with
    | inl hnorm => exact (execNormal_safeAndEnsures hnorm hreach).1
    | inr hcte => exact (execCompileTimeError_safe_and_not_normal hcte hreach).1
  refine ⟨hcwf, hcwf.1, ?_, ?_⟩
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

/-- Discharge `FnVerifiedAndRetInv` when
`hasCompileTimeGuardWaiver fn tcb = true`. -/
theorem execNormalOrGuard_fnVerifiedAndRetInv {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    {tcb : List TCBItem}
    (hguard : hasCompileTimeGuardWaiver fn tcb = true)
    (hcwf : ContractWellFormed adts bodies fn (fn.resolveBody bodies))
    (h_exec : ∀ s,
      SafetyPre adts bodies adtInv fn (fn.resolveBody bodies) s tcb →
      (s.adtPad = (fun _ => 0) ∧ s.tySizes = (fun _ => 8) →
        ExecNormal adts bodies (fn.resolveBody bodies) s (fun r =>
          r.value.valid adts adtInv r.state (fn.resolveBody bodies).localCount
            (fn.resolveBody bodies).retTy)) ∧
      (ExecNormal adts bodies (fn.resolveBody bodies) s (fun r =>
          r.value.valid adts adtInv r.state (fn.resolveBody bodies).localCount
            (fn.resolveBody bodies).retTy) ∨
       ExecCompileTimeError adts bodies (fn.resolveBody bodies) s)) :
    FnVerifiedAndRetInv adts bodies adtInv fn tcb :=
  execNormalOrGuard_fnBodySafetyVerified fn (fn.resolveBody bodies) hguard hcwf
    h_exec

/-- Transfer `ContractWellFormed` from `target = lowerBody body` back to `body`
when `target` has no `.call1` terminators. -/
theorem contractWellFormed_of_lowerBody {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {body target : MirBody}
    (hres : lowerBody body = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcwf : ContractWellFormed adts bodies fn target) :
    ContractWellFormed adts bodies fn body := by
  have hcallsOrig :
      body.blocks.all (fun bb => !isCall1 bb.terminator) = true := by
    rw [← noCall_lowerBody body, hres]
    exact hcalls
  have hwf : StaticBodyWf adts body := by
    rw [← staticBodyWf_lowerBody adts body, hres]
    exact hcwf.1
  have htot : ConstsTotal adts bodies body := by
    rw [← constsTotal_lowerBody_iff (adts := adts) (bodies := bodies) hcallsOrig,
        hres]
    exact hcwf.2.1
  refine ⟨hwf, htot, ?_⟩
  have hm := hcwf.2.2
  unfold MonoConstsWf at hm
  unfold MonoConstsWf
  cases hflag : fn.requires.isSome || !fn.specs.isEmpty with
  | true =>
    rw [hflag] at hm
    intro tySizes hval hloc
    rw [← monoAdmitted_lowerBody_iff (adts := adts) (bodies := bodies)
          (tySizes := tySizes) hcallsOrig,
        hres]
    apply hm tySizes hval
    rw [← hres, localLayoutsAdmitted_lowerBody]
    exact hloc
  | false =>
    rw [hflag] at hm
    cases hm with
    | intro tySizes hty =>
      refine ⟨tySizes, hty.1, ?_, ?_⟩
      · have hloc := hty.2.1
        rw [← hres, localLayoutsAdmitted_lowerBody] at hloc
        exact hloc
      · rw [← monoAdmitted_lowerBody_iff (adts := adts) (bodies := bodies)
              (tySizes := tySizes) hcallsOrig,
            hres]
        exact hty.2.2

/-- Equivalence of `SafetyPre` across in-place lowering `lowerBody` when
`lowerBody body = target`, `target` has no `.call1` terminators, and
`hasPinnedCoupledWaiver fn tcb = false`. -/
theorem safetyPre_of_lowerBody_eq {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} {fn : CapturedFn}
    {body target : MirBody} {s : MirState} {tcb : List TCBItem}
    (hres : lowerBody body = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    SafetyPre adts bodies adtInv fn body s tcb ↔
      initMirState adts bodies target s ∧
      argsMatchInv adts adtInv target.localCount s target.argTys ∧
      (fn.isUnsafe = true → fn.safetyPre s) := by
  have hcallsOrig :
      body.blocks.all (fun bb => !isCall1 bb.terminator) = true := by
    rw [← noCall_lowerBody body, hres]
    exact hcalls
  have hinitIff :=
    initMirState_lowerBody_iff (adts := adts) (bodies := bodies)
      (b := body) (s := s) hcallsOrig
  have hlc : body.localCount = target.localCount := by
    rw [← lowerBody_localCount body, hres]
  have hargs : body.argTys = target.argTys := by
    rw [← lowerBody_argTys body, hres]
  dsimp [SafetyPre]
  rw [hpin, ← hinitIff, hres, hlc, hargs]
  exact Iff.rfl

/-- Discharge `FnBodySafetyVerified` for `body` from an `ExecNormal` proof on
its normalized body `target = lowerBody body`. -/
theorem execNormal_fnBodySafetyVerified_of_lowerBody {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    (body target : MirBody) {tcb : List TCBItem}
    (hres : lowerBody body = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcwf : ContractWellFormed adts bodies fn target)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl)
    (h_exec : ∀ s,
      initMirState adts bodies target s →
      argsMatchInv adts adtInv target.localCount s target.argTys →
      (fn.isUnsafe = true → fn.safetyPre s) →
      ExecNormal adts bodies target s (fun r =>
        r.value.valid adts adtInv r.state target.localCount target.retTy)) :
    FnBodySafetyVerified adts bodies adtInv fn body tcb := by
  have hcwfBody := contractWellFormed_of_lowerBody hres hcalls hcwf
  have hcallsOrig :
      body.blocks.all (fun bb => !isCall1 bb.terminator) = true := by
    rw [← noCall_lowerBody body, hres]
    exact hcalls
  have hlc : body.localCount = target.localCount := by
    rw [← lowerBody_localCount body, hres]
  have hret : body.retTy = target.retTy := by
    rw [← lowerBody_retTy body, hres]
  refine execNormal_fnBodySafetyVerified fn body hcwfBody ?_
  intro s hpre
  have ⟨hinitT, hargsT, hsafetyT⟩ :=
    (safetyPre_of_lowerBody_eq hres hcalls hpin).mp hpre
  rw [hlc, hret]
  have hexecLow :
      ExecNormal adts bodies (lowerBody body) s
        (fun r =>
          r.value.valid adts adtInv r.state target.localCount target.retTy) := by
    rw [hres]
    exact h_exec s hinitT hargsT hsafetyT
  exact lowerBody_simulates hcallsOrig
    (stmtIdxInvariant_valid adts adtInv target.localCount target.retTy)
    hinitT.1.2.1 hinitT.1.2.2.1 hinitT.1.2.2.2.1 hexecLow

/-- Discharge `FnVerifiedAndRetInv` for `fn` from an `ExecNormal` proof on its
normalized body `target = lowerBody (fn.resolveBody bodies)`. -/
theorem execNormal_fnVerifiedAndRetInv_of_lowerBody {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} (fn : CapturedFn)
    (target : MirBody) {tcb : List TCBItem}
    (hres : lowerBody (fn.resolveBody bodies) = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hcwf : ContractWellFormed adts bodies fn target)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl)
    (h_exec : ∀ s,
      initMirState adts bodies target s →
      argsMatchInv adts adtInv target.localCount s target.argTys →
      (fn.isUnsafe = true → fn.safetyPre s) →
      ExecNormal adts bodies target s (fun r =>
        r.value.valid adts adtInv r.state target.localCount target.retTy)) :
    FnVerifiedAndRetInv adts bodies adtInv fn tcb :=
  execNormal_fnBodySafetyVerified_of_lowerBody fn (fn.resolveBody bodies)
    target hres hcalls hcwf hpin h_exec

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

theorem mem_cons_eq_or_mem {α : Type} {x y : α} {ys : List α}
    (h : x ∈ y :: ys) : x = y ∨ x ∈ ys := by
  cases h with
  | head => exact Or.inl rfl
  | tail _ hm => exact Or.inr hm

/-- The unwaivable contract well-formedness and behavioral verification
obligations of the only function of an unwaived single-function crate,
extracted from `CrateTheorem`. -/
theorem crateTheorem_single_fnVerified {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {tcb : List TCBItem}
    (h : CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := tcb }) :
    ContractWellFormed adts bodies fn (fn.resolveBody bodies) ∧
    FnBodyVerified adts bodies (denoteAdtInv adts) fn
      (fn.resolveBody bodies) tcb := by
  have hcwf : ContractWellFormed adts bodies fn (fn.resolveBody bodies) :=
    h.2.2.2.2.1.1.1
  cases h.2.2.2.2.2.2.2.2.1 with
  | inl hVer => exact ⟨hcwf, hVer.1⟩
  | inr hIn => cases hIn

/-- A function that fails from some state satisfying `SafetyPre` makes a
single-function crate unverifiable. -/
theorem crateTheorem_single_rejects_of_safetyPre_fail {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {tcb : List TCBItem}
    (s0 : MirState)
    (hpre :
      SafetyPre adts bodies (denoteAdtInv adts) fn (fn.resolveBody bodies) s0
        tcb)
    (hfail : ExecFail adts bodies (fn.resolveBody bodies) s0) :
    ¬ CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := tcb } := by
  intro hCrate
  have hWF := (crateTheorem_single_fnVerified hCrate).2.2.2
  cases execFail_reaches hfail with
  | intro n hr => exact (hWF s0 hpre).1 hpre.1 n [] .failed hr

/-- A function that fails from some state satisfying its effective precondition
makes a single-function crate unverifiable. -/
theorem crateTheorem_single_rejects_of_fail {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {tcb : List TCBItem}
    (s0 : MirState)
    (hpre : fnEffectivePre adts bodies (denoteAdtInv adts) fn s0)
    (hfail : ExecFail adts bodies (fn.resolveBody bodies) s0)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    ¬ CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := tcb } := by
  refine crateTheorem_single_rejects_of_safetyPre_fail s0 ?_ hfail
  dsimp [SafetyPre]
  rw [hpin]
  exact ⟨hpre.1, hpre.2.1, fun _ => hpre.2.2⟩

/-- A function whose required constants are not total across valid `tySizes`
makes a single-function crate unverifiable (`ContractWellFormed` fails
closed). -/
theorem crateTheorem_single_rejects_of_not_constsTotal {adts : List AdtDecl}
    {bodies : List BodyDecl} {fn : CapturedFn} {tcb : List TCBItem}
    (hnot : ¬ ConstsTotal adts bodies (fn.resolveBody bodies)) :
    ¬ CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := tcb } :=
  fun hCrate => hnot (crateTheorem_single_fnVerified hCrate).1.2.1

/-- Generic single-function `CrateTheorem` discharge for a function with
`fn.debugBodyId = none`, given `NoDupIds` for `bodies`, its per-function
`FnVerifiedAndRetInv` proof `h_ver`, and a proof of its `ContractPost` on
`SafetyPre ∧ fn.safetyPre`. -/
theorem verify_single_fn_crate_gen {adts : List AdtDecl}
    {bodies : List BodyDecl} (fn : CapturedFn) {tcb : List TCBItem}
    (h_dbg : fn.debugBodyId = none := by rfl)
    (h_bodies_nodup : NoDupIds (bodies.map (fun d => d.id.index)))
    (h_adm : AdmissibleAdtInv adts (denoteAdtInv adts))
    (h_ver : FnVerifiedAndRetInv adts bodies (denoteAdtInv adts) fn tcb)
    (h_specs :
      MirSem adts bodies (fn.resolveBody bodies) ≤
        (MirLang adts bodies).SpecOn
          (fun s =>
            SafetyPre adts bodies (denoteAdtInv adts) fn
              (fn.resolveBody bodies) s tcb ∧
            fn.safetyPre s)
          (ContractPost adts bodies fn)) :
    CrateTheorem {
      adts := adts
      bodies := bodies
      functions := [fn]
      tcb := tcb
    } := by
  have hcwf : FnContractWellFormed adts bodies fn := by
    unfold FnContractWellFormed
    rw [h_dbg]
    exact ⟨h_ver.1, True.intro⟩
  have hfnVer : FnVerified adts bodies (denoteAdtInv adts) fn tcb := by
    unfold FnVerified
    rw [h_dbg]
    exact ⟨verified_split h_ver.2 h_specs, True.intro⟩
  exact ⟨(by intro h; cases h),
   h_bodies_nodup,
   ⟨True.intro, True.intro⟩,
   h_adm,
   ⟨hcwf, True.intro⟩,
   ⟨(by intro h; cases h),
    ⟨True.intro, True.intro⟩,
    True.intro,
    ⟨Or.inl hfnVer, True.intro⟩⟩⟩

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
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
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
      | ref _ _ _ _ => cases hvty
      | atomicLoc _ => cases hvty
      | ordering _ => cases hvty
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

/-- `idCopyBody` satisfies `FnBodySafetyVerified` for any `fn` and `body` whose
lowered body is `idCopyBody`. -/
theorem idCopyBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = idCopyBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb :=
  execNormal_fnBodySafetyVerified_of_lowerBody fn body idCopyBody hres rfl
    (contractWellFormed_of_simple mkStaticBodyWf rfl rfl) hpin
    (fun s hinitS _ _ => (idCopyBody_execNormal s hinitS).map (fun _ h => h.2))

/-- `idMoveBody` executes to normal termination returning the initial `_1`
under any `bodies` table. -/
theorem idMoveBody_execNormal {bodies : List BodyDecl} (s : MirState)
    (hinit : initMirState [] bodies idMoveBody s) :
    ExecNormal [] bodies idMoveBody s (fun r =>
      s.locals 1 = some r.value ∧
      r.value.valid [] defaultAdtInv r.state 2 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 mem0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
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
      | ref _ _ _ _ => cases hvty
      | atomicLoc _ => cases hvty
      | ordering _ => cases hvty
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

/-- `idMoveBody` satisfies `FnBodySafetyVerified` for any `fn` and `body` whose
lowered body is `idMoveBody`. -/
theorem idMoveBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = idMoveBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb :=
  execNormal_fnBodySafetyVerified_of_lowerBody fn body idMoveBody hres rfl
    (contractWellFormed_of_simple mkStaticBodyWf rfl rfl) hpin
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

/-- Canonical `Runtime(PostCleanup)` MIR body for
`pub fn load_relaxed(a: &AtomicUsize) -> usize { a.load(Ordering::Relaxed) }`. -/
def loadRelaxedBody : MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 4
  blocks := [
    { stmts := [
        .storageLive ⟨2⟩,
        .assign (locPlace 2) (.ref (derefPlace 1)),
        .storageLive ⟨3⟩,
        .assign (locPlace 3) (.use (.constVal (.ordering .relaxed)))
      ]
      terminator :=
        .callAtomicLoad (locPlace 0) (.move (locPlace 2))
          (.move (locPlace 3)) ⟨1⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

/-- `loadRelaxedBody` executes across the demonic weak-memory choice in `bb0`
to normal termination in `bb1`, returning `MirVal.usize msg.bits` for some
visible modification-order message `msg ∈ s.mem.visibleAtomicMsgs loc`. -/
theorem loadRelaxedBody_execChoiceNormal {bodies : List BodyDecl}
    (s : MirState)
    (hinit : initMirState [] bodies loadRelaxedBody s) :
    ExecChoiceNormal [] bodies loadRelaxedBody s (fun r =>
      (∃ loc msg,
        s.locals 1 = some (.atomicLoc loc) ∧
        msg ∈ s.mem.visibleAtomicMsgs loc ∧
        r.value = .usize msg.bits) ∧
      r.value.valid [] defaultAdtInv r.state 4 .usize) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0
       nextFrameId0 adtPad0 ubChecks0 mem0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit => cases hvty
      | usize _ => cases hvty
      | bool _ => cases hvty
      | unit => cases hvty
      | adt _ _ => cases hvty
      | fieldCons _ _ => cases hvty
      | bytes _ _ => cases hvty
      | ref _ _ _ _ => cases hvty
      | ordering _ => cases hvty
      | atomicLoc loc =>
        have hvis : mem0.visibleAtomicMsgs loc ≠ [] := hvty
        refine .step rfl ?_
        apply ExecChoiceNormal.step
        · dsimp only [evalMirStep, evalMirStepDepth, evalMirStepWith,
            lookupAt, List.foldr, Option.getD, evalMirStmt, evalRefPlace,
            evalRefProj, assignPlace, locPlace, derefPlace,
            loadRelaxedBody, updateLocal]
          rw [hv1]
          rfl
        · refine .step rfl (.step rfl ?_)
          cases hlist : mem0.visibleAtomicMsgs loc with
          | nil => exact False.elim (hvis hlist)
          | cons head tail =>
            let localsAfterMoves : Nat → Option MirVal :=
              updateLocal
                (updateLocal
                  (updateLocal
                    (updateLocal
                      (updateLocal
                        (updateLocal locals0 2 none)
                        2 (some (.atomicLoc loc)))
                      3 none)
                    3 (some (.ordering .relaxed)))
                  2 none)
                3 none
            let stepMsg (msg : AtomicMsg) : MirState := {
              locals :=
                updateLocal localsAfterMoves 0 (some (.usize msg.bits))
              localGens := bumpGen (bumpGen (fun _ => 0) 2) 3
              block := 1
              stmtIdx := 0
              tySizes := tySizes0
              curBody := none
              stack := []
              frameId := 0
              nextFrameId := 1
              adtPad := adtPad0
              ubChecks := ubChecks0
              mem := mem0.applyAtomicLoad .relaxed msg
            }
            apply ExecChoiceNormal.choice (head := stepMsg head)
              (tail := tail.map stepMsg)
            · change (match mem0.visibleAtomicMsgs loc with
                | [] => RawStep.failed
                | head :: tail =>
                  RawStep.choiceList (stepMsg head) (tail.map stepMsg)) = _
              rw [hlist]
            · intro s' hs'
              cases mem_cons_map stepMsg head tail hs' with
              | intro msg hmsg =>
                have hmem : msg ∈ head :: tail := hmsg.1
                have hs'Eq : s' = stepMsg msg := hmsg.2
                subst hs'Eq
                refine .step rfl (.step rfl (.normal rfl ?_))
                refine ⟨⟨loc, msg, hv1, ?_, rfl⟩, True.intro⟩
                rw [hlist]
                exact hmem

/-- `loadRelaxedBody` satisfies `EnsuresAtomicLoad 1` under any `bodies`. -/
theorem loadRelaxedBody_satisfies_ensures {bodies : List BodyDecl} :
    MirSem [] bodies loadRelaxedBody ≤ EnsuresAtomicLoad 1 [] bodies :=
  execChoiceNormal_spec (fun s hinit =>
    (loadRelaxedBody_execChoiceNormal s hinit).map (fun _ h => h.1))

/-- `loadRelaxedBody` satisfies `wellFormed (MirLang [] bodies)`. -/
theorem loadRelaxedBody_satisfies_wellFormed {bodies : List BodyDecl} :
    MirSem [] bodies loadRelaxedBody ≤ wellFormed (MirLang [] bodies) :=
  Preorder.le_trans loadRelaxedBody_satisfies_ensures
    (ensuresAtomicLoad_le_wellFormed 1)

/-- `loadRelaxedBody` satisfies `FnBodySafetyVerified` for any `fn` and `body`
equal to `loadRelaxedBody`. -/
theorem loadRelaxedBody_verified_of_eq {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : body = loadRelaxedBody) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb := by
  rw [hres]
  exact execChoiceNormal_fnBodySafetyVerified fn loadRelaxedBody
    (contractWellFormed_of_simple mkStaticBodyWf rfl rfl)
    (fun s hpre =>
      (loadRelaxedBody_execChoiceNormal s hpre.1).map (fun _ h => h.2))

/-- `loadRelaxedBody` satisfies `ContractPost` when
`fn.specs = [.ensuresAtomicLoad 1]`. -/
theorem loadRelaxedBody_specs_of_eq {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : body = loadRelaxedBody)
    (hspecs : fn.specs = [.ensuresAtomicLoad 1]) :
    MirSem [] bodies body ≤
      (MirLang [] bodies).SpecOn
        (fun s => SafetyPre [] bodies defaultAdtInv fn body s tcb ∧ fn.safetyPre s)
        (ContractPost [] bodies fn) := by
  rw [hres]
  exact specOn_contractPost_ensuresAtomicLoad1 hspecs (fun s hpre =>
    (loadRelaxedBody_execChoiceNormal s hpre.1.1).map (fun _ h => h.1))

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
    } := by
  intro bodies
  have hargs : argsMatchInv [] defaultAdtInv 5 pmeInitState [.param 0] :=
    ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies (transmuteCheckedBody ⟨0⟩) pmeInitState :=
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
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
    } := by
  intro bodies
  have hargs : argsMatchInv [] defaultAdtInv 4 pmeInitState [.param 0] :=
    ⟨⟨.bytes 8 0, rfl, rfl⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies transmuteUncheckedBody pmeInitState :=
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
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

theorem concreteTransmuteCaller_noRequires {bodies : List BodyDecl}
    {calleeId constId : BodyId} {dstTy : MirTy} {c : Option MirBody}
    (hcallee : findBody bodies calleeId = some (transmuteCheckedBody constId))
    (hc : RequiresConst bodies
      (some (concreteTransmuteCallerBody calleeId dstTy)) c) :
    False := by
  cases hc with
  | direct hmem => cases hmem
  | viaConst hmem _ => cases hmem
  | viaCall hbb hterm hrest =>
    cases hbb with
    | head =>
      cases hterm
      rw [hcallee] at hrest
      change RequiresConst bodies
        (some (transmuteCheckedBodyAt constId .usize dstTy)) _ at hrest
      exact noRequires_of_simple rfl rfl hrest
    | tail _ hbb1 =>
      cases hbb1 with
      | head => cases hterm
      | tail _ hnil => cases hnil

theorem concreteTransmuteCaller_constsTotal {bodies : List BodyDecl}
    {calleeId constId : BodyId} {dstTy : MirTy}
    (hcallee : findBody bodies calleeId = some (transmuteCheckedBody constId)) :
    ConstsTotal [] bodies (concreteTransmuteCallerBody calleeId dstTy) :=
  fun _ _ _ hc => False.elim (concreteTransmuteCaller_noRequires hcallee hc)

theorem concreteTransmuteCaller_monoAdmitted {bodies : List BodyDecl}
    {calleeId constId : BodyId} {dstTy : MirTy}
    (hcallee : findBody bodies calleeId = some (transmuteCheckedBody constId))
    (tySizes : Nat → Nat) :
    MonoAdmitted [] bodies tySizes
      (concreteTransmuteCallerBody calleeId dstTy) :=
  fun _ hc => False.elim (concreteTransmuteCaller_noRequires hcallee hc)

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
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
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
      | ref _ _ _ _ => cases hvty
      | atomicLoc _ => cases hvty
      | ordering _ => cases hvty
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
`FnBodySafetyVerified` for any `fn` and `body` resolving to it when `calleeId`
and `constId` resolve in `bodies`. -/
theorem concreteTransmuteCaller_verified_of_resolve {bodies : List BodyDecl}
    {calleeId constId : BodyId} {tcb : List TCBItem} (fn : CapturedFn)
    (body : MirBody := fn.resolveBody bodies)
    (hres : body = concreteTransmuteCallerBody calleeId .usize)
    (hcallee : findBody bodies calleeId = some (transmuteCheckedBody constId))
    (hconst : findBody bodies constId = some sizeEqConstBody) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb := by
  have hwf : StaticBodyWf [] (concreteTransmuteCallerBody calleeId .usize) :=
    mkStaticBodyWf
      (hcount := Nat.le_succ_of_le (Nat.le_refl 2))
      (hblocks := Nat.zero_lt_succ 1)
  have hcwf :
      ContractWellFormed [] bodies fn
        (concreteTransmuteCallerBody calleeId .usize) :=
    ⟨hwf,
     concreteTransmuteCaller_constsTotal hcallee,
     monoConstsWf_of_all_monoAdmitted hwf
       (concreteTransmuteCaller_monoAdmitted hcallee)⟩
  rw [hres]
  exact execNormal_fnBodySafetyVerified fn
    (concreteTransmuteCallerBody calleeId .usize) hcwf
    (fun s hpre => concreteTransmuteCaller_execNormal hcallee hconst s hpre.1)

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
  have hSem := (crateTheorem_single_fnVerified hCrate).2.2.2
  have hargs : argsMatchInv [] defaultAdtInv 3 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit :
      initMirState [] bodies (concreteTransmuteCallerBody ⟨1⟩ .bool)
        singleArgUsizeInitState :=
    ⟨mkInitEntryState hargs,
     concreteTransmuteCaller_constsTotal rfl,
     concreteTransmuteCaller_monoAdmitted rfl _⟩
  have hpre :
      SafetyPre [] bodies defaultAdtInv
        { name := fnName, bodyId := ⟨2⟩ }
        (concreteTransmuteCallerBody ⟨1⟩ .bool)
        singleArgUsizeInitState [] :=
    ⟨hinit, hargs, fun h => by cases h⟩
  cases hSem singleArgUsizeInitState hpre with
  | intro hdef hval =>
    cases execCompileTimeError_reaches hexec with
    | intro n hr =>
      have hpfx :
          (MirSem [] bodies (concreteTransmuteCallerBody ⟨1⟩ .bool)
            singleArgUsizeInitState).val hdef
            (.terminated [] .compileTimeError) :=
        ⟨hinit, n, hr⟩
      exact (hval _ hpfx).1.2 [] rfl

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
      have hentry := hinit.1
      have hb : block0 = 0 := hentry.1
      have hs : stmtIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      have hst : stack0 = [] := hentry.2.2.2.1
      have hfid : frameId0 = 0 := hentry.2.2.2.2.1
      have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
      have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
      subst hb hs hc hst hfid hnfid hlg
      cases (initEntryState_argsMatch hentry).1 with
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
        | ref _ _ _ _ => cases hvty
        | atomicLoc _ => cases hvty
        | ordering _ => cases hvty
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

/-- `makeNonZeroBody` satisfies `FnBodySafetyVerified` for any `fn` and `body`
whose lowered body is `makeNonZeroBody`. -/
theorem makeNonZeroBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem} {repr : AdtRepr}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = makeNonZeroBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    FnBodySafetyVerified [nonZeroAdtDecl 0 repr] bodies (nonZeroAdtInv repr) fn
      body tcb := by
  have hl0 :
      LocalLayoutsAdmitted [nonZeroAdtDecl 0 repr] makeNonZeroBody
        (fun _ => 0) = true := by
    cases hrepr with
    | inl h | inr h => subst h; rfl
  have hl1 :
      LocalLayoutsAdmitted [nonZeroAdtDecl 0 repr] makeNonZeroBody
        (fun _ => 1) = true := by
    cases hrepr with
    | inl h | inr h => subst h; rfl
  exact execNormal_fnBodySafetyVerified_of_lowerBody fn body makeNonZeroBody
    hres rfl
    (contractWellFormed_of_simple (mkStaticBodyWf (hl0 := hl0) (hl1 := hl1))
      rfl rfl)
    hpin (fun s hinitS _ _ => makeNonZeroBody_execNormal s hinitS hrepr)

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
    | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 mem0 =>
      have hentry := hinit.1
      have hb : block0 = 0 := hentry.1
      have hs : stmtIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      have hst : stack0 = [] := hentry.2.2.2.1
      have hfid : frameId0 = 0 := hentry.2.2.2.2.1
      have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
      have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
      subst hb hs hc hst hfid hnfid hlg
      cases (initEntryState_argsMatch hentry).1 with
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
        | ref _ _ _ _ => cases hvty
        | atomicLoc _ => cases hvty
        | ordering _ => cases hvty
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

/-- `newUncheckedBody` satisfies `FnBodySafetyVerified` for any `unsafe fn`
(`fn.isUnsafe = true`) whose lowered body is `newUncheckedBody` with
`requires = newUncheckedRequires`. -/
theorem newUncheckedBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem} {repr : AdtRepr}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = newUncheckedBody)
    (hunsafe : fn.isUnsafe = true)
    (hreq : fn.requires = newUncheckedRequires)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    FnBodySafetyVerified [nonZeroAdtDecl 0 repr] bodies (nonZeroAdtInv repr) fn
      body tcb := by
  have hl0 :
      LocalLayoutsAdmitted [nonZeroAdtDecl 0 repr] newUncheckedBody
        (fun _ => 0) = true := by
    cases hrepr with
    | inl h | inr h => subst h; rfl
  have hl1 :
      LocalLayoutsAdmitted [nonZeroAdtDecl 0 repr] newUncheckedBody
        (fun _ => 1) = true := by
    cases hrepr with
    | inl h | inr h => subst h; rfl
  refine execNormal_fnBodySafetyVerified_of_lowerBody fn body newUncheckedBody
    hres rfl
    (contractWellFormed_of_simple (mkStaticBodyWf (hl0 := hl0) (hl1 := hl1))
      rfl rfl)
    hpin ?_
  intro s hinitS _ hsafetyImp
  have hsafetyS : newUncheckedSafetyPre s := by
    have h1 := hsafetyImp hunsafe
    dsimp [CapturedFn.safetyPre] at h1
    rw [hreq] at h1
    exact h1
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
    | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 mem0 =>
      have hentry := hinit.1
      have hb : block0 = 0 := hentry.1
      have hs : stmtIdx0 = 0 := hentry.2.1
      have hc : curBody0 = none := hentry.2.2.1
      have hst : stack0 = [] := hentry.2.2.2.1
      have hfid : frameId0 = 0 := hentry.2.2.2.2.1
      have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
      have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
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
        | ref _ _ _ _ => cases hvinv
        | atomicLoc _ => cases hvinv
        | ordering _ => cases hvinv
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
          | ref _ _ _ _ => cases hvinv.2.2
          | atomicLoc _ => cases hvinv.2.2
          | ordering _ => cases hvinv.2.2
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

/-- `getUncheckedNonZeroBodyAt 0 moveFinal` satisfies `FnBodySafetyVerified`
for any `fn` and `body` whose lowered body is `getUncheckedNonZeroBodyAt 0
moveFinal`. -/
theorem getUncheckedNonZeroBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem} {repr : AdtRepr}
    (moveFinal : Bool) (fn : CapturedFn)
    (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = getUncheckedNonZeroBodyAt 0 moveFinal)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hrepr : repr = .rust ∨ repr = .transparent) :
    FnBodySafetyVerified [nonZeroAdtDecl 0 repr] bodies (nonZeroAdtInv repr) fn
      body tcb := by
  have hl0 :
      LocalLayoutsAdmitted [nonZeroAdtDecl 0 repr]
        (getUncheckedNonZeroBodyAt 0 moveFinal) (fun _ => 0) = true := by
    cases hrepr with
    | inl h | inr h => subst h; rfl
  have hl1 :
      LocalLayoutsAdmitted [nonZeroAdtDecl 0 repr]
        (getUncheckedNonZeroBodyAt 0 moveFinal) (fun _ => 1) = true := by
    cases hrepr with
    | inl h | inr h => subst h; rfl
  have hwf :
      StaticBodyWf [nonZeroAdtDecl 0 repr]
        (getUncheckedNonZeroBodyAt 0 moveFinal) :=
    mkStaticBodyWf
      (hcount := Nat.le_succ_of_le
        (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2))))
      (hblocks := Nat.zero_lt_succ 2)
      (hl0 := hl0)
      (hl1 := hl1)
  exact execNormal_fnBodySafetyVerified_of_lowerBody fn body
    (getUncheckedNonZeroBodyAt 0 moveFinal) hres
    (by cases moveFinal <;> rfl)
    (contractWellFormed_of_simple hwf rfl (by cases moveFinal <;> rfl))
    hpin
    (fun s hinitS hargsS _ =>
      getUncheckedNonZeroBody_execNormal moveFinal s hinitS hargsS hrepr)

/-- Canary: a safe function `buggy_zero` that returns
`NonZeroUsize { val: 0 }` violates `SafetyPost` and refutes
`CrateTheorem`. -/
theorem canary_buggy_zero_rejected (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := buggyZeroBody }]
    ¬ CrateTheorem {
      adts := [nonZeroAdtDecl 0]
      bodies := bodies
      functions := [{ name := fnName, bodyId := ⟨0⟩ }]
    } := by
  intro bodies hCrate
  have hSafe := (crateTheorem_single_fnVerified hCrate).2.2.2
  let s0 : MirState := singleArgUsizeInitState
  have hargs : argsMatchInv [nonZeroAdtDecl 0] defaultAdtInv 2 s0 [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [nonZeroAdtDecl 0] bodies buggyZeroBody s0 :=
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
  have hexec :
      ExecNormal [nonZeroAdtDecl 0] bodies buggyZeroBody s0
        (fun r => r.value = .adt 0 (.usize 0)) :=
    .step rfl (.normal rfl rfl)
  have hpre :
      SafetyPre [nonZeroAdtDecl 0] bodies nonZeroAdtInv
        { name := fnName, bodyId := ⟨0⟩ } buggyZeroBody s0 :=
    ⟨hinit,
     ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩,
     fun _ => True.intro⟩
  cases hSafe s0 hpre with
  | intro hdef hval =>
    cases execNormal_reaches hexec with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        have hpfx :
            (MirSem [nonZeroAdtDecl 0] bodies buggyZeroBody s0).val hdef
              (.terminated [] (.normal v)) :=
          ⟨hinit, n, hv.1⟩
        have hinv := (hval _ hpfx).1.1 [] v rfl
        have hv_eq : v.value = .adt 0 (.usize 0) := hv.2
        rw [hv_eq] at hinv
        exact hinv.2.1 rfl

/-- Canary: a safe function (`isUnsafe = false`) with body `newUncheckedBody`
cannot use `requires = newUncheckedRequires` (`/// anneal:requires x != 0`) to
avoid violating `NonZeroUsize`'s representation invariant at `x = 0`, because
`SafetyPre` only includes `fn.safetyPre` when `fn.isUnsafe = true`. -/
theorem canary_safe_new_unchecked_with_requires_rejected (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := newUncheckedBody }]
    ¬ CrateTheorem {
      adts := [nonZeroAdtDecl 0]
      bodies := bodies
      functions := [{
        name := fnName
        bodyId := ⟨0⟩
        isUnsafe := false
        requires := newUncheckedRequires
      }]
    } := by
  intro bodies hCrate
  have hSafe := (crateTheorem_single_fnVerified hCrate).2.2.2
  let s0 : MirState := singleArgUsizeInitState
  have hargs : argsMatchInv [nonZeroAdtDecl 0] defaultAdtInv 3 s0 [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [nonZeroAdtDecl 0] bodies newUncheckedBody s0 :=
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
  have hexec :
      ExecNormal [nonZeroAdtDecl 0] bodies newUncheckedBody s0
        (fun r => r.value = .adt 0 (.usize 0)) :=
    .step rfl (.step rfl (.step rfl (.step rfl (.normal rfl rfl))))
  have hpre :
      SafetyPre [nonZeroAdtDecl 0] bodies nonZeroAdtInv
        { name := fnName
          bodyId := ⟨0⟩
          isUnsafe := false
          requires := newUncheckedRequires }
        newUncheckedBody s0 :=
    ⟨hinit,
     ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩,
     fun h => by cases h⟩
  cases hSafe s0 hpre with
  | intro hdef hval =>
    cases execNormal_reaches hexec with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        have hpfx :
            (MirSem [nonZeroAdtDecl 0] bodies newUncheckedBody s0).val hdef
              (.terminated [] (.normal v)) :=
          ⟨hinit, n, hv.1⟩
        have hinv := (hval _ hpfx).1.1 [] v rfl
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

/-- Negative canary: returning an uninitialized `_0` fails at step `1`. -/
theorem canary_uninit_return_violates_wellFormed :
    ¬ (MirSem [] [] uninitReturnBody ≤ wellFormed (MirLang [] [])) := by
  intro hWF
  let s0 : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hinit : initMirState [] [] uninitReturnBody s0 :=
    ⟨mkInitEntryState (fun _ _ _ => rfl),
     constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
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
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
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

/-- MIR body that accepts `_1 : &AtomicUsize` (`MirTy.refAtomicUsize`) and
returns constant `0` instead of loading from `_1`. -/
def wrongAtomicReturnZeroBody : MirBody where
  argTys := [.refAtomicUsize]
  retTy := .usize
  localCount := 2
  blocks := [
    { stmts := [.assign (locPlace 0) (.use (.constVal (.usize 0)))]
      terminator := .return_ }
  ]

/-- Negative canary for weak-memory atomic loads: returning constant `0` without
reading `_1` violates `EnsuresAtomicLoad 1` when location `0`'s only visible
modification-order message has `bits = 1`. -/
theorem canary_wrong_atomic_load_violates_ensures :
    ¬ (MirSem [] [] wrongAtomicReturnZeroBody ≤ EnsuresAtomicLoad 1 [] []) := by
  intro hEns
  let msg0 : AtomicMsg := { loc := 0, ts := 0, bits := 1, relView := View.bot }
  let mem0 : MemState := { MemState.empty with atomicMsgs := [msg0] }
  let s0 : MirState := {
    locals := updateLocal (fun _ => none) 1 (some (.atomicLoc 0))
    block := 0
    stmtIdx := 0
    mem := mem0
  }
  have hvis : mem0.visibleAtomicMsgs 0 ≠ [] := by
    intro hnil
    cases hnil
  have hargs : argsMatchInv [] defaultAdtInv 2 s0 [.refAtomicUsize] :=
    ⟨⟨MirVal.atomicLoc 0, rfl, hvis⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] [] wrongAtomicReturnZeroBody s0 :=
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
  have hexec :
      ExecNormal [] [] wrongAtomicReturnZeroBody s0
        (fun r => r.value = .usize 0) :=
    .step rfl (.normal rfl rfl)
  cases hEns s0 True.intro with
  | intro hdef hval =>
    cases execNormal_reaches hexec with
    | intro n hn =>
      cases hn with
      | intro v hv =>
        have hpfx :
            (MirSem [] [] wrongAtomicReturnZeroBody s0).val hdef
              (.terminated [] (.normal v)) :=
          ⟨hinit, n, hv.1⟩
        have hpost := hval _ hpfx [] v rfl
        cases hpost with
        | intro loc hpost2 =>
          cases hpost2 with
          | intro msg hprops =>
            have hloc : s0.locals 1 = some (MirVal.atomicLoc 0) := rfl
            have hloc_eq := hprops.1
            rw [hloc] at hloc_eq
            injection hloc_eq with hval'
            injection hval' with hloc0
            subst hloc0
            have hmem : msg ∈ [msg0] := hprops.2.1
            cases hmem with
            | head =>
              have hret := hprops.2.2
              rw [hv.2] at hret
              injection hret with hbits
              cases hbits
            | tail _ htail =>
              cases htail

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
    fnEffectivePre [] bodies defaultAdtInv fn idRefCallerState ∧
    ∃ s1,
      evalMirStep [] bodies idRefBody idRefCallerState = .silent s1 ∧
      evalMirStep [] bodies idRefBody s1 =
        .terminated (.normal ⟨.ref 0 0 ⟨2⟩, s1⟩) := by
  intro bodies fn
  have hrest : ∀ j, 2 ≤ j → j < 2 → idRefCallerState.locals j = none :=
    fun _ hge hlt => False.elim (Nat.not_le_of_gt hlt hge)
  have hargs : argsMatchInv [] defaultAdtInv 2 idRefCallerState [.ref .usize] :=
    ⟨⟨.ref 0 0 ⟨2⟩, rfl, rfl, Nat.le_refl 2, True.intro⟩, hrest⟩
  exact ⟨⟨⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩,
    hargs, True.intro⟩, _, rfl, rfl⟩

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

/-- A constant body with an argument is never a successful constant and fails
`.evalConst` because `evalMirStmt` requires `cBody.argTys.isEmpty`. -/
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
    (∀ tySizes, ¬ ConstSucceeds [] [] tySizes branchingArgConstBody) ∧
    evalMirStep [] bodies evalBranchingArgConstBody
      (constEntryState (fun _ => 8)) = .failed := by
  refine ⟨?_, rfl⟩
  intro _ h
  cases h.1

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
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
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
    } := by
  intro bodies
  let s0 : MirState := { locals := fun _ => none, block := 0, stmtIdx := 0 }
  have hargs : argsMatchInv [nonZeroAdtDecl 0] defaultAdtInv 2 s0 [] :=
    fun _ _ _ => rfl
  have hargsInv : argsMatchInv [nonZeroAdtDecl 0] nonZeroAdtInv 2 s0 [] :=
    fun _ _ _ => rfl
  have hinit : initMirState [nonZeroAdtDecl 0] bodies (boomBody ⟨0⟩) s0 :=
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
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
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
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
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
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
      | ref _ _ _ _ => cases hvty
      | atomicLoc _ => cases hvty
      | ordering _ => cases hvty
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

/-- `idNonZeroUncheckedBody` satisfies `FnBodySafetyVerified` for any
`unsafe fn` (`fn.isUnsafe = true`) whose lowered body is
`idNonZeroUncheckedBody` with `fn.requires = newUncheckedRequires`. -/
theorem idNonZeroUnchecked_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = idNonZeroUncheckedBody)
    (hunsafe : fn.isUnsafe = true)
    (hreq : fn.requires = newUncheckedRequires)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb := by
  have hwf : StaticBodyWf [] idNonZeroUncheckedBody :=
    mkStaticBodyWf
      (hcount := Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2)))
      (hblocks := Nat.zero_lt_succ 2)
  refine execNormal_fnBodySafetyVerified_of_lowerBody fn body
    idNonZeroUncheckedBody hres rfl
    (contractWellFormed_of_simple hwf rfl rfl) hpin ?_
  intro s hinitS _ hsafetyImp
  have hsafetyS : newUncheckedSafetyPre s := by
    have h1 := hsafetyImp hunsafe
    dsimp [CapturedFn.safetyPre] at h1
    rw [hreq] at h1
    exact h1
  exact (idNonZeroUnchecked_execNormal s hinitS hsafetyS).map (fun _ h => h.2)

/-- Positive canary (`P3-M1`): an `unsafe fn` with a non-trivial `safetyPre`
(`newUncheckedSafetyPre`, which fails at `x = 0`) and a user specification
`specs := [.ensuresEqArg 1]` satisfies `CrateTheorem` because `SafetyPre`
includes `fn.safetyPre` on `unsafe fn` and `EffectivePost` restricts
`ContractPost` to `fn.safetyPre`. -/
theorem canary_p3_m1_safetyPre_with_ensuresEqArg_crate (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := idNonZeroUncheckedBody }]
    CrateTheorem {
      bodies := bodies
      functions := [{
        name := fnName
        bodyId := ⟨0⟩
        isUnsafe := true
        requires := newUncheckedRequires
        specs := [.ensuresEqArg 1]
      }]
    } := by
  intro bodies
  let fn : CapturedFn := {
    name := fnName
    bodyId := ⟨0⟩
    isUnsafe := true
    requires := newUncheckedRequires
    specs := [.ensuresEqArg 1]
  }
  have h_ver : FnVerifiedAndRetInv [] bodies defaultAdtInv fn :=
    idNonZeroUnchecked_verified_of_resolve fn (body := fn.resolveBody bodies)
      rfl rfl rfl
  exact verify_single_fn_crate_gen fn rfl ⟨True.intro, True.intro⟩
    defaultAdtInv_admissible h_ver
    (specOn_contractPost_ensuresEqArg1 rfl (fun s hpre =>
      (idNonZeroUnchecked_execNormal s hpre.1.1 hpre.2).map (fun _ h => h.1)))

/-- Negative canary: a safe function (`isUnsafe = false`) cannot use
`/// anneal:requires x != 0` to guard undefined behavior (`unreachable` at
`x = 0`), because `SafetyPre` only includes `fn.safetyPre` when
`fn.isUnsafe = true`. -/
theorem canary_safe_fn_cannot_use_requires_for_ub (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := idNonZeroUncheckedBody }]
    ¬ CrateTheorem {
      bodies := bodies
      functions := [{
        name := fnName
        bodyId := ⟨0⟩
        isUnsafe := false
        requires := newUncheckedRequires
        specs := [.ensuresEqArg 1]
      }]
    } := by
  intro bodies
  have hargs : argsMatchInv [] defaultAdtInv 4 singleArgUsizeInitState [.usize] :=
    ⟨⟨.usize 0, rfl, True.intro⟩, fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinit : initMirState [] bodies idNonZeroUncheckedBody singleArgUsizeInitState :=
    ⟨mkInitEntryState hargs, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
  exact crateTheorem_single_rejects_of_safetyPre_fail
    (bodies := bodies)
    (fn := {
      name := fnName
      bodyId := ⟨0⟩
      isUnsafe := false
      requires := newUncheckedRequires
      specs := [.ensuresEqArg 1]
    })
    singleArgUsizeInitState
    ⟨hinit, hargs, fun h => by cases h⟩
    (.step rfl (.step rfl (.step rfl (.step rfl (.step rfl
      (.step rfl (.fail rfl)))))))

/-- `pub fn clamp_nonzero(x: usize) -> usize { if x == 0 { 1 } else { x } }`:
a safe function that returns `1` when `x == 0` and `x` when `x ≠ 0`. -/
def clampNonZeroBody : MirBody where
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
    { stmts := [
        .storageDead ⟨3⟩,
        .assign (locPlace 0) (.use (.constVal (.usize 1)))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .storageDead ⟨3⟩,
        .assign (locPlace 0) (.use (.copy (locPlace 1)))
      ]
      terminator := .goto ⟨3⟩ },
    { stmts := [
        .storageDead ⟨2⟩
      ]
      terminator := .return_ }
  ]

theorem clampNonZero_execNormal {bodies : List BodyDecl} (s : MirState)
    (hinit : initMirState [] bodies clampNonZeroBody s) :
    ExecNormal [] bodies clampNonZeroBody s (fun r =>
      r.value.valid [] defaultAdtInv r.state 4 .usize ∧
      (newUncheckedSafetyPre s → s.locals 1 = some r.value)) := by
  cases s with
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
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
      | ref _ _ _ _ => cases hvty
      | atomicLoc _ => cases hvty
      | ordering _ => cases hvty
      | usize n =>
        have hL : locals0 = updateLocal locals0 1 (some (.usize n)) := by
          funext i
          cases i with
          | zero => rfl
          | succ m =>
            cases m with
            | zero => exact hv1
            | succ _ => rfl
        rw [hL]
        cases n with
        | zero =>
          refine .step rfl (.step rfl (.step rfl (.step rfl (.step rfl ?_))))
          dsimp only [updateLocal, bumpGen]
          exact .step rfl (.step rfl (.step rfl (.step rfl (.normal rfl
            ⟨True.intro, fun hsaf => False.elim (hsaf 0 rfl rfl)⟩))))
        | succ k =>
          refine .step rfl (.step rfl (.step rfl (.step rfl (.step rfl ?_))))
          dsimp only [updateLocal, bumpGen]
          exact .step rfl (.step rfl (.step rfl (.step rfl (.normal rfl
            ⟨True.intro, fun _ => rfl⟩))))

/-- `clampNonZeroBody` satisfies `FnBodySafetyVerified` unconditionally for any
`fn` and `body` whose lowered body is `clampNonZeroBody`. -/
theorem clampNonZeroBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = clampNonZeroBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb := by
  have hwf : StaticBodyWf [] clampNonZeroBody :=
    mkStaticBodyWf
      (hcount := Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2)))
      (hblocks := Nat.zero_lt_succ 3)
  exact execNormal_fnBodySafetyVerified_of_lowerBody fn body clampNonZeroBody
    hres rfl (contractWellFormed_of_simple hwf rfl rfl) hpin
    (fun s hinitS _ _ => (clampNonZero_execNormal s hinitS).map (fun _ h => h.1))

/-- Positive canary: a safe function (`isUnsafe = false`) with body
`clampNonZeroBody`, functional precondition `requires := newUncheckedRequires`
(`/// anneal:requires x != 0`), and postcondition `specs := [.ensuresEqArg 1]`
(`/// anneal:ensures ret == x`) satisfies `CrateTheorem`: it is UB-free across
all valid `usize` inputs (`SafetyPre`) and satisfies `ret == x` when `x ≠ 0`
(`SafetyPre ∧ fn.safetyPre`). -/
theorem canary_safe_fn_with_requires_and_ensures_verified (fnName : String) :
    let bodies : List BodyDecl := [{ id := ⟨0⟩, body := clampNonZeroBody }]
    CrateTheorem {
      bodies := bodies
      functions := [{
        name := fnName
        bodyId := ⟨0⟩
        isUnsafe := false
        requires := newUncheckedRequires
        specs := [.ensuresEqArg 1]
      }]
    } := by
  intro bodies
  let fn : CapturedFn := {
    name := fnName
    bodyId := ⟨0⟩
    isUnsafe := false
    requires := newUncheckedRequires
    specs := [.ensuresEqArg 1]
  }
  have h_ver : FnVerifiedAndRetInv [] bodies defaultAdtInv fn :=
    clampNonZeroBody_verified_of_resolve fn (body := fn.resolveBody bodies) rfl
  exact verify_single_fn_crate_gen fn rfl ⟨True.intro, True.intro⟩
    defaultAdtInv_admissible h_ver
    (specOn_contractPost_ensuresEqArg1 rfl (fun s hpre =>
      (clampNonZero_execNormal s hpre.1.1).map (fun _ h => h.2 hpre.2)))

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
      (.ref 0 0 ⟨1⟩) = some (.bytes 8 (1 + 2 * Nat.pow 2 32)) ∧
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

/-- Const-guarded `const { assert!(size_of::<RustWrap>() ==
size_of::<usize>()) }; unsafe { core::mem::transmute::<RustWrap, usize>(x) }`.
-/
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
    } ∧
    ExecCompileTimeError [reprRustWrapAdtDecl] bodiesGuarded
      (reprRustGuardedTransmuteBody ⟨0⟩) sPadded ∧
    ¬ CrateTheorem {
      adts := [reprRustWrapAdtDecl]
      bodies := bodiesGuarded
      functions := [{ name := fnName, bodyId := ⟨1⟩ }]
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
    ⟨mkInitEntryState hargsU, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
  have hRejU :
      ¬ CrateTheorem {
        adts := [reprRustWrapAdtDecl]
        bodies := [{ id := ⟨0⟩, body := reprRustUnguardedTransmuteBody }]
        functions := [{ name := fnName, bodyId := ⟨0⟩ }]
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
  have hSafe := (crateTheorem_single_fnVerified hCrate).2.2.2
  have hargsG :
      argsMatchInv [reprRustWrapAdtDecl] defaultAdtInv 3 sPadded [.adt 0] :=
    ⟨⟨.adt 0 (.usize 7), rfl, rfl, True.intro, True.intro⟩,
     fun j hj _ => updateLocal_one_gt_one j hj⟩
  have hinitG :
      initMirState [reprRustWrapAdtDecl] bodiesGuarded
        (reprRustGuardedTransmuteBody ⟨0⟩) sPadded :=
    ⟨mkInitEntryState hargsG, constsTotal_and_monoAdmitted_of_simple rfl rfl⟩
  have hpreG :
      SafetyPre [reprRustWrapAdtDecl] bodiesGuarded defaultAdtInv
        { name := fnName, bodyId := ⟨1⟩ } (reprRustGuardedTransmuteBody ⟨0⟩)
        sPadded :=
    ⟨hinitG, hargsG, fun _ => True.intro⟩
  cases hSafe sPadded hpreG with
  | intro hdef hval =>
    cases execCompileTimeError_reaches hexecCte with
    | intro n hr =>
      have hpfx :
          (MirSem [reprRustWrapAdtDecl] bodiesGuarded
            (reprRustGuardedTransmuteBody ⟨0⟩) sPadded).val hdef
            (.terminated [] .compileTimeError) :=
        ⟨hinitG, n, hr⟩
      exact (hval _ hpfx).1.2 [] rfl

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
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit | usize _ | bool _ | unit | fieldCons _ _ | bytes _ _ | ref _ _ _ _
      | atomicLoc _ | ordering _ =>
        cases hvty
      | adt vAdtId inner =>
        have hveq : vAdtId = 0 := hvty.1
        subst hveq
        cases inner with
        | uninit | bool _ | unit | adt _ _ | fieldCons _ _ | bytes _ _ | ref _ _ _ _
        | atomicLoc _ | ordering _ =>
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
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = adtTransmuteBody 0)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnBodySafetyVerified [reprTransparentWrapAdtDecl] bodies
      (denoteAdtInv [reprTransparentWrapAdtDecl]) fn body tcb :=
  execNormal_fnBodySafetyVerified_of_lowerBody fn body (adtTransmuteBody 0)
    hres rfl (contractWellFormed_of_simple mkStaticBodyWf rfl rfl) hpin
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
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 mem0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    dsimp at hpad
    subst hb hs hc hst hfid hnfid hlg hpad
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit | usize _ | bool _ | unit | fieldCons _ _ | bytes _ _ | ref _ _ _ _
      | atomicLoc _ | ordering _ =>
        cases hvty
      | adt vAdtId inner =>
        have hveq : vAdtId = 0 := hvty.1
        subst hveq
        cases inner with
        | uninit | bool _ | unit | adt _ _ | fieldCons _ _ | bytes _ _ | ref _ _ _ _
        | atomicLoc _ | ordering _ =>
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
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : body = adtTransmuteBody 0)
    (hpin : hasPinnedCoupledWaiver fn tcb = true) :
    FnBodySafetyVerified [reprRustWrapAdtDecl] bodies
      (denoteAdtInv [reprRustWrapAdtDecl]) fn body tcb := by
  subst hres
  refine execNormal_fnBodySafetyVerified fn (adtTransmuteBody 0)
    (contractWellFormed_of_simple mkStaticBodyWf rfl rfl) ?_
  intro s hpre
  dsimp [SafetyPre] at hpre
  rw [hpin] at hpre
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
    (adtPad0 : Nat → Nat) (ubChecks0 : Bool) (mem0 : MemState) (n : Nat) :
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
        ubChecks := ubChecks0
        mem := mem0 }
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
    (adtPad0 : Nat → Nat) (ubChecks0 : Bool) (mem0 : MemState) (n k : Nat) :
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
        ubChecks := ubChecks0
        mem := mem0 } := by
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
  | mk locals0 localGens0 block0 stmtIdx0 tySizes0 curBody0 stack0 frameId0 nextFrameId0 adtPad0 ubChecks0 mem0 =>
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
    | intro v hv =>
      have hv1 : locals0 1 = some v := hv.1
      have hvty := hv.2
      cases v with
      | uninit | usize _ | bool _ | unit | fieldCons _ _ | bytes _ _ | ref _ _ _ _
      | atomicLoc _ | ordering _ =>
        cases hvty
      | adt vAdtId inner =>
        have hveq : vAdtId = 0 := hvty.1
        subst hveq
        cases inner with
        | uninit | bool _ | unit | adt _ _ | fieldCons _ _ | bytes _ _ | ref _ _ _ _
        | atomicLoc _ | ordering _ =>
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
              tySizes0 adtPad0 ubChecks0 mem0 n
          · rw [hL, hPad]
            cases adtPad0 0 with
            | zero =>
              exact Or.inl (capturedGuardedAdtTransmuteBody_exec_zero hconst
                locals0 tySizes0 adtPad0 ubChecks0 mem0 n)
            | succ k =>
              exact Or.inr (capturedGuardedAdtTransmuteBody_exec_succ hconst
                locals0 tySizes0 adtPad0 ubChecks0 mem0 n k)

theorem capturedGuardedAdtTransmuteBody_rustGuarded_verified_of_resolve
    {bodies : List BodyDecl} {constId : BodyId} {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : body = capturedGuardedAdtTransmuteBody constId 0)
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt (.adt 0) .usize))
    (_hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hguard : hasCompileTimeGuardWaiver fn tcb = true) :
    FnBodySafetyVerified [reprRustWrapAdtDecl] bodies
      (denoteAdtInv [reprRustWrapAdtDecl]) fn body tcb := by
  subst hres
  have hwf :
      StaticBodyWf [reprRustWrapAdtDecl]
        (capturedGuardedAdtTransmuteBody constId 0) :=
    mkStaticBodyWf
      (hcount := Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2)))
      (hblocks := Nat.zero_lt_succ 0)
  refine execNormalOrGuard_fnBodySafetyVerified fn
    (capturedGuardedAdtTransmuteBody constId 0) hguard
    (contractWellFormed_of_simple hwf rfl rfl) ?_
  intro s hpre
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
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
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
      | ref _ _ _ _ => cases hvty
      | atomicLoc _ => cases hvty
      | ordering _ => cases hvty
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

/-- `alloc_passthrough` satisfies `FnBodySafetyVerified` for any `fn` and `body`
whose lowered body is `allocPassthroughBody`. -/
theorem allocPassthroughBody_verified_of_resolve {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = allocPassthroughBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb :=
  execNormal_fnBodySafetyVerified_of_lowerBody fn body allocPassthroughBody
    hres rfl (contractWellFormed_of_simple mkStaticBodyWf rfl rfl) hpin
    (fun s hinitS _ _ =>
      (allocPassthroughBody_execNormal s hinitS).map (fun _ h => h.2))

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
    have hentry := hinit.1
    have hb : block0 = 0 := hentry.1
    have hs : stmtIdx0 = 0 := hentry.2.1
    have hc : curBody0 = none := hentry.2.2.1
    have hst : stack0 = [] := hentry.2.2.2.1
    have hfid : frameId0 = 0 := hentry.2.2.2.2.1
    have hnfid : nextFrameId0 = 1 := hentry.2.2.2.2.2.1
    have hlg : localGens0 = (fun _ => 0) := hentry.2.2.2.2.2.2.1
    subst hb hs hc hst hfid hnfid hlg
    cases (initEntryState_argsMatch hentry).1 with
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
      | ref _ _ _ _ => cases hvty
      | atomicLoc _ => cases hvty
      | ordering _ => cases hvty
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

/-- `inlineConstTransmuteBody constId` satisfies `FnBodySafetyVerified` for any
`fn` and `body` whose lowered body is `inlineConstTransmuteBody constId` when
`constId` resolves to `sizeEqConstBodyAt .usize .usize`. -/
theorem inlineConstTransmute_verified_of_resolve {bodies : List BodyDecl}
    {constId : BodyId} {tcb : List TCBItem} (fn : CapturedFn)
    (body : MirBody := fn.resolveBody bodies)
    (hres : lowerBody body = inlineConstTransmuteBody constId)
    (hconst :
      findBody bodies constId = some (sizeEqConstBodyAt .usize .usize))
    (hpin : hasPinnedCoupledWaiver fn tcb = false := by rfl) :
    FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb := by
  have hwf : StaticBodyWf [] (inlineConstTransmuteBody constId) :=
    mkStaticBodyWf
      (hcount := Nat.le_succ_of_le
        (Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_refl 2))))
      (hblocks := Nat.zero_lt_succ 1)
  exact execNormal_fnBodySafetyVerified_of_lowerBody fn body
    (inlineConstTransmuteBody constId) hres rfl
    (contractWellFormed_of_simple hwf rfl rfl) hpin
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

def beqAtomicOrdering : AtomicOrdering → AtomicOrdering → Bool
  | .relaxed, .relaxed => true
  | .acquire, .acquire => true
  | _, _ => false

theorem eq_of_beqAtomicOrdering {a b : AtomicOrdering}
    (h : beqAtomicOrdering a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

def beqMirTy : MirTy → MirTy → Bool
  | .usize => fun b => match b with | .usize => true | _ => false
  | .bool => fun b => match b with | .bool => true | _ => false
  | .unit => fun b => match b with | .unit => true | _ => false
  | .adt i => fun b => match b with | .adt j => i == j | _ => false
  | .param i => fun b => match b with | .param j => i == j | _ => false
  | .ref a => fun b => match b with | .ref b1 => beqMirTy a b1 | _ => false
  | .refAtomicUsize => fun b =>
    match b with | .refAtomicUsize => true | _ => false
  | .atomicOrdering => fun b =>
    match b with | .atomicOrdering => true | _ => false
  | .array a n => fun b =>
    match b with | .array b1 m => beqMirTy a b1 && n == m | _ => false
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
  | .refAtomicUsize, b, h => by cases b <;> first | rfl | cases h
  | .atomicOrdering, b, h => by cases b <;> first | rfl | cases h
  | .array _ _, b, h => by
    cases b with
    | array _ _ =>
      simp [beqMirTy] at h
      rw [eq_of_beqMirTy h.1, h.2]
    | _ => cases h
  | .isize, _, h | .uint _, _, h | .int _, _, h | .float _, _, h
  | .char, _, h | .str, _, h | .never, _, h | .refMut _, _, h
  | .rawPtr _ _, _, h | .slice _, _, h
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
  | .transparent, .transparent => true
  | .c, .c => true
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
  | .ref d1 g1 l1 f1, .ref d2 g2 l2 f2 =>
    d1 == d2 && g1 == g2 && beqLocalId l1 l2 && f1 == f2
  | .atomicLoc a, .atomicLoc b => a == b
  | .ordering a, .ordering b => beqAtomicOrdering a b
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
  | .ref _ _ _ _, .ref _ _ _ _, h => by
    simp [beqMirVal] at h
    rw [h.1.1.1, h.1.1.2, eq_of_beqLocalId h.1.2, h.2]
  | .atomicLoc _, .atomicLoc _, h => by
    simp [beqMirVal] at h; exact congrArg MirVal.atomicLoc h
  | .ordering _, .ordering _, h =>
    congrArg MirVal.ordering (eq_of_beqAtomicOrdering h)

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

def beqRcPair : BodyId × List MirTy → BodyId × List MirTy → Bool
  | (b1, tys1), (b2, tys2) => beqBodyId b1 b2 && listBeq beqMirTy tys1 tys2

theorem eq_of_beqRcPair :
    ∀ {p1 p2 : BodyId × List MirTy}, beqRcPair p1 p2 = true → p1 = p2
  | (_, _), (_, _), h => by
    simp [beqRcPair] at h
    rw [eq_of_beqBodyId h.1, listEq_of_beq eq_of_beqMirTy h.2]

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
  | .panic c1 => match b with | .panic c2 => c1 == c2 | _ => false
  | .assert c1 e1 t1 k1 cl1 =>
    match b with
    | .assert c2 e2 t2 k2 cl2 =>
      beqOperand c1 c2 && e1 == e2 && beqBlockId t1 t2 &&
      beqAssertFailKind k1 k2 && cl1 == cl2
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
  | .callAtomicLoad d1 p1 o1 t1 =>
    match b with
    | .callAtomicLoad d2 p2 o2 t2 =>
      beqPlace d1 d2 && beqOperand p1 p2 && beqOperand o1 o2 &&
      beqBlockId t1 t2
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
  | panic c1 =>
    cases b with
    | panic c2 =>
      simp [beqTerminator] at h
      rw [h]
    | _ => cases h
  | assert c1 e1 t1 k1 cl1 =>
    cases b with
    | assert c2 e2 t2 k2 cl2 =>
      simp [beqTerminator] at h
      rw [eq_of_beqOperand h.1.1.1.1, h.1.1.1.2, eq_of_beqBlockId h.1.1.2,
        eq_of_beqAssertFailKind h.1.2, h.2]
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
  | callAtomicLoad d1 p1 o1 t1 =>
    cases b with
    | callAtomicLoad d2 p2 o2 t2 =>
      simp [beqTerminator] at h
      rw [eq_of_beqPlace h.1.1.1, eq_of_beqOperand h.1.1.2,
        eq_of_beqOperand h.1.2, eq_of_beqBlockId h.2]
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
  listBeq beqBasicBlock a.blocks b.blocks &&
  listBeq beqRcPair a.requiredConsts b.requiredConsts &&
  listBeq beqMirTy a.requiredLayouts b.requiredLayouts

theorem eq_of_beqMirBody {a b : MirBody} (h : beqMirBody a b = true) : a = b := by
  cases a; cases b; simp [beqMirBody] at h
  rw [listEq_of_beq eq_of_beqMirTy h.1.1.1.1.1,
    eq_of_beqMirTy h.1.1.1.1.2,
    h.1.1.1.2,
    listEq_of_beq eq_of_beqBasicBlock h.1.1.2,
    listEq_of_beq eq_of_beqRcPair h.1.2,
    listEq_of_beq eq_of_beqMirTy h.2]

def beqRequiresSpec (a b : RequiresSpec) : Bool :=
  a.argLocal == b.argLocal && a.ne == b.ne

theorem eq_of_beqRequiresSpec {a b : RequiresSpec}
    (h : beqRequiresSpec a b = true) : a = b := by
  cases a; cases b; simp [beqRequiresSpec] at h; rw [h.1, h.2]

def beqPostSpec : PostSpec → PostSpec → Bool
  | .ensuresEqArg a, .ensuresEqArg b => a == b
  | .ensuresAtomicLoad a, .ensuresAtomicLoad b => a == b
  | _, _ => false

theorem eq_of_beqPostSpec : ∀ {a b : PostSpec}, beqPostSpec a b = true → a = b
  | .ensuresEqArg _, .ensuresEqArg _, h => by
    simp [beqPostSpec] at h; exact congrArg PostSpec.ensuresEqArg h
  | .ensuresAtomicLoad _, .ensuresAtomicLoad _, h => by
    simp [beqPostSpec] at h; exact congrArg PostSpec.ensuresAtomicLoad h

def beqObligationId : ObligationId → ObligationId → Bool
  | .fnBody n1, .fnBody n2 => decide (n1 = n2)

theorem eq_of_beqObligationId :
    ∀ {a b : ObligationId}, beqObligationId a b = true → a = b
  | .fnBody _, .fnBody _, h => by
    simp [beqObligationId] at h; rw [h]

theorem beqObligationId_refl (a : ObligationId) :
    beqObligationId a a = true := by
  cases a
  dsimp [beqObligationId]
  exact decide_eq_true rfl

theorem ne_of_beqObligationId_false {a b : ObligationId}
    (h : beqObligationId a b = false) : a ≠ b := by
  intro heq
  subst heq
  rw [beqObligationId_refl] at h
  cases h

/-! ### Generic `NoDupIds` and `ObligationId` waiver checkers -/

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

def checkMemObligationId (x : ObligationId) : List ObligationId → Bool
  | [] => false
  | y :: ys => beqObligationId x y || checkMemObligationId x ys

theorem mem_of_checkMemObligationId {x : ObligationId} :
    ∀ {ys : List ObligationId}, checkMemObligationId x ys = true → x ∈ ys
  | [], h => by cases h
  | y :: ys, h => by
    have h' : (beqObligationId x y || checkMemObligationId x ys) = true := h
    cases hxy : beqObligationId x y with
    | true =>
      rw [eq_of_beqObligationId hxy]
      exact .head _
    | false =>
      rw [hxy] at h'
      exact .tail _ (mem_of_checkMemObligationId h')

theorem allHold_fnBody_ne {m : String} :
    ∀ {ns : List String},
      AllHold (ns.map (fun n' => m ≠ n')) →
      AllHold ((ns.map ObligationId.fnBody).map (fun id' =>
        ObligationId.fnBody m ≠ id'))
  | [], _ => True.intro
  | _ :: _, ⟨h1, h2⟩ =>
    ⟨fun heq => by injection heq with hname; exact h1 hname,
     allHold_fnBody_ne h2⟩

theorem noDupIds_fnBody_of_names :
    ∀ {fns : List CapturedFn},
      NoDupIds (fns.map CapturedFn.name) →
      NoDupIds (fns.map (fun fn => ObligationId.fnBody fn.name)) ∧
      ((fns.map (fun fn => ObligationId.fnBody fn.name)).foldr
        (fun id (acc : Prop × List ObligationId) =>
          (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1,
           id :: acc.2))
        (True, [])).2 =
      ((fns.map CapturedFn.name).foldr
        (fun n (acc : Prop × List String) =>
          (AllHold (acc.2.map (fun n' => n ≠ n')) ∧ acc.1,
           n :: acc.2))
        (True, [])).2.map ObligationId.fnBody
  | [], _ => ⟨True.intro, rfl⟩
  | fn :: rest, ⟨hall, hrest⟩ => by
    have ih := noDupIds_fnBody_of_names hrest
    dsimp [List.map, List.foldr, NoDupIds]
    refine ⟨⟨?_, ih.1⟩, congrArg (List.cons (.fnBody fn.name)) ih.2⟩
    rw [ih.2]
    exact allHold_fnBody_ne hall

theorem map_obligation_id {adts : List AdtDecl} {bodies : List BodyDecl}
    {adtInv : AdtInv} {tcb : List TCBItem} :
    ∀ (fns : List CapturedFn),
      (fns.map (fun fn => fn.obligation adts bodies adtInv tcb)).map
          Obligation.id =
        fns.map (fun fn => ObligationId.fnBody fn.name)
  | [] => rfl
  | fn :: rest => by
    dsimp [List.map, CapturedFn.obligation]
    exact congrArg (List.cons (.fnBody fn.name)) (map_obligation_id rest)

/-! ### Compositional per-body, per-function, and per-crate verification -/

abbrev BodyUserSpecsHold (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (body : MirBody)
    (tcb : List TCBItem := []) : Prop :=
  MirSem adts bodies body ≤
    (MirLang adts bodies).SpecOn
      (fun s => SafetyPre adts bodies adtInv fn body s tcb ∧ fn.safetyPre s)
      (ContractPost adts bodies fn)

abbrev UserSpecsHold (adts : List AdtDecl) (bodies : List BodyDecl)
    (adtInv : AdtInv) (fn : CapturedFn) (tcb : List TCBItem := []) : Prop :=
  BodyUserSpecsHold adts bodies adtInv fn (fn.resolveBody bodies) tcb

theorem fnBodyVerified_of_safety_and_specs {adts : List AdtDecl}
    {bodies : List BodyDecl} {adtInv : AdtInv} {fn : CapturedFn}
    {body : MirBody} {tcb : List TCBItem}
    (hver : FnBodySafetyVerified adts bodies adtInv fn body tcb)
    (hspecs : BodyUserSpecsHold adts bodies adtInv fn body tcb) :
    ContractWellFormed adts bodies fn body ∧
    FnBodyVerified adts bodies adtInv fn body tcb :=
  ⟨hver.1, verified_split hver.2 hspecs⟩

theorem bodyUserSpecsHold_nil {adts : List AdtDecl} {bodies : List BodyDecl}
    {adtInv : AdtInv} {fn : CapturedFn} {body : MirBody} {tcb : List TCBItem}
    (hver : FnBodySafetyVerified adts bodies adtInv fn body tcb)
    (h : fn.specs = []) :
    BodyUserSpecsHold adts bodies adtInv fn body tcb := by
  intro s hpre
  have hsafe := hver.2.2.2 s hpre.1
  refine ⟨hsafe.1, fun out _ => ?_⟩
  unfold ContractPost
  rw [h]
  exact True.intro

theorem bodyUserSpecs_ensuresEqArg1_of_lowerBody {bodies : List BodyDecl}
    {tcb : List TCBItem}
    (fn : CapturedFn) (body target : MirBody)
    (hres : lowerBody body = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hspecs : fn.specs = [.ensuresEqArg 1])
    (h_exec : ∀ s, initMirState [] bodies target s → fn.safetyPre s →
      ExecNormal [] bodies target s (fun r => s.locals 1 = some r.value)) :
    BodyUserSpecsHold [] bodies defaultAdtInv fn body tcb := by
  unfold BodyUserSpecsHold
  refine specOn_contractPost_ensuresEqArg1 hspecs (fun s hpre => ?_)
  have ⟨hinitT, _, _⟩ :=
    (safetyPre_of_lowerBody_eq hres hcalls hpin).mp hpre.1
  have hcallsOrig :
      body.blocks.all (fun bb => !isCall1 bb.terminator) = true := by
    rw [← noCall_lowerBody body, hres]
    exact hcalls
  have hexecLow :
      ExecNormal [] bodies (lowerBody body) s
        (fun r => s.locals 1 = some r.value) := by
    rw [hres]
    exact h_exec s hinitT hpre.2
  exact lowerBody_simulates hcallsOrig (fun _ _ _ h => h)
    hinitT.1.2.1 hinitT.1.2.2.1 hinitT.1.2.2.2.1 hexecLow

/-- Structured diagnostic returned when `proveCrateOpt` cannot discharge a
function or crate obligation. -/
structure ProofError where
  message : String
  scope : String

/-- Discharge either `fn.specs = []` or `fn.specs = [.ensuresEqArg 1]` for an
identity-like intra-procedural body `target = lowerBody body`. -/
def dispatchIdLikeSpecs {bodies : List BodyDecl} {tcb : List TCBItem}
    (fn : CapturedFn) (body target : MirBody)
    (hres : lowerBody body = target)
    (hcalls : target.blocks.all (fun bb => !isCall1 bb.terminator) = true)
    (hpin : hasPinnedCoupledWaiver fn tcb = false)
    (hver : FnBodySafetyVerified [] bodies defaultAdtInv fn body tcb)
    (h_exec : ∀ s, initMirState [] bodies target s → fn.safetyPre s →
      ExecNormal [] bodies target s (fun r => s.locals 1 = some r.value))
    (errMsg : String) :
    Except ProofError
      (PLift
        (ContractWellFormed [] bodies fn body ∧
         FnBodyVerified [] bodies defaultAdtInv fn body tcb)) :=
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    .ok (.up (fnBodyVerified_of_safety_and_specs hver
      (bodyUserSpecsHold_nil hver (listEq_of_beq eq_of_beqPostSpec hs0))))
  else if hs1 : listBeq beqPostSpec fn.specs [.ensuresEqArg 1] = true then
    .ok (.up (fnBodyVerified_of_safety_and_specs hver
      (bodyUserSpecs_ensuresEqArg1_of_lowerBody fn body target hres hcalls hpin
        (listEq_of_beq eq_of_beqPostSpec hs1) h_exec)))
  else
    .error ⟨errMsg, fn.name⟩

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

/-- Extract the first `.evalConst` or `requiredConsts` constant `BodyId` from a
body, if any. -/
def firstRequiredConstId (b : MirBody) : BodyId :=
  match b.blocks with
  | bb :: _ =>
    match firstEvalConstInStmts bb.stmts with
    | some constId => constId
    | none =>
      match b.requiredConsts with
      | (constId, _) :: _ => constId
      | _ => ⟨0⟩
  | _ => ⟨0⟩

/-- Per-body proof dispatcher for crates without ADTs (`adts = []`).
Normalizes intra-procedural bodies with `lowerBody` before matching so that
functions containing `Stmt.nop` or forwarding `goto` chains reduce to the
same canonical verification theorems. -/
def proveBodyNoAdtOpt (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) (b : MirBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false) :
    Except ProofError
      (PLift
        (ContractWellFormed [] bodies fn b ∧
         FnBodyVerified [] bodies defaultAdtInv fn b tcb)) :=
  let lb := lowerBody b
  if hb : beqMirBody lb idCopyBody = true then
    have hres : lowerBody b = idCopyBody := eq_of_beqMirBody hb
    dispatchIdLikeSpecs fn b idCopyBody hres rfl hpin
      (idCopyBody_verified_of_resolve fn b hres hpin)
      (fun s hinit _ => (idCopyBody_execNormal s hinit).map (fun _ h => h.1))
      "unsupported specs on id (copy)"
  else if hb : beqMirBody lb idMoveBody = true then
    have hres : lowerBody b = idMoveBody := eq_of_beqMirBody hb
    dispatchIdLikeSpecs fn b idMoveBody hres rfl hpin
      (idMoveBody_verified_of_resolve fn b hres hpin)
      (fun s hinit _ => (idMoveBody_execNormal s hinit).map (fun _ h => h.1))
      "unsupported specs on id (move)"
  else if hb : beqMirBody lb allocPassthroughBody = true then
    have hres : lowerBody b = allocPassthroughBody := eq_of_beqMirBody hb
    dispatchIdLikeSpecs fn b allocPassthroughBody hres rfl hpin
      (allocPassthroughBody_verified_of_resolve fn b hres hpin)
      (fun s hinit _ =>
        (allocPassthroughBody_execNormal s hinit).map (fun _ h => h.1))
      "unsupported specs on alloc_passthrough"
  else if hb : beqMirBody b loadRelaxedBody = true then
    have hres : b = loadRelaxedBody := eq_of_beqMirBody hb
    if optBeq beqRequiresSpec fn.requires none = true then
      have hver := loadRelaxedBody_verified_of_eq fn b hres
      if hs0 : listBeq beqPostSpec fn.specs [] = true then
        .ok (.up (fnBodyVerified_of_safety_and_specs hver
          (bodyUserSpecsHold_nil hver (listEq_of_beq eq_of_beqPostSpec hs0))))
      else if hs1 :
          listBeq beqPostSpec fn.specs [.ensuresAtomicLoad 1] = true then
        .ok (.up (fnBodyVerified_of_safety_and_specs hver
          (loadRelaxedBody_specs_of_eq fn b hres
            (listEq_of_beq eq_of_beqPostSpec hs1))))
      else
        .error ⟨"unsupported specs on load_relaxed", fn.name⟩
    else
      .error ⟨"unsupported requires clause on load_relaxed", fn.name⟩
  else if hb : beqMirBody lb clampNonZeroBody = true then
    have hres : lowerBody b = clampNonZeroBody := eq_of_beqMirBody hb
    have hver := clampNonZeroBody_verified_of_resolve fn b hres hpin
    if hreq : optBeq beqRequiresSpec fn.requires newUncheckedRequires = true then
      have hreqEq : fn.requires = newUncheckedRequires :=
        optEq_of_beq eq_of_beqRequiresSpec hreq
      dispatchIdLikeSpecs fn b clampNonZeroBody hres rfl hpin hver
        (fun s hinit hsaf => by
          have hsaf' : newUncheckedSafetyPre s := by
            dsimp [CapturedFn.safetyPre] at hsaf
            rw [hreqEq] at hsaf
            exact hsaf
          exact (clampNonZero_execNormal s hinit).map (fun _ h => h.2 hsaf'))
        "unsupported specs on clamp_nonzero"
    else if optBeq beqRequiresSpec fn.requires none = true then
      if hs0 : listBeq beqPostSpec fn.specs [] = true then
        .ok (.up (fnBodyVerified_of_safety_and_specs hver
          (bodyUserSpecsHold_nil hver (listEq_of_beq eq_of_beqPostSpec hs0))))
      else
        .error ⟨"unsupported specs on unannotated clamp_nonzero", fn.name⟩
    else
      .error ⟨"unsupported requires clause on clamp_nonzero", fn.name⟩
  else if hb : beqMirBody lb idNonZeroUncheckedBody = true then
    have hres : lowerBody b = idNonZeroUncheckedBody := eq_of_beqMirBody hb
    if hunsafe : fn.isUnsafe = true then
      if hreq : optBeq beqRequiresSpec fn.requires newUncheckedRequires = true then
        have hreqEq : fn.requires = newUncheckedRequires :=
          optEq_of_beq eq_of_beqRequiresSpec hreq
        have hver :=
          idNonZeroUnchecked_verified_of_resolve fn b hres hunsafe hreqEq hpin
        dispatchIdLikeSpecs fn b idNonZeroUncheckedBody hres rfl hpin hver
          (fun s hinit hsaf => by
            have hsaf' : newUncheckedSafetyPre s := by
              dsimp [CapturedFn.safetyPre] at hsaf
              rw [hreqEq] at hsaf
              exact hsaf
            exact (idNonZeroUnchecked_execNormal s hinit hsaf').map
              (fun _ h => h.1))
          "unsupported specs on id_nonzero_unchecked"
      else
        .error ⟨"missing requires clause on id_nonzero_unchecked", fn.name⟩
    else
      .error ⟨"safe function cannot use requires for UB", fn.name⟩
  else if optBeq beqRequiresSpec fn.requires none = true then
    let constId := firstRequiredConstId lb
    if hb : beqMirBody lb (inlineConstTransmuteBody constId) = true then
      have hres : lowerBody b = inlineConstTransmuteBody constId :=
        eq_of_beqMirBody hb
      if hconst :
          optBeq beqMirBody (findBody bodies constId)
            (some (sizeEqConstBodyAt .usize .usize)) = true then
        if hs0 : listBeq beqPostSpec fn.specs [] = true then
          have hver :=
            inlineConstTransmute_verified_of_resolve fn b hres
              (optEq_of_beq eq_of_beqMirBody hconst) hpin
          .ok (.up (fnBodyVerified_of_safety_and_specs hver
            (bodyUserSpecsHold_nil hver
              (listEq_of_beq eq_of_beqPostSpec hs0))))
        else
          .error ⟨"unsupported specs on inline_const_transmute", fn.name⟩
      else
        .error ⟨"unproved required const", fn.name⟩
    else
      let calleeId := firstCalleeId b
      if hb : beqMirBody b (concreteTransmuteCallerBody calleeId .usize) = true then
        have hres : b = concreteTransmuteCallerBody calleeId .usize :=
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
                have hver :=
                  concreteTransmuteCaller_verified_of_resolve fn b hres
                    hcalleeEq (optEq_of_beq eq_of_beqMirBody hconst)
                .ok (.up (fnBodyVerified_of_safety_and_specs hver
                  (bodyUserSpecsHold_nil hver
                    (listEq_of_beq eq_of_beqPostSpec hs0))))
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

/-- Per-body proof dispatcher for crates with `[nonZeroAdtDecl 0 repr]`. -/
def proveBodyNonZeroOpt (repr : AdtRepr)
    (hrepr : repr = .rust ∨ repr = .transparent)
    (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) (b : MirBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false) :
    Except ProofError
      (PLift
        (ContractWellFormed [nonZeroAdtDecl 0 repr] bodies fn b ∧
         FnBodyVerified [nonZeroAdtDecl 0 repr] bodies
           (nonZeroAdtInv repr) fn b tcb)) :=
  let lb := lowerBody b
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    have hs0Eq : fn.specs = [] := listEq_of_beq eq_of_beqPostSpec hs0
    if optBeq beqRequiresSpec fn.requires none = true then
      if hb : beqMirBody lb makeNonZeroBody = true then
        have hver :=
          makeNonZeroBody_verified_of_resolve fn b (eq_of_beqMirBody hb)
            hpin hrepr
        .ok (.up (fnBodyVerified_of_safety_and_specs hver
          (bodyUserSpecsHold_nil hver hs0Eq)))
      else if hb : beqMirBody lb (getUncheckedNonZeroBodyAt 0 false) = true then
        have hver :=
          getUncheckedNonZeroBody_verified_of_resolve false fn b
            (eq_of_beqMirBody hb) hpin hrepr
        .ok (.up (fnBodyVerified_of_safety_and_specs hver
          (bodyUserSpecsHold_nil hver hs0Eq)))
      else if hb : beqMirBody lb (getUncheckedNonZeroBodyAt 0 true) = true then
        have hver :=
          getUncheckedNonZeroBody_verified_of_resolve true fn b
            (eq_of_beqMirBody hb) hpin hrepr
        .ok (.up (fnBodyVerified_of_safety_and_specs hver
          (bodyUserSpecsHold_nil hver hs0Eq)))
      else
        .error ⟨"unproved safe NonZeroUsize function", fn.name⟩
    else if hreq :
        optBeq beqRequiresSpec fn.requires newUncheckedRequires = true then
      have hreqEq : fn.requires = newUncheckedRequires :=
        optEq_of_beq eq_of_beqRequiresSpec hreq
      if hunsafe : fn.isUnsafe = true then
        if hb : beqMirBody lb newUncheckedBody = true then
          have hver :=
            newUncheckedBody_verified_of_resolve fn b (eq_of_beqMirBody hb)
              hunsafe hreqEq hpin hrepr
          .ok (.up (fnBodyVerified_of_safety_and_specs hver
            (bodyUserSpecsHold_nil hver hs0Eq)))
        else
          .error ⟨"unproved unsafe NonZeroUsize function", fn.name⟩
      else
        .error ⟨"safe function cannot use requires for invariant safety", fn.name⟩
    else
      .error ⟨"unsupported requires clause", fn.name⟩
  else
    .error ⟨"unsupported specs on NonZeroUsize function", fn.name⟩

/-- Per-body proof dispatcher for `[reprTransparentWrapAdtDecl]`. -/
def proveBodyTransWrapOpt (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) (b : MirBody)
    (hpin : hasPinnedCoupledWaiver fn tcb = false) :
    Except ProofError
      (PLift
        (ContractWellFormed [reprTransparentWrapAdtDecl] bodies fn b ∧
         FnBodyVerified [reprTransparentWrapAdtDecl] bodies
           (denoteAdtInv [reprTransparentWrapAdtDecl]) fn b tcb)) :=
  let lb := lowerBody b
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    have hs0Eq : fn.specs = [] := listEq_of_beq eq_of_beqPostSpec hs0
    if optBeq beqRequiresSpec fn.requires none = true then
      if hb : beqMirBody lb (adtTransmuteBody 0) = true then
        have hver :=
          adtTransmuteBody_transparent_verified_of_resolve fn b
            (eq_of_beqMirBody hb) hpin
        .ok (.up (fnBodyVerified_of_safety_and_specs hver
          (bodyUserSpecsHold_nil hver hs0Eq)))
      else
        .error ⟨"unproved #[repr(transparent)] function", fn.name⟩
    else
      .error ⟨"unsupported requires clause on #[repr(transparent)] function", fn.name⟩
  else
    .error ⟨"unsupported specs on #[repr(transparent)] function", fn.name⟩

/-- Per-body proof dispatcher for `[reprRustWrapAdtDecl]`:
- Unguarded `adtTransmuteBody 0` requires `TCBItem.pinnedCompilerCoupled`.
- Const-guarded `capturedGuardedAdtTransmuteBody constId 0` requires
  `TCBItem.compileTimeGuard`. -/
def proveBodyRustWrapOpt (bodies : List BodyDecl) (tcb : List TCBItem)
    (fn : CapturedFn) (b : MirBody) :
    Except ProofError
      (PLift
        (ContractWellFormed [reprRustWrapAdtDecl] bodies fn b ∧
         FnBodyVerified [reprRustWrapAdtDecl] bodies
           (denoteAdtInv [reprRustWrapAdtDecl]) fn b tcb)) :=
  if hs0 : listBeq beqPostSpec fn.specs [] = true then
    have hs0Eq : fn.specs = [] := listEq_of_beq eq_of_beqPostSpec hs0
    if optBeq beqRequiresSpec fn.requires none = true then
      if hb : beqMirBody b (adtTransmuteBody 0) = true then
        if hpin : decide (hasPinnedCoupledWaiver fn tcb = true) = true then
          have hver :=
            adtTransmuteBody_rustPinned_verified_of_resolve fn b
              (eq_of_beqMirBody hb) (of_decide_eq_true hpin)
          .ok (.up (fnBodyVerified_of_safety_and_specs hver
            (bodyUserSpecsHold_nil hver hs0Eq)))
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
                have hver :=
                  capturedGuardedAdtTransmuteBody_rustGuarded_verified_of_resolve
                    fn b (eq_of_beqMirBody hb)
                    (optEq_of_beq eq_of_beqMirBody hconst)
                    (of_decide_eq_true hpin) (of_decide_eq_true hguard)
                .ok (.up (fnBodyVerified_of_safety_and_specs hver
                  (bodyUserSpecsHold_nil hver hs0Eq)))
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

/-- Lift a per-body prover across both `fn.bodyId` (`--release`) and optional
`fn.debugBodyId` (`--debug`). -/
def liftProveBodyToFn {adts : List AdtDecl} {bodies : List BodyDecl}
    {adtInv : AdtInv} {tcb : List TCBItem}
    (proveBody :
      ∀ (fn : CapturedFn) (body : MirBody),
        Except ProofError
          (PLift
            (ContractWellFormed adts bodies fn body ∧
             FnBodyVerified adts bodies adtInv fn body tcb)))
    (fn : CapturedFn) :
    Except ProofError
      (PLift
        (FnContractWellFormed adts bodies fn ∧
         FnVerified adts bodies adtInv fn tcb)) :=
  match proveBody fn (fn.resolveBody bodies) with
  | .error err => .error err
  | .ok pRel =>
    match hdbg : fn.debugBodyId with
    | none =>
      have hcwf : FnContractWellFormed adts bodies fn := by
        unfold FnContractWellFormed
        rw [hdbg]
        exact ⟨pRel.down.1, True.intro⟩
      have hver : FnVerified adts bodies adtInv fn tcb := by
        unfold FnVerified
        rw [hdbg]
        exact ⟨pRel.down.2, True.intro⟩
      .ok (.up ⟨hcwf, hver⟩)
    | some dbgId =>
      match proveBody fn (resolveBodyById bodies dbgId) with
      | .error err => .error err
      | .ok pDbg =>
        have hcwf : FnContractWellFormed adts bodies fn := by
          unfold FnContractWellFormed
          rw [hdbg]
          exact ⟨pRel.down.1, pDbg.down.1⟩
        have hver : FnVerified adts bodies adtInv fn tcb := by
          unfold FnVerified
          rw [hdbg]
          exact ⟨pRel.down.2, pDbg.down.2⟩
        .ok (.up ⟨hcwf, hver⟩)

/-- Discharge `ContractWellFormed` for any intra-procedural body with
`requiredConsts = []` (including bodies waived via `/// anneal:trusted`), or
fall back to `proveBody` when the body has required constants or calls. -/
def proveBodyContractWfOpt (adts : List AdtDecl) (bodies : List BodyDecl)
    (tcb : List TCBItem)
    (proveBody :
      ∀ (fn : CapturedFn) (body : MirBody),
        Except ProofError
          (PLift
            (ContractWellFormed adts bodies fn body ∧
             FnBodyVerified adts bodies (denoteAdtInv adts) fn body tcb)))
    (fn : CapturedFn) (body : MirBody) :
    Except ProofError (PLift (ContractWellFormed adts bodies fn body)) :=
  if hcount : decide (1 + body.argTys.length ≤ body.localCount) = true then
    if hblocks : decide (0 < body.blocks.length) = true then
      if hl0 : LocalLayoutsAdmitted adts body (fun _ => 0) = true then
        if hl1 : LocalLayoutsAdmitted adts body (fun _ => 1) = true then
          if hrc : decide (body.requiredConsts = []) = true then
            if hcalls :
                (body.blocks.all (fun bb => !isCall1 bb.terminator)) = true then
              have hwf : StaticBodyWf adts body :=
                mkStaticBodyWf
                  (of_decide_eq_true hcount)
                  (of_decide_eq_true hblocks)
                  hl0 hl1
              .ok (.up (contractWellFormed_of_simple hwf
                (of_decide_eq_true hrc) hcalls))
            else
              match proveBody fn body with
              | .ok p => .ok (.up p.down.1)
              | .error err => .error err
          else
            match proveBody fn body with
            | .ok p => .ok (.up p.down.1)
            | .error err => .error err
        else
          .error ⟨"unsatisfiable LocalLayoutsAdmitted at 1 in StaticBodyWf", fn.name⟩
      else
        .error ⟨"unsatisfiable LocalLayoutsAdmitted at 0 in StaticBodyWf", fn.name⟩
    else
      .error ⟨"empty basic-block list in StaticBodyWf", fn.name⟩
  else
    .error ⟨"insufficient localCount in StaticBodyWf", fn.name⟩

/-- Lift `proveBodyContractWfOpt` across both `fn.bodyId` and optional
`fn.debugBodyId`. -/
def proveFnContractWfOpt (adts : List AdtDecl) (bodies : List BodyDecl)
    (tcb : List TCBItem)
    (proveBody :
      ∀ (fn : CapturedFn) (body : MirBody),
        Except ProofError
          (PLift
            (ContractWellFormed adts bodies fn body ∧
             FnBodyVerified adts bodies (denoteAdtInv adts) fn body tcb)))
    (fn : CapturedFn) :
    Except ProofError (PLift (FnContractWellFormed adts bodies fn)) :=
  match proveBodyContractWfOpt adts bodies tcb proveBody fn
      (fn.resolveBody bodies) with
  | .error err => .error err
  | .ok pRel =>
    match hdbg : fn.debugBodyId with
    | none =>
      have hcwf : FnContractWellFormed adts bodies fn := by
        unfold FnContractWellFormed
        rw [hdbg]
        exact ⟨pRel.down, True.intro⟩
      .ok (.up hcwf)
    | some dbgId =>
      match proveBodyContractWfOpt adts bodies tcb proveBody fn
          (resolveBodyById bodies dbgId) with
      | .error err => .error err
      | .ok pDbg =>
        have hcwf : FnContractWellFormed adts bodies fn := by
          unfold FnContractWellFormed
          rw [hdbg]
          exact ⟨pRel.down, pDbg.down⟩
        .ok (.up hcwf)

/-- Compositionally discharge `AllHold (FnContractWellFormed ...)` and
per-function behavioral obligations (either proved via `proveBody` or waived in
`c.tcbWaivedIds`) across any list of `CapturedFn`s. -/
def proveFnsLoop (c : Crate)
    (proveBody :
      ∀ (fn : CapturedFn) (body : MirBody),
        Except ProofError
          (PLift
            (ContractWellFormed c.adts c.bodies fn body ∧
             FnBodyVerified c.adts c.bodies c.adtInv fn body c.tcb))) :
    ∀ (fns : List CapturedFn),
      Except ProofError
        (PLift
          (AllHold (fns.map (FnContractWellFormed c.adts c.bodies)) ∧
           AllHold
             ((fns.map
               (fun fn => fn.obligation c.adts c.bodies c.adtInv c.tcb)).map
               (fun o => o.prop ∨ o.id ∈ c.tcbWaivedIds))))
  | [] => .ok (.up ⟨True.intro, True.intro⟩)
  | fn :: rest =>
    if hwaived : checkMemObligationId (.fnBody fn.name) c.tcbWaivedIds = true then
      match proveFnContractWfOpt c.adts c.bodies c.tcb proveBody fn with
      | .error err => .error err
      | .ok pCwf =>
        match proveFnsLoop c proveBody rest with
        | .error err => .error err
        | .ok pRest =>
          .ok (.up
            ⟨⟨pCwf.down, pRest.down.1⟩,
             ⟨Or.inr (mem_of_checkMemObligationId hwaived), pRest.down.2⟩⟩)
    else
      match liftProveBodyToFn proveBody fn with
      | .error err => .error err
      | .ok pFn =>
        match proveFnsLoop c proveBody rest with
        | .error err => .error err
        | .ok pRest =>
          .ok (.up
            ⟨⟨pFn.down.1, pRest.down.1⟩,
             ⟨Or.inl pFn.down.2, pRest.down.2⟩⟩)

/-- Compositional Lean proof dispatcher: validates crate-level structural
invariants (`c.functions ≠ []`, `NoDupIds` on bodies, functions, and
`tcbWaivedIds`, and `AdmissibleAdtInv`) and then verifies each function in
`c.functions` independently via `proveFnsLoop`. -/
def proveCrateOpt (c : Crate) :
    Except ProofError (PLift (CrateTheorem c)) :=
  if hne : decide (c.functions = []) = false then
    if hbnodup :
        checkNoDupIds (fun a b => decide (a = b))
          (c.bodies.map (fun d => d.id.index)) = true then
      if hfnodup :
          checkNoDupIds (fun a b => decide (a = b))
            (c.functions.map CapturedFn.name) = true then
        if htnodup : checkNoDupIds beqObligationId c.tcbWaivedIds = true then
          have h_fns_ne : c.functions ≠ [] := of_decide_eq_false hne
          have h_bodies_nodup :
              NoDupIds (c.bodies.map (fun d => d.id.index)) :=
            noDupIds_of_check (fun h => of_decide_eq_false h) hbnodup
          have h_fns_nodup : NoDupIds (c.functions.map CapturedFn.name) :=
            noDupIds_of_check (fun h => of_decide_eq_false h) hfnodup
          have h_obs_ne :
              c.functions.map
                (fun fn => fn.obligation c.adts c.bodies c.adtInv c.tcb) ≠
                [] := by
            intro hnil
            cases hfns : c.functions with
            | nil => exact h_fns_ne hfns
            | cons _ _ => rw [hfns] at hnil; cases hnil
          have h_obs_nodup :
              NoDupIds
                ((c.functions.map
                  (fun fn => fn.obligation c.adts c.bodies c.adtInv c.tcb)).map
                  Obligation.id) := by
            rw [map_obligation_id c.functions]
            exact (noDupIds_fnBody_of_names h_fns_nodup).1
          have h_tcb_nodup : NoDupIds c.tcbWaivedIds :=
            noDupIds_of_check ne_of_beqObligationId_false htnodup
          let finish (hadm : AdmissibleAdtInv c.adts c.adtInv)
              (proveBody :
                ∀ (fn : CapturedFn) (body : MirBody),
                  Except ProofError
                    (PLift
                      (ContractWellFormed c.adts c.bodies fn body ∧
                       FnBodyVerified c.adts c.bodies c.adtInv fn body c.tcb))) :
              Except ProofError (PLift (CrateTheorem c)) :=
            match proveFnsLoop c proveBody c.functions with
            | .ok pFns =>
              .ok (.up
                ⟨h_fns_ne, h_bodies_nodup, h_fns_nodup, hadm, pFns.down.1,
                 ⟨h_obs_ne, h_obs_nodup, h_tcb_nodup, pFns.down.2⟩⟩)
            | .error err => .error err
          let finishNoPin (hadm : AdmissibleAdtInv c.adts c.adtInv)
              (proveBody :
                ∀ (fn : CapturedFn) (body : MirBody),
                  hasPinnedCoupledWaiver fn c.tcb = false →
                  Except ProofError
                    (PLift
                      (ContractWellFormed c.adts c.bodies fn body ∧
                       FnBodyVerified c.adts c.bodies c.adtInv fn body c.tcb))) :
              Except ProofError (PLift (CrateTheorem c)) :=
            finish hadm (fun fn body =>
              if hpin : decide (hasPinnedCoupledWaiver fn c.tcb = false) = true then
                proveBody fn body (of_decide_eq_true hpin)
              else
                .error ⟨"unsupported pinnedCompilerCoupled waiver", fn.name⟩)
          if hadts0 : listBeq beqAdtDecl c.adts [] = true then
            have hadtsEq : c.adts = [] :=
              listEq_of_beq eq_of_beqAdtDecl hadts0
            have hadm : AdmissibleAdtInv c.adts c.adtInv := by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact defaultAdtInv_admissible
            finishNoPin hadm (fun fn body hpin => by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact proveBodyNoAdtOpt c.bodies c.tcb fn body hpin)
          else if hadt1 :
              listBeq beqAdtDecl c.adts [nonZeroAdtDecl 0 .rust] = true then
            have hadtsEq : c.adts = [nonZeroAdtDecl 0 .rust] :=
              listEq_of_beq eq_of_beqAdtDecl hadt1
            have hadm : AdmissibleAdtInv c.adts c.adtInv := by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact nonZeroAdtInv_admissible
            finishNoPin hadm (fun fn body hpin => by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact proveBodyNonZeroOpt .rust (Or.inl rfl) c.bodies c.tcb fn body
                hpin)
          else if hadt2 :
              listBeq beqAdtDecl c.adts [nonZeroAdtDecl 0 .transparent] = true then
            have hadtsEq : c.adts = [nonZeroAdtDecl 0 .transparent] :=
              listEq_of_beq eq_of_beqAdtDecl hadt2
            have hadm : AdmissibleAdtInv c.adts c.adtInv := by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact nonZeroAdtInv_admissible
            finishNoPin hadm (fun fn body hpin => by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact proveBodyNonZeroOpt .transparent (Or.inr rfl) c.bodies c.tcb
                fn body hpin)
          else if hadt3 :
              listBeq beqAdtDecl c.adts [reprTransparentWrapAdtDecl] = true then
            have hadtsEq : c.adts = [reprTransparentWrapAdtDecl] :=
              listEq_of_beq eq_of_beqAdtDecl hadt3
            have hadm : AdmissibleAdtInv c.adts c.adtInv := by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact reprTransparentWrapAdtInv_admissible
            finishNoPin hadm (fun fn body hpin => by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact proveBodyTransWrapOpt c.bodies c.tcb fn body hpin)
          else if hadt4 :
              listBeq beqAdtDecl c.adts [reprRustWrapAdtDecl] = true then
            have hadtsEq : c.adts = [reprRustWrapAdtDecl] :=
              listEq_of_beq eq_of_beqAdtDecl hadt4
            have hadm : AdmissibleAdtInv c.adts c.adtInv := by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact reprRustWrapAdtInv_admissible
            finish hadm (fun fn body => by
              unfold Crate.adtInv
              rw [hadtsEq]
              exact proveBodyRustWrapOpt c.bodies c.tcb fn body)
          else
            .error ⟨"unsupported ADT inventory", "crate"⟩
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
}

/-- Expected `Crate` for unannotated `id` (`Operand.copy`, `specs := []`). -/
def idCopyWfCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := idCopyBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [] }]
}

/-- Expected `Crate` for `id` (`Operand.move`, `specs := [.ensuresEqArg 1]`). -/
def idMoveEnsuresCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := idMoveBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [.ensuresEqArg 1] }]
}

/-- Expected `Crate` for unannotated `id` (`Operand.move`, `specs := []`). -/
def idMoveWfCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := idMoveBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [] }]
}

/-- Expected `Crate` for `alloc_passthrough` (`specs := [.ensuresEqArg 1]`). -/
def allocPassthroughCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := allocPassthroughBody }]
  functions := [{
    name := fnName
    bodyId := ⟨0⟩
    specs := [.ensuresEqArg 1]
  }]
}

/-- Expected `Crate` for unannotated `alloc_passthrough` (`specs := []`). -/
def allocPassthroughWfCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := allocPassthroughBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [] }]
}

/-- Expected `Crate` for concrete PME caller `f`. -/
def pmeConcreteTransmuteCrate (fnName : String) : Crate := {
  bodies := [
    { id := ⟨0⟩, body := sizeEqConstBody },
    { id := ⟨1⟩, body := (transmuteCheckedBody ⟨0⟩) },
    { id := ⟨2⟩, body := (concreteTransmuteCallerBody ⟨1⟩ .usize) }
  ]
  functions := [{ name := fnName, bodyId := ⟨2⟩ }]
}

/-- Expected `Crate` for inline-const PME `inline_const_transmute`. -/
def inlineConstPmeCrate (fnName : String) : Crate := {
  bodies := [
    { id := ⟨0⟩, body := (sizeEqConstBodyAt .usize .usize) },
    { id := ⟨1⟩, body := (inlineConstTransmuteBody ⟨0⟩) }
  ]
  functions := [{ name := fnName, bodyId := ⟨1⟩ }]
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
      isUnsafe := true
      requires := newUncheckedRequires },
    { name := fn3Name, bodyId := ⟨2⟩ }
  ]
}

/-- Expected `Crate` for safe `clamp_nonzero` with `requires` and `ensures`. -/
def clampNonZeroCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := clampNonZeroBody }]
  functions := [{
    name := fnName
    bodyId := ⟨0⟩
    isUnsafe := false
    requires := newUncheckedRequires
    specs := [.ensuresEqArg 1]
  }]
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

/-- Expected `Crate` for `load_relaxed` (`specs := [.ensuresAtomicLoad 1]`). -/
def loadRelaxedEnsuresCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := loadRelaxedBody }]
  functions := [{
    name := fnName
    bodyId := ⟨0⟩
    specs := [.ensuresAtomicLoad 1]
  }]
}

/-- Expected `Crate` for unannotated `load_relaxed` (`specs := []`). -/
def loadRelaxedWfCrate (fnName : String) : Crate := {
  bodies := [{ id := ⟨0⟩, body := loadRelaxedBody }]
  functions := [{ name := fnName, bodyId := ⟨0⟩, specs := [] }]
}

/-- Canary confirming that `proveCrate` discharges all fifteen verified crate
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
    CrateTheorem (clampNonZeroCrate "clamp_nonzero") ∧
    CrateTheorem (transWrapTransmuteCrate "transparent_transmute") ∧
    CrateTheorem (rustWrapPinnedCrate "unguarded_transmute") ∧
    CrateTheorem (rustWrapGuardedCrate "guarded_transmute") ∧
    CrateTheorem (loadRelaxedEnsuresCrate "load_relaxed") ∧
    CrateTheorem (loadRelaxedWfCrate "load_relaxed") :=
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
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl,
   proveCrate _ rfl⟩

/-- Canary: when `--release` (`bodyId`) and `--debug` (`debugBodyId`) produce
distinct lowered `MirBody` entries (`idMoveBody` vs `idCopyBody`), `proveCrate`
verifies both profiles. -/
def dualProfileIdCrate : Crate := {
  bodies := [
    { id := ⟨0⟩, body := idMoveBody },
    { id := ⟨1⟩, body := idCopyBody }
  ]
  functions := [{
    name := "id"
    bodyId := ⟨0⟩
    debugBodyId := some ⟨1⟩
    specs := [.ensuresEqArg 1]
  }]
}

theorem canary_proveCrate_verifies_both_release_and_debug_bodies :
    CrateTheorem dualProfileIdCrate :=
  proveCrate _ rfl

/-- Canary: a function whose behavioral obligation is waived in `tcbWaivedIds`
(`/// anneal:trusted`) still has its `ContractWellFormed` obligation checked
unwaivably, while `proveCrate` accepts the waived behavioral obligation. -/
def trustedWaivedFunctionCrate : Crate := {
  bodies := [{ id := ⟨0⟩, body := wrongReturnZeroBody }]
  functions := [{
    name := "trusted_fn"
    bodyId := ⟨0⟩
    specs := [.ensuresEqArg 1]
  }]
  tcbWaivedIds := [.fnBody "trusted_fn"]
}

theorem canary_proveCrate_accepts_trusted_waiver :
    CrateTheorem trustedWaivedFunctionCrate :=
  proveCrate _ rfl

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
}

theorem canary_proveCrate_lowers_nop_in_id :
    CrateTheorem crateWithNopInIdBody :=
  proveCrate _ rfl

/-- Canary: projected shared borrows (`&x.0`) record `fieldDepth := 1`, resolve
to the inner field payload rather than the outer struct, and reject dangling
reads after a partial move of field `0`. -/
def borrowField0Body : MirBody where
  localCount := 4
  argTys := [.adt 0]
  retTy := .usize
  blocks := [{
    stmts := [
      .assign (locPlace 2) (.ref (field0Place 1)),
      .assign (locPlace 0) (.use (.copy (derefPlace 2)))
    ]
    terminator := .return_
  }]

theorem canary_projected_field_borrow_resolves_payload :
    let s0 : MirState := singleArgAdtNonZeroInitState 0
    ExecNormal [nonZeroAdtDecl 0] [] borrowField0Body s0
      (fun r => r.value = .usize 1) :=
  .step rfl (.step rfl (.normal rfl rfl))

/-- Canary: `Terminator.panic true` and `Terminator.assert _ _ _ .unwind true`
(`hasCleanup := true`) fail closed (`.failed`) rather than unwinding past an
unmodeled cleanup pad. -/
theorem canary_cleanup_unwind_fails_closed :
    let s0 : MirState := {
      locals := fun i => if i == 1 then some (.bool false) else none
      block := 0
      stmtIdx := 0
    }
    evalMirTerminator [] [] idCopyBody s0 (.panic true) = .failed ∧
    evalMirTerminator [] [] idCopyBody s0
      (.assert (.copy (locPlace 1)) true ⟨0⟩ .unwind true) = .failed :=
  ⟨rfl, rfl⟩

end Anneal
