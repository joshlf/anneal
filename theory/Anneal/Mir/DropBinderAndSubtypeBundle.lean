/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.DualCorrespondenceBundle
import MiniRustSpec.DropBinderAndSubtypeMR

/-!
# Episode 2 Dual-Authority Correspondence Bundle (`Anneal.Mir.DropBinderAndSubtypeBundle`)

Constructive (`[propext, Quot.sound]`, zero `Classical.choice` in codecs and
bundle combinators) dual-authority correspondence packaging for all 8
already-trusted MIR variants:

1. `StatementKind.coverage`
2. `StatementKind.backwardIncompatibleDropHint`
3. `TerminatorKind.drop` (whole-local, projected sub-place, dead-local UB, and
   genuine `basic` vs. `protectedTB` active-protector mode sensitivity)
4. `Rvalue.shallowInitBox`
5. `Rvalue.wrapUnsafeBinder`
6. `CastKind.subtype`
7. `AggregateKind.rawPtr` (thin `()` and wide `[u32]`/`str` metadata)
8. `AggregateKind.closure` (0-capture ZST and 2-capture `(u32, *const u32)`)

Design:
- **Authority 0 (Anneal Trusted MIR)**: `ep2AnnealEval` directly executes
  `Trusted.Rustc.V2026_06_01.MirSemantics.{stepMirFn, runAVal, faultsA}` on the
  concrete `CapturedMir` fixtures for all 8 variants (zero shadow evaluators).
- **Authority 1 (MiniRust)**: `mrAuthority` directly wraps
  `MiniRustSpec.DropBinderAndSubtypeMR.ep2MrObserve` (executing
  `MiniRustSpec.Interp.{steps, stepsTB}` on `Mach` and `MachTB`) via
  `ObsAuthority` with kernel-checked `denoteConsistent` and `Side.check`.
- **Authority 2 (LeanMiri)**: parameterized over any `ObsAuthority Ep2Key Ep2ObsVal`
  satisfying `lmCheckOf lmAuth = true` (closed in the cross-root kernel bridge
  in `tests/mir/DropBinderAndSubtypeCorrTests.lean` directly over
  `LeanMiriSpec.DropBinderAndSubtypeLM.ep2LmObserve`, which steps unmodified
  vendored `Miri.Interpreter.Step.step`).
- **Strict Import Isolation**: imports `Anneal.DualCorrespondenceBundle` and
  `MiniRustSpec.DropBinderAndSubtypeMR`, with NO `LeanMiriSpec.*` import.
-/

namespace Anneal.Mir.DropBinderAndSubtypeBundle

open Anneal.DualCorrespondenceBundle
open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01 Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness hiding constU32
open MiniRustSpec.Correspondence.PointerWitness MiniRustSpec.Correspondence.RefWitness
open MiniRustSpec.Correspondence.TbWitness
open MiniRustSpec.UnwindSetDiscrAndFnPtrMR
open MiniRustSpec.DropBinderAndSubtypeMR

/-! ## §1. Authority-Agnostic Constructive Finite-Corpus Layer -/

namespace Corpus

/-- Authority-independent description of one complete execution. -/
inductive Verdict (V : Type) : Type where
  | returns (v : V)
  | undefinedBehavior
  | unsupported
  deriving DecidableEq, Repr

/-- The four-way outcome denoted by a verdict. -/
def Verdict.toOutcome {V : Type} : Verdict V → ExecOutcome4 V Unit
  | .returns v => .normal v
  | .undefinedBehavior => .fault .undefined
  | .unsupported => .fault .unsupported

/-- Outcome of an optional verdict; `none` is a missing (stuck) run. -/
def outcome? {V : Type} (v : Option (Verdict V)) : Option (ExecOutcome4 V Unit) :=
  v.map Verdict.toOutcome

theorem Verdict.toOutcome_injective {V : Type} {a b : Verdict V}
    (h : a.toOutcome = b.toOutcome) : a = b := by
  cases a <;> cases b <;> first | rfl | (cases h; rfl) | cases h

theorem outcome?_injective {V : Type} {a b : Option (Verdict V)}
    (h : outcome? a = outcome? b) : a = b := by
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some _ => cases h
  | some x =>
    cases b with
    | none => cases h
    | some y =>
      have h' : x.toOutcome = y.toOutcome := Option.some.inj h
      rw [Verdict.toOutcome_injective h']

def isReturn {V : Type} : Option (Verdict V) → Bool
  | some (.returns _) => true
  | _ => false

def isFaultV {V : Type} : Option (Verdict V) → Bool
  | some .undefinedBehavior => true
  | some .unsupported => true
  | _ => false

def faultKindOf {V : Type} : Option (Verdict V) → CorrFaultKind
  | some .unsupported => .unsupported
  | _ => .undefined

/-- Reference authority presented strictly through its own authority-typed
observations (`Obs`) and decidable equality (`decEq`). -/
structure ObsAuthority (Key V : Type) : Type 1 where
  Obs : Type
  decEq : DecidableEq Obs
  observe : Key → Option Obs
  denote : List (Verdict V × Obs)

namespace ObsAuthority

variable {Key V : Type}

def decode (A : ObsAuthority Key V) (o : A.Obs) : Option (Verdict V) :=
  (A.denote.find? (fun d => @decide (d.2 = o) (A.decEq d.2 o))).map (fun d => d.1)

def verdict (A : ObsAuthority Key V) (k : Key) : Option (Verdict V) :=
  (A.observe k).bind A.decode

theorem verdict_eq_of_observe_eq (A : ObsAuthority Key V) {k k' : Key}
    (h : A.observe k = A.observe k') : A.verdict k = A.verdict k' := by
  unfold verdict; rw [h]

def matchesOn [DecidableEq V] (A : ObsAuthority Key V)
    (f : Key → Option (Verdict V)) (keys : List Key) : Bool :=
  keys.all (fun k => decide (A.verdict k = f k))

theorem matchesOn_sound [DecidableEq V] (A : ObsAuthority Key V)
    (f : Key → Option (Verdict V)) (keys : List Key)
    (h : A.matchesOn f keys = true) :
    ∀ k, k ∈ keys → A.verdict k = f k := by
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h k hk)

def denoteConsistent [DecidableEq V] (A : ObsAuthority Key V) : Bool :=
  A.denote.all fun d₁ =>
    A.denote.all fun d₂ =>
      !(@decide (d₁.2 = d₂.2) (A.decEq d₁.2 d₂.2)) || decide (d₁.1 = d₂.1)

private theorem find?_of_mem_pred {α : Type} (p : α → Bool) {xs : List α} {x : α}
    (h : x ∈ xs) (hp : p x = true) :
    ∃ y, xs.find? p = some y ∧ y ∈ xs ∧ p y = true := by
  induction xs with
  | nil => cases h
  | cons a tl ih =>
    unfold List.find?
    cases ha : p a with
    | true => exact ⟨a, rfl, List.mem_cons_self, ha⟩
    | false =>
      cases h with
      | head => rw [ha] at hp; cases hp
      | tail _ hmem =>
        obtain ⟨y, hy, hyl, hyp⟩ := ih hmem
        exact ⟨y, hy, List.mem_cons_of_mem _ hyl, hyp⟩

theorem denoteConsistent_sound [DecidableEq V] (A : ObsAuthority Key V)
    (h : A.denoteConsistent = true) {v : Verdict V} {o : A.Obs}
    (hm : (v, o) ∈ A.denote) : A.decode o = some v := by
  let p : Verdict V × A.Obs → Bool := fun d => @decide (d.2 = o) (A.decEq d.2 o)
  have hpo : p (v, o) = true := @decide_eq_true (o = o) (A.decEq o o) rfl
  obtain ⟨y, hy, hyl, hyp⟩ := find?_of_mem_pred p hm hpo
  have hyo : y.2 = o := @of_decide_eq_true (y.2 = o) (A.decEq y.2 o) hyp
  have hall₁ := List.all_eq_true.mp h y hyl
  have hall₂ := List.all_eq_true.mp hall₁ (v, o) hm
  have hdec : @decide (y.2 = o) (A.decEq y.2 o) = true :=
    @decide_eq_true (y.2 = o) (A.decEq y.2 o) hyo
  rw [hdec] at hall₂
  have hyv : y.1 = v := of_decide_eq_true hall₂
  unfold decode
  change (A.denote.find? p).map (fun d => d.1) = some v
  rw [hy]
  exact congrArg some hyv

end ObsAuthority

structure Model (ModeA Prog Query Choice VA Rep : Type) : Type where
  evalA : ModeA → Prog → Query → Choice → Option (Verdict VA)
  codec : CodecLaws VA Rep
  progs : List Prog
  queries : List Query
  choices : List Choice
  progs_complete : ∀ p, p ∈ progs
  queries_complete : ∀ q, q ∈ queries
  choices_complete : ∀ c, c ∈ choices

structure Side (ModeA Mode Prog Query Choice VR Rep : Type) : Type where
  toAnneal : Mode → ModeA
  gate : Mode → Prog → Query → Bool
  verdictR : Mode → Prog → Query → Choice → Option (Verdict VR)
  rep : VR → Rep
  modes : List Mode
  modes_complete : ∀ m, m ∈ modes
  wMode : Mode
  okProg : Prog
  okQuery : Query
  okChoice : Choice
  faultProg : Prog
  faultQuery : Query
  faultChoice : Choice
  flip : Option (Mode × Mode × Prog × Query × Choice)

def couplesB {VA VR Rep : Type} [DecidableEq Rep] (enc : VA → Rep) (rep : VR → Rep) :
    Option (Verdict VA) → Option (Verdict VR) → Bool
  | some (.returns a), some (.returns r) => decide (rep r = enc a)
  | some .undefinedBehavior, some .undefinedBehavior => true
  | some .unsupported, some .unsupported => true
  | _, _ => false

theorem couplesB_sound {VA VR Rep : Type} [DecidableEq Rep]
    {enc : VA → Rep} {rep : VR → Rep}
    {va : Option (Verdict VA)} {vr : Option (Verdict VR)}
    (h : couplesB enc rep va vr = true) :
    ∃ oa orr, outcome? va = some oa ∧ outcome? vr = some orr ∧
      ChoiceCoupledOutcomeRel (fun a r => rep r = enc a)
        (fun (_ : Unit) (_ : Unit) => True) oa orr := by
  cases va with
  | none => cases vr <;> cases h
  | some a =>
    cases vr with
    | none => cases a <;> cases h
    | some r =>
      cases a <;> cases r <;>
        first
        | exact ⟨_, _, rfl, rfl, ChoiceCoupledOutcomeRel.ofNormal (of_decide_eq_true h)⟩
        | exact ⟨_, _, rfl, rfl, ChoiceCoupledOutcomeRel.ofFault _⟩
        | cases h

theorem couplesB_returns {VA VR Rep : Type} [DecidableEq Rep]
    {enc : VA → Rep} {rep : VR → Rep} {a : VA} {vr : Option (Verdict VR)}
    (h : couplesB enc rep (some (.returns a)) vr = true) :
    ∃ r, vr = some (.returns r) ∧ rep r = enc a := by
  cases vr with
  | none => cases h
  | some r =>
    cases r with
    | returns r => exact ⟨r, rfl, of_decide_eq_true h⟩
    | undefinedBehavior => cases h
    | unsupported => cases h

theorem couplesB_fault {VA VR Rep : Type} [DecidableEq Rep]
    {enc : VA → Rep} {rep : VR → Rep}
    {va : Option (Verdict VA)} {vr : Option (Verdict VR)}
    (h : couplesB enc rep va vr = true) (hf : isFaultV va = true) :
    outcome? va = some (.fault (faultKindOf va)) ∧
      outcome? vr = some (.fault (faultKindOf va)) := by
  cases va with
  | none => cases hf
  | some a =>
    cases a with
    | returns _ => cases hf
    | undefinedBehavior =>
      cases vr with
      | none => cases h
      | some r => cases r <;> first | exact ⟨rfl, rfl⟩ | cases h
    | unsupported =>
      cases vr with
      | none => cases h
      | some r => cases r <;> first | exact ⟨rfl, rfl⟩ | cases h

namespace Side

variable {ModeA Mode Prog Query Choice VA VR Rep : Type}

def rel (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) :
    ModeParamStepRel Mode Prog Query Choice VA VR Unit Unit where
  SupportGate := fun m p q => S.gate m p q = true
  ExecA := fun m p q c out => outcome? (M.evalA (S.toAnneal m) p q c) = some out
  ExecR := fun m p q c out => outcome? (S.verdictR m p q c) = some out
  RetRel := fun a r => S.rep r = M.codec.encode a
  UnwRel := fun _ _ => True

def simCheck [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) : Bool :=
  S.modes.all fun m => M.progs.all fun p => M.queries.all fun q =>
    M.choices.all fun c =>
      !S.gate m p q ||
        couplesB M.codec.encode S.rep (M.evalA (S.toAnneal m) p q c) (S.verdictR m p q c)

def witCheck [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) : Bool :=
  S.gate S.wMode S.okProg S.okQuery &&
  isReturn (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery S.okChoice) &&
  M.choices.all (fun c => !isFaultV (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery c)) &&
  S.gate S.wMode S.faultProg S.faultQuery &&
  isFaultV (M.evalA (S.toAnneal S.wMode) S.faultProg S.faultQuery S.faultChoice) &&
  (match S.flip with
   | none => true
   | some (m₁, m₂, p, q, c) =>
     S.gate m₁ p q && S.gate m₂ p q &&
     (M.evalA (S.toAnneal m₁) p q c).isSome &&
     M.choices.all (fun c' => decide
       (M.evalA (S.toAnneal m₂) p q c' ≠ M.evalA (S.toAnneal m₁) p q c)) &&
     M.choices.all (fun c' => decide
       (S.verdictR m₂ p q c' ≠ S.verdictR m₁ p q c)))

def check [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) : Bool :=
  S.simCheck M && S.witCheck M

theorem simCheck_spec [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.simCheck M = true)
    (m : Mode) (p : Prog) (q : Query) (c : Choice) (hg : S.gate m p q = true) :
    couplesB M.codec.encode S.rep (M.evalA (S.toAnneal m) p q c) (S.verdictR m p q c) = true := by
  have h₁ := List.all_eq_true.mp h m (S.modes_complete m)
  have h₂ := List.all_eq_true.mp h₁ p (M.progs_complete p)
  have h₃ := List.all_eq_true.mp h₂ q (M.queries_complete q)
  have h₄ := List.all_eq_true.mp h₃ c (M.choices_complete c)
  rw [hg] at h₄
  exact h₄

theorem forward [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.simCheck M = true) :
    (S.rel M).ForwardTotal := by
  intro m p q c outR hg hR
  obtain ⟨oa, orr, ha, hr, hc⟩ := couplesB_sound (S.simCheck_spec M h m p q c hg)
  have hR' : outcome? (S.verdictR m p q c) = some outR := hR
  rw [hr] at hR'; cases hR'
  exact ⟨oa, ha, hc⟩

theorem reverseTotal [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.simCheck M = true) :
    (S.rel M).ReverseTotal := by
  intro m p q c outA hg hA
  obtain ⟨oa, orr, ha, hr, hc⟩ := couplesB_sound (S.simCheck_spec M h m p q c hg)
  have hA' : outcome? (M.evalA (S.toAnneal m) p q c) = some outA := hA
  rw [ha] at hA'; cases hA'
  exact ⟨orr, hr, hc⟩

theorem reverseFault [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.simCheck M = true) :
    (S.rel M).ReverseFaultTotal := by
  intro m p q c k hg hA
  obtain ⟨outR, hR, hc⟩ := S.reverseTotal M h m p q c (.fault k) hg hA
  have hk : outR = .fault k := (hc.fault_iff k).mp rfl
  rw [hk] at hR; exact hR

theorem witCheck_parts [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.witCheck M = true) :
    S.gate S.wMode S.okProg S.okQuery = true ∧
    isReturn (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery S.okChoice) = true ∧
    (M.choices.all (fun c => !isFaultV (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery c))) = true ∧
    S.gate S.wMode S.faultProg S.faultQuery = true ∧
    isFaultV (M.evalA (S.toAnneal S.wMode) S.faultProg S.faultQuery S.faultChoice) = true := by
  unfold witCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

def positiveAt [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (hs : S.simCheck M = true)
    (m : Mode) (p : Prog) (q : Query) (c : Choice) (hg : S.gate m p q = true)
    (hr : isReturn (M.evalA (S.toAnneal m) p q c) = true)
    (hwf : (M.choices.all (fun c' => !isFaultV (M.evalA (S.toAnneal m) p q c'))) = true) :
    PositiveWitness (S.rel M) where
  m := m; p := p; q := q; c := c; gate := hg
  wf := fun c' k hk => by
    have hc := List.all_eq_true.mp hwf c' (M.choices_complete c')
    have hk' : outcome? (M.evalA (S.toAnneal m) p q c') = some (.fault k) := hk
    cases hv : M.evalA (S.toAnneal m) p q c' with
    | none => rw [hv] at hk'; cases hk'
    | some v =>
      rw [hv] at hk' hc
      cases v with
      | returns _ => cases hk'
      | undefinedBehavior => cases hc
      | unsupported => cases hc
  agree := by
    have hc := S.simCheck_spec M hs m p q c hg
    cases hv : M.evalA (S.toAnneal m) p q c with
    | none => rw [hv] at hr; cases hr
    | some v =>
      rw [hv] at hr hc
      cases v with
      | returns a =>
        obtain ⟨r, hvr, hrep⟩ := couplesB_returns hc
        refine ⟨a, r, ?_, ?_, hrep⟩
        · show outcome? (M.evalA (S.toAnneal m) p q c) = some (.normal a); rw [hv]; rfl
        · show outcome? (S.verdictR m p q c) = some (.normal r); rw [hvr]; rfl
      | undefinedBehavior => cases hr
      | unsupported => cases hr

def faultAt [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (hs : S.simCheck M = true)
    (m : Mode) (p : Prog) (q : Query) (c : Choice) (hg : S.gate m p q = true)
    (hf : isFaultV (M.evalA (S.toAnneal m) p q c) = true) :
    FaultEquivWitness (S.rel M) where
  m := m; p := p; q := q; c := c
  kind := faultKindOf (M.evalA (S.toAnneal m) p q c)
  gate := hg
  execA := (couplesB_fault (S.simCheck_spec M hs m p q c hg) hf).1
  execR := (couplesB_fault (S.simCheck_spec M hs m p q c hg) hf).2

def positive [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.check M = true) :
    PositiveWitness (S.rel M) :=
  have hs : S.simCheck M = true := (Bool.and_eq_true _ _ ▸ h).1
  have hw := S.witCheck_parts M (Bool.and_eq_true _ _ ▸ h).2
  S.positiveAt M hs S.wMode S.okProg S.okQuery S.okChoice hw.1 hw.2.1 hw.2.2.1

def faultW [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.check M = true) :
    FaultEquivWitness (S.rel M) :=
  have hs : S.simCheck M = true := (Bool.and_eq_true _ _ ▸ h).1
  have hw := S.witCheck_parts M (Bool.and_eq_true _ _ ▸ h).2
  S.faultAt M hs S.wMode S.faultProg S.faultQuery S.faultChoice hw.2.2.2.1 hw.2.2.2.2

def flipW [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) (h : S.check M = true) :
    Option (ModeSensitivityWitness (S.rel M)) :=
  have hs : S.simCheck M = true := (Bool.and_eq_true _ _ ▸ h).1
  have hw : S.witCheck M = true := (Bool.and_eq_true _ _ ▸ h).2
  match hfl : S.flip with
  | none => none
  | some (m₁, m₂, p, q, c) =>
    have hparts :
        S.gate m₁ p q = true ∧ S.gate m₂ p q = true ∧
        (M.evalA (S.toAnneal m₁) p q c).isSome = true ∧
        (M.choices.all (fun c' => decide
          (M.evalA (S.toAnneal m₂) p q c' ≠ M.evalA (S.toAnneal m₁) p q c))) = true ∧
        (M.choices.all (fun c' => decide
          (S.verdictR m₂ p q c' ≠ S.verdictR m₁ p q c))) = true := by
      unfold witCheck at hw; rw [hfl] at hw; simp only [Bool.and_eq_true] at hw
      exact ⟨hw.2.1.1.1.1, hw.2.1.1.1.2, hw.2.1.1.2, hw.2.1.2, hw.2.2⟩
    some
      { m₁ := m₁
        m₂ := m₂
        p := p
        q := q
        c := c
        gate₁ := hparts.1
        gate₂ := hparts.2.1
        flips := by
          obtain ⟨oa, orr, ha, hr, hc⟩ := couplesB_sound (S.simCheck_spec M hs m₁ p q c hparts.1)
          refine ⟨oa, orr, ha, hr, hc, ?_, ?_⟩
          · intro c' hA
            have hA' : outcome? (M.evalA (S.toAnneal m₂) p q c') = some oa := hA
            rw [← ha] at hA'
            exact of_decide_eq_true
              (List.all_eq_true.mp hparts.2.2.2.1 c' (M.choices_complete c'))
              (outcome?_injective hA')
          · intro c' hR
            have hR' : outcome? (S.verdictR m₂ p q c') = some orr := hR
            rw [← hr] at hR'
            exact of_decide_eq_true
              (List.all_eq_true.mp hparts.2.2.2.2 c' (M.choices_complete c'))
              (outcome?_injective hR') }

end Side

def bundle {ModeA Prog Query Choice VA Rep ModeMR VMR ModeLM VLM : Type}
    [DecidableEq Rep] [DecidableEq VA] [DecidableEq VMR] [DecidableEq VLM]
    (M : Model ModeA Prog Query Choice VA Rep)
    (SMR : Side ModeA ModeMR Prog Query Choice VMR Rep)
    (SLM : Side ModeA ModeLM Prog Query Choice VLM Rep)
    (hMR : SMR.check M = true) (hLM : SLM.check M = true) :
    DualCorrespondenceBundle ModeA Prog Query VA Unit Rep ModeMR Choice VMR
      Unit ModeLM Choice VLM Unit :=
  DualCorrespondenceBundle.fromRelEquiv M.codec SMR.rep SLM.rep
    (fun mA p q out => ∃ c, outcome? (M.evalA mA p q c) = some out)
    SMR.toAnneal SLM.toAnneal (SMR.rel M) (SLM.rel M)
    (fun _ _ h => h) (fun _ _ h => h)
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    (SMR.forward M (Bool.and_eq_true _ _ ▸ hMR).1)
    (SMR.reverseFault M (Bool.and_eq_true _ _ ▸ hMR).1)
    (SLM.forward M (Bool.and_eq_true _ _ ▸ hLM).1)
    (SLM.reverseFault M (Bool.and_eq_true _ _ ▸ hLM).1)
    (SMR.positive M hMR) (SLM.positive M hLM)
    (SMR.faultW M hMR) (SLM.faultW M hLM) rfl rfl
    (SMR.flipW M hMR) (SLM.flipW M hLM)
    (some ⟨SMR.reverseTotal M (Bool.and_eq_true _ _ ▸ hMR).1⟩)
    (some ⟨SLM.reverseTotal M (Bool.and_eq_true _ _ ▸ hLM).1⟩)

end Corpus

/-! ## §2. Episode 2 Observable Value Domain & Constructive `CodecLaws` -/

/-- Shared observable value domain for all 8 Episode 2 MIR variants. -/
inductive Ep2ObsVal : Type where
  | u32Val (bits : Nat)
  | u8Val (bits : Nat)
  | usizeVal (bits : Nat)
  | ptrAlloc (allocId : Nat)
  | zst
  | closureCap (u32Bits : Nat) (allocId : Nat)
  deriving DecidableEq, Repr

/-- Canonical tagged-tuple wire representation (`tag, payload1, payload2`) for
`Ep2ObsVal`, strictly constructive with tight `ValidRep`. -/
abbrev Ep2Rep : Type := Nat × Nat × Nat

def ep2Encode : Ep2ObsVal → Ep2Rep
  | .u32Val n => (0, n, 0)
  | .u8Val n => (1, n, 0)
  | .usizeVal n => (2, n, 0)
  | .ptrAlloc aid => (3, aid, 0)
  | .zst => (4, 0, 0)
  | .closureCap u aid => (5, u, aid)

def ep2Decode : Ep2Rep → Option Ep2ObsVal
  | (0, n, 0) => some (.u32Val n)
  | (1, n, 0) => some (.u8Val n)
  | (2, n, 0) => some (.usizeVal n)
  | (3, aid, 0) => some (.ptrAlloc aid)
  | (4, 0, 0) => some .zst
  | (5, u, aid) => some (.closureCap u aid)
  | _ => none

def ep2ValidRep : Ep2Rep → Prop
  | (0, _, 0) => True
  | (1, _, 0) => True
  | (2, _, 0) => True
  | (3, _, 0) => True
  | (4, 0, 0) => True
  | (5, _, _) => True
  | _ => False

/-- Constructive `CodecLaws Ep2ObsVal Ep2Rep` (uses only `[propext, Quot.sound]`,
zero `Classical.choice`, with tight `ValidRep`). -/
def ep2Codec : CodecLaws Ep2ObsVal Ep2Rep where
  encode := ep2Encode
  decode := ep2Decode
  ValidRep := ep2ValidRep
  decode_encode := fun a => by cases a <;> rfl
  encode_valid := fun a => by cases a <;> exact True.intro
  encode_decode_of_valid := fun b a hv hd => by
    rcases b with ⟨t, x, y⟩
    match t with
    | 0 => cases y with | zero => cases hd; rfl | succ _ => exact False.elim hv
    | 1 => cases y with | zero => cases hd; rfl | succ _ => exact False.elim hv
    | 2 => cases y with | zero => cases hd; rfl | succ _ => exact False.elim hv
    | 3 => cases y with | zero => cases hd; rfl | succ _ => exact False.elim hv
    | 4 =>
      cases x with
      | zero => cases y with | zero => cases hd; rfl | succ _ => exact False.elim hv
      | succ _ => exact False.elim hv
    | 5 => cases hd; rfl
    | n + 6 => exact False.elim hv

theorem ep2Codec_tight : ep2Codec.TightValidRep := by
  intro b hv
  rcases b with ⟨t, x, y⟩
  match t with
  | 0 => cases y with | zero => exact ⟨.u32Val x, rfl⟩ | succ _ => exact False.elim hv
  | 1 => cases y with | zero => exact ⟨.u8Val x, rfl⟩ | succ _ => exact False.elim hv
  | 2 => cases y with | zero => exact ⟨.usizeVal x, rfl⟩ | succ _ => exact False.elim hv
  | 3 => cases y with | zero => exact ⟨.ptrAlloc x, rfl⟩ | succ _ => exact False.elim hv
  | 4 =>
    cases x with
    | zero => cases y with | zero => exact ⟨.zst, rfl⟩ | succ _ => exact False.elim hv
    | succ _ => exact False.elim hv
  | 5 => exact ⟨.closureCap x y, rfl⟩
  | n + 6 => exact False.elim hv

/-! ## §3. Mode, Key Enumerations, & Executable Trusted Anneal Model (`ep2AnnealEval`) -/

/-- Dual-authority execution mode: basic memory / unprotected borrows vs.
Tree Borrows active-protector enforcement. -/
inductive Ep2Mode : Type where
  | basic
  | protectedTB
  deriving DecidableEq, Repr

/-- Unified corpus key across all 2 modes × 8 variants × 4 cases = 64 keys. -/
abbrev Ep2Key : Type := Ep2Mode × Ep2Variant × Ep2Case

def ep2ModeToMr : Ep2Mode → Ep2MrMode
  | .basic => .basicMemory
  | .protectedTB => .treeBorrows

def ep2MrToMode : Ep2MrMode → Ep2Mode
  | .basicMemory => .basic
  | .treeBorrows => .protectedTB

def ep2ModeToLmProtected : Ep2Mode → Bool
  | .basic => false
  | .protectedTB => true

def ep2LmProtectedToMode : Bool → Ep2Mode
  | false => .basic
  | true => .protectedTB

def allEp2Modes : List Ep2Mode := [.basic, .protectedTB]
def allEp2MrModes : List Ep2MrMode := [.basicMemory, .treeBorrows]
def allEp2LmModes : List Bool := [false, true]

def allEp2Variants : List Ep2Variant :=
  [.coverage, .backwardIncompatibleDropHint, .dropTerminator, .shallowInitBox,
   .wrapUnsafeBinder, .castSubtype, .aggregateRawPtr, .aggregateClosure]

def allEp2Cases : List Ep2Case := [.okPrimary, .okSecondary, .ubFault, .modeCase]

def allEp2Keys : List Ep2Key :=
  allEp2Modes.flatMap fun m =>
    allEp2Variants.flatMap fun v =>
      allEp2Cases.map fun c => (m, v, c)

theorem allEp2Modes_complete (m : Ep2Mode) : m ∈ allEp2Modes := by
  cases m <;> simp [allEp2Modes]

theorem allEp2MrModes_complete (m : Ep2MrMode) : m ∈ allEp2MrModes := by
  cases m <;> simp [allEp2MrModes]

theorem allEp2LmModes_complete (b : Bool) : b ∈ allEp2LmModes := by
  cases b <;> simp [allEp2LmModes]

theorem allEp2Variants_complete (v : Ep2Variant) : v ∈ allEp2Variants := by
  cases v <;> simp [allEp2Variants]

theorem allEp2Cases_complete (c : Ep2Case) : c ∈ allEp2Cases := by
  cases c <;> simp [allEp2Cases]

/-- V8 0-capture ZST closure `CapturedMir` fixture (exported for cross-root fixture locks). -/
def v8ClosureZstMir : CapturedMir :=
  mkMirBody "ep2::v8_closure_zst" [mkDecl (closureZstMirTy "ep2::zst")] 0
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.closure "ep2::zst") []))] .return_]

def ep2ZstClosureLayout : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

def ep2U32FieldLayout : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xffffffff⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def ep2PtrFieldLayout : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xffffffffffffffff⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def ep2ClosureCapLayout : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩,
    backendRepr := .scalarPair
      (.initialized (.int 32 false) ⟨0, 0xffffffff⟩)
      (.initialized (.pointer 0) ⟨0, 0xffffffffffffffff⟩),
    fields := .arbitrary [⟨0⟩, ⟨8⟩] [0, 1],
    fieldLayouts := [2, 3],
    variants := .single 0, isUninhabited := false }

def ep2ClosureCapLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [ep2ZstClosureLayout, ep2ClosureCapLayout, ep2U32FieldLayout, ep2PtrFieldLayout] }

@[reducible] def v8ClosureCapMirTy : MirAst.Ty :=
  { kind := .closure "ep2::cap" [.uint .u32, .rawPtr .not (.uint .u32)], layoutIdx := 1 }

/-- V8 2-capture `(u32, *const u32)` closure `CapturedMir` fixture (exported for cross-root fixture locks). -/
def v8ClosureCapMir : CapturedMir :=
  mkMirBody "ep2::v8_closure_cap"
    [mkDecl v8ClosureCapMirTy, mkDecl u32MirTy, mkDecl rawConstU32MirTy] 2
    [mkBb [mkSt (.assign (locPlace 0) (.aggregate (.closure "ep2::cap") [.move (locPlace 1), .copy (locPlace 2)]))]
      .return_]
    ep2ClosureCapLayouts

/-- Extract an `Ep2ObsVal` directly from a Trusted `MirSemantics.Value`. -/
def obsTrustedValue : MirSemantics.Value → Option Ep2ObsVal
  | .scalar ⟨bits, 1⟩ => some (.u8Val bits)
  | .scalar ⟨bits, 4⟩ => some (.u32Val bits)
  | .scalar ⟨bits, 8⟩ => some (.usizeVal bits)
  | .ptr p 8 => some (.ptrAlloc p.allocId)
  | .aggregate 0 [] => some .zst
  | .aggregate 0 [.scalar ⟨bits, 1⟩] => some (.u8Val bits)
  | .aggregate 0 [.scalar ⟨u, 4⟩, .ptr p 8] => some (.closureCap u p.allocId)
  | _ => none

/-- State of a bounded Trusted `stepMirFn` execution. -/
private inductive TrustedRunState : Type where
  | running (s : MachineState)
  | done (v : Option (Corpus.Verdict Ep2ObsVal))

private def trustedRunStep (body : CapturedMir) : TrustedRunState → TrustedRunState
  | .done v => .done v
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => .running s'
      | _ => .done none
    | .ret (.normal r) => .done ((obsTrustedValue r.1).map Corpus.Verdict.returns)
    | .vis (.inl (.fail .ub)) _ => .done (some .undefinedBehavior)
    | .vis (.inl (.fail .unsupported)) _ => .done (some .unsupported)
    | _ => .done none

/-- Execute `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` directly for up to
`fuel` steps and return the observable `Corpus.Verdict Ep2ObsVal`. -/
def runTrustedVerdict (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    Option (Corpus.Verdict Ep2ObsVal) :=
  match Nat.repeat (trustedRunStep body) fuel (.running s) with
  | .done v => v
  | .running _ => none

/-- Direct Trusted Anneal execution for EVERY `(mode, variant, case)` key across
all 8 Episode 2 MIR variants. Zero shadow evaluators: every arm invokes
`runTrustedVerdict` -> `Trusted.Rustc.V2026_06_01.MirSemantics.stepMirFn` on the
actual `CapturedMir` fixture! -/
def ep2AnnealEval (mode : Ep2Mode) (v : Ep2Variant) (c : Ep2Case) (_ch : Unit) :
    Option (Corpus.Verdict Ep2ObsVal) :=
  match v, c with
  | .coverage, .okPrimary =>
    runTrustedVerdict v1CoverageOkMir 10 (initMachineState v1CoverageOkMir [])
  | .coverage, .okSecondary =>
    runTrustedVerdict v1CoverageOkMir 10 (initMachineState v1CoverageOkMir [])
  | .coverage, .ubFault =>
    runTrustedVerdict v1CoverageUbMir 10 (initMachineState v1CoverageUbMir [])
  | .coverage, .modeCase =>
    runTrustedVerdict v1CoverageOkMir 10 (initMachineState v1CoverageOkMir [])
  | .backwardIncompatibleDropHint, .okPrimary =>
    runTrustedVerdict v2DropHintOkMir 10 (initMachineState v2DropHintOkMir [])
  | .backwardIncompatibleDropHint, .okSecondary =>
    runTrustedVerdict v2DropHintOkMir 10 (initMachineState v2DropHintOkMir [])
  | .backwardIncompatibleDropHint, .ubFault =>
    runTrustedVerdict v2DropHintDeadReadUbMir 10 (initMachineState v2DropHintDeadReadUbMir [])
  | .backwardIncompatibleDropHint, .modeCase =>
    runTrustedVerdict v2DropHintOkMir 10 (initMachineState v2DropHintOkMir [])
  | .dropTerminator, .okPrimary =>
    runTrustedVerdict v3DropWholeOkMir 10 (initMachineState v3DropWholeOkMir [.scalar ⟨11, 4⟩])
  | .dropTerminator, .okSecondary =>
    runTrustedVerdict v3DropProjSiblingOkMir 10
      (initMachineState v3DropProjSiblingOkMir [.aggregate 0 [.scalar ⟨11, 4⟩, .scalar ⟨99, 4⟩]])
  | .dropTerminator, .ubFault =>
    runTrustedVerdict v3DropDeadUbMir 10 (initMachineState v3DropDeadUbMir [.scalar ⟨11, 4⟩])
  | .dropTerminator, .modeCase =>
    runTrustedVerdict v3DropProtectedMir 10
      (v3DropProtectedInitState (mode == .protectedTB))
  | .shallowInitBox, .okPrimary =>
    runTrustedVerdict v4ShallowInitBoxOkMir 10
      (initMachineState v4ShallowInitBoxOkMir [.ptr { allocId := 2, offsetBytes := 0 } 8])
  | .shallowInitBox, .okSecondary =>
    runTrustedVerdict v4ShallowInitBoxDistinctOkMir 10
      (initMachineState v4ShallowInitBoxDistinctOkMir [.ptr { allocId := 5, offsetBytes := 0 } 8])
  | .shallowInitBox, .ubFault =>
    runTrustedVerdict v4ShallowInitBoxOkMir 10
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead] }, memory := emptyMemory }
  | .shallowInitBox, .modeCase =>
    runTrustedVerdict v4ShallowInitBoxOkMir 10
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] }, memory := emptyMemory }
  | .wrapUnsafeBinder, .okPrimary =>
    runTrustedVerdict v5WrapStructRoundtripMir 10
      (initMachineState v5WrapStructRoundtripMir [.scalar ⟨73, 4⟩])
  | .wrapUnsafeBinder, .okSecondary =>
    runTrustedVerdict v5WrapNzU8Mir 10 (initMachineState v5WrapNzU8Mir [.scalar ⟨7, 1⟩])
  | .wrapUnsafeBinder, .ubFault =>
    runTrustedVerdict v5WrapNzU8Mir 10 (initMachineState v5WrapNzU8Mir [.scalar ⟨0, 1⟩])
  | .wrapUnsafeBinder, .modeCase =>
    runTrustedVerdict v5WrapBoolMir 10 (initMachineState v5WrapBoolMir [.scalar ⟨2, 1⟩])
  | .castSubtype, .okPrimary =>
    runTrustedVerdict c7SubtypeU32ToI32Mir 10
      (initMachineState c7SubtypeU32ToI32Mir [.scalar ⟨4294967295, 4⟩])
  | .castSubtype, .okSecondary =>
    runTrustedVerdict c7SubtypeU8ToNzMir 10 (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨7, 1⟩])
  | .castSubtype, .ubFault =>
    runTrustedVerdict c7SubtypeU8ToBoolMir 10 (initMachineState c7SubtypeU8ToBoolMir [.scalar ⟨2, 1⟩])
  | .castSubtype, .modeCase =>
    runTrustedVerdict c7SubtypeU8ToNzMir 10 (initMachineState c7SubtypeU8ToNzMir [.scalar ⟨0, 1⟩])
  | .aggregateRawPtr, .okPrimary =>
    runTrustedVerdict v7RawPtrThinMir 10
      (initMachineState v7RawPtrThinMir [.ptr { allocId := 5, offsetBytes := 0 } 8, .unit])
  | .aggregateRawPtr, .okSecondary =>
    runTrustedVerdict v7RawPtrWideSliceMetaMir 10
      (initMachineState v7RawPtrWideSliceMetaMir [.ptr { allocId := 5, offsetBytes := 0 } 8, .scalar ⟨5, 8⟩])
  | .aggregateRawPtr, .ubFault =>
    runTrustedVerdict v7RawPtrThinMir 10
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead, .init .unit] }, memory := emptyMemory }
  | .aggregateRawPtr, .modeCase =>
    runTrustedVerdict v7RawPtrWideSliceMetaMir 10
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .init (.ptr { allocId := 5, offsetBytes := 0 } 8), .uninit, .uninit] },
        memory := emptyMemory }
  | .aggregateClosure, .okPrimary =>
    runTrustedVerdict v8ClosureZstMir 10 (initMachineState v8ClosureZstMir [])
  | .aggregateClosure, .okSecondary =>
    runTrustedVerdict v8ClosureCapMir 10
      (initMachineState v8ClosureCapMir [.scalar ⟨7, 4⟩, .ptr { allocId := 1, offsetBytes := 0 } 8])
  | .aggregateClosure, .ubFault =>
    runTrustedVerdict v8ClosureCapMir 10
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .dead, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] },
        memory := emptyMemory }
  | .aggregateClosure, .modeCase =>
    runTrustedVerdict v8ClosureCapMir 10
      { frame := { blockIdx := 0, stmtIdx := 0,
                   locals := [.uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] },
        memory := emptyMemory }

/-- Anneal corpus model over all 8 Episode 2 MIR variants. -/
def ep2Model : Corpus.Model Ep2Mode Ep2Variant Ep2Case Unit Ep2ObsVal Ep2Rep where
  evalA := ep2AnnealEval
  codec := ep2Codec
  progs := allEp2Variants
  queries := allEp2Cases
  choices := [()]
  progs_complete := allEp2Variants_complete
  queries_complete := allEp2Cases_complete
  choices_complete := fun u => by cases u; simp

/-! ## §4. Concrete MiniRust Authority (`mrAuthority`) Directly Over `MiniRustSpec.Interp` -/

private def mrBytesObs (bs : List Byte) : Ep2MrObs :=
  .retBytes (bs.map (projByteTB ∘ liftByteTB))

/-- Non-colliding observation denotation table for `MiniRustSpec.DropBinderAndSubtypeMR.ep2MrObserve`. -/
def mrDenote : List (Corpus.Verdict Ep2ObsVal × Ep2MrObs) :=
  [ (.returns (.u32Val 17), mrBytesObs (scalarBytes u32 17)),
    (.returns (.u32Val 23), mrBytesObs (scalarBytes u32 23)),
    (.returns (.u32Val 42), mrBytesObs (scalarBytes u32 42)),
    (.returns (.u32Val 99), mrBytesObs (scalarBytes u32 99)),
    (.returns (.u32Val 73), mrBytesObs (scalarBytes u32 73)),
    (.returns (.u32Val 4294967295), mrBytesObs (scalarBytes u32 4294967295)),
    (.returns (.u8Val 7), mrBytesObs [.Init 7 none]),
    (.returns (.usizeVal 5), mrBytesObs (scalarBytes IntType.usize_ty 5)),
    (.returns (.ptrAlloc 2), mrBytesObs (ptrBytes 384 (some (⟨2⟩, ())))),
    (.returns (.ptrAlloc 5), mrBytesObs (ptrBytes 1024 (some (⟨5⟩, ())))),
    (.returns .zst, mrBytesObs []),
    (.returns (.closureCap 7 1), mrBytesObs c10ExpectedCapBytes),
    (.undefinedBehavior, .ub),
    (.unsupported, .unsupported) ]

/-- MiniRust `ObsAuthority` directly invoking `MiniRustSpec.DropBinderAndSubtypeMR.ep2MrObserve`
(which runs `MiniRustSpec.Interp.steps` / `stepsTB` on `Mach` / `MachTB`). -/
def mrAuthority : Corpus.ObsAuthority Ep2Key Ep2ObsVal where
  Obs := Ep2MrObs
  decEq := inferInstance
  observe := fun (m, v, c) => some (ep2MrObserve (ep2ModeToMr m) v c)
  denote := mrDenote

/-- Kernel-checked non-shadowing / injectivity of `mrAuthority.denote`. -/
theorem mrAuthority_denoteConsistent : mrAuthority.denoteConsistent = true := by
  decide +kernel

/-- Unified MiniRust corpus side covering all 8 variants, including genuine
`basicMemory` vs. `treeBorrows` mode sensitivity on `dropTerminator.modeCase`! -/
def mrSide : Corpus.Side Ep2Mode Ep2MrMode Ep2Variant Ep2Case Unit Ep2ObsVal Ep2Rep where
  toAnneal := ep2MrToMode
  gate := fun _ _ _ => true
  verdictR := fun m v c _ => mrAuthority.verdict (ep2MrToMode m, v, c)
  rep := ep2Encode
  modes := allEp2MrModes
  modes_complete := allEp2MrModes_complete
  wMode := .basicMemory
  okProg := .dropTerminator
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .dropTerminator
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (.basicMemory, .treeBorrows, .dropTerminator, .modeCase, ())

/-- Kernel-checked full simulation + positive + fault + mode-sensitivity certificate
for MiniRust across ALL 64 `(mode, variant, case)` keys! -/
theorem mrSide_check : mrSide.check ep2Model = true := by
  decide +kernel

/-- Per-variant MiniRust side focusing the support gate strictly on variant `v`,
so each of the 8 MIR variants gets its own dedicated `DualCorrespondenceBundle`
with non-vacuous positive and fault witnesses! -/
def mrVariantSide (v : Ep2Variant) :
    Corpus.Side Ep2Mode Ep2MrMode Ep2Variant Ep2Case Unit Ep2ObsVal Ep2Rep where
  toAnneal := ep2MrToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := fun m p c _ => mrAuthority.verdict (ep2MrToMode m, p, c)
  rep := ep2Encode
  modes := allEp2MrModes
  modes_complete := allEp2MrModes_complete
  wMode := .basicMemory
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .dropTerminator => some (.basicMemory, .treeBorrows, .dropTerminator, .modeCase, ())
    | _ => none

/-- Kernel-checked per-variant MiniRust certificates for all 8 variants! -/
theorem mrVariantSide_check (v : Ep2Variant) : (mrVariantSide v).check ep2Model = true := by
  cases v <;> decide +kernel

/-! ## §5. Parameterized LeanMiri Side & Dual-Authority `DualCorrespondenceBundle` Builders -/

/-- Unified LeanMiri side parameterized over any `ObsAuthority Ep2Key Ep2ObsVal`
(closed in the cross-root kernel bridge over `LeanMiriSpec.DropBinderAndSubtypeLM.ep2LmObserve`). -/
def lmSideOf (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal) :
    Corpus.Side Ep2Mode Bool Ep2Variant Ep2Case Unit Ep2ObsVal Ep2Rep where
  toAnneal := ep2LmProtectedToMode
  gate := fun _ _ _ => true
  verdictR := fun b v c _ => lmAuth.verdict (ep2LmProtectedToMode b, v, c)
  rep := ep2Encode
  modes := allEp2LmModes
  modes_complete := allEp2LmModes_complete
  wMode := false
  okProg := .dropTerminator
  okQuery := .okPrimary
  okChoice := ()
  faultProg := .dropTerminator
  faultQuery := .ubFault
  faultChoice := ()
  flip := some (false, true, .dropTerminator, .modeCase, ())

/-- Boolean certificate predicate for closing the unified dual-authority bundle
against an arbitrary LeanMiri `ObsAuthority`. -/
def lmCheckOf (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal) : Bool :=
  (lmSideOf lmAuth).check ep2Model

/-- Extensional congruence for `lmCheckOf`: two LeanMiri `ObsAuthority` records
that produce identical verdicts on every key yield identical `lmCheckOf`
certificates (constructive, `[propext, Quot.sound]` only). -/
theorem lmCheckOf_congr (a1 a2 : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmCheckOf a1 = lmCheckOf a2 := by
  have hSide : lmSideOf a1 = lmSideOf a2 := by
    unfold lmSideOf
    congr 1
    funext b v c u
    exact h (ep2LmProtectedToMode b, v, c)
  unfold lmCheckOf
  rw [hSide]

/-- Per-variant LeanMiri side focusing the support gate strictly on variant `v`. -/
def lmVariantSideOf (v : Ep2Variant) (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal) :
    Corpus.Side Ep2Mode Bool Ep2Variant Ep2Case Unit Ep2ObsVal Ep2Rep where
  toAnneal := ep2LmProtectedToMode
  gate := fun _ p _ => decide (p = v)
  verdictR := fun b p c _ => lmAuth.verdict (ep2LmProtectedToMode b, p, c)
  rep := ep2Encode
  modes := allEp2LmModes
  modes_complete := allEp2LmModes_complete
  wMode := false
  okProg := v
  okQuery := .okPrimary
  okChoice := ()
  faultProg := v
  faultQuery := .ubFault
  faultChoice := ()
  flip := match v with
    | .dropTerminator => some (false, true, .dropTerminator, .modeCase, ())
    | _ => none

/-- Per-variant LeanMiri certificate predicate. -/
def lmVariantCheckOf (v : Ep2Variant) (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal) : Bool :=
  (lmVariantSideOf v lmAuth).check ep2Model

/-- Extensional congruence for `lmVariantCheckOf`. -/
theorem lmVariantCheckOf_congr (v : Ep2Variant) (a1 a2 : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (h : ∀ k, a1.verdict k = a2.verdict k) :
    lmVariantCheckOf v a1 = lmVariantCheckOf v a2 := by
  have hSide : lmVariantSideOf v a1 = lmVariantSideOf v a2 := by
    unfold lmVariantSideOf
    congr 1
    funext b p c u
    exact h (ep2LmProtectedToMode b, p, c)
  unfold lmVariantCheckOf
  rw [hSide]

/-- Unified `DualCorrespondenceBundle` over all 8 already-trusted Episode 2 MIR
variants, parameterized by a verified LeanMiri `ObsAuthority`. -/
def bundleWith (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (hLM : lmCheckOf lmAuth = true) :
    DualCorrespondenceBundle Ep2Mode Ep2Variant Ep2Case Ep2ObsVal Unit Ep2Rep
      Ep2MrMode Unit Ep2ObsVal Unit Bool Unit Ep2ObsVal Unit :=
  Corpus.bundle ep2Model mrSide (lmSideOf lmAuth) mrSide_check hLM

/-- Per-variant `DualCorrespondenceBundle` for each of the 8 Episode 2 MIR variants. -/
def variantBundleWith (v : Ep2Variant) (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (hLM : lmVariantCheckOf v lmAuth = true) :
    DualCorrespondenceBundle Ep2Mode Ep2Variant Ep2Case Ep2ObsVal Unit Ep2Rep
      Ep2MrMode Unit Ep2ObsVal Unit Bool Unit Ep2ObsVal Unit :=
  Corpus.bundle ep2Model (mrVariantSide v) (lmVariantSideOf v lmAuth)
    (mrVariantSide_check v) hLM

/-! ## §6. Lifted Dual-Authority Theorems & Flip-Direction / Mode-Sensitivity Witnesses -/

/-- Three-way normal agreement across Anneal (`Trusted`), MiniRust (`Mach`/`MachTB`),
and LeanMiri (`Miri.Interpreter`) at every gated key! -/
theorem threeWayNormalAgreement_with (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : Ep2MrMode) (mLM : Bool) (p : Ep2Variant) (q : Ep2Case)
    (hMode : ep2MrToMode mMR = ep2LmProtectedToMode mLM)
    (cMR cLM : Unit) (vMR vLM : Ep2ObsVal)
    (hRMR : (bundleWith lmAuth hLM).mrRel.ExecR mMR p q cMR (.normal vMR))
    (hRLM : (bundleWith lmAuth hLM).lmRel.ExecR mLM p q cLM (.normal vLM)) :
    ep2Encode vMR = ep2Encode vLM := by
  have hDet : ∀ out out', (bundleWith lmAuth hLM).ExecAnneal ((bundleWith lmAuth hLM).toAnnealMR mMR) p q out →
      (bundleWith lmAuth hLM).ExecAnneal ((bundleWith lmAuth hLM).toAnnealMR mMR) p q out' → out = out' := by
    rintro out out' ⟨⟨⟩, h1⟩ ⟨⟨⟩, h2⟩
    exact Option.some.inj (h1.symm.trans h2)
  exact ((bundleWith lmAuth hLM).threeWayNormalAgreement_rep hMode rfl rfl hDet hRMR hRLM).1

/-- Cross-authority fault equivalence between MiniRust and LeanMiri at every gated key! -/
theorem crossAuthorityFaultEquiv_with (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : Ep2MrMode) (mLM : Bool) (p : Ep2Variant) (q : Ep2Case)
    (hMode : ep2MrToMode mMR = ep2LmProtectedToMode mLM) (k : CorrFaultKind) :
    (∃ c, (bundleWith lmAuth hLM).mrRel.ExecR mMR p q c (.fault k)) ↔
    (∃ c, (bundleWith lmAuth hLM).lmRel.ExecR mLM p q c (.fault k)) :=
  (bundleWith lmAuth hLM).crossAuthorityFaultEquiv hMode rfl rfl k

/-- Exact behavioral equivalence on BOTH MiniRust and LeanMiri (reverse totality). -/
theorem exactBehaviorEq_both_with (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (hLM : lmCheckOf lmAuth = true)
    (mMR : Ep2MrMode) (mLM : Bool) (p : Ep2Variant) (q : Ep2Case) :
    ExactBehaviorEq (bundleWith lmAuth hLM).mrRel mMR p q ∧
    ExactBehaviorEq (bundleWith lmAuth hLM).lmRel mLM p q :=
  ⟨(bundleWith lmAuth hLM).mrSim.exactBehaviorEq_of_reverseTotal
      (mrSide.reverseTotal ep2Model (Bool.and_eq_true _ _ ▸ mrSide_check).1) rfl,
   (bundleWith lmAuth hLM).lmSim.exactBehaviorEq_of_reverseTotal
      ((lmSideOf lmAuth).reverseTotal ep2Model (Bool.and_eq_true _ _ ▸ hLM).1) rfl⟩

/-- Non-vacuous MiniRust `ModeSensitivityWitness` on `dropTerminator.modeCase`
(`BasicMemory` returns `42`, `TreeBorrowsMemory` faults with protector UB!). -/
theorem mr_modeSensitivity_present :
    (mrSide.flipW ep2Model mrSide_check).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Non-vacuous LeanMiri `ModeSensitivityWitness` on `dropTerminator.modeCase`
(`treeBorrows = false` returns `42`; `treeBorrows = true` faults with a vendored Tree
Borrows write conflict on the protected child of the dropped allocation's borrow tree). -/
theorem lm_modeSensitivity_present_with (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (hLM : lmCheckOf lmAuth = true) :
    ((lmSideOf lmAuth).flipW ep2Model hLM).isSome = true := by
  unfold Corpus.Side.flipW
  rfl

/-- Every per-variant bundle carries genuine `correspondenceClaim`, `faultEquivClaim`,
and non-vacuous flip-direction guards (`okAgree`, `faultA`, `faultR`) on BOTH
authorities (ruling out constant-outcome collapse for all 8 variants)! -/
theorem variant_bundle_claims_with (v : Ep2Variant) (lmAuth : Corpus.ObsAuthority Ep2Key Ep2ObsVal)
    (hLM : lmVariantCheckOf v lmAuth = true) :
    let B := variantBundleWith v lmAuth hLM
    CorrespondenceClaim B.mrRel ∧
    FaultEquivClaim B.mrRel ∧
    CorrespondenceClaim B.lmRel ∧
    FaultEquivClaim B.lmRel ∧
    B.mrFlip.m = .basicMemory ∧
    B.lmFlip.m = false ∧
    (∃ a r, B.mrRel.ExecA B.mrFlip.m B.mrFlip.pOk B.mrFlip.qOk B.mrFlip.cOk (.normal a) ∧
            B.mrRel.ExecR B.mrFlip.m B.mrFlip.pOk B.mrFlip.qOk B.mrFlip.cOk (.normal r) ∧
            B.mrRel.RetRel a r) ∧
    B.mrRel.ExecA B.mrFlip.m B.mrFlip.pFault B.mrFlip.qFault B.mrFlip.cFault (.fault B.mrFlip.kind) ∧
    B.mrRel.ExecR B.mrFlip.m B.mrFlip.pFault B.mrFlip.qFault B.mrFlip.cFault (.fault B.mrFlip.kind) ∧
    (∃ a r, B.lmRel.ExecA B.lmFlip.m B.lmFlip.pOk B.lmFlip.qOk B.lmFlip.cOk (.normal a) ∧
            B.lmRel.ExecR B.lmFlip.m B.lmFlip.pOk B.lmFlip.qOk B.lmFlip.cOk (.normal r) ∧
            B.lmRel.RetRel a r) ∧
    B.lmRel.ExecA B.lmFlip.m B.lmFlip.pFault B.lmFlip.qFault B.lmFlip.cFault (.fault B.lmFlip.kind) ∧
    B.lmRel.ExecR B.lmFlip.m B.lmFlip.pFault B.lmFlip.qFault B.lmFlip.cFault (.fault B.lmFlip.kind) :=
  ⟨(variantBundleWith v lmAuth hLM).mrSim.correspondenceClaim,
   (variantBundleWith v lmAuth hLM).mrSim.faultEquivClaim,
   (variantBundleWith v lmAuth hLM).lmSim.correspondenceClaim,
   (variantBundleWith v lmAuth hLM).lmSim.faultEquivClaim,
   rfl, rfl,
   (variantBundleWith v lmAuth hLM).mrFlip.okAgree,
   (variantBundleWith v lmAuth hLM).mrFlip.faultA,
   (variantBundleWith v lmAuth hLM).mrFlip.faultR,
   (variantBundleWith v lmAuth hLM).lmFlip.okAgree,
   (variantBundleWith v lmAuth hLM).lmFlip.faultA,
   (variantBundleWith v lmAuth hLM).lmFlip.faultR⟩

end Anneal.Mir.DropBinderAndSubtypeBundle
