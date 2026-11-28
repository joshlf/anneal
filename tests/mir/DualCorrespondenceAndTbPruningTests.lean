/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.DualCorrespondenceBundle
import Anneal.TreeBorrowsPruningAndFrameWp
import MiniRustSpec.Correspondence.WideSliceDst
import Lean

/-!
# Dual-correspondence bundles and Tree Borrows pruning: instantiation tests

Instantiates `Anneal.DualCorrespondenceBundle` over two dual-authority proof
families and exercises `Anneal.TreeBorrowsPruningAndFrameWp` on concrete and
symbolic witnesses.

* **A. Finite-corpus layer** (`Corpus`): a `DualCorrespondenceBundle` for a
  finite corpus of `(mode, program, query, choice)` keys, from one Boolean
  certificate per authority that the kernel evaluates. A reference authority
  is presented by the observations of its own interpreter (`ObsAuthority`).
* **B. Wide-slice and unsized DST pointer metadata** (`WideSlice`): the
  trusted `stepMirFn` against MiniRust (`BasicMemory` and
  `TreeBorrowsMemory`) and LeanMiri, with the safe-reference versus
  raw-pointer `isize::MAX` regime as mode.
* **C. IEEE-754 float casts** (`FloatCast`): trusted cast statements against
  MiniRust's translation gate and bit carriers and against the float engine
  of the vendored `Miri` interpreter, with the deterministic versus
  nondeterministic `nanChoices` selection as mode.
* **D. Laws** (`BundleLaws`): every remaining law of the bundle abstraction
  on the corpus codecs, outcomes, relations, and witnesses.
* **E, F. Tree Borrows pruning and frame-prep weakest preconditions**
  (`TbPruning`, `FrameWp`).
* **G. Cross-root kernel bridge**: the LeanMiri modules live in another
  package root and cannot be imported here. A trailing command imports both
  roots into a fresh kernel environment, replays the surface declarations it
  needs, builds the two authorities over the vendored `Miri` interpreter
  itself, and submits the resulting bundles and theorems to the kernel.
* **H. Audit**: constructive axiom closures and transitive reachability of
  every public theorem of both modules under test.
-/

namespace Anneal.DualCorrespondenceAndTbPruningTests

/-! ## A. Finite-corpus dual-authority layer

A reusable, authority-agnostic construction of `DualCorrespondenceBundle`s
over a finite corpus of `(mode, program, query, choice)` keys. Each reference
authority is presented by the observations of its own interpreter on the
corpus (`ObsAuthority`), so the same construction is instantiated both with
authorities available to this file and, inside the cross-root kernel bridge
at the end of the file, with authorities that live in another package root.
Every simulation and witness obligation is discharged from one Boolean
certificate (`Side.check`) evaluated by the kernel. -/

namespace Corpus

open Anneal.DualCorrespondenceBundle

/-- Authority-independent description of one complete execution. -/
inductive Verdict (V : Type) : Type where
  /-- Normal return with observable value `v`. -/
  | returns (v : V)
  /-- Undefined behavior. -/
  | undefinedBehavior
  /-- Fail-closed boundary of the model. -/
  | unsupported
  deriving DecidableEq

/-- The four-way outcome denoted by a verdict. -/
def Verdict.toOutcome {V : Type} : Verdict V → ExecOutcome4 V Unit
  | .returns v => .normal v
  | .undefinedBehavior => .fault .undefined
  | .unsupported => .fault .unsupported

/-- Outcome of an optional verdict; `none` is a missing (stuck) run. -/
def outcome? {V : Type} (v : Option (Verdict V)) :
    Option (ExecOutcome4 V Unit) :=
  v.map Verdict.toOutcome

/-- `Verdict.toOutcome` is injective. -/
theorem Verdict.toOutcome_injective {V : Type} {a b : Verdict V}
    (h : a.toOutcome = b.toOutcome) : a = b := by
  cases a <;> cases b <;> first | rfl | (cases h; rfl) | cases h

/-- `outcome?` is injective. -/
theorem outcome?_injective {V : Type} {a b : Option (Verdict V)}
    (h : outcome? a = outcome? b) : a = b := by
  cases a with
  | none => cases b with
    | none => rfl
    | some y => cases h
  | some x => cases b with
    | none => cases h
    | some y =>
      have h' : x.toOutcome = y.toOutcome := Option.some.inj h
      rw [Verdict.toOutcome_injective h']

/-- `true` exactly on normal returns. -/
def isReturn {V : Type} : Option (Verdict V) → Bool
  | some (.returns _) => true
  | _ => false

/-- `true` exactly on faults. -/
def isFaultV {V : Type} : Option (Verdict V) → Bool
  | some .undefinedBehavior => true
  | some .unsupported => true
  | _ => false

/-- Fault classification of a verdict (`undefined` unless `unsupported`). -/
def faultKindOf {V : Type} : Option (Verdict V) → CorrFaultKind
  | some .unsupported => .unsupported
  | _ => .undefined

/--
A reference authority presented through its own observations: `observe`
is the authority-typed observation of the authority's interpreter on each
corpus key (`none` outside the corpus), and `denote` lists the
authority-typed observation denoted by each verdict. Observations are
compared with the authority's own decidable equality, so no conversion out
of the authority's types is trusted, and the verdict of a key depends on
the key only through its observation.
-/
structure ObsAuthority (Key V : Type) : Type 1 where
  /-- Authority-typed observations. -/
  Obs : Type
  /-- Decidable equality of observations. -/
  decEq : DecidableEq Obs
  /-- Observation of the authority's run on each corpus key. -/
  observe : Key → Option Obs
  /-- Observation denoted by each verdict. -/
  denote : List (Verdict V × Obs)

namespace ObsAuthority

variable {Key V : Type}

/-- First verdict whose denotation is the observation `o`. -/
def decode (A : ObsAuthority Key V) (o : A.Obs) : Option (Verdict V) :=
  (A.denote.find? (fun d => @decide (d.2 = o) (A.decEq d.2 o))).map
    (fun d => d.1)

/-- Verdict of the authority's run on `k`. -/
def verdict (A : ObsAuthority Key V) (k : Key) : Option (Verdict V) :=
  (A.observe k).bind A.decode

/-- Two keys with the same observation have the same verdict: the
verdict is a function of the authority's own observation. -/
theorem verdict_eq_of_observe_eq (A : ObsAuthority Key V) {k k' : Key}
    (h : A.observe k = A.observe k') : A.verdict k = A.verdict k' := by
  unfold verdict
  rw [h]

/-- Boolean agreement of an authority with a verdict table on `keys`. -/
def matchesOn [DecidableEq V] (A : ObsAuthority Key V)
    (f : Key → Option (Verdict V)) (keys : List Key) : Bool :=
  keys.all (fun k => decide (A.verdict k = f k))

/-- `matchesOn` certifies pointwise equality with the table. -/
theorem matchesOn_sound [DecidableEq V]
    (A : ObsAuthority Key V) (f : Key → Option (Verdict V))
    (keys : List Key) (h : A.matchesOn f keys = true) :
    ∀ k, k ∈ keys → A.verdict k = f k := by
  intro k hk
  exact of_decide_eq_true (List.all_eq_true.mp h k hk)

/-- Boolean check that `A.denote` never assigns the same observation to two
distinct verdicts (non-shadowing / injectivity on observations). -/
def denoteConsistent [DecidableEq V] (A : ObsAuthority Key V) : Bool :=
  A.denote.all fun d₁ =>
    A.denote.all fun d₂ =>
      !(@decide (d₁.2 = d₂.2) (A.decEq d₁.2 d₂.2)) || decide (d₁.1 = d₂.1)

/-- If some element of `l` satisfies `p`, `l.find? p` returns an element of
`l` satisfying `p`. -/
theorem find?_of_mem_pred {α : Type} (p : α → Bool) :
    ∀ {l : List α} {x : α}, x ∈ l → p x = true →
      ∃ y, l.find? p = some y ∧ y ∈ l ∧ p y = true
  | [], _, h, _ => by cases h
  | a :: as, x, h, hp => by
    unfold List.find?
    cases ha : p a with
    | true => exact ⟨a, rfl, List.mem_cons_self .., ha⟩
    | false =>
      cases h with
      | head => rw [ha] at hp; cases hp
      | tail _ hmem =>
        obtain ⟨y, hy, hyl, hyp⟩ := find?_of_mem_pred p hmem hp
        exact ⟨y, hy, List.mem_cons_of_mem _ hyl, hyp⟩

/-- Consistency of `denote` certifies exact round-tripping: every `(v, o)`
in `A.denote` decodes back to `some v` with no shadowing by an earlier
entry. -/
theorem denoteConsistent_sound [DecidableEq V] (A : ObsAuthority Key V)
    (h : A.denoteConsistent = true) {v : Verdict V} {o : A.Obs}
    (hm : (v, o) ∈ A.denote) : A.decode o = some v := by
  let p : Verdict V × A.Obs → Bool :=
    fun d => @decide (d.2 = o) (A.decEq d.2 o)
  have hpo : p (v, o) = true :=
    @decide_eq_true (o = o) (A.decEq o o) rfl
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

/-- Pair the value of an interpreter step result with an observation of
its final state; an error keeps only the error. -/
def pairObs {S E A B : Type} (f : S → B) (r : S × Except E A) :
    Except E (A × B) :=
  r.2.map (fun a => (a, f r.1))

/-- The Anneal side of a corpus: evaluator, codec, and enumerations. -/
structure Model (ModeA Prog Query Choice VA Rep : Type) : Type where
  /-- Verdict of the Anneal model along each choice. -/
  evalA : ModeA → Prog → Query → Choice → Option (Verdict VA)
  /-- Codec from Anneal return values to the shared representation. -/
  codec : CodecLaws VA Rep
  /-- All programs. -/
  progs : List Prog
  /-- All queries. -/
  queries : List Query
  /-- All choices. -/
  choices : List Choice
  /-- `progs` is exhaustive. -/
  progs_complete : ∀ p, p ∈ progs
  /-- `queries` is exhaustive. -/
  queries_complete : ∀ q, q ∈ queries
  /-- `choices` is exhaustive. -/
  choices_complete : ∀ c, c ∈ choices

/-- One reference authority's side of a corpus. -/
structure Side (ModeA Mode Prog Query Choice VR Rep : Type) : Type where
  /-- Anneal mode matched with each authority mode. -/
  toAnneal : Mode → ModeA
  /-- Audited fragment of the authority. -/
  gate : Mode → Prog → Query → Bool
  /-- Verdict of the authority along each choice. -/
  verdictR : Mode → Prog → Query → Choice → Option (Verdict VR)
  /-- Shared representation of the authority's return values. -/
  rep : VR → Rep
  /-- All authority modes. -/
  modes : List Mode
  /-- `modes` is exhaustive. -/
  modes_complete : ∀ m, m ∈ modes
  /-- Mode shared by the positive and fault witnesses. -/
  wMode : Mode
  /-- Program of the positive witness. -/
  okProg : Prog
  /-- Query of the positive witness. -/
  okQuery : Query
  /-- Choice of the positive witness. -/
  okChoice : Choice
  /-- Program of the fault witness. -/
  faultProg : Prog
  /-- Query of the fault witness. -/
  faultQuery : Query
  /-- Choice of the fault witness. -/
  faultChoice : Choice
  /-- Optional mode flip `(m₁, m₂, p, q, c)`. -/
  flip : Option (Mode × Mode × Prog × Query × Choice)

/-- Boolean coupling of two verdicts through the codec. -/
def couplesB {VA VR Rep : Type} [DecidableEq Rep] (enc : VA → Rep)
    (rep : VR → Rep) : Option (Verdict VA) → Option (Verdict VR) → Bool
  | some (.returns a), some (.returns r) => decide (rep r = enc a)
  | some .undefinedBehavior, some .undefinedBehavior => true
  | some .unsupported, some .unsupported => true
  | _, _ => false

section Coupling

variable {VA VR Rep : Type} [DecidableEq Rep] {enc : VA → Rep}
  {rep : VR → Rep}

/-- Coupled verdicts denote coupled outcomes. -/
theorem couplesB_sound {va : Option (Verdict VA)} {vr : Option (Verdict VR)}
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
      cases a with
      | returns a =>
        cases r with
        | returns r =>
          exact ⟨_, _, rfl, rfl,
            ChoiceCoupledOutcomeRel.ofNormal (of_decide_eq_true h)⟩
        | undefinedBehavior => cases h
        | unsupported => cases h
      | undefinedBehavior =>
        cases r with
        | returns r => cases h
        | undefinedBehavior =>
          exact ⟨_, _, rfl, rfl, ChoiceCoupledOutcomeRel.ofFault _⟩
        | unsupported => cases h
      | unsupported =>
        cases r with
        | returns r => cases h
        | undefinedBehavior => cases h
        | unsupported =>
          exact ⟨_, _, rfl, rfl, ChoiceCoupledOutcomeRel.ofFault _⟩

/-- A coupled normal Anneal return has a coupled normal reference return. -/
theorem couplesB_returns {a : VA} {vr : Option (Verdict VR)}
    (h : couplesB enc rep (some (.returns a)) vr = true) :
    ∃ r, vr = some (.returns r) ∧ rep r = enc a := by
  cases vr with
  | none => cases h
  | some r =>
    cases r with
    | returns r => exact ⟨r, rfl, of_decide_eq_true h⟩
    | undefinedBehavior => cases h
    | unsupported => cases h

/-- A coupled faulting Anneal verdict has the same reference verdict. -/
theorem couplesB_fault {va : Option (Verdict VA)}
    {vr : Option (Verdict VR)} (h : couplesB enc rep va vr = true)
    (hf : isFaultV va = true) :
    outcome? va = some (.fault (faultKindOf va)) ∧
      outcome? vr = some (.fault (faultKindOf va)) := by
  cases va with
  | none => cases hf
  | some a =>
    cases a with
    | returns a => cases hf
    | undefinedBehavior =>
      cases vr with
      | none => cases h
      | some r => cases r <;> first | exact ⟨rfl, rfl⟩ | cases h
    | unsupported =>
      cases vr with
      | none => cases h
      | some r => cases r <;> first | exact ⟨rfl, rfl⟩ | cases h

end Coupling

namespace Side

variable {ModeA Mode Prog Query Choice VA VR Rep : Type}

/-- Step relation of the Anneal model against one authority. -/
def rel (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) :
    ModeParamStepRel Mode Prog Query Choice VA VR Unit Unit where
  SupportGate := fun m p q => S.gate m p q = true
  ExecA := fun m p q c out =>
    outcome? (M.evalA (S.toAnneal m) p q c) = some out
  ExecR := fun m p q c out => outcome? (S.verdictR m p q c) = some out
  RetRel := fun a r => S.rep r = M.codec.encode a
  UnwRel := fun _ _ => True

/-- An Anneal verdict is an Anneal execution of the step relation. -/
theorem execA_of_verdict (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) {m : Mode} {p : Prog}
    {q : Query} {c : Choice} {v : Verdict VA}
    (h : M.evalA (S.toAnneal m) p q c = some v) :
    (S.rel M).ExecA m p q c v.toOutcome := by
  show outcome? (M.evalA (S.toAnneal m) p q c) = some v.toOutcome
  rw [h]; rfl

/-- A reference verdict is a reference execution of the step relation. -/
theorem execR_of_verdict (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) {m : Mode} {p : Prog}
    {q : Query} {c : Choice} {v : Verdict VR}
    (h : S.verdictR m p q c = some v) :
    (S.rel M).ExecR m p q c v.toOutcome := by
  show outcome? (S.verdictR m p q c) = some v.toOutcome
  rw [h]; rfl

/-- A reference execution determines the reference verdict. -/
theorem verdict_of_execR (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) {m : Mode} {p : Prog}
    {q : Query} {c : Choice} {v : Verdict VR}
    (h : (S.rel M).ExecR m p q c v.toOutcome) :
    S.verdictR m p q c = some v :=
  outcome?_injective (a := S.verdictR m p q c) (b := some v) h

/-- Simulation certificate: every gated key has coupled verdicts. -/
def simCheck [DecidableEq Rep] (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) : Bool :=
  S.modes.all fun m => M.progs.all fun p => M.queries.all fun q =>
    M.choices.all fun c =>
      !S.gate m p q ||
        couplesB M.codec.encode S.rep (M.evalA (S.toAnneal m) p q c)
          (S.verdictR m p q c)

/-- Witness certificate: the designated witnesses are genuine. -/
def witCheck [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) : Bool :=
  S.gate S.wMode S.okProg S.okQuery &&
  isReturn (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery S.okChoice) &&
  M.choices.all (fun c =>
    !isFaultV (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery c)) &&
  S.gate S.wMode S.faultProg S.faultQuery &&
  isFaultV
    (M.evalA (S.toAnneal S.wMode) S.faultProg S.faultQuery S.faultChoice) &&
  (match S.flip with
   | none => true
   | some (m₁, m₂, p, q, c) =>
     S.gate m₁ p q && S.gate m₂ p q &&
     (M.evalA (S.toAnneal m₁) p q c).isSome &&
     M.choices.all (fun c' => decide
       (M.evalA (S.toAnneal m₂) p q c' ≠ M.evalA (S.toAnneal m₁) p q c)) &&
     M.choices.all (fun c' => decide
       (S.verdictR m₂ p q c' ≠ S.verdictR m₁ p q c)))

/-- Full certificate of one side. -/
def check [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (M : Model ModeA Prog Query Choice VA Rep)
    (S : Side ModeA Mode Prog Query Choice VR Rep) : Bool :=
  S.simCheck M && S.witCheck M

section Laws

variable (M : Model ModeA Prog Query Choice VA Rep)
variable (S : Side ModeA Mode Prog Query Choice VR Rep)

/-- `simCheck` certifies coupling at every gated key. -/
theorem simCheck_spec [DecidableEq Rep] (h : S.simCheck M = true)
    (m : Mode) (p : Prog) (q : Query) (c : Choice)
    (hg : S.gate m p q = true) :
    couplesB M.codec.encode S.rep (M.evalA (S.toAnneal m) p q c)
      (S.verdictR m p q c) = true := by
  have h₁ := List.all_eq_true.mp h m (S.modes_complete m)
  have h₂ := List.all_eq_true.mp h₁ p (M.progs_complete p)
  have h₃ := List.all_eq_true.mp h₂ q (M.queries_complete q)
  have h₄ := List.all_eq_true.mp h₃ c (M.choices_complete c)
  rw [hg] at h₄
  exact h₄

/-- Forward totality from the certificate. -/
theorem forward [DecidableEq Rep] (h : S.simCheck M = true) :
    (S.rel M).ForwardTotal := by
  intro m p q c outR hg hR
  obtain ⟨oa, orr, ha, hr, hc⟩ :=
    couplesB_sound (S.simCheck_spec M h m p q c hg)
  have hR' : outcome? (S.verdictR m p q c) = some outR := hR
  rw [hr] at hR'
  cases hR'
  exact ⟨oa, ha, hc⟩

/-- Reverse totality from the certificate. -/
theorem reverseTotal [DecidableEq Rep] (h : S.simCheck M = true) :
    (S.rel M).ReverseTotal := by
  intro m p q c outA hg hA
  obtain ⟨oa, orr, ha, hr, hc⟩ :=
    couplesB_sound (S.simCheck_spec M h m p q c hg)
  have hA' : outcome? (M.evalA (S.toAnneal m) p q c) = some outA := hA
  rw [ha] at hA'
  cases hA'
  exact ⟨orr, hr, hc⟩

/-- Reverse totality on faults from the certificate. -/
theorem reverseFault [DecidableEq Rep] (h : S.simCheck M = true) :
    (S.rel M).ReverseFaultTotal := by
  intro m p q c k hg hA
  obtain ⟨outR, hR, hc⟩ := S.reverseTotal M h m p q c (.fault k) hg hA
  have hk : outR = .fault k := (hc.fault_iff k).mp rfl
  rw [hk] at hR
  exact hR

/-- Two-sided productivity from the certificate. -/
theorem productiveBoth [DecidableEq Rep] (h : S.simCheck M = true)
    (c₀ : Choice) : (S.rel M).ProductiveBoth := by
  constructor
  · intro m p q hg
    obtain ⟨oa, _, ha, _, _⟩ :=
      couplesB_sound (S.simCheck_spec M h m p q c₀ hg)
    exact ⟨c₀, oa, ha⟩
  · intro m p q hg
    obtain ⟨_, orr, _, hr, _⟩ :=
      couplesB_sound (S.simCheck_spec M h m p q c₀ hg)
    exact ⟨c₀, orr, hr⟩

/-- Components of the witness certificate. -/
theorem witCheck_parts [DecidableEq VA] [DecidableEq VR]
    (h : S.witCheck M = true) :
    S.gate S.wMode S.okProg S.okQuery = true ∧
    isReturn (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery S.okChoice) =
      true ∧
    (M.choices.all (fun c =>
      !isFaultV (M.evalA (S.toAnneal S.wMode) S.okProg S.okQuery c))) =
      true ∧
    S.gate S.wMode S.faultProg S.faultQuery = true ∧
    isFaultV (M.evalA (S.toAnneal S.wMode) S.faultProg S.faultQuery
      S.faultChoice) = true := by
  unfold witCheck at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2⟩

/-- Positive witness at an arbitrary key, from Boolean facts about it. -/
def positiveAt [DecidableEq Rep] (hs : S.simCheck M = true) (m : Mode)
    (p : Prog) (q : Query) (c : Choice) (hg : S.gate m p q = true)
    (hr : isReturn (M.evalA (S.toAnneal m) p q c) = true)
    (hwf : (M.choices.all (fun c' =>
      !isFaultV (M.evalA (S.toAnneal m) p q c'))) = true) :
    PositiveWitness (S.rel M) where
  m := m
  p := p
  q := q
  c := c
  gate := hg
  wf := fun c' k hk => by
    have hc := List.all_eq_true.mp hwf c' (M.choices_complete c')
    have hk' : outcome? (M.evalA (S.toAnneal m) p q c') = some (.fault k) :=
      hk
    cases hv : M.evalA (S.toAnneal m) p q c' with
    | none => rw [hv] at hk'; cases hk'
    | some v =>
      rw [hv] at hk' hc
      cases v with
      | returns a => cases hk'
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
        · show outcome? (M.evalA (S.toAnneal m) p q c) = some (.normal a)
          rw [hv]; rfl
        · show outcome? (S.verdictR m p q c) = some (.normal r)
          rw [hvr]; rfl
      | undefinedBehavior => cases hr
      | unsupported => cases hr

/-- Fault-equivalence witness at an arbitrary key, from Boolean facts. -/
def faultAt [DecidableEq Rep] (hs : S.simCheck M = true) (m : Mode)
    (p : Prog) (q : Query) (c : Choice) (hg : S.gate m p q = true)
    (hf : isFaultV (M.evalA (S.toAnneal m) p q c) = true) :
    FaultEquivWitness (S.rel M) where
  m := m
  p := p
  q := q
  c := c
  kind := faultKindOf (M.evalA (S.toAnneal m) p q c)
  gate := hg
  execA := (couplesB_fault (S.simCheck_spec M hs m p q c hg) hf).1
  execR := (couplesB_fault (S.simCheck_spec M hs m p q c hg) hf).2

/-- The positive witness designated by the side. -/
def positive [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (h : S.check M = true) : PositiveWitness (S.rel M) :=
  have hs : S.simCheck M = true := (Bool.and_eq_true _ _ ▸ h).1
  have hw := S.witCheck_parts M (Bool.and_eq_true _ _ ▸ h).2
  S.positiveAt M hs S.wMode S.okProg S.okQuery S.okChoice hw.1 hw.2.1
    hw.2.2.1

/-- The fault-equivalence witness designated by the side. -/
def faultW [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (h : S.check M = true) : FaultEquivWitness (S.rel M) :=
  have hs : S.simCheck M = true := (Bool.and_eq_true _ _ ▸ h).1
  have hw := S.witCheck_parts M (Bool.and_eq_true _ _ ▸ h).2
  S.faultAt M hs S.wMode S.faultProg S.faultQuery S.faultChoice hw.2.2.2.1
    hw.2.2.2.2

/-- The mode-sensitivity witness designated by the side, if any. -/
def flipW [DecidableEq Rep] [DecidableEq VA] [DecidableEq VR]
    (h : S.check M = true) :
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
          (M.evalA (S.toAnneal m₂) p q c' ≠
            M.evalA (S.toAnneal m₁) p q c))) = true ∧
        (M.choices.all (fun c' => decide
          (S.verdictR m₂ p q c' ≠ S.verdictR m₁ p q c))) = true := by
      unfold witCheck at hw
      rw [hfl] at hw
      simp only [Bool.and_eq_true] at hw
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
          obtain ⟨oa, orr, ha, hr, hc⟩ :=
            couplesB_sound (S.simCheck_spec M hs m₁ p q c hparts.1)
          refine ⟨oa, orr, ha, hr, hc, ?_, ?_⟩
          · intro c' hA
            have hA' : outcome? (M.evalA (S.toAnneal m₂) p q c') = some oa :=
              hA
            rw [← ha] at hA'
            exact of_decide_eq_true
              (List.all_eq_true.mp hparts.2.2.2.1 c'
                (M.choices_complete c')) (outcome?_injective hA')
          · intro c' hR
            have hR' : outcome? (S.verdictR m₂ p q c') = some orr := hR
            rw [← hr] at hR'
            exact of_decide_eq_true
              (List.all_eq_true.mp hparts.2.2.2.2 c'
                (M.choices_complete c')) (outcome?_injective hR') }

end Laws

end Side

/--
Dual-authority bundle of a finite corpus: both simulations, all witnesses,
and reverse totality follow from the two Boolean certificates.
-/
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

/-! ### A.2 Shared carrier codec: a machine word as two 32-bit halves -/

namespace Corpus

open Anneal.DualCorrespondenceBundle

/-- High and low 32-bit halves of a natural number. -/
def halves (n : Nat) : Nat × Nat := (n / 4294967296, n % 4294967296)

/-- Codec from `usize` observables to `(high, low)` halves, with the
permissive validity predicate (every pair is declared valid). -/
def looseHalvesCodec : CodecLaws Nat (Nat × Nat) where
  encode := halves
  decode := fun p =>
    if p.2 < 4294967296 then some (p.1 * 4294967296 + p.2) else none
  decode_encode := fun n => by
    have hlt : n % 4294967296 < 4294967296 := Nat.mod_lt n (by decide)
    show (if n % 4294967296 < 4294967296 then
      some (n / 4294967296 * 4294967296 + n % 4294967296) else none) = some n
    simp only [hlt, ↓reduceIte]
    congr 1
    omega
  encode_valid := fun _ => True.intro
  encode_decode_of_valid := fun p a _ hd => by
    cases p with
    | mk hi lo =>
      by_cases hlo : lo < 4294967296
      · have hd' : (if lo < 4294967296 then some (hi * 4294967296 + lo)
            else none) = some a := hd
        simp only [hlo, ↓reduceIte] at hd'
        have ha : hi * 4294967296 + lo = a := Option.some.inj hd'
        show (a / 4294967296, a % 4294967296) = (hi, lo)
        rw [← ha]
        congr 1 <;> omega
      · have hd' : (if lo < 4294967296 then some (hi * 4294967296 + lo)
            else none) = some a := hd
        simp only [hlo, ↓reduceIte] at hd'
        cases hd'

/-- The canonical codec: `looseHalvesCodec` with tight validity. -/
def halvesCodec : CodecLaws Nat (Nat × Nat) := looseHalvesCodec.tighten


end Corpus

/-! ### A.3 Deterministic-evaluator bundles (`fromDetEquiv`) -/

namespace Corpus

open Anneal.DualCorrespondenceBundle

/-- Total outcome of an optional verdict: a key without a run fails
closed. Inside a certified gate every key has a run. -/
def totalOutcome {V : Type} : Option (Verdict V) → ExecOutcome4 V Unit
  | some v => v.toOutcome
  | none => .fault .unsupported

/-- On a key with a run, `totalOutcome` is that run's outcome. -/
theorem totalOutcome_eq {V : Type} {v : Option (Verdict V)}
    {o : ExecOutcome4 V Unit} (h : outcome? v = some o) :
    totalOutcome v = o := by
  cases v with
  | none => cases h
  | some v => exact Option.some.inj h

namespace Side

variable {ModeA Mode Prog Query Choice VA VR Rep : Type}
variable (M : Model ModeA Prog Query Choice VA Rep)
variable (S : Side ModeA Mode Prog Query Choice VR Rep)

/-- Deterministic step relation of a side: the Anneal evaluator read along
the fixed choice `c₀` against the authority's total evaluator. -/
abbrev detRel (c₀ : Choice) :
    ModeParamStepRel Mode Prog Query Choice VA VR Unit Unit :=
  ModeParamStepRel.ofAnnealEval S.toAnneal
    (fun m p q => S.gate m p q = true)
    (fun mA p q => totalOutcome (M.evalA mA p q c₀))
    (fun m p q c out => totalOutcome (S.verdictR m p q c) = out)
    (fun a r => S.rep r = M.codec.encode a) (fun _ _ => True)

/-- The total evaluators are coupled on every gated key. -/
theorem detCoupled [DecidableEq Rep] (c₀ : Choice)
    (hs : S.simCheck M = true)
    (hconst : ∀ mA p q c, M.evalA mA p q c = M.evalA mA p q c₀) (m : Mode)
    (p : Prog) (q : Query) (c : Choice) (hg : S.gate m p q = true) :
    ChoiceCoupledOutcomeRel (fun a r => S.rep r = M.codec.encode a)
      (fun (_ : Unit) (_ : Unit) => True)
      (totalOutcome (M.evalA (S.toAnneal m) p q c₀))
      (totalOutcome (S.verdictR m p q c)) := by
  obtain ⟨oa, orr, ha, hr, hc⟩ :=
    couplesB_sound (S.simCheck_spec M hs m p q c hg)
  rw [hconst] at ha
  rw [totalOutcome_eq ha, totalOutcome_eq hr]
  exact hc

/-- A positive witness of the relational side is one of the deterministic
side. -/
def detPositive (c₀ : Choice) (w : PositiveWitness (S.rel M))
    (hconst : ∀ mA p q c, M.evalA mA p q c = M.evalA mA p q c₀) :
    PositiveWitness (S.detRel M c₀) where
  m := w.m
  p := w.p
  q := w.q
  c := w.c
  gate := w.gate
  wf := fun _ k hk => by
    obtain ⟨a, r, hA, _, _⟩ := w.agree
    have hA' : outcome? (M.evalA (S.toAnneal w.m) w.p w.q w.c) =
        some (.normal a) := hA
    rw [hconst] at hA'
    have hk' : totalOutcome (M.evalA (S.toAnneal w.m) w.p w.q c₀) =
        .fault k := hk
    rw [totalOutcome_eq hA'] at hk'
    cases hk'
  agree := by
    obtain ⟨a, r, hA, hR, hrel⟩ := w.agree
    have hA' : outcome? (M.evalA (S.toAnneal w.m) w.p w.q w.c) =
        some (.normal a) := hA
    rw [hconst] at hA'
    exact ⟨a, r, totalOutcome_eq hA', totalOutcome_eq hR, hrel⟩

/-- A fault witness of the relational side is one of the deterministic
side. -/
def detFault (c₀ : Choice) (w : FaultEquivWitness (S.rel M))
    (hconst : ∀ mA p q c, M.evalA mA p q c = M.evalA mA p q c₀) :
    FaultEquivWitness (S.detRel M c₀) where
  m := w.m
  p := w.p
  q := w.q
  c := w.c
  kind := w.kind
  gate := w.gate
  execA := by
    have hA : outcome? (M.evalA (S.toAnneal w.m) w.p w.q w.c) =
        some (.fault w.kind) := w.execA
    rw [hconst] at hA
    exact totalOutcome_eq hA
  execR := totalOutcome_eq w.execR

end Side

/-- Dual-authority bundle of a corpus whose Anneal evaluator does not
depend on the choice, built with `fromDetEquiv` from total deterministic
evaluators. -/
def detBundle {ModeA Prog Query Choice VA Rep ModeMR VMR ModeLM VLM : Type}
    [DecidableEq Rep] [DecidableEq VA] [DecidableEq VMR] [DecidableEq VLM]
    (M : Model ModeA Prog Query Choice VA Rep)
    (SMR : Side ModeA ModeMR Prog Query Choice VMR Rep)
    (SLM : Side ModeA ModeLM Prog Query Choice VLM Rep) (c₀ : Choice)
    (hconst : ∀ mA p q c, M.evalA mA p q c = M.evalA mA p q c₀)
    (hMR : SMR.check M = true) (hLM : SLM.check M = true) :
    DualCorrespondenceBundle ModeA Prog Query VA Unit Rep ModeMR Choice VMR
      Unit ModeLM Choice VLM Unit :=
  DualCorrespondenceBundle.fromDetEquiv M.codec SMR.rep SLM.rep
    (fun mA p q => totalOutcome (M.evalA mA p q c₀)) SMR.toAnneal
    SLM.toAnneal (fun m p q => SMR.gate m p q = true)
    (fun m p q => SLM.gate m p q = true)
    (fun m p q c => totalOutcome (SMR.verdictR m p q c))
    (fun m p q c => totalOutcome (SLM.verdictR m p q c))
    (fun a r => SMR.rep r = M.codec.encode a) (fun _ _ => True)
    (fun a r => SLM.rep r = M.codec.encode a) (fun _ _ => True)
    (fun _ _ h => h) (fun _ _ h => h)
    (SMR.detCoupled M c₀ (Bool.and_eq_true _ _ ▸ hMR).1 hconst)
    (SLM.detCoupled M c₀ (Bool.and_eq_true _ _ ▸ hLM).1 hconst)
    (SMR.detPositive M c₀ (SMR.positive M hMR) hconst)
    (SLM.detPositive M c₀ (SLM.positive M hLM) hconst)
    (SMR.detFault M c₀ (SMR.faultW M hMR) hconst)
    (SLM.detFault M c₀ (SLM.faultW M hLM) hconst) rfl rfl

/-- Every `detBundle` is productive on both sides of both authorities
(`fromDetEquiv_productiveBoth`). -/
theorem detBundle_productiveBoth
    {ModeA Prog Query Choice VA Rep ModeMR VMR ModeLM VLM : Type}
    [DecidableEq Rep] [DecidableEq VA] [DecidableEq VMR] [DecidableEq VLM]
    (M : Model ModeA Prog Query Choice VA Rep)
    (SMR : Side ModeA ModeMR Prog Query Choice VMR Rep)
    (SLM : Side ModeA ModeLM Prog Query Choice VLM Rep) (c₀ : Choice)
    (hconst : ∀ mA p q c, M.evalA mA p q c = M.evalA mA p q c₀)
    (hMR : SMR.check M = true) (hLM : SLM.check M = true) :
    (detBundle M SMR SLM c₀ hconst hMR hLM).mrRel.ProductiveBoth ∧
      (detBundle M SMR SLM c₀ hconst hMR hLM).lmRel.ProductiveBoth :=
  DualCorrespondenceBundle.fromDetEquiv_productiveBoth M.codec SMR.rep
    SLM.rep (fun mA p q => totalOutcome (M.evalA mA p q c₀)) SMR.toAnneal
    SLM.toAnneal (fun m p q => SMR.gate m p q = true)
    (fun m p q => SLM.gate m p q = true)
    (fun m p q c => totalOutcome (SMR.verdictR m p q c))
    (fun m p q c => totalOutcome (SLM.verdictR m p q c))
    (fun a r => SMR.rep r = M.codec.encode a) (fun _ _ => True)
    (fun a r => SLM.rep r = M.codec.encode a) (fun _ _ => True)
    (fun _ _ h => h) (fun _ _ h => h)
    (SMR.detCoupled M c₀ (Bool.and_eq_true _ _ ▸ hMR).1 hconst)
    (SLM.detCoupled M c₀ (Bool.and_eq_true _ _ ▸ hLM).1 hconst)
    (SMR.detPositive M c₀ (SMR.positive M hMR) hconst)
    (SLM.detPositive M c₀ (SLM.positive M hLM) hconst)
    (SMR.detFault M c₀ (SMR.faultW M hMR) hconst)
    (SLM.detFault M c₀ (SLM.faultW M hLM) hconst) rfl rfl

end Corpus

/-! ## B. Family 1: wide-slice and unsized DST pointer metadata

One Anneal model (the trusted `stepMirFn`) is related to MiniRust
(`MiniRustSpec.Correspondence.WideSliceDst`, over `BasicMemory` and
`TreeBorrowsMemory`) and to LeanMiri. The LeanMiri side of the surface
bundle is the reference table `lmReference`; the cross-root kernel bridge
at the end of the file rebuilds the same bundle over the vendored `Miri`
interpreter itself and proves that interpreter equal to the table. -/

namespace WideSlice

open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Anneal.DualCorrespondenceBundle
open Corpus

/-! ### B.1 Corpus: modes, programs, and queries -/

/-- Pointer-validity regime of a reborrow: raw pointers carry no validity
obligation, safe references must be dereferenceable and at most
`isize::MAX` bytes. -/
inductive Regime : Type where
  /-- Raw pointer (`&raw const (*p)`). -/
  | raw
  /-- Safe shared reference (`&(*p)`). -/
  | safe
  deriving DecidableEq

/-- MiniRust memory model. -/
inductive MrMem : Type where
  /-- `BasicMemory`. -/
  | basic
  /-- `TreeBorrowsMemory`. -/
  | treeBorrows
  deriving DecidableEq

/-- Corpus programs. The first five are single statements over the frame
`_1 : [u32; 4] = [10, 20, 30, 40]`, `_2 : *mut [u32]` (a wide pointer to
`_1` with the query's length), `_3 : usize` (the query's index). -/
inductive Prog : Type where
  /-- `_0 = PtrMetadata(copy _2)` (`ptr::metadata`). -/
  | metadata
  /-- `_0 = Len(*_2)`. -/
  | placeLen
  /-- `_0 = copy (*_2)[_3]`. -/
  | indexRead
  /-- `_0 = &raw const (*_2)` or `_0 = &(*_2)`, by regime. -/
  | reborrow
  /-- `_0 = size_of_val::<[u32]>(copy _1)` on a raw wide pointer. -/
  | sizeOfVal
  /-- `from_raw_parts` / `to_raw_parts` / `ptr::metadata` round trip. -/
  | roundTrip
  /-- Out-of-bounds indexing `(*p)[4]` through a wide pointer. -/
  | indexOob
  /-- Read through a wide reference disabled by a parent write. -/
  | disabledDeref
  /-- Non-dereferencing `ptr::metadata` on a disabled wide pointer. -/
  | disabledMetadata
  /-- LeanMiri multi-step `from_raw_parts` / `ptr::metadata` / `to_raw_parts`
  / `size_of_val` pipeline (`CastKind.ptrToPtr` + `AggregateKind.rawPtr`). -/
  | pipeline
  deriving DecidableEq

/-- Corpus queries: the wide pointer's length and the index operand. -/
inductive Query : Type where
  /-- `len = 3`, `idx = 1`. -/
  | inBounds
  /-- `len = 3`, `idx = 4`. -/
  | oobIndex
  /-- `len = 5` over a four-element array, `idx = 1`. -/
  | oobLen
  /-- `len = 2^61`: the `[u32]` byte size `2^63` exceeds `isize::MAX`. -/
  | tooBig
  deriving DecidableEq

/-- Length metadata of a query. -/
def Query.len : Query → Nat
  | .inBounds => 3
  | .oobIndex => 3
  | .oobLen => 5
  | .tooBig => 2 ^ 61

/-- Index operand of a query. -/
def Query.idx : Query → Nat
  | .oobIndex => 4
  | _ => 1

/-- All regimes. -/
def allRegimes : List Regime := [.raw, .safe]

/-- All MiniRust modes (memory model and regime). -/
def allMrModes : List (MrMem × Regime) :=
  [(.basic, .raw), (.basic, .safe), (.treeBorrows, .raw),
    (.treeBorrows, .safe)]

/-- All programs. -/
def allProgs : List Prog :=
  [.metadata, .placeLen, .indexRead, .reborrow, .sizeOfVal, .roundTrip,
    .indexOob, .disabledDeref, .disabledMetadata, .pipeline]

/-- All queries. -/
def allQueries : List Query := [.inBounds, .oobIndex, .oobLen, .tooBig]

/-! ### B.2 Anneal: the trusted machine on the corpus -/

/-- `usize`. -/
def usizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }

/-- `u32`. -/
def u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }

/-- `[u32; 4]`. -/
def arrU32x4Ty : Ty := { kind := .array (.uint .u32) 4, layoutIdx := 0 }

/-- `*mut [u32]`. -/
def rawMutSliceU32Ty : Ty :=
  { kind := .rawPtr .mut (.slice (.uint .u32)), layoutIdx := 0 }

/-- `*const [u32]`. -/
def rawSliceU32Ty : Ty :=
  { kind := .rawPtr .not (.slice (.uint .u32)), layoutIdx := 0 }

/-- `&[u32]`. -/
def sharedRefSliceU32Ty : Ty :=
  { kind := .ref .not (.slice (.uint .u32)), layoutIdx := 0 }

/-- `[u32]`. -/
def sliceU32PointeeTy : Ty := { kind := .slice (.uint .u32), layoutIdx := 0 }

/-- Primitive layout of `bytes` bytes. -/
def primLayout (bytes : Nat) : TypeLayout :=
  { size := { bytes := bytes }
    align := { bytes := bytes }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Function ABI returning a `bytes`-byte primitive. -/
def fnAbiOf (bytes : Nat) : FnAbi :=
  { args := []
    ret := { layout := primLayout bytes, mode := .direct }
    conv := .rust
    canUnwind := false }

/-- Single-statement body `_0 = rv` over the four-local frame. -/
def frameBody (name : String) (retTy : Ty) (abi : FnAbi) (rv : Rvalue) :
    CapturedMir :=
  { defPath := name
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := retTy, debugName := none }
      , { mutability := .mut, ty := arrU32x4Ty, debugName := none }
      , { mutability := .mut, ty := rawMutSliceU32Ty, debugName := none }
      , { mutability := .not, ty := usizeTy, debugName := none } ]
    basicBlocks :=
      [ { statements := [ ⟨.assign ⟨0, []⟩ rv, "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := abi
    layouts := emptyLayoutTable
    allocations := [] }

/-- `_0 = PtrMetadata(copy _2)`. -/
def metadataBody : CapturedMir :=
  frameBody "wide_slice_single_metadata" usizeTy (fnAbiOf 8)
    (.unaryOp .ptrMetadata (.copy ⟨2, []⟩))

/-- `_0 = Len(*_2)`. -/
def placeLenBody : CapturedMir :=
  frameBody "wide_slice_single_len" usizeTy (fnAbiOf 8) (.len ⟨2, [.deref]⟩)

/-- `_0 = copy (*_2)[_3]`. -/
def indexReadBody : CapturedMir :=
  frameBody "wide_slice_single_index_read" u32Ty (fnAbiOf 4)
    (.use (.copy ⟨2, [.deref, .index 3]⟩))

/-- Reborrow rvalue of a regime. -/
def reborrowRvalue : Regime → Rvalue
  | .raw => .rawPtr .not ⟨2, [.deref]⟩
  | .safe => .ref .shared ⟨2, [.deref]⟩

/-- Type of the reborrowed pointer in a regime. -/
def reborrowTy : Regime → Ty
  | .raw => rawSliceU32Ty
  | .safe => sharedRefSliceU32Ty

/-- Reborrow of `*_2` in the given regime. -/
def reborrowBody (r : Regime) : CapturedMir :=
  frameBody "wide_slice_reborrow" (reborrowTy r) (fnAbiOf 8)
    (reborrowRvalue r)

/-- The array value `[10, 20, 30, 40]`. -/
def arrVal : Value :=
  .aggregate 0 [.scalar ⟨10, 4⟩, .scalar ⟨20, 4⟩, .scalar ⟨30, 4⟩,
    .scalar ⟨40, 4⟩]

/-- Memory with one active borrow (tag `1`) of local `_1`. -/
def arrMemory : Memory :=
  { emptyMemory with
    borrows :=
      [ { tag := 1, targetLocal := 1, targetProjection := [],
          perm := .active, allocDead := false } ]
    nextTag := 2 }

/-- Wide pointer to `_1` with length `len`. -/
def wideVal (len : Nat) : Value :=
  .aggregate 0 [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨len, 8⟩]

/-- Initial state of the four-local frame. -/
def frameInit (len idx : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals :=
          [ .uninit, .init arrVal, .init (wideVal len),
            .init (.scalar ⟨idx, 8⟩) ] }
    memory := arrMemory }

/-- `_0 = size_of_val::<[u32]>(copy _1)` with `_1 : *const [u32]`. -/
def sizeOfValBody : CapturedMir :=
  { defPath := "single_wide_intrinsic"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := usizeTy, debugName := none }
      , { mutability := .not, ty := rawSliceU32Ty, debugName := none } ]
    basicBlocks :=
      [ { statements := []
          terminator :=
            ⟨.call
              (.constant
                { ty :=
                    { kind :=
                        .fnDef "core::intrinsics::size_of_val"
                          [sliceU32PointeeTy.kind]
                      layoutIdx := 0 }
                  val := .zeroSized })
              [.copy ⟨1, []⟩] ⟨0, []⟩ (some 1) .unreachable, "t0"⟩
          isCleanup := false }
      , { statements := []
          terminator := ⟨.return_, "t1"⟩
          isCleanup := false } ]
    fnAbi := fnAbiOf 8
    layouts := emptyLayoutTable
    allocations := [] }

/-- `*const u32`. -/
def rawU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }

/-- Multi-step `from_raw_parts` → `ptr::metadata` → `to_raw_parts`
(`CastKind.ptrToPtr`) → `from_raw_parts` → `size_of_val<[u32]>` → `Return`
pipeline body, locked in the cross-root bridge to
`LeanMiriSpec.Correspondence.WideSliceWitnesses.wideSlicePipelineBody`. -/
def pipelineBody : CapturedMir :=
  { defPath := "wide_slice_pipeline"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls :=
      [ { mutability := .mut, ty := usizeTy, debugName := none }
      , { mutability := .mut, ty := rawSliceU32Ty, debugName := none }
      , { mutability := .not, ty := rawU32Ty, debugName := none }
      , { mutability := .not, ty := usizeTy, debugName := none }
      , { mutability := .mut, ty := usizeTy, debugName := none }
      , { mutability := .mut, ty := rawU32Ty, debugName := none }
      , { mutability := .mut, ty := rawSliceU32Ty, debugName := none } ]
    basicBlocks :=
      [ { statements :=
            [ ⟨.assign ⟨1, []⟩ (.aggregate (.rawPtr sliceU32PointeeTy .not)
                [.copy ⟨2, []⟩, .copy ⟨3, []⟩]), "s0"⟩
            , ⟨.assign ⟨4, []⟩ (.unaryOp .ptrMetadata (.copy ⟨1, []⟩)), "s1"⟩
            , ⟨.assign ⟨5, []⟩ (.cast .ptrToPtr (.copy ⟨1, []⟩) rawU32Ty),
                "s2"⟩
            , ⟨.assign ⟨6, []⟩ (.aggregate (.rawPtr sliceU32PointeeTy .not)
                [.copy ⟨5, []⟩, .copy ⟨4, []⟩]), "s3"⟩ ]
          terminator :=
            ⟨.call
              (.constant
                { ty :=
                    { kind :=
                        .fnDef "core::intrinsics::size_of_val"
                          [sliceU32PointeeTy.kind]
                      layoutIdx := 0 }
                  val := .zeroSized })
              [.copy ⟨6, []⟩] ⟨0, []⟩ (some 1) .unreachable, "t0"⟩
          isCleanup := false }
      , { statements := []
          terminator := ⟨.return_, "t1"⟩
          isCleanup := false } ]
    fnAbi := fnAbiOf 8
    layouts := emptyLayoutTable
    allocations := [] }

/-- Initial state of `pipelineBody` with `_2 = ptr(1, 0)` and `_3 = 3`. -/
def pipelineInit : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals :=
          [ .uninit, .uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)
          , .init (.scalar ⟨3, 8⟩), .uninit, .uninit, .uninit ] }
    memory := emptyMemory }

/-- Initial state of `sizeOfValBody`. -/
def sizeOfValInit (len : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (wideVal len)] }
    memory := emptyMemory }

/-- Observable of a value: scalar bits, or the length metadata of a wide
pointer. -/
def obsValue : Value → Option Nat
  | .scalar sc => some sc.bits
  | .aggregate _ [.ptr _ _, .scalar sc] => some sc.bits
  | _ => none

/-- One trusted `stepMirFn` step of `body`, observing local `_0`. -/
def frameVerdict (body : CapturedMir) (s : MachineState) :
    Option (Verdict Nat) :=
  match stepMirFn body s with
  | .tau (.running s') =>
    match get? s'.frame.locals 0 with
    | some (.init v) => (obsValue v).map Verdict.returns
    | _ => none
  | .vis (.inl (.fail .ub)) _ => some .undefinedBehavior
  | .vis (.inl (.fail .unsupported)) _ => some .unsupported
  | _ => none

/-- State of a bounded run of the trusted machine. -/
inductive RunState : Type where
  /-- Still running, in machine state `s`. -/
  | running (s : MachineState)
  /-- Finished with verdict `v` (`none`: no verdict). -/
  | done (v : Option (Verdict Nat))

/-- One trusted `stepMirFn` step of a bounded run. -/
def runStep (body : CapturedMir) : RunState → RunState
  | .done v => .done v
  | .running s =>
    match stepMirFn body s with
    | .tau (.running s') => .running s'
    | .vis (.inr (.inl (.emit _))) k =>
      match k PUnit.unit with
      | .running s' => .running s'
      | _ => .done none
    | .ret (.normal r) => .done ((obsValue r.1).map Verdict.returns)
    | .vis (.inl (.fail .ub)) _ => .done (some .undefinedBehavior)
    | .vis (.inl (.fail .unsupported)) _ => .done (some .unsupported)
    | _ => .done none

/-- At most `fuel` trusted `stepMirFn` steps of `body`, observing the
returned value. -/
def runVerdict (body : CapturedMir) (fuel : Nat) (s : MachineState) :
    Option (Verdict Nat) :=
  match Nat.repeat (runStep body) fuel (.running s) with
  | .done v => v
  | .running _ => none

open MiniRustSpec.Correspondence.WideSliceDst in
/-- Verdict of the trusted machine on each corpus key. -/
def annealVerdict (r : Regime) (p : Prog) (q : Query) (_c : Unit) :
    Option (Verdict Nat) :=
  match p with
  | .metadata => frameVerdict metadataBody (frameInit q.len q.idx)
  | .placeLen => frameVerdict placeLenBody (frameInit q.len q.idx)
  | .indexRead => frameVerdict indexReadBody (frameInit q.len q.idx)
  | .reborrow => frameVerdict (reborrowBody r) (frameInit q.len q.idx)
  | .sizeOfVal => frameVerdict sizeOfValBody (sizeOfValInit q.len)
  | .roundTrip => runVerdict wideRawPartsMir 40 wideRawPartsS0
  | .indexOob => runVerdict wideSliceIdxOobMir 30 wideSliceIdxOobS0
  | .disabledDeref =>
    runVerdict wideSliceDisabledDerefUbMir 30 wideSliceDisabledDerefUbS0
  | .disabledMetadata =>
    runVerdict wideSliceMetadataAfterParentWriteMir 30
      wideSliceMetadataAfterParentWriteS0
  | .pipeline => runVerdict pipelineBody 10 pipelineInit

/-! ### B.3 MiniRust: `MiniRustSpec` on the corpus -/

section MiniRust

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr
open MiniRustSpec.Interp MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.WideSliceDst
open MiniRustSpec.Correspondence.RefWitness

/-- `BasicMemory` machine whose allocation `3` is a live 16-byte
`[u32; 4]` at address `2^32` (four steps into the round-trip witness). -/
def mrMach : Mach :=
  match Interp.steps 4 wideRawPartsMInit with
  | .ok m => m
  | .error _ => wideRawPartsMInit

/-- `TreeBorrowsMemory` counterpart of `mrMach`. -/
def mrMachTB : MachTB :=
  match Interp.stepsTB 4 wideRawPartsTBInit with
  | .ok m => m
  | .error _ => wideRawPartsTBInit

/-- Wide `BasicMemory` pointer to the array with length `len`. -/
def mrWide (len : Nat) : Pointer Prov :=
  ThinPointer.widen { addr := 2 ^ 32, provenance := some (⟨3⟩, ()) }
    (some (.ElementCount (Int.ofNat len)))

/-- Wide `TreeBorrowsMemory` pointer to the array with length `len`. -/
def mrWideTB (len : Nat) : Pointer (Memory.Provenance TBM) :=
  ThinPointer.widen { addr := 2 ^ 32, provenance := some (⟨3⟩, []) }
    (some (.ElementCount (Int.ofNat len)))

/-- MiniRust pointer type of a regime: `*const [u32]` or `&[u32]`. -/
def mrPtrType : Regime → PtrType
  | .raw => .Raw .ElementCount
  | .safe => sliceRefPtrType .not ⟨4⟩ ⟨4⟩

/-- Verdict of a MiniRust computation returning a non-negative integer. -/
def intVerdict : Interp Int → Option (Verdict Nat)
  | .ok i => if 0 ≤ i then some (.returns i.toNat) else none
  | .error (.ub _) => some .undefinedBehavior
  | .error (.unsupported _) => some .unsupported
  | .error _ => none

/-- `ptr::metadata` of a `BasicMemory` wide pointer
(`PointerMetaKind::encode_as_value`). -/
def mrMetadata (len : Nat) : Interp Int := do
  match ← PointerMetaKind.encode_as_value .ElementCount (mrWide len).metadata
    with
  | .Int i => pure i
  | _ => .error (.specPanic "metadata is not an integer")

/-- `ptr::metadata` of a `TreeBorrowsMemory` wide pointer. -/
def mrMetadataTB (len : Nat) : Interp Int := do
  match ← PointerMetaKind.encode_as_valueM (M := TBM) .ElementCount
    (mrWideTB len).metadata with
  | .Int i => pure i
  | _ => .error (.specPanic "metadata is not an integer")

/-- Reborrow in MiniRust: `Machine::check_ptr` at the regime's pointer
type, then the pointer's metadata. -/
def mrReborrow (mem : MrMem) (r : Regime) (len : Nat) : Interp Int :=
  match mem with
  | .basic => do
    checkPtr (mrWide len) (mrPtrType r) (some mrMach)
    mrMetadata len
  | .treeBorrows => do
    checkPtrM (M := TBM) (mrWideTB len) (mrPtrType r) (some mrMachTB)
    mrMetadataTB len

/-- `size_of_val` in MiniRust: `Machine::compute_size` of the slice. -/
def mrSizeOfVal (mem : MrMem) (len : Nat) : Interp Int :=
  match mem with
  | .basic => do
    let sz ← computeSize mrMach (.Slice ⟨4⟩ ⟨4⟩)
      (some (.ElementCount (Int.ofNat len)))
    pure sz.bytes
  | .treeBorrows => do
    let sz ← computeSizeM (M := TBM) mrMachTB (.Slice ⟨4⟩ ⟨4⟩)
      (some (.ElementCount (Int.ofNat len)))
    pure sz.bytes

/-- Little-endian value of fully initialized bytes. -/
def bytesNat? {P : Type} (bytes : List (AbstractByte P)) : Option Nat :=
  bytes.foldr
    (fun b acc =>
      match b with
      | .Init x _ => acc.map (fun n => x.toNat + 256 * n)
      | .Uninit => none)
    (some 0)

/-- Verdict of a `BasicMemory` machine run: the caller's return
allocation once the callee has returned. -/
def machVerdict : Interp Mach → Option (Verdict Nat)
  | .ok m =>
    match m.mem.memory.allocations[0]?, m.threads.map (·.stack.length) with
    | some a, [1] => (bytesNat? a.data).map Verdict.returns
    | _, _ => none
  | .error (.ub _) => some .undefinedBehavior
  | .error (.unsupported _) => some .unsupported
  | .error _ => none

/-- Verdict of a `TreeBorrowsMemory` machine run. -/
def machVerdictTB : Interp MachTB → Option (Verdict Nat)
  | .ok m =>
    match m.mem.memory.mem.allocations[0]?,
      m.threads.map (·.stack.length) with
    | some a, [1] => (bytesNat? a.data).map Verdict.returns
    | _, _ => none
  | .error (.ub _) => some .undefinedBehavior
  | .error (.unsupported _) => some .unsupported
  | .error _ => none

/-- Companion MiniRust function to `wideSliceDisabledDerefUbFn`: activates
`_4`'s borrow, copies it to a raw wide pointer `_7`, disables its borrow tag
by overwriting `_2`, and then extracts `ptr::metadata(_7)` without
dereferencing memory, returning `4` under both `BasicMemory` and
`TreeBorrowsMemory`. -/
def disabledMetadataFn : Gen.Function where
  locals := ⟨[(localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, .Array (.Int u32) 4),
    (localName 3, .Ptr (.Ref .Mutable arrU32_4PointeeInfo)),
    (localName 4, .Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩)),
    (localName 5, .Int IntType.usize_ty),
    (localName 6, mrWidePairTupleTy),
    (localName 7, .Ptr (.Raw .ElementCount))]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6), .StorageLive (localName 7),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 10) (.Int u32),
                 .Constant (.Int 20) (.Int u32),
                 .Constant (.Int 30) (.Int u32),
                 .Constant (.Int 40) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Local (localName 2))
          (.Ref .Mutable arrU32_4PointeeInfo)),
      .Assign (.Local (localName 4))
        (.UnOp (.Cast (.Transmute (.Ptr (sliceRefPtrType .mut ⟨4⟩ ⟨4⟩))))
          (.Tuple [.UnOp (.Cast (.Transmute (.Ptr (.Raw .None))))
                     (.Load (.Local (localName 3))),
                   .Constant (.Int 4) (.Int IntType.usize_ty)]
            mrWidePairTupleTy)),
      .Assign (.Local (localName 5))
        (.Constant (.Int 0) (.Int IntType.usize_ty)),
      .Assign
        (.Index (.Deref (.Load (.Local (localName 4))) (.Slice (.Int u32)))
          (.Load (.Local (localName 5))))
        (.Constant (.Int 77) (.Int u32)),
      .Assign (.Local (localName 7))
        (.UnOp (.Cast (.Transmute (.Ptr (.Raw .ElementCount))))
          (.Load (.Local (localName 4)))),
      .Assign (.Local (localName 2))
        (.Tuple [.Constant (.Int 1) (.Int u32),
                 .Constant (.Int 2) (.Int u32),
                 .Constant (.Int 3) (.Int u32),
                 .Constant (.Int 4) (.Int u32)]
          (.Array (.Int u32) 4)),
      .Assign (.Local (localName 6))
        (.UnOp (.Cast (.Transmute mrWidePairTupleTy))
          (.Load (.Local (localName 7)))),
      .Assign (.Local (localName 5))
        (.Load (.Field (.Local (localName 6)) 1)),
      .Assign (.Local (localName 0))
        (.UnOp (.Cast (.IntToInt u32)) (.Load (.Local (localName 5))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

/-- Initial `BasicMemory` machine for `disabledMetadataFn`. -/
def disabledMetadataMInit : Mach :=
  machine wideSliceMetadataAfterParentWriteMir disabledMetadataFn
    wideSliceMetadataAfterParentWriteS0.frame.locals disabledMetadataFn.start

/-- Initial `TreeBorrowsMemory` machine for `disabledMetadataFn`. -/
def disabledMetadataTBInit : MachTB := liftMachToTB disabledMetadataMInit

/-- Verdict of MiniRust on each corpus key. Programs outside the MiniRust
fragment of this corpus have no run. -/
def mrVerdict (m : MrMem × Regime) (p : Prog) (q : Query) (_c : Unit) :
    Option (Verdict Nat) :=
  match p, m.1 with
  | .metadata, .basic => intVerdict (mrMetadata q.len)
  | .metadata, .treeBorrows => intVerdict (mrMetadataTB q.len)
  | .reborrow, mem => intVerdict (mrReborrow mem m.2 q.len)
  | .sizeOfVal, mem => intVerdict (mrSizeOfVal mem q.len)
  | .roundTrip, .basic => machVerdict (Interp.steps 25 wideRawPartsMInit)
  | .roundTrip, .treeBorrows =>
    machVerdictTB (Interp.stepsTB 25 wideRawPartsTBInit)
  | .indexOob, .basic => machVerdict (Interp.steps 10 wideSliceIdxOobMInit)
  | .indexOob, .treeBorrows =>
    machVerdictTB (Interp.stepsTB 10 wideSliceIdxOobTBInit)
  | .disabledDeref, .basic =>
    machVerdict (Interp.steps 13 wideSliceDisabledDerefUbMInit)
  | .disabledDeref, .treeBorrows =>
    machVerdictTB (Interp.stepsTB 12 wideSliceDisabledDerefUbTBInit)
  | .disabledMetadata, .basic =>
    machVerdict (Interp.steps 18 disabledMetadataMInit)
  | .disabledMetadata, .treeBorrows =>
    machVerdictTB (Interp.stepsTB 18 disabledMetadataTBInit)
  | _, _ => none

end MiniRust

/-- MiniRust fragment of the corpus. Excluded keys are documented
divergences or programs without a MiniRust run:
`sizeOfVal` at `tooBig` (MiniRust's `compute_size` is total on raw
pointers), and `disabledDeref` under `BasicMemory` (no aliasing model). -/
def gateMR (m : MrMem × Regime) (p : Prog) (q : Query) : Bool :=
  match p with
  | .metadata => true
  | .reborrow => true
  | .sizeOfVal => decide (q ≠ .tooBig)
  | .roundTrip => decide (m.2 = .raw ∧ q = .inBounds)
  | .indexOob => decide (m.2 = .raw ∧ q = .inBounds)
  | .disabledDeref =>
    decide (m.1 = .treeBorrows ∧ m.2 = .raw ∧ q = .inBounds)
  | .disabledMetadata => decide (m.2 = .raw ∧ q = .inBounds)
  | _ => false

/-! ### B.4 LeanMiri: reference table of the vendored `Miri` interpreter

`lmReference` records, per corpus key, the verdict of one
`Miri.Interpreter.Step.step` under the wide-slice hooks of
`LeanMiriSpec.Correspondence.WideSliceDstLM`. The cross-root kernel bridge
proves the vendored interpreter equal to this table on every key. -/

/-- Reference verdict of the vendored `Miri` interpreter. -/
def lmReference (r : Regime) (p : Prog) (q : Query) (_c : Unit) :
    Option (Verdict Nat) :=
  match p, r, q with
  | .metadata, _, q => some (.returns q.len)
  | .placeLen, _, q => some (.returns q.len)
  | .indexRead, _, .oobIndex => some .undefinedBehavior
  | .indexRead, _, _ => some (.returns 20)
  | .reborrow, .raw, q => some (.returns q.len)
  | .reborrow, .safe, .inBounds => some (.returns 3)
  | .reborrow, .safe, .oobIndex => some (.returns 3)
  | .reborrow, .safe, _ => some .undefinedBehavior
  | .sizeOfVal, _, .tooBig => some .undefinedBehavior
  | .sizeOfVal, _, q => some (.returns (q.len * 4))
  | .pipeline, .raw, .inBounds => some (.returns 12)
  | _, _, _ => none

/-- LeanMiri fragment of the corpus. Excluded keys are the documented
divergences `DIV-LM-PLACE-LEN-BORROW-BOUNDS` and
`DIV-LM-RAW-SLICE-PARTIAL-OOB-LEN-INDEX` (Anneal checks the whole slice
against its backing array before `Len` and indexing), and the MiniRust-only
whole-program fixtures. -/
def gateLM (r : Regime) (p : Prog) (q : Query) : Bool :=
  match p with
  | .metadata => true
  | .reborrow => true
  | .sizeOfVal => true
  | .placeLen => decide (q = .inBounds ∨ q = .oobIndex)
  | .indexRead => decide (q = .inBounds ∨ q = .oobIndex)
  | .pipeline => decide (r = .raw ∧ q = .inBounds)
  | _ => false

/-! ### B.5 Model, sides, and certificates -/

/-- The Anneal side of the wide-slice corpus. -/
def model : Model Regime Prog Query Unit Nat (Nat × Nat) where
  evalA := annealVerdict
  codec := halvesCodec
  progs := allProgs
  queries := allQueries
  choices := [()]
  progs_complete := fun p => by cases p <;> decide
  queries_complete := fun q => by cases q <;> decide
  choices_complete := fun _ => List.mem_singleton.mpr rfl

/-- The MiniRust side: positive and fault witnesses at
`(BasicMemory, safe)`, and the raw-versus-safe `isize::MAX` mode flip. -/
def sideMR : Side Regime (MrMem × Regime) Prog Query Unit Nat (Nat × Nat)
    where
  toAnneal := fun m => m.2
  gate := gateMR
  verdictR := mrVerdict
  rep := halves
  modes := allMrModes
  modes_complete := fun m => by
    cases m with
    | mk a b => cases a <;> cases b <;> decide
  wMode := (.basic, .safe)
  okProg := .reborrow
  okQuery := .inBounds
  okChoice := ()
  faultProg := .reborrow
  faultQuery := .tooBig
  faultChoice := ()
  flip := some ((.basic, .safe), (.basic, .raw), .reborrow, .tooBig, ())

/-- The LeanMiri side over an arbitrary presentation `verdictLM` of the
LeanMiri authority. -/
def sideLM (verdictLM : Regime → Prog → Query → Unit → Option (Verdict Nat)) :
    Side Regime Regime Prog Query Unit Nat (Nat × Nat) where
  toAnneal := fun m => m
  gate := gateLM
  verdictR := verdictLM
  rep := halves
  modes := allRegimes
  modes_complete := fun m => by cases m <;> decide
  wMode := .safe
  okProg := .reborrow
  okQuery := .inBounds
  okChoice := ()
  faultProg := .reborrow
  faultQuery := .tooBig
  faultChoice := ()
  flip := some (.safe, .raw, .reborrow, .tooBig, ())

/-- Kernel-evaluated certificate of the MiniRust side. -/
theorem sideMR_check : sideMR.check model = true := by decide +kernel

/-- Kernel-evaluated certificate of the LeanMiri reference side. -/
theorem sideLM_reference_check : (sideLM lmReference).check model = true := by
  decide +kernel

/-- Wide-slice bundle over any LeanMiri presentation that passes the
certificate. The cross-root kernel bridge applies this to the vendored
`Miri` interpreter. -/
def bundleWith
    (verdictLM : Regime → Prog → Query → Unit → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle Regime Prog Query Nat Unit (Nat × Nat)
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  Corpus.bundle model sideMR (sideLM verdictLM) sideMR_check h

/-- The surface wide-slice bundle (LeanMiri presented by `lmReference`). -/
def bundle :
    DualCorrespondenceBundle Regime Prog Query Nat Unit (Nat × Nat)
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  bundleWith lmReference sideLM_reference_check

/-! ### B.6 Presenting the LeanMiri authority by its own observations -/

/-- LeanMiri corpus keys: every regime, single-step LeanMiri program, and
query (including keys excluded from `gateLM`), plus the multi-step
`from_raw_parts`/`to_raw_parts` pipeline. -/
def lmKeys : List (Regime × Prog × Query × Unit) :=
  (allRegimes.flatMap fun r =>
    [Prog.metadata, .placeLen, .indexRead, .reborrow, .sizeOfVal].flatMap
      fun p => allQueries.map fun q => (r, p, q, ())) ++
  [(.raw, .pipeline, .inBounds, ())]

/-- `lmReference` on a key. -/
def lmReferenceAt (k : Regime × Prog × Query × Unit) :
    Option (Verdict Nat) :=
  lmReference k.1 k.2.1 k.2.2.1 k.2.2.2

/-- Body stepped by LeanMiri for a frame program. -/
def lmBody : Regime → Prog → CapturedMir
  | _, .metadata => metadataBody
  | _, .placeLen => placeLenBody
  | _, .indexRead => indexReadBody
  | r, .reborrow => reborrowBody r
  | _, _ => sizeOfValBody

/-- Type of the result local `_0` of a frame program. -/
def lmRetTy : Regime → Prog → Ty
  | _, .indexRead => u32Ty
  | r, .reborrow => reborrowTy r
  | _, _ => usizeTy

/-- Undefined-behavior diagnostics of the vendored interpreter on the
corpus. -/
def lmUbMessages : List String :=
  ["place index 4 out of bounds for 3", "pointer dereference check failed",
    "InvalidMeta(SliceTooBig)"]

/-- Representation class of a returned LeanMiri local. -/
inductive RetClass : Type where
  /-- A `usize` local. -/
  | usize
  /-- A `u32` local. -/
  | u32
  /-- A wide-pointer local. -/
  | wide
  deriving DecidableEq

/-- Representation class of the result of a program. -/
def retClassOf : Prog → RetClass
  | .indexRead => .u32
  | .reborrow => .wide
  | _ => .usize

/-- The distinct normal returns of `lmReference` on the LeanMiri keys, with
their representation classes. -/
def lmReturnDenotations : List (Nat × RetClass) :=
  (lmKeys.filterMap fun k =>
    match lmReferenceAt k with
    | some (.returns n) => some (n, retClassOf k.2.1)
    | _ => none).eraseDups

/-- The LeanMiri authority assembled from interpreter-typed observation
functions: `frameObs body retTy len idx` is one interpreter step of a frame
program observing `_0`, `sizeObs body len` is one step of `size_of_val`,
`pipelineObs` is the 5-step `from_raw_parts` / `ptr::metadata` /
`to_raw_parts` / `size_of_val` pipeline observation of `_0`,
`retUsize` / `retU32` / `retWide` embed an expected result as a `usize`,
`u32`, or wide-pointer local, and `ubObs` embeds a diagnostic. -/
def authorityOf (Obs : Type) (decEq : DecidableEq Obs)
    (frameObs : CapturedMir → Ty → Nat → Nat → Obs)
    (sizeObs : CapturedMir → Nat → Obs) (pipelineObs : Obs)
    (retUsize retU32 retWide : Nat → Obs) (ubObs : String → Obs) :
    ObsAuthority (Regime × Prog × Query × Unit) Nat where
  Obs := Obs
  decEq := decEq
  observe := fun k =>
    match k.2.1 with
    | .sizeOfVal => some (sizeObs sizeOfValBody k.2.2.1.len)
    | .metadata | .placeLen | .indexRead | .reborrow =>
      some (frameObs (lmBody k.1 k.2.1) (lmRetTy k.1 k.2.1) k.2.2.1.len
        k.2.2.1.idx)
    | .pipeline =>
      match k.1, k.2.2.1 with
      | .raw, .inBounds => some pipelineObs
      | _, _ => none
    | _ => none
  denote :=
    (lmReturnDenotations.map fun d =>
      (.returns d.1,
        match d.2 with
        | .u32 => retU32 d.1
        | .wide => retWide d.1
        | .usize => retUsize d.1)) ++
    lmUbMessages.map fun s => (.undefinedBehavior, ubObs s)

/-- Verdict function of an authority. -/
def verdictOf (A : ObsAuthority (Regime × Prog × Query × Unit) Nat) :
    Regime → Prog → Query → Unit → Option (Verdict Nat) :=
  fun r p q c => A.verdict (r, p, q, c)

/-- Certificate of the LeanMiri side for an authority. -/
def checkOf (A : ObsAuthority (Regime × Prog × Query × Unit) Nat) : Bool :=
  (sideLM (verdictOf A)).check model

/-- Agreement of an authority with `lmReference` on every LeanMiri key. -/
def matchesReference
    (A : ObsAuthority (Regime × Prog × Query × Unit) Nat) : Bool :=
  A.matchesOn lmReferenceAt lmKeys

/-- `matchesReference` certifies that the authority's interpreter computes
exactly `lmReference` on every LeanMiri key. -/
theorem matchesReference_sound
    (A : ObsAuthority (Regime × Prog × Query × Unit) Nat)
    (h : matchesReference A = true) :
    ∀ k, k ∈ lmKeys → A.verdict k = lmReferenceAt k :=
  A.matchesOn_sound lmReferenceAt lmKeys h

/-- Wide-slice bundle over an authority presented by its observations. -/
def bundleOfAuthority
    (A : ObsAuthority (Regime × Prog × Query × Unit) Nat)
    (h : checkOf A = true) :
    DualCorrespondenceBundle Regime Prog Query Nat Unit (Nat × Nat)
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  bundleWith (verdictOf A) h

end WideSlice

/-! ### B.7 Theorems of the wide-slice bundle

Each `*_with` theorem holds for every presentation of the LeanMiri authority
that passes the certificate; the cross-root kernel bridge instantiates them
at the vendored `Miri` interpreter. -/

namespace WideSlice

open Anneal.DualCorrespondenceBundle
open Corpus

/-- Simulation certificate of the MiniRust side. -/
theorem sideMR_sim : sideMR.simCheck model = true :=
  (Bool.and_eq_true _ _ ▸ sideMR_check).1

/-- The trusted machine is deterministic on the corpus. -/
theorem anneal_det (r : Regime) (p : Prog) (q : Query)
    (out out' : ExecOutcome4 Nat Unit)
    (h₁ : ∃ c, outcome? (annealVerdict r p q c) = some out)
    (h₂ : ∃ c, outcome? (annealVerdict r p q c) = some out') :
    out = out' := by
  obtain ⟨⟨⟩, e₁⟩ := h₁
  obtain ⟨⟨⟩, e₂⟩ := h₂
  exact Option.some.inj (e₁.symm.trans e₂)

/-- No corpus verdict is an unwind. -/
theorem outcome?_ne_unwind {V : Type} (v : Option (Verdict V)) (u : Unit) :
    outcome? v ≠ some (.unwind u) := by
  intro h
  cases v with
  | none => cases h
  | some v => cases v <;> cases h

/-- MiniRust's `check_ptr` rejects the `&[u32]` reborrow whose byte size
`2^63` exceeds `isize::MAX` (fault-equivalence witness, MiniRust side). -/
theorem mr_safe_tooBig_faults :
    (sideMR.rel model).ExecR (.basic, .safe) .reborrow .tooBig ()
      (.fault .undefined) :=
  Side.execR_of_verdict model sideMR (v := .undefinedBehavior)
    (by decide +kernel)

/-- The same pointer reborrowed raw is accepted by `check_ptr`, and its
metadata `2^61` is returned: the regime flips the outcome. -/
theorem mr_raw_tooBig_returns :
    (sideMR.rel model).ExecR (.basic, .raw) .reborrow .tooBig ()
      (.normal (2 ^ 61)) :=
  Side.execR_of_verdict model sideMR (v := .returns (2 ^ 61))
    (by decide +kernel)

/-- Tree Borrows: reading through the reference disabled by a parent write
is undefined behavior in `TreeBorrowsMemory` and in the trusted machine. -/
theorem mr_disabledDeref_faults :
    (sideMR.rel model).ExecR (.treeBorrows, .raw) .disabledDeref .inBounds
        () (.fault .undefined) ∧
      (sideMR.rel model).ExecA (.treeBorrows, .raw) .disabledDeref .inBounds
        () (.fault .undefined) :=
  ⟨Side.execR_of_verdict model sideMR (v := .undefinedBehavior)
      (by decide +kernel),
   Side.execA_of_verdict model sideMR (v := .undefinedBehavior)
      (by decide +kernel)⟩

/-- Mode regime `TreeBorrowsMemory` versus `BasicMemory`: without an
aliasing model MiniRust returns `1` on the disabled-reference program,
where the trusted machine faults; the key is therefore outside `gateMR`,
and the exclusion is necessary. -/
theorem gateMR_disabledDeref_basic_exclusion_is_tight :
    gateMR (.basic, .raw) .disabledDeref .inBounds = false ∧
      mrVerdict (.basic, .raw) .disabledDeref .inBounds () =
        some (.returns 1) ∧
      annealVerdict .raw .disabledDeref .inBounds () =
        some .undefinedBehavior ∧
      couplesB halvesCodec.encode halves
        (annealVerdict .raw .disabledDeref .inBounds ())
        (mrVerdict (.basic, .raw) .disabledDeref .inBounds ()) = false := by
  decide +kernel

/-- `isize::MAX` on raw pointers: MiniRust's `compute_size` is total and
returns `2^63`, where the trusted machine faults; the key is outside
`gateMR`, and the exclusion is necessary. -/
theorem gateMR_sizeOfVal_tooBig_exclusion_is_tight :
    gateMR (.basic, .raw) .sizeOfVal .tooBig = false ∧
      mrVerdict (.basic, .raw) .sizeOfVal .tooBig () =
        some (.returns (2 ^ 63)) ∧
      annealVerdict .raw .sizeOfVal .tooBig () = some .undefinedBehavior := by
  decide +kernel

/-- The LeanMiri exclusions are necessary: on a length exceeding the
backing array the vendored interpreter returns the metadata (`Len`) and
reads the element (indexing), where the trusted machine faults. -/
theorem gateLM_exclusions_are_tight :
    gateLM .raw .placeLen .oobLen = false ∧
      lmReference .raw .placeLen .oobLen () = some (.returns 5) ∧
      annealVerdict .raw .placeLen .oobLen () = some .undefinedBehavior ∧
      gateLM .raw .indexRead .oobLen = false ∧
      lmReference .raw .indexRead .oobLen () = some (.returns 20) ∧
      annealVerdict .raw .indexRead .oobLen () = some .undefinedBehavior := by
  decide +kernel

/-- Non-dereferencing `ptr::metadata` succeeds on the same out-of-bounds
wide pointer on which `Len` faults. -/
theorem metadata_total_where_len_faults :
    annealVerdict .raw .metadata .oobLen () = some (.returns 5) ∧
      annealVerdict .raw .placeLen .oobLen () = some .undefinedBehavior ∧
      mrVerdict (.basic, .raw) .metadata .oobLen () = some (.returns 5) ∧
      mrVerdict (.treeBorrows, .raw) .metadata .oobLen () =
        some (.returns 5) := by
  decide +kernel

/-- The corpus exercises every program class on the trusted machine. -/
theorem anneal_corpus_values :
    annealVerdict .raw .roundTrip .inBounds () = some (.returns 46) ∧
      annealVerdict .raw .indexOob .inBounds () = some .undefinedBehavior ∧
      annealVerdict .raw .sizeOfVal .inBounds () = some (.returns 12) ∧
      annealVerdict .raw .indexRead .inBounds () = some (.returns 20) ∧
      annealVerdict .raw .indexRead .oobIndex () =
        some .undefinedBehavior ∧
      annealVerdict .safe .reborrow .oobLen () = some .undefinedBehavior ∧
      annealVerdict .raw .reborrow .oobLen () = some (.returns 5) := by
  decide +kernel

section Derived

variable (verdictLM : Regime → Prog → Query → Unit → Option (Verdict Nat))

/-- Simulation certificate of the LeanMiri side. -/
theorem sideLM_sim_with
    (h : (sideLM verdictLM).check model = true) :
    (sideLM verdictLM).simCheck model = true :=
  (Bool.and_eq_true _ _ ▸ h).1

/-- **Cross-authority fault equivalence** at the `isize::MAX` reborrow in
the safe regime. -/
theorem safe_tooBig_fault_equiv_with
    (h : (sideLM verdictLM).check model = true) :
    (∃ c, (bundleWith verdictLM h).mrRel.ExecR (.basic, .safe) .reborrow
        .tooBig c (.fault .undefined)) ↔
      (∃ c, (bundleWith verdictLM h).lmRel.ExecR .safe .reborrow .tooBig c
        (.fault .undefined)) :=
  (bundleWith verdictLM h).crossAuthorityFaultEquiv
    (mMR := (.basic, .safe)) (mLM := .safe) (p := .reborrow) (q := .tooBig)
    rfl rfl rfl .undefined

/-- Hence every LeanMiri presentation that passes the certificate rejects
that reborrow as well: MiniRust's verdict transfers across authorities. -/
theorem lm_safe_tooBig_faults_with
    (h : (sideLM verdictLM).check model = true) :
    verdictLM .safe .reborrow .tooBig () = some .undefinedBehavior := by
  obtain ⟨⟨⟩, hc⟩ :=
    (safe_tooBig_fault_equiv_with verdictLM h).mp ⟨(), mr_safe_tooBig_faults⟩
  exact Side.verdict_of_execR model (sideLM verdictLM)
    (v := .undefinedBehavior) hc

/-- **Three-way normal agreement** at the in-bounds safe reborrow: any
normal MiniRust return and any normal LeanMiri return are the metadata `3`
computed by the trusted machine. -/
theorem inBounds_reborrow_threeWay_with
    (h : (sideLM verdictLM).check model = true) {rMR rLM : Nat}
    (hMR : (sideMR.rel model).ExecR (.basic, .safe) .reborrow .inBounds ()
      (.normal rMR))
    (hLM : ((sideLM verdictLM).rel model).ExecR .safe .reborrow .inBounds ()
      (.normal rLM)) :
    rMR = 3 ∧ rLM = 3 := by
  obtain ⟨a, hA, _, _, hrMR, hrLM⟩ :=
    (bundleWith verdictLM h).threeWayNormalAgreement
      (mMR := (.basic, .safe)) (mLM := .safe)
      (p := .reborrow) (q := .inBounds) rfl rfl rfl
      (fun out out' => anneal_det .safe .reborrow .inBounds out out')
      hMR hLM
  have ha : a = 3 := by
    obtain ⟨⟨⟩, e⟩ := hA
    have e3 : outcome? (annealVerdict .safe .reborrow .inBounds ()) =
        some (.normal 3) :=
      congrArg outcome?
        (by decide +kernel :
          annealVerdict .safe .reborrow .inBounds () = some (.returns 3))
    have e' := Option.some.inj (e.symm.trans e3)
    cases e'
    rfl
  subst ha
  exact ⟨halvesCodec.encode_injective hrMR,
    halvesCodec.encode_injective hrLM⟩

/-- Three-way agreement of shared representations and their validity. -/
theorem inBounds_reborrow_rep_with
    (h : (sideLM verdictLM).check model = true) {rMR rLM : Nat}
    (hMR : (sideMR.rel model).ExecR (.basic, .safe) .reborrow .inBounds ()
      (.normal rMR))
    (hLM : ((sideLM verdictLM).rel model).ExecR .safe .reborrow .inBounds ()
      (.normal rLM)) :
    halves rMR = halves rLM ∧ halvesCodec.ValidRep (halves rMR) ∧
      halvesCodec.ValidRep (halves rLM) :=
  ⟨((bundleWith verdictLM h).threeWayNormalAgreement_rep
      (mMR := (.basic, .safe)) (mLM := .safe)
      (p := .reborrow) (q := .inBounds) rfl rfl rfl
      (fun out out' => anneal_det .safe .reborrow .inBounds out out')
      hMR hLM).1,
   (bundleWith verdictLM h).threeWayNormalAgreement_validRep
      (mMR := (.basic, .safe)) (mLM := .safe)
      (p := .reborrow) (q := .inBounds) rfl rfl rfl
      (fun out out' => anneal_det .safe .reborrow .inBounds out out')
      hMR hLM⟩

/-- No authority unwinds on a shared corpus key (Case 3 is exercised and
refuted by the trusted machine, which has no unwinding corpus run). -/
theorem no_unwind_with
    (h : (sideLM verdictLM).check model = true) {uMR uLM : Unit}
    (hMR : (sideMR.rel model).ExecR (.basic, .safe) .reborrow .inBounds ()
      (.unwind uMR))
    (hLM : ((sideLM verdictLM).rel model).ExecR .safe .reborrow .inBounds ()
      (.unwind uLM)) : False := by
  obtain ⟨uA, ⟨c, hA⟩, _, _⟩ :=
    (bundleWith verdictLM h).threeWayUnwindAgreement
      (mMR := (.basic, .safe)) (mLM := .safe)
      (p := .reborrow) (q := .inBounds) rfl rfl rfl
      (fun out out' => anneal_det .safe .reborrow .inBounds out out')
      hMR hLM
  exact outcome?_ne_unwind _ uA hA

/-- **Cross-authority well-formedness equivalence** at non-dereferencing
metadata of an out-of-bounds wide pointer. -/
theorem raw_metadata_wellFormed_with
    (h : (sideLM verdictLM).check model = true) :
    (sideMR.rel model).WellFormedRef (.basic, .raw) .metadata .oobLen ↔
      ((sideLM verdictLM).rel model).WellFormedRef .raw .metadata .oobLen :=
  ((bundleWith verdictLM h).crossAuthorityWellFormedEquiv
    (mMR := (.basic, .raw)) (mLM := .raw)
    (p := .metadata) (q := .oobLen) rfl rfl rfl).2.2

/-- **Cross-authority normal equivalence** at the raw `isize::MAX`
reborrow. -/
theorem raw_tooBig_normal_equiv_with
    (h : (sideLM verdictLM).check model = true) (a : Nat) :
    (∃ c r, (sideMR.rel model).ExecR (.basic, .raw) .reborrow .tooBig c
        (.normal r) ∧ halves r = halvesCodec.encode a) ↔
      (∃ c r, ((sideLM verdictLM).rel model).ExecR .raw .reborrow .tooBig c
        (.normal r) ∧ halves r = halvesCodec.encode a) :=
  (((bundleWith verdictLM h).crossAuthorityNormalEquiv
    (mMR := (.basic, .raw)) (mLM := .raw)
    (p := .reborrow) (q := .tooBig) rfl rfl rfl
    (sideMR.reverseTotal model sideMR_sim)
    ((sideLM verdictLM).reverseTotal model (sideLM_sim_with verdictLM h))).1
    a).2.2

/-- Hence every LeanMiri presentation returns the metadata `2^61` on the
raw reborrow: the regime flip transfers across authorities. -/
theorem lm_raw_tooBig_returns_with
    (h : (sideLM verdictLM).check model = true) :
    ∃ r, verdictLM .raw .reborrow .tooBig () = some (.returns r) ∧
      halves r = halves (2 ^ 61) := by
  obtain ⟨⟨⟩, r, hc, hr⟩ :=
    (raw_tooBig_normal_equiv_with verdictLM h (2 ^ 61)).mp
      ⟨(), 2 ^ 61, mr_raw_tooBig_returns, rfl⟩
  exact ⟨r, Side.verdict_of_execR model (sideLM verdictLM)
    (v := .returns r) hc, hr⟩

/-- **Exact cross-authority equivalence**: no authority diverges at the
shared key unless the other does. -/
theorem raw_tooBig_diverge_equiv_with
    (h : (sideLM verdictLM).check model = true) :
    (∃ c, (sideMR.rel model).ExecR (.basic, .raw) .reborrow .tooBig c
        .diverge) ↔
      (∃ c, ((sideLM verdictLM).rel model).ExecR .raw .reborrow .tooBig c
        .diverge) :=
  ((bundleWith verdictLM h).crossAuthorityExactEquiv
    (mMR := (.basic, .raw)) (mLM := .raw)
    (p := .reborrow) (q := .tooBig) rfl rfl rfl
    (sideMR.reverseTotal model sideMR_sim)
    ((sideLM verdictLM).reverseTotal model
      (sideLM_sim_with verdictLM h))).2.2.2

/-- Cross-authority unwind equivalence at the shared key. -/
theorem raw_tooBig_unwind_iff_with
    (h : (sideLM verdictLM).check model = true) (uA : Unit) :
    (∃ c u, (sideMR.rel model).ExecR (.basic, .raw) .reborrow .tooBig c
        (.unwind u) ∧ (sideMR.rel model).UnwRel uA u) ↔
      (∃ c u, ((sideLM verdictLM).rel model).ExecR .raw .reborrow .tooBig c
        (.unwind u) ∧ ((sideLM verdictLM).rel model).UnwRel uA u) :=
  ((bundleWith verdictLM h).crossAuthorityUnwindIff
    (mMR := (.basic, .raw)) (mLM := .raw)
    (p := .reborrow) (q := .tooBig) rfl rfl rfl
    (sideMR.reverseTotal model sideMR_sim)
    ((sideLM verdictLM).reverseTotal model (sideLM_sim_with verdictLM h))
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) uA).2.2

/-- The positive witnesses project to the single trusted machine. -/
theorem projectPositive_with
    (h : (sideLM verdictLM).check model = true) :
    ∃ a r, (bundleWith verdictLM h).ExecAnneal .safe .reborrow .inBounds
        (.normal a) ∧ halves r = halvesCodec.encode a := by
  obtain ⟨a, r, hA, _, _, hrep, _⟩ :=
    (bundleWith verdictLM h).projectPositive.1
  exact ⟨a, r, hA, hrep⟩

/-- The fault witnesses project to the single trusted machine. -/
theorem projectFault_with
    (h : (sideLM verdictLM).check model = true) :
    (bundleWith verdictLM h).ExecAnneal .safe .reborrow .tooBig
      (.fault (faultKindOf (annealVerdict .safe .reborrow .tooBig ()))) :=
  (bundleWith verdictLM h).projectFault.1.1

/-- The trusted machine is neither constantly normal nor constantly
faulting inside the gates. -/
theorem anneal_not_constant_with
    (h : (sideLM verdictLM).check model = true) :
    (¬ ∀ m p q out, (bundleWith verdictLM h).mrRel.SupportGate m p q →
        (bundleWith verdictLM h).ExecAnneal
          ((bundleWith verdictLM h).toAnnealMR m) p q out →
        ∃ a, out = .normal a) ∧
    (¬ ∀ m p q out, (bundleWith verdictLM h).lmRel.SupportGate m p q →
        (bundleWith verdictLM h).ExecAnneal
          ((bundleWith verdictLM h).toAnnealLM m) p q out →
        ∃ k, out = .fault k) :=
  ⟨(bundleWith verdictLM h).not_constant_anneal_outcome.1,
   (bundleWith verdictLM h).not_constant_anneal_outcome.2.2.2⟩

/-- Both correspondence claims and both fault-equivalence claims. -/
theorem claims_with
    (h : (sideLM verdictLM).check model = true) :
    (CorrespondenceClaim (bundleWith verdictLM h).mrRel ∧
      CorrespondenceClaim (bundleWith verdictLM h).lmRel) ∧
    (FaultEquivClaim (bundleWith verdictLM h).mrRel ∧
      FaultEquivClaim (bundleWith verdictLM h).lmRel) :=
  ⟨(bundleWith verdictLM h).correspondenceClaims,
   (bundleWith verdictLM h).faultEquivClaims⟩

/-- Two-sided productivity (`ProductiveBoth`) on both authorities. -/
theorem productiveBoth_with
    (h : (sideLM verdictLM).check model = true) :
    (bundleWith verdictLM h).mrRel.ProductiveBoth ∧
      (bundleWith verdictLM h).lmRel.ProductiveBoth :=
  ⟨sideMR.productiveBoth model sideMR_sim (),
   (sideLM verdictLM).productiveBoth model (sideLM_sim_with verdictLM h) ()⟩

/-- Productivity transfers in both directions through the bundle. -/
theorem productivity_transfer_with
    (h : (sideLM verdictLM).check model = true) :
    ((bundleWith verdictLM h).mrRel.ProductiveAnneal ∧
      (bundleWith verdictLM h).lmRel.ProductiveAnneal) ∧
    ((bundleWith verdictLM h).mrRel.ProductiveRef ∧
      (bundleWith verdictLM h).lmRel.ProductiveRef) :=
  ⟨(bundleWith verdictLM h).productiveAnneal_of_productiveRef
      (productiveBoth_with verdictLM h).1.2
      (productiveBoth_with verdictLM h).2.2,
   (bundleWith verdictLM h).productiveRef_of_reverseTotal
      (sideMR.reverseTotal model sideMR_sim)
      ((sideLM verdictLM).reverseTotal model (sideLM_sim_with verdictLM h))
      (productiveBoth_with verdictLM h).1.1
      (productiveBoth_with verdictLM h).2.1⟩

/-- Reverse totality is recorded, so two-sided productivity also follows
from the bundle-level lemma. -/
theorem productiveBoth_of_recorded_reverse_with
    (h : (sideLM verdictLM).check model = true) :
    (bundleWith verdictLM h).mrRel.ProductiveBoth ∧
      (bundleWith verdictLM h).lmRel.ProductiveBoth :=
  (bundleWith verdictLM h).productiveBoth_of_reverseTotal_some
    (productiveBoth_with verdictLM h).1.1
    (productiveBoth_with verdictLM h).2.1 rfl rfl

/-- The mode-sensitivity witness of the LeanMiri side: the safe-versus-raw
`isize::MAX` regime flip. -/
def lmModeWitness_with
    (h : (sideLM verdictLM).check model = true) :
    ModeSensitivityWitness ((sideLM verdictLM).rel model) :=
  ((sideLM verdictLM).flipW model h).get rfl

/-- The witness separates the safe and raw regimes at `tooBig`, and the
regimes are genuinely different modes. -/
theorem lmModeWitness_spec_with
    (h : (sideLM verdictLM).check model = true) :
    (lmModeWitness_with verdictLM h).m₁ = .safe ∧
      (lmModeWitness_with verdictLM h).m₂ = .raw ∧
      (lmModeWitness_with verdictLM h).p = .reborrow ∧
      (lmModeWitness_with verdictLM h).q = .tooBig ∧
      (lmModeWitness_with verdictLM h).m₁ ≠
        (lmModeWitness_with verdictLM h).m₂ :=
  ⟨rfl, rfl, rfl, rfl, (lmModeWitness_with verdictLM h).mode_ne⟩

/-- The mode-sensitivity witness of the MiniRust side (`safe` vs `raw` at
`tooBig`) is a genuine fault flip (`IsFaultFlip`): the safe reborrow faults
`.undefined`, whereas the raw reborrow returns `2^61`. -/
theorem mrModeWitness_isFaultFlip :
    ∀ ms, (sideMR.flipW model sideMR_check) = some ms → ms.IsFaultFlip := by
  intro ms hms
  have hms' : ms = (sideMR.flipW model sideMR_check).get rfl := by
    have : some ms = some ((sideMR.flipW model sideMR_check).get rfl) :=
      hms.symm
    exact Option.some.inj this
  subst hms'
  obtain ⟨oa, orr, ha, hr, hc, hna, hnr⟩ :=
    ((sideMR.flipW model sideMR_check).get rfl).flips
  refine ⟨oa, orr, ha, hr, hc, hna, hnr, .undefined, ?_⟩
  have hA : outcome? (annealVerdict .safe .reborrow .tooBig ()) =
      some (.fault .undefined) :=
    congrArg outcome?
      (by decide +kernel :
        annealVerdict .safe .reborrow .tooBig () = some .undefinedBehavior)
  exact Option.some.inj (ha.symm.trans hA)

/-- The mode-sensitivity witness of the LeanMiri side is likewise a genuine
fault flip (`IsFaultFlip`), for every certified presentation. -/
theorem lmModeWitness_isFaultFlip_with
    (h : (sideLM verdictLM).check model = true) :
    ∀ ms, ((sideLM verdictLM).flipW model h) = some ms → ms.IsFaultFlip := by
  intro ms hms
  have hms' : ms = lmModeWitness_with verdictLM h := by
    have : some ms = some (lmModeWitness_with verdictLM h) := hms.symm
    exact Option.some.inj this
  subst hms'
  obtain ⟨oa, orr, ha, hr, hc, hna, hnr⟩ :=
    (lmModeWitness_with verdictLM h).flips
  refine ⟨oa, orr, ha, hr, hc, hna, hnr, .undefined, ?_⟩
  have hA : outcome? (annealVerdict .safe .reborrow .tooBig ()) =
      some (.fault .undefined) :=
    congrArg outcome?
      (by decide +kernel :
        annealVerdict .safe .reborrow .tooBig () = some .undefinedBehavior)
  exact Option.some.inj (ha.symm.trans hA)

/-- Identity front model over the wide-slice corpus (with `CodecLaws.id Nat`)
for non-vacuous fault-flip-preserving vertical and transitive composition. -/
def frontModel : Model Regime Prog Query Unit Nat Nat where
  evalA := annealVerdict
  codec := CodecLaws.id Nat
  progs := allProgs
  queries := allQueries
  choices := [()]
  progs_complete := model.progs_complete
  queries_complete := model.queries_complete
  choices_complete := model.choices_complete

/-- Machine-level view of the front model on the MiniRust modes. -/
def frontSideMR :
    Side Regime (MrMem × Regime) Prog Query Unit Nat Nat where
  toAnneal := sideMR.toAnneal
  gate := gateMR
  verdictR := fun m p q c => annealVerdict m.2 p q c
  rep := fun r => r
  modes := sideMR.modes
  modes_complete := sideMR.modes_complete
  wMode := sideMR.wMode
  okProg := sideMR.okProg
  okQuery := sideMR.okQuery
  okChoice := sideMR.okChoice
  faultProg := sideMR.faultProg
  faultQuery := sideMR.faultQuery
  faultChoice := sideMR.faultChoice
  flip := sideMR.flip

/-- Machine-level view of the front model on the LeanMiri modes. -/
def frontSideLM : Side Regime Regime Prog Query Unit Nat Nat where
  toAnneal := fun m => m
  gate := gateLM
  verdictR := annealVerdict
  rep := fun r => r
  modes := allRegimes
  modes_complete := fun m => by cases m <;> decide
  wMode := .safe
  okProg := .reborrow
  okQuery := .inBounds
  okChoice := ()
  faultProg := .reborrow
  faultQuery := .tooBig
  faultChoice := ()
  flip := some (.safe, .raw, .reborrow, .tooBig, ())

/-- Certificate of the front MiniRust view. -/
theorem frontSideMR_check : frontSideMR.check frontModel = true := by
  decide +kernel

/-- Certificate of the front LeanMiri view. -/
theorem frontSideLM_check : frontSideLM.check frontModel = true := by
  decide +kernel

/-- Front bundle of the wide-slice corpus. -/
def frontBundle :
    DualCorrespondenceBundle Regime Prog Query Nat Unit Nat
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  Corpus.bundle frontModel frontSideMR frontSideLM frontSideMR_check
    frontSideLM_check

/-- **Fault-flip-preserving vertical composition** (`compPreserveFaultMode`):
transports BOTH genuine `some ms` fault-flip witnesses (`safe` vs `raw` at
`tooBig`) WITHOUT using `ReverseTotal` on either authority. -/
def faultFlipComp_with
    (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle Regime Prog Query Nat Unit (Nat × Nat)
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  (bundleWith verdictLM h).compPreserveFaultMode (CodecLaws.id Nat)
    frontBundle.mrSim frontBundle.lmSim
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ hg => hg) (fun _ _ _ hg => hg)
    (fun _ _ hr => hr) (fun _ _ hr => hr)
    mrModeWitness_isFaultFlip (lmModeWitness_isFaultFlip_with verdictLM h)
    frontBundle.toAnnealMR frontBundle.toAnnealLM frontBundle.ExecAnneal
    frontBundle.anneal_exec_coherent

/-- **Fault-flip-preserving transitive composition**
(`transPreserveFaultMode`): transports both genuine fault-flip witnesses
across `frontBundle` without `ReverseTotal`. -/
def faultFlipTrans_with
    (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle Regime Prog Query Nat Unit (Nat × Nat)
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  frontBundle.transPreserveFaultMode (bundleWith verdictLM h)
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ hg => hg) (fun _ _ _ hg => hg)
    (fun _ => rfl) (fun _ => rfl)
    mrModeWitness_isFaultFlip (lmModeWitness_isFaultFlip_with verdictLM h)

/-- **Non-vacuous mixed-transport vertical composition**
(`compPreserveModeMixed`): transports MiniRust's genuine `some` fault-flip
witness via `.faultFlip` (no `ReverseTotal`) and LeanMiri's genuine `some`
mode witness via `.reverseTotal`. -/
def mixedComp_with
    (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle Regime Prog Query Nat Unit (Nat × Nat)
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  (bundleWith verdictLM h).compPreserveModeMixed (CodecLaws.id Nat)
    frontBundle.mrSim frontBundle.lmSim
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ hg => hg) (fun _ _ _ hg => hg)
    (fun _ _ hr => hr) (fun _ _ hr => hr)
    (.faultFlip mrModeWitness_isFaultFlip)
    (.reverseTotal
      (frontSideLM.reverseTotal frontModel
        (Bool.and_eq_true _ _ ▸ frontSideLM_check).1)
      (fun _ _ _ _ _ => rfl))
    frontBundle.toAnnealMR frontBundle.toAnnealLM frontBundle.ExecAnneal
    frontBundle.anneal_exec_coherent

/-- Both authorities retain genuine (`isSome = true`) mode-sensitivity
witnesses through `compPreserveFaultMode`, `transPreserveFaultMode`, and
non-vacuous `compPreserveModeMixed`. -/
theorem faultFlipComp_modeSensitive_with
    (h : (sideLM verdictLM).check model = true) :
    (faultFlipComp_with verdictLM h).mrFlip.modeSensitivity?.isSome = true ∧
      (faultFlipComp_with verdictLM h).lmFlip.modeSensitivity?.isSome =
        true ∧
      (faultFlipTrans_with verdictLM h).mrFlip.modeSensitivity?.isSome =
        true ∧
      (faultFlipTrans_with verdictLM h).lmFlip.modeSensitivity?.isSome =
        true ∧
      (mixedComp_with verdictLM h).mrFlip.modeSensitivity?.isSome = true ∧
      (mixedComp_with verdictLM h).lmFlip.modeSensitivity?.isSome = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Neither model is mode-invariant on the LeanMiri side. -/
theorem lm_not_mode_invariant_with
    (h : (sideLM verdictLM).check model = true) :
    (¬ ∀ m m' p q c out, ((sideLM verdictLM).rel model).ExecA m p q c out →
        ∃ c', ((sideLM verdictLM).rel model).ExecA m' p q c' out) ∧
    (¬ ∀ m m' p q c out, ((sideLM verdictLM).rel model).ExecR m p q c out →
        ∃ c', ((sideLM verdictLM).rel model).ExecR m' p q c' out) :=
  (lmModeWitness_with verdictLM h).not_mode_invariant

/-- Both flip-direction guards record mode sensitivity, as stored by
`FlipDirectionWitness.ofFaultAndMode`. -/
theorem modeSensitive_with
    (h : (sideLM verdictLM).check model = true) :
    (bundleWith verdictLM h).mrFlip.modeSensitivity?.isSome = true ∧
      (bundleWith verdictLM h).lmFlip.modeSensitivity? =
        (sideLM verdictLM).flipW model h :=
  ⟨rfl,
   FlipDirectionWitness.ofFaultAndMode_modeSensitivity?
    (bundleWith verdictLM h).lmSim ((sideLM verdictLM).positive model h)
    ((sideLM verdictLM).faultW model h) rfl
    ((sideLM verdictLM).flipW model h)⟩

/-- The flip-direction guard of the LeanMiri side: the verdict flips
between the in-bounds and the `isize::MAX` safe reborrow, which are
distinct inputs, and well-formedness is not input-invariant. -/
theorem lmFlip_guard_with
    (h : (sideLM verdictLM).check model = true) :
    ¬ ((bundleWith verdictLM h).lmFlip.pOk =
          (bundleWith verdictLM h).lmFlip.pFault ∧
        (bundleWith verdictLM h).lmFlip.qOk =
          (bundleWith verdictLM h).lmFlip.qFault) ∧
    (¬ ∀ p q p' q',
        (bundleWith verdictLM h).lmRel.WellFormedRef .safe p q →
        (bundleWith verdictLM h).lmRel.WellFormedRef .safe p' q') ∧
    (¬ ∀ m p q c out, (bundleWith verdictLM h).lmRel.SupportGate m p q →
        (bundleWith verdictLM h).lmRel.ExecA m p q c out →
        ∃ a, out = .normal a) :=
  ⟨(bundleWith verdictLM h).lmFlip.inputs_ne,
   (bundleWith verdictLM h).lmFlip.not_input_invariant.2,
   (bundleWith verdictLM h).lmFlip.not_constant_outcome.1⟩

/-- Out-of-bounds indexing: a second fault-equivalence witness, on the
LeanMiri side. -/
def lmIndexOobFault_with
    (h : (sideLM verdictLM).check model = true) :
    FaultEquivWitness ((sideLM verdictLM).rel model) :=
  (sideLM verdictLM).faultAt model (sideLM_sim_with verdictLM h) .raw
    .indexRead .oobIndex () rfl
    (show isFaultV (annealVerdict .raw .indexRead .oobIndex ()) = true by
      decide +kernel)

/-- The out-of-bounds index is ill-formed in both models. -/
theorem lmIndexOob_not_wellFormed_with
    (h : (sideLM verdictLM).check model = true) :
    ¬ ((sideLM verdictLM).rel model).WellFormedAnneal .raw .indexRead
        .oobIndex ∧
      ¬ ((sideLM verdictLM).rel model).WellFormedRef .raw .indexRead
        .oobIndex :=
  (lmIndexOobFault_with verdictLM h).not_wellFormed

/-- In-bounds `size_of_val`: a second positive witness, on the LeanMiri
side, well-formed in the reference model too. -/
def lmSizeOfValPositive_with
    (h : (sideLM verdictLM).check model = true) :
    PositiveWitness ((sideLM verdictLM).rel model) :=
  (sideLM verdictLM).positiveAt model (sideLM_sim_with verdictLM h) .raw
    .sizeOfVal .inBounds () rfl
    (show isReturn (annealVerdict .raw .sizeOfVal .inBounds ()) = true by
      decide +kernel)
    (show ([()].all fun c' =>
        !isFaultV (annealVerdict .raw .sizeOfVal .inBounds c')) = true by
      decide +kernel)

/-- The positive witness inhabits the antecedent of the correspondence
claim and is well-formed in the reference model. -/
theorem lmSizeOfVal_wellFormed_with
    (h : (sideLM verdictLM).check model = true) :
    (∃ m p q, ((sideLM verdictLM).rel model).SupportGate m p q ∧
        ((sideLM verdictLM).rel model).WellFormedAnneal m p q) ∧
      ((sideLM verdictLM).rel model).WellFormedRef .raw .sizeOfVal
        .inBounds :=
  ⟨(lmSizeOfValPositive_with verdictLM h).antecedent_inhabited,
   (lmSizeOfValPositive_with verdictLM h).wellFormedRef
    (bundleWith verdictLM h).lmSim⟩

/-- Multi-step `from_raw_parts` / `ptr::metadata` / `to_raw_parts` /
`size_of_val` pipeline: a third positive witness on the LeanMiri side,
returning `12` in lockstep across Anneal and vendored `Miri`. -/
def lmPipelinePositive_with
    (h : (sideLM verdictLM).check model = true) :
    PositiveWitness ((sideLM verdictLM).rel model) :=
  (sideLM verdictLM).positiveAt model (sideLM_sim_with verdictLM h) .raw
    .pipeline .inBounds () rfl
    (show isReturn (annealVerdict .raw .pipeline .inBounds ()) = true by
      decide +kernel)
    (show ([()].all fun c' =>
        !isFaultV (annealVerdict .raw .pipeline .inBounds c')) = true by
      decide +kernel)

/-- The multi-step pipeline is well-formed in the LeanMiri authority and
returns `12`. -/
theorem lmPipeline_wellFormed_with
    (h : (sideLM verdictLM).check model = true) :
    ((sideLM verdictLM).rel model).WellFormedRef .raw .pipeline .inBounds ∧
      verdictLM .raw .pipeline .inBounds () = some (.returns 12) := by
  refine ⟨(lmPipelinePositive_with verdictLM h).wellFormedRef
      (bundleWith verdictLM h).lmSim, ?_⟩
  have hcp := (sideLM verdictLM).simCheck_spec model
    (sideLM_sim_with verdictLM h) .raw .pipeline .inBounds () rfl
  obtain ⟨oa, orr, ha, hr, hc⟩ := couplesB_sound hcp
  have ha12 : outcome? (annealVerdict .raw .pipeline .inBounds ()) =
      some (.normal 12) :=
    congrArg outcome?
      (by decide +kernel :
        annealVerdict .raw .pipeline .inBounds () = some (.returns 12))
  have hoa : oa = .normal 12 := Option.some.inj (ha.symm.trans ha12)
  subst hoa
  obtain ⟨r, horr, hrep⟩ := hc.normal_anneal_to_ref 12 rfl
  subst horr
  have h12 : r = 12 := halvesCodec.encode_injective hrep
  subst h12
  exact outcome?_injective hr

end Derived

/-- Tree Borrows `Disabled` dereference: a fault-equivalence witness on
the MiniRust side at `TreeBorrowsMemory`. -/
def mrDisabledDerefFault : FaultEquivWitness (sideMR.rel model) :=
  sideMR.faultAt model sideMR_sim (.treeBorrows, .raw) .disabledDeref
    .inBounds () rfl (by decide +kernel)

/-- Non-dereferencing `ptr::metadata` on the same parent-write-disabled wide
pointer: a positive witness on the MiniRust side at `TreeBorrowsMemory`,
contrasting directly with `mrDisabledDerefFault`. -/
def mrDisabledMetadataPositive : PositiveWitness (sideMR.rel model) :=
  sideMR.positiveAt model sideMR_sim (.treeBorrows, .raw) .disabledMetadata
    .inBounds () rfl (by decide +kernel) (by decide +kernel)

/-- Direct contrast on a Tree Borrows `Disabled` wide pointer: dereferencing
it is UB in both Anneal and MiniRust (`TreeBorrowsMemory`), whereas
non-dereferencing `ptr::metadata` succeeds returning `4` in Anneal,
`BasicMemory`, and `TreeBorrowsMemory`. -/
theorem disabledDeref_vs_disabledMetadata_contrast :
    annealVerdict .raw .disabledDeref .inBounds () =
        some .undefinedBehavior ∧
      mrVerdict (.treeBorrows, .raw) .disabledDeref .inBounds () =
        some .undefinedBehavior ∧
      annealVerdict .raw .disabledMetadata .inBounds () =
        some (.returns 4) ∧
      mrVerdict (.treeBorrows, .raw) .disabledMetadata .inBounds () =
        some (.returns 4) ∧
      mrVerdict (.basic, .raw) .disabledMetadata .inBounds () =
        some (.returns 4) := by
  decide +kernel

/-- The `from_raw_parts` / `to_raw_parts` / `ptr::metadata` round trip: a
positive witness on the MiniRust side at `TreeBorrowsMemory`. -/
def mrRoundTripPositive : PositiveWitness (sideMR.rel model) :=
  sideMR.positiveAt model sideMR_sim (.treeBorrows, .raw) .roundTrip
    .inBounds () rfl (by decide +kernel) (by decide +kernel)

/-- The round trip returns `46` in the trusted machine and in both
MiniRust memory models. -/
theorem roundTrip_three_way :
    annealVerdict .raw .roundTrip .inBounds () = some (.returns 46) ∧
      mrVerdict (.basic, .raw) .roundTrip .inBounds () =
        some (.returns 46) ∧
      mrVerdict (.treeBorrows, .raw) .roundTrip .inBounds () =
        some (.returns 46) := by
  decide +kernel

/-! ### B.8 Surface instances at the reference table -/

/-- Cross-authority fault equivalence of the surface bundle. -/
theorem safe_tooBig_fault_equiv :
    (∃ c, bundle.mrRel.ExecR (.basic, .safe) .reborrow .tooBig c
        (.fault .undefined)) ↔
      (∃ c, bundle.lmRel.ExecR .safe .reborrow .tooBig c
        (.fault .undefined)) :=
  safe_tooBig_fault_equiv_with lmReference sideLM_reference_check

/-- The surface bundle is mode-sensitive on both authorities. -/
theorem bundle_modeSensitive :
    bundle.mrFlip.modeSensitivity?.isSome = true ∧
      bundle.lmFlip.modeSensitivity?.isSome = true :=
  ⟨rfl, rfl⟩

/-- The surface bundle records reverse totality on both authorities. -/
theorem bundle_reverseTotal :
    bundle.mrSim.reverse_total?.isSome = true ∧
      bundle.lmSim.reverse_total?.isSome = true :=
  ⟨rfl, rfl⟩

end WideSlice

/-! ### B.9 The deterministic wide-slice bundle (`fromDetEquiv`) -/

namespace WideSlice

open Anneal.DualCorrespondenceBundle
open Corpus

/-- The wide-slice bundle built with `fromDetEquiv`: the trusted machine as
a deterministic evaluator against the total evaluators of MiniRust and of
any certified LeanMiri presentation. -/
def detBundleWith
    (verdictLM : Regime → Prog → Query → Unit → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle Regime Prog Query Nat Unit (Nat × Nat)
      (MrMem × Regime) Unit Nat Unit Regime Unit Nat Unit :=
  Corpus.detBundle model sideMR (sideLM verdictLM) ()
    (fun _ _ _ _ => rfl) sideMR_check h

/-- The deterministic bundle records reverse totality and is productive
on both sides of both authorities. -/
theorem detBundle_spec_with
    (verdictLM : Regime → Prog → Query → Unit → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    ((detBundleWith verdictLM h).mrSim.reverse_total?.isSome = true ∧
      (detBundleWith verdictLM h).lmSim.reverse_total?.isSome = true) ∧
    ((detBundleWith verdictLM h).mrRel.ProductiveBoth ∧
      (detBundleWith verdictLM h).lmRel.ProductiveBoth) :=
  ⟨⟨rfl, rfl⟩,
   Corpus.detBundle_productiveBoth model sideMR (sideLM verdictLM) ()
    (fun _ _ _ _ => rfl) sideMR_check h⟩

/-- Anneal productivity of the deterministic bundle, through the
underlying `fromEquiv` construction. -/
theorem detBundle_productiveAnneal_with
    (verdictLM : Regime → Prog → Query → Unit → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    (detBundleWith verdictLM h).mrRel.ProductiveAnneal ∧
      (detBundleWith verdictLM h).lmRel.ProductiveAnneal :=
  DualCorrespondenceBundle.fromEquiv_productiveAnneal _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- Exact behavioral equality of the deterministic bundle at the
`isize::MAX` safe reborrow, from the recorded reverse totality; its fault
component is the cross-model fault equivalence along every choice. -/
theorem detBundle_exact_with
    (verdictLM : Regime → Prog → Query → Unit → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) (k : CorrFaultKind) :
    (detBundleWith verdictLM h).lmRel.ExecA .safe .reborrow .tooBig ()
        (.fault k) ↔
      (detBundleWith verdictLM h).lmRel.ExecR .safe .reborrow .tooBig ()
        (.fault k) :=
  ((detBundleWith verdictLM h).lmSim.exactBehaviorEq_of_reverseTotal_isSome
    (m := .safe) (p := .reborrow) (q := .tooBig) rfl rfl).fault_iff () k

end WideSlice

/-! ## C. Family 2: IEEE-754 float casts and `nanChoices` modes

One Anneal model (the trusted `stepMirFn` on cast statements, extended by
the NaN-selection mode) is related to MiniRust (the fail-closed float
translation gate and the integer bit carriers of `MiniRustSpec.Interp`) and
to LeanMiri (the float engine of the vendored `Miri` interpreter). The
LeanMiri side of the surface bundle is the reference specification `Ref`, a
transliteration of that engine over bit patterns; the cross-root kernel
bridge proves the vendored engine equal to it on every corpus key. -/

namespace FloatCast

open Trusted.Effect Trusted.ITree Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Anneal.DualCorrespondenceBundle
open Corpus

/-! ### C.1 Reference specification of the vendored float engine -/

namespace Ref

/-- Binary interchange format. -/
inductive Fmt : Type where
  /-- `f32`. -/
  | binary32
  /-- `f64`. -/
  | binary64
  deriving DecidableEq

/-- Total width in bits. -/
def Fmt.width : Fmt → Nat
  | .binary32 => 32
  | .binary64 => 64

/-- Exponent field width. -/
def Fmt.exponentBits : Fmt → Nat
  | .binary32 => 8
  | .binary64 => 11

/-- Fraction field width. -/
def Fmt.fractionBits (f : Fmt) : Nat := f.width - f.exponentBits - 1

/-- Exponent bias. -/
def Fmt.bias (f : Fmt) : Nat := 2 ^ (f.exponentBits - 1) - 1

/-- Minimum unbiased exponent. -/
def Fmt.minExponent (f : Fmt) : Int := 1 - Int.ofNat f.bias

/-- Maximum unbiased exponent. -/
def Fmt.maxExponent (f : Fmt) : Int := Int.ofNat f.bias

/-- Class of a decoded float. -/
inductive Class : Type where
  /-- Finite value `n / d`. -/
  | finite (n d : Nat)
  /-- Infinity. -/
  | infinite
  /-- NaN with fraction `payload`. -/
  | nan (payload : Nat)
  deriving DecidableEq

/-- Decoded float: sign and class. -/
structure Decoded : Type where
  /-- Sign bit. -/
  negative : Bool
  /-- Class. -/
  value : Class
  deriving DecidableEq

/-- Scale `n / d` by `2 ^ e`. -/
def powScale (n d : Nat) (e : Int) : Nat × Nat :=
  if e ≥ 0 then (n * 2 ^ e.toNat, d) else (n, d * 2 ^ (-e).toNat)

/-- Bit pattern from sign, biased exponent, and fraction (128-bit carrier). -/
def encode (f : Fmt) (negative : Bool) (exponent fraction : Nat) : Nat :=
  ((if negative then 2 ^ (f.width - 1) else 0) +
    exponent * 2 ^ f.fractionBits + fraction) % 2 ^ 128

/-- Signed zero. -/
def zero (f : Fmt) (negative : Bool) : Nat := encode f negative 0 0

/-- Signed infinity. -/
def infinity (f : Fmt) (negative : Bool) : Nat :=
  encode f negative (2 ^ f.exponentBits - 1) 0

/-- The preferred (canonical, positive, quiet, zero-payload) NaN. -/
def preferredNaN (f : Fmt) : Nat :=
  encode f false (2 ^ f.exponentBits - 1) (2 ^ (f.fractionBits - 1))

/-- Decode a bit pattern; patterns wider than the format are rejected. -/
def decode (f : Fmt) (bits : Nat) : Option Decoded :=
  if bits ≥ 2 ^ f.width then none
  else
    let negative := bits / 2 ^ (f.width - 1) != 0
    let exponent := (bits / 2 ^ f.fractionBits) % 2 ^ f.exponentBits
    let fraction := bits % 2 ^ f.fractionBits
    if exponent == 2 ^ f.exponentBits - 1 then
      some ⟨negative, if fraction == 0 then .infinite else .nan fraction⟩
    else
      let significand :=
        if exponent == 0 then fraction else 2 ^ f.fractionBits + fraction
      let unbiased : Int :=
        if exponent == 0 then f.minExponent
        else Int.ofNat exponent - Int.ofNat f.bias
      let nd := powScale significand 1 (unbiased - Int.ofNat f.fractionBits)
      some ⟨negative, .finite nd.1 nd.2⟩

/-- Flip the sign bit. -/
def negate (f : Fmt) (bits : Nat) : Option Nat :=
  (decode f bits).map fun d =>
    (if d.negative then bits - 2 ^ (f.width - 1)
      else bits + 2 ^ (f.width - 1)) % 2 ^ 128

/-- Whether the pattern is a NaN. -/
def isNaN (f : Fmt) (bits : Nat) : Option Bool :=
  (decode f bits).map fun d =>
    match d.value with
    | .nan _ => true
    | _ => false

/-- Whether the pattern is a signaling NaN. -/
def isSignaling (f : Fmt) (bits : Nat) : Option Bool :=
  (decode f bits).map fun d =>
    match d.value with
    | .nan payload => decide (payload < 2 ^ (f.fractionBits - 1))
    | _ => false

/-- `floor (log2 (n / d))` for positive `n`, `d`. -/
def ratioExponent (n d : Nat) : Int :=
  if n ≥ d then Int.ofNat (n / d).log2
  else
    let k := (d / n).log2
    if n * 2 ^ k ≥ d then -(Int.ofNat k) else -(Int.ofNat k + 1)

/-- Quotient rounded to nearest, ties to even. -/
def roundQuotientEven (n d : Nat) : Nat :=
  let q := n / d
  let r := n % d
  if r * 2 > d || (r * 2 == d && q % 2 == 1) then q + 1 else q

/-- Correctly rounded encoding of `(-1)^negative * n / d`. -/
def roundRatio (f : Fmt) (negative : Bool) (n d : Nat) : Option Nat :=
  if d == 0 then none
  else if n == 0 then some (zero f negative)
  else
    let exponent := max (ratioExponent n d) f.minExponent
    if exponent > f.maxExponent then some (infinity f negative)
    else
      let sc := powScale n d (Int.ofNat f.fractionBits - exponent)
      let significand := roundQuotientEven sc.1 sc.2
      let se : Nat × Int :=
        if significand ≥ 2 ^ (f.fractionBits + 1) then
          (significand / 2, exponent + 1)
        else (significand, exponent)
      if se.2 > f.maxExponent then some (infinity f negative)
      else if se.1 < 2 ^ f.fractionBits then
        if se.2 != f.minExponent then none
        else some (encode f negative 0 se.1)
      else if se.1 ≥ 2 ^ (f.fractionBits + 1) then none
      else
        some (encode f negative (se.2 + Int.ofNat f.bias).toNat
          (se.1 - 2 ^ f.fractionBits))

/-- Float-to-float conversion; a NaN is quieted and its payload shifted. -/
def convert (src dst : Fmt) (bits : Nat) : Option Nat :=
  (decode src bits).bind fun d =>
    match d.value with
    | .finite n dd => roundRatio dst d.negative n dd
    | .infinite => some (infinity dst d.negative)
    | .nan payload =>
      let quiet := Nat.lor payload (2 ^ (src.fractionBits - 1))
      let shifted :=
        if dst.fractionBits ≥ src.fractionBits then
          quiet * 2 ^ (dst.fractionBits - src.fractionBits)
        else quiet / 2 ^ (src.fractionBits - dst.fractionBits)
      some (encode dst d.negative (2 ^ dst.exponentBits - 1)
        (Nat.lor shifted (2 ^ (dst.fractionBits - 1))))

/-- One input's contribution to the quieted and signaling candidates. -/
def nanStep (target : Fmt) (acc : List Nat × List Nat) (inp : Fmt × Nat) :
    Option (List Nat × List Nat) :=
  (isNaN inp.1 inp.2).bind fun isN =>
  (if isN then (convert inp.1 target inp.2).map (fun c => acc.1 ++ [c])
    else some acc.1).bind fun quieted =>
  (isSignaling inp.1 inp.2).bind fun isS =>
  if isS then
    (convert inp.1 target inp.2).bind fun c =>
    (decode target c).bind fun d =>
    match d.value with
    | .nan payload =>
      let lower := payload % 2 ^ (target.fractionBits - 1)
      some (quieted,
        if lower != 0 then
          acc.2 ++ [encode target d.negative (2 ^ target.exponentBits - 1)
            lower]
        else acc.2)
    | _ => none
  else some (quieted, acc.2)

/-- All NaN results permitted for `inputs`: the preferred NaN, each quieted
input, each signaling input with a non-zero low payload, in both signs.
Deterministic mode permits only the preferred NaN. -/
def nanChoices (target : Fmt) (inputs : List (Fmt × Nat))
    (nondeterministic : Bool) : Option (List Nat) :=
  if !nondeterministic then some [preferredNaN target]
  else
    (inputs.foldlM (nanStep target) ([], [])).bind fun qs =>
    (preferredNaN target :: (qs.1 ++ qs.2)).foldlM
      (fun signed cand =>
        (negate target cand).map fun n => signed ++ [cand, n]) []

/-- NaN adjustment: a non-NaN result is kept; a NaN result becomes the
preferred NaN in deterministic mode and the candidate selected by the
oracle index `pick` (reduced modulo the candidate count) otherwise. -/
def adjustNaN (nondeterministic : Bool) (pick : Nat) (f : Fmt)
    (value : Nat) (inputs : List (Fmt × Nat)) : Option Nat :=
  (isNaN f value).bind fun isN =>
  if !isN then some value
  else
    (nanChoices f inputs nondeterministic).bind fun cands =>
    if !nondeterministic then some (preferredNaN f)
    else cands[pick % cands.length]?

/-- Signed numerator. -/
def signedNumerator (negative : Bool) (n : Nat) : Int :=
  if negative then -(Int.ofNat n) else Int.ofNat n

/-- Saturating float-to-integer conversion (NaN maps to zero). -/
def toInteger (f : Fmt) (bits : Nat) (width : Nat) (isSigned : Bool) :
    Option Int :=
  if width == 0 || width > 128 then none
  else
    (decode f bits).map fun d =>
      let minValue : Int := if isSigned then -(2 ^ (width - 1)) else 0
      let maxValue : Int :=
        if isSigned then 2 ^ (width - 1) - 1 else 2 ^ width - 1
      match d.value with
      | .nan _ => 0
      | .infinite => if d.negative then minValue else maxValue
      | .finite n dd =>
        max minValue (min maxValue (signedNumerator d.negative (n / dd)))

/-- Integer-to-float conversion, rounding to nearest even. -/
def fromInteger (f : Fmt) (value : Int) : Option Nat :=
  roundRatio f (decide (value < 0)) value.natAbs 1

end Ref

/-! ### C.2 Corpus: modes, programs, queries, and oracle picks -/

/-- NaN-selection mode (`floatNondeterministic`). -/
inductive NanMode : Type where
  /-- Deterministic: every NaN result is the preferred NaN. -/
  | deterministic
  /-- Nondeterministic: any candidate of `nanChoices` may be produced. -/
  | nondeterministic
  deriving DecidableEq

/-- The `floatNondeterministic` flag of a mode. -/
def NanMode.flag : NanMode → Bool
  | .deterministic => false
  | .nondeterministic => true

/-- Corpus programs: one cast statement each. -/
inductive Prog : Type where
  /-- `_0 = copy _1 as f64 (FloatToFloat)`, `_1 : f32`. -/
  | f32ToF64
  /-- `_0 = copy _1 as f32 (FloatToFloat)`, `_1 : f64`. -/
  | f64ToF32
  /-- `_0 = copy _1 as i32 (FloatToInt)`, `_1 : f32`. -/
  | f32ToI32
  /-- `_0 = copy _1 as f32 (IntToFloat)`, `_1 : i32`. -/
  | i32ToF32
  /-- `_0 = copy _1 as i32 (Transmute)`, `_1 : u32`: 32-bit bit carrier. -/
  | bitsU32ToI32
  /-- `_0 = copy _1 as i64 (Transmute)`, `_1 : u64`: 64-bit bit carrier. -/
  | bitsU64ToI64
  /-- `_0 = copy _1 as u64 (FloatToInt)`, `_1 : f64`: unsigned saturation. -/
  | f64ToU64
  /-- `_0 = copy _1 as f64 (IntToFloat)`, `_1 : u64`: rounds above `2^53`. -/
  | u64ToF64
  /-- `_0 = copy _1 as f32 (FloatToFloat)`, `_1 : f16`. -/
  | f16ToF32
  /-- `_0 = copy _1 as f32 (FloatToFloat)`, `_1 : f128`. -/
  | f128ToF32
  /-- A `FloatToInt` cast whose source local is uninitialized. -/
  | uninitCast
  deriving DecidableEq

/-- Corpus queries: the source bit pattern. -/
inductive Query : Type where
  /-- `1.5`. -/
  | onePointFive
  /-- Quiet NaN with payload bit `0` set. -/
  | quietNaN
  /-- Signaling NaN with payload bit `0` set. -/
  | signalingNaN
  /-- Negative infinity. -/
  | negInfinity
  /-- `3.0e9` (above `i32::MAX`). -/
  | threeBillion
  deriving DecidableEq

/-- Oracle picks for NaN selection. -/
inductive Pick : Type where
  | p0 | p1 | p2 | p3 | p4 | p5
  deriving DecidableEq

/-- Index of a pick. -/
def Pick.toNat : Pick → Nat
  | .p0 => 0
  | .p1 => 1
  | .p2 => 2
  | .p3 => 3
  | .p4 => 4
  | .p5 => 5

/-- All NaN modes. -/
def allModes : List NanMode := [.deterministic, .nondeterministic]

/-- All programs. -/
def allProgs : List Prog :=
  [.f32ToF64, .f64ToF32, .f32ToI32, .i32ToF32, .bitsU32ToI32, .bitsU64ToI64,
    .f64ToU64, .u64ToF64, .f16ToF32, .f128ToF32, .uninitCast]

/-- All queries. -/
def allQueries : List Query :=
  [.onePointFive, .quietNaN, .signalingNaN, .negInfinity, .threeBillion]

/-- All picks. -/
def allPicks : List Pick := [.p0, .p1, .p2, .p3, .p4, .p5]

/-- The query as an `f32` (equivalently `u32` / `i32`) bit pattern. -/
def Query.bits32 : Query → Nat
  | .onePointFive => 0x3fc00000
  | .quietNaN => 0x7fc00001
  | .signalingNaN => 0x7f800001
  | .negInfinity => 0xff800000
  | .threeBillion => 0x4f32d05e

/-- The query as an `f64` (equivalently `u64` / `i64`) bit pattern; the NaN
payloads carry bit `29` (`0x20000000`), which survives the 29-bit narrowing
shift to `f32` so narrowing preserves a non-canonical quiet payload and all
six signaling-NaN candidates. -/
def Query.bits64 : Query → Nat
  | .onePointFive => 0x3ff8000000000000
  | .quietNaN => 0x7ff8000020000000
  | .signalingNaN => 0x7ff0000020000000
  | .negInfinity => 0xfff0000000000000
  | .threeBillion => 0x41e65a0bc0000000

/-- Source bit pattern of a program on a query. -/
def srcBits (p : Prog) (q : Query) : Nat :=
  match p with
  | .f64ToF32 | .bitsU64ToI64 | .f64ToU64 | .u64ToF64 => q.bits64
  | .f16ToF32 => 0x3e00
  | .f128ToF32 => 0x3fff8000000000000000000000000000
  | _ => q.bits32

/-- Source and target formats of the float-to-float programs. -/
def f2fFormats : Prog → Option (Ref.Fmt × Ref.Fmt)
  | .f32ToF64 => some (.binary32, .binary64)
  | .f64ToF32 => some (.binary64, .binary32)
  | _ => none

/-! ### C.3 Anneal: trusted cast statements and the NaN-selection mode -/

/-- Scalar type of the given kind. -/
def scalarTy (k : RigidTy) : Ty := { kind := k, layoutIdx := 0 }

/-- Source type, source byte width, target type, and cast kind. -/
def castShape : Prog → Ty × Nat × Ty × CastKind
  | .f32ToF64 =>
    (scalarTy (.float .f32), 4, scalarTy (.float .f64), .floatToFloat)
  | .f64ToF32 =>
    (scalarTy (.float .f64), 8, scalarTy (.float .f32), .floatToFloat)
  | .f32ToI32 =>
    (scalarTy (.float .f32), 4, scalarTy (.int .i32), .floatToInt)
  | .i32ToF32 =>
    (scalarTy (.int .i32), 4, scalarTy (.float .f32), .intToFloat)
  | .bitsU32ToI32 =>
    (scalarTy (.uint .u32), 4, scalarTy (.int .i32), .transmute)
  | .bitsU64ToI64 =>
    (scalarTy (.uint .u64), 8, scalarTy (.int .i64), .transmute)
  | .f64ToU64 =>
    (scalarTy (.float .f64), 8, scalarTy (.uint .u64), .floatToInt)
  | .u64ToF64 =>
    (scalarTy (.uint .u64), 8, scalarTy (.float .f64), .intToFloat)
  | .f16ToF32 =>
    (scalarTy (.float .f16), 2, scalarTy (.float .f32), .floatToFloat)
  | .f128ToF32 =>
    (scalarTy (.float .f128), 16, scalarTy (.float .f32), .floatToFloat)
  | .uninitCast =>
    (WideSlice.usizeTy, 8, WideSlice.usizeTy, .floatToInt)

/-- Target byte width of each cast program. -/
def dstBytes : Prog → Nat
  | .f32ToF64 | .bitsU64ToI64 | .f64ToU64 | .u64ToF64 | .uninitCast => 8
  | .f64ToF32 | .f32ToI32 | .i32ToF32 | .bitsU32ToI32 | .f16ToF32
  | .f128ToF32 => 4

/-- The cast rvalue of a program (`_0 = copy _1 as T`). -/
def castRvalue (p : Prog) : Rvalue :=
  .cast (castShape p).2.2.2 (.copy ⟨1, []⟩) (castShape p).2.2.1

/-- Local declarations of a cast body: `_0 : target`, `_1 : source`. -/
def castDecls (p : Prog) : List LocalDecl :=
  [ { mutability := .mut, ty := (castShape p).2.2.1, debugName := none }
  , { mutability := .not, ty := (castShape p).1, debugName := none } ]

/-- Single-statement cast body. -/
def castBody (p : Prog) : CapturedMir :=
  { defPath := "float_cast"
    phase := .runtimePostCleanup
    role := .subject
    argCount := 0
    localDecls := castDecls p
    basicBlocks :=
      [ { statements := [ ⟨.assign ⟨0, []⟩ (castRvalue p), "s0"⟩ ]
          terminator := ⟨.return_, "t0"⟩
          isCleanup := false } ]
    fnAbi := WideSlice.fnAbiOf 8
    layouts := emptyLayoutTable
    allocations := [] }

/-- Initial state of a cast body on a query. -/
def castInit (p : Prog) (q : Query) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals :=
          [.uninit, .init (.scalar ⟨srcBits p q, (castShape p).2.1⟩)] }
    memory := emptyMemory }

/-- The uninitialized-source cast over the four-local wide-slice frame:
`_0 = copy _0 as usize (FloatToInt)` with `_0` uninitialized. Both machines
fault on the operand read. -/
def uninitCastBody : CapturedMir :=
  WideSlice.frameBody "float_cast_uninit" WideSlice.usizeTy
    (WideSlice.fnAbiOf 8) (.cast .floatToInt (.copy ⟨0, []⟩) WideSlice.usizeTy)

/-- Verdict of the trusted machine on a cast statement. -/
def trustedVerdict (p : Prog) (q : Query) : Option (Verdict Nat) :=
  match p with
  | .uninitCast =>
    WideSlice.frameVerdict uninitCastBody (WideSlice.frameInit 3 1)
  | _ => WideSlice.frameVerdict (castBody p) (castInit p q)

/-- On every cast program supported by Anneal, executing the trusted machine
writes a scalar whose byte width equals `dstBytes p`. -/
theorem trusted_dstBytes_eq :
    ∀ p ∈ [Prog.f32ToF64, .f64ToF32, .f32ToI32, .i32ToF32,
           .bitsU32ToI32, .bitsU64ToI64, .f64ToU64, .u64ToF64],
      match stepMirFn (castBody p) (castInit p .onePointFive) with
      | .step s₁ =>
        match s₁.frame.locals with
        | .init (.scalar sc) :: _ => sc.sizeBytes = dstBytes p
        | _ => False
      | _ => False := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- Verdict of the Anneal model: the trusted machine, with a NaN result of
a float-to-float cast replaced by the NaN the mode selects. The trusted
machine's own NaN is the payload-preserving candidate
(`trusted_nan_is_candidate_two`). -/
def annealVerdict (mode : NanMode) (p : Prog) (q : Query) (c : Pick) :
    Option (Verdict Nat) :=
  match trustedVerdict p q, f2fFormats p with
  | some (.returns bits), some (src, dst) =>
    (Ref.adjustNaN mode.flag c.toNat dst bits [(src, srcBits p q)]).map
      Verdict.returns
  | v, _ => v

/-! ### C.4 MiniRust: translation gate and integer bit carriers -/

section MiniRust

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr
open MiniRustSpec.Interp MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness

/-- MiniRust 64-bit unsigned integer type (`u64`). -/
def u64It : Gen.IntType := ⟨.Unsigned, ⟨8⟩⟩

/-- MiniRust 64-bit signed integer type (`i64`). -/
def i64It : Gen.IntType := ⟨.Signed, ⟨8⟩⟩

/-- MiniRust 8-bit unsigned integer type (`u8`). -/
def u8It : Gen.IntType := ⟨.Unsigned, ⟨1⟩⟩

/-- Verdict of a MiniRust computation returning a `w`-bit integer value,
as its two's-complement bit pattern. -/
def carrierVerdictW {M : Type} [Memory M] (mod : Nat) :
    Interp (Gen.Value M) → Option (Verdict Nat)
  | .ok (.Int i) => some (.returns (i % mod).toNat)
  | .ok _ => none
  | .error (.ub _) => some .undefinedBehavior
  | .error (.unsupported _) => some .unsupported
  | .error _ => none

/-- Verdict of MiniRust's typed load of eight uninitialized bytes at
`usize`: no value decodes, which is undefined behavior. -/
def uninitLoadVerdict : Interp (Option Val) → Option (Verdict Nat)
  | .ok none => some .undefinedBehavior
  | _ => none

/-- Verdict of MiniRust on each corpus key: the 32-bit and 64-bit carriers
are transmuted (`u32` to `i32`, `u64` to `i64`) in the chosen memory model,
the uninitialized load is undefined behavior, and every float cast is
rejected by the translation (`translateRvalue`), which is the fail-closed
`unsupported` verdict. -/
def mrVerdict (mem : WideSlice.MrMem) (p : Prog) (q : Query) (_c : Pick) :
    Option (Verdict Nat) :=
  match p, mem with
  | .bitsU32ToI32, .basic =>
    carrierVerdictW (M := BM) 4294967296
      (Interp.transmute (.Int (Int.ofNat q.bits32)) (.Int u32) (.Int i32))
  | .bitsU32ToI32, .treeBorrows =>
    carrierVerdictW (M := TBM) 4294967296
      (transmuteM (M := TBM) (.Int (Int.ofNat q.bits32)) (.Int u32)
        (.Int i32))
  | .bitsU64ToI64, .basic =>
    carrierVerdictW (M := BM) 18446744073709551616
      (Interp.transmute (.Int (Int.ofNat q.bits64)) (.Int u64It)
        (.Int i64It))
  | .bitsU64ToI64, .treeBorrows =>
    carrierVerdictW (M := TBM) 18446744073709551616
      (transmuteM (M := TBM) (.Int (Int.ofNat q.bits64)) (.Int u64It)
        (.Int i64It))
  | .uninitCast, _ =>
    uninitLoadVerdict
      (Type.decode (.Int ⟨.Unsigned, ⟨8⟩⟩) (List.replicate 8 .Uninit))
  | p, _ =>
    match translateRvalue (layouts := ⟨64, true, []⟩) (decls := castDecls p)
      (targetTy := none) (castRvalue p) with
    | none => some .unsupported
    | some _ => none

end MiniRust

/-- MiniRust fragment: the 32-bit and 64-bit carriers, the uninitialized
load, and the `f16` / `f128` casts that both sides reject. The `f32` / `f64`
casts are excluded: MiniRust has no float type, so its verdict there is
`unsupported` while Anneal returns (`gateMR_exclusion_is_tight`). -/
def gateMR (_m : WideSlice.MrMem) (p : Prog) (q : Query) : Bool :=
  match p with
  | .bitsU32ToI32 => true
  | .bitsU64ToI64 => true
  | .uninitCast => decide (q = .onePointFive)
  | .f16ToF32 => decide (q = .onePointFive)
  | .f128ToF32 => decide (q = .onePointFive)
  | _ => false

/-! ### C.5 LeanMiri: the reference specification on the corpus -/

/-- Two's-complement bit pattern of an integer at `w` bits. -/
def twosComplement (w : Nat) (i : Int) : Nat := (i % (2 ^ w : Nat)).toNat

/-- Signed value of a `w`-bit pattern. -/
def signedOfBits (w : Nat) (b : Nat) : Int :=
  if b < 2 ^ (w - 1) then Int.ofNat b else Int.ofNat b - (2 ^ w : Nat)

/-- Reference verdict of the vendored float engine on each corpus key. -/
def lmReference (mode : NanMode) (p : Prog) (q : Query) (c : Pick) :
    Option (Verdict Nat) :=
  match p with
  | .f32ToF64 =>
    ((Ref.convert .binary32 .binary64 q.bits32).bind fun r =>
      Ref.adjustNaN mode.flag c.toNat .binary64 r
        [(.binary32, q.bits32)]).map Verdict.returns
  | .f64ToF32 =>
    ((Ref.convert .binary64 .binary32 q.bits64).bind fun r =>
      Ref.adjustNaN mode.flag c.toNat .binary32 r
        [(.binary64, q.bits64)]).map Verdict.returns
  | .f32ToI32 =>
    (Ref.toInteger .binary32 q.bits32 32 true).map fun i =>
      Verdict.returns (twosComplement 32 i)
  | .i32ToF32 =>
    (Ref.fromInteger .binary32 (signedOfBits 32 q.bits32)).map
      Verdict.returns
  | .bitsU32ToI32 =>
    some (.returns (twosComplement 32 (signedOfBits 32 q.bits32)))
  | .bitsU64ToI64 =>
    some (.returns (twosComplement 64 (signedOfBits 64 q.bits64)))
  | .f64ToU64 =>
    (Ref.toInteger .binary64 q.bits64 64 false).map fun i =>
      Verdict.returns (twosComplement 64 i)
  | .u64ToF64 =>
    (Ref.fromInteger .binary64 (Int.ofNat q.bits64)).map Verdict.returns
  | .uninitCast => some .undefinedBehavior
  | .f16ToF32 => none
  | .f128ToF32 => none

/-- LeanMiri fragment: every `f32` / `f64` cast, the 32-bit and 64-bit
carriers, and the uninitialized-source cast. The `f16` and `f128` casts are
excluded: the vendored engine converts `binary16` and `binary128`, where
Anneal fails closed (proved tight in the cross-root kernel bridge). -/
def gateLM (_m : NanMode) (p : Prog) (q : Query) : Bool :=
  match p with
  | .f16ToF32 | .f128ToF32 => false
  | .uninitCast => decide (q = .onePointFive)
  | _ => true

/-! ### C.6 Model, sides, and certificates -/

/-- The Anneal side of the float-cast corpus. -/
def model : Model NanMode Prog Query Pick Nat (Nat × Nat) where
  evalA := annealVerdict
  codec := halvesCodec
  progs := allProgs
  queries := allQueries
  choices := allPicks
  progs_complete := fun p => by cases p <;> decide
  queries_complete := fun q => by cases q <;> decide
  choices_complete := fun c => by cases c <;> decide

/-- The MiniRust side: the NaN bit carrier as positive witness and the
`f16` fail-closed `unsupported` cast as fault witness. MiniRust is
NaN-mode agnostic and is matched with the deterministic Anneal mode. -/
def sideMR :
    Side NanMode WideSlice.MrMem Prog Query Pick Nat (Nat × Nat) where
  toAnneal := fun _ => .deterministic
  gate := gateMR
  verdictR := mrVerdict
  rep := halves
  modes := [.basic, .treeBorrows]
  modes_complete := fun m => by cases m <;> decide
  wMode := .basic
  okProg := .bitsU32ToI32
  okQuery := .quietNaN
  okChoice := .p0
  faultProg := .f16ToF32
  faultQuery := .onePointFive
  faultChoice := .p0
  flip := none

/-- The LeanMiri side over an arbitrary presentation of the authority:
`1.5f32 as f64` as positive witness, the uninitialized source as fault
witness, and the payload-preserving quiet NaN (oracle pick `2`) as the
outcome reachable in nondeterministic mode only. -/
def sideLM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat)) :
    Side NanMode NanMode Prog Query Pick Nat (Nat × Nat) where
  toAnneal := fun m => m
  gate := gateLM
  verdictR := verdictLM
  rep := halves
  modes := allModes
  modes_complete := fun m => by cases m <;> decide
  wMode := .nondeterministic
  okProg := .f32ToF64
  okQuery := .onePointFive
  okChoice := .p0
  faultProg := .uninitCast
  faultQuery := .onePointFive
  faultChoice := .p0
  flip :=
    some (.nondeterministic, .deterministic, .f32ToF64, .quietNaN, .p2)

/-- Kernel-evaluated certificate of the MiniRust side. -/
theorem sideMR_check : sideMR.check model = true := by decide +kernel

/-- Kernel-evaluated certificate of the LeanMiri reference side. -/
theorem sideLM_reference_check : (sideLM lmReference).check model = true := by
  decide +kernel

/-- Float-cast bundle over any LeanMiri presentation that passes the
certificate. -/
def bundleWith
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat)
      WideSlice.MrMem Pick Nat Unit NanMode Pick Nat Unit :=
  Corpus.bundle model sideMR (sideLM verdictLM) sideMR_check h

/-- The surface float-cast bundle (LeanMiri presented by `Ref`). -/
def bundle :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat)
      WideSlice.MrMem Pick Nat Unit NanMode Pick Nat Unit :=
  bundleWith lmReference sideLM_reference_check

/-! ### C.7 Presenting the LeanMiri authority by its own observations -/

/-- LeanMiri corpus keys: every mode, LeanMiri program, query, and pick
(the uninitialized-source cast at one query only). -/
def lmKeys : List (NanMode × Prog × Query × Pick) :=
  allModes.flatMap fun m =>
    ([Prog.f32ToF64, .f64ToF32, .f32ToI32, .i32ToF32, .bitsU32ToI32,
        .bitsU64ToI64, .f64ToU64, .u64ToF64].flatMap
      fun p => allQueries.flatMap fun q => allPicks.map fun c =>
        (m, p, q, c)) ++
    allPicks.map fun c => (m, .uninitCast, .onePointFive, c)

/-- `lmReference` on a key. -/
def lmReferenceAt (k : NanMode × Prog × Query × Pick) :
    Option (Verdict Nat) :=
  lmReference k.1 k.2.1 k.2.2.1 k.2.2.2

/-- Diagnostic of the vendored interpreter on the uninitialized source. -/
def lmUninitMessage : String := "read of uninitialized local"

/-- Whether a program returns a 64-bit scalar. -/
def returns64 : Prog → Bool
  | .f32ToF64 | .bitsU64ToI64 | .f64ToU64 | .u64ToF64 => true
  | _ => false

/-- The distinct normal returns of `lmReference` on the LeanMiri keys, with
their widths (`true`: 64-bit). -/
def lmReturnDenotations : List (Nat × Bool) :=
  (lmKeys.filterMap fun k =>
    match lmReferenceAt k with
    | some (.returns n) => some (n, returns64 k.2.1)
    | _ => none).eraseDups

/-- The LeanMiri authority assembled from `Cast.cast` and `Step.step`
observation functions: `widenObs bits flag pick` / `narrowObs bits flag pick`
run `FloatToFloat` under the `floatNondeterministic` flag and oracle pick;
`toIntObs` / `toU64Obs`, `fromIntObs` / `fromU64Obs`, and `carrier32Obs` /
`carrier64Obs` run `FloatToInt` (to `i32` / `u64`), `IntToFloat` (from `i32`
/ `u64`), and 32/64-bit `Transmute` directly on raw bit patterns;
`uninitObs body` steps the uninitialized-source cast; `ret32` / `ret64` /
`ubObs` embed expected 4-byte scalars, 8-byte scalars, and diagnostics. -/
def authorityOf (Obs : Type) (decEq : DecidableEq Obs)
    (widenObs narrowObs : Nat → Bool → Nat → Obs)
    (toIntObs fromIntObs toU64Obs fromU64Obs carrier32Obs carrier64Obs :
      Nat → Obs)
    (uninitObs : CapturedMir → Obs) (ret32 ret64 : Nat → Obs)
    (ubObs : String → Obs) :
    ObsAuthority (NanMode × Prog × Query × Pick) Nat where
  Obs := Obs
  decEq := decEq
  observe := fun k =>
    match k.2.1 with
    | .f32ToF64 => some (widenObs k.2.2.1.bits32 k.1.flag k.2.2.2.toNat)
    | .f64ToF32 => some (narrowObs k.2.2.1.bits64 k.1.flag k.2.2.2.toNat)
    | .f32ToI32 => some (toIntObs k.2.2.1.bits32)
    | .i32ToF32 => some (fromIntObs k.2.2.1.bits32)
    | .bitsU32ToI32 => some (carrier32Obs k.2.2.1.bits32)
    | .bitsU64ToI64 => some (carrier64Obs k.2.2.1.bits64)
    | .f64ToU64 => some (toU64Obs k.2.2.1.bits64)
    | .u64ToF64 => some (fromU64Obs k.2.2.1.bits64)
    | .uninitCast =>
      match k.2.2.1 with
      | .onePointFive => some (uninitObs uninitCastBody)
      | _ => none
    | _ => none
  denote :=
    (lmReturnDenotations.map fun d =>
      (.returns d.1, if d.2 then ret64 d.1 else ret32 d.1)) ++
    [(.undefinedBehavior, ubObs lmUninitMessage)]

/-- Verdict function of an authority. -/
def verdictOf (A : ObsAuthority (NanMode × Prog × Query × Pick) Nat) :
    NanMode → Prog → Query → Pick → Option (Verdict Nat) :=
  fun m p q c => A.verdict (m, p, q, c)

/-- Certificate of the LeanMiri side for an authority. -/
def checkOf (A : ObsAuthority (NanMode × Prog × Query × Pick) Nat) : Bool :=
  (sideLM (verdictOf A)).check model

/-- Agreement of an authority with `lmReference` on every LeanMiri key. -/
def matchesReference
    (A : ObsAuthority (NanMode × Prog × Query × Pick) Nat) : Bool :=
  A.matchesOn lmReferenceAt lmKeys

/-- `matchesReference` certifies that the authority's engine computes
exactly the reference specification `Ref` on every LeanMiri key. -/
theorem matchesReference_sound
    (A : ObsAuthority (NanMode × Prog × Query × Pick) Nat)
    (h : matchesReference A = true) :
    ∀ k, k ∈ lmKeys → A.verdict k = lmReferenceAt k :=
  A.matchesOn_sound lmReferenceAt lmKeys h

/-- Float-cast bundle over an authority presented by its observations. -/
def bundleOfAuthority
    (A : ObsAuthority (NanMode × Prog × Query × Pick) Nat)
    (h : checkOf A = true) :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat)
      WideSlice.MrMem Pick Nat Unit NanMode Pick Nat Unit :=
  bundleWith (verdictOf A) h

end FloatCast

/-! ### C.8 Theorems of the float-cast bundle -/

namespace FloatCast

open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Anneal.DualCorrespondenceBundle
open Corpus

/-- Simulation certificate of the MiniRust side. -/
theorem sideMR_sim : sideMR.simCheck model = true :=
  (Bool.and_eq_true _ _ ▸ sideMR_check).1

/-- `nanChoices`: four candidates for a quiet NaN input, six for a
signaling NaN input, and only the preferred NaN in deterministic mode. -/
theorem nanChoices_candidates :
    Ref.nanChoices .binary64 [(.binary32, 0x7fc00001)] true =
        some [0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000020000000,
          0xfff8000020000000] ∧
      Ref.nanChoices .binary64 [(.binary32, 0x7f800001)] true =
        some [0x7ff8000000000000, 0xfff8000000000000, 0x7ff8000020000000,
          0xfff8000020000000, 0x7ff0000020000000, 0xfff0000020000000] ∧
      Ref.nanChoices .binary64 [(.binary32, 0x7f800001)] false =
        some [0x7ff8000000000000] := by
  decide +kernel

/-- Narrowing `nanChoices` (`f64 → f32`): because `bits64` puts the NaN
payload in bit `29` (`0x20000000`), it survives the 29-bit narrowing shift
to yield four distinct quiet-NaN candidates, six distinct signaling-NaN
candidates, and a genuine deterministic-vs-nondeterministic mode flip. -/
theorem nanChoices_narrowing_candidates :
    Ref.nanChoices .binary32 [(.binary64, 0x7ff8000020000000)] true =
        some [0x7fc00000, 0xffc00000, 0x7fc00001, 0xffc00001] ∧
      Ref.nanChoices .binary32 [(.binary64, 0x7ff0000020000000)] true =
        some [0x7fc00000, 0xffc00000, 0x7fc00001, 0xffc00001,
          0x7f800001, 0xff800001] ∧
      Ref.nanChoices .binary32 [(.binary64, 0x7ff0000020000000)] false =
        some [0x7fc00000] ∧
      annealVerdict .deterministic .f64ToF32 .quietNaN .p2 =
        some (.returns 0x7fc00000) ∧
      annealVerdict .nondeterministic .f64ToF32 .quietNaN .p2 =
        some (.returns 0x7fc00001) := by
  decide +kernel

/-- The trusted machine's deterministic NaN is the payload-preserving
candidate: oracle pick `2` of the nondeterministic mode, for both widening
and narrowing NaN casts. -/
theorem trusted_nan_is_candidate_two :
    trustedVerdict .f32ToF64 .quietNaN =
        some (.returns 0x7ff8000020000000) ∧
      trustedVerdict .f64ToF32 .quietNaN = some (.returns 0x7fc00001) ∧
      annealVerdict .nondeterministic .f32ToF64 .quietNaN .p2 =
        trustedVerdict .f32ToF64 .quietNaN ∧
      annealVerdict .nondeterministic .f32ToF64 .signalingNaN .p2 =
        trustedVerdict .f32ToF64 .signalingNaN ∧
      annealVerdict .nondeterministic .f64ToF32 .quietNaN .p2 =
        trustedVerdict .f64ToF32 .quietNaN ∧
      annealVerdict .nondeterministic .f64ToF32 .signalingNaN .p2 =
        trustedVerdict .f64ToF32 .signalingNaN := by
  decide +kernel

/-- Deterministic mode canonicalizes every NaN result to the preferred
NaN, for every oracle pick. -/
theorem deterministic_canonicalizes (c : Pick) :
    annealVerdict .deterministic .f32ToF64 .quietNaN c =
        some (.returns 0x7ff8000000000000) ∧
      annealVerdict .deterministic .f32ToF64 .signalingNaN c =
        some (.returns 0x7ff8000000000000) := by
  cases c <;> decide +kernel

/-- Nondeterministic mode reaches all six candidates of the signaling
input, including the two that keep it signaling. -/
theorem nondeterministic_signaling_outcomes :
    allPicks.map (annealVerdict .nondeterministic .f32ToF64 .signalingNaN) =
      [some (.returns 0x7ff8000000000000),
        some (.returns 0xfff8000000000000),
        some (.returns 0x7ff8000020000000),
        some (.returns 0xfff8000020000000),
        some (.returns 0x7ff0000020000000),
        some (.returns 0xfff0000020000000)] := by
  decide +kernel

/-- The machine-level verdicts are the trusted cast functions, including
unsigned 64-bit casts (`f64ToU64`, `u64ToF64`) and both 32-bit and 64-bit
`evalByteCast` bit carriers. -/
theorem trusted_matches_cast_functions (q : Query) :
    trustedVerdict .f32ToI32 q =
        some (.returns
          (evalFloatToIntSaturating .binary32 q.bits32 (.signed .i32)
            .bits64).bits) ∧
      trustedVerdict .i32ToF32 q =
        some (.returns
          (evalIntToFloatRoundTiesToEven true 32 q.bits32 .binary32)) ∧
      trustedVerdict .f64ToU64 q =
        some (.returns
          (evalFloatToIntSaturating .binary64 q.bits64 (.unsigned .u64)
            .bits64).bits) ∧
      trustedVerdict .u64ToF64 q =
        some (.returns
          (evalIntToFloatRoundTiesToEven false 64 q.bits64 .binary64)) ∧
      trustedVerdict .f32ToF64 q =
        some (.returns
          (evalFloatToFloatRoundTiesToEven .binary32 .binary64 q.bits32)) ∧
      trustedVerdict .f64ToF32 q =
        some (.returns
          (evalFloatToFloatRoundTiesToEven .binary64 .binary32 q.bits64)) ∧
      trustedVerdict .bitsU32ToI32 q = some (.returns q.bits32) ∧
      trustedVerdict .bitsU64ToI64 q = some (.returns q.bits64) := by
  cases q <;> decide +kernel

/-- Little-endian `[u8; 4]` value in Anneal (non-recursive). -/
def annealLeBytes4 (bits : Nat) : List Value :=
  [.scalar ⟨bits % 256, 1⟩, .scalar ⟨(bits / 256) % 256, 1⟩,
   .scalar ⟨(bits / 65536) % 256, 1⟩, .scalar ⟨(bits / 16777216) % 256, 1⟩]

/-- Little-endian `[u8; 8]` value in Anneal (non-recursive). -/
def annealLeBytes8 (bits : Nat) : List Value :=
  annealLeBytes4 bits ++ annealLeBytes4 (bits / 4294967296)

/-- Byte-array layout `[u8; n]` for Anneal `evalByteCast`. -/
def byteArrayLayout (n : Nat) : TypeLayout :=
  { size := { bytes := n }
    align := { bytes := 1 }
    backendRepr := .memory
    fields := .array { bytes := 1 } n
    variants := .single 0
    isUninhabited := false }

/-- Primitive scalar layout of `n` bytes with primitive kind `p`. -/
def floatPrimLayout (n : Nat) (p : PrimitiveKind) : TypeLayout :=
  { size := { bytes := n }
    align := { bytes := n }
    backendRepr :=
      .scalar (.initialized p { start := 0, end_ := 2 ^ (8 * n) - 1 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Layout table carrying `f32` (1), `f64` (2), `[u8; 4]` (3), `[u8; 8]` (4). -/
def byteCarrierLayouts : LayoutTable :=
  { pointerBits := 64
    isLittleEndian := true
    entries :=
      [WideSlice.primLayout 4, floatPrimLayout 4 (.float 32),
       floatPrimLayout 8 (.float 64), byteArrayLayout 4,
       byteArrayLayout 8] }

/-- Direct `evalByteCast` witness on IEEE-754 bit carriers: `f32 ↔ [u8; 4]`
and `f64 ↔ [u8; 8]` preserve quiet and signaling NaN bit patterns verbatim. -/
theorem trusted_evalByteCast_byte_carriers :
    let f32Ty : Ty := { kind := .float .f32, layoutIdx := 1 }
    let f64Ty : Ty := { kind := .float .f64, layoutIdx := 2 }
    let b4Ty : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 3 }
    let b8Ty : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 4 }
    let d4 := [{ mutability := .mut, ty := b4Ty, debugName := none },
      { mutability := .not, ty := f32Ty, debugName := none }]
    let d4Rev := [{ mutability := .mut, ty := f32Ty, debugName := none },
      { mutability := .not, ty := b4Ty, debugName := none }]
    let d8 := [{ mutability := .mut, ty := b8Ty, debugName := none },
      { mutability := .not, ty := f64Ty, debugName := none }]
    let d8Rev := [{ mutability := .mut, ty := f64Ty, debugName := none },
      { mutability := .not, ty := b8Ty, debugName := none }]
    let q32 := Query.quietNaN.bits32
    let s64 := Query.signalingNaN.bits64
    evalByteCast [.uninit, .init (.scalar ⟨q32, 4⟩)] (.copy ⟨1, []⟩) b4Ty
        emptyMemory d4 byteCarrierLayouts =
      .ok (.aggregate 0 (annealLeBytes4 q32))
        [.uninit, .init (.scalar ⟨q32, 4⟩)] emptyMemory ∧
    evalByteCast [.uninit, .init (.aggregate 0 (annealLeBytes4 q32))]
        (.copy ⟨1, []⟩) f32Ty emptyMemory d4Rev byteCarrierLayouts =
      .ok (.scalar ⟨q32, 4⟩)
        [.uninit, .init (.aggregate 0 (annealLeBytes4 q32))]
        emptyMemory ∧
    evalByteCast [.uninit, .init (.scalar ⟨s64, 8⟩)] (.copy ⟨1, []⟩) b8Ty
        emptyMemory d8 byteCarrierLayouts =
      .ok (.aggregate 0 (annealLeBytes8 s64))
        [.uninit, .init (.scalar ⟨s64, 8⟩)] emptyMemory ∧
    evalByteCast [.uninit, .init (.aggregate 0 (annealLeBytes8 s64))]
        (.copy ⟨1, []⟩) f64Ty emptyMemory d8Rev byteCarrierLayouts =
      .ok (.scalar ⟨s64, 8⟩)
        [.uninit, .init (.aggregate 0 (annealLeBytes8 s64))]
        emptyMemory :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Fail-closed boundaries of the trusted machine (`f16`, `f128`, uninit). -/
theorem trusted_fail_closed :
    trustedVerdict .f16ToF32 .onePointFive = some .unsupported ∧
      trustedVerdict .f128ToF32 .onePointFive = some .unsupported ∧
      trustedVerdict .uninitCast .onePointFive = some .undefinedBehavior := by
  decide +kernel

/-- Second fail-closed `unsupported` fault-equivalence witness on MiniRust:
`f128 → f32` fails closed in both Anneal and MiniRust translation. -/
def mrF128Fault : FaultEquivWitness (sideMR.rel model) :=
  sideMR.faultAt model sideMR_sim .treeBorrows .f128ToF32 .onePointFive .p0
    rfl (by decide +kernel)

/-- Saturation and NaN handling of the float-to-`i32` cast: `NaN ↦ 0`,
`-∞ ↦ i32::MIN`, `3.0e9 ↦ i32::MAX`. -/
theorem f32ToI32_saturates :
    trustedVerdict .f32ToI32 .quietNaN = some (.returns 0) ∧
      trustedVerdict .f32ToI32 .negInfinity = some (.returns 0x80000000) ∧
      trustedVerdict .f32ToI32 .threeBillion = some (.returns 0x7fffffff) := by
  decide +kernel

/-- Initial state of a cast body on an explicit raw bit pattern. -/
def castInitBits (p : Prog) (bits : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨bits, (castShape p).2.1⟩)] }
    memory := emptyMemory }

/-- Unsigned 64-bit casts: `f64 as u64` truncates `1.5` to `1`, keeps
`3.0e9`, saturates `-∞` and NaN to `0`, and saturates `+∞` to `u64::MAX`;
`u64 as f64` converts bit-63-set `0xfff0000000000000` as unsigned (not
negative), rounds halfway ties above `2^53` to even (`2^53 + 1 ↦ 2^53`,
`2^53 + 3 ↦ 2^53 + 4`), and carries `u64::MAX` to `2^64`. The trusted
machine agrees with the reference specification on every query and boundary
input. -/
theorem u64_casts :
    trustedVerdict .f64ToU64 .onePointFive = some (.returns 1) ∧
      trustedVerdict .f64ToU64 .threeBillion = some (.returns 3000000000) ∧
      trustedVerdict .f64ToU64 .negInfinity = some (.returns 0) ∧
      trustedVerdict .f64ToU64 .quietNaN = some (.returns 0) ∧
      trustedVerdict .u64ToF64 .onePointFive =
        some (.returns 0x43cffc0000000000) ∧
      trustedVerdict .u64ToF64 .quietNaN =
        some (.returns 0x43dffe0000080000) ∧
      trustedVerdict .u64ToF64 .negInfinity =
        some (.returns 0x43effe0000000000) ∧
      WideSlice.frameVerdict (castBody .f64ToU64)
          (castInitBits .f64ToU64 0x7ff0000000000000) =
        some (.returns 0xffffffffffffffff) ∧
      WideSlice.frameVerdict (castBody .u64ToF64)
          (castInitBits .u64ToF64 (2 ^ 53 + 1)) =
        some (.returns 0x4340000000000000) ∧
      WideSlice.frameVerdict (castBody .u64ToF64)
          (castInitBits .u64ToF64 (2 ^ 53 + 3)) =
        some (.returns 0x4340000000000002) ∧
      WideSlice.frameVerdict (castBody .u64ToF64)
          (castInitBits .u64ToF64 (2 ^ 64 - 1)) =
        some (.returns 0x43f0000000000000) ∧
      Ref.toInteger .binary64 0x7ff0000000000000 64 false =
        some 0xffffffffffffffff ∧
      Ref.fromInteger .binary64 (2 ^ 53 + 1) = some 0x4340000000000000 ∧
      Ref.fromInteger .binary64 (2 ^ 53 + 3) = some 0x4340000000000002 ∧
      Ref.fromInteger .binary64 (2 ^ 64 - 1) = some 0x43f0000000000000 ∧
      allQueries.all (fun q =>
        decide (trustedVerdict .f64ToU64 q =
            lmReference .deterministic .f64ToU64 q .p0) &&
          decide (trustedVerdict .u64ToF64 q =
            lmReference .deterministic .u64ToF64 q .p0)) = true := by
  decide +kernel

/-- MiniRust rejects every float cast in translation, so its verdict on
the `f32` / `f64` casts is `unsupported` where the trusted machine
returns: those keys are outside `gateMR`, and the exclusion is necessary. -/
theorem gateMR_exclusion_is_tight :
    gateMR .basic .f32ToF64 .onePointFive = false ∧
      mrVerdict .basic .f32ToF64 .onePointFive .p0 = some .unsupported ∧
      annealVerdict .deterministic .f32ToF64 .onePointFive .p0 =
        some (.returns 0x3ff8000000000000) ∧
      mrVerdict .basic .f32ToI32 .onePointFive .p0 = some .unsupported ∧
      mrVerdict .treeBorrows .i32ToF32 .onePointFive .p0 =
        some .unsupported := by
  decide +kernel

section MiniRust

open MiniRustSpec MiniRustSpec.Gen MiniRustSpec.LibSpecr
open MiniRustSpec.Interp MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.RefWitness

/-- Little-endian `[u8; 4]` tuple value in MiniRust (`Memory M`,
non-recursive). -/
def mrLeBytes4 {M : Type} [Memory M] (bits : Nat) : List (Gen.Value M) :=
  [.Int (Int.ofNat (bits % 256)),
   .Int (Int.ofNat ((bits / 256) % 256)),
   .Int (Int.ofNat ((bits / 65536) % 256)),
   .Int (Int.ofNat ((bits / 16777216) % 256))]

/-- Little-endian `[u8; 8]` tuple value in MiniRust (`Memory M`,
non-recursive). -/
def mrLeBytes8 {M : Type} [Memory M] (bits : Nat) : List (Gen.Value M) :=
  mrLeBytes4 bits ++ mrLeBytes4 (bits / 4294967296)

/-- Little-endian `Nat` byte list of length 4. -/
def leNatBytes4 (bits : Nat) : List Nat :=
  [bits % 256, (bits / 256) % 256, (bits / 65536) % 256,
   (bits / 16777216) % 256]

/-- Little-endian `Nat` byte list of length 8. -/
def leNatBytes8 (bits : Nat) : List Nat :=
  leNatBytes4 bits ++ leNatBytes4 (bits / 4294967296)

/-- Extract byte values from a decoded MiniRust tuple of integer bytes. -/
def mrTupleBytes? : Interp (Option Val) → Option (List Nat)
  | .ok (some (.Tuple vs)) =>
    vs.mapM fun v => match v with | .Int i => some i.toNat | _ => none
  | _ => none

/-- The translation gate: `f16`/`f32`/`f64`/`f128` types and float-cast
bodies are rejected; 32-bit and 64-bit integer carriers are accepted. -/
theorem translation_gate :
    (translateTy (t := scalarTy (.float .f16))).isNone = true ∧
      (translateTy (t := scalarTy (.float .f32))).isNone = true ∧
      (translateTy (t := scalarTy (.float .f64))).isNone = true ∧
      (translateTy (t := scalarTy (.float .f128))).isNone = true ∧
      (translateFn (castBody .f32ToF64)).isNone = true ∧
      (translateFn (castBody .f32ToI32)).isNone = true ∧
      (translateFn (castBody .f16ToF32)).isNone = true ∧
      (translateFn (castBody .f128ToF32)).isNone = true ∧
      (translateRvalue (layouts := ⟨64, true, []⟩)
        (decls := castDecls .bitsU32ToI32) (targetTy := none)
        (castRvalue .bitsU32ToI32)).isSome = true ∧
      (translateRvalue (layouts := ⟨64, true, []⟩)
        (decls := castDecls .bitsU64ToI64) (targetTy := none)
        (castRvalue .bitsU64ToI64)).isSome = true := by
  decide +kernel

/-- MiniRust `Type.encode`, `Type.decode`, `Interp.transmute`, and
`transmuteM` (`BasicMemory` and `TreeBorrowsMemory`) preserve IEEE-754
32-bit and 64-bit NaN bit patterns across `u32`/`i32`/`[u8; 4]` and
`u64`/`i64`/`[u8; 8]`. -/
theorem mr_byte_carrier_encode_decode_transmute :
    let q32 := Query.quietNaN.bits32
    let s64 := Query.signalingNaN.bits64
    let b4Ty : Gen.Type := .Array (.Int u8It) 4
    let b8Ty : Gen.Type := .Array (.Int u8It) 8
    mrTupleBytes?
        (Type.encode (.Int u32) (.Int (Int.ofNat q32)) >>= Type.decode b4Ty) =
        some (leNatBytes4 q32) ∧
      mrTupleBytes?
        (Type.encode (.Int u64It) (.Int (Int.ofNat s64)) >>=
          Type.decode b8Ty) =
        some (leNatBytes8 s64) ∧
      carrierVerdictW (M := BM) 4294967296
        (Interp.transmute (.Tuple (mrLeBytes4 (M := BM) q32)) b4Ty
          (.Int i32)) = some (.returns q32) ∧
      carrierVerdictW (M := TBM) 4294967296
        (transmuteM (M := TBM) (.Tuple (mrLeBytes4 (M := TBM) q32)) b4Ty
          (.Int i32)) = some (.returns q32) ∧
      carrierVerdictW (M := BM) 18446744073709551616
        (Interp.transmute (.Tuple (mrLeBytes8 (M := BM) s64)) b8Ty
          (.Int i64It)) = some (.returns s64) ∧
      carrierVerdictW (M := TBM) 18446744073709551616
        (transmuteM (M := TBM) (.Tuple (mrLeBytes8 (M := TBM) s64)) b8Ty
          (.Int i64It)) = some (.returns s64) := by
  decide +kernel

/-- One-argument 32-bit carrier body `fn(x: u32) -> i32 { transmute(x) }`. -/
def carrier32Body : CapturedMir :=
  { castBody .bitsU32ToI32 with
    defPath := "float_cast::carrier_u32_i32"
    argCount := 1
    fnAbi := WideSlice.fnAbiOf 4 }

/-- One-argument 64-bit carrier body `fn(x: u64) -> i64 { transmute(x) }`. -/
def carrier64Body : CapturedMir :=
  { castBody .bitsU64ToI64 with
    defPath := "float_cast::carrier_u64_i64"
    argCount := 1
    fnAbi := WideSlice.fnAbiOf 8 }

/-- Eight-byte caller context for 64-bit MiniRust carrier machine runs. -/
def ctx8 : Ctx :=
  { ctx0 with
    base :=
      [{ retAlloc with data := List.replicate 8 .Uninit, align := ⟨8⟩ }] }

/-- Whole-program `translateFn`, `Interp.steps` (`BasicMemory`), and
`Interp.stepsTB` (`TreeBorrowsMemory`) runs on both 32-bit and 64-bit float
bit carriers agree with Anneal `stepMirFn` on quiet-NaN bit patterns. -/
theorem mr_carrier_steps_three_way :
    let q32 := Query.quietNaN.bits32
    let q64 := Query.quietNaN.bits64
    let s32 := initMachineState carrier32Body [.scalar ⟨q32, 4⟩]
    let s64 := initMachineState carrier64Body [.scalar ⟨q64, 8⟩]
    (match translateFn carrier32Body with
     | some fn32 =>
       let m0 := machine carrier32Body fn32 s32.frame.locals fn32.start
       WideSlice.runVerdict carrier32Body 10 s32 = some (.returns q32) ∧
         WideSlice.machVerdict (Interp.steps 3 m0) = some (.returns q32) ∧
         WideSlice.machVerdictTB (Interp.stepsTB 3 (liftMachToTB m0)) =
           some (.returns q32)
     | none => False) ∧
    (match translateFn carrier64Body with
     | some fn64 =>
       let m0 := machineWithCtx ctx8 carrier64Body fn64 s64.frame.locals
         fn64.start
       WideSlice.runVerdict carrier64Body 10 s64 = some (.returns q64) ∧
         WideSlice.machVerdict (Interp.steps 3 m0) = some (.returns q64) ∧
         WideSlice.machVerdictTB (Interp.stepsTB 3 (liftMachToTB m0)) =
           some (.returns q64)
     | none => False) :=
  ⟨⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩⟩

end MiniRust

/-! #### Vertical composition: the function-level front model -/

/-- Verdict of the function-level trusted cast (`evalFloatCast` for numeric
float casts and `evalByteCast` for 32/64-bit bit-carrier transmutes, without
the machine); the uninitialized operand read is undefined behavior. -/
def frontBase (p : Prog) (q : Query) : Option (Verdict Nat) :=
  match p with
  | .uninitCast => some .undefinedBehavior
  | .bitsU32ToI32 | .bitsU64ToI64 =>
    match evalByteCast (castInit p q).frame.locals (.copy ⟨1, []⟩)
        (castShape p).2.2.1 emptyMemory (castDecls p) emptyLayoutTable with
    | .ok (.scalar sc) _ _ => some (.returns sc.bits)
    | .ub => some .undefinedBehavior
    | _ => some .unsupported
  | _ =>
    match evalFloatCast (castShape p).2.2.2 (some (castShape p).1)
      (castShape p).2.2.1 emptyLayoutTable
      (.scalar ⟨srcBits p q, (castShape p).2.1⟩) with
    | some (.scalar sc) => some (.returns sc.bits)
    | _ => some .unsupported

/-- The front model: the function-level cast with the NaN-selection
mode. -/
def frontVerdict (mode : NanMode) (p : Prog) (q : Query) (c : Pick) :
    Option (Verdict Nat) :=
  match frontBase p q, f2fFormats p with
  | some (.returns bits), some (src, dst) =>
    (Ref.adjustNaN mode.flag c.toNat dst bits [(src, srcBits p q)]).map
      Verdict.returns
  | v, _ => v

/-- The front model, with the identity codec onto machine results. -/
def frontModel : Model NanMode Prog Query Pick Nat Nat where
  evalA := frontVerdict
  codec := CodecLaws.id Nat
  progs := allProgs
  queries := allQueries
  choices := allPicks
  progs_complete := fun p => by cases p <;> decide
  queries_complete := fun q => by cases q <;> decide
  choices_complete := fun c => by cases c <;> decide

/-- The machine-level Anneal model viewed from the MiniRust modes. -/
def frontSideMR : Side NanMode WideSlice.MrMem Prog Query Pick Nat Nat where
  toAnneal := sideMR.toAnneal
  gate := gateMR
  verdictR := fun m p q c => annealVerdict (sideMR.toAnneal m) p q c
  rep := fun r => r
  modes := sideMR.modes
  modes_complete := sideMR.modes_complete
  wMode := sideMR.wMode
  okProg := sideMR.okProg
  okQuery := sideMR.okQuery
  okChoice := sideMR.okChoice
  faultProg := sideMR.faultProg
  faultQuery := sideMR.faultQuery
  faultChoice := sideMR.faultChoice
  flip := none

/-- The machine-level Anneal model viewed from the LeanMiri modes. -/
def frontSideLM : Side NanMode NanMode Prog Query Pick Nat Nat where
  toAnneal := fun m => m
  gate := gateLM
  verdictR := annealVerdict
  rep := fun r => r
  modes := allModes
  modes_complete := fun m => by cases m <;> decide
  wMode := .nondeterministic
  okProg := .f32ToF64
  okQuery := .onePointFive
  okChoice := .p0
  faultProg := .uninitCast
  faultQuery := .onePointFive
  faultChoice := .p0
  flip :=
    some (.nondeterministic, .deterministic, .f32ToF64, .quietNaN, .p2)

/-- Certificate: the function-level model agrees with the machine. -/
theorem frontSideMR_check : frontSideMR.check frontModel = true := by
  decide +kernel

/-- Certificate: the function-level model agrees with the machine. -/
theorem frontSideLM_check : frontSideLM.check frontModel = true := by
  decide +kernel

/-- Bundle of the function-level model against the machine-level model
(both of its authorities are views of the machine-level model). -/
def frontBundle :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit Nat
      WideSlice.MrMem Pick Nat Unit NanMode Pick Nat Unit :=
  Corpus.bundle frontModel frontSideMR frontSideLM frontSideMR_check
    frontSideLM_check

section Derived

variable
  (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))

/-- Simulation certificate of the LeanMiri side. -/
theorem sideLM_sim_with (h : (sideLM verdictLM).check model = true) :
    (sideLM verdictLM).simCheck model = true :=
  (Bool.and_eq_true _ _ ▸ h).1

/-- **Cross-authority fault equivalence** at the uninitialized source. -/
theorem uninit_fault_equiv_with
    (h : (sideLM verdictLM).check model = true) :
    (∃ c, (bundleWith verdictLM h).mrRel.ExecR .basic .uninitCast
        .onePointFive c (.fault .undefined)) ↔
      (∃ c, (bundleWith verdictLM h).lmRel.ExecR .deterministic .uninitCast
        .onePointFive c (.fault .undefined)) :=
  (bundleWith verdictLM h).crossAuthorityFaultEquiv
    (mMR := .basic) (mLM := .deterministic) (p := .uninitCast)
    (q := .onePointFive) rfl rfl rfl .undefined

/-- MiniRust's typed load of uninitialized bytes is undefined behavior,
hence so is the uninitialized source for every LeanMiri presentation. -/
theorem lm_uninit_faults_with (h : (sideLM verdictLM).check model = true) :
    ∃ c, verdictLM .deterministic .uninitCast .onePointFive c =
      some .undefinedBehavior := by
  obtain ⟨c, hc⟩ :=
    (uninit_fault_equiv_with verdictLM h).mp
      ⟨.p0, Side.execR_of_verdict model sideMR (v := .undefinedBehavior)
        (by decide +kernel)⟩
  exact ⟨c, Side.verdict_of_execR model (sideLM verdictLM)
    (v := .undefinedBehavior) hc⟩

/-- **Cross-authority normal equivalence** at the 32-bit NaN bit carrier:
the quiet-NaN pattern is carried unchanged by both authorities. -/
theorem carrier_normal_equiv_with
    (h : (sideLM verdictLM).check model = true) (a : Nat) :
    (∃ c r, (sideMR.rel model).ExecR .basic .bitsU32ToI32 .quietNaN c
        (.normal r) ∧ halves r = halvesCodec.encode a) ↔
      (∃ c r, ((sideLM verdictLM).rel model).ExecR .deterministic
        .bitsU32ToI32 .quietNaN c (.normal r) ∧
        halves r = halvesCodec.encode a) :=
  (((bundleWith verdictLM h).crossAuthorityNormalEquiv
    (mMR := .basic) (mLM := .deterministic) (p := .bitsU32ToI32)
    (q := .quietNaN) rfl rfl rfl
    (sideMR.reverseTotal model sideMR_sim)
    ((sideLM verdictLM).reverseTotal model (sideLM_sim_with verdictLM h))).1
    a).2.2

/-- **Cross-authority normal equivalence** at the 64-bit NaN bit carrier:
the 64-bit signaling-NaN pattern is carried unchanged by both authorities
(`TreeBorrowsMemory` on MiniRust vs LeanMiri `Cast.cast .Transmute`). -/
theorem carrier64_normal_equiv_with
    (h : (sideLM verdictLM).check model = true) (a : Nat) :
    (∃ c r, (sideMR.rel model).ExecR .treeBorrows .bitsU64ToI64 .signalingNaN
        c (.normal r) ∧ halves r = halvesCodec.encode a) ↔
      (∃ c r, ((sideLM verdictLM).rel model).ExecR .deterministic
        .bitsU64ToI64 .signalingNaN c (.normal r) ∧
        halves r = halvesCodec.encode a) :=
  (((bundleWith verdictLM h).crossAuthorityNormalEquiv
    (mMR := .treeBorrows) (mLM := .deterministic) (p := .bitsU64ToI64)
    (q := .signalingNaN) rfl rfl rfl
    (sideMR.reverseTotal model sideMR_sim)
    ((sideLM verdictLM).reverseTotal model (sideLM_sim_with verdictLM h))).1
    a).2.2

/-- On the LeanMiri fragment, a normal return of the Anneal model is the
normal return of every certified LeanMiri presentation. -/
theorem lm_returns_of_anneal_with
    (h : (sideLM verdictLM).check model = true) {m : NanMode} {p : Prog}
    {q : Query} {c : Pick} {n : Nat} (hg : gateLM m p q = true)
    (hA : annealVerdict m p q c = some (.returns n)) :
    verdictLM m p q c = some (.returns n) := by
  obtain ⟨oa, orr, ha, hr, hc⟩ := couplesB_sound
    ((sideLM verdictLM).simCheck_spec model (sideLM_sim_with verdictLM h)
      m p q c hg)
  have hA' : outcome? (annealVerdict m p q c) = some (.normal n) := by
    rw [hA]; rfl
  have hoa : oa = .normal n := Option.some.inj (ha.symm.trans hA')
  subst hoa
  obtain ⟨r, horr, hrep⟩ := hc.normal_anneal_to_ref n rfl
  subst horr
  have hrn : r = n := halvesCodec.encode_injective hrep
  subst hrn
  exact outcome?_injective hr

/-- Unsigned saturating `f64 as u64` (`3.0e9 ↦ 3000000000`): a positive
witness on the LeanMiri side. -/
def lmU64Positive_with (h : (sideLM verdictLM).check model = true) :
    PositiveWitness ((sideLM verdictLM).rel model) :=
  (sideLM verdictLM).positiveAt model (sideLM_sim_with verdictLM h)
    .deterministic .f64ToU64 .threeBillion .p0 rfl
    (show isReturn
        (annealVerdict .deterministic .f64ToU64 .threeBillion .p0) = true by
      decide +kernel)
    (show (allPicks.all fun c' =>
        !isFaultV (annealVerdict .deterministic .f64ToU64 .threeBillion c'))
        = true by
      decide +kernel)

/-- Every certified LeanMiri presentation is well-formed on `3.0e9 as u64`
and saturates `NaN as u64` and `-∞ as u64` to `0`, and converts
`0x7ff8000020000000 as f64` exactly. -/
theorem lm_u64_casts_with (h : (sideLM verdictLM).check model = true) :
    ((sideLM verdictLM).rel model).WellFormedRef .deterministic .f64ToU64
        .threeBillion ∧
      verdictLM .deterministic .f64ToU64 .quietNaN .p0 = some (.returns 0) ∧
      verdictLM .nondeterministic .f64ToU64 .negInfinity .p3 =
        some (.returns 0) ∧
      verdictLM .deterministic .u64ToF64 .quietNaN .p0 =
        some (.returns 0x43dffe0000080000) :=
  ⟨(lmU64Positive_with verdictLM h).wellFormedRef
      (bundleWith verdictLM h).lmSim,
   lm_returns_of_anneal_with verdictLM h rfl (by decide +kernel),
   lm_returns_of_anneal_with verdictLM h rfl (by decide +kernel),
   lm_returns_of_anneal_with verdictLM h rfl (by decide +kernel)⟩

/-- The mode-sensitivity witness of the LeanMiri side: the
payload-preserving quiet NaN is reachable in nondeterministic mode only. -/
def lmModeWitness_with (h : (sideLM verdictLM).check model = true) :
    ModeSensitivityWitness ((sideLM verdictLM).rel model) :=
  ((sideLM verdictLM).flipW model h).get rfl

/-- The witness separates the two NaN modes on the quiet-NaN widening. -/
theorem lmModeWitness_spec_with
    (h : (sideLM verdictLM).check model = true) :
    (lmModeWitness_with verdictLM h).m₁ = .nondeterministic ∧
      (lmModeWitness_with verdictLM h).m₂ = .deterministic ∧
      (lmModeWitness_with verdictLM h).p = .f32ToF64 ∧
      (lmModeWitness_with verdictLM h).q = .quietNaN ∧
      (lmModeWitness_with verdictLM h).c = .p2 ∧
      (lmModeWitness_with verdictLM h).m₁ ≠
        (lmModeWitness_with verdictLM h).m₂ :=
  ⟨rfl, rfl, rfl, rfl, rfl, (lmModeWitness_with verdictLM h).mode_ne⟩

/-- The flip is on a normal outcome, not on a fault: the deterministic
mode still returns (the preferred NaN) on the same input. -/
theorem lmModeWitness_normal_flip_with :
    ((sideLM verdictLM).rel model).ExecA .nondeterministic .f32ToF64
        .quietNaN .p2 (.normal 0x7ff8000020000000) ∧
      (∀ c, ((sideLM verdictLM).rel model).ExecA .deterministic .f32ToF64
        .quietNaN c (.normal 0x7ff8000000000000)) :=
  ⟨Side.execA_of_verdict model (sideLM verdictLM)
      (v := .returns 0x7ff8000020000000)
      (show annealVerdict .nondeterministic .f32ToF64 .quietNaN .p2 =
          some (.returns 0x7ff8000020000000) by decide +kernel),
   fun c => Side.execA_of_verdict model (sideLM verdictLM)
      (v := .returns 0x7ff8000000000000) (deterministic_canonicalizes c).1⟩

/-- Two-sided productivity on both authorities. -/
theorem productiveBoth_with (h : (sideLM verdictLM).check model = true) :
    (bundleWith verdictLM h).mrRel.ProductiveBoth ∧
      (bundleWith verdictLM h).lmRel.ProductiveBoth :=
  ⟨sideMR.productiveBoth model sideMR_sim .p0,
   (sideLM verdictLM).productiveBoth model (sideLM_sim_with verdictLM h)
    .p0⟩

/-- **Transitive composition** (`trans`): the function-level model against
MiniRust and LeanMiri, through the machine-level model. -/
def frontTrans_with (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat)
      WideSlice.MrMem Pick Nat Unit NanMode Pick Nat Unit :=
  frontBundle.trans (bundleWith verdictLM h) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ hg => hg) (fun _ _ _ hg => hg)
    (fun _ => rfl) (fun _ => rfl)

/-- The transitive bundle's codec is the composition of the codecs. -/
theorem frontTrans_codec_with (h : (sideLM verdictLM).check model = true) :
    (frontTrans_with verdictLM h).codec =
      (CodecLaws.id Nat).comp halvesCodec :=
  frontBundle.trans_codec (bundleWith verdictLM h)
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ hg => hg) (fun _ _ _ hg => hg) (fun _ => rfl) (fun _ => rfl)

/-- The transitive bundle is productive on both sides. -/
theorem frontTrans_productiveBoth_with
    (h : (sideLM verdictLM).check model = true) :
    (frontTrans_with verdictLM h).mrRel.ProductiveBoth ∧
      (frontTrans_with verdictLM h).lmRel.ProductiveBoth :=
  frontBundle.trans_productiveBoth (bundleWith verdictLM h)
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ hg => hg) (fun _ _ _ hg => hg) (fun _ => rfl) (fun _ => rfl)
    (frontSideMR.productiveBoth frontModel
      (Bool.and_eq_true _ _ ▸ frontSideMR_check).1 .p0).1
    (frontSideLM.productiveBoth frontModel
      (Bool.and_eq_true _ _ ▸ frontSideLM_check).1 .p0).1
    (productiveBoth_with verdictLM h).1.2
    (productiveBoth_with verdictLM h).2.2

/-- **Vertical composition** (`comp`) with the front simulations. -/
def frontComp_with (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat)
      WideSlice.MrMem Pick Nat Unit NanMode Pick Nat Unit :=
  (bundleWith verdictLM h).comp (CodecLaws.id Nat) frontBundle.mrSim
    frontBundle.lmSim (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ hg => hg) (fun _ _ _ hg => hg) (fun _ _ hr => hr)
    (fun _ _ hr => hr) frontBundle.toAnnealMR frontBundle.toAnnealLM
    frontBundle.ExecAnneal frontBundle.anneal_exec_coherent

/-- The composed bundle is productive on both sides. -/
theorem frontComp_productive_with
    (h : (sideLM verdictLM).check model = true) :
    ((frontComp_with verdictLM h).mrRel.ProductiveAnneal ∧
      (frontComp_with verdictLM h).lmRel.ProductiveAnneal) ∧
    ((frontComp_with verdictLM h).mrRel.ProductiveBoth ∧
      (frontComp_with verdictLM h).lmRel.ProductiveBoth) :=
  ⟨(bundleWith verdictLM h).comp_productiveAnneal (CodecLaws.id Nat)
      frontBundle.mrSim frontBundle.lmSim (fun _ _ _ _ _ => Iff.rfl)
      (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ hg => hg) (fun _ _ _ hg => hg)
      (fun _ _ hr => hr) (fun _ _ hr => hr) frontBundle.toAnnealMR
      frontBundle.toAnnealLM frontBundle.ExecAnneal
      frontBundle.anneal_exec_coherent
      (frontSideMR.productiveBoth frontModel
        (Bool.and_eq_true _ _ ▸ frontSideMR_check).1 .p0).1
      (frontSideLM.productiveBoth frontModel
        (Bool.and_eq_true _ _ ▸ frontSideLM_check).1 .p0).1,
   (bundleWith verdictLM h).comp_productiveBoth (CodecLaws.id Nat)
      frontBundle.mrSim frontBundle.lmSim (fun _ _ _ _ _ => Iff.rfl)
      (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ hg => hg) (fun _ _ _ hg => hg)
      (fun _ _ hr => hr) (fun _ _ hr => hr) frontBundle.toAnnealMR
      frontBundle.toAnnealLM frontBundle.ExecAnneal
      frontBundle.anneal_exec_coherent
      (frontSideMR.productiveBoth frontModel
        (Bool.and_eq_true _ _ ▸ frontSideMR_check).1 .p0).1
      (frontSideLM.productiveBoth frontModel
        (Bool.and_eq_true _ _ ▸ frontSideLM_check).1 .p0).1
      (productiveBoth_with verdictLM h).1.2
      (productiveBoth_with verdictLM h).2.2⟩

/-- **Mode-preserving vertical composition** (`compPreserveModeMixed`):
the MiniRust side has no mode witness to transport (fault-flip strategy,
vacuously), and the LeanMiri side transports its normal-outcome NaN
witness through the reverse-total front simulation. -/
def frontCompMixed_with (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat)
      WideSlice.MrMem Pick Nat Unit NanMode Pick Nat Unit :=
  (bundleWith verdictLM h).compPreserveModeMixed (CodecLaws.id Nat)
    frontBundle.mrSim frontBundle.lmSim (fun _ _ _ _ _ => Iff.rfl)
    (fun _ _ _ _ _ => Iff.rfl) (fun _ _ _ hg => hg) (fun _ _ _ hg => hg)
    (fun _ _ hr => hr) (fun _ _ hr => hr)
    (.faultFlip (fun ms hms => by
      have h0 : (none : Option (ModeSensitivityWitness (sideMR.rel model))) =
          some ms := hms
      cases h0))
    (.reverseTotal
      (frontSideLM.reverseTotal frontModel
        (Bool.and_eq_true _ _ ▸ frontSideLM_check).1)
      (fun _ _ _ _ _ => rfl))
    frontBundle.toAnnealMR frontBundle.toAnnealLM frontBundle.ExecAnneal
    frontBundle.anneal_exec_coherent

/-- The NaN mode sensitivity survives the composition on the LeanMiri
side, and the MiniRust side stays without one. -/
theorem frontCompMixed_modeSensitive_with
    (h : (sideLM verdictLM).check model = true) :
    (frontCompMixed_with verdictLM h).lmFlip.modeSensitivity?.isSome =
        true ∧
      (frontCompMixed_with verdictLM h).mrFlip.modeSensitivity?.isSome =
        false :=
  ⟨rfl, rfl⟩

/-- Memory model named by a Boolean. -/
def memOfBool (b : Bool) : WideSlice.MrMem :=
  if b then .treeBorrows else .basic

/-- Boolean naming a memory model. -/
def boolOfMem : WideSlice.MrMem → Bool
  | .basic => false
  | .treeBorrows => true

/-- NaN mode named by a Boolean (the `floatNondeterministic` flag). -/
def modeOfBool (b : Bool) : NanMode :=
  if b then .nondeterministic else .deterministic

/-- Mode reindexing: `Bool` for the NaN mode and for the memory model. -/
def boolModes_with (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat) Bool
      Pick Nat Unit Bool Pick Nat Unit :=
  (bundleWith verdictLM h).liftMode memOfBool boolOfMem
    (fun m => by cases m <;> rfl) modeOfBool NanMode.flag
    (fun m => by cases m <;> rfl)

/-- Mode reindexing preserves productivity. -/
theorem boolModes_productive_with
    (h : (sideLM verdictLM).check model = true) :
    ((boolModes_with verdictLM h).mrRel.ProductiveAnneal ∧
      (boolModes_with verdictLM h).lmRel.ProductiveAnneal) ∧
    ((boolModes_with verdictLM h).mrRel.ProductiveRef ∧
      (boolModes_with verdictLM h).lmRel.ProductiveRef) ∧
    ((boolModes_with verdictLM h).mrRel.ProductiveBoth ∧
      (boolModes_with verdictLM h).lmRel.ProductiveBoth) :=
  ⟨(bundleWith verdictLM h).liftMode_productiveAnneal memOfBool boolOfMem
      (fun m => by cases m <;> rfl) modeOfBool NanMode.flag
      (fun m => by cases m <;> rfl)
      (productiveBoth_with verdictLM h).1.1
      (productiveBoth_with verdictLM h).2.1,
   (bundleWith verdictLM h).liftMode_productiveRef memOfBool boolOfMem
      (fun m => by cases m <;> rfl) modeOfBool NanMode.flag
      (fun m => by cases m <;> rfl)
      (productiveBoth_with verdictLM h).1.2
      (productiveBoth_with verdictLM h).2.2,
   (bundleWith verdictLM h).liftMode_productiveBoth memOfBool boolOfMem
      (fun m => by cases m <;> rfl) modeOfBool NanMode.flag
      (fun m => by cases m <;> rfl)
      (productiveBoth_with verdictLM h).1
      (productiveBoth_with verdictLM h).2⟩

/-- The reindexed bundle keeps the NaN mode sensitivity (now between the
`Bool` modes `true` and `false`). -/
theorem boolModes_modeSensitive_with
    (h : (sideLM verdictLM).check model = true) :
    (boolModes_with verdictLM h).lmFlip.modeSensitivity?.isSome = true :=
  rfl

/-- Mode restriction: only `BasicMemory` and only the nondeterministic
NaN mode (the maps are not surjective). -/
def nondetOnly_with (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle NanMode Prog Query Nat Unit (Nat × Nat) Unit
      Pick Nat Unit Unit Pick Nat Unit :=
  (bundleWith verdictLM h).restrictMode (fun _ => .basic)
    (fun _ => .nondeterministic) () () () rfl rfl rfl () () () rfl rfl rfl

/-- Mode restriction preserves productivity. -/
theorem nondetOnly_productive_with
    (h : (sideLM verdictLM).check model = true) :
    ((nondetOnly_with verdictLM h).mrRel.ProductiveAnneal ∧
      (nondetOnly_with verdictLM h).lmRel.ProductiveAnneal) ∧
    ((nondetOnly_with verdictLM h).mrRel.ProductiveRef ∧
      (nondetOnly_with verdictLM h).lmRel.ProductiveRef) ∧
    ((nondetOnly_with verdictLM h).mrRel.ProductiveBoth ∧
      (nondetOnly_with verdictLM h).lmRel.ProductiveBoth) :=
  ⟨(bundleWith verdictLM h).restrictMode_productiveAnneal _ _ () () () rfl
      rfl rfl () () () rfl rfl rfl none none
      (productiveBoth_with verdictLM h).1.1
      (productiveBoth_with verdictLM h).2.1,
   (bundleWith verdictLM h).restrictMode_productiveRef _ _ () () () rfl
      rfl rfl () () () rfl rfl rfl none none
      (productiveBoth_with verdictLM h).1.2
      (productiveBoth_with verdictLM h).2.2,
   (bundleWith verdictLM h).restrictMode_productiveBoth _ _ () () () rfl
      rfl rfl () () () rfl rfl rfl none none
      (productiveBoth_with verdictLM h).1
      (productiveBoth_with verdictLM h).2⟩

/-- Codec tightening is idempotent on the bundle and yields a tight
codec. -/
theorem tightenCodec_with (h : (sideLM verdictLM).check model = true) :
    (bundleWith verdictLM h).tightenCodec.codec.TightValidRep ∧
      (bundleWith verdictLM h).tightenCodec.tightenCodec =
        (bundleWith verdictLM h).tightenCodec :=
  ⟨(bundleWith verdictLM h).tightenCodec_tightValidRep,
   (bundleWith verdictLM h).tightenCodec_idem⟩

end Derived

/-! #### Surface instances at the reference specification -/

/-- The surface bundle is mode-sensitive on the LeanMiri side only. -/
theorem bundle_modeSensitive :
    bundle.lmFlip.modeSensitivity?.isSome = true ∧
      bundle.mrFlip.modeSensitivity?.isSome = false :=
  ⟨rfl, rfl⟩

/-- Cross-authority fault equivalence of the surface bundle. -/
theorem uninit_fault_equiv :
    (∃ c, bundle.mrRel.ExecR .basic .uninitCast .onePointFive c
        (.fault .undefined)) ↔
      (∃ c, bundle.lmRel.ExecR .deterministic .uninitCast .onePointFive c
        (.fault .undefined)) :=
  uninit_fault_equiv_with lmReference sideLM_reference_check

end FloatCast

/-! ### C.9 The trusted machine verbatim under the payload-preserving
schedule (`fromEquivGated`)

The bundle of C.6 gives the Anneal model a NaN-selection mode. Here the
Anneal evaluator is the trusted machine itself, deterministic and
mode-independent, and the choice gate restricts the reference executions
to the oracle schedule that selects the trusted machine's NaN: pick `2`
of the nondeterministic mode on the LeanMiri side, and the trivial pick
`0` on the NaN-agnostic MiniRust side. -/

namespace FloatCast

open Anneal.DualCorrespondenceBundle
open Corpus

/-- On the LeanMiri fragment, the nondeterministic mode at oracle pick `2`
is the trusted machine verbatim. -/
theorem schedule_is_trusted (p : Prog) (q : Query)
    (hg : gateLM .nondeterministic p q = true) :
    annealVerdict .nondeterministic p q .p2 = trustedVerdict p q := by
  cases p <;> cases q <;> revert hg <;> decide +kernel

/-- On the MiniRust fragment, the deterministic mode is the trusted machine
verbatim (no float-to-float NaN is inside `gateMR`). -/
theorem mr_schedule_is_trusted (m : WideSlice.MrMem) (p : Prog) (q : Query)
    (hg : gateMR m p q = true) :
    annealVerdict .deterministic p q .p0 = trustedVerdict p q := by
  cases m <;> cases p <;> cases q <;> revert hg <;> decide +kernel

/-- The trusted machine as a deterministic, mode-independent evaluator. -/
def trustedOutcome (_m : Unit) (p : Prog) (q : Query) :
    ExecOutcome4 Nat Unit :=
  totalOutcome (trustedVerdict p q)

/-- MiniRust executions under the trivial schedule (pick `0`). -/
def gatedExecMR (m : WideSlice.MrMem) (p : Prog) (q : Query) (c : Pick)
    (out : ExecOutcome4 Nat Unit) : Prop :=
  c = .p0 ∧ outcome? (mrVerdict m p q c) = some out

/-- LeanMiri executions in nondeterministic mode under the
payload-preserving schedule (pick `2`). -/
def gatedExecLM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (_m : Unit) (p : Prog) (q : Query) (c : Pick)
    (out : ExecOutcome4 Nat Unit) : Prop :=
  c = .p2 ∧ outcome? (verdictLM .nondeterministic p q c) = some out

/-- Payload relation of the gated bundle. -/
abbrev gatedRetRel (a r : Nat) : Prop := halves r = halvesCodec.encode a

/-- MiniRust step relation of the gated bundle. -/
abbrev gatedRelMR :
    ModeParamStepRel WideSlice.MrMem Prog Query Pick Nat Nat Unit Unit :=
  ModeParamStepRel.ofAnnealEvalGated (fun _ => ())
    (fun m p q => gateMR m p q = true) (fun _ _ _ c => c = Pick.p0)
    trustedOutcome gatedExecMR gatedRetRel (fun _ _ => True)

/-- LeanMiri step relation of the gated bundle. -/
abbrev gatedRelLM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat)) :
    ModeParamStepRel Unit Prog Query Pick Nat Nat Unit Unit :=
  ModeParamStepRel.ofAnnealEvalGated (fun _ => ())
    (fun _ p q => gateLM .nondeterministic p q = true)
    (fun _ _ _ c => c = Pick.p2) trustedOutcome (gatedExecLM verdictLM)
    gatedRetRel (fun _ _ => True)

/-- The trusted machine is coupled with MiniRust on every gated key. -/
theorem gated_coupled_MR (m : WideSlice.MrMem) (p : Prog) (q : Query)
    (hg : gateMR m p q = true) :
    ∃ orr, outcome? (mrVerdict m p q .p0) = some orr ∧
      ChoiceCoupledOutcomeRel gatedRetRel
        (fun (_ : Unit) (_ : Unit) => True) (trustedOutcome () p q) orr := by
  obtain ⟨oa, orr, ha, hr, hc⟩ :=
    couplesB_sound (sideMR.simCheck_spec model sideMR_sim m p q .p0 hg)
  have ha' : outcome? (annealVerdict .deterministic p q .p0) = some oa := ha
  rw [mr_schedule_is_trusted m p q hg] at ha'
  have ht : trustedOutcome () p q = oa := totalOutcome_eq ha'
  rw [ht]
  exact ⟨orr, hr, hc⟩

/-- The trusted machine is coupled with every certified LeanMiri
presentation on every gated key, along the payload-preserving schedule. -/
theorem gated_coupled_LM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) (p : Prog) (q : Query)
    (hg : gateLM .nondeterministic p q = true) :
    ∃ orr, outcome? (verdictLM .nondeterministic p q .p2) = some orr ∧
      ChoiceCoupledOutcomeRel gatedRetRel
        (fun (_ : Unit) (_ : Unit) => True) (trustedOutcome () p q) orr := by
  obtain ⟨oa, orr, ha, hr, hc⟩ :=
    couplesB_sound ((sideLM verdictLM).simCheck_spec model
      (sideLM_sim_with verdictLM h) .nondeterministic p q .p2 hg)
  have ha' : outcome? (annealVerdict .nondeterministic p q .p2) = some oa :=
    ha
  rw [schedule_is_trusted p q hg] at ha'
  have ht : trustedOutcome () p q = oa := totalOutcome_eq ha'
  rw [ht]
  exact ⟨orr, hr, hc⟩

/-- Reverse totality of the gated MiniRust relation. -/
theorem gated_reverse_MR : gatedRelMR.ReverseTotal := by
  intro m p q c outA hg hA
  obtain ⟨hc0, hA'⟩ := hA
  have hc0' : c = Pick.p0 := hc0
  subst hc0'
  obtain ⟨orr, hr, hc⟩ := gated_coupled_MR m p q hg
  have hA'' : trustedOutcome () p q = outA := hA'
  rw [← hA'']
  exact ⟨orr, ⟨rfl, hr⟩, hc⟩

/-- Reverse totality of the gated LeanMiri relation. -/
theorem gated_reverse_LM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    (gatedRelLM verdictLM).ReverseTotal := by
  intro _ p q c outA hg hA
  obtain ⟨hc0, hA'⟩ := hA
  have hc0' : c = Pick.p2 := hc0
  subst hc0'
  obtain ⟨orr, hr, hc⟩ := gated_coupled_LM verdictLM h p q hg
  have hA'' : trustedOutcome () p q = outA := hA'
  rw [← hA'']
  exact ⟨orr, ⟨rfl, hr⟩, hc⟩

/-- The trusted carrier of the quiet-NaN pattern. -/
theorem trusted_carrier_outcome :
    trustedOutcome () .bitsU32ToI32 .quietNaN = .normal 0x7fc00001 :=
  totalOutcome_eq (congrArg outcome?
    (by decide +kernel :
      trustedVerdict .bitsU32ToI32 .quietNaN = some (.returns 0x7fc00001)))

/-- The trusted widening of `1.5`. -/
theorem trusted_widen_outcome :
    trustedOutcome () .f32ToF64 .onePointFive =
      .normal 0x3ff8000000000000 :=
  totalOutcome_eq (congrArg outcome?
    (by decide +kernel :
      trustedVerdict .f32ToF64 .onePointFive =
        some (.returns 0x3ff8000000000000)))

/-- The trusted `f16` cast fails closed. -/
theorem trusted_f16_outcome :
    trustedOutcome () .f16ToF32 .onePointFive = .fault .unsupported :=
  totalOutcome_eq (congrArg outcome?
    (by decide +kernel :
      trustedVerdict .f16ToF32 .onePointFive = some .unsupported))

/-- The trusted uninitialized-source cast is undefined behavior. -/
theorem trusted_uninit_outcome :
    trustedOutcome () .uninitCast .onePointFive = .fault .undefined :=
  totalOutcome_eq (congrArg outcome?
    (by decide +kernel :
      trustedVerdict .uninitCast .onePointFive = some .undefinedBehavior))

/-- Positive witness of the gated LeanMiri relation: `1.5f32 as f64`. -/
def gatedPositiveLM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    PositiveWitness (gatedRelLM verdictLM) where
  m := ()
  p := .f32ToF64
  q := .onePointFive
  c := .p2
  gate := rfl
  wf := fun _ k hk => by
    have hk' : trustedOutcome () .f32ToF64 .onePointFive = .fault k := hk.2
    rw [trusted_widen_outcome] at hk'
    cases hk'
  agree := by
    obtain ⟨orr, hr, hc⟩ :=
      gated_coupled_LM verdictLM h .f32ToF64 .onePointFive rfl
    rw [trusted_widen_outcome] at hc
    obtain ⟨r, hr', hrel⟩ := hc.normal_anneal_to_ref _ rfl
    subst hr'
    exact ⟨_, r, ⟨rfl, trusted_widen_outcome⟩, ⟨rfl, hr⟩, hrel⟩

/-- Fault witness of the gated LeanMiri relation: the uninitialized
source. -/
def gatedFaultLM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    FaultEquivWitness (gatedRelLM verdictLM) where
  m := ()
  p := .uninitCast
  q := .onePointFive
  c := .p2
  kind := .undefined
  gate := rfl
  execA := ⟨rfl, trusted_uninit_outcome⟩
  execR := by
    obtain ⟨orr, hr, hc⟩ :=
      gated_coupled_LM verdictLM h .uninitCast .onePointFive rfl
    rw [trusted_uninit_outcome] at hc
    have hk : orr = .fault .undefined := (hc.fault_iff .undefined).mp rfl
    subst hk
    exact ⟨rfl, hr⟩

/-- Forward coupling of the gated MiniRust relation. -/
theorem gated_fwd_MR (m : WideSlice.MrMem) (p : Prog) (q : Query)
    (c : Pick) (out : ExecOutcome4 Nat Unit) (hg : gateMR m p q = true)
    (hR : gatedExecMR m p q c out) :
    c = Pick.p0 ∧
      ChoiceCoupledOutcomeRel gatedRetRel
        (fun (_ : Unit) (_ : Unit) => True) (trustedOutcome () p q) out := by
  obtain ⟨hc0, hR'⟩ := hR
  subst hc0
  obtain ⟨orr, hr, hc⟩ := gated_coupled_MR m p q hg
  have he : orr = out := Option.some.inj (hr.symm.trans hR')
  subst he
  exact ⟨rfl, hc⟩

/-- Fault reflection of the gated MiniRust relation. -/
theorem gated_rev_MR (m : WideSlice.MrMem) (p : Prog) (q : Query)
    (c : Pick) (k : CorrFaultKind) (hg : gateMR m p q = true)
    (hvc : c = Pick.p0) (hA : trustedOutcome () p q = .fault k) :
    gatedExecMR m p q c (.fault k) := by
  subst hvc
  obtain ⟨orr, hr, hc⟩ := gated_coupled_MR m p q hg
  rw [hA] at hc
  have hk : orr = .fault k := (hc.fault_iff k).mp rfl
  subst hk
  exact ⟨rfl, hr⟩

/-- Forward coupling of the gated LeanMiri relation. -/
theorem gated_fwd_LM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) (_m : Unit) (p : Prog)
    (q : Query) (c : Pick) (out : ExecOutcome4 Nat Unit)
    (hg : gateLM .nondeterministic p q = true)
    (hR : gatedExecLM verdictLM () p q c out) :
    c = Pick.p2 ∧
      ChoiceCoupledOutcomeRel gatedRetRel
        (fun (_ : Unit) (_ : Unit) => True) (trustedOutcome () p q) out := by
  obtain ⟨hc0, hR'⟩ := hR
  subst hc0
  obtain ⟨orr, hr, hc⟩ := gated_coupled_LM verdictLM h p q hg
  have he : orr = out := Option.some.inj (hr.symm.trans hR')
  subst he
  exact ⟨rfl, hc⟩

/-- Fault reflection of the gated LeanMiri relation. -/
theorem gated_rev_LM
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) (_m : Unit) (p : Prog)
    (q : Query) (c : Pick) (k : CorrFaultKind)
    (hg : gateLM .nondeterministic p q = true) (hvc : c = Pick.p2)
    (hA : trustedOutcome () p q = .fault k) :
    gatedExecLM verdictLM () p q c (.fault k) := by
  subst hvc
  obtain ⟨orr, hr, hc⟩ := gated_coupled_LM verdictLM h p q hg
  rw [hA] at hc
  have hk : orr = .fault k := (hc.fault_iff k).mp rfl
  subst hk
  exact ⟨rfl, hr⟩

/-- Positive witness of the gated MiniRust relation: the NaN carrier. -/
def gatedPositiveMR : PositiveWitness gatedRelMR :=
  PositiveWitness.ofAnnealEvalGated .basic .bitsU32ToI32 .quietNaN .p0
    0x7fc00001 0x7fc00001 rfl rfl trusted_carrier_outcome
    ⟨rfl, congrArg outcome?
      (by decide +kernel :
        mrVerdict .basic .bitsU32ToI32 .quietNaN .p0 =
          some (.returns 0x7fc00001))⟩ rfl

/-- Fault witness of the gated MiniRust relation: the `f16` cast. -/
def gatedFaultMR : FaultEquivWitness gatedRelMR :=
  FaultEquivWitness.ofAnnealEvalGated .basic .f16ToF32 .onePointFive .p0
    .unsupported rfl rfl trusted_f16_outcome
    ⟨rfl, congrArg outcome?
      (by decide +kernel :
        mrVerdict .basic .f16ToF32 .onePointFive .p0 = some .unsupported)⟩

/-- The choice-gated bundle: the trusted machine verbatim against MiniRust
and against any certified LeanMiri presentation in nondeterministic mode
under the payload-preserving schedule. -/
def gatedBundleWith
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    DualCorrespondenceBundle Unit Prog Query Nat Unit (Nat × Nat)
      WideSlice.MrMem Pick Nat Unit Unit Pick Nat Unit :=
  DualCorrespondenceBundle.fromEquivGated halvesCodec halves halves
    trustedOutcome (fun _ => ()) (fun _ => ())
    (fun m p q => gateMR m p q = true)
    (fun _ p q => gateLM .nondeterministic p q = true)
    (fun _ _ _ c => c = Pick.p0) (fun _ _ _ c => c = Pick.p2)
    (fun _ _ _ => ⟨.p0, rfl⟩) (fun _ _ _ => ⟨.p2, rfl⟩) gatedExecMR
    (gatedExecLM verdictLM) gatedRetRel (fun _ _ => True) gatedRetRel
    (fun _ _ => True) (fun _ _ hr => hr) (fun _ _ hr => hr) gated_fwd_MR
    gated_rev_MR (gated_fwd_LM verdictLM h) (gated_rev_LM verdictLM h)
    gatedPositiveMR (gatedPositiveLM verdictLM h) gatedFaultMR
    (gatedFaultLM verdictLM h) rfl rfl none none (some ⟨gated_reverse_MR⟩)
    (some ⟨gated_reverse_LM verdictLM h⟩)

/-- The gated bundle is productive on both sides of both authorities:
the inhabited schedules give Anneal productivity and the recorded reverse
totality transfers it to the references. -/
theorem gatedBundle_productiveBoth_with
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat))
    (h : (sideLM verdictLM).check model = true) :
    (gatedBundleWith verdictLM h).mrRel.ProductiveBoth ∧
      (gatedBundleWith verdictLM h).lmRel.ProductiveBoth :=
  DualCorrespondenceBundle.fromEquivGated_productiveBoth_of_reverseTotal
    halvesCodec halves halves trustedOutcome (fun _ => ()) (fun _ => ())
    (fun m p q => gateMR m p q = true)
    (fun _ p q => gateLM .nondeterministic p q = true)
    (fun _ _ _ c => c = Pick.p0) (fun _ _ _ c => c = Pick.p2)
    (fun _ _ _ => ⟨.p0, rfl⟩) (fun _ _ _ => ⟨.p2, rfl⟩) gatedExecMR
    (gatedExecLM verdictLM) gatedRetRel (fun _ _ => True) gatedRetRel
    (fun _ _ => True) (fun _ _ hr => hr) (fun _ _ hr => hr) gated_fwd_MR
    gated_rev_MR (gated_fwd_LM verdictLM h) (gated_rev_LM verdictLM h)
    gatedPositiveMR (gatedPositiveLM verdictLM h) gatedFaultMR
    (gatedFaultLM verdictLM h) rfl rfl none none gated_reverse_MR
    (gated_reverse_LM verdictLM h)

/-- Sharpness of the choice gate: with an empty schedule the
uninitialized-source cast would be vacuously well-formed, although the
trusted machine faults on it; with the inhabited schedule it is not
well-formed. -/
theorem empty_schedule_is_vacuous
    (verdictLM : NanMode → Prog → Query → Pick → Option (Verdict Nat)) :
    (ModeParamStepRel.ofAnnealEvalGated (fun (_ : Unit) => ())
        (fun _ p q => gateLM .nondeterministic p q = true)
        (fun _ _ _ (_ : Pick) => False) trustedOutcome
        (gatedExecLM verdictLM) gatedRetRel
        (fun (_ : Unit) (_ : Unit) => True)).WellFormedAnneal ()
        .uninitCast .onePointFive ∧
      ¬ (gatedRelLM verdictLM).WellFormedAnneal () .uninitCast
        .onePointFive :=
  ⟨ModeParamStepRel.ofAnnealEvalGated_vacuous_of_empty_choice _ _ _ _ _ _ _
      (fun _ hf => hf),
   fun hwf =>
    ((ModeParamStepRel.ofAnnealEvalGated_wellFormedAnneal_iff
      (fun (_ : Unit) => ())
      (fun _ p q => gateLM .nondeterministic p q = true)
      (fun _ _ _ c => c = Pick.p2) trustedOutcome (gatedExecLM verdictLM)
      gatedRetRel (fun (_ : Unit) (_ : Unit) => True)
      (m := ()) (p := .uninitCast) (q := .onePointFive)
      ⟨.p2, rfl⟩).1.mp hwf) .undefined trusted_uninit_outcome⟩

end FloatCast

/-! ### C.10 Agreement of a float engine with the reference specification

`Engine` abstracts the primitive operations of an IEEE-754 engine over its
own format, bit-pattern, and error types. `Engine.agrees` compares an engine
with `Ref` on every corpus input, in both directions and in both NaN
modes; the cross-root kernel bridge instantiates it with the vendored
`Miri.Interpreter.FloatBits` engine, so the reference specification used
by the surface bundle is locked to the vendored engine primitive by
primitive, not only through the authority's observations. -/

namespace FloatCast

/-- Primitive operations of an IEEE-754 engine. -/
structure Engine : Type 1 where
  /-- Formats. -/
  F : Type
  /-- Bit patterns tagged with their format. -/
  B : Type
  /-- Errors. -/
  E : Type
  /-- `binary32`. -/
  f32 : F
  /-- `binary64`. -/
  f64 : F
  /-- Bit pattern of a format. -/
  ofBits : F → Nat → B
  /-- Raw bits of a pattern. -/
  bits : B → Nat
  /-- Preferred NaN of a format. -/
  preferredNaN : F → B
  /-- Decode a bit pattern (rejecting out-of-width encodings with `none`). -/
  decode : B → Option Ref.Decoded
  /-- Float-to-float conversion. -/
  convert : B → F → Except E B
  /-- NaN candidates for a result format, inputs, and NaN mode. -/
  nanChoices : F → List B → Bool → Except E (List B)
  /-- NaN adjustment under `floatNondeterministic` flag and oracle pick. -/
  adjustNaN : Bool → Nat → B → List B → Option B
  /-- Saturating float-to-integer conversion. -/
  toInteger : B → Nat → Bool → Except E Int
  /-- Integer-to-float conversion. -/
  fromInteger : F → Int → Except E B

namespace Engine

variable (G : Engine)

/-- The engine's format for a reference format. -/
def fmt : Ref.Fmt → G.F
  | .binary32 => G.f32
  | .binary64 => G.f64

/-- Decoding on raw bits. -/
def dec (src : Ref.Fmt) (b : Nat) : Option Ref.Decoded :=
  G.decode (G.ofBits (G.fmt src) b)

/-- Conversion on raw bits. -/
def conv (src dst : Ref.Fmt) (b : Nat) : Option Nat :=
  (G.convert (G.ofBits (G.fmt src) b) (G.fmt dst)).toOption.map G.bits

/-- NaN candidates on raw bits, for one input. -/
def choices (src dst : Ref.Fmt) (b : Nat) (flag : Bool) :
    Option (List Nat) :=
  (G.nanChoices (G.fmt dst) [G.ofBits (G.fmt src) b] flag).toOption.map
    (List.map G.bits)

/-- NaN adjustment on raw bits, for one input after conversion. -/
def adj (flag : Bool) (pick : Nat) (src dst : Ref.Fmt) (valBits inpBits : Nat) :
    Option Nat :=
  (G.adjustNaN flag pick (G.ofBits (G.fmt dst) valBits)
    [G.ofBits (G.fmt src) inpBits]).map G.bits

/-- Converted bit pattern of `src → dst` (falling back to `0` only if
conversion fails). -/
def refConvBits (src dst : Ref.Fmt) (b : Nat) : Nat :=
  (Ref.convert src dst b).getD 0

/-- Saturating float-to-integer conversion on raw bits. -/
def toInt (src : Ref.Fmt) (b w : Nat) (signed : Bool) : Option Int :=
  (G.toInteger (G.ofBits (G.fmt src) b) w signed).toOption

/-- Integer-to-float conversion to raw bits. -/
def fromInt (dst : Ref.Fmt) (v : Int) : Option Nat :=
  (G.fromInteger (G.fmt dst) v).toOption.map G.bits

/-- Agreement of `adjustNaN` with `Ref.adjustNaN` across all oracle picks
on `src → dst` for one input and NaN mode. -/
def adjAgrees (flag : Bool) (src dst : Ref.Fmt) (b : Nat) : Bool :=
  let v := refConvBits src dst b
  allPicks.all fun c =>
    decide (G.adj flag c.toNat src dst v b =
      Ref.adjustNaN flag c.toNat dst v [(src, b)])

/-- Agreement with `Ref` on the corpus input `q`: decoding, conversions in
both directions, NaN candidates and `adjustNaN` in both directions, both
modes, and all picks, saturating `toInteger` (`i32` and `u64`), and
`fromInteger` (`i32 → f32`, `i32 → f64`, and unsigned `u64 → f64`). -/
def agreesAt (q : Query) : Bool :=
  decide (G.dec .binary32 q.bits32 = Ref.decode .binary32 q.bits32) &&
  decide (G.dec .binary64 q.bits64 = Ref.decode .binary64 q.bits64) &&
  decide (G.conv .binary32 .binary64 q.bits32 =
    Ref.convert .binary32 .binary64 q.bits32) &&
  decide (G.conv .binary64 .binary32 q.bits64 =
    Ref.convert .binary64 .binary32 q.bits64) &&
  decide (G.choices .binary32 .binary64 q.bits32 true =
    Ref.nanChoices .binary64 [(.binary32, q.bits32)] true) &&
  decide (G.choices .binary32 .binary64 q.bits32 false =
    Ref.nanChoices .binary64 [(.binary32, q.bits32)] false) &&
  decide (G.choices .binary64 .binary32 q.bits64 true =
    Ref.nanChoices .binary32 [(.binary64, q.bits64)] true) &&
  decide (G.choices .binary64 .binary32 q.bits64 false =
    Ref.nanChoices .binary32 [(.binary64, q.bits64)] false) &&
  G.adjAgrees true .binary32 .binary64 q.bits32 &&
  G.adjAgrees false .binary32 .binary64 q.bits32 &&
  G.adjAgrees true .binary64 .binary32 q.bits64 &&
  G.adjAgrees false .binary64 .binary32 q.bits64 &&
  decide (G.toInt .binary32 q.bits32 32 true =
    Ref.toInteger .binary32 q.bits32 32 true) &&
  decide (G.toInt .binary64 q.bits64 64 false =
    Ref.toInteger .binary64 q.bits64 64 false) &&
  decide (G.fromInt .binary32 (signedOfBits 32 q.bits32) =
    Ref.fromInteger .binary32 (signedOfBits 32 q.bits32)) &&
  decide (G.fromInt .binary64 (signedOfBits 32 q.bits32) =
    Ref.fromInteger .binary64 (signedOfBits 32 q.bits32)) &&
  decide (G.fromInt .binary64 (Int.ofNat q.bits64) =
    Ref.fromInteger .binary64 (Int.ofNat q.bits64))

/-- Agreement with `Ref` on every corpus input, on both preferred NaNs, on
out-of-width decode rejection (`2^32` for `f32`, `2^64` for `f64`), and on
unsigned 64-bit overflow and tie-to-even rounding (`+∞ ↦ u64::MAX`,
`2^53 + 1 ↦ 2^53`, `2^53 + 3 ↦ 2^53 + 4`, `u64::MAX ↦ 2^64`). -/
def agrees : Bool :=
  decide (G.bits (G.preferredNaN G.f32) = Ref.preferredNaN .binary32) &&
  decide (G.bits (G.preferredNaN G.f64) = Ref.preferredNaN .binary64) &&
  decide (G.dec .binary32 (2 ^ 32) = none) &&
  decide (G.dec .binary64 (2 ^ 64) = none) &&
  decide (G.toInt .binary64 0x7ff0000000000000 64 false =
    some 0xffffffffffffffff) &&
  decide (G.fromInt .binary64 (2 ^ 53 + 1) = some 0x4340000000000000) &&
  decide (G.fromInt .binary64 (2 ^ 53 + 3) = some 0x4340000000000002) &&
  decide (G.fromInt .binary64 (2 ^ 64 - 1) = some 0x43f0000000000000) &&
  allQueries.all G.agreesAt

/-- `agrees` certifies every primitive checked by `agreesAt` and `agrees`
(preferred NaNs, out-of-width decode rejection, unsigned 64-bit overflow
and tie-to-even rounding, `decode`, `convert`, `nanChoices`, `adjustNaN`
across all picks, `toInteger`, and `fromInteger`), discarding none. -/
theorem agrees_sound (h : G.agrees = true) :
    G.bits (G.preferredNaN G.f32) = Ref.preferredNaN .binary32 ∧
    G.bits (G.preferredNaN G.f64) = Ref.preferredNaN .binary64 ∧
    G.dec .binary32 (2 ^ 32) = none ∧
    G.dec .binary64 (2 ^ 64) = none ∧
    G.toInt .binary64 0x7ff0000000000000 64 false =
      some 0xffffffffffffffff ∧
    G.fromInt .binary64 (2 ^ 53 + 1) = some 0x4340000000000000 ∧
    G.fromInt .binary64 (2 ^ 53 + 3) = some 0x4340000000000002 ∧
    G.fromInt .binary64 (2 ^ 64 - 1) = some 0x43f0000000000000 ∧
    ∀ (q : Query) (flag : Bool) (c : Pick),
      G.dec .binary32 q.bits32 = Ref.decode .binary32 q.bits32 ∧
      G.dec .binary64 q.bits64 = Ref.decode .binary64 q.bits64 ∧
      G.conv .binary32 .binary64 q.bits32 =
        Ref.convert .binary32 .binary64 q.bits32 ∧
      G.conv .binary64 .binary32 q.bits64 =
        Ref.convert .binary64 .binary32 q.bits64 ∧
      G.choices .binary32 .binary64 q.bits32 flag =
        Ref.nanChoices .binary64 [(.binary32, q.bits32)] flag ∧
      G.choices .binary64 .binary32 q.bits64 flag =
        Ref.nanChoices .binary32 [(.binary64, q.bits64)] flag ∧
      G.adj flag c.toNat .binary32 .binary64
          (refConvBits .binary32 .binary64 q.bits32) q.bits32 =
        Ref.adjustNaN flag c.toNat .binary64
          (refConvBits .binary32 .binary64 q.bits32)
          [(.binary32, q.bits32)] ∧
      G.adj flag c.toNat .binary64 .binary32
          (refConvBits .binary64 .binary32 q.bits64) q.bits64 =
        Ref.adjustNaN flag c.toNat .binary32
          (refConvBits .binary64 .binary32 q.bits64)
          [(.binary64, q.bits64)] ∧
      G.toInt .binary32 q.bits32 32 true =
        Ref.toInteger .binary32 q.bits32 32 true ∧
      G.toInt .binary64 q.bits64 64 false =
        Ref.toInteger .binary64 q.bits64 64 false ∧
      G.fromInt .binary32 (signedOfBits 32 q.bits32) =
        Ref.fromInteger .binary32 (signedOfBits 32 q.bits32) ∧
      G.fromInt .binary64 (signedOfBits 32 q.bits32) =
        Ref.fromInteger .binary64 (signedOfBits 32 q.bits32) ∧
      G.fromInt .binary64 (Int.ofNat q.bits64) =
        Ref.fromInteger .binary64 (Int.ofNat q.bits64) := by
  simp only [agrees, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h32, h64⟩, ho32⟩, ho64⟩, hinf⟩, ht1⟩, ht3⟩, hmax⟩, hall⟩ := h
  refine ⟨h32, h64, ho32, ho64, hinf, ht1, ht3, hmax, fun q flag c => ?_⟩
  have hq := List.all_eq_true.mp hall q (by cases q <;> decide)
  simp only [agreesAt, Bool.and_eq_true, decide_eq_true_eq] at hq
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd32, hd64⟩, hc1⟩, hc2⟩, hct1⟩, hcf1⟩, hct2⟩, hcf2⟩,
    hat1⟩, haf1⟩, hat2⟩, haf2⟩, hti1⟩, hti2⟩, hfi1⟩, hfi2⟩, hfu64⟩ := hq
  have hcMem : c ∈ allPicks := by cases c <;> decide
  cases flag
  · exact ⟨hd32, hd64, hc1, hc2, hcf1, hcf2,
      of_decide_eq_true (List.all_eq_true.mp haf1 c hcMem),
      of_decide_eq_true (List.all_eq_true.mp haf2 c hcMem),
      hti1, hti2, hfi1, hfi2, hfu64⟩
  · exact ⟨hd32, hd64, hc1, hc2, hct1, hct2,
      of_decide_eq_true (List.all_eq_true.mp hat1 c hcMem),
      of_decide_eq_true (List.all_eq_true.mp hat2 c hcMem),
      hti1, hti2, hfi1, hfi2, hfu64⟩

end Engine

/-- The reference specification is itself an engine, and agrees with
itself (the agreement check is therefore satisfiable). -/
def refEngine : Engine where
  F := Ref.Fmt
  B := Ref.Fmt × Nat
  E := Unit
  f32 := .binary32
  f64 := .binary64
  ofBits := fun f b => (f, b)
  bits := fun p => p.2
  preferredNaN := fun f => (f, Ref.preferredNaN f)
  decode := fun p => Ref.decode p.1 p.2
  convert := fun p dst =>
    match Ref.convert p.1 dst p.2 with
    | some b => .ok (dst, b)
    | none => .error ()
  nanChoices := fun f inputs flag =>
    match Ref.nanChoices f inputs flag with
    | some l => .ok (l.map fun b => (f, b))
    | none => .error ()
  adjustNaN := fun flag pick v inputs =>
    (Ref.adjustNaN flag pick v.1 v.2 inputs).map fun b => (v.1, b)
  toInteger := fun p w signed =>
    match Ref.toInteger p.1 p.2 w signed with
    | some i => .ok i
    | none => .error ()
  fromInteger := fun f v =>
    match Ref.fromInteger f v with
    | some b => .ok (f, b)
    | none => .error ()

/-- The reference engine passes the agreement check. -/
theorem refEngine_agrees : refEngine.agrees = true := by decide +kernel

/-- An engine that answers the deterministic NaN mode with the
nondeterministic candidates fails the agreement check, so the check
separates the two NaN modes. -/
theorem modeSwapped_engine_disagrees :
    { refEngine with
        nanChoices := fun f inputs _ => refEngine.nanChoices f inputs true
      }.agrees = false := by
  decide +kernel

end FloatCast

/-! ## D. Laws of the abstraction on the corpus codecs and relations

Every remaining law of `Anneal.DualCorrespondenceBundle` is applied to the
concrete codecs, outcomes, relations, and witnesses of the two families. -/

namespace BundleLaws

open Trusted.Effect
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.DualCorrespondenceBundle
open Corpus

/-! ### D.1 Codec laws on the carrier codec -/

/-- The carrier codec is tight. -/
theorem halvesCodec_tight : halvesCodec.TightValidRep :=
  looseHalvesCodec.tighten_tightValidRep

/-- The permissive codec is not tight: `(0, 2^32)` is declared valid but
decodes to nothing. -/
theorem looseHalvesCodec_not_tight : ¬ looseHalvesCodec.TightValidRep := by
  intro h
  obtain ⟨a, ha⟩ := h (0, 4294967296) True.intro
  have hn : looseHalvesCodec.decode (0, 4294967296) = none := rfl
  rw [hn] at ha
  cases ha

/-- `tighten` fixes exactly the tight codecs. -/
theorem tighten_fixed_points :
    halvesCodec.tighten = halvesCodec ∧
      looseHalvesCodec.tighten ≠ looseHalvesCodec :=
  ⟨(CodecLaws.tighten_eq_self_iff halvesCodec).mpr halvesCodec_tight,
   fun h => looseHalvesCodec_not_tight
    ((CodecLaws.tighten_eq_self_iff looseHalvesCodec).mp h)⟩

/-- Equal codecs have equal data (`CodecLaws.mk.injEq`). -/
theorem codec_data_of_eq {α β : Type} (c₁ c₂ : CodecLaws α β)
    (h : c₁ = c₂) :
    c₁.encode = c₂.encode ∧ c₁.decode = c₂.decode ∧
      c₁.ValidRep = c₂.ValidRep :=
  Eq.mp
    (CodecLaws.mk.injEq c₁.encode c₁.decode c₁.ValidRep c₁.decode_encode
      c₁.encode_valid c₁.encode_decode_of_valid c₂.encode c₂.decode
      c₂.ValidRep c₂.decode_encode c₂.encode_valid
      c₂.encode_decode_of_valid) h

/-- The permissive and the tight carrier codecs differ, in their validity
predicate only. -/
theorem loose_ne_tight_validRep :
    looseHalvesCodec ≠ halvesCodec ∧
      looseHalvesCodec.encode = halvesCodec.encode ∧
      looseHalvesCodec.decode = halvesCodec.decode := by
  refine ⟨fun h => ?_, rfl, rfl⟩
  have hv := (codec_data_of_eq _ _ h).2.2
  have hbad : halvesCodec.ValidRep (0, 4294967296) := by
    rw [← hv]
    exact True.intro
  obtain ⟨_, a, ha⟩ := hbad
  have hn : looseHalvesCodec.decode (0, 4294967296) = none := rfl
  rw [hn] at ha
  cases ha

/-- A codec is one constructor application (`CodecLaws.mk.sizeOf_spec`). -/
theorem codec_sizeOf {α β : Type} (c : CodecLaws α β) : sizeOf c = 1 :=
  CodecLaws.mk.sizeOf_spec c.encode c.decode c.ValidRep c.decode_encode
    c.encode_valid c.encode_decode_of_valid

/-- Valid representations of the carrier codec are exactly the halves of
a number. -/
theorem halves_validRep_iff (b : Nat × Nat) :
    halvesCodec.ValidRep b ↔ ∃ a, halves a = b :=
  CodecLaws.tightValidRep_validRep_iff halvesCodec_tight b

/-- Decoding the halves `(0, 3)` and encoding `3` are equivalent facts. -/
theorem halves_decode_three :
    halvesCodec.decode (0, 3) = some 3 ↔ halvesCodec.encode 3 = (0, 3) :=
  halvesCodec.decode_eq_some_iff ⟨True.intro, 3, rfl⟩

/-- Every number, in particular the `isize::MAX` length `2^61`, has a
valid representation that decodes to it. -/
theorem halves_decode_surjective :
    ∃ b, halvesCodec.ValidRep b ∧ halvesCodec.decode b = some (2 ^ 61) :=
  halvesCodec.decode_surjective (2 ^ 61)

/-- Valid representations decoding to the same number are equal. -/
theorem halves_decode_injective {b b' : Nat × Nat} {a : Nat}
    (hb : halvesCodec.ValidRep b) (hb' : halvesCodec.ValidRep b')
    (h : halvesCodec.decode b = some a)
    (h' : halvesCodec.decode b' = some a) : b = b' :=
  halvesCodec.decode_injective_of_valid hb hb' h h'

/-- Unit and associativity laws of codec composition on the carrier. -/
theorem halves_comp_laws :
    (CodecLaws.id Nat).comp halvesCodec = halvesCodec ∧
      halvesCodec.comp (CodecLaws.id (Nat × Nat)) = halvesCodec ∧
      ((CodecLaws.id Nat).comp halvesCodec).comp
          (CodecLaws.id (Nat × Nat)) =
        (CodecLaws.id Nat).comp
          (halvesCodec.comp (CodecLaws.id (Nat × Nat))) :=
  ⟨CodecLaws.comp_id_left halvesCodec, CodecLaws.comp_id_right halvesCodec,
   CodecLaws.comp_assoc (CodecLaws.id Nat) halvesCodec
    (CodecLaws.id (Nat × Nat))⟩

/-- Tightness is preserved by composition and by products. -/
theorem halves_tight_closure :
    ((CodecLaws.id Nat).comp halvesCodec).TightValidRep ∧
      (halvesCodec.prod halvesCodec).TightValidRep :=
  ⟨CodecLaws.comp_tightValidRep _ _ (CodecLaws.id_tightValidRep Nat)
      halvesCodec_tight,
   CodecLaws.prod_tightValidRep _ _ halvesCodec_tight halvesCodec_tight⟩

/-- Product laws: identity, and interchange with composition for tight
right factors and after tightening. -/
theorem halves_prod_laws :
    (CodecLaws.id Nat).prod (CodecLaws.id Nat) = CodecLaws.id (Nat × Nat) ∧
      ((CodecLaws.id Nat).comp looseHalvesCodec.tighten).prod
          ((CodecLaws.id Nat).comp looseHalvesCodec.tighten) =
        ((CodecLaws.id Nat).prod (CodecLaws.id Nat)).comp
          (looseHalvesCodec.tighten.prod looseHalvesCodec.tighten) ∧
      (((CodecLaws.id Nat).comp looseHalvesCodec).prod
          ((CodecLaws.id Nat).comp looseHalvesCodec)).tighten =
        (((CodecLaws.id Nat).prod (CodecLaws.id Nat)).comp
          (looseHalvesCodec.prod looseHalvesCodec)).tighten :=
  ⟨CodecLaws.prod_id Nat Nat, CodecLaws.prod_comp_tighten _ _ _ _,
   CodecLaws.tighten_prod_comp_interchange _ _ _ _⟩

/-- Without tightness the interchange law fails, so it is not a law of
arbitrary codecs. -/
theorem interchange_needs_tightness :
    ¬ ∀ (c₁ : CodecLaws Unit Bool) (d₁ : CodecLaws Bool Bool)
        (c₂ : CodecLaws Unit Unit) (d₂ : CodecLaws Unit Bool),
        (c₁.comp d₁).prod (c₂.comp d₂) = (c₁.prod c₂).comp (d₁.prod d₂) := by
  intro h
  obtain ⟨c₁, d₁, c₂, d₂, hne⟩ :=
    CodecLaws.prod_comp_not_eq_without_tightValidRep
  exact hne (h c₁ d₁ c₂ d₂)

/-- The NaN mode and its `floatNondeterministic` flag as an equivalence
codec. -/
def modeCodec : CodecLaws FloatCast.NanMode Bool :=
  CodecLaws.ofEquiv FloatCast.NanMode.flag FloatCast.modeOfBool
    (fun m => by cases m <;> rfl) (fun b => by cases b <;> rfl)

/-- Laws of equivalence codecs on `modeCodec`. -/
theorem modeCodec_laws (b : Bool) :
    modeCodec.decode b = some (FloatCast.modeOfBool b) ∧
      (CodecLaws.ofEquiv_symm FloatCast.NanMode.flag FloatCast.modeOfBool
        (fun m => by cases m <;> rfl)
        (fun b => by cases b <;> rfl)).TightValidRep ∧
      (CodecLaws.ofEquiv_symm FloatCast.NanMode.flag FloatCast.modeOfBool
          (fun m => by cases m <;> rfl)
          (fun b => by cases b <;> rfl)).comp modeCodec =
        CodecLaws.id Bool ∧
      modeCodec.tighten = modeCodec ∧
      (CodecLaws.id Nat).tighten = CodecLaws.id Nat :=
  ⟨CodecLaws.ofEquiv_decode _ _ _ _ b,
   CodecLaws.ofEquiv_symm_tightValidRep _ _ _ _,
   CodecLaws.symm_comp_ofEquiv _ _ _ _, CodecLaws.tighten_ofEquiv _ _ _ _,
   CodecLaws.tighten_id Nat⟩

/-! ### D.2 The fault codec onto the trusted fault effect -/

/-- The fault kinds of corpus verdicts encode to the trusted fault
requests, fuel exhaustion decodes to no fault, and the codec is tight. -/
theorem fault_codec_on_verdicts :
    mirFailCodec.encode
        (faultKindOf (some (Verdict.undefinedBehavior : Verdict Nat))) =
        FailReq.fail FailureKind.ub ∧
      mirFailCodec.encode
        (faultKindOf (some (Verdict.unsupported : Verdict Nat))) =
        FailReq.fail FailureKind.unsupported ∧
      mirFailCodec.decode (FailReq.fail FailureKind.outOfFuel) = none ∧
      mirFailCodec.tighten = mirFailCodec :=
  ⟨mirFailCodec_encode_undefined, mirFailCodec_encode_unsupported,
   mirFailCodec_decode_outOfFuel, mirFailCodec_tighten⟩

/-- The opposite orientation is lawful only without fuel exhaustion. -/
theorem fault_codec_orientation :
    (mirFailNonFuelCodec.decode .undefined).map Subtype.val =
        some (FailReq.fail FailureKind.ub) ∧
      (mirFailNonFuelCodec.decode .unsupported).map Subtype.val =
        some (FailReq.fail FailureKind.unsupported) ∧
      ¬ Nonempty (CodecLaws MirFailE.I CorrFaultKind) :=
  ⟨mirFailNonFuelCodec_decode_undefined,
   mirFailNonFuelCodec_decode_unsupported,
   fun ⟨c⟩ => not_codecLaws_mirFail_corrFaultKind c⟩

/-! ### D.3 The four-way outcome partition -/

/-- Outcomes of the trusted execution states. -/
theorem mirExecState_outcomes (s : MachineState) (r : MirReturn) :
    [ExecOutcome4.ofMirExecState (.running s),
      ExecOutcome4.ofMirExecState (.faulted .ub),
      ExecOutcome4.ofMirExecState (.faulted .unsupported),
      ExecOutcome4.ofMirExecState (.faulted .outOfFuel),
      ExecOutcome4.ofMirExecState (.halted (.normal r)),
      ExecOutcome4.ofMirExecState (.halted .panic),
      ExecOutcome4.ofMirExecState (.halted .abort)] =
    [none, some (.fault .undefined), some (.fault .unsupported), none,
      some (.normal r), some (.unwind ()), some (.fault .unsupported)] := by
  rw [ExecOutcome4.ofMirExecState_running,
    ExecOutcome4.ofMirExecState_faulted_ub,
    ExecOutcome4.ofMirExecState_faulted_unsupported,
    ExecOutcome4.ofMirExecState_faulted_outOfFuel,
    ExecOutcome4.ofMirExecState_halted_normal,
    ExecOutcome4.ofMirExecState_halted_panic,
    ExecOutcome4.ofMirExecState_halted_abort]

/-- No trusted state is observed as divergence; a trusted `.ub` fault is
the `undefined` classification exactly through the fault codec; a trusted
outcome is normal only if it is a normal return, and never an
undefined-behavior fault. -/
theorem mirOutcome_classification (r : MirReturn) :
    ExecOutcome4.ofMirExecState (.halted .panic) ≠ some .diverge ∧
      (ExecOutcome4.ofMirExecState (.faulted .ub) =
          some (.fault .undefined) ↔
        mirFailCodec.encode .undefined = FailReq.fail FailureKind.ub) ∧
      (ExecOutcome4.ofMirOutcome .panic = .normal r ↔
        (.panic : MirOutcome) = .normal r) ∧
      ExecOutcome4.ofMirOutcome .abort ≠ .fault .undefined :=
  ⟨ExecOutcome4.ofMirExecState_ne_diverge _,
   ExecOutcome4.ofMirExecState_faulted_iff .ub .undefined,
   ExecOutcome4.ofMirOutcome_eq_normal_iff .panic r,
   ExecOutcome4.ofMirOutcome_ne_undefined .abort⟩

/-- A corpus verdict denotes a normal return or a fault, never an unwind
or divergence. -/
theorem verdict_outcome_classes (v : Verdict Nat) :
    (∃ r, v.toOutcome = .normal r) ∨ (∃ k, v.toOutcome = .fault k) := by
  rcases ExecOutcome4.partition v.toOutcome with h | h | h | h
  · exact Or.inl h
  · obtain ⟨p, hp⟩ := h
    cases v <;> cases hp
  · exact Or.inr h
  · cases v <;> cases h

/-- `isFault` on a corpus verdict. -/
theorem verdict_isFault_iff (v : Verdict Nat) :
    v.toOutcome.isFault = true ↔ ∃ k, v.toOutcome = .fault k :=
  ExecOutcome4.isFault_iff v.toOutcome

/-- Constructor injectivity of outcomes. -/
theorem outcome_injectivity (a b : Nat) (k k' : CorrFaultKind) :
    ((ExecOutcome4.normal a : ExecOutcome4 Nat Unit) = .normal b → a = b) ∧
      ((ExecOutcome4.fault k : ExecOutcome4 Nat Unit) = .fault k' →
        k = k') ∧
      ((ExecOutcome4.unwind () : ExecOutcome4 Nat Unit) = .unwind () →
        () = ()) :=
  ⟨Eq.mp (ExecOutcome4.normal.injEq a b),
   Eq.mp (ExecOutcome4.fault.injEq k k'),
   Eq.mp (ExecOutcome4.unwind.injEq () ())⟩

/-- Sizes of outcomes and fault kinds. -/
theorem outcome_sizes (n : Nat) :
    sizeOf (ExecOutcome4.normal n : ExecOutcome4 Nat Unit) = 1 + n ∧
      sizeOf (ExecOutcome4.fault .undefined : ExecOutcome4 Nat Unit) = 2 ∧
      sizeOf (ExecOutcome4.fault .unsupported : ExecOutcome4 Nat Unit) =
        2 ∧
      sizeOf (ExecOutcome4.unwind () : ExecOutcome4 Nat Unit) = 2 ∧
      sizeOf (ExecOutcome4.diverge : ExecOutcome4 Nat Unit) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [ExecOutcome4.normal.sizeOf_spec]
    rfl
  · rw [ExecOutcome4.fault.sizeOf_spec, CorrFaultKind.undefined.sizeOf_spec]
  · rw [ExecOutcome4.fault.sizeOf_spec,
      CorrFaultKind.unsupported.sizeOf_spec]
  · rw [ExecOutcome4.unwind.sizeOf_spec]
    rfl
  · exact ExecOutcome4.diverge.sizeOf_spec

/-! ### D.4 The coupled outcome relation -/

/-- Coupling through the carrier codec weakens to coupling of outcome
classes, and flips to the converse payload relations. -/
theorem coupled_weaken_and_flip {oa orr : ExecOutcome4 Nat Unit}
    (h : ChoiceCoupledOutcomeRel
      (fun a r => halves r = halvesCodec.encode a)
      (fun (_ : Unit) (_ : Unit) => True) oa orr) :
    ChoiceCoupledOutcomeRel (fun (_ : Nat) (_ : Nat) => True)
        (fun (_ : Unit) (_ : Unit) => True) oa orr ∧
      ChoiceCoupledOutcomeRel (fun r a => halves r = halvesCodec.encode a)
        (fun (_ : Unit) (_ : Unit) => True) orr oa :=
  ⟨h.mono (fun _ _ _ => True.intro) (fun _ _ hu => hu), h.flip⟩

/-- A normal return is never coupled with a fault, and coupled normal
returns are exactly the related ones. -/
theorem coupled_classes (a r : Nat) :
    (ChoiceCoupledOutcomeRel (fun (x : Nat) (y : Nat) => x = y)
        (fun (_ : Unit) (_ : Unit) => True) (.normal a)
        (.fault .undefined) ↔ False) ∧
      (ChoiceCoupledOutcomeRel (fun (x : Nat) (y : Nat) => x = y)
        (fun (_ : Unit) (_ : Unit) => True) (.normal a) (.normal r) ↔
        a = r) :=
  ⟨ChoiceCoupledOutcomeRel.iff_sameClass,
   ChoiceCoupledOutcomeRel.iff_sameClass⟩

/-! ### D.5 Simulations and witnesses of the wide-slice bundle -/

/-- Exact behavioral equality of the surface wide-slice bundle from its
recorded reverse totality: divergence agrees along every choice. -/
theorem ws_exact_diverge :
    WideSlice.bundle.mrRel.ExecA (.basic, .safe) .reborrow .tooBig ()
        .diverge ↔
      WideSlice.bundle.mrRel.ExecR (.basic, .safe) .reborrow .tooBig ()
        .diverge :=
  (WideSlice.bundle.mrSim.exactBehaviorEq_of_reverseTotal?
    (m := (.basic, .safe)) (p := .reborrow) (q := .tooBig) rfl
    rfl).diverge_iff ()

/-- The total evaluators of the MiniRust side form a deterministic
simulation, which records reverse totality. -/
theorem ws_deterministic_sim_reverse :
    (ModeStepSim.fromDeterministicEval
      (fun m p q => WideSlice.sideMR.gate m p q = true)
      (fun (m : WideSlice.MrMem × WideSlice.Regime) p q (_ : Unit) =>
        totalOutcome (WideSlice.annealVerdict m.2 p q ()))
      (fun m p q c => totalOutcome (WideSlice.mrVerdict m p q c))
      (fun a r => halves r = halvesCodec.encode a)
      (fun (_ : Unit) (_ : Unit) => True)
      (fun m p q c hg =>
        WideSlice.sideMR.detCoupled WideSlice.model ()
          WideSlice.sideMR_sim (fun _ _ _ _ => rfl) m p q c
          hg)).reverse_total?.isSome = true :=
  ModeStepSim.fromDeterministicEval_reverse_total?_isSome _ _ _ _ _ _

/-- Equal witnesses have equal data (`mk.injEq` of the four witness
structures). -/
theorem witness_data_of_eq
    {R : ModeParamStepRel (WideSlice.MrMem × WideSlice.Regime)
      WideSlice.Prog WideSlice.Query Unit Nat Nat Unit Unit}
    (p₁ p₂ : PositiveWitness R) (f₁ f₂ : FaultEquivWitness R)
    (s₁ s₂ : ModeSensitivityWitness R) (d₁ d₂ : FlipDirectionWitness R)
    (hp : p₁ = p₂) (hf : f₁ = f₂) (hs : s₁ = s₂) (hd : d₁ = d₂) :
    p₁.p = p₂.p ∧ f₁.kind = f₂.kind ∧ s₁.m₂ = s₂.m₂ ∧
      d₁.pFault = d₂.pFault :=
  ⟨(Eq.mp (PositiveWitness.mk.injEq p₁.m p₁.p p₁.q p₁.c p₁.gate p₁.wf
      p₁.agree p₂.m p₂.p p₂.q p₂.c p₂.gate p₂.wf p₂.agree) hp).2.1,
   (Eq.mp (FaultEquivWitness.mk.injEq f₁.m f₁.p f₁.q f₁.c f₁.kind f₁.gate
      f₁.execA f₁.execR f₂.m f₂.p f₂.q f₂.c f₂.kind f₂.gate f₂.execA
      f₂.execR) hf).2.2.2.2,
   (Eq.mp (ModeSensitivityWitness.mk.injEq s₁.m₁ s₁.m₂ s₁.p s₁.q s₁.c
      s₁.gate₁ s₁.gate₂ s₁.flips s₂.m₁ s₂.m₂ s₂.p s₂.q s₂.c s₂.gate₁
      s₂.gate₂ s₂.flips) hs).2.1,
   by cases hd; rfl⟩

/-- The round-trip witness and the designated positive witness of the
MiniRust side are different witnesses: their programs differ. -/
theorem ws_positive_witnesses_differ :
    WideSlice.mrRoundTripPositive ≠
      WideSlice.sideMR.positive WideSlice.model WideSlice.sideMR_check := by
  intro h
  have hp := (Eq.mp (PositiveWitness.mk.injEq _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    h).2.1
  have hp' : WideSlice.Prog.roundTrip = WideSlice.Prog.reborrow := hp
  cases hp'

end BundleLaws

/-! ### D.6 Structural laws of relations, simulations, witnesses, and
bundles -/

namespace BundleLaws

open Anneal.DualCorrespondenceBundle
open Corpus

/-- Every corpus verdict is coupled with itself. -/
theorem verdict_self_coupled (v : Verdict Nat) :
    ChoiceCoupledOutcomeRel (fun (x : Nat) (y : Nat) => x = y)
      (fun (_ : Unit) (_ : Unit) => True) v.toOutcome v.toOutcome :=
  ChoiceCoupledOutcomeRel.refl (fun _ => rfl) (fun _ => True.intro) _

/-- Fault kinds are recovered from their constructor index. -/
theorem faultKind_ofNat_ctorIdx (k : CorrFaultKind) :
    CorrFaultKind.ofNat k.ctorIdx = k :=
  CorrFaultKind.ofNat_ctorIdx k

/-- Anneal productivity alone does not give reference productivity: the
corpus bundles therefore establish `ProductiveBoth` from their
certificates. -/
theorem productiveAnneal_does_not_give_productiveRef :
    ¬ ∀ (B : DualCorrespondenceBundle Unit Unit Nat Unit Unit Unit Unit Unit
        Unit Unit Unit Unit Unit Unit),
        B.mrRel.ProductiveAnneal → B.mrRel.ProductiveRef := by
  intro h
  obtain ⟨B, hA, _, hnR, _⟩ :=
    DualCorrespondenceBundle.fromEquiv_admits_stuck_ref
  exact hnR (h B hA)

/-- Equal step relations have equal components
(`ModeParamStepRel.mk.injEq`). -/
theorem rel_data_of_eq {Mode Prog Query Choice RetA RetR : Type}
    (R₁ R₂ : ModeParamStepRel Mode Prog Query Choice RetA RetR Unit Unit)
    (h : R₁ = R₂) :
    R₁.SupportGate = R₂.SupportGate ∧ R₁.ExecA = R₂.ExecA ∧
      R₁.ExecR = R₂.ExecR ∧ R₁.RetRel = R₂.RetRel ∧
      R₁.UnwRel = R₂.UnwRel :=
  Eq.mp
    (ModeParamStepRel.mk.injEq R₁.SupportGate R₁.ExecA R₁.ExecR R₁.RetRel
      R₁.UnwRel R₂.SupportGate R₂.ExecA R₂.ExecR R₂.RetRel R₂.UnwRel) h

/-- The choice-gated relation and the mode-model relation of the
float-cast MiniRust side are different relations: only the latter has an
Anneal execution along oracle pick `1`. -/
theorem gated_rel_ne_mode_rel :
    FloatCast.gatedRelMR ≠ FloatCast.sideMR.rel FloatCast.model := by
  intro h
  have hA := (rel_data_of_eq _ _ h).2.1
  have hex : (FloatCast.sideMR.rel FloatCast.model).ExecA .basic
      .bitsU32ToI32 .quietNaN .p1 (.normal 0x7fc00001) :=
    Side.execA_of_verdict FloatCast.model FloatCast.sideMR
      (v := .returns 0x7fc00001) (by decide +kernel)
  rw [← hA] at hex
  have hc : FloatCast.Pick.p1 = FloatCast.Pick.p0 := hex.1
  cases hc

/-- A step relation is one constructor application. -/
theorem rel_sizeOf {Mode Prog Query Choice RetA RetR : Type}
    (R : ModeParamStepRel Mode Prog Query Choice RetA RetR Unit Unit) :
    sizeOf R = 1 := by
  cases R
  exact ModeParamStepRel.mk.sizeOf_spec _ _ _ _ _

/-- Equal simulations record the same reverse totality
(`ModeStepSim.mk.injEq`). -/
theorem sim_reverse_of_eq {Mode Prog Query Choice RetA RetR : Type}
    {R : ModeParamStepRel Mode Prog Query Choice RetA RetR Unit Unit}
    (S₁ S₂ : ModeStepSim R) (h : S₁ = S₂) :
    S₁.reverse_total? = S₂.reverse_total? :=
  Eq.mp
    (ModeStepSim.mk.injEq S₁.forward_total S₁.reverse_fault_total
      S₁.reverse_total? S₂.forward_total S₂.reverse_fault_total
      S₂.reverse_total?) h

/-- Forgetting the recorded reverse totality changes the simulation. -/
theorem ws_sim_ne_without_reverse :
    WideSlice.bundle.mrSim ≠
      { WideSlice.bundle.mrSim with reverse_total? := none } := by
  intro h
  have hr := sim_reverse_of_eq _ _ h
  have hs : WideSlice.bundle.mrSim.reverse_total?.isSome = true := rfl
  rw [hr] at hs
  cases hs

/-- A simulation has positive size. -/
theorem sim_sizeOf_pos {Mode Prog Query Choice RetA RetR : Type}
    {R : ModeParamStepRel Mode Prog Query Choice RetA RetR Unit Unit}
    (S : ModeStepSim R) : 0 < sizeOf S := by
  cases S
  rw [ModeStepSim.mk.sizeOf_spec]
  omega

/-- Witnesses have positive size (`mk.sizeOf_spec` of the four witness
structures). -/
theorem witness_sizeOf_pos {Mode Prog Query Choice RetA RetR : Type}
    {R : ModeParamStepRel Mode Prog Query Choice RetA RetR Unit Unit}
    (p : PositiveWitness R) (f : FaultEquivWitness R)
    (s : ModeSensitivityWitness R) (d : FlipDirectionWitness R) :
    0 < sizeOf p ∧ 0 < sizeOf f ∧ 0 < sizeOf s ∧ 0 < sizeOf d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases p
    rw [PositiveWitness.mk.sizeOf_spec]
    omega
  · cases f
    rw [FaultEquivWitness.mk.sizeOf_spec]
    omega
  · cases s
    rw [ModeSensitivityWitness.mk.sizeOf_spec]
    omega
  · cases d
    rw [FlipDirectionWitness.mk.sizeOf_spec]
    omega

/-- Equal flip-direction guards have equal data
(`FlipDirectionWitness.mk.injEq`). -/
theorem flip_data_of_eq {Mode Prog Query Choice RetA RetR : Type}
    {R : ModeParamStepRel Mode Prog Query Choice RetA RetR Unit Unit}
    (d₁ d₂ : FlipDirectionWitness R) (h : d₁ = d₂) :
    d₁.m = d₂.m ∧ d₁.pOk = d₂.pOk ∧ d₁.qOk = d₂.qOk :=
  have hall := Eq.mp
    (FlipDirectionWitness.mk.injEq d₁.m d₁.pOk d₁.qOk d₁.cOk d₁.pFault
      d₁.qFault d₁.cFault d₁.kind d₁.gateOk d₁.gateFault d₁.okAgree
      d₁.wfOkA d₁.wfOkR d₁.faultA d₁.faultR d₁.modeSensitivity? d₂.m d₂.pOk
      d₂.qOk d₂.cOk d₂.pFault d₂.qFault d₂.cFault d₂.kind d₂.gateOk
      d₂.gateFault d₂.okAgree d₂.wfOkA d₂.wfOkR d₂.faultA d₂.faultR
      d₂.modeSensitivity?) h
  ⟨hall.1, hall.2.1, hall.2.2.1⟩

/-- Equal bundles have equal codecs
(`DualCorrespondenceBundle.mk.injEq`). -/
theorem bundle_codec_of_eq
    {ModeA Prog Query ModeMR ChoiceMR ModeLM ChoiceLM : Type}
    (B₁ B₂ : DualCorrespondenceBundle ModeA Prog Query Nat Unit (Nat × Nat)
      ModeMR ChoiceMR Nat Unit ModeLM ChoiceLM Nat Unit)
    (h : B₁ = B₂) : B₁.codec = B₂.codec :=
  (Eq.mp
    (DualCorrespondenceBundle.mk.injEq B₁.codec B₁.repMR B₁.repLM B₁.mrRel
      B₁.lmRel B₁.mrSim B₁.lmSim B₁.mr_ret_codec B₁.lm_ret_codec
      B₁.toAnnealMR B₁.toAnnealLM B₁.ExecAnneal B₁.anneal_exec_coherent
      B₁.mrPositive B₁.lmPositive B₁.mrFault B₁.lmFault B₁.mrFlip B₁.lmFlip
      B₂.codec B₂.repMR B₂.repLM B₂.mrRel B₂.lmRel B₂.mrSim B₂.lmSim
      B₂.mr_ret_codec B₂.lm_ret_codec B₂.toAnnealMR B₂.toAnnealLM
      B₂.ExecAnneal B₂.anneal_exec_coherent B₂.mrPositive B₂.lmPositive
      B₂.mrFault B₂.lmFault B₂.mrFlip B₂.lmFlip) h).1

/-- Idempotence of bundle tightening, read on the codec. -/
theorem ws_tighten_codec_idem :
    WideSlice.bundle.tightenCodec.tightenCodec.codec =
      WideSlice.bundle.tightenCodec.codec :=
  bundle_codec_of_eq _ _ WideSlice.bundle.tightenCodec_idem

/-- A bundle has positive size. -/
theorem bundle_sizeOf_pos
    {ModeA Prog Query ModeMR ChoiceMR ModeLM ChoiceLM : Type}
    (B : DualCorrespondenceBundle ModeA Prog Query Nat Unit (Nat × Nat)
      ModeMR ChoiceMR Nat Unit ModeLM ChoiceLM Nat Unit) :
    0 < sizeOf B := by
  cases B
  rw [DualCorrespondenceBundle.mk.sizeOf_spec]
  omega

/-- Both mode-sensitivity transport strategies are single constructor
applications. -/
theorem transport_sizeOf {Mode Prog Query Choice RetX RetA RetR : Type}
    {R₁ : ModeParamStepRel Mode Prog Query Choice RetX RetA Unit Unit}
    {R₂ : ModeParamStepRel Mode Prog Query Choice RetA RetR Unit Unit}
    {ms? : Option (ModeSensitivityWitness R₂)}
    (t : DualCorrespondenceBundle.ModeSensitivityTransport R₁ R₂ ms?) :
    sizeOf t = 1 := by
  cases t with
  | faultFlip hf =>
    exact
      DualCorrespondenceBundle.ModeSensitivityTransport.faultFlip.sizeOf_spec
        hf
  | reverseTotal hrev hUnw =>
    exact
      DualCorrespondenceBundle.ModeSensitivityTransport.reverseTotal.sizeOf_spec
        hrev hUnw

/-! ### D.7 The worked instances of the abstraction -/

/-- The worked NaN relation is a simulation with reverse totality. -/
def exampleNanSimMR : ModeStepSim Example.nanMrRel where
  forward_total := Example.nanMrRel_forward
  reverse_fault_total := fun m p q c k hg hA => by
    obtain ⟨outR, hR, hc⟩ := Example.nanMrRel_reverse m p q c _ hg hA
    have hk : outR = .fault k := (hc.fault_iff k).mp rfl
    rw [hk] at hR
    exact hR
  reverse_total? := some ⟨Example.nanMrRel_reverse⟩

/-- The worked NaN relation of the second authority, likewise. -/
def exampleNanSimLM : ModeStepSim Example.nanLmRel where
  forward_total := Example.nanLmRel_forward
  reverse_fault_total := fun m p q c k hg hA => by
    obtain ⟨outR, hR, hc⟩ := Example.nanLmRel_reverse m p q c _ hg hA
    have hk : outR = .fault k := (hc.fault_iff k).mp rfl
    rw [hk] at hR
    exact hR
  reverse_total? := some ⟨Example.nanLmRel_reverse⟩

/-- Both worked NaN simulations satisfy the fault-equivalence claim. -/
theorem example_nan_faultEquiv :
    FaultEquivClaim Example.nanMrRel ∧ FaultEquivClaim Example.nanLmRel :=
  ⟨exampleNanSimMR.faultEquivClaim, exampleNanSimLM.faultEquivClaim⟩

/-- The worked NaN bundle is nondeterministic at `q = 1`, so the
determinism premise of three-way agreement fails there. -/
theorem example_nan_not_deterministic :
    ¬ ∀ out out', Example.nanBundle.ExecAnneal true () 1 out →
        Example.nanBundle.ExecAnneal true () 1 out' → out = out' := by
  intro h
  have he := h _ _ Example.nanBundle_nondet.1 Example.nanBundle_nondet.2
  cases he

/-- Instances of the worked division bundle: strict division by zero
faults in both authorities alike, mode sensitivity and reverse totality
are recorded, and every input has an execution. -/
theorem example_div_instances :
    ((∃ c, Example.divBundle.mrRel.ExecR true () (7, 0) c
          (.fault .undefined)) ↔
        (∃ c, Example.divBundle.lmRel.ExecR true () (7, 0) c
          (.fault .undefined))) ∧
      (∃ w, Example.divBundle.mrFlip.modeSensitivity? = some w) ∧
      (∃ r, Example.divBundle.mrSim.reverse_total? = some r) ∧
      (∃ c out, Example.divBundle.mrRel.ExecA true () (1, 0) c out) ∧
      (∃ c out, Example.gatedDivBundle.mrRel.ExecR true () (1, 0) c out) :=
  ⟨Example.divBundle_fault_iff true 7,
   Option.isSome_iff_exists.mp Example.divBundle_modeSensitive.1,
   Option.isSome_iff_exists.mp Example.divBundle_reverseTotal.1,
   Example.divBundle_productiveBoth.1.1 true () (1, 0) True.intro,
   Example.gatedDivBundle_productiveBoth.1.2 true () (1, 0) True.intro⟩

/-- Instances of the worked NaN bundle: cross-authority well-formedness
at the faulting query, normal equivalence at payload `1`, productivity,
and a codec fixed by tightening. -/
theorem example_nan_instances :
    (Example.nanBundle.mrRel.WellFormedRef ((), true) () 0 ↔
        Example.nanBundle.lmRel.WellFormedRef (true, ()) () 0) ∧
      ((∃ c r, Example.nanBundle.mrRel.ExecR ((), true) () 1 c (.normal r) ∧
            Example.nanBundle.mrRel.RetRel 1 r) ↔
        (∃ c r, Example.nanBundle.lmRel.ExecR (true, ()) () 1 c
            (.normal r) ∧ Example.nanBundle.lmRel.RetRel 1 r)) ∧
      (∃ c out, Example.nanBundle.lmRel.ExecR (true, ()) () 1 c out) ∧
      Example.nanRepCodec.tighten = Example.nanRepCodec :=
  ⟨Example.nanBundle_crossAuthorityWellFormed true 0,
   Example.nanBundle_crossAuthorityNormalEquiv 1,
   Example.nanBundle_productiveBoth.2.2 (true, ()) () 1 True.intro,
   (CodecLaws.tighten_eq_self_iff _).mpr Example.nanRepCodec_tightValidRep⟩

end BundleLaws

end Anneal.DualCorrespondenceAndTbPruningTests

/-! ## E. Tree Borrows foreign-subtree pruning -/

namespace Anneal.DualCorrespondenceAndTbPruningTests.TbPruning

noncomputable section
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.PureMirExec
open Anneal.MirLiftCore
open Anneal.TreeBorrowsPruningAndFrameWp

/-! ## Tree Borrows foreign-subtree pruning on concrete forests

Multi-root, multi-depth `BorrowForest` fixtures exercise every pruned
traversal of the module against the trusted full scans: each test applies a
module theorem to a fixture, discharges its hypotheses by evaluation, and
states the resulting table or flag explicitly.
-/

/-! ### Decision procedures for the subtree invariants -/

deriving instance DecidableEq for TreeBorrowPerm

mutual
/-- Decision procedure for a decidable node invariant on a subtree. -/
noncomputable def decAllSubtrees {P : BorrowEntry → List BorrowSubtree → Prop}
    (d : ∀ r c, Decidable (P r c)) :
    ∀ t : BorrowSubtree, Decidable (AllSubtrees P t)
  | .node r c =>
    match d r c, decAllSubtreesForest d c with
    | isTrue h₁, isTrue h₂ => isTrue (AllSubtrees.node_iff.mpr ⟨h₁, h₂⟩)
    | isFalse h₁, _ => isFalse fun h => h₁ (AllSubtrees.node_iff.mp h).1
    | _, isFalse h₂ => isFalse fun h => h₂ (AllSubtrees.node_iff.mp h).2
/-- Decision procedure for a decidable node invariant on a forest. -/
noncomputable def decAllSubtreesForest
    {P : BorrowEntry → List BorrowSubtree → Prop}
    (d : ∀ r c, Decidable (P r c)) :
    ∀ ts : List BorrowSubtree, Decidable (AllSubtreesForest P ts)
  | [] => isTrue (AllSubtreesForest.nil_iff.mpr True.intro)
  | t :: ts =>
    match decAllSubtrees d t, decAllSubtreesForest d ts with
    | isTrue h₁, isTrue h₂ =>
      isTrue (AllSubtreesForest.cons_iff.mpr ⟨h₁, h₂⟩)
    | isFalse h₁, _ =>
      isFalse fun h => h₁ (AllSubtreesForest.cons_iff.mp h).1
    | _, isFalse h₂ =>
      isFalse fun h => h₂ (AllSubtreesForest.cons_iff.mp h).2
end

instance {P : BorrowEntry → List BorrowSubtree → Prop}
    [d : ∀ r c, Decidable (P r c)] (ts : List BorrowSubtree) :
    Decidable (AllSubtreesForest P ts) :=
  decAllSubtreesForest d ts

instance (ps : List Nat) (r : BorrowEntry) (c : List BorrowSubtree) :
    Decidable (ForeignReadNoopNode ps r c) :=
  inferInstanceAs (Decidable (_ → ∀ e, e ∈ BorrowForest.toList c → _))

instance (ps : List Nat) (r : BorrowEntry) (c : List BorrowSubtree) :
    Decidable (ForeignWriteNoopNode ps r c) :=
  inferInstanceAs (Decidable (_ → ∀ e, e ∈ BorrowForest.toList c → _))

instance (r : BorrowEntry) (c : List BorrowSubtree) :
    Decidable (DisabledClosedNode r c) :=
  inferInstanceAs (Decidable (_ → ∀ e, e ∈ BorrowForest.toList c → _))

instance (r : BorrowEntry) (c : List BorrowSubtree) :
    Decidable (FrozenClosedNode r c) :=
  inferInstanceAs (Decidable (_ → ∀ e, e ∈ BorrowForest.toList c → _ ∨ _))

instance (ps : List Nat) (r : BorrowEntry) (c : List BorrowSubtree) :
    Decidable (DisabledRootWriteNoopNode ps r c) :=
  inferInstanceAs (Decidable (_ → ∀ e, e ∈ BorrowForest.toList c → _))

instance (ps : List Nat) (r : BorrowEntry) (c : List BorrowSubtree) :
    Decidable (FrozenOrDisabledRootReadNoopNode ps r c) :=
  inferInstanceAs
    (Decidable (_ ∨ _ → ∀ e, e ∈ BorrowForest.toList c → _))

instance (ps : List Nat) (ts : List BorrowSubtree) :
    Decidable (ForeignReadNoopForest ps ts) :=
  inferInstanceAs (Decidable (AllSubtreesForest _ ts))

instance (ps : List Nat) (ts : List BorrowSubtree) :
    Decidable (ForeignWriteNoopForest ps ts) :=
  inferInstanceAs (Decidable (AllSubtreesForest _ ts))

instance (ts : BorrowForest) : Decidable (DisabledClosedForest ts) :=
  inferInstanceAs (Decidable (AllSubtreesForest _ ts))

instance (ts : BorrowForest) : Decidable (FrozenClosedForest ts) :=
  inferInstanceAs (Decidable (AllSubtreesForest _ ts))

instance (ps : List Nat) (ts : BorrowForest) :
    Decidable (DisabledRootWriteNoopForest ps ts) :=
  inferInstanceAs (Decidable (AllSubtreesForest _ ts))

instance (ps : List Nat) (ts : BorrowForest) :
    Decidable (FrozenOrDisabledRootReadNoopForest ps ts) :=
  inferInstanceAs (Decidable (AllSubtreesForest _ ts))

/-! ### A finite, exact certificate for `SameAllocForest`

`SameAllocNode` quantifies over every provenance tag. The certificate below
checks only the tags of the table and of the subtree, and is equivalent to
`SameAllocNode`, so structural well-formedness of a concrete forest is
decided by evaluation.
-/

/-- Distinct naturals have a false `Nat.beq`. -/
theorem beq_false_of_ne {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact absurd (Nat.eq_of_beq_eq_true hb) h

mutual
/-- A tag contained in a subtree is carried by one of its entries. -/
theorem subtree_mem_of_containsTag {tag : Nat} :
    ∀ (t : BorrowSubtree), t.containsTag tag = true →
      ∃ e, e ∈ t.toList ∧ e.tag = tag
  | .node root children, h => by
    rw [BorrowSubtree.containsTag_node] at h
    rw [BorrowSubtree.toList_node]
    cases hr : Nat.beq root.tag tag with
    | true =>
      exact ⟨root, List.mem_cons_self .., Nat.eq_of_beq_eq_true hr⟩
    | false =>
      rw [hr] at h
      obtain ⟨e, he, ht⟩ := forest_mem_of_containsTag children h
      exact ⟨e, List.mem_cons_of_mem _ he, ht⟩
/-- A tag contained in a forest is carried by one of its entries. -/
theorem forest_mem_of_containsTag {tag : Nat} :
    ∀ (ts : List BorrowSubtree), BorrowForest.containsTag ts tag = true →
      ∃ e, e ∈ BorrowForest.toList ts ∧ e.tag = tag
  | [], h => by
    rw [BorrowForest.containsTag_nil] at h
    cases h
  | t :: ts, h => by
    rw [BorrowForest.containsTag_cons] at h
    rw [BorrowForest.toList_cons]
    cases ht : t.containsTag tag with
    | true =>
      obtain ⟨e, he, hb⟩ := subtree_mem_of_containsTag t ht
      exact ⟨e, List.mem_append_left _ he, hb⟩
    | false =>
      rw [ht] at h
      obtain ⟨e, he, hb⟩ := forest_mem_of_containsTag ts h
      exact ⟨e, List.mem_append_right _ he, hb⟩
end

/-- Every entry of a subtree has its tag contained in the subtree: the
converse of `subtree_mem_of_containsTag`, from the module's
`BorrowSubtree.tag_ne_of_not_containsTag`. -/
theorem containsTag_of_mem (t : BorrowSubtree) (e : BorrowEntry)
    (he : e ∈ t.toList) : t.containsTag e.tag = true := by
  cases hc : t.containsTag e.tag with
  | true => rfl
  | false =>
    have hb := BorrowSubtree.tag_ne_of_not_containsTag t hc e he
    rw [Nat.beq_refl] at hb
    cases hb

/-- Forest form of `containsTag_of_mem`, from the module's
`BorrowForest.tag_ne_of_not_containsTag`. -/
theorem forest_containsTag_of_mem (ts : List BorrowSubtree) (e : BorrowEntry)
    (he : e ∈ BorrowForest.toList ts) :
    BorrowForest.containsTag ts e.tag = true := by
  cases hc : BorrowForest.containsTag ts e.tag with
  | true => rfl
  | false =>
    have hb := BorrowForest.tag_ne_of_not_containsTag ts hc e he
    rw [Nat.beq_refl] at hb
    cases hb

/-- A tag carried by no entry of the table has no table entry. -/
theorem lookupBorrow_none_of_absent :
    ∀ (bs : List BorrowEntry) (tag : Nat),
      (∀ e, e ∈ bs → e.tag ≠ tag) → lookupBorrow bs tag = none
  | [], _, _ => rfl
  | e :: bs, tag, h => by
    have hb : Nat.beq e.tag tag = false :=
      beq_false_of_ne (h e (List.mem_cons_self ..))
    unfold lookupBorrow
    rw [hb]
    exact lookupBorrow_none_of_absent bs tag
      (fun e' he' => h e' (List.mem_cons_of_mem _ he'))

/-- A tag outside the table descends only from itself. -/
theorem descendant_false_of_absent (bs : List BorrowEntry) (tag anc : Nat)
    (hne : tag ≠ anc) (habs : ∀ e, e ∈ bs → e.tag ≠ tag) :
    isBorrowDescendantOrSelf bs tag anc = false := by
  have hb : Nat.beq tag anc = false := beq_false_of_ne hne
  have hl := lookupBorrow_none_of_absent bs tag habs
  unfold isBorrowDescendantOrSelf
  cases Trusted.Sequence.length bs with
  | zero => exact hb
  | succ n =>
    unfold isBorrowDescendantOrSelfAux
    rw [hb, hl]

/-- Finite certificate for `SameAllocNode`: the three clauses of
`SameAllocNode` restricted to the tags of the table and of the subtree. -/
def SameAllocCertNode (bs : List BorrowEntry) (root : BorrowEntry)
    (children : List BorrowSubtree) : Prop :=
  (∀ e, e ∈ BorrowForest.toList children →
    e.targetFrameDepth = root.targetFrameDepth ∧
      e.targetLocal = root.targetLocal) ∧
  (∀ e, e ∈ bs →
    (BorrowSubtree.node root children).containsTag e.tag = false →
      isBorrowDescendantOrSelf bs e.tag root.tag = false) ∧
  (∀ e, e ∈ (BorrowSubtree.node root children).toList →
    isBorrowDescendantOrSelf bs e.tag root.tag = true)

instance (bs : List BorrowEntry) (r : BorrowEntry)
    (c : List BorrowSubtree) : Decidable (SameAllocCertNode bs r c) :=
  inferInstanceAs
    (Decidable
      ((∀ e, e ∈ BorrowForest.toList c → _) ∧
        (∀ e, e ∈ bs → _) ∧
        (∀ e, e ∈ (BorrowSubtree.node r c).toList → _)))

/-- The certificate implies `SameAllocNode`. -/
theorem sameAllocNode_of_cert {bs : List BorrowEntry} {root : BorrowEntry}
    {children : List BorrowSubtree} (h : SameAllocCertNode bs root children) :
    SameAllocNode bs root children := by
  refine ⟨h.1, fun tag hc => ?_, fun tag hc => ?_⟩
  · cases hm : bs.any (fun e => Nat.beq e.tag tag) with
    | true =>
      obtain ⟨e, he, hb⟩ := List.any_eq_true.mp hm
      have ht : e.tag = tag := Nat.eq_of_beq_eq_true hb
      subst ht
      exact h.2.1 e he hc
    | false =>
      have habs : ∀ e, e ∈ bs → e.tag ≠ tag := fun e he ht =>
        List.any_eq_false.mp hm e he (by rw [ht]; exact Nat.beq_refl tag)
      have hroot : tag ≠ root.tag := fun ht => by
        rw [BorrowSubtree.containsTag_node, ht, Nat.beq_refl] at hc
        cases hc
      exact descendant_false_of_absent bs tag root.tag hroot habs
  · obtain ⟨e, he, ht⟩ := subtree_mem_of_containsTag _ hc
    subst ht
    exact h.2.2 e he

/-- `SameAllocNode` implies the certificate: the certificate is exact. -/
theorem cert_of_sameAllocNode {bs : List BorrowEntry} {root : BorrowEntry}
    {children : List BorrowSubtree} (h : SameAllocNode bs root children) :
    SameAllocCertNode bs root children :=
  ⟨h.1, fun e _ hc => h.2.1 e.tag hc,
    fun e he => h.2.2 e.tag (containsTag_of_mem _ e he)⟩

/-- `SameAllocForest` is equivalent to its finite certificate, by
`AllSubtreesForest.mono_strong` in both directions. -/
theorem sameAllocForest_iff_cert {bs : List BorrowEntry}
    {ts : List BorrowSubtree} :
    SameAllocForest bs ts ↔ AllSubtreesForest (SameAllocCertNode bs) ts :=
  ⟨AllSubtreesForest.mono_strong
      (fun _ _ hn => cert_of_sameAllocNode (AllSubtrees.node_iff.mp hn).1) ts,
    AllSubtreesForest.mono_strong
      (fun _ _ hn => sameAllocNode_of_cert (AllSubtrees.node_iff.mp hn).1)
      ts⟩

instance (bs : List BorrowEntry) (ts : List BorrowSubtree) :
    Decidable (SameAllocForest bs ts) :=
  decidable_of_iff _ sameAllocForest_iff_cert.symm

/-! ### Fixtures -/

/-- Whole-allocation borrow entry used by the fixtures. -/
def mkEntry (tag : Nat) (loc : Local) (perm : TreeBorrowPerm)
    (parent : Option Nat := none) (prot : Option Nat := none)
    (depth : Nat := 0) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := [], perm := perm,
    protector := prot, parentTag := parent, targetFrameDepth := depth }

/-- Roots of unrelated allocations: a depth-3 subtree on local `_5` of the
root frame, and a protected borrow of local `_0` of the frame at depth 1. -/
def fxUnrelated : BorrowForest :=
  [ .node (mkEntry 10 5 .unique)
      [.node (mkEntry 11 5 (.reservedFrz false) (some 10))
        [.node (mkEntry 12 5 .reservedIM (some 11)) []]],
    .node (mkEntry 13 0 .unique none (some 7) 1) [] ]

/-- A `.disabled` root of local `_0` with a branching depth-3 `.disabled`
subtree. -/
def fxDisabledTree : BorrowSubtree :=
  .node (mkEntry 20 0 .disabled)
    [.node (mkEntry 21 0 .disabled (some 20))
      [.node (mkEntry 22 0 .disabled (some 21)) []],
     .node (mkEntry 23 0 .disabled (some 20)) []]

/-- A root of local `_0` (initially `.frozen`) whose child carries protector
`4` and whose grandchild is `.disabled`. -/
def fxFrozenTree (p30 p31 : TreeBorrowPerm) : BorrowSubtree :=
  .node (mkEntry 30 0 p30)
    [.node (mkEntry 31 0 p31 (some 30) (some 4))
      [.node (mkEntry 32 0 .disabled (some 31)) []]]

/-- An interior-mutable `.cell` root of local `_0` with a `.reservedIM`
child and a `.cell` grandchild. -/
def fxCellTree : BorrowSubtree :=
  .node (mkEntry 40 0 .cell)
    [.node (mkEntry 41 0 .reservedIM (some 40))
      [.node (mkEntry 42 0 .cell (some 41)) []]]

/-- A live root of local `_0` carrying protector `3`, with a reservation
child carrying protector `6` and a `.reservedIM` grandchild. -/
def fxLiveTree (p50 p51 p52 : TreeBorrowPerm) : BorrowSubtree :=
  .node (mkEntry 50 0 p50 none (some 3))
    [.node (mkEntry 51 0 p51 (some 50) (some 6))
      [.node (mkEntry 52 0 p52 (some 51)) []]]

/-- The main fixture, parameterised by the five permissions that the
accesses of this file change. -/
def fxForestOf (p30 p31 p50 p51 p52 : TreeBorrowPerm) : BorrowForest :=
  fxUnrelated ++
    [fxDisabledTree, fxFrozenTree p30 p31, fxCellTree,
      fxLiveTree p50 p51 p52]

/-- The main fixture: six roots, depth 3, seventeen entries. -/
def fxForest : BorrowForest :=
  fxForestOf .frozen .frozen .unique (.reservedFrz false) .reservedIM

/-- The trusted flat borrow table of the main fixture. -/
def fxBorrows : List BorrowEntry := BorrowForest.toList fxForest

/-- Tag and permission of every entry of a forest, in table order. -/
def summary (f : BorrowForest) : List (Nat × TreeBorrowPerm) :=
  (BorrowForest.toList f).map fun e => (e.tag, e.perm)

/-- The flat table lists the entries in preorder. -/
theorem fxBorrows_tags :
    fxBorrows.map BorrowEntry.tag =
      [10, 11, 12, 13, 20, 21, 22, 23, 30, 31, 32, 40, 41, 42, 50, 51, 52] :=
  rfl

/-- The parent pointers of the flat table mirror the forest shape. -/
theorem fxBorrows_parents :
    fxBorrows.map BorrowEntry.parentTag =
      [none, some 10, some 11, none, none, some 20, some 21, some 20, none,
        some 30, some 31, none, some 40, some 41, none, some 50, some 51] :=
  rfl

/-- The main fixture is structurally well formed against its table. -/
theorem fx_sameAlloc : SameAllocForest fxBorrows fxForest := by
  decide +kernel

/-- Foreign-read no-op invariant of the main fixture, for every protector
set used below. -/
theorem fx_readNoop :
    ForeignReadNoopForest [] fxForest ∧
    ForeignReadNoopForest [6] fxForest ∧
    ForeignReadNoopForest [3, 6] fxForest ∧
    ForeignReadNoopForest [4, 6, 3] fxForest := by
  decide +kernel

/-- Foreign-write no-op invariant of the main fixture. -/
theorem fx_writeNoop :
    ForeignWriteNoopForest [] fxForest ∧
    ForeignWriteNoopForest [6] fxForest ∧
    ForeignWriteNoopForest [3] fxForest ∧
    ForeignWriteNoopForest [4, 6] fxForest := by
  decide +kernel

/-- The main fixture satisfies the `.disabled`- and `.frozen`-closure
invariants. -/
theorem fx_closed :
    DisabledClosedForest fxForest ∧ FrozenClosedForest fxForest := by
  decide +kernel

/-! ### Foreign reads on the main fixture -/

/-- A direct read of `_0` with protector `6` active: the pruned read is the
trusted full scan. -/
theorem fx_directRead_equiv :
    BorrowForest.toList
        (pruneForeignRead fxBorrows fxForest 0 none [] 0 0 [6] 0) =
      freezeTreeBorrowsOnReadAtProj fxBorrows fxBorrows 0 none [] 0 0 [6]
        0 :=
  pruneForeignRead_equiv_fullScan fx_sameAlloc fx_readNoop.2.1 0 none [] 0 0
    0

/-- The direct read freezes the live root `50` and latches the conflict
flag of its protected reservation child `51`; every skipped subtree is
untouched. -/
theorem fx_directRead_result :
    pruneForeignRead fxBorrows fxForest 0 none [] 0 0 [6] 0 =
      fxForestOf .frozen .frozen .frozen (.reservedFrz true) .reservedIM :=
  rfl

/-- The pruned read-UB test agrees with the trusted scan, with and without
the protector of the live root. -/
theorem fx_directRead_ub_equiv :
    pruneHasTreeReadUB fxBorrows fxForest [6] 0 none [] 0 0 0 =
        hasTreeReadUB fxBorrows fxBorrows [6] 0 none [] 0 0 0 ∧
    pruneHasTreeReadUB fxBorrows fxForest [3, 6] 0 none [] 0 0 0 =
        hasTreeReadUB fxBorrows fxBorrows [3, 6] 0 none [] 0 0 0 :=
  ⟨pruneHasTreeReadUB_equiv_fullScan fx_sameAlloc fx_readNoop.2.1 0 none []
      0 0 0,
    pruneHasTreeReadUB_equiv_fullScan fx_sameAlloc fx_readNoop.2.2.1 0 none
      [] 0 0 0⟩

/-- A direct read is defined while protector `3` is inactive, and is
undefined behavior once it protects the `.unique` root `50`. -/
theorem fx_directRead_ub_values :
    pruneHasTreeReadUB fxBorrows fxForest [6] 0 none [] 0 0 0 = false ∧
    pruneHasTreeReadUB fxBorrows fxForest [3, 6] 0 none [] 0 0 0 = true :=
  ⟨rfl, rfl⟩

/-- A read through the depth-3 tag `52` is a child read of its ancestors:
the pruned read agrees with the trusted scan and changes nothing, even with
every protector active. -/
theorem fx_childRead_unchanged :
    BorrowForest.toList
        (pruneForeignRead fxBorrows fxForest 0 (some 52) [] 0 0 [4, 6, 3] 0) =
      freezeTreeBorrowsOnReadAtProj fxBorrows fxBorrows 0 (some 52) [] 0 0
        [4, 6, 3] 0 ∧
    pruneForeignRead fxBorrows fxForest 0 (some 52) [] 0 0 [4, 6, 3] 0 =
      fxForest ∧
    pruneHasTreeReadUB fxBorrows fxForest [4, 6, 3] 0 (some 52) [] 0 0 0 =
      false :=
  ⟨pruneForeignRead_equiv_fullScan fx_sameAlloc fx_readNoop.2.2.2 0
      (some 52) [] 0 0 0, rfl, rfl⟩

/-- A read through the `.disabled` tag `21` is undefined behavior. The
pruned test must not skip the `.disabled` root `20`, because the access is
not foreign to it; a skip on the permission alone would miss the fault. -/
theorem fx_disabledChildRead_ub :
    pruneHasTreeReadUB fxBorrows fxForest [] 0 (some 21) [] 0 0 0 =
        hasTreeReadUB fxBorrows fxBorrows [] 0 (some 21) [] 0 0 0 ∧
    pruneHasTreeReadUB fxBorrows fxForest [] 0 (some 21) [] 0 0 0 = true ∧
    pruneAnyForest (readSkipRoot [] 0 0)
        (fun e => borrowEntryReadUB fxBorrows [] e 0 (some 21) [] 0 0 0)
        fxForest = false :=
  ⟨pruneHasTreeReadUB_equiv_fullScan fx_sameAlloc fx_readNoop.1 0 (some 21)
      [] 0 0 0, rfl, rfl⟩

/-- Reads never change protectors or tags, on every entry of the table. -/
theorem fx_directRead_preserves_protectors_tags :
    (BorrowForest.toList
        (pruneForeignRead fxBorrows fxForest 0 none [] 0 0 [6] 0)).map
        BorrowEntry.protector =
      [none, none, none, some 7, none, none, none, none, none, some 4, none,
        none, none, none, some 3, some 6, none] ∧
    (BorrowForest.toList
        (pruneForeignRead fxBorrows fxForest 0 none [] 0 0 [6] 0)).map
        BorrowEntry.tag =
      [10, 11, 12, 13, 20, 21, 22, 23, 30, 31, 32, 40, 41, 42, 50, 51, 52] :=
  ⟨(pruneForeignRead_preserves_protectors fxBorrows fxForest 0 none [] 0 0
      [6] 0).trans rfl,
    (pruneForeignRead_preserves_tags fxBorrows fxForest 0 none [] 0 0 [6]
      0).trans rfl⟩

/-- An unrelated-allocation root is skipped with an arbitrary subtree: the
pruned read never inspects the children of the root of local `_5`. -/
theorem read_skips_unrelated_root (bs : List BorrowEntry)
    (children : List BorrowSubtree) (rest : BorrowForest)
    (readerTag : Option Nat) (ps : List Nat) :
    pruneForeignRead bs (.node (mkEntry 10 5 .unique) children :: rest) 0
        readerTag [] 0 0 ps 0 =
      .node (mkEntry 10 5 .unique) children ::
        pruneForeignRead bs rest 0 readerTag [] 0 0 ps 0 :=
  pruneForeignRead_skip_unrelated bs (mkEntry 10 5 .unique) children rest 0
    readerTag [] 0 0 ps 0 rfl

/-- A `.disabled` or `.frozen` root of the accessed local is skipped with an
arbitrary subtree. -/
theorem read_skips_disabled_and_frozen_roots (bs : List BorrowEntry)
    (children : List BorrowSubtree) (rest : BorrowForest)
    (readerTag : Option Nat) (ps : List Nat) :
    pruneForeignRead bs (.node (mkEntry 20 0 .disabled) children :: rest) 0
        readerTag [] 0 0 ps 0 =
      .node (mkEntry 20 0 .disabled) children ::
        pruneForeignRead bs rest 0 readerTag [] 0 0 ps 0 ∧
    pruneForeignRead bs (.node (mkEntry 30 0 .frozen) children :: rest) 0
        readerTag [] 0 0 ps 0 =
      .node (mkEntry 30 0 .frozen) children ::
        pruneForeignRead bs rest 0 readerTag [] 0 0 ps 0 :=
  ⟨pruneForeignRead_skip_noop bs (mkEntry 20 0 .disabled) children rest 0
      readerTag [] 0 0 ps 0 rfl,
    pruneForeignRead_skip_noop bs (mkEntry 30 0 .frozen) children rest 0
      readerTag [] 0 0 ps 0 rfl⟩

/-! ### Foreign writes on the main fixture -/

/-- A write through the depth-3 tag `52`, resolved against the borrow tree:
the pruned write is the trusted full scan. -/
theorem fx_childWrite_equiv :
    BorrowForest.toList
        (pruneForeignWrite fxBorrows fxForest 0 (some 52) [] 0 0 0 [6]) =
      invalidateTreeBorrowsAtProj fxBorrows fxBorrows 0 (some 52) [] 0 0 0 :=
  pruneForeignWrite_equiv_fullScan fx_sameAlloc fx_writeNoop.2.1 0 (some 52)
    [] 0 0 0

/-- The write through `52` activates `52` and its ancestors `51` and `50`,
disables the foreign `.frozen` subtree, and leaves the skipped `.disabled`,
`.cell`, and unrelated subtrees untouched. -/
theorem fx_childWrite_result :
    pruneForeignWrite fxBorrows fxForest 0 (some 52) [] 0 0 0 [6] =
      fxForestOf .disabled .disabled .unique .unique .unique :=
  rfl

/-- A direct write to `_0` is foreign to every borrow: both live subtrees
are disabled, except the unprotected `.reservedIM` leaf `52`. -/
theorem fx_directWrite :
    BorrowForest.toList
        (pruneForeignWrite fxBorrows fxForest 0 none [] 0 0 0 []) =
      invalidateTreeBorrowsAtProj fxBorrows fxBorrows 0 none [] 0 0 0 ∧
    pruneForeignWrite fxBorrows fxForest 0 none [] 0 0 0 [] =
      fxForestOf .disabled .disabled .disabled .disabled .reservedIM :=
  ⟨pruneForeignWrite_equiv_fullScan fx_sameAlloc fx_writeNoop.1 0 none [] 0
      0 0, rfl⟩

/-- The simple write compares the writer tag without resolving ancestry:
through `52` it activates only `52` and disables its ancestors. The pruned
simple write is the trusted `invalidateConflictingBorrows`. -/
theorem fx_simpleWrite :
    BorrowForest.toList
        (pruneForeignWriteSimple fxBorrows fxForest 0 (some 52) 0 [6]) =
      invalidateConflictingBorrows fxBorrows 0 (some 52) 0 ∧
    pruneForeignWriteSimple fxBorrows fxForest 0 (some 52) 0 [6] =
      fxForestOf .disabled .disabled .disabled .disabled .unique :=
  ⟨pruneForeignWriteSimple_equiv_fullScan fx_sameAlloc fx_writeNoop.2.1 0
      (some 52) 0, rfl⟩

/-- The projection-sensitive write at the whole allocation agrees with the
trusted `invalidateConflictingBorrowsAtProj`. -/
theorem fx_projWrite_wholeAlloc :
    BorrowForest.toList
        (pruneForeignWriteProj fxBorrows fxForest 0 none [] 0 0 0 []) =
      invalidateConflictingBorrowsAtProj fxBorrows 0 none [] 0 0 0 ∧
    pruneForeignWriteProj fxBorrows fxForest 0 none [] 0 0 0 [] =
      fxForestOf .disabled .disabled .disabled .disabled .reservedIM :=
  ⟨pruneForeignWriteProj_equiv_fullScan fx_sameAlloc fx_writeNoop.1 0 none
      [] 0 0 0, rfl⟩

/-- Writes never change protectors or tags. -/
theorem fx_write_preserves_protectors_tags :
    (BorrowForest.toList
        (pruneForeignWrite fxBorrows fxForest 0 (some 52) [] 0 0 0 [6])).map
        BorrowEntry.protector = fxBorrows.map BorrowEntry.protector ∧
    (BorrowForest.toList
        (pruneForeignWrite fxBorrows fxForest 0 (some 52) [] 0 0 0 [6])).map
        BorrowEntry.tag = fxBorrows.map BorrowEntry.tag ∧
    (BorrowForest.toList
        (pruneForeignWriteSimple fxBorrows fxForest 0 (some 52) 0 [6])).map
        BorrowEntry.protector = fxBorrows.map BorrowEntry.protector ∧
    (BorrowForest.toList
        (pruneForeignWriteProj fxBorrows fxForest 0 none [] 0 0 0 [])).map
        BorrowEntry.protector = fxBorrows.map BorrowEntry.protector ∧
    (BorrowForest.toList
        (pruneForeignWriteProj fxBorrows fxForest 0 none [] 0 0 0 [])).map
        BorrowEntry.tag = fxBorrows.map BorrowEntry.tag :=
  ⟨pruneForeignWrite_preserves_protectors fxBorrows fxForest 0 (some 52) []
      0 0 0 [6],
    pruneForeignWrite_preserves_tags fxBorrows fxForest 0 (some 52) [] 0 0 0
      [6],
    pruneForeignWriteSimple_preserves_protectors fxBorrows fxForest 0
      (some 52) 0 [6],
    pruneForeignWriteProj_preserves_protectors fxBorrows fxForest 0 none []
      0 0 0 [],
    pruneForeignWriteProj_preserves_tags fxBorrows fxForest 0 none [] 0 0 0
      []⟩

/-- A root skipped by the write test is returned with an arbitrary subtree:
a direct write never inspects below a `.disabled` or `.cell` root. -/
theorem write_skips_disabled_and_cell_roots (bs : List BorrowEntry)
    (children : List BorrowSubtree) (rest : BorrowForest) (ps : List Nat) :
    pruneForeignWrite bs (.node (mkEntry 20 0 .disabled) children :: rest) 0
        none [] 0 0 0 ps =
      .node (mkEntry 20 0 .disabled) children ::
        pruneForeignWrite bs rest 0 none [] 0 0 0 ps ∧
    pruneForeignWrite bs (.node (mkEntry 40 0 .cell) children :: rest) 0
        none [] 0 0 0 ps =
      .node (mkEntry 40 0 .cell) children ::
        pruneForeignWrite bs rest 0 none [] 0 0 0 ps :=
  ⟨pruneForeignWrite_skip bs (mkEntry 20 0 .disabled) children rest 0 none
      [] 0 0 0 ps rfl,
    pruneForeignWrite_skip bs (mkEntry 40 0 .cell) children rest 0 none [] 0
      0 0 ps rfl⟩

/-! ### Protected write conflicts on the main fixture -/

/-- The pruned protected-write-conflict tests agree with the trusted scans
for a direct write, for each protector set. -/
theorem fx_directWrite_conflict_equiv (ps : List Nat)
    (hNoop : ForeignWriteNoopForest ps fxForest) (depth : Nat) :
    pruneHasProtectedWriteConflict fxBorrows fxForest ps 0 none [] 0 0
        depth =
      hasProtectedWriteConflict fxBorrows ps 0 none [] 0 0 depth ∧
    pruneHasProtectedTreeWriteConflict fxBorrows fxForest ps 0 none [] 0 0
        depth =
      hasProtectedTreeWriteConflict fxBorrows fxBorrows ps 0 none [] 0 0
        depth :=
  ⟨pruneHasProtectedWriteConflict_equiv_fullScan fx_sameAlloc hNoop 0 none
      [] 0 0 depth,
    pruneHasProtectedTreeWriteConflict_equiv_fullScan fx_sameAlloc hNoop 0
      none [] 0 0 depth⟩

/-- Foreign-write no-op invariant for the protector sets of the conflict
tests. -/
theorem fx_writeNoop_conflictSets :
    ForeignWriteNoopForest [7] fxForest ∧
    ForeignWriteNoopForest [4, 7] fxForest := by
  decide +kernel

/-- A direct write to `_0` of the root frame conflicts with no protector
while only the callee-frame protector `7` is active, conflicts with the
protected `.frozen` child `31` once protector `4` is active, and a direct
write to `_0` of the frame at depth 1 conflicts with protector `7`. -/
theorem fx_directWrite_conflict_values :
    pruneHasProtectedWriteConflict fxBorrows fxForest [7] 0 none [] 0 0 0 =
      false ∧
    pruneHasProtectedWriteConflict fxBorrows fxForest [4, 7] 0 none [] 0 0
      0 = true ∧
    pruneHasProtectedWriteConflict fxBorrows fxForest [7] 0 none [] 0 0 1 =
      true ∧
    hasProtectedWriteConflict fxBorrows [7] 0 none [] 0 0 0 = false ∧
    hasProtectedWriteConflict fxBorrows [4, 7] 0 none [] 0 0 0 = true ∧
    hasProtectedWriteConflict fxBorrows [7] 0 none [] 0 0 1 = true :=
  ⟨rfl, rfl, rfl,
    (fx_directWrite_conflict_equiv [7] fx_writeNoop_conflictSets.1 0).1.symm
      |>.trans rfl,
    (fx_directWrite_conflict_equiv [4, 7] fx_writeNoop_conflictSets.2
      0).1.symm |>.trans rfl,
    (fx_directWrite_conflict_equiv [7] fx_writeNoop_conflictSets.1 1).1.symm
      |>.trans rfl⟩

/-- With protector `3` on the live root `50`, a write through its
descendant `52` is a child write for the tree-resolved test (no conflict)
but a foreign write for the tag-comparing test (conflict). Each pruned test
agrees with its own trusted scan. -/
theorem fx_childWrite_conflict :
    pruneHasProtectedTreeWriteConflict fxBorrows fxForest [3] 0 (some 52) []
        0 0 0 =
      hasProtectedTreeWriteConflict fxBorrows fxBorrows [3] 0 (some 52) [] 0
        0 0 ∧
    pruneHasProtectedTreeWriteConflict fxBorrows fxForest [3] 0 (some 52) []
      0 0 0 = false ∧
    pruneHasProtectedWriteConflict fxBorrows fxForest [3] 0 (some 52) [] 0 0
        0 =
      hasProtectedWriteConflict fxBorrows [3] 0 (some 52) [] 0 0 0 ∧
    pruneHasProtectedWriteConflict fxBorrows fxForest [3] 0 (some 52) [] 0 0
      0 = true :=
  ⟨pruneHasProtectedTreeWriteConflict_equiv_fullScan fx_sameAlloc
      fx_writeNoop.2.2.1 0 (some 52) [] 0 0 0, rfl,
    pruneHasProtectedWriteConflict_equiv_fullScan fx_sameAlloc
      fx_writeNoop.2.2.1 0 (some 52) [] 0 0 0, rfl⟩

/-- A tree-resolved write through `52` conflicts with the foreign protected
`.frozen` child `31` once protector `4` is active. -/
theorem fx_childWrite_conflict_foreign_protector :
    pruneHasProtectedTreeWriteConflict fxBorrows fxForest [4, 6] 0 (some 52)
        [] 0 0 0 =
      hasProtectedTreeWriteConflict fxBorrows fxBorrows [4, 6] 0 (some 52)
        [] 0 0 0 ∧
    pruneHasProtectedTreeWriteConflict fxBorrows fxForest [4, 6] 0 (some 52)
      [] 0 0 0 = true ∧
    pruneHasProtectedTreeWriteConflict fxBorrows fxForest [6] 0 (some 52) []
      0 0 0 = false :=
  ⟨pruneHasProtectedTreeWriteConflict_equiv_fullScan fx_sameAlloc
      fx_writeNoop.2.2.2 0 (some 52) [] 0 0 0, rfl, rfl⟩

/-! ### `.disabled`-root and `.frozen`/`.disabled`-root variants

These traversals skip on the root permission alone, under the closure
invariants `DisabledClosedForest` and `FrozenClosedForest`.
-/

/-- The three `.disabled`-root writes agree with the three trusted write
scans on the main fixture. -/
theorem fx_writeDisabled_equiv :
    BorrowForest.toList
        (pruneForeignWriteDisabled fxBorrows fxForest 0 (some 52) [] 0 0 0) =
      invalidateTreeBorrowsAtProj fxBorrows fxBorrows 0 (some 52) [] 0 0 0 ∧
    BorrowForest.toList
        (pruneForeignWriteSimpleDisabled fxBorrows fxForest 0 none 0) =
      invalidateConflictingBorrows fxBorrows 0 none 0 ∧
    BorrowForest.toList
        (pruneForeignWriteProjDisabled fxBorrows fxForest 0 none [] 0 0 0) =
      invalidateConflictingBorrowsAtProj fxBorrows 0 none [] 0 0 0 :=
  ⟨pruneForeignWriteDisabled_equiv_fullScan fx_sameAlloc fx_closed.1 0
      (some 52) [] 0 0 0,
    pruneForeignWriteSimpleDisabled_equiv_fullScan fx_sameAlloc fx_closed.1 0
      none 0,
    pruneForeignWriteProjDisabled_equiv_fullScan fx_sameAlloc fx_closed.1 0
      none [] 0 0 0⟩

/-- The `.disabled`-root writes visit the `.cell` subtree (which the
permission-aware writes skip) and still produce the same forests. -/
theorem fx_writeDisabled_results :
    pruneForeignWriteDisabled fxBorrows fxForest 0 (some 52) [] 0 0 0 =
      fxForestOf .disabled .disabled .unique .unique .unique ∧
    pruneForeignWriteSimpleDisabled fxBorrows fxForest 0 none 0 =
      fxForestOf .disabled .disabled .disabled .disabled .reservedIM ∧
    pruneForeignWriteProjDisabled fxBorrows fxForest 0 none [] 0 0 0 =
      fxForestOf .disabled .disabled .disabled .disabled .reservedIM :=
  ⟨rfl, rfl, rfl⟩

/-- The `.disabled`-root conflict tests agree with the trusted scans and
report the conflict with protector `4`. -/
theorem fx_conflictDisabled :
    pruneHasProtectedWriteConflictDisabled fxBorrows fxForest [4, 7] 0 none
        [] 0 0 0 =
      hasProtectedWriteConflict fxBorrows [4, 7] 0 none [] 0 0 0 ∧
    pruneHasProtectedWriteConflictDisabled fxBorrows fxForest [4, 7] 0 none
      [] 0 0 0 = true ∧
    pruneHasProtectedWriteConflictDisabled fxBorrows fxForest [7] 0 none []
      0 0 0 = false ∧
    pruneHasProtectedTreeWriteConflictDisabled fxBorrows fxForest [3] 0
        (some 52) [] 0 0 0 =
      hasProtectedTreeWriteConflict fxBorrows fxBorrows [3] 0 (some 52) [] 0
        0 0 ∧
    pruneHasProtectedTreeWriteConflictDisabled fxBorrows fxForest [3] 0
      (some 52) [] 0 0 0 = false :=
  ⟨pruneHasProtectedWriteConflictDisabled_equiv_fullScan fx_sameAlloc
      fx_closed.1 0 none [] 0 0 0, rfl, rfl,
    pruneHasProtectedTreeWriteConflictDisabled_equiv_fullScan fx_sameAlloc
      fx_closed.1 0 (some 52) [] 0 0 0, rfl⟩

/-- The `.disabled`-root writes preserve protectors and tags. -/
theorem fx_writeDisabled_preserves_protectors_tags :
    (BorrowForest.toList
        (pruneForeignWriteDisabled fxBorrows fxForest 0 (some 52) [] 0 0
          0)).map BorrowEntry.protector =
      fxBorrows.map BorrowEntry.protector ∧
    (BorrowForest.toList
        (pruneForeignWriteDisabled fxBorrows fxForest 0 (some 52) [] 0 0
          0)).map BorrowEntry.tag = fxBorrows.map BorrowEntry.tag ∧
    (BorrowForest.toList
        (pruneForeignWriteSimpleDisabled fxBorrows fxForest 0 none 0)).map
        BorrowEntry.protector = fxBorrows.map BorrowEntry.protector ∧
    (BorrowForest.toList
        (pruneForeignWriteSimpleDisabled fxBorrows fxForest 0 none 0)).map
        BorrowEntry.tag = fxBorrows.map BorrowEntry.tag ∧
    (BorrowForest.toList
        (pruneForeignWriteProjDisabled fxBorrows fxForest 0 none [] 0 0
          0)).map BorrowEntry.protector =
      fxBorrows.map BorrowEntry.protector ∧
    (BorrowForest.toList
        (pruneForeignWriteProjDisabled fxBorrows fxForest 0 none [] 0 0
          0)).map BorrowEntry.tag = fxBorrows.map BorrowEntry.tag :=
  ⟨pruneForeignWriteDisabled_preserves_protectors fxBorrows fxForest 0
      (some 52) [] 0 0 0,
    pruneForeignWriteDisabled_preserves_tags fxBorrows fxForest 0 (some 52)
      [] 0 0 0,
    pruneForeignWriteSimpleDisabled_preserves_protectors fxBorrows fxForest 0
      none 0,
    pruneForeignWriteSimpleDisabled_preserves_tags fxBorrows fxForest 0 none
      0,
    pruneForeignWriteProjDisabled_preserves_protectors fxBorrows fxForest 0
      none [] 0 0 0,
    pruneForeignWriteProjDisabled_preserves_tags fxBorrows fxForest 0 none
      [] 0 0 0⟩

/-- The `.frozen`/`.disabled`-root read agrees with the trusted scan and
produces the same forest as the permission-aware read. -/
theorem fx_readFrozenOrDisabled :
    BorrowForest.toList
        (pruneForeignReadFrozenOrDisabled fxBorrows fxForest 0 none [] 0 0
          [6] 0) =
      freezeTreeBorrowsOnReadAtProj fxBorrows fxBorrows 0 none [] 0 0 [6]
        0 ∧
    pruneForeignReadFrozenOrDisabled fxBorrows fxForest 0 none [] 0 0 [6]
        0 =
      fxForestOf .frozen .frozen .frozen (.reservedFrz true) .reservedIM :=
  ⟨pruneForeignReadFrozenOrDisabled_equiv_fullScan fx_sameAlloc fx_closed.1
      fx_closed.2 0 none [] 0 0 [6] 0, rfl⟩

/-- The `.frozen`/`.disabled`-root read-UB test agrees with the trusted
scan, with and without protector `3`. -/
theorem fx_readUBFrozenOrDisabled :
    pruneHasTreeReadUBFrozenOrDisabled fxBorrows fxForest [3, 6] 0 none [] 0
        0 0 =
      hasTreeReadUB fxBorrows fxBorrows [3, 6] 0 none [] 0 0 0 ∧
    pruneHasTreeReadUBFrozenOrDisabled fxBorrows fxForest [3, 6] 0 none [] 0
      0 0 = true ∧
    pruneHasTreeReadUBFrozenOrDisabled fxBorrows fxForest [6] 0 none [] 0 0
      0 = false ∧
    pruneHasTreeReadUBFrozenOrDisabled fxBorrows fxForest [] 0 (some 21) []
      0 0 0 = true :=
  ⟨pruneHasTreeReadUBFrozenOrDisabled_equiv_fullScan fx_sameAlloc
      fx_closed.1 fx_closed.2 0 none [] 0 0 0, rfl, rfl, rfl⟩

/-- The `.frozen`/`.disabled`-root read preserves protectors, tags, and
(absent undefined behavior) the `.disabled`-closure invariant. -/
theorem fx_readFrozenOrDisabled_preserves :
    (BorrowForest.toList
        (pruneForeignReadFrozenOrDisabled fxBorrows fxForest 0 none [] 0 0
          [6] 0)).map BorrowEntry.protector =
      fxBorrows.map BorrowEntry.protector ∧
    (BorrowForest.toList
        (pruneForeignReadFrozenOrDisabled fxBorrows fxForest 0 none [] 0 0
          [6] 0)).map BorrowEntry.tag = fxBorrows.map BorrowEntry.tag ∧
    DisabledClosedForest
      (pruneForeignReadFrozenOrDisabled fxBorrows fxForest 0 none [] 0 0 [6]
        0) :=
  ⟨pruneForeignReadFrozenOrDisabled_preserves_protectors fxBorrows fxForest
      0 none [] 0 0 [6] 0,
    pruneForeignReadFrozenOrDisabled_preserves_tags fxBorrows fxForest 0
      none [] 0 0 [6] 0,
    pruneForeignReadFrozenOrDisabled_preserves_disabledClosed
      (allBorrows := fxBorrows) (activeProtectors := [6]) fx_closed.1 0 none
      [] 0 0 0 rfl⟩

/-! ### Frame deallocation and protector attachment on the main fixture -/

/-- Tag, permission, and deallocation flag of every entry of a table. -/
def deallocSummary (bs : List BorrowEntry) :
    List (Nat × TreeBorrowPerm × Bool) :=
  bs.map fun e => (e.tag, e.perm, e.allocDead)

/-- Deallocating local `_0` of the root frame: the pruned traversal is the
trusted `disableFrameBorrows`. -/
theorem fx_disableFrame_equiv :
    BorrowForest.toList (pruneDisableFrameBorrows fxForest 0 1) =
      disableFrameBorrows fxBorrows 0 1 :=
  pruneDisableFrameBorrows_equiv_fullScan fx_sameAlloc 0 1

/-- Deallocation disables and marks dead exactly the thirteen borrows of
`_0` in the root frame; the borrows of `_5` and of the frame at depth 1 are
skipped at their roots. -/
theorem fx_disableFrame_result :
    deallocSummary
        (BorrowForest.toList (pruneDisableFrameBorrows fxForest 0 1)) =
      [(10, .unique, false), (11, .reservedFrz false, false),
        (12, .reservedIM, false), (13, .unique, false),
        (20, .disabled, true), (21, .disabled, true), (22, .disabled, true),
        (23, .disabled, true), (30, .disabled, true), (31, .disabled, true),
        (32, .disabled, true), (40, .disabled, true), (41, .disabled, true),
        (42, .disabled, true), (50, .disabled, true), (51, .disabled, true),
        (52, .disabled, true)] :=
  rfl

/-- The pruned frame-deallocation protector test agrees with the trusted
scan for every protector set. -/
theorem fx_frameDeallocConflict_equiv (ps : List Nat) (depth n : Nat) :
    pruneHasFrameDeallocProtectorConflict fxForest ps depth n =
      hasFrameDeallocProtectorConflict fxBorrows ps depth n :=
  pruneHasFrameDeallocProtectorConflict_equiv_fullScan fx_sameAlloc
    fx_closed.1 ps depth n

/-- Deallocating `_0` of the root frame conflicts with the protectors of
the live root (`3`) and of the `.frozen` child (`4`), not with the
callee-frame protector `7`; deallocating `_0` of the frame at depth 1
conflicts with `7`. -/
theorem fx_frameDeallocConflict_values :
    pruneHasFrameDeallocProtectorConflict fxForest [3] 0 1 = true ∧
    pruneHasFrameDeallocProtectorConflict fxForest [4] 0 1 = true ∧
    pruneHasFrameDeallocProtectorConflict fxForest [7] 0 1 = false ∧
    pruneHasFrameDeallocProtectorConflict fxForest [7] 1 1 = true ∧
    hasFrameDeallocProtectorConflict fxBorrows [7] 0 1 = false ∧
    hasFrameDeallocProtectorConflict fxBorrows [7] 1 1 = true :=
  ⟨rfl, rfl, rfl, rfl,
    (fx_frameDeallocConflict_equiv [7] 0 1).symm.trans rfl,
    (fx_frameDeallocConflict_equiv [7] 1 1).symm.trans rfl⟩

/-- Attaching protector `9` to the depth-3 tag `52`: the pruned traversal
is the trusted `attachBorrowProtector`, descends only into the subtree of
root `50`, and changes exactly the protector of `52`. -/
theorem fx_attachProtector :
    BorrowForest.toList (pruneAttachBorrowProtector fxBorrows fxForest 52 9) =
      attachBorrowProtector fxBorrows 52 9 ∧
    (BorrowForest.toList
        (pruneAttachBorrowProtector fxBorrows fxForest 52 9)).map
        BorrowEntry.protector =
      [none, none, none, some 7, none, none, none, none, none, some 4, none,
        none, none, none, some 3, some 6, some 9] ∧
    summary (pruneAttachBorrowProtector fxBorrows fxForest 52 9) =
      summary fxForest :=
  ⟨pruneAttachBorrowProtector_equiv_fullScan fx_sameAlloc 52 9, rfl, rfl⟩

/-! ### Multi-step accesses under the permission-aware invariants -/

/-- Every entry of the main fixture borrows the whole allocation. -/
theorem fx_wholeAlloc :
    ∀ e, e ∈ BorrowForest.toList fxForest → e.targetProjection = [] := by
  decide +kernel

/-- Forest after the direct read with protector `6` active. -/
def fxRead1 : BorrowForest :=
  pruneForeignRead fxBorrows fxForest 0 none [] 0 0 [6] 0

/-- Trusted table after the direct read with protector `6` active. -/
def fxReadTable1 : List BorrowEntry :=
  freezeTreeBorrowsOnReadAtProj fxBorrows fxBorrows 0 none [] 0 0 [6] 0

/-- After the first read the forest is still well formed against the
updated trusted table and still satisfies the foreign-read no-op invariant:
both facts are derived from the preservation theorems, not re-evaluated. -/
theorem fxRead1_invariants :
    SameAllocForest fxReadTable1 fxRead1 ∧
    ForeignReadNoopForest [6] fxRead1 :=
  ⟨pruneForeignRead_preserves_sameAlloc fx_sameAlloc 0 none [] 0 0 [6] 0,
    pruneForeignRead_preserves_foreignReadNoop_wholeAlloc fx_sameAlloc
      fx_readNoop.2.1 0 none 0 fx_wholeAlloc rfl⟩

/-- Second access: a read through `52` on the forest produced by the first
read. The derived invariants give agreement with the trusted scans, the
forest is unchanged, and the read is defined. -/
theorem fxRead1_then_childRead :
    BorrowForest.toList
        (pruneForeignRead fxReadTable1 fxRead1 0 (some 52) [] 0 0 [6] 0) =
      freezeTreeBorrowsOnReadAtProj fxReadTable1
        (BorrowForest.toList fxRead1) 0 (some 52) [] 0 0 [6] 0 ∧
    pruneHasTreeReadUB fxReadTable1 fxRead1 [6] 0 (some 52) [] 0 0 0 =
      hasTreeReadUB fxReadTable1 (BorrowForest.toList fxRead1) [6] 0
        (some 52) [] 0 0 0 ∧
    pruneForeignRead fxReadTable1 fxRead1 0 (some 52) [] 0 0 [6] 0 =
      fxForestOf .frozen .frozen .frozen (.reservedFrz true) .reservedIM ∧
    pruneHasTreeReadUB fxReadTable1 fxRead1 [6] 0 (some 52) [] 0 0 0 =
      false :=
  ⟨pruneForeignRead_equiv_fullScan fxRead1_invariants.1
      fxRead1_invariants.2 0 (some 52) [] 0 0 0,
    pruneHasTreeReadUB_equiv_fullScan fxRead1_invariants.1
      fxRead1_invariants.2 0 (some 52) [] 0 0 0, rfl, rfl⟩

/-- Forest after the direct write with protector `7` active. -/
def fxWrite1 : BorrowForest :=
  pruneForeignWrite fxBorrows fxForest 0 none [] 0 0 0 [7]

/-- Trusted table after the direct write. -/
def fxWriteTable1 : List BorrowEntry :=
  invalidateTreeBorrowsAtProj fxBorrows fxBorrows 0 none [] 0 0 0

/-- After the first write the forest is still well formed against the
updated trusted table and still satisfies the foreign-write no-op
invariant, by the preservation theorems. -/
theorem fxWrite1_invariants :
    SameAllocForest fxWriteTable1 fxWrite1 ∧
    ForeignWriteNoopForest [7] fxWrite1 :=
  ⟨pruneForeignWrite_preserves_sameAlloc fx_sameAlloc 0 none [] 0 0 0 [7],
    pruneForeignWrite_preserves_foreignWriteNoop_direct fx_sameAlloc
      fx_writeNoop_conflictSets.1 0 0 fx_wholeAlloc rfl⟩

/-- Second access: a write through `52` on the forest produced by the first
write. Its ancestors are already `.disabled` (the child write through them
is rejected and leaves them unchanged) and `52` is activated; the pruned
write and conflict test agree with the trusted scans. -/
theorem fxWrite1_then_childWrite :
    BorrowForest.toList
        (pruneForeignWrite fxWriteTable1 fxWrite1 0 (some 52) [] 0 0 0 [7]) =
      invalidateTreeBorrowsAtProj fxWriteTable1
        (BorrowForest.toList fxWrite1) 0 (some 52) [] 0 0 0 ∧
    pruneHasProtectedTreeWriteConflict fxWriteTable1 fxWrite1 [7] 0
        (some 52) [] 0 0 0 =
      hasProtectedTreeWriteConflict fxWriteTable1
        (BorrowForest.toList fxWrite1) [7] 0 (some 52) [] 0 0 0 ∧
    pruneForeignWrite fxWriteTable1 fxWrite1 0 (some 52) [] 0 0 0 [7] =
      fxForestOf .disabled .disabled .disabled .disabled .unique ∧
    pruneHasProtectedTreeWriteConflict fxWriteTable1 fxWrite1 [7] 0
      (some 52) [] 0 0 0 = false :=
  ⟨pruneForeignWrite_equiv_fullScan fxWrite1_invariants.1
      fxWrite1_invariants.2 0 (some 52) [] 0 0 0,
    pruneHasProtectedTreeWriteConflict_equiv_fullScan fxWrite1_invariants.1
      fxWrite1_invariants.2 0 (some 52) [] 0 0 0, rfl, rfl⟩

/-- The simple and projection-sensitive writes, and their `.disabled`-root
variants, keep the forest well formed against the updated trusted table;
hence a later protector attachment on the written forest is still the
trusted `attachBorrowProtector`. -/
theorem fx_writes_then_attach :
    BorrowForest.toList
        (pruneAttachBorrowProtector
          (invalidateConflictingBorrows fxBorrows 0 (some 52) 0)
          (pruneForeignWriteSimple fxBorrows fxForest 0 (some 52) 0 [6]) 52
          9) =
      attachBorrowProtector
        (BorrowForest.toList
          (pruneForeignWriteSimple fxBorrows fxForest 0 (some 52) 0 [6])) 52
        9 ∧
    BorrowForest.toList
        (pruneAttachBorrowProtector
          (invalidateConflictingBorrowsAtProj fxBorrows 0 none [] 0 0 0)
          (pruneForeignWriteProj fxBorrows fxForest 0 none [] 0 0 0 []) 52
          9) =
      attachBorrowProtector
        (BorrowForest.toList
          (pruneForeignWriteProj fxBorrows fxForest 0 none [] 0 0 0 [])) 52
        9 ∧
    BorrowForest.toList
        (pruneAttachBorrowProtector
          (invalidateConflictingBorrows fxBorrows 0 none 0)
          (pruneForeignWriteSimpleDisabled fxBorrows fxForest 0 none 0) 52
          9) =
      attachBorrowProtector
        (BorrowForest.toList
          (pruneForeignWriteSimpleDisabled fxBorrows fxForest 0 none 0)) 52
        9 ∧
    BorrowForest.toList
        (pruneAttachBorrowProtector
          (invalidateConflictingBorrowsAtProj fxBorrows 0 none [] 0 0 0)
          (pruneForeignWriteProjDisabled fxBorrows fxForest 0 none [] 0 0 0)
          52 9) =
      attachBorrowProtector
        (BorrowForest.toList
          (pruneForeignWriteProjDisabled fxBorrows fxForest 0 none [] 0 0
            0)) 52 9 :=
  ⟨pruneAttachBorrowProtector_equiv_fullScan
      (pruneForeignWriteSimple_preserves_sameAlloc fx_sameAlloc 0 (some 52)
        0 [6]) 52 9,
    pruneAttachBorrowProtector_equiv_fullScan
      (pruneForeignWriteProj_preserves_sameAlloc fx_sameAlloc 0 none [] 0 0
        0 []) 52 9,
    pruneAttachBorrowProtector_equiv_fullScan
      (pruneForeignWriteSimpleDisabled_preserves_sameAlloc fx_sameAlloc 0
        none 0) 52 9,
    pruneAttachBorrowProtector_equiv_fullScan
      (pruneForeignWriteProjDisabled_preserves_sameAlloc fx_sameAlloc 0 none
        [] 0 0 0) 52 9⟩

/-! ### Cell-aware root no-op invariants: fixture

`DisabledRootWriteNoopForest` and `FrozenOrDisabledRootReadNoopForest`
constrain only `.disabled` (and `.frozen`) roots, so they hold on forests
that mix interior-mutable `.cell` borrows with live ones.
-/

/-- The cell-aware fixture, parameterised by the four permissions that the
accesses change and by the protector of tag `91`: an unrelated depth-3
subtree on `_9`; a `.disabled` root with a protected `.cell` child and a
`.reservedIM` grandchild; a root (initially `.frozen`) with a reservation
child and a `.cell` grandchild; a `.cell` root with a live child; and a
live root with a `.cell` child. -/
def cellForestOf (q0 q1 r1 s : TreeBorrowPerm) (prot91 : Option Nat) :
    BorrowForest :=
  [ .node (mkEntry 60 9 .frozen)
      [.node (mkEntry 61 9 .frozen (some 60))
        [.node (mkEntry 62 9 .disabled (some 61)) []]],
    .node (mkEntry 70 0 .disabled)
      [.node (mkEntry 71 0 .cell (some 70) (some 8))
        [.node (mkEntry 72 0 .reservedIM (some 71)) []],
       .node (mkEntry 73 0 .disabled (some 70)) []],
    .node (mkEntry 80 0 q0)
      [.node (mkEntry 81 0 q1 (some 80))
        [.node (mkEntry 82 0 .cell (some 81)) []]],
    .node (mkEntry 90 0 .cell)
      [.node (mkEntry 91 0 r1 (some 90) prot91)
        [.node (mkEntry 92 0 .reservedIM (some 91)) []]],
    .node (mkEntry 95 0 s)
      [.node (mkEntry 96 0 .cell (some 95)) []] ]

/-- The cell-aware fixture: five roots, depth 3, fifteen entries. -/
def cellForest : BorrowForest :=
  cellForestOf .frozen (.reservedFrz false) .unique .unique none

/-- The trusted flat borrow table of the cell-aware fixture. -/
def cellBorrows : List BorrowEntry := BorrowForest.toList cellForest

/-- The cell-aware fixture is structurally well formed. -/
theorem cell_sameAlloc : SameAllocForest cellBorrows cellForest := by
  decide +kernel

/-- The cell-aware fixture satisfies both root no-op invariants with
protector `8` active. -/
theorem cell_rootNoop :
    DisabledRootWriteNoopForest [8] cellForest ∧
    FrozenOrDisabledRootReadNoopForest [8] cellForest := by
  decide +kernel

/-- The cell-aware fixture violates all four stricter invariants, so only
the root no-op theorems apply to it. -/
theorem cell_not_strict :
    ¬ DisabledClosedForest cellForest ∧
    ¬ FrozenClosedForest cellForest ∧
    ¬ ForeignWriteNoopForest [8] cellForest ∧
    ¬ ForeignReadNoopForest [8] cellForest := by
  decide +kernel

/-- Every entry of the cell-aware fixture borrows the whole allocation and
carries a protector other than `9`. -/
theorem cell_wholeAlloc_fresh :
    (∀ e, e ∈ BorrowForest.toList cellForest → e.targetProjection = []) ∧
    (∀ e, e ∈ BorrowForest.toList cellForest → e.protector ≠ some 9) := by
  decide +kernel

/-! ### Cell-aware root no-op invariants: single accesses -/

/-- A direct write under the root no-op invariant: the `.disabled`-root
pruned writes agree with all three trusted write scans. -/
theorem cell_directWrite_equiv :
    BorrowForest.toList
        (pruneForeignWriteDisabled cellBorrows cellForest 0 none [] 0 0 0) =
      invalidateTreeBorrowsAtProj cellBorrows cellBorrows 0 none [] 0 0 0 ∧
    BorrowForest.toList
        (pruneForeignWriteSimpleDisabled cellBorrows cellForest 0 none 0) =
      invalidateConflictingBorrows cellBorrows 0 none 0 ∧
    BorrowForest.toList
        (pruneForeignWriteProjDisabled cellBorrows cellForest 0 none [] 0 0
          0) =
      invalidateConflictingBorrowsAtProj cellBorrows 0 none [] 0 0 0 :=
  ⟨pruneForeignWriteDisabled_rootNoop_equiv_fullScan cell_sameAlloc
      cell_rootNoop.1 0 none [] 0 0 0,
    pruneForeignWriteSimpleDisabled_rootNoop_equiv_fullScan cell_sameAlloc
      cell_rootNoop.1 0 none 0,
    pruneForeignWriteProjDisabled_rootNoop_equiv_fullScan cell_sameAlloc
      cell_rootNoop.1 0 none [] 0 0 0⟩

/-- The direct write disables every live borrow of `_0`, including the
live child `91` of the `.cell` root, and keeps every `.cell` and
unprotected `.reservedIM` borrow, including those below the skipped
`.disabled` root. -/
theorem cell_directWrite_result :
    pruneForeignWriteDisabled cellBorrows cellForest 0 none [] 0 0 0 =
      cellForestOf .disabled .disabled .disabled .disabled none ∧
    pruneForeignWriteSimpleDisabled cellBorrows cellForest 0 none 0 =
      cellForestOf .disabled .disabled .disabled .disabled none ∧
    pruneForeignWriteProjDisabled cellBorrows cellForest 0 none [] 0 0 0 =
      cellForestOf .disabled .disabled .disabled .disabled none :=
  ⟨rfl, rfl, rfl⟩

/-- Negative twin: the permission-aware write skips the `.cell` root `90`
and so misses its live child `91`. Without `ForeignWriteNoopForest` it
differs from the trusted scan on the cell-aware fixture. -/
theorem cell_permissionAware_write_diverges :
    pruneForeignWrite cellBorrows cellForest 0 none [] 0 0 0 [8] =
      cellForestOf .disabled .disabled .unique .disabled none ∧
    summary (pruneForeignWrite cellBorrows cellForest 0 none [] 0 0 0 [8]) ≠
      (invalidateTreeBorrowsAtProj cellBorrows cellBorrows 0 none [] 0 0
        0).map fun e => (e.tag, e.perm) := by
  refine ⟨rfl, ?_⟩
  decide +kernel

/-- A direct read under the root no-op invariant: the `.frozen`/`.disabled`
root read agrees with the trusted scan, freezing the live child `91` of the
`.cell` root and the live root `95`. -/
theorem cell_directRead :
    BorrowForest.toList
        (pruneForeignReadFrozenOrDisabled cellBorrows cellForest 0 none [] 0
          0 [8] 0) =
      freezeTreeBorrowsOnReadAtProj cellBorrows cellBorrows 0 none [] 0 0
        [8] 0 ∧
    pruneForeignReadFrozenOrDisabled cellBorrows cellForest 0 none [] 0 0
        [8] 0 =
      cellForestOf .frozen (.reservedFrz false) .frozen .frozen none :=
  ⟨pruneForeignReadFrozenOrDisabled_rootNoop_equiv_fullScan cell_sameAlloc
      cell_rootNoop.2 0 none [] 0 0 0, rfl⟩

/-- Negative twin: the permission-aware read skips the `.cell` root `90`
and leaves its child `91` `.unique`, unlike the trusted scan. -/
theorem cell_permissionAware_read_diverges :
    pruneForeignRead cellBorrows cellForest 0 none [] 0 0 [8] 0 =
      cellForestOf .frozen (.reservedFrz false) .unique .frozen none ∧
    summary (pruneForeignRead cellBorrows cellForest 0 none [] 0 0 [8] 0) ≠
      (freezeTreeBorrowsOnReadAtProj cellBorrows cellBorrows 0 none [] 0 0
        [8] 0).map fun e => (e.tag, e.perm) := by
  refine ⟨rfl, ?_⟩
  decide +kernel

/-- The root no-op conflict and read-UB tests agree with the trusted scans.
The protected `.cell` borrow `71` is inspected by the trusted scans but
never conflicts. -/
theorem cell_flags_equiv :
    pruneHasProtectedWriteConflictDisabled cellBorrows cellForest [8] 0 none
        [] 0 0 0 =
      hasProtectedWriteConflict cellBorrows [8] 0 none [] 0 0 0 ∧
    pruneHasProtectedTreeWriteConflictDisabled cellBorrows cellForest [8] 0
        none [] 0 0 0 =
      hasProtectedTreeWriteConflict cellBorrows cellBorrows [8] 0 none [] 0
        0 0 ∧
    pruneHasTreeReadUBFrozenOrDisabled cellBorrows cellForest [8] 0 none []
        0 0 0 =
      hasTreeReadUB cellBorrows cellBorrows [8] 0 none [] 0 0 0 ∧
    pruneHasFrameDeallocProtectorConflict cellForest [8] 0 1 =
      hasFrameDeallocProtectorConflict cellBorrows [8] 0 1 :=
  ⟨pruneHasProtectedWriteConflictDisabled_rootNoop_equiv_fullScan
      cell_sameAlloc cell_rootNoop.1 0 none [] 0 0 0,
    pruneHasProtectedTreeWriteConflictDisabled_rootNoop_equiv_fullScan
      cell_sameAlloc cell_rootNoop.1 0 none [] 0 0 0,
    pruneHasTreeReadUBFrozenOrDisabled_rootNoop_equiv_fullScan
      cell_sameAlloc cell_rootNoop.2 0 none [] 0 0 0,
    pruneHasFrameDeallocProtectorConflict_rootNoop_equiv_fullScan
      cell_sameAlloc cell_rootNoop.1 0 1⟩

/-- All four flags are clear on the cell-aware fixture with protector `8`
active. -/
theorem cell_flags_values :
    pruneHasProtectedWriteConflictDisabled cellBorrows cellForest [8] 0 none
      [] 0 0 0 = false ∧
    pruneHasProtectedTreeWriteConflictDisabled cellBorrows cellForest [8] 0
      none [] 0 0 0 = false ∧
    pruneHasTreeReadUBFrozenOrDisabled cellBorrows cellForest [8] 0 none []
      0 0 0 = false ∧
    pruneHasFrameDeallocProtectorConflict cellForest [8] 0 1 = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Cross-call protector push and pop over four steps

A call that retags the borrow `91` with protector `9`, reads through it,
and returns; the caller then writes `_0` directly. Every invariant after
the first step is derived from the preservation theorems.
-/

/-- Step 1 (function entry): attach protector `9` to tag `91`. -/
def cellEntry : BorrowForest :=
  pruneAttachBorrowProtector cellBorrows cellForest 91 9

/-- Trusted table after step 1. -/
def cellEntryTable : List BorrowEntry :=
  attachBorrowProtector cellBorrows 91 9

/-- Step 1 changes exactly the protector of `91`, and its flattening is the
trusted table. -/
theorem cellEntry_result :
    cellEntry =
      cellForestOf .frozen (.reservedFrz false) .unique .unique (some 9) ∧
    BorrowForest.toList cellEntry = cellEntryTable :=
  ⟨rfl, pruneAttachBorrowProtector_equiv_fullScan cell_sameAlloc 91 9⟩

/-- After step 1 all three invariants hold with the new protector pushed:
`[9, 8]` is active. -/
theorem cellEntry_invariants :
    SameAllocForest cellEntryTable cellEntry ∧
    DisabledRootWriteNoopForest [9, 8] cellEntry ∧
    FrozenOrDisabledRootReadNoopForest [9, 8] cellEntry :=
  ⟨pruneAttachBorrowProtector_preserves_sameAlloc cell_sameAlloc 91 9,
    pruneAttachBorrowProtector_preserves_disabledRootWriteNoop
      cell_sameAlloc cell_rootNoop.1 91 9 cell_wholeAlloc_fresh.2
      (by decide +kernel),
    pruneAttachBorrowProtector_preserves_frozenOrDisabledRootReadNoop
      cell_sameAlloc cell_rootNoop.2 91 9 cell_wholeAlloc_fresh.2
      (by decide +kernel)⟩

/-- Step 2 (callee body): read `_0` through the protected tag `91`. -/
def cellCallee : BorrowForest :=
  pruneForeignReadFrozenOrDisabled cellEntryTable cellEntry 0 (some 91) [] 0
    0 [9, 8] 0

/-- Trusted table after step 2. -/
def cellCalleeTable : List BorrowEntry :=
  freezeTreeBorrowsOnReadAtProj cellEntryTable cellEntryTable 0 (some 91) []
    0 0 [9, 8] 0

/-- Entries of the step-1 forest borrow the whole allocation. -/
theorem cellEntry_wholeAlloc :
    ∀ e, e ∈ BorrowForest.toList cellEntry → e.targetProjection = [] := by
  decide +kernel

/-- Step 2 freezes only the foreign live root `95`; its flattening is the
trusted table, and the read is defined. -/
theorem cellCallee_result :
    cellCallee =
      cellForestOf .frozen (.reservedFrz false) .unique .frozen (some 9) ∧
    BorrowForest.toList cellCallee = cellCalleeTable ∧
    hasTreeReadUB cellEntryTable (BorrowForest.toList cellEntry) [9, 8] 0
      (some 91) [] 0 0 0 = false :=
  ⟨rfl,
    (pruneForeignReadFrozenOrDisabled_rootNoop_equiv_fullScan
      cellEntry_invariants.1 cellEntry_invariants.2.2 0 (some 91) [] 0 0
      0).trans
      (congrArg
        (fun bs =>
          freezeTreeBorrowsOnReadAtProj cellEntryTable bs 0 (some 91) [] 0 0
            [9, 8] 0)
        cellEntry_result.2),
    rfl⟩

/-- After step 2 all three invariants still hold under `[9, 8]`. -/
theorem cellCallee_invariants :
    SameAllocForest cellCalleeTable cellCallee ∧
    DisabledRootWriteNoopForest [9, 8] cellCallee ∧
    FrozenOrDisabledRootReadNoopForest [9, 8] cellCallee :=
  ⟨pruneForeignReadFrozenOrDisabled_preserves_sameAlloc
      cellEntry_invariants.1 0 (some 91) [] 0 0 [9, 8] 0,
    pruneForeignReadFrozenOrDisabled_preserves_disabledRootWriteNoop
      (allBorrows := cellEntryTable) cellEntry_invariants.2.1 0 (some 91) []
      0 0 0 cellCallee_result.2.2,
    pruneForeignReadFrozenOrDisabled_preserves_frozenOrDisabledRootReadNoop
      cellEntry_invariants.1 cellEntry_invariants.2.2 0 (some 91) 0
      cellEntry_wholeAlloc cellCallee_result.2.2⟩

/-- Step 3 (function return): protector `9` is popped. Both root no-op
invariants are antitone in the protector set, so they hold under `[8]`. -/
theorem cellReturn_invariants :
    DisabledRootWriteNoopForest [8] cellCallee ∧
    FrozenOrDisabledRootReadNoopForest [8] cellCallee :=
  ⟨cellCallee_invariants.2.1.antitone_protectors
      (fun _ hp => List.mem_cons_of_mem _ hp),
    cellCallee_invariants.2.2.antitone_protectors
      (fun _ hp => List.mem_cons_of_mem _ hp)⟩

/-- Step 4 (caller): write `_0` directly. -/
def cellAfterWrite : BorrowForest :=
  pruneForeignWriteDisabled cellCalleeTable cellCallee 0 none [] 0 0 0

/-- Trusted table after step 4. -/
def cellAfterWriteTable : List BorrowEntry :=
  invalidateTreeBorrowsAtProj cellCalleeTable cellCalleeTable 0 none [] 0 0
    0

/-- Entries of the step-2 forest borrow the whole allocation. -/
theorem cellCallee_wholeAlloc :
    ∀ e, e ∈ BorrowForest.toList cellCallee → e.targetProjection = [] := by
  decide +kernel

/-- The direct write is conflict-free once protector `9` is popped, and
would have conflicted with the protected `.unique` borrow `91` before the
pop. -/
theorem cellAfterWrite_conflict :
    hasProtectedTreeWriteConflict cellCalleeTable
      (BorrowForest.toList cellCallee) [8] 0 none [] 0 0 0 = false ∧
    hasProtectedTreeWriteConflict cellCalleeTable
      (BorrowForest.toList cellCallee) [9, 8] 0 none [] 0 0 0 = true :=
  ⟨rfl, rfl⟩

/-- Step 4 disables every live borrow of `_0`; its flattening is the
trusted table. -/
theorem cellAfterWrite_result :
    cellAfterWrite =
      cellForestOf .disabled .disabled .disabled .disabled (some 9) ∧
    BorrowForest.toList cellAfterWrite = cellAfterWriteTable :=
  ⟨rfl,
    (pruneForeignWriteDisabled_rootNoop_equiv_fullScan
      cellCallee_invariants.1 cellReturn_invariants.1 0 none [] 0 0 0).trans
      (congrArg
        (fun bs =>
          invalidateTreeBorrowsAtProj cellCalleeTable bs 0 none [] 0 0 0)
        cellCallee_result.2.1)⟩

/-- After step 4 all three invariants still hold under `[8]`. -/
theorem cellAfterWrite_invariants :
    SameAllocForest cellAfterWriteTable cellAfterWrite ∧
    DisabledRootWriteNoopForest [8] cellAfterWrite ∧
    FrozenOrDisabledRootReadNoopForest [8] cellAfterWrite :=
  ⟨pruneForeignWriteDisabled_preserves_sameAlloc cellCallee_invariants.1 0
      none [] 0 0 0,
    pruneForeignWriteDisabled_preserves_disabledRootWriteNoop_direct
      cellCallee_invariants.1 cellReturn_invariants.1 0 0
      cellCallee_wholeAlloc cellAfterWrite_conflict.1,
    pruneForeignWriteDisabled_preserves_frozenOrDisabledRootReadNoop_direct
      cellCallee_invariants.1 cellReturn_invariants.1
      cellReturn_invariants.2 0 0 cellCallee_wholeAlloc
      cellAfterWrite_conflict.1⟩

/-- After the four steps, the derived invariants still give exact
agreement with the trusted scans: reading through `92`, whose parent `91`
was disabled by the write, is undefined behavior, while a direct read is
defined and a second direct write is conflict-free. -/
theorem cellAfterWrite_final_checks :
    pruneHasTreeReadUBFrozenOrDisabled cellAfterWriteTable cellAfterWrite
        [8] 0 (some 92) [] 0 0 0 =
      hasTreeReadUB cellAfterWriteTable (BorrowForest.toList cellAfterWrite)
        [8] 0 (some 92) [] 0 0 0 ∧
    pruneHasTreeReadUBFrozenOrDisabled cellAfterWriteTable cellAfterWrite
      [8] 0 (some 92) [] 0 0 0 = true ∧
    pruneHasTreeReadUBFrozenOrDisabled cellAfterWriteTable cellAfterWrite
      [8] 0 none [] 0 0 0 = false ∧
    pruneHasProtectedTreeWriteConflictDisabled cellAfterWriteTable
        cellAfterWrite [8] 0 none [] 0 0 0 =
      hasProtectedTreeWriteConflict cellAfterWriteTable
        (BorrowForest.toList cellAfterWrite) [8] 0 none [] 0 0 0 ∧
    pruneHasProtectedTreeWriteConflictDisabled cellAfterWriteTable
      cellAfterWrite [8] 0 none [] 0 0 0 = false :=
  ⟨pruneHasTreeReadUBFrozenOrDisabled_rootNoop_equiv_fullScan
      cellAfterWrite_invariants.1 cellAfterWrite_invariants.2.2 0 (some 92)
      [] 0 0 0, rfl, rfl,
    pruneHasProtectedTreeWriteConflictDisabled_rootNoop_equiv_fullScan
      cellAfterWrite_invariants.1 cellAfterWrite_invariants.2.1 0 none [] 0
      0 0, rfl⟩

/-! ### Protector push without attachment, and invariant conversions -/

/-- No entry of the main fixture carries protector `9`. -/
theorem fx_fresh9 :
    ∀ e, e ∈ BorrowForest.toList fxForest → e.protector ≠ some 9 := by
  decide +kernel

/-- Each stricter invariant of the main fixture yields the root no-op
invariants, for any protector set. -/
theorem fx_rootNoop_of_strict (ps : List Nat) :
    DisabledRootWriteNoopForest ps fxForest ∧
    FrozenOrDisabledRootReadNoopForest ps fxForest ∧
    DisabledRootWriteNoopForest [6] fxForest ∧
    FrozenOrDisabledRootReadNoopForest [6] fxForest :=
  ⟨fx_closed.1.to_disabledRootWriteNoop,
    FrozenClosedForest.to_frozenOrDisabledRootReadNoop fx_closed.1
      fx_closed.2,
    fx_writeNoop.2.1.to_disabledRootWriteNoop,
    fx_readNoop.2.1.to_frozenOrDisabledRootReadNoop⟩

/-- A call that pushes the fresh protector `9` without retagging any borrow
of the forest keeps both root no-op invariants, and so does the return that
pops it again. -/
theorem fx_push_pop_fresh_protector :
    DisabledRootWriteNoopForest [9, 6] fxForest ∧
    FrozenOrDisabledRootReadNoopForest [9, 6] fxForest ∧
    DisabledRootWriteNoopForest [6] fxForest ∧
    FrozenOrDisabledRootReadNoopForest [6] fxForest :=
  have hW := (fx_rootNoop_of_strict [6]).1.push_fresh_protector 9 fx_fresh9
  have hR :=
    (fx_rootNoop_of_strict [6]).2.1.push_fresh_protector 9 fx_fresh9
  ⟨hW, hR,
    hW.antitone_protectors (fun _ hp => List.mem_cons_of_mem _ hp),
    hR.antitone_protectors (fun _ hp => List.mem_cons_of_mem _ hp)⟩

/-- With the fresh protector pushed, the root no-op traversals still agree
with the trusted scans on the main fixture. -/
theorem fx_pushed_protector_equiv :
    BorrowForest.toList
        (pruneForeignReadFrozenOrDisabled fxBorrows fxForest 0 none [] 0 0
          [9, 6] 0) =
      freezeTreeBorrowsOnReadAtProj fxBorrows fxBorrows 0 none [] 0 0
        [9, 6] 0 ∧
    pruneHasProtectedTreeWriteConflictDisabled fxBorrows fxForest [9, 6] 0
        (some 52) [] 0 0 0 =
      hasProtectedTreeWriteConflict fxBorrows fxBorrows [9, 6] 0 (some 52)
        [] 0 0 0 ∧
    pruneHasProtectedTreeWriteConflictDisabled fxBorrows fxForest [9, 6] 0
      (some 52) [] 0 0 0 = false :=
  ⟨pruneForeignReadFrozenOrDisabled_rootNoop_equiv_fullScan fx_sameAlloc
      fx_push_pop_fresh_protector.2.1 0 none [] 0 0 0,
    pruneHasProtectedTreeWriteConflictDisabled_rootNoop_equiv_fullScan
      fx_sameAlloc fx_push_pop_fresh_protector.1 0 (some 52) [] 0 0 0, rfl⟩

/-- A `.disabled` root whose `.reservedIM` child carries the inactive
protector `5`. -/
def staleProtForest : BorrowForest :=
  [.node (mkEntry 1 0 .disabled)
    [.node (mkEntry 2 0 .reservedIM (some 1) (some 5)) []]]

/-- Tightness of the freshness hypothesis of `push_fresh_protector`: the
forest satisfies the root no-op write invariant while protector `5` is
inactive, pushing the fresh protector `9` keeps it, and pushing the stale
protector `5` breaks it. -/
theorem push_stale_protector_breaks_rootNoop :
    DisabledRootWriteNoopForest [] staleProtForest ∧
    DisabledRootWriteNoopForest [9] staleProtForest ∧
    ¬ DisabledRootWriteNoopForest [5] staleProtForest := by
  have h0 : DisabledRootWriteNoopForest [] staleProtForest := by
    decide +kernel
  exact ⟨h0, h0.push_fresh_protector 9 (by decide +kernel),
    by decide +kernel⟩

/-! ### Projection-sensitive accesses

A fixture whose borrows target disjoint fields of local `_0`, so that the
projection-sensitive traversals leave disjoint subtrees untouched.
-/

/-- Field `i` of the borrowed local. -/
def fld (i : Nat) : ProjectionElem := .field i cexUnitTy

/-- Borrow entry of local `_0` at projection `proj`. -/
def mkProjEntry (tag : Nat) (proj : List ProjectionElem)
    (perm : TreeBorrowPerm) (parent : Option Nat := none)
    (prot : Option Nat := none) : BorrowEntry :=
  { tag := tag, targetLocal := 0, targetProjection := proj, perm := perm,
    protector := prot, parentTag := parent }

/-- The projection fixture, parameterised by four permissions: a
whole-allocation root `1` with a subtree on field `0` (tags `2`, `4`) and a
subtree on field `1` (tags `3`, `5`); a root `6` on field `1` carrying
protector `2`; and an unrelated root on local `_3`. -/
def projForestOf (p1 p2 p3 p6 : TreeBorrowPerm) : BorrowForest :=
  [ .node (mkProjEntry 1 [] p1)
      [.node (mkProjEntry 2 [fld 0] p2 (some 1))
        [.node (mkProjEntry 4 [fld 0] (.reservedFrz false) (some 2)) []],
       .node (mkProjEntry 3 [fld 1] p3 (some 1))
        [.node (mkProjEntry 5 [fld 1] .cell (some 3)) []]],
    .node (mkProjEntry 6 [fld 1] p6 none (some 2)) [],
    .node (mkEntry 7 3 .unique) [] ]

/-- The projection fixture. -/
def projForest : BorrowForest := projForestOf .unique .unique .unique .frozen

/-- The trusted flat borrow table of the projection fixture. -/
def projBorrows : List BorrowEntry := BorrowForest.toList projForest

/-- The projection fixture is well formed and satisfies both
permission-aware invariants. -/
theorem proj_invariants :
    SameAllocForest projBorrows projForest ∧
    ForeignWriteNoopForest [] projForest ∧
    ForeignWriteNoopForest [2] projForest ∧
    ForeignReadNoopForest [2] projForest := by
  decide +kernel

/-- A direct write to field `1`: the projection-sensitive pruned write is
the trusted scan. It disables the whole-allocation root and the borrows of
field `1`, and leaves the subtree on field `0` and the `.cell` leaf alone. -/
theorem proj_fieldWrite :
    BorrowForest.toList
        (pruneForeignWriteProj projBorrows projForest 0 none [fld 1] 0 0 0
          []) =
      invalidateConflictingBorrowsAtProj projBorrows 0 none [fld 1] 0 0 0 ∧
    pruneForeignWriteProj projBorrows projForest 0 none [fld 1] 0 0 0 [] =
      projForestOf .disabled .unique .disabled .disabled :=
  ⟨pruneForeignWriteProj_equiv_fullScan proj_invariants.1
      proj_invariants.2.1 0 none [fld 1] 0 0 0, rfl⟩

/-- A tree-resolved write to field `1` through the `.cell` leaf `5` is a
child write of its ancestors `3` and `1`, and disables only the foreign
root `6` on the same field. -/
theorem proj_fieldTreeWrite :
    BorrowForest.toList
        (pruneForeignWrite projBorrows projForest 0 (some 5) [fld 1] 0 0 0
          []) =
      invalidateTreeBorrowsAtProj projBorrows projBorrows 0 (some 5) [fld 1]
        0 0 0 ∧
    pruneForeignWrite projBorrows projForest 0 (some 5) [fld 1] 0 0 0 [] =
      projForestOf .unique .unique .unique .disabled :=
  ⟨pruneForeignWrite_equiv_fullScan proj_invariants.1 proj_invariants.2.1 0
      (some 5) [fld 1] 0 0 0, rfl⟩

/-- The conflict test is projection-sensitive: with protector `2` active, a
direct write to field `1` conflicts with the protected root `6`, and a
direct write to field `0` does not. -/
theorem proj_fieldWrite_conflict :
    pruneHasProtectedWriteConflict projBorrows projForest [2] 0 none [fld 1]
        0 0 0 =
      hasProtectedWriteConflict projBorrows [2] 0 none [fld 1] 0 0 0 ∧
    pruneHasProtectedWriteConflict projBorrows projForest [2] 0 none [fld 1]
      0 0 0 = true ∧
    pruneHasProtectedWriteConflict projBorrows projForest [2] 0 none [fld 0]
        0 0 0 =
      hasProtectedWriteConflict projBorrows [2] 0 none [fld 0] 0 0 0 ∧
    pruneHasProtectedWriteConflict projBorrows projForest [2] 0 none [fld 0]
      0 0 0 = false :=
  ⟨pruneHasProtectedWriteConflict_equiv_fullScan proj_invariants.1
      proj_invariants.2.2.1 0 none [fld 1] 0 0 0, rfl,
    pruneHasProtectedWriteConflict_equiv_fullScan proj_invariants.1
      proj_invariants.2.2.1 0 none [fld 0] 0 0 0, rfl⟩

/-- A direct read of field `0` freezes the whole-allocation root and the
live borrow of field `0`, and leaves the subtree on field `1` alone. -/
theorem proj_fieldRead :
    BorrowForest.toList
        (pruneForeignRead projBorrows projForest 0 none [fld 0] 0 0 [2] 0) =
      freezeTreeBorrowsOnReadAtProj projBorrows projBorrows 0 none [fld 0] 0
        0 [2] 0 ∧
    pruneForeignRead projBorrows projForest 0 none [fld 0] 0 0 [2] 0 =
      projForestOf .frozen .frozen .unique .frozen :=
  ⟨pruneForeignRead_equiv_fullScan proj_invariants.1 proj_invariants.2.2.2
      0 none [fld 0] 0 0 0, rfl⟩

/-! ### `MirLiftCore` integration: `assignLocalPlace` -/

/-- An unprojected assignment to `_0` on the main fixture: the borrow table
returned by `assignLocalPlace` is the flattening of the pruned write, which
is the explicit forest of the direct write. -/
theorem fx_assignLocalPlace_pruned :
    assignLocalPlace [.uninit] fxBorrows { local_ := 0, projection := [] }
        .unit =
      some ([.init .unit], invalidateConflictingBorrows fxBorrows 0 none 0) ∧
    invalidateConflictingBorrows fxBorrows 0 none 0 =
      BorrowForest.toList
        (pruneAssignLocalPlaceBorrows fxBorrows fxForest [.uninit]
          { local_ := 0, projection := [] } [] emptyLayoutTable 0 [7]) ∧
    pruneAssignLocalPlaceBorrows fxBorrows fxForest [.uninit]
        { local_ := 0, projection := [] } [] emptyLayoutTable 0 [7] =
      fxForestOf .disabled .disabled .disabled .disabled .reservedIM :=
  ⟨rfl,
    assignLocalPlace_pruned_borrows fx_sameAlloc fx_writeNoop_conflictSets.1
      (show assignLocalPlace [.uninit] (BorrowForest.toList fxForest)
          { local_ := 0, projection := [] } .unit [] emptyLayoutTable 0 =
          some ([.init .unit],
            invalidateConflictingBorrows fxBorrows 0 none 0) from rfl),
    rfl⟩

/-- Root value of a two-field local. -/
def pairVal : Value := .aggregate 0 [.unit, .unit]

/-- A projected assignment to field `1` of `_0` on the projection fixture:
`assignLocalPlace` returns the projection-sensitive trusted scan, which is
the flattening of the pruned projection write. -/
theorem proj_assignLocalPlace_pruned :
    assignLocalPlace [.init pairVal] projBorrows
        { local_ := 0, projection := [fld 1] } .unit =
      some ([.init pairVal],
        invalidateConflictingBorrowsAtProj projBorrows 0 none [fld 1] 0 0
          0) ∧
    invalidateConflictingBorrowsAtProj projBorrows 0 none [fld 1] 0 0 0 =
      BorrowForest.toList
        (pruneAssignLocalPlaceBorrows projBorrows projForest [.init pairVal]
          { local_ := 0, projection := [fld 1] } [] emptyLayoutTable 0 []) ∧
    pruneAssignLocalPlaceBorrows projBorrows projForest [.init pairVal]
        { local_ := 0, projection := [fld 1] } [] emptyLayoutTable 0 [] =
      projForestOf .disabled .unique .disabled .disabled :=
  ⟨rfl,
    assignLocalPlace_pruned_borrows proj_invariants.1 proj_invariants.2.1
      (show assignLocalPlace [.init pairVal] (BorrowForest.toList projForest)
          { local_ := 0, projection := [fld 1] } .unit [] emptyLayoutTable
          0 =
          some ([.init pairVal],
            invalidateConflictingBorrowsAtProj projBorrows 0 none [fld 1] 0
              0 0) from rfl),
    rfl⟩

/-- The cell-aware `assignLocalPlace` rule on the cell-aware fixture, under
the root no-op invariant only. -/
theorem cell_assignLocalPlace_pruned :
    assignLocalPlace [.uninit] cellBorrows { local_ := 0, projection := [] }
        .unit =
      some ([.init .unit],
        invalidateConflictingBorrows cellBorrows 0 none 0) ∧
    invalidateConflictingBorrows cellBorrows 0 none 0 =
      BorrowForest.toList
        (pruneAssignLocalPlaceBorrowsDisabled cellBorrows cellForest
          [.uninit] { local_ := 0, projection := [] } [] emptyLayoutTable
          0) ∧
    pruneAssignLocalPlaceBorrowsDisabled cellBorrows cellForest [.uninit]
        { local_ := 0, projection := [] } [] emptyLayoutTable 0 =
      cellForestOf .disabled .disabled .disabled .disabled none :=
  ⟨rfl,
    assignLocalPlace_pruned_borrows_rootNoop cell_sameAlloc cell_rootNoop.1
      (show assignLocalPlace [.uninit] (BorrowForest.toList cellForest)
          { local_ := 0, projection := [] } .unit [] emptyLayoutTable 0 =
          some ([.init .unit],
            invalidateConflictingBorrows cellBorrows 0 none 0) from rfl),
    rfl⟩

/-- The `.disabled`-closure `assignLocalPlace` rule on the main fixture. -/
theorem fx_assignLocalPlace_pruned_disabled :
    invalidateConflictingBorrows fxBorrows 0 none 0 =
      BorrowForest.toList
        (pruneAssignLocalPlaceBorrowsDisabled fxBorrows fxForest [.uninit]
          { local_ := 0, projection := [] } [] emptyLayoutTable 0) ∧
    pruneAssignLocalPlaceBorrowsDisabled fxBorrows fxForest [.uninit]
        { local_ := 0, projection := [] } [] emptyLayoutTable 0 =
      fxForestOf .disabled .disabled .disabled .disabled .reservedIM :=
  ⟨assignLocalPlace_pruned_borrows_disabled fx_sameAlloc fx_closed.1
      (show assignLocalPlace [.uninit] (BorrowForest.toList fxForest)
          { local_ := 0, projection := [] } .unit [] emptyLayoutTable 0 =
          some ([.init .unit],
            invalidateConflictingBorrows fxBorrows 0 none 0) from rfl),
    rfl⟩

/-- The unrelated roots of the main fixture are well formed against their
own table, and each root is unrelated to local `_0` of the root frame. -/
theorem fxUnrelated_facts :
    SameAllocForest (BorrowForest.toList fxUnrelated) fxUnrelated ∧
    (∀ t, t ∈ fxUnrelated → isForeignUnrelatedRoot t.root 0 0 = true) := by
  decide +kernel

/-- Any successful assignment to `_0`, at any projection and of any value,
returns a table of unrelated subtrees unchanged, after inspecting only the
two roots. -/
theorem fxUnrelated_assign_unchanged {locals locals' : PureEnv}
    {borrows' : List BorrowEntry} (proj : List ProjectionElem) (val : Value)
    (h : assignLocalPlace locals (BorrowForest.toList fxUnrelated)
      { local_ := 0, projection := proj } val = some (locals', borrows')) :
    borrows' = BorrowForest.toList fxUnrelated :=
  assignLocalPlace_unrelated_forest_borrows fxUnrelated_facts.1
    fxUnrelated_facts.2 h

/-- The subtrees of local `_0` in the main fixture. -/
def fxLocal0 : BorrowForest :=
  [fxDisabledTree, fxFrozenTree .frozen .frozen, fxCellTree,
    fxLiveTree .unique (.reservedFrz false) .reservedIM]

/-- Unrelated subtrees appended to a table are erased from both trusted
write scans, for every writer, projection, and byte range. -/
theorem fxUnrelated_erased (writerTag : Option Nat)
    (writeProj : List ProjectionElem) (off len : Nat) :
    invalidateConflictingBorrows
        (BorrowForest.toList fxLocal0 ++ BorrowForest.toList fxUnrelated) 0
        writerTag 0 =
      invalidateConflictingBorrows (BorrowForest.toList fxLocal0) 0
          writerTag 0 ++
        BorrowForest.toList fxUnrelated ∧
    invalidateConflictingBorrowsAtProj
        (BorrowForest.toList fxLocal0 ++ BorrowForest.toList fxUnrelated) 0
        writerTag writeProj off len 0 =
      invalidateConflictingBorrowsAtProj (BorrowForest.toList fxLocal0) 0
          writerTag writeProj off len 0 ++
        BorrowForest.toList fxUnrelated :=
  ⟨invalidateConflictingBorrows_erase_foreign (BorrowForest.toList fxLocal0)
      fxUnrelated_facts.1 0 writerTag 0 fxUnrelated_facts.2,
    invalidateConflictingBorrowsAtProj_erase_foreign
      (BorrowForest.toList fxLocal0) fxUnrelated_facts.1 0 writerTag
      writeProj off len 0 fxUnrelated_facts.2⟩

/-! ### `MirLiftCore` integration: `LiftFrame` on the trusted machine

The unit-assigning body `_0 = (); return` is run on the trusted machine
from memories whose borrow tables are the fixtures. The assignment is a
direct write to `_0`, so the machine produces the trusted full scan, and
the `LiftFrame` congruences transport the frame proved at the pruned table.
-/

/-- Memory with borrow table `bs` and active protectors `ps`. -/
def memWith (bs : List BorrowEntry) (ps : List Nat := []) : Memory :=
  { emptyMemory with borrows := bs, activeProtectors := ps }

/-- The return frame at the explicit pruned table of the cell-aware
fixture, by running the trusted machine with protector `8` active. -/
theorem cell_returnFrame_pruned :
    LiftFrame emptyFnAssignUnit 0 1 [.init .unit]
      (memWith
        (BorrowForest.toList
          (cellForestOf .disabled .disabled .disabled .disabled none)) [8])
      (fun v => v = .unit) 1 :=
  liftState_iff_liftFrame.mp (LiftState.of_retNormal rfl rfl)

/-- The return frame at the memory holding the trusted full scan, by the
cell-aware congruence: no evaluation of the full scan is needed. -/
theorem cell_returnFrame_fullScan :
    LiftFrame emptyFnAssignUnit 0 1 [.init .unit]
      (memWith (invalidateConflictingBorrows cellBorrows 0 none 0) [8])
      (fun v => v = .unit) 1 :=
  LiftFrame_congr_pruned_borrows_rootNoop cell_sameAlloc cell_rootNoop.1 0
    none 0 rfl cell_returnFrame_pruned

/-- End to end on the trusted machine: from the cell-aware fixture, the
assignment steps to the memory holding the trusted full scan, where the
transported return frame applies. -/
theorem cell_liftFrame_end_to_end :
    LiftFrame emptyFnAssignUnit 0 0 [.uninit] (memWith cellBorrows [8])
      (fun v => v = .unit) 2 :=
  liftState_iff_liftFrame.mp
    (LiftState.of_step
      (s' := PureState.toMachineState
        { bb := 0, stmtIdx := 1, env := [.init .unit] }
        (memWith (invalidateConflictingBorrows cellBorrows 0 none 0) [8]))
      rfl (liftState_iff_liftFrame.mpr cell_returnFrame_fullScan))

/-- The same transport stated across `assignLocalPlace`: the frame after
the lifted assignment follows from the frame at the pruned table. -/
theorem cell_returnFrame_assignLocalPlace :
    LiftFrame emptyFnAssignUnit 0 1 [.init .unit]
      (memWith (invalidateConflictingBorrows cellBorrows 0 none 0) [8])
      (fun v => v = .unit) 1 :=
  LiftFrame_congr_assignLocalPlace_rootNoop cell_sameAlloc cell_rootNoop.1
    (show assignLocalPlace [.uninit] (BorrowForest.toList cellForest)
        { local_ := 0, projection := [] } .unit [] emptyLayoutTable 0 =
        some ([.init .unit],
          invalidateConflictingBorrows cellBorrows 0 none 0) from rfl)
    rfl cell_returnFrame_pruned

/-- The return frame at the explicit pruned table of the main fixture, with
the callee-frame protector `7` active. -/
theorem fx_returnFrame_pruned :
    LiftFrame emptyFnAssignUnit 0 1 [.init .unit]
      (memWith
        (BorrowForest.toList
          (fxForestOf .disabled .disabled .disabled .disabled .reservedIM))
        [7])
      (fun v => v = .unit) 1 :=
  liftState_iff_liftFrame.mp (LiftState.of_retNormal rfl rfl)

/-- End to end on the trusted machine from the main fixture, through the
permission-aware congruence. -/
theorem fx_liftFrame_end_to_end :
    LiftFrame emptyFnAssignUnit 0 0 [.uninit] (memWith fxBorrows [7])
      (fun v => v = .unit) 2 :=
  liftState_iff_liftFrame.mp
    (LiftState.of_step
      (s' := PureState.toMachineState
        { bb := 0, stmtIdx := 1, env := [.init .unit] }
        (memWith (invalidateConflictingBorrows fxBorrows 0 none 0) [7]))
      rfl
      (liftState_iff_liftFrame.mpr
        (LiftFrame_congr_pruned_borrows fx_sameAlloc
          fx_writeNoop_conflictSets.1 0 none 0 rfl fx_returnFrame_pruned)))

/-- Body performing a projected field write `_0.1 = (); return`. -/
def cellProjWriteBody : CapturedMir :=
  { emptyFnAssignUnit with
    defPath := "Anneal::TbPruningTests::cell_proj_write"
    basicBlocks := [
      { statements := [
          { kind := .assign { local_ := 0, projection := [fld 1] }
              (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
            span := "proj_write" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false }] }

/-- End-to-end on the trusted machine for a projected field write on the
cell-aware fixture: `stepMirFn` runs `invalidateConflictingBorrowsAtProj`,
and `LiftFrame_congr_pruned_borrows_proj_rootNoop` transports the return
frame proved at the explicit pruned forest (where strict invariants fail). -/
theorem cell_projWrite_liftFrame_end_to_end :
    LiftFrame cellProjWriteBody 0 0 [.init pairVal] (memWith cellBorrows [8])
      (fun v => v = pairVal) 2 :=
  liftState_iff_liftFrame.mp
    (LiftState.of_step
      (s' := PureState.toMachineState
        { bb := 0, stmtIdx := 1, env := [.init pairVal] }
        (memWith
          (invalidateConflictingBorrowsAtProj cellBorrows 0 none [fld 1] 0 0
            0) [8]))
      rfl
      (liftState_iff_liftFrame.mpr
        (LiftFrame_congr_pruned_borrows_proj_rootNoop cell_sameAlloc
          cell_rootNoop.1 0 none [fld 1] 0 0 0 rfl
          (liftState_iff_liftFrame.mp (LiftState.of_retNormal rfl rfl)))))

/-- Body performing a pointer-dereference write `*_1 = (); return`. -/
def cellPtrWriteBody : CapturedMir :=
  { emptyFnAssignUnit with
    defPath := "Anneal::TbPruningTests::cell_ptr_write"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .not
        ty := { kind := .ref .mut (.tuple []), layoutIdx := 0 }
        debugName := some "_1" }]
    basicBlocks := [
      { statements := [
          { kind := .assign { local_ := 1, projection := [.deref] }
              (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
            span := "ptr_write" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false }] }

/-- End-to-end on the trusted machine for a tree-resolved pointer write
through tag `91` (the `.unique` child of `.cell` root `90`): `stepMirFn` runs
`invalidateTreeBorrowsAtProj`, and
`LiftFrame_congr_pruned_borrows_tree_rootNoop` transports the return frame
proved at the explicit pruned forest (tag `91` stays `.unique`). -/
theorem cell_ptrWrite_liftFrame_end_to_end :
    LiftFrame cellPtrWriteBody 0 0
      [.init .unit, .init (.ptr { allocId := 91, offsetBytes := 0 } 8)]
      (memWith cellBorrows [8]) (fun v => v = .unit) 2 :=
  liftState_iff_liftFrame.mp
    (LiftState.of_step
      (s' := PureState.toMachineState
        { bb := 0, stmtIdx := 1,
          env :=
            [.init .unit,
              .init (.ptr { allocId := 91, offsetBytes := 0 } 8)] }
        (memWith
          (invalidateTreeBorrowsAtProj cellBorrows cellBorrows 0 (some 91) []
            0 0 0) [8]))
      rfl
      (liftState_iff_liftFrame.mpr
        (LiftFrame_congr_pruned_borrows_tree_rootNoop cell_sameAlloc
          cell_rootNoop.1 0 (some 91) [] 0 0 0 rfl
          (liftState_iff_liftFrame.mp (LiftState.of_retNormal rfl rfl)))))

/-- Body performing a pointer-dereference read `_1 = copy (*_2); return`. -/
def cellReadBody : CapturedMir :=
  { emptyFnAssignUnit with
    defPath := "Anneal::TbPruningTests::cell_read"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_1" },
      { mutability := .not
        ty := { kind := .ref .not (.tuple []), layoutIdx := 0 }
        debugName := some "_2" }]
    basicBlocks := [
      { statements := [
          { kind := .assign { local_ := 1, projection := [] }
              (.use (.copy { local_ := 2, projection := [.deref] }))
            span := "ptr_read" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false }] }

/-- End-to-end on the trusted machine for a dereference read through tag `91`
on the cell-aware fixture: `stepMirFn` runs `freezeTreeBorrowsOnReadAtProj`
(and writing the unborrowed local `_1` leaves the table unchanged), and
`LiftFrame_congr_pruned_borrows_read_rootNoop` transports the return frame
proved at the explicit pruned forest (freezing only foreign live root `95`). -/
theorem cell_read_liftFrame_end_to_end :
    LiftFrame cellReadBody 0 0
      [.init .unit, .uninit,
        .init (.ptr { allocId := 91, offsetBytes := 0 } 8)]
      (memWith cellBorrows [8]) (fun v => v = .unit) 2 :=
  liftState_iff_liftFrame.mp
    (LiftState.of_step
      (s' := PureState.toMachineState
        { bb := 0, stmtIdx := 1,
          env :=
            [.init .unit, .init .unit,
              .init (.ptr { allocId := 91, offsetBytes := 0 } 8)] }
        (memWith
          (freezeTreeBorrowsOnReadAtProj cellBorrows cellBorrows 0 (some 91)
            [] 0 0 [8] 0) [8]))
      rfl
      (liftState_iff_liftFrame.mpr
        (LiftFrame_congr_pruned_borrows_read_rootNoop cell_sameAlloc
          cell_rootNoop.2 0 (some 91) [] 0 0 0 rfl
          (liftState_iff_liftFrame.mp (LiftState.of_retNormal rfl rfl)))))

/-! ### `MirLiftCore` integration: `LiftFrame` congruences for any frame

For an arbitrary body, frame, postcondition, and fuel: a frame at a memory
holding a trusted full scan of a fixture follows from the frame at the
explicit pruned forest.
-/

section LiftFrameCongruence

variable {body : CapturedMir} {bbIdx : BasicBlockIdx} {stmtIdx : Nat}
  {env : PureEnv} {mem : Memory} {post : Value → Prop} {fuel : Nat}

/-- Projection-sensitive write to field `1` on the projection fixture. -/
theorem proj_liftFrame_congr_proj
    (hmem : mem.borrows =
      invalidateConflictingBorrowsAtProj projBorrows 0 none [fld 1] 0 0 0)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (projForestOf .disabled .unique .disabled .disabled) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_pruned_borrows_proj proj_invariants.1 proj_invariants.2.1
    0 none [fld 1] 0 0 0 hmem h

/-- Tree-resolved write through `52` on the main fixture. -/
theorem fx_liftFrame_congr_tree
    (hmem : mem.borrows =
      invalidateTreeBorrowsAtProj fxBorrows fxBorrows 0 (some 52) [] 0 0 0)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (fxForestOf .disabled .disabled .unique .unique .unique) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_pruned_borrows_tree fx_sameAlloc fx_writeNoop.2.1 0
    (some 52) [] 0 0 0 hmem h

/-- Direct read with protector `6` active on the main fixture. -/
theorem fx_liftFrame_congr_read
    (hmem : mem.borrows =
      freezeTreeBorrowsOnReadAtProj fxBorrows fxBorrows 0 none [] 0 0 [6] 0)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (fxForestOf .frozen .frozen .frozen (.reservedFrz true)
              .reservedIM) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_pruned_borrows_read fx_sameAlloc fx_readNoop.2.1 0 none []
    0 0 0 hmem h

/-- Cell-aware projection-sensitive direct write on the cell-aware
fixture. -/
theorem cell_liftFrame_congr_proj_rootNoop
    (hmem : mem.borrows =
      invalidateConflictingBorrowsAtProj cellBorrows 0 none [] 0 0 0)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (cellForestOf .disabled .disabled .disabled .disabled none) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_pruned_borrows_proj_rootNoop cell_sameAlloc
    cell_rootNoop.1 0 none [] 0 0 0 hmem h

/-- Cell-aware tree-resolved write through `91` on the cell-aware fixture:
the live child of the `.cell` root stays `.unique`. -/
theorem cell_liftFrame_congr_tree_rootNoop
    (hmem : mem.borrows =
      invalidateTreeBorrowsAtProj cellBorrows cellBorrows 0 (some 91) [] 0 0
        0)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (cellForestOf .disabled .disabled .unique .disabled none) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_pruned_borrows_tree_rootNoop cell_sameAlloc
    cell_rootNoop.1 0 (some 91) [] 0 0 0 hmem h

/-- Cell-aware direct read with protector `8` active on the cell-aware
fixture. -/
theorem cell_liftFrame_congr_read_rootNoop
    (hmem : mem.borrows =
      freezeTreeBorrowsOnReadAtProj cellBorrows cellBorrows 0 none [] 0 0
        [8] 0)
    (h : LiftFrame body bbIdx stmtIdx env
      { mem with
        borrows :=
          BorrowForest.toList
            (cellForestOf .frozen (.reservedFrz false) .frozen .frozen
              none) }
      post fuel) :
    LiftFrame body bbIdx stmtIdx env mem post fuel :=
  LiftFrame_congr_pruned_borrows_read_rootNoop cell_sameAlloc
    cell_rootNoop.2 0 none [] 0 0 0 hmem h

end LiftFrameCongruence

/-! ### Tightness: `.frozen` root with a live child

Each counterexample of the module is restated on its witness, and paired
with a positive twin on which the invariant holds and the pruned traversal
agrees with the trusted scan.
-/

/-- The two-node witness forest satisfies the foreign-read no-op invariant
exactly when its child is not `.unique`. -/
theorem cexForestOf_readNoop_iff (p : TreeBorrowPerm) :
    ForeignReadNoopForest [] (cexForestOf p) ↔ p ≠ .unique := by
  cases p with
  | reservedFrz c => cases c <;> decide +kernel
  | _ => decide +kernel

/-- Negative: under a `.frozen` root with a `.unique` child the pruned read
skips the child, which the trusted scan freezes. The decision procedure of
this file and the module's proof agree that the invariant fails. -/
theorem cex_frozen_root_unique_child_diverges :
    SameAllocForest (cexBorrows .unique) (cexForestOf .unique) ∧
    ¬ ForeignReadNoopForest [] (cexForestOf .unique) ∧
    summary (pruneForeignRead (cexBorrows .unique) (cexForestOf .unique) 0
      none []) = [(1, .frozen), (2, .unique)] ∧
    (freezeTreeBorrowsOnReadAtProj (cexBorrows .unique) (cexBorrows .unique)
        0 none []).map (fun e => (e.tag, e.perm)) =
      [(1, .frozen), (2, .frozen)] ∧
    BorrowForest.toList
        (pruneForeignRead (cexBorrows .unique) (cexForestOf .unique) 0 none
          []) ≠
      freezeTreeBorrowsOnReadAtProj (cexBorrows .unique)
        (BorrowForest.toList (cexForestOf .unique)) 0 none [] :=
  have h := naive_frozen_root_without_subtree_inv_counterexample
  ⟨h.1, cexForestOf_unique_not_readNoop, rfl, rfl, h.2.2.2.2⟩

/-- The two proofs that the witness violates the invariant coincide with
the characterisation above. -/
theorem cex_frozen_root_unique_child_not_readNoop :
    ¬ ForeignReadNoopForest [] (cexForestOf .unique) :=
  fun h => (cexForestOf_readNoop_iff .unique).mp h rfl

/-- Positive twin: for every child permission other than `.unique` the
witness satisfies the invariant, and the pruned read is the trusted scan of
the witness table. -/
theorem cex_frozen_root_other_child_agrees (p : TreeBorrowPerm)
    (hp : p ≠ .unique) :
    BorrowForest.toList
        (pruneForeignRead (cexBorrows p) (cexForestOf p) 0 none [] 0 0 [] 0) =
      freezeTreeBorrowsOnReadAtProj (cexBorrows p) (cexBorrows p) 0 none []
        0 0 [] 0 :=
  (pruneForeignRead_equiv_fullScan (cexForestOf_sameAlloc p)
    ((cexForestOf_readNoop_iff p).mpr hp) 0 none [] 0 0 0).trans
    (congrArg
      (fun bs =>
        freezeTreeBorrowsOnReadAtProj (cexBorrows p) bs 0 none [] 0 0 [] 0)
      (cexForestOf_toList p))

/-- Positive twin on the `.frozen` child: the pruned read agrees with the
trusted scan and returns the forest unchanged, and so does the trusted
scan of the table. -/
theorem cex_frozen_root_frozen_child_agrees :
    BorrowForest.toList
        (pruneForeignRead (cexBorrows .frozen) (cexForestOf .frozen) 0 none
          []) =
      freezeTreeBorrowsOnReadAtProj (cexBorrows .frozen)
        (BorrowForest.toList (cexForestOf .frozen)) 0 none [] ∧
    pruneForeignRead (cexBorrows .frozen) (cexForestOf .frozen) 0 none [] =
      cexForestOf .frozen ∧
    ForeignReadNoopForest [] (cexForestOf .frozen) ∧
    freezeTreeBorrowsOnReadAtProj (cexBorrows .frozen) (cexBorrows .frozen)
      0 none [] = cexBorrows .frozen :=
  ⟨pruneForeignRead_frozen_subtree_agrees.1,
    pruneForeignRead_frozen_subtree_agrees.2, cexForestOf_frozen_readNoop,
    rfl⟩

/-! ### Tightness: the read-UB skip needs the foreignness test -/

/-- Negative: on the `.disabled`-child witness a read through the child is
undefined behavior, and a skip on the root permission alone misses it. -/
theorem cex_readUB_naive_skip_misses :
    pruneAnyForest (readSkipRoot [] 0 0)
      (fun e =>
        borrowEntryReadUB (cexBorrows .disabled) [] e 0 (some 2) [] 0 0 0)
      (cexForestOf .disabled) = false ∧
    hasTreeReadUB (cexBorrows .disabled)
      (BorrowForest.toList (cexForestOf .disabled)) [] 0 (some 2) [] 0 0 0 =
      true :=
  have h := naive_readUB_skip_without_foreign_check_counterexample
  ⟨h.2.2.1, h.2.2.2.1⟩

/-- Positive twin: the pruned test with the foreignness check agrees with
the trusted scan on the same witness and access, by the equivalence theorem
applied to the invariants established by the counterexample itself; and for
a direct read both the skip on the permission alone and the trusted scan
report no fault. -/
theorem cex_readUB_foreign_check_agrees :
    pruneHasTreeReadUB (cexBorrows .disabled) (cexForestOf .disabled) [] 0
        (some 2) [] 0 0 0 =
      hasTreeReadUB (cexBorrows .disabled)
        (BorrowForest.toList (cexForestOf .disabled)) [] 0 (some 2) [] 0 0
        0 ∧
    pruneHasTreeReadUB (cexBorrows .disabled) (cexForestOf .disabled) [] 0
      (some 2) [] 0 0 0 = true ∧
    pruneAnyForest (readSkipRoot [] 0 0)
      (fun e => borrowEntryReadUB (cexBorrows .disabled) [] e 0 none [] 0 0 0)
      (cexForestOf .disabled) = false ∧
    hasTreeReadUB (cexBorrows .disabled) (cexBorrows .disabled) [] 0 none []
      0 0 0 = false :=
  have h := naive_readUB_skip_without_foreign_check_counterexample
  ⟨pruneHasTreeReadUB_equiv_fullScan h.1 h.2.1 0 (some 2) [] 0 0 0,
    h.2.2.2.2, rfl, rfl⟩

/-! ### Tightness: `.cell` root with a live child -/

/-- Negative: a `.cell` root with a `.unique` child violates
`ForeignWriteNoopForest`, and the permission-aware write misses the child
that the trusted scan disables. -/
theorem cex_cell_root_unique_child_diverges :
    ¬ ForeignWriteNoopForest [] cexCellUniqueForest ∧
    summary (pruneForeignWrite cexCellUniqueBorrows cexCellUniqueForest 0
      none []) = [(1, .cell), (2, .unique)] ∧
    (invalidateTreeBorrowsAtProj cexCellUniqueBorrows cexCellUniqueBorrows 0
        none []).map (fun e => (e.tag, e.perm)) =
      [(1, .cell), (2, .disabled)] :=
  ⟨cell_root_unique_child_breaks_foreignWriteNoop.1, rfl, rfl⟩

/-- The module's permission lists for the same witness. -/
theorem cex_cell_root_unique_child_perms :
    (BorrowForest.toList
        (pruneForeignWrite cexCellUniqueBorrows cexCellUniqueForest 0 none
          [])).map BorrowEntry.perm = [.cell, .unique] ∧
    (invalidateTreeBorrowsAtProj cexCellUniqueBorrows
        (BorrowForest.toList cexCellUniqueForest) 0 none []).map
        BorrowEntry.perm = [.cell, .disabled] :=
  cell_root_unique_child_breaks_foreignWriteNoop.2

/-- Positive twin on the same forest: the `.disabled`-root write agrees
with the trusted scan and disables the child. -/
theorem cex_cell_root_unique_child_disabledVariant_agrees :
    BorrowForest.toList
        (pruneForeignWriteDisabled cexCellUniqueBorrows cexCellUniqueForest
          0 none []) =
      invalidateTreeBorrowsAtProj cexCellUniqueBorrows
        (BorrowForest.toList cexCellUniqueForest) 0 none [] ∧
    summary (pruneForeignWriteDisabled cexCellUniqueBorrows
      cexCellUniqueForest 0 none []) = [(1, .cell), (2, .disabled)] ∧
    BorrowForest.toList
        (pruneForeignWriteSimpleDisabled cexCellUniqueBorrows
          cexCellUniqueForest 0 none) =
      invalidateConflictingBorrows
        (BorrowForest.toList cexCellUniqueForest) 0 none :=
  have h := cexCellUniqueForest_pruneForeignWriteDisabled_agrees
  ⟨h.2.2, rfl,
    pruneForeignWriteSimpleDisabled_equiv_fullScan h.1 h.2.1 0 none 0⟩

/-- A `.cell` root with a `.cell` child. -/
def cellCellForest : BorrowForest :=
  [.node cexCellRoot [.node (cexChild .cell) []]]

/-- Positive twin with an invariant-respecting child: under a `.cell` root
with a `.cell` child the permission-aware write agrees with the trusted
scan and changes nothing. -/
theorem cex_cell_root_cell_child_agrees :
    ForeignWriteNoopForest [] cellCellForest ∧
    BorrowForest.toList
        (pruneForeignWrite (BorrowForest.toList cellCellForest)
          cellCellForest 0 none [] 0 0 0 []) =
      invalidateTreeBorrowsAtProj (BorrowForest.toList cellCellForest)
        (BorrowForest.toList cellCellForest) 0 none [] 0 0 0 ∧
    pruneForeignWrite (BorrowForest.toList cellCellForest) cellCellForest 0
      none [] 0 0 0 [] = cellCellForest := by
  have hA :
      SameAllocForest (BorrowForest.toList cellCellForest) cellCellForest :=
    by decide +kernel
  have hN : ForeignWriteNoopForest [] cellCellForest := by decide +kernel
  exact ⟨hN, pruneForeignWrite_equiv_fullScan hA hN 0 none [] 0 0 0, rfl⟩

/-! ### Tightness: live root with a `.cell` child -/

/-- Negative: the closure invariants hold on the witness, yet a direct
write breaks `.disabled`-closure and a direct read breaks `.frozen`-closure,
because the `.cell` child survives under the changed root. -/
theorem cex_unique_root_cell_child_breaks_closure :
    DisabledClosedForest cexUniqueCellForest ∧
    FrozenClosedForest cexUniqueCellForest ∧
    summary (pruneForeignWriteDisabled cexUniqueCellBorrows
      cexUniqueCellForest 0 none [] 0 0 0) = [(1, .disabled), (2, .cell)] ∧
    ¬ DisabledClosedForest
        (pruneForeignWriteDisabled cexUniqueCellBorrows cexUniqueCellForest
          0 none [] 0 0 0) ∧
    summary (pruneForeignReadFrozenOrDisabled cexUniqueCellBorrows
      cexUniqueCellForest 0 none [] 0 0 [] 0) = [(1, .frozen), (2, .cell)] ∧
    ¬ FrozenClosedForest
        (pruneForeignReadFrozenOrDisabled cexUniqueCellBorrows
          cexUniqueCellForest 0 none [] 0 0 [] 0) :=
  have h := unique_root_cell_child_breaks_disabledClosed_and_frozenClosed
  ⟨h.1, h.2.1, rfl, h.2.2.1, rfl, h.2.2.2.1⟩

/-- Positive twin: the root no-op invariants hold on the same witness and
survive both accesses. The post-access facts are obtained twice: from the
module's worked instance, and from the general preservation theorems. -/
theorem cex_unique_root_cell_child_rootNoop_preserved :
    DisabledRootWriteNoopForest []
      (pruneForeignWriteDisabled cexUniqueCellBorrows cexUniqueCellForest 0
        none [] 0 0 0) ∧
    FrozenOrDisabledRootReadNoopForest []
      (pruneForeignWriteDisabled cexUniqueCellBorrows cexUniqueCellForest 0
        none [] 0 0 0) ∧
    DisabledRootWriteNoopForest []
      (pruneForeignReadFrozenOrDisabled cexUniqueCellBorrows
        cexUniqueCellForest 0 none [] 0 0 [] 0) ∧
    FrozenOrDisabledRootReadNoopForest []
      (pruneForeignReadFrozenOrDisabled cexUniqueCellBorrows
        cexUniqueCellForest 0 none [] 0 0 [] 0) :=
  have h := cexUniqueCellForest_preserves_rootNoop_invariants
  have hProj :
      ∀ e, e ∈ BorrowForest.toList cexUniqueCellForest →
        e.targetProjection = [] := by decide +kernel
  ⟨pruneForeignWriteDisabled_preserves_disabledRootWriteNoop_direct h.1
      h.2.1 0 0 hProj rfl,
    h.2.2.2.2.1,
    pruneForeignReadFrozenOrDisabled_preserves_disabledRootWriteNoop
      (allBorrows := cexUniqueCellBorrows) h.2.1 0 none [] 0 0 0 rfl,
    h.2.2.2.2.2.2⟩

/-- After the direct write, the preserved root no-op invariants still give
exact agreement with the trusted scans, which the broken closure invariant
could not: a read through the surviving `.cell` child is undefined
behavior below its `.disabled` parent, and a second direct write changes
nothing. -/
theorem cex_unique_root_cell_child_second_access :
    pruneHasTreeReadUBFrozenOrDisabled
        (invalidateTreeBorrowsAtProj cexUniqueCellBorrows
          cexUniqueCellBorrows 0 none [] 0 0 0)
        (pruneForeignWriteDisabled cexUniqueCellBorrows cexUniqueCellForest
          0 none [] 0 0 0) [] 0 (some 2) [] 0 0 0 =
      hasTreeReadUB
        (invalidateTreeBorrowsAtProj cexUniqueCellBorrows
          cexUniqueCellBorrows 0 none [] 0 0 0)
        (BorrowForest.toList
          (pruneForeignWriteDisabled cexUniqueCellBorrows
            cexUniqueCellForest 0 none [] 0 0 0)) [] 0 (some 2) [] 0 0 0 ∧
    pruneHasTreeReadUBFrozenOrDisabled
      (invalidateTreeBorrowsAtProj cexUniqueCellBorrows cexUniqueCellBorrows
        0 none [] 0 0 0)
      (pruneForeignWriteDisabled cexUniqueCellBorrows cexUniqueCellForest 0
        none [] 0 0 0) [] 0 (some 2) [] 0 0 0 = true ∧
    summary
      (pruneForeignWriteDisabled
        (invalidateTreeBorrowsAtProj cexUniqueCellBorrows
          cexUniqueCellBorrows 0 none [] 0 0 0)
        (pruneForeignWriteDisabled cexUniqueCellBorrows cexUniqueCellForest
          0 none [] 0 0 0) 0 none [] 0 0 0) =
      [(1, .disabled), (2, .cell)] :=
  have h := cexUniqueCellForest_preserves_rootNoop_invariants
  ⟨pruneHasTreeReadUBFrozenOrDisabled_rootNoop_equiv_fullScan
      (pruneForeignWriteDisabled_preserves_sameAlloc h.1 0 none [] 0 0 0)
      h.2.2.2.2.1 0 (some 2) [] 0 0 0, rfl, rfl⟩

/-! ### Tightness: reads of one field break the read invariant -/

/-- Negative: a read of field `0` freezes the whole-allocation root and
leaves its `.unique` child on the disjoint field `1` alone, so the
foreign-read no-op invariant is lost. Only the whole-allocation hypothesis
of the preservation theorem fails on this witness. -/
theorem cex_field_read_breaks_readNoop :
    ForeignReadNoopForest [] cexPartialProjForest ∧
    summary (pruneForeignRead cexPartialProjBorrows cexPartialProjForest 0
      none [.field 0 cexUnitTy]) = [(1, .frozen), (2, .unique)] ∧
    ¬ ForeignReadNoopForest []
        (pruneForeignRead cexPartialProjBorrows cexPartialProjForest 0 none
          [.field 0 cexUnitTy]) ∧
    SameAllocForest cexPartialProjBorrows cexPartialProjForest ∧
    ¬ (∀ e, e ∈ BorrowForest.toList cexPartialProjForest →
        e.targetProjection = []) := by
  have h := partial_proj_read_breaks_foreignReadNoop
  exact ⟨h.1, rfl, h.2, by decide +kernel, by decide +kernel⟩

/-- Positive twin on the same forest: a read of the whole allocation
freezes root and child together, and the invariant survives. -/
theorem cex_field_forest_wholeAlloc_read_keeps_readNoop :
    summary (pruneForeignRead cexPartialProjBorrows cexPartialProjForest 0
      none []) = [(1, .frozen), (2, .frozen)] ∧
    ForeignReadNoopForest []
      (pruneForeignRead cexPartialProjBorrows cexPartialProjForest 0 none
        []) := by
  refine ⟨rfl, ?_⟩
  decide +kernel

/-- The witness with the child moved to the whole allocation. -/
def wholeAllocTwinForest : BorrowForest :=
  [.node cexUniqueRoot [.node (cexChild .unique) []]]

/-- Positive twin by theorem: once every borrow targets the whole
allocation, the preservation theorem applies and the invariant survives the
read, which freezes both borrows. -/
theorem cex_field_wholeAlloc_twin_preserved :
    ForeignReadNoopForest []
      (pruneForeignRead (BorrowForest.toList wholeAllocTwinForest)
        wholeAllocTwinForest 0 none [] 0 0 [] 0) ∧
    summary
      (pruneForeignRead (BorrowForest.toList wholeAllocTwinForest)
        wholeAllocTwinForest 0 none [] 0 0 [] 0) =
      [(1, .frozen), (2, .frozen)] := by
  have hA :
      SameAllocForest (BorrowForest.toList wholeAllocTwinForest)
        wholeAllocTwinForest := by decide +kernel
  have hN : ForeignReadNoopForest [] wholeAllocTwinForest := by
    decide +kernel
  have hP :
      ∀ e, e ∈ BorrowForest.toList wholeAllocTwinForest →
        e.targetProjection = [] := by decide +kernel
  exact ⟨pruneForeignRead_preserves_foreignReadNoop_wholeAlloc hA hN 0 none
    0 hP rfl, rfl⟩

/-! ### Tightness: protector attachment below a `.disabled` root -/

/-- A `.disabled` root of `_0` with one child of permission `p`. -/
def disabledRootForest (p : TreeBorrowPerm) : BorrowForest :=
  [.node (mkEntry 1 0 .disabled) [.node (mkEntry 2 0 p (some 1)) []]]

/-- Negative: with a `.reservedIM` child the root no-op write invariant
holds before and after pushing the fresh protector `10`, and attaching the
protector to the child breaks it. Only the `.reservedIM` hypothesis of the
preservation theorem fails. -/
theorem cex_attach_reservedIM_child_breaks :
    DisabledRootWriteNoopForest [] (disabledRootForest .reservedIM) ∧
    DisabledRootWriteNoopForest [10] (disabledRootForest .reservedIM) ∧
    ¬ DisabledRootWriteNoopForest [10]
        (pruneAttachBorrowProtector
          (BorrowForest.toList (disabledRootForest .reservedIM))
          (disabledRootForest .reservedIM) 2 10) ∧
    ¬ (∀ e, e ∈ BorrowForest.toList (disabledRootForest .reservedIM) →
        e.tag = 2 → e.perm ≠ .reservedIM) := by
  have h := attachBorrowProtector_reservedIM_child_breaks_disabledRootWriteNoop
  exact ⟨h.1, h.2.1, h.2.2, by decide +kernel⟩

/-- Positive twin: with a `.cell` child every hypothesis of the
preservation theorem holds, and the invariant survives the attachment. -/
theorem cex_attach_cell_child_preserved :
    DisabledRootWriteNoopForest [10]
      (pruneAttachBorrowProtector
        (BorrowForest.toList (disabledRootForest .cell))
        (disabledRootForest .cell) 2 10) ∧
    (BorrowForest.toList
        (pruneAttachBorrowProtector
          (BorrowForest.toList (disabledRootForest .cell))
          (disabledRootForest .cell) 2 10)).map BorrowEntry.protector =
      [none, some 10] := by
  have hA :
      SameAllocForest (BorrowForest.toList (disabledRootForest .cell))
        (disabledRootForest .cell) := by decide +kernel
  have hW : DisabledRootWriteNoopForest [] (disabledRootForest .cell) := by
    decide +kernel
  exact ⟨pruneAttachBorrowProtector_preserves_disabledRootWriteNoop hA hW 2
    10 (by decide +kernel) (by decide +kernel), rfl⟩

/-- A `.frozen` root of `_0` with one child of permission `p`. -/
def frozenRootForest (p : TreeBorrowPerm) : BorrowForest :=
  [.node (mkEntry 1 0 .frozen) [.node (mkEntry 2 0 p (some 1)) []]]

/-- Tightness of the reservation hypothesis of the read-invariant
attachment theorem: an unconflicted reservation child is a read no-op while
unprotected, and stops being one when protector `10` is attached to it. -/
theorem attach_reservation_child_breaks_readRootNoop :
    FrozenOrDisabledRootReadNoopForest []
      (frozenRootForest (.reservedFrz false)) ∧
    ¬ FrozenOrDisabledRootReadNoopForest [10]
        (pruneAttachBorrowProtector
          (BorrowForest.toList (frozenRootForest (.reservedFrz false)))
          (frozenRootForest (.reservedFrz false)) 2 10) := by
  decide +kernel

/-- Positive twin: a conflicted reservation child satisfies the hypothesis,
and the read invariant survives the attachment. -/
theorem attach_conflicted_reservation_child_preserved :
    FrozenOrDisabledRootReadNoopForest [10]
      (pruneAttachBorrowProtector
        (BorrowForest.toList (frozenRootForest (.reservedFrz true)))
        (frozenRootForest (.reservedFrz true)) 2 10) := by
  have hA :
      SameAllocForest
        (BorrowForest.toList (frozenRootForest (.reservedFrz true)))
        (frozenRootForest (.reservedFrz true)) := by decide +kernel
  have hR :
      FrozenOrDisabledRootReadNoopForest []
        (frozenRootForest (.reservedFrz true)) := by decide +kernel
  exact pruneAttachBorrowProtector_preserves_frozenOrDisabledRootReadNoop hA
    hR 2 10 (by decide +kernel) (by decide +kernel)

/-! ### Tightness: structural well-formedness cannot be dropped -/

/-- A root of local `_5` whose child targets local `loc`. -/
def mixedAllocForest (loc : Local) : BorrowForest :=
  [.node (mkEntry 1 5 .unique) [.node (mkEntry 2 loc .unique (some 1)) []]]

/-- Negative: when the child of an unrelated root targets the written local
`_0`, the forest is not `SameAllocForest`; the pruned write skips the
subtree at its root and misses the child that the trusted scan disables,
although the foreign-write no-op invariant holds. -/
theorem mixed_alloc_subtree_diverges :
    ¬ SameAllocForest (BorrowForest.toList (mixedAllocForest 0))
        (mixedAllocForest 0) ∧
    ForeignWriteNoopForest [] (mixedAllocForest 0) ∧
    summary (pruneForeignWrite (BorrowForest.toList (mixedAllocForest 0))
      (mixedAllocForest 0) 0 none [] 0 0 0 []) =
      [(1, .unique), (2, .unique)] ∧
    (invalidateTreeBorrowsAtProj (BorrowForest.toList (mixedAllocForest 0))
        (BorrowForest.toList (mixedAllocForest 0)) 0 none [] 0 0 0).map
        (fun e => (e.tag, e.perm)) = [(1, .unique), (2, .disabled)] := by
  refine ⟨?_, ?_, rfl, rfl⟩ <;> decide +kernel

/-- Positive twin: when the child targets the same local `_5` as its root,
the forest is well formed and the pruned write is the trusted scan. -/
theorem same_alloc_subtree_agrees :
    BorrowForest.toList
        (pruneForeignWrite (BorrowForest.toList (mixedAllocForest 5))
          (mixedAllocForest 5) 0 none [] 0 0 0 []) =
      invalidateTreeBorrowsAtProj (BorrowForest.toList (mixedAllocForest 5))
        (BorrowForest.toList (mixedAllocForest 5)) 0 none [] 0 0 0 := by
  have hA :
      SameAllocForest (BorrowForest.toList (mixedAllocForest 5))
        (mixedAllocForest 5) := by decide +kernel
  have hN : ForeignWriteNoopForest [] (mixedAllocForest 5) := by
    decide +kernel
  exact pruneForeignWrite_equiv_fullScan hA hN 0 none [] 0 0 0

/-! ### Shape of the representation

Characterisations of the forest representation and of the generic pruned
traversals in terms of list operations, each obtained from one unfolding
step of the corresponding definition.
-/

/-- A subtree flattens to its root followed by its children's tables. -/
theorem toList_eq_root_cons (t : BorrowSubtree) :
    t.toList = t.root :: BorrowForest.toList t.children := by
  rw [BorrowSubtree.toList.eq_def]
  cases t
  rfl

/-- A forest flattens to the concatenation of its subtrees' tables. -/
theorem forest_toList_eq_flatMap (ts : List BorrowSubtree) :
    BorrowForest.toList ts = ts.flatMap BorrowSubtree.toList := by
  induction ts with
  | nil => rw [BorrowForest.toList.eq_def]; rfl
  | cons t ts ih =>
    rw [BorrowForest.toList.eq_def, List.flatMap_cons, ← ih]

/-- Every subtree contains the tag of its root. -/
theorem containsTag_root (t : BorrowSubtree) :
    t.containsTag t.root.tag = true := by
  rw [BorrowSubtree.containsTag.eq_def]
  cases t
  simp only [BorrowSubtree.root, Nat.beq_refl, Bool.true_or]

/-- A forest contains a tag exactly when one of its subtrees does. -/
theorem forest_containsTag_eq_any (ts : List BorrowSubtree) (tag : Nat) :
    BorrowForest.containsTag ts tag =
      ts.any (fun t => t.containsTag tag) := by
  induction ts with
  | nil => rw [BorrowForest.containsTag.eq_def]; rfl
  | cons t ts ih =>
    rw [BorrowForest.containsTag.eq_def, List.any_cons, ← ih]

/-- A node invariant holds on a subtree exactly when it holds at the root
and on the forest of children. -/
theorem allSubtrees_iff_root (P : BorrowEntry → List BorrowSubtree → Prop)
    (t : BorrowSubtree) :
    AllSubtrees P t ↔
      P t.root t.children ∧ AllSubtreesForest P t.children := by
  rw [AllSubtrees.eq_def]
  cases t
  exact Iff.rfl

/-- A node invariant holds on a forest exactly when it holds on each of
its subtrees. -/
theorem allSubtreesForest_iff_forall
    (P : BorrowEntry → List BorrowSubtree → Prop) (ts : List BorrowSubtree) :
    AllSubtreesForest P ts ↔ ∀ t, t ∈ ts → AllSubtrees P t := by
  induction ts with
  | nil =>
    rw [AllSubtreesForest.eq_def]
    exact ⟨fun _ _ h => (nomatch h), fun _ => True.intro⟩
  | cons t ts ih =>
    rw [AllSubtreesForest.eq_def]
    exact ⟨fun h u hu => by
        cases hu with
        | head => exact h.1
        | tail _ hm => exact ih.mp h.2 u hm,
      fun h => ⟨h t (List.mem_cons_self ..),
        ih.mpr (fun u hu => h u (List.mem_cons_of_mem _ hu))⟩⟩

/-- The pruned map of a forest maps the pruned subtree map over it. -/
theorem pruneMapForest_eq_map (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) (ts : List BorrowSubtree) :
    pruneMapForest skip upd ts = ts.map (pruneMapSubtree skip upd) := by
  induction ts with
  | nil => rw [pruneMapForest.eq_def]; rfl
  | cons t ts ih => rw [pruneMapForest.eq_def, List.map_cons, ← ih]

/-- The root of a pruned subtree is the old root when skipped and the
updated root otherwise. -/
theorem pruneMapSubtree_root (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) (t : BorrowSubtree) :
    (pruneMapSubtree skip upd t).root =
      bif skip t.root then t.root else upd t.root := by
  rw [pruneMapSubtree.eq_def]
  cases t with
  | node root children =>
    simp only [BorrowSubtree.root]
    cases skip root <;> rfl

/-- The pruned test of a forest is the disjunction of the pruned subtree
tests. -/
theorem pruneAnyForest_eq_any_subtrees (skip test : BorrowEntry → Bool)
    (ts : List BorrowSubtree) :
    pruneAnyForest skip test ts = ts.any (pruneAnySubtree skip test) := by
  induction ts with
  | nil => rw [pruneAnyForest.eq_def]; rfl
  | cons t ts ih =>
    rw [pruneAnyForest.eq_def]
    show (match pruneAnySubtree skip test t with
      | true => true
      | false => pruneAnyForest skip test ts) = _
    rw [List.any_cons, ← ih]
    cases pruneAnySubtree skip test t <;> rfl

/-- The pruned test of a subtree: not skipped, and the test holds at the
root or in the children. -/
theorem pruneAnySubtree_eq_guard (skip test : BorrowEntry → Bool)
    (t : BorrowSubtree) :
    pruneAnySubtree skip test t =
      (!skip t.root &&
        (test t.root || pruneAnyForest skip test t.children)) := by
  rw [pruneAnySubtree.eq_def]
  cases t with
  | node root children =>
    simp only [BorrowSubtree.root, BorrowSubtree.children]
    cases skip root <;> cases test root <;> rfl

/-- A child subtree is strictly smaller than its parent, so the pruned
traversals terminate structurally. -/
theorem child_sizeOf_lt (r : BorrowEntry) (c : BorrowSubtree)
    (cs : List BorrowSubtree) :
    sizeOf c < sizeOf (BorrowSubtree.node r (c :: cs)) := by
  rw [BorrowSubtree.node.sizeOf_spec, List.cons.sizeOf_spec]
  omega

/-- Two nodes are equal exactly when their roots and children are. -/
theorem node_eq_iff (r r' : BorrowEntry) (c c' : List BorrowSubtree) :
    BorrowSubtree.node r c = BorrowSubtree.node r' c' ↔ r = r' ∧ c = c' := by
  rw [BorrowSubtree.node.injEq]

/-- The live subtree of the main fixture determines its three permission
parameters, so the explicit result forests of this file are discriminating:
different permissions give different forests. -/
theorem fxLiveTree_injective {a b c a' b' c' : TreeBorrowPerm}
    (h : fxLiveTree a b c = fxLiveTree a' b' c') :
    a = a' ∧ b = b' ∧ c = c' := by
  have h₁ := BorrowSubtree.node.inj h
  have h₂ := BorrowSubtree.node.inj (List.cons.inj h₁.2).1
  have h₃ := BorrowSubtree.node.inj (List.cons.inj h₂.2).1
  exact ⟨congrArg BorrowEntry.perm h₁.1, congrArg BorrowEntry.perm h₂.1,
    congrArg BorrowEntry.perm h₃.1⟩

/-- The direct read really changes the live subtree. -/
theorem fxLiveTree_read_changes :
    fxLiveTree .frozen (.reservedFrz true) .reservedIM ≠
      fxLiveTree .unique (.reservedFrz false) .reservedIM :=
  fun h => absurd (fxLiveTree_injective h).1 (by decide)

mutual
/-- Height of a subtree: a leaf has height `1`. -/
noncomputable def subtreeHeight : BorrowSubtree → Nat
  | .node _ children => forestHeight children + 1
/-- Height of a forest: the maximum height of its subtrees. -/
noncomputable def forestHeight : List BorrowSubtree → Nat
  | [] => 0
  | t :: ts => max (subtreeHeight t) (forestHeight ts)
end

/-- The fixtures are multi-root and of depth three. -/
theorem fixture_shapes :
    fxForest.length = 6 ∧ forestHeight fxForest = 3 ∧
    fxBorrows.length = 17 ∧
    cellForest.length = 5 ∧ forestHeight cellForest = 3 ∧
    cellBorrows.length = 15 ∧
    projForest.length = 3 ∧ forestHeight projForest = 3 ∧
    projBorrows.length = 7 := by
  decide +kernel

mutual
/-- A pruned map never changes the shape of a subtree. -/
theorem pruneMapSubtree_height (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) :
    ∀ t : BorrowSubtree,
      subtreeHeight (pruneMapSubtree skip upd t) = subtreeHeight t
  | .node root children => by
    cases hs : skip root with
    | true => rw [pruneMapSubtree_skip children hs]
    | false =>
      rw [pruneMapSubtree_visit children hs, subtreeHeight, subtreeHeight,
        pruneMapForest_height skip upd children]
/-- A pruned map never changes the shape of a forest. -/
theorem pruneMapForest_height (skip : BorrowEntry → Bool)
    (upd : BorrowEntry → BorrowEntry) :
    ∀ ts : List BorrowSubtree,
      forestHeight (pruneMapForest skip upd ts) = forestHeight ts
  | [] => by rw [pruneMapForest_nil]
  | t :: ts => by
    rw [pruneMapForest_cons, forestHeight, forestHeight,
      pruneMapSubtree_height skip upd t, pruneMapForest_height skip upd ts]
end

/-! ### Subtree-level theorems on the live subtree -/

instance {P : BorrowEntry → List BorrowSubtree → Prop}
    [d : ∀ r c, Decidable (P r c)] (t : BorrowSubtree) :
    Decidable (AllSubtrees P t) :=
  decAllSubtrees d t

/-- Subtree form of `sameAllocForest_iff_cert`, by
`AllSubtrees.mono_strong` in both directions. -/
theorem sameAllocSubtree_iff_cert {bs : List BorrowEntry}
    {t : BorrowSubtree} :
    SameAllocSubtree bs t ↔ AllSubtrees (SameAllocCertNode bs) t :=
  ⟨AllSubtrees.mono_strong
      (fun _ _ hn => cert_of_sameAllocNode (AllSubtrees.node_iff.mp hn).1) t,
    AllSubtrees.mono_strong
      (fun _ _ hn => sameAllocNode_of_cert (AllSubtrees.node_iff.mp hn).1)
      t⟩

instance (bs : List BorrowEntry) (t : BorrowSubtree) :
    Decidable (SameAllocSubtree bs t) :=
  decidable_of_iff _ sameAllocSubtree_iff_cert.symm

instance (ps : List Nat) (t : BorrowSubtree) :
    Decidable (ForeignReadNoopSubtree ps t) :=
  inferInstanceAs (Decidable (AllSubtrees _ t))

/-- The live subtree of the main fixture. -/
def liveTree : BorrowSubtree :=
  fxLiveTree .unique (.reservedFrz false) .reservedIM

/-- Read update of one entry for a direct read of `_0` under `ps`. -/
def readUpd (ps : List Nat) (e : BorrowEntry) : BorrowEntry :=
  updateBorrowPermOnReadAtProj fxBorrows e 0 none [] 0 0 ps 0

/-- The live subtree is well formed against the fixture table and satisfies
the foreign-read no-op invariant. -/
theorem liveTree_invariants :
    SameAllocSubtree fxBorrows liveTree ∧
    ForeignReadNoopSubtree [6] liveTree ∧
    ForeignReadNoopSubtree [3, 6] liveTree := by
  decide +kernel

/-- The two subtree invariants combine into the conjunction that the skip
soundness lemmas consume, and split again. -/
theorem liveTree_combined :
    AllSubtrees
      (fun r c =>
        SameAllocNode fxBorrows r c ∧ ForeignReadNoopNode [6] r c)
      liveTree ∧
    AllSubtrees (ForeignReadNoopNode [6]) liveTree :=
  have h := AllSubtrees.and liveTree liveTree_invariants.1
    liveTree_invariants.2.1
  ⟨h, AllSubtrees.and_right h⟩

/-- The pruned read of the single live subtree flattens to the map of the
entry update over its table, and is the explicit read result. -/
theorem liveTree_read :
    (pruneMapSubtree (readSkipRoot [6] 0 0) (readUpd [6]) liveTree).toList =
      liveTree.toList.map (readUpd [6]) ∧
    pruneMapSubtree (readSkipRoot [6] 0 0) (readUpd [6]) liveTree =
      fxLiveTree .frozen (.reservedFrz true) .reservedIM :=
  ⟨pruneMapSubtree_toList liveTree
      (AllSubtrees.mono_strong
        (fun _ _ h =>
          readSkip_sound (targetLocal := 0) (readerTag := none)
            (readProj := []) (readRangeOff := 0) (readRangeLen := 0)
            (targetFrameDepth := 0) h)
        liveTree liveTree_combined.1),
    rfl⟩

/-- The pruned read-UB test of the single live subtree is the trusted
per-entry test over its table, and reports the fault once protector `3` is
active. -/
theorem liveTree_readUB :
    pruneAnySubtree (readUBSkipRoot fxBorrows [3, 6] 0 none 0)
        (fun e => borrowEntryReadUB fxBorrows [3, 6] e 0 none [] 0 0 0)
        liveTree =
      liveTree.toList.any
        (fun e => borrowEntryReadUB fxBorrows [3, 6] e 0 none [] 0 0 0) ∧
    pruneAnySubtree (readUBSkipRoot fxBorrows [3, 6] 0 none 0)
      (fun e => borrowEntryReadUB fxBorrows [3, 6] e 0 none [] 0 0 0)
      liveTree = true :=
  ⟨pruneAnySubtree_eq_any liveTree
      (AllSubtrees.mono_strong (fun _ _ h => readUBSkip_sound h) liveTree
        (AllSubtrees.and liveTree liveTree_invariants.1
          liveTree_invariants.2.2)),
    rfl⟩

/-- The foreign-read no-op invariant of the single live subtree survives
the direct read, by the subtree preservation theorem. -/
theorem liveTree_read_preserves_readNoop :
    ForeignReadNoopSubtree [6]
      (pruneMapSubtree (readSkipRoot [6] 0 0) (readUpd [6]) liveTree) :=
  pruneForeignRead_preserves_foreignReadNoop_subtree
    (allBorrows := fxBorrows) (activeProtectors := [6]) (targetLocal := 0)
    (readerTag := none) (targetFrameDepth := 0) liveTree
    liveTree_invariants.1 liveTree_combined.2 (by decide +kernel)
    (by decide +kernel)

/-- A pruned read never changes which tags a subtree contains. -/
theorem read_preserves_containsTag (bs : List BorrowEntry)
    (t : BorrowSubtree) (tag : Nat) (readerTag : Option Nat)
    (ps : List Nat) :
    (pruneMapSubtree (readSkipRoot ps 0 0)
        (fun e =>
          updateBorrowPermOnReadAtProj bs e 0 readerTag [] 0 0 ps 0)
        t).containsTag tag = t.containsTag tag :=
  pruneMapSubtree_containsTag
    (fun e => updateBorrowPermOnReadAtProj_tag bs e 0 readerTag [] 0 0 ps 0)
    tag t

/-- A pruned read never changes the parent pointers of a subtree. -/
theorem read_preserves_parents (bs : List BorrowEntry) (t : BorrowSubtree)
    (readerTag : Option Nat) (ps : List Nat) :
    (pruneMapSubtree (readSkipRoot ps 0 0)
        (fun e =>
          updateBorrowPermOnReadAtProj bs e 0 readerTag [] 0 0 ps 0)
        t).toList.map BorrowEntry.parentTag =
      t.toList.map BorrowEntry.parentTag :=
  pruneMapSubtree_map_proj BorrowEntry.parentTag
    (fun e =>
      (updateBorrowPermOnReadAtProj_struct_fields bs e 0 readerTag [] 0 0 ps
        0).2.2.2.1)
    t

/-- A pruned read keeps a subtree well formed against the unchanged table:
well-formedness depends only on tags, parents, and targets. -/
theorem read_subtree_preserves_sameAlloc (bs : List BorrowEntry)
    (t : BorrowSubtree) (readerTag : Option Nat) (ps : List Nat)
    (h : SameAllocSubtree bs t) :
    SameAllocSubtree bs
      (pruneMapSubtree (readSkipRoot ps 0 0)
        (fun e =>
          updateBorrowPermOnReadAtProj bs e 0 readerTag [] 0 0 ps 0)
        t) :=
  pruneMapSubtree_preserves_sameAlloc
    (fun e =>
      (updateBorrowPermOnReadAtProj_struct_fields bs e 0 readerTag [] 0 0 ps
        0).1)
    (fun e =>
      (updateBorrowPermOnReadAtProj_struct_fields bs e 0 readerTag [] 0 0 ps
        0).2.1)
    (fun e =>
      (updateBorrowPermOnReadAtProj_struct_fields bs e 0 readerTag [] 0 0 ps
        0).2.2.1)
    (fun _ _ => rfl) t h

/-- Every entry of a pruned subtree carries the tag of an entry of the
original subtree, for any tag-preserving update. -/
theorem pruned_entry_tag_from_original {skip : BorrowEntry → Bool}
    {upd : BorrowEntry → BorrowEntry} (htag : ∀ e, (upd e).tag = e.tag)
    (t : BorrowSubtree) (e : BorrowEntry)
    (he : e ∈ (pruneMapSubtree skip upd t).toList) :
    ∃ e₀, e₀ ∈ t.toList ∧ e.tag = e₀.tag := by
  obtain ⟨e₀, h₀, h | h⟩ := mem_pruneMapSubtree_toList t e he
  · exact ⟨e₀, h₀, by rw [h]⟩
  · exact ⟨e₀, h₀, by rw [h, htag]⟩

/-- A tag outside the main fixture is foreign to every entry of it. -/
theorem fx_absent_tag_foreign (tag : Nat)
    (hc : BorrowForest.containsTag fxForest tag = false) :
    ∀ e, e ∈ fxBorrows → isBorrowDescendantOrSelf fxBorrows tag e.tag = false :=
  SameAllocForest.foreign_of_not_containsTag fxForest fx_sameAlloc hc

/-- The unused tag `99` descends from no borrow of the main fixture. -/
theorem fx_tag99_foreign_to_every_entry :
    ∀ e, e ∈ fxBorrows →
      isBorrowDescendantOrSelf fxBorrows 99 e.tag = false :=
  fx_absent_tag_foreign 99 rfl

/-- A `.cell` borrow survives every write, through any writer tag, at any
projection and byte range. -/
theorem cell_entry_survives_every_write (bs : List BorrowEntry)
    (tag : Nat) (loc targetLocal : Local) (parent prot writerTag : Option Nat)
    (writeProj : List ProjectionElem) (depth off len d : Nat) :
    updateBorrowPermTreeAtProj bs (mkEntry tag loc .cell parent prot depth)
        targetLocal writerTag writeProj off len d =
      mkEntry tag loc .cell parent prot depth :=
  updateBorrowPermTreeAtProj_cell bs _ targetLocal writerTag writeProj off
    len d rfl

/-! ### Exactness of the no-op predicates, and writes through a tag -/

/-- The foreign-read no-op predicate is exact: a permission that a foreign
read leaves unchanged without a fault is a foreign-read no-op. This is the
converse of the module's `foreignRead_noop_transition`. -/
theorem foreignRead_noop_exact (isProt : Bool) (p : TreeBorrowPerm) :
    isForeignReadNoopPerm isProt p = true ↔
      treeBorrowNodeAccess .read .foreignAccess p isProt = .transition p := by
  refine ⟨foreignRead_noop_transition p isProt, fun h => ?_⟩
  cases isProt <;> cases p <;>
    first
      | rfl
      | (rename_i c; cases c <;> first | rfl | cases h)
      | cases h

/-- The foreign-write no-op predicate is exact, as the converse of the
module's `foreignWrite_noop_transition`. -/
theorem foreignWrite_noop_exact (isProt : Bool) (p : TreeBorrowPerm) :
    isForeignWriteNoopPerm isProt p = true ↔
      treeBorrowNodeAccess .write .foreignAccess p isProt =
        .transition p := by
  refine ⟨foreignWrite_noop_transition p isProt, fun h => ?_⟩
  cases isProt <;> cases p <;>
    first
      | rfl
      | (rename_i c; cases c <;> first | rfl | cases h)
      | cases h

/-- Forest after a write through tag `41`, the `.reservedIM` child of the
`.cell` root of the main fixture. -/
def fxTaggedWrite : BorrowForest :=
  pruneForeignWrite fxBorrows fxForest 0 (some 41) [] 0 0 0 []

/-- The write through `41` is conflict-free and agrees with the trusted
scan; it activates `41` below the `.cell` root `40`. -/
theorem fxTaggedWrite_result :
    hasProtectedTreeWriteConflict fxBorrows fxBorrows [] 0 (some 41) [] 0 0
      0 = false ∧
    BorrowForest.toList fxTaggedWrite =
      invalidateTreeBorrowsAtProj fxBorrows fxBorrows 0 (some 41) [] 0 0 0 ∧
    summary fxTaggedWrite =
      [(10, .unique), (11, .reservedFrz false), (12, .reservedIM),
        (13, .unique), (20, .disabled), (21, .disabled), (22, .disabled),
        (23, .disabled), (30, .disabled), (31, .disabled), (32, .disabled),
        (40, .cell), (41, .unique), (42, .cell), (50, .disabled),
        (51, .disabled), (52, .reservedIM)] :=
  ⟨rfl,
    pruneForeignWrite_equiv_fullScan fx_sameAlloc fx_writeNoop.1 0 (some 41)
      [] 0 0 0, rfl⟩

/-- Scope of the preservation theorems: they cover direct writes only. A
write through a tag can break both permission-aware invariants, here by
leaving a `.unique` borrow below a `.cell` root, while structural
well-formedness and both root no-op invariants survive. -/
theorem fxTaggedWrite_invariants :
    ¬ ForeignWriteNoopForest [] fxTaggedWrite ∧
    ¬ ForeignReadNoopForest [] fxTaggedWrite ∧
    SameAllocForest (BorrowForest.toList fxTaggedWrite) fxTaggedWrite ∧
    DisabledRootWriteNoopForest [] fxTaggedWrite ∧
    FrozenOrDisabledRootReadNoopForest [] fxTaggedWrite := by
  decide +kernel

/-- Consequently, on the next direct write the permission-aware traversal
misses borrow `41`, while the `.disabled`-root traversal, justified by the
surviving root no-op invariant, is the trusted scan. -/
theorem fxTaggedWrite_then_directWrite :
    summary
      (pruneForeignWrite (BorrowForest.toList fxTaggedWrite) fxTaggedWrite 0
        none [] 0 0 0 []) ≠
      (invalidateTreeBorrowsAtProj (BorrowForest.toList fxTaggedWrite)
        (BorrowForest.toList fxTaggedWrite) 0 none [] 0 0 0).map
        (fun e => (e.tag, e.perm)) ∧
    BorrowForest.toList
        (pruneForeignWriteDisabled (BorrowForest.toList fxTaggedWrite)
          fxTaggedWrite 0 none [] 0 0 0) =
      invalidateTreeBorrowsAtProj (BorrowForest.toList fxTaggedWrite)
        (BorrowForest.toList fxTaggedWrite) 0 none [] 0 0 0 :=
  ⟨by decide +kernel,
    pruneForeignWriteDisabled_rootNoop_equiv_fullScan
      fxTaggedWrite_invariants.2.2.1 fxTaggedWrite_invariants.2.2.2.1 0 none
      [] 0 0 0⟩

end

end Anneal.DualCorrespondenceAndTbPruningTests.TbPruning

/-! ## F. `Std.Do` frame-prep weakest preconditions -/

namespace Anneal.DualCorrespondenceAndTbPruningTests.FrameWp

noncomputable section
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Effect
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.MirAst
open Anneal.MirLiftCore
open Anneal.PureMirExec (PureState)
open Std.Do
open Anneal.TreeBorrowsPruningAndFrameWp

/-!
## Part 2 tests: `Std.Do` frame-prep composition

Tests of the four-stage call pipeline (`prepResolveAndArgs`,
`prepPushCalleeFrame`, the stage-3 retag stages, `prepTeardownAndWriteback`)
and of the weakest preconditions `wpFramePrep`, `wpFramePrepWithProtectors`,
and `wpFramePrepStage3` built from them. Every statement is about the
trusted machine: a concrete resulting state, a `stepMirFn` run, a derived
postcondition, or a refutation. Symbolic tests quantify over machine
states, values, tag and protector counters, or whole MIR bodies.
-/

/-! ### Frame-prep monad and its weakest preconditions -/

/-- A fault raised in `FramePrepM` is a request of the trusted fault effect:
it aborts the run, and it transports to `MirFailE.I` unchanged. -/
theorem framePrep_fault_is_trusted_request (s : MachineState) :
    (throw (FailReq.fail FailureKind.ub) : FramePrepM Unit).run s =
        .error (FailReq.fail .ub) s ∧
      cast framePrepFault_eq_mirFailE (FailReq.fail FailureKind.ub) =
        (FailReq.fail FailureKind.ub : MirFailE.I) :=
  ⟨rfl, rfl⟩

/-- Registering two protectors in sequence, for every state and every pair
of tags: the bind rule reduces the weakest precondition to two unfoldings,
and the final state holds both fresh protectors in registration order. -/
theorem wp_register_two_protectors (t₁ t₂ : Nat) (s : MachineState) :
    (wp⟦prepRegisterProtectors [t₁] >>= fun _ => prepRegisterProtectors [t₂]⟧
      (framePost fun _ s' =>
        s'.memory.nextProtector = s.memory.nextProtector + 2 ∧
        s'.memory.activeProtectors =
          (s.memory.nextProtector + 1) :: s.memory.nextProtector ::
            s.memory.activeProtectors ∧
        s'.frame = s.frame) s).down := by
  refine (wp_framePrep_bind _ _ _ _).mpr
    ((wp_framePost_iff _ _ _).mpr ⟨(), _,
      (prepRegisterProtectors_cons_run t₁ [] s).trans
        (prepRegisterProtectors_nil_run _), ?_⟩)
  exact (wp_framePost_iff _ _ _).mpr ⟨(), _,
    (prepRegisterProtectors_cons_run t₂ [] _).trans
      (prepRegisterProtectors_nil_run _), rfl, rfl, rfl⟩

/-- Stage 4 fails closed on the root frame: with an empty call stack no
total-correctness postcondition has a weakest precondition. -/
theorem wp_teardown_root_frame_false (Q : Unit → MachineState → Prop)
    (s : MachineState) (hRoot : s.memory.callStack = []) :
    ¬ (wp⟦prepTeardownAndWriteback⟧ (framePost Q) s).down := by
  intro h
  obtain ⟨_, s', hRun, _⟩ := (wp_framePost_iff _ _ _).mp h
  obtain ⟨_, caller, rest, _, _, hStack, _⟩ :=
    prepTeardownAndWriteback_spec hRun
  rw [hRoot] at hStack
  cases hStack

/-- A `Std.Do.Triple` for stage 3 on symbolic tags: started with protector
counter `n`, registration ends with counter `n + tags.length`. -/
theorem triple_registerProtectors_counter (tags : List Nat) (n : Nat) :
    Triple (prepRegisterProtectors tags)
      (fun s => ⌜s.memory.nextProtector = n⌝)
      (framePost fun _ s' => s'.memory.nextProtector = n + tags.length) := by
  refine (triple_framePrep_iff _ _ _).mpr fun s hs => ?_
  obtain ⟨s', hRun, _, _, _, hNext, _⟩ := prepRegisterProtectors_ok tags s
  exact (wp_framePost_iff _ _ _).mpr ⟨(), s', hRun, by rw [hNext, hs]⟩

/-- The 0-protector fast path as a weakest precondition: the empty
registration establishes exactly the facts that already hold. -/
theorem wp_registerProtectors_nil_fixes_state (s : MachineState) :
    (wp⟦prepRegisterProtectors []⟧ (framePost fun _ s' => s' = s) s).down ∧
      ¬ (wp⟦prepRegisterProtectors []⟧
        (framePost fun _ s' =>
          s'.memory.nextProtector = s.memory.nextProtector + 1) s).down :=
  ⟨(wp_prepRegisterProtectors_nil _ s).mpr rfl, fun h =>
    Nat.succ_ne_self _ ((wp_prepRegisterProtectors_nil _ s).mp h).symm⟩

/-- A total-correctness triple, read operationally: from any state
satisfying the precondition, the program runs successfully into a result
and state satisfying the postcondition. -/
theorem triple_framePost_run {α : Type} {x : FramePrepM α}
    {P : Assertion FramePrepShape} {Q : α → MachineState → Prop}
    (h : Triple x P (framePost Q)) (s : MachineState) (hs : (P s).down) :
    ∃ a s', x.run s = .ok a s' ∧ Q a s' :=
  (wp_framePost_iff x Q s).mp ((triple_framePrep_iff x P _).mp h s hs)

/-- A total-correctness triple whose postcondition pins the final state:
from any state satisfying the precondition, the program runs successfully
into that state. -/
theorem triple_framePost_run_eq {α : Type} {x : FramePrepM α}
    {P : Assertion FramePrepShape} {sEnd : MachineState}
    (h : Triple x P (framePost fun _ s' => s' = sEnd)) (s : MachineState)
    (hs : (P s).down) : ∃ a, x.run s = .ok a sEnd := by
  obtain ⟨a, s', hRun, hQ⟩ := triple_framePost_run h s hs
  cases hQ
  exact ⟨a, hRun⟩

/-! ### The four stages and their exactness against the trusted machine -/

/-- Function operand naming the empty function `emptyFnAssignUnit`. -/
def emptyFnOperand : Operand :=
  .constant { ty := emptyFnItemTy, val := .zeroSized }

/-- Destination place `_1` of the calls in the worked callers. -/
def destLocal1 : Place := { local_ := 1, projection := [] }

/-- `emptyFnCaller` at the call terminator of `bb0`, after `StorageLive(_1)`. -/
def callerAtCall : MachineState :=
  PureState.toMachineState
    { bb := 0, stmtIdx := 1, env := [.uninit, .uninit] } emptyFnCallerMem

/-- The prepared call of `emptyFnCaller`: the linked empty function, no
argument values, and unchanged caller locals. -/
def emptyPreparedCall : PreparedCall :=
  ⟨emptyFnAssignUnit, [], [.uninit, .uninit]⟩

/-- Entry state of the empty callee pushed by `emptyFnCaller`. -/
def calleeEntry : MachineState :=
  pushCalleeFrame callerAtCall emptyFnCaller [.uninit, .uninit] destLocal1 1
    emptyFnAssignUnit [] .continue_

/-- Stage 1 on the concrete caller: the call resolves to the linked empty
function and leaves the machine state unchanged. -/
theorem stage1_resolves_empty_fn :
    (prepResolveAndArgs emptyFnCaller emptyFnOperand []).run callerAtCall =
      .ok emptyPreparedCall callerAtCall := rfl

/-- Stage 1 records the results of the trusted functions it runs: the
trusted `lookupCallee` of the resolved target is the empty function and the
trusted compatibility check passes. -/
theorem stage1_exact_trusted_lookup :
    ∃ (target : ResolvedCallTarget) (locals : List LocalSlot),
      resolveCallTarget callerAtCall emptyFnOperand 0 emptyFnCaller.localDecls
          emptyFnCaller.layouts = .ok target locals ∧
      lookupCallee callerAtCall.memory.callees emptyFnCaller.layouts
          target.defPath target.typeArgs callerAtCall.memory.traitImpls =
        some emptyFnAssignUnit ∧
      checkCalleeTargetCompatible target emptyFnAssignUnit 0 = true := by
  obtain ⟨_, target, locals, rawArgVals, hRes, hArgs, hLookup, hCompat, _⟩ :=
    prepResolveAndArgs_ok stage1_resolves_empty_fn
  have hNil : rawArgVals = [] := by
    cases hArgs; rfl
  subst hNil
  exact ⟨target, locals, hRes, hLookup, hCompat⟩

/-- Stage 1 fails closed with `.unsupported` when the callee has no linked
body: the same call from a memory without callees is outside frame prep. -/
theorem stage1_unlinked_callee_unsupported :
    (prepResolveAndArgs emptyFnCaller emptyFnOperand []).run
        { callerAtCall with
          memory := { callerAtCall.memory with callees := [] } } =
      .error (FailReq.fail .unsupported)
        { callerAtCall with
          memory := { callerAtCall.memory with callees := [] } } := rfl

/-- Stage 1 and the trusted machine agree on undefined behavior: a call
whose argument operand reads the uninitialized local `_1` faults with `.ub`
in stage 1, and the trusted `evalTerminator` of that call is `fail .ub`. -/
theorem stage1_uninit_argument_ub :
    (prepResolveAndArgs emptyFnCaller emptyFnOperand
        [.copy { local_ := 1, projection := [] }]).run callerAtCall =
        .error (FailReq.fail .ub) callerAtCall ∧
      evalTerminator callerAtCall
          { kind := .call emptyFnOperand
              [.copy { local_ := 1, projection := [] }] destLocal1 (some 1)
              .continue_
            span := "call" }
          (some emptyFnCaller) =
        MirStepNode.fail .ub :=
  ⟨rfl, rfl⟩

/-- Stage 2 on the concrete caller: the pushed frame is the entry frame of
the empty function one frame deep, and it satisfies `EmptyFnEntry`. -/
theorem stage2_pushes_empty_callee_frame :
    (prepPushCalleeFrame emptyFnCaller destLocal1 1 .continue_
        emptyPreparedCall).run callerAtCall = .ok () calleeEntry ∧
      calleeEntry.frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] } ∧
      calleeEntry.memory.activeCallee = some emptyFnAssignUnit ∧
      length calleeEntry.memory.callStack = 1 ∧
      EmptyFnEntry calleeEntry :=
  ⟨rfl, rfl, rfl, rfl,
    emptyFnEntry_of_pushCalleeFrame callerAtCall emptyFnCaller
      [.uninit, .uninit] destLocal1 1 [] .continue_ rfl⟩

/-- Call entry (stages 1 and 2) on the concrete caller. -/
theorem callEntry_run_empty_fn :
    (prepCallEntry emptyFnCaller emptyFnOperand [] destLocal1 1
        .continue_).run callerAtCall = .ok emptyPreparedCall calleeEntry :=
  rfl

/-- The trusted silent-step node is injective in its successor state. -/
theorem mirStepNode_step_injective {s₁ s₂ : MachineState}
    (h : MirStepNode.step s₁ = MirStepNode.step s₂) : s₁ = s₂ := by
  unfold MirStepNode.step at h
  cases h
  rfl

/-- **Call entry is one `stepMirFn` step**, for every body and state at a
`TerminatorKind.call` terminator: a successful call entry is the trusted
step into the trusted `pushCalleeFrame` of the prepared call. -/
theorem callEntry_is_stepMirFn {body cur : CapturedMir} {s s₁ : MachineState}
    {blk : BasicBlockData} {func : Operand} {argOps : List Operand}
    {destination : Place} {targetBb : BasicBlockIdx} {unwind : UnwindAction}
    {call : PreparedCall}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator.kind =
      .call func argOps destination (some targetBb) unwind)
    (h : (prepCallEntry cur func argOps destination targetBb unwind).run s =
      .ok call s₁) :
    stepMirFn body s =
      MirStepNode.step
        (pushCalleeFrame s cur call.localsAfterArgs destination targetBb
          call.calleeBody call.argVals unwind) := by
  rw [stepMirFn_at_terminator hCur hPhase hBb hEnd,
    evalTerminator_call_of_prepCallEntry hTerm h, (prepCallEntry_ok h).1]

/-- The concrete call of `emptyFnCaller` is one trusted step into the entry
state of the empty function. -/
theorem stepMirFn_emptyFnCaller_call :
    stepMirFn emptyFnCaller callerAtCall = MirStepNode.step calleeEntry :=
  callEntry_is_stepMirFn (body := emptyFnCaller) (cur := emptyFnCaller)
    (s := callerAtCall) (blk :=
      { statements := [{ kind := .storageLive 1, span := "live" }]
        terminator := {
          kind := .call emptyFnOperand [] destLocal1 (some 1) .continue_
          span := "call" }
        isCleanup := false })
    rfl (Or.inl rfl) rfl rfl rfl callEntry_run_empty_fn

/-- **Teardown is one `stepMirFn` step**, for every body and state at a
`TerminatorKind.return_` terminator: a successful stage 4 is the trusted
step, and it resumes the popped caller at its return target with statement
index `0`. -/
theorem teardown_is_stepMirFn {body cur : CapturedMir} {s s' : MachineState}
    {blk : BasicBlockData}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator.kind = .return_)
    (h : prepTeardownAndWriteback.run s = .ok () s') :
    stepMirFn body s = MirStepNode.step s' ∧ s'.frame.stmtIdx = 0 ∧
      ∃ (caller : SavedCallerFrame) (rest : List SavedCallerFrame),
        s.memory.callStack = caller :: rest ∧
        s'.frame.blockIdx = caller.returnTarget := by
  obtain ⟨_, caller, rest, locals, mem', hStack, _, hEq⟩ :=
    prepTeardownAndWriteback_spec h
  refine ⟨?_, ?_, caller, rest, hStack, ?_⟩
  · rw [stepMirFn_at_terminator hCur hPhase hBb hEnd]
    exact evalTerminator_return_of_prepTeardown hTerm h
  · rw [hEq]
  · rw [hEq]

/-- Return-ready state of the empty callee of `emptyFnCaller`. -/
def calleeReturn : MachineState := emptyFnReturnState calleeEntry

/-- `emptyFnCaller` resumed at `bb1` with `_1 = ()` written back. -/
def callerResumed : MachineState :=
  PureState.toMachineState
    { bb := 1, stmtIdx := 0, env := [.uninit, .init .unit] }
    { emptyFnCallerMem with activeCallee := some emptyFnCaller }

/-- Stage 4 on the concrete return-ready callee state: the caller frame is
popped, `()` is written to `_1`, and the caller resumes at `bb1`. -/
theorem stage4_run_empty_fn :
    prepTeardownAndWriteback.run calleeReturn = .ok () callerResumed := rfl

/-- The concrete teardown is one trusted `stepMirFn` step of the caller. -/
theorem stepMirFn_emptyFn_return :
    stepMirFn emptyFnCaller calleeReturn = MirStepNode.step callerResumed :=
  (teardown_is_stepMirFn (body := emptyFnCaller) (cur := emptyFnAssignUnit)
    (s := calleeReturn) (blk :=
      { statements := [
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
            span := "unit" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false })
    rfl (Or.inl rfl) rfl rfl rfl stage4_run_empty_fn).1

/-- Stage 4 and the trusted machine agree on a return with an uninitialized
return place, for every memory: stage 4 faults with `.ub` and the trusted
`stepMirFn` of the direct-return empty function is undefined behavior. -/
theorem stage4_uninit_return_place_ub {body : CapturedMir}
    {s₀ : MachineState}
    (hCallee : s₀.memory.activeCallee = some emptyFnDirect)
    (hFrame : s₀.frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] }) :
    prepTeardownAndWriteback.run s₀ = .error (FailReq.fail .ub) s₀ ∧
      stepMirFn body s₀ = MirStepNode.fail .ub := by
  refine ⟨?_, emptyFnDirect_entry_ub hCallee hFrame⟩
  cases s₀ with
  | mk frame memory =>
    cases hFrame
    rfl

/-- Stage 4 rejects a frame deallocation that conflicts with an active
protector: a protected `.unique` borrow of the callee's own `_0` makes the
return undefined behavior in stage 4 and in the trusted machine alike. -/
theorem stage4_protector_conflict_ub :
    let s : MachineState :=
      { calleeReturn with
        memory :=
          { calleeReturn.memory with
            borrows := [
              { tag := 4, targetLocal := 0, targetProjection := [],
                perm := .unique, protector := some 7, targetFrameDepth := 1 }]
            activeProtectors := [7] } }
    prepTeardownAndWriteback.run s = .error (FailReq.fail .ub) s ∧
      stepMirFn emptyFnCaller s = MirStepNode.fail .ub := by
  intro s
  exact ⟨rfl, rfl⟩

/-! ### Stage 3: function-entry protector registration -/

/-- Stage 3 on a symbolic state and two symbolic tags: both borrows receive
consecutive fresh protectors, pushed in registration order, and the frame is
untouched. -/
theorem stage3_two_tags_run (t₁ t₂ : Nat) (s : MachineState) :
    (prepRegisterProtectors [t₁, t₂]).run s =
      .ok ()
        { s with
          memory :=
            { s.memory with
              borrows :=
                attachBorrowProtector
                  (attachBorrowProtector s.memory.borrows t₁
                    s.memory.nextProtector)
                  t₂ (s.memory.nextProtector + 1)
              activeProtectors :=
                (s.memory.nextProtector + 1) :: s.memory.nextProtector ::
                  s.memory.activeProtectors
              nextProtector := s.memory.nextProtector + 2 } } :=
  (prepRegisterProtectors_cons_run t₁ [t₂] s).trans
    ((prepRegisterProtectors_cons_run t₂ [] _).trans
      (prepRegisterProtectors_nil_run _))

/-- `protCaller` at its call terminator, holding the `&[u8]` argument. -/
def protCallerAtCall : MachineState :=
  PureState.toMachineState
    { bb := 0, stmtIdx := 0,
      env := [.uninit, .uninit, .init protSliceVal] } protCallerMem

/-- Entry state of `protCallee`, before its function-entry retag. -/
def protCalleeEntry : MachineState :=
  pushCalleeFrame protCallerAtCall protCaller
    [.uninit, .uninit, .init protSliceVal] destLocal1 1 protCallee
    [protSliceVal] .continue_

/-- `protCalleeEntry` with a symbolic protector counter `n` and a symbolic
slice length `len` in the `&[u8]` argument. -/
def fatRetagEntry (n len : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [
          .uninit,
          .init (.aggregate 0
            [.ptr { allocId := 1, offsetBytes := 0 } 8, .scalar ⟨len, 8⟩])] }
    memory := { protCalleeEntry.memory with nextProtector := n } }

/-- **Fat-reference function-entry retag, symbolic in the protector counter
and the slice length.** The trusted `stepMirFn` advances the statement,
attaches the fresh protector `n` to the slice borrow, activates it, and
leaves the locals unchanged: exactly stage 3 for tag `1`. -/
theorem fatRef_retag_step (n len : Nat) :
    stepMirFn protCaller (fatRetagEntry n len) =
      MirStepNode.step
        { frame :=
            { (fatRetagEntry n len).frame with stmtIdx := 1 }
          memory :=
            { (fatRetagEntry n len).memory with
              borrows := [
                { tag := 1, targetLocal := 3, targetFrameDepth := 0,
                  targetProjection := [], perm := .frozen,
                  protector := some n }]
              activeProtectors := [n]
              nextProtector := n + 1 } } :=
  stepMirFn_retag_fnEntry_fatRef (body := protCaller) (cur := protCallee)
    (s := fatRetagEntry n len)
    (parentEntry :=
      { tag := 1, targetLocal := 3, targetFrameDepth := 0,
        targetProjection := [], perm := .frozen })
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl (fun h => by cases h)
    (fun h => by cases h) rfl

/-- A callee whose only statement retags `_1`, a local with no declaration
(its place has no recorded type): the attach-only retag path. -/
def untypedRetagCallee : CapturedMir :=
  { emptyFnAssignUnit with
    defPath := "Anneal::FrameWpTests::untyped_retag_callee"
    basicBlocks := [
      { statements := [
          { kind := .retag .fnEntry { local_ := 1, projection := [] }
            span := "retag_untyped" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false }] }

/-- Entry state of `untypedRetagCallee` with the thin pointer of borrow `1`
in the undeclared local `_1` and protector counter `n`. -/
def untypedRetagEntry (n : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [.uninit, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
    memory :=
      { borrows := [
          { tag := 1, targetLocal := 3, targetProjection := [],
            perm := .unique }]
        activeCallee := some untypedRetagCallee
        nextProtector := n } }

/-- **Attach-only function-entry retag, symbolic in the protector counter.**
With no recorded place type, the trusted `stepMirFn` performs exactly the
memory update of `prepRegisterProtectors [1]`: no child tag is minted and the
pointer in `_1` is not rewritten. -/
theorem attachOnly_retag_step (n : Nat) :
    stepMirFn untypedRetagCallee (untypedRetagEntry n) =
      MirStepNode.step
        { frame := { (untypedRetagEntry n).frame with stmtIdx := 1 }
          memory :=
            { (untypedRetagEntry n).memory with
              borrows := [
                { tag := 1, targetLocal := 3, targetProjection := [],
                  perm := .unique, protector := some n }]
              activeProtectors := [n]
              nextProtector := n + 1 } } :=
  stepMirFn_retag_fnEntry_attachOnly (body := untypedRetagCallee)
    (cur := untypedRetagCallee) (s := untypedRetagEntry n)
    (parentEntry :=
      { tag := 1, targetLocal := 3, targetProjection := [], perm := .unique })
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl (fun h => by cases h) rfl

/-- Untracked non-null empty shared slice `&[] : &[u8]` at the symbolic
dangling address `a + 1`. -/
def danglingEmptySlice (a : Nat) : Value :=
  .aggregate 0 [.ptr { allocId := a + 1, offsetBytes := 0 } 8, .scalar ⟨0, 8⟩]

/-- `twoArgMixedCallee` at its second retag (`_2 : &[u8]`) holding an
untracked empty slice, with an empty borrow table. -/
def emptySliceRetagEntry (v : Value) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 1
        locals := [.uninit, .init thinRefChildVal, .init v] }
    memory :=
      { activeCallee := some twoArgMixedCallee, nextProtector := 10 } }

/-- **Untracked non-null empty shared slice, symbolic in its address.** The
function-entry retag of `&[]` is one trusted step that registers no protector
and changes no memory, and the unified stage-3 retag runs to the same
state. -/
theorem emptySlice_retag_step (a : Nat) :
    stepMirFn twoArgMixedCallee
        (emptySliceRetagEntry (danglingEmptySlice a)) =
        MirStepNode.step
          { emptySliceRetagEntry (danglingEmptySlice a) with
            frame :=
              { (emptySliceRetagEntry (danglingEmptySlice a)).frame with
                stmtIdx := 2 } } ∧
      (prepFnEntryRetagAny twoArgMixedCallee 2).run
          (emptySliceRetagEntry (danglingEmptySlice a)) =
        .ok ()
          { emptySliceRetagEntry (danglingEmptySlice a) with
            frame :=
              { (emptySliceRetagEntry (danglingEmptySlice a)).frame with
                stmtIdx := 2 } } :=
  ⟨stepMirFn_retag_fnEntry_emptySlice (body := twoArgMixedCallee)
      (cur := twoArgMixedCallee)
      (s := emptySliceRetagEntry (danglingEmptySlice a))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl,
    rfl⟩

/-- **Null empty slices are rejected.** An untracked empty slice at the null
address is undefined behavior in the unified stage-3 retag and in the trusted
`stepMirFn` alike. -/
theorem nullEmptySlice_retag_ub :
    let s := emptySliceRetagEntry
      (.aggregate 0 [.ptr { allocId := 0, offsetBytes := 0 } 8, .scalar ⟨0, 8⟩])
    (prepFnEntryRetagAny twoArgMixedCallee 2).run s =
        .error (FailReq.fail .ub) s ∧
      stepMirFn twoArgMixedCallee s = MirStepNode.fail .ub := by
  intro s
  exact ⟨rfl, rfl⟩

/-- **Untracked non-empty slices are rejected.** A dangling slice of length
`len + 1` has no borrow-table entry to protect: undefined behavior in the
unified stage-3 retag and in the trusted `stepMirFn`, for every length. -/
theorem danglingNonEmptySlice_retag_ub (len : Nat) :
    let s := emptySliceRetagEntry
      (.aggregate 0
        [.ptr { allocId := 99, offsetBytes := 0 } 8, .scalar ⟨len + 1, 8⟩])
    (prepFnEntryRetagAny twoArgMixedCallee 2).run s =
        .error (FailReq.fail .ub) s ∧
      stepMirFn twoArgMixedCallee s = MirStepNode.fail .ub := by
  intro s
  exact ⟨rfl, rfl⟩

/-! ### Stage 3: typed thin, zero-sized, and mutable fat retags -/

/-- `thinRefCaller` at its call terminator, holding the `&u8` argument. -/
def thinCallerAtCall : MachineState :=
  PureState.toMachineState
    { bb := 0, stmtIdx := 0,
      env := [.uninit, .uninit, .init thinRefParentVal] } thinRefCallerMem

/-- Entry state of `thinRefCallee`, before its function-entry retag. -/
def thinCalleeEntry : MachineState :=
  pushCalleeFrame thinCallerAtCall thinRefCaller
    [.uninit, .uninit, .init thinRefParentVal] destLocal1 1 thinRefCallee
    [thinRefParentVal] .continue_

/-- `thinCalleeEntry` with a symbolic tag counter `t`, a symbolic protector
counter `n`, the given borrow table, and the given active protectors. -/
def thinRetagEntry (t n : Nat) (borrows : List BorrowEntry)
    (active : List Nat := []) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [.uninit, .init thinRefParentVal] }
    memory :=
      { thinCalleeEntry.memory with
        borrows := borrows, nextTag := t, nextProtector := n
        activeProtectors := active } }

/-- Unprotected borrow of caller-owned local `3` at frame depth `0`. -/
def callerBorrow (tag : Nat) (perm : TreeBorrowPerm) : BorrowEntry :=
  { tag := tag, targetLocal := 3, targetFrameDepth := 0,
    targetProjection := [], perm := perm }

/-- State after the thin `&u8` retag: `_1` points to the fresh child tag `t`
protected by `n`, and the sibling borrow `9` has been frozen by the initial
read through the parent. -/
def thinRetagResult (t n : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 1
        locals := [.uninit, .init (.ptr { allocId := t, offsetBytes := 0 } 8)] }
    memory :=
      { thinCalleeEntry.memory with
        borrows := [
          { tag := t, targetLocal := 3, targetFrameDepth := 0,
            allocDead := false, targetProjection := [], perm := .frozen,
            rangeOffset := 0, rangeLen := 0, protector := some n,
            parentTag := some 1 },
          callerBorrow 1 .unique, callerBorrow 9 .frozen]
        nextTag := t + 1
        activeProtectors := [n]
        nextProtector := n + 1 } }

/-- The thin stage-3 retag on symbolic counters: it mints child tag `t`,
registers protector `n`, rewrites `_1`, and freezes the sibling borrow. -/
theorem thinRetag_run (t n : Nat) :
    (prepFnEntryRetagThin thinRefCallee 1).run
        (thinRetagEntry t n [callerBorrow 1 .unique, callerBorrow 9 .unique]) =
      .ok () (thinRetagResult t n) := rfl

/-- The block of `thinRefCallee`, as data for the stepping lemmas. -/
def thinCalleeBlock : BasicBlockData :=
  { statements := [
      { kind := .retag .fnEntry { local_ := 1, projection := [] }
        span := "fn_entry_thin_retag" },
      { kind := .assign { local_ := 0, projection := [] }
          (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
        span := "unit" }]
    terminator := { kind := .return_, span := "ret" }
    isCleanup := false }

/-- **Thin-reference function-entry retag is one trusted step**, symbolic in
the tag and protector counters: `stepMirFn` reaches exactly the state
computed by the thin stage, and the saved caller frames are preserved. -/
theorem thinRef_retag_step (t n : Nat) :
    stepMirFn thinRefCaller
        (thinRetagEntry t n [callerBorrow 1 .unique, callerBorrow 9 .unique]) =
        MirStepNode.step (thinRetagResult t n) ∧
      (thinRetagResult t n).memory.callStack =
        thinCalleeEntry.memory.callStack := by
  have h := stepMirFn_retag_fnEntry_thinRef (body := thinRefCaller)
    (cur := thinRefCallee)
    (s := thinRetagEntry t n [callerBorrow 1 .unique, callerBorrow 9 .unique])
    (blk := thinCalleeBlock) (loc := 1) (span := "fn_entry_thin_retag")
    (mutability := .not) (pointee := .uint .u8) (lIdx := 0) (sz := 8)
    (ptrVal := { allocId := 1, offsetBytes := 0 })
    (parentEntry := callerBorrow 1 .unique)
    (locals' := [.uninit, .init thinRefParentVal])
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl
  exact ⟨h.1 _ (thinRetag_run t n), h.2.2 _ (thinRetag_run t n)⟩

/-- **A disabled parent borrow is undefined behavior.** Retagging a `&u8`
whose borrow is `.disabled` faults with `.ub` in the thin stage, and the
trusted `stepMirFn` is `fail .ub`, for all counters. -/
theorem thinRef_retag_disabled_parent_ub (t n : Nat) :
    (prepFnEntryRetagThin thinRefCallee 1).run
        (thinRetagEntry t n [callerBorrow 1 .disabled]) =
        .error (FailReq.fail .ub)
          (thinRetagEntry t n [callerBorrow 1 .disabled]) ∧
      stepMirFn thinRefCaller
          (thinRetagEntry t n [callerBorrow 1 .disabled]) =
        MirStepNode.fail .ub := by
  have h := stepMirFn_retag_fnEntry_thinRef (body := thinRefCaller)
    (cur := thinRefCallee) (s := thinRetagEntry t n [callerBorrow 1 .disabled])
    (blk := thinCalleeBlock) (loc := 1) (span := "fn_entry_thin_retag")
    (mutability := .not) (pointee := .uint .u8) (lIdx := 0) (sz := 8)
    (ptrVal := { allocId := 1, offsetBytes := 0 })
    (parentEntry := callerBorrow 1 .disabled)
    (locals' := [.uninit, .init thinRefParentVal])
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl
  exact ⟨rfl, h.2.1 rfl⟩

/-- **A protected sibling makes the initial read undefined behavior.** The
retag reads through the parent borrow `1`; a sibling `.unique` borrow held
under the active protector `7` forbids that foreign read, so the thin stage
faults with `.ub` and the trusted `stepMirFn` is `fail .ub`. -/
theorem thinRef_retag_protected_sibling_ub (t n : Nat) :
    let s := thinRetagEntry t n
      [callerBorrow 1 .unique,
        { callerBorrow 9 .unique with protector := some 7 }] [7]
    (prepFnEntryRetagThin thinRefCallee 1).run s =
        .error (FailReq.fail .ub) s ∧
      stepMirFn thinRefCaller s = MirStepNode.fail .ub := by
  intro s
  have h := stepMirFn_retag_fnEntry_thinRef (body := thinRefCaller)
    (cur := thinRefCallee) (s := s) (blk := thinCalleeBlock) (loc := 1)
    (span := "fn_entry_thin_retag") (mutability := .not)
    (pointee := .uint .u8) (lIdx := 0) (sz := 8)
    (ptrVal := { allocId := 1, offsetBytes := 0 })
    (parentEntry := callerBorrow 1 .unique)
    (locals' := [.uninit, .init thinRefParentVal])
    rfl (Or.inl rfl) rfl rfl rfl rfl rfl
  exact ⟨rfl, h.2.1 rfl⟩

/-- A callee taking `_1 : &()`: the retagged reference is a zero-sized
scalar address, not a tracked pointer. -/
def zstRefCallee : CapturedMir :=
  { thinRefCallee with
    defPath := "Anneal::FrameWpTests::zst_ref_callee"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .not
        ty := { kind := .ref .not (.tuple []), layoutIdx := 0 }
        debugName := some "_1" }] }

/-- Entry state of `zstRefCallee` holding the scalar address `addr`. -/
def zstRetagEntry (addr : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨addr, 8⟩)] }
    memory := { activeCallee := some zstRefCallee, nextProtector := 10 } }

/-- **Zero-sized reference retag.** A non-null `&()` address retags in one
trusted step without registering a protector, for every address `a + 1`;
the null address is undefined behavior in the unified stage and in the
trusted `stepMirFn`. -/
theorem zstRef_retag_step_and_null_ub (a : Nat) :
    stepMirFn zstRefCallee (zstRetagEntry (a + 1)) =
        MirStepNode.step
          { zstRetagEntry (a + 1) with
            frame := { (zstRetagEntry (a + 1)).frame with stmtIdx := 1 } } ∧
      (prepFnEntryRetagAny zstRefCallee 1).run (zstRetagEntry 0) =
        .error (FailReq.fail .ub) (zstRetagEntry 0) ∧
      stepMirFn zstRefCallee (zstRetagEntry 0) = MirStepNode.fail .ub := by
  have h := fun addr =>
    stepMirFn_retag_fnEntry_any_zst (body := zstRefCallee)
      (cur := zstRefCallee) (s := zstRetagEntry addr) (blk := thinCalleeBlock)
      (loc := 1) (span := "fn_entry_thin_retag") (mutability := .not)
      (pointee := .tuple []) (lIdx := 0) (sc := ⟨addr, 8⟩)
      (locals' := [.uninit, .init (.scalar ⟨addr, 8⟩)])
      rfl (Or.inl rfl) rfl rfl rfl rfl
  exact ⟨(h (a + 1)).1 _ rfl, rfl, (h 0).2.1 rfl⟩

/-- A callee taking `_1 : &mut [u8]`. -/
def mutSliceCallee : CapturedMir :=
  { protCallee with
    defPath := "Anneal::FrameWpTests::mut_slice_callee"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .not
        ty := { kind := .ref .mut (.slice (.uint .u8)), layoutIdx := 0 }
        debugName := some "_1" }] }

/-- Entry state of `mutSliceCallee` whose slice borrow `1` has permission
`perm`, with protector counter `n`. -/
def mutSliceRetagEntry (n : Nat) (perm : TreeBorrowPerm) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init protSliceVal] }
    memory :=
      { borrows := [callerBorrow 1 perm]
        activeCallee := some mutSliceCallee
        nextProtector := n } }

/-- **Mutable fat-reference retag.** A `&mut [u8]` whose borrow is `.unique`
receives the fresh protector `n` in one trusted step; a `.frozen` borrow
cannot be retagged mutably and is undefined behavior in the unified stage
and in the trusted `stepMirFn`. -/
theorem mutFatRef_retag_step_and_frozen_ub (n : Nat) :
    stepMirFn mutSliceCallee (mutSliceRetagEntry n .unique) =
        MirStepNode.step
          { frame :=
              { (mutSliceRetagEntry n .unique).frame with stmtIdx := 1 }
            memory :=
              { (mutSliceRetagEntry n .unique).memory with
                borrows := [
                  { callerBorrow 1 .unique with protector := some n }]
                activeProtectors := [n]
                nextProtector := n + 1 } } ∧
      (prepFnEntryRetagAny mutSliceCallee 1).run
          (mutSliceRetagEntry n .frozen) =
        .error (FailReq.fail .ub) (mutSliceRetagEntry n .frozen) ∧
      stepMirFn mutSliceCallee (mutSliceRetagEntry n .frozen) =
        MirStepNode.fail .ub := by
  have h := fun perm =>
    stepMirFn_retag_fnEntry_any_fat (body := mutSliceCallee)
      (cur := mutSliceCallee) (s := mutSliceRetagEntry n perm)
      (blk :=
        { statements := [
            { kind := .retag .fnEntry { local_ := 1, projection := [] }
              span := "fn_entry_retag" },
            { kind := .assign { local_ := 0, projection := [] }
                (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
              span := "unit" }]
          terminator := { kind := .return_, span := "ret" }
          isCleanup := false })
      (loc := 1) (span := "fn_entry_retag") (mutability := .mut)
      (pointee := .slice (.uint .u8)) (lIdx := 0)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (lenSc := ⟨4, 8⟩)
      (parentEntry := callerBorrow 1 perm)
      (locals' := [.uninit, .init protSliceVal])
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl
  exact ⟨(h .unique).1 _ rfl, rfl, (h .frozen).2.1 rfl⟩

/-- **Untracked empty mutable slices (`&mut []`) are rejected**, contrasting
with `emptySlice_retag_step` for `&[]`: a dangling `&mut []` at any non-null
address `a + 1` is undefined behavior in both `prepFnEntryRetagAny` and the
trusted `stepMirFn`. -/
theorem danglingEmptyMutSlice_retag_ub (a : Nat) :
    let s : MachineState :=
      { frame :=
          { blockIdx := 0, stmtIdx := 0
            locals := [.uninit, .init (danglingEmptySlice a)] }
        memory := { activeCallee := some mutSliceCallee, nextProtector := 10 } }
    (prepFnEntryRetagAny mutSliceCallee 1).run s =
        .error (FailReq.fail .ub) s ∧
      stepMirFn mutSliceCallee s = MirStepNode.fail .ub := by
  intro s
  exact ⟨rfl, rfl⟩

/-- **Disabled shared fat slices are rejected.** Retagging a `&[u8]` whose
borrow-table entry is `.disabled` is undefined behavior in both
`prepFnEntryRetagAny` and the trusted `stepMirFn`, for every protector
counter. -/
theorem disabledSharedFatSlice_retag_ub (n : Nat) :
    let s : MachineState :=
      { frame :=
          { blockIdx := 0, stmtIdx := 0
            locals := [.uninit, .init protSliceVal] }
        memory :=
          { borrows := [callerBorrow 1 .disabled]
            activeCallee := some protCallee
            nextProtector := n } }
    (prepFnEntryRetagAny protCallee 1).run s =
        .error (FailReq.fail .ub) s ∧
      stepMirFn protCallee s = MirStepNode.fail .ub := by
  intro s
  exact ⟨rfl, rfl⟩

/-- A callee taking `_1 : &!` (reference to the uninhabited never type). -/
def uninhabitedRefCallee : CapturedMir :=
  { thinRefCallee with
    defPath := "Anneal::FrameWpTests::uninhabited_ref_callee"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .not
        ty := { kind := .ref .not .never, layoutIdx := 0 }
        debugName := some "_1" }] }

/-- **Uninhabited pointees are rejected even with a live borrow.** Retagging
`_1 : &!` whose borrow `1` is `.unique` is undefined behavior in both
`prepFnEntryRetagAny` and the trusted `stepMirFn`, for all counters. -/
theorem uninhabitedRef_retag_ub (t n : Nat) :
    let s : MachineState :=
      { frame :=
          { blockIdx := 0, stmtIdx := 0
            locals := [.uninit, .init thinRefParentVal] }
        memory :=
          { borrows := [callerBorrow 1 .unique]
            nextTag := t
            activeCallee := some uninhabitedRefCallee
            nextProtector := n } }
    (prepFnEntryRetagAny uninhabitedRefCallee 1).run s =
        .error (FailReq.fail .ub) s ∧
      stepMirFn uninhabitedRefCallee s = MirStepNode.fail .ub := by
  intro s
  exact ⟨rfl, rfl⟩

/-- **Stage 3 fails closed on a global-allocation fat slice.** A `&[u8]`
whose pointer targets an untracked `globals` allocation (`lookupBorrow =
none`, `lookupGlobalAlloc = some _`) is rejected by `prepFnEntryRetagAny`
with `.unsupported`, even though the trusted `stepMirFn` retags it as a
no-op step. The divergence is conservative: Stage 3 proves nothing about
this state instead of claiming an outcome the machine does not produce. -/
theorem globalAllocFatSlice_retag_fails_closed (n : Nat) :
    let gAlloc : CapturedAllocation :=
      { allocId := 1
        bytes := [some 1, some 2, some 3, some 4]
        relocations := []
        align := { bytes := 1 }
        mutability := .not }
    let s : MachineState :=
      { frame :=
          { blockIdx := 0, stmtIdx := 0
            locals := [.uninit, .init protSliceVal] }
        memory :=
          { globals := [gAlloc]
            activeCallee := some protCallee
            nextProtector := n } }
    (prepFnEntryRetagAny protCallee 1).run s =
        .error (FailReq.fail .unsupported) s ∧
      stepMirFn protCallee s =
        MirStepNode.step { s with frame := { s.frame with stmtIdx := 1 } } := by
  intro gAlloc s
  exact ⟨rfl, rfl⟩

/-! ### Stage 3: multi-parameter retag pipelines -/

/-- The thin stage is the unified stage restricted to thin pointers: every
successful thin retag is a successful unified retag into the same state. -/
theorem thinRetag_ok_is_anyRetag_ok {cur : CapturedMir} {loc : Local}
    {s s' : MachineState}
    (h : (prepFnEntryRetagThin cur loc).run s = .ok () s') :
    (prepFnEntryRetagAny cur loc).run s = .ok () s' := by
  have h' := h
  unfold prepFnEntryRetagThin EStateM.run at h'
  unfold prepFnEntryRetagAny EStateM.run
  dsimp only [] at h' ⊢
  cases hOp : evalOperand s.frame.locals
      (.copy { local_ := loc, projection := [] }) s.memory.borrows
      s.memory.globals cur.layouts s.memory.callerLocals cur.localDecls
      s.memory.callStack with
  | ub => rw [hOp] at h'; cases h'
  | unsupported => rw [hOp] at h'; cases h'
  | ok val locals' =>
    rw [hOp] at h'; dsimp only [] at h' ⊢
    cases hTy : placeTy cur.localDecls cur.layouts
        { local_ := loc, projection := [] } with
    | none => rw [hTy] at h'; cases h'
    | some ty =>
      rw [hTy] at h'
      cases ty with
      | mk kind lIdx =>
        cases kind with
        | ref mutability pointee =>
          dsimp only [] at h' ⊢
          cases hU : rigidTyIsUninhabited 16 pointee with
          | true => rw [hU] at h'; cases h'
          | false =>
            rw [hU] at h'; dsimp only [] at h' ⊢
            cases val with
            | ptr ptrVal sz => exact h
            | _ => cases h'
        | _ => cases h'

/-- A successful two-parameter unified retag pipeline, for every body,
locals, and state: it advances the statement index by two inside the same
block and preserves the active callee and the saved caller frames. -/
theorem retags_two_locals_meta (cur : CapturedMir) (l₁ l₂ : Local)
    {s s' : MachineState}
    (h : (prepFnEntryRetags cur [l₁, l₂]).run s = .ok () s') :
    s'.frame.blockIdx = s.frame.blockIdx ∧
      s'.frame.stmtIdx = s.frame.stmtIdx + 2 ∧
      s'.memory.activeCallee = s.memory.activeCallee ∧
      s'.memory.callStack = s.memory.callStack := by
  rw [prepFnEntryRetags_cons] at h
  obtain ⟨_, s₁, h₁, hRest⟩ := run_bind_ok_inv h
  rw [prepFnEntryRetags_cons] at hRest
  obtain ⟨_, s₂, h₂, hNil⟩ := run_bind_ok_inv hRest
  rw [prepFnEntryRetags_nil] at hNil
  have hNil' : EStateM.Result.ok (ε := FramePrepFault) () s₂ = .ok () s' :=
    hNil
  cases hNil'
  obtain ⟨hb₁, hi₁, hc₁, hk₁⟩ := prepFnEntryRetagAny_preserves_meta h₁
  obtain ⟨hb₂, hi₂, hc₂, hk₂⟩ := prepFnEntryRetagAny_preserves_meta h₂
  exact ⟨hb₂.trans hb₁, by rw [hi₂, hi₁], hc₂.trans hc₁, hk₂.trans hk₁⟩

/-- **Syntactic stepping for the thin pipeline.** For every body and state,
if the active block holds `retag fnEntry` statements for `locs` starting at
the current statement, a successful `prepFnEntryRetagThins` run is
`length locs` trusted steps that preserve the saved caller frames. -/
theorem thinRetags_stepsTo_of_stmts {body cur : CapturedMir}
    {blk : BasicBlockData} (locs : List Local) {s s' : MachineState}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hStmts : ∀ (i : Nat) (loc : Local), get? locs i = some loc →
      ∃ span, get? blk.statements (s.frame.stmtIdx + i) =
        some { kind := .retag .fnEntry { local_ := loc, projection := [] },
               span := span })
    (hRun : (prepFnEntryRetagThins cur locs).run s = .ok () s') :
    StepsTo body s (length locs) s' ∧
      s'.memory.callStack = s.memory.callStack :=
  prepFnEntryRetagThins_stepsTo_indexed locs hRun
    fun i loc st st₁ hget hblk hidx hcal hrun => by
      obtain ⟨span, hStmt⟩ := hStmts i loc hget
      exact (stepMirFn_retag_fnEntry_any_ok (span := span)
        (by rw [hcal]; exact hCur) hPhase (by rw [hblk]; exact hBb)
        (by rw [hidx]; exact hStmt) (thinRetag_ok_is_anyRetag_ok hrun)).1

/-- State after both thin retags of `twoArgThinCallee`: `_1` and `_2` point
to the fresh child tags `3` and `4`, protected by `10` and `11`. -/
def twoArgThinRetagged : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 2
        locals := [
          .uninit, .init (.ptr { allocId := 3, offsetBytes := 0 } 8),
          .init (.ptr { allocId := 4, offsetBytes := 0 } 8)] }
    memory :=
      { twoArgThinEntryState.memory with
        borrows := [
          { tag := 4, targetLocal := 4, targetFrameDepth := 0,
            allocDead := false, targetProjection := [], perm := .frozen,
            rangeOffset := 0, rangeLen := 0, protector := some 11,
            parentTag := some 2 },
          { tag := 3, targetLocal := 3, targetFrameDepth := 0,
            allocDead := false, targetProjection := [], perm := .frozen,
            rangeOffset := 0, rangeLen := 0, protector := some 10,
            parentTag := some 1 },
          { tag := 1, targetLocal := 3, targetFrameDepth := 0,
            targetProjection := [], perm := .frozen },
          { tag := 2, targetLocal := 4, targetFrameDepth := 0,
            targetProjection := [], perm := .frozen }]
        nextTag := 5
        activeProtectors := [11, 10]
        nextProtector := 12 } }

/-- The two-parameter thin pipeline on `twoArgThinCallee`, concretely: it
runs to `twoArgThinRetagged`, and by the statement-indexed stepping theorem
that run is exactly two trusted `stepMirFn` steps. -/
theorem twoArgThin_retags_two_steps :
    (prepFnEntryRetagThins twoArgThinCallee [1, 2]).run twoArgThinEntryState =
        .ok () twoArgThinRetagged ∧
      StepsTo twoArgThinCallee twoArgThinEntryState 2 twoArgThinRetagged ∧
      twoArgThinRetagged.memory.callStack = [] := by
  have hRun :
      (prepFnEntryRetagThins twoArgThinCallee [1, 2]).run
          twoArgThinEntryState = .ok () twoArgThinRetagged := rfl
  have hSt :=
    thinRetags_stepsTo_of_stmts (body := twoArgThinCallee)
      (cur := twoArgThinCallee) [1, 2] rfl (Or.inl rfl) rfl
      (fun i loc hget => by
        cases i with
        | zero => cases hget; exact ⟨"retag_1", rfl⟩
        | succ i' =>
          cases i' with
          | zero => cases hget; exact ⟨"retag_2", rfl⟩
          | succ _ => cases hget)
      hRun
  exact ⟨hRun, hSt.1, hSt.2⟩

/-- Entry state of `twoArgMixedCallee` as a root body, with a tracked `&u8`
in `_1`, a tracked `&[u8]` in `_2`, and a symbolic protector counter. -/
def twoArgMixedEntry (n : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [.uninit, .init thinRefParentVal, .init twoArgSliceVal] }
    memory :=
      { borrows := [
          { tag := 1, targetLocal := 4, targetProjection := [],
            perm := .unique },
          { tag := 5, targetLocal := 5, targetProjection := [],
            perm := .frozen }]
        nextTag := 2
        activeCallee := some twoArgMixedCallee
        nextProtector := n } }

/-- State after the mixed thin and fat retags: `_1` points to the fresh
child tag `2` protected by `n`, and the slice borrow `5` carries the next
protector `n + 1`. -/
def twoArgMixedRetagged (n : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 2
        locals := [.uninit, .init thinRefChildVal, .init twoArgSliceVal] }
    memory :=
      { (twoArgMixedEntry n).memory with
        borrows := [
          { tag := 2, targetLocal := 4, targetFrameDepth := 0,
            allocDead := false, targetProjection := [], perm := .frozen,
            rangeOffset := 0, rangeLen := 0, protector := some n,
            parentTag := some 1 },
          { tag := 1, targetLocal := 4, targetProjection := [],
            perm := .unique },
          { tag := 5, targetLocal := 5, targetProjection := [],
            perm := .frozen, protector := some (n + 1) }]
        nextTag := 3
        activeProtectors := [n + 1, n]
        nextProtector := n + 2 } }

/-- **Mixed two-parameter retag pipeline, symbolic in the protector
counter.** The unified pipeline on `(&u8, &[u8])` runs to
`twoArgMixedRetagged`, and the syntactic stepping theorem turns that run
into exactly two trusted steps with no per-statement case analysis. -/
theorem twoArgMixed_retags_two_steps (n : Nat) :
    (prepFnEntryRetags twoArgMixedCallee [1, 2]).run (twoArgMixedEntry n) =
        .ok () (twoArgMixedRetagged n) ∧
      StepsTo twoArgMixedCallee (twoArgMixedEntry n) 2
        (twoArgMixedRetagged n) := by
  have hRun :
      (prepFnEntryRetags twoArgMixedCallee [1, 2]).run (twoArgMixedEntry n) =
        .ok () (twoArgMixedRetagged n) := rfl
  have hSt :=
    prepFnEntryRetags_stepsTo_of_stmts (body := twoArgMixedCallee)
      (cur := twoArgMixedCallee) [1, 2] rfl (Or.inl rfl) rfl
      (fun i loc hget => by
        cases i with
        | zero => cases hget; exact ⟨"retag_thin_1", rfl⟩
        | succ i' =>
          cases i' with
          | zero => cases hget; exact ⟨"retag_fat_2", rfl⟩
          | succ _ => cases hget)
      hRun
  exact ⟨hRun, hSt.1⟩

/-- The worked two-parameter witness with an untracked dangling empty slice,
sharpened by the symbolic pipeline law: the two trusted steps start from a
frame holding the dangling `&[]` in `_2`, advance the statement index by
exactly two, and preserve the saved caller frames. -/
theorem danglingEmptySlice_two_steps_advance_two :
    ∃ s₀ s₃ : MachineState,
      StepsTo twoArgMixedCallee s₀ 2 s₃ ∧
      s₀.frame.locals =
        [.uninit, .init thinRefParentVal, .init danglingEmptySliceVal] ∧
      s₃.frame.stmtIdx = s₀.frame.stmtIdx + 2 ∧
      s₃.memory.callStack = s₀.memory.callStack := by
  obtain ⟨s₃, hRun, hSteps, hStack⟩ := twoArgWithDanglingEmptySlice_stepsTo
  obtain ⟨_, hIdx, _, _⟩ := retags_two_locals_meta _ _ _ hRun
  exact ⟨_, s₃, hSteps, rfl, hIdx, hStack⟩

/-- The one-parameter thin pipeline is the thin stage, for every body, local,
and pair of states. -/
theorem thinRetags_singleton_iff (cur : CapturedMir) (loc : Local)
    (s s' : MachineState) :
    (prepFnEntryRetagThins cur [loc]).run s = .ok () s' ↔
      (prepFnEntryRetagThin cur loc).run s = .ok () s' := by
  rw [prepFnEntryRetagThins_cons, prepFnEntryRetagThins_nil]
  constructor
  · intro h
    obtain ⟨_, s₁, h₁, hNil⟩ := run_bind_ok_inv h
    have hNil' : EStateM.Result.ok (ε := FramePrepFault) () s₁ = .ok () s' :=
      hNil
    cases hNil'
    exact h₁
  · intro h
    exact (run_bind_ok h).trans rfl

/-- Entry state of the one-parameter thin callee with concrete counters. -/
def thinEntry : MachineState :=
  thinRetagEntry 2 10 [callerBorrow 1 .unique, callerBorrow 9 .unique]

/-- State reached when the thin stage is run a second time at statement
index `1`: it retags `_1` again, minting child tag `3` under tag `2`. -/
def thinRetaggedTwice : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 2
        locals := [.uninit, .init (.ptr { allocId := 3, offsetBytes := 0 } 8)] }
    memory :=
      { (thinRetagResult 2 10).memory with
        borrows :=
          { tag := 3, targetLocal := 3, targetFrameDepth := 0,
            allocDead := false, targetProjection := [], perm := .frozen,
            rangeOffset := 0, rangeLen := 0, protector := some 11,
            parentTag := some 2 } :: (thinRetagResult 2 10).memory.borrows
        nextTag := 4
        activeProtectors := [11, 10]
        nextProtector := 12 } }

/-- State the trusted machine actually reaches from statement index `1` of
`thinRefCallee`: it executes `_0 = const ()`. -/
def thinUnitAssigned : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 2
        locals := [.init .unit, .init thinRefChildVal] }
    memory := (thinRetagResult 2 10).memory }

/-- **The unindexed stepping theorem of the thin pipeline is usable only on
the empty parameter list.** With no parameter it yields the zero-step
execution. On the one-parameter `thinRefCallee` the pipeline succeeds and is
one trusted step, yet the unindexed per-local premise is false: it ranges
over every statement index of the block, and at index `1` the thin stage
would retag `_1` again while the trusted machine executes `_0 = const ()`. -/
theorem thinRetags_unindexed_premise_false_one_arg :
    (∀ s', (prepFnEntryRetagThins thinRefCallee []).run thinEntry = .ok () s' →
      StepsTo thinRefCaller thinEntry 0 s') ∧
    (prepFnEntryRetagThins thinRefCallee [1]).run thinEntry =
      .ok () (thinRetagResult 2 10) ∧
    StepsTo thinRefCaller thinEntry 1 (thinRetagResult 2 10) ∧
    ¬ (∀ (loc : Local) (st st₁ : MachineState),
        loc ∈ ([1] : List Local) →
        st.frame.blockIdx = thinEntry.frame.blockIdx →
        st.memory.activeCallee = thinEntry.memory.activeCallee →
        (prepFnEntryRetagThin thinRefCallee loc).run st = .ok () st₁ →
        stepMirFn thinRefCaller st = MirStepNode.step st₁) := by
  refine ⟨fun s' h => ?_, rfl, StepsTo.single (thinRef_retag_step 2 10).1,
    fun hBad => ?_⟩
  · exact (prepFnEntryRetagThins_stepsTo (body := thinRefCaller) [] h
      (fun _ _ _ hMem => nomatch hMem)).1
  · have hAgain :
        (prepFnEntryRetagThin thinRefCallee 1).run (thinRetagResult 2 10) =
          .ok () thinRetaggedTwice := rfl
    have hReal :
        stepMirFn thinRefCaller (thinRetagResult 2 10) =
          MirStepNode.step thinUnitAssigned := rfl
    have hEq : thinUnitAssigned = thinRetaggedTwice :=
      mirStepNode_step_injective
        (hReal.symm.trans
          (hBad 1 _ _ (List.mem_cons_self ..) rfl rfl hAgain))
    have hLocals :
        thinUnitAssigned.frame.locals = thinRetaggedTwice.frame.locals :=
      congrArg (fun st => st.frame.locals) hEq
    cases hLocals

/-! ### Executions of the trusted machine and `LiftState` -/

/-- **The trusted machine is deterministic on silent executions**: two
`n`-step executions from the same state end in the same state. -/
theorem stepsTo_deterministic {body : CapturedMir} :
    ∀ {s : MachineState} {n : Nat} {s₁ s₂ : MachineState},
      StepsTo body s n s₁ → StepsTo body s n s₂ → s₁ = s₂
  | _, _, _, _, .refl _, .refl _ => rfl
  | _, _, _, _, .step h₁ t₁, .step h₂ t₂ => by
    cases mirStepNode_step_injective (h₁.symm.trans h₂)
    exact stepsTo_deterministic t₁ t₂

/-- The whole call of `emptyFnCaller` on the trusted machine: call entry,
the callee body, and the return are three silent steps from the call
terminator to the resumed caller, and no other three-step execution
exists. -/
theorem emptyFnCaller_call_three_steps :
    StepsTo emptyFnCaller callerAtCall 3 callerResumed ∧
      ∀ s', StepsTo emptyFnCaller callerAtCall 3 s' → s' = callerResumed := by
  have hBody :
      stepMirFn emptyFnCaller calleeEntry = MirStepNode.step calleeReturn :=
    emptyFn_step stage2_pushes_empty_callee_frame.2.2.2.2
  have hRun : StepsTo emptyFnCaller callerAtCall 3 callerResumed :=
    StepsTo.trans (StepsTo.single stepMirFn_emptyFnCaller_call)
      (StepsTo.trans (StepsTo.single hBody)
        (StepsTo.single stepMirFn_emptyFn_return))
  exact ⟨hRun, fun s' h => stepsTo_deterministic h hRun⟩

/-- The same call as a frame-prep program: three applications of the
trusted step succeed into the resumed caller, and a fourth executes the
caller's `_0 = const ()`. The fifth trusted step is the return of the root
frame, which is not a silent step, and `prepStep` rejects it with
`.unsupported`. -/
theorem prepSteps_emptyFnCaller_call :
    (prepSteps emptyFnCaller 3).run callerAtCall = .ok () callerResumed ∧
      ∃ sEnd, (prepSteps emptyFnCaller 4).run callerAtCall = .ok () sEnd ∧
        (prepStep emptyFnCaller).run sEnd =
          .error (FailReq.fail .unsupported) sEnd :=
  ⟨prepSteps_ok_of_stepsTo emptyFnCaller_call_three_steps.1, _,
    prepSteps_ok_of_stepsTo
      (StepsTo.trans emptyFnCaller_call_three_steps.1
        (StepsTo.single (s' := advanceStmt callerResumed
          [.init .unit, .init .unit]) rfl)),
    rfl⟩

/-- `prepStep` reports a trusted fault with the trusted fault kind: at the
entry of the direct-return empty function it fails with `.ub`, and a silent
trusted step is a successful `prepStep`. -/
theorem prepStep_fault_and_success :
    (prepStep emptyFnCaller).run
        { calleeEntry with
          memory :=
            { calleeEntry.memory with activeCallee := some emptyFnDirect } } =
        .error (FailReq.fail .ub)
          { calleeEntry with
            memory :=
              { calleeEntry.memory with
                activeCallee := some emptyFnDirect } } ∧
      (prepStep emptyFnCaller).run callerAtCall = .ok () calleeEntry :=
  ⟨rfl, prepStep_ok_of_step stepMirFn_emptyFnCaller_call⟩

/-- **`emptyFnCaller` lifted from its trace.** Composing the three-step call
execution with two continuations of distinct postconditions lifts the
initial frame for their conjunction, for every fuel of at least six steps:
one step for `StorageLive(_1)`, three for the call, two for the return. -/
theorem emptyFnCaller_liftFrame_from_trace (fuel : Nat) (hFuel : 6 ≤ fuel) :
    LiftFrame emptyFnCaller 0 0 [.uninit, .dead] emptyFnCallerMem
      (fun v => v = .unit ∧ v ≠ .scalar { bits := 0, sizeBytes := 1 })
      fuel := by
  have hCont₁ : LiftState emptyFnCaller callerResumed (fun v => v = .unit) 2 :=
    LiftState.of_step rfl (LiftState.of_retNormal rfl rfl)
  have hCont₂ :
      LiftState emptyFnCaller callerResumed
        (fun v => v ≠ .scalar { bits := 0, sizeBytes := 1 }) 2 :=
    LiftState.of_step rfl (LiftState.of_retNormal rfl (fun h => by cases h))
  have hCall :=
    LiftState.of_stepsTo emptyFnCaller_call_three_steps.1
      (LiftState.and hCont₁ hCont₂)
  have hInit :
      LiftState emptyFnCaller
        (PureState.toMachineState
          { bb := 0, stmtIdx := 0, env := [.uninit, .dead] } emptyFnCallerMem)
        (fun v => v = .unit ∧ v ≠ .scalar { bits := 0, sizeBytes := 1 })
        (2 + 3 + 1) :=
    LiftState.of_step (s' := callerAtCall) rfl hCall
  exact liftState_iff_liftFrame.mp (LiftState.mono hFuel hInit)

/-! ### Callee contracts and `wpFramePrep` -/

/-- **Contract extensionality.** A callee contract is determined by its
precondition, postcondition, and step count: the execution guarantee is a
proof and carries no data. -/
theorem framePrepContract_ext {body : CapturedMir}
    (C₁ C₂ : FramePrepContract body) (hPre : C₁.Pre = C₂.Pre)
    (hPost : C₁.Post = C₂.Post) (hSteps : C₁.steps = C₂.steps) : C₁ = C₂ := by
  cases C₁
  cases C₂
  rw [FramePrepContract.mk.injEq]
  exact ⟨hPre, hPost, hSteps⟩

/-- Two contracts that differ in their step count on some state are
different contracts, and a contract has no structural size beyond its
constructor. -/
theorem framePrepContract_steps_ne_and_sizeOf {body : CapturedMir}
    (C₁ C₂ : FramePrepContract body) (s : MachineState)
    (hNe : C₁.steps s ≠ C₂.steps s) : C₁ ≠ C₂ ∧ sizeOf C₁ = 1 := by
  cases C₁
  cases C₂
  refine ⟨fun hEq => hNe ?_, FramePrepContract.mk.sizeOf_spec _ _ _ _⟩
  obtain ⟨_, _, hSteps⟩ := FramePrepContract.mk.inj hEq
  exact congrFun hSteps s

/-- The contract execution as a frame-prep program, for every contract and
every entry state satisfying its precondition: running the trusted machine
for the prescribed number of steps succeeds in a return-ready state that
satisfies the postcondition. -/
theorem contract_exec_runs_prepSteps {body : CapturedMir}
    (C : FramePrepContract body) {s₀ : MachineState} (hPre : C.Pre s₀) :
    ∃ (sRet : MachineState) (retVal : Value),
      (prepSteps body (C.steps s₀)).run s₀ = .ok () sRet ∧
      ReturnReady body sRet retVal ∧ C.Post s₀ retVal sRet := by
  obtain ⟨sRet, retVal, hSteps, hReady, _, hPost⟩ := C.exec s₀ hPre
  exact ⟨sRet, retVal, prepSteps_ok_of_stepsTo hSteps, hReady, hPost⟩

/-- Inversion of the concrete call entry: any successful call entry of
`emptyFnCaller` prepared the empty function with no arguments and reached
the entry state `calleeEntry`; its argument list is a strict structural
sub-term of the prepared call. -/
theorem callEntry_empty_fn_inversion {call : PreparedCall}
    {s₁ : MachineState}
    (h : (prepCallEntry emptyFnCaller emptyFnOperand [] destLocal1 1
      .continue_).run callerAtCall = .ok call s₁) :
    call.calleeBody = emptyFnAssignUnit ∧ call.argVals = [] ∧
      call.localsAfterArgs = [.uninit, .uninit] ∧ s₁ = calleeEntry ∧
      sizeOf call.argVals < sizeOf call := by
  rw [callEntry_run_empty_fn] at h
  cases call with
  | mk calleeBody argVals localsAfterArgs =>
    obtain ⟨hCall, hState⟩ := EStateM.Result.ok.inj h
    have hCall' :
        PreparedCall.mk emptyFnAssignUnit [] [.uninit, .uninit] =
          PreparedCall.mk calleeBody argVals localsAfterArgs := hCall
    rw [PreparedCall.mk.injEq] at hCall'
    obtain ⟨hBody, hArgs, hLocals⟩ := hCall'
    refine ⟨hBody.symm, hArgs.symm, hLocals.symm, hState.symm, ?_⟩
    show sizeOf argVals <
      sizeOf (PreparedCall.mk calleeBody argVals localsAfterArgs)
    rw [PreparedCall.mk.sizeOf_spec]
    omega

/-- **`wpFramePrep` of the concrete empty-function call.** Against the
once-and-for-all contract, the weakest precondition holds at the call
terminator of `emptyFnCaller` for the exact resumed caller state. -/
theorem wpFramePrep_emptyFnCaller :
    (wpFramePrep (emptyFnContract emptyFnCaller) emptyFnCaller emptyFnOperand
      [] destLocal1 1 .continue_ (fun s' => s' = callerResumed)
      callerAtCall).down :=
  (wpFramePrep_emptyFn_iff _ _ _ _ _ _ _ _ _).mpr
    ⟨emptyPreparedCall, calleeEntry, callEntry_run_empty_fn,
      stage2_pushes_empty_callee_frame.2.2.2.2, callerResumed,
      stage4_run_empty_fn, rfl⟩

/-- **A wrong continuation predicate is rejected.** `wpFramePrep` is not
satisfied by a predicate that the real teardown state violates: the call
does not end in the callee's entry state. -/
theorem wpFramePrep_emptyFnCaller_wrong_post_false :
    ¬ (wpFramePrep (emptyFnContract emptyFnCaller) emptyFnCaller
      emptyFnOperand [] destLocal1 1 .continue_ (fun s' => s' = calleeEntry)
      callerAtCall).down := by
  intro h
  obtain ⟨call, s₁, hEntry, hPre, hAll⟩ :=
    (wpFramePrep_iff _ _ _ _ _ _ _ _ _).mp h
  obtain ⟨_, _, _, hS₁, _⟩ := callEntry_empty_fn_inversion hEntry
  cases hS₁
  obtain ⟨s', hTd, hQ⟩ :=
    hAll calleeReturn .unit ⟨rfl, rfl⟩ (emptyFn_returnReady hPre) rfl
  rw [stage4_run_empty_fn] at hTd
  obtain ⟨_, hS'⟩ := EStateM.Result.ok.inj hTd
  have hIdx : callerResumed.frame.blockIdx = calleeEntry.frame.blockIdx :=
    congrArg (fun st => st.frame.blockIdx) (hS'.trans hQ)
  cases hIdx

/-- The execution extracted from `wpFramePrep` of the concrete call: the
contract runs the callee for exactly one trusted step, the returned value is
`()`, and the pipeline ends in the resumed caller. -/
theorem wpFramePrep_emptyFnCaller_run :
    ∃ (sRet : MachineState) (retVal : Value),
      StepsTo emptyFnCaller calleeEntry 1 sRet ∧ retVal = .unit ∧
      sRet = calleeReturn ∧
      prepTeardownAndWriteback.run sRet = .ok () callerResumed := by
  obtain ⟨call, s₁, sRet, retVal, s', hEntry, _, hSteps, _, _, hPost, hTd,
    hQ⟩ := wpFramePrep_run _ _ _ _ _ _ _ _ _ wpFramePrep_emptyFnCaller
  obtain ⟨_, _, _, hS₁, _⟩ := callEntry_empty_fn_inversion hEntry
  cases hS₁
  cases hQ
  exact ⟨sRet, retVal, hSteps, hPost.1, hPost.2, hTd⟩

/-- **The executable call pipeline runs to the resumed caller.** By the
`Std.Do.Triple` soundness of `wpFramePrep`, the program `framePrepCall`
(call entry, the callee on the trusted machine, teardown) succeeds from the
call terminator of `emptyFnCaller` exactly into `callerResumed`. -/
theorem framePrepCall_emptyFnCaller_run :
    (framePrepCall emptyFnCaller (emptyFnContract emptyFnCaller) emptyFnCaller
      emptyFnOperand [] destLocal1 1 .continue_).run callerAtCall =
      .ok () callerResumed :=
  let ⟨_, hRun⟩ :=
    triple_framePost_run_eq
      (wpFramePrep_triple_sound (emptyFnContract emptyFnCaller) emptyFnCaller
        emptyFnOperand [] destLocal1 1 .continue_
        (fun s' => s' = callerResumed))
      callerAtCall wpFramePrep_emptyFnCaller
  hRun

/-- The block of `emptyFnCaller` holding the call, as data. -/
def emptyFnCallerBlock : BasicBlockData :=
  { statements := [{ kind := .storageLive 1, span := "live" }]
    terminator := {
      kind := .call emptyFnOperand [] destLocal1 (some 1) .continue_
      span := "call" }
    isCleanup := false }

/-- Continuation of `emptyFnCaller` at `bb1`: two trusted steps return a
value satisfying each of two distinct postconditions. -/
theorem emptyFnCaller_continuations :
    LiftState emptyFnCaller callerResumed (fun v => v = .unit) 2 ∧
      LiftState emptyFnCaller callerResumed
        (fun v => v ≠ .scalar { bits := 0, sizeBytes := 1 }) 2 :=
  ⟨LiftState.of_step rfl (LiftState.of_retNormal rfl rfl),
    LiftState.of_step rfl (LiftState.of_retNormal rfl (fun h => by cases h))⟩

/-- **Soundness of `wpFramePrep` on the concrete call.** The contract-based
weakest precondition lifts the caller frame at the call terminator: one
step of call entry, one contract step, one step of teardown, then the
two-step continuation. -/
theorem wpFramePrep_sound_emptyFnCaller :
    LiftFrame emptyFnCaller 0 1 [.uninit, .uninit] emptyFnCallerMem
      (fun v => v = .unit) (2 + 1 + 2) :=
  wpFramePrep_sound_stepMirFn (body := emptyFnCaller) (cur := emptyFnCaller)
    (blk := emptyFnCallerBlock) (emptyFnContract emptyFnCaller) 1 rfl
    (Or.inl rfl) rfl rfl rfl (fun _ _ => Nat.le_refl 1)
    wpFramePrep_emptyFnCaller
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp (hQ ▸ emptyFnCaller_continuations.1))

/-- **Monotonicity and conjunctivity on the concrete call.** The exact
post-state predicate weakens to two independent observations, which
recombine into one `wpFramePrep` for their conjunction; conversely a
conjunction containing a violated predicate is rejected. -/
theorem wpFramePrep_emptyFnCaller_conj :
    (wpFramePrep (emptyFnContract emptyFnCaller) emptyFnCaller emptyFnOperand
      [] destLocal1 1 .continue_
      (fun s' =>
        s'.frame.blockIdx = 1 ∧ s'.memory.activeCallee = some emptyFnCaller)
      callerAtCall).down ∧
    ¬ (wpFramePrep (emptyFnContract emptyFnCaller) emptyFnCaller
      emptyFnOperand [] destLocal1 1 .continue_
      (fun s' => s'.frame.blockIdx = 1 ∧ s' = calleeEntry)
      callerAtCall).down := by
  refine ⟨wpFramePrep_conj _ _ _ _ _ _ _ _ ?_ ?_, fun h => ?_⟩
  · exact wpFramePrep_mono _ _ _ _ _ _ _ (fun s' h => by rw [h]; rfl) _
      wpFramePrep_emptyFnCaller
  · exact wpFramePrep_mono _ _ _ _ _ _ _ (fun s' h => by rw [h]; rfl) _
      wpFramePrep_emptyFnCaller
  · exact wpFramePrep_emptyFnCaller_wrong_post_false
      ((wpFramePrep_conj_iff _ _ _ _ _ _ _ _).mpr h).2

/-! ### Four-stage weakest preconditions: `wpFramePrepWithProtectors` and
`wpFramePrepStage3` -/

/-- **0-protector fast path through the four-stage soundness theorem.** With
no protector to register, `wpFramePrepWithProtectors` is `wpFramePrep`, the
stage-3 execution is the empty execution, and the four-stage theorem lifts
the concrete caller with `0` extra steps. -/
theorem wpFramePrepWithProtectors_nil_emptyFnCaller :
    LiftFrame emptyFnCaller 0 1 [.uninit, .uninit] emptyFnCallerMem
      (fun v => v = .unit) (2 + 1 + 0 + 2) :=
  wpFramePrepWithProtectors_sound_stepMirFn (body := emptyFnCaller)
    (cur := emptyFnCaller) (blk := emptyFnCallerBlock) (protTags := [])
    (emptyFnContract emptyFnCaller) 1 rfl (Or.inl rfl) rfl rfl rfl
    (fun _ _ => Nat.le_refl 1)
    ((wpFramePrepWithProtectors_nil_iff _ _ _ _ _ _ _ _ _).mpr
      wpFramePrep_emptyFnCaller)
    (fun _ s₁ sReg _ hReg => by
      have hReg' :
          EStateM.Result.ok (ε := FramePrepFault) () s₁ = .ok () sReg := hReg
      cases hReg'
      exact StepsTo.refl s₁)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp (hQ ▸ emptyFnCaller_continuations.1))

/-- **0-retag fast path of the general four-stage theorem.** With the empty
stage-3 pipeline, `wpFramePrepStage3` is `wpFramePrep`, and the general
soundness theorem lifts the concrete caller with `k = 0` stage-3 steps. -/
theorem wpFramePrepStage3_pure_emptyFnCaller :
    LiftFrame emptyFnCaller 0 1 [.uninit, .uninit] emptyFnCallerMem
      (fun v => v = .unit) (2 + 1 + 0 + 2) :=
  wpFramePrepStage3_sound_stepMirFn (body := emptyFnCaller)
    (cur := emptyFnCaller) (blk := emptyFnCallerBlock) (stage3 := pure ())
    (emptyFnContract emptyFnCaller) 0 1 rfl (Or.inl rfl) rfl rfl rfl
    (fun _ _ => Nat.le_refl 1)
    ((wpFramePrepStage3_pure_iff _ _ _ _ _ _ _ _ _).mpr
      wpFramePrep_emptyFnCaller)
    (fun _ s₁ s₃ _ hS3 => by
      have hS3' : EStateM.Result.ok (ε := FramePrepFault) () s₁ = .ok () s₃ :=
        hS3
      cases hS3'
      exact ⟨StepsTo.refl s₁, rfl⟩)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp (hQ ▸ emptyFnCaller_continuations.1))

/-- **A callee contract authored against the trusted machine**, for every
root body and symbolic counters: after its function-entry retag,
`thinRefCallee` holds the child pointer `t` in `_1` under the single active
protector `n`; it then executes `_0 = const ()` in one trusted step and is
ready to return `()`. -/
def thinTailContract (body : CapturedMir) (t n : Nat) :
    FramePrepContract body where
  Pre := fun s =>
    s.memory.activeCallee = some thinRefCallee ∧
    s.frame =
      { blockIdx := 0, stmtIdx := 1
        locals :=
          [.uninit, .init (.ptr { allocId := t, offsetBytes := 0 } 8)] } ∧
    s.memory.activeProtectors = [n] ∧
    ∀ e, e ∈ s.memory.borrows → e.targetFrameDepth ≠ length s.memory.callStack
  Post := fun s₀ retVal sRet =>
    retVal = .unit ∧
    sRet =
      { frame :=
          { blockIdx := 0, stmtIdx := 2
            locals :=
              [.init .unit,
                .init (.ptr { allocId := t, offsetBytes := 0 } 8)] }
        memory :=
          { s₀.memory with
            borrows :=
              invalidateConflictingBorrows s₀.memory.borrows 0 .none
                (length s₀.memory.callStack) } }
  steps := fun _ => 1
  exec := fun s₀ h => by
    obtain ⟨hCal, hFr, hProt, hFresh⟩ := h
    cases s₀ with
    | mk frame memory =>
      have hFr' :
          frame =
            { blockIdx := 0, stmtIdx := 1
              locals :=
                [.uninit,
                  .init (.ptr { allocId := t, offsetBytes := 0 } 8)] } := hFr
      rw [hFr']
      have hCur : memory.activeCallee.getD body = thinRefCallee := by
        rw [hCal]; rfl
      have hStep :
          stepMirFn body
              { frame :=
                  { blockIdx := 0, stmtIdx := 1
                    locals :=
                      [.uninit,
                        .init (.ptr { allocId := t, offsetBytes := 0 } 8)] }
                memory := memory } =
            MirStepNode.step
              { frame :=
                  { blockIdx := 0, stmtIdx := 2
                    locals :=
                      [.init .unit,
                        .init (.ptr { allocId := t, offsetBytes := 0 } 8)] }
                memory :=
                  { memory with
                    borrows :=
                      invalidateConflictingBorrows memory.borrows 0 .none
                        (length memory.callStack) } } := by
        rw [stepMirFn_frame_stmt hCur (Or.inl rfl) rfl rfl]
        have hrv :
            evalRvalue
                [.uninit, .init (.ptr { allocId := t, offsetBytes := 0 } 8)]
                (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
                memory thinRefCallee.localDecls thinRefCallee.layouts =
              .ok .unit
                [.uninit, .init (.ptr { allocId := t, offsetBytes := 0 } 8)]
                memory := rfl
        unfold evalStmt
        dsimp only []
        rw [hrv]
        dsimp only []
        rw [hProt]
        dsimp only []
        rw [hasProtectedWriteConflict_unrelated_frame memory.borrows [n]
          0 .none .nil 0 0 (length memory.callStack) hFresh]
        rfl
      have hReady :
          ReturnReady body
            { frame :=
                { blockIdx := 0, stmtIdx := 2
                  locals :=
                    [.init .unit,
                      .init (.ptr { allocId := t, offsetBytes := 0 } 8)] }
              memory :=
                { memory with
                  borrows :=
                    invalidateConflictingBorrows memory.borrows 0 .none
                      (length memory.callStack) } }
            .unit := by
        refine ⟨thinRefCallee, _, hCur, Or.inl rfl, rfl, rfl, rfl, rfl, ?_⟩
        have hEq :
            invalidateConflictingBorrows memory.borrows 0 .none
              (length memory.callStack) = memory.borrows :=
          invalidateConflictingBorrows_unrelated_eq memory.borrows 0 .none
            (length memory.callStack) fun e he => by
              cases hb :
                  Nat.beq e.targetFrameDepth (length memory.callStack) with
              | false => rfl
              | true =>
                exact absurd (Nat.eq_of_beq_eq_true hb) (hFresh e he)
        rw [hEq]
        exact hasFrameDeallocProtectorConflict_unrelated_frame
          memory.borrows memory.activeProtectors (length memory.callStack)
          2 hFresh
      exact ⟨_, .unit, StepsTo.single hStep, hReady, rfl, rfl, rfl⟩

/-- Function operand naming `thinRefCallee`. -/
def thinOperand : Operand :=
  .constant { ty := thinRefCalleeItemTy, val := .zeroSized }

/-- `thinRefCaller` at its call terminator with symbolic tag counter `t` and
protector counter `n`. -/
def thinCallerStart (t n : Nat) : MachineState :=
  PureState.toMachineState
    { bb := 0, stmtIdx := 0,
      env := [.uninit, .uninit, .init thinRefParentVal] }
    { thinRefCallerMem with nextTag := t, nextProtector := n }

/-- The prepared call of `thinRefCaller`. -/
def thinPreparedCall : PreparedCall :=
  ⟨thinRefCallee, [thinRefParentVal],
    [.uninit, .uninit, .init thinRefParentVal]⟩

/-- The child borrow minted by the thin retag: tag `t`, protector `n`. -/
def thinChildBorrow (t n : Nat) : BorrowEntry :=
  { tag := t, targetLocal := 3, targetFrameDepth := 0, allocDead := false,
    targetProjection := [], perm := .frozen, rangeOffset := 0, rangeLen := 0,
    protector := some n, parentTag := some 1 }

/-- `thinRefCaller` resumed at `bb1`: `()` written to `_1`, the caller's
protectors restored (none active), the child borrow and its protector id
left in the table, and both counters advanced. -/
def thinCallerResumed (t n : Nat) : MachineState :=
  PureState.toMachineState
    { bb := 1, stmtIdx := 0,
      env := [.uninit, .init .unit, .init thinRefParentVal] }
    { thinRefCallerMem with
      borrows :=
        [thinChildBorrow t n, callerBorrow 1 .unique, callerBorrow 9 .frozen]
      activeProtectors := []
      activeCallee := some thinRefCaller
      nextTag := t + 1
      nextProtector := n + 1 }

/-- Stages 1 to 3 of the thin call, symbolic in both counters: call entry
followed by the one-parameter thin pipeline reaches `thinRetagResult`. -/
theorem thinCall_entry_and_stage3_run (t n : Nat) :
    (prepCallEntryStage3 thinRefCaller thinOperand
        [.copy { local_ := 2, projection := [] }] destLocal1 1 .continue_
        (prepFnEntryRetagThins thinRefCallee [1])).run (thinCallerStart t n) =
      .ok thinPreparedCall (thinRetagResult t n) := rfl

/-- Membership in a three-element borrow table, by cases. -/
theorem forall_mem_three {p : BorrowEntry → Prop} {a b c : BorrowEntry}
    (ha : p a) (hb : p b) (hc : p c) : ∀ e, e ∈ [a, b, c] → p e := by
  intro e he
  cases he with
  | head => exact ha
  | tail _ he =>
    cases he with
    | head => exact hb
    | tail _ he =>
      cases he with
      | head => exact hc
      | tail _ he => cases he

/-- **Four-stage weakest precondition of the thin call**, symbolic in both
counters: against the authored contract, the call from `thinCallerStart`
ends exactly in `thinCallerResumed`. -/
theorem thinCall_wpFramePrepStage3 (t n : Nat) :
    (wpFramePrepStage3 (thinTailContract thinRefCaller t n) thinRefCaller
      thinOperand [.copy { local_ := 2, projection := [] }] destLocal1 1
      .continue_ (prepFnEntryRetagThins thinRefCallee [1])
      (fun s' => s' = thinCallerResumed t n) (thinCallerStart t n)).down :=
  (wpFramePrepStage3_iff _ _ _ _ _ _ _ _ _ _).mpr
    ⟨thinPreparedCall, thinRetagResult t n,
      thinCall_entry_and_stage3_run t n,
      ⟨rfl, rfl, rfl,
        forall_mem_three (fun h => by cases h) (fun h => by cases h)
          (fun h => by cases h)⟩,
      fun sRet retVal hPost _ _ => by
        rw [hPost.2]
        exact ⟨thinCallerResumed t n, rfl, rfl⟩⟩

/-- The execution extracted from the four-stage weakest precondition: one
trusted callee step after the retag, then a teardown into the resumed
caller. -/
theorem thinCall_wpFramePrepStage3_run (t n : Nat) :
    ∃ sRet : MachineState,
      StepsTo thinRefCaller (thinRetagResult t n) 1 sRet ∧
      sRet.memory.callStack = (thinRetagResult t n).memory.callStack ∧
      prepTeardownAndWriteback.run sRet = .ok () (thinCallerResumed t n) := by
  obtain ⟨call, s₃, sRet, retVal, s', hEntry, _, hSteps, _, hStack, _, hTd,
    hQ⟩ := wpFramePrepStage3_run _ _ _ _ _ _ _ _ _ _
      (thinCall_wpFramePrepStage3 t n)
  rw [thinCall_entry_and_stage3_run] at hEntry
  obtain ⟨_, hS₃⟩ := EStateM.Result.ok.inj hEntry
  cases hS₃
  cases hQ
  exact ⟨sRet, hSteps, hStack, hTd⟩

/-- **The executable four-stage pipeline runs to the resumed caller**, by
the `Std.Do.Triple` soundness of `wpFramePrepStage3`. -/
theorem framePrepCallStage3_thinCall_run (t n : Nat) :
    (framePrepCallStage3 thinRefCaller (thinTailContract thinRefCaller t n)
      thinRefCaller thinOperand [.copy { local_ := 2, projection := [] }]
      destLocal1 1 .continue_
      (prepFnEntryRetagThins thinRefCallee [1])).run (thinCallerStart t n) =
      .ok () (thinCallerResumed t n) :=
  let ⟨_, hRun⟩ :=
    triple_framePost_run_eq
      (wpFramePrepStage3_triple_sound (thinTailContract thinRefCaller t n)
        thinRefCaller thinOperand [.copy { local_ := 2, projection := [] }]
        destLocal1 1 .continue_ (prepFnEntryRetagThins thinRefCallee [1])
        (fun s' => s' = thinCallerResumed t n))
      (thinCallerStart t n) (thinCall_wpFramePrepStage3 t n)
  hRun

/-- **Stage-3 monotonicity and conjunctivity on the thin call.** The exact
post-state weakens to two observations that recombine: after the call no
protector is active, yet the protector counter has advanced past `n`, so
the callee's protector id is never reused. -/
theorem thinCall_wpFramePrepStage3_conj (t n : Nat) :
    (wpFramePrepStage3 (thinTailContract thinRefCaller t n) thinRefCaller
      thinOperand [.copy { local_ := 2, projection := [] }] destLocal1 1
      .continue_ (prepFnEntryRetagThins thinRefCallee [1])
      (fun s' =>
        s'.memory.activeProtectors = [] ∧ s'.memory.nextProtector = n + 1)
      (thinCallerStart t n)).down :=
  (wpFramePrepStage3_conj_iff _ _ _ _ _ _ _ _ _).mp
    ⟨wpFramePrepStage3_mono _ _ _ _ _ _ _ _ (fun s' h => by rw [h]; rfl) _
        (thinCall_wpFramePrepStage3 t n),
      wpFramePrepStage3_mono _ _ _ _ _ _ _ _ (fun s' h => by rw [h]; rfl) _
        (thinCall_wpFramePrepStage3 t n)⟩

/-- The call block of `thinRefCaller`, as data. -/
def thinCallerBlock : BasicBlockData :=
  { statements := []
    terminator := {
      kind := .call thinOperand [.copy { local_ := 2, projection := [] }]
        destLocal1 (some 1) .continue_
      span := "call_thin" }
    isCleanup := false }

/-- The stage-3 execution of the thin call: by the syntactic stepping
theorem, any successful run of the thin pipeline from the pushed callee
frame is one trusted step that preserves the saved caller frames. -/
theorem thinCall_stage3_steps (t n : Nat) (call : PreparedCall)
    (s₁ s₃ : MachineState)
    (hEntry : (prepCallEntry thinRefCaller thinOperand
      [.copy { local_ := 2, projection := [] }] destLocal1 1 .continue_).run
        (thinCallerStart t n) = .ok call s₁)
    (hS3 : (prepFnEntryRetagThins thinRefCallee [1]).run s₁ = .ok () s₃) :
    StepsTo thinRefCaller s₁ 1 s₃ ∧
      s₃.memory.callStack = s₁.memory.callStack := by
  have hRun :
      (prepCallEntry thinRefCaller thinOperand
        [.copy { local_ := 2, projection := [] }] destLocal1 1 .continue_).run
          (thinCallerStart t n) =
        .ok thinPreparedCall
          (thinRetagEntry t n
            [callerBorrow 1 .unique, callerBorrow 9 .unique]) := rfl
  rw [hRun] at hEntry
  obtain ⟨_, hS₁⟩ := EStateM.Result.ok.inj hEntry
  cases hS₁
  exact thinRetags_stepsTo_of_stmts (body := thinRefCaller)
    (cur := thinRefCallee) (blk := thinCalleeBlock) [1] rfl (Or.inl rfl) rfl
    (fun i loc hget => by
      cases i with
      | zero => cases hget; exact ⟨"fn_entry_thin_retag", rfl⟩
      | succ _ => cases hget)
    hS3

/-- Continuations of `thinRefCaller` at `bb1`, for all counters: two trusted
steps return a value satisfying each of two distinct postconditions. -/
theorem thinCaller_continuations (t n : Nat) :
    LiftState thinRefCaller (thinCallerResumed t n) (fun v => v = .unit) 2 ∧
      LiftState thinRefCaller (thinCallerResumed t n)
        (fun v => v ≠ .scalar { bits := 0, sizeBytes := 1 }) 2 :=
  ⟨LiftState.of_step rfl (LiftState.of_retNormal rfl rfl),
    LiftState.of_step rfl (LiftState.of_retNormal rfl (fun h => by cases h))⟩

/-- **General four-stage soundness on the thin call, symbolic in both
counters.** The caller of the `&u8` callee is lifted in six trusted steps:
call entry, the function-entry retag, the callee body, teardown, and the
two-step continuation. -/
theorem thinCall_liftFrame (t n : Nat) :
    LiftFrame thinRefCaller 0 0 [.uninit, .uninit, .init thinRefParentVal]
      { thinRefCallerMem with nextTag := t, nextProtector := n }
      (fun v => v = .unit) (2 + 1 + 1 + 2) :=
  wpFramePrepStage3_sound_stepMirFn (body := thinRefCaller)
    (cur := thinRefCaller) (blk := thinCallerBlock)
    (thinTailContract thinRefCaller t n) 1 1 rfl (Or.inl rfl) rfl rfl rfl
    (fun _ _ => Nat.le_refl 1) (thinCall_wpFramePrepStage3 t n)
    (thinCall_stage3_steps t n)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp (hQ ▸ (thinCaller_continuations t n).1))

/-- **One verified four-stage prefix, two suffix specifications.** The thin
call is verified once for the exact mid-state; the two continuations with
distinct postconditions are discharged against that single prefix, and the
caller is lifted for their conjunction. -/
theorem thinCall_duplicate_prefix_liftFrame (t n : Nat) :
    LiftFrame thinRefCaller 0 0 [.uninit, .uninit, .init thinRefParentVal]
      { thinRefCallerMem with nextTag := t, nextProtector := n }
      (fun v => v = .unit ∧ v ≠ .scalar { bits := 0, sizeBytes := 1 })
      (2 + 1 + 1 + 2) :=
  wpFramePrepStage3_duplicate_prefix_liftFrame (body := thinRefCaller)
    (cur := thinRefCaller) (blk := thinCallerBlock)
    (thinTailContract thinRefCaller t n) 1 1 rfl (Or.inl rfl) rfl rfl rfl
    (fun _ _ => Nat.le_refl 1) (thinCall_wpFramePrepStage3 t n)
    (thinCall_stage3_steps t n)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp (hQ ▸ (thinCaller_continuations t n).1))
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp (hQ ▸ (thinCaller_continuations t n).2))

/-! ### Sequential composition against the trusted machine -/

/-- A caller with three consecutive calls to the empty function that keeps a
symbolic value in `_2` and returns it:
`bb0: { _1 = empty() -> bb1 }`, `bb1: { _1 = empty() -> bb2 }`,
`bb2: { StorageLive(_3); _3 = empty() -> bb3 }`,
`bb3: { _0 = copy _2; return }`. -/
def seqCaller : CapturedMir :=
  { emptyFnCallerProt with
    defPath := "Anneal::FrameWpTests::seq_caller"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_1" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_2" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_3" }]
    basicBlocks := [
      { statements := []
        terminator := {
          kind := .call emptyFnOperand [] destLocal1 (some 1) .continue_
          span := "call_a" }
        isCleanup := false },
      { statements := []
        terminator := {
          kind := .call emptyFnOperand [] destLocal1 (some 2) .continue_
          span := "call_b" }
        isCleanup := false },
      { statements := [{ kind := .storageLive 3, span := "live_3" }]
        terminator := {
          kind := .call emptyFnOperand [] { local_ := 3, projection := [] }
            (some 3) .continue_
          span := "call_c" }
        isCleanup := false },
      { statements := [
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 2, projection := [] }))
            span := "ret_copy" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false }] }

/-- Initial memory of `seqCaller` linked against the empty function. -/
def seqCallerMem : Memory :=
  (initMachineStateWithCallees seqCaller [] [emptyFnAssignUnit]).memory

/-- Memory of `seqCaller` after any of its calls has returned. -/
def seqResumedMem : Memory :=
  { seqCallerMem with activeCallee := some seqCaller }

/-- `seqCaller` at the start of block `bb` after at least one call, holding
the symbolic value `v` in `_2`. -/
def seqAt (bb : Nat) (v : Value) : MachineState :=
  PureState.toMachineState
    { bb := bb, stmtIdx := 0,
      env := [.uninit, .init .unit, .init v, .dead] } seqResumedMem

/-- The once-and-for-all contract of the empty function over `seqCaller`. -/
def seqContract : FramePrepContract seqCaller := emptyFnContract seqCaller

/-- `wpFramePrep` of the first call of `seqCaller`: it reduces to the
continuation predicate at the resumed state `seqAt 1 v`. -/
theorem seqCaller_wp_call_a (v : Value) (Q : MachineState → Prop)
    (hQ : Q (seqAt 1 v)) :
    (wpFramePrep seqContract seqCaller emptyFnOperand [] destLocal1 1
      .continue_ Q
      (PureState.toMachineState
        { bb := 0, stmtIdx := 0,
          env := [.uninit, .uninit, .init v, .dead] } seqCallerMem)).down :=
  (wpFramePrep_emptyFn_iff _ _ _ _ _ _ _ _ _).mpr
    ⟨⟨emptyFnAssignUnit, [], [.uninit, .uninit, .init v, .dead]⟩, _, rfl,
      emptyFnEntry_of_pushCalleeFrame _ _ _ _ _ _ _ rfl, seqAt 1 v, rfl, hQ⟩

/-- `wpFramePrep` of the second call of `seqCaller`, from `seqAt 1 v`. -/
theorem seqCaller_wp_call_b (v : Value) (Q : MachineState → Prop)
    (hQ : Q (seqAt 2 v)) :
    (wpFramePrep seqContract seqCaller emptyFnOperand [] destLocal1 2
      .continue_ Q (seqAt 1 v)).down :=
  (wpFramePrep_emptyFn_iff _ _ _ _ _ _ _ _ _).mpr
    ⟨⟨emptyFnAssignUnit, [], [.uninit, .init .unit, .init v, .dead]⟩, _, rfl,
      emptyFnEntry_of_pushCalleeFrame _ _ _ _ _ _ _ rfl, seqAt 2 v, rfl, hQ⟩

/-- `seqCaller` at `bb3` after its third call wrote `()` to `_3`. -/
def seqAtEnd (v : Value) : MachineState :=
  PureState.toMachineState
    { bb := 3, stmtIdx := 0,
      env := [.uninit, .init .unit, .init v, .init .unit] } seqResumedMem

/-- `wpFramePrep` of the third call of `seqCaller`, from the call terminator
of `bb2` (after `StorageLive(_3)`). -/
theorem seqCaller_wp_call_c (v : Value) (Q : MachineState → Prop)
    (hQ : Q (seqAtEnd v)) :
    (wpFramePrep seqContract seqCaller emptyFnOperand []
      { local_ := 3, projection := [] } 3 .continue_ Q
      (PureState.toMachineState
        { bb := 2, stmtIdx := 1,
          env := [.uninit, .init .unit, .init v, .uninit] }
        seqResumedMem)).down :=
  (wpFramePrep_emptyFn_iff _ _ _ _ _ _ _ _ _).mpr
    ⟨⟨emptyFnAssignUnit, [], [.uninit, .init .unit, .init v, .uninit]⟩, _,
      rfl, emptyFnEntry_of_pushCalleeFrame _ _ _ _ _ _ _ rfl, seqAtEnd v,
      rfl, hQ⟩

/-- The final continuation of `seqCaller` at `bb3`: `_0 = copy _2; return`
returns any initialized symbolic value in two trusted steps, so every
postcondition that holds of `v` is established. -/
theorem seqCaller_final_continuation (v : Value) (post : Value → Prop)
    (hv : valueContainsUninit v = false) (hPost : post v) :
    LiftState seqCaller (seqAtEnd v) post 2 := by
  let mem₀ : Memory := seqResumedMem
  let mem₁ : Memory :=
    { mem₀ with borrows := invalidateConflictingBorrows mem₀.borrows 0 .none 0 }
  let mem₂ : Memory :=
    { mem₁ with borrows := disableFrameBorrows mem₁.borrows 0 4 }
  refine
    LiftState.of_step
      (s' :=
        { frame :=
            { blockIdx := 3, stmtIdx := 1,
              locals := [.init v, .init .unit, .init v, .init .unit] }
          memory := mem₁ })
      ?_
      (LiftState.of_retNormal (mem' := mem₂) ?_ hPost)
  · have hRval :
        evalRvalue [.uninit, .init .unit, .init v, .init .unit]
          (.use (.copy { local_ := 2, projection := [] })) mem₀
          seqCaller.localDecls emptyFnLayouts =
          .ok v [.uninit, .init .unit, .init v, .init .unit] mem₀ := by
      change
        (match
          match
            match valueContainsUninit v with
            | false => ProjReadResult.ok v
            | true => ProjReadResult.ub
          with
          | .ok fieldVal =>
            PlaceReadResult.ok fieldVal
              [.uninit, .init .unit, .init v, .init .unit]
          | .ub => PlaceReadResult.ub
          | .unsupported => PlaceReadResult.unsupported
         with
         | .ok val locals' => RvalueEvalResult.ok val locals' mem₀
         | .ub => RvalueEvalResult.ub
         | .unsupported => RvalueEvalResult.unsupported) = _
      rw [hv]
    change
      (match
        evalRvalue [.uninit, .init .unit, .init v, .init .unit]
          (.use (.copy { local_ := 2, projection := [] })) mem₀
          seqCaller.localDecls emptyFnLayouts
       with
       | .ok val locals₁ mem₁' => _
       | .ub => _
       | .unsupported => _) = _
    rw [hRval]
    rfl
  · change
      (match valueContainsUninit v with
       | true => MirStepNode.fail .ub
       | false => MirStepNode.retNormal v mem₂) = _
    rw [hv]

/-- Block `bb0` of `seqCaller`, as data. -/
def seqBlockA : BasicBlockData :=
  { statements := []
    terminator := {
      kind := .call emptyFnOperand [] destLocal1 (some 1) .continue_
      span := "call_a" }
    isCleanup := false }

/-- Block `bb1` of `seqCaller`, as data. -/
def seqBlockB : BasicBlockData :=
  { statements := []
    terminator := {
      kind := .call emptyFnOperand [] destLocal1 (some 2) .continue_
      span := "call_b" }
    isCleanup := false }

/-- Block `bb2` of `seqCaller`, as data. -/
def seqBlockC : BasicBlockData :=
  { statements := [{ kind := .storageLive 3, span := "live_3" }]
    terminator := {
      kind := .call emptyFnOperand [] { local_ := 3, projection := [] }
        (some 3) .continue_
      span := "call_c" }
    isCleanup := false }

/-- **Bridged two-call soundness, symbolic in the kept value.** From
`seqAt 1 v`, the second call returns to `bb2`, one bridge step
(`StorageLive(_3)`) reaches the third call, and the caller returns `v`:
`2 + 1 + 2 + 1 + 1 + 2` trusted steps, for every postcondition of `v`. -/
theorem seqCaller_bridge_liftFrame (v : Value) (post : Value → Prop)
    (hv : valueContainsUninit v = false) (hPost : post v) :
    LiftFrame seqCaller 1 0 [.uninit, .init .unit, .init v, .dead]
      seqResumedMem post (2 + 1 + 2 + 1 + 1 + 2) :=
  wpFramePrep_seq_bridge_sound_stepMirFn (body := seqCaller)
    (cur := seqCaller) (blk₀ := seqBlockB) (blk₁' := seqBlockC)
    (bb₁' := 2) (stmtIdx₁' := 1) (Mid := fun s' => s' = seqAt 2 v)
    (Q := fun s' => s' = seqAtEnd v) seqContract seqContract 1 1 1 rfl
    (Or.inl rfl) rfl rfl rfl rfl rfl rfl (fun _ _ => Nat.le_refl 1)
    (fun _ _ => Nat.le_refl 1) (seqCaller_wp_call_b v _ rfl)
    (fun _ _ hMid =>
      ⟨[.uninit, .init .unit, .init v, .uninit], seqResumedMem,
        hMid ▸ StepsTo.single rfl, rfl, seqCaller_wp_call_c v _ rfl⟩)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp
        (hQ ▸ seqCaller_final_continuation v post hv hPost))

/-- Continuation of `seqCaller` at `bb2`, symbolic in the kept value: one
step for `StorageLive(_3)`, then the third call discharged by the
once-and-for-all empty-function rule (three steps, callee never unfolded),
then the two-step return of `v`. -/
theorem seqCaller_continuation_at_c (v : Value) (post : Value → Prop)
    (hv : valueContainsUninit v = false) (hPost : post v) :
    LiftState seqCaller (seqAt 2 v) post 6 := by
  refine LiftState.of_step
    (s' := PureState.toMachineState
      { bb := 2, stmtIdx := 1,
        env := [.uninit, .init .unit, .init v, .uninit] } seqResumedMem)
    rfl (liftState_iff_liftFrame.mpr ?_)
  exact wpFramePrep_empty_function (body := seqCaller) (cur := seqCaller)
    (blk := seqBlockC)
    (call := ⟨emptyFnAssignUnit, [],
      [.uninit, .init .unit, .init v, .uninit]⟩)
    (s' := seqAtEnd v) rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl
    (fun _ _ h =>
      liftState_iff_liftFrame.mp
        (h ▸ seqCaller_final_continuation v post hv hPost))

/-- **Sequential two-call soundness, symbolic in the kept value.** The two
adjacent calls of `bb0` and `bb1`, composed by nesting `wpFramePrep`, lift
`seqCaller` from its initial frame: `6 + 1 + 2 + 1 + 2` trusted steps, and
the caller returns the value it kept in `_2` across all three calls. -/
theorem seqCaller_seq_liftFrame (v : Value)
    (hv : valueContainsUninit v = false) :
    LiftFrame seqCaller 0 0 [.uninit, .uninit, .init v, .dead] seqCallerMem
      (fun r => r = v) (6 + 1 + 2 + 1 + 2) :=
  wpFramePrep_seq_sound_stepMirFn (body := seqCaller) (cur := seqCaller)
    (blk₀ := seqBlockA) (blk₁ := seqBlockB)
    (Q := fun s' => s' = seqAt 2 v) seqContract seqContract 1 1 rfl
    (Or.inl rfl) rfl rfl rfl rfl rfl rfl (fun _ _ => Nat.le_refl 1)
    (fun _ _ => Nat.le_refl 1)
    (seqCaller_wp_call_a v _ ⟨rfl, seqCaller_wp_call_b v _ rfl⟩)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp
        (hQ ▸ seqCaller_continuation_at_c v _ hv rfl))

/-- **A two-call prefix verified once, two suffix specifications.** The
nested `wpFramePrep` of the calls of `bb0` and `bb1` is established once
for the mid-state `seqAt 2 v`; two continuations with distinct
postconditions are discharged against it, and the caller is lifted for
their conjunction. -/
theorem seqCaller_seq_duplicate_prefix_liftFrame (v : Value)
    (hv : valueContainsUninit v = false) :
    LiftFrame seqCaller 0 0 [.uninit, .uninit, .init v, .dead] seqCallerMem
      (fun r => r = v ∧ (v = .unit → r = .unit)) (6 + 1 + 2 + 1 + 2) :=
  wpFramePrep_seq_duplicate_prefix_liftFrame (body := seqCaller)
    (cur := seqCaller) (blk₀ := seqBlockA) (blk₁ := seqBlockB)
    (Mid := fun s' => s' = seqAt 2 v) seqContract seqContract 1 1 rfl
    (Or.inl rfl) rfl rfl rfl rfl rfl rfl (fun _ _ => Nat.le_refl 1)
    (fun _ _ => Nat.le_refl 1)
    (seqCaller_wp_call_a v _ ⟨rfl, seqCaller_wp_call_b v _ rfl⟩)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp
        (hQ ▸ seqCaller_continuation_at_c v _ hv rfl))
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp
        (hQ ▸ seqCaller_continuation_at_c v _ hv (fun h => h)))

/-- **One call verified once, two suffix specifications.** The first call of
`seqCaller` is verified once for the mid-state `seqAt 1 v`; the bridged
remainder of the body is lifted for two distinct postconditions against
that single prefix, and the caller is lifted for their conjunction. -/
theorem seqCaller_duplicate_prefix_liftFrame (v : Value)
    (hv : valueContainsUninit v = false) :
    LiftFrame seqCaller 0 0 [.uninit, .uninit, .init v, .dead] seqCallerMem
      (fun r => r = v ∧ (v = .unit → r = .unit))
      (2 + 1 + 2 + 1 + 1 + 2 + 1 + 2) :=
  wpFramePrep_duplicate_prefix_liftFrame (body := seqCaller)
    (cur := seqCaller) (blk := seqBlockA) (Mid := fun s' => s' = seqAt 1 v)
    seqContract 1 rfl (Or.inl rfl) rfl rfl rfl (fun _ _ => Nat.le_refl 1)
    (seqCaller_wp_call_a v _ rfl)
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp
        (hQ ▸ liftState_iff_liftFrame.mpr
          (seqCaller_bridge_liftFrame v _ hv rfl)))
    (fun _ _ hQ =>
      liftState_iff_liftFrame.mp
        (hQ ▸ liftState_iff_liftFrame.mpr
          (seqCaller_bridge_liftFrame v _ hv (fun h => h))))

/-! ### Sequential composition and prefix sharing as `Std.Do.Triple`s -/

/-- Initial state of `seqCaller` holding the symbolic value `v` in `_2`. -/
def seqStart (v : Value) : MachineState :=
  PureState.toMachineState
    { bb := 0, stmtIdx := 0,
      env := [.uninit, .uninit, .init v, .dead] } seqCallerMem

/-- The executable pipeline of the first call of `seqCaller`. -/
def seqCallA : FramePrepM Unit :=
  framePrepCall seqCaller seqContract seqCaller emptyFnOperand [] destLocal1 1
    .continue_

/-- The executable pipeline of the second call of `seqCaller`. -/
def seqCallB : FramePrepM Unit :=
  framePrepCall seqCaller seqContract seqCaller emptyFnOperand [] destLocal1 2
    .continue_

/-- **Two call pipelines in sequence run to the second return point.** The
nested weakest precondition is a valid precondition of the two executable
pipelines composed with bind, so the composed program succeeds from the
initial state exactly into `seqAt 2 v`. -/
theorem seqCaller_two_pipelines_run (v : Value) :
    (seqCallA >>= fun _ => seqCallB).run (seqStart v) = .ok () (seqAt 2 v) :=
  let ⟨_, hRun⟩ :=
    triple_framePost_run_eq
      (wpFramePrep_seq seqContract seqContract seqCaller seqCaller
        emptyFnOperand emptyFnOperand [] [] destLocal1 destLocal1 1 2
        .continue_ .continue_ (fun s' => s' = seqAt 2 v))
      (seqStart v) (seqCaller_wp_call_a v _ (seqCaller_wp_call_b v _ rfl))
  hRun

/-- **The shared prefix, verified once.** The first call pipeline, started
in the initial state, ends in `seqAt 1 v`. -/
theorem seqCallA_triple (v : Value) :
    Triple seqCallA (fun s => ⌜s = seqStart v⌝)
      (framePost fun _ s' => s' = seqAt 1 v) :=
  (triple_framePrep_iff _ _ _).mpr fun s hs => by
    have hs' : s = seqStart v := hs
    rw [hs']
    exact (triple_framePrep_iff _ _ _).mp
      (wpFramePrep_triple_sound seqContract seqCaller emptyFnOperand []
        destLocal1 1 .continue_ (fun s' => s' = seqAt 1 v))
      (seqStart v) (seqCaller_wp_call_a v _ rfl)

/-- A suffix specification of the second call pipeline: from the mid-state
`seqAt 1 v` it establishes every predicate that holds at `seqAt 2 v`. -/
theorem seqCallB_triple (v : Value) (Q : MachineState → Prop)
    (hQ : Q (seqAt 2 v)) :
    Triple seqCallB (fun s => ⌜s = seqAt 1 v⌝) (framePost fun _ s' => Q s') :=
  (triple_framePrep_iff _ _ _).mpr fun s hs => by
    have hs' : s = seqAt 1 v := hs
    rw [hs']
    exact (triple_framePrep_iff _ _ _).mp
      (wpFramePrep_triple_sound seqContract seqCaller emptyFnOperand []
        destLocal1 2 .continue_ Q)
      (seqAt 1 v) (seqCaller_wp_call_b v _ hQ)

/-- **Prefix sharing, total-correctness form.** The prefix triple
`seqCallA_triple` is used once and discharges two suffix specifications of
the second pipeline (its return block; the caller's preserved locals): the
composed program ends in a state satisfying both. -/
theorem seqCaller_shared_prefix_post (v : Value) :
    ∃ s', (seqCallA >>= fun _ => seqCallB).run (seqStart v) = .ok () s' ∧
      s'.frame.blockIdx = 2 ∧
      s'.frame.locals = [.uninit, .init .unit, .init v, .dead] := by
  have hT :=
    wpFramePrep_duplicate_prefix_post seqCallA (fun _ => seqCallB)
      (Mid := fun _ s => s = seqAt 1 v)
      (Q₁ := fun _ s' => s'.frame.blockIdx = 2)
      (Q₂ := fun _ s' =>
        s'.frame.locals = [.uninit, .init .unit, .init v, .dead])
      (seqCallA_triple v) (fun _ => seqCallB_triple v _ rfl)
      (fun _ => seqCallB_triple v _ rfl)
  obtain ⟨_, s', hRun, hQ₁, hQ₂⟩ := triple_framePost_run hT (seqStart v) rfl
  exact ⟨s', hRun, hQ₁, hQ₂⟩

/-- **Prefix sharing across two distinct suffix programs.** The same prefix
triple discharges the second call pipeline (a `Unit` program) and the bare
call entry of the second call (a `PreparedCall` program): both composed
programs succeed from the initial state with their own postconditions. -/
theorem seqCaller_shared_prefix_two_suffixes (v : Value) :
    (∃ s', (seqCallA >>= fun _ => seqCallB).run (seqStart v) = .ok () s' ∧
      s' = seqAt 2 v) ∧
    (∃ call s',
      (seqCallA >>= fun _ =>
        prepCallEntry seqCaller emptyFnOperand [] destLocal1 2
          .continue_).run (seqStart v) = .ok call s' ∧
      call.calleeBody = emptyFnAssignUnit ∧ EmptyFnEntry s') := by
  have hT :=
    wpFramePrep_duplicate_prefix_two_suffixes seqCallA (fun _ => seqCallB)
      (fun _ =>
        prepCallEntry seqCaller emptyFnOperand [] destLocal1 2 .continue_)
      (Mid := fun _ s => s = seqAt 1 v) (Q₁ := fun _ s' => s' = seqAt 2 v)
      (Q₂ := fun call s' =>
        call.calleeBody = emptyFnAssignUnit ∧ EmptyFnEntry s')
      (seqCallA_triple v) (fun _ => seqCallB_triple v _ rfl)
      (fun _ => (triple_framePrep_iff _ _ _).mpr fun s hs => by
        have hs' : s = seqAt 1 v := hs
        rw [hs']
        exact (wp_framePost_iff _ _ _).mpr
          ⟨⟨emptyFnAssignUnit, [],
              [.uninit, .init .unit, .init v, .dead]⟩, _, rfl, rfl,
            emptyFnEntry_of_pushCalleeFrame _ _ _ _ _ _ _ rfl⟩)
  obtain ⟨_, s₁, hRun₁, hQ₁⟩ := triple_framePost_run hT.1 (seqStart v) rfl
  obtain ⟨call, s₂, hRun₂, hQ₂⟩ := triple_framePost_run hT.2 (seqStart v) rfl
  exact ⟨⟨s₁, hRun₁, hQ₁⟩, call, s₂, hRun₂, hQ₂⟩

/-- A total-correctness triple of a frame-prep program holds for every
exception postcondition: the program never faults from its precondition. -/
theorem triple_framePost_any_exceptConds {α : Type} (x : FramePrepM α)
    (P : Assertion FramePrepShape) (Mid : α → MachineState → Prop)
    (E : ExceptConds FramePrepShape) (h : Triple x P (framePost Mid)) :
    Triple x P (fun a s => ⌜Mid a s⌝, E) := by
  rw [triple_framePrep_iff] at h ⊢
  intro s hs
  obtain ⟨a, s₁, hRun, hMid⟩ := (wp_framePost_iff _ _ _).mp (h s hs)
  simp only [wp, PredTrans.apply]
  split
  · rename_i a' s' heq
    rw [hRun] at heq
    cases heq
    exact hMid
  · rename_i e s' heq
    rw [hRun] at heq
    cases heq

/-- The weakest precondition for the conjunction `∧ₚ` of two
total-correctness postconditions: a successful run into a state satisfying
both. -/
theorem wp_framePost_and_iff {α : Type} (x : FramePrepM α)
    (Q₁ Q₂ : α → MachineState → Prop) (s : MachineState) :
    (wp⟦x⟧ (framePost Q₁ ∧ₚ framePost Q₂) s).down ↔
      ∃ a s', x.run s = .ok a s' ∧ Q₁ a s' ∧ Q₂ a s' := by
  simp only [wp, PredTrans.apply]
  split
  · rename_i a s' heq
    exact ⟨fun hq => ⟨a, s', heq, hq.1, hq.2⟩, fun ⟨a', s'', he, hq⟩ => by
      rw [heq] at he
      cases he
      exact hq⟩
  · rename_i e s' heq
    exact ⟨fun hq => False.elim hq.1, fun ⟨a', s'', he, _⟩ => by
      rw [heq] at he
      cases he⟩

/-- First suffix specification: the caller is the active body again. -/
def seqPostActive : PostCond Unit FramePrepShape :=
  framePost fun _ s' => s'.memory.activeCallee = some seqCaller

/-- Second suffix specification: no saved caller frame remains. -/
def seqPostStack : PostCond Unit FramePrepShape :=
  framePost fun _ s' => s'.memory.callStack = []

/-- The mid-condition of the shared prefix, as a `Std.Do` assertion. -/
def seqMidAssertion (v : Value) : Unit → Assertion FramePrepShape :=
  fun _ s => ⌜s = seqAt 1 v⌝

/-- The shared prefix triple in the form required by the general rule: its
exception postcondition is that of the conjunction of the two suffix
specifications. -/
theorem seqCallA_triple_postCond (v : Value) :
    Triple seqCallA (fun s => ⌜s = seqStart v⌝)
      (seqMidAssertion v, (seqPostActive ∧ₚ seqPostStack).2) :=
  triple_framePost_any_exceptConds seqCallA _ (fun _ s => s = seqAt 1 v) _
    (seqCallA_triple v)

/-- A triple for the conjunction `∧ₚ` of two total-correctness
postconditions yields, from any state satisfying its precondition, a
successful run into a state satisfying both. -/
theorem triple_framePost_and_run {α : Type} {x : FramePrepM α}
    {P : Assertion FramePrepShape} {Q₁ Q₂ : α → MachineState → Prop}
    (h : Triple x P (framePost Q₁ ∧ₚ framePost Q₂)) (s : MachineState)
    (hs : (P s).down) :
    ∃ a s', x.run s = .ok a s' ∧ Q₁ a s' ∧ Q₂ a s' :=
  (wp_framePost_and_iff x Q₁ Q₂ s).mp ((triple_framePrep_iff x P _).mp h s hs)

/-- **Prefix sharing, general `PostCond` form.** With the postcondition
conjunction `∧ₚ` of `Std.Do`, the single prefix triple discharges both
suffix triples (combined by conjunctivity of the predicate transformer), and
the composed program ends in a state satisfying both suffix
specifications. -/
theorem seqCaller_shared_prefix_postCond (v : Value) :
    ∃ s', (seqCallA >>= fun _ => seqCallB).run (seqStart v) = .ok () s' ∧
      s'.memory.activeCallee = some seqCaller ∧ s'.memory.callStack = [] := by
  have hT :
      Triple (seqCallA >>= fun _ => seqCallB) (fun s => ⌜s = seqStart v⌝)
        (seqPostActive ∧ₚ seqPostStack) :=
    wpFramePrep_duplicate_prefix seqCallA (fun _ => seqCallB)
      (seqCallA_triple_postCond v) (fun _ => seqCallB_triple v _ rfl)
      (fun _ => seqCallB_triple v _ rfl)
  obtain ⟨_, s', hRun, hQ₁, hQ₂⟩ :=
    triple_framePost_and_run hT (seqStart v) rfl
  exact ⟨s', hRun, hQ₁, hQ₂⟩

/-! ### Sequential composition of general four-stage calls -/

/-- A caller with two calls: a `&u8` callee whose entry retags its
parameter, then, after one bridge statement, the empty function. It keeps a
symbolic value in `_5` and returns it:
`bb0: { _1 = thin_ref_callee(copy _2) -> bb1 }`,
`bb1: { StorageLive(_6); _4 = empty() -> bb2 }`,
`bb2: { _0 = copy _5; return }`. -/
def mixedSeqCaller : CapturedMir :=
  { emptyFnCallerProt with
    defPath := "Anneal::FrameWpTests::mixed_seq_caller"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_1" },
      { mutability := .not, ty := thinRefU8Ty, debugName := some "_2" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_3" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_4" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_5" },
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_6" }]
    basicBlocks := [
      { statements := []
        terminator := {
          kind := .call thinOperand [.copy { local_ := 2, projection := [] }]
            destLocal1 (some 1) .continue_
          span := "call_thin" }
        isCleanup := false },
      { statements := [{ kind := .storageLive 6, span := "live_6" }]
        terminator := {
          kind := .call emptyFnOperand [] { local_ := 4, projection := [] }
            (some 2) .continue_
          span := "call_empty" }
        isCleanup := false },
      { statements := [
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.copy { local_ := 5, projection := [] }))
            span := "ret_copy" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false }] }

/-- Initial memory of `mixedSeqCaller`: both callees linked, the parent
borrow `1` and a sibling borrow `9` of the referent local `3`, and symbolic
tag and protector counters. -/
def mixedSeqMem (t n : Nat) : Memory :=
  { (initMachineStateWithCallees mixedSeqCaller []
      [thinRefCallee, emptyFnAssignUnit]).memory with
    borrows := [callerBorrow 1 .unique, callerBorrow 9 .unique]
    nextTag := t
    nextProtector := n }

/-- Initial state of `mixedSeqCaller` holding the symbolic value `v`. -/
def mixedSeqStart (t n : Nat) (v : Value) : MachineState :=
  PureState.toMachineState
    { bb := 0, stmtIdx := 0,
      env := [.uninit, .uninit, .init thinRefParentVal, .dead, .uninit,
        .init v, .dead] } (mixedSeqMem t n)

/-- Memory of `mixedSeqCaller` after its first call returned: the child
borrow remains, no protector is active, and both counters have advanced. -/
def mixedSeqResumedMem (t n : Nat) : Memory :=
  { mixedSeqMem t n with
    borrows :=
      [thinChildBorrow t n, callerBorrow 1 .unique, callerBorrow 9 .frozen]
    activeCallee := some mixedSeqCaller
    nextTag := t + 1
    nextProtector := n + 1 }

/-- `mixedSeqCaller` after its first call, at block `bb` and statement
`stmtIdx`, with the given storage states of `_4` and `_6`. -/
def mixedSeqAt (bb stmtIdx : Nat) (slot4 slot6 : LocalSlot) (t n : Nat)
    (v : Value) : MachineState :=
  PureState.toMachineState
    { bb := bb, stmtIdx := stmtIdx,
      env := [.uninit, .init .unit, .init thinRefParentVal, .dead, slot4,
        .init v, slot6] } (mixedSeqResumedMem t n)

/-- Stages 1 to 3 of the first call of `mixedSeqCaller`. -/
theorem mixedSeq_entry_and_stage3_run (t n : Nat) (v : Value) :
    (prepCallEntryStage3 mixedSeqCaller thinOperand
        [.copy { local_ := 2, projection := [] }] destLocal1 1 .continue_
        (prepFnEntryRetagThins thinRefCallee [1])).run (mixedSeqStart t n v) =
      .ok
        ⟨thinRefCallee, [thinRefParentVal],
          [.uninit, .uninit, .init thinRefParentVal, .dead, .uninit, .init v,
            .dead]⟩
        { frame := (thinRetagResult t n).frame
          memory :=
            { (thinRetagResult t n).memory with
              callees := (mixedSeqMem t n).callees
              callStack := [
                { callerBody := mixedSeqCaller
                  frame :=
                    { blockIdx := 0, stmtIdx := 0
                      locals := [.uninit, .uninit, .init thinRefParentVal,
                        .dead, .uninit, .init v, .dead] }
                  destination := destLocal1
                  returnTarget := 1 }] } } := rfl

/-- **Four-stage weakest precondition of the first call**, symbolic in the
counters and the kept value: it reduces to the continuation predicate at
the resumed state. -/
theorem mixedSeq_wp_call_thin (t n : Nat) (v : Value)
    (Q : MachineState → Prop) (hQ : Q (mixedSeqAt 1 0 .uninit .dead t n v)) :
    (wpFramePrepStage3 (thinTailContract mixedSeqCaller t n) mixedSeqCaller
      thinOperand [.copy { local_ := 2, projection := [] }] destLocal1 1
      .continue_ (prepFnEntryRetagThins thinRefCallee [1]) Q
      (mixedSeqStart t n v)).down :=
  (wpFramePrepStage3_iff _ _ _ _ _ _ _ _ _ _).mpr
    ⟨_, _, mixedSeq_entry_and_stage3_run t n v,
      ⟨rfl, rfl, rfl,
        forall_mem_three (fun h => by cases h) (fun h => by cases h)
          (fun h => by cases h)⟩,
      fun sRet retVal hPost _ _ => by
        rw [hPost.2]
        exact ⟨mixedSeqAt 1 0 .uninit .dead t n v, rfl, hQ⟩⟩

/-- **Four-stage weakest precondition of the second call**, whose callee has
no parameter to retag (the empty stage-3 pipeline): from block `bb1` at any
statement index and any storage state of `_6`, it reduces to the
continuation predicate at `bb2` with `()` written to `_4`. -/
theorem mixedSeq_wp_call_empty (stmtIdx : Nat) (slot6 : LocalSlot)
    (t n : Nat) (v : Value) (Q : MachineState → Prop)
    (hQ : Q (mixedSeqAt 2 0 (.init .unit) slot6 t n v)) :
    (wpFramePrepStage3 (emptyFnContract mixedSeqCaller) mixedSeqCaller
      emptyFnOperand [] { local_ := 4, projection := [] } 2 .continue_
      (pure ()) Q (mixedSeqAt 1 stmtIdx .uninit slot6 t n v)).down :=
  (wpFramePrepStage3_pure_iff _ _ _ _ _ _ _ _ _).mpr
    ((wpFramePrep_emptyFn_iff _ _ _ _ _ _ _ _ _).mpr
      ⟨⟨emptyFnAssignUnit, [],
          [.uninit, .init .unit, .init thinRefParentVal, .dead, .uninit,
            .init v, slot6]⟩, _, rfl,
        emptyFnEntry_of_pushCalleeFrame _ _ _ _ _ _ _ rfl,
        mixedSeqAt 2 0 (.init .unit) slot6 t n v, rfl, hQ⟩)

/-- Block `bb0` of `mixedSeqCaller`, as data. -/
def mixedSeqBlockA : BasicBlockData :=
  { statements := []
    terminator := {
      kind := .call thinOperand [.copy { local_ := 2, projection := [] }]
        destLocal1 (some 1) .continue_
      span := "call_thin" }
    isCleanup := false }

/-- Block `bb1` of `mixedSeqCaller`, as data. -/
def mixedSeqBlockB : BasicBlockData :=
  { statements := [{ kind := .storageLive 6, span := "live_6" }]
    terminator := {
      kind := .call emptyFnOperand [] { local_ := 4, projection := [] }
        (some 2) .continue_
      span := "call_empty" }
    isCleanup := false }

/-- The stage-3 execution of the first call of `mixedSeqCaller`: one trusted
step, by the syntactic stepping theorem of the thin pipeline. -/
theorem mixedSeq_stage3_steps (t n : Nat) (v : Value) (call : PreparedCall)
    (s₁ s₃ : MachineState)
    (hEntry : (prepCallEntry mixedSeqCaller thinOperand
      [.copy { local_ := 2, projection := [] }] destLocal1 1 .continue_).run
        (mixedSeqStart t n v) = .ok call s₁)
    (hS3 : (prepFnEntryRetagThins thinRefCallee [1]).run s₁ = .ok () s₃) :
    StepsTo mixedSeqCaller s₁ 1 s₃ ∧
      s₃.memory.callStack = s₁.memory.callStack := by
  have hRun :
      (prepCallEntry mixedSeqCaller thinOperand
        [.copy { local_ := 2, projection := [] }] destLocal1 1 .continue_).run
          (mixedSeqStart t n v) =
        .ok
          ⟨thinRefCallee, [thinRefParentVal],
            [.uninit, .uninit, .init thinRefParentVal, .dead, .uninit,
              .init v, .dead]⟩
          (pushCalleeFrame (mixedSeqStart t n v) mixedSeqCaller
            [.uninit, .uninit, .init thinRefParentVal, .dead, .uninit,
              .init v, .dead] destLocal1 1 thinRefCallee [thinRefParentVal]
            .continue_) := rfl
  rw [hRun] at hEntry
  obtain ⟨_, hS₁⟩ := EStateM.Result.ok.inj hEntry
  cases hS₁
  exact thinRetags_stepsTo_of_stmts (body := mixedSeqCaller)
    (cur := thinRefCallee) (blk := thinCalleeBlock) [1] rfl (Or.inl rfl) rfl
    (fun i loc hget => by
      cases i with
      | zero => cases hget; exact ⟨"fn_entry_thin_retag", rfl⟩
      | succ _ => cases hget)
    hS3

/-- **Sequential four-stage soundness with a bridge step**, symbolic in both
counters and in the kept value. The retagging call, the bridge statement
`StorageLive(_6)`, and the call to the empty function lift the caller from
its initial frame in `2 + 1 + 0 + 2 + 1 + 1 + 1 + 2` trusted steps, and it
returns the value kept in `_5`. -/
theorem mixedSeq_bridge_liftFrame (t n : Nat) (v : Value)
    (hv : valueContainsUninit v = false) :
    LiftFrame mixedSeqCaller 0 0
      [.uninit, .uninit, .init thinRefParentVal, .dead, .uninit, .init v,
        .dead]
      (mixedSeqMem t n) (fun r => r = v) (2 + 1 + 0 + 2 + 1 + 1 + 1 + 2) :=
  wpFramePrepStage3_seq_bridge_sound_stepMirFn (body := mixedSeqCaller)
    (cur := mixedSeqCaller) (blk₀ := mixedSeqBlockA)
    (blk₁' := mixedSeqBlockB) (bb₁' := 1) (stmtIdx₁' := 1)
    (stage3₂ := pure ())
    (Mid := fun s' => s' = mixedSeqAt 1 0 .uninit .dead t n v)
    (Q := fun s' => s' = mixedSeqAt 2 0 (.init .unit) .uninit t n v)
    (thinTailContract mixedSeqCaller t n) (emptyFnContract mixedSeqCaller)
    1 1 1 0 1 rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl
    (fun _ _ => Nat.le_refl 1) (fun _ _ => Nat.le_refl 1)
    (mixedSeq_wp_call_thin t n v _ rfl) (mixedSeq_stage3_steps t n v)
    (fun _ _ hMid =>
      ⟨[.uninit, .init .unit, .init thinRefParentVal, .dead, .uninit,
          .init v, .uninit], mixedSeqResumedMem t n,
        hMid ▸ StepsTo.single rfl, rfl,
        mixedSeq_wp_call_empty 1 .uninit t n v _ rfl,
        fun _ s₁ s₃ _ hS3 => by
          have hS3' :
              EStateM.Result.ok (ε := FramePrepFault) () s₁ = .ok () s₃ := hS3
          cases hS3'
          exact ⟨StepsTo.refl s₁, rfl⟩⟩)
    (fun _ _ hQ => by
      let env₀ : List LocalSlot :=
        [.uninit, .init .unit, .init thinRefParentVal, .dead, .init .unit,
          .init v, .uninit]
      let env₁ : List LocalSlot :=
        [.init v, .init .unit, .init thinRefParentVal, .dead, .init .unit,
          .init v, .uninit]
      let mem₀ : Memory := mixedSeqResumedMem t n
      let mem₁ : Memory :=
        { mem₀ with
          borrows := invalidateConflictingBorrows mem₀.borrows 0 .none 0 }
      let mem₂ : Memory :=
        { mem₁ with borrows := disableFrameBorrows mem₁.borrows 0 7 }
      have hEnd :
          LiftState mixedSeqCaller
            (mixedSeqAt 2 0 (.init .unit) .uninit t n v)
            (fun r => r = v) 2 := by
        refine
          LiftState.of_step
            (s' := { frame := { blockIdx := 2, stmtIdx := 1, locals := env₁ }
                     memory := mem₁ })
            ?_
            (LiftState.of_retNormal (mem' := mem₂) ?_ rfl)
        · have hRval :
              evalRvalue env₀ (.use (.copy { local_ := 5, projection := [] }))
                mem₀ mixedSeqCaller.localDecls emptyFnLayouts =
                .ok v env₀ mem₀ := by
            change
              (match
                match
                  match valueContainsUninit v with
                  | false => ProjReadResult.ok v
                  | true => ProjReadResult.ub
                with
                | .ok fieldVal => PlaceReadResult.ok fieldVal env₀
                | .ub => PlaceReadResult.ub
                | .unsupported => PlaceReadResult.unsupported
               with
               | .ok val locals' => RvalueEvalResult.ok val locals' mem₀
               | .ub => RvalueEvalResult.ub
               | .unsupported => RvalueEvalResult.unsupported) = _
            rw [hv]
          change
            (match
              evalRvalue env₀ (.use (.copy { local_ := 5, projection := [] }))
                mem₀ mixedSeqCaller.localDecls emptyFnLayouts
             with
             | .ok val locals₁ mem₁' => _
             | .ub => _
             | .unsupported => _) = _
          rw [hRval]
          rfl
        · change
            (match valueContainsUninit v with
             | true => MirStepNode.fail .ub
             | false => MirStepNode.retNormal v mem₂) = _
          rw [hv]
      exact liftState_iff_liftFrame.mp (hQ ▸ hEnd))

/-- **Two executable four-stage pipelines in sequence.** The nested
four-stage weakest precondition is a valid precondition of the two
pipelines composed with bind: started in the initial state, the retagging
call followed directly by the call to the empty function succeeds exactly
into the state at `bb2` (the caller's bridge statement is not part of the
composed program, so `_6` is still dead). -/
theorem mixedSeq_two_pipelines_run (t n : Nat) (v : Value) :
    (framePrepCallStage3 mixedSeqCaller (thinTailContract mixedSeqCaller t n)
        mixedSeqCaller thinOperand [.copy { local_ := 2, projection := [] }]
        destLocal1 1 .continue_
        (prepFnEntryRetagThins thinRefCallee [1]) >>= fun _ =>
      framePrepCallStage3 mixedSeqCaller (emptyFnContract mixedSeqCaller)
        mixedSeqCaller emptyFnOperand [] { local_ := 4, projection := [] } 2
        .continue_ (pure ())).run (mixedSeqStart t n v) =
      .ok () (mixedSeqAt 2 0 (.init .unit) .dead t n v) :=
  let ⟨_, hRun⟩ :=
    triple_framePost_run_eq
      (wpFramePrepStage3_seq (thinTailContract mixedSeqCaller t n)
        (emptyFnContract mixedSeqCaller) mixedSeqCaller mixedSeqCaller
        thinOperand emptyFnOperand
        [.copy { local_ := 2, projection := [] }] [] destLocal1
        { local_ := 4, projection := [] } 1 2 .continue_ .continue_
        (prepFnEntryRetagThins thinRefCallee [1]) (pure ())
        (fun s' => s' = mixedSeqAt 2 0 (.init .unit) .dead t n v))
      (mixedSeqStart t n v)
      (mixedSeq_wp_call_thin t n v _
        (mixedSeq_wp_call_empty 0 .dead t n v _ rfl))
  hRun

/-! ### Empty functions: the weakest precondition `EmptyFnEntry` -/

/-- Entry state of the empty function one frame deep whose borrow table
holds one stale disabled borrow of the callee's own `_0` (tag `tag`), under
an arbitrary list of active protectors. -/
def staleDisabledEntry (active : List Nat) (tag : Nat) : MachineState :=
  { emptyFnStaleEntry with
    memory :=
      { emptyFnStaleEntry.memory with
        borrows := [
          { tag := tag, targetLocal := 0, targetProjection := [],
            perm := .disabled, targetFrameDepth := 1, allocDead := true }]
        activeProtectors := active } }

/-- **Success path under protectors and stale borrows**, symbolic in the
active protectors and the stale tag: the entry state satisfies
`EmptyFnEntry`, so for every root body the trusted machine takes one silent
step to the explicit return-ready state, which is ready to return `()`. -/
theorem staleDisabledEntry_runs (body : CapturedMir) (active : List Nat)
    (tag : Nat) :
    EmptyFnEntry (staleDisabledEntry active tag) ∧
      stepMirFn body (staleDisabledEntry active tag) =
        MirStepNode.step (emptyFnReturnState (staleDisabledEntry active tag)) ∧
      ReturnReady body (emptyFnReturnState (staleDisabledEntry active tag))
        .unit := by
  have hEntry : EmptyFnEntry (staleDisabledEntry active tag) :=
    EmptyFnEntry.of_staleDisabled rfl rfl fun e he _ => by
      cases he with
      | head => rfl
      | tail _ he => cases he
  exact ⟨hEntry, emptyFn_step hEntry, emptyFn_returnReady hEntry⟩

/-- Entry state of the empty function one frame deep with a live `.unique`
borrow of the callee's own `_0` held under the active protector `7`. -/
def protectedLiveEntry : MachineState :=
  { emptyFnStaleEntry with
    memory :=
      { emptyFnStaleEntry.memory with
        borrows := [
          { tag := 4, targetLocal := 0, targetProjection := [],
            perm := .unique, protector := some 7, targetFrameDepth := 1 }] } }

/-- **Refutation: a protected live borrow of `_0` blocks the empty
function.** The write `_0 = const ()` conflicts with the protector, so the
trusted step is undefined behavior for every root body, and, because
`EmptyFnEntry` is exactly the condition under which the machine runs, the
state is not an `EmptyFnEntry`. -/
theorem protectedLiveEntry_not_emptyFnEntry (body : CapturedMir) :
    stepMirFn body protectedLiveEntry = MirStepNode.fail .ub ∧
      ¬ EmptyFnEntry protectedLiveEntry := by
  have hUb : stepMirFn body protectedLiveEntry = MirStepNode.fail .ub :=
    emptyFn_step_ub rfl rfl rfl
  refine ⟨hUb, fun hEntry => ?_⟩
  obtain ⟨sRet, hStep, _⟩ :=
    (emptyFnEntry_iff_runs (body := body) rfl rfl).mp hEntry
  have hNode : MirStepNode.fail .ub = MirStepNode.step sRet :=
    hUb.symm.trans hStep
  unfold MirStepNode.fail MirStepNode.step at hNode
  cases hNode

/-- **`EmptyFnEntry` is weaker than both sufficient conditions.** The
worked stale-borrow state runs on the trusted machine to a state ready to
return `()`, for every root body, although a protector is active and a
borrow targets the callee frame depth. -/
theorem emptyFnStaleEntry_runs (body : CapturedMir) :
    (∃ sRet, stepMirFn body emptyFnStaleEntry = MirStepNode.step sRet ∧
      ReturnReady body sRet .unit) ∧
    emptyFnStaleEntry.memory.activeProtectors ≠ [] ∧
    ¬ (∀ e, e ∈ emptyFnStaleEntry.memory.borrows →
      e.targetFrameDepth ≠ length emptyFnStaleEntry.memory.callStack) :=
  ⟨(emptyFnEntry_iff_runs rfl rfl).mp emptyFnEntry_stale_disabled_borrow.1,
    emptyFnEntry_stale_disabled_borrow.2⟩

/-- **Fresh callee frame**, for every entry state of the empty function in
which no borrow targets the callee frame depth, whatever protectors are
active: the state is an `EmptyFnEntry`, the trusted step reaches the
return-ready state, and that step leaves the borrow table unchanged. -/
theorem freshFrame_entry_runs_borrows_unchanged {body : CapturedMir}
    {s₀ : MachineState}
    (hCallee : s₀.memory.activeCallee = some emptyFnAssignUnit)
    (hFrame : s₀.frame = { blockIdx := 0, stmtIdx := 0, locals := [.uninit] })
    (hFresh : ∀ e, e ∈ s₀.memory.borrows →
      e.targetFrameDepth ≠ length s₀.memory.callStack) :
    stepMirFn body s₀ = MirStepNode.step (emptyFnReturnState s₀) ∧
      (emptyFnReturnState s₀).memory.borrows = s₀.memory.borrows :=
  ⟨emptyFn_step (EmptyFnEntry.of_freshFrame hCallee hFrame hFresh),
    emptyFnReturnState_borrows_eq_of_fresh_frame s₀ hFresh⟩

/-- **Call entry into the empty function from a protector-holding caller**,
for every caller state in which no borrow targets the new frame depth: the
pushed frame is an `EmptyFnEntry` and its return-ready state keeps the
caller's protectors active. -/
theorem pushed_empty_callee_fresh (s : MachineState)
    (callerBody : CapturedMir) (locals : List LocalSlot) (dest : Place)
    (targetBb : BasicBlockIdx) (unwind : UnwindAction)
    (hFresh : ∀ e, e ∈ s.memory.borrows →
      e.targetFrameDepth ≠ length s.memory.callStack + 1) :
    EmptyFnEntry
        (pushCalleeFrame s callerBody locals dest targetBb emptyFnAssignUnit
          [] unwind) ∧
      (emptyFnReturnState
          (pushCalleeFrame s callerBody locals dest targetBb
            emptyFnAssignUnit [] unwind)).memory.activeProtectors =
        s.memory.activeProtectors :=
  ⟨emptyFnEntry_of_pushCalleeFrame_fresh s callerBody locals dest targetBb []
      unwind hFresh, rfl⟩

/-- Function operand naming the direct-return empty function. -/
def directOperand : Operand :=
  .constant
    { ty := { kind := .fnDef emptyFnDirect.defPath [], layoutIdx := 0 }
      val := .zeroSized }

/-- `emptyFnCaller` at its call terminator, linked against the direct-return
empty function. -/
def callerAtDirectCall : MachineState :=
  { callerAtCall with
    memory := { callerAtCall.memory with callees := [emptyFnDirect] } }

/-- Call entry into the direct-return empty function succeeds: stages 1 and
2 do not inspect the callee body. -/
theorem callEntry_run_direct :
    (prepCallEntry emptyFnCaller directOperand [] destLocal1 1
        .continue_).run callerAtDirectCall =
      .ok ⟨emptyFnDirect, [], [.uninit, .uninit]⟩
        (pushCalleeFrame callerAtDirectCall emptyFnCaller [.uninit, .uninit]
          destLocal1 1 emptyFnDirect [] .continue_) := rfl

/-- **Refutation: the direct-return empty function has no `wpFramePrep`.**
For every contract and every continuation predicate, the weakest
precondition of the concrete call is false; the reason is visible on the
trusted machine, where the pushed frame is undefined behavior at its first
step, so the entry state satisfies no contract precondition. -/
theorem direct_return_callee_no_wpFramePrep
    (C : FramePrepContract emptyFnCaller) (Q : MachineState → Prop) :
    ¬ (wpFramePrep C emptyFnCaller directOperand [] destLocal1 1 .continue_ Q
        callerAtDirectCall).down ∧
      stepMirFn emptyFnCaller
          (pushCalleeFrame callerAtDirectCall emptyFnCaller
            [.uninit, .uninit] destLocal1 1 emptyFnDirect [] .continue_) =
        MirStepNode.fail .ub ∧
      ¬ C.Pre
        (pushCalleeFrame callerAtDirectCall emptyFnCaller [.uninit, .uninit]
          destLocal1 1 emptyFnDirect [] .continue_) :=
  ⟨wpFramePrep_empty_function_direct_ub C emptyFnCaller directOperand []
      destLocal1 1 .continue_ Q callerAtDirectCall fun call s₁ h => by
        rw [callEntry_run_direct] at h
        obtain ⟨hCall, _⟩ := EStateM.Result.ok.inj h
        rw [← hCall],
    emptyFnDirect_entry_ub rfl rfl, emptyFnDirect_not_contract_pre C rfl rfl⟩

/-- **Symbolic teardown of an empty-function call from a borrow-free
caller**, for every caller state without borrows, every caller body, every
live destination slot, and whatever protectors are active: stage 4 writes
`()` to `_1`, resumes the caller at `targetBb`, and changes nothing else. -/
theorem teardown_empty_fn_borrow_free (s : MachineState)
    (callerBody : CapturedMir) (slot : LocalSlot) (hLive : slot ≠ .dead)
    (targetBb : BasicBlockIdx) (hNoBorrows : s.memory.borrows = []) :
    prepTeardownAndWriteback.run
        (emptyFnReturnState
          (pushCalleeFrame s callerBody [.uninit, slot] destLocal1 targetBb
            emptyFnAssignUnit [] .continue_)) =
      .ok ()
        (PureState.toMachineState
          { bb := targetBb, stmtIdx := 0, env := [.uninit, .init .unit] }
          { s.memory with activeCallee := some callerBody }) :=
  (prepTeardownAndWriteback_emptyFn_local s callerBody [.uninit, slot]
    [.uninit, .init .unit] 1 targetBb [] .continue_ slot
    (fun e he => by rw [hNoBorrows] at he; cases he) rfl hLive
    (by rw [hNoBorrows]; rfl) rfl).trans
    (congrArg
      (fun borrows =>
        EStateM.Result.ok (ε := FramePrepFault) ()
          (PureState.toMachineState
            { bb := targetBb, stmtIdx := 0, env := [.uninit, .init .unit] }
            { s.memory with
              borrows := borrows, activeCallee := some callerBody }))
      (show invalidateConflictingBorrows s.memory.borrows 1 .none
          (length s.memory.callStack) = s.memory.borrows by
        rw [hNoBorrows]; rfl))

/-! ### Limits of the contract layer -/

/-- A callee that branches on its argument:
`bb0: { switchInt(copy _1) -> [0: bb1, otherwise: bb1] }`,
`bb1: { _0 = const (); return }`. -/
def branchCallee : CapturedMir :=
  { thinRefCallee with
    defPath := "Anneal::FrameWpTests::branch_callee"
    localDecls := [
      { mutability := .mut, ty := emptyFnUnitTy, debugName := some "_0" },
      { mutability := .not, ty := emptyFnUnitTy, debugName := some "_1" }]
    basicBlocks := [
      { statements := []
        terminator := {
          kind := .switchInt (.copy { local_ := 1, projection := [] })
            { branches := [(0, 1)], otherwise := 1 }
          span := "switch" }
        isCleanup := false },
      { statements := [
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
            span := "unit" }]
        terminator := { kind := .return_, span := "ret" }
        isCleanup := false }] }

/-- Entry state of `branchCallee` holding the scalar `bits` in `_1`. -/
def branchEntry (bits : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨bits, 1⟩)] }
    memory := { activeCallee := some branchCallee } }

/-- The trusted machine reports a `switchInt` as a visible branch event: its
step is not a silent step, for every scrutinee. -/
theorem branchEntry_step_is_event (body : CapturedMir) (bits : Nat) :
    stepMirFn body (branchEntry bits) =
      MirStepNode.emitStep (.event bits)
        { branchEntry bits with
          frame :=
            { (branchEntry bits).frame with
              blockIdx := lookupSwitchTarget bits [(0, 1)] 1 } } := rfl

/-- **Refutation: contracts cover silent callee executions only.** A callee
contract promises a silent execution up to a return-ready state. At a state
about to execute a `switchInt` the machine can take no silent step and is
not at a `return_`, so no contract precondition holds there, for every
contract, root body, and scrutinee. -/
theorem no_contract_at_switchInt {body : CapturedMir}
    (C : FramePrepContract body) (bits : Nat) : ¬ C.Pre (branchEntry bits) := by
  intro hPre
  obtain ⟨sRet, retVal, hSteps, hReady, _, _⟩ := C.exec _ hPre
  generalize C.steps (branchEntry bits) = k at hSteps
  cases hSteps with
  | refl =>
    obtain ⟨cur, blk, hCur, _, hBb, _, hTerm, _, _⟩ := hReady
    have hCur' : branchCallee = cur := hCur
    cases hCur'
    have hBb' :
        some
            ({ statements := []
               terminator := {
                 kind := .switchInt (.copy { local_ := 1, projection := [] })
                   { branches := [(0, 1)], otherwise := 1 }
                 span := "switch" }
               isCleanup := false } : BasicBlockData) = some blk := hBb
    cases hBb'
    cases hTerm
  | step hStep _ =>
    rw [branchEntry_step_is_event] at hStep
    unfold MirStepNode.emitStep MirStepNode.step at hStep
    cases hStep

/-- **Stage 3 fails closed on an untracked thin reference.** A `&u8` whose
pointer has no borrow-table entry is rejected by the unified retag stage
with `.unsupported`, while the trusted `stepMirFn` reports undefined
behavior: on this path the stage is fail-closed and not exact, for all
counters. -/
theorem untrackedThinRef_retag_fails_closed (t n : Nat) :
    (prepFnEntryRetagAny thinRefCallee 1).run (thinRetagEntry t n []) =
        .error (FailReq.fail .unsupported) (thinRetagEntry t n []) ∧
      stepMirFn thinRefCaller (thinRetagEntry t n []) =
        MirStepNode.fail .ub :=
  ⟨rfl, rfl⟩

/-! ### The empty-function rules on a protector-holding caller -/

/-- Protected borrow of a caller-owned referent outside the frame, held
under the active protector `p`. -/
def farProtectedBorrow (p : Nat) : BorrowEntry :=
  { tag := 1, targetLocal := 9, targetProjection := [], perm := .unique,
    protector := some p }

/-- Stale disabled borrow of an earlier callee frame at depth `1`. -/
def staleCalleeBorrow : BorrowEntry :=
  { tag := 5, targetLocal := 0, targetProjection := [], perm := .disabled,
    targetFrameDepth := 1, allocDead := true }

/-- Memory of `seqCaller` before its third call, holding the protected
borrow under the symbolic active protector `p`, preceded by `stale`. -/
def seqProtMem (p : Nat) (stale : List BorrowEntry) : Memory :=
  { seqResumedMem with
    borrows :=
      match stale with
      | [] => [farProtectedBorrow p]
      | e :: _ => [e, farProtectedBorrow p]
    activeProtectors := [p]
    nextTag := 2
    nextProtector := p + 1 }

/-- Locals of `seqCaller` at its third call, holding `v` in `_2`. -/
def seqEnvAtC (v : Value) : List LocalSlot :=
  [.uninit, .init .unit, .init v, .uninit]

/-- **The protector-compatible rules on a fresh callee frame**, symbolic in
the kept value and the active protector: the third call of `seqCaller`
lifts by the rule with an explicit teardown state and, for a second
postcondition, by the fully symbolic rule. The caller's protector stays
active across the call and the caller returns `v`. -/
private theorem seqCaller_bb3_prot_liftFrame (v : Value) (p : Nat)
    (useStale : Bool) (post : Value → Prop)
    (hv : valueContainsUninit v = false) (hPost : post v) :
    LiftFrame seqCaller 3 0 [.uninit, .init .unit, .init v, .init .unit]
      { (seqProtMem p (if useStale then [staleCalleeBorrow] else [])) with
        borrows :=
          disableFrameBorrows
            (seqProtMem p
              (if useStale then [staleCalleeBorrow] else [])).borrows
            1 1
        activeCallee := some seqCaller }
      post 2 := by
  let mem₀ : Memory :=
    { (seqProtMem p (if useStale then [staleCalleeBorrow] else [])) with
      borrows :=
        disableFrameBorrows
          (seqProtMem p
            (if useStale then [staleCalleeBorrow] else [])).borrows
          1 1
      activeCallee := some seqCaller }
  let mem₁ : Memory :=
    { mem₀ with borrows := invalidateConflictingBorrows mem₀.borrows 0 .none 0 }
  let mem₂ : Memory :=
    { mem₁ with borrows := disableFrameBorrows mem₁.borrows 0 4 }
  refine liftState_iff_liftFrame.mp
    (LiftState.of_step
      (s' :=
        { frame :=
            { blockIdx := 3, stmtIdx := 1,
              locals := [.init v, .init .unit, .init v, .init .unit] }
          memory := mem₁ })
      ?_
      (LiftState.of_retNormal (mem' := mem₂) ?_ hPost))
  · have hRval :
        evalRvalue [.uninit, .init .unit, .init v, .init .unit]
          (.use (.copy { local_ := 2, projection := [] })) mem₀
          seqCaller.localDecls emptyFnLayouts =
          .ok v [.uninit, .init .unit, .init v, .init .unit] mem₀ := by
      change
        (match
          match
            match valueContainsUninit v with
            | false => ProjReadResult.ok v
            | true => ProjReadResult.ub
          with
          | .ok fieldVal =>
            PlaceReadResult.ok fieldVal
              [.uninit, .init .unit, .init v, .init .unit]
          | .ub => PlaceReadResult.ub
          | .unsupported => PlaceReadResult.unsupported
         with
         | .ok val locals' => RvalueEvalResult.ok val locals' mem₀
         | .ub => RvalueEvalResult.ub
         | .unsupported => RvalueEvalResult.unsupported) = _
      rw [hv]
    cases useStale
    · change
        (match
          evalRvalue [.uninit, .init .unit, .init v, .init .unit]
            (.use (.copy { local_ := 2, projection := [] })) mem₀
            seqCaller.localDecls emptyFnLayouts
         with
         | .ok val locals₁ mem₁' => _
         | .ub => _
         | .unsupported => _) = _
      rw [hRval]
      rfl
    · change
        (match
          evalRvalue [.uninit, .init .unit, .init v, .init .unit]
            (.use (.copy { local_ := 2, projection := [] })) mem₀
            seqCaller.localDecls emptyFnLayouts
         with
         | .ok val locals₁ mem₁' => _
         | .ub => _
         | .unsupported => _) = _
      rw [hRval]
      rfl
  · cases useStale
    · change
        (match valueContainsUninit v with
         | true => MirStepNode.fail .ub
         | false => MirStepNode.retNormal v mem₂) = _
      rw [hv]
    · change
        (match valueContainsUninit v with
         | true => MirStepNode.fail .ub
         | false => MirStepNode.retNormal v mem₂) = _
      rw [hv]

theorem seqCaller_call_c_protected (v : Value) (p : Nat)
    (hv : valueContainsUninit v = false) :
    LiftFrame seqCaller 2 1 (seqEnvAtC v) (seqProtMem p []) (fun r => r = v)
        (2 + 3) ∧
      LiftFrame seqCaller 2 1 (seqEnvAtC v) (seqProtMem p [])
        (fun r => v = .unit → r = .unit) (2 + 3) := by
  have hFresh :
      ∀ e, e ∈ (seqProtMem p []).borrows →
        e.targetFrameDepth ≠ length (seqProtMem p []).callStack + 1 := by
    intro e he
    cases he with
    | head => intro h; cases h
    | tail _ he => cases he
  constructor
  · exact wpFramePrep_empty_function_protected (body := seqCaller)
      (cur := seqCaller) (blk := seqBlockC)
      (call := ⟨emptyFnAssignUnit, [], seqEnvAtC v⟩)
      (s' := PureState.toMachineState
        { bb := 3, stmtIdx := 0,
          env := [.uninit, .init .unit, .init v, .init .unit] }
        (seqProtMem p []))
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl hFresh rfl
      (fun _ _ h =>
        liftState_iff_liftFrame.mp
          (h ▸ liftState_iff_liftFrame.mpr
            (seqCaller_bb3_prot_liftFrame v p false _ hv rfl)))
  · exact wpFramePrep_empty_function_symbolic (body := seqCaller)
      (cur := seqCaller) (blk := seqBlockC)
      (call := ⟨emptyFnAssignUnit, [], seqEnvAtC v⟩) (slot := .uninit)
      (updatedCallerLocals :=
        [.uninit, .init .unit, .init v, .init .unit])
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl hFresh rfl (fun h => by cases h)
      rfl rfl
      (seqCaller_bb3_prot_liftFrame v p false _ hv fun h => h)

/-- **The weakest-precondition rules with a stale borrow under an active
protector**, symbolic in the kept value and the protector: neither "no
active protector" nor "no borrow at the callee depth" holds, yet the third
call of `seqCaller` lifts by the weakest-precondition rule with an explicit
teardown state and, for a second postcondition, by its fully symbolic
form. -/
theorem seqCaller_call_c_stale (v : Value) (p : Nat)
    (hv : valueContainsUninit v = false) :
    LiftFrame seqCaller 2 1 (seqEnvAtC v) (seqProtMem p [staleCalleeBorrow])
        (fun r => r = v) (2 + 3) ∧
      LiftFrame seqCaller 2 1 (seqEnvAtC v)
        (seqProtMem p [staleCalleeBorrow]) (fun r => v = .unit → r = .unit)
        (2 + 3) := by
  constructor
  · exact wpFramePrep_empty_function_wp (body := seqCaller)
      (cur := seqCaller) (blk := seqBlockC)
      (call := ⟨emptyFnAssignUnit, [], seqEnvAtC v⟩)
      (s' := PureState.toMachineState
        { bb := 3, stmtIdx := 0,
          env := [.uninit, .init .unit, .init v, .init .unit] }
        { (seqProtMem p [staleCalleeBorrow]) with
          borrows :=
            disableFrameBorrows (seqProtMem p [staleCalleeBorrow]).borrows 1 1
          activeCallee := some seqCaller })
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl
      (fun _ _ h =>
        liftState_iff_liftFrame.mp
          (h ▸ liftState_iff_liftFrame.mpr
            (seqCaller_bb3_prot_liftFrame v p true _ hv rfl)))
  · exact wpFramePrep_empty_function_symbolic_wp (body := seqCaller)
      (cur := seqCaller) (blk := seqBlockC)
      (call := ⟨emptyFnAssignUnit, [], seqEnvAtC v⟩) (slot := .uninit)
      (updatedCallerLocals :=
        [.uninit, .init .unit, .init v, .init .unit])
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl rfl rfl rfl (fun h => by cases h)
      rfl rfl
      (seqCaller_bb3_prot_liftFrame v p true _ hv fun h => h)

/-! ### Frame teardown and root-level pruning of the borrow forest -/

/-- **Return readiness from a fresh frame**, for every body and state at a
`return_` terminator whose return place is initialized: if no borrow
targets the frame's depth, deallocating the frame conflicts with no
protector (whatever protectors are active), so the state is return-ready,
and the teardown's borrow update is the identity. -/
theorem returnReady_of_fresh_frame {body cur : CapturedMir}
    {blk : BasicBlockData} {s : MachineState} {retVal : Value}
    (hCur : s.memory.activeCallee.getD body = cur)
    (hPhase : cur.phase = .runtimePostCleanup ∨ cur.phase = .runtimeOptimized)
    (hBb : get? cur.basicBlocks s.frame.blockIdx = some blk)
    (hEnd : s.frame.stmtIdx = length blk.statements)
    (hTerm : blk.terminator.kind = .return_)
    (hRet : get? s.frame.locals 0 = some (.init retVal))
    (hFresh : ∀ e, e ∈ s.memory.borrows →
      e.targetFrameDepth ≠ length s.memory.callStack) :
    ReturnReady body s retVal ∧
      disableFrameBorrows s.memory.borrows (length s.memory.callStack)
        (length s.frame.locals) = s.memory.borrows :=
  ⟨⟨cur, blk, hCur, hPhase, hBb, hEnd, hTerm, hRet,
      hasFrameDeallocProtectorConflict_unrelated_frame _ _ _ _ hFresh⟩,
    disableFrameBorrows_unrelated_frame _ _ _ hFresh⟩

/-- Tearing down the same frame twice is tearing it down once, in the
per-entry form of the trusted `disableFrameBorrows`: the torn-down table is
a fixed point of the per-entry update. -/
theorem disableFrameBorrows_map_fixed (borrows : List BorrowEntry)
    (depth nLocals : Nat) :
    (disableFrameBorrows borrows depth nLocals).map
        (disableFrameBorrowEntry depth nLocals) =
      disableFrameBorrows borrows depth nLocals := by
  rw [← disableFrameBorrows_eq_map, disableFrameBorrows_idem]

/-- A torn-down frame can be torn down again without a protector conflict:
on the two-node witness table every entry of frame `(0, 1)` is disabled by
the teardown, and disabled borrows never block deallocation, whatever
protectors are active and whatever permission the child had. -/
theorem tornDown_witness_no_dealloc_conflict (perm : TreeBorrowPerm)
    (active : List Nat) :
    disableFrameBorrows (cexBorrows perm) 0 1 =
        [{ cexFrozenRoot with perm := .disabled, allocDead := true },
          { cexChild perm with perm := .disabled, allocDead := true }] ∧
      hasFrameDeallocProtectorConflict
          (disableFrameBorrows (cexBorrows perm) 0 1) active 0 1 = false := by
  refine ⟨rfl, ?_⟩
  rw [hasFrameDeallocProtectorConflict_eq_any]
  rfl

/-- After a pruned teardown, the forest is still structurally well formed
against its own flattening, so every pruned traversal remains applicable. -/
theorem tornDown_sameAlloc {forest : BorrowForest}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (depth nLocals : Nat) :
    SameAllocForest
      (BorrowForest.toList (pruneDisableFrameBorrows forest depth nLocals))
      (pruneDisableFrameBorrows forest depth nLocals) := by
  rw [pruneDisableFrameBorrows_equiv_fullScan hAlloc]
  exact pruneDisableFrameBorrows_preserves_sameAlloc hAlloc depth nLocals

/-- **Pruned teardown is idempotent on the flattened table**, for every
structurally well-formed forest: a second pruned teardown of the same frame
changes nothing. -/
theorem pruneDisableFrameBorrows_toList_idem {forest : BorrowForest}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (depth nLocals : Nat) :
    BorrowForest.toList
        (pruneDisableFrameBorrows
          (pruneDisableFrameBorrows forest depth nLocals) depth nLocals) =
      BorrowForest.toList (pruneDisableFrameBorrows forest depth nLocals) := by
  rw [pruneDisableFrameBorrows_equiv_fullScan
      (tornDown_sameAlloc hAlloc depth nLocals),
    pruneDisableFrameBorrows_equiv_fullScan hAlloc, disableFrameBorrows_idem]

/-- **Teardown neither mints tags nor touches protectors.** The pruned
teardown keeps the number of entries, and a forest in which no entry
carries a protector stays protector-free. -/
theorem pruneDisableFrameBorrows_length_and_protectors (forest : BorrowForest)
    (depth nLocals : Nat) :
    (BorrowForest.toList
        (pruneDisableFrameBorrows forest depth nLocals)).length =
        (BorrowForest.toList forest).length ∧
      ((∀ e, e ∈ BorrowForest.toList forest → e.protector = none) →
        ∀ e, e ∈ BorrowForest.toList
            (pruneDisableFrameBorrows forest depth nLocals) →
          e.protector = none) := by
  refine ⟨?_, fun hNone e he => ?_⟩
  · have h := congrArg List.length
      (pruneDisableFrameBorrows_preserves_tags forest depth nLocals)
    rw [List.length_map, List.length_map] at h
    exact h
  · have hMem :
        e.protector ∈
          (BorrowForest.toList
            (pruneDisableFrameBorrows forest depth nLocals)).map
              BorrowEntry.protector := List.mem_map_of_mem he
    rw [pruneDisableFrameBorrows_preserves_protectors] at hMem
    obtain ⟨e₀, he₀, hEq⟩ := List.mem_map.mp hMem
    rw [← hEq]
    exact hNone e₀ he₀

/-- **The pruned deallocation-conflict check stays exact across a
teardown**, under the `.disabled`-subtree invariant: on the torn-down forest
it equals the trusted full scan of the torn-down table. -/
theorem pruned_dealloc_check_after_teardown {forest : BorrowForest}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (hDis : DisabledClosedForest forest) (active : List Nat)
    (depth nLocals depth' nLocals' : Nat) :
    pruneHasFrameDeallocProtectorConflict
        (pruneDisableFrameBorrows forest depth nLocals) active depth'
        nLocals' =
      hasFrameDeallocProtectorConflict
        (disableFrameBorrows (BorrowForest.toList forest) depth nLocals)
        active depth' nLocals' := by
  rw [pruneHasFrameDeallocProtectorConflict_equiv_fullScan
      (tornDown_sameAlloc hAlloc depth nLocals)
      (pruneDisableFrameBorrows_preserves_disabledClosed hAlloc hDis depth
        nLocals),
    pruneDisableFrameBorrows_equiv_fullScan hAlloc]

/-- The same exactness under the cell-aware root-noop invariant, which
survives `.cell` children below disabled roots. -/
theorem pruned_dealloc_check_after_teardown_rootNoop {forest : BorrowForest}
    {active : List Nat}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (hWrite : DisabledRootWriteNoopForest active forest)
    (depth nLocals depth' nLocals' : Nat) :
    pruneHasFrameDeallocProtectorConflict
        (pruneDisableFrameBorrows forest depth nLocals) active depth'
        nLocals' =
      hasFrameDeallocProtectorConflict
        (disableFrameBorrows (BorrowForest.toList forest) depth nLocals)
        active depth' nLocals' := by
  rw [pruneHasFrameDeallocProtectorConflict_rootNoop_equiv_fullScan
      (tornDown_sameAlloc hAlloc depth nLocals)
      (pruneDisableFrameBorrows_preserves_disabledRootWriteNoop hAlloc hWrite
        depth nLocals),
    pruneDisableFrameBorrows_equiv_fullScan hAlloc]

/-- **The pruned protected-write check stays exact across a teardown**,
under the foreign-write no-op invariant: the write of a return value into
the caller can use the pruned scan on the torn-down forest. -/
theorem pruned_write_check_after_teardown {forest : BorrowForest}
    {active : List Nat}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (hNoop : ForeignWriteNoopForest active forest) (depth nLocals : Nat)
    (targetLocal : Local) (writerTag : Option Nat) (targetFrameDepth : Nat) :
    pruneHasProtectedWriteConflict
        (BorrowForest.toList (pruneDisableFrameBorrows forest depth nLocals))
        (pruneDisableFrameBorrows forest depth nLocals) active targetLocal
        writerTag .nil 0 0 targetFrameDepth =
      hasProtectedWriteConflict
        (disableFrameBorrows (BorrowForest.toList forest) depth nLocals)
        active targetLocal writerTag .nil 0 0 targetFrameDepth := by
  rw [pruneHasProtectedWriteConflict_equiv_fullScan
      (tornDown_sameAlloc hAlloc depth nLocals)
      (pruneDisableFrameBorrows_preserves_foreignWriteNoop hAlloc hNoop depth
        nLocals),
    pruneDisableFrameBorrows_equiv_fullScan hAlloc]

/-! ### Stage 3 after stage 4: the pruned retag reads on a torn-down forest -/

/-- Exactness of the pruned read checks of a thin function-entry retag on
`forest`: the trusted read-UB scan and read-freeze performed by
`prepFnEntryRetagThin` agree with the root-level pruned traversals. -/
def RetagReadPruningExact (active : List Nat) (forest : BorrowForest) : Prop :=
  ∀ (parent : BorrowEntry) (ptrTag : Nat),
    hasTreeReadUB (BorrowForest.toList forest) (BorrowForest.toList forest)
        active parent.targetLocal (.some ptrTag) parent.targetProjection
        parent.rangeOffset parent.rangeLen parent.targetFrameDepth =
      pruneHasTreeReadUB (BorrowForest.toList forest) forest active
        parent.targetLocal (.some ptrTag) parent.targetProjection
        parent.rangeOffset parent.rangeLen parent.targetFrameDepth ∧
    freezeTreeBorrowsOnReadAtProj (BorrowForest.toList forest)
        (BorrowForest.toList forest) parent.targetLocal (.some ptrTag)
        parent.targetProjection parent.rangeOffset parent.rangeLen active
        parent.targetFrameDepth =
      BorrowForest.toList
        (pruneForeignRead (BorrowForest.toList forest) forest
          parent.targetLocal (.some ptrTag) parent.targetProjection
          parent.rangeOffset parent.rangeLen active parent.targetFrameDepth)

/-- The same exactness for the conservative traversals that skip only
unrelated, `.frozen`, and `.disabled` roots. -/
def RetagReadPruningExactConservative (active : List Nat)
    (forest : BorrowForest) : Prop :=
  ∀ (parent : BorrowEntry) (ptrTag : Nat),
    hasTreeReadUB (BorrowForest.toList forest) (BorrowForest.toList forest)
        active parent.targetLocal (.some ptrTag) parent.targetProjection
        parent.rangeOffset parent.rangeLen parent.targetFrameDepth =
      pruneHasTreeReadUBFrozenOrDisabled (BorrowForest.toList forest) forest
        active parent.targetLocal (.some ptrTag) parent.targetProjection
        parent.rangeOffset parent.rangeLen parent.targetFrameDepth ∧
    freezeTreeBorrowsOnReadAtProj (BorrowForest.toList forest)
        (BorrowForest.toList forest) parent.targetLocal (.some ptrTag)
        parent.targetProjection parent.rangeOffset parent.rangeLen active
        parent.targetFrameDepth =
      BorrowForest.toList
        (pruneForeignReadFrozenOrDisabled (BorrowForest.toList forest) forest
          parent.targetLocal (.some ptrTag) parent.targetProjection
          parent.rangeOffset parent.rangeLen active parent.targetFrameDepth)

/-- **The pruned retag reads survive a frame teardown**, under the
foreign-read no-op invariant: after stage 4 tears a frame down by the pruned
traversal, stage 3 of the next call can use the pruned read-UB check and
read-freeze on the resulting forest. -/
theorem retagReadPruning_after_teardown {forest : BorrowForest}
    {active : List Nat}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (hNoop : ForeignReadNoopForest active forest) (depth nLocals : Nat) :
    RetagReadPruningExact active
      (pruneDisableFrameBorrows forest depth nLocals) :=
  fun parent ptrTag =>
    prepFnEntryRetagThin_pruned_borrows
      (tornDown_sameAlloc hAlloc depth nLocals)
      (pruneDisableFrameBorrows_preserves_foreignReadNoop hAlloc hNoop depth
        nLocals)
      parent ptrTag

/-- The conservative pruned retag reads survive a frame teardown under the
classical `.disabled`- and `.frozen`-subtree invariants, for every list of
active protectors. -/
theorem retagReadPruning_conservative_after_teardown {forest : BorrowForest}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (hDis : DisabledClosedForest forest) (hFrz : FrozenClosedForest forest)
    (active : List Nat) (depth nLocals : Nat) :
    RetagReadPruningExactConservative active
      (pruneDisableFrameBorrows forest depth nLocals) :=
  fun parent ptrTag =>
    prepFnEntryRetagThin_pruned_borrows_conservative
      (tornDown_sameAlloc hAlloc depth nLocals)
      (pruneDisableFrameBorrows_preserves_disabledClosed hAlloc hDis depth
        nLocals)
      (pruneDisableFrameBorrows_preserves_frozenClosed hAlloc hFrz depth
        nLocals)
      parent ptrTag

/-- The conservative pruned retag reads survive a frame teardown under the
cell-aware root-noop invariant. -/
theorem retagReadPruning_rootNoop_after_teardown {forest : BorrowForest}
    {active : List Nat}
    (hAlloc : SameAllocForest (BorrowForest.toList forest) forest)
    (hRead : FrozenOrDisabledRootReadNoopForest active forest)
    (depth nLocals : Nat) :
    RetagReadPruningExactConservative active
      (pruneDisableFrameBorrows forest depth nLocals) :=
  fun parent ptrTag =>
    prepFnEntryRetagThin_pruned_borrows_rootNoop
      (tornDown_sameAlloc hAlloc depth nLocals)
      (pruneDisableFrameBorrows_preserves_frozenOrDisabledRootReadNoop hAlloc
        hRead depth nLocals)
      parent ptrTag

/-- The two-node witness table after tearing down frame `(0, 1)`. -/
def tornDownFrozenTable : List BorrowEntry :=
  [{ cexFrozenRoot with perm := .disabled, allocDead := true },
    { cexChild .frozen with perm := .disabled, allocDead := true }]

/-- **Concrete witness: teardown, then the pruned retag reads.** On the
two-node witness forest (a `.frozen` root with a `.frozen` child), the
pruned teardown of frame `(0, 1)` flattens to the fully disabled table. A
reference into that torn-down frame is dangling: the pruned read-UB check of
a retag through tag `1` reports undefined behavior, and the pruned
read-freeze changes nothing. Both values are computed through the exactness
theorem from the trusted full scans. -/
theorem tornDown_witness_retag_reads :
    BorrowForest.toList (pruneDisableFrameBorrows (cexForestOf .frozen) 0 1) =
        tornDownFrozenTable ∧
      pruneHasTreeReadUB tornDownFrozenTable
          (pruneDisableFrameBorrows (cexForestOf .frozen) 0 1) [] 0 (some 1)
          [] 0 0 0 = true ∧
      BorrowForest.toList
          (pruneForeignRead tornDownFrozenTable
            (pruneDisableFrameBorrows (cexForestOf .frozen) 0 1) 0 (some 1)
            [] 0 0 [] 0) = tornDownFrozenTable := by
  have hAlloc :
      SameAllocForest (BorrowForest.toList (cexForestOf .frozen))
        (cexForestOf .frozen) := by
    rw [cexForestOf_toList]
    exact cexForestOf_sameAlloc .frozen
  have hTable :
      BorrowForest.toList
          (pruneDisableFrameBorrows (cexForestOf .frozen) 0 1) =
        tornDownFrozenTable := by
    rw [pruneDisableFrameBorrows_equiv_fullScan hAlloc, cexForestOf_toList]
    rfl
  have hExact :=
    retagReadPruning_after_teardown hAlloc cexForestOf_frozen_readNoop 0 1
      cexFrozenRoot 1
  rw [hTable] at hExact
  exact ⟨hTable, hExact.1.symm.trans rfl, hExact.2.symm.trans rfl⟩

/-- The `.unique`-over-`.cell` witness forest satisfies the foreign-write
no-op invariant: its `.unique` root is not a write no-op, and its `.cell`
leaf has no descendants. -/
theorem uniqueCellForest_foreignWriteNoop :
    ForeignWriteNoopForest [] cexUniqueCellForest := by
  unfold ForeignWriteNoopForest cexUniqueCellForest
  exact AllSubtreesForest.cons_iff.mpr
    ⟨AllSubtrees.node_iff.mpr ⟨fun h => (by cases h),
      AllSubtreesForest.cons_iff.mpr
        ⟨AllSubtrees.node_iff.mpr ⟨fun _ e he => (by
            rw [BorrowForest.toList_nil] at he
            cases he),
          AllSubtreesForest.nil_iff.mpr True.intro⟩,
         AllSubtreesForest.nil_iff.mpr True.intro⟩⟩,
     AllSubtreesForest.nil_iff.mpr True.intro⟩

/-- **Concrete witness: every pruned check stays exact after a teardown.**
On the `.unique`-over-`.cell` witness forest, torn down at frame `(0, 1)`:
the pruned deallocation-conflict check agrees with the trusted scan under
both the `.disabled`-subtree and the root-noop invariants and reports no
conflict for every list of active protectors; the pruned protected-write
check agrees with the trusted scan; and the conservative pruned retag reads
are exact under both invariant families. -/
theorem tornDown_uniqueCell_checks (active : List Nat) :
    pruneHasFrameDeallocProtectorConflict
        (pruneDisableFrameBorrows cexUniqueCellForest 0 1) active 0 1 =
        false ∧
      pruneHasFrameDeallocProtectorConflict
          (pruneDisableFrameBorrows cexUniqueCellForest 0 1) [] 0 1 =
        hasFrameDeallocProtectorConflict
          (disableFrameBorrows cexUniqueCellBorrows 0 1) [] 0 1 ∧
      pruneHasProtectedWriteConflict
          (BorrowForest.toList
            (pruneDisableFrameBorrows cexUniqueCellForest 0 1))
          (pruneDisableFrameBorrows cexUniqueCellForest 0 1) [] 0 none [] 0 0
          0 =
        hasProtectedWriteConflict
          (disableFrameBorrows cexUniqueCellBorrows 0 1) [] 0 none [] 0 0 0 ∧
      RetagReadPruningExactConservative active
        (pruneDisableFrameBorrows cexUniqueCellForest 0 1) ∧
      RetagReadPruningExactConservative []
        (pruneDisableFrameBorrows cexUniqueCellForest 0 1) := by
  have hInv := cexUniqueCellForest_preserves_rootNoop_invariants
  have hClosed := unique_root_cell_child_breaks_disabledClosed_and_frozenClosed
  have hAlloc :
      SameAllocForest (BorrowForest.toList cexUniqueCellForest)
        cexUniqueCellForest := hInv.1
  refine ⟨?_, pruned_dealloc_check_after_teardown_rootNoop hAlloc hInv.2.1 0
      1 0 1,
    pruned_write_check_after_teardown hAlloc
      uniqueCellForest_foreignWriteNoop 0 1 0 none 0,
    retagReadPruning_conservative_after_teardown hAlloc hClosed.1 hClosed.2.1
      active 0 1,
    retagReadPruning_rootNoop_after_teardown hAlloc hInv.2.2.1 0 1⟩
  rw [pruned_dealloc_check_after_teardown hAlloc hClosed.1 active 0 1 0 1,
    hasFrameDeallocProtectorConflict_eq_any]
  rfl

/-! ### Worked instances of the module, composed with the laws above -/

/-- Postcondition weakening for `LiftState`: a lifted state stays lifted for
every weaker postcondition, at the same fuel. -/
theorem liftState_weaken_post {body : CapturedMir} {s : MachineState}
    {post₁ post₂ : Value → Prop} {fuel : Nat}
    (hImp : ∀ v, post₁ v → post₂ v) (h : LiftState body s post₁ fuel) :
    LiftState body s post₂ fuel :=
  Anneal.MirFuelFree.wpMirExecSym_mono_post
    (fun out hOut => by
      cases out with
      | normal p => exact hImp _ hOut
      | panic => exact hOut
      | abort => exact hOut)
    h

/-- **The empty-function caller converges from its trusted initial state.**
The module's end-to-end lift starts at the frame that `initPureEnv` computes
for `emptyFnCaller`, so it discharges the fuel-free convergence of the
trusted machine from `initMachineStateWithCallees`, with result `()`; and
the module's teardown witness is the resumed caller computed by stage 4. -/
theorem emptyFnCaller_converges_from_init :
    Anneal.MirFuelFree.MirWpConverges emptyFnCaller
        (initMachineStateWithCallees emptyFnCaller [] [emptyFnAssignUnit])
        (Anneal.Rustc.V2026_06_01.SymbolicEval.mirNormalPost
          fun retVal _ => retVal = .unit) ∧
      ∃ s', prepTeardownAndWriteback.run calleeReturn = .ok () s' ∧
        s' = callerResumed ∧
        LiftState emptyFnCaller s' (fun v => v = .unit) 2 := by
  refine ⟨LiftFrame.mirWpConverges_withCallees (fuel := 6) ?_, ?_⟩
  · rw [emptyFnCaller_initPureEnv]
    exact emptyFnCaller_liftFrame
  · obtain ⟨s', hTd, hLift⟩ := emptyFnCaller_teardown_and_continuation
    obtain ⟨_, hS'⟩ :=
      EStateM.Result.ok.inj (hTd.symm.trans stage4_run_empty_fn)
    exact ⟨s', hTd, hS', hLift⟩

/-- **A stale disabled borrow is unobservable.** For every value, protector
id, and fuel of at least five steps, the protector-holding caller of the
empty function returns the value it kept in `_2`, both from the fresh
memory and from the memory that additionally holds a stale disabled borrow
at the callee frame depth. -/
theorem emptyFnCallerProt_fresh_and_stale (v : Value) (protId fuel : Nat)
    (hv : valueContainsUninit v = false) (hFuel : 5 ≤ fuel) :
    LiftFrame emptyFnCallerProt 0 0 [.uninit, .uninit, .init v]
        (emptyFnCallerProtMem protId) (fun r => r = v) fuel ∧
      LiftFrame emptyFnCallerProt 0 0 [.uninit, .uninit, .init v]
        (emptyFnCallerStaleProtMem protId) (fun r => r = v) fuel :=
  ⟨LiftFrame.mono hFuel (emptyFnCallerWithProtector_liftFrame v protId hv),
    LiftFrame.mono hFuel (emptyFnCallerStaleProtected_liftFrame v protId hv)⟩

/-- **The protector-registering callee: explicit trace prefix and lift.**
From the call terminator of `protCaller`, the first two trusted steps are
call entry and the fat function-entry retag, reaching the state in which
protector `10` is attached to the slice borrow and active; and the whole
caller is lifted to return `()` for every fuel of at least six steps. -/
theorem protCaller_trace_prefix_and_lift (fuel : Nat) (hFuel : 6 ≤ fuel) :
    StepsTo protCaller protCallerAtCall 2
        { frame := { (fatRetagEntry 10 4).frame with stmtIdx := 1 }
          memory :=
            { (fatRetagEntry 10 4).memory with
              borrows := [
                { tag := 1, targetLocal := 3, targetFrameDepth := 0,
                  targetProjection := [], perm := .frozen,
                  protector := some 10 }]
              activeProtectors := [10]
              nextProtector := 11 } } ∧
      LiftState protCaller protCallerAtCall (fun v => v = .unit) fuel :=
  ⟨StepsTo.step (s₁ := fatRetagEntry 10 4) rfl
      (StepsTo.single (fatRef_retag_step 10 4)),
    LiftState.mono hFuel
      (liftState_iff_liftFrame.mpr protectedCallee_liftFrame)⟩

/-- **Both conclusions of the shared four-stage prefix.** The module's
duplicate-prefix instance lifts `thinRefCaller` for the conjunction of two
postconditions; weakening recovers the second suffix specification on its
own, the single-postcondition instance gives the first, and both hold for
every fuel of at least six steps. -/
theorem thinRefCaller_both_suffix_specs (fuel : Nat) (hFuel : 6 ≤ fuel) :
    LiftState thinRefCaller thinCallerAtCall (fun v => v = .unit) fuel ∧
      LiftState thinRefCaller thinCallerAtCall
        (fun v => v ≠ .scalar { bits := 0, sizeBytes := 1 }) fuel :=
  ⟨LiftState.mono hFuel
      (liftState_iff_liftFrame.mpr thinRefProtectedCallee_liftFrame),
    LiftState.mono hFuel
      (liftState_weaken_post (fun _ h => h.2)
        (liftState_iff_liftFrame.mpr
          thinRefProtectedCallee_duplicate_prefix_liftFrame))⟩

/-- Entry state of `thinMutRefCallee` as a root body with symbolic tag and
protector counters. -/
def thinMutRetagEntry (t n : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [.uninit, .init thinRefParentVal] }
    memory :=
      { borrows := [callerBorrow 1 .unique, callerBorrow 9 .unique]
        nextTag := t
        activeCallee := some thinMutRefCallee
        nextProtector := n } }

/-- **Mutable thin-reference retag and the mutable worked instance.** The
function-entry retag of a `&mut u8` is one trusted step that mints the
child tag `t` with the two-phase permission `.reservedFrz false` under the
fresh protector `n` and freezes the sibling borrow, for all counters; and
the module's end-to-end mutable caller returns `()` for every fuel of at
least six steps. -/
theorem thinMutRef_retag_step_and_lift (t n fuel : Nat) (hFuel : 6 ≤ fuel) :
    stepMirFn thinMutRefCallee (thinMutRetagEntry t n) =
        MirStepNode.step
          { frame :=
              { blockIdx := 0, stmtIdx := 1
                locals :=
                  [.uninit, .init (.ptr { allocId := t, offsetBytes := 0 } 8)] }
            memory :=
              { (thinMutRetagEntry t n).memory with
                borrows := [
                  { thinChildBorrow t n with perm := .reservedFrz false },
                  callerBorrow 1 .unique, callerBorrow 9 .frozen]
                nextTag := t + 1
                activeProtectors := [n]
                nextProtector := n + 1 } } ∧
      LiftFrame thinMutRefCaller 0 0
        [.uninit, .uninit, .init thinRefParentVal] thinMutRefCallerMem
        (fun v => v = .unit) fuel := by
  have h :=
    stepMirFn_retag_fnEntry_any_ptr (body := thinMutRefCallee)
      (cur := thinMutRefCallee) (s := thinMutRetagEntry t n)
      (blk :=
        { statements := [
            { kind := .retag .fnEntry { local_ := 1, projection := [] }
              span := "fn_entry_thin_mut_retag" },
            { kind := .assign { local_ := 0, projection := [] }
                (.use (.constant { ty := emptyFnUnitTy, val := .zeroSized }))
              span := "unit" }]
          terminator := { kind := .return_, span := "ret" }
          isCleanup := false })
      (loc := 1) (span := "fn_entry_thin_mut_retag") (mutability := .mut)
      (pointee := .uint .u8) (lIdx := 0) (sz := 8)
      (ptrVal := { allocId := 1, offsetBytes := 0 })
      (parentEntry := callerBorrow 1 .unique)
      (locals' := [.uninit, .init thinRefParentVal])
      rfl (Or.inl rfl) rfl rfl rfl rfl rfl
  exact ⟨h.1 _ rfl, LiftFrame.mono hFuel thinMutRefProtectedCallee_liftFrame⟩

/-- **The mixed two-parameter caller, by both stepping routes.** The
module lifts `twoArgMixedCaller` once with hand-written per-statement
stepping and once with the syntactic stepping theorem; both give the same
seven-step lift, hence the lift for every larger fuel, and for the weaker
postcondition that the result is not a scalar. -/
theorem twoArgMixedCaller_lift_both_routes (fuel : Nat) (hFuel : 7 ≤ fuel) :
    LiftFrame twoArgMixedCaller 0 0
        [.uninit, .uninit, .init thinRefParentVal, .init twoArgSliceVal]
        twoArgMixedCallerMem (fun v => v = .unit) fuel ∧
      LiftState twoArgMixedCaller
        (PureState.toMachineState
          { bb := 0, stmtIdx := 0,
            env := [.uninit, .uninit, .init thinRefParentVal,
              .init twoArgSliceVal] } twoArgMixedCallerMem)
        (fun v => ∀ sc, v ≠ .scalar sc) 7 :=
  ⟨LiftFrame.mono hFuel twoArgMixedProtectedCallee_liftFrame,
    liftState_weaken_post (fun _ h sc hEq => by rw [h] at hEq; cases hEq)
      (liftState_iff_liftFrame.mpr
        twoArgMixedProtectedCallee_liftFrame_syntactic)⟩

/-- **Two parameters: the indexed theorem applies, the unindexed premise is
refuted.** Every successful run of the two-parameter thin pipeline from the
module's entry state ends in `twoArgThinRetagged` (reached in two trusted
steps by the statement-indexed theorem), while the unindexed per-local
premise is false on this callee. -/
theorem twoArgThin_indexed_applies_unindexed_refuted :
    (∀ s₃, (prepFnEntryRetagThins twoArgThinCallee [1, 2]).run
        twoArgThinEntryState = .ok () s₃ → s₃ = twoArgThinRetagged) ∧
    ¬ (∀ (loc : Local) (st st₁ : MachineState),
        loc ∈ ([1, 2] : List Local) →
        st.frame.blockIdx = twoArgThinEntryState.frame.blockIdx →
        st.memory.activeCallee = twoArgThinEntryState.memory.activeCallee →
        (prepFnEntryRetagThin twoArgThinCallee loc).run st = .ok () st₁ →
        stepMirFn twoArgThinCallee st = MirStepNode.step st₁) := by
  obtain ⟨_, _, _, hFalse⟩ :=
    prepFnEntryRetagThins_stepsTo_unindexed_premise_false_two_args
  refine ⟨fun s₃ h => ?_, hFalse⟩
  rw [twoArgThin_retags_two_steps.1] at h
  obtain ⟨_, hS₃⟩ := EStateM.Result.ok.inj h
  exact hS₃.symm
end

end Anneal.DualCorrespondenceAndTbPruningTests.FrameWp

namespace Anneal.DualCorrespondenceAndTbPruningTests.Audit

open Lean in
/-- Non-recursive CNF worklist recognizing syntactically trivial propositions
under universal, implication, `let`, and metadata wrappers: `True`, `¬ False`,
`False → P`, `P → P`, reflexive `a = a`, `a ↔ a`, and `HEq a a`, conjunctions
of trivial propositions, and disjunctions with a trivial disjunct. Bounded at
4096 steps with no recursion, so no `_unsafe_rec` twin is emitted. Exhausting
the budget fails closed: a proposition whose first 4096 nodes are all still
trivial is reported as trivial, so padding cannot smuggle one past. -/
def trivialProp (e : Expr) : Bool := Id.run do
  let mut todo : List (List Expr) := [[e]]
  for _ in [0:4096] do
    match todo with
    | [] => return true
    | [] :: _ => return false
    | (x :: alts) :: rest =>
      match x with
      | .mdata _ b => todo := (b :: alts) :: rest
      | .letE _ _ _ b _ => todo := (b :: alts) :: rest
      | .forallE _ d b _ =>
        let dc := d.consumeMData
        if dc.isConstOf ``False || dc.liftLooseBVars 0 1 == b.consumeMData then
          todo := rest
        else
          todo := (b :: alts) :: rest
      | .const ``True _ => todo := rest
      | .app (.const ``Not _) a =>
        if a.consumeMData.isConstOf ``False then todo := rest
        else todo := alts :: rest
      | .app (.app (.const ``And _) a) b =>
        todo := (a :: alts) :: (b :: alts) :: rest
      | .app (.app (.const ``Or _) a) b =>
        todo := (a :: b :: alts) :: rest
      | .app (.app (.app (.const ``Eq _) _) a) b =>
        if a == b then todo := rest else todo := alts :: rest
      | .app (.app (.const ``Iff _) a) b =>
        if a == b then todo := rest else todo := alts :: rest
      | .app (.app (.app (.app (.const ``HEq _) _) a) _) b =>
        if a == b then todo := rest else todo := alts :: rest
      | _ => todo := alts :: rest
  return true

end Anneal.DualCorrespondenceAndTbPruningTests.Audit

/-! ## G. Cross-root kernel bridge

The LeanMiri correspondence modules and the vendored `Miri` interpreter are
built in another package root. The command below imports both roots into a
fresh kernel environment, replays the surface declarations of this file
that the cross-root declarations depend on, and then submits to the kernel:

* the two authorities built over the vendored interpreter itself
  (`Step.step` under the wide-slice hooks; `Cast.cast` with real
  `CastHooks` / `FloatOpsHooks` for `FloatToFloat`, `FloatToInt`,
  `IntToFloat`, and 32/64-bit `Transmute`, plus `Step.step` for
  uninitialized-source UB);
* the proofs that these interpreters compute exactly the reference tables
  `WideSlice.lmReference` and `FloatCast.lmReference`, pass the LeanMiri
  side certificates, and convert `binary16` / `binary128` via `Cast.cast`
  (proving `FloatCast.gateLM`'s exclusions tight);
* every bundle (12 cross-root bundles) and every `*_with` theorem
  instantiated at them;
* the equalities of the Anneal fixtures of this file with the fixtures of
  the LeanMiri correspondence module.

Forged declarations across both families are submitted to scratch copies of
the environment and must be rejected, and every accepted declaration is
inspected. -/

open Lean Meta Elab Command in
run_cmd do
  let srcEnv ← getEnv
  let ns := `Anneal.DualCorrespondenceAndTbPruningTests
  let lm := `LeanMiriSpec.Correspondence
  let lw := `LeanMiriSpec.Correspondence.WideSliceWitnesses
  let mi := `Miri.Interpreter
  let sysroot ← Lean.findSysroot
  Lean.initSearchPath sysroot
    [".lake/build/lib/lean", "examples/.lake/build/lib/lean"]
  let imports : Array Lean.Import := #[
    { module := `Anneal.DualCorrespondenceBundle },
    { module := `MiniRustSpec.Correspondence.WideSliceDst },
    { module := `LeanMiriSpec.Correspondence.WideSliceDstLM },
    { module := `Miri.Interpreter.Float },
    { module := `Miri.Interpreter.FloatOps },
    { module := `Miri.Interpreter.Cast },
    { module := `Miri.Interpreter.Step }
  ]
  let baseEnv ← liftCoreM <| Lean.importModules imports {} 0
  let opts : Options := ({} : Options).setBool `Elab.async false
  let act : CoreM (Nat × Nat × Nat × Nat × Array Name) := do
    -- 1. Replay the closure of the surface declarations used below.
    let wsWith : Array Name :=
      #[`safe_tooBig_fault_equiv_with, `lm_safe_tooBig_faults_with,
        `inBounds_reborrow_threeWay_with, `inBounds_reborrow_rep_with,
        `no_unwind_with, `raw_metadata_wellFormed_with,
        `raw_tooBig_normal_equiv_with, `lm_raw_tooBig_returns_with,
        `raw_tooBig_diverge_equiv_with, `raw_tooBig_unwind_iff_with,
        `projectPositive_with, `projectFault_with,
        `anneal_not_constant_with, `claims_with, `productiveBoth_with,
        `productivity_transfer_with,
        `productiveBoth_of_recorded_reverse_with, `lmModeWitness_spec_with,
        `lmModeWitness_isFaultFlip_with, `faultFlipComp_modeSensitive_with,
        `lm_not_mode_invariant_with, `modeSensitive_with,
        `lmFlip_guard_with, `lmIndexOob_not_wellFormed_with,
        `lmSizeOfVal_wellFormed_with, `lmPipeline_wellFormed_with,
        `detBundle_spec_with, `detBundle_productiveAnneal_with,
        `detBundle_exact_with]
    let wsDefs : Array Name :=
      #[`bundleWith, `detBundleWith, `faultFlipComp_with,
        `faultFlipTrans_with, `mixedComp_with]
    let fcWith : Array Name :=
      #[`uninit_fault_equiv_with, `lm_uninit_faults_with, `lm_u64_casts_with,
        `carrier_normal_equiv_with, `carrier64_normal_equiv_with,
        `lmModeWitness_spec_with, `productiveBoth_with,
        `frontTrans_codec_with, `frontTrans_productiveBoth_with,
        `frontComp_productive_with, `frontCompMixed_modeSensitive_with,
        `boolModes_productive_with, `boolModes_modeSensitive_with,
        `nondetOnly_productive_with, `tightenCodec_with,
        `gatedBundle_productiveBoth_with]
    let fcDefs : Array Name :=
      #[`bundleWith, `frontTrans_with, `frontComp_with,
        `frontCompMixed_with, `boolModes_with, `nondetOnly_with,
        `gatedBundleWith]
    let mut roots : Array Name :=
      #[ns ++ `WideSlice.authorityOf, ns ++ `WideSlice.checkOf,
        ns ++ `WideSlice.matchesReference_sound, ns ++ `Corpus.pairObs,
        ns ++ `Corpus.ObsAuthority.denoteConsistent,
        ns ++ `Corpus.ObsAuthority.denoteConsistent_sound,
        ns ++ `WideSlice.frameInit, ns ++ `WideSlice.sizeOfValInit,
        ns ++ `WideSlice.pipelineBody, ns ++ `WideSlice.pipelineInit,
        ns ++ `FloatCast.authorityOf, ns ++ `FloatCast.checkOf,
        ns ++ `FloatCast.matchesReference_sound,
        ns ++ `FloatCast.empty_schedule_is_vacuous,
        ns ++ `FloatCast.Engine.agrees_sound, ns ++ `FloatCast.castShape,
        ns ++ `FloatCast.dstBytes]
    for n in wsWith ++ wsDefs do roots := roots.push (ns ++ `WideSlice ++ n)
    for n in fcWith ++ fcDefs do roots := roots.push (ns ++ `FloatCast ++ n)
    let mut pending : Array Name := #[]
    let mut seen : NameSet := {}
    let mut stack := roots
    while !stack.isEmpty do
      let n := stack.back!
      stack := stack.pop
      if seen.contains n || baseEnv.contains n then continue
      seen := seen.insert n
      let some ci := srcEnv.find? n | throwError "replay: unknown {n}"
      pending := pending.push n
      let mut deps := ci.getUsedConstantsAsSet
      match ci with
      | .inductInfo v =>
        for c in v.ctors do
          if let some cc := srcEnv.find? c then
            deps := cc.type.getUsedConstantsAsSet.foldl (·.insert ·) deps
        for i in v.all do deps := deps.insert i
      | .ctorInfo v => deps := deps.insert v.induct
      | .recInfo v => for i in v.all do deps := deps.insert i
      | _ => pure ()
      for d in deps do
        if !seen.contains d then stack := stack.push d
    let mut replayed : Nat := 0
    let mut progress := true
    while progress && !pending.isEmpty do
      progress := false
      let mut rest : Array Name := #[]
      for n in pending do
        if (← getEnv).contains n then
          progress := true
          continue
        let some ci := srcEnv.find? n | throwError "replay: unknown {n}"
        let ready (e : Expr) : CoreM Bool := do
          let env ← getEnv
          return e.getUsedConstantsAsSet.all fun d => d == n || env.contains d
        match ci with
        | .defnInfo v =>
          if (← ready v.type) && (← ready v.value) then
            addDecl (.defnDecl v)
            replayed := replayed + 1
            progress := true
          else rest := rest.push n
        | .thmInfo v =>
          if (← ready v.type) && (← ready v.value) then
            addDecl (.thmDecl v)
            replayed := replayed + 1
            progress := true
          else rest := rest.push n
        | .inductInfo v =>
          let env ← getEnv
          let mut ok := true
          let mut types : List InductiveType := []
          for i in v.all do
            let some (.inductInfo iv) := srcEnv.find? i
              | throwError "replay: bad inductive {i}"
            let mut ctors : List Constructor := []
            for c in iv.ctors do
              let some (.ctorInfo cv) := srcEnv.find? c
                | throwError "replay: bad constructor {c}"
              unless cv.type.getUsedConstantsAsSet.all
                  (fun d => v.all.contains d || env.contains d) do
                ok := false
              ctors := ctors ++ [{ name := c, type := cv.type }]
            unless iv.type.getUsedConstantsAsSet.all
                (fun d => v.all.contains d || env.contains d) do
              ok := false
            types := types ++ [{ name := i, type := iv.type, ctors := ctors }]
          if ok then
            addDecl (.inductDecl v.levelParams v.numParams types v.isUnsafe)
            replayed := replayed + 1
            progress := true
          else rest := rest.push n
        | .ctorInfo _ | .recInfo _ => rest := rest.push n
        | _ => throwError "replay: unsupported declaration {n}"
      pending := rest
    unless pending.isEmpty do
      throwError "replay: stuck on {pending}"
    -- 2. WideSlice Miri authority
    let prov := mkConst (lm ++ `AnnealProv)
    let stepErr := mkConst (mi ++ `StepError)
    let lv ← MetaM.run' <| mkAppM (mi ++ `LocalValue) #[prov]
    let optLv ← MetaM.run' <| mkAppM ``Option #[lv]
    let payload ← MetaM.run' <| mkAppM ``Prod #[mkConst ``Bool, optLv]
    let obsTy ← MetaM.run' <| mkAppM ``Except #[stepErr, payload]
    let decLv ← MetaM.run' <| mkAppOptM (mi ++ `instDecidableEqLocalValue)
      #[some prov, some (mkConst `Miri.Memory.instDecidableEqProvenance)]
    let decOptLv ← MetaM.run' <| mkAppOptM ``Option.instDecidableEq
      #[some lv, some decLv]
    let decPayload ← MetaM.run' <| mkAppOptM ``instDecidableEqProd
      #[some (mkConst ``Bool), some optLv, some (mkConst ``instDecidableEqBool),
        some decOptLv]
    let decObs ← MetaM.run' <| mkAppOptM `Miri.ABI.instDecidableEqExcept_miri
      #[some stepErr, some payload,
        some (mkConst (mi ++ `instDecidableEqStepError)), some decPayload]
    let capMir := mkConst ``Trusted.Rustc.V2026_06_01.MirAst.CapturedMir
    let tyTy := mkConst ``Trusted.Rustc.V2026_06_01.MirAst.Ty
    let natTy := mkConst ``Nat
    let stateTy := mkConst (lm ++ `AnnealStepState)
    let (wsAuth, wsFrameObs, wsSizeObs, wsPipelineObs, wsRetU32, wsRetWide,
        wsUbObs) ← MetaM.run' do
      let u64 (e : Expr) : MetaM Expr := mkAppM ``UInt64.ofNat #[e]
      let hooksOf (b : Expr) : MetaM Expr := do
        mkAppM (lm ++ `annealStepHooksWideSlice)
          #[← mkAppM ``Trusted.Rustc.V2026_06_01.MirAst.CapturedMir.localDecls
              #[b],
            ← mkAppM ``Trusted.Rustc.V2026_06_01.MirAst.CapturedMir.layouts
              #[b]]
      let observe (r : Expr) : MetaM Expr := do
        let proj ← withLocalDeclD `s stateTy fun s => do
          mkLambdaFVars #[s]
            (← mkAppM (lw ++ `miriTopLocal?) #[s, mkNatLit 0])
        mkAppM (ns ++ `Corpus.pairObs) #[proj, r]
      let wideImm (len : Expr) : MetaM Expr := do
        mkAppM (mi ++ `Immediate.scalarPair)
          #[mkConst (lw ++ `sampleMiriPtrSc),
            ← mkAppOptM `Miri.Memory.Scalar.fromScalarInt
              #[some prov,
                some (← mkAppM `Miri.Memory.ScalarInt.ofUInt64 #[← u64 len])]]
      let frameObs ← withLocalDeclD `b capMir fun b =>
        withLocalDeclD `ty tyTy fun ty =>
        withLocalDeclD `len natTy fun len =>
        withLocalDeclD `idx natTy fun idx => do
          let init ← mkAppM (lw ++ `wideSlice4LocalInitMiri)
            #[b, ty, mkConst (lw ++ `sampleMiriPtr), ← u64 len, ← u64 idx,
              mkConst (lw ++ `sampleArrU32Machine)]
          let r ← mkAppM (mi ++ `Step.step)
            #[← hooksOf b, mkConst ``Unit.unit, init]
          mkLambdaFVars #[b, ty, len, idx] (← observe r)
      let sizeObs ← withLocalDeclD `b capMir fun b =>
        withLocalDeclD `len natTy fun len => do
          let init ← mkAppM (lw ++ `singleWideIntrinsicInitMiri)
            #[mkConst ``Bool.false, mkConst (lw ++ `rawSliceU32Ty),
              mkConst (lw ++ `sliceU32PointeeTy), ← wideImm len]
          let r ← mkAppM (mi ++ `Step.step)
            #[← hooksOf b, mkConst ``Unit.unit, init]
          mkLambdaFVars #[b, len] (← observe r)
      let pipeStep ← mkAppM (mi ++ `Step.step)
        #[mkConst (lw ++ `wideSlicePipelineHooks), mkConst ``Unit.unit,
          mkConst (lw ++ `wideSlicePipelineMiri4)]
      let pipelineObs ← observe pipeStep
      let okWith (f : Expr → MetaM Expr) : MetaM Expr :=
        withLocalDeclD `n natTy fun n => do
          let pair ← mkAppM ``Prod.mk #[mkConst ``Bool.true, ← f n]
          mkLambdaFVars #[n]
            (← mkAppOptM ``Except.ok #[some stepErr, some payload, some pair])
      let retUsize ← okWith fun n => mkAppM (lw ++ `miriUsizeLocal) #[n]
      let retU32 ← okWith fun n => mkAppM (lw ++ `miriU32Local) #[n]
      let retWide ← okWith fun n => do
        let op ← mkAppM (mi ++ `Operand.immediate) #[← wideImm n]
        mkAppM ``Option.some #[← mkAppM (mi ++ `LocalValue.live) #[op]]
      let ubObs ← withLocalDeclD `s (mkConst ``String) fun s => do
        let err ← mkAppM (mi ++ `StepError.undefinedBehavior) #[s]
        mkLambdaFVars #[s]
          (← mkAppOptM ``Except.error #[some stepErr, some payload, some err])
      let auth ← mkAppM (ns ++ `WideSlice.authorityOf)
        #[obsTy, decObs, frameObs, sizeObs, pipelineObs, retUsize, retU32,
          retWide, ubObs]
      return (auth, frameObs, sizeObs, pipelineObs, retU32, retWide, ubObs)
    let authTy ← MetaM.run' <| inferType wsAuth
    let miriName := ns ++ `CrossRoot.WideSlice.miri
    let dv : DefinitionVal :=
      { name := miriName
        levelParams := []
        type := authTy
        value := wsAuth
        hints := .regular 0
        safety := .safe }
    addDecl (.defnDecl dv)
    let miriC := mkConst miriName
    let boolTrue := mkConst ``Bool.true
    let reflTrue := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) boolTrue
    let eqTrue (e : Expr) : Expr :=
      mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e boolTrue
    let mut added : Array Name := #[miriName]
    let addThm (name : Name) (type value : Expr) : CoreM Unit :=
      addDecl (.thmDecl
        { name := name, levelParams := [], type := type, value := value })
    let addDef (name : Name) (value : Expr) : CoreM Expr := do
      let type ← MetaM.run' <| inferType value
      let dv : DefinitionVal :=
        { name := name
          levelParams := []
          type := type
          value := value
          hints := .regular 0
          safety := .safe }
      addDecl (.defnDecl dv)
      return type
    -- The vendored interpreter computes exactly the reference table, has a
    -- non-shadowing `denote` table, and passes the LeanMiri certificate.
    addThm (ns ++ `CrossRoot.WideSlice.miri_matches)
      (eqTrue (mkApp (mkConst (ns ++ `WideSlice.matchesReference)) miriC))
      reflTrue
    addThm (ns ++ `CrossRoot.WideSlice.miri_check)
      (eqTrue (mkApp (mkConst (ns ++ `WideSlice.checkOf)) miriC)) reflTrue
    let wsDenoteC ← MetaM.run' <|
      mkAppOptM (ns ++ `Corpus.ObsAuthority.denoteConsistent)
        #[none, none, some (mkConst ``instDecidableEqNat), some miriC]
    let wsDenoteName := ns ++ `CrossRoot.WideSlice.miri_denoteConsistent
    addThm wsDenoteName (eqTrue wsDenoteC) reflTrue
    let wsDenoteSpec ← MetaM.run' <|
      mkAppOptM (ns ++ `Corpus.ObsAuthority.denoteConsistent_sound)
        #[none, none, some (mkConst ``instDecidableEqNat), some miriC,
          some (mkConst wsDenoteName)]
    let wsDenoteSpecName :=
      ns ++ `CrossRoot.WideSlice.miri_denoteConsistent_spec
    addThm wsDenoteSpecName (← MetaM.run' <| inferType wsDenoteSpec)
      wsDenoteSpec
    -- Every prefix step (1..4) and return/termination step (6..7) of the
    -- multi-step `wideSlicePipeline` succeeds cleanly in vendored Miri
    -- (step 5 and `_0 = 12` are pinned by `miri_matches`).
    let (pipeAllTy, pipeAllPf) ← MetaM.run' do
      let okBool (b : Name) : MetaM Expr :=
        mkAppOptM ``Except.ok
          #[some stepErr, some (mkConst ``Bool), some (mkConst b)]
      let stepRes (stName : Name) (resB : Name) : MetaM (Expr × Expr) := do
        let stp ← mkAppM (mi ++ `Step.step)
          #[mkConst (lw ++ `wideSlicePipelineHooks), mkConst ``Unit.unit,
            mkConst (lw ++ stName)]
        let lhs ← mkAppM ``Prod.snd #[stp]
        let rhs ← okBool resB
        return (← mkEq lhs rhs, ← mkEqRefl rhs)
      let items ←
        [stepRes `wideSlicePipelineInitMiri ``Bool.true,
         stepRes `wideSlicePipelineMiri1 ``Bool.true,
         stepRes `wideSlicePipelineMiri2 ``Bool.true,
         stepRes `wideSlicePipelineMiri3 ``Bool.true,
         stepRes `wideSlicePipelineMiri5 ``Bool.true].mapM id
      let last ← stepRes `wideSlicePipelineMiri6 ``Bool.false
      return items.foldr
        (fun (t, p) (tr, pr) =>
          (mkApp2 (mkConst ``And) t tr, mkApp4 (mkConst ``And.intro) t tr p pr))
        last
    let wsPipeAllName := ns ++ `CrossRoot.WideSlice.pipeline_steps_ok
    addThm wsPipeAllName pipeAllTy pipeAllPf
    added := added ++ #[ns ++ `CrossRoot.WideSlice.miri_matches,
      ns ++ `CrossRoot.WideSlice.miri_check, wsDenoteName, wsDenoteSpecName,
      wsPipeAllName]
    -- 3. FloatCast Miri authority over `Miri.Interpreter.Cast.cast`
    let immTy ← MetaM.run' <| mkAppM (mi ++ `Immediate) #[prov]
    let castS ← MetaM.run' <| mkAppM ``Option #[immTy]
    let fcObsTy ← MetaM.run' <| mkAppM ``Except #[stepErr, castS]
    let decImm ← MetaM.run' <| mkAppOptM (mi ++ `instDecidableEqImmediate)
      #[some prov, some (mkConst `Miri.Memory.instDecidableEqProvenance)]
    let decCastS ← MetaM.run' <| mkAppOptM ``Option.instDecidableEq
      #[some immTy, some decImm]
    let decFcObs ← MetaM.run' <| mkAppOptM `Miri.ABI.instDecidableEqExcept_miri
      #[some stepErr, some castS,
        some (mkConst (mi ++ `instDecidableEqStepError)), some decCastS]
    let (fcRunCast, fcRet32, fcRet64, fcUbObs, fcUninitObs) ← MetaM.run' do
      let boolTy := mkConst ``Bool
      let unitTy := mkConst ``Unit
      let tyIdTy := mkConst `Miri.MIR.TyId
      let defIdTy := mkConst `Miri.MIR.DefId
      let u64Ty := mkConst ``UInt64
      let intKindTy := mkConst `Miri.MIR.IntegerKind
      let fmtTy := mkConst (mi ++ `FloatFormat)
      let fbTy := mkConst (mi ++ `FloatBits)
      let castInfoTy := mkConst (mi ++ `CastTypeInfo)
      let castKindTy := mkConst `Miri.MIR.CastKind
      let layoutTy ← mkAppM `Miri.ABI.TyAndLayout #[tyIdTy]
      let opTy ← mkAppM (mi ++ `OpTy) #[prov]
      let rvImmTy ← mkAppM (mi ++ `RvalueImmTy) #[prov]
      let optProv ← mkAppM ``Option #[prov]
      let ptrOptTy ← mkAppM `Miri.Memory.Pointer #[optProv]
      let arrGArg ← mkAppM ``Array #[mkConst `Miri.MIR.GenericArg]
      let callInstTy := mkConst (mi ++ `CallInstance)
      let optCallInst ← mkAppM ``Option #[callInstTy]
      let optTyId ← mkAppM ``Option #[tyIdTy]
      let optNat ← mkAppM ``Option #[natTy]
      let prodTyId ← mkAppM ``Prod #[tyIdTy, tyIdTy]
      let vtEntry ← mkAppM (mi ++ `VTableEntry) #[callInstTy]
      let arrVtEntry ← mkAppM ``Array #[vtEntry]
      let layDataTy := mkConst `Miri.ABI.LayoutData
      let empLay :=
        mkConst ``Trusted.Rustc.V2026_06_01.MirSemantics.emptyLayoutTable
      let pureM (aTy val : Expr) : MetaM Expr :=
        mkAppOptM ``EStateM.pure #[some stepErr, some castS, some aTy, some val]
      let leaf (name : String) (aTy : Expr) : MetaM Expr :=
        mkAppOptM (lm ++ `annealUnsupportedLeaf)
          #[some castS, some aTy, some (mkStrLit name)]
      let layOf (t : Expr) : MetaM Expr :=
        mkAppM (lm ++ `layoutOfEncodedTyId) #[t, empLay]
      let switchNat (t : Expr) (cases : List (Nat × Expr)) (dflt : Expr) :
          MetaM Expr :=
        cases.foldrM (fun (k, rhs) acc => do
          let condB ← mkAppM ``Nat.beq #[t, mkNatLit k]
          mkAppM ``cond #[condB, rhs, acc]) dflt
      let scOfInt (si : Expr) : MetaM Expr :=
        mkAppOptM `Miri.Memory.Scalar.fromScalarInt #[some prov, some si]
      let sc32 (n : Expr) : MetaM Expr := do
        scOfInt (← mkAppM `Miri.Memory.ScalarInt.ofUInt32
          #[← mkAppM ``UInt32.ofNat #[n]])
      let sc64 (n : Expr) : MetaM Expr := do
        scOfInt (← mkAppM `Miri.Memory.ScalarInt.ofUInt64
          #[← mkAppM ``UInt64.ofNat #[n]])
      let sc16 (n : Expr) : MetaM Expr := do
        scOfInt (← mkAppM `Miri.Memory.ScalarInt.ofUInt16
          #[← mkAppM ``UInt16.ofNat #[n]])
      let sc128 (n : Expr) : MetaM Expr := do
        scOfInt (← mkAppM `Miri.Memory.ScalarInt.ofUInt128
          #[← mkAppM ``BitVec.ofNat #[mkNatLit 128, n]])
      let hooksOf (flag : Expr) : MetaM Expr := do
        let kindOf ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `t tyIdTy fun t => do
            let body ← switchNat t
              [(12, ← pureM intKindTy (mkConst `Miri.MIR.IntegerKind.i32)),
               (13, ← pureM intKindTy (mkConst `Miri.MIR.IntegerKind.i64)),
               (22, ← pureM intKindTy (mkConst `Miri.MIR.IntegerKind.u32)),
               (23, ← pureM intKindTy (mkConst `Miri.MIR.IntegerKind.u64))]
              (← leaf "integerKindOf" intKindTy)
            mkLambdaFVars #[c, t] body
        let formatOf ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `t tyIdTy fun t => do
            let body ← switchNat t
              [(30, ← pureM fmtTy (mkConst (mi ++ `FloatFormat.binary16))),
               (31, ← pureM fmtTy (mkConst (mi ++ `FloatFormat.binary32))),
               (32, ← pureM fmtTy (mkConst (mi ++ `FloatFormat.binary64))),
               (33, ← pureM fmtTy (mkConst (mi ++ `FloatFormat.binary128)))]
              (← leaf "formatOf" fmtTy)
            mkLambdaFVars #[c, t] body
        let boolLay ← withLocalDeclD `c natTy fun c => do
          mkLambdaFVars #[c] (← pureM layoutTy (← layOf (mkNatLit 1)))
        let fbList ← mkAppM ``List #[fbTy]
        let choose ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `cands fbList fun cands => do
            let idx ← mkAppM ``Nat.mod #[c, ← mkAppM ``List.length #[cands]]
            mkLambdaFVars #[c, cands] (← pureM natTy idx)
        let floatHooks ← mkAppOptM (mi ++ `FloatOpsHooks.mk)
          #[some prov, some castS, some natTy, some kindOf, some formatOf,
            some boolLay, some flag, some choose]
        let typeInfo ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `t tyIdTy fun t => do
            let flt (f : Name) : MetaM Expr := do
              pureM castInfoTy
                (← mkAppM (mi ++ `CastTypeInfo.floating) #[mkConst (mi ++ f)])
            let intI (k : Name) : MetaM Expr := do
              pureM castInfoTy
                (← mkAppM (mi ++ `CastTypeInfo.integer)
                  #[mkConst (`Miri.MIR.IntegerKind ++ k)])
            let body ← switchNat t
              [(30, ← flt `FloatFormat.binary16),
               (31, ← flt `FloatFormat.binary32),
               (32, ← flt `FloatFormat.binary64),
               (33, ← flt `FloatFormat.binary128),
               (12, ← intI `i32), (13, ← intI `i64),
               (22, ← intI `u32), (23, ← intI `u64)]
              (← leaf "typeInfo" castInfoTy)
            mkLambdaFVars #[c, t] body
        let layoutOf ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `t tyIdTy fun t => do
            mkLambdaFVars #[c, t] (← pureM layoutTy (← layOf t))
        let destLayout ← withLocalDeclD `v layoutTy fun v =>
          mkLambdaFVars #[v] v
        let opTyOperand ← mkAppM (mi ++ `Operand) #[prov]
        let readImm ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `op opTy fun op => do
            let opField ← mkAppM (mi ++ `OpTy.op) #[op]
            let layField ← mkAppM (mi ++ `OpTy.layout) #[op]
            let retM ← mkAppM (mi ++ `RvalueM) #[castS, rvImmTy]
            let motive ← withLocalDeclD `_o opTyOperand fun o =>
              mkLambdaFVars #[o] retM
            let onImm ← withLocalDeclD `imm immTy fun imm => do
              let r ← mkAppM (mi ++ `RvalueImmTy.mk) #[imm, layField]
              mkLambdaFVars #[imm] (← pureM rvImmTy r)
            let mpTy ← mkAppM (mi ++ `MemPlace) #[prov]
            let onInd ← withLocalDeclD `_mp mpTy fun mp => do
              mkLambdaFVars #[mp] (← leaf "readImmediate" rvImmTy)
            let body ← mkAppOptM (mi ++ `Operand.casesOn)
              #[some prov, some motive, some opField, some onImm, some onInd]
            mkLambdaFVars #[c, op] body
        let writeImm ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `imm immTy fun imm =>
          withLocalDeclD `v layoutTy fun v =>
          withLocalDeclD `_st castS fun st => do
            let someImm ← mkAppOptM ``Option.some #[some immTy, some imm]
            let res ← mkAppOptM ``EStateM.Result.ok
              #[some stepErr, some castS, some unitTy,
                some (mkConst ``Unit.unit), some someImm]
            mkLambdaFVars #[c, imm, v, st] res
        let copyTrans ← withLocalDeclD `c natTy fun c =>
          withLocalDeclD `op opTy fun op =>
          withLocalDeclD `v layoutTy fun v =>
          withLocalDeclD `st castS fun st => do
            let opField ← mkAppM (mi ++ `OpTy.op) #[op]
            let resTy ← mkAppM ``EStateM.Result #[stepErr, castS, unitTy]
            let motive ← withLocalDeclD `_o opTyOperand fun o =>
              mkLambdaFVars #[o] resTy
            let onImm ← withLocalDeclD `imm immTy fun imm => do
              let someImm ← mkAppOptM ``Option.some #[some immTy, some imm]
              let okR ← mkAppOptM ``EStateM.Result.ok
                #[some stepErr, some castS, some unitTy,
                  some (mkConst ``Unit.unit), some someImm]
              mkLambdaFVars #[imm] okR
            let mpTy ← mkAppM (mi ++ `MemPlace) #[prov]
            let onInd ← withLocalDeclD `_mp mpTy fun mp => do
              let err ← mkAppM (mi ++ `StepError.unsupported)
                #[mkStrLit "copyAllowTransmute"]
              let errR ← mkAppOptM ``EStateM.Result.error
                #[some stepErr, some castS, some unitTy, some err, some st]
              mkLambdaFVars #[mp] errR
            let body ← mkAppOptM (mi ++ `Operand.casesOn)
              #[some prov, some motive, some opField, some onImm, some onInd]
            mkLambdaFVars #[c, op, v, st] body
        let fn2 (t1 t2 aTy : Expr) (name : String) : MetaM Expr :=
          withLocalDeclD `_1 t1 fun x1 => withLocalDeclD `_2 t2 fun x2 => do
            mkLambdaFVars #[x1, x2] (← leaf name aTy)
        let fn3 (t1 t2 t3 aTy : Expr) (name : String) : MetaM Expr :=
          withLocalDeclD `_1 t1 fun x1 => withLocalDeclD `_2 t2 fun x2 =>
          withLocalDeclD `_3 t3 fun x3 => do
            mkLambdaFVars #[x1, x2, x3] (← leaf name aTy)
        let fn4 (t1 t2 t3 t4 aTy : Expr) (name : String) : MetaM Expr :=
          withLocalDeclD `_1 t1 fun x1 => withLocalDeclD `_2 t2 fun x2 =>
          withLocalDeclD `_3 t3 fun x3 => withLocalDeclD `_4 t4 fun x4 => do
            mkLambdaFVars #[x1, x2, x3, x4] (← leaf name aTy)
        let enf ← withLocalDeclD `_c natTy fun c =>
          withLocalDeclD `_l layoutTy fun l => do
            mkLambdaFVars #[c, l] (← pureM boolTy (mkConst ``Bool.true))
        let usizeL ← withLocalDeclD `_c natTy fun c => do
          mkLambdaFVars #[c] (← pureM layoutTy (← layOf (mkNatLit 25)))
        let ensMono ← withLocalDeclD `_c natTy fun c =>
          withLocalDeclD `_t tyIdTy fun t => do
            mkLambdaFVars #[c, t] (← pureM unitTy (mkConst ``Unit.unit))
        let reqNoBv ← withLocalDeclD `_c natTy fun c =>
          withLocalDeclD `_a arrGArg fun a => do
            mkLambdaFVars #[c, a] (← pureM unitTy (mkConst ``Unit.unit))
        let valAbi ← withLocalDeclD `_i immTy fun i =>
          withLocalDeclD `_l layDataTy fun l => do
            let err ← mkAppM (mi ++ `StepError.unsupported)
              #[mkStrLit "validateImmediateABI"]
            mkLambdaFVars #[i, l]
              (← mkAppOptM ``Except.error
                #[some stepErr, some unitTy, some err])
        mkAppOptM (mi ++ `CastHooks.mk)
          #[some prov, some castS, some natTy, some layoutTy,
            some (mkConst (lm ++ `annealTargetDataLayout)),
            some typeInfo, some layoutOf, some destLayout,
            some readImm, some writeImm,
            some (← fn3 natTy ptrOptTy layoutTy unitTy "writePointer"),
            some enf, some enf,
            some (← fn4 natTy layoutTy boolTy boolTy unitTy "validatePlace"),
            some (← fn2 natTy opTy unitTy "derefPointer"),
            some (← fn2 natTy ptrOptTy unitTy "checkFunctionPointer"),
            some (← fn2 natTy prov unitTy "exposeProvenance"),
            some (← fn2 natTy u64Ty ptrOptTy "pointerFromExposedAddress"),
            some usizeL, some floatHooks, some ensMono, some reqNoBv,
            some (← fn3 natTy defIdTy arrGArg optCallInst "resolveFunction"),
            some (← fn3 natTy defIdTy arrGArg callInstTy "resolveClosure"),
            some (← fn2 natTy callInstTy ptrOptTy "functionPointer"),
            some (← fn3 natTy tyIdTy boolTy optTyId "builtinDeref"),
            some (← fn2 natTy tyIdTy layoutTy "boxLayout"),
            some valAbi, some copyTrans,
            some (← fn4 natTy opTy layoutTy boolTy unitTy "copyNoValidate"),
            some (← fn3 natTy opTy natTy opTy "projectRead"),
            some (← fn3 natTy layoutTy natTy layoutTy "projectWrite"),
            some (← fn3 natTy layoutTy natTy layoutTy "fieldLayout"),
            some (← fn3 natTy tyIdTy tyIdTy prodTyId "lockstepTails"),
            some (← fn3 natTy ptrOptTy optNat tyIdTy "vtableType"),
            some (← fn3 natTy tyIdTy natTy ptrOptTy "vtablePointer"),
            some (← fn2 natTy natTy optNat "principal"),
            some (← fn3 natTy optNat tyIdTy arrVtEntry "vtableEntries"),
            some (← fn3 natTy tyIdTy tyIdTy optNat "supertraitSlot"),
            some (← fn2 natTy natTy natTy "eraseSelfTraitRef"),
            some (← fn2 natTy natTy optNat "normalizePrincipal")]
      let runCast ← withLocalDeclD `flag boolTy fun flag =>
        withLocalDeclD `pick natTy fun pick =>
        withLocalDeclD `srcTyId tyIdTy fun srcTyId =>
        withLocalDeclD `dstTyId tyIdTy fun dstTyId =>
        withLocalDeclD `kind castKindTy fun kind =>
        withLocalDeclD `bits natTy fun bits =>
        withLocalDeclD `srcBytes natTy fun srcBytes => do
          let sc ← switchNat srcBytes
            [(2, ← sc16 bits), (4, ← sc32 bits), (8, ← sc64 bits)]
            (← sc128 bits)
          let imm ← mkAppM (mi ++ `Immediate.scalar) #[sc]
          let op ← mkAppM (mi ++ `Operand.immediate) #[imm]
          let srcOp ← mkAppM (mi ++ `OpTy.mk) #[op, ← layOf srcTyId]
          let dstLay ← layOf dstTyId
          let actCast ← mkAppOptM (mi ++ `Cast.cast)
            #[some prov, some castS, some natTy, some layoutTy,
              some (mkConst `Miri.Memory.instPointerProvenanceProvenance),
              some (← hooksOf flag), some pick, some (mkNatLit 8),
              some srcOp, some kind, some dstTyId, some dstLay]
          let initS ← mkAppOptM ``Option.none #[some immTy]
          let runRes ← mkAppM ``EStateM.run #[actCast, initS]
          let resTy ← mkAppM ``EStateM.Result #[stepErr, castS, unitTy]
          let motive ← withLocalDeclD `_r resTy fun r =>
            mkLambdaFVars #[r] fcObsTy
          let onOk ← withLocalDeclD `_u unitTy fun u =>
            withLocalDeclD `st castS fun st => do
              mkLambdaFVars #[u, st]
                (← mkAppOptM ``Except.ok #[some stepErr, some castS, some st])
          let onErr ← withLocalDeclD `e stepErr fun e =>
            withLocalDeclD `_st castS fun st => do
              mkLambdaFVars #[e, st]
                (← mkAppOptM ``Except.error
                  #[some stepErr, some castS, some e])
          let obs ← mkAppOptM ``EStateM.Result.casesOn
            #[some stepErr, some castS, some unitTy, some motive,
              some runRes, some onOk, some onErr]
          mkLambdaFVars
            #[flag, pick, srcTyId, dstTyId, kind, bits, srcBytes] obs
      let okSc (mkSc : Expr → MetaM Expr) : MetaM Expr :=
        withLocalDeclD `n natTy fun n => do
          let imm ← mkAppM (mi ++ `Immediate.scalar) #[← mkSc n]
          let someImm ← mkAppOptM ``Option.some #[some immTy, some imm]
          mkLambdaFVars #[n]
            (← mkAppOptM ``Except.ok
              #[some stepErr, some castS, some someImm])
      let ret32 ← okSc sc32
      let ret64 ← okSc sc64
      let ubObs ← withLocalDeclD `s (mkConst ``String) fun s => do
        let err ← mkAppM (mi ++ `StepError.undefinedBehavior) #[s]
        mkLambdaFVars #[s]
          (← mkAppOptM ``Except.error #[some stepErr, some castS, some err])
      let uninitObs ← withLocalDeclD `b capMir fun b => do
        let hooks ← mkAppM (lm ++ `annealStepHooksWideSlice)
          #[← mkAppM ``Trusted.Rustc.V2026_06_01.MirAst.CapturedMir.localDecls
              #[b],
            ← mkAppM ``Trusted.Rustc.V2026_06_01.MirAst.CapturedMir.layouts
              #[b]]
        let init ← mkAppM (lw ++ `wideSlice4LocalInitMiri)
          #[b, mkConst (ns ++ `WideSlice.usizeTy),
            mkConst (lw ++ `sampleMiriPtr),
            ← mkAppM ``UInt64.ofNat #[mkNatLit 3],
            ← mkAppM ``UInt64.ofNat #[mkNatLit 1],
            mkConst (lw ++ `sampleArrU32Machine)]
        let r ← mkAppM (mi ++ `Step.step) #[hooks, mkConst ``Unit.unit, init]
        let noneImm ← mkAppOptM ``Option.none #[some immTy]
        let toObs ← withLocalDeclD `_b boolTy fun bb =>
          mkLambdaFVars #[bb] noneImm
        let mapped ← mkAppM ``Except.map #[toObs, ← mkAppM ``Prod.snd #[r]]
        mkLambdaFVars #[b] mapped
      return (runCast, ret32, ret64, ubObs, uninitObs)
    let fcRunCastName := ns ++ `CrossRoot.FloatCast.runCast
    let _ ← addDef fcRunCastName fcRunCast
    added := added.push fcRunCastName
    let fcRunCastC := mkConst fcRunCastName
    let mkFcAuth (invertFlag : Bool) (collideDenote : Bool := false) :
        MetaM Expr := do
      let boolTy := mkConst ``Bool
      let flagOf (f : Expr) : MetaM Expr :=
        if invertFlag then mkAppM ``Bool.not #[f] else pure f
      let f2fObs (srcId dstId srcB : Nat) : MetaM Expr :=
        withLocalDeclD `bits natTy fun bits =>
        withLocalDeclD `flag boolTy fun flag =>
        withLocalDeclD `pick natTy fun pick => do
          let e ← mkAppM fcRunCastName
            #[← flagOf flag, pick, mkNatLit srcId, mkNatLit dstId,
              mkConst `Miri.MIR.CastKind.FloatToFloat, bits, mkNatLit srcB]
          mkLambdaFVars #[bits, flag, pick] e
      let simpleObs (srcId dstId srcB : Nat) (k : Name) : MetaM Expr :=
        withLocalDeclD `bits natTy fun bits => do
          let e ← mkAppM fcRunCastName
            #[mkConst ``Bool.false, mkNatLit 0, mkNatLit srcId,
              mkNatLit dstId, mkConst (`Miri.MIR.CastKind ++ k), bits,
              mkNatLit srcB]
          mkLambdaFVars #[bits] e
      let widenObs ← f2fObs 31 32 4
      let narrowObs ← f2fObs 32 31 8
      let toIntObs ← simpleObs 31 12 4 `FloatToInt
      let fromIntObs ← simpleObs 12 31 4 `IntToFloat
      let carrier32Obs ← simpleObs 22 12 4 `Transmute
      let carrier64Obs ← simpleObs 23 13 8 `Transmute
      let toU64Obs ← simpleObs 32 23 8 `FloatToInt
      let fromU64Obs ← simpleObs 23 32 8 `IntToFloat
      let (r32, r64) ←
        if collideDenote then do
          let c0 ← withLocalDeclD `_n natTy fun n =>
            mkLambdaFVars #[n] (mkApp fcRet32 (mkNatLit 0))
          pure (c0, c0)
        else pure (fcRet32, fcRet64)
      mkAppM (ns ++ `FloatCast.authorityOf)
        #[fcObsTy, decFcObs, widenObs, narrowObs, toIntObs, fromIntObs,
          toU64Obs, fromU64Obs, carrier32Obs, carrier64Obs, fcUninitObs,
          r32, r64, fcUbObs]
    let fcAuth ← MetaM.run' <| mkFcAuth false
    let fcMiriName := ns ++ `CrossRoot.FloatCast.miri
    let _ ← addDef fcMiriName fcAuth
    let fcMiriC := mkConst fcMiriName
    addThm (ns ++ `CrossRoot.FloatCast.miri_matches)
      (eqTrue (mkApp (mkConst (ns ++ `FloatCast.matchesReference)) fcMiriC))
      reflTrue
    addThm (ns ++ `CrossRoot.FloatCast.miri_check)
      (eqTrue (mkApp (mkConst (ns ++ `FloatCast.checkOf)) fcMiriC)) reflTrue
    let fcDenoteC ← MetaM.run' <|
      mkAppOptM (ns ++ `Corpus.ObsAuthority.denoteConsistent)
        #[none, none, some (mkConst ``instDecidableEqNat), some fcMiriC]
    let fcDenoteName := ns ++ `CrossRoot.FloatCast.miri_denoteConsistent
    addThm fcDenoteName (eqTrue fcDenoteC) reflTrue
    let fcDenoteSpec ← MetaM.run' <|
      mkAppOptM (ns ++ `Corpus.ObsAuthority.denoteConsistent_sound)
        #[none, none, some (mkConst ``instDecidableEqNat), some fcMiriC,
          some (mkConst fcDenoteName)]
    let fcDenoteSpecName :=
      ns ++ `CrossRoot.FloatCast.miri_denoteConsistent_spec
    addThm fcDenoteSpecName (← MetaM.run' <| inferType fcDenoteSpec)
      fcDenoteSpec
    added := added ++ #[fcMiriName, ns ++ `CrossRoot.FloatCast.miri_matches,
      ns ++ `CrossRoot.FloatCast.miri_check, fcDenoteName, fcDenoteSpecName]
    -- Tightness of `FloatCast.gateLM` against `Miri.Interpreter.Cast.cast`:
    -- vendored `Cast.cast` converts `1.5f16` (`0x3e00`) and `1.5f128`
    -- (`0x3fff8000000000000000000000000000`) cleanly to `1.5f32`
    -- (`0x3fc00000`), where Anneal fails closed `.unsupported`.
    let (f16Ty, f16Pf, f128Ty, f128Pf) ← MetaM.run' do
      let expected := mkApp fcRet32 (mkNatLit 0x3fc00000)
      let f16Call := mkAppN fcRunCastC
        #[mkConst ``Bool.false, mkNatLit 0, mkNatLit 30, mkNatLit 31,
          mkConst `Miri.MIR.CastKind.FloatToFloat, mkNatLit 0x3e00,
          mkNatLit 2]
      let f128Call := mkAppN fcRunCastC
        #[mkConst ``Bool.false, mkNatLit 0, mkNatLit 33, mkNatLit 31,
          mkConst `Miri.MIR.CastKind.FloatToFloat,
          mkNatLit 0x3fff8000000000000000000000000000, mkNatLit 16]
      return (← mkEq f16Call expected, ← mkEqRefl expected,
        ← mkEq f128Call expected, ← mkEqRefl expected)
    addThm (ns ++ `CrossRoot.FloatCast.f16_gateLM_tight) f16Ty f16Pf
    addThm (ns ++ `CrossRoot.FloatCast.f128_gateLM_tight) f128Ty f128Pf
    -- Unsigned 64-bit boundary casts through vendored `Cast.cast`:
    -- `+∞ ↦ u64::MAX`, halfway ties `2^53 + 1 ↦ 2^53` and `2^53 + 3 ↦
    -- 2^53 + 4`, and `u64::MAX ↦ 2^64`.
    let (u64BndTy, u64BndPf) ← MetaM.run' do
      let u64Cast (src dst : Nat) (k : Name) (bits exp : Nat) :
          MetaM (Expr × Expr) := do
        let call := mkAppN fcRunCastC
          #[mkConst ``Bool.false, mkNatLit 0, mkNatLit src, mkNatLit dst,
            mkConst (`Miri.MIR.CastKind ++ k), mkNatLit bits, mkNatLit 8]
        let rhs := mkApp fcRet64 (mkNatLit exp)
        return (← mkEq call rhs, ← mkEqRefl rhs)
      let (t1, p1) ← u64Cast 32 23 `FloatToInt 0x7ff0000000000000
        0xffffffffffffffff
      let (t2, p2) ← u64Cast 23 32 `IntToFloat (2 ^ 53 + 1)
        0x4340000000000000
      let (t3, p3) ← u64Cast 23 32 `IntToFloat (2 ^ 53 + 3)
        0x4340000000000002
      let (t4, p4) ← u64Cast 23 32 `IntToFloat (2 ^ 64 - 1)
        0x43f0000000000000
      let t34 := mkApp2 (mkConst ``And) t3 t4
      let p34 := mkApp4 (mkConst ``And.intro) t3 t4 p3 p4
      let t234 := mkApp2 (mkConst ``And) t2 t34
      let p234 := mkApp4 (mkConst ``And.intro) t2 t34 p2 p34
      return (mkApp2 (mkConst ``And) t1 t234,
        mkApp4 (mkConst ``And.intro) t1 t234 p1 p234)
    let u64BndName := ns ++ `CrossRoot.FloatCast.u64_overflow_and_tie_cast
    addThm u64BndName u64BndTy u64BndPf
    added := added ++ #[ns ++ `CrossRoot.FloatCast.f16_gateLM_tight,
      ns ++ `CrossRoot.FloatCast.f128_gateLM_tight, u64BndName]
    -- 3b. The vendored float engine agrees with the reference specification
    -- `FloatCast.Ref` primitive by primitive (`decode`, `convert`,
    -- `nanChoices`, `FloatOps.adjustNaN`, `toInteger`, `fromInteger`), and
    -- the type identifiers + byte widths used by `runCast` are
    -- LeanMiriSpec's encodings of the Anneal cast types.
    let fbTy := mkConst (mi ++ `FloatBits)
    let fmtTy := mkConst (mi ++ `FloatFormat)
    -- `engKind`: 0 = valid, 1 = mode-swapped `nanChoices`, 2 = forged
    -- `decode` accepting out-of-width floats, 3 = forged `adjustNaN`
    -- ignoring the oracle pick.
    let mkEngine (engKind : Nat) : MetaM Expr := do
      let boolTy := mkConst ``Bool
      let unitTy := mkConst ``Unit
      let feTy := mkConst (mi ++ `FloatError)
      let fdTy := mkConst (mi ++ `FloatDecoded)
      let refClsTy := mkConst (ns ++ `FloatCast.Ref.Class)
      let refDecTy := mkConst (ns ++ `FloatCast.Ref.Decoded)
      let optRefDecTy ← mkAppM ``Option #[refDecTy]
      let mkB ← withLocalDeclD `f fmtTy fun f =>
        withLocalDeclD `n natTy fun n => do
          mkLambdaFVars #[f, n] (← mkAppM (mi ++ `FloatBits.mk)
            #[f, ← mkAppM ``BitVec.ofNat #[mkNatLit 128, n]])
      let bitsF ← withLocalDeclD `b fbTy fun b => do
        mkLambdaFVars #[b] (← mkAppM ``BitVec.toNat
          #[← mkAppM (mi ++ `FloatBits.bits) #[b]])
      let decFn ← withLocalDeclD `b fbTy fun b => do
        let decCall ← mkAppM (mi ++ `FloatBits.decode) #[b]
        let exTy ← mkAppM ``Except #[feTy, fdTy]
        let motiveE ← withLocalDeclD `_e exTy fun e =>
          mkLambdaFVars #[e] optRefDecTy
        let onErr ← withLocalDeclD `_err feTy fun err => do
          if engKind == 2 then
            let infDec := mkApp2 (mkConst (ns ++ `FloatCast.Ref.Decoded.mk))
              (mkConst ``Bool.false)
              (mkConst (ns ++ `FloatCast.Ref.Class.infinite))
            mkLambdaFVars #[err]
              (← mkAppOptM ``Option.some #[some refDecTy, some infDec])
          else
            mkLambdaFVars #[err]
              (← mkAppOptM ``Option.none #[some refDecTy])
        let onOk ← withLocalDeclD `fd fdTy fun fd => do
          let neg ← mkAppM (mi ++ `FloatDecoded.negative) #[fd]
          let val ← mkAppM (mi ++ `FloatDecoded.value) #[fd]
          let motiveC ← withLocalDeclD `_c (mkConst (mi ++ `FloatClass))
            fun c => mkLambdaFVars #[c] refClsTy
          let onFin ← withLocalDeclD `n natTy fun n =>
            withLocalDeclD `d natTy fun d =>
              mkLambdaFVars #[n, d]
                (mkApp2 (mkConst (ns ++ `FloatCast.Ref.Class.finite)) n d)
          let onInf := mkConst (ns ++ `FloatCast.Ref.Class.infinite)
          let onNan ← withLocalDeclD `p natTy fun p =>
            mkLambdaFVars #[p]
              (mkApp (mkConst (ns ++ `FloatCast.Ref.Class.nan)) p)
          let cls ← mkAppOptM (mi ++ `FloatClass.casesOn)
            #[some motiveC, some val, some onFin, some onInf, some onNan]
          let decV := mkApp2 (mkConst (ns ++ `FloatCast.Ref.Decoded.mk))
            neg cls
          mkLambdaFVars #[fd]
            (← mkAppOptM ``Option.some #[some refDecTy, some decV])
        let body ← mkAppOptM ``Except.casesOn
          #[some feTy, some fdTy, some motiveE, some decCall, some onErr,
            some onOk]
        mkLambdaFVars #[b] body
      let listFb ← mkAppM ``List #[fbTy]
      let nanCh ←
        if engKind == 1 then
          withLocalDeclD `f fmtTy fun f =>
          withLocalDeclD `l listFb fun l =>
          withLocalDeclD `_b boolTy fun b => do
            mkLambdaFVars #[f, l, b] (← mkAppM (mi ++ `FloatBits.nanChoices)
              #[f, l, mkConst ``Bool.true])
        else pure (mkConst (mi ++ `FloatBits.nanChoices))
      let tyIdTy := mkConst `Miri.MIR.TyId
      let intKindTy := mkConst `Miri.MIR.IntegerKind
      let layoutTy ← mkAppM `Miri.ABI.TyAndLayout #[tyIdTy]
      let optFbTy ← mkAppM ``Option #[fbTy]
      let leafU (name : String) (aTy : Expr) : MetaM Expr :=
        mkAppOptM (lm ++ `annealUnsupportedLeaf)
          #[some unitTy, some aTy, some (mkStrLit name)]
      let kindOfU ← withLocalDeclD `_c natTy fun c =>
        withLocalDeclD `_t tyIdTy fun t => do
          mkLambdaFVars #[c, t] (← leafU "integerKindOf" intKindTy)
      let fmtOfU ← withLocalDeclD `_c natTy fun c =>
        withLocalDeclD `_t tyIdTy fun t => do
          mkLambdaFVars #[c, t] (← leafU "formatOf" fmtTy)
      let boolLayU ← withLocalDeclD `_c natTy fun c => do
        mkLambdaFVars #[c] (← leafU "boolLayout" layoutTy)
      let chooseU ← withLocalDeclD `c natTy fun c =>
        withLocalDeclD `cands listFb fun cands => do
          let idx ←
            if engKind == 3 then pure (mkNatLit 0)
            else mkAppM ``Nat.mod #[c, ← mkAppM ``List.length #[cands]]
          mkLambdaFVars #[c, cands]
            (← mkAppOptM ``EStateM.pure
              #[some stepErr, some unitTy, some natTy, some idx])
      let adjFn ← withLocalDeclD `flag boolTy fun flag =>
        withLocalDeclD `pick natTy fun pick =>
        withLocalDeclD `val fbTy fun val =>
        withLocalDeclD `inps listFb fun inps => do
          let fHooks ← mkAppOptM (mi ++ `FloatOpsHooks.mk)
            #[some prov, some unitTy, some natTy, some kindOfU, some fmtOfU,
              some boolLayU, some flag, some chooseU]
          let actAdj ← mkAppOptM (mi ++ `FloatOps.adjustNaN)
            #[some prov, some unitTy, some natTy, some fHooks, some pick,
              some val, some inps]
          let runAdj ← mkAppM ``EStateM.run #[actAdj, mkConst ``Unit.unit]
          let resTy ← mkAppM ``EStateM.Result #[stepErr, unitTy, fbTy]
          let motiveR ← withLocalDeclD `_r resTy fun r =>
            mkLambdaFVars #[r] optFbTy
          let onOkR ← withLocalDeclD `fb fbTy fun fb =>
            withLocalDeclD `_st unitTy fun st => do
              mkLambdaFVars #[fb, st]
                (← mkAppOptM ``Option.some #[some fbTy, some fb])
          let onErrR ← withLocalDeclD `_e stepErr fun e =>
            withLocalDeclD `_st unitTy fun st => do
              mkLambdaFVars #[e, st]
                (← mkAppOptM ``Option.none #[some fbTy])
          let res ← mkAppOptM ``EStateM.Result.casesOn
            #[some stepErr, some unitTy, some fbTy, some motiveR, some runAdj,
              some onOkR, some onErrR]
          mkLambdaFVars #[flag, pick, val, inps] res
      return mkAppN (mkConst (ns ++ `FloatCast.Engine.mk))
        #[fmtTy, fbTy, feTy,
          mkConst (mi ++ `FloatFormat.binary32),
          mkConst (mi ++ `FloatFormat.binary64), mkB, bitsF,
          mkConst (mi ++ `FloatBits.preferredNaN), decFn,
          mkConst (mi ++ `FloatBits.convert), nanCh, adjFn,
          mkConst (mi ++ `FloatBits.toInteger),
          mkConst (mi ++ `FloatBits.fromInteger)]
    let engName := ns ++ `CrossRoot.FloatCast.engine
    let _ ← addDef engName (← MetaM.run' <| mkEngine 0)
    let engC := mkConst engName
    let engAgreesName := ns ++ `CrossRoot.FloatCast.engine_agrees
    addThm engAgreesName
      (eqTrue (mkApp (mkConst (ns ++ `FloatCast.Engine.agrees)) engC))
      reflTrue
    let engSpec := mkApp2 (mkConst (ns ++ `FloatCast.Engine.agrees_sound))
      engC (mkConst engAgreesName)
    let engSpecName := ns ++ `CrossRoot.FloatCast.engine_agrees_spec
    addThm engSpecName (← MetaM.run' <| inferType engSpec) engSpec
    -- Direct statements over the vendored constants: preferred NaNs,
    -- out-of-width `decode` `.encodingExceedsWidth` errors, and `nanChoices`
    -- across widening quiet NaN, widening signaling NaN, and narrowing
    -- signaling NaN in both modes.
    let (directTys, directPfs) ← MetaM.run' do
      let refC (n : Name) : Expr := mkConst (ns ++ `FloatCast.Ref ++ n)
      let bitsOfFb (b : Expr) : MetaM Expr := do
        mkAppM ``BitVec.toNat #[← mkAppM (mi ++ `FloatBits.bits) #[b]]
      let pref (f r : Name) : MetaM (Expr × Expr) := do
        let lhs ← bitsOfFb (← mkAppM (mi ++ `FloatBits.preferredNaN)
          #[mkConst (mi ++ `FloatFormat ++ f)])
        let rhs := mkApp (refC `preferredNaN) (refC (`Fmt ++ r))
        return (← mkEq lhs rhs, ← mkEqRefl lhs)
      let choicesAt (src dst : Name) (bits : Nat) (flag : Name) :
          MetaM (Expr × Expr) := do
        let input ← mkAppM (mi ++ `FloatBits.mk)
          #[mkConst (mi ++ `FloatFormat ++ src),
            ← mkAppM ``BitVec.ofNat #[mkNatLit 128, mkNatLit bits]]
        let call ← mkAppM (mi ++ `FloatBits.nanChoices)
          #[mkConst (mi ++ `FloatFormat ++ dst),
            ← mkListLit fbTy [input], mkConst flag]
        let bitsF ← withLocalDeclD `b fbTy fun b => do
          mkLambdaFVars #[b] (← bitsOfFb b)
        let lhs ← mkAppM ``Option.map
          #[← mkAppM ``List.map #[bitsF], ← mkAppM ``Except.toOption #[call]]
        let pairTy ← mkAppM ``Prod #[refC `Fmt, natTy]
        let pair ← mkAppM ``Prod.mk #[refC (`Fmt ++ src), mkNatLit bits]
        let rhs := mkApp3 (refC `nanChoices) (refC (`Fmt ++ dst))
          (← mkListLit pairTy [pair]) (mkConst flag)
        return (← mkEq lhs rhs, ← mkEqRefl lhs)
      let oobDec (f : Name) (bits : Nat) : MetaM (Expr × Expr) := do
        let inp ← mkAppM (mi ++ `FloatBits.mk)
          #[mkConst (mi ++ `FloatFormat ++ f),
            ← mkAppM ``BitVec.ofNat #[mkNatLit 128, mkNatLit bits]]
        let lhs ← mkAppM (mi ++ `FloatBits.decode) #[inp]
        let rhs ← mkAppOptM ``Except.error
          #[some (mkConst (mi ++ `FloatError)),
            some (mkConst (mi ++ `FloatDecoded)),
            some (mkConst (mi ++ `FloatError.encodingExceedsWidth))]
        return (← mkEq lhs rhs, ← mkEqRefl lhs)
      let ds ←
        [pref `binary32 `binary32, pref `binary64 `binary64,
         choicesAt `binary32 `binary64 0x7f800001 ``Bool.true,
         choicesAt `binary32 `binary64 0x7f800001 ``Bool.false,
         choicesAt `binary32 `binary64 0x7fc00001 ``Bool.true,
         choicesAt `binary64 `binary32 0x7ff0000020000000 ``Bool.true,
         choicesAt `binary64 `binary32 0x7ff0000020000000 ``Bool.false,
         oobDec `binary32 (2 ^ 32), oobDec `binary64 (2 ^ 64)].mapM id
      return (ds.map (·.1), ds.map (·.2))
    let directNames : List Name :=
      [`preferredNaN32_eq, `preferredNaN64_eq, `nanChoices_signaling_nondet,
        `nanChoices_signaling_det, `nanChoices_quiet_widen_nondet,
        `nanChoices_narrow_signaling_nondet, `nanChoices_narrow_signaling_det,
        `decode_oob32_eq_error, `decode_oob64_eq_error]
    for (n, ty, pf) in directNames.zip (directTys.zip directPfs) do
      addThm (ns ++ `CrossRoot.FloatCast ++ n) ty pf
      added := added.push (ns ++ `CrossRoot.FloatCast ++ n)
    let castIds : List (Name × Nat × Nat) :=
      [(`f32ToF64, 31, 32), (`f64ToF32, 32, 31), (`f32ToI32, 31, 12),
        (`i32ToF32, 12, 31), (`bitsU32ToI32, 22, 12),
        (`bitsU64ToI64, 23, 13), (`f64ToU64, 32, 23), (`u64ToF64, 23, 32),
        (`f16ToF32, 30, 31), (`f128ToF32, 33, 31)]
    let tyIdLock (prog : Name) (src dst : Nat)
        (srcWidthOverride? : Option Nat := none)
        (dstWidthOverride? : Option Nat := none) : MetaM (Expr × Expr) := do
      let progC := mkConst (ns ++ `FloatCast.Prog ++ prog)
      let shape := mkApp (mkConst (ns ++ `FloatCast.castShape)) progC
      let srcTy ← mkAppM ``Prod.fst #[shape]
      let rest ← mkAppM ``Prod.snd #[shape]
      let srcBytes ← mkAppM ``Prod.fst #[rest]
      let dstTy ← mkAppM ``Prod.fst #[← mkAppM ``Prod.snd #[rest]]
      let dstBytes := mkApp (mkConst (ns ++ `FloatCast.dstBytes)) progC
      let enc (t : Expr) : Expr := mkApp (mkConst (lm ++ `encodeTyId)) t
      let empLay :=
        mkConst ``Trusted.Rustc.V2026_06_01.MirSemantics.emptyLayoutTable
      let laySize (id : Nat) : MetaM Expr := do
        let lay :=
          mkApp2 (mkConst (lm ++ `layoutOfEncodedTyId)) (mkNatLit id) empLay
        mkAppM ``UInt64.toNat
          #[← mkAppM `Miri.ABI.Size.bytes
            #[← mkAppM `Miri.ABI.LayoutData.size
              #[← mkAppM `Miri.ABI.TyAndLayout.layout #[lay]]]]
      let srcLayBytes ← laySize src
      let dstLayBytes ← laySize dst
      let targetSrc := match srcWidthOverride? with
        | some w => mkNatLit w
        | none => srcBytes
      let targetDst := match dstWidthOverride? with
        | some w => mkNatLit w
        | none => dstBytes
      let e1 ← mkEq (enc srcTy) (mkNatLit src)
      let e2 ← mkEq (enc dstTy) (mkNatLit dst)
      let e3 ← mkEq srcLayBytes targetSrc
      let e4 ← mkEq dstLayBytes targetDst
      let e34 := mkApp2 (mkConst ``And) e3 e4
      let pf34 := mkApp4 (mkConst ``And.intro) e3 e4
        (← mkEqRefl srcLayBytes) (← mkEqRefl dstLayBytes)
      let e234 := mkApp2 (mkConst ``And) e2 e34
      let pf234 := mkApp4 (mkConst ``And.intro) e2 e34
        (← mkEqRefl (enc dstTy)) pf34
      return (mkApp2 (mkConst ``And) e1 e234,
        mkApp4 (mkConst ``And.intro) e1 e234 (← mkEqRefl (enc srcTy)) pf234)
    for (prog, src, dst) in castIds do
      let (ty, pf) ← MetaM.run' <| tyIdLock prog src dst
      let name := ns ++ `CrossRoot.FloatCast.tyIdLock ++ prog
      addThm name ty pf
      added := added.push name
    added := added ++ #[engName, engAgreesName, engSpecName]
    -- 4. Bundles and theorems over the vendored interpreter: every
    -- `*_with` declaration instantiated at the cross-root authority.
    let mut bundleCount : Nat := 0
    for (fam, auth, withs, defs) in
        [(`WideSlice, miriC, wsWith, wsDefs),
         (`FloatCast, fcMiriC, fcWith, fcDefs)] do
      let verdict := mkApp (mkConst (ns ++ fam ++ `verdictOf)) auth
      let check := mkConst (ns ++ `CrossRoot ++ fam ++ `miri_check)
      let agreesName := ns ++ `CrossRoot ++ fam ++ `miri_agrees
      let agrees := mkApp2
        (mkConst (ns ++ fam ++ `matchesReference_sound)) auth
        (mkConst (ns ++ `CrossRoot ++ fam ++ `miri_matches))
      addThm agreesName (← MetaM.run' <| inferType agrees) agrees
      added := added.push agreesName
      for d in defs do
        let name := ns ++ `CrossRoot ++ fam ++ d
        let ty ← addDef name (mkApp2 (mkConst (ns ++ fam ++ d)) verdict check)
        unless ty.getAppFn.isConstOf
            ``Anneal.DualCorrespondenceBundle.DualCorrespondenceBundle do
          throwError "cross-root: {name} is not a bundle: {ty}"
        bundleCount := bundleCount + 1
        added := added.push name
      for t in withs do
        let name := ns ++ `CrossRoot ++ fam ++ t
        let value := mkApp2 (mkConst (ns ++ fam ++ t)) verdict check
        let ty ← MetaM.run' <| inferType value
        unless ty.getUsedConstantsAsSet.contains auth.constName! do
          throwError "cross-root: {name} does not mention the authority"
        addThm name ty value
        added := added.push name
    let fcVacName := ns ++ `CrossRoot.FloatCast.empty_schedule_is_vacuous
    let fcVacVal := mkApp
      (mkConst (ns ++ `FloatCast.empty_schedule_is_vacuous))
      (mkApp (mkConst (ns ++ `FloatCast.verdictOf)) fcMiriC)
    addThm fcVacName (← MetaM.run' <| inferType fcVacVal) fcVacVal
    added := added.push fcVacName
    -- 5. Fixture locks: the Anneal fixtures of this file are the fixtures
    -- of the LeanMiri correspondence module.
    let lockEq (name : Name) (lhs rhs : Expr) (xs : Array Expr) :
        MetaM (Name × Expr × Expr) := do
      let ty ← mkForallFVars xs (← mkEq lhs rhs)
      let pf ← mkLambdaFVars xs (← mkEqRefl lhs)
      return (name, ty, pf)
    let ws (n : Name) : Expr := mkConst (ns ++ `WideSlice ++ n)
    let lwc (n : Name) : Expr := mkConst (lw ++ n)
    let locks ← MetaM.run' do
      let mut out : Array (Name × Expr × Expr) := #[]
      out := out.push (← lockEq `metadataBody (ws `metadataBody)
        (lwc `wideSliceSingleMetadataBody) #[])
      out := out.push (← lockEq `placeLenBody (ws `placeLenBody)
        (lwc `wideSliceSingleLenBody) #[])
      out := out.push (← lockEq `indexReadBody (ws `indexReadBody)
        (lwc `wideSliceSingleIndexReadBody) #[])
      out := out.push (← lockEq `sizeOfValBody (ws `sizeOfValBody)
        (← mkAppM (lw ++ `singleWideIntrinsicBody)
          #[mkConst ``Bool.false, lwc `rawSliceU32Ty,
            lwc `sliceU32PointeeTy]) #[])
      out := out.push (← withLocalDeclD `r (ws `Regime) fun r => do
        lockEq `reborrowBody (mkApp (ws `reborrowBody) r)
          (← mkAppM (lw ++ `wideSliceReborrowBody)
            #[mkApp (ws `reborrowTy) r, mkApp (ws `reborrowRvalue) r])
          #[r])
      out := out.push (← withLocalDeclD `len natTy fun len =>
        withLocalDeclD `idx natTy fun idx => do
          lockEq `frameInit (mkApp2 (ws `frameInit) len idx)
            (← mkAppM (lw ++ `wideSlice4LocalInitAnneal)
              #[lwc `sampleAnnealPtr, len, idx, lwc `sampleAnnealArrMemory])
            #[len, idx])
      out := out.push (← withLocalDeclD `len natTy fun len => do
        lockEq `sizeOfValInit (mkApp (ws `sizeOfValInit) len)
          (← mkAppM (lw ++ `singleWideIntrinsicInitAnneal)
            #[mkApp (ws `wideVal) len]) #[len])
      out := out.push (← lockEq `pipelineBody (ws `pipelineBody)
        (lwc `wideSlicePipelineBody) #[])
      out := out.push (← lockEq `pipelineInit (ws `pipelineInit)
        (lwc `wideSlicePipelineInitAnneal) #[])
      return out
    for (n, ty, pf) in locks do
      let name := ns ++ `CrossRoot.WideSlice.lock ++ n
      addThm name ty pf
      added := added.push name
    -- 6. Negative self-tests on scratch copies of the environment: the
    -- kernel must reject each forged declaration across both families.
    let saved ← getEnv
    let rejects (d : Declaration) : CoreM Bool := do
      let r ← try addDecl d; pure false catch _ => pure true
      setEnv saved
      return r
    let boolFalse := mkConst ``Bool.false
    let forgedAuth ← MetaM.run' <| mkAppM (ns ++ `WideSlice.authorityOf)
      #[obsTy, decObs, wsFrameObs, wsSizeObs, wsPipelineObs, wsRetU32,
        wsRetU32, wsRetWide, wsUbObs]
    let collidingAuth ← MetaM.run' do
      let constObs ← withLocalDeclD `_n natTy fun n =>
        mkLambdaFVars #[n] (mkApp wsRetU32 (mkNatLit 0))
      mkAppM (ns ++ `WideSlice.authorityOf)
        #[obsTy, decObs, wsFrameObs, wsSizeObs, wsPipelineObs, constObs,
          constObs, wsRetWide, wsUbObs]
    let collidingDenote ← MetaM.run' <|
      mkAppOptM (ns ++ `Corpus.ObsAuthority.denoteConsistent)
        #[none, none, some (mkConst ``instDecidableEqNat), some collidingAuth]
    let forgedFcAuth ← MetaM.run' <| mkFcAuth true
    let collidingFcAuth ← MetaM.run' <| mkFcAuth false true
    let collidingFcDenote ← MetaM.run' <|
      mkAppOptM (ns ++ `Corpus.ObsAuthority.denoteConsistent)
        #[none, none, some (mkConst ``instDecidableEqNat),
          some collidingFcAuth]
    let forgedEngine ← MetaM.run' <| mkEngine 1
    let forgedDecodeEngine ← MetaM.run' <| mkEngine 2
    let forgedAdjustEngine ← MetaM.run' <| mkEngine 3
    let (forgedTyIdTy, forgedTyIdPf) ← MetaM.run' <| tyIdLock `f32ToF64 32 31
    let (forgedWidthTy, forgedWidthPf) ← MetaM.run' <|
      tyIdLock `f32ToF64 31 32 (some 8)
    let (forgedDstWidthTy, forgedDstWidthPf) ← MetaM.run' <|
      tyIdLock `f32ToF64 31 32 none (some 4)
    let (forgedF16Ty, forgedF16Pf) ← MetaM.run' do
      let bad := mkApp fcRet32 (mkNatLit 0x3f800000)
      let f16Call := mkAppN fcRunCastC
        #[mkConst ``Bool.false, mkNatLit 0, mkNatLit 30, mkNatLit 31,
          mkConst `Miri.MIR.CastKind.FloatToFloat, mkNatLit 0x3e00,
          mkNatLit 2]
      return (← mkEq f16Call bad, ← mkEqRefl bad)
    let (forgedTieTy, forgedTiePf) ← MetaM.run' do
      let bad := mkApp fcRet64 (mkNatLit 0x4340000000000001)
      let tieCall := mkAppN fcRunCastC
        #[mkConst ``Bool.false, mkNatLit 0, mkNatLit 23, mkNatLit 32,
          mkConst `Miri.MIR.CastKind.IntToFloat, mkNatLit (2 ^ 53 + 1),
          mkNatLit 8]
      return (← mkEq tieCall bad, ← mkEqRefl bad)
    let forged : List (String × Declaration) :=
      [("ill-typed theorem", .thmDecl
          { name := ns ++ `CrossRoot.forged.zeroEqOne
            levelParams := []
            type := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 0) (mkNatLit 1)
            value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 0) }),
       ("ill-typed definition", .defnDecl
          { name := ns ++ `CrossRoot.forged.natTrue
            levelParams := []
            type := natTy
            value := boolTrue
            hints := .regular 0
            safety := .safe }),
       ("negated WideSlice certificate", .thmDecl
          { name := ns ++ `CrossRoot.forged.checkFalse
            levelParams := []
            type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
              (mkApp (mkConst (ns ++ `WideSlice.checkOf)) miriC) boolFalse
            value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool)
              boolFalse }),
       ("certificate of a forged WideSlice authority", .thmDecl
          { name := ns ++ `CrossRoot.forged.forgedCheck
            levelParams := []
            type := eqTrue
              (mkApp (mkConst (ns ++ `WideSlice.checkOf)) forgedAuth)
            value := reflTrue }),
       ("agreement of a forged WideSlice authority", .thmDecl
          { name := ns ++ `CrossRoot.forged.forgedMatches
            levelParams := []
            type := eqTrue
              (mkApp (mkConst (ns ++ `WideSlice.matchesReference))
                forgedAuth)
            value := reflTrue }),
       ("colliding WideSlice denote table", .thmDecl
          { name := ns ++ `CrossRoot.forged.collidingDenote
            levelParams := []
            type := eqTrue collidingDenote
            value := reflTrue }),
       ("swapped fixture lock", .thmDecl
          { name := ns ++ `CrossRoot.forged.swappedLock
            levelParams := []
            type := mkApp3 (mkConst ``Eq [1]) capMir (ws `metadataBody)
              (lwc `wideSliceSingleLenBody)
            value := mkApp2 (mkConst ``Eq.refl [1]) capMir
              (ws `metadataBody) }),
       ("negated FloatCast certificate", .thmDecl
          { name := ns ++ `CrossRoot.forged.fcCheckFalse
            levelParams := []
            type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool)
              (mkApp (mkConst (ns ++ `FloatCast.checkOf)) fcMiriC) boolFalse
            value := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool)
              boolFalse }),
       ("mode-inverted FloatCast authority certificate", .thmDecl
          { name := ns ++ `CrossRoot.forged.fcInvertedCheck
            levelParams := []
            type := eqTrue
              (mkApp (mkConst (ns ++ `FloatCast.checkOf)) forgedFcAuth)
            value := reflTrue }),
       ("mode-inverted FloatCast authority agreement", .thmDecl
          { name := ns ++ `CrossRoot.forged.fcInvertedMatches
            levelParams := []
            type := eqTrue
              (mkApp (mkConst (ns ++ `FloatCast.matchesReference))
                forgedFcAuth)
            value := reflTrue }),
       ("wrong f16 Cast.cast result", .thmDecl
          { name := ns ++ `CrossRoot.forged.fcWrongF16
            levelParams := []
            type := forgedF16Ty
            value := forgedF16Pf }),
       ("agreement of a mode-swapped float engine", .thmDecl
          { name := ns ++ `CrossRoot.forged.engineSwapped
            levelParams := []
            type := eqTrue
              (mkApp (mkConst (ns ++ `FloatCast.Engine.agrees)) forgedEngine)
            value := reflTrue }),
       ("agreement of an out-of-width-accepting float engine", .thmDecl
          { name := ns ++ `CrossRoot.forged.engineBadDecode
            levelParams := []
            type := eqTrue
              (mkApp (mkConst (ns ++ `FloatCast.Engine.agrees))
                forgedDecodeEngine)
            value := reflTrue }),
       ("agreement of a pick-ignoring adjustNaN float engine", .thmDecl
          { name := ns ++ `CrossRoot.forged.engineBadAdjust
            levelParams := []
            type := eqTrue
              (mkApp (mkConst (ns ++ `FloatCast.Engine.agrees))
                forgedAdjustEngine)
            value := reflTrue }),
       ("wrong type-identifier lock", .thmDecl
          { name := ns ++ `CrossRoot.forged.wrongTyId
            levelParams := []
            type := forgedTyIdTy
            value := forgedTyIdPf }),
       ("wrong byte-width type-identifier lock", .thmDecl
          { name := ns ++ `CrossRoot.forged.wrongTyWidth
            levelParams := []
            type := forgedWidthTy
            value := forgedWidthPf }),
       ("wrong destination byte-width type-identifier lock", .thmDecl
          { name := ns ++ `CrossRoot.forged.wrongDstTyWidth
            levelParams := []
            type := forgedDstWidthTy
            value := forgedDstWidthPf }),
       ("colliding FloatCast denote table", .thmDecl
          { name := ns ++ `CrossRoot.forged.collidingFcDenote
            levelParams := []
            type := eqTrue collidingFcDenote
            value := reflTrue }),
       ("wrong u64 tie-to-even Cast.cast result", .thmDecl
          { name := ns ++ `CrossRoot.forged.wrongU64Tie
            levelParams := []
            type := forgedTieTy
            value := forgedTiePf })]
    let mut rejected : Nat := 0
    for (what, d) in forged do
      unless ← rejects d do
        throwError "cross-root: the kernel accepted a forged {what}"
      rejected := rejected + 1
    -- 7. Inspection of every cross-root declaration: kernel-checked
    -- definitions and theorems only, with standard axioms only (plus
    -- self-tests of the cross-root axiom checker).
    let env ← getEnv
    let isStdAx (a : Name) : Bool :=
      a == ``propext || a == ``Classical.choice || a == ``Quot.sound
    let mut crAxioms : NameSet := {}
    for n in added do
      let some ci := env.find? n
        | throwError "cross-root: {n} is missing"
      match ci with
      | .defnInfo v =>
        if v.safety != .safe then throwError "cross-root: {n} is not safe"
      | .thmInfo _ =>
        if Anneal.DualCorrespondenceAndTbPruningTests.Audit.trivialProp
            ci.type then
          throwError "cross-root: {n} is trivial"
      | _ => throwError "cross-root: {n} is not a definition or theorem"
      for a in ← collectAxioms n do
        unless isStdAx a do
          throwError "cross-root: {n} depends on the axiom {a}"
        crAxioms := crAxioms.insert a
    unless !(← collectAxioms ``sorryAx).all isStdAx do
      throwError "cross-root self-test: `sorryAx` was not detected"
    unless !(← collectAxioms ``Lean.ofReduceBool).all isStdAx do
      throwError "cross-root self-test: `Lean.ofReduceBool` was not detected"
    let crTrivialProp :=
      Anneal.DualCorrespondenceAndTbPruningTests.Audit.trivialProp
    let crRefl := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
    let crLetRefl := Expr.letE `x natTy (mkNatLit 1)
      (mkApp3 (mkConst ``Eq [1]) natTy (.bvar 0) (.bvar 0)) false
    unless crTrivialProp crRefl && crTrivialProp crLetRefl &&
        !crTrivialProp f16Ty do
      throwError "cross-root self-test: trivial theorem detector failed"
    -- The authorities, `runCast`, `engine`, and every one of the 12
    -- cross-root bundles genuinely reach BOTH MiniRust and vendored Miri.
    let mut reachChecks : List (Name × List Name) :=
      [(miriName,
        [mi ++ `Step.step, mi ++ `Cast.cast,
          lm ++ `annealStepHooksWideSlice, lw ++ `wideSlicePipelineMiri4,
          lw ++ `wideSlicePipelineInitMiri, lw ++ `wideSlicePipelineHooks]),
       (fcRunCastName,
        [mi ++ `Cast.cast, mi ++ `Cast.castFromIntLike,
          mi ++ `FloatOps.readBits, mi ++ `FloatOps.adjustNaN,
          mi ++ `FloatBits.nanChoices, mi ++ `FloatBits.preferredNaN,
          mi ++ `FloatBits.convert, mi ++ `FloatBits.decode,
          mi ++ `FloatBits.toInteger, mi ++ `FloatBits.fromInteger]),
       (fcMiriName,
        [fcRunCastName, mi ++ `Cast.cast, mi ++ `Step.step]),
       (engName,
        [mi ++ `FloatBits.nanChoices, mi ++ `FloatBits.preferredNaN,
          mi ++ `FloatBits.convert, mi ++ `FloatBits.decode,
          mi ++ `FloatBits.toInteger, mi ++ `FloatBits.fromInteger,
          mi ++ `FloatOps.adjustNaN])]
    for d in wsDefs do
      reachChecks := reachChecks ++
        [(ns ++ `CrossRoot.WideSlice ++ d,
          [`MiniRustSpec.Interp.stepsTB, mi ++ `Step.step, mi ++ `Cast.cast,
            lw ++ `wideSlicePipelineMiri4])]
    for d in fcDefs do
      reachChecks := reachChecks ++
        [(ns ++ `CrossRoot.FloatCast ++ d,
          [`MiniRustSpec.Interp.transmute,
            `MiniRustSpec.Correspondence.translateRvalue, mi ++ `Cast.cast,
            mi ++ `FloatOps.adjustNaN, mi ++ `FloatBits.nanChoices,
            mi ++ `Step.step])]
    for (auth, needed) in reachChecks do
      let mut reach : NameSet := {}
      let mut todo : Array Name := #[auth]
      while !todo.isEmpty do
        let n := todo.back!
        todo := todo.pop
        if reach.contains n then continue
        reach := reach.insert n
        if let some ci := env.find? n then
          for d in ci.getUsedConstantsAsSet do
            if !reach.contains d then todo := todo.push d
      for n in needed do
        unless reach.contains n do
          throwError "cross-root: {auth} does not reach {n}"
    return (replayed, added.size, bundleCount, rejected, crAxioms.toArray)
  let ctx : Core.Context :=
    { fileName := "<cross-root>"
      fileMap := default
      options := opts
      maxHeartbeats := 0 }
  let ((replayed, added, bundles, rejected, crAxioms), _) ←
    liftCoreM <| (act.toIO ctx { env := baseEnv })
  unless replayed ≥ 850 && added ≥ 106 && bundles = 12 && rejected = 19 do
    throwError "cross-root: unexpected counts \
      (replayed={replayed}, added={added}, bundles={bundles}, \
      rejected={rejected})"
  logInfo m!"cross-root kernel bridge: replayed {replayed} surface \
    declarations, added {added} cross-root declarations ({bundles} \
    bundles), rejected {rejected} forged declarations, axioms {crAxioms}"

/-! ## H. Constructive-axiom and transitive-reachability audit

Fail-closed audit of both modules under test and of every declaration of
this file (public, private, and compiler-generated): only kernel-checked safe
definitions, theorems, and inductive types (nothing opaque, postulated, or
outside the safe fragment), no trivial theorems, no stray public or private
declarations outside the test namespace, axiom closures within
`[propext, Quot.sound]`, the declaration-count floors of both modules, and
transitive reachability of every public theorem of both modules from the
declarations of this file, with no exemption list. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let testNs := `Anneal.DualCorrespondenceAndTbPruningTests
  let trivialProp :=
    Anneal.DualCorrespondenceAndTbPruningTests.Audit.trivialProp
  let modules : List (Name × Nat × Nat) :=
    [(`Anneal.DualCorrespondenceBundle, 700, 228),
     (`Anneal.TreeBorrowsPruningAndFrameWp, 950, 378)]
  -- Union of the axiom closures of `names`.
  let scanAxioms (names : Array Name) : CommandElabM (Array Name) := do
    let mut acc : NameSet := {}
    for n in names do
      for a in ← liftCoreM <| Lean.collectAxioms n do
        acc := acc.insert a
    return acc.toArray
  let constructive (axs : Array Name) : Bool :=
    axs.all fun a => a == ``propext || a == ``Quot.sound
  -- Declarations that are not kernel-checked safe definitions.
  let rejected (ci : ConstantInfo) : Bool :=
    match ci with
    | .defnInfo v => v.safety != .safe
    | .opaqueInfo _ => true
    | .axiomInfo _ => true
    | .inductInfo v => v.isUnsafe
    | .ctorInfo v => v.isUnsafe
    | .recInfo v => v.isUnsafe
    | .thmInfo _ => false
    | .quotInfo _ => false
  -- User-visible name after stripping any `_private.<mod>.<idx>.` prefix, so
  -- user-authored `private` declarations are not mistaken for compiler
  -- internals (`_proof_*`, `match_*`).
  let userName (n : Name) : Name :=
    (Lean.privateToUserName? n).getD n
  -- Trivial theorem detector: `True` for every theorem, and additionally all
  -- `trivialProp` shapes for every user-authored (public or `private`) theorem;
  -- compiler-abstracted `_proof_*` obligations remain legitimately reflexive.
  let isTrivialThm (ci : ConstantInfo) : Bool :=
    match ci with
    | .thmInfo v =>
      v.type.isConstOf ``True ||
        (!(userName ci.name).isInternal && trivialProp v.type)
    | _ => false
  -- Lazy equational lemma (`*.eq_*` / `*.eq_def`, or private
  -- `<imported>.match_*.eq_*`) synthesized on demand in `map₂` for an imported
  -- definition.
  let isLazyEq (n : Name) (ci : ConstantInfo) : Bool :=
    let u := userName n
    let pre := u.getPrefix
    let leaf := match u with | .str _ s => s | _ => ""
    let preLeaf := match pre with | .str _ s => s | _ => ""
    let parentImportedDef :=
      (env.getModuleIdxFor? pre).isSome &&
        (match env.find? pre with
          | some (.defnInfo _) => true
          | _ => false)
    (!Lean.isPrivateName n || preLeaf.startsWith "match_") &&
    (match ci with | .thmInfo _ => true | _ => false) &&
    (leaf.startsWith "eq_" || leaf == "eq_def") && parentImportedDef
  -- Lazy matcher splitter (`_private.<mod>.0.<imported>.match_*.splitter`)
  -- synthesized on demand as a safe definition in `map₂` for an imported
  -- matcher.
  let isLazySplitter (n : Name) (ci : ConstantInfo) : Bool :=
    match Lean.privateToUserName? n with
    | some (.str pre "splitter") =>
      let preLeaf := match pre with | .str _ s => s | _ => ""
      preLeaf.startsWith "match_" &&
      (env.getModuleIdxFor? pre).isSome &&
      (match env.find? pre with | some (.defnInfo _) => true | _ => false) &&
      (match ci with | .defnInfo _ => true | _ => false)
    | _ => false
  -- Private declaration belonging to `ns`.
  let isPrivateIn (ns : Name) (n : Name) : Bool :=
    match Lean.privateToUserName? n with
    | some u => ns.isPrefixOf u
    | none => false
  -- Transitive closure of the used-constant relation.
  let closure (start : Array Name) : NameSet := Id.run do
    let mut seen : NameSet := {}
    let mut stack := start
    while !stack.isEmpty do
      let n := stack.back!
      stack := stack.pop
      if seen.contains n then continue
      seen := seen.insert n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet do
          if !seen.contains d then stack := stack.push d
    return seen
  -- 1. Every declaration added by this file (`env.constants.map₂`), with
  -- zero exemptions for `_private` or internal compiler helpers.
  let mut roots : Array Name := #[]
  let mut auxDecls : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if testNs.isPrefixOf n || isPrivateIn testNs n then
      if rejected ci then
        throwError "audit: test declaration {n} is not a safe definition"
      if isTrivialThm ci then
        throwError "audit: test theorem {n} is trivial"
      roots := roots.push n
    else if !(userName n).isInternal then
      -- Lean lazily synthesizes equational lemmas (`*.eq_*` / `*.eq_def`) and
      -- matcher splitters (`_private...<imported>.match_*.splitter`) on demand
      -- in `map₂`; reject any other public or `private` decl outside `testNs`.
      unless isLazyEq n ci || isLazySplitter n ci do
        throwError "audit: stray declaration {n} outside {testNs}"
      if rejected ci then
        throwError "audit: lazy auxiliary lemma {n} is not safe"
      if isTrivialThm ci then
        throwError "audit: trivial lazy auxiliary theorem {n}"
      auxDecls := auxDecls.push n
    else
      if rejected ci then
        throwError "audit: non-safe internal declaration {n}"
      if isTrivialThm ci then
        throwError "audit: trivial internal theorem {n}"
      auxDecls := auxDecls.push n
  unless roots.size ≥ 2000 do
    throwError "audit: only {roots.size} test declarations"
  let testAxioms ← scanAxioms (roots ++ auxDecls)
  unless constructive testAxioms do
    throwError "audit: test declarations use the axioms {testAxioms}"
  let reached := closure roots
  -- 2. Both modules under test.
  let mut report : Array MessageData := #[]
  for (modName, minDecls, minThms) in modules do
    let some idx := env.getModuleIdx? modName
      | throwError "audit: module {modName} is not imported"
    let mut decls : Array Name := #[]
    let mut pubThms : Array Name := #[]
    for (n, ci) in env.constants.map₁.toList do
      if env.getModuleIdxFor? n == some idx then
        if rejected ci then
          throwError "audit: {n} is not a safe definition"
        decls := decls.push n
        if let .thmInfo _ := ci then
          if isTrivialThm ci then
            throwError "audit: {modName} theorem {n} is trivial"
          if !n.isInternal then pubThms := pubThms.push n
    unless decls.size ≥ minDecls do
      throwError "audit: {modName} has only {decls.size} declarations"
    unless pubThms.size ≥ minThms do
      throwError "audit: {modName} has only {pubThms.size} public theorems"
    let axioms ← scanAxioms decls
    unless constructive axioms do
      throwError "audit: {modName} uses the axioms {axioms}"
    let unreached := pubThms.filter fun n => !reached.contains n
    unless unreached.isEmpty do
      throwError "audit: unreached public theorems of {modName}: {unreached}"
    report := report.push
      m!"{modName}: {decls.size} declarations, {pubThms.size} public \
        theorems, 0 unreached, axioms {axioms}"
  -- 3. Self-tests: the scanners fail closed.
  unless !constructive (← scanAxioms #[``Classical.em]) do
    throwError "audit self-test: a classical axiom was not detected"
  unless !constructive (← scanAxioms #[``sorryAx]) do
    throwError "audit self-test: `sorryAx` was not detected"
  unless !constructive (← scanAxioms #[``Lean.ofReduceBool]) do
    throwError "audit self-test: `Lean.ofReduceBool` was not detected"
  match env.find? ``unsafeCast with
  | some ci =>
    unless rejected ci do
      throwError "audit self-test: a non-safe definition was not detected"
  | none => throwError "audit self-test: `unsafeCast` is missing"
  match env.find? ``trivial with
  | some ci =>
    unless isTrivialThm ci do
      throwError "audit self-test: trivial `: True` theorem was not detected"
  | none => throwError "audit self-test: `trivial` is missing"
  match env.find? ``Iff.rfl, env.find? ``Nat.add_comm with
  | some refl, some comm =>
    unless isTrivialThm refl && !isTrivialThm comm do
      throwError "audit self-test: reflexive theorem classifier failed"
  | _, _ => throwError "audit self-test: `Iff.rfl` is missing"
  -- Reflexive, heterogeneous, `let`/binder-wrapped, conjunctive, disjunctive,
  -- `¬ False`, `False → P`, and `P → P` trivialities are flagged, and genuine
  -- statements are not.
  let natTy := mkConst ``Nat
  let eqN (a b : Nat) : Expr :=
    mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit a) (mkNatLit b)
  let heqN (a b : Nat) : Expr :=
    mkApp4 (mkConst ``HEq [1]) natTy (mkNatLit a) natTy (mkNatLit b)
  let trivialShapes : List Expr :=
    [eqN 1 1, heqN 1 1,
      mkApp2 (mkConst ``Iff) (mkConst ``False) (mkConst ``False),
      mkApp2 (mkConst ``And) (mkConst ``True) (eqN 2 2),
      mkApp2 (mkConst ``Or) (mkConst ``True) (eqN 1 2),
      mkApp2 (mkConst ``Or) (eqN 1 2) (eqN 3 3),
      mkApp (mkConst ``Not) (mkConst ``False),
      .forallE `_ (mkConst ``False) (eqN 1 2) .default,
      .forallE `_ (eqN 1 2) (eqN 1 2) .default,
      .letE `x natTy (mkNatLit 1)
        (mkApp3 (mkConst ``Eq [1]) natTy (.bvar 0) (.bvar 0)) false,
      .forallE `n natTy (mkApp3 (mkConst ``Eq [1]) natTy (.bvar 0) (.bvar 0))
        .default]
  for e in trivialShapes do
    unless trivialProp e do
      throwError "audit self-test: trivial proposition {e} was not detected"
  for e in [eqN 1 2, heqN 1 2,
      mkApp2 (mkConst ``And) (mkConst ``True) (eqN 1 2),
      mkApp2 (mkConst ``Or) (eqN 1 2) (eqN 2 3),
      mkApp (mkConst ``Not) (mkConst ``True),
      .forallE `_ (mkConst ``True) (eqN 1 2) .default,
      .letE `x natTy (mkNatLit 1)
        (mkApp3 (mkConst ``Eq [1]) natTy (.bvar 0) (mkNatLit 2)) false,
      mkConst ``False] do
    if trivialProp e then
      throwError "audit self-test: genuine proposition {e} was flagged"
  -- Padding fails closed: 300 nested `True ∧ …` conjuncts (past the former
  -- 256-step budget) are still flagged, and stay genuine if any conjunct is.
  let pad (last : Expr) : Expr :=
    (List.replicate 300 ()).foldl
      (fun acc _ => mkApp2 (mkConst ``And) (mkConst ``True) acc) last
  unless trivialProp (pad (mkConst ``True)) && !trivialProp (pad (eqN 1 2)) do
    throwError "audit self-test: padded trivial proposition classifier failed"
  -- User-authored `private` reflexive theorems are flagged, while compiler
  -- `_proof_*` field obligations are flagged only when their type is `True`.
  let privReflCi : ConstantInfo := .thmInfo
    { name := Lean.mkPrivateName env (testNs ++ `bogusRefl)
      levelParams := []
      type := eqN 1 1
      value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 1) }
  let compProofReflCi : ConstantInfo := .thmInfo
    { name := Lean.mkPrivateName env (testNs ++ `foo ++ `_proof_1)
      levelParams := []
      type := eqN 1 1
      value := mkApp2 (mkConst ``Eq.refl [1]) natTy (mkNatLit 1) }
  let compProofTrueCi : ConstantInfo := .thmInfo
    { name := Lean.mkPrivateName env (testNs ++ `foo ++ `_proof_1)
      levelParams := []
      type := mkConst ``True
      value := mkConst ``True.intro }
  unless isTrivialThm privReflCi && !isTrivialThm compProofReflCi &&
      isTrivialThm compProofTrueCi do
    throwError "audit self-test: private/internal triviality classifier failed"
  -- A theorem or definition shaped like a lazy equational lemma or splitter
  -- whose parent is not an imported definition (or imported matcher when
  -- `private`) is stray, not a lazy auxiliary.
  match env.find? ``Nat.add_comm, env.find? ``Nat.add with
  | some thm, some defn =>
    let matchPre :=
      `Anneal.TreeBorrowsPruningAndFrameWp.BorrowSubtree.root.match_1
    unless isLazyEq (``Nat.add ++ `eq_1) thm &&
        isLazyEq (Lean.mkPrivateName env (matchPre ++ `eq_1)) thm do
      throwError "audit self-test: a lazy equational lemma was rejected"
    if isLazyEq (`Other ++ `eq_1) thm ||
        isLazyEq (``Nat.add_comm ++ `eq_1) thm ||
        isLazyEq (Lean.mkPrivateName env (``Nat.add ++ `eq_1)) thm ||
        isLazySplitter (Lean.mkPrivateName env (`Other ++ `splitter)) defn ||
        isLazySplitter (Lean.mkPrivateName env (``Nat.add ++ `splitter)) defn
        then
      throwError "audit self-test: a stray lazy-shaped decl was accepted"
    let okSplit := Lean.mkPrivateName env (matchPre ++ `splitter)
    unless isLazySplitter okSplit defn do
      throwError "audit self-test: a lazy matcher splitter was rejected"
  | _, _ => throwError "audit self-test: `Nat.add_comm` is missing"
  match env.find? ``Nat.add with
  | some ci =>
    unless !testNs.isPrefixOf ``Nat.add && !isLazyEq ``Nat.add ci &&
        !isLazySplitter ``Nat.add ci do
      throwError "audit self-test: stray declaration was not detected"
    let privOk := Lean.mkPrivateName env (testNs ++ `dummy)
    let privBad := Lean.mkPrivateName env (`Other ++ `dummy)
    unless isPrivateIn testNs privOk && !isPrivateIn testNs privBad &&
        !(userName privBad).isInternal && !isLazyEq privBad ci &&
        !isLazySplitter privBad ci do
      throwError "audit self-test: stray private declaration was not detected"
  | none => throwError "audit self-test: `Nat.add` is missing"
  unless (closure #[]).isEmpty do
    throwError "audit self-test: the empty closure is not empty"
  let bundleOnly := closure <| roots.filter fun n =>
    !(testNs ++ `TbPruning).isPrefixOf n && !(testNs ++ `FrameWp).isPrefixOf n
  unless !bundleOnly.contains
      ``Anneal.TreeBorrowsPruningAndFrameWp.wpFramePrep_seq do
    throwError "audit self-test: reachability does not depend on the roots"
  logInfo m!"audit: {roots.size} test declarations, axioms {testAxioms}; \
    {report}"
