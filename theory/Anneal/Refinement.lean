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
import Trusted.Refinement

/-!
# Core Refinement Lattice and Multi-Guarantee Meta-Theorems (`Anneal.Refinement`)

Proves foundational zero-axiom meta-theorems over `Trusted.Refinement`:
1. `SpecOn`, `wellFormedOn`, `wellFormed`, and demonic lattice-meet
   (`le_specOn_meet_iff`, `verified_meet_iff`, `verified_single_pass`,
   `verified_split`) equivalences,
2. `BehaviorCodec` identity, composition, monotonicity, and compilation
   judgments (`Compiles`, `ProductiveCompiles`),
3. Adequacy canaries showing that `Language.Verified`, `VerificationResult`,
   and `ProductiveCompiles` reject ill-formed programs (`¬ L.wf prog`),
   miracles, duplicate obligation/waiver IDs, and unwaived false obligations.
-/

namespace Anneal

open Trusted

/-- Order-preserving mapping between preorders (moved out of `Trusted`
because no trusted statement depends on it). -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Conditional well-formedness (UB-freedom) on `pre`. -/
abbrev wellFormedOn (L : Language)
    (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness (UB-freedom) on all queries. -/
abbrev wellFormed (L : Language) : L.Behavior :=
  wellFormedOn L (fun _ => True)

/-!
## 1. `SpecOn`, `wellFormedOn`, `wellFormed`, and Lattice-Meet Lemmas
-/

/-- Refining `L.SpecOn pre post` is equivalent to being defined on `pre` and
satisfying `post q` on every outcome in `(b q).val`. -/
theorem le_specOn_iff {L : Language} (b : L.Behavior)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    b ≤ L.SpecOn pre post ↔
      ∀ q, pre q → ∃ h : (b q).defined, ∀ o, (b q).val h o → post q o :=
  ⟨fun hle q hpre => hle q hpre, fun h q hpre => h q hpre⟩

/-- Refining `wellFormedOn L pre` is equivalent to `(b q).defined` holding at
every query `q` satisfying `pre q`. -/
theorem le_wellFormedOn_iff {L : Language}
    (b : L.Behavior) (pre : L.Query → Prop) :
    b ≤ wellFormedOn L pre ↔ ∀ q, pre q → (b q).defined :=
  ⟨fun h q hpre => (h q hpre).1,
   fun h q hpre => ⟨h q hpre, fun _ _ => True.intro⟩⟩

/-- Refining `wellFormed L` is equivalent to `(b q).defined` holding at every
query `q`. -/
theorem le_wellFormed_iff {L : Language}
    (b : L.Behavior) :
    b ≤ wellFormed L ↔ ∀ q, (b q).defined :=
  ⟨fun h q => (h q True.intro).1,
   fun h q _ => ⟨h q, fun _ _ => True.intro⟩⟩

/-- Every conditional specification `L.SpecOn pre post` refines conditional
well-formedness `wellFormedOn L pre` on the same precondition `pre`. -/
theorem specOn_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ wellFormedOn L pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Every unconditional specification `L.Spec post` refines `wellFormed L`. -/
theorem spec_le_wellFormed {L : Language}
    (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ wellFormed L :=
  specOn_le_wellFormedOn (fun _ => True) post

/-- Contravariance of `SpecOn` in its precondition `pre`. -/
theorem specOn_mono_pre {L : Language}
    {pre₁ pre₂ : L.Query → Prop} (post : L.Query → L.Out → Prop)
    (himp : ∀ q, pre₂ q → pre₁ q) :
    L.SpecOn pre₁ post ≤ L.SpecOn pre₂ post :=
  fun q hpre₂ => ⟨himp q hpre₂, fun _ h => h⟩

/-- Unconditional `wellFormed L` refines `wellFormedOn L pre` for any `pre`. -/
theorem wellFormed_le_wellFormedOn {L : Language}
    (pre : L.Query → Prop) :
    wellFormed L ≤ wellFormedOn L pre :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-- Demonic refinement lattice meet for multi-guarantee specifications:
refining `SpecOn safetyPre safetyPost` and refining `SpecOn (safetyPre ∧ req)
contractPost` is equivalent to refining a single `SpecOn safetyPre` whose
postcondition is `safetyPost q o ∧ (req q → contractPost q o)`. -/
theorem le_specOn_meet_iff {L : Language} (b : L.Behavior)
    (safetyPre req : L.Query → Prop)
    (safetyPost contractPost : L.Query → L.Out → Prop) :
    (b ≤ L.SpecOn safetyPre
        (fun q o => safetyPost q o ∧ (req q → contractPost q o))) ↔
      (b ≤ L.SpecOn safetyPre safetyPost ∧
       b ≤ L.SpecOn (fun q => safetyPre q ∧ req q) contractPost) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro q hs
      cases h q hs with
      | intro hdef hpost =>
        exact ⟨hdef, fun o ho => (hpost o ho).1⟩
    · intro q ⟨hs, hreq⟩
      cases h q hs with
      | intro hdef hpost =>
        exact ⟨hdef, fun o ho => (hpost o ho).2 hreq⟩
  · intro ⟨hSafe, hContract⟩ q hs
    cases hSafe q hs with
    | intro hdef hpost₁ =>
      refine ⟨hdef, fun o ho => ⟨hpost₁ o ho, fun hreq => ?_⟩⟩
      cases hContract q ⟨hs, hreq⟩ with
      | intro _ hpost₂ => exact hpost₂ o ho

/-- Multi-guarantee `Language.Verified` lattice-meet equivalence: verifying
`prog` against `(safetyPre, fun q o => safetyPost q o ∧ (req q → contractPost q o))`
is equivalent to verifying `(safetyPre, safetyPost)` and refining
`SpecOn (safetyPre ∧ req) contractPost`. -/
theorem verified_meet_iff {L : Language}
    (safetyPre req : L.Query → Prop)
    (safetyPost contractPost : L.Query → L.Out → Prop)
    (prog : L.Prog) :
    L.Verified safetyPre
        (fun q o => safetyPost q o ∧ (req q → contractPost q o)) prog ↔
      (L.Verified safetyPre safetyPost prog ∧
       L.sem prog ≤ L.SpecOn (fun q => safetyPre q ∧ req q) contractPost) := by
  constructor
  · intro ⟨hwf, hprod, hsem⟩
    have ⟨hSafe, hContract⟩ :=
      (le_specOn_meet_iff (L.sem prog) safetyPre req safetyPost
        contractPost).mp hsem
    exact ⟨⟨hwf, hprod, hSafe⟩, hContract⟩
  · intro ⟨⟨hwf, hprod, hSafe⟩, hContract⟩
    refine ⟨hwf, hprod, ?_⟩
    exact
      (le_specOn_meet_iff (L.sem prog) safetyPre req safetyPost
        contractPost).mpr ⟨hSafe, hContract⟩

/-- Single-pass verification helper (`proveFnSinglePass` foundation): when
`safetyPre` already entails `req` (for example, on an `unsafe fn` where
`safetyPre` includes `req`, or on a function with no `requires` clause where
`req := True`), proving `safetyPost q o ∧ contractPost q o` under `safetyPre`
establishes the multi-guarantee `Language.Verified` obligation in one pass. -/
theorem verified_single_pass {L : Language}
    {safetyPre req : L.Query → Prop}
    {safetyPost contractPost : L.Query → L.Out → Prop}
    {prog : L.Prog}
    (hver : L.Verified safetyPre
      (fun q o => safetyPost q o ∧ contractPost q o) prog) :
    L.Verified safetyPre
      (fun q o => safetyPost q o ∧ (req q → contractPost q o)) prog := by
  cases hver with
  | intro hwf hrest =>
    cases hrest with
    | intro hprod hsem =>
      refine ⟨hwf, hprod, fun q hs => ?_⟩
      cases hsem q hs with
      | intro hdef hpost =>
        exact ⟨hdef, fun o ho => ⟨(hpost o ho).1, fun _ => (hpost o ho).2⟩⟩

/-- Split verification helper (`proveSafeFnSplit` foundation): on a safe
function with a non-trivial `requires` clause `req`, proving baseline safety
`L.Verified safetyPre safetyPost prog` together with conditional functional
correctness `L.sem prog ≤ L.SpecOn (fun q => safetyPre q ∧ req q) contractPost`
establishes the multi-guarantee `Language.Verified` obligation without assuming
`req` for baseline safety. -/
theorem verified_split {L : Language}
    {safetyPre req : L.Query → Prop}
    {safetyPost contractPost : L.Query → L.Out → Prop}
    {prog : L.Prog}
    (hSafe : L.Verified safetyPre safetyPost prog)
    (hContract :
      L.sem prog ≤ L.SpecOn (fun q => safetyPre q ∧ req q) contractPost) :
    L.Verified safetyPre
      (fun q o => safetyPost q o ∧ (req q → contractPost q o)) prog :=
  (verified_meet_iff safetyPre req safetyPost contractPost prog).mpr
    ⟨hSafe, hContract⟩

/-!
## 2. `BehaviorCodec` Algebra and Compilation Judgments
-/

/-- Representation codec between two languages `L₁` and `L₂`. `decodeQuery` is
a left inverse of `encodeQuery` (so distinct source queries never collapse onto
one target query) and `decodeOut` is a left inverse of `encodeOut`. -/
structure BehaviorCodec (L₁ L₂ : Language) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁

/-- Transport a source behavior to the target language along `c`. A target
outcome is permitted only if it decodes to a permitted source outcome. -/
def BehaviorCodec.toMorphism {L₁ L₂ : Language}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
  fun q₂ => {
    defined := (b (c.decodeQuery q₂)).defined
    val     := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b (c.decodeQuery q₂)).val h o₁
  }

/-- Compilation correctness: the target program refines the transported source
behavior. -/
abbrev Compiles (L_src L_tgt : Language)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Miracle-free compilation that also preserves static program
well-formedness. -/
def ProductiveCompiles (L_src L_tgt : Language)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  (L_src.wf s ↔ L_tgt.wf t) ∧
  ∀ q₂,
    (∃ h₁ : (L_src.sem s (c.decodeQuery q₂)).defined,
      ∃ o₁, (L_src.sem s (c.decodeQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t q₂).defined,
      ∃ o₂, (L_tgt.sem t q₂).val h₂ o₂)

/-- Identity `BehaviorCodec` on any language `L`. -/
def BehaviorCodec.id (L : Language) :
    BehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl

/-- Sequential composition of `BehaviorCodec L₁ L₂` and `BehaviorCodec L₂ L₃`. -/
def BehaviorCodec.comp {L₁ L₂ L₃ : Language}
    (c₁ : BehaviorCodec L₁ L₂) (c₂ : BehaviorCodec L₂ L₃) :
    BehaviorCodec L₁ L₃ where
  encodeQuery q₁ := c₂.encodeQuery (c₁.encodeQuery q₁)
  decodeQuery q₃ := c₁.decodeQuery (c₂.decodeQuery q₃)
  encodeOut o₁   := c₂.encodeOut (c₁.encodeOut o₁)
  decodeOut o₃   :=
    match c₂.decodeOut o₃ with
    | some o₂ => c₁.decodeOut o₂
    | none    => none
  decodeQuery_encodeQuery q₁ := by
    rw [c₂.decodeQuery_encodeQuery, c₁.decodeQuery_encodeQuery]
  decodeOut_encodeOut o₁ := by
    rw [c₂.decodeOut_encodeOut]
    exact c₁.decodeOut_encodeOut o₁

/-- Every `BehaviorCodec.toMorphism` is automatically `Monotone`. -/
theorem BehaviorCodec.toMorphism_monotone
    {L₁ L₂ : Language} (c : BehaviorCodec L₁ L₂) :
    Monotone c.toMorphism := by
  intro b₁ b₂ hle q₂ hdef₂
  cases hle (c.decodeQuery q₂) hdef₂ with
  | intro hdef₁ hval =>
    refine ⟨hdef₁, ?_⟩
    intro o₂ ⟨o₁, hdec, ho₁⟩
    exact ⟨o₁, hdec, hval o₁ ho₁⟩

/-!
## 3. Adequacy Canaries
-/

/-- Canary: a program that fails static well-formedness (`¬ L.wf p`) cannot be
verified against any specification, even under a false precondition
(`pre := fun _ => False`). -/
theorem verified_rejects_ill_formed {L : Language}
    (p : L.Prog) (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (hbad : ¬ L.wf p) :
    ¬ L.Verified pre post p
  | ⟨hwf, _, _⟩ => hbad hwf

/-- A one-program, one-query language whose behavior is defined but has no
outcome at all (a miracle). -/
def MiracleCanaryLang : Language where
  Prog  := Unit
  Query := Unit
  Out   := Unit
  wf    := fun _ => True
  sem   := fun _ _ => ⟨True, fun _ _ => False⟩

/-- Canary: a miraculous semantics (defined, but with no outcome) is rejected
by `Language.Verified`, because `Language.Verified` requires `ProductiveOn`. -/
theorem verified_rejects_miracle :
    ¬ MiracleCanaryLang.Verified (fun _ => True) (fun _ _ => True) () := by
  intro ⟨_, hprod, _⟩
  cases hprod () trivial with
  | intro _ hout =>
    cases hout with
    | intro _ hval => exact hval

/-- Canary: duplicate obligation identifiers are rejected unconditionally by
`VerificationResult`, so one waiver cannot cover two obligations. -/
theorem verificationResult_rejects_duplicate_obligation_ids :
    let ob₁ : Obligation String := ⟨"dup", True⟩
    let ob₂ : Obligation String := ⟨"dup", False⟩
    ¬ VerificationResult ["dup"] [ob₁, ob₂] := by
  intro ob₁ ob₂ ⟨_, hnodup, _⟩
  exact hnodup.1.1 rfl

/-- Canary: duplicate waived identifiers are rejected unconditionally by
`VerificationResult`. -/
theorem verificationResult_rejects_duplicate_waived_ids :
    let ob₁ : Obligation String := ⟨"id1", True⟩
    ¬ VerificationResult ["id1", "id1"] [ob₁] := by
  intro ob₁ ⟨_, _, hnodupW, _⟩
  exact hnodupW.1.1 rfl

/-- Canary: an unwaived false obligation is rejected by `VerificationResult`. -/
theorem verificationResult_rejects_unwaived_false :
    let ob₁ : Obligation String := ⟨"id1", False⟩
    ¬ VerificationResult [] [ob₁] := by
  intro ob₁ ⟨_, _, _, ⟨h, _⟩⟩
  cases h with
  | inl hFalse => exact hFalse
  | inr hIn => nomatch hIn

/-- Source language for the query-slack canary: one query, whose only outcome
is `true`. -/
def SrcUnitCanaryLang : Language where
  Prog  := Unit
  Query := Unit
  Out   := Bool
  wf    := fun _ => True
  sem   := fun _ _ => ⟨True, fun _ o => o = true⟩

/-- Target language for the query-slack canary: query `true` behaves like the
source, and query `false` is a miracle (defined, no outcome). -/
def TgtBoolSlackMiracleCanaryLang : Language where
  Prog  := Unit
  Query := Bool
  Out   := Bool
  wf    := fun _ => True
  sem   := fun _ q =>
    if q then ⟨True, fun _ o => o = true⟩ else ⟨True, fun _ _ => False⟩

/-- Codec that encodes the single source query as target query `true`, leaving
target query `false` as slack. -/
def unitBoolSlackCanaryCodec :
    BehaviorCodec SrcUnitCanaryLang TgtBoolSlackMiracleCanaryLang where
  encodeQuery _ := true
  decodeQuery _ := ()
  encodeOut   o := o
  decodeOut   o := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl

/-- Canary: a target that is miraculous on a query outside the codec's image
(query slack) is rejected by `ProductiveCompiles`, which requires every target
query to be productive when its decoded source query is. -/
theorem productiveCompiles_rejects_query_slack_miracle :
    ¬ ProductiveCompiles SrcUnitCanaryLang TgtBoolSlackMiracleCanaryLang
        unitBoolSlackCanaryCodec () () := by
  intro ⟨_, _, hprod⟩
  cases hprod false ⟨trivial, true, rfl⟩ with
  | intro _ hout =>
    cases hout with
    | intro _ hval => exact hval

end Anneal
