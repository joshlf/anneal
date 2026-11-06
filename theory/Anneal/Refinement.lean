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
# Core Refinement Lattice and Non-Vacuity Meta-Theorems (`Anneal.Refinement`)

Proves foundational zero-axiom meta-theorems over `Trusted.Refinement`:
1. `SpecOn`, `wellFormedOn`, and `wellFormed` refinement lattice equivalences
   (the well-formedness combinators live here because no trusted statement
   uses them),
2. `BehaviorCodec` identity, composition, monotonicity, and compilation
   judgments (`Compiles`, `ProductiveCompiles`),
3. Non-vacuity (`NonVacuousOn`) introduction lemmas and adequacy canaries
   showing that `Language.Verified`, `Obligation.wellFormedAndSpecsOn`,
   `VerificationResult`, `Obligation.assumed`, and `ProductiveCompiles` reject
   the degenerate cases they exist to reject, including programs with an empty
   domain.
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
## 1. `SpecOn`, `wellFormedOn`, and `wellFormed` Lattice Lemmas
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

/-!
## 2. `BehaviorCodec` Algebra and Compilation Judgments
-/

/-- Representation codec between two languages `L₁` and `L₂` (moved out of
`Trusted` because `CrateTheorem` uses `Obligation.assumed` for the `rustc`
lowering waiver). `decodeQuery` is a left inverse of `encodeQuery` (so distinct
source queries never collapse onto one target query) and `decodeOut` is a left
inverse of `encodeOut`. -/
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

/-- Miracle-free compilation that also preserves the program's domain. -/
def ProductiveCompiles (L_src L_tgt : Language)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  (∀ q₁, L_src.dom s q₁ ↔ L_tgt.dom t (c.encodeQuery q₁)) ∧
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
## 3. Non-Vacuity and Adequacy Canaries
-/

/-- Witnessing `dom q₀` and `pre q₀` establishes `NonVacuousOn dom pre`. -/
theorem nonVacuousOn_of_witness {Query : Type} {dom pre : Query → Prop}
    (q₀ : Query) (hdom : dom q₀) (hpre : pre q₀) :
    NonVacuousOn dom pre :=
  ⟨q₀, hdom, hpre⟩

/-- Canary: a program with no initial state cannot be verified against any
specification. This is what makes model limits at function entry (which
empty the domain) fail closed. -/
theorem verified_rejects_empty_dom {L : Language}
    (p : L.Prog) (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (hempty : ∀ q, ¬ L.dom p q) :
    ¬ L.Verified pre post p
  | ⟨⟨q, hdom, _⟩, _, _⟩ => hempty q hdom

/-- Canary: `Obligation.wellFormedAndSpecsOn` rejects a contradictory
specification (`L.SpecOn (fun _ => False) post`) on every program, with no
assumption about the program's domain. -/
theorem wellFormedAndSpecsOn_rejects_contradictory_spec
    {Id : Type} {L : Language} (id : Id) (p : L.Prog)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    ¬ (Obligation.wellFormedAndSpecsOn id L pre
        [L.SpecOn (fun _ => False) post] p).prop
  | ⟨_, ⟨⟨_, _, _, hfalse⟩, _⟩, _⟩ => hfalse

/-- A one-program, one-query language whose behavior is defined but has no
outcome at all (a miracle). Its domain is inhabited. -/
def MiracleCanaryLang : Language where
  Prog  := Unit
  Query := Unit
  Out   := Unit
  sem   := fun _ _ => ⟨True, fun _ _ => False⟩
  dom   := fun _ _ => True

/-- Canary: a miraculous semantics (defined, but with no outcome) is rejected
by `Obligation.wellFormedAndSpecsOn`, because `Language.Verified` requires
`ProductiveOn`. -/
theorem obligation_wellFormedAndSpecsOn_rejects_miracle :
    ¬ (Obligation.wellFormedAndSpecsOn "miracle" MiracleCanaryLang
        (fun _ => True) [] ()).prop := by
  intro ⟨⟨_, hprod, _⟩, _⟩
  cases hprod () trivial with
  | intro _ hout =>
    cases hout with
    | intro _ hval => exact hval

/-- Canary: a contradictory precondition (`fun _ => False`) is rejected by
`Obligation.wellFormedAndSpecsOn`. -/
theorem obligation_wellFormedAndSpecsOn_rejects_vacuous_pre :
    ¬ (Obligation.wellFormedAndSpecsOn "vacuous" MiracleCanaryLang
        (fun _ => False) [] ()).prop := by
  intro ⟨⟨⟨_, _, hfalse⟩, _, _⟩, _⟩
  exact hfalse

/-- Canary: duplicate obligation identifiers are rejected unconditionally by
`VerificationResult`, so one waiver cannot cover two obligations. -/
theorem verificationResult_rejects_duplicate_obligation_ids :
    let ob₁ := Obligation.wellFormedAndSpecsOn "dup" MiracleCanaryLang
      (fun _ => True) [] ()
    let ob₂ := Obligation.wellFormedAndSpecsOn "dup" MiracleCanaryLang
      (fun _ => False) [] ()
    ¬ VerificationResult ⟨fun _ => True⟩ ["dup"] [ob₁, ob₂] := by
  intro ob₁ ob₂ ⟨_, hnodup, _⟩
  exact hnodup.1.1 rfl

/-- Canary: duplicate waived identifiers are rejected unconditionally by
`VerificationResult`. -/
theorem verificationResult_rejects_duplicate_waived_ids :
    let ob₁ := Obligation.wellFormedAndSpecsOn "id1" MiracleCanaryLang
      (fun _ => True) [] ()
    ¬ VerificationResult ⟨fun _ => True⟩ ["id1", "id1"] [ob₁] := by
  intro ob₁ ⟨_, _, hnodupW, _⟩
  exact hnodupW.1.1 rfl

/-- Source language for the query-slack canary: one query, whose only outcome
is `true`. -/
def SrcUnitCanaryLang : Language where
  Prog  := Unit
  Query := Unit
  Out   := Bool
  sem   := fun _ _ => ⟨True, fun _ o => o = true⟩
  dom   := fun _ _ => True

/-- Target language for the query-slack canary: query `true` behaves like the
source, and query `false` is a miracle (defined, no outcome). -/
def TgtBoolSlackMiracleCanaryLang : Language where
  Prog  := Unit
  Query := Bool
  Out   := Bool
  sem   := fun _ q =>
    if q then ⟨True, fun _ o => o = true⟩ else ⟨True, fun _ _ => False⟩
  dom   := fun _ _ => True

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

/-- An assumed obligation (`Obligation.assumed id`) holds in
`VerificationResult` whenever `id ∈ waived`, and cannot be discharged without
being listed in `waived`. -/
theorem obligation_assumed_waived_iff {Id : Type} (id : Id) (waived : List Id) :
    ((Obligation.assumed id).id ∈ waived ∨ (Obligation.assumed id).prop) ↔
      id ∈ waived := by
  constructor
  · intro h
    cases h with
    | inl hIn => exact hIn
    | inr hFalse => exact False.elim hFalse
  · intro hIn
    exact Or.inl hIn

end Anneal
