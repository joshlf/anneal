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
2. `BehaviorCodec` identity, composition, monotonicity, and observable spine
   preservation (`obs_encodeOut_of_decodeOut`),
3. Non-vacuity (`NonVacuousOn`) introduction lemmas and adequacy canaries
   showing that `Language.Verified`, `Obligation.wellFormedAndSpecsOn`,
   `VerificationResult`, and `ProductiveCompiles` reject the degenerate cases
   they exist to reject, including programs with an empty domain.
-/

namespace Anneal

open Trusted

/-- Order-preserving mapping between preorders (moved out of `Trusted`
because no trusted statement depends on it). -/
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Conditional well-formedness (UB-freedom) on `pre`. -/
abbrev wellFormedOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness (UB-freedom) on all queries. -/
abbrev wellFormed {SemObs : Type} (L : Language SemObs) : L.Behavior :=
  wellFormedOn L (fun _ => True)

/-!
## 1. `SpecOn`, `wellFormedOn`, and `wellFormed` Lattice Lemmas
-/

/-- Refining `L.SpecOn pre post` is equivalent to being defined on `pre` and
satisfying `post q` on every outcome in `(b q).val`. -/
theorem le_specOn_iff {SemObs : Type} {L : Language SemObs} (b : L.Behavior)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    b ≤ L.SpecOn pre post ↔
      ∀ q, pre q → ∃ h : (b q).defined, ∀ o, (b q).val h o → post q o :=
  ⟨fun hle q hpre => hle q hpre, fun h q hpre => h q hpre⟩

/-- Refining `wellFormedOn L pre` is equivalent to `(b q).defined` holding at
every query `q` satisfying `pre q`. -/
theorem le_wellFormedOn_iff {SemObs : Type} {L : Language SemObs}
    (b : L.Behavior) (pre : L.Query → Prop) :
    b ≤ wellFormedOn L pre ↔ ∀ q, pre q → (b q).defined :=
  ⟨fun h q hpre => (h q hpre).1,
   fun h q hpre => ⟨h q hpre, fun _ _ => True.intro⟩⟩

/-- Refining `wellFormed L` is equivalent to `(b q).defined` holding at every
query `q`. -/
theorem le_wellFormed_iff {SemObs : Type} {L : Language SemObs}
    (b : L.Behavior) :
    b ≤ wellFormed L ↔ ∀ q, (b q).defined :=
  ⟨fun h q => (h q True.intro).1,
   fun h q _ => ⟨h q, fun _ _ => True.intro⟩⟩

/-- Every conditional specification `L.SpecOn pre post` refines conditional
well-formedness `wellFormedOn L pre` on the same precondition `pre`. -/
theorem specOn_le_wellFormedOn {SemObs : Type} {L : Language SemObs}
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    L.SpecOn pre post ≤ wellFormedOn L pre :=
  fun _ hpre => ⟨hpre, fun _ _ => True.intro⟩

/-- Every unconditional specification `L.Spec post` refines `wellFormed L`. -/
theorem spec_le_wellFormed {SemObs : Type} {L : Language SemObs}
    (post : L.Query → L.Out → Prop) :
    L.Spec post ≤ wellFormed L :=
  specOn_le_wellFormedOn (fun _ => True) post

/-- Contravariance of `SpecOn` in its precondition `pre`. -/
theorem specOn_mono_pre {SemObs : Type} {L : Language SemObs}
    {pre₁ pre₂ : L.Query → Prop} (post : L.Query → L.Out → Prop)
    (himp : ∀ q, pre₂ q → pre₁ q) :
    L.SpecOn pre₁ post ≤ L.SpecOn pre₂ post :=
  fun q hpre₂ => ⟨himp q hpre₂, fun _ h => h⟩

/-- Unconditional `wellFormed L` refines `wellFormedOn L pre` for any `pre`. -/
theorem wellFormed_le_wellFormedOn {SemObs : Type} {L : Language SemObs}
    (pre : L.Query → Prop) :
    wellFormed L ≤ wellFormedOn L pre :=
  fun _ _ => ⟨True.intro, fun _ _ => True.intro⟩

/-!
## 2. `BehaviorCodec` Algebra and Observable Spine Theorems
-/

/-- Identity `BehaviorCodec` on any language `L`. -/
def BehaviorCodec.id {SemObs : Type} (L : Language SemObs) :
    BehaviorCodec L L where
  encodeQuery q := q
  decodeQuery q := q
  encodeOut o   := o
  decodeOut o   := some o
  decodeQuery_encodeQuery _ := rfl
  decodeOut_encodeOut _     := rfl
  obs_decodeOut _ _ h       := by cases h; rfl

/-- Sequential composition of `BehaviorCodec L₁ L₂` and `BehaviorCodec L₂ L₃`. -/
def BehaviorCodec.comp {SemObs : Type} {L₁ L₂ L₃ : Language SemObs}
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
  obs_decodeOut o₃ o₁ h := by
    cases h₂ : c₂.decodeOut o₃ with
    | none =>
      rw [h₂] at h
      cases h
    | some o₂ =>
      rw [h₂] at h
      exact Eq.trans (c₂.obs_decodeOut o₃ o₂ h₂) (c₁.obs_decodeOut o₂ o₁ h)

/-- Every `BehaviorCodec.toMorphism` is automatically `Monotone`. -/
theorem BehaviorCodec.toMorphism_monotone {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂) :
    Monotone c.toMorphism := by
  intro b₁ b₂ hle q₂ hdef₂
  cases hle (c.decodeQuery q₂) hdef₂ with
  | intro hdef₁ hval =>
    refine ⟨hdef₁, ?_⟩
    intro o₂ ⟨o₁, hdec, ho₁⟩
    exact ⟨o₁, hdec, hval o₁ ho₁⟩

/-- Every target outcome `o₂` that decodes to `some o₁` has the exact same
observable spine in `L₂` as the canonical encoding `c.encodeOut o₁`. -/
theorem BehaviorCodec.obs_encodeOut_of_decodeOut {SemObs : Type}
    {L₁ L₂ : Language SemObs} (c : BehaviorCodec L₁ L₂)
    {o₂ : L₂.Out} {o₁ : L₁.Out} (h : c.decodeOut o₂ = some o₁) :
    L₂.obs o₂ = L₂.obs (c.encodeOut o₁) := by
  have h₁ := c.obs_decodeOut o₂ o₁ h
  have h₂ := c.obs_decodeOut (c.encodeOut o₁) o₁ (c.decodeOut_encodeOut o₁)
  exact Eq.trans h₁ (Eq.symm h₂)

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
theorem verified_rejects_empty_dom {SemObs : Type} {L : Language SemObs}
    (p : L.Prog) (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (hempty : ∀ q, ¬ L.dom p q) :
    ¬ L.Verified pre post p
  | ⟨⟨q, hdom, _⟩, _, _⟩ => hempty q hdom

/-- Canary: `Obligation.wellFormedAndSpecsOn` rejects a contradictory
specification (`L.SpecOn (fun _ => False) post`) on every program, with no
assumption about the program's domain. -/
theorem wellFormedAndSpecsOn_rejects_contradictory_spec
    {Id SemObs : Type} {L : Language SemObs} (id : Id) (p : L.Prog)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) :
    ¬ (Obligation.wellFormedAndSpecsOn id L pre
        [L.SpecOn (fun _ => False) post] p).prop
  | ⟨_, ⟨⟨_, _, _, hfalse⟩, _⟩, _⟩ => hfalse

/-- A one-program, one-query language whose behavior is defined but has no
outcome at all (a miracle). Its domain is inhabited. -/
def MiracleCanaryLang : Language Unit where
  Prog  := Unit
  Query := Unit
  Out   := Unit
  obs   := fun _ => ()
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
def SrcUnitCanaryLang : Language Bool where
  Prog  := Unit
  Query := Unit
  Out   := Bool
  obs   := fun o => o
  sem   := fun _ _ => ⟨True, fun _ o => o = true⟩
  dom   := fun _ _ => True

/-- Target language for the query-slack canary: query `true` behaves like the
source, and query `false` is a miracle (defined, no outcome). -/
def TgtBoolSlackMiracleCanaryLang : Language Bool where
  Prog  := Unit
  Query := Bool
  Out   := Bool
  obs   := fun o => o
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
  obs_decodeOut _ _ h       := by injection h

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
