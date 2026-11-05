-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

-- anneal-trust-tier: candidate:refinement
prelude
import Init.NotationExtra
import Init.Core

/-!
# Refinement Core and Verification Judgments

Defines the language-independent vocabulary in which `Trusted.CrateTheorem`
(`Trusted/MirSemantics.lean`) is stated:

1. A constructive refinement order (`Preorder`, `Partial`, `Behavior`), where a
   behavior maps each query to a partial predicate over outcomes and undefined
   behavior (UB) is the top element.
2. Program-indexed languages (`Language`), pairing static program
   well-formedness (`wf : Prog → Prop`) with demonic behavioral semantics
   (`sem : Prog → Behavior Query Out`).
3. The verification judgment `Language.Verified`, which bundles static program
   well-formedness (`L.wf prog`), miracle-freedom (`L.ProductiveOn pre prog`),
   and demonic refinement (`L.sem prog ≤ L.SpecOn pre post`). Because `Behavior`
   forms a refinement lattice, multi-guarantee specifications—such as
   unconditional UB-freedom on `SafetyPre` paired with conditional functional
   correctness on `ContractPre := SafetyPre ∧ RequiresAdmits`—are expressed by a
   single `Language.Verified` judgment over `(SafetyPre, EffectivePost)` where
   `EffectivePost q out :=`
   `SafetyPost q out ∧ (RequiresAdmits q → ContractPost q out)`.
4. Named obligations (`Obligation`) and the waiver-aware `VerificationResult`.

Derived combinators (`wellFormedOn`), lattice-meet equivalences, cross-language
compilation codecs (`BehaviorCodec`, `Compiles`, `ProductiveCompiles`), and
their meta-theory live in `theory/` (`Anneal/Refinement.lean`), outside the
trusted computing base.
-/

namespace Trusted

/-- Reflexive and transitive refinement relation (`b₁ ≤ b₂`). -/
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting equips `A → B` with a refinement preorder. -/
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Constructive partiality carrier representing `B ∪ {UB}`: `defined` is
`False` exactly when the computation exhibits undefined behavior. -/
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Demonic refinement on `Partial B`: `p₁ ≤ p₂` holds when, wherever `p₂` is
defined, `p₁` is also defined and refines it. UB (`defined := False`) is
therefore the top element: it refines only itself, and everything refines it.
-/
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Query-indexed partial behaviors: for each query, either UB or a predicate
describing the set of permitted outcomes. -/
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language.

`wf prog` states static program well-formedness (for example, that all signature
and local types are modeled and within target size bounds, even when a runtime
precondition `pre` is uninhabited). -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  wf    : Prog → Prop
  sem   : Prog → Behavior Query Out

/-- Behavior domain of `L`. -/
abbrev Language.Behavior (L : Language) : Type :=
  Trusted.Behavior L.Query L.Out

/-- The specification "on queries satisfying `pre`, every outcome satisfies
`post`"; it is UB (undefined, hence unconstrained) outside `pre`. -/
def Language.SpecOn (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Unconditional specification on `L` (`pre := fun _ => True`). -/
abbrev Language.Spec (L : Language)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete behavioral verification of `prog` against `(pre, post)`: static
program well-formedness (`L.wf prog`), miracle-freedom
(`L.ProductiveOn pre prog`), and demonic behavioral refinement
(`L.sem prog ≤ L.SpecOn pre post`). -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.wf prog ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation pairing its canonical identifier `id` with its
proposition `prop`. -/
structure Obligation (Id : Type) where
  id   : Id
  prop : Prop

/-- Pairwise distinctness of the identifiers in `ids`. -/
def NoDupIds {Id : Type} (ids : List Id) : Prop :=
  (ids.foldr
    (fun id (acc : Prop × List Id) =>
      (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1, id :: acc.2))
    (True, [])).1

/-- Every obligation in `obligations` either holds by proof (`ob.prop`) or is
explicitly waived in `waived` (`ob.id ∈ waived`), with pairwise-distinct
obligation and waiver identifiers so one waiver cannot cover two obligations. -/
def VerificationResult {Id : Type}
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (obligations.map (fun ob => ob.prop ∨ ob.id ∈ waived))

end Trusted
