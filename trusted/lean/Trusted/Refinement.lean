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

Defines the language-independent vocabulary that `Trusted.CrateTheorem`
(`Trusted/MirSemantics.lean`) is stated in, and nothing else:

1. A constructive refinement order (`Preorder`, `Partial`, `Behavior`), where a
   behavior maps each query to a partial predicate over outcomes and undefined
   behavior (UB) is the top element.
2. Program-indexed languages (`Language`), whose `dom prog` is the set of
   queries (initial states) on which `prog` can actually be started.
3. The positive verification judgment `Language.Verified`, which bundles
   non-vacuity, miracle-freedom, and refinement so that no single conjunct can
   be satisfied in isolation.
4. Named obligations (`Obligation.assumed`, `Obligation.wellFormedAndSpecsOn`)
   and the waiver-aware `VerificationResult`.

Every definition here is reachable from `Trusted.CrateTheorem`. Derived
combinators (for example `wellFormedOn`), cross-language compilation codecs
(`BehaviorCodec`, `Compiles`, `ProductiveCompiles`), and their meta-theory live
in `theory/` (`Anneal/Refinement.lean`), outside the trusted computing base, so
an auditor reads only what the crate theorem means.

## How the judgments resist vacuity

A verification claim `L.Verified pre post prog` can be trivially true in three
ways, and each conjunct closes exactly one of them:

- **Empty precondition or domain:** `NonVacuousOn (L.dom prog) pre` requires a
  query that is both a real initial state of `prog` *and* satisfies `pre`. The
  witness must satisfy both at once; a `pre`-witness outside the domain does
  not count. There is no exception for an empty domain: a program with no
  initial state cannot be verified at all. This matters because the domain is
  where model limits surface at function entry (an argument type the model
  cannot measure, or a required constant the model cannot evaluate). Each such
  limit empties the domain, and an empty domain makes the claim unprovable
  rather than vacuously true, so model limits fail closed at entry just as
  they do during execution.
- **Miracles (no outcome at all):** `ProductiveOn pre prog` requires every
  admitted query to have at least one defined outcome, so a semantics that
  "produces nothing" cannot satisfy every postcondition.
- **Refinement itself:** `L.sem prog ≤ L.SpecOn pre post` is demonic
  refinement: wherever the specification is defined (`pre q`), the program must
  be defined (UB-free) and every program outcome must satisfy `post`.
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

`dom prog` is the set of queries on which `prog` can actually be started (for
an operational language, its initial states). It is indexed by the program so
that one program's initial states can never witness another program's
non-vacuity. `dom` has no default: a language that forgot to state its domain
would otherwise silently admit every query as an initial state. -/
structure Language where
  Prog  : Type
  Query : Type
  Out   : Type
  sem   : Prog → Behavior Query Out
  dom   : Prog → Query → Prop

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

/-- Domain-intersected precondition non-vacuity: some query is in `dom` *and*
satisfies `pre`.

There is deliberately no "or `dom` is empty" alternative. See the module
documentation: an empty domain is how a model limit at function entry shows
up, so accepting it would turn every such limit into vacuous verification. -/
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  ∃ q, dom q ∧ pre q

/-- Dijkstra's Law of the Excluded Miracle: every admitted query has at least
one defined outcome. -/
def Language.ProductiveOn (L : Language)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog` against
`(pre, post)` within `prog`'s own domain `L.dom prog`.

The domain is not a parameter: callers cannot substitute a smaller (or empty)
domain to make the non-vacuity conjunct trivially true. -/
def Language.Verified (L : Language)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn (L.dom prog) pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Right-nested conjunction of a list of propositions. -/
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- A named proof obligation. The constructor is private, so the only
obligations that exist are the ones built by the smart constructors below; a
proof author cannot invent a weaker proposition and give it a trusted name. -/
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

/-- Obligation representing an explicit, unproved assumption (such as `rustc`'s
lowering of a verified MIR body, an assumed external contract, or a waived
unverified function) that can only be discharged when `id` appears in the
crate's `waived` TCB list. -/
abbrev Obligation.assumed {Id : Type} (id : Id) : Obligation Id :=
  ⟨id, False⟩

/-- Obligation that `prog` is UB-free and productive on `pre` (non-vacuously)
and refines every specification in `specs` on `pre`. Each specification carries
its own non-vacuity requirement, so a specification whose own precondition is
unsatisfiable within `pre` cannot hold vacuously. -/
abbrev Obligation.wellFormedAndSpecsOn {Id : Type} (id : Id)
    (L : Language) (pre : L.Query → Prop) (specs : List L.Behavior)
    (prog : L.Prog) : Obligation Id :=
  ⟨id,
    L.Verified pre (fun _ _ => True) prog ∧
    AllHold (specs.map (fun spec =>
      NonVacuousOn (L.dom prog) (fun q => pre q ∧ (spec q).defined) ∧
      L.sem prog ≤ (fun q => ⟨pre q ∧ (spec q).defined,
        fun h o => (spec q).val h.2 o⟩)))⟩

/-- Policy governing which obligation identifiers `Id` may be waived. -/
structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

/-- Pairwise distinctness of the identifiers in `ids`. -/
def NoDupIds {Id : Type} : List Id → Prop
  | [] => True
  | id :: rest => AllHold (rest.map (fun id' => id ≠ id')) ∧ NoDupIds rest

/-- Every obligation either holds or is explicitly waived, and every waiver is
permitted by `policy`. Identifiers are distinct, so one waiver cannot cover two
different obligations. -/
def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

end Trusted
