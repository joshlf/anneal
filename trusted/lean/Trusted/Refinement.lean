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
import Trusted.Attributes

/-!
# Universal Refinement Core, Spine-Preserving Codecs, and Verification Units

This module (`Trusted/Refinement.lean`) defines Anneal's language-independent
semantic and verification kernel in `trusted/lean/`:

1. **Constructive Refinement Lattice (`Preorder`, `Partial`, `Behavior`):**
   Models query-indexed nondeterministic behaviors
   `Query → Partial (Out → Prop)` where Undefined Behavior (`Partial.ub`,
   `defined := False`) is the top
   element (`⊤`) and subset inclusion orders defined outcome sets, with zero
   `Classical.choice` or `propext` axioms.
2. **Spine-Indexed Languages (`Language SemObs`, `SpineSpecOn`):**
   Equips every language with an observable spine projection
   `obs : Out → SemObs` (defaulting to `SemObs := Out` and `obs := id` in
   `Language.mkSimple`),
   separating externally observable behavior (return values, terminal phases,
   and I/O or leakage traces) from concrete representation slack (caller-saved
   scratch registers, dead flags, uninitialized padding bytes, or redundant
   field limbs).
3. **Non-Vacuous, Miracle-Free Verification (`NonVacuousOn`, `NonVacuousPre`,
   `ProductiveOn`, `Language.VerifiedOn`, `Language.VerifiedInhabitedOn`):**
   Combines Dijkstra's Law of the Excluded Miracle (`ProductiveOn`), conditional
   specification refinement (`SpecOn`), and structural-domain non-vacuity
   (`NonVacuousOn dom pre` / `NonVacuousPre pre`), blocking empty-outcome
   miracles and contradictory preconditions while constructively admitting
   uninhabited parameter types (`Infallible` / `!`) and clean compile-time PME
   rejections.
4. **Spine-Preserving Representation Codecs (`BehaviorCodec`, `Compiles`,
   `ProductiveCompiles`, `Abstracts`):**
   Ensures all cross-language compilation (`Compiles` / `ProductiveCompiles`)
   and verification abstraction (`Abstracts`) passes are induced by structured
   query/outcome codecs that cover all source queries
   (`decodeQuery_encodeQuery`), fail closed on invalid target bit-patterns
   (`decodeOut o₂ = none`), and preserve the observable spine
   (`obs_decodeOut`).
5. **Non-Exploding Root Verification Envelope (`Obligation`, `TrustPolicy`,
   `EmittedArtifact`, `NoDupIds`, `VerificationResult`, `VerificationUnit`,
   `UnitTheorem`, `StrictUnitTheorem`):**
   Checks that the obligation inventory is non-empty, every waived obligation is
   permitted by `TrustPolicy`, and every obligation holds via the positive
   per-obligation disjunction `ob.id ∈ waived ∨ ob.prop` (with zero antecedent
   `hTcb → ...` implications that could explode across obligations via
   `False.elim`).

This file contains only definitions, structures, classes, and instances (zero
theorems and zero axioms).
-/

namespace Trusted

/-- A reflexive and transitive refinement relation (`b₁ ≤ b₂`), read "`b₁` is at
    least as defined as `b₂` and permits no more observable outcomes than
    `b₂`." -/
@[candidate refinement]
class Preorder (B : Type u) extends LE B where
  le_refl  : ∀ (b : B), b ≤ b
  le_trans : ∀ {a b c : B}, a ≤ b → b ≤ c → a ≤ c

/-- Implication (`P → Q`) equips `Prop` with a refinement preorder. -/
@[candidate refinement]
instance instPreorderProp : Preorder Prop where
  le P Q := P → Q
  le_refl _ h := h
  le_trans h₁ h₂ hp := h₂ (h₁ hp)

/-- Pointwise lifting (`∀ a, f a ≤ g a`) equips function spaces `A → B` with a
    refinement preorder whenever `B` is a `Preorder`. Together with
    `instPreorderProp`, this equips outcome predicates `Out → Prop` with subset
    inclusion (`∀ o, P o → Q o`). -/
@[candidate refinement]
instance instPreorderFun (A : Type u) (B : Type v) [Preorder B] :
    Preorder (A → B) where
  le f g := ∀ a, f a ≤ g a
  le_refl f a := Preorder.le_refl (f a)
  le_trans h₁ h₂ a := Preorder.le_trans (h₁ a) (h₂ a)

/-- Order-preserving mapping between preorders. -/
@[candidate refinement]
def Monotone {B₁ : Type u} {B₂ : Type v} [Preorder B₁] [Preorder B₂]
    (π : B₁ → B₂) : Prop :=
  ∀ ⦃x y : B₁⦄, x ≤ y → π x ≤ π y

/-- Constructive partiality carrier representing `B ∪ {UB}` without
    `Classical.choice`:
    - `defined : Prop` holds when the behavior is well-defined (free of UB).
    - `val : defined → B` yields the underlying value in `B` when `defined`
      holds, and is inhabited constructively by `False.elim` when `defined` is
      `False` (avoiding any `Inhabited B` or `Classical.choice` requirement).
      Gating `val` by `h : defined` makes it a type error to inspect outcomes
      without first proving definedness. -/
@[candidate refinement]
structure Partial (B : Type u) where
  defined : Prop
  val     : defined → B

/-- Embed an unconditionally defined value `b : B` into `Partial B`. -/
@[candidate refinement]
def Partial.pure {B : Type u} (b : B) : Partial B :=
  ⟨True, fun _ => b⟩

/-- The Undefined Behavior top element (`⊤`, `defined := False`) of
    `Partial B`. -/
@[candidate refinement]
def Partial.ub {B : Type u} : Partial B :=
  ⟨False, False.elim⟩

/-- The bottom predicate element (`⊥`, `defined := True`,
    `val := fun _ _ => False`) of `Partial (Out → Prop)`, representing an empty
    outcome set (such as an
    inapplicable query or a program rejected at compile time before runtime
    execution). -/
@[candidate refinement]
def Partial.bot {Out : Type u} : Partial (Out → Prop) :=
  ⟨True, fun _ _ => False⟩

/-- Map `f : B₁ → B₂` over the defined payload of `Partial B₁`. -/
@[candidate refinement]
def Partial.map {B₁ : Type u} {B₂ : Type v} (f : B₁ → B₂) (p : Partial B₁) :
    Partial B₂ :=
  ⟨p.defined, fun h => f (p.val h)⟩

/-- Dependent monadic bind on `Partial`: `Partial.bind p f` is defined when `p`
    is defined (`h : p.defined`) and `f (p.val h)` is defined, yielding
    `(f (p.val h.1)).val h.2`. Used to sequence partial compiler passes and to
    define demonic partial program semantics (`Language.semPartial`). -/
@[candidate refinement]
def Partial.bind {B₁ : Type u} {B₂ : Type v}
    (p : Partial B₁) (f : B₁ → Partial B₂) : Partial B₂ :=
  ⟨∃ h : p.defined, (f (p.val h)).defined, fun h => (f (p.val h.1)).val h.2⟩

/-- Canonical embedding of a computable `Option B` into `Partial B`
    (`some b ↦ Partial.pure b`, `none ↦ Partial.ub`). -/
@[candidate refinement]
def Option.toPartial {B : Type u} : Option B → Partial B
  | some b => Partial.pure b
  | none   => Partial.ub

/-- Directional demonic refinement on `Partial B`: whenever `p₂` is defined,
    `p₁` must also be defined and its value must refine `p₂`'s value.

    # Auditor Note on Lattice Polarity (`⊤` vs. `⊥`)
    In demonic refinement, `impl ≤ spec` reverses the Scott information order:
    - `Partial.ub` (`defined := False`) is the **top element** (`⊤`)
      (`p₁ ≤ Partial.ub` holds vacuously for all `p₁` via `False.elim`). On the
      right-hand side (`SpecOn` outside `pre`), `Partial.ub` places zero
      obligation on `p₁`. On the left-hand side (`impl = Partial.ub`), `p₁`
      cannot refine any defined specification (`p₂.defined → False`).
    - Conversely, when `B = (Out → Prop)`, a defined computation with an empty
      outcome set `⟨True, fun _ _ => False⟩` is the **bottom element** (`⊥`)
      ("Dijkstra's miracle"), which refines every defined specification
      vacuously and is ruled out by `Language.ProductiveOn`. -/
@[candidate refinement]
instance instPreorderPartial (B : Type u) [Preorder B] :
    Preorder (Partial B) where
  le p₁ p₂ := ∀ h₂ : p₂.defined, ∃ h₁ : p₁.defined, p₁.val h₁ ≤ p₂.val h₂
  le_refl p h := ⟨h, Preorder.le_refl (p.val h)⟩
  le_trans h₁₂ h₂₃ h₃ :=
    let ⟨h₂, hle₂₃⟩ := h₂₃ h₃
    let ⟨h₁, hle₁₂⟩ := h₁₂ h₂
    ⟨h₁, Preorder.le_trans hle₁₂ hle₂₃⟩

/-- Query-indexed partial behaviors `Query → Partial (Out → Prop)`. -/
@[candidate refinement]
abbrev Behavior (Query Out : Type) : Type :=
  Query → Partial (Out → Prop)

/-- A semantic language parameterized by its representation-invariant observable
    spine `SemObs` (such as terminal phase, external event trace, and canonical
    observable return value):
    - `obs : Out → SemObs` projects concrete outcomes onto `SemObs`.
    - `sem : Prog → Behavior Query Out` assigns each program its behavior.

    # Trust Contract on `SemObs` and `obs`
    Cross-language codecs (`BehaviorCodec`) enforce `L₂.obs o₂ = L₁.obs o₁` so
    concrete target representation slack can be erased many-to-one without
    permuting observable values:
    1. `SemObs` MUST include all boundary-observable outcome data: the
       architectural return value (or unwind/panic payload), the terminal phase
       (`.terminated`, `.diverges`, `.reacts`), any ABI-preserved (callee-saved)
       registers, and any external I/O or security leakage trace.
    2. `obs : Out → SemObs` may erase ONLY concrete representation slack that is
       invisible across the language boundary (caller-saved scratch registers,
       dead ALU status flags, uninitialized padding bytes, or redundant field
       limbs). Defining `obs` as a constant function (e.g., `fun _ => ()`) on a
       value-returning language is a trust-boundary bug. -/
@[candidate refinement]
structure Language (SemObs : Type) where
  Prog  : Type
  Query : Type
  Out   : Type
  obs   : Out → SemObs
  sem   : Prog → Behavior Query Out
  /-- Intrinsic structural query domain of the language instance. Defaults to
      `fun _ => True`, and is specialized via `Language.withDom` when scoping a
      language to a typed function or module boundary (`BB1.BoundaryDom`). -/
  dom   : Query → Prop := fun _ => True

/-- Construct a `Language` whose concrete outcomes `Out` coincide with its
    observable spine (`SemObs := Out`, `obs := id`). -/
@[candidate refinement]
abbrev Language.mkSimple (Prog Query Out : Type)
    (sem : Prog → Behavior Query Out) : Language Out where
  Prog  := Prog
  Query := Query
  Out   := Out
  obs   := fun o => o
  sem   := sem

/-- Specialize a language's intrinsic structural query domain `L.dom` to
    `dom'`. -/
@[candidate refinement]
abbrev Language.withDom {SemObs : Type} (L : Language SemObs)
    (dom' : L.Query → Prop) : Language SemObs :=
  { L with dom := dom' }

/-- Post-compose `f : SemObs₁ → SemObs₂` onto the observable spine of `L`,
    preserving `L.dom`. -/
@[candidate refinement]
abbrev Language.mapObs {SemObs₁ SemObs₂ : Type}
    (f : SemObs₁ → SemObs₂) (L : Language SemObs₁) : Language SemObs₂ where
  Prog  := L.Prog
  Query := L.Query
  Out   := L.Out
  obs   := fun o => f (L.obs o)
  sem   := L.sem
  dom   := L.dom

/-- Behavior domain of `L`. -/
@[candidate refinement]
abbrev Language.Behavior {SemObs : Type} (L : Language SemObs) : Type :=
  Trusted.Behavior L.Query L.Out

/-- Query-indexed specification on `L` requiring definedness on `pre q` and
    restricting outcomes at `q` to `post q`. Outside `pre`, `SpecOn` evaluates
    to `Partial.ub`, leaving behavior unconstrained. -/
@[candidate refinement]
def Language.SpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop) : L.Behavior :=
  fun q => ⟨pre q, fun _ => post q⟩

/-- Spine-anchored specification on `L` whose postcondition `obsPost` inspects
    only the observable spine `L.obs o : SemObs`. Transfers directly across any
    `BehaviorCodec` without referencing `decodeOut` in the target theorem, and
    exposes trivial `SemObs := Unit` erasure in the specification type
    itself. -/
@[candidate refinement]
def Language.SpineSpecOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop) : L.Behavior :=
  L.SpecOn pre (fun q o => obsPost q (L.obs o))

/-- Unconditional specification on `L` (`pre := fun _ => True`). -/
@[candidate refinement]
abbrev Language.Spec {SemObs : Type} (L : Language SemObs)
    (post : L.Query → L.Out → Prop) : L.Behavior :=
  L.SpecOn (fun _ => True) post

/-- Conditional well-formedness (UB-freedom) on `pre`. -/
@[candidate refinement]
abbrev Language.WellFormedOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) : L.Behavior :=
  L.SpecOn pre (fun _ _ => True)

/-- Unconditional well-formedness (UB-freedom) on all queries. -/
@[candidate refinement]
abbrev Language.WellFormed {SemObs : Type} (L : Language SemObs) : L.Behavior :=
  L.WellFormedOn (fun _ => True)

/-- Precondition non-vacuity relative to structural domain `dom`: either `pre`
    is inhabited (`∃ q, pre q`), or the structural domain `dom` is itself
    provably uninhabited (`∀ q, ¬ dom q`, as in `fn absurd(x: Infallible)` or
    clean compile-time PME rejection).

    # Auditor Trust Requirement on `dom`
    When using 4-argument `Language.VerifiedOn dom pre post prog`, `dom` MUST be
    locked by the trusted boundary generator to the unfiltered structural
    parameter domain (before user `requires` clauses). Passing `dom := pre` or
    `dom := fun _ => False` is forbidden; for standard inhabited-domain tools,
    use 3-argument `Language.VerifiedInhabitedOn` (`NonVacuousPre`), which fixes
    `dom := fun _ => True`. -/
@[candidate refinement]
def NonVacuousOn {Query : Type} (dom pre : Query → Prop) : Prop :=
  (∃ q, pre q) ∨ (∀ q, ¬ dom q)

/-- Parameterless precondition non-vacuity (`dom := fun _ => True`): either
    `pre` is inhabited (`∃ q, pre q`) or the query type `Query` itself is
    uninhabited (`∀ _ : Query, False`, e.g., `Query = Empty`). Cannot be
    bypassed by supplying a synthetic `dom` predicate. -/
@[candidate refinement]
abbrev NonVacuousPre {Query : Type} (pre : Query → Prop) : Prop :=
  NonVacuousOn (fun _ => True) pre

/-- Unconditional precondition inhabitation (`∃ q, pre q`). -/
@[candidate refinement]
abbrev InhabitedPre {Query : Type} (pre : Query → Prop) : Prop :=
  ∃ q, pre q

/-- Dijkstra's Law of the Excluded Miracle on `L`: at every query `q` satisfying
    `pre q`, `prog` is both defined (UB-free) and produces at least one valid
    outcome (`∃ o, (L.sem prog q).val h o`). Rules out empty-outcome miracles
    and negative-polarity `.stuck` / `initState` vacuity. -/
@[candidate refinement]
def Language.ProductiveOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (prog : L.Prog) : Prop :=
  ∀ q, pre q → ∃ h : (L.sem prog q).defined, ∃ o : L.Out, (L.sem prog q).val h o

/-- Complete, non-vacuous behavioral verification of `prog : L.Prog` on `pre`
    (within structural domain `dom`) against postcondition `post`:
    1. `NonVacuousOn dom pre` (blocks contradictory `requires false` on
       inhabited domains),
    2. `L.ProductiveOn pre prog` (blocks empty-outcome `⊥` miracles and
       uninhabited `initState` / over-constrained relation vacuity), and
    3. `L.sem prog ≤ L.SpecOn pre post` (enforces UB-freedom and postcondition
       satisfaction on `pre`). -/
@[candidate refinement]
def Language.VerifiedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  NonVacuousOn dom pre ∧
  L.ProductiveOn pre prog ∧
  L.sem prog ≤ L.SpecOn pre post

/-- Canonical 3-argument verification judgment fixing `dom := fun _ => True`.
    Eliminates the `dom` parameter for tools whose query domain is typed
    directly by `L.Query` (returning `Or.inr Empty.elim` when `L.Query = Empty`
    and
    requiring `∃ q, pre q` whenever `L.Query` is inhabited). -/
@[candidate refinement]
abbrev Language.VerifiedInhabitedOn {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn (fun _ => True) pre post prog

/-- Canonical 3-argument domain-intrinsic verification judgment locking `dom`
    to `L.dom`. Eliminates free `dom` spoofing on theorem statements; when `L`
    uses the default `dom := fun _ => True`, `L.Verified pre post prog` is
    judgmentally equal (`rfl`) to `L.VerifiedInhabitedOn pre post prog`. -/
@[candidate refinement]
abbrev Language.Verified {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn L.dom pre post prog

/-- Explicit-domain spine-anchored verification judgment inspecting only the
    observable spine `L.obs o : SemObs`. -/
@[candidate refinement]
abbrev Language.VerifiedSpineOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedOn dom pre (fun q o => obsPost q (L.obs o)) prog

/-- Canonical 3-argument spine-anchored verification judgment locking `dom` to
    `L.dom` and `post` to `L.obs`. -/
@[candidate refinement]
abbrev Language.VerifiedSpine {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Prop :=
  L.VerifiedSpineOn L.dom pre obsPost prog

/-- Explicit-domain negative canary (`¬ L.VerifiedOn dom pre post badProg`). -/
@[candidate refinement]
abbrev Language.RefutedOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  ¬ L.VerifiedOn dom pre post badProg

/-- Canonical 3-argument negative canary judgment locked to `L.dom`. -/
@[candidate refinement]
abbrev Language.Refuted {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.RefutedOn L.dom pre post badProg

/-- Productive negative-canary judgment: `badProg` is defined and productive on
    `pre` (`L.ProductiveOn pre badProg`) yet fails
    `L.VerifiedOn dom pre post badProg` because it produces an outcome
    violating `post`. Simultaneously refutes `post := fun _ _ => True`,
    constant `L.obs`, and `SemObs := Unit` with zero external side
    conditions. -/
@[candidate refinement]
def Language.RefutedProductiveOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.ProductiveOn pre badProg ∧ ¬ L.VerifiedOn dom pre post badProg

/-- Canonical 3-argument productive negative-canary judgment locked to
    `L.dom`. -/
@[candidate refinement]
abbrev Language.RefutedProductive {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Prop :=
  L.RefutedProductiveOn L.dom pre post badProg

/-- Right-nested conjunction of a list of propositions. -/
@[candidate refinement]
def AllHold (props : List Prop) : Prop :=
  props.foldr (· ∧ ·) True

/-- Two-sided verification judgment with explicit `dom` and non-empty negative
    canary list `badProgs`: proves positive verification of `goodProg`,
    `badProgs ≠ []`, and refutation of every canary in `badProgs` under the
    exact same `(dom, pre, post)` contract. -/
@[candidate refinement]
def Language.VerifiedWithCanariesOn {SemObs : Type} (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedOn dom pre post goodProg ∧
  badProgs ≠ [] ∧
  AllHold (badProgs.map (L.RefutedOn dom pre post))

/-- Canonical 3-argument two-sided verification judgment with paired negative
    canaries `badProgs` locked to `L.dom`. -/
@[candidate refinement]
abbrev Language.VerifiedWithCanaries {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedWithCanariesOn L.dom pre post goodProg badProgs

/-- Two-sided spine-anchored verification judgment with explicit `dom` and
    paired negative canaries `badProgs`. -/
@[candidate refinement]
abbrev Language.VerifiedSpineWithCanariesOn {SemObs : Type}
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedWithCanariesOn dom pre (fun q o => obsPost q (L.obs o))
    goodProg badProgs

/-- Canonical 3-argument spine-anchored two-sided verification judgment with
    paired negative canaries `badProgs` locked to `L.dom` and `L.obs`. -/
@[candidate refinement]
abbrev Language.VerifiedSpineWithCanaries {SemObs : Type} (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Prop :=
  L.VerifiedSpineWithCanariesOn L.dom pre obsPost goodProg badProgs

/-- Representation codec between two languages `L₁` and `L₂` sharing observable
    spine `SemObs`:
    - `decodeQuery_encodeQuery`: `decodeQuery` is a retraction of `encodeQuery`,
      ensuring every source query `q₁` is covered.
    - `decodeOut_encodeOut`: `decodeOut` is a partial retraction of `encodeOut`,
      allowing `decodeOut o₂ = none` to reject invalid target bit patterns while
      permitting many-to-one concrete slack (scratch registers, padding bytes,
      redundant limbs) inside each valid fiber.
    - `obs_decodeOut`: every valid outcome decode preserves the observable spine
      `SemObs` identically (`L₂.obs o₂ = L₁.obs o₁`), replacing injective
      `encodeOut_of_decodeOut` so many-to-one concrete target states are
      admitted while value-permutation codecs remain refuted. -/
@[candidate refinement]
structure BehaviorCodec {SemObs : Type} (L₁ L₂ : Language SemObs) where
  encodeQuery : L₁.Query → L₂.Query
  decodeQuery : L₂.Query → L₁.Query
  encodeOut   : L₁.Out → L₂.Out
  decodeOut   : L₂.Out → Option L₁.Out
  decodeQuery_encodeQuery : ∀ q₁, decodeQuery (encodeQuery q₁) = q₁
  decodeOut_encodeOut     : ∀ o₁, decodeOut (encodeOut o₁) = some o₁
  obs_decodeOut           : ∀ o₂ o₁,
    decodeOut o₂ = some o₁ → L₂.obs o₂ = L₁.obs o₁

/-- Canonical monotone behavior morphism induced by `c : BehaviorCodec L₁ L₂`.
    When `c.decodeOut o₂ = none` (e.g., an invalid `0x02` bit-pattern in a
    target `bool` register), no `o₁` satisfies `none = some o₁`, so the mapped
    predicate evaluates to `False` (fail-closed target decoding). -/
@[candidate refinement]
def BehaviorCodec.toMorphism {SemObs : Type} {L₁ L₂ : Language SemObs}
    (c : BehaviorCodec L₁ L₂) (b : L₁.Behavior) : L₂.Behavior :=
  fun q₂ => {
    defined := (b (c.decodeQuery q₂)).defined
    val     := fun h o₂ =>
      ∃ o₁, c.decodeOut o₂ = some o₁ ∧ (b (c.decodeQuery q₂)).val h o₁
  }

/-- Downward/horizontal compilation
    (`L_tgt.sem t ≤ c.toMorphism (L_src.sem s)`):
    preserves definedness forward and refines allowed outcomes downward. -/
@[candidate refinement]
abbrev Compiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  L_tgt.sem t ≤ c.toMorphism (L_src.sem s)

/-- Miracle-free downward/horizontal compilation: pairs `Compiles` with
    universal target query productivity preservation from `s` to `t` across
    every target query `q₂` whose decoded source query `c.decodeQuery q₂` is
    productive in `s`. Quantifying universally over all `q₂ : L_tgt.Query`
    (rather than only `c.encodeQuery q₁`) rules out target query-slack miracles
    on non-canonical target query fibers as well as empty outcome sets
    (`initState = False` or over-constrained R1CS circuits `1 = 0`). -/
@[candidate refinement]
def ProductiveCompiles {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog) (t : L_tgt.Prog) : Prop :=
  Compiles L_src L_tgt c s t ∧
  ∀ q₂,
    (∃ h₁ : (L_src.sem s (c.decodeQuery q₂)).defined,
      ∃ o₁, (L_src.sem s (c.decodeQuery q₂)).val h₁ o₁) →
    (∃ h₂ : (L_tgt.sem t q₂).defined,
      ∃ o₂, (L_tgt.sem t q₂).val h₂ o₂)

/-- Conditional downward/horizontal compilation for a partial target program
    `t? : Partial L_tgt.Prog`: whenever compilation succeeds (`h : t?.defined`),
    the emitted target artifact `t?.val h` compiles `s` under `c`. -/
@[candidate refinement]
def CompilesPartial {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog)
    (t? : Partial L_tgt.Prog) : Prop :=
  ∀ h : t?.defined, Compiles L_src L_tgt c s (t?.val h)

/-- Miracle-free conditional compilation for a partial target program
    `t? : Partial L_tgt.Prog`: whenever compilation succeeds (`h : t?.defined`),
    the emitted target artifact `t?.val h` satisfies `ProductiveCompiles` for
    `s` under `c`. -/
@[candidate refinement]
def ProductiveCompilesPartial {SemObs : Type} (L_src L_tgt : Language SemObs)
    (c : BehaviorCodec L_src L_tgt) (s : L_src.Prog)
    (t? : Partial L_tgt.Prog) : Prop :=
  ∀ h : t?.defined, ProductiveCompiles L_src L_tgt c s (t?.val h)

/-- Upward abstraction (`L_src.sem s ≤ c.toMorphism (L_v.sem v)`): reflects
    definedness backward from verifier model `v` to `s` and over-approximates
    outcomes. -/
@[candidate refinement]
abbrev Abstracts {SemObs : Type} (L_v L_src : Language SemObs)
    (c : BehaviorCodec L_v L_src) (v : L_v.Prog) (s : L_src.Prog) : Prop :=
  L_src.sem s ≤ c.toMorphism (L_v.sem v)

/-- Constructor-gated named proof obligation with identifier `id : Id` and
    proposition `prop : Prop`.
    The raw constructor `Obligation.mk` is marked `private` to
    `Trusted/Refinement.lean` so external modules (`Mir.lean`, `Anneal/*`,
    `Proof.lean`) cannot construct raw `{ id := ..., prop := True }` or
    unhardened `L.sem p ≤ spec` claims. All external `Obligation` values must be
    constructed through the smart constructors below (which enforce
    `NonVacuousOn`, `ProductiveOn`, `WellFormedOn`, or `ProductiveCompiles`),
    while concrete verification gates (`Trusted.CrateTheorem`) fix the language
    (`MirLang`), domain (`MirLang.dom`), and effective precondition
    (`fn.effectivePre`), keeping `Obligation Id : Type` (`Type 0`) and literal
    `rfl` projection of `.id` and `.prop`. -/
@[candidate refinement]
structure Obligation (Id : Type) where
  private mk ::
  id   : Id
  prop : Prop

/-- Smart constructor for 3-argument domain-intrinsic `L.Verified`. -/
@[candidate refinement]
abbrev Obligation.verified {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.Verified pre post prog⟩

/-- Smart constructor for 4-argument `L.VerifiedOn`. -/
@[candidate refinement]
abbrev Obligation.verifiedOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedOn dom pre post prog⟩

/-- Smart constructor for 3-argument `L.VerifiedInhabitedOn`. -/
@[candidate refinement]
abbrev Obligation.verifiedInhabitedOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedInhabitedOn pre post prog⟩

/-- Smart constructor for 3-argument spine-anchored `L.VerifiedSpine`. -/
@[candidate refinement]
abbrev Obligation.verifiedSpine {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedSpine pre obsPost prog⟩

/-- Smart constructor for 4-argument spine-anchored `L.VerifiedSpineOn`. -/
@[candidate refinement]
abbrev Obligation.verifiedSpineOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (prog : L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedSpineOn dom pre obsPost prog⟩

/-- Smart constructor for two-sided `L.VerifiedWithCanariesOn`. -/
@[candidate refinement]
abbrev Obligation.verifiedWithCanariesOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedWithCanariesOn dom pre post goodProg badProgs⟩

/-- Smart constructor for 3-argument two-sided `L.VerifiedWithCanaries`. -/
@[candidate refinement]
abbrev Obligation.verifiedWithCanaries {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedWithCanaries pre post goodProg badProgs⟩

/-- Smart constructor for 4-argument spine-anchored two-sided
    `L.VerifiedSpineWithCanariesOn`. -/
@[candidate refinement]
abbrev Obligation.verifiedSpineWithCanariesOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedSpineWithCanariesOn dom pre obsPost goodProg badProgs⟩

/-- Smart constructor for 3-argument spine-anchored two-sided
    `L.VerifiedSpineWithCanaries`. -/
@[candidate refinement]
abbrev Obligation.verifiedSpineWithCanaries {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (obsPost : L.Query → SemObs → Prop)
    (goodProg : L.Prog) (badProgs : List L.Prog) : Obligation Id :=
  ⟨id, L.VerifiedSpineWithCanaries pre obsPost goodProg badProgs⟩

/-- Smart constructor for miracle-free `ProductiveCompiles`. -/
@[candidate refinement]
abbrev Obligation.compiles {Id SemObs : Type} (id : Id)
    (L_src L_tgt : Language SemObs) (c : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t : L_tgt.Prog) : Obligation Id :=
  ⟨id, ProductiveCompiles L_src L_tgt c s t⟩

/-- Smart constructor for miracle-free `ProductiveCompiles`. -/
@[candidate refinement]
abbrev Obligation.productiveCompiles {Id SemObs : Type} (id : Id)
    (L_src L_tgt : Language SemObs) (c : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t : L_tgt.Prog) : Obligation Id :=
  ⟨id, ProductiveCompiles L_src L_tgt c s t⟩

/-- Smart constructor for `CompilesPartial`. -/
@[candidate refinement]
abbrev Obligation.compilesPartial {Id SemObs : Type} (id : Id)
    (L_src L_tgt : Language SemObs) (c : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t? : Partial L_tgt.Prog) : Obligation Id :=
  ⟨id, CompilesPartial L_src L_tgt c s t?⟩

/-- Smart constructor for miracle-free `ProductiveCompilesPartial`. -/
@[candidate refinement]
abbrev Obligation.productiveCompilesPartial {Id SemObs : Type} (id : Id)
    (L_src L_tgt : Language SemObs) (c : BehaviorCodec L_src L_tgt)
    (s : L_src.Prog) (t? : Partial L_tgt.Prog) : Obligation Id :=
  ⟨id, ProductiveCompilesPartial L_src L_tgt c s t?⟩

/-- Smart constructor for proof-gated pipeline verification (`L_src.VerifiedOn`
    paired with positive compilation `∃ h : t?.defined, Compiles ...`). -/
@[candidate refinement]
abbrev Obligation.verifiedCompilesPartialOn {Id SemObs : Type} (id : Id)
    (L_src L_tgt : Language SemObs) (c : BehaviorCodec L_src L_tgt)
    (dom pre : L_src.Query → Prop) (post : L_src.Query → L_src.Out → Prop)
    (s : L_src.Prog) (t? : Partial L_tgt.Prog) : Obligation Id :=
  ⟨id, L_src.VerifiedOn dom pre post s ∧
    ∃ h : t?.defined, Compiles L_src L_tgt c s (t?.val h)⟩

/-- Smart constructor for `Abstracts`. -/
@[candidate refinement]
abbrev Obligation.abstracts {Id SemObs : Type} (id : Id)
    (L_v L_src : Language SemObs) (c : BehaviorCodec L_v L_src)
    (v : L_v.Prog) (s : L_src.Prog) : Obligation Id :=
  ⟨id, Abstracts L_v L_src c v s⟩

/-- Smart constructor for 4-argument negative canary `L.RefutedOn`. -/
@[candidate refinement]
abbrev Obligation.refutedOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Obligation Id :=
  ⟨id, L.RefutedOn dom pre post badProg⟩

/-- Smart constructor for 3-argument negative canary `L.Refuted`. -/
@[candidate refinement]
abbrev Obligation.refuted {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Obligation Id :=
  ⟨id, L.Refuted pre post badProg⟩

/-- Smart constructor for 4-argument productive negative canary
    `L.RefutedProductiveOn`. -/
@[candidate refinement]
abbrev Obligation.refutedProductiveOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (dom pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Obligation Id :=
  ⟨id, L.RefutedProductiveOn dom pre post badProg⟩

/-- Smart constructor for 3-argument productive negative canary
    `L.RefutedProductive`. -/
@[candidate refinement]
abbrev Obligation.refutedProductive {Id SemObs : Type} (id : Id)
    (L : Language SemObs)
    (pre : L.Query → Prop) (post : L.Query → L.Out → Prop)
    (badProg : L.Prog) : Obligation Id :=
  ⟨id, L.RefutedProductive pre post badProg⟩

/-- Inductive conjunction of two already-constructed `Obligation` values. -/
@[candidate refinement]
abbrev Obligation.and {Id : Type} (id : Id)
    (ob₁ ob₂ : Obligation Id) : Obligation Id :=
  ⟨id, ob₁.prop ∧ ob₂.prop⟩

/-- Smart constructor for multi-specification refinement anchored at baseline
    domain-intrinsic verification `L.Verified pre (fun _ _ => True) prog`
    (locking `dom` to `L.dom` and enforcing `NonVacuousOn L.dom pre`,
    `L.ProductiveOn pre prog`, and `L.WellFormedOn pre`). -/
@[candidate refinement]
abbrev Obligation.wellFormedAndSpecsOn {Id SemObs : Type} (id : Id)
    (L : Language SemObs) (pre : L.Query → Prop) (specs : List L.Behavior)
    (prog : L.Prog) : Obligation Id :=
  ⟨id,
    L.Verified pre (fun _ _ => True) prog ∧
    AllHold (specs.map (fun spec => L.sem prog ≤ spec))⟩

/-- Policy governing which obligation identifiers `Id` may be waived. -/
@[candidate refinement]
structure TrustPolicy (Id : Type) where
  isAllowed : Id → Prop

/-- Default strict policy forbidding all waivers (`isAllowed _ := False`). -/
@[candidate refinement]
def TrustPolicy.strict {Id : Type} : TrustPolicy Id :=
  ⟨fun _ => False⟩

/-- Single-source `.olean`-bound external artifact binding: pairs relative path
    `path` with the actual content `contents` (computed inside Lean from the
    verified target AST) and the expected literal string `expected` (defaulting
    to `contents` and checked byte-for-byte against disk by `anneal-audit`). -/
@[candidate refinement]
structure EmittedArtifact where
  path     : String
  contents : String
  expected : String := contents

/-- Kernel-checked equality verifying that the pure Lean emitter expression
    `a.contents` equals the expected literal `a.expected`. -/
@[candidate refinement]
def EmittedArtifact.holds (a : EmittedArtifact) : Prop :=
  a.contents = a.expected

/-- Pairwise distinctness of obligation identifiers in `ids`, preventing a
    single waived identifier from shadowing multiple distinct obligations.
    Expressed via `List.foldr` so `trusted/lean/` introduces no recursive
    auxiliary definitions. -/
@[candidate refinement]
def NoDupIds {Id : Type} (ids : List Id) : Prop :=
  (ids.foldr
    (fun id (acc : Prop × List Id) =>
      (AllHold (acc.2.map (fun id' => id ≠ id')) ∧ acc.1, id :: acc.2))
    (True, [])).1

/-- Positive per-obligation verification judgment:
    1. `obligations ≠ []`: the obligation inventory is non-empty,
    2. `NoDupIds (obligations.map Obligation.id)`: obligation identifiers are
       pairwise distinct,
    3. `NoDupIds waived`: waived identifiers are pairwise distinct,
    4. `AllHold (waived.map policy.isAllowed)`: every identifier in `waived` is
       allowed by `policy`, and
    5. `AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))`: every
       obligation in `obligations` is either listed in `waived` (`Or.inl`) or
       constructively proven (`Or.inr`).
    Contains zero antecedent implications (`→`), preventing cross-obligation
    Principle of Explosion when a waived obligation is false. -/
@[candidate refinement]
def VerificationResult {Id : Type}
    (policy : TrustPolicy Id)
    (waived : List Id)
    (obligations : List (Obligation Id)) : Prop :=
  obligations ≠ [] ∧
  NoDupIds (obligations.map Obligation.id) ∧
  NoDupIds waived ∧
  AllHold (waived.map policy.isAllowed) ∧
  AllHold (obligations.map (fun ob => ob.id ∈ waived ∨ ob.prop))

/-- Universal verification target checked by `anneal-audit`, bundling its
    `policy`, `waived` list, `obligations` inventory, and optional single-source
    emitted disk artifacts `artifacts` (`[]` for pure source verifiers). -/
@[candidate refinement]
structure VerificationUnit (Id : Type) where
  policy      : TrustPolicy Id := TrustPolicy.strict
  waived      : List Id := []
  obligations : List (Obligation Id)
  artifacts   : List EmittedArtifact := []

/-- Incremental verification unit theorem allowing explicit waivers permitted by
    `u.policy`. -/
@[candidate refinement]
def UnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  VerificationResult u.policy u.waived u.obligations

/-- Hardened zero-debt root theorem bundling `UnitTheorem u` with kernel-checked
    `u.waived = []` (enforcing zero waivers inside the Lean kernel regardless of
    `u.policy`), `NoDupIds` (blocking duplicate-ID waiver shadowing), and
    `AllHold (u.artifacts.map EmittedArtifact.holds)` (binding emitted artifacts
    to `u.artifacts`). -/
@[candidate refinement]
def StrictUnitTheorem {Id : Type} (u : VerificationUnit Id) : Prop :=
  UnitTheorem u ∧
  u.waived = [] ∧
  NoDupIds (u.obligations.map Obligation.id) ∧
  AllHold (u.artifacts.map EmittedArtifact.holds)

end Trusted
