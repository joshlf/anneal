/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Lean
import Miri.Interpreter.ValidityVisitor
import Anneal.MirFuelFree

/-!
# Schema 17 validation rank certificates and fuel-free validation (`LeanMiriSpec.ValidationRankCert`)

Upstream `proofs-rs/lean-miri#90` removes the arbitrary validation traversal budget
(`limits.validation`) from `Miri.Interpreter.ValidityVisitor`: every compiler `TypeNode` carries a
Schema 17 by-value `validation_rank`, `unionRanges` recurses by well-founded recursion on the
static order `layoutOrder` (`3 * rank + phase`), `visit` recurses on the lexicographic order
`visitOrder` (`(if isSized then 0 else 1, layoutOrder)` under `Prod.Lex`) so dynamic `dyn Trait`
unpacking from an unsized place to an arbitrary higher-rank concrete sized type still descends,
every effectful projection hook result is checked dynamically to descend (`.invalidProgram "… does
not descend"` otherwise), and tracked pointees are drained in LIFO order without further tracking
so cyclic pointer graphs never feed back into the by-value recursion.

This module formalizes that design over the *unmodified* vendored `lean-miri` (which still uses
fuel), against the real `Miri.Interpreter.ValidityVisitor.{Hooks, M, unionRanges, visit}`,
`Miri.Interpreter.StepError`, `LocalLayout`, `RuntimePlace`, `ValidationSession`, `RefTracking`,
and `DataRangeSet` types:

1. `layoutOrder` and `visitOrder` (verbatim from `lean-miri#90`) and their descent lemmas across
   smaller-rank children, enum variants, synthetic scalar fields, and unsized-to-sized dynamic
   unpacking (`visitOrder_lt_of_unsized_unpack`).
2. `ValidationRankCert` (`checkCert`, closed by construction so missing children cannot hide
   cycles) alongside `Schema17TypeNode` / `checkSchema17Table` mirroring `lean-miri#90`
   `Decoder.validateParsedDocument` across `.adt`, `.array`, `.slice`, `.patternType`,
   `.unsafeBinder`, `.tuple`, `.closure`, `.coroutine` `savedTypes`, and `normalizedType` aliases
   while decoupling `.pointerIndirection` edges, with soundness and acyclicity theorems.
3. Rank-guarded traversals:
   - `RankedWalk` (`layoutOrder`) and `VisitLexWalk` (`visitOrder` under `Prod.Lex`, paired with an
     unconditional `Classical.choice`-free `ω · 2` nested-`Nat.rec` structural companion
     `VisitLexWalk.walkRank`),
   - `realUnionRangesNoFuel` (verbatim `lean-miri#90` `unionRanges` over real
     `ValidityVisitor.Hooks`) proved equivalent to the **actual vendored
     `Miri.Interpreter.ValidityVisitor.unionRanges`** for all `fuel > layoutOrder typeRank root`
     (`vendored_unionRanges_eq_noFuel`), and
   - `drainPointees` / `pointeeSession` LIFO pointee queue draining.
4. Equivalences, deterministic `.invalidProgram` hook-violation rejection, and the
   `Anneal.MirFuelFree` bridge (`rankCountdown_converges_iff`, `rankCountdown_canonical`,
   `walkFuel_eq_walkNoFuel_of_wpCoalBounded`, `vendored_unionRanges_eq_noFuel_of_wpCoalBounded`).
5. Kernel-evaluated 150-level nested single-field wrapper, union, and pattern witnesses over both
   the companion traversals and the actual vendored `ValidityVisitor.{unionRanges, visit}`.
6. `leanprover/lean4#13851` axiom footprint audit (`#guard_msgs` `#print axioms`,
   `#assert_choice_free`, and module-wide `#assert_standard_axioms` sweeping `env.constants.map₂`).
-/

set_option autoImplicit false

/-- Fail unless every listed declaration carries a non-empty docstring and every declaration
elaborated in this module (`env.constants.map₂`, public and private) depends only on Lean's
standard axioms (`propext`, `Quot.sound`, `Classical.choice`): zero `sorryAx` and zero
`Lean.ofReduceBool`. -/
local elab "#assert_standard_axioms " ids:ident* : command => do
  let env ← Lean.getEnv
  for id in ids do
    let n ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    let axs ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    match ← Lean.findDocString? env n with
    | some doc =>
      if doc.trimAscii.isEmpty then
        throwError "{n} has an empty docstring"
    | none =>
      throwError "{n} is missing a docstring"
    Lean.logInfo m!"{n} depends on axioms: {axs.toList}"
  let mut checked : Nat := 0
  let mut seen : Array Lean.Name := #[]
  for (c, _) in env.constants.map₂.toList do
    let axs ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms c
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{c} (in LeanMiriSpec.ValidationRankCert) depends on non-standard axiom {a}"
      unless seen.contains a do
        seen := seen.push a
    checked := checked + 1
  if checked == 0 then
    throwError "module-wide axiom audit checked 0 declarations"
  Lean.logInfo m!"LeanMiriSpec.ValidationRankCert module-wide audit: {checked} declarations depend only on {seen.toList}"

/-- Fail unless every listed declaration depends only on `propext` and `Quot.sound` (no
`Classical.choice`): the structural footprint that survives `leanprover/lean4#13851`. -/
local elab "#assert_choice_free " ids:ident* : command => do
  for id in ids do
    let n ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    let axs ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound do
        throwError "{n} depends on {a}, outside the Classical.choice-free footprint"
    Lean.logInfo m!"{n} is Classical.choice-free: {axs.toList}"

namespace LeanMiriSpec.ValidationRankCert

open Miri.ABI Miri.Memory Miri.Memory.Validity Miri.Interpreter
open Miri.Interpreter.ValidityVisitor (Hooks M Key Session)

/-! ## 1. Schema 17 `layoutOrder` and `visitOrder` (`lean-miri#90`) -/

/-- The phase of a layout within its type id (`lean-miri#90`): a selected enum variant precedes
its multi-variant parent (phase `2`) and a synthetic primitive field (phase `0`) precedes its
aggregate parent (phase `1`), even when they share the parent's type id. -/
def layoutPhase (place : LocalLayout) : Nat :=
  match place.layout.variants, place.layout.fields with
  | .Multiple .., _ => 2
  | _, .Primitive => 0
  | _, _ => 1

/-- `lean-miri#90`'s static layout order `3 * rank + phase` (used directly by `unionRanges` and as
the second component of `visitOrder`). -/
def layoutOrder (typeRank : Miri.MIR.TyId → Nat) (place : LocalLayout) : Nat :=
  3 * typeRank place.ty + layoutPhase place

/-- `lean-miri#90`'s lexicographic place order `(if isSized then 0 else 1, layoutOrder)` used by
`visit`: dynamic `dyn Trait` unpacking transitions from an unsized place (`1`) to a concrete sized
place (`0`), descending on the first component even when the concrete implementor's static
`typeRank` exceeds the trait object's rank. -/
def visitOrder (typeRank : Miri.MIR.TyId → Nat) (place : LocalLayout) : Nat × Nat :=
  (if place.layout.isSized then 0 else 1, layoutOrder typeRank place)

/-- Strict lexicographic order `Prod.Lex (· < ·) (· < ·)` on `visitOrder` pairs (`ω · 2`). -/
abbrev VisitOrderLt (a b : Nat × Nat) : Prop :=
  Prod.Lex (· < ·) (· < ·) a b

instance instDecidableVisitOrderLt (a b : Nat × Nat) : Decidable (VisitOrderLt a b) :=
  decidable_of_iff (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2))
    ⟨fun h => by
      rcases h with h1 | ⟨heq, h2⟩
      · exact Prod.Lex.left _ _ h1
      · cases a; cases b; dsimp at heq h2; subst heq; exact Prod.Lex.right _ h2,
     fun h => by
      cases h with
      | left _ _ h1 => exact Or.inl h1
      | right _ h2 => exact Or.inr ⟨rfl, h2⟩⟩

theorem layoutPhase_le_two (place : LocalLayout) : layoutPhase place ≤ 2 := by
  unfold layoutPhase
  split <;> omega

theorem layoutPhase_of_multiple (place : LocalLayout)
    (h : ∃ tag enc field vs, place.layout.variants = .Multiple tag enc field vs) :
    layoutPhase place = 2 := by
  obtain ⟨tag, enc, field, vs, hv⟩ := h
  simp [layoutPhase, hv]

theorem layoutPhase_le_one (place : LocalLayout)
    (h : ∀ tag enc field vs, place.layout.variants ≠ .Multiple tag enc field vs) :
    layoutPhase place ≤ 1 := by
  unfold layoutPhase
  cases hv : place.layout.variants with
  | Multiple tag enc field vs => exact absurd hv (h tag enc field vs)
  | Empty => cases place.layout.fields <;> simp
  | Single _ => cases place.layout.fields <;> simp

theorem layoutPhase_of_primitive (place : LocalLayout) (hf : place.layout.fields = .Primitive)
    (h : ∀ tag enc field vs, place.layout.variants ≠ .Multiple tag enc field vs) :
    layoutPhase place = 0 := by
  unfold layoutPhase
  cases hv : place.layout.variants with
  | Multiple tag enc field vs => exact absurd hv (h tag enc field vs)
  | Empty => simp [hf]
  | Single _ => simp [hf]

theorem layoutPhase_pos_of_not_primitive (place : LocalLayout)
    (hf : place.layout.fields ≠ .Primitive) : 1 ≤ layoutPhase place := by
  unfold layoutPhase
  cases hv : place.layout.variants with
  | Multiple _ _ _ _ => simp
  | Empty => cases hfs : place.layout.fields <;> simp_all
  | Single _ => cases hfs : place.layout.fields <;> simp_all

/-- A child of strictly smaller Schema 17 rank always descends in `layoutOrder`, whatever the
phases. -/
theorem layoutOrder_lt_of_rank_lt (typeRank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (h : typeRank child.ty < typeRank parent.ty) :
    layoutOrder typeRank child < layoutOrder typeRank parent := by
  have := layoutPhase_le_two child
  unfold layoutOrder
  omega

/-- A selected variant sharing the parent's type id descends from a multi-variant parent. -/
theorem layoutOrder_variant_lt (typeRank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (hty : child.ty = parent.ty)
    (hparent : ∃ tag enc field vs, parent.layout.variants = .Multiple tag enc field vs)
    (hchild : ∀ tag enc field vs, child.layout.variants ≠ .Multiple tag enc field vs) :
    layoutOrder typeRank child < layoutOrder typeRank parent := by
  have h1 := layoutPhase_of_multiple parent hparent
  have h2 := layoutPhase_le_one child hchild
  unfold layoutOrder
  rw [hty]
  omega

/-- A synthetic primitive field sharing the parent's type id descends from a non-primitive,
single-variant aggregate parent. -/
theorem layoutOrder_primitive_lt (typeRank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (hty : child.ty = parent.ty) (hfields : child.layout.fields = .Primitive)
    (hchild : ∀ tag enc field vs, child.layout.variants ≠ .Multiple tag enc field vs)
    (hparentFields : parent.layout.fields ≠ .Primitive) :
    layoutOrder typeRank child < layoutOrder typeRank parent := by
  have h1 := layoutPhase_of_primitive child hfields hchild
  have h2 := layoutPhase_pos_of_not_primitive parent hparentFields
  unfold layoutOrder
  rw [hty]
  omega

/-- Within the same sizedness phase (`child.layout.isSized = parent.layout.isSized`), any
`layoutOrder` decrease lifts to `visitOrder` descent (`Prod.Lex.right`). -/
theorem visitOrder_lt_of_same_sized (typeRank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (hsized : child.layout.isSized = parent.layout.isSized)
    (hlt : layoutOrder typeRank child < layoutOrder typeRank parent) :
    VisitOrderLt (visitOrder typeRank child) (visitOrder typeRank parent) := by
  unfold visitOrder
  rw [hsized]
  exact Prod.Lex.right _ hlt

/-- Dynamic unpacking (`lean-miri#90` `VTable.unpackDynTrait`) from an unsized trait object
(`parent.layout.isSized = false`) to a concrete sized layout (`child.layout.isSized = true`)
always descends in `visitOrder` (`Prod.Lex.left`), regardless of how large `typeRank child.ty` is. -/
theorem visitOrder_lt_of_unsized_unpack (typeRank : Miri.MIR.TyId → Nat) (parent child : LocalLayout)
    (hdynamic : parent.layout.isSized = false) (hconcrete : child.layout.isSized = true) :
    VisitOrderLt (visitOrder typeRank child) (visitOrder typeRank parent) := by
  unfold visitOrder
  rw [hdynamic, hconcrete]
  exact Prod.Lex.left _ _ (by decide)

/-! ## 2. Rank certificates over layout graphs and Schema 17 decoder tables -/

/-- A Schema 17 rank certificate: the `validation_rank` recorded for each compiler `TypeNode`
(types absent from the table default to rank `0`, as `RuntimeArrayTypes.typeRank` does). -/
structure ValidationRankCert where
  ranks : List (Miri.MIR.TyId × Nat)
  deriving Repr

namespace ValidationRankCert

/-- The rank map `tyRank` of a certificate. -/
def tyRank (cert : ValidationRankCert) (ty : Miri.MIR.TyId) : Nat :=
  ((cert.ranks.find? (·.1 == ty)).map (·.2)).getD 0

/-- Upper bound on `tyRank` across all entries in the certificate table. -/
def maxRank (cert : ValidationRankCert) : Nat :=
  cert.ranks.foldl (fun acc entry => Nat.max acc entry.2) 0

theorem tyRank_le_maxRank (cert : ValidationRankCert) (ty : Miri.MIR.TyId) :
    cert.tyRank ty ≤ cert.maxRank := by
  unfold tyRank maxRank
  have haux : ∀ (rs : List (Miri.MIR.TyId × Nat)) (acc : Nat),
      ((rs.find? (·.1 == ty)).map (·.2)).getD 0 ≤
        rs.foldl (fun a entry => Nat.max a entry.2) acc := by
    intro rs
    induction rs with
    | nil => intro acc; simp
    | cons hd tl ih =>
      intro acc
      simp only [List.find?_cons, List.foldl_cons]
      cases hd.1 == ty
      · exact ih (Nat.max acc hd.2)
      · simp only [Option.map_some, Option.getD_some]
        have hmono : ∀ (l : List (Miri.MIR.TyId × Nat)) (a : Nat),
            a ≤ l.foldl (fun m e => Nat.max m e.2) a := by
          intro l
          induction l with
          | nil => intro a; exact Nat.le_refl a
          | cons e es ihl =>
            intro a
            exact Nat.le_trans (Nat.le_max_left a e.2) (ihl (Nat.max a e.2))
        exact Nat.le_trans (Nat.le_max_right acc hd.2) (hmono tl (Nat.max acc hd.2))
  exact haux cert.ranks 0

end ValidationRankCert

/-- A finite compiler-layout graph: each node's composite children (struct/tuple fields,
array/slice elements, and enum/coroutine/union variants), as returned by the compiler layout
projections `field` / `variant`. -/
structure LayoutGraph where
  nodes : List LocalLayout
  children : LocalLayout → List LocalLayout

/-- Executable closure check: the children of every node are present in `g.nodes`. -/
def LayoutGraph.closed (g : LayoutGraph) : Bool :=
  g.nodes.all fun p => (g.children p).all fun c => g.nodes.contains c

/-- Executable Schema 17 layout-graph certificate check: every child of every node belongs to
`g.nodes` (mirroring `Decoder.lean`'s `"missing validation child"` check so omitted nodes cannot
hide cycles) and strictly descends in `layoutOrder cert.tyRank`. -/
def checkCert (cert : ValidationRankCert) (g : LayoutGraph) : Bool :=
  g.nodes.all fun p => (g.children p).all fun c =>
    g.nodes.contains c && decide (layoutOrder cert.tyRank c < layoutOrder cert.tyRank p)

/-- Soundness of `checkCert`: every edge from `g.nodes` lands in `g.nodes` and strictly decreases
`layoutOrder cert.tyRank`. -/
theorem checkCert_sound (cert : ValidationRankCert) (g : LayoutGraph)
    (h : checkCert cert g = true) :
    ∀ p ∈ g.nodes, ∀ c ∈ g.children p,
      c ∈ g.nodes ∧ layoutOrder cert.tyRank c < layoutOrder cert.tyRank p := by
  intro p hp c hc
  simp only [checkCert, List.all_eq_true, Bool.and_eq_true, List.contains_iff_mem,
    decide_eq_true_eq] at h
  exact h p hp c hc

/-- A valid `checkCert` implies `g.closed = true`. -/
theorem checkCert_closed (cert : ValidationRankCert) (g : LayoutGraph)
    (h : checkCert cert g = true) : g.closed = true := by
  simp only [LayoutGraph.closed, List.all_eq_true, List.contains_iff_mem]
  intro p hp c hc
  exact (checkCert_sound cert g h p hp c hc).1

theorem LayoutGraph.closed_sound (g : LayoutGraph) (h : g.closed = true) :
    ∀ p ∈ g.nodes, ∀ c ∈ g.children p, c ∈ g.nodes := by
  intro p hp c hc
  simp only [LayoutGraph.closed, List.all_eq_true, List.contains_iff_mem] at h
  exact h p hp c hc

/-- Reachability through the graph's child edges (transitive closure). -/
inductive Reach (g : LayoutGraph) : LocalLayout → LocalLayout → Prop
  | edge {p c : LocalLayout} : p ∈ g.nodes → c ∈ g.children p → Reach g p c
  | trans {p q r : LocalLayout} : Reach g p q → Reach g q r → Reach g p r

/-- Under a valid certificate every reachable layout is in `g.nodes` and strictly smaller in
`layoutOrder cert.tyRank`. -/
theorem checkCert_reach_descends (cert : ValidationRankCert) (g : LayoutGraph)
    (h : checkCert cert g = true) {p q : LocalLayout} (hr : Reach g p q) :
    layoutOrder cert.tyRank q < layoutOrder cert.tyRank p := by
  induction hr with
  | edge hp hc => exact (checkCert_sound cert g h _ hp _ hc).2
  | trans _ _ ih₁ ih₂ => omega

/-- A valid certificate excludes cycles. -/
theorem checkCert_acyclic (cert : ValidationRankCert) (g : LayoutGraph)
    (h : checkCert cert g = true) (p : LocalLayout) : ¬ Reach g p p := fun hr =>
  Nat.lt_irrefl _ (checkCert_reach_descends cert g h hr)

/-- Cyclic layout graphs are rejected by `checkCert` for every rank table. -/
theorem checkCert_rejects_cycle (cert : ValidationRankCert) (g : LayoutGraph) (p : LocalLayout)
    (hr : Reach g p p) : checkCert cert g = false := by
  cases hc : checkCert cert g with
  | false => rfl
  | true => exact absurd hr (checkCert_acyclic cert g hc p)

/-! ### Schema 17 compiler type-table checker (`lean-miri#90` `Miri/Input/Decoder.lean`) -/

/-- Schema 17 compiler type shapes (`proofs-rs/lean-miri#90` `Decoder.lean` L56–80).
Pointer indirections (`&T`, `&mut T`, `*const T`, `*mut T`, `fn(...)`) carry *no* static by-value
rank edge because pointee validation is decoupled via `RefTracking` LIFO draining, allowing
recursive pointer types such as `struct List { next: Option<&List> }` to pass Schema 17 checks. -/
inductive Schema17Shape where
  | primitive
  | pointerIndirection (pointee : Miri.MIR.TyId)
  | adt (variants : List (List Miri.MIR.TyId))
  | array (element : Miri.MIR.TyId)
  | slice (element : Miri.MIR.TyId)
  | patternType (base : Miri.MIR.TyId)
  | unsafeBinder (base : Miri.MIR.TyId)
  | tuple (elements : List Miri.MIR.TyId)
  | closure (upvars : List Miri.MIR.TyId)
  | coroutine (prefixTypes : List Miri.MIR.TyId) (savedTypes : Array Miri.MIR.TyId)
      (variants : List (List Nat))
  deriving Repr, DecidableEq

/-- A Schema 17 `TypeNode` entry with `validationRank` and optional `normalizedType` alias. -/
structure Schema17TypeNode where
  id : Miri.MIR.TyId
  validationRank : Nat
  normalizedType : Miri.MIR.TyId := id
  shape : Schema17Shape
  deriving Repr, DecidableEq

/-- Resolve coroutine saved-local indices into child `TyId`s (`Decoder.lean` L76–79). -/
def resolveCoroutineSaved (savedTypes : Array Miri.MIR.TyId) :
    List Nat → Except String (List Miri.MIR.TyId)
  | [] => .ok []
  | field :: rest =>
    match savedTypes[field]? with
    | none => .error "missing coroutine saved type"
    | some child => do
      let tail ← resolveCoroutineSaved savedTypes rest
      return child :: tail

/-- Direct by-value child `TyId`s checked by `Decoder.validateParsedDocument` (`lean-miri#90`). -/
def schema17ByValueChildren (node : Schema17TypeNode) : Except String (List Miri.MIR.TyId) :=
  if node.normalizedType != node.id then
    .ok [node.normalizedType]
  else
    match node.shape with
    | .primitive | .pointerIndirection _ => .ok []
    | .adt variants => .ok variants.flatten
    | .array el | .slice el | .patternType el | .unsafeBinder el => .ok [el]
    | .tuple els | .closure els => .ok els
    | .coroutine pfx saved variants => do
      let savedChildren ← resolveCoroutineSaved saved variants.flatten
      return pfx ++ savedChildren

/-- Extract the `ValidationRankCert` table from a Schema 17 `TypeNode` list. -/
def Schema17TypeNode.toCert (nodes : List Schema17TypeNode) : ValidationRankCert :=
  ⟨nodes.map fun n => (n.id, n.validationRank)⟩

/-- Executable Schema 17 table validator mirroring `lean-miri#90` `Decoder.lean` L56–80:
verifies coroutine saved-type indices, rejects missing child `TyId`s, and enforces strict
`source.validationRank < node.validationRank` across all composite/alias by-value edges. -/
def checkSchema17Table (nodes : List Schema17TypeNode) : Except String Unit := do
  let checkNode (node : Schema17TypeNode) : Except String Unit := do
    let children ← schema17ByValueChildren node
    children.forM fun childId => do
      let some source := nodes.find? (·.id == childId)
        | throw s!"missing validation child {childId}"
      if source.validationRank < node.validationRank then
        pure ()
      else
        throw s!"validation rank does not decrease from type {node.id} to {childId}"
  nodes.forM checkNode

private theorem list_forM_ok_iff {α : Type} (f : α → Except String Unit) (xs : List α) :
    xs.forM f = .ok () ↔ ∀ x ∈ xs, f x = .ok () := by
  induction xs with
  | nil => simp [List.forM_nil, pure, Except.pure]
  | cons x xs ih =>
    change (f x >>= fun _ => xs.forM f) = .ok () ↔ _
    cases hx : f x with
    | error e =>
      simp only [bind, Except.bind, reduceCtorEq, false_iff, List.mem_cons]
      intro hall
      have := hall x (Or.inl rfl)
      rw [hx] at this
      cases this
    | ok u =>
      simp only [bind, Except.bind, ih, List.mem_cons, forall_eq_or_imp, hx, true_and]

/-- Soundness of `checkSchema17Table`: every node's by-value child list resolves cleanly and every
referenced child exists in `nodes` with strictly smaller `validationRank`. -/
theorem checkSchema17Table_sound (nodes : List Schema17TypeNode)
    (h : checkSchema17Table nodes = .ok ()) :
    ∀ node ∈ nodes, ∃ children,
      schema17ByValueChildren node = .ok children ∧
      ∀ childId ∈ children, ∃ source,
        nodes.find? (·.id == childId) = some source ∧
        source.validationRank < node.validationRank := by
  unfold checkSchema17Table at h
  rw [list_forM_ok_iff] at h
  intro node hnode
  have hn := h node hnode
  cases hch : schema17ByValueChildren node with
  | error e => simp [hch, bind, Except.bind] at hn
  | ok children =>
    refine ⟨children, rfl, ?_⟩
    simp only [hch, bind, Except.bind, list_forM_ok_iff] at hn
    intro childId hc
    have hci := hn childId hc
    cases hfind : nodes.find? (·.id == childId) with
    | none => simp [hfind, throw] at hci
    | some source =>
      refine ⟨source, rfl, ?_⟩
      by_cases hlt : source.validationRank < node.validationRank
      · exact hlt
      · simp [hfind, hlt, throw] at hci

/-- Transitive by-value dependency relation across a Schema 17 type table. -/
inductive Schema17Reach (nodes : List Schema17TypeNode) :
    Schema17TypeNode → Schema17TypeNode → Prop
  | edge {p c : Schema17TypeNode} {children : List Miri.MIR.TyId} {childId : Miri.MIR.TyId} :
      p ∈ nodes →
      schema17ByValueChildren p = .ok children →
      childId ∈ children →
      nodes.find? (·.id == childId) = some c →
      Schema17Reach nodes p c
  | trans {p q r : Schema17TypeNode} :
      Schema17Reach nodes p q → Schema17Reach nodes q r → Schema17Reach nodes p r

theorem checkSchema17Table_reach_descends (nodes : List Schema17TypeNode)
    (h : checkSchema17Table nodes = .ok ()) {p q : Schema17TypeNode}
    (hr : Schema17Reach nodes p q) : q.validationRank < p.validationRank := by
  induction hr with
  | edge hp hch hmem hfind =>
    obtain ⟨children', hch', hall⟩ := checkSchema17Table_sound nodes h _ hp
    rw [hch] at hch'; injection hch' with hce; subst hce
    obtain ⟨src, hfind', hlt⟩ := hall _ hmem
    rw [hfind] at hfind'; injection hfind' with hse; subst hse
    exact hlt
  | trans _ _ ih₁ ih₂ => omega

/-- Any Schema 17 type table accepted by `checkSchema17Table` has an acyclic by-value graph
(even when `.pointerIndirection` edges form cycles through references or boxes). -/
theorem checkSchema17Table_acyclic (nodes : List Schema17TypeNode)
    (h : checkSchema17Table nodes = .ok ()) (p : Schema17TypeNode) :
    ¬ Schema17Reach nodes p p := fun hr =>
  Nat.lt_irrefl _ (checkSchema17Table_reach_descends nodes h hr)

/-! ## 3. Rank-guarded traversals (`RankedWalk`, `VisitLexWalk`, real `unionRanges`, `drainPointees`) -/

/-- A `layoutOrder`-guarded traversal over effectful projection hooks in the real validity monad
`ValidityVisitor.M S = EStateM StepError S`. -/
structure RankedWalk (S Pl α : Type) where
  typeRank : Miri.MIR.TyId → Nat
  layoutOf : Pl → LocalLayout
  pre : Pl → α → M S α
  children : Pl → M S (Array Pl)
  descendMsg : String := "validity projection does not descend"
  fuelMsg : String := "validity traversal fuel"

namespace RankedWalk

variable {S Pl α : Type} (h : RankedWalk S Pl α)

/-- The `layoutOrder` of a place. -/
def order (p : Pl) : Nat := layoutOrder h.typeRank (h.layoutOf p)

/-- Fuel-free well-founded traversal (`lean-miri#90` `layoutOrder`): recursion is justified by the
dynamic descent guard at every projection hook result. -/
def walkNoFuel (p : Pl) (acc : α) : M S α := do
  let acc ← h.pre p acc
  let cs ← h.children p
  cs.toList.foldlM (fun acc c =>
    if _smaller : h.order c < h.order p then walkNoFuel c acc
    else throw (.invalidProgram h.descendMsg)) acc
termination_by h.order p

/-- Bounded-fuel traversal with the same dynamic descent guard (structural on fuel). -/
def walkGuarded : Nat → Pl → α → M S α
  | 0, _, _ => throw (.resourceExhaustion h.fuelMsg)
  | n + 1, p, acc => do
    let acc ← h.pre p acc
    let cs ← h.children p
    cs.toList.foldlM (fun acc c =>
      if h.order c < h.order p then walkGuarded n c acc
      else throw (.invalidProgram h.descendMsg)) acc

/-- Unguarded bounded-fuel traversal: no descent guard, exhaustion at fuel `0`. -/
def walkFuel : Nat → Pl → α → M S α
  | 0, _, _ => throw (.resourceExhaustion h.fuelMsg)
  | n + 1, p, acc => do
    let acc ← h.pre p acc
    let cs ← h.children p
    cs.toList.foldlM (fun acc c => walkFuel n c acc) acc

/-- The structural (`Nat.rec`, `Classical.choice`-free) rank-fuelled companion at canonical static
fuel `order p + 1`. -/
def walkRank (p : Pl) (acc : α) : M S α := h.walkGuarded (h.order p + 1) p acc

/-- The hooks honour the rank certificate on `Good` places: every child they return is `Good` and
strictly descends in `layoutOrder`. -/
def DescendsOn (Good : Pl → Prop) : Prop :=
  ∀ p, Good p → ∀ (s : S) (cs : Array Pl) (s' : S), h.children p s = .ok cs s' →
    ∀ c ∈ cs.toList, Good c ∧ h.order c < h.order p

private theorem foldlM_congr_mem {β γ : Type} (l : List γ) (f g : β → γ → M S β)
    (hfg : ∀ c ∈ l, ∀ b, f b c = g b c) (b : β) : l.foldlM f b = l.foldlM g b := by
  induction l generalizing b with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldlM_cons]
    rw [hfg c (List.mem_cons_self ..) b]
    congr 1
    funext b'
    exact ih (fun c' hc' b'' => hfg c' (List.mem_cons_of_mem _ hc') b'') b'

/-- Any fuel above `order root` makes the guarded traversal agree with `walkNoFuel`. -/
theorem walkGuarded_eq_walkNoFuel :
    ∀ (n : Nat) (p : Pl) (acc : α), h.order p < n → h.walkGuarded n p acc = h.walkNoFuel p acc
  | 0, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | n + 1, p, acc, hlt => by
    rw [walkNoFuel]
    simp only [walkGuarded]
    have hfun : (fun acc c =>
        if h.order c < h.order p then h.walkGuarded n c acc
        else (throw (.invalidProgram h.descendMsg) : M S α)) =
      (fun acc c =>
        if _smaller : h.order c < h.order p then h.walkNoFuel c acc
        else throw (.invalidProgram h.descendMsg)) := by
      funext acc c
      by_cases hc : h.order c < h.order p
      · simp only [hc, ↓reduceIte, ↓reduceDIte]
        exact walkGuarded_eq_walkNoFuel n c acc (by omega)
      · simp only [hc, ↓reduceIte, ↓reduceDIte]
    rw [hfun]

/-- The structural companion equals `walkNoFuel` unconditionally. -/
theorem walkRank_eq_walkNoFuel (p : Pl) (acc : α) : h.walkRank p acc = h.walkNoFuel p acc :=
  h.walkGuarded_eq_walkNoFuel _ p acc (Nat.lt_succ_self _)

theorem walkRank_eq_walkNoFuel' : h.walkRank = h.walkNoFuel := by
  funext p acc
  exact h.walkRank_eq_walkNoFuel p acc

/-- Under `DescendsOn`, the dynamic guard never fires: `walkFuel` equals `walkGuarded` at every
fuel. -/
theorem walkFuel_eq_walkGuarded (Good : Pl → Prop) (hd : h.DescendsOn Good) :
    ∀ (n : Nat) (p : Pl) (acc : α), Good p → h.walkFuel n p acc = h.walkGuarded n p acc
  | 0, _, _, _ => rfl
  | n + 1, p, acc, hp => by
    funext s
    simp only [walkFuel, walkGuarded, bind, EStateM.bind]
    cases hpre : h.pre p acc s with
    | error e s₁ => rfl
    | ok acc₁ s₁ =>
      dsimp only
      cases hch : h.children p s₁ with
      | error e s₂ => rfl
      | ok cs s₂ =>
        dsimp only
        have hcs := hd p hp s₁ cs s₂ hch
        rw [foldlM_congr_mem cs.toList (fun b c => h.walkFuel n c b)
          (fun b c => if h.order c < h.order p then h.walkGuarded n c b
            else throw (.invalidProgram h.descendMsg))
          (fun c hc b => by
            obtain ⟨hgood, hlt⟩ := hcs c hc
            simp only [hlt, ↓reduceIte]
            exact walkFuel_eq_walkGuarded Good hd n c b hgood) acc₁]

/-- **Adequacy.** For hooks satisfying the rank certificate, bounded-fuel validation agrees
identically with `walkNoFuel` whenever `fuel > order root`. -/
theorem walkFuel_eq_walkNoFuel (Good : Pl → Prop) (hd : h.DescendsOn Good) (n : Nat) (p : Pl)
    (acc : α) (hp : Good p) (hlt : h.order p < n) : h.walkFuel n p acc = h.walkNoFuel p acc :=
  (h.walkFuel_eq_walkGuarded Good hd n p acc hp).trans (h.walkGuarded_eq_walkNoFuel n p acc hlt)

/-- The canonical static fuel `order root + 1` suffices. -/
theorem walkFuel_rank_succ (Good : Pl → Prop) (hd : h.DescendsOn Good) (p : Pl) (acc : α)
    (hp : Good p) : h.walkFuel (h.order p + 1) p acc = h.walkNoFuel p acc :=
  h.walkFuel_eq_walkNoFuel Good hd _ p acc hp (Nat.lt_succ_self _)

/-- **Deterministic rejection.** If a projection hook returns a first child that does not descend,
`walkNoFuel` fails immediately with `.invalidProgram`. -/
theorem walkNoFuel_rejects_nondescending (p : Pl) (acc acc₁ : α) (c : Pl) (rest : List Pl)
    (s s₁ s₂ : S) (cs : Array Pl)
    (hpre : h.pre p acc s = .ok acc₁ s₁) (hch : h.children p s₁ = .ok cs s₂)
    (hcs : cs.toList = c :: rest) (hbad : ¬ h.order c < h.order p) :
    h.walkNoFuel p acc s = .error (.invalidProgram h.descendMsg) s₂ := by
  rw [walkNoFuel]
  simp only [bind, EStateM.bind, hpre, hch, hcs, List.foldlM_cons, hbad, ↓reduceDIte]
  rfl

end RankedWalk

/-! ### Lexicographic `visitOrder` traversal (`VisitLexWalk`, `ω · 2` dynamic `dyn Trait` unpack) -/

/-- Lexicographic `visitOrder`-guarded traversal (`lean-miri#90` `ValidityVisitor.visit`):
supports both within-phase `layoutOrder` descent and unsized-to-sized dynamic unpacking
(`isSized = false → true`) to arbitrary higher-rank concrete implementors. -/
structure VisitLexWalk (S Pl α : Type) where
  typeRank : Miri.MIR.TyId → Nat
  layoutOf : Pl → LocalLayout
  pre : Pl → α → M S α
  children : Pl → M S (Array Pl)
  descendMsg : String := "validity projection does not descend"
  fuelMsg : String := "validity traversal fuel"

namespace VisitLexWalk

variable {S Pl α : Type} (h : VisitLexWalk S Pl α)

def vOrder (p : Pl) : Nat × Nat := visitOrder h.typeRank (h.layoutOf p)
def lOrder (p : Pl) : Nat := layoutOrder h.typeRank (h.layoutOf p)
def isSized (p : Pl) : Bool := (h.layoutOf p).layout.isSized

/-- Fuel-free `visitOrder` traversal via well-founded `Prod.Lex` recursion (`lean-miri#90`). -/
def walkNoFuel (p : Pl) (acc : α) : M S α := do
  let acc ← h.pre p acc
  let cs ← h.children p
  cs.toList.foldlM (fun acc c =>
    if _smaller : VisitOrderLt (h.vOrder c) (h.vOrder p) then walkNoFuel c acc
    else throw (.invalidProgram h.descendMsg)) acc
termination_by h.vOrder p
decreasing_by exact _smaller

/-- Phase-0 (`isSized = true`) structural companion (`Nat.rec`, `Classical.choice`-free). -/
def walkSized : Nat → Pl → α → M S α
  | 0, _, _ => throw (.resourceExhaustion h.fuelMsg)
  | n + 1, p, acc => do
    let acc ← h.pre p acc
    let cs ← h.children p
    cs.toList.foldlM (fun acc c =>
      if h.isSized c && decide (h.lOrder c < h.lOrder p) then walkSized n c acc
      else throw (.invalidProgram h.descendMsg)) acc

/-- Phase-1 (`isSized = false`) structural companion (`Nat.rec`, `Classical.choice`-free):
when a dynamic unpack transitions to a sized child `c`, enters `walkSized` with fresh budget
`lOrder c + 1` computed on the fly! -/
def walkUnsized : Nat → Pl → α → M S α
  | 0, _, _ => throw (.resourceExhaustion h.fuelMsg)
  | n + 1, p, acc => do
    let acc ← h.pre p acc
    let cs ← h.children p
    cs.toList.foldlM (fun acc c =>
      if h.isSized c then h.walkSized (h.lOrder c + 1) c acc
      else if h.lOrder c < h.lOrder p then walkUnsized n c acc
      else throw (.invalidProgram h.descendMsg)) acc

/-- `Classical.choice`-free `ω · 2` (`Nat.rec × Nat.rec`) structural realization of
`VisitLexWalk.walkNoFuel`, requiring no upper bound on `typeRank`. -/
def walkRank (p : Pl) (acc : α) : M S α :=
  if h.isSized p then h.walkSized (h.lOrder p + 1) p acc
  else h.walkUnsized (h.lOrder p + 1) p acc

/-- Unguarded bounded-fuel traversal over the same hooks. -/
def walkFuel : Nat → Pl → α → M S α
  | 0, _, _ => throw (.resourceExhaustion h.fuelMsg)
  | n + 1, p, acc => do
    let acc ← h.pre p acc
    let cs ← h.children p
    cs.toList.foldlM (fun acc c => walkFuel n c acc) acc

theorem vOrder_lt_of_sized {p c : Pl} (hp : h.isSized p = true) :
    VisitOrderLt (h.vOrder c) (h.vOrder p) ↔ (h.isSized c = true ∧ h.lOrder c < h.lOrder p) := by
  unfold vOrder visitOrder isSized lOrder at *
  cases hc : (h.layoutOf c).layout.isSized
  · rw [hp]
    simp only [Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
    intro hlex
    cases hlex with
    | left _ _ h1 => omega
  · rw [hp]
    simp only [↓reduceIte, true_and]
    constructor
    · intro hlex
      cases hlex with
      | left _ _ h1 => omega
      | right _ h2 => exact h2
    · exact Prod.Lex.right _

theorem walkSized_eq_walkNoFuel :
    ∀ (n : Nat) (p : Pl) (acc : α), h.isSized p = true → h.lOrder p < n →
      h.walkSized n p acc = h.walkNoFuel p acc
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | n + 1, p, acc, hp, hlt => by
    rw [walkNoFuel.eq_1]
    simp only [walkSized]
    congr 1; funext acc₁; congr 1; funext cs
    have hfun : (fun acc c =>
        if (h.isSized c && decide (h.lOrder c < h.lOrder p)) = true then h.walkSized n c acc
        else (throw (.invalidProgram h.descendMsg) : M S α)) =
      (fun acc c =>
        if _smaller : VisitOrderLt (h.vOrder c) (h.vOrder p) then h.walkNoFuel c acc
        else throw (.invalidProgram h.descendMsg)) := by
      funext acc c
      by_cases hlt_lex : VisitOrderLt (h.vOrder c) (h.vOrder p)
      · obtain ⟨hc_sz, hc_lt⟩ := (h.vOrder_lt_of_sized hp).mp hlt_lex
        have hcond : (h.isSized c && decide (h.lOrder c < h.lOrder p)) = true := by
          simp [hc_sz, hc_lt]
        simp only [hcond, hlt_lex, ↓reduceIte, ↓reduceDIte]
        exact walkSized_eq_walkNoFuel n c acc hc_sz (by omega)
      · have hcond : (h.isSized c && decide (h.lOrder c < h.lOrder p)) = false := by
          cases hb : (h.isSized c && decide (h.lOrder c < h.lOrder p))
          · rfl
          · simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
            exact absurd ((h.vOrder_lt_of_sized hp).mpr hb) hlt_lex
        simp only [hcond, hlt_lex, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]
    exact congrArg (cs.toList.foldlM · acc₁) hfun

theorem walkUnsized_eq_walkNoFuel :
    ∀ (n : Nat) (p : Pl) (acc : α), h.isSized p = false → h.lOrder p < n →
      h.walkUnsized n p acc = h.walkNoFuel p acc
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | n + 1, p, acc, hp, hlt => by
    rw [walkNoFuel.eq_1]
    simp only [walkUnsized]
    congr 1; funext acc₁; congr 1; funext cs
    have hfun : (fun acc c =>
        if h.isSized c = true then h.walkSized (h.lOrder c + 1) c acc
        else if h.lOrder c < h.lOrder p then h.walkUnsized n c acc
        else (throw (.invalidProgram h.descendMsg) : M S α)) =
      (fun acc c =>
        if _smaller : VisitOrderLt (h.vOrder c) (h.vOrder p) then h.walkNoFuel c acc
        else throw (.invalidProgram h.descendMsg)) := by
      funext acc c
      cases hc_sz : h.isSized c
      · have hiff : VisitOrderLt (h.vOrder c) (h.vOrder p) ↔ h.lOrder c < h.lOrder p := by
          unfold vOrder visitOrder isSized lOrder at *
          rw [hc_sz, hp]
          constructor
          · intro hlex
            cases hlex with
            | left _ _ h1 => omega
            | right _ h2 => exact h2
          · exact Prod.Lex.right _
        by_cases hc_lt : h.lOrder c < h.lOrder p
        · have hlex : VisitOrderLt (h.vOrder c) (h.vOrder p) := hiff.mpr hc_lt
          simp only [Bool.false_eq_true, ↓reduceIte, hc_lt, hlex, ↓reduceDIte]
          exact walkUnsized_eq_walkNoFuel n c acc hc_sz (by omega)
        · have hnlex : ¬ VisitOrderLt (h.vOrder c) (h.vOrder p) := fun hx => hc_lt (hiff.mp hx)
          simp only [Bool.false_eq_true, ↓reduceIte, hc_lt, hnlex, ↓reduceDIte]
      · have hlex : VisitOrderLt (h.vOrder c) (h.vOrder p) :=
          visitOrder_lt_of_unsized_unpack h.typeRank (h.layoutOf p) (h.layoutOf c) hp hc_sz
        simp only [↓reduceIte, hlex, ↓reduceDIte]
        exact h.walkSized_eq_walkNoFuel (h.lOrder c + 1) c acc hc_sz (Nat.lt_succ_self _)
    exact congrArg (cs.toList.foldlM · acc₁) hfun

/-- Unconditional extensional equality between the `Classical.choice`-free `ω · 2` structural
companion `walkRank` and the `Prod.Lex` well-founded `walkNoFuel`. -/
theorem walkRank_eq_walkNoFuel (p : Pl) (acc : α) : h.walkRank p acc = h.walkNoFuel p acc := by
  unfold walkRank
  cases hp : h.isSized p
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h.walkUnsized_eq_walkNoFuel (h.lOrder p + 1) p acc hp (Nat.lt_succ_self _)
  · simp only [↓reduceIte]
    exact h.walkSized_eq_walkNoFuel (h.lOrder p + 1) p acc hp (Nat.lt_succ_self _)

/-- Lexicographic descent certificate with upper bound `maxSizedOrder` on sized `layoutOrder`s
(for a finite `ValidationRankCert`, `maxSizedOrder := 3 * cert.maxRank + 2`). -/
def DescendsLexOn (Good : Pl → Prop) (maxSizedOrder : Nat) : Prop :=
  ∀ p, Good p → ∀ (s : S) (cs : Array Pl) (s' : S), h.children p s = .ok cs s' →
    ∀ c ∈ cs.toList,
      Good c ∧ VisitOrderLt (h.vOrder c) (h.vOrder p) ∧
        (h.isSized c = true → h.lOrder c ≤ maxSizedOrder)

/-- Static fuel upper bound for `VisitLexWalk`: `lOrder p` for sized places, and
`lOrder p + maxSizedOrder + 1` for unsized places (accounting for at most one unsized-to-sized
dynamic unpack followed by sized descent). -/
def effectiveOrder (maxSizedOrder : Nat) (p : Pl) : Nat :=
  if h.isSized p then h.lOrder p else h.lOrder p + maxSizedOrder + 1

private theorem foldlM_lex_congr {β γ : Type} (l : List γ) (f g : β → γ → M S β)
    (hfg : ∀ c ∈ l, ∀ b, f b c = g b c) (b : β) : l.foldlM f b = l.foldlM g b := by
  induction l generalizing b with
  | nil => rfl
  | cons c rest ih =>
    simp only [List.foldlM_cons]
    rw [hfg c (List.mem_cons_self ..) b]
    congr 1; funext b'
    exact ih (fun c' hc' b'' => hfg c' (List.mem_cons_of_mem _ hc') b'') b'

/-- **Lexicographic adequacy.** Under `DescendsLexOn Good maxSizedOrder`, bounded-fuel validation
agrees identically with `VisitLexWalk.walkNoFuel` whenever `fuel > effectiveOrder maxSizedOrder p`
— including across `dyn Trait` unsized-to-sized dynamic unpacking where `layoutOrder` increases! -/
theorem walkFuel_eq_walkNoFuel (Good : Pl → Prop) (maxSizedOrder : Nat)
    (hd : h.DescendsLexOn Good maxSizedOrder) :
    ∀ (fuel : Nat) (p : Pl) (acc : α), Good p → h.effectiveOrder maxSizedOrder p < fuel →
      h.walkFuel fuel p acc = h.walkNoFuel p acc
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, p, acc, hp, hlt => by
    funext s
    rw [walkNoFuel.eq_1]
    simp only [walkFuel, bind, EStateM.bind]
    cases hpre : h.pre p acc s with
    | error e s₁ => rfl
    | ok acc₁ s₁ =>
      dsimp only
      cases hch : h.children p s₁ with
      | error e s₂ => rfl
      | ok cs s₂ =>
        dsimp only
        have hcs := hd p hp s₁ cs s₂ hch
        rw [foldlM_lex_congr cs.toList (fun b c => h.walkFuel fuel c b)
          (fun b c => if _smaller : VisitOrderLt (h.vOrder c) (h.vOrder p) then h.walkNoFuel c b
            else throw (.invalidProgram h.descendMsg))
          (fun c hc b => by
            obtain ⟨hgood, hlex, hmax⟩ := hcs c hc
            simp only [hlex, ↓reduceDIte]
            have heff : h.effectiveOrder maxSizedOrder c < fuel := by
              unfold effectiveOrder at hlt ⊢
              cases hp_sz : h.isSized p
              · simp only [hp_sz, Bool.false_eq_true, ↓reduceIte] at hlt
                cases hc_sz : h.isSized c
                · simp only [Bool.false_eq_true, ↓reduceIte]
                  unfold vOrder visitOrder at hlex
                  unfold isSized at hc_sz hp_sz
                  rw [hc_sz, hp_sz] at hlex
                  cases hlex with
                  | left _ _ h1 => omega
                  | right _ h2 => change h.lOrder c < h.lOrder p at h2; omega
                · simp only [↓reduceIte]
                  have := hmax hc_sz
                  omega
              · simp only [hp_sz, ↓reduceIte] at hlt
                obtain ⟨hc_sz, hc_lt⟩ := (h.vOrder_lt_of_sized hp_sz).mp hlex
                simp only [hc_sz, ↓reduceIte]
                omega
            exact walkFuel_eq_walkNoFuel Good maxSizedOrder hd fuel c b hgood heff) acc₁]

/-- Deterministic `.invalidProgram` rejection on non-descending `visitOrder` child. -/
theorem walkNoFuel_rejects_nondescending (p : Pl) (acc acc₁ : α) (c : Pl) (rest : List Pl)
    (s s₁ s₂ : S) (cs : Array Pl)
    (hpre : h.pre p acc s = .ok acc₁ s₁) (hch : h.children p s₁ = .ok cs s₂)
    (hcs : cs.toList = c :: rest) (hbad : ¬ VisitOrderLt (h.vOrder c) (h.vOrder p)) :
    h.walkNoFuel p acc s = .error (.invalidProgram h.descendMsg) s₂ := by
  rw [walkNoFuel.eq_1]
  simp only [bind, EStateM.bind, hpre, hch, hcs, List.foldlM_cons, hbad, ↓reduceDIte]
  rfl

end VisitLexWalk

/-! ### `visitNoFuel`, `visitLexNoFuel`, real `ValidityVisitor.unionRanges`, and `drainPointees` -/

/-- `visit` over `layoutOrder` (`RankedWalk`). -/
abbrev VisitWalk (P S : Type) := RankedWalk S (RuntimePlace P) (Session P)

/-- Fuel-free by-value validity traversal (`RankedWalk` instance). -/
def visitNoFuel {P S : Type} (h : VisitWalk P S) (session : Session P) (place : RuntimePlace P) :
    M S (Session P) :=
  h.walkNoFuel place session

/-- Fuel-free `visitOrder` (`Prod.Lex`, `dyn Trait` unpacking) validity traversal over
`RuntimePlace P` and `Session P`. -/
def visitLexNoFuel {P S : Type} (h : VisitLexWalk S (RuntimePlace P) (Session P))
    (session : Session P) (place : RuntimePlace P) : M S (Session P) :=
  h.walkNoFuel place session

/-- `unionRanges`: data ranges accumulated over `(LocalLayout, Size)` pairs (`RankedWalk`). -/
abbrev UnionWalk (S : Type) := RankedWalk S (LocalLayout × Size) DataRangeSet

/-- Fuel-free union data-range walk (`RankedWalk` instance). -/
def unionRangesNoFuel {S : Type} (h : UnionWalk S) (layout : LocalLayout) (base : Size)
    (initial : DataRangeSet) : M S DataRangeSet :=
  h.walkNoFuel (layout, base) initial

private def liftResultU {S A : Type} (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def sizeResultU {S A : Type} (value : Except SizeError A) : M S A :=
  liftResultU (value.mapError fun error => .invalidProgram s!"validity size: {repr error}")
private def rangeResultU {S A : Type} (value : Except RangeSetError A) : M S A :=
  liftResultU (value.mapError fun error => .invalidProgram s!"validity range: {repr error}")

/-- Single-node body of `Miri.Interpreter.ValidityVisitor.unionRanges`, factored over its recursive
continuation `descend` so the vendored `unionRanges`, `realUnionRangesGuarded`, and
`realUnionRangesNoFuel` share definitionally identical per-node semantics. -/
def unionRangesStep {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C)
    (layout : LocalLayout) (base : Size) (initial : DataRangeSet)
    (descend : LocalLayout → Size → DataRangeSet → M S DataRangeSet) : M S DataRangeSet := do
  if layout.layout.isZst then return initial
  let mut ranges := initial
  match layout.layout.fields with
  | .Primitive => ranges ← rangeResultU (ranges.addRange base layout.layout.size)
  | .Union count =>
    for field in [:count] do
      ranges ← descend (← h.projection.field c layout field) base ranges
  | .Array stride count =>
    let element ← h.projection.field c layout 0
    if element.layout.backendRepr.isScalar then
      ranges ← rangeResultU (ranges.addRange base (← sizeResultU (element.layout.size.mul count)))
    else
      for index in [:count.toNat] do
        let offset ← sizeResultU (stride.mul (UInt64.ofNat index))
        ranges ← descend element (← sizeResultU (base.add offset)) ranges
  | .Arbitrary offsets _ =>
    for index in [:offsets.size] do
      let some offset := offsets[index]? | throw (.invalidProgram "union layout field offset")
      ranges ← descend (← h.projection.field c layout index) (← sizeResultU (base.add offset)) ranges
  if let .Multiple _ _ _ variants := layout.layout.variants then
    for variant in [:variants.size] do
      ranges ← descend (← h.projection.variant c layout variant) base ranges
  return ranges

/-- Fuel-free `ValidityVisitor.unionRanges` verbatim from `proofs-rs/lean-miri#90` over the real
vendored `ValidityVisitor.Hooks P S C E F A Pad`. -/
def realUnionRangesNoFuel {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (layout : LocalLayout) (base : Size) (initial : DataRangeSet) : M S DataRangeSet :=
  unionRangesStep h c layout base initial fun child offset ranges =>
    if _smaller : layoutOrder typeRank child < layoutOrder typeRank layout then
      realUnionRangesNoFuel h c typeRank child offset ranges
    else throw (.invalidProgram "union layout projection does not descend")
termination_by layoutOrder typeRank layout
decreasing_by exact _smaller

/-- Structural (`Nat.rec`, `Classical.choice`-free) guarded companion for `realUnionRangesNoFuel`. -/
def realUnionRangesGuarded {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat) :
    Nat → LocalLayout → Size → DataRangeSet → M S DataRangeSet
  | 0, _, _, _ => throw (.resourceExhaustion "union layout traversal fuel")
  | fuel + 1, layout, base, initial =>
    unionRangesStep h c layout base initial fun child offset ranges =>
      if layoutOrder typeRank child < layoutOrder typeRank layout then
        realUnionRangesGuarded h c typeRank fuel child offset ranges
      else throw (.invalidProgram "union layout projection does not descend")

/-- Canonical `Classical.choice`-free structural companion at `layoutOrder typeRank layout + 1`. -/
def realUnionRangesRank {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (layout : LocalLayout) (base : Size) (initial : DataRangeSet) : M S DataRangeSet :=
  realUnionRangesGuarded h c typeRank (layoutOrder typeRank layout + 1) layout base initial

theorem realUnionRangesGuarded_eq_noFuel {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat) :
    ∀ (fuel : Nat) (layout : LocalLayout) (base : Size) (initial : DataRangeSet),
      layoutOrder typeRank layout < fuel →
      realUnionRangesGuarded h c typeRank fuel layout base initial =
        realUnionRangesNoFuel h c typeRank layout base initial
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, layout, base, initial, hlt => by
    rw [realUnionRangesNoFuel.eq_1]
    simp only [realUnionRangesGuarded]
    congr 1
    funext child offset ranges
    by_cases hc : layoutOrder typeRank child < layoutOrder typeRank layout
    · simp only [hc, ↓reduceIte, ↓reduceDIte]
      exact realUnionRangesGuarded_eq_noFuel h c typeRank fuel child offset ranges (by omega)
    · simp only [hc, ↓reduceIte, ↓reduceDIte]

/-- Unconditional equality between structural `realUnionRangesRank` and `realUnionRangesNoFuel`. -/
theorem realUnionRangesRank_eq_noFuel {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (layout : LocalLayout) (base : Size) (initial : DataRangeSet) :
    realUnionRangesRank h c typeRank layout base initial =
      realUnionRangesNoFuel h c typeRank layout base initial :=
  realUnionRangesGuarded_eq_noFuel h c typeRank _ layout base initial (Nat.lt_succ_self _)

/-- Projection-hook rank-descent invariant for `ValidityVisitor.unionRanges` (checked only on
non-primitive aggregate field shapes and `.Multiple` variant layouts where `unionRanges` actually
invokes `projection.field` / `projection.variant`). -/
def UnionHooksDescend {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (Good : LocalLayout → Prop) : Prop :=
  ∀ layout, Good layout → layout.layout.isZst = false →
    (layout.layout.fields ≠ .Primitive →
      ∀ idx s child s', h.projection.field c layout idx s = .ok child s' →
        Good child ∧ layoutOrder typeRank child < layoutOrder typeRank layout) ∧
    ((∃ tag enc field vs, layout.layout.variants = .Multiple tag enc field vs) →
      ∀ v s child s', h.projection.variant c layout v s = .ok child s' →
        Good child ∧ layoutOrder typeRank child < layoutOrder typeRank layout)

private theorem forIn_range_congr {S β : Type} {n : Nat} {init : β}
    {f g : Nat → β → M S (ForInStep β)}
    (hfg : ∀ i b, f i b = g i b) :
    forIn [:n] init f = forIn [:n] init g := by
  have : f = g := by funext i b; exact hfg i b
  rw [this]

private theorem bind_congr_ok {S α β : Type} {m : M S α} {f g : α → M S β}
    (hfg : ∀ s a s', m s = .ok a s' → f a s' = g a s') :
    (m >>= f) = (m >>= g) := by
  funext s
  simp only [bind, EStateM.bind]
  cases hm : m s with
  | error e s' => rfl
  | ok a s' => exact hfg s a s' hm

private theorem bind_eq_bind {S α β : Type} {m₁ m₂ : M S α} {k₁ k₂ : α → M S β}
    (hm : m₁ = m₂) (hk : ∀ a, k₁ a = k₂ a) :
    (m₁ >>= k₁) = (m₂ >>= k₂) := by
  rw [hm]
  have : k₁ = k₂ := by funext a; exact hk a
  rw [this]

private theorem unionRangesStep_congr {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (Good : LocalLayout → Prop) (hd : UnionHooksDescend h c typeRank Good)
    (layout : LocalLayout) (hp : Good layout) (base : Size) (initial : DataRangeSet)
    (d₁ d₂ : LocalLayout → Size → DataRangeSet → M S DataRangeSet)
    (hd_eq : ∀ child offset ranges,
      Good child → layoutOrder typeRank child < layoutOrder typeRank layout →
      d₁ child offset ranges = d₂ child offset ranges) :
    unionRangesStep h c layout base initial d₁ =
      unionRangesStep h c layout base initial d₂ := by
  unfold unionRangesStep
  cases hz : layout.layout.isZst
  · simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨hfield, hvar⟩ := hd layout hp hz
    have hvar_congr : ∀ ranges : DataRangeSet,
        (match layout.layout.variants with
         | .Multiple _ _ _ variants => do
           let mut r := ranges
           for variant in [:variants.size] do
             r ← d₁ (← h.projection.variant c layout variant) base r
           pure r
         | _ => pure ranges : M S DataRangeSet) =
        (match layout.layout.variants with
         | .Multiple _ _ _ variants => do
           let mut r := ranges
           for variant in [:variants.size] do
             r ← d₂ (← h.projection.variant c layout variant) base r
           pure r
         | _ => pure ranges) := by
      intro ranges
      cases hvs : layout.layout.variants with
      | Empty => rfl
      | Single _ => rfl
      | Multiple tag enc field variants =>
        dsimp only
        apply bind_eq_bind
        · apply forIn_range_congr; intro variant r
          apply bind_congr_ok; intro s child s' hm
          obtain ⟨hg, hlt⟩ := hvar ⟨tag, enc, field, variants, hvs⟩ variant s child s' hm
          rw [hd_eq child base r hg hlt]
        · intro _; rfl
    cases hfs : layout.layout.fields with
    | Primitive =>
      dsimp only
      exact bind_eq_bind rfl hvar_congr
    | Union count =>
      dsimp only
      apply bind_eq_bind
      · apply forIn_range_congr; intro field r
        apply bind_congr_ok; intro s child s' hm
        obtain ⟨hg, hlt⟩ := hfield (by simp [hfs]) field s child s' hm
        rw [hd_eq child base r hg hlt]
      · exact hvar_congr
    | Array stride count =>
      dsimp only
      apply bind_congr_ok; intro s element s' hm
      obtain ⟨hg_el, hlt_el⟩ := hfield (by simp [hfs]) 0 s element s' hm
      cases element.layout.backendRepr.isScalar
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact congrFun (bind_eq_bind
          (forIn_range_congr fun index r => by simp only [hd_eq element _ _ hg_el hlt_el])
          hvar_congr) s'
      · simp only [↓reduceIte]
        exact congrFun (bind_eq_bind rfl fun _ => bind_eq_bind rfl hvar_congr) s'
    | Arbitrary offsets _ =>
      dsimp only
      apply bind_eq_bind
      · apply forIn_range_congr; intro index r
        cases offsets[index]? with
        | none => rfl
        | some offset =>
          dsimp only
          apply bind_congr_ok; intro s child s' hm
          obtain ⟨hg, hlt⟩ := hfield (by simp [hfs]) index s child s' hm
          simp only [hd_eq child _ _ hg hlt]
      · exact hvar_congr
  · simp only [↓reduceIte]

/-- Under `UnionHooksDescend`, the actual vendored `ValidityVisitor.unionRanges` equals
`realUnionRangesGuarded` at every fuel budget (including fuel exhaustion on small budgets). -/
theorem vendored_unionRanges_eq_guarded {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (Good : LocalLayout → Prop) (hd : UnionHooksDescend h c typeRank Good) :
    ∀ (fuel : Nat) (layout : LocalLayout) (base : Size) (initial : DataRangeSet),
      Good layout →
      ValidityVisitor.unionRanges h c fuel layout base initial =
        realUnionRangesGuarded h c typeRank fuel layout base initial
  | 0, _, _, _, _ => by rw [ValidityVisitor.unionRanges.eq_1]; rfl
  | fuel + 1, layout, base, initial, hp => by
    have hstep : ValidityVisitor.unionRanges h c (fuel + 1) layout base initial =
        unionRangesStep h c layout base initial (ValidityVisitor.unionRanges h c fuel) := by
      rw [ValidityVisitor.unionRanges.eq_2]; rfl
    rw [hstep]
    simp only [realUnionRangesGuarded]
    exact unionRangesStep_congr h c typeRank Good hd layout hp base initial _ _
      fun child offset ranges hg hlt => by
        simp only [hlt, ↓reduceIte]
        exact vendored_unionRanges_eq_guarded h c typeRank Good hd fuel child offset ranges hg

/-- **Real vendored `unionRanges` adequacy.** Whenever `UnionHooksDescend` holds and
`fuel > layoutOrder typeRank layout`, the unmodified vendored
`Miri.Interpreter.ValidityVisitor.unionRanges` agrees identically with `realUnionRangesNoFuel`. -/
theorem vendored_unionRanges_eq_noFuel {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (Good : LocalLayout → Prop) (hd : UnionHooksDescend h c typeRank Good)
    (fuel : Nat) (layout : LocalLayout) (base : Size) (initial : DataRangeSet)
    (hp : Good layout) (hfuel : layoutOrder typeRank layout < fuel) :
    ValidityVisitor.unionRanges h c fuel layout base initial =
      realUnionRangesNoFuel h c typeRank layout base initial :=
  (vendored_unionRanges_eq_guarded h c typeRank Good hd fuel layout base initial hp).trans
    (realUnionRangesGuarded_eq_noFuel h c typeRank fuel layout base initial hfuel)

/-- `lean-miri#90`'s pointee drain: the tracked pointees are visited in LIFO order
(`tracking.todo.reverse`), each under a fresh session with tracking disabled, so pointer cycles
never re-enter the by-value rank recursion; the loop is structural over the finite queue. -/
def drainPointees {P S : Type} (tracking : RefTracking (Key P) ValidationPath)
    (visitPointee : Key P → ValidationPath → M S Unit) : M S Unit :=
  tracking.todo.toList.reverse.forM fun entry => visitPointee entry.1 entry.2

/-- The fresh session used for a tracked pointee (`lean-miri#90`): no reset, `mayDangle`, no
CTFE mode, no further reference tracking, no data-byte tracking. -/
def pointeeSession {P : Type} (path : ValidationPath) : Session P :=
  { path, flags := ⟨false, true⟩, ctfeMode := none, refTracking := none, dataBytes := none }

/-- Draining pointees with the fuel-free by-value traversal (`RankedWalk`). -/
def drainPointeesNoFuel {P S : Type} (h : VisitWalk P S)
    (tracking : RefTracking (Key P) ValidationPath) : M S Unit :=
  drainPointees tracking fun key path => do
    let _ ← visitNoFuel h (pointeeSession path) ⟨.memory key.mplace, key.layout⟩
    pure ()

/-- Draining pointees with the lexicographic `visitOrder` fuel-free traversal (`VisitLexWalk`). -/
def drainPointeesLexNoFuel {P S : Type} (h : VisitLexWalk S (RuntimePlace P) (Session P))
    (tracking : RefTracking (Key P) ValidationPath) : M S Unit :=
  drainPointees tracking fun key path => do
    let _ ← visitLexNoFuel h (pointeeSession path) ⟨.memory key.mplace, key.layout⟩
    pure ()

theorem drainPointees_empty {P S : Type} (tracking : RefTracking (Key P) ValidationPath)
    (visitPointee : Key P → ValidationPath → M S Unit) (h : tracking.todo = #[]) :
    drainPointees tracking visitPointee = pure () := by
  simp [drainPointees, h, List.forM_nil]

/-- LIFO: the most recently tracked pointee is visited first. -/
theorem drainPointees_push {P S : Type} (tracking : RefTracking (Key P) ValidationPath)
    (visitPointee : Key P → ValidationPath → M S Unit) (key : Key P) (path : ValidationPath) :
    drainPointees { tracking with todo := tracking.todo.push (key, path) } visitPointee =
      (do visitPointee key path; drainPointees tracking visitPointee) := by
  simp [drainPointees, Array.toList_push, List.reverse_append, List.forM_cons]

/-! ## 4. Static certificates induce certified hooks -/

/-- Hooks whose child projections are read off a static layout graph. -/
def ofGraph {S α : Type} (cert : ValidationRankCert) (g : LayoutGraph)
    (pre : LocalLayout → α → M S α) : RankedWalk S LocalLayout α where
  typeRank := cert.tyRank
  layoutOf := id
  pre := pre
  children := fun p => pure (g.children p).toArray

/-- A valid certificate (`checkCert cert g = true`, which already enforces node closure) makes the
graph hooks descend on every node in `g.nodes`. -/
theorem ofGraph_descendsOn {S α : Type} (cert : ValidationRankCert) (g : LayoutGraph)
    (pre : LocalLayout → α → M S α) (hcert : checkCert cert g = true) :
    (ofGraph cert g pre).DescendsOn (· ∈ g.nodes) := by
  intro p hp s cs s' hch
  simp only [ofGraph, pure, EStateM.pure, EStateM.Result.ok.injEq] at hch
  obtain ⟨rfl, -⟩ := hch
  intro c hc
  exact checkCert_sound cert g hcert p hp c hc

/-- **Certificate adequacy.** For any certificate accepted by `checkCert`, bounded-fuel validation
of any node in `g.nodes` agrees with fuel-free validation for every `fuel > layoutOrder root`. -/
theorem certified_walkFuel_eq_walkNoFuel {S α : Type} (cert : ValidationRankCert) (g : LayoutGraph)
    (pre : LocalLayout → α → M S α) (hcert : checkCert cert g = true)
    (root : LocalLayout) (hroot : root ∈ g.nodes) (acc : α) (fuel : Nat)
    (hfuel : layoutOrder cert.tyRank root < fuel) :
    (ofGraph cert g pre).walkFuel fuel root acc = (ofGraph cert g pre).walkNoFuel root acc :=
  (ofGraph cert g pre).walkFuel_eq_walkNoFuel _ (ofGraph_descendsOn cert g pre hcert)
    fuel root acc hroot hfuel

/-! ## 5. Bridge to `Anneal.MirFuelFree` -/

section MirFuelFreeBridge
open Trusted.Effect Trusted.ITree Anneal.EffectWP Anneal.ITreeWP

/-- The rank countdown coalgebra: from rank `n` it takes `n` silent steps and halts, i.e. the
depth profile of a rank-ordered traversal. -/
def rankCountdown : Nat → ITreeF EmptyE.{0} Unit Nat
  | 0 => .ret ()
  | n + 1 => .tau n

/-- The (vacuous) predicate transformer of the operation-free effect. -/
def emptyWP : StateEffectWP PUnit EmptyE.{0} where
  wp i _ _ := PEmpty.elim i
  mono {i} _ _ := PEmpty.elim i

/-- In `Anneal.MirFuelFree`'s fuel-indexed semantics, the rank countdown from `n` converges
exactly when the budget exceeds `n`. -/
theorem rankCountdown_converges_iff (fuel n : Nat) (s : PUnit) :
    wpCoalBounded fuel emptyWP rankCountdown (fun _ _ => True) n s ↔ n < fuel := by
  induction fuel generalizing n with
  | zero => simp [wpCoalBounded]
  | succ fuel ih =>
    cases n with
    | zero => simp [wpCoalBounded, rankCountdown]
    | succ n => simp only [wpCoalBounded, rankCountdown]; rw [ih]; omega

/-- `fuel := rank + 1` is the canonical static fuel bound, and by
`Anneal.MirFuelFree.wpCoalBounded_mono_fuel` every larger budget converges too. -/
theorem rankCountdown_canonical (n fuel : Nat) (s : PUnit) (hle : n + 1 ≤ fuel) :
    wpCoalBounded fuel emptyWP rankCountdown (fun _ _ => True) n s :=
  Anneal.MirFuelFree.wpCoalBounded_mono_fuel hle
    ((rankCountdown_converges_iff (n + 1) n s).mpr (Nat.lt_succ_self n))

/-- **Bridge (`RankedWalk`).** Any budget under which the root's rank countdown converges in
`Anneal.ITreeWP.wpCoalBounded` suffices for bounded-fuel validation to agree with `walkNoFuel`. -/
theorem walkFuel_eq_walkNoFuel_of_wpCoalBounded {S Pl α : Type} (h : RankedWalk S Pl α)
    (Good : Pl → Prop) (hd : h.DescendsOn Good) (fuel : Nat) (p : Pl) (acc : α) (hp : Good p)
    (s : PUnit) (hconv : wpCoalBounded fuel emptyWP rankCountdown (fun _ _ => True) (h.order p) s) :
    h.walkFuel fuel p acc = h.walkNoFuel p acc :=
  h.walkFuel_eq_walkNoFuel Good hd fuel p acc hp ((rankCountdown_converges_iff _ _ s).mp hconv)

/-- **Bridge (vendored `ValidityVisitor.unionRanges`).** Any budget under which `layoutOrder`
converges in `Anneal.ITreeWP.wpCoalBounded` suffices for the actual vendored
`ValidityVisitor.unionRanges` to equal `realUnionRangesNoFuel`. -/
theorem vendored_unionRanges_eq_noFuel_of_wpCoalBounded {P S C E F A Pad : Type}
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : Miri.MIR.TyId → Nat)
    (Good : LocalLayout → Prop) (hd : UnionHooksDescend h c typeRank Good)
    (fuel : Nat) (layout : LocalLayout) (base : Size) (initial : DataRangeSet) (hp : Good layout)
    (s : PUnit)
    (hconv : wpCoalBounded fuel emptyWP rankCountdown (fun _ _ => True)
      (layoutOrder typeRank layout) s) :
    ValidityVisitor.unionRanges h c fuel layout base initial =
      realUnionRangesNoFuel h c typeRank layout base initial :=
  vendored_unionRanges_eq_noFuel h c typeRank Good hd fuel layout base initial hp
    ((rankCountdown_converges_iff _ _ s).mp hconv)

end MirFuelFreeBridge

/-! ## 6. Concrete 150-level nested wrapper, union, and pattern witnesses -/

/-- A sized single-field aggregate layout (one field at offset `0`, single variant). -/
def wrapperLayout : LayoutData where
  fields := .Arbitrary #[Size.ZERO] #[0]
  variants := .Single 0
  backendRepr := .Memory (sized := true)
  largestNiche := none
  uninhabited := false
  align := ⟨Align.ONE⟩
  size := Size.ofBytes 1
  maxReprAlign := none
  unadjustedAbiAlign := Align.ONE
  reprC := false
  randomizationSeed := 0

/-- Type `k + 1` wraps type `k`; type `0` is the innermost leaf. -/
def wrapperChildren (place : LocalLayout) : Array LocalLayout :=
  if place.ty = 0 then #[] else #[{ place with ty := place.ty - 1 }]

/-- Validation of the wrapper chain with ranks `rank k = k` and no per-node failures. -/
def wrapperWalk : RankedWalk Unit LocalLayout Unit where
  typeRank := id
  layoutOf := id
  pre := fun _ acc => pure acc
  children := fun place => pure (wrapperChildren place)

/-- The root of a wrapper chain of the given depth. -/
def wrapperRoot (depth : Nat) : LocalLayout := ⟨depth, wrapperLayout⟩

/-- `true` iff a validation result succeeded. -/
def resultOk {ε σ β : Type} : EStateM.Result ε σ β → Bool
  | .ok .. => true
  | .error .. => false

/-- `true` iff a validation result is a fuel exhaustion with the given reason. -/
def resultExhausted {σ β : Type} (reason : String) : EStateM.Result StepError σ β → Bool
  | .error (.resourceExhaustion r) _ => r == reason
  | _ => false

theorem wrapperWalk_descendsOn : wrapperWalk.DescendsOn (fun _ => True) := by
  intro p _ s cs s' hch
  simp only [wrapperWalk, pure, EStateM.pure, EStateM.Result.ok.injEq] at hch
  obtain ⟨rfl, -⟩ := hch
  intro c hc
  refine ⟨trivial, ?_⟩
  unfold wrapperChildren at hc
  by_cases hz : p.ty = 0
  · simp [hz] at hc
  · simp only [hz, ↓reduceIte, List.mem_singleton] at hc
    subst hc
    exact layoutOrder_lt_of_rank_lt id p ⟨p.ty - 1, p.layout⟩
      (Nat.sub_lt (Nat.pos_of_ne_zero hz) Nat.one_pos)

theorem resultOk_unit (r : EStateM.Result StepError Unit Unit) (h : resultOk r = true) :
    r = .ok () () := by
  cases r with
  | ok a s => rfl
  | error e s => simp [resultOk] at h

theorem resultExhausted_unit (reason : String) (r : EStateM.Result StepError Unit Unit)
    (h : resultExhausted reason r = true) : r = .error (.resourceExhaustion reason) () := by
  cases r with
  | ok a s => simp [resultExhausted] at h
  | error e s =>
    cases e <;> simp_all [resultExhausted]

/-- Depth 150: fuel-free validation succeeds. Kernel-evaluated (no `native_decide`) through the
structural companion `walkRank`, which is equal to `walkNoFuel` by `walkRank_eq_walkNoFuel`. -/
theorem wrapper150_noFuel : wrapperWalk.walkNoFuel (wrapperRoot 150) () () = .ok () () := by
  apply resultOk_unit
  rw [← wrapperWalk.walkRank_eq_walkNoFuel]
  decide +kernel

/-- Depth 150 with bounded fuel `151` succeeds. -/
theorem wrapper150_fuel151 : wrapperWalk.walkFuel 151 (wrapperRoot 150) () () = .ok () () := by
  apply resultOk_unit
  decide +kernel

/-- Fuel `151` agrees with fuel-free validation at depth 150. -/
theorem wrapper150_fuel151_eq_noFuel :
    wrapperWalk.walkFuel 151 (wrapperRoot 150) () = wrapperWalk.walkNoFuel (wrapperRoot 150) () := by
  funext s
  cases s
  rw [wrapper150_fuel151, wrapper150_noFuel]

/-- Every budget `fuel ≤ 150` exhausts at depth 150 (all 151 budgets kernel-evaluated). -/
theorem wrapper150_small_fuel_exhausts (fuel : Nat) (hfuel : fuel ≤ 150) :
    wrapperWalk.walkFuel fuel (wrapperRoot 150) () () =
      .error (.resourceExhaustion "validity traversal fuel") () := by
  have hall : ((List.range 151).all fun n =>
      resultExhausted "validity traversal fuel"
        (wrapperWalk.walkFuel n (wrapperRoot 150) () ())) = true := by
    decide +kernel
  apply resultExhausted_unit
  simp only [List.all_eq_true, List.mem_range] at hall
  exact hall fuel (by omega)

/-! ### Concrete 150-level witnesses on vendored `ValidityVisitor.{unionRanges, visit}` -/

private def unusedHook {S A : Type} : M S A := throw (.unsupported "unused hook")

/-- Minimal concrete `ValidityVisitor.Hooks` instance over `Unit` state for kernel evaluation of
vendored `ValidityVisitor.unionRanges` and `ValidityVisitor.visit`. -/
def minimalValidityHooks {P : Type} [PointerProvenance P]
    (fieldFn : LocalLayout → Nat → LocalLayout)
    (layoutOfFn : Miri.MIR.TyId → LocalLayout)
    (classifyFn : Miri.MIR.TyId → ValidityVisitor.TypeKind) :
    Hooks P Unit Unit Unit Unit Unit Unit where
  target := RuntimeTargetDataLayout.default
  projection := {
    place := {
      getFrame := unusedHook, setFrame := fun _ => unusedHook, debugAssertions := false
      frameIndex := unusedHook, resolveLayout := fun _ _ => unusedHook
      localToOp := fun _ _ => unusedHook, projection := fun _ => unusedHook
      deref := fun _ _ _ => unusedHook, checkPlaceType := fun _ _ _ => unusedHook
      allocateStack := fun _ _ => unusedHook, writeMemoryNoValidate := fun _ _ _ => unusedHook
      afterLocalMovedToMemory := fun _ _ _ => unusedHook
      memoryOffset := fun _ base offset _ metaVal =>
        match base.ptr.offset.add offset with
        | .ok off => pure { base with ptr := { base.ptr with offset := off }, metadata := metaVal }
        | .error e => throw (.invalidProgram (reprStr e))
      writeLocalImmediate := fun _ _ _ _ => unusedHook
      enforceValidity := fun _ _ => pure true, validate := fun _ _ => pure ()
    }
    target := RuntimeTargetDataLayout.default.base
    maxSizeOfVal := Size.ofBytes 0x7FFF_FFFF_FFFF_FFFF
    dynamic := {
      target := RuntimeTargetDataLayout.default.base
      maxSizeOfVal := Size.ofBytes 0x7FFF_FFFF_FFFF_FFFF
      classify := fun _ _ => unusedHook, field := fun _ _ _ => unusedHook
      packedAlign := fun _ _ => pure none, vtableSizeAndAlign := fun _ _ _ => unusedHook
    }
    dynamicFuel := 0
    isSliceOrStr := fun _ _ => pure false
    field := fun _ parent idx => pure (fieldFn parent idx)
    variant := fun _ parent _ => pure parent
    packedAlign := fun _ _ => pure none
    subsliceLayout := fun _ _ _ => unusedHook
    layoutOf := fun _ ty => pure (layoutOfFn ty)
    localIndex := fun _ _ => unusedHook
  }
  vtable := {
    target := RuntimeTargetDataLayout.default.base
    isDynamic := fun _ _ => pure false, memoryOffset := fun _ _ _ _ _ => unusedHook
    resolvePointer := fun _ _ => unusedHook, globalVTable := fun _ _ => unusedHook
    globalFunction := fun _ _ => unusedHook, predicates := fun _ _ => unusedHook
    normalizePredicate := fun _ _ => unusedHook, layoutOf := fun _ _ => unusedHook
    eraseAndAnonymize := fun _ _ _ => unusedHook, ensureMonomorphicType := fun _ _ => pure ()
    ensureMonomorphicDyn := fun _ _ => pure (), globalSalt := fun _ => pure 0
    reserveVTable := fun _ _ _ _ => unusedHook, globalRootPointer := fun _ _ => unusedHook
    entries := fun _ _ _ => pure #[], assertVirtualInstanceMatches := fun _ _ _ _ _ => pure ()
  }
  discriminant := {
    runtimeTarget := RuntimeTargetDataLayout.default
    discriminantLayout := fun _ _ => unusedHook, tagLayout := fun _ _ => unusedHook
    discriminantValue := fun _ _ _ => unusedHook, variantForDiscriminant := fun _ _ _ => unusedHook
    adtVariantCount := fun _ _ => unusedHook, projectRead := fun _ _ _ => unusedHook
    readImmediate := fun _ _ => unusedHook, destLayout := fun p => p.layout
    projectWrite := fun _ _ _ => unusedHook, writeScalar := fun _ _ _ => unusedHook
    toOp := fun _ _ => unusedHook, scalarMayBeNull := fun _ _ => pure false
  }
  debugAssertions := false
  classify := fun _ ty => pure (classifyFn ty)
  unitLayout := fun _ => pure ⟨0, wrapperLayout⟩
  typeName := fun _ _ => pure "Root"
  opsemInhabited := fun _ _ => pure true
  isFreeze := fun _ _ => pure true
  fieldPath := fun _ _ _ _ => unusedHook
  variantPath := fun _ _ _ => unusedHook
  projectBox := fun _ _ => unusedHook
  toOp := fun _ _ => unusedHook
  readImmediate := fun _ _ _ => unusedHook
  clearProvenance := fun _ _ => pure ()
  writeNoValidate := fun _ _ _ => pure ()
  sizeAndAlign := fun _ _ => pure none
  ptrToPlace := fun _ _ => unusedHook
  metadataTail := fun _ _ => unusedHook
  checkPointerAccess := fun _ _ _ => pure (.ok ())
  checkPointerAlign := fun _ _ _ => pure ()
  checkPointerAlignResult := fun _ _ _ => pure (.ok ())
  scalarMayBeNull := fun _ _ => pure false
  retagPointer := fun _ _ _ => pure none
  ctfePointerLookup := fun _ _ _ => unusedHook
  inMutableMemory := fun _ _ => pure true
  readBytes := fun _ _ _ _ => pure ()
  clearBytesProvenance := fun _ _ _ => pure ()
  beginPadding := fun _ _ _ => pure none
  writePadding := fun _ _ _ => pure ()
  cachedUnionRanges := fun _ _ comp => comp
  withGhostValidation := fun comp => comp

/-- Depth-`ty` nested union layout (`lean-miri#90` `ConnectedPointerAlignment.lean` L917):
`.Primitive` 1-byte leaf at `0`, `.Union 1` wrapping `ty - 1` for `ty > 0`. -/
def deepUnionLayout (ty : Nat) : LocalLayout :=
  ⟨ty, { wrapperLayout with fields := if ty == 0 then .Primitive else .Union 1 }⟩

def deepUnionHooks : Hooks CtfeProvenance Unit Unit Unit Unit Unit Unit :=
  minimalValidityHooks (fun parent _ => deepUnionLayout (parent.ty - 1)) deepUnionLayout
    (fun _ => .foreign)

/-- Depth 150 on `realUnionRangesNoFuel` succeeds in the kernel and returns `[0, 1)`. -/
theorem deepUnion150_noFuel :
    (match realUnionRangesNoFuel deepUnionHooks () id (deepUnionLayout 150) Size.ZERO .empty () with
     | .ok ranges () => ranges.toArray == #[allocRange Size.ZERO (Size.ofBytes 1)]
     | .error _ _ => false) = true := by
  rw [← realUnionRangesRank_eq_noFuel]
  decide +kernel

/-- Depth 150 on the actual vendored `ValidityVisitor.unionRanges` succeeds at `fuel = 151` and
exhausts at `fuel = 150`. -/
theorem deepUnion150_vendored :
    (match ValidityVisitor.unionRanges deepUnionHooks () 151
        (deepUnionLayout 150) Size.ZERO .empty () with
     | .ok ranges () => ranges.toArray == #[allocRange Size.ZERO (Size.ofBytes 1)]
     | .error _ _ => false) = true ∧
    resultExhausted "union layout traversal fuel"
      (ValidityVisitor.unionRanges deepUnionHooks () 150
        (deepUnionLayout 150) Size.ZERO .empty ()) = true := by
  exact ⟨by decide +kernel, by decide +kernel⟩

def deepPatternHooks : Hooks CtfeProvenance Unit Unit Unit Unit Unit Unit :=
  minimalValidityHooks (fun parent _ => parent) (fun ty => ⟨ty, wrapperLayout⟩)
    (fun ty => if ty == 0 then .foreign else .pattern (ty - 1))

/-- Depth 150 nested `.pattern` walk on the actual vendored `ValidityVisitor.visit`
(`lean-miri#90` `ConnectedPointerAlignment.lean` L909): succeeds at `fuel = 151` and exhausts at
`fuel = 150`. -/
theorem deepPattern150_vendored_visit :
    let root : RuntimePlace CtfeProvenance :=
      ⟨.memory ⟨⟨Size.ZERO, none⟩, .none, none⟩, ⟨150, wrapperLayout⟩⟩
    let init : Session CtfeProvenance :=
      { path := ⟨"Root", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    resultOk (ValidityVisitor.visit deepPatternHooks () 151 init root ()) = true ∧
    resultExhausted "validity traversal fuel"
      (ValidityVisitor.visit deepPatternHooks () 150 init root ()) = true := by
  exact ⟨by decide +kernel, by decide +kernel⟩

/-! ## 7. `leanprover/lean4#13851` axiom footprint audit

`lean4#13851` reimplements `WellFounded.fix` with `Classical.choice`, so every `termination_by`
definition (`RankedWalk.walkNoFuel`, `VisitLexWalk.walkNoFuel`, `realUnionRangesNoFuel`, and their
wrappers `visitNoFuel`, `visitLexNoFuel`, `unionRangesNoFuel`, `drainPointeesNoFuel`), and every
theorem whose statement mentions one, will acquire `Classical.choice`. The structural (`Nat.rec`
and `Nat.rec × Nat.rec`) companions (`RankedWalk.walkRank`, `VisitLexWalk.walkRank`,
`realUnionRangesRank`, `checkCert`, `checkSchema17Table`) do not use `WellFounded.fix`:

* `#guard_msgs` pins exact current footprints on both the `layoutOrder` (`ω`) and `visitOrder`
  (`ω · 2`) structural vs. well-founded layers plus `realUnionRanges*`;
* `#assert_choice_free` guards the entire structural layer against `{propext, Quot.sound}` so it
  remains `Classical.choice`-free after `lean4#13851`;
* `#assert_standard_axioms` guards the well-founded layer and sweeps all declarations in
  `env.constants.map₂` against `{propext, Quot.sound, Classical.choice}`. -/

/-- info: 'LeanMiriSpec.ValidationRankCert.RankedWalk.walkRank' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RankedWalk.walkRank

/-- info: 'LeanMiriSpec.ValidationRankCert.RankedWalk.walkFuel' does not depend on any axioms -/
#guard_msgs in
#print axioms RankedWalk.walkFuel

/-- info: 'LeanMiriSpec.ValidationRankCert.RankedWalk.walkNoFuel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RankedWalk.walkNoFuel

/-- info: 'LeanMiriSpec.ValidationRankCert.VisitLexWalk.walkRank' depends on axioms: [propext] -/
#guard_msgs in
#print axioms VisitLexWalk.walkRank

/-- info: 'LeanMiriSpec.ValidationRankCert.VisitLexWalk.walkNoFuel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms VisitLexWalk.walkNoFuel

/-- info: 'LeanMiriSpec.ValidationRankCert.realUnionRangesRank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms realUnionRangesRank

/-- info: 'LeanMiriSpec.ValidationRankCert.realUnionRangesNoFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms realUnionRangesNoFuel

#assert_choice_free
  layoutOrder
  visitOrder
  layoutOrder_lt_of_rank_lt
  layoutOrder_variant_lt
  layoutOrder_primitive_lt
  visitOrder_lt_of_same_sized
  visitOrder_lt_of_unsized_unpack
  checkCert
  checkCert_sound
  checkCert_reach_descends
  checkCert_acyclic
  checkCert_rejects_cycle
  checkSchema17Table
  checkSchema17Table_sound
  checkSchema17Table_acyclic
  RankedWalk.walkGuarded
  RankedWalk.walkFuel
  RankedWalk.walkRank
  VisitLexWalk.walkSized
  VisitLexWalk.walkUnsized
  VisitLexWalk.walkRank
  VisitLexWalk.walkFuel
  realUnionRangesGuarded
  realUnionRangesRank
  vendored_unionRanges_eq_guarded
  drainPointees
  drainPointees_push
  wrapper150_fuel151
  wrapper150_small_fuel_exhausts
  deepUnion150_vendored
  deepPattern150_vendored_visit

#assert_standard_axioms
  RankedWalk.walkNoFuel
  VisitLexWalk.walkNoFuel
  visitNoFuel
  visitLexNoFuel
  unionRangesNoFuel
  realUnionRangesNoFuel
  drainPointeesNoFuel
  drainPointeesLexNoFuel
  RankedWalk.walkGuarded_eq_walkNoFuel
  RankedWalk.walkRank_eq_walkNoFuel
  RankedWalk.walkFuel_eq_walkGuarded
  RankedWalk.walkFuel_eq_walkNoFuel
  RankedWalk.walkFuel_rank_succ
  RankedWalk.walkNoFuel_rejects_nondescending
  VisitLexWalk.walkRank_eq_walkNoFuel
  VisitLexWalk.walkFuel_eq_walkNoFuel
  VisitLexWalk.walkNoFuel_rejects_nondescending
  realUnionRangesRank_eq_noFuel
  vendored_unionRanges_eq_noFuel
  ofGraph_descendsOn
  certified_walkFuel_eq_walkNoFuel
  rankCountdown_converges_iff
  rankCountdown_canonical
  walkFuel_eq_walkNoFuel_of_wpCoalBounded
  vendored_unionRanges_eq_noFuel_of_wpCoalBounded
  wrapper150_noFuel
  wrapper150_fuel151_eq_noFuel
  deepUnion150_noFuel

end LeanMiriSpec.ValidationRankCert
