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
     (`vendored_unionRanges_eq_noFuel`),
   - `RealVisit.realVisitNoFuel` (verbatim `lean-miri#90` `visit`, well-founded on `visitOrder`,
     over the kernel-checked factorization `RealVisit.vendored_visit_succ` of the **actual
     vendored `Miri.Interpreter.ValidityVisitor.visit`** into `RealVisit.visitStep`), proved
     equivalent to the vendored `visit` for every hook instance satisfying the one-step
     `RealVisit.VisitHooksDescend` (`RealVisit.vendored_visit_eq_noFuel`; sized-root form
     `RealVisit.vendored_visit_eq_noFuel_of_sized` at fuel `> layoutOrder + 1`), with the
     hypothesis discharged for the deep `.pattern` chain at *every* depth
     (`RealVisit.deepPattern_vendored_visit_eq_noFuel`) and a self-looping projection rejected
     (`RealVisit.selfPattern_noFuel_rejects_vendored_exhausts`), and
   - `drainPointees` / `pointeeSession` LIFO pointee queue draining.
4. Equivalences, deterministic `.invalidProgram` hook-violation rejection, and the
   `Anneal.MirFuelFree` bridge (`rankCountdown_converges_iff`, `rankCountdown_canonical`,
   `walkFuel_eq_walkNoFuel_of_wpCoalBounded`, `vendored_unionRanges_eq_noFuel_of_wpCoalBounded`).
5. Kernel-evaluated 150-level nested single-field wrapper, union, and pattern witnesses over both
   the companion traversals and the actual vendored `ValidityVisitor.{unionRanges, visit}`.
6. `leanprover/lean4#13851` axiom footprint audit (§8: `#guard_msgs` `#print axioms`,
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

/-! ## 7. Real vendored `ValidityVisitor.visit` adequacy (`lean-miri#90` fuel-free `visit`)

`visitStep` is the body of the vendored `Miri.Interpreter.ValidityVisitor.visit` *verbatim*, with
its two recursive occurrences factored into continuations: `descend` (every
`visit h c fuel {…} child` call) and `unionComp` (the `unionRanges h c fuel place.layout …` hand-off
in the union data-range branch). The vendored private helpers (`liftResult`, `failure`, `scalarOf`,
`sizeResult`, `rangeResult`, `sizePlace`, `markRange`, `dataOffset`, `markPlace`, `resetPointer`,
`checkMetadata`, `checkSafe`, `checkScalarRange`, `abiRanges`, `primitive`) are mirrored verbatim, and
`vendored_visit_succ` is proved by unfolding the vendored equation lemma and closing with `rfl`, so
the kernel itself certifies that `visitStep` *is* one unfolding of the unmodified vendored `visit`.

`realVisitNoFuel` is then `lean-miri#90`'s fuel-free `visit` (well-founded on `visitOrder` under
`Prod.Lex`, `.invalidProgram "validity projection does not descend"` at every projection boundary,
and `realUnionRangesNoFuel` for the union hand-off). Adequacy against the actual vendored `visit` is
proved for *every* hook instance satisfying the one-step hypothesis `VisitHooksDescend`. -/

namespace RealVisit

open Miri Miri.Interpreter.ValidityVisitor

section
variable {P S C E F A Pad : Type}

private def liftResult (value : Except StepError A) : M S A :=
  match value with | .ok value => pure value | .error error => throw error
private def failure (session : Session P) (message : String) : M S A :=
  throw (.undefinedBehavior s!"validation{session.path.render}: {message}")
private def scalarOf (value : Immediate P) : M S (Scalar P) :=
  liftResult (value.toScalar.mapError fun error => .invalidProgram s!"validity scalar: {repr error}")
private def sizeResult (value : Except SizeError A) : M S A :=
  liftResult (value.mapError fun error => .invalidProgram s!"validity size: {repr error}")
private def rangeResult (value : Except RangeSetError A) : M S A :=
  liftResult (value.mapError fun error => .invalidProgram s!"validity range: {repr error}")

private def sizePlace (h : Hooks P S C E F A Pad) (c : C) (place : RuntimePlace P) : M S (Option (Size × Align)) := do
  if place.layout.layout.isSized then return some (place.layout.layout.size,place.layout.layout.align.abi)
  match place.ref with
  | .memory memory => h.sizeAndAlign c ⟨memory,place.layout⟩
  | .local .. => throw (.invalidProgram "unsized local validity place")

private def markRange (session : Session P) (offset size : Size) : M S (Session P) := do
  let some ranges := session.dataBytes | return session
  let ranges ← rangeResult (ranges.addRange offset size)
  return {session with dataBytes := some ranges}
private def dataOffset (h : Hooks P S C E F A Pad) (c : C) (place : RuntimePlace P) : M S Size := do
  match (← h.toOp c place).op with
  | .indirect memory => return memory.ptr.offset
  | .immediate _ => throw (.invalidProgram "tracked validity data is not in memory")
private def markPlace (h : Hooks P S C E F A Pad) (c : C) (session : Session P)
    (place : RuntimePlace P) : M S (Session P) := do
  if session.dataBytes.isNone then return session
  if !place.layout.layout.isSized then throw (.invalidProgram "unsized validity data range")
  markRange session (← dataOffset h c place) place.layout.layout.size

private def resetPointer (h : Hooks P S C E F A Pad) (c : C) (place : RuntimePlace P)
    (pointer : RvalueImmTy P) : M S Unit := do
  match pointer.layout.layout.backendRepr with
  | .Scalar _ => if !(← scalarOf pointer.imm).isPointer then h.clearProvenance c place
  | _ => h.writeNoValidate c pointer.imm place

private def checkMetadata [PointerProvenance P] (h : Hooks P S C E F A Pad) (c : C)
    (place : MPlaceTy P) : M S Unit := do
  match ← h.metadataTail c place.layout.ty with
  | .foreign => pure ()
  | .sliceOrStr =>
    let scalar ← liftResult (place.mplace.metadata.unwrapMeta.mapError fun e => .invalidProgram (reprStr e))
    let _ ← liftResult ((scalar.toTargetUsize h.target.pointerSize).mapError ScalarOps.scalarError)
  | .dynamic expected =>
    let scalar ← liftResult (place.mplace.metadata.unwrapMeta.mapError fun e => .invalidProgram (reprStr e))
    let pointer ← liftResult ((scalar.toPointer h.target.base).mapError ScalarOps.scalarError)
    let _ ← VTable.getPtrVTableType h.vtable c pointer (some expected)

private def checkSafe [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (value : RuntimePlace P) (ty : MIR.TyId) (kind : SafePointerKind) : M S (Session P) := do
  let pointer ← h.readImmediate c value (match kind with | .box => .box | _ => .reference)
  let mut session := session
  if session.flags.resetProvenanceAndPadding then session ← markPlace h c session value
  let place ← h.ptrToPlace c pointer
  if !place.layout.layout.isSized then checkMetadata h c place
  let dynamic ← h.sizeAndAlign c place
  let (size, align) := dynamic.getD (place.layout.layout.size, place.layout.layout.align.abi)
  let adjusted ← if !session.flags.mayDangle then do
      match ← h.checkPointerAccess c place.mplace.ptr size with
      | .ok () => pure ()
      | .error error => throw (classifyPointerAccessError session.path kind error)
      if session.flags.resetProvenanceAndPadding then
        retagSafePointer session.path kind h.retagPointer c pointer ty
      else pure none
    else do
      let scalar ← liftResult ((Scalar.fromMaybePointer h.target.base place.mplace.ptr).mapError ScalarOps.scalarError)
      match scalar.tryToScalarInt with
      | .ok (.integer integer) =>
        let address ← liftResult ((integer.toTargetUsize h.target.pointerSize).mapError fun e => .invalidProgram (reprStr e))
        let maximum := (2^h.target.base.pointerWidth.bits.toNat - 1 : Nat)
        if address.toNat + size.bytes.toNat >= maximum then failure session "safe pointer too close to address-space end"
      | .ok (.erasedPointer ..) => pure ()
      | .error error => throw (ScalarOps.scalarError error)
      pure none
  if let some adjusted := adjusted then h.writeNoValidate c adjusted.imm value
  else if session.flags.resetProvenanceAndPadding then resetPointer h c value pointer
  let scalar ← liftResult ((Scalar.fromMaybePointer h.target.base place.mplace.ptr).mapError ScalarOps.scalarError)
  if ← h.scalarMayBeNull c scalar then failure session "null or maybe-null safe pointer"
  unless ← h.opsemInhabited c place.layout.ty do failure session "safe pointer to uninhabited type"
  mapPointerAlignmentOutcome session.path kind
    (h.checkPointerAlignResult c place.mplace.ptr align)
  if let some tracker := session.refTracking then
    unless session.flags.mayDangle do
      let mut skip := false
      if let some mode := session.ctfeMode then
        let lookup ← h.ctfePointerLookup c place mode
        match ctfeRecursionDecision mode kind lookup with
        | .error error => failure session (reprStr error)
        | .ok value => skip := value
      unless skip do
        let key : Key P := ⟨place.mplace, place.layout⟩
        let tracker := tracker.track key (fun _ => session.path.push .deref)
        session := {session with refTracking := some tracker}
  return session
private def checkScalarRange [PointerProvenance P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (scalar : Scalar P) (abi : ABI.Scalar) : M S Unit := do
  match abi with
  | .Union .. => pure ()
  | .Initialized (value := primitive) (validRange := validRange) =>
    let size ← liftResult ((Primitive.size primitive h.target).mapError fun e => .invalidProgram (reprStr e))
    let callback := fun scalar state => h.scalarMayBeNull c scalar state
    match Validity.checkScalar ⟨size, validRange⟩ scalar callback (← get) with
    | .ok () state => set state
    | .error (.machine error) state => set state; throw error
    | .error error state => set state; failure session (reprStr error)

private def abiRanges [PointerProvenance P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (place : RuntimePlace P) : M S Unit := do
  match place.layout.layout.backendRepr with
  | .Scalar abi =>
    if let .Initialized .. := abi then
      let scalar ← scalarOf (← h.readImmediate c place .integer).imm
      checkScalarRange h c session scalar abi
  | .ScalarPair (a := abiA) (b := abiB) .. =>
    if let .Initialized .. := abiA then
      if let .Initialized .. := abiB then
        match (← h.readImmediate c place .integer).imm with
        | .scalarPair a b => checkScalarRange h c session a abiA; checkScalarRange h c session b abiB
        | _ => throw (.invalidProgram "validity scalar-pair ABI mismatch")
  | _ => pure ()

private def primitive [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (session : Session P) (place : RuntimePlace P) (kind : TypeKind) : M S (Option (Session P)) := do
  match kind with
  | .never => failure session "never value"
  | .foreign | .functionDefinition => return some session
  | .unsafeBinder => throw (.unsupported "upstream unsafe-binder validity is unimplemented")
  | .invalid => throw (.invalidProgram "invalid/non-normalized type during validity")
  | .boolean | .character | .integer | .float =>
    let expected := match kind with | .boolean => ExpectedValue.boolean | .character => .character | .float => .float | _ => .integer
    let scalar ← scalarOf (← h.readImmediate c place expected).imm
    if kind == .boolean then
      let _ ← liftResult (scalar.toBool.mapError fun error => .undefinedBehavior s!"validation{session.path.render}: {repr error}")
    if kind == .character then
      let _ ← liftResult (scalar.toChar.mapError fun error => .undefinedBehavior s!"validation{session.path.render}: {repr error}")
    if session.flags.resetProvenanceAndPadding then
      h.clearProvenance c place
      return some (← markPlace h c session place)
    return some session
  | .rawPointer _ sized =>
    let pointer ← h.readImmediate c place .rawPointer
    let mut session := session
    if session.flags.resetProvenanceAndPadding then
      resetPointer h c place pointer
      session ← markPlace h c session place
    if !sized then
      let target ← h.ptrToPlace c pointer
      if target.layout.layout.isSized then throw (.invalidProgram "unsized raw-pointer target resolved sized")
      checkMetadata h c target
    return some session
  | .reference mutable => return some (← checkSafe h c session place place.layout.ty (.reference mutable))
  | .functionPointer =>
    let scalar ← scalarOf (← h.readImmediate c place .functionPointer).imm
    if session.refTracking.isSome then
      let pointer ← liftResult ((scalar.toPointer h.target.base).mapError ScalarOps.scalarError)
      let _ ← VTable.getPtrFn h.vtable c pointer
    else if ← h.scalarMayBeNull c scalar then failure session "null or maybe-null function pointer"
    if session.flags.resetProvenanceAndPadding then
      if !scalar.isPointer then h.clearProvenance c place
      return some (← markPlace h c session place)
    return some session
  | _ => return none

/-- One unfolding of the vendored `ValidityVisitor.visit` body, verbatim, with the recursive
`visit h c fuel` calls abstracted as `descend` and the union data-range traversal
`unionRanges h c fuel place.layout Size.ZERO .empty` abstracted as `unionComp`. -/
def visitStep [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (descend : Session P → RuntimePlace P → M S (Session P)) (unionComp : M S DataRangeSet)
    (session : Session P) (place : RuntimePlace P) : M S (Session P) := do
    let kind ← h.classify c place.layout.ty
    if let some session ← primitive h c session place kind then return session
    let mut session := session
    if let some mode := session.ctfeMode then
      if !allowsImmutableUnsafeCell mode then
        let sized ← sizePlace h c place
        if sized.map Prod.fst != some Size.ZERO then
          if let .aggregate _ true _ := kind then
            unless ← h.inMutableMemory c place do failure session "UnsafeCell in read-only memory"
    match kind with
    | .string =>
      let .indirect memory := (← h.toOp c place).op | throw (.invalidProgram "str immediate")
      let len ← PlaceDynamic.length h.projection c place
      h.readBytes c ⟨memory, place.layout⟩ (Size.ofBytes len) .string
    | .sequence element =>
      let elementKind ← h.classify c element
      if elementKind == .integer || elementKind == .float then
        let len ← PlaceDynamic.length h.projection c place
        let elementLayout ← h.projection.layoutOf c element
        let size ← sizeResult (elementLayout.layout.size.mul len)
        if size == Size.ZERO then return session
        let op ← h.toOp c place
        let memory ← match op.op with
          | .indirect memory => pure memory
          | .immediate .uninit => failure session "uninitialized numeric array"
          | .immediate _ => throw (.invalidProgram "numeric array scalar ABI")
        let expected := if elementKind == .float then ExpectedValue.float else .integer
        h.readBytes c ⟨memory, place.layout⟩ size expected
        if session.flags.resetProvenanceAndPadding then
          h.clearBytesProvenance c ⟨memory, place.layout⟩ size
          session ← markRange session memory.ptr.offset size
      else
        let elementLayout ← h.projection.layoutOf c element
        if elementLayout.layout.isZst then
          if (← PlaceDynamic.length h.projection c place) > 0 then
            let child ← PlaceDynamic.index h.projection c place 0
            let path := session.path
            session ← descend {session with path := path.push (.arrayElem 0)} child
            session := {session with path}
        else
          let stride ← match place.layout.layout.fields with
            | .Array stride _ => pure stride
            | _ => throw (.invalidProgram "sequence has non-array fields")
          let len ← PlaceDynamic.length h.projection c place
          let element ← h.projection.field c place.layout 0
          let endOffset ← sizeResult (stride.mul len)
          let _ ← PlaceDynamic.offsetWithMeta h.projection c place endOffset .inbounds .none (← h.unitLayout c)
          for index in [:len.toNat] do
            let offset ← sizeResult (stride.mul (UInt64.ofNat index))
            let child ← PlaceDynamic.offsetWithMeta h.projection c place offset .wrapping .none element
            let path := session.path
            session ← descend {session with path := path.push (.arrayElem index)} child
            session := {session with path}
    | .pattern base =>
      let layout ← h.projection.layoutOf c base
      if !layout.layout.isSized || !place.layout.layout.isSized || layout.layout.size != place.layout.layout.size then
        throw (.invalidProgram "pattern base transmute layout mismatch")
      let child ← PlaceDynamic.offsetWithMeta h.projection c place .ZERO .wrapping .none layout
      session ← descend session child
      abiRanges h c session place
    | _ =>
      let oldMayDangle := session.flags.mayDangle
      if let .aggregate maybeDangling _ _ := kind then
        session := {session with flags := {session.flags with mayDangle := oldMayDangle || maybeDangling}}
      if let .dynamic expected := kind then
        let op ← h.toOp c place
        let inner ← VTable.unpackDynTrait h.vtable c op expected
        let .indirect memory := inner.op | throw (.invalidProgram "dynamic unpack returned immediate")
        let path := session.path
        session ← descend {session with path := path.push (← h.fieldPath c place.layout 0 inner.layout.ty)} ⟨.memory memory,inner.layout⟩
        session := {session with path}
      else if kind == .box then
        let (pointer, allocator) ← h.projectBox c place
        session ← checkSafe h c session pointer place.layout.ty .box
        let path := session.path
        session ← descend {session with path := path.push (← h.fieldPath c place.layout 1 allocator.layout.ty)} allocator
        session := {session with path}
      else
        match place.layout.layout.fields with
        | .Primitive => pure ()
        | .Union _ =>
          if let some mode := session.ctfeMode then
            if !allowsImmutableUnsafeCell mode then
              let size ← sizePlace h c place
              if size.map Prod.fst != some Size.ZERO then
                unless ← h.isFreeze c place.layout.ty do
                  unless ← h.inMutableMemory c place do failure session "UnsafeCell union in read-only memory"
          if session.flags.resetProvenanceAndPadding && session.dataBytes.isSome then
            let base ← dataOffset h c place
            if !place.layout.layout.isSized then throw (.invalidProgram "unsized union data ranges")
            let ranges ← h.cachedUnionRanges c place.layout (unionComp)
            for range in ranges.toArray do
              session ← markRange session (← sizeResult (base.add range.start)) range.size
        | .Arbitrary _ order =>
          for index in order do
            let child ← PlaceDynamic.field h.projection c place index
            let path := session.path
            session ← descend {session with path := path.push (← h.fieldPath c place.layout index child.layout.ty)} child
            session := {session with path}
        | .Array stride _ =>
          let len ← PlaceDynamic.length h.projection c place
          let element ← h.projection.field c place.layout 0
          let endOffset ← sizeResult (stride.mul len)
          let _ ← PlaceDynamic.offsetWithMeta h.projection c place endOffset .inbounds .none (← h.unitLayout c)
          for index in [:len.toNat] do
            let offset ← sizeResult (stride.mul (UInt64.ofNat index))
            let child ← PlaceDynamic.offsetWithMeta h.projection c place offset .wrapping .none element
            let path := session.path
            session ← descend {session with path := path.push (.arrayElem index)} child
            session := {session with path}
        match place.layout.layout.variants with
        | .Multiple .. =>
          let variant ← Discriminant.readDiscriminant h.discriminant c (← h.toOp c place)
          let child ← PlaceDynamic.downcast h.projection c place variant
          let path := session.path
          session ← descend {session with path := path.push (← h.variantPath c place.layout variant)} child
          session := {session with path}
        | .Empty =>
          match kind with
          | .aggregate _ _ true => failure session "zero-variant enum value"
          | _ => throw (.invalidProgram "variantless validity type is not an enum")
        | .Single _ => pure ()
      session := {session with flags := {session.flags with mayDangle := oldMayDangle}}
    unless ← h.opsemInhabited c place.layout.ty do throw (.invalidProgram "uninhabited type passed validity")
    if h.debugAssertions then abiRanges h c session place
    return session

/-- **Kernel-checked factorization of the unmodified vendored `visit`.** One fuel step of
`Miri.Interpreter.ValidityVisitor.visit` is exactly `visitStep` applied to the vendored recursive
call and the vendored `unionRanges` hand-off at the remaining fuel. -/
theorem vendored_visit_succ [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad)
    (c : C) (fuel : Nat) (session : Session P) (place : RuntimePlace P) :
    ValidityVisitor.visit h c (fuel + 1) session place =
      visitStep h c (ValidityVisitor.visit h c fuel)
        (ValidityVisitor.unionRanges h c fuel place.layout Size.ZERO .empty) session place := by
  rw [ValidityVisitor.visit.eq_2]; rfl

/-- `lean-miri#90`'s dynamic `visit` projection guard: recurse only into children that strictly
descend in `visitOrder` (`Prod.Lex`), otherwise throw `.invalidProgram`. -/
def visitGuard (typeRank : MIR.TyId → Nat) (place : RuntimePlace P)
    (k : Session P → RuntimePlace P → M S (Session P)) (session : Session P)
    (child : RuntimePlace P) : M S (Session P) :=
  if VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout) then
    k session child
  else throw (.invalidProgram "validity projection does not descend")

/-- **Fuel-free `ValidityVisitor.visit` (`lean-miri#90`) over the real vendored hooks.** Well-founded
recursion on `visitOrder typeRank place.layout` under `Prod.Lex`, with the dynamic
`.invalidProgram "validity projection does not descend"` guard at every projection boundary and the
fuel-free `realUnionRangesNoFuel` for union data ranges. -/
def realVisitNoFuel [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (typeRank : MIR.TyId → Nat) (session : Session P) (place : RuntimePlace P) :
    M S (Session P) :=
  visitStep h c
    (fun childSession child =>
      if _smaller : VisitOrderLt (visitOrder typeRank child.layout)
          (visitOrder typeRank place.layout) then
        realVisitNoFuel h c typeRank childSession child
      else throw (.invalidProgram "validity projection does not descend"))
    (realUnionRangesNoFuel h c typeRank place.layout Size.ZERO .empty) session place
termination_by visitOrder typeRank place.layout
decreasing_by exact _smaller

/-- Structural (`Nat.rec`, `Classical.choice`-free) fuelled companion of `realVisitNoFuel`: the
same guarded step, with the vendored fuel discipline (the union hand-off receives the remaining
fuel, exactly like the vendored `visit`). -/
def realVisitGuarded [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (typeRank : MIR.TyId → Nat) : Nat → Session P → RuntimePlace P → M S (Session P)
  | 0, _, _ => throw (.resourceExhaustion "validity traversal fuel")
  | fuel + 1, session, place =>
    visitStep h c (visitGuard typeRank place (realVisitGuarded h c typeRank fuel))
      (realUnionRangesGuarded h c typeRank fuel place.layout Size.ZERO .empty) session place

/-- Canonical structural companion for sized roots at fuel `layoutOrder + 2` (one step for the
place itself and one for the union hand-off, which the vendored `visit` performs at the *remaining*
fuel on the *same* layout). -/
def realVisitRank [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (typeRank : MIR.TyId → Nat) (session : Session P) (place : RuntimePlace P) :
    M S (Session P) :=
  realVisitGuarded h c typeRank (layoutOrder typeRank place.layout + 2) session place

/-- Unfolding equation of `realVisitNoFuel` through `visitGuard`. -/
theorem realVisitNoFuel_eq [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad)
    (c : C) (typeRank : MIR.TyId → Nat) (session : Session P) (place : RuntimePlace P) :
    realVisitNoFuel h c typeRank session place =
      visitStep h c (visitGuard typeRank place (realVisitNoFuel h c typeRank))
        (realUnionRangesNoFuel h c typeRank place.layout Size.ZERO .empty) session place := by
  rw [realVisitNoFuel.eq_1]
  rfl

/-- A `visitOrder` descent from a sized parent lands on a sized child of strictly smaller
`layoutOrder` (sized places never unpack to unsized ones). -/
theorem visitOrder_lt_of_sized_parent (typeRank : MIR.TyId → Nat) (parent child : LocalLayout)
    (hp : parent.layout.isSized = true)
    (hlt : VisitOrderLt (visitOrder typeRank child) (visitOrder typeRank parent)) :
    child.layout.isSized = true ∧ layoutOrder typeRank child < layoutOrder typeRank parent := by
  unfold VisitOrderLt visitOrder at hlt
  rw [Prod.lex_def] at hlt
  cases hc : child.layout.isSized <;> simp only [hc, hp, Bool.false_eq_true, ↓reduceIte] at hlt
  · omega
  · exact ⟨rfl, by omega⟩

/-- **Unconditional structural adequacy for sized roots.** For every hook instance, the
structural `realVisitGuarded` equals the well-founded `realVisitNoFuel` at every fuel strictly
above `layoutOrder + 1`. -/
theorem realVisitGuarded_eq_noFuel_of_sized [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat) :
    ∀ (fuel : Nat) (session : Session P) (place : RuntimePlace P),
      place.layout.layout.isSized = true → layoutOrder typeRank place.layout + 1 < fuel →
      realVisitGuarded h c typeRank fuel session place = realVisitNoFuel h c typeRank session place
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, session, place, hs, hlt => by
    rw [realVisitNoFuel_eq]
    simp only [realVisitGuarded]
    rw [realUnionRangesGuarded_eq_noFuel h c typeRank fuel place.layout Size.ZERO .empty
      (by omega)]
    congr 1
    funext s child
    unfold visitGuard
    by_cases hc : VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
    · simp only [hc, ↓reduceIte]
      obtain ⟨hcs, hclt⟩ := visitOrder_lt_of_sized_parent typeRank place.layout child.layout hs hc
      exact realVisitGuarded_eq_noFuel_of_sized h c typeRank fuel s child hcs (by omega)
    · simp only [hc, ↓reduceIte]

/-- Unconditional equality between the structural `realVisitRank` and `realVisitNoFuel` on every
sized root. -/
theorem realVisitRank_eq_noFuel [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad)
    (c : C) (typeRank : MIR.TyId → Nat) (session : Session P) (place : RuntimePlace P)
    (hs : place.layout.layout.isSized = true) :
    realVisitRank h c typeRank session place = realVisitNoFuel h c typeRank session place :=
  realVisitGuarded_eq_noFuel_of_sized h c typeRank _ session place hs (Nat.lt_succ_self _)

/-- Guard that additionally requires the child to satisfy a caller-chosen invariant `good`. -/
def goodGuard (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (place : RuntimePlace P)
    (k : Session P → RuntimePlace P → M S (Session P)) (session : Session P)
    (child : RuntimePlace P) : M S (Session P) :=
  if good child = true ∧
      VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout) then
    k session child
  else throw (.invalidProgram "validity projection does not descend")

/-- Guard on the union hand-off: run it only when the place's layout satisfies `goodU`. -/
def unionGuard (goodU : LocalLayout → Bool) (place : RuntimePlace P)
    (u : M S DataRangeSet) : M S DataRangeSet :=
  if goodU place.layout = true then u
  else throw (.invalidProgram "union layout projection does not descend")

/-- **One-step projection-hook descent hypothesis for the real vendored `visit`.** At every
`good` place, one unfolding of the vendored `visit` body only ever recurses into `good` children
that strictly descend in `visitOrder`, and only reaches the union hand-off on `goodU` layouts:
guarding both continuations changes nothing, *whatever* the continuations are. Because the
continuations are universally quantified this is a property of the hooks alone. -/
def VisitHooksDescend [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad) (c : C)
    (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool) :
    Prop :=
  ∀ place, good place = true → ∀ k u session,
    visitStep h c (goodGuard typeRank good place k) (unionGuard goodU place u) session place =
      visitStep h c k u session place

/-- Sufficient vendored fuel for a place (`maxSized` bounds the `layoutOrder` of the sized concrete
places reached by unpacking an unsized one). -/
def visitFuelBound (maxSized : Nat) (typeRank : MIR.TyId → Nat) (l : LocalLayout) : Nat :=
  (if l.layout.isSized then 0 else maxSized + 1) + layoutOrder typeRank l + 1

/-- `visitOrder` descent strictly decreases `visitFuelBound`. -/
theorem visitFuelBound_lt (maxSized : Nat) (typeRank : MIR.TyId → Nat) (parent child : LocalLayout)
    (hsized : parent.layout.isSized = false → child.layout.isSized = true →
      layoutOrder typeRank child ≤ maxSized)
    (hlt : VisitOrderLt (visitOrder typeRank child) (visitOrder typeRank parent)) :
    visitFuelBound maxSized typeRank child < visitFuelBound maxSized typeRank parent := by
  unfold visitFuelBound
  unfold VisitOrderLt visitOrder at hlt
  rw [Prod.lex_def] at hlt
  cases hc : child.layout.isSized <;> cases hp : parent.layout.isSized <;>
    simp only [hc, hp, Bool.false_eq_true, ↓reduceIte] at hlt ⊢
  · omega
  · omega
  · have := hsized hp hc
    omega
  · omega

private theorem goodGuard_visitGuard (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool)
    (place : RuntimePlace P) (k : Session P → RuntimePlace P → M S (Session P)) :
    goodGuard typeRank good place (visitGuard typeRank place k) = goodGuard typeRank good place k := by
  funext s child
  unfold goodGuard visitGuard
  by_cases hc : good child = true ∧
      VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
  · simp only [hc, and_self, ↓reduceIte]
  · simp only [hc, ↓reduceIte]

/-- Under `VisitHooksDescend` and `UnionHooksDescend`, the unmodified vendored
`ValidityVisitor.visit` equals the structural `realVisitGuarded` at every fuel budget (including
identical fuel exhaustion on small budgets). -/
theorem vendored_visit_eq_guarded [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad)
    (c : C) (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool)
    (hd : VisitHooksDescend h c typeRank good goodU)
    (hdU : UnionHooksDescend h c typeRank (fun l => goodU l = true)) :
    ∀ (fuel : Nat) (session : Session P) (place : RuntimePlace P), good place = true →
      ValidityVisitor.visit h c fuel session place = realVisitGuarded h c typeRank fuel session place
  | 0, _, _, _ => by rw [ValidityVisitor.visit.eq_1]; rfl
  | fuel + 1, session, place, hp => by
    rw [vendored_visit_succ, ← hd place hp]
    have hk : goodGuard typeRank good place (ValidityVisitor.visit h c fuel) =
        goodGuard typeRank good place (realVisitGuarded h c typeRank fuel) := by
      funext s child
      unfold goodGuard
      by_cases hc : good child = true ∧
          VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
      · simp only [hc, and_self, ↓reduceIte]
        exact vendored_visit_eq_guarded h c typeRank good goodU hd hdU fuel s child hc.1
      · simp only [hc, ↓reduceIte]
    have hu : unionGuard goodU place
          (ValidityVisitor.unionRanges h c fuel place.layout Size.ZERO .empty) =
        unionGuard goodU place
          (realUnionRangesGuarded h c typeRank fuel place.layout Size.ZERO .empty) := by
      unfold unionGuard
      by_cases hg : goodU place.layout = true
      · simp only [hg, ↓reduceIte]
        exact vendored_unionRanges_eq_guarded h c typeRank _ hdU fuel place.layout Size.ZERO
          .empty hg
      · simp only [hg, Bool.false_eq_true, ↓reduceIte]
    rw [hk, hu, ← goodGuard_visitGuard, hd place hp]
    rfl

/-- Under `VisitHooksDescend`, `realVisitGuarded` equals `realVisitNoFuel` above
`visitFuelBound`, including unsized roots (`dyn Trait` unpacking) when `maxSized` bounds the
`good` sized places reachable from `good` unsized ones. -/
theorem realVisitGuarded_eq_noFuel [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool)
    (goodU : LocalLayout → Bool) (hd : VisitHooksDescend h c typeRank good goodU) (maxSized : Nat)
    (hmax : ∀ parent child : RuntimePlace P, good parent = true → good child = true →
      parent.layout.layout.isSized = false → child.layout.layout.isSized = true →
      layoutOrder typeRank child.layout ≤ maxSized) :
    ∀ (fuel : Nat) (session : Session P) (place : RuntimePlace P), good place = true →
      visitFuelBound maxSized typeRank place.layout < fuel →
      realVisitGuarded h c typeRank fuel session place = realVisitNoFuel h c typeRank session place
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, session, place, hp, hlt => by
    have hu : layoutOrder typeRank place.layout < fuel := by
      unfold visitFuelBound at hlt; split at hlt <;> omega
    rw [realVisitNoFuel_eq]
    simp only [realVisitGuarded]
    rw [realUnionRangesGuarded_eq_noFuel h c typeRank fuel place.layout Size.ZERO .empty hu,
      ← hd place hp (visitGuard typeRank place (realVisitGuarded h c typeRank fuel)),
      ← hd place hp (visitGuard typeRank place (realVisitNoFuel h c typeRank)),
      goodGuard_visitGuard, goodGuard_visitGuard]
    congr 1
    funext s child
    unfold goodGuard
    by_cases hc : good child = true ∧
        VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
    · simp only [hc, and_self, ↓reduceIte]
      exact realVisitGuarded_eq_noFuel h c typeRank good goodU hd maxSized hmax fuel s child hc.1
        (Nat.lt_of_lt_of_le (visitFuelBound_lt maxSized typeRank place.layout child.layout
          (hmax place child hp hc.1) hc.2) (Nat.le_of_lt_succ hlt))
    · simp only [hc, ↓reduceIte]

/-- **Real vendored `visit` adequacy (`lean-miri#90`).** Under the one-step hook descent
hypotheses, the unmodified vendored `Miri.Interpreter.ValidityVisitor.visit` agrees identically
with the fuel-free `realVisitNoFuel` whenever `fuel > visitFuelBound maxSized typeRank root`. -/
theorem vendored_visit_eq_noFuel [PointerProvenance P] [DecidableEq P] (h : Hooks P S C E F A Pad)
    (c : C) (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool)
    (hd : VisitHooksDescend h c typeRank good goodU)
    (hdU : UnionHooksDescend h c typeRank (fun l => goodU l = true)) (maxSized : Nat)
    (hmax : ∀ parent child : RuntimePlace P, good parent = true → good child = true →
      parent.layout.layout.isSized = false → child.layout.layout.isSized = true →
      layoutOrder typeRank child.layout ≤ maxSized)
    (fuel : Nat) (session : Session P) (place : RuntimePlace P) (hp : good place = true)
    (hfuel : visitFuelBound maxSized typeRank place.layout < fuel) :
    ValidityVisitor.visit h c fuel session place = realVisitNoFuel h c typeRank session place :=
  (vendored_visit_eq_guarded h c typeRank good goodU hd hdU fuel session place hp).trans
    (realVisitGuarded_eq_noFuel h c typeRank good goodU hd maxSized hmax fuel session place hp hfuel)

/-- Sized-root form of `vendored_visit_eq_noFuel` (no `maxSized` side condition): the canonical
vendored fuel is `layoutOrder typeRank root + 2`. -/
theorem vendored_visit_eq_noFuel_of_sized [PointerProvenance P] [DecidableEq P]
    (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool)
    (goodU : LocalLayout → Bool) (hd : VisitHooksDescend h c typeRank good goodU)
    (hdU : UnionHooksDescend h c typeRank (fun l => goodU l = true))
    (fuel : Nat) (session : Session P) (place : RuntimePlace P) (hp : good place = true)
    (hs : place.layout.layout.isSized = true)
    (hfuel : layoutOrder typeRank place.layout + 1 < fuel) :
    ValidityVisitor.visit h c fuel session place = realVisitNoFuel h c typeRank session place :=
  (vendored_visit_eq_guarded h c typeRank good goodU hd hdU fuel session place hp).trans
    (realVisitGuarded_eq_noFuel_of_sized h c typeRank fuel session place hs hfuel)

end

/-! ### `VisitHooksDescend` is satisfiable: the deep `.pattern` chain at every depth -/

/-- The `deepPatternHooks` chain invariant: memory places with the `wrapperLayout` layout. -/
def deepGood (p : RuntimePlace CtfeProvenance) : Bool :=
  match p.ref with
  | .memory _ => decide (p.layout.layout = wrapperLayout)
  | .local .. => false

private theorem eb_pure {σ ε α β : Type} (a : α) (f : α → EStateM ε σ β) :
    EStateM.bind (EStateM.pure a) f = f a := rfl

private theorem eb_throw {σ ε α β : Type} (e : ε) (f : α → EStateM ε σ β) :
    EStateM.bind (throw e : EStateM ε σ α) f = throw e := rfl

private theorem eb_assoc {σ ε α β γ : Type} (m : EStateM ε σ α) (f : α → EStateM ε σ β)
    (g : β → EStateM ε σ γ) :
    EStateM.bind (EStateM.bind m f) g = EStateM.bind m (fun a => EStateM.bind (f a) g) := by
  funext s; simp only [EStateM.bind]; cases m s <;> rfl

private theorem goodGuard_deep (n : Nat) (r : RuntimePlaceRef CtfeProvenance)
    (m : MemPlace CtfeProvenance)
    (k : Session CtfeProvenance → RuntimePlace CtfeProvenance → M Unit (Session CtfeProvenance))
    (s : Session CtfeProvenance) :
    goodGuard id deepGood ⟨r, ⟨n + 1, wrapperLayout⟩⟩ k s ⟨.memory m, ⟨n, wrapperLayout⟩⟩ =
      k s ⟨.memory m, ⟨n, wrapperLayout⟩⟩ := by
  unfold goodGuard
  rw [ite_eq_left_iff.mpr]
  intro hn
  exfalso; apply hn
  refine ⟨by simp [deepGood], ?_⟩
  unfold VisitOrderLt visitOrder layoutOrder layoutPhase
  rw [Prod.lex_def]
  simp [wrapperLayout]

/-- **Non-vacuity of `VisitHooksDescend`.** The `deepPatternHooks` (`.pattern (ty - 1)` at every
`ty > 0`, `.foreign` leaf at `ty = 0`) descend at every depth, for every session and memory place. -/
theorem deepPattern_visitHooksDescend :
    VisitHooksDescend deepPatternHooks () id deepGood (fun _ => false) := by
  intro place hp k u session
  obtain ⟨ref, ty, lay⟩ := place
  cases ref with
  | «local» => simp [deepGood] at hp
  | memory m =>
  have hW : lay = wrapperLayout := by simpa [deepGood] using hp
  subst hW
  unfold visitStep
  cases ty with
  | zero =>
    funext σ
    simp [deepPatternHooks, minimalValidityHooks, primitive, bind, EStateM.bind, pure,
      EStateM.pure]
  | succ n =>
    cases hadd : m.ptr.offset.add Size.ZERO <;>
    simp [deepPatternHooks, minimalValidityHooks, primitive, bind, pure, eb_pure, eb_throw,
      eb_assoc, PlaceDynamic.offsetWithMeta, goodGuard_deep, hadd]

/-- `UnionHooksDescend` holds vacuously for the empty union invariant. -/
theorem deepPattern_unionHooksDescend :
    UnionHooksDescend deepPatternHooks () id (fun l => (fun _ => false : LocalLayout → Bool) l = true) := by
  intro l hl
  exact absurd hl (by simp)

/-- **General-depth instance of real vendored `visit` adequacy.** For every depth `n`, memory
place, session, and vendored fuel `> 3 * n + 2`, the unmodified vendored `ValidityVisitor.visit` on
the deep `.pattern` chain agrees with the fuel-free `realVisitNoFuel`. -/
theorem deepPattern_vendored_visit_eq_noFuel (n fuel : Nat) (m : MemPlace CtfeProvenance)
    (session : Session CtfeProvenance) (hfuel : 3 * n + 2 < fuel) :
    ValidityVisitor.visit deepPatternHooks () fuel session ⟨.memory m, ⟨n, wrapperLayout⟩⟩ =
      realVisitNoFuel deepPatternHooks () id session ⟨.memory m, ⟨n, wrapperLayout⟩⟩ :=
  vendored_visit_eq_noFuel_of_sized deepPatternHooks () id deepGood (fun _ => false)
    deepPattern_visitHooksDescend deepPattern_unionHooksDescend fuel session _
    (by simp [deepGood]) rfl
    (by simp [layoutOrder, layoutPhase, wrapperLayout]; omega)

/-- `true` iff a validation result is an `.invalidProgram` error with the given message. -/
def resultInvalidProgram {σ β : Type} (message : String) : EStateM.Result StepError σ β → Bool
  | .error (.invalidProgram m) _ => m == message
  | _ => false

/-- A self-looping `.pattern` chain (`classify ty = .pattern ty`): the projected child never
descends. -/
def selfPatternHooks : Hooks CtfeProvenance Unit Unit Unit Unit Unit Unit :=
  minimalValidityHooks (fun parent _ => parent) (fun ty => ⟨ty, wrapperLayout⟩)
    (fun ty => .pattern ty)

/-- **Negative witness on the real vendored `visit`.** On a non-descending projection hook the
fuel-free `realVisitNoFuel` deterministically rejects with `.invalidProgram "validity projection
does not descend"`, whereas the vendored fuelled `visit` merely exhausts its fuel (`151`). -/
theorem selfPattern_noFuel_rejects_vendored_exhausts :
    let root : RuntimePlace CtfeProvenance :=
      ⟨.memory ⟨⟨Size.ZERO, none⟩, .none, none⟩, ⟨7, wrapperLayout⟩⟩
    let init : Session CtfeProvenance :=
      { path := ⟨"Root", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    resultInvalidProgram "validity projection does not descend"
        (realVisitNoFuel selfPatternHooks () id init root ()) = true ∧
      resultExhausted "validity traversal fuel"
        (ValidityVisitor.visit selfPatternHooks () 151 init root ()) = true := by
  refine ⟨?_, by decide +kernel⟩
  rw [realVisitNoFuel_eq]
  decide +kernel


/-! ### Unconditional `ω · 2` structural companion (`realVisitLexRank`, `Classical.choice`-free)

`realVisitRank` above budgets `layoutOrder + 2`, which suffices only on sized roots (`hs : isSized = true`):
when an unsized `dyn Trait` root (`isSized = false`) unpacks via `VTable.unpackDynTrait` to a concrete
sized implementor of higher `typeRank` and deeper field chain, `realVisitRank` falsely exhausts fuel.
Matching `VisitLexWalk.walkRank`, `realVisitLexRank` uses nested structural recursion (`Nat.rec` inside
`Nat.rec`, `ω · 2`) together with `realUnionRangesRank`, dynamically budgeting `layoutOrder child + 1`
upon unsized-to-sized transition so `realVisitLexRank_eq_noFuel` holds **unconditionally** on every
place (sized or unsized) while remaining `Classical.choice`-free after `leanprover/lean4#13851`. -/

section LexStructuralAndCongruence
variable {P S C E F A Pad : Type} [PointerProvenance P] [DecidableEq P]

/-- Structural (`Nat.rec`, `Classical.choice`-free) companion for sized subtrees of `realVisitNoFuel`. -/
def realVisitSized (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat) :
    Nat → Session P → RuntimePlace P → M S (Session P)
  | 0, _, _ => throw (.resourceExhaustion "validity traversal fuel")
  | fuel + 1, session, place =>
    visitStep h c (visitGuard typeRank place (realVisitSized h c typeRank fuel))
      (realUnionRangesRank h c typeRank place.layout Size.ZERO .empty) session place

/-- Structural (`Nat.rec`, `Classical.choice`-free) companion for unsized places (`dyn Trait`, slices):
transitions into `realVisitSized (layoutOrder typeRank child.layout + 1)` whenever dynamic unpacking
produces a sized concrete child. -/
def realVisitUnsized (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat) :
    Nat → Session P → RuntimePlace P → M S (Session P)
  | 0, _, _ => throw (.resourceExhaustion "validity traversal fuel")
  | fuel + 1, session, place =>
    visitStep h c
      (visitGuard typeRank place fun s child =>
        if child.layout.layout.isSized then
          realVisitSized h c typeRank (layoutOrder typeRank child.layout + 1) s child
        else
          realVisitUnsized h c typeRank fuel s child)
      (realUnionRangesRank h c typeRank place.layout Size.ZERO .empty) session place

/-- **Unconditional `Classical.choice`-free structural companion of `realVisitNoFuel`** across the
entire `ω · 2` `visitOrder` domain (valid on both sized and unsized roots, any hooks). -/
def realVisitLexRank (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat)
    (session : Session P) (place : RuntimePlace P) : M S (Session P) :=
  if place.layout.layout.isSized then
    realVisitSized h c typeRank (layoutOrder typeRank place.layout + 1) session place
  else
    realVisitUnsized h c typeRank (layoutOrder typeRank place.layout + 1) session place

/-- Sized structural companion agrees with `realVisitNoFuel` whenever `fuel > layoutOrder`. -/
theorem realVisitSized_eq_noFuel (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat) :
    ∀ (fuel : Nat) (session : Session P) (place : RuntimePlace P),
      place.layout.layout.isSized = true → layoutOrder typeRank place.layout < fuel →
      realVisitSized h c typeRank fuel session place = realVisitNoFuel h c typeRank session place
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, session, place, hs, hlt => by
    rw [realVisitNoFuel_eq]
    simp only [realVisitSized, realUnionRangesRank_eq_noFuel]
    congr 1
    funext s child
    unfold visitGuard
    by_cases hc : VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
    · simp only [hc, ↓reduceIte]
      obtain ⟨hcs, hclt⟩ := visitOrder_lt_of_sized_parent typeRank place.layout child.layout hs hc
      exact realVisitSized_eq_noFuel h c typeRank fuel s child hcs (by omega)
    · simp only [hc, ↓reduceIte]

/-- Unsized structural companion agrees with `realVisitNoFuel` whenever `fuel > layoutOrder`. -/
theorem realVisitUnsized_eq_noFuel (h : Hooks P S C E F A Pad) (c : C) (typeRank : MIR.TyId → Nat) :
    ∀ (fuel : Nat) (session : Session P) (place : RuntimePlace P),
      place.layout.layout.isSized = false → layoutOrder typeRank place.layout < fuel →
      realVisitUnsized h c typeRank fuel session place = realVisitNoFuel h c typeRank session place
  | 0, _, _, _, hlt => absurd hlt (Nat.not_lt_zero _)
  | fuel + 1, session, place, hunsz, hlt => by
    rw [realVisitNoFuel_eq]
    simp only [realVisitUnsized, realUnionRangesRank_eq_noFuel]
    congr 1
    funext s child
    unfold visitGuard
    by_cases hc : VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
    · simp only [hc, ↓reduceIte]
      cases hcs : child.layout.layout.isSized
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hclt : layoutOrder typeRank child.layout < layoutOrder typeRank place.layout := by
          unfold VisitOrderLt visitOrder at hc
          rw [Prod.lex_def] at hc
          simp only [hcs, hunsz, Bool.false_eq_true, ↓reduceIte] at hc
          omega
        exact realVisitUnsized_eq_noFuel h c typeRank fuel s child hcs (by omega)
      · simp only [↓reduceIte]
        exact realVisitSized_eq_noFuel h c typeRank _ s child hcs (Nat.lt_succ_self _)
    · simp only [hc, ↓reduceIte]

/-- **Unconditional structural adequacy (`Classical.choice`-free `realVisitLexRank = realVisitNoFuel`)**
for every place (sized or unsized) and every hook instance, with zero side conditions. -/
theorem realVisitLexRank_eq_noFuel (h : Hooks P S C E F A Pad) (c : C)
    (typeRank : MIR.TyId → Nat) (session : Session P) (place : RuntimePlace P) :
    realVisitLexRank h c typeRank session place = realVisitNoFuel h c typeRank session place := by
  unfold realVisitLexRank
  cases hs : place.layout.layout.isSized
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact realVisitUnsized_eq_noFuel h c typeRank _ session place hs (Nat.lt_succ_self _)
  · simp only [↓reduceIte]
    exact realVisitSized_eq_noFuel h c typeRank _ session place hs (Nat.lt_succ_self _)

/-! ### `Anneal.MirFuelFree` `wpCoalBounded` bridges for `RealVisit` -/

/-- **`Anneal.MirFuelFree` bridge for `ValidityVisitor.visit` (general unsized/sized form).**
Whenever `rankCountdown` converges in `fuel` steps from `visitFuelBound maxSized typeRank place.layout`,
the unmodified vendored `ValidityVisitor.visit` agrees identically with `realVisitNoFuel`. -/
theorem vendored_visit_eq_noFuel_of_wpCoalBounded (h : Hooks P S C E F A Pad)
    (c : C) (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool)
    (hd : VisitHooksDescend h c typeRank good goodU)
    (hdU : UnionHooksDescend h c typeRank (fun l => goodU l = true)) (maxSized : Nat)
    (hmax : ∀ parent child : RuntimePlace P, good parent = true → good child = true →
      parent.layout.layout.isSized = false → child.layout.layout.isSized = true →
      layoutOrder typeRank child.layout ≤ maxSized)
    (fuel : Nat) (session : Session P) (place : RuntimePlace P) (hp : good place = true) (s : PUnit)
    (hconv : Anneal.ITreeWP.wpCoalBounded fuel emptyWP rankCountdown (fun _ _ => True)
      (visitFuelBound maxSized typeRank place.layout) s) :
    ValidityVisitor.visit h c fuel session place = realVisitNoFuel h c typeRank session place :=
  vendored_visit_eq_noFuel h c typeRank good goodU hd hdU maxSized hmax fuel session place hp
    ((rankCountdown_converges_iff _ _ s).mp hconv)

/-- **`Anneal.MirFuelFree` bridge for `ValidityVisitor.visit` (sized-root form).** -/
theorem vendored_visit_eq_noFuel_of_sized_wpCoalBounded (h : Hooks P S C E F A Pad)
    (c : C) (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool)
    (hd : VisitHooksDescend h c typeRank good goodU)
    (hdU : UnionHooksDescend h c typeRank (fun l => goodU l = true))
    (fuel : Nat) (session : Session P) (place : RuntimePlace P) (hp : good place = true)
    (hs : place.layout.layout.isSized = true) (s : PUnit)
    (hconv : Anneal.ITreeWP.wpCoalBounded fuel emptyWP rankCountdown (fun _ _ => True)
      (layoutOrder typeRank place.layout + 1) s) :
    ValidityVisitor.visit h c fuel session place = realVisitNoFuel h c typeRank session place :=
  vendored_visit_eq_noFuel_of_sized h c typeRank good goodU hd hdU fuel session place hp hs
    ((rankCountdown_converges_iff _ _ s).mp hconv)

/-! ### Structural decomposition of `VisitHooksDescend` across all 7 projection boundaries -/

/-- Explicit hook-level descent conditions corresponding to the 7 recursive `descend` sites and 1
`unionRanges` hand-off in `ValidityVisitor.visit` (`lean-miri#90` L402–486). -/
structure VisitHookConditions (h : Hooks P S C E F A Pad) (c : C)
    (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool) :
    Prop where
  seqZst : ∀ place, good place = true →
    ∀ elem s₀ s₁ s₂ child s₃,
      h.classify c place.layout.ty s₀ = .ok (.sequence elem) s₁ →
      PlaceDynamic.index h.projection c place 0 s₂ = .ok child s₃ →
      good child = true ∧ VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
  arrayElem : ∀ place, good place = true →
    ∀ stride cnt, place.layout.layout.fields = .Array stride cnt →
    ∀ s₀ elem s₁ off s₂ child s₃,
      h.projection.field c place.layout 0 s₀ = .ok elem s₁ →
      PlaceDynamic.offsetWithMeta h.projection c place off .wrapping .none elem s₂ = .ok child s₃ →
      good child = true ∧ VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
  pattern : ∀ place, good place = true →
    ∀ base s₀ s₁ s₂ lay s₃ s₄ child s₅,
      h.classify c place.layout.ty s₀ = .ok (.pattern base) s₁ →
      h.projection.layoutOf c base s₂ = .ok lay s₃ →
      PlaceDynamic.offsetWithMeta h.projection c place Size.ZERO .wrapping .none lay s₄ = .ok child s₅ →
      good child = true ∧ VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
  dynamic : ∀ place, good place = true →
    ∀ expected s₀ s₁ s₂ op s₃ s₄ inner s₅ memory,
      h.classify c place.layout.ty s₀ = .ok (.dynamic expected) s₁ →
      h.toOp c place s₂ = .ok op s₃ →
      VTable.unpackDynTrait h.vtable c op expected s₄ = .ok inner s₅ →
      inner.op = .indirect memory →
      good ⟨.memory memory, inner.layout⟩ = true ∧
        VisitOrderLt (visitOrder typeRank inner.layout) (visitOrder typeRank place.layout)
  box : ∀ place, good place = true →
    ∀ s₀ s₁ s₂ ptr allocator s₃,
      h.classify c place.layout.ty s₀ = .ok .box s₁ →
      h.projectBox c place s₂ = .ok (ptr, allocator) s₃ →
      good allocator = true ∧
        VisitOrderLt (visitOrder typeRank allocator.layout) (visitOrder typeRank place.layout)
  arbitrary : ∀ place, good place = true →
    ∀ offsets order, place.layout.layout.fields = .Arbitrary offsets order →
    ∀ idx s₀ child s₁,
      PlaceDynamic.field h.projection c place idx s₀ = .ok child s₁ →
      good child = true ∧ VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
  multiple : ∀ place, good place = true →
    ∀ tag enc tf vs, place.layout.layout.variants = .Multiple tag enc tf vs →
    ∀ s₀ op s₁ s₂ variant s₃ s₄ child s₅,
      h.toOp c place s₀ = .ok op s₁ →
      Discriminant.readDiscriminant h.discriminant c op s₂ = .ok variant s₃ →
      PlaceDynamic.downcast h.projection c place variant s₄ = .ok child s₅ →
      good child = true ∧ VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)
  union : ∀ place, good place = true →
    ∀ cnt, place.layout.layout.fields = .Union cnt → goodU place.layout = true

private theorem bind_congr_ok' {σ α β : Type} {m : M σ α} {f g : α → M σ β}
    (hfg : ∀ s a s', m s = .ok a s' → f a s' = g a s') :
    (m >>= f) = (m >>= g) := by
  funext s
  simp only [bind, EStateM.bind]
  cases hm : m s with
  | error e s' => rfl
  | ok a s' => exact hfg s a s' hm

private theorem bind_eq_bind' {σ α β : Type} {m₁ m₂ : M σ α} {k₁ k₂ : α → M σ β}
    (hm : m₁ = m₂) (hk : ∀ a, k₁ a = k₂ a) :
    (m₁ >>= k₁) = (m₂ >>= k₂) := by
  rw [hm]
  have : k₁ = k₂ := by funext a; exact hk a
  rw [this]

private theorem have_eq_both {α β : Type} (f₁ f₂ : α → β) (v₁ v₂ : α)
    (hv : v₁ = v₂) (hf : ∀ x, f₁ x = f₂ x) :
    f₁ v₁ = f₂ v₂ :=
  congr (funext hf) hv

private theorem have_eq_val {α β : Type} (f : α → β) (v₁ v₂ : α)
    (hv : v₁ = v₂) : f v₁ = f v₂ :=
  congrArg f hv

private theorem have_eq_body {α β : Type} (f₁ f₂ : α → β) (v : α)
    (hf : ∀ x, f₁ x = f₂ x) : f₁ v = f₂ v :=
  congrFun (funext hf) v

open Lean Meta Elab Tactic in
local elab "peel_have" : tactic => withMainContext do
  let goal ← getMainGoal
  let tgt ← instantiateMVars (← goal.getType)
  let some (_, lhs0, rhs0) := tgt.eq? | throwError "peel_have: expected equality goal"
  let (lhs, rhs) ← withConfig (fun cfg => { cfg with zeta := false, zetaHave := false, zetaDelta := false }) do
    pure (← whnf lhs0, ← whnf rhs0)
  let .letE nm ty v₁ b₁ _ := lhs | throwError "peel_have: LHS is not a `have`, got:\n{lhs}"
  let .letE _ _ v₂ b₂ _ := rhs | throwError "peel_have: RHS is not a `have`, got:\n{rhs}"
  let f₁ := mkLambda nm .default ty b₁
  let f₂ := mkLambda nm .default ty b₂
  let fEq ← withLocalDeclD nm ty fun x => do
    mkForallFVars #[x] (← mkEq (b₁.instantiate1 x) (b₂.instantiate1 x))
  if v₁ == v₂ then
    let subF ← mkFreshExprMVar fEq
    let pf ← mkAppM ``have_eq_body #[f₁, f₂, v₁, subF]
    goal.assign pf
    replaceMainGoal [subF.mvarId!]
  else if f₁ == f₂ then
    let subV ← mkFreshExprMVar (← mkEq v₁ v₂)
    let pf ← mkAppM ``have_eq_val #[f₁, v₁, v₂, subV]
    goal.assign pf
    replaceMainGoal [subV.mvarId!]
  else
    let subV ← mkFreshExprMVar (← mkEq v₁ v₂)
    let subF ← mkFreshExprMVar fEq
    let pf ← mkAppM ``have_eq_both #[f₁, f₂, v₁, v₂, subV, subF]
    goal.assign pf
    replaceMainGoal [subV.mvarId!, subF.mvarId!]

omit [PointerProvenance P] [DecidableEq P] in
private theorem goodGuard_of_descends (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool)
    (place child : RuntimePlace P) (k : Session P → RuntimePlace P → M S (Session P))
    (session : Session P)
    (hcd : good child = true ∧ VisitOrderLt (visitOrder typeRank child.layout) (visitOrder typeRank place.layout)) :
    goodGuard typeRank good place k session child = k session child := by
  unfold goodGuard
  simp only [hcd, and_self, ↓reduceIte]

/-- **General body-congruence theorem for `ValidityVisitor.visit`.** Discharges `VisitHooksDescend`
across all 7 projection boundaries (`sequence`, `pattern`, `dynamic`, `box`, `Arbitrary`, `Array`,
`Multiple`) and the `.Union` `unionRanges` hand-off from `VisitHookConditions`, without requiring
callers to unfold `visitStep` (`Classical.choice`-free). -/
theorem visitHooksDescend_of_conditions (h : Hooks P S C E F A Pad) (c : C)
    (typeRank : MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool)
    (hcond : VisitHookConditions h c typeRank good goodU) :
    VisitHooksDescend h c typeRank good goodU := by
  intro place hp k u session
  have harr : ∀ stride cnt, place.layout.layout.fields = .Array stride cnt →
      ∀ (stride' : Size) elem0 s₀ s₁, h.projection.field c place.layout 0 s₀ = .ok elem0 s₁ →
      (fun (index : Nat) (sess : Session P) => do
        let offset ← sizeResult (stride'.mul (UInt64.ofNat index))
        let child ← PlaceDynamic.offsetWithMeta h.projection c place offset .wrapping .none elem0
        let path := sess.path
        let sess ← goodGuard typeRank good place k { sess with path := path.push (.arrayElem index) } child
        pure (ForInStep.yield { sess with path })) =
      (fun (index : Nat) (sess : Session P) => do
        let offset ← sizeResult (stride'.mul (UInt64.ofNat index))
        let child ← PlaceDynamic.offsetWithMeta h.projection c place offset .wrapping .none elem0
        let path := sess.path
        let sess ← k { sess with path := path.push (.arrayElem index) } child
        pure (ForInStep.yield { sess with path })) := by
    intro stride cnt hfs stride' elem0 s₀ s₁ hfield0
    funext index sess
    apply bind_eq_bind' rfl; intro offset
    apply bind_congr_ok'; intro s₂ child s₃ hoff
    rw [goodGuard_of_descends _ _ _ _ _ _
      (hcond.arrayElem place hp stride cnt hfs s₀ elem0 s₁ offset s₂ child s₃ hfield0 hoff)]
  have harb : ∀ offsets order, place.layout.layout.fields = .Arbitrary offsets order →
      (fun (index : Nat) (sess : Session P) => do
        let child ← PlaceDynamic.field h.projection c place index
        let path := sess.path
        let sess ← goodGuard typeRank good place k { sess with path := path.push (← h.fieldPath c place.layout index child.layout.ty) } child
        pure (ForInStep.yield { sess with path })) =
      (fun (index : Nat) (sess : Session P) => do
        let child ← PlaceDynamic.field h.projection c place index
        let path := sess.path
        let sess ← k { sess with path := path.push (← h.fieldPath c place.layout index child.layout.ty) } child
        pure (ForInStep.yield { sess with path })) := by
    intro offsets order hfs
    funext index sess
    apply bind_congr_ok'; intro s₀ child s₁ hfield
    refine congrFun (bind_eq_bind' rfl fun fpath => ?_) s₁
    rw [goodGuard_of_descends _ _ _ _ _ _
      (hcond.arbitrary place hp offsets order hfs index s₀ child s₁ hfield)]
  unfold visitStep
  apply bind_congr_ok'; intro s₀ kind s₁ hcls
  apply congrFun
  apply bind_eq_bind' rfl
  rintro (_ | session)
  · peel_have; intro session
    peel_have; funext _
    peel_have; intro jpEpi
    cases kind with
    | string => rfl
    | sequence elem =>
      apply bind_congr_ok'; intro s₂ elemKind s₃ _
      by_cases hnum : (elemKind == .integer || elemKind == .float) = true
      · simp only [hnum, ↓reduceIte]
      · simp only [hnum, Bool.false_eq_true, ↓reduceIte]
        refine congrFun (bind_congr_ok' fun s₄ elemLay s₅ _ => ?_) s₃
        cases elemLay.layout.isZst
        · simp only [Bool.false_eq_true, ↓reduceIte]
          cases hfs : place.layout.layout.fields with
          | Primitive | Union _ | Arbitrary _ _ => rfl
          | Array stride cnt =>
            apply congrFun
            apply bind_eq_bind' rfl; intro stride'
            apply bind_eq_bind' rfl; intro len
            apply bind_congr_ok'; intro s₆ elem0 s₇ hfield0
            refine congrFun (bind_eq_bind' rfl fun endOff => ?_) s₇
            apply bind_eq_bind' rfl; intro _
            rw [harr stride cnt hfs stride' elem0 s₆ s₇ hfield0]
        · simp only [↓reduceIte]
          apply congrFun
          apply bind_eq_bind' rfl; intro len
          by_cases hgt : len > 0
          · simp only [hgt, ↓reduceIte]
            apply bind_congr_ok'; intro s₆ child s₇ hidx
            rw [goodGuard_of_descends _ _ _ _ _ _ (hcond.seqZst place hp elem s₀ s₁ s₆ child s₇ hcls hidx)]
          · simp only [hgt, ↓reduceIte]
    | pattern base =>
      apply bind_congr_ok'; intro s₂ lay s₃ hlay
      by_cases hmis : (!lay.layout.isSized || !place.layout.layout.isSized || lay.layout.size != place.layout.layout.size) = true
      · simp only [hmis, ↓reduceIte]; rfl
      · simp only [hmis, Bool.false_eq_true, ↓reduceIte]
        refine congrFun (bind_congr_ok' fun s₄ child s₅ hoff => ?_) s₃
        rw [goodGuard_of_descends _ _ _ _ _ _ (hcond.pattern place hp base s₀ s₁ s₂ lay s₃ s₄ child s₅ hcls hlay hoff)]
    | dynamic expected =>
      peel_have; intro oldMayDangle
      peel_have; funext _ session
      peel_have; intro _
      apply bind_congr_ok'; intro s₂ op s₃ htoOp
      refine congrFun (bind_congr_ok' fun s₄ inner s₅ hunpack => ?_) s₃
      cases hop : inner.op with
      | immediate _ => rfl
      | indirect memory =>
        apply congrFun
        peel_have; intro path
        apply bind_eq_bind' rfl; intro fpath
        rw [goodGuard_of_descends _ _ _ _ _ _
          (hcond.dynamic place hp expected s₀ s₁ s₂ op s₃ s₄ inner s₅ memory hcls htoOp hunpack hop)]
    | box =>
      peel_have; intro oldMayDangle
      peel_have; funext _ session
      peel_have; intro _
      simp only [beq_self_eq_true, ↓reduceIte]
      apply bind_congr_ok'; intro s₂ ⟨ptr, allocator⟩ s₃ hbox
      refine congrFun (bind_eq_bind' rfl fun sess1 => ?_) s₃
      apply bind_eq_bind' rfl; intro fpath
      rw [goodGuard_of_descends _ _ _ _ _ _ (hcond.box place hp s₀ s₁ s₂ ptr allocator s₃ hcls hbox)]
    | boolean | character | integer | float | functionPointer | never | foreign | functionDefinition
    | rawPointer _ _ | reference _ | unsafeBinder | invalid | aggregate _ _ _ =>
      (peel_have; intro oldMayDangle
       peel_have; funext _ session
       peel_have; intro _
       peel_have
       · funext _ sess
         cases hvs : place.layout.layout.variants with
         | Empty | Single _ => rfl
         | Multiple tag enc tf vs =>
           apply bind_congr_ok'; intro s₂ op s₃ htoOp
           refine congrFun (bind_congr_ok' fun s₄ variant s₅ hdiscr => ?_) s₃
           refine congrFun (bind_congr_ok' fun s₆ child s₇ hdown => ?_) s₅
           refine congrFun (bind_eq_bind' rfl fun vpath => ?_) s₇
           rw [goodGuard_of_descends _ _ _ _ _ _
             (hcond.multiple place hp tag enc tf vs hvs s₂ op s₃ s₄ variant s₅ s₆ child s₇ htoOp hdiscr hdown)]
       · intro jpVar
         cases hfs : place.layout.layout.fields with
         | Primitive => rfl
         | Union cnt =>
           have hu : unionGuard goodU place u = u := by
             unfold unionGuard; simp only [hcond.union place hp cnt hfs, ↓reduceIte]
           simp only [hu]
         | Arbitrary offsets order =>
           rw [harb offsets order hfs]
         | Array stride cnt =>
           apply bind_eq_bind' rfl; intro len
           apply bind_congr_ok'; intro s₂ elem0 s₃ hfield0
           refine congrFun (bind_eq_bind' rfl fun endOff => ?_) s₃
           apply bind_eq_bind' rfl; intro _
           rw [harr stride cnt hfs stride elem0 s₂ s₃ hfield0])
  · rfl

/-! ### Fuel-free `validatePlace` and `constValidatePlace` (`lean-miri#90` LIFO pointee drain) -/

private def resetPaddingMirrored (h : Hooks P S C E F A Pad) (c : C) (session : Session P)
    (place : RuntimePlace P) : M S Unit := do
  let some ranges := session.dataBytes | return
  let memory ← forceAllocation h.projection.place c place
  let dynamic ← h.sizeAndAlign c memory
  let size := (dynamic.getD (memory.layout.layout.size, memory.layout.layout.align.abi)).1
  let start := memory.mplace.ptr.offset
  if ranges.toArray == #[allocRange start size] then return
  let some handle ← h.beginPadding c memory size | return
  let writes ← liftResult ((paddingWrites ranges start size).mapError fun error => .invalidProgram s!"padding: {repr error}")
  for range in writes do h.writePadding c handle range

/-- **Fuel-free `constValidatePlace` (`lean-miri#90` L787–797)** over `realVisitNoFuel`. As in
`lean-miri#90` (`visit h c (h.typeRank (← get)) …`), the Schema 17 rank map is read from the machine
state at the visit site (`typeRankOf (← get)`), not fixed up front. -/
def realConstValidatePlaceNoFuel (h : Hooks P S C E F A Pad) (c : C)
    (typeRankOf : S → MIR.TyId → Nat) (place : RuntimePlace P) (path : ValidationPath)
    (tracking : RefTracking (Key P) ValidationPath) (mode : CtfeMode) :
    M S (RefTracking (Key P) ValidationPath) := h.withGhostValidation do
  let session : Session P :=
    { path, flags := ⟨false, false⟩, ctfeMode := some mode, refTracking := some tracking, dataBytes := none }
  let session ← realVisitNoFuel h c (typeRankOf (← get)) session place
  match session.refTracking with
  | some tracking => return tracking
  | none => throw (.invalidProgram "const validation lost tracker")

/-- **`Classical.choice`-free structural companion of `realConstValidatePlaceNoFuel`** via `realVisitLexRank`. -/
def realConstValidatePlaceLexRank (h : Hooks P S C E F A Pad) (c : C)
    (typeRankOf : S → MIR.TyId → Nat) (place : RuntimePlace P) (path : ValidationPath)
    (tracking : RefTracking (Key P) ValidationPath) (mode : CtfeMode) :
    M S (RefTracking (Key P) ValidationPath) := h.withGhostValidation do
  let session : Session P :=
    { path, flags := ⟨false, false⟩, ctfeMode := some mode, refTracking := some tracking, dataBytes := none }
  let session ← realVisitLexRank h c (typeRankOf (← get)) session place
  match session.refTracking with
  | some tracking => return tracking
  | none => throw (.invalidProgram "const validation lost tracker")

/-- Unconditional equality between `Classical.choice`-free `realConstValidatePlaceLexRank` and
`realConstValidatePlaceNoFuel`. -/
theorem realConstValidatePlaceLexRank_eq_noFuel (h : Hooks P S C E F A Pad) (c : C)
    (typeRankOf : S → MIR.TyId → Nat) (place : RuntimePlace P) (path : ValidationPath)
    (tracking : RefTracking (Key P) ValidationPath) (mode : CtfeMode) :
    realConstValidatePlaceLexRank h c typeRankOf place path tracking mode =
      realConstValidatePlaceNoFuel h c typeRankOf place path tracking mode := by
  unfold realConstValidatePlaceLexRank realConstValidatePlaceNoFuel
  simp only [realVisitLexRank_eq_noFuel]

/-- **Real vendored `constValidatePlace` adequacy.** Whenever, for every machine state `σ` the
rank map `typeRankOf σ` may be read in, the hooks descend and
`fuel > visitFuelBound maxSized (typeRankOf σ) place.layout`, the unmodified vendored
`Miri.Interpreter.ValidityVisitor.constValidatePlace` agrees identically with
`realConstValidatePlaceNoFuel`. -/
theorem vendored_constValidatePlace_eq_noFuel (h : Hooks P S C E F A Pad) (c : C)
    (typeRankOf : S → MIR.TyId → Nat) (good : RuntimePlace P → Bool) (goodU : LocalLayout → Bool)
    (hd : ∀ σ, VisitHooksDescend h c (typeRankOf σ) good goodU)
    (hdU : ∀ σ, UnionHooksDescend h c (typeRankOf σ) (fun l => goodU l = true)) (maxSized : Nat)
    (hmax : ∀ σ, ∀ parent child : RuntimePlace P, good parent = true → good child = true →
      parent.layout.layout.isSized = false → child.layout.layout.isSized = true →
      layoutOrder (typeRankOf σ) child.layout ≤ maxSized)
    (fuel : Nat) (place : RuntimePlace P) (path : ValidationPath)
    (tracking : RefTracking (Key P) ValidationPath) (mode : CtfeMode)
    (hp : good place = true)
    (hfuel : ∀ σ, visitFuelBound maxSized (typeRankOf σ) place.layout < fuel) :
    ValidityVisitor.constValidatePlace h c fuel place path tracking mode =
      realConstValidatePlaceNoFuel h c typeRankOf place path tracking mode := by
  have hv : ∀ (σ : S) (session : Session P),
      realVisitNoFuel h c (typeRankOf σ) session place =
        ValidityVisitor.visit h c fuel session place := fun σ session =>
    (vendored_visit_eq_noFuel h c (typeRankOf σ) good goodU (hd σ) (hdU σ) maxSized (hmax σ)
      fuel session place hp (hfuel σ)).symm
  unfold ValidityVisitor.constValidatePlace realConstValidatePlaceNoFuel
  simp only [hv]
  rfl

/-- **Fuel-free `validatePlace` (`lean-miri#90` L746–784)**: validates the root place via
`realVisitNoFuel`, then drains tracked pointees in LIFO order via `drainPointees` (`todo.reverse`)
under `pointeeSession` without arbitrary `"recursive validity tracker fuel"`. As in `lean-miri#90`,
the rank map is re-read from the current machine state (`typeRankOf (← get)`) at the root visit and
again at *each* pointee visit. -/
def realValidatePlaceNoFuel (h : Hooks P S C E F A Pad) (c : C)
    (typeRankOf : S → MIR.TyId → Nat) (place : RuntimePlace P) (recursive reset : Bool) :
    M S Unit := do
  let name ← h.typeName c place.layout.ty
  let initial : Session P := {
    path := ⟨name, #[]⟩, flags := ⟨reset, false⟩, ctfeMode := none
    refTracking := if recursive then some .empty else none, dataBytes := none }
  let session ← h.withGhostValidation do
    let mut session := initial
    if reset then
      if let .indirect _ := (← h.toOp c place).op then session := { session with dataBytes := some .empty }
    session ← realVisitNoFuel h c (typeRankOf (← get)) session place
    resetPaddingMirrored h c session place
    return session
  if recursive then
    let some tracking := session.refTracking | return
    drainPointees tracking fun key path =>
      h.withGhostValidation do
        let child : RuntimePlace P := ⟨.memory key.mplace, key.layout⟩
        let visited ← realVisitNoFuel h c (typeRankOf (← get)) (pointeeSession path) child
        resetPaddingMirrored h c visited child

/-- **`Classical.choice`-free structural companion of `realValidatePlaceNoFuel`** via `realVisitLexRank`. -/
def realValidatePlaceLexRank (h : Hooks P S C E F A Pad) (c : C)
    (typeRankOf : S → MIR.TyId → Nat) (place : RuntimePlace P) (recursive reset : Bool) :
    M S Unit := do
  let name ← h.typeName c place.layout.ty
  let initial : Session P := {
    path := ⟨name, #[]⟩, flags := ⟨reset, false⟩, ctfeMode := none
    refTracking := if recursive then some .empty else none, dataBytes := none }
  let session ← h.withGhostValidation do
    let mut session := initial
    if reset then
      if let .indirect _ := (← h.toOp c place).op then session := { session with dataBytes := some .empty }
    session ← realVisitLexRank h c (typeRankOf (← get)) session place
    resetPaddingMirrored h c session place
    return session
  if recursive then
    let some tracking := session.refTracking | return
    drainPointees tracking fun key path =>
      h.withGhostValidation do
        let child : RuntimePlace P := ⟨.memory key.mplace, key.layout⟩
        let visited ← realVisitLexRank h c (typeRankOf (← get)) (pointeeSession path) child
        resetPaddingMirrored h c visited child

/-- Unconditional equality between `Classical.choice`-free `realValidatePlaceLexRank` and
`realValidatePlaceNoFuel` (both root and LIFO pointee sub-traversals). -/
theorem realValidatePlaceLexRank_eq_noFuel (h : Hooks P S C E F A Pad) (c : C)
    (typeRankOf : S → MIR.TyId → Nat) (place : RuntimePlace P) (recursive reset : Bool) :
    realValidatePlaceLexRank h c typeRankOf place recursive reset =
      realValidatePlaceNoFuel h c typeRankOf place recursive reset := by
  unfold realValidatePlaceLexRank realValidatePlaceNoFuel
  simp only [realVisitLexRank_eq_noFuel]

end LexStructuralAndCongruence

/-! ### Fuelled `RefTracking.next` loop adequacy against `drainPointees` -/

private theorem list_dropLast_snoc {α : Type} :
    ∀ (l : List α) (n : Nat) (hlen : l.length = n + 1),
      l.dropLast ++ [l[n]'(by omega)] = l
  | [], _, hlen => nomatch hlen
  | [x], 0, _ => rfl
  | x :: y :: zs, n + 1, hlen => by
    have hlen' : (y :: zs).length = n + 1 := by simp only [List.length_cons] at hlen ⊢; omega
    show x :: ((y :: zs).dropLast ++ [(y :: zs)[n]'(by omega)]) = x :: y :: zs
    rw [list_dropLast_snoc (y :: zs) n hlen']

/-- Structural (`Nat.rec`, `Classical.choice`-free) *model* of the body of the vendored
`validatePlace` `RefTracking.next` worklist loop (`ValidityVisitor.lean` L543–556), consuming 1 unit
of `"recursive validity tracker fuel"` per popped pointee.

It is a model, not a mirror: the vendored `while continueLoop do …` elaborates to
`Lean.Loop.forIn` / `repeatM`, whose implementation `repeatM.impl` is an `opaque` constant with no
unfolding equations (and pulls `Classical.choice` into `ValidityVisitor.validatePlace`, see the
`#guard_msgs` pin in §8). No theorem can therefore relate the vendored loop's behaviour to anything;
`lean-miri#90`'s replacement `for (key, path) in tracking.todo.reverse do …` is a structural
`forIn` over a finite array, which `drainPointees` mirrors. -/
def drainPointeesFuel {P S : Type} :
    Nat → RefTracking (Key P) ValidationPath → (Key P → ValidationPath → M S Unit) → M S Unit
  | 0, tracking, _ =>
    match tracking.next with
    | none => pure ()
    | some _ => throw (.resourceExhaustion "recursive validity tracker fuel")
  | remaining + 1, tracking, visitPointee =>
    match tracking.next with
    | none => pure ()
    | some ((key, path), tracking') => do
      visitPointee key path
      drainPointeesFuel remaining tracking' visitPointee

/-- Whenever `remaining ≥ tracking.todo.size`, iterative `RefTracking.next` popping agrees
identically with `lean-miri#90`'s fuel-free `drainPointees` (`tracking.todo.reverse.forM`). -/
theorem drainPointeesFuel_eq_drainPointees {P S : Type} :
    ∀ (remaining : Nat) (tracking : RefTracking (Key P) ValidationPath)
      (visitPointee : Key P → ValidationPath → M S Unit),
      tracking.todo.size ≤ remaining →
      drainPointeesFuel remaining tracking visitPointee = drainPointees tracking visitPointee
  | 0, tracking, visitPointee, hrem => by
    have hsz : tracking.todo.size = 0 := Nat.eq_zero_of_le_zero hrem
    have hback : tracking.todo.back? = none := by simp [Array.back?, hsz]
    have hlist : tracking.todo.toList = [] :=
      Array.toList_eq_nil_iff.mpr (Array.size_eq_zero_iff.mp hsz)
    simp [drainPointeesFuel, RefTracking.next, hback, drainPointees, hlist, List.forM_nil]
  | remaining + 1, tracking, visitPointee, hrem => by
    cases hsz : tracking.todo.size with
    | zero =>
      have hback : tracking.todo.back? = none := by simp [Array.back?, hsz]
      have hlist : tracking.todo.toList = [] :=
        Array.toList_eq_nil_iff.mpr (Array.size_eq_zero_iff.mp hsz)
      simp [drainPointeesFuel, RefTracking.next, hback, drainPointees, hlist, List.forM_nil]
    | succ n =>
      have hback_some : tracking.todo.back? = some (tracking.todo[n]'(by omega)) := by
        simp [Array.back?, hsz]
      simp only [drainPointeesFuel, RefTracking.next, hback_some, bind, Option.bind, pure]
      have hpop_sz : tracking.todo.pop.size = n := by simp [Array.size_pop, hsz]
      have hsplit : tracking.todo.toList =
          tracking.todo.pop.toList ++ [tracking.todo[n]'(by omega)] := by
        rw [Array.toList_pop]
        have hlen : tracking.todo.toList.length = n + 1 := by simp [hsz]
        exact (list_dropLast_snoc tracking.todo.toList n hlen).symm
      unfold drainPointees
      rw [hsplit]
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
      change (do
          let _ ← visitPointee (tracking.todo[n]'(by omega)).1 (tracking.todo[n]'(by omega)).2
          drainPointeesFuel remaining { seen := tracking.seen, todo := tracking.todo.pop } visitPointee) =
        (do
          let _ ← visitPointee (tracking.todo[n]'(by omega)).1 (tracking.todo[n]'(by omega)).2
          tracking.todo.pop.toList.reverse.forM fun entry => visitPointee entry.1 entry.2)
      congr 1; funext _
      exact drainPointeesFuel_eq_drainPointees remaining
        { seen := tracking.seen, todo := tracking.todo.pop } visitPointee (by simp [hpop_sz]; omega)

/-- Conversely, when `remaining < tracking.todo.size` and each pointee check succeeds,
`drainPointeesFuel` deterministically fails with `"recursive validity tracker fuel"`. -/
theorem drainPointeesFuel_exhausts_of_lt {P S : Type} :
    ∀ (remaining : Nat) (tracking : RefTracking (Key P) ValidationPath)
      (visitPointee : Key P → ValidationPath → M S Unit) (s : S),
      remaining < tracking.todo.size →
      (∀ k p σ, ∃ σ', visitPointee k p σ = .ok () σ') →
      ∃ s', drainPointeesFuel remaining tracking visitPointee s =
        .error (.resourceExhaustion "recursive validity tracker fuel") s'
  | 0, tracking, _, s, hlt, _ => by
    have _ := hlt
    have hback : tracking.todo.back? = some (tracking.todo[tracking.todo.size - 1]'(by omega)) := by
      simp [Array.back?]
    exact ⟨s, by simp [drainPointeesFuel, RefTracking.next, hback, bind, Option.bind, pure]; rfl⟩
  | remaining + 1, tracking, visitPointee, s, hlt, hok => by
    have hpos : 0 < tracking.todo.size := by omega
    have _ := hpos
    have hback : tracking.todo.back? = some (tracking.todo[tracking.todo.size - 1]'(by omega)) := by
      simp [Array.back?]
    simp only [drainPointeesFuel, RefTracking.next, hback, bind, Option.bind, pure, EStateM.bind]
    obtain ⟨s₁, hs₁⟩ := hok _ _ s
    rw [hs₁]
    exact drainPointeesFuel_exhausts_of_lt remaining
      { seen := tracking.seen, todo := tracking.todo.pop } visitPointee s₁
      (by simp [Array.size_pop]; omega) hok

/-! ### Non-vacuous `RealVisit` witnesses:
1. Unsized `dyn Trait` dynamic unpacking (`VTable.unpackDynTrait`) discharging general `vendored_visit_eq_noFuel`
   and proving `realVisitLexRank` succeeds where sized-only `realVisitRank` falsely exhausts fuel.
2. Same-`TyId` multi-variant enum + aggregate (`Discriminant.readDiscriminant` + `PlaceDynamic.downcast` +
   `PlaceDynamic.field`) descending purely by `layoutPhase` `2 -> 1 -> 0` at constant `typeRank = 0`.
3. 3-reference array LIFO pointee draining (`realValidatePlaceNoFuel`, `#[16, 8, 0]`, `"validation[0]"`)
   mirroring `lean-miri#90` `ConnectedPointerAlignment.lean` L863–906. -/

/-- Canonical test `AllocId = 1` for symbolic vtable and reference witnesses. -/
def witnessAllocId : AllocId := ⟨1, by decide⟩

/-- Canonical `CtfeProvenance` on `witnessAllocId`. -/
def witnessProv : CtfeProvenance :=
  match h : CtfeProvenance.fromAllocId witnessAllocId with
  | .ok p => p
  | .error _ => False.elim (by simp [CtfeProvenance.fromAllocId, witnessAllocId] at h)

/-- Symbolic vtable metadata scalar pointing to `witnessAllocId` at offset `0`. -/
def witnessVTableMeta : MemPlaceMeta CtfeProvenance :=
  .metadata (Scalar.fromPointer RuntimeTargetDataLayout.default.base ⟨Size.ZERO, witnessProv⟩)

/-- Layouts for the unsized `dyn Trait` `RealVisit` witness:
- `ty = 100`: unsized `dyn Trait` (`typeRank 100 = 0`, `isSized = false`, `fields = .Arbitrary #[] #[]`,
  `layoutOrder = 1`, `visitOrder = (1, 1)`),
- `ty = 50, 49, 48`: concrete sized single-field aggregates (`typeRank ty = ty`, `isSized = true`,
  `layoutOrder = 151, 148, 145`),
- `ty = 0`: sized `.Primitive` leaf (`typeRank 0 = 0`, `layoutOrder = 0`, `visitOrder = (0, 0)`). -/
def dynVisitLayout (ty : MIR.TyId) : LocalLayout :=
  if ty == 100 then
    ⟨100, { wrapperLayout with fields := .Arbitrary #[] #[], backendRepr := .Memory (sized := false) }⟩
  else if ty == 0 then
    ⟨0, { wrapperLayout with fields := .Primitive }⟩
  else
    ⟨ty, wrapperLayout⟩

/-- Schema 17 `typeRank` assigning rank `0` to the unsized trait object `ty = 100` and `ty` otherwise. -/
def dynVisitTypeRank (ty : MIR.TyId) : Nat :=
  if ty == 100 then 0 else ty

/-- Concrete `ValidityVisitor.Hooks` exercising `VTable.unpackDynTrait` (`ty = 100 -> ty = 50`)
followed by 3 `.Arbitrary` aggregate field projections (`50 -> 49 -> 48 -> 0`). -/
def dynTraitVisitHooks : Hooks CtfeProvenance Unit Unit Unit Unit Unit Unit :=
  let base := minimalValidityHooks
    (fun parent _ => dynVisitLayout (if parent.ty == 48 then 0 else parent.ty - 1))
    dynVisitLayout
    (fun ty =>
      if ty == 100 then .dynamic 0
      else if ty == 0 then .foreign
      else .aggregate false false false)
  { base with
    fieldPath := fun _ _ idx _ => pure (.field s!"{idx}")
    toOp := fun _ place =>
      match place.ref with
      | .memory m => pure ⟨.indirect m, place.layout⟩
      | .local .. => throw (.invalidProgram "expected memory place")
    vtable := { base.vtable with
      isDynamic := fun _ ty => pure (ty == 100)
      memoryOffset := fun _ baseMem offset _ metaVal =>
        match baseMem.ptr.offset.add offset with
        | .ok off => pure { baseMem with ptr := { baseMem.ptr with offset := off }, metadata := metaVal }
        | .error e => throw (.invalidProgram (reprStr e))
      resolvePointer := fun _ ptr => pure (.ok (witnessAllocId, ptr.offset))
      globalVTable := fun _ _ => pure (some (50, 0))
      predicates := fun _ _ => pure #[]
      normalizePredicate := fun _ p => pure p.id
      layoutOf := fun _ ty => pure (dynVisitLayout ty) } }

/-- Good places for `dynTraitVisitHooks`: zero-offset memory places at `ty ∈ {100, 50, 49, 48, 0}`
with `witnessVTableMeta` at `ty = 100` and `.none` metadata on concrete sized projections. -/
def dynTraitGood (p : RuntimePlace CtfeProvenance) : Bool :=
  match p.ref with
  | .memory ⟨⟨off, _⟩, metaVal, _⟩ =>
    off == Size.ZERO &&
      ((p.layout.ty == 100 && decide (metaVal = witnessVTableMeta)) ||
       ((p.layout.ty == 50 || p.layout.ty == 49 || p.layout.ty == 48 || p.layout.ty == 0) &&
        decide (metaVal = .none))) &&
      decide (p.layout = dynVisitLayout p.layout.ty)
  | .local .. => false

private theorem dyn_field_ok_inv (prov : Option CtfeProvenance) (mis : Option Misalignment)
    (t next : Nat) (ht : t = 50 ∨ t = 49 ∨ t = 48)
    (hnext : (if t == 48 then 0 else t - 1) = next)
    (idx : Nat) (child : RuntimePlace CtfeProvenance)
    (hfield : PlaceDynamic.field dynTraitVisitHooks.projection ()
      ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, dynVisitLayout t⟩ idx () = .ok child ()) :
    child = ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, dynVisitLayout next⟩ := by
  subst hnext
  have hstep : ∀ s, s = 50 ∨ s = 49 ∨ s = 48 →
      PlaceDynamic.field dynTraitVisitHooks.projection ()
        ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, dynVisitLayout s⟩ idx () =
        (match idx with
         | 0 => .ok ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, dynVisitLayout (if s == 48 then 0 else s - 1)⟩ ()
         | k + 1 => .error (.invalidProgram s!"place layout: {repr (LayoutError.fieldOutOfBounds (k + 1) 1)}") ()) := by
    intro s hs
    rcases hs with rfl | rfl | rfl <;> (cases idx <;> rfl)
  rw [hstep t ht] at hfield
  cases idx with
  | zero => cases hfield; rfl
  | succ _ => cases hfield

/-- `dynTraitVisitHooks` satisfies `VisitHooksDescend` (discharged via `visitHooksDescend_of_conditions`). -/
theorem dynTrait_visitHooksDescend :
    VisitHooksDescend dynTraitVisitHooks () dynVisitTypeRank dynTraitGood (fun _ => false) := by
  apply visitHooksDescend_of_conditions
  have unpackTy : ∀ p : RuntimePlace CtfeProvenance, dynTraitGood p = true →
      ∃ prov mis,
        (p = ⟨.memory ⟨⟨Size.ZERO, prov⟩, witnessVTableMeta, mis⟩, dynVisitLayout 100⟩ ∧ p.layout.ty = 100) ∨
        (p = ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, dynVisitLayout p.layout.ty⟩ ∧
          (p.layout.ty = 50 ∨ p.layout.ty = 49 ∨ p.layout.ty = 48 ∨ p.layout.ty = 0)) := by
    rintro ⟨ref, lay⟩ hp
    cases ref with
    | «local» => simp [dynTraitGood] at hp
    | memory m =>
      rcases m with ⟨⟨off, prov⟩, metaVal, mis⟩
      simp only [dynTraitGood, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
        or_assoc] at hp
      rcases hp with ⟨⟨rfl, ⟨hty, rfl⟩ | ⟨htys, rfl⟩⟩, hlay⟩
      · exact ⟨prov, mis, Or.inl ⟨by rw [hlay, hty], hty⟩⟩
      · exact ⟨prov, mis, Or.inr ⟨by dsimp only; rw [← hlay], htys⟩⟩
  have badCls : ∀ {ty : MIR.TyId} {k : TypeKind} {s₀ s₁ : Unit},
      (∀ e, k ≠ .dynamic e) → k ≠ .foreign → (∀ a b c, k ≠ .aggregate a b c) →
      dynTraitVisitHooks.classify () ty s₀ = .ok k s₁ → False := by
    intro ty k s₀ s₁ h1 h2 h3 hcls
    simp only [dynTraitVisitHooks, minimalValidityHooks, pure, EStateM.pure, EStateM.Result.ok.injEq] at hcls
    obtain ⟨hcls, -⟩ := hcls
    cases h100 : (ty == 100)
    · simp only [h100, Bool.false_eq_true, ↓reduceIte] at hcls
      cases h0 : (ty == 0)
      · simp only [h0, Bool.false_eq_true, ↓reduceIte] at hcls
        exact h3 _ _ _ hcls.symm
      · simp only [h0, ↓reduceIte] at hcls
        exact h2 hcls.symm
    · simp only [h100, ↓reduceIte] at hcls
      exact h1 0 hcls.symm
  refine {
    seqZst := fun _ _ _ _ _ _ _ _ hcls _ =>
      False.elim (badCls (fun _ h => by cases h) (fun h => by cases h) (fun _ _ _ h => by cases h) hcls)
    arrayElem := fun place hp stride cnt hfs => by
      obtain ⟨_, _, ⟨heq, _⟩ | ⟨heq, hcases⟩⟩ := unpackTy place hp
      · rw [heq] at hfs; simp [dynVisitLayout, wrapperLayout] at hfs
      · rcases hcases with h | h | h | h <;> (rw [heq] at hfs; simp [h, dynVisitLayout, wrapperLayout] at hfs)
    pattern := fun _ _ _ _ _ _ _ _ _ _ _ hcls _ _ =>
      False.elim (badCls (fun _ h => by cases h) (fun h => by cases h) (fun _ _ _ h => by cases h) hcls)
    dynamic := ?_
    box := fun _ _ _ _ _ _ _ _ hcls _ =>
      False.elim (badCls (fun _ h => by cases h) (fun h => by cases h) (fun _ _ _ h => by cases h) hcls)
    arbitrary := ?_
    multiple := fun place hp tag enc tf vs hvs => by
      obtain ⟨_, _, ⟨heq, _⟩ | ⟨heq, hcases⟩⟩ := unpackTy place hp
      · rw [heq] at hvs; simp [dynVisitLayout, wrapperLayout] at hvs
      · rcases hcases with h | h | h | h <;> (rw [heq] at hvs; simp [h, dynVisitLayout, wrapperLayout] at hvs)
    union := fun place hp cnt hfs => by
      obtain ⟨_, _, ⟨heq, _⟩ | ⟨heq, hcases⟩⟩ := unpackTy place hp
      · rw [heq] at hfs; simp [dynVisitLayout, wrapperLayout] at hfs
      · rcases hcases with h | h | h | h <;> (rw [heq] at hfs; simp [h, dynVisitLayout, wrapperLayout] at hfs)
  }
  · intro place hp expected s₀ s₁ s₂ op s₃ s₄ inner s₅ memory hcls htoOp hunpack hop
    cases s₂; cases s₃; cases s₄; cases s₅
    obtain ⟨prov, mis, ⟨heq, hty100⟩ | ⟨_, hcases⟩⟩ := unpackTy place hp
    · have hexp : expected = 0 := by
        simp [hty100, dynTraitVisitHooks, minimalValidityHooks, pure, EStateM.pure] at hcls
        exact hcls.symm
      subst hexp
      rw [heq] at htoOp ⊢
      simp only [dynTraitVisitHooks, pure, EStateM.pure, EStateM.Result.ok.injEq] at htoOp
      obtain ⟨rfl, -⟩ := htoOp
      have hm : VTable.unpackDynTrait dynTraitVisitHooks.vtable ()
          ⟨.indirect ⟨⟨Size.ZERO, prov⟩, witnessVTableMeta, mis⟩, dynVisitLayout 100⟩ 0 () =
          .ok ⟨.indirect ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, dynVisitLayout 50⟩ () := rfl
      rw [hm] at hunpack
      cases hunpack
      cases hop
      refine ⟨by simp [dynTraitGood, dynVisitLayout], ?_⟩
      exact visitOrder_lt_of_unsized_unpack dynVisitTypeRank
        (dynVisitLayout 100) (dynVisitLayout 50) rfl rfl
    · simp only [dynTraitVisitHooks, minimalValidityHooks, pure, EStateM.pure,
        EStateM.Result.ok.injEq] at hcls
      rcases hcases with h | h | h | h <;> simp [h] at hcls
  · intro place hp offsets order hfs idx s₀ child s₁ hfield
    cases s₀; cases s₁
    obtain ⟨prov, mis, ⟨heq, _⟩ | ⟨heq, hcases⟩⟩ := unpackTy place hp
    · rw [heq] at hfield
      have herr : PlaceDynamic.field dynTraitVisitHooks.projection ()
          ⟨.memory ⟨⟨Size.ZERO, prov⟩, witnessVTableMeta, mis⟩, dynVisitLayout 100⟩ idx () =
          .error (.invalidProgram s!"place layout: {repr (LayoutError.fieldOutOfBounds idx 0)}") () := rfl
      rw [herr] at hfield; cases hfield
    · rcases hcases with h50 | h49 | h48 | h0
      · rw [heq, h50] at hfield ⊢
        rw [dyn_field_ok_inv prov mis 50 49 (Or.inl rfl) rfl idx child hfield]
        exact ⟨by simp [dynTraitGood, dynVisitLayout], by dsimp only; decide +kernel⟩
      · rw [heq, h49] at hfield ⊢
        rw [dyn_field_ok_inv prov mis 49 48 (Or.inr (Or.inl rfl)) rfl idx child hfield]
        exact ⟨by simp [dynTraitGood, dynVisitLayout], by dsimp only; decide +kernel⟩
      · rw [heq, h48] at hfield ⊢
        rw [dyn_field_ok_inv prov mis 48 0 (Or.inr (Or.inr rfl)) rfl idx child hfield]
        exact ⟨by simp [dynTraitGood, dynVisitLayout], by dsimp only; decide +kernel⟩
      · rw [heq, h0] at hfs
        simp [dynVisitLayout] at hfs

/-- `UnionHooksDescend` holds vacuously for `dynTraitVisitHooks`'s empty union invariant. -/
theorem dynTrait_unionHooksDescend :
    UnionHooksDescend dynTraitVisitHooks () dynVisitTypeRank
      (fun l => (fun _ => false : LocalLayout → Bool) l = true) := by
  intro l hl
  exact absurd hl (by simp)

/-- **General unsized `vendored_visit_eq_noFuel` instantiated on `dynTraitVisitHooks` (`maxSized = 151`).**
For every valid vtable-backed `dyn Trait` place (`ty = 100`) and every `fuel > 154`
(`visitFuelBound 151 dynVisitTypeRank (dynVisitLayout 100) = 154`), the unmodified vendored
`ValidityVisitor.visit` equals `realVisitNoFuel` across `VTable.unpackDynTrait` and all 3 concrete
field projections. -/
theorem dynTrait_vendored_visit_eq_noFuel (fuel : Nat) (prov : Option CtfeProvenance)
    (mis : Option Misalignment) (session : Session CtfeProvenance) (hfuel : 154 < fuel) :
    ValidityVisitor.visit dynTraitVisitHooks () fuel session
        ⟨.memory ⟨⟨Size.ZERO, prov⟩, witnessVTableMeta, mis⟩, dynVisitLayout 100⟩ =
      realVisitNoFuel dynTraitVisitHooks () dynVisitTypeRank session
        ⟨.memory ⟨⟨Size.ZERO, prov⟩, witnessVTableMeta, mis⟩, dynVisitLayout 100⟩ := by
  refine vendored_visit_eq_noFuel dynTraitVisitHooks () dynVisitTypeRank dynTraitGood
    (fun _ => false) dynTrait_visitHooksDescend dynTrait_unionHooksDescend 151 ?_
    fuel session _ (by simp [dynTraitGood, dynVisitLayout]) ?_
  · rintro ⟨refP, layP⟩ ⟨refC, layC⟩ _ hgoodC _ hszC
    cases refC with
    | «local» => simp [dynTraitGood] at hgoodC
    | memory m =>
      rcases m with ⟨⟨off, _⟩, metaVal, _⟩
      simp only [dynTraitGood, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
        or_assoc] at hgoodC
      rcases hgoodC with ⟨⟨_, ⟨h100, _⟩ | ⟨h50 | h49 | h48 | h0, _⟩⟩, hlayC⟩
      · have hbad : layC.layout.isSized = false := by rw [hlayC, h100]; rfl
        rw [hbad] at hszC; cases hszC
      · dsimp only; rw [hlayC, h50]; decide +kernel
      · dsimp only; rw [hlayC, h49]; decide +kernel
      · dsimp only; rw [hlayC, h48]; decide +kernel
      · dsimp only; rw [hlayC, h0]; decide +kernel
  · change visitFuelBound 151 dynVisitTypeRank (dynVisitLayout 100) < fuel
    have hb : visitFuelBound 151 dynVisitTypeRank (dynVisitLayout 100) = 154 := by decide +kernel
    omega

/-- **Kernel-evaluated witness separating `realVisitLexRank` from sized-only `realVisitRank` on `dyn Trait`!**
On the unsized `dyn Trait` root (`ty = 100 -> 50 -> 49 -> 48 -> 0`, 5 places):
- `realVisitLexRank` (and therefore `realVisitNoFuel`, by `realVisitLexRank_eq_noFuel`) **succeeds**,
- vendored `ValidityVisitor.visit` at `fuel = 5` **succeeds**, whereas
- sized-only `realVisitRank` (`fuel = layoutOrder 100 + 2 = 3`) **falsely exhausts fuel**! -/
theorem dynTrait_lexRank_succeeds_while_sizedRank_exhausts :
    let root : RuntimePlace CtfeProvenance :=
      ⟨.memory ⟨⟨Size.ZERO, none⟩, witnessVTableMeta, none⟩, dynVisitLayout 100⟩
    let init : Session CtfeProvenance :=
      { path := ⟨"DynRoot", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    resultOk (realVisitLexRank dynTraitVisitHooks () dynVisitTypeRank init root ()) = true ∧
      resultOk (realVisitNoFuel dynTraitVisitHooks () dynVisitTypeRank init root ()) = true ∧
      resultOk (ValidityVisitor.visit dynTraitVisitHooks () 5 init root ()) = true ∧
      resultExhausted "validity traversal fuel"
        (realVisitRank dynTraitVisitHooks () dynVisitTypeRank init root ()) = true := by
  intro root init
  have hlex : realVisitLexRank dynTraitVisitHooks () dynVisitTypeRank init root =
      realVisitNoFuel dynTraitVisitHooks () dynVisitTypeRank init root :=
    realVisitLexRank_eq_noFuel _ _ _ _ _
  refine ⟨by decide +kernel, ?_, by decide +kernel, by decide +kernel⟩
  rw [← hlex]
  decide +kernel

/-! #### Witness 2: Same-`TyId` multi-variant enum -> aggregate -> scalar (`typeRank = 0` throughout) -/

/-- One-byte `u8` tag scalar (`0..=1` valid range) for the multi-variant enum witness. -/
def enumU8Tag : ABI.Scalar :=
  ABI.Scalar.Initialized (value := .Int .I8 false) (validRange := ⟨0, 1⟩)

/-- Variant 0 layout for the same-`TyId` enum witness (`size = 1`, one field at offset `0`). -/
def enumVariant0 : VariantLayout where
  size := Size.ofBytes 1
  backendRepr := .Scalar enumU8Tag
  fieldOffsets := #[Size.ZERO]
  fieldsInMemoryOrder := #[0]
  largestNiche := none
  uninhabited := false

/-- Phase-2 multi-variant enum layout (`ty = 0`, `variants = .Multiple`, `layoutPhase = 2`). -/
def enumRootLayout : LocalLayout :=
  ⟨0, { wrapperLayout with
    fields := .Primitive
    variants := .Multiple enumU8Tag .Direct 0 #[enumVariant0, enumVariant0]
    backendRepr := .Scalar enumU8Tag }⟩

/-- Phase-1 downcasted single-variant aggregate layout (`ty = 0`, `variants = .Single 0`, `fields = .Arbitrary`, `layoutPhase = 1`). -/
def enumDowncastLayout : LocalLayout :=
  ⟨0, wrapperLayout⟩

/-- Phase-0 primitive scalar field layout (`ty = 0`, `variants = .Single 0`, `fields = .Primitive`, `layoutPhase = 0`). -/
def enumScalarLeafLayout : LocalLayout :=
  ⟨0, { wrapperLayout with
    fields := .Primitive
    backendRepr := .Scalar enumU8Tag }⟩

/-- Tag scalar layout (`u8`, unsigned scalar backendRepr) returned by `discriminantLayout` / `tagLayout`. -/
def enumTagFieldLayout : LocalLayout :=
  ⟨0, { wrapperLayout with
    fields := .Primitive
    backendRepr := .Scalar (ABI.Scalar.Initialized (value := .Int .I8 false) (validRange := ⟨0, 255⟩)) }⟩

/-- Valid `0 : u8` scalar immediate (`Scalar.fromBool false`) for discriminant reading. -/
def zeroU8Scalar : Scalar CtfeProvenance :=
  Scalar.fromBool false

/-- Concrete `ValidityVisitor.Hooks` exercising `.Multiple` enum discriminant read + `PlaceDynamic.downcast`
(`phase 2 -> phase 1`) followed by `.Arbitrary` `PlaceDynamic.field` (`phase 1 -> phase 0`), all at
the SAME `TyId = 0` (`typeRank = fun _ => 0`)! -/
def enumPhaseVisitHooks : Hooks CtfeProvenance Unit Unit Unit Unit Unit Unit :=
  let base := minimalValidityHooks
    (fun _ _ => enumScalarLeafLayout)
    (fun _ => enumRootLayout)
    (fun _ => .aggregate false false true)
  { base with
    classify := fun _ _ => pure (.aggregate false false true)
    fieldPath := fun _ _ idx _ => pure (.field s!"{idx}")
    variantPath := fun _ _ v => pure (.variant s!"{v}")
    toOp := fun _ place =>
      match place.ref with
      | .memory m => pure ⟨.indirect m, place.layout⟩
      | .local .. => throw (.invalidProgram "expected memory place")
    projection := { base.projection with
      variant := fun _ _ _ => pure enumDowncastLayout
      field := fun _ _ _ => pure enumScalarLeafLayout }
    discriminant := { base.discriminant with
      discriminantLayout := fun _ _ => pure enumTagFieldLayout
      tagLayout := fun _ _ => pure enumTagFieldLayout
      projectRead := fun _ op _ => pure ⟨op.op, enumTagFieldLayout⟩
      readImmediate := fun _ _ => pure ⟨.scalar zeroU8Scalar, enumTagFieldLayout⟩
      variantForDiscriminant := fun _ _ _ => pure (some 0) } }

/-- Good places for `enumPhaseVisitHooks`: zero-offset thin memory places at one of the 3 `ty = 0` phase layouts. -/
def enumPhaseGood (p : RuntimePlace CtfeProvenance) : Bool :=
  match p.ref with
  | .memory ⟨⟨off, _⟩, metaVal, _⟩ =>
    off == Size.ZERO && decide (metaVal = .none) &&
      (decide (p.layout = enumRootLayout) ||
        decide (p.layout = enumDowncastLayout) ||
        decide (p.layout = enumScalarLeafLayout))
  | .local .. => false

/-- `enumPhaseVisitHooks` satisfies `VisitHooksDescend` at constant `typeRank = 0`, descending purely
via `layoutOrder_variant_lt` (`2 -> 1`) and `layoutOrder_primitive_lt` (`1 -> 0`). -/
theorem enumPhase_visitHooksDescend :
    VisitHooksDescend enumPhaseVisitHooks () (fun _ => 0) enumPhaseGood (fun _ => false) := by
  apply visitHooksDescend_of_conditions
  have unpackP : ∀ p : RuntimePlace CtfeProvenance, enumPhaseGood p = true →
      ∃ prov mis, p = ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, p.layout⟩ ∧
        (p.layout = enumRootLayout ∨ p.layout = enumDowncastLayout ∨ p.layout = enumScalarLeafLayout) := by
    rintro ⟨ref, lay⟩ hp
    cases ref with
    | «local» => simp [enumPhaseGood] at hp
    | memory m =>
      rcases m with ⟨⟨off, prov⟩, metaVal, mis⟩
      simp only [enumPhaseGood, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq, or_assoc] at hp
      rcases hp with ⟨⟨rfl, rfl⟩, hlay⟩
      exact ⟨prov, mis, rfl, hlay⟩
  refine {
    seqZst := fun _ _ _ _ _ _ _ _ hcls _ => nomatch hcls
    arrayElem := fun place hp stride cnt hfs => by
      obtain ⟨_, _, _, hlay⟩ := unpackP place hp
      rcases hlay with h | h | h <;> (rw [h] at hfs; simp [enumRootLayout, enumDowncastLayout, enumScalarLeafLayout, wrapperLayout] at hfs)
    pattern := fun _ _ _ _ _ _ _ _ _ _ _ hcls _ _ => nomatch hcls
    dynamic := fun _ _ _ _ _ _ _ _ _ _ _ _ hcls _ _ _ => nomatch hcls
    box := fun _ _ _ _ _ _ _ _ hcls _ => nomatch hcls
    arbitrary := ?_
    multiple := ?_
    union := fun place hp cnt hfs => by
      obtain ⟨_, _, _, hlay⟩ := unpackP place hp
      rcases hlay with h | h | h <;> (rw [h] at hfs; simp [enumRootLayout, enumDowncastLayout, enumScalarLeafLayout, wrapperLayout] at hfs)
  }
  · intro place hp offsets order hfs idx s₀ child s₁ hfield
    cases s₀; cases s₁
    obtain ⟨prov, mis, heq, hlay⟩ := unpackP place hp
    rcases hlay with hroot | hdown | hleaf
    · rw [hroot] at hfs; simp [enumRootLayout] at hfs
    · rw [heq, hdown] at hfield ⊢
      cases idx with
      | zero =>
        have h0 : PlaceDynamic.field enumPhaseVisitHooks.projection ()
            ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, enumDowncastLayout⟩ 0 () =
            .ok ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, enumScalarLeafLayout⟩ () := rfl
        rw [h0] at hfield
        cases hfield
        refine ⟨by simp [enumPhaseGood], ?_⟩
        exact visitOrder_lt_of_same_sized (fun _ => 0) enumDowncastLayout enumScalarLeafLayout rfl
          (layoutOrder_primitive_lt (fun _ => 0) enumDowncastLayout enumScalarLeafLayout
            rfl rfl (by intro _ _ _ _ h; cases h) (by decide))
      | succ k =>
        have herr : PlaceDynamic.field enumPhaseVisitHooks.projection ()
            ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, enumDowncastLayout⟩ (k + 1) () =
            .error (.invalidProgram s!"place layout: {repr (LayoutError.fieldOutOfBounds (k + 1) 1)}") () := rfl
        rw [herr] at hfield; cases hfield
    · rw [hleaf] at hfs; simp [enumScalarLeafLayout] at hfs
  · intro place hp tag enc tf vs hvs s₀ op s₁ s₂ variant s₃ s₄ child s₅ _ _ hdown
    cases s₄; cases s₅
    obtain ⟨prov, mis, heq, hlay⟩ := unpackP place hp
    rcases hlay with hroot | hdownL | hleaf
    · rw [heq, hroot] at hdown ⊢
      have hd : PlaceDynamic.downcast enumPhaseVisitHooks.projection ()
          ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, enumRootLayout⟩ variant () =
          .ok ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, enumDowncastLayout⟩ () := rfl
      rw [hd] at hdown
      cases hdown
      refine ⟨by simp [enumPhaseGood], ?_⟩
      exact visitOrder_lt_of_same_sized (fun _ => 0) enumRootLayout enumDowncastLayout rfl
        (layoutOrder_variant_lt (fun _ => 0) enumRootLayout enumDowncastLayout
          rfl ⟨_, _, _, _, rfl⟩ (by intro _ _ _ _ h; cases h))
    · rw [hdownL] at hvs; simp [enumDowncastLayout, wrapperLayout] at hvs
    · rw [hleaf] at hvs; simp [enumScalarLeafLayout, wrapperLayout] at hvs

/-- **Same-`TyId` enum + aggregate adequacy (`typeRank = 0`):** for every `fuel > 3`, unmodified
vendored `ValidityVisitor.visit` equals `realVisitNoFuel` across `.Multiple` downcast and `.Arbitrary`
field projection, AND succeeds in the kernel (`decide +kernel`). -/
theorem enumPhase_vendored_visit_eq_noFuel (fuel : Nat) (prov : Option CtfeProvenance)
    (mis : Option Misalignment) (session : Session CtfeProvenance) (hfuel : 3 < fuel) :
    ValidityVisitor.visit enumPhaseVisitHooks () fuel session
        ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, enumRootLayout⟩ =
      realVisitNoFuel enumPhaseVisitHooks () (fun _ => 0) session
        ⟨.memory ⟨⟨Size.ZERO, prov⟩, .none, mis⟩, enumRootLayout⟩ := by
  refine vendored_visit_eq_noFuel_of_sized enumPhaseVisitHooks () (fun _ => 0) enumPhaseGood
    (fun _ => false) enumPhase_visitHooksDescend (fun l hl => absurd hl (by simp))
    fuel session _ (by simp [enumPhaseGood]) rfl ?_
  change layoutOrder (fun _ => 0) enumRootLayout + 1 < fuel
  have hord : layoutOrder (fun _ => 0) enumRootLayout = 2 := by decide +kernel
  omega

/-- Kernel-evaluated success of `enumPhaseVisitHooks` on both vendored `visit` (`fuel = 4`) and
`realVisitNoFuel` (via `realVisitLexRank`). -/
theorem enumPhase_visit_ok :
    let root : RuntimePlace CtfeProvenance :=
      ⟨.memory ⟨⟨Size.ZERO, none⟩, .none, none⟩, enumRootLayout⟩
    let init : Session CtfeProvenance :=
      { path := ⟨"EnumRoot", #[]⟩, flags := ⟨false, false⟩, ctfeMode := none,
        refTracking := none, dataBytes := none }
    resultOk (realVisitNoFuel enumPhaseVisitHooks () (fun _ => 0) init root ()) = true ∧
      resultOk (ValidityVisitor.visit enumPhaseVisitHooks () 4 init root ()) = true := by
  intro root init
  rw [← realVisitLexRank_eq_noFuel]
  exact ⟨by decide +kernel, by decide +kernel⟩

/-! #### Witness 3: 3-reference array LIFO pointee draining (`lean-miri#90` `ConnectedPointerAlignment.lean` L863–906) -/

/-- Reference layout (`ty = 1`, 8-byte thin pointer). -/
def lifoRefLayout : LocalLayout :=
  ⟨1, { wrapperLayout with
    fields := .Primitive
    size := Size.ofBytes 8
    backendRepr := .Scalar (ABI.Scalar.Initialized
      (value := .Pointer .ZERO) (validRange := ⟨0, 0xFFFF_FFFF_FFFF_FFFF⟩)) }⟩

/-- 3-element array `[&bool; 3]` layout (`ty = 2`, stride `8`, count `3`, size `24`). -/
def lifoArrayLayout : LocalLayout :=
  ⟨2, { wrapperLayout with
    fields := .Array (Size.ofBytes 8) 3
    size := Size.ofBytes 24 }⟩

/-- Pointee `bool` layout (`ty = 3`, 1-byte boolean). -/
def lifoBoolLayout : LocalLayout :=
  ⟨3, { wrapperLayout with
    fields := .Primitive
    size := Size.ofBytes 1
    backendRepr := .Scalar (ABI.Scalar.Initialized (value := .Int .I8 false) (validRange := ⟨0, 1⟩)) }⟩

private def unusedLifo {A : Type} : M (Array UInt64) A := throw (StepError.unsupported "unused")

/-- Concrete `ValidityVisitor.Hooks` over `State := Array UInt64` (recording visited boolean byte
offsets) reproducing `lean-miri#90` `ConnectedPointerAlignment.lean` L863–906:
- `ty = 2` is `.sequence 1` (`[&bool; 3]` at offsets `0, 8, 16`),
- `ty = 1` is `.reference false` reading a pointer to the same offset (`0, 8, 16`),
- `ty = 3` is `.boolean` recording `offset.bytes` into state and returning `2` (invalid `bool`!) at
  offset `0` vs `1` (valid `true`) at offsets `8` and `16`. -/
def lifo3RefHooks : Hooks CtfeProvenance (Array UInt64) Unit Unit Unit Unit Unit where
  target := RuntimeTargetDataLayout.default
  projection := {
    place := {
      getFrame := unusedLifo, setFrame := fun _ => unusedLifo
      debugAssertions := false, frameIndex := unusedLifo
      resolveLayout := fun _ _ => unusedLifo
      localToOp := fun _ _ => unusedLifo
      projection := fun _ => unusedLifo
      deref := fun _ _ _ => unusedLifo
      checkPlaceType := fun _ _ _ => unusedLifo
      allocateStack := fun _ _ => unusedLifo
      writeMemoryNoValidate := fun _ _ _ => unusedLifo
      afterLocalMovedToMemory := fun _ _ _ => unusedLifo
      memoryOffset := fun _ base offset _ metaVal =>
        match base.ptr.offset.add offset with
        | .ok off => pure { base with ptr := { base.ptr with offset := off }, metadata := metaVal }
        | .error e => throw (StepError.invalidProgram (reprStr e))
      writeLocalImmediate := fun _ _ _ _ => unusedLifo
      enforceValidity := fun _ _ => pure true, validate := fun _ _ => pure ()
    }
    target := RuntimeTargetDataLayout.default.base
    maxSizeOfVal := Size.ofBytes 0x7FFF_FFFF_FFFF_FFFF
    dynamic := {
      target := RuntimeTargetDataLayout.default.base
      maxSizeOfVal := Size.ofBytes 0x7FFF_FFFF_FFFF_FFFF
      classify := fun _ _ => unusedLifo
      field := fun _ _ _ => unusedLifo
      packedAlign := fun _ _ => pure none
      vtableSizeAndAlign := fun _ _ _ => unusedLifo
    }
    dynamicFuel := 0
    isSliceOrStr := fun _ _ => pure false
    field := fun _ _ _ => pure lifoRefLayout
    variant := fun _ parent _ => pure parent
    packedAlign := fun _ _ => pure none
    subsliceLayout := fun _ _ _ => unusedLifo
    layoutOf := fun _ ty =>
      pure (if ty == 2 then lifoArrayLayout else if ty == 1 then lifoRefLayout else lifoBoolLayout)
    localIndex := fun _ _ => unusedLifo
  }
  vtable := {
    target := RuntimeTargetDataLayout.default.base
    isDynamic := fun _ _ => pure false, memoryOffset := fun _ _ _ _ _ => unusedLifo
    resolvePointer := fun _ _ => unusedLifo
    globalVTable := fun _ _ => unusedLifo
    globalFunction := fun _ _ => unusedLifo
    predicates := fun _ _ => pure #[], normalizePredicate := fun _ p => pure p.id
    layoutOf := fun _ _ => unusedLifo
    eraseAndAnonymize := fun _ _ _ => unusedLifo
    ensureMonomorphicType := fun _ _ => pure (), ensureMonomorphicDyn := fun _ _ => pure ()
    globalSalt := fun _ => pure 0, reserveVTable := fun _ _ _ _ => unusedLifo
    globalRootPointer := fun _ _ => unusedLifo
    entries := fun _ _ _ => pure #[], assertVirtualInstanceMatches := fun _ _ _ _ _ => pure ()
  }
  discriminant := {
    runtimeTarget := RuntimeTargetDataLayout.default
    discriminantLayout := fun _ _ => unusedLifo
    tagLayout := fun _ _ => unusedLifo
    discriminantValue := fun _ _ _ => unusedLifo
    variantForDiscriminant := fun _ _ _ => unusedLifo
    adtVariantCount := fun _ _ => pure 0
    projectRead := fun _ _ _ => unusedLifo
    readImmediate := fun _ _ => unusedLifo
    destLayout := fun p => p.layout
    projectWrite := fun _ _ _ => unusedLifo
    writeScalar := fun _ _ _ => unusedLifo
    toOp := fun _ _ => unusedLifo
    scalarMayBeNull := fun _ _ => pure false
  }
  debugAssertions := false
  classify := fun _ ty =>
    pure (if ty == 2 then .sequence 1 else if ty == 1 then .reference false else .boolean)
  unitLayout := fun _ => pure lifoRefLayout
  typeName := fun _ _ => pure "Root"
  opsemInhabited := fun _ _ => pure true
  isFreeze := fun _ _ => pure true
  fieldPath := fun _ _ idx _ => pure (.field s!"{idx}")
  variantPath := fun _ _ v => pure (.variant s!"{v}")
  projectBox := fun _ _ => unusedLifo
  toOp := fun _ place =>
    match place.ref with
    | .memory m => pure ⟨.indirect m, place.layout⟩
    | .local .. => throw (StepError.invalidProgram "expected memory place")
  readImmediate := fun _ place _ => do
    let .memory memory := place.ref | throw (StepError.invalidProgram "expected memory place")
    if place.layout.ty == 1 then
      let sc := Scalar.fromPointer RuntimeTargetDataLayout.default.base
        ⟨memory.ptr.offset, witnessProv⟩
      pure ⟨.scalar sc, place.layout⟩
    else
      modify fun trace => trace.push memory.ptr.offset.bytes
      let bits : U128 := if memory.ptr.offset == Size.ZERO then 2 else 1
      match Scalar.fromUInt (Prov := CtfeProvenance) bits (Size.ofBytes 1) with
      | .ok sc => pure ⟨.scalar sc, place.layout⟩
      | .error _ => throw (StepError.invalidProgram "scalar construction failed")
  clearProvenance := fun _ _ => pure ()
  writeNoValidate := fun _ _ _ => pure ()
  sizeAndAlign := fun _ _ => pure (some (Size.ofBytes 1, Align.ONE))
  ptrToPlace := fun _ val => do
    let .scalar sc := val.imm | throw (StepError.invalidProgram "expected scalar pointer")
    let .ok ptr := sc.toPointer RuntimeTargetDataLayout.default.base
      | throw (StepError.invalidProgram "expected valid pointer")
    pure ⟨⟨ptr, .none, none⟩, lifoBoolLayout⟩
  metadataTail := fun _ _ => pure .foreign
  checkPointerAccess := fun _ _ _ => pure (.ok ())
  checkPointerAlign := fun _ _ _ => pure ()
  checkPointerAlignResult := fun _ _ _ => pure (.ok ())
  scalarMayBeNull := fun _ _ => pure false
  retagPointer := fun _ _ _ => pure none
  ctfePointerLookup := fun _ _ _ => unusedLifo
  inMutableMemory := fun _ _ => pure true
  readBytes := fun _ _ _ _ => pure ()
  clearBytesProvenance := fun _ _ _ => pure ()
  beginPadding := fun _ _ _ => pure none
  writePadding := fun _ _ _ => pure ()
  cachedUnionRanges := fun _ _ comp => comp
  withGhostValidation := fun comp => comp

/-- **Kernel-evaluated 3-reference LIFO pointee witness (`lean-miri#90` `ConnectedPointerAlignment.lean` L863–906).**
Validating `[&b0, &b1, &b2]` recursively via `realValidatePlaceNoFuel` (transported through the
`Classical.choice`-free `realValidatePlaceLexRank`) visits the three pointees in **reverse discovery
order `#[16, 8, 0]`** and fails with `.undefinedBehavior` starting with `"validation[0]"` on the
invalid first boolean (`b0 = 2`). -/
theorem lifo3Ref_validatePlace_visits_reverse_order :
    let arrayRoot : RuntimePlace CtfeProvenance :=
      ⟨.memory ⟨⟨Size.ZERO, some witnessProv⟩, .none, none⟩, lifoArrayLayout⟩
    let typeRank : MIR.TyId → Nat := fun ty => if ty == 2 then 1 else 0
    (match realValidatePlaceNoFuel lifo3RefHooks () (fun _ => typeRank) arrayRoot true false #[] with
     | .error (.undefinedBehavior msg) visitedOffsets =>
       visitedOffsets == #[16, 8, 0] && msg.startsWith "validation[0]"
     | _ => false) = true := by
  intro arrayRoot typeRank
  rw [← realValidatePlaceLexRank_eq_noFuel]
  decide +kernel

end RealVisit

/-! ## 8. `leanprover/lean4#13851` axiom footprint audit

`lean4#13851` reimplements `WellFounded.fix` with `Classical.choice`, so every `termination_by`
definition (`RankedWalk.walkNoFuel`, `VisitLexWalk.walkNoFuel`, `realUnionRangesNoFuel`,
`RealVisit.realVisitNoFuel`, and their
wrappers `visitNoFuel`, `visitLexNoFuel`, `unionRangesNoFuel`, `drainPointeesNoFuel`), and every
theorem whose statement mentions one, will acquire `Classical.choice`. The structural (`Nat.rec`
and `Nat.rec × Nat.rec`) companions (`RankedWalk.walkRank`, `VisitLexWalk.walkRank`,
`realUnionRangesRank`, `checkCert`, `checkSchema17Table`) do not use `WellFounded.fix`:

* `#guard_msgs` pins exact current footprints on both the `layoutOrder` (`ω`) and `visitOrder`
  (`ω · 2`) structural vs. well-founded layers plus `realUnionRanges*` and the real vendored
  `visit` layer (`RealVisit.realVisitGuarded` / `realVisitRank` structural vs. the
  `termination_by` `RealVisit.realVisitNoFuel`, which is `Classical.choice`-free *today* but will
  acquire `Classical.choice` under `lean4#13851`, hence it is guarded by `#assert_standard_axioms`
  rather than `#assert_choice_free`);
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

/-- info: 'LeanMiriSpec.ValidationRankCert.RealVisit.realVisitGuarded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RealVisit.realVisitGuarded

/-- info: 'LeanMiriSpec.ValidationRankCert.RealVisit.realVisitRank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RealVisit.realVisitRank

/-- info: 'LeanMiriSpec.ValidationRankCert.RealVisit.realVisitNoFuel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RealVisit.realVisitNoFuel

/-- info: 'LeanMiriSpec.ValidationRankCert.RealVisit.realVisitLexRank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RealVisit.realVisitLexRank

/- The vendored fuelled `validatePlace` already depends on `Classical.choice` *today* (its `while`
loop goes through the opaque `repeatM.impl`), whereas `lean-miri#90`'s structural LIFO drain
(`RealVisit.realValidatePlaceLexRank` below) is `Classical.choice`-free. -/
/-- info: 'Miri.Interpreter.ValidityVisitor.validatePlace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ValidityVisitor.validatePlace

/-- info: 'Miri.Interpreter.ValidityVisitor.visit' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ValidityVisitor.visit

/-- info: 'LeanMiriSpec.ValidationRankCert.RealVisit.realValidatePlaceLexRank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms RealVisit.realValidatePlaceLexRank

/-- info: 'LeanMiriSpec.ValidationRankCert.RealVisit.drainPointeesFuel' does not depend on any axioms -/
#guard_msgs in
#print axioms RealVisit.drainPointeesFuel


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
  RealVisit.visitStep
  RealVisit.vendored_visit_succ
  RealVisit.realVisitGuarded
  RealVisit.realVisitRank
  RealVisit.realVisitSized
  RealVisit.realVisitUnsized
  RealVisit.realVisitLexRank
  RealVisit.realVisitLexRank_eq_noFuel
  RealVisit.realConstValidatePlaceLexRank
  RealVisit.realConstValidatePlaceLexRank_eq_noFuel
  RealVisit.vendored_constValidatePlace_eq_noFuel
  RealVisit.realValidatePlaceLexRank
  RealVisit.realValidatePlaceLexRank_eq_noFuel
  RealVisit.drainPointeesFuel
  RealVisit.drainPointeesFuel_eq_drainPointees
  RealVisit.drainPointeesFuel_exhausts_of_lt
  RealVisit.vendored_visit_eq_guarded
  RealVisit.visitHooksDescend_of_conditions
  RealVisit.dynTrait_lexRank_succeeds_while_sizedRank_exhausts
  RealVisit.enumPhase_visitHooksDescend
  RealVisit.enumPhase_vendored_visit_eq_noFuel
  RealVisit.enumPhase_visit_ok

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
  RealVisit.realVisitNoFuel
  RealVisit.realVisitNoFuel_eq
  RealVisit.deepPattern_visitHooksDescend
  RealVisit.realVisitGuarded_eq_noFuel_of_sized
  RealVisit.realVisitRank_eq_noFuel
  RealVisit.realVisitGuarded_eq_noFuel
  RealVisit.vendored_visit_eq_noFuel
  RealVisit.vendored_visit_eq_noFuel_of_sized
  RealVisit.realVisitSized_eq_noFuel
  RealVisit.realVisitUnsized_eq_noFuel
  RealVisit.realVisitLexRank_eq_noFuel
  RealVisit.vendored_visit_eq_noFuel_of_wpCoalBounded
  RealVisit.vendored_visit_eq_noFuel_of_sized_wpCoalBounded
  RealVisit.realConstValidatePlaceNoFuel
  RealVisit.realConstValidatePlaceLexRank_eq_noFuel
  RealVisit.vendored_constValidatePlace_eq_noFuel
  RealVisit.realValidatePlaceNoFuel
  RealVisit.realValidatePlaceLexRank_eq_noFuel
  RealVisit.deepPattern_vendored_visit_eq_noFuel
  RealVisit.selfPattern_noFuel_rejects_vendored_exhausts
  RealVisit.dynTrait_visitHooksDescend
  RealVisit.dynTrait_vendored_visit_eq_noFuel
  RealVisit.dynTrait_lexRank_succeeds_while_sizedRank_exhausts
  RealVisit.enumPhase_vendored_visit_eq_noFuel
  RealVisit.enumPhase_visit_ok
  RealVisit.lifo3Ref_validatePlace_visits_reverse_order

end LeanMiriSpec.ValidationRankCert
