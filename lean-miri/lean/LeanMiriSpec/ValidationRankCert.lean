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
Schema 17 by-value `validation_rank`, `visit` and `unionRanges` recurse by well-founded recursion
on the static order `layoutOrder` (`3 * rank + phase`), every effectful projection hook result is
checked dynamically to descend (`.invalidProgram "… does not descend"` otherwise), and tracked
pointees are drained in LIFO order without further tracking, so cyclic pointer graphs never feed
back into the by-value recursion.

This module formalizes that design over the *unmodified* vendored `lean-miri` (which still uses
fuel), against the real `Miri.Interpreter.ValidityVisitor.M` monad, `Miri.Interpreter.StepError`,
`LocalLayout`, `RuntimePlace`, `ValidationSession`, `RefTracking`, and `DataRangeSet` types:

1. `layoutOrder` (verbatim from `lean-miri#90`) and its descent lemmas for children of strictly
   smaller rank, enum variants, and synthetic scalar fields.
2. `ValidationRankCert` (a finite Schema 17 rank table) with an executable checker `checkCert`
   over a finite compiler-layout graph, its soundness (`checkCert_sound`), transitive descent
   (`checkCert_reach_descends`), and acyclicity (`checkCert_acyclic`, `checkCert_rejects_cycle`).
3. `RankedWalk`, a rank-ordered traversal over effectful projection hooks. `walkNoFuel` is the
   fuel-free well-founded traversal with the dynamic descent guard; `visitNoFuel` (sessions over
   `RuntimePlace`s) and `unionRangesNoFuel` (`DataRangeSet` accumulation over offset layouts) are
   its two `lean-miri#90` instances; `drainPointees` is the LIFO pointee queue drain.
4. Equivalences: the structural (`Nat.rec`) rank-fuelled companion `walkRank` equals `walkNoFuel`
   unconditionally (`walkRank_eq_walkNoFuel`), and the vendored-style unguarded bounded-fuel
   traversal `walkFuel` agrees with the guarded one at *every* fuel, hence with `walkNoFuel` for
   every `fuel > layoutOrder root`, whenever the hooks satisfy the rank certificate
   (`walkFuel_eq_walkNoFuel`); hooks that fail to descend are rejected deterministically
   (`walkNoFuel_rejects_nondescending`).
5. The `Anneal.MirFuelFree` bridge: the rank countdown coalgebra converges in
   `Anneal.ITreeWP.wpCoalBounded` exactly for `fuel > layoutOrder root`, `fuel := rank + 1` is the
   canonical static bound, and `Anneal.MirFuelFree.wpCoalBounded_mono_fuel` lifts it to every
   larger budget (`walkFuel_eq_walkNoFuel_of_wpCoalBounded`).
6. A kernel-evaluated 150-level nested single-field wrapper witness.
7. The `leanprover/lean4#13851` axiom footprint audit: the structural companions are checked to be
   `Classical.choice`-free, while the `termination_by` entry points are only checked against the
   standard axioms, so they keep building once `WellFounded.fix` is reimplemented with
   `Classical.choice`.
-/

set_option autoImplicit false

/-- Fail unless every listed declaration depends only on Lean's standard axioms (`propext`,
`Quot.sound`, `Classical.choice`): in particular on no `sorryAx` and no `Lean.ofReduceBool`. -/
local elab "#assert_standard_axioms " ids:ident* : command => do
  for id in ids do
    let n ← Lean.Elab.Command.liftCoreM <| Lean.Elab.realizeGlobalConstNoOverloadWithInfo id
    let axs ← Lean.Elab.Command.liftCoreM <| Lean.collectAxioms n
    for a in axs do
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "{n} depends on the non-standard axiom {a}"
    Lean.logInfo m!"{n} depends on axioms: {axs.toList}"

/-- Fail unless every listed declaration depends only on `propext` and `Quot.sound` (no
`Classical.choice`): the footprint that must survive `leanprover/lean4#13851`. -/
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
open Miri.Interpreter.ValidityVisitor (M Key Session)

/-! ## 1. The Schema 17 layout order (`lean-miri#90`) -/

/-- The phase of a layout within its type id (`lean-miri#90`): a selected enum variant precedes
its multi-variant parent (phase `2`) and a synthetic primitive field (phase `0`) precedes its
aggregate parent (phase `1`), even when they share the parent's type id. -/
def layoutPhase (place : LocalLayout) : Nat :=
  match place.layout.variants, place.layout.fields with
  | .Multiple .., _ => 2
  | _, .Primitive => 0
  | _, _ => 1

/-- `lean-miri#90`'s static traversal order `3 * rank + phase`. -/
def layoutOrder (typeRank : Miri.MIR.TyId → Nat) (place : LocalLayout) : Nat :=
  3 * typeRank place.ty + layoutPhase place

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

/-- A child of strictly smaller Schema 17 rank always descends, whatever the phases. -/
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

/-! ## 2. Rank certificates over finite compiler-layout graphs -/

/-- A Schema 17 rank certificate: the `validation_rank` recorded for each compiler `TypeNode`
(types absent from the table default to rank `0`, as `RuntimeArrayTypes.typeRank` does). -/
structure ValidationRankCert where
  ranks : List (Miri.MIR.TyId × Nat)
  deriving Repr

namespace ValidationRankCert

/-- The rank map `tyRank` of a certificate. -/
def tyRank (cert : ValidationRankCert) (ty : Miri.MIR.TyId) : Nat :=
  ((cert.ranks.find? (·.1 == ty)).map (·.2)).getD 0

end ValidationRankCert

/-- A finite compiler-layout graph: each node's composite children (struct/tuple fields,
array/slice elements, and enum/coroutine/union variants), as returned by the compiler layout
projections `field` / `variant`. -/
structure LayoutGraph where
  nodes : List LocalLayout
  children : LocalLayout → List LocalLayout

/-- Executable Schema 17 certificate check: every child of every node strictly descends in
`layoutOrder cert.tyRank`. -/
def checkCert (cert : ValidationRankCert) (g : LayoutGraph) : Bool :=
  g.nodes.all fun p => (g.children p).all fun c =>
    decide (layoutOrder cert.tyRank c < layoutOrder cert.tyRank p)

/-- Executable closure check: the children of every node are nodes. -/
def LayoutGraph.closed (g : LayoutGraph) : Bool :=
  g.nodes.all fun p => (g.children p).all fun c => g.nodes.contains c

/-- Soundness of the certificate checker. -/
theorem checkCert_sound (cert : ValidationRankCert) (g : LayoutGraph)
    (h : checkCert cert g = true) :
    ∀ p ∈ g.nodes, ∀ c ∈ g.children p, layoutOrder cert.tyRank c < layoutOrder cert.tyRank p := by
  intro p hp c hc
  simp only [checkCert, List.all_eq_true, decide_eq_true_eq] at h
  exact h p hp c hc

theorem LayoutGraph.closed_sound (g : LayoutGraph) (h : g.closed = true) :
    ∀ p ∈ g.nodes, ∀ c ∈ g.children p, c ∈ g.nodes := by
  intro p hp c hc
  simp only [LayoutGraph.closed, List.all_eq_true, List.contains_iff_mem] at h
  exact h p hp c hc

/-- Reachability through the graph's child edges (transitive closure). -/
inductive Reach (g : LayoutGraph) : LocalLayout → LocalLayout → Prop
  | edge {p c : LocalLayout} : p ∈ g.nodes → c ∈ g.children p → Reach g p c
  | trans {p q r : LocalLayout} : Reach g p q → Reach g q r → Reach g p r

/-- Under a valid certificate every reachable layout is strictly smaller. -/
theorem checkCert_reach_descends (cert : ValidationRankCert) (g : LayoutGraph)
    (h : checkCert cert g = true) {p q : LocalLayout} (hr : Reach g p q) :
    layoutOrder cert.tyRank q < layoutOrder cert.tyRank p := by
  induction hr with
  | edge hp hc => exact checkCert_sound cert g h _ hp _ hc
  | trans _ _ ih₁ ih₂ => omega

/-- A valid certificate excludes cycles. -/
theorem checkCert_acyclic (cert : ValidationRankCert) (g : LayoutGraph)
    (h : checkCert cert g = true) (p : LocalLayout) : ¬ Reach g p p := fun hr =>
  Nat.lt_irrefl _ (checkCert_reach_descends cert g h hr)

/-- Cyclic layout graphs are rejected by the checker for every rank table. -/
theorem checkCert_rejects_cycle (cert : ValidationRankCert) (g : LayoutGraph) (p : LocalLayout)
    (hr : Reach g p p) : checkCert cert g = false := by
  cases hc : checkCert cert g with
  | false => rfl
  | true => exact absurd hr (checkCert_acyclic cert g hc p)

/-! ## 3. Rank-guarded traversal over effectful projection hooks -/

/-- A rank-ordered traversal over effectful projection hooks in the real validity monad
`ValidityVisitor.M S = EStateM StepError S`. `Pl` is the visited place (a `RuntimePlace` for
`visit`, an offset layout for `unionRanges`) and `α` the accumulator (the `Session` for `visit`, a
`DataRangeSet` for `unionRanges`). -/
structure RankedWalk (S Pl α : Type) where
  /-- The Schema 17 rank map, read once from the state (`h.typeRank (← get)` in `lean-miri#90`). -/
  typeRank : Miri.MIR.TyId → Nat
  /-- The compiler layout of a place. -/
  layoutOf : Pl → LocalLayout
  /-- Per-node work before children (primitive checks, range marking, …). -/
  pre : Pl → α → M S α
  /-- Effectful child projection hook (fields, elements, variants, dynamic unpacking, …). -/
  children : Pl → M S (Array Pl)
  /-- `.invalidProgram` reason raised when a projected child does not descend. -/
  descendMsg : String := "validity projection does not descend"
  /-- `.resourceExhaustion` reason raised by the bounded-fuel traversal. -/
  fuelMsg : String := "validity traversal fuel"

namespace RankedWalk

variable {S Pl α : Type} (h : RankedWalk S Pl α)

/-- The traversal order of a place. -/
def order (p : Pl) : Nat := layoutOrder h.typeRank (h.layoutOf p)

/-- Fuel-free well-founded traversal (`lean-miri#90`): recursion is justified by the dynamic
descent guard at every projection hook result. -/
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

/-- Vendored-style bounded-fuel traversal: no descent guard, exhaustion at fuel `0` (the shape of
the pinned `ValidityVisitor.visit` / `unionRanges`). -/
def walkFuel : Nat → Pl → α → M S α
  | 0, _, _ => throw (.resourceExhaustion h.fuelMsg)
  | n + 1, p, acc => do
    let acc ← h.pre p acc
    let cs ← h.children p
    cs.toList.foldlM (fun acc c => walkFuel n c acc) acc

/-- The structural rank-fuelled companion: the canonical static fuel `order p + 1`. -/
def walkRank (p : Pl) (acc : α) : M S α := h.walkGuarded (h.order p + 1) p acc

/-- The hooks honour the rank certificate on `Good` places: every child they actually return
is `Good` and strictly descends. -/
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

/-- Any fuel above the order of the root makes the guarded traversal agree with `walkNoFuel`. -/
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

/-- The structural companion is the fuel-free traversal, unconditionally. -/
theorem walkRank_eq_walkNoFuel (p : Pl) (acc : α) : h.walkRank p acc = h.walkNoFuel p acc :=
  h.walkGuarded_eq_walkNoFuel _ p acc (Nat.lt_succ_self _)

theorem walkRank_eq_walkNoFuel' : h.walkRank = h.walkNoFuel := by
  funext p acc
  exact h.walkRank_eq_walkNoFuel p acc

/-- Under the rank certificate the dynamic guard never fires: the unguarded vendored-style
traversal equals the guarded one at every fuel (so small budgets exhaust identically). -/
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
identically with the fuel-free traversal whenever `fuel > order root`. -/
theorem walkFuel_eq_walkNoFuel (Good : Pl → Prop) (hd : h.DescendsOn Good) (n : Nat) (p : Pl)
    (acc : α) (hp : Good p) (hlt : h.order p < n) : h.walkFuel n p acc = h.walkNoFuel p acc :=
  (h.walkFuel_eq_walkGuarded Good hd n p acc hp).trans (h.walkGuarded_eq_walkNoFuel n p acc hlt)

/-- The canonical static fuel `order root + 1` suffices. -/
theorem walkFuel_rank_succ (Good : Pl → Prop) (hd : h.DescendsOn Good) (p : Pl) (acc : α)
    (hp : Good p) : h.walkFuel (h.order p + 1) p acc = h.walkNoFuel p acc :=
  h.walkFuel_eq_walkNoFuel Good hd _ p acc hp (Nat.lt_succ_self _)

/-- **Deterministic rejection.** If a projection hook returns a first child that does not
descend, the fuel-free traversal fails with `.invalidProgram` right after that hook. -/
theorem walkNoFuel_rejects_nondescending (p : Pl) (acc acc₁ : α) (c : Pl) (rest : List Pl)
    (s s₁ s₂ : S) (cs : Array Pl)
    (hpre : h.pre p acc s = .ok acc₁ s₁) (hch : h.children p s₁ = .ok cs s₂)
    (hcs : cs.toList = c :: rest) (hbad : ¬ h.order c < h.order p) :
    h.walkNoFuel p acc s = .error (.invalidProgram h.descendMsg) s₂ := by
  rw [walkNoFuel]
  simp only [bind, EStateM.bind, hpre, hch, hcs, List.foldlM_cons, hbad, ↓reduceDIte]
  rfl

end RankedWalk

/-! ### The two `lean-miri#90` instances and the LIFO pointee drain -/

/-- `visit`: sessions threaded through `RuntimePlace`s, in the real validity monad. -/
abbrev VisitWalk (P S : Type) := RankedWalk S (RuntimePlace P) (Session P)

/-- Fuel-free by-value validity traversal (`lean-miri#90` `visit`). -/
def visitNoFuel {P S : Type} (h : VisitWalk P S) (session : Session P) (place : RuntimePlace P) :
    M S (Session P) :=
  h.walkNoFuel place session

/-- `unionRanges`: data ranges accumulated over (layout, absolute offset) pairs. -/
abbrev UnionWalk (S : Type) := RankedWalk S (LocalLayout × Size) DataRangeSet

/-- Fuel-free union data-range walk (`lean-miri#90` `unionRanges`). -/
def unionRangesNoFuel {S : Type} (h : UnionWalk S) (layout : LocalLayout) (base : Size)
    (initial : DataRangeSet) : M S DataRangeSet :=
  h.walkNoFuel (layout, base) initial

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

/-- Draining pointees with the fuel-free by-value traversal. -/
def drainPointeesNoFuel {P S : Type} (h : VisitWalk P S)
    (tracking : RefTracking (Key P) ValidationPath) : M S Unit :=
  drainPointees tracking fun key path => do
    let _ ← visitNoFuel h (pointeeSession path) ⟨.memory key.mplace, key.layout⟩
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

/-- A valid, closed certificate makes the graph hooks descend on every node. -/
theorem ofGraph_descendsOn {S α : Type} (cert : ValidationRankCert) (g : LayoutGraph)
    (pre : LocalLayout → α → M S α) (hcert : checkCert cert g = true) (hclosed : g.closed = true) :
    (ofGraph cert g pre).DescendsOn (· ∈ g.nodes) := by
  intro p hp s cs s' hch
  simp only [ofGraph, pure, EStateM.pure, EStateM.Result.ok.injEq] at hch
  obtain ⟨rfl, -⟩ := hch
  intro c hc
  exact ⟨g.closed_sound hclosed p hp c hc, checkCert_sound cert g hcert p hp c hc⟩

/-- **Certificate adequacy.** For a valid closed certificate, bounded-fuel validation of any
node agrees with fuel-free validation for every `fuel > layoutOrder root`. -/
theorem certified_walkFuel_eq_walkNoFuel {S α : Type} (cert : ValidationRankCert) (g : LayoutGraph)
    (pre : LocalLayout → α → M S α) (hcert : checkCert cert g = true) (hclosed : g.closed = true)
    (root : LocalLayout) (hroot : root ∈ g.nodes) (acc : α) (fuel : Nat)
    (hfuel : layoutOrder cert.tyRank root < fuel) :
    (ofGraph cert g pre).walkFuel fuel root acc = (ofGraph cert g pre).walkNoFuel root acc :=
  (ofGraph cert g pre).walkFuel_eq_walkNoFuel _ (ofGraph_descendsOn cert g pre hcert hclosed)
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

/-- **Bridge.** Any budget under which the root's rank countdown converges in
`Anneal.ITreeWP.wpCoalBounded` is sufficient for bounded-fuel validation to agree with the
fuel-free traversal. -/
theorem walkFuel_eq_walkNoFuel_of_wpCoalBounded {S Pl α : Type} (h : RankedWalk S Pl α)
    (Good : Pl → Prop) (hd : h.DescendsOn Good) (fuel : Nat) (p : Pl) (acc : α) (hp : Good p)
    (s : PUnit) (hconv : wpCoalBounded fuel emptyWP rankCountdown (fun _ _ => True) (h.order p) s) :
    h.walkFuel fuel p acc = h.walkNoFuel p acc :=
  h.walkFuel_eq_walkNoFuel Good hd fuel p acc hp ((rankCountdown_converges_iff _ _ s).mp hconv)

end MirFuelFreeBridge

/-! ## 6. A 150-level nested single-field wrapper -/

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

/-- Depth 150 with the vendored-style bounded fuel `151` succeeds. -/
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

/-! ## 7. `leanprover/lean4#13851` axiom footprint audit

`lean4#13851` reimplements `WellFounded.fix` with `Classical.choice`, so every `termination_by`
definition (here `walkNoFuel` and its instances `visitNoFuel`, `unionRangesNoFuel`,
`drainPointeesNoFuel`), and every theorem whose statement mentions one, will acquire
`Classical.choice`. The structural (`Nat.rec`) companions do not use `WellFounded.fix`:

* the exact current footprints are pinned with `#guard_msgs` below: the structural companion
  `walkRank` and the vendored-style `walkFuel` are `Classical.choice`-free, and so is the
  well-founded `walkNoFuel` *today*;
* `#assert_choice_free` checks the structural layer (definitions and the certificate, adequacy-free
  and witness theorems that mention only structural definitions) against `{propext, Quot.sound}`;
  this must keep holding after `lean4#13851`;
* `#assert_standard_axioms` checks the well-founded layer against
  `{propext, Quot.sound, Classical.choice}`, which also keeps holding after `lean4#13851`.

Downstream developments that must stay `Classical.choice`-free should state results about
`walkRank` / `walkGuarded` and transport them along `walkRank_eq_walkNoFuel` only where the
well-founded entry point is needed. -/

/-- info: 'LeanMiriSpec.ValidationRankCert.RankedWalk.walkRank' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RankedWalk.walkRank

/-- info: 'LeanMiriSpec.ValidationRankCert.RankedWalk.walkFuel' does not depend on any axioms -/
#guard_msgs in
#print axioms RankedWalk.walkFuel

/-- info: 'LeanMiriSpec.ValidationRankCert.RankedWalk.walkNoFuel' depends on axioms: [propext] -/
#guard_msgs in
#print axioms RankedWalk.walkNoFuel

#assert_choice_free
  layoutOrder
  layoutOrder_lt_of_rank_lt
  layoutOrder_variant_lt
  layoutOrder_primitive_lt
  checkCert
  checkCert_sound
  checkCert_reach_descends
  checkCert_acyclic
  checkCert_rejects_cycle
  RankedWalk.walkGuarded
  RankedWalk.walkFuel
  RankedWalk.walkRank
  drainPointees
  drainPointees_push
  wrapper150_fuel151
  wrapper150_small_fuel_exhausts

#assert_standard_axioms
  RankedWalk.walkNoFuel
  visitNoFuel
  unionRangesNoFuel
  drainPointeesNoFuel
  RankedWalk.walkGuarded_eq_walkNoFuel
  RankedWalk.walkRank_eq_walkNoFuel
  RankedWalk.walkFuel_eq_walkGuarded
  RankedWalk.walkFuel_eq_walkNoFuel
  RankedWalk.walkFuel_rank_succ
  RankedWalk.walkNoFuel_rejects_nondescending
  ofGraph_descendsOn
  certified_walkFuel_eq_walkNoFuel
  rankCountdown_converges_iff
  rankCountdown_canonical
  walkFuel_eq_walkNoFuel_of_wpCoalBounded
  wrapper150_noFuel
  wrapper150_fuel151_eq_noFuel

end LeanMiriSpec.ValidationRankCert
