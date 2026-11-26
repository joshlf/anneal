-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Anneal.PTree
import Anneal.SepAC.Normalize
import Anneal.PureLift.SpatialMemV2026

/-!
# Lithium `PTree` Keyed Framing, $O(1)$ Symbolic `ByteRange`, & `V2026_06_01` Memory Framing (`RangeSpanV2026`)

Converges `google/zerocopy#4249` (`Anneal.SepAC.RangeSpan`) onto `unstable`'s unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics`, `Anneal.SepAC.Normalize`, `Anneal.PTree`, and
`Anneal.PureLift.SpatialMemV2026`:

1. **Part I — Canonical `PTree` Partial Commutative Monoid & Lithium Keyed Framing:**
   - Proves `ptree_disjoint_symm`, `ptree_union_assoc`, `ptree_disjoint_union_left_iff`,
     and `ptree_disjoint_union_right_iff` (`[]` zero axioms).
   - Defines `PHeapProp α := PTree α → Prop`, `PHeapEntails`, `pheapEmp`, `pheapPointsTo`,
     and `pheapSepConj`, instantiating `Anneal.SepAC.SepACULaws` directly via
     `pheapProp_sepACULaws` (`[]` zero axioms), proving `not_affineEntails_pheapProp`, and
     providing reflective ACU framing `frame_cancel` (combining `sepAC_entails_of_cancelAtoms`
     with `pheapProp_sepACULaws`).
   - Proves `LithiumTriple`, `ptree_set_lithiumTriple_exists`, `lithiumTriple_union_disjoint`,
     `lithiumFrame_of_diffWith`, and `lithiumFrame_diamond_comm`.
2. **Part II — $O(1)$ Symbolic `ByteRange` Algebra (`rangeSplit` / `rangeMerge`) & V2026 Overlap Bridge:**
   - Constant-size `ByteRange` (`allocId`, `start`, `len`), `InRange`, `RangeDisjoint`,
     computable `rangeDisjointBool` + `rangeDisjointBool_iff`, `rangeDisjoint_symm`,
     `rangeDisjoint_no_shared_offset`, `rangeSplit`, `rangeMerge`, `rangeSplit_disjoint`,
     `rangeMerge_split`, `rangeSplit_covers_iff`, `rangeDisjoint_of_subrange`, and exact
     bridge to unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.byteRangesOverlapBool`.
3. **Part III — Direct `V2026_06_01` `Memory` & `PureLift.SpatialMemV2026` Disjoint Byte-Range Soundness:**
   - `AllocBytesAtV2026` over unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.Memory`
     (`lookupGlobalAlloc` + `globalAllocSliceToAbstractBytes`), proving `ownRange_split_iff`
     and `allocBytesAtV2026_frame_of_write_disjoint` (both cross-allocation and same-allocation
     disjoint sub-ranges).
   - `AllocBytesAtByteMem` over `Anneal.PureLift.SpatialMemV2026.V2026ByteMem`, proving
     `allocBytesAtByteMem_split_iff`, `allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint`,
     `allocBytesAtByteMem_of_allocBytesAtV2026`, and direct framing over unmodified
     `sliceAbstractBytes` / `writeAbstractBytesAt`.
4. **Part IV — Reflective ACU `SepACULaws` over `V2026_06_01` `ByteRange` Assertions (`V2026RangeProp`):**
   - Byte-footprint separation logic `V2026RangeProp` directly over `Memory` obeying
     `SepACULaws` (`v2026RangeProp_sepACULaws`), linear non-affinity
     (`not_affineEntails_v2026RangeProp`), exact `rangeSplit` bientailment
     (`v2026RangePointsTo_split_bientails`), and reflective ACU framing (`v2026Range_frame_cancel`).
5. **Part V — Concrete Positive & Fail-Closed Negative Witnesses.**

Pass-1 hygiene: non-`module`, zero `Std.Do`/`MiniRustSpec`/`Miri`/`LeanMiriSpec`/`Lean` imports,
zero `omega`/`bv_decide`/`by_cases`/`grind`/`native_decide`/`._unsafe_rec`/`sorry`; axioms
strictly `⊆ {propext}`.
-/

namespace Anneal.SepAC.RangeSpanV2026

set_option autoImplicit false

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.PTree
open Anneal.SepAC
open Anneal.PureLift.SpatialMemV2026

/-! ## Part I: Canonical `PTree` PCM, `PHeapProp`, & Lithium Keyed Framing -/

/-- Symmetry of `PTree.DisjointProp` (`[]` zero axioms). -/
theorem ptree_disjoint_symm {α : Type} {a b : PTree α}
    (h : PTree.DisjointProp a b) : PTree.DisjointProp b a := by
  intro k
  cases h k with
  | inl ha => exact Or.inr ha
  | inr hb => exact Or.inl hb

/-- Empty left disjointness for `PTree` (`[]` zero axioms). -/
theorem ptree_disjoint_empty_left {α : Type} (t : PTree α) :
    PTree.DisjointProp PTree.empty t :=
  fun _ => Or.inl rfl

/-- Empty right disjointness for `PTree` (`[]` zero axioms). -/
theorem ptree_disjoint_empty_right {α : Type} (t : PTree α) :
    PTree.DisjointProp t PTree.empty :=
  fun _ => Or.inr rfl

/-- Associativity of `PTree.union` (`[]` zero axioms). -/
theorem ptree_union_assoc {α : Type} (a b c : PTree α) :
    PTree.union (PTree.union a b) c = PTree.union a (PTree.union b c) := by
  apply ptree_eq_of_get
  intro k
  rw [ptree_get_union, ptree_get_union, ptree_get_union, ptree_get_union]
  cases a.get k with
  | some _ => rfl
  | none =>
    cases b.get k <;> rfl

/-- Disjointness with a left `PTree.union` splits conjunctively (`[]` zero axioms). -/
theorem ptree_disjoint_union_left_iff {α : Type} (a b c : PTree α) :
    PTree.DisjointProp (PTree.union a b) c ↔
      PTree.DisjointProp a c ∧ PTree.DisjointProp b c := by
  refine ⟨?_, ?_⟩
  · intro h
    refine ⟨fun k => ?_, fun k => ?_⟩
    · cases h k with
      | inr hc => exact Or.inr hc
      | inl hab =>
        rw [ptree_get_union] at hab
        cases ha : a.get k with
        | none => exact Or.inl rfl
        | some _ =>
          rw [ha] at hab
          nomatch hab
    · cases h k with
      | inr hc => exact Or.inr hc
      | inl hab =>
        rw [ptree_get_union] at hab
        cases ha : a.get k with
        | some _ =>
          rw [ha] at hab
          nomatch hab
        | none =>
          rw [ha] at hab
          exact Or.inl hab
  · intro h k
    cases h.1 k with
    | inr hc => exact Or.inr hc
    | inl ha =>
      cases h.2 k with
      | inr hc => exact Or.inr hc
      | inl hb =>
        left
        rw [ptree_get_union, ha, hb]

/-- Disjointness with a right `PTree.union` splits conjunctively (`[]` zero axioms). -/
theorem ptree_disjoint_union_right_iff {α : Type} (a b c : PTree α) :
    PTree.DisjointProp a (PTree.union b c) ↔
      PTree.DisjointProp a b ∧ PTree.DisjointProp a c := by
  refine ⟨?_, ?_⟩
  · intro h
    have hSym :=
      (ptree_disjoint_union_left_iff b c a).mp (ptree_disjoint_symm h)
    exact ⟨ptree_disjoint_symm hSym.1, ptree_disjoint_symm hSym.2⟩
  · intro h
    exact ptree_disjoint_symm
      ((ptree_disjoint_union_left_iff b c a).mpr
        ⟨ptree_disjoint_symm h.1, ptree_disjoint_symm h.2⟩)

/-- Canonical separation-logic assertion over a keyed `PTree α` heap. -/
def PHeapProp (α : Type) : Type :=
  PTree α → Prop

/-- Entailment between canonical `PHeapProp α` assertions. -/
def PHeapEntails {α : Type} (P Q : PHeapProp α) : Prop :=
  ∀ h : PTree α, P h → Q h

/-- Empty `PTree` heap assertion (`h = PTree.empty`). -/
def pheapEmp {α : Type} : PHeapProp α :=
  fun h => h = PTree.empty

/-- Single-key `PTree` points-to assertion (`h = PTree.singleton k v`). -/
def pheapPointsTo {α : Type} (k : Pos) (v : α) : PHeapProp α :=
  fun h => h = PTree.singleton k v

/-- Separating conjunction over canonical `PTree α` heaps. -/
def pheapSepConj {α : Type} (P Q : PHeapProp α) : PHeapProp α :=
  fun h =>
    ∃ h₁ h₂ : PTree α,
      PTree.DisjointProp h₁ h₂ ∧ PTree.union h₁ h₂ = h ∧ P h₁ ∧ Q h₂

/-- `PHeapProp α` with `pheapSepConj`, `pheapEmp`, and `PHeapEntails` satisfies
`Anneal.SepAC.SepACULaws` natively (`[]` zero axioms), plugging canonical `PTree` heaps
directly into `Anneal.SepAC.Normalize`. -/
theorem pheapProp_sepACULaws (α : Type) :
    SepACULaws (@pheapSepConj α) (@pheapEmp α) (@PHeapEntails α) := by
  refine ⟨fun _ _ h => h, fun _ _ _ h12 h23 h hp => h23 h (h12 h hp),
    ?_, ?_, ?_, ?_⟩
  · intro F P Q hPQ h hSep
    cases hSep with
    | intro h1 hR =>
      cases hR with
      | intro h2 hC =>
        exact ⟨h1, h2, hC.1, hC.2.1, hC.2.2.1, hPQ h2 hC.2.2.2⟩
  · intro P Q R
    refine ⟨?_, ?_⟩
    · intro h hL
      cases hL with
      | intro h12 hR1 =>
        cases hR1 with
        | intro h3 hC1 =>
          cases hC1.2.2.1 with
          | intro h1 hR2 =>
            cases hR2 with
            | intro h2 hC2 =>
              have hD12_3 : PTree.DisjointProp (PTree.union h1 h2) h3 := by
                rw [hC2.2.1]
                exact hC1.1
              have hSplits := (ptree_disjoint_union_left_iff h1 h2 h3).mp hD12_3
              have hD1_23 : PTree.DisjointProp h1 (PTree.union h2 h3) :=
                (ptree_disjoint_union_right_iff h1 h2 h3).mpr ⟨hC2.1, hSplits.1⟩
              have hEq : PTree.union h1 (PTree.union h2 h3) = h := by
                rw [← ptree_union_assoc h1 h2 h3, hC2.2.1, hC1.2.1]
              exact ⟨h1, PTree.union h2 h3, hD1_23, hEq, hC2.2.2.1,
                ⟨h2, h3, hSplits.2, rfl, hC2.2.2.2, hC1.2.2.2⟩⟩
    · intro h hR
      cases hR with
      | intro h1 hR1 =>
        cases hR1 with
        | intro h23 hC1 =>
          cases hC1.2.2.2 with
          | intro h2 hR2 =>
            cases hR2 with
            | intro h3 hC2 =>
              have hD1_23 : PTree.DisjointProp h1 (PTree.union h2 h3) := by
                rw [hC2.2.1]
                exact hC1.1
              have hSplits := (ptree_disjoint_union_right_iff h1 h2 h3).mp hD1_23
              have hD12_3 : PTree.DisjointProp (PTree.union h1 h2) h3 :=
                (ptree_disjoint_union_left_iff h1 h2 h3).mpr ⟨hSplits.2, hC2.1⟩
              have hEq : PTree.union (PTree.union h1 h2) h3 = h := by
                rw [ptree_union_assoc h1 h2 h3, hC2.2.1, hC1.2.1]
              exact ⟨PTree.union h1 h2, h3, hD12_3, hEq,
                ⟨h1, h2, hSplits.1, rfl, hC1.2.2.1, hC2.2.2.1⟩, hC2.2.2.2⟩
  · intro P Q
    have hOneDir :
        ∀ (A B : PHeapProp α),
          PHeapEntails (pheapSepConj A B) (pheapSepConj B A) := by
      intro A B h hAB
      cases hAB with
      | intro h1 hR =>
        cases hR with
        | intro h2 hC =>
          refine ⟨h2, h1, ptree_disjoint_symm hC.1, ?_, hC.2.2.2, hC.2.2.1⟩
          rw [ptree_union_comm_of_disjoint (ptree_disjoint_symm hC.1)]
          exact hC.2.1
    exact ⟨hOneDir P Q, hOneDir Q P⟩
  · intro P
    refine ⟨?_, ?_⟩
    · intro h hPE
      cases hPE with
      | intro h1 hR =>
        cases hR with
        | intro h2 hC =>
          have h2Emp : h2 = PTree.empty := hC.2.2.2
          have hEq : h1 = h := by
            rw [h2Emp, ptree_union_empty_right h1] at hC
            exact hC.2.1
          rw [← hEq]
          exact hC.2.2.1
    · intro h hP
      exact ⟨h, PTree.empty, ptree_disjoint_empty_right h,
        ptree_union_empty_right h, hP, rfl⟩

/-- `PHeapProp α` is strictly linear (not affine) whenever `α` is inhabited (`[]` zero axioms). -/
theorem not_affineEntails_pheapProp {α : Type} (v₀ : α) :
    ¬ AffineEntails (@pheapEmp α) (@PHeapEntails α) := by
  intro hAff
  have hEq : PTree.singleton Pos.xH v₀ = PTree.empty :=
    hAff (pheapPointsTo Pos.xH v₀) (PTree.singleton Pos.xH v₀) rfl
  have hGet : (PTree.singleton Pos.xH v₀).get Pos.xH =
      (PTree.empty : PTree α).get Pos.xH :=
    congrArg (fun t => t.get Pos.xH) hEq
  nomatch hGet

/-- Reflective ACU bientailment on `PHeapProp α` via `SepAC.Normalize.sepAC_bientails_of_norm_eq`
(`[]` zero axioms). -/
theorem frame_bientails_of_norm_eq {α : Type} (env : Nat → PHeapProp α)
    {fuel : Nat} {e₁ e₂ : SepExpr}
    (hNorm : normSepFuel fuel e₁ = normSepFuel fuel e₂) :
    Bientails (@PHeapEntails α)
      (evalSepExprFuel pheapSepConj pheapEmp env fuel e₁)
      (evalSepExprFuel pheapSepConj pheapEmp env fuel e₂) :=
  sepAC_bientails_of_norm_eq (pheapProp_sepACULaws α) env hNorm

/-- Reflective keyed frame cancellation on `PHeapProp α`, combining
`SepAC.Normalize.sepAC_entails_of_cancelAtoms` with `pheapProp_sepACULaws` (`[]` zero axioms). -/
theorem frame_cancel {α : Type} (env : Nat → PHeapProp α)
    {fuel : Nat} {lhs rhs : SepExpr}
    (hRes :
      PHeapEntails
        (evalAtomList pheapSepConj pheapEmp env
          (cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).1)
        (evalAtomList pheapSepConj pheapEmp env
          (cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).2)) :
    PHeapEntails
      (evalSepExprFuel pheapSepConj pheapEmp env fuel lhs)
      (evalSepExprFuel pheapSepConj pheapEmp env fuel rhs) :=
  sepAC_entails_of_cancelAtoms (pheapProp_sepACULaws α) env hRes

/-- Local in-place framed transition over a canonical `PTree α` context:
preserves every disjoint frame `rem` while transforming `req` into `post`. -/
def LithiumTriple {α : Type} (req post : PTree α)
    (step : PTree α → Option (PTree α)) : Prop :=
  ∀ rem : PTree α,
    PTree.DisjointProp req rem →
    PTree.DisjointProp post rem ∧
      step (PTree.union req rem) = some (PTree.union post rem)

private theorem posBeq_refl_rs : ∀ p : Pos, Pos.beq p p = true
  | .xH => rfl
  | .xO q => posBeq_refl_rs q
  | .xI q => posBeq_refl_rs q

private theorem posEq_of_beq_true_rs :
    ∀ {p q : Pos}, Pos.beq p q = true → p = q
  | .xH, .xH, _ => rfl
  | .xH, .xO _, h => Bool.noConfusion h
  | .xH, .xI _, h => Bool.noConfusion h
  | .xO _, .xH, h => Bool.noConfusion h
  | .xO _, .xI _, h => Bool.noConfusion h
  | .xI _, .xH, h => Bool.noConfusion h
  | .xI _, .xO _, h => Bool.noConfusion h
  | .xO _, .xO _, h => congrArg Pos.xO (posEq_of_beq_true_rs h)
  | .xI _, .xI _, h => congrArg Pos.xI (posEq_of_beq_true_rs h)

/-- Concrete `LithiumTriple` inhabitation theorem (`[propext]` only) for an
in-place single-key `PTree.set` update `k ↦ v₁` to `k ↦ v₂`. -/
theorem ptree_set_lithiumTriple_exists {α : Type} (eqB : α → α → Bool)
    (hRefl : ∀ x : α, eqB x x = true) (k : Pos) (v₁ v₂ : α) :
    ∃ step : PTree α → Option (PTree α),
      LithiumTriple (PTree.singleton k v₁) (PTree.singleton k v₂) step := by
  let step : PTree α → Option (PTree α) := fun ctx =>
    match ctx.get k with
    | none => none
    | some v =>
      match eqB v v₁ with
      | true => some (ctx.set k v₂)
      | false => none
  refine ⟨step, ?_⟩
  intro rem hDisj
  have hRemK : rem.get k = none := by
    cases hDisj k with
    | inl hS =>
      dsimp only [PTree.singleton] at hS
      rw [ptree_get_set_same] at hS
      nomatch hS
    | inr hR => exact hR
  refine ⟨?_, ?_⟩
  · intro k'
    cases hEq : Pos.beq k k' with
    | true =>
      have hkEq : k = k' := posEq_of_beq_true_rs hEq
      rw [← hkEq]
      exact Or.inr hRemK
    | false =>
      have hkNe : k ≠ k' := fun heq => by
        rw [heq, posBeq_refl_rs] at hEq
        exact Bool.noConfusion hEq
      left
      dsimp only [PTree.singleton]
      rw [ptree_get_set_other PTree.empty k k' v₂ hkNe, ptree_get_empty]
  · dsimp only [step]
    rw [ptree_get_union]
    dsimp only [PTree.singleton]
    rw [ptree_get_set_same]
    dsimp only
    rw [hRefl v₁]
    dsimp only
    apply congrArg some
    apply ptree_eq_of_get
    intro k'
    cases hEq : Pos.beq k k' with
    | true =>
      have hkEq : k = k' := posEq_of_beq_true_rs hEq
      rw [← hkEq, ptree_get_set_same, ptree_get_union, ptree_get_set_same]
    | false =>
      have hkNe : k ≠ k' := fun heq => by
        rw [heq, posBeq_refl_rs] at hEq
        exact Bool.noConfusion hEq
      rw [ptree_get_set_other _ k k' v₂ hkNe, ptree_get_union,
        ptree_get_union, ptree_get_set_other PTree.empty k k' v₁ hkNe,
        ptree_get_set_other PTree.empty k k' v₂ hkNe, ptree_get_empty]

/-- Sequential composition of two `Option`-returning `PTree` transitions. -/
def ptreeBindStep {α : Type}
    (step₁ step₂ : PTree α → Option (PTree α)) (ctx : PTree α) :
    Option (PTree α) :=
  match step₁ ctx with
  | none => none
  | some mid => step₂ mid

/-- Disjoint footprint composition of two `LithiumTriple`s (`[]` zero axioms). -/
theorem lithiumTriple_union_disjoint {α : Type}
    {req₁ post₁ req₂ post₂ : PTree α}
    {step₁ step₂ : PTree α → Option (PTree α)}
    (hDreq : PTree.DisjointProp req₁ req₂)
    (hT1 : LithiumTriple req₁ post₁ step₁)
    (hT2 : LithiumTriple req₂ post₂ step₂) :
    LithiumTriple (PTree.union req₁ req₂) (PTree.union post₁ post₂)
      (ptreeBindStep step₁ step₂) := by
  intro rem hDisj
  have hParts := (ptree_disjoint_union_left_iff req₁ req₂ rem).mp hDisj
  have h1Rem :=
    (ptree_disjoint_union_right_iff req₁ req₂ rem).mpr ⟨hDreq, hParts.1⟩
  have hRes1 := hT1 (PTree.union req₂ rem) h1Rem
  have hP1Parts :=
    (ptree_disjoint_union_right_iff post₁ req₂ rem).mp hRes1.1
  have h2Rem :=
    (ptree_disjoint_union_right_iff req₂ post₁ rem).mpr
      ⟨ptree_disjoint_symm hP1Parts.1, hParts.2⟩
  have hRes2 := hT2 (PTree.union post₁ rem) h2Rem
  have hP2Parts :=
    (ptree_disjoint_union_right_iff post₂ post₁ rem).mp hRes2.1
  refine ⟨(ptree_disjoint_union_left_iff post₁ post₂ rem).mpr
      ⟨hP1Parts.2, hP2Parts.2⟩, ?_⟩
  dsimp only [ptreeBindStep]
  rw [ptree_union_assoc req₁ req₂ rem, hRes1.2]
  dsimp only
  rw [← ptree_union_assoc post₁ req₂ rem,
    ptree_union_comm_of_disjoint hP1Parts.1,
    ptree_union_assoc req₂ post₁ rem, hRes2.2,
    ← ptree_union_assoc post₂ post₁ rem,
    ptree_union_comm_of_disjoint hP2Parts.1,
    ptree_union_assoc post₁ post₂ rem]

/-- Lithium deterministic non-backtracking frame rule (`[]` zero axioms): a
single `PTree.diffWith eqB ctx req = some rem` pass splits `ctx = req ⊎ rem`
and lifts any `LithiumTriple req post step` onto `ctx` without context search. -/
theorem lithiumFrame_of_diffWith {α : Type} (eqB : α → α → Bool)
    (hSoundEq : ∀ {x y : α}, eqB x y = true → x = y)
    {ctx req post rem : PTree α} {step : PTree α → Option (PTree α)}
    (hDiff : PTree.diffWith eqB ctx req = some rem)
    (hTr : LithiumTriple req post step) :
    PTree.DisjointProp req rem ∧
    PTree.DisjointProp post rem ∧
    step ctx = some (PTree.union post rem) := by
  have hSplit := ptree_diffWith_sound eqB hSoundEq hDiff
  have hRes := hTr rem hSplit.1
  rw [hSplit.2] at hRes
  exact ⟨hSplit.1, hRes.1, hRes.2⟩

/-- Canonical `PTree.union` commutation lemma (`[]` zero axioms). -/
theorem lithiumFrame_diamond_comm {α : Type}
    {post₁ post₂ rem : PTree α}
    (hD12 : PTree.DisjointProp post₁ post₂) :
    PTree.union post₁ (PTree.union post₂ rem) =
      PTree.union post₂ (PTree.union post₁ rem) := by
  rw [← ptree_union_assoc post₁ post₂ rem,
    ptree_union_comm_of_disjoint hD12,
    ptree_union_assoc post₂ post₁ rem]

/-! ## Part II: $O(1)$ Symbolic `ByteRange` Algebra & `V2026_06_01` Overlap Bridge -/

/-- Constant-size half-open byte range `[start, start + len)` inside allocation
`allocId : Trusted.Rustc.V2026_06_01.MirAst.AllocId`, scaling flatly to
`len = 1_000_000+` without per-byte points-to materialization. -/
structure ByteRange where
  allocId : AllocId
  start : Nat
  len : Nat
  deriving DecidableEq

/-- Byte membership predicate: `(aid, off)` lies inside `r`. -/
def InRange (r : ByteRange) (aid : AllocId) (off : Nat) : Prop :=
  r.allocId = aid ∧ r.start ≤ off ∧ off < r.start + r.len

/-- Disjointness between two `ByteRange`s: either distinct allocations or
non-overlapping half-open byte intervals. -/
def RangeDisjoint (r₁ r₂ : ByteRange) : Prop :=
  r₁.allocId ≠ r₂.allocId ∨
    r₁.start + r₁.len ≤ r₂.start ∨
    r₂.start + r₂.len ≤ r₁.start

/-- Computable $O(1)$ boolean decision procedure for `RangeDisjoint` (`0` `._unsafe_rec`). -/
def rangeDisjointBool (r₁ r₂ : ByteRange) : Bool :=
  (!Nat.beq r₁.allocId r₂.allocId) ||
    Nat.ble (r₁.start + r₁.len) r₂.start ||
    Nat.ble (r₂.start + r₂.len) r₁.start

private theorem natBeq_refl_rs : ∀ a : Nat, Nat.beq a a = true
  | 0 => rfl
  | n + 1 => natBeq_refl_rs n

private theorem natEq_of_beq_rs : ∀ {a b : Nat}, Nat.beq a b = true → a = b
  | 0, 0, _ => rfl
  | 0, _ + 1, h => Bool.noConfusion h
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => congrArg Nat.succ (natEq_of_beq_rs h)

private theorem natLe_of_ble_rs : ∀ {a b : Nat}, Nat.ble a b = true → a ≤ b
  | 0, b, _ => Nat.zero_le b
  | _ + 1, 0, h => Bool.noConfusion h
  | _ + 1, _ + 1, h => Nat.succ_le_succ (natLe_of_ble_rs h)

private theorem natBle_of_le_rs : ∀ {a b : Nat}, a ≤ b → Nat.ble a b = true
  | 0, _, _ => rfl
  | Nat.succ _, 0, h => nomatch h
  | Nat.succ a, Nat.succ b, h =>
    @natBle_of_le_rs a b (Nat.le_of_succ_le_succ h)

private theorem natBle_false_of_lt_rs {a b : Nat} (h : b < a) :
    Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge (natLe_of_ble_rs hb) h)

/-- Boolean reflection equivalence `rangeDisjointBool r₁ r₂ = true ↔ RangeDisjoint r₁ r₂`
(`[]` zero axioms). -/
theorem rangeDisjointBool_iff (r₁ r₂ : ByteRange) :
    rangeDisjointBool r₁ r₂ = true ↔ RangeDisjoint r₁ r₂ := by
  dsimp only [rangeDisjointBool, RangeDisjoint]
  refine ⟨?_, ?_⟩
  · intro h
    cases hId : Nat.beq r₁.allocId r₂.allocId with
    | false =>
      left
      intro hEq
      rw [hEq, natBeq_refl_rs] at hId
      exact Bool.noConfusion hId
    | true =>
      rw [hId] at h
      cases h12 : Nat.ble (r₁.start + r₁.len) r₂.start with
      | true => exact Or.inr (Or.inl (natLe_of_ble_rs h12))
      | false =>
        rw [h12] at h
        exact Or.inr (Or.inr (natLe_of_ble_rs h))
  · intro h
    cases h with
    | inl hNe =>
      cases hId : Nat.beq r₁.allocId r₂.allocId with
      | false => rfl
      | true => exact False.elim (hNe (natEq_of_beq_rs hId))
    | inr hInt =>
      cases hInt with
      | inl h12 =>
        rw [natBle_of_le_rs h12]
        cases Nat.beq r₁.allocId r₂.allocId <;> rfl
      | inr h21 =>
        rw [natBle_of_le_rs h21]
        cases Nat.beq r₁.allocId r₂.allocId <;>
          cases Nat.ble (r₁.start + r₁.len) r₂.start <;> rfl

/-- Symmetry of `RangeDisjoint` (`[]` zero axioms). -/
theorem rangeDisjoint_symm {r₁ r₂ : ByteRange} (h : RangeDisjoint r₁ r₂) :
    RangeDisjoint r₂ r₁ := by
  cases h with
  | inl hNe => exact Or.inl (fun heq => hNe heq.symm)
  | inr hInt =>
    cases hInt with
    | inl h12 => exact Or.inr (Or.inr h12)
    | inr h21 => exact Or.inr (Or.inl h21)

/-- Two disjoint `ByteRange`s share no `(allocId, offset)` byte (`[]` zero axioms). -/
theorem rangeDisjoint_no_shared_offset {r₁ r₂ : ByteRange} {aid : AllocId}
    {off : Nat} (hD : RangeDisjoint r₁ r₂)
    (h1 : InRange r₁ aid off) (h2 : InRange r₂ aid off) : False := by
  cases hD with
  | inl hNe => exact hNe (Eq.trans h1.1 h2.1.symm)
  | inr hInt =>
    cases hInt with
    | inl h12 =>
      exact Nat.not_lt_of_ge (Nat.le_trans h12 h2.2.1) h1.2.2
    | inr h21 =>
      exact Nat.not_lt_of_ge (Nat.le_trans h21 h1.2.1) h2.2.2

/-- $O(1)$ `slice::split_at_mut` descriptor split at index `k`. -/
def rangeSplit (r : ByteRange) (k : Nat) : ByteRange × ByteRange :=
  (⟨r.allocId, r.start, k⟩, ⟨r.allocId, r.start + k, r.len - k⟩)

/-- $O(1)$ total adjacent-range combiner characterized on split halves by `rangeMerge_split`. -/
def rangeMerge (rL rR : ByteRange) : ByteRange :=
  ⟨rL.allocId, rL.start, rL.len + rR.len⟩

/-- Both halves produced by `rangeSplit r k` are unconditionally disjoint (`[]` zero axioms). -/
theorem rangeSplit_disjoint (r : ByteRange) (k : Nat) :
    RangeDisjoint (rangeSplit r k).1 (rangeSplit r k).2 :=
  Or.inr (Or.inl (Nat.le_refl (r.start + k)))

private theorem natSub_add_cancel_rs :
    ∀ {k n : Nat}, k ≤ n → k + (n - k) = n
  | 0, n, _ => by
    rw [Nat.zero_add, Nat.sub_zero]
  | _ + 1, 0, h => nomatch h
  | k + 1, n + 1, h => by
    rw [Nat.succ_sub_succ, Nat.succ_add]
    exact congrArg Nat.succ (natSub_add_cancel_rs (Nat.le_of_succ_le_succ h))

/-- Re-merging `rangeSplit r k` recovers `r` identically whenever `k ≤ r.len`
(`[]` zero axioms). -/
theorem rangeMerge_split (r : ByteRange) {k : Nat} (hk : k ≤ r.len) :
    rangeMerge (rangeSplit r k).1 (rangeSplit r k).2 = r := by
  cases r with
  | mk aid st len =>
    dsimp only [rangeMerge, rangeSplit]
    rw [natSub_add_cancel_rs hk]

/-- Fail-closed $O(1)$ adjacent `ByteRange` merger (`0` `._unsafe_rec`): returns
`some (rangeMerge rL rR)` iff `rL` and `rR` belong to the same allocation and
`rL.start + rL.len = rR.start` (rejecting non-adjacent or cross-allocation ranges). -/
def rangeMergeChecked (rL rR : ByteRange) : Option ByteRange :=
  match Nat.beq rL.allocId rR.allocId && Nat.beq (rL.start + rL.len) rR.start with
  | true => some (rangeMerge rL rR)
  | false => none

/-- Checked re-merge of `rangeSplit r k` succeeds with `some r` whenever `k ≤ r.len`
(`[]` zero axioms). -/
theorem rangeMergeChecked_split (r : ByteRange) {k : Nat} (hk : k ≤ r.len) :
    rangeMergeChecked (rangeSplit r k).1 (rangeSplit r k).2 = some r := by
  unfold rangeMergeChecked
  dsimp only [rangeSplit]
  rw [natBeq_refl_rs r.allocId, natBeq_refl_rs (r.start + k)]
  dsimp only [Bool.and]
  exact congrArg some (rangeMerge_split r hk)

/-- Soundness of `rangeMergeChecked` (`[]` zero axioms): success guarantees same-allocation
adjacency, disjointness, and exact equality with `rangeMerge rL rR`. -/
theorem rangeMergeChecked_sound {rL rR rM : ByteRange}
    (h : rangeMergeChecked rL rR = some rM) :
    rL.allocId = rR.allocId ∧
    rL.start + rL.len = rR.start ∧
    RangeDisjoint rL rR ∧
    rM = rangeMerge rL rR := by
  unfold rangeMergeChecked at h
  cases hId : Nat.beq rL.allocId rR.allocId with
  | false => rw [hId] at h; nomatch h
  | true =>
    rw [hId] at h
    cases hAdj : Nat.beq (rL.start + rL.len) rR.start with
    | false => rw [hAdj] at h; nomatch h
    | true =>
      rw [hAdj] at h
      dsimp only [Bool.and] at h
      injection h with hEqM
      have hSame := natEq_of_beq_rs hId
      have hAd := natEq_of_beq_rs hAdj
      have hDisj : RangeDisjoint rL rR := Or.inr (Or.inl (by rw [hAd]; exact Nat.le_refl _))
      exact ⟨hSame, hAd, hDisj, hEqM.symm⟩

/-- Exact byte coverage of `rangeSplit r k` (`[]` zero axioms): when `k ≤ r.len`,
`(aid, off)` lies in `r` iff it lies in the left or right half. -/
theorem rangeSplit_covers_iff (r : ByteRange) {k : Nat} (hk : k ≤ r.len)
    (aid : AllocId) (off : Nat) :
    InRange r aid off ↔
      InRange (rangeSplit r k).1 aid off ∨
      InRange (rangeSplit r k).2 aid off := by
  have hEnd : r.start + k + (r.len - k) = r.start + r.len := by
    rw [Nat.add_assoc, natSub_add_cancel_rs hk]
  dsimp only [InRange, rangeSplit]
  refine ⟨?_, ?_⟩
  · intro hIn
    cases Nat.lt_or_ge off (r.start + k) with
    | inl hLt => exact Or.inl ⟨hIn.1, hIn.2.1, hLt⟩
    | inr hGe =>
      right
      refine ⟨hIn.1, hGe, ?_⟩
      rw [hEnd]
      exact hIn.2.2
  · intro hOr
    cases hOr with
    | inl hL =>
      refine ⟨hL.1, hL.2.1, Nat.lt_of_lt_of_le hL.2.2 ?_⟩
      exact Nat.add_le_add_left hk r.start
    | inr hR =>
      refine ⟨hR.1, Nat.le_trans (Nat.le_add_right r.start k) hR.2.1, ?_⟩
      rw [← hEnd]
      exact hR.2.2

/-- Disjointness descends from a parent `ByteRange` to both halves of
`rangeSplit r k` whenever `k ≤ r.len` (`[]` zero axioms). -/
theorem rangeDisjoint_of_subrange {r rOther : ByteRange} {k : Nat}
    (hk : k ≤ r.len) (hD : RangeDisjoint r rOther) :
    RangeDisjoint (rangeSplit r k).1 rOther ∧
    RangeDisjoint (rangeSplit r k).2 rOther := by
  have hEnd : r.start + k + (r.len - k) = r.start + r.len := by
    rw [Nat.add_assoc, natSub_add_cancel_rs hk]
  cases hD with
  | inl hNe => exact ⟨Or.inl hNe, Or.inl hNe⟩
  | inr hInt =>
    cases hInt with
    | inl hLe =>
      dsimp only [rangeSplit]
      refine ⟨Or.inr (Or.inl
        (Nat.le_trans (Nat.add_le_add_left hk r.start) hLe)),
        Or.inr (Or.inl ?_)⟩
      rw [hEnd]
      exact hLe
    | inr hGe =>
      exact ⟨Or.inr (Or.inr hGe),
        Or.inr (Or.inr (Nat.le_trans hGe (Nat.le_add_right r.start k)))⟩

/-- Direct bridge to unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.byteRangesOverlapBool`
(`[]` zero axioms): same-allocation `RangeDisjoint` implies `byteRangesOverlapBool = false`. -/
theorem byteRangesOverlapBool_false_of_sameAlloc_rangeDisjoint
    {r₁ r₂ : ByteRange} (hSame : r₁.allocId = r₂.allocId)
    (hDisj : RangeDisjoint r₁ r₂) :
    byteRangesOverlapBool r₁.start r₁.len r₂.start r₂.len = false := by
  dsimp only [byteRangesOverlapBool]
  cases hDisj with
  | inl hNe => exact False.elim (hNe hSame)
  | inr hInt =>
    cases hInt with
    | inl h12 =>
      have hF : Nat.ble (Nat.succ r₂.start) (Nat.add r₁.start r₁.len) = false :=
        natBle_false_of_lt_rs (Nat.lt_succ_of_le h12)
      rw [hF]
      cases Nat.beq r₁.len 0 <;> cases Nat.beq r₂.len 0 <;>
        cases Nat.ble (Nat.succ r₁.start) (Nat.add r₂.start r₂.len) <;> rfl
    | inr h21 =>
      have hF : Nat.ble (Nat.succ r₁.start) (Nat.add r₂.start r₂.len) = false :=
        natBle_false_of_lt_rs (Nat.lt_succ_of_le h21)
      rw [hF]
      cases Nat.beq r₁.len 0 <;> cases Nat.beq r₂.len 0 <;> rfl

/-- Exact converse for positive-length same-allocation ranges (`[]` zero axioms):
`byteRangesOverlapBool r₁.start r₁.len r₂.start r₂.len = false ↔ RangeDisjoint r₁ r₂`. -/
theorem byteRangesOverlapBool_false_iff_rangeDisjoint_pos
    {r₁ r₂ : ByteRange} (hSame : r₁.allocId = r₂.allocId)
    (hPos1 : 0 < r₁.len) (hPos2 : 0 < r₂.len) :
    byteRangesOverlapBool r₁.start r₁.len r₂.start r₂.len = false ↔
      RangeDisjoint r₁ r₂ := by
  refine ⟨?_, byteRangesOverlapBool_false_of_sameAlloc_rangeDisjoint hSame⟩
  intro hF
  have hNe1 : Nat.beq r₁.len 0 = false := by
    cases hL : r₁.len with
    | zero => rw [hL] at hPos1; exact False.elim (Nat.lt_irrefl 0 hPos1)
    | succ _ => rfl
  have hNe2 : Nat.beq r₂.len 0 = false := by
    cases hL : r₂.len with
    | zero => rw [hL] at hPos2; exact False.elim (Nat.lt_irrefl 0 hPos2)
    | succ _ => rfl
  dsimp only [byteRangesOverlapBool] at hF
  rw [hNe1, hNe2] at hF
  cases hA : Nat.ble (Nat.succ r₁.start) (Nat.add r₂.start r₂.len) with
  | false =>
    cases Nat.lt_or_ge r₁.start (r₂.start + r₂.len) with
    | inl hLt =>
      have hT : Nat.ble (Nat.succ r₁.start) (Nat.add r₂.start r₂.len) = true :=
        natBle_of_le_rs hLt
      rw [hT] at hA
      exact Bool.noConfusion hA
    | inr hGe => exact Or.inr (Or.inr hGe)
  | true =>
    rw [hA] at hF
    cases hB : Nat.ble (Nat.succ r₂.start) (Nat.add r₁.start r₁.len) with
    | true =>
      rw [hB] at hF
      exact Bool.noConfusion hF
    | false =>
      cases Nat.lt_or_ge r₂.start (r₁.start + r₁.len) with
      | inl hLt =>
        have hT : Nat.ble (Nat.succ r₂.start) (Nat.add r₁.start r₁.len) = true :=
          natBle_of_le_rs hLt
        rw [hT] at hB
        exact Bool.noConfusion hB
      | inr hGe => exact Or.inr (Or.inl hGe)

/-! ## Part III: Direct `V2026_06_01.MirSemantics.Memory` & `SpatialMemV2026` Framing -/

private theorem listDrop_nil_rs {α : Type} :
    ∀ k : Nat, ([] : List α).drop k = []
  | 0 => rfl
  | _ + 1 => rfl

private theorem listDrop_drop_rs {α : Type} :
    ∀ (m n : Nat) (xs : List α), (xs.drop m).drop n = xs.drop (m + n)
  | 0, n, xs => by
    rw [Nat.zero_add]
    rfl
  | m + 1, n, [] => by
    change ([] : List α).drop n = ([] : List α).drop (m + 1 + n)
    rw [listDrop_nil_rs, listDrop_nil_rs]
  | m + 1, n, _ :: xs => by
    rw [Nat.succ_add]
    exact listDrop_drop_rs m n xs

private theorem listTake_add_rs {α : Type} :
    ∀ (a b : Nat) (xs : List α),
      xs.take (a + b) = xs.take a ++ (xs.drop a).take b
  | 0, b, xs => by
    rw [Nat.zero_add]
    rfl
  | a + 1, b, [] => by
    rw [Nat.succ_add]
    change [] = [] ++ (([] : List α).drop (a + 1)).take b
    rw [listDrop_nil_rs]
    cases b <;> rfl
  | a + 1, b, x :: xs => by
    rw [Nat.succ_add]
    exact congrArg (List.cons x) (listTake_add_rs a b xs)

private theorem listTake_take_of_le_rs {α : Type} :
    ∀ (a b : Nat) (xs : List α), a ≤ b → (xs.take b).take a = xs.take a
  | 0, _, _, _ => rfl
  | _ + 1, 0, _, h => nomatch h
  | _ + 1, _ + 1, [], _ => rfl
  | a + 1, b + 1, x :: xs, h =>
    congrArg (List.cons x)
      (listTake_take_of_le_rs a b xs (Nat.le_of_succ_le_succ h))

private theorem listDrop_take_rs {α : Type} :
    ∀ (a b : Nat) (xs : List α), (xs.take b).drop a = (xs.drop a).take (b - a)
  | 0, _, xs => by
    rw [Nat.sub_zero]
    rfl
  | a + 1, 0, _ => by
    change ([] : List α).drop (a + 1) =
      ((_ : List α).drop (a + 1)).take (0 - (a + 1))
    rw [listDrop_nil_rs]
    have hZ : 0 - (a + 1) = 0 := Nat.zero_sub (a + 1)
    rw [hZ]
    rfl
  | _ + 1, _ + 1, [] => by
    rw [Nat.succ_sub_succ]
    change ([] : List α).drop _ = ([] : List α).take _
    rw [listDrop_nil_rs]
    cases (_ : Nat) - _ <;> rfl
  | a + 1, b + 1, _ :: xs => by
    rw [Nat.succ_sub_succ]
    exact listDrop_take_rs a b xs

private theorem listSplit_take_drop_rs {α : Type} :
    ∀ (k : Nat) (bs : List α), bs.take k ++ bs.drop k = bs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | k + 1, b :: bs => congrArg (List.cons b) (listSplit_take_drop_rs k bs)

private theorem listLength_take_of_le_rs {α : Type} :
    ∀ (k : Nat) (bs : List α), k ≤ bs.length → (bs.take k).length = k
  | 0, _, _ => rfl
  | _ + 1, [], h => nomatch h
  | k + 1, _ :: bs, h =>
    congrArg Nat.succ (listLength_take_of_le_rs k bs (Nat.le_of_succ_le_succ h))

private theorem listLength_drop_rs {α : Type} :
    ∀ (k : Nat) (bs : List α), (bs.drop k).length = bs.length - k
  | 0, _ => rfl
  | k + 1, [] => by
    change 0 = 0 - (k + 1)
    rw [Nat.zero_sub]
  | k + 1, _ :: bs => by
    change (bs.drop k).length = (bs.length + 1) - (k + 1)
    rw [Nat.succ_sub_succ, listLength_drop_rs k bs]

private theorem listTake_append_prefix_rs {α : Type} :
    ∀ (xs ys : List α), (xs ++ ys).take xs.length = xs
  | [], _ => rfl
  | x :: xs, ys => congrArg (List.cons x) (listTake_append_prefix_rs xs ys)

private theorem listDrop_append_ge_rs {α : Type} :
    ∀ (xs ys : List α) {n : Nat},
      xs.length ≤ n → (xs ++ ys).drop n = ys.drop (n - xs.length)
  | [], ys, n, _ => by
    change ys.drop n = ys.drop (n - 0)
    rw [Nat.sub_zero]
  | _ :: _, _, 0, h => nomatch h
  | _ :: xs, ys, n + 1, h => by
    change (xs ++ ys).drop n = ys.drop ((n + 1) - (xs.length + 1))
    rw [Nat.succ_sub_succ]
    exact listDrop_append_ge_rs xs ys (Nat.le_of_succ_le_succ h)

private theorem listDrop_take_inside_prefix {α : Type} (xs : List α)
    {a b n : Nat} (hLe : a + b ≤ n) :
    ((xs.take n).drop a).take b = (xs.drop a).take b := by
  rw [listDrop_take_rs a n xs]
  have hbLe : b ≤ n - a := by
    have hSub := Nat.sub_le_sub_right hLe a
    rw [Nat.add_sub_cancel_left] at hSub
    exact hSub
  exact listTake_take_of_le_rs b (n - a) (xs.drop a) hbLe

private theorem listSlice_splice_left {α : Type} (xs mid : List α)
    {wStart fStart fLen : Nat}
    (hWLe : wStart ≤ xs.length)
    (hBefore : fStart + fLen ≤ wStart) :
    ((((xs.take wStart ++ mid) ++
        xs.drop (wStart + mid.length)).drop fStart).take fLen) =
      (xs.drop fStart).take fLen := by
  let spliced := (xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)
  have hTakeW : spliced.take wStart = xs.take wStart := by
    dsimp only [spliced]
    rw [List.append_assoc]
    have hLen : (xs.take wStart).length = wStart :=
      listLength_take_of_le_rs wStart xs hWLe
    have hPref := listTake_append_prefix_rs (xs.take wStart)
      (mid ++ xs.drop (wStart + mid.length))
    rw [hLen] at hPref
    exact hPref
  rw [← listDrop_take_inside_prefix spliced hBefore, hTakeW,
    listDrop_take_inside_prefix xs hBefore]

private theorem listSlice_splice_right {α : Type} (xs mid : List α)
    {wStart fStart fLen : Nat}
    (hWLe : wStart ≤ xs.length)
    (hAfter : wStart + mid.length ≤ fStart) :
    ((((xs.take wStart ++ mid) ++
        xs.drop (wStart + mid.length)).drop fStart).take fLen) =
      (xs.drop fStart).take fLen := by
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, listLength_take_of_le_rs wStart xs hWLe]
  have hDrop :
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)).drop fStart =
        xs.drop fStart := by
    rw [listDrop_append_ge_rs (xs.take wStart ++ mid)
      (xs.drop (wStart + mid.length)) (by rw [hPreLen]; exact hAfter)]
    rw [hPreLen, listDrop_drop_rs (wStart + mid.length)
      (fStart - (wStart + mid.length)) xs, natSub_add_cancel_rs hAfter]
  rw [hDrop]

private theorem listGet_append_left_rs {α : Type} :
    ∀ (xs ys : List α) (i : Nat), i < xs.length →
      Trusted.Sequence.get? (xs ++ ys) i = Trusted.Sequence.get? xs i
  | [], _, _, hLt => nomatch hLt
  | _ :: _, _, 0, _ => rfl
  | _ :: xs, ys, i + 1, hLt =>
    listGet_append_left_rs xs ys i (Nat.lt_of_succ_lt_succ hLt)

private theorem listGet_append_right_rs {α : Type} :
    ∀ (xs ys : List α) (i : Nat), xs.length ≤ i →
      Trusted.Sequence.get? (xs ++ ys) i = Trusted.Sequence.get? ys (i - xs.length)
  | [], ys, i, _ => by
    change Trusted.Sequence.get? ys i = Trusted.Sequence.get? ys (i - 0)
    rw [Nat.sub_zero]
  | _ :: _, _, 0, hLe => nomatch hLe
  | _ :: xs, ys, i + 1, hLe => by
    change Trusted.Sequence.get? (xs ++ ys) i =
      Trusted.Sequence.get? ys ((i + 1) - (xs.length + 1))
    rw [Nat.succ_sub_succ]
    exact listGet_append_right_rs xs ys i (Nat.le_of_succ_le_succ hLe)

private theorem listGet_take_lt_rs {α : Type} :
    ∀ (n : Nat) (xs : List α) (i : Nat), i < n →
      Trusted.Sequence.get? (xs.take n) i = Trusted.Sequence.get? xs i
  | 0, _, _, hLt => nomatch hLt
  | _ + 1, [], _, _ => rfl
  | _ + 1, _ :: _, 0, _ => rfl
  | n + 1, _ :: xs, i + 1, hLt =>
    listGet_take_lt_rs n xs i (Nat.lt_of_succ_lt_succ hLt)

private theorem listGet_drop_rs {α : Type} :
    ∀ (n : Nat) (xs : List α) (i : Nat),
      Trusted.Sequence.get? (xs.drop n) i = Trusted.Sequence.get? xs (n + i)
  | 0, xs, i => by
    rw [Nat.zero_add]
    rfl
  | n + 1, [], i => by
    rw [listDrop_nil_rs, Nat.succ_add]
    rfl
  | n + 1, _ :: xs, i => by
    rw [Nat.succ_add]
    exact listGet_drop_rs n xs i

private theorem listGet_splice_lt {α : Type} (xs mid : List α)
    {wStart i : Nat} (hWLe : wStart ≤ xs.length) (hLt : i < wStart) :
    Trusted.Sequence.get?
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)) i =
      Trusted.Sequence.get? xs i := by
  have hTakeLen : (xs.take wStart).length = wStart :=
    listLength_take_of_le_rs wStart xs hWLe
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, hTakeLen]
  have hLtPre : i < (xs.take wStart ++ mid).length := by
    rw [hPreLen]
    exact Nat.lt_of_lt_of_le hLt (Nat.le_add_right wStart mid.length)
  rw [listGet_append_left_rs (xs.take wStart ++ mid) _ i hLtPre,
    listGet_append_left_rs (xs.take wStart) mid i (by rw [hTakeLen]; exact hLt),
    listGet_take_lt_rs wStart xs i hLt]

private theorem listGet_splice_ge {α : Type} (xs mid : List α)
    {wStart i : Nat} (hWLe : wStart ≤ xs.length) (hGe : wStart + mid.length ≤ i) :
    Trusted.Sequence.get?
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)) i =
      Trusted.Sequence.get? xs i := by
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, listLength_take_of_le_rs wStart xs hWLe]
  rw [listGet_append_right_rs (xs.take wStart ++ mid) _ i (by rw [hPreLen]; exact hGe),
    hPreLen, listGet_drop_rs (wStart + mid.length) xs (i - (wStart + mid.length)),
    natSub_add_cancel_rs hGe]

private theorem globalAllocBytesAux_split
    (bytes : List (Option UInt8)) (relocs : List (Nat × ProvenancePtr)) :
    ∀ (a b start : Nat) (bs : List AbstractByte),
      globalAllocBytesAux bytes relocs start (a + b) = some bs ↔
        ∃ bsL bsR : List AbstractByte,
          globalAllocBytesAux bytes relocs start a = some bsL ∧
          globalAllocBytesAux bytes relocs (start + a) b = some bsR ∧
          bs = bsL ++ bsR
  | 0, b, start, bs => by
    rw [Nat.zero_add, Nat.add_zero]
    refine ⟨fun h => ⟨[], bs, rfl, h, rfl⟩, ?_⟩
    intro hEx
    cases hEx with
    | intro bsL hR =>
      cases hR with
      | intro bsR hC =>
        injection hC.1 with hNil
        rw [← hNil] at hC
        rw [hC.2.2]
        exact hC.2.1
  | a + 1, b, start, bs => by
    rw [Nat.succ_add]
    refine ⟨?_, ?_⟩
    · intro h
      unfold globalAllocBytesAux at h
      cases hGet : Trusted.Sequence.get? bytes start with
      | none => rw [hGet] at h; nomatch h
      | some optB =>
        rw [hGet] at h
        cases hRest : globalAllocBytesAux bytes relocs (start + 1) (a + b) with
        | none => rw [hRest] at h; nomatch h
        | some restBs =>
          rw [hRest] at h
          injection h with hBsEq
          have hSub :=
            (globalAllocBytesAux_split bytes relocs a b (start + 1) restBs).mp hRest
          cases hSub with
          | intro bsL hSubR =>
            cases hSubR with
            | intro bsR hC =>
              let absB : AbstractByte :=
                match optB with
                | .none => AbstractByte.uninit
                | .some byte =>
                  let prov :=
                    match lookupRelocAllocId relocs start with
                    | .some targetPtr => .some (targetPtr.allocId, targetPtr.tag)
                    | .none => .none
                  AbstractByte.init byte prov
              refine ⟨absB :: bsL, bsR, ?_, ?_, ?_⟩
              · unfold globalAllocBytesAux
                rw [hGet]
                dsimp only
                rw [hC.1]
                dsimp only [absB]
                cases optB <;> rfl
              · have hStEq : start + (a + 1) = (start + 1) + a := by
                  rw [Nat.add_comm a 1, ← Nat.add_assoc]
                rw [hStEq]
                exact hC.2.1
              · rw [← hBsEq, hC.2.2]
                dsimp only [absB]
                cases optB <;> rfl
    · intro hEx
      cases hEx with
      | intro bsL hR =>
        cases hR with
        | intro bsR hC =>
          have hL := hC.1
          unfold globalAllocBytesAux at hL
          cases hGet : Trusted.Sequence.get? bytes start with
          | none => rw [hGet] at hL; nomatch hL
          | some optB =>
            rw [hGet] at hL
            dsimp only at hL
            cases hRestL : globalAllocBytesAux bytes relocs (start + 1) a with
            | none => rw [hRestL] at hL; nomatch hL
            | some tailL =>
              rw [hRestL] at hL
              injection hL with hBsLEq
              have hStEq : (start + 1) + a = start + (a + 1) := by
                rw [Nat.add_assoc, Nat.add_comm 1 a]
              have hR2 : globalAllocBytesAux bytes relocs ((start + 1) + a) b = some bsR := by
                rw [hStEq]; exact hC.2.1
              have hJoin :=
                (globalAllocBytesAux_split bytes relocs a b (start + 1) (tailL ++ bsR)).mpr
                  ⟨tailL, bsR, hRestL, hR2, rfl⟩
              unfold globalAllocBytesAux
              rw [hGet]
              dsimp only
              rw [hJoin, hC.2.2, ← hBsLEq]
              rfl

private theorem globalAllocBytesAux_length_rs
    (bytes : List (Option UInt8)) (relocs : List (Nat × ProvenancePtr)) :
    ∀ (start len : Nat) (bs : List AbstractByte),
      globalAllocBytesAux bytes relocs start len = some bs → bs.length = len
  | _, 0, _, h => by
    injection h with hEq
    rw [← hEq]
    rfl
  | start, len + 1, bs, h => by
    unfold globalAllocBytesAux at h
    cases hGet : Trusted.Sequence.get? bytes start with
    | none => rw [hGet] at h; nomatch h
    | some _ =>
      rw [hGet] at h
      cases hRest : globalAllocBytesAux bytes relocs (start + 1) len with
      | none => rw [hRest] at h; nomatch h
      | some restBs =>
        rw [hRest] at h
        injection h with hEq
        rw [← hEq]
        exact congrArg Nat.succ
          (globalAllocBytesAux_length_rs bytes relocs (start + 1) len restBs hRest)

private theorem globalAllocBytesAux_congr_get
    (bytes₁ bytes₂ : List (Option UInt8)) (relocs : List (Nat × ProvenancePtr)) :
    ∀ (start len : Nat),
      (∀ i : Nat, start ≤ i → i < start + len →
        Trusted.Sequence.get? bytes₁ i = Trusted.Sequence.get? bytes₂ i) →
      globalAllocBytesAux bytes₁ relocs start len =
        globalAllocBytesAux bytes₂ relocs start len
  | _, 0, _ => rfl
  | start, len + 1, hEq => by
    unfold globalAllocBytesAux
    have h0 : Trusted.Sequence.get? bytes₁ start = Trusted.Sequence.get? bytes₂ start :=
      hEq start (Nat.le_refl start) (Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le len)) start))
    rw [h0]
    cases Trusted.Sequence.get? bytes₂ start with
    | none => rfl
    | some _ =>
      have hRest := globalAllocBytesAux_congr_get bytes₁ bytes₂ relocs (start + 1) len
        (fun i hGe hLt => by
          have hSt : start + 1 + len = start + (len + 1) := by
            rw [Nat.add_assoc, Nat.add_comm 1 len]
          rw [hSt] at hLt
          exact hEq i (Nat.le_trans (Nat.le_succ start) hGe) hLt)
      rw [hRest]

/-- Exact in-bounds byte-slice ownership predicate directly over unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory`: global allocation `r.allocId` exists
in `m.globals`, `[r.start, r.start + r.len)` is in bounds, and
`globalAllocSliceToAbstractBytes a r.start r.len = some bs`. -/
def AllocBytesAtV2026 (m : Memory) (r : ByteRange) (bs : List AbstractByte) : Prop :=
  ∃ a : CapturedAllocation,
    lookupGlobalAlloc m.globals r.allocId = some a ∧
    r.start + r.len ≤ a.bytes.length ∧
    bs.length = r.len ∧
    globalAllocSliceToAbstractBytes a r.start r.len = some bs

/-- $O(1)$ `slice::split_at_mut` soundness directly over unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory` (`[propext]` only): for any `k ≤ r.len`,
`AllocBytesAtV2026 m r bs` holds iff the left half holds `bs.take k` and the right half
holds `bs.drop k`. -/
theorem ownRange_split_iff (m : Memory) (r : ByteRange)
    (bs : List AbstractByte) {k : Nat} (hk : k ≤ r.len) :
    AllocBytesAtV2026 m r bs ↔
      AllocBytesAtV2026 m (rangeSplit r k).1 (bs.take k) ∧
      AllocBytesAtV2026 m (rangeSplit r k).2 (bs.drop k) := by
  have hEnd : r.start + k + (r.len - k) = r.start + r.len := by
    rw [Nat.add_assoc, natSub_add_cancel_rs hk]
  refine ⟨?_, ?_⟩
  · intro hAll
    cases hAll with
    | intro a ha =>
      have hBsLen : bs.length = r.len := ha.2.2.1
      have hTakeLen : (bs.take k).length = k :=
        listLength_take_of_le_rs k bs (by rw [hBsLen]; exact hk)
      have hDropLen : (bs.drop k).length = r.len - k := by
        rw [listLength_drop_rs, hBsLen]
      have hStartLe : r.start ≤ a.bytes.length :=
        Nat.le_trans (Nat.le_add_right r.start r.len) ha.2.1
      have hMidLe : r.start + k ≤ a.bytes.length :=
        Nat.le_trans (Nat.add_le_add_left hk r.start) ha.2.1
      have hGlob := ha.2.2.2
      unfold globalAllocSliceToAbstractBytes at hGlob
      have hBleStart : Nat.ble r.start (Trusted.Sequence.length a.bytes) = true :=
        natBle_of_le_rs hStartLe
      rw [hBleStart] at hGlob
      have hGlobSum :
          globalAllocBytesAux a.bytes a.relocations r.start (k + (r.len - k)) = some bs := by
        rw [natSub_add_cancel_rs hk]; exact hGlob
      have hSplit :=
        (globalAllocBytesAux_split a.bytes a.relocations k (r.len - k) r.start bs).mp hGlobSum
      cases hSplit with
      | intro bsL hSpR =>
        cases hSpR with
        | intro bsR hC =>
          have hLenL : bsL.length = k :=
            globalAllocBytesAux_length_rs a.bytes a.relocations r.start k bsL hC.1
          have hTakeEq : bs.take k = bsL := by
            rw [hC.2.2, ← hLenL]
            exact listTake_append_prefix_rs bsL bsR
          have hDropEq : bs.drop k = bsR := by
            rw [hC.2.2, ← hLenL, listDrop_append_ge_rs bsL bsR (Nat.le_refl bsL.length),
              Nat.sub_self]
            rfl
          refine ⟨⟨a, ha.1, hMidLe, hTakeLen, ?_⟩, ⟨a, ha.1, ?_, hDropLen, ?_⟩⟩
          · dsimp only [rangeSplit]
            unfold globalAllocSliceToAbstractBytes
            rw [hBleStart, hTakeEq]
            exact hC.1
          · dsimp only [rangeSplit]
            rw [hEnd]
            exact ha.2.1
          · dsimp only [rangeSplit]
            unfold globalAllocSliceToAbstractBytes
            have hBleMid : Nat.ble (r.start + k) (Trusted.Sequence.length a.bytes) = true :=
              natBle_of_le_rs hMidLe
            rw [hBleMid, hDropEq]
            exact hC.2.1
  · intro hPair
    cases hPair.1 with
    | intro aL haL =>
      cases hPair.2 with
      | intro aR haR =>
        dsimp only [rangeSplit] at haL haR
        have hFindEq : some aL = some aR := Eq.trans haL.1.symm haR.1
        injection hFindEq with hAeq
        rw [← hAeq] at haR
        have hBsLen : bs.length = r.len := by
          rw [← listSplit_take_drop_rs k bs, List.length_append,
            haL.2.2.1, haR.2.2.1, natSub_add_cancel_rs hk]
        have hBound : r.start + r.len ≤ aL.bytes.length := by
          rw [← hEnd]
          exact haR.2.1
        have hStartLe : r.start ≤ aL.bytes.length :=
          Nat.le_trans (Nat.le_add_right r.start r.len) hBound
        have hMidLe : r.start + k ≤ aL.bytes.length := haL.2.1
        have hBleStart : Nat.ble r.start (Trusted.Sequence.length aL.bytes) = true :=
          natBle_of_le_rs hStartLe
        have hBleMid : Nat.ble (r.start + k) (Trusted.Sequence.length aL.bytes) = true :=
          natBle_of_le_rs hMidLe
        have hL := haL.2.2.2
        have hR := haR.2.2.2
        unfold globalAllocSliceToAbstractBytes at hL hR
        rw [hBleStart] at hL
        rw [hBleMid] at hR
        have hJoin :=
          (globalAllocBytesAux_split aL.bytes aL.relocations k (r.len - k) r.start bs).mpr
            ⟨bs.take k, bs.drop k, hL, hR, (listSplit_take_drop_rs k bs).symm⟩
        rw [natSub_add_cancel_rs hk] at hJoin
        refine ⟨aL, haL.1, hBound, hBsLen, ?_⟩
        unfold globalAllocSliceToAbstractBytes
        rw [hBleStart]
        exact hJoin

/-- General fail-closed adjacent `ByteRange` ownership merge over unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory` (`[propext]` only): whenever
`rangeMergeChecked rL rR = some rM`, owning `rL ↦ bsL` and `rR ↦ bsR` combines into
`rM ↦ bsL ++ bsR`. -/
theorem ownRange_of_rangeMergeChecked
    {m : Memory} {rL rR rM : ByteRange} {bsL bsR : List AbstractByte}
    (hL : AllocBytesAtV2026 m rL bsL)
    (hR : AllocBytesAtV2026 m rR bsR)
    (hMerge : rangeMergeChecked rL rR = some rM) :
    AllocBytesAtV2026 m rM (bsL ++ bsR) := by
  have hSnd := rangeMergeChecked_sound hMerge
  have hk : rL.len ≤ rM.len := by
    rw [hSnd.2.2.2]
    exact Nat.le_add_right rL.len rR.len
  have hSplitL : (rangeSplit rM rL.len).1 = rL := by
    rw [hSnd.2.2.2]
    cases rL
    rfl
  have hSplitR : (rangeSplit rM rL.len).2 = rR := by
    rw [hSnd.2.2.2]
    cases rL with
    | mk aidL stL lenL =>
      cases rR with
      | mk aidR stR lenR =>
        dsimp only at hSnd
        dsimp only [rangeMerge, rangeSplit]
        rw [hSnd.1, hSnd.2.1, Nat.add_sub_cancel_left]
  cases hL with
  | intro aL haL =>
    have hTakeEq : (bsL ++ bsR).take rL.len = bsL := by
      rw [← haL.2.2.1]
      exact listTake_append_prefix_rs bsL bsR
    have hDropEq : (bsL ++ bsR).drop rL.len = bsR := by
      rw [listDrop_append_ge_rs bsL bsR (by rw [haL.2.2.1]; exact Nat.le_refl _),
        haL.2.2.1, Nat.sub_self]
      rfl
    apply (ownRange_split_iff m rM (bsL ++ bsR) hk).mpr
    rw [hSplitL, hSplitR, hTakeEq, hDropEq]
    exact ⟨⟨aL, haL⟩, hR⟩

/-- Replace matching global `CapturedAllocation` entries for `a'.allocId` (`0` `._unsafe_rec`). -/
def replaceGlobalAllocV2026 (a' : CapturedAllocation)
    (gs : List CapturedAllocation) : List CapturedAllocation :=
  gs.map (fun a =>
    match Nat.beq a.allocId a'.allocId with
    | true => a'
    | false => a)

/-- `true` iff no 8-byte relocation span `[ro, ro + 8)` (the span consulted by unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.lookupRelocAllocId`) overlaps `[s, s + l)` under
unmodified `MirSemantics.byteRangesOverlapBool` (non-recursive `List.all`, `0` `._unsafe_rec`).
Using `!byteRangesOverlapBool p.1 8 s l` ensures empty writes (`l = 0`) never falsely fail
even when `s` lies inside a relocation span. -/
def relocsAvoidRange (relocs : List (Nat × ProvenancePtr)) (s l : Nat) : Bool :=
  relocs.all (fun p => !byteRangesOverlapBool p.1 8 s l)

/-- Zero-length byte slices (`l = 0`) avoid every relocation span unconditionally (`[]`). -/
theorem relocsAvoidRange_zero_len :
    ∀ (relocs : List (Nat × ProvenancePtr)) (s : Nat),
      relocsAvoidRange relocs s 0 = true
  | [], _ => rfl
  | (ro, _) :: rest, s => by
    have hSub := relocsAvoidRange_zero_len rest s
    change (!byteRangesOverlapBool ro 8 s 0 && relocsAvoidRange rest s 0) = true
    have hOv0 : byteRangesOverlapBool ro 8 s 0 = false := by
      dsimp only [byteRangesOverlapBool]
      rfl
    rw [hOv0, hSub]
    rfl

/-- Fail-closed byte-range write into a mutable global `CapturedAllocation` of unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory`: rejects missing, read-only (`.not`),
mismatched-length, or out-of-bounds writes with `none`, AND rejects raw-byte writes that
would overlap any pointer relocation span (`relocsAvoidRange`). Without the relocation guard,
overwriting pointer bytes with plain data would leave a stale `relocations` entry behind and
`globalAllocSliceToAbstractBytes` would read the new bytes back WITH the old pointer's
provenance (provenance forgery). -/
def writeMemoryBytesV2026 (m : Memory) (r : ByteRange)
    (patch : List (Option UInt8)) : Option Memory :=
  match lookupGlobalAlloc m.globals r.allocId with
  | none => none
  | some a =>
    match a.mutability with
    | .not => none
    | .mut =>
      match Nat.beq patch.length r.len &&
          (Nat.ble (r.start + r.len) a.bytes.length &&
            relocsAvoidRange a.relocations r.start r.len) with
      | false => none
      | true =>
        let bytes' :=
          (a.bytes.take r.start ++ patch) ++ a.bytes.drop (r.start + patch.length)
        let a' : CapturedAllocation := { a with bytes := bytes' }
        some { m with globals := replaceGlobalAllocV2026 a' m.globals }

private theorem lookupGlobalAlloc_allocId_eq :
    ∀ (globals : List CapturedAllocation) (aid : AllocId) (a : CapturedAllocation),
      lookupGlobalAlloc globals aid = some a → a.allocId = aid
  | [], _, _, h => nomatch h
  | hd :: tl, aid, a, h => by
    unfold lookupGlobalAlloc at h
    cases hb : Nat.beq hd.allocId aid with
    | true =>
      rw [hb] at h
      injection h with hEq
      rw [← hEq]
      exact natEq_of_beq_rs hb
    | false =>
      rw [hb] at h
      exact lookupGlobalAlloc_allocId_eq tl aid a h

private theorem lookupGlobalAlloc_replace_eq (a' : CapturedAllocation) :
    ∀ {globals : List CapturedAllocation} {a : CapturedAllocation},
      lookupGlobalAlloc globals a'.allocId = some a →
      lookupGlobalAlloc (replaceGlobalAllocV2026 a' globals) a'.allocId = some a'
  | [], _, h => nomatch h
  | hd :: tl, a, h => by
    unfold lookupGlobalAlloc at h
    dsimp only [replaceGlobalAllocV2026, List.map]
    cases hb : Nat.beq hd.allocId a'.allocId with
    | true =>
      dsimp only
      unfold lookupGlobalAlloc
      rw [natBeq_refl_rs a'.allocId]
    | false =>
      rw [hb] at h
      dsimp only
      unfold lookupGlobalAlloc
      rw [hb]
      exact lookupGlobalAlloc_replace_eq a' h

private theorem lookupGlobalAlloc_replace_ne (a' : CapturedAllocation) (otherId : AllocId)
    (hNe : otherId ≠ a'.allocId) :
    ∀ (globals : List CapturedAllocation),
      lookupGlobalAlloc (replaceGlobalAllocV2026 a' globals) otherId =
        lookupGlobalAlloc globals otherId
  | [] => rfl
  | hd :: tl => by
    dsimp only [replaceGlobalAllocV2026, List.map]
    cases hb : Nat.beq hd.allocId a'.allocId with
    | true =>
      have hEq : hd.allocId = a'.allocId := natEq_of_beq_rs hb
      have hNe1 : Nat.beq a'.allocId otherId = false := by
        cases h2 : Nat.beq a'.allocId otherId with
        | false => rfl
        | true => exact False.elim (hNe (natEq_of_beq_rs h2).symm)
      have hNe2 : Nat.beq hd.allocId otherId = false := by
        rw [hEq]; exact hNe1
      dsimp only
      unfold lookupGlobalAlloc
      rw [hNe1, hNe2]
      exact lookupGlobalAlloc_replace_ne a' otherId hNe tl
    | false =>
      dsimp only
      unfold lookupGlobalAlloc
      cases Nat.beq hd.allocId otherId with
      | true => rfl
      | false => exact lookupGlobalAlloc_replace_ne a' otherId hNe tl

private theorem bool_and_left_rs {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | true => rfl
  | false => exact Bool.noConfusion h

private theorem bool_and_right_rs {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | true => exact h
  | false => exact Bool.noConfusion h

/-- Disjoint-range write frame law directly over unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory` (`[propext]` only): writing `patch` into
range `rW` via `writeMemoryBytesV2026` preserves `AllocBytesAtV2026 m rF bsF` whenever
`RangeDisjoint rW rF`, covering BOTH cross-allocation writes AND same-allocation
`split_at_mut` sub-slice writes! -/
theorem allocBytesAtV2026_frame_of_write_disjoint
    {m m' : Memory} {rW rF : ByteRange}
    {patch : List (Option UInt8)} {bsF : List AbstractByte}
    (hDisj : RangeDisjoint rW rF)
    (hWrite : writeMemoryBytesV2026 m rW patch = some m')
    (hFrame : AllocBytesAtV2026 m rF bsF) :
    AllocBytesAtV2026 m' rF bsF := by
  unfold writeMemoryBytesV2026 at hWrite
  cases hFindW : lookupGlobalAlloc m.globals rW.allocId with
  | none => rw [hFindW] at hWrite; nomatch hWrite
  | some aW =>
    rw [hFindW] at hWrite
    dsimp only at hWrite
    cases hMutW : aW.mutability with
    | not => rw [hMutW] at hWrite; nomatch hWrite
    | «mut» =>
      rw [hMutW] at hWrite
      dsimp only at hWrite
      cases hChk : (Nat.beq patch.length rW.len &&
          (Nat.ble (rW.start + rW.len) aW.bytes.length &&
            relocsAvoidRange aW.relocations rW.start rW.len)) with
      | false => rw [hChk] at hWrite; nomatch hWrite
      | true =>
        rw [hChk] at hWrite
        dsimp only at hWrite
        injection hWrite with hMeq
        have hLenW : patch.length = rW.len := natEq_of_beq_rs (bool_and_left_rs hChk)
        have hBndW : rW.start + rW.len ≤ aW.bytes.length :=
          natLe_of_ble_rs (bool_and_left_rs (bool_and_right_rs hChk))
        have hAwId : aW.allocId = rW.allocId :=
          lookupGlobalAlloc_allocId_eq m.globals rW.allocId aW hFindW
        let bytes' : List (Option UInt8) :=
          (aW.bytes.take rW.start ++ patch) ++ aW.bytes.drop (rW.start + patch.length)
        let aW' : CapturedAllocation := { aW with bytes := bytes' }
        have hM'Glob : m'.globals = replaceGlobalAllocV2026 aW' m.globals := by
          rw [← hMeq]
          dsimp only [aW', bytes']
          cases aW
          dsimp only at hMutW ⊢
          rw [hMutW]
        cases hFrame with
        | intro aF haF =>
          cases hIdEq : Nat.beq rW.allocId rF.allocId with
          | false =>
            have hNeId : rW.allocId ≠ rF.allocId := fun h => by
              rw [h, natBeq_refl_rs] at hIdEq
              exact Bool.noConfusion hIdEq
            have hFNe : rF.allocId ≠ aW'.allocId := by
              dsimp only [aW']
              rw [hAwId]
              exact fun h => hNeId h.symm
            refine ⟨aF, ?_, haF.2.1, haF.2.2.1, haF.2.2.2⟩
            rw [hM'Glob, lookupGlobalAlloc_replace_ne aW' rF.allocId hFNe m.globals]
            exact haF.1
          | true =>
            have hIdSame : rW.allocId = rF.allocId := natEq_of_beq_rs hIdEq
            have hInt : rW.start + rW.len ≤ rF.start ∨ rF.start + rF.len ≤ rW.start := by
              cases hDisj with
              | inl hNe => exact False.elim (hNe hIdSame)
              | inr hI => exact hI
            have hFindSame : some aW = some aF := by
              rw [← hFindW, hIdSame, haF.1]
            injection hFindSame with hAeq
            rw [← hAeq] at haF
            have hWStartLe : rW.start ≤ aW.bytes.length :=
              Nat.le_trans (Nat.le_add_right rW.start rW.len) hBndW
            have hBndPatch : rW.start + patch.length ≤ aW.bytes.length := by
              rw [hLenW]; exact hBndW
            have hBytesLenEq : bytes'.length = aW.bytes.length := by
              dsimp only [bytes']
              rw [List.length_append, List.length_append,
                listLength_take_of_le_rs rW.start aW.bytes hWStartLe,
                listLength_drop_rs, Nat.add_sub_of_le hBndPatch]
            have hFind' : lookupGlobalAlloc m'.globals rF.allocId = some aW' := by
              rw [hM'Glob, ← hIdSame, ← hAwId]
              exact lookupGlobalAlloc_replace_eq aW'
                (by dsimp only [aW']; rw [hAwId]; exact hFindW)
            refine ⟨aW', hFind', ?_, haF.2.2.1, ?_⟩
            · dsimp only [aW']
              rw [hBytesLenEq]
              exact haF.2.1
            · unfold globalAllocSliceToAbstractBytes
              have hFStartLe : rF.start ≤ aW.bytes.length :=
                Nat.le_trans (Nat.le_add_right rF.start rF.len) haF.2.1
              have hBle1 : Nat.ble rF.start (Trusted.Sequence.length aW'.bytes) = true := by
                change Nat.ble rF.start bytes'.length = true
                rw [hBytesLenEq]
                exact natBle_of_le_rs hFStartLe
              have hBle0 : Nat.ble rF.start (Trusted.Sequence.length aW.bytes) = true :=
                natBle_of_le_rs hFStartLe
              rw [hBle1]
              have hCongr :
                  globalAllocBytesAux aW'.bytes aW'.relocations rF.start rF.len =
                    globalAllocBytesAux aW.bytes aW.relocations rF.start rF.len := by
                apply globalAllocBytesAux_congr_get aW'.bytes aW.bytes aW.relocations rF.start rF.len
                intro i hGeF hLtF
                cases hInt with
                | inl hAfter =>
                  have hGeW : rW.start + patch.length ≤ i := by
                    rw [hLenW]
                    exact Nat.le_trans hAfter hGeF
                  exact listGet_splice_ge aW.bytes patch hWStartLe hGeW
                | inr hBefore =>
                  have hLtW : i < rW.start := Nat.lt_of_lt_of_le hLtF hBefore
                  exact listGet_splice_lt aW.bytes patch hWStartLe hLtW
              rw [hCongr]
              have hOrig := haF.2.2.2
              unfold globalAllocSliceToAbstractBytes at hOrig
              rw [hBle0] at hOrig
              exact hOrig

/-! ### General Read-After-Write over `V2026_06_01` `Memory` (Provenance-Exact) -/

/-- Provenance-free `AbstractByte` view of a raw `Option UInt8` patch: exactly how unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocBytesAux` decodes relocation-free bytes
(non-recursive `List.map`, `0` `._unsafe_rec`). -/
def rawToAbstractBytes (patch : List (Option UInt8)) : List AbstractByte :=
  patch.map (fun o =>
    match o with
    | none => .uninit
    | some b => .init b none)

/-- `rawToAbstractBytes` is length-preserving (`[]` zero axioms). -/
theorem rawToAbstractBytes_length : ∀ (patch : List (Option UInt8)),
    (rawToAbstractBytes patch).length = patch.length
  | [] => rfl
  | _ :: rest => congrArg Nat.succ (rawToAbstractBytes_length rest)

/-- Every offset inside a `relocsAvoidRange`-clean range has no relocation provenance under
unmodified `lookupRelocAllocId`. -/
private theorem lookupRelocAllocId_none_of_avoid :
    ∀ (relocs : List (Nat × ProvenancePtr)) (s l off : Nat),
      relocsAvoidRange relocs s l = true → s ≤ off → off < s + l →
      lookupRelocAllocId relocs off = none
  | [], _, _, _, _, _, _ => rfl
  | (ro, tp) :: rest, s, l, off, hAv, hGe, hLt => by
    have hAv' : ((!byteRangesOverlapBool ro 8 s l) &&
        relocsAvoidRange rest s l) = true := hAv
    have hHead := bool_and_left_rs hAv'
    have hRest :=
      lookupRelocAllocId_none_of_avoid rest s l off (bool_and_right_rs hAv') hGe hLt
    have hPosL : 0 < l := by
      cases l with
      | zero =>
        rw [Nat.add_zero] at hLt
        exact False.elim (Nat.not_lt_of_ge hGe hLt)
      | succ n => exact Nat.zero_lt_succ n
    have hOvF : byteRangesOverlapBool ro 8 s l = false := by
      cases hOv : byteRangesOverlapBool ro 8 s l with
      | false => rfl
      | true => rw [hOv] at hHead; exact Bool.noConfusion hHead
    have hDisj :=
      (byteRangesOverlapBool_false_iff_rangeDisjoint_pos
        (r₁ := ⟨0, ro, 8⟩) (r₂ := ⟨0, s, l⟩) rfl (Nat.zero_lt_succ 7) hPosL).mp hOvF
    unfold lookupRelocAllocId
    cases hDisj with
    | inl hNe0 => exact False.elim (hNe0 rfl)
    | inr hOrd =>
      cases hOrd with
      | inl hBefore =>
        have hLe : ro + 8 ≤ off := Nat.le_trans hBefore hGe
        have hB : Nat.ble (Nat.add ro 8) off = true := natBle_of_le_rs hLe
        rw [hB]
        cases Nat.ble ro off with
        | true => exact hRest
        | false => exact hRest
      | inr hAfter =>
        have hLt2 : off < ro := Nat.lt_of_lt_of_le hLt hAfter
        have hB : Nat.ble ro off = false := natBle_false_of_lt_rs hLt2
        rw [hB]
        exact hRest

/-- Reading `patch.length` bytes at `off` returns `rawToAbstractBytes patch` whenever the
underlying bytes agree with `patch` and no relocation covers the read window. -/
private theorem globalAllocBytesAux_of_patch :
    ∀ (patch bytes : List (Option UInt8)) (relocs : List (Nat × ProvenancePtr)) (off : Nat),
      (∀ j, j < patch.length →
        Trusted.Sequence.get? bytes (off + j) = Trusted.Sequence.get? patch j) →
      (∀ j, j < patch.length → lookupRelocAllocId relocs (off + j) = none) →
      globalAllocBytesAux bytes relocs off patch.length = some (rawToAbstractBytes patch)
  | [], _, _, _, _, _ => rfl
  | p :: ps, bytes, relocs, off, hGet, hRel => by
    have hShift : ∀ j, off + 1 + j = off + (j + 1) := fun j => by
      rw [Nat.add_assoc, Nat.add_comm 1 j]
    have hIH : globalAllocBytesAux bytes relocs (Nat.add off 1) ps.length =
        some (rawToAbstractBytes ps) :=
      globalAllocBytesAux_of_patch ps bytes relocs (off + 1)
        (fun j hj => by
          rw [hShift j]
          exact hGet (j + 1) (Nat.succ_lt_succ hj))
        (fun j hj => by
          rw [hShift j]
          exact hRel (j + 1) (Nat.succ_lt_succ hj))
    have h0 : Trusted.Sequence.get? bytes off = some p := by
      have h := hGet 0 (Nat.zero_lt_succ _)
      rw [Nat.add_zero] at h
      exact h
    have hR0 : lookupRelocAllocId relocs off = none := by
      have h := hRel 0 (Nat.zero_lt_succ _)
      rw [Nat.add_zero] at h
      exact h
    change globalAllocBytesAux bytes relocs off (ps.length + 1) = _
    unfold globalAllocBytesAux
    rw [h0]
    dsimp only
    rw [hIH]
    cases p with
    | none => rfl
    | some b =>
      dsimp only
      rw [hR0]
      rfl

/-- Bytes inside the spliced window read back as the patch. -/
private theorem listGet_splice_mid {α : Type} (xs mid : List α)
    {wStart j : Nat} (hWLe : wStart ≤ xs.length) (hj : j < mid.length) :
    Trusted.Sequence.get?
      ((xs.take wStart ++ mid) ++ xs.drop (wStart + mid.length)) (wStart + j) =
      Trusted.Sequence.get? mid j := by
  have hTakeLen : (xs.take wStart).length = wStart :=
    listLength_take_of_le_rs wStart xs hWLe
  have hPreLen : (xs.take wStart ++ mid).length = wStart + mid.length := by
    rw [List.length_append, hTakeLen]
  rw [listGet_append_left_rs (xs.take wStart ++ mid) _ (wStart + j)
      (by rw [hPreLen]; exact Nat.add_lt_add_left hj wStart),
    listGet_append_right_rs (xs.take wStart) mid (wStart + j)
      (by rw [hTakeLen]; exact Nat.le_add_right wStart j),
    hTakeLen, Nat.add_sub_cancel_left]

/-- General provenance-exact read-after-write law directly over unmodified
`Trusted.Rustc.V2026_06_01.MirSemantics.Memory` (`[propext]` only): after a successful
`writeMemoryBytesV2026 m rW patch = some m'`, unmodified `globalAllocSliceToAbstractBytes`
reads `rW` back as exactly `rawToAbstractBytes patch` — every initialized byte carries
`none` provenance, so no pointer provenance can be forged by a raw-data write. -/
theorem allocBytesAtV2026_of_write_self
    {m m' : Memory} {rW : ByteRange} {patch : List (Option UInt8)}
    (hWrite : writeMemoryBytesV2026 m rW patch = some m') :
    AllocBytesAtV2026 m' rW (rawToAbstractBytes patch) := by
  unfold writeMemoryBytesV2026 at hWrite
  cases hFindW : lookupGlobalAlloc m.globals rW.allocId with
  | none => rw [hFindW] at hWrite; nomatch hWrite
  | some aW =>
    rw [hFindW] at hWrite
    dsimp only at hWrite
    cases hMutW : aW.mutability with
    | not => rw [hMutW] at hWrite; nomatch hWrite
    | «mut» =>
      rw [hMutW] at hWrite
      dsimp only at hWrite
      cases hChk : (Nat.beq patch.length rW.len &&
          (Nat.ble (rW.start + rW.len) aW.bytes.length &&
            relocsAvoidRange aW.relocations rW.start rW.len)) with
      | false => rw [hChk] at hWrite; nomatch hWrite
      | true =>
        rw [hChk] at hWrite
        dsimp only at hWrite
        injection hWrite with hMeq
        have hLenW : patch.length = rW.len := natEq_of_beq_rs (bool_and_left_rs hChk)
        have hBndW : rW.start + rW.len ≤ aW.bytes.length :=
          natLe_of_ble_rs (bool_and_left_rs (bool_and_right_rs hChk))
        have hAvoid : relocsAvoidRange aW.relocations rW.start rW.len = true :=
          bool_and_right_rs (bool_and_right_rs hChk)
        have hAwId : aW.allocId = rW.allocId :=
          lookupGlobalAlloc_allocId_eq m.globals rW.allocId aW hFindW
        let bytes' : List (Option UInt8) :=
          (aW.bytes.take rW.start ++ patch) ++ aW.bytes.drop (rW.start + patch.length)
        let aW' : CapturedAllocation := { aW with bytes := bytes' }
        have hM'Glob : m'.globals = replaceGlobalAllocV2026 aW' m.globals := by
          rw [← hMeq]
          dsimp only [aW', bytes']
          cases aW
          dsimp only at hMutW ⊢
          rw [hMutW]
        have hWStartLe : rW.start ≤ aW.bytes.length :=
          Nat.le_trans (Nat.le_add_right rW.start rW.len) hBndW
        have hBndPatch : rW.start + patch.length ≤ aW.bytes.length := by
          rw [hLenW]; exact hBndW
        have hBytesLenEq : bytes'.length = aW.bytes.length := by
          dsimp only [bytes']
          rw [List.length_append, List.length_append,
            listLength_take_of_le_rs rW.start aW.bytes hWStartLe,
            listLength_drop_rs, Nat.add_sub_of_le hBndPatch]
        have hFind' : lookupGlobalAlloc m'.globals rW.allocId = some aW' := by
          rw [hM'Glob, ← hAwId]
          exact lookupGlobalAlloc_replace_eq aW'
            (by dsimp only [aW']; rw [hAwId]; exact hFindW)
        refine ⟨aW', hFind', ?_, ?_, ?_⟩
        · dsimp only [aW']
          rw [hBytesLenEq]
          exact hBndW
        · rw [rawToAbstractBytes_length, hLenW]
        · unfold globalAllocSliceToAbstractBytes
          have hBle1 : Nat.ble rW.start (Trusted.Sequence.length aW'.bytes) = true := by
            change Nat.ble rW.start bytes'.length = true
            rw [hBytesLenEq]
            exact natBle_of_le_rs hWStartLe
          rw [hBle1, ← hLenW]
          apply globalAllocBytesAux_of_patch
          · intro j hj
            exact listGet_splice_mid aW.bytes patch hWStartLe hj
          · intro j hj
            exact lookupRelocAllocId_none_of_avoid aW.relocations rW.start rW.len (rW.start + j)
              hAvoid (Nat.le_add_right _ _)
              (by rw [← hLenW]; exact Nat.add_lt_add_left hj _)

/-! ### `SpatialMemV2026.V2026ByteMem` & `sliceAbstractBytes`/`writeAbstractBytesAt` Bridge -/

/-- Exact in-bounds live byte-slice predicate over `Anneal.PureLift.SpatialMemV2026.V2026ByteMem`. -/
def AllocBytesAtByteMem (bm : V2026ByteMem) (r : ByteRange)
    (bs : List AbstractByte) : Prop :=
  ∃ a : V2026ByteAlloc,
    findV2026Alloc r.allocId bm.allocs = some a ∧
    a.live = true ∧
    r.start + r.len ≤ a.bytes.length ∧
    bs.length = r.len ∧
    (a.bytes.drop r.start).take r.len = bs

/-- $O(1)$ `slice::split_at_mut` soundness over `SpatialMemV2026.V2026ByteMem`
(`[propext]` only). -/
theorem allocBytesAtByteMem_split_iff (bm : V2026ByteMem) (r : ByteRange)
    (bs : List AbstractByte) {k : Nat} (hk : k ≤ r.len) :
    AllocBytesAtByteMem bm r bs ↔
      AllocBytesAtByteMem bm (rangeSplit r k).1 (bs.take k) ∧
      AllocBytesAtByteMem bm (rangeSplit r k).2 (bs.drop k) := by
  have hEnd : r.start + k + (r.len - k) = r.start + r.len := by
    rw [Nat.add_assoc, natSub_add_cancel_rs hk]
  refine ⟨?_, ?_⟩
  · intro hAll
    cases hAll with
    | intro a ha =>
      have hBsLen : bs.length = r.len := ha.2.2.2.1
      have hTakeLen : (bs.take k).length = k :=
        listLength_take_of_le_rs k bs (by rw [hBsLen]; exact hk)
      have hDropLen : (bs.drop k).length = r.len - k := by
        rw [listLength_drop_rs, hBsLen]
      refine ⟨⟨a, ha.1, ha.2.1,
        Nat.le_trans (Nat.add_le_add_left hk r.start) ha.2.2.1,
        hTakeLen, ?_⟩,
        ⟨a, ha.1, ha.2.1, ?_, hDropLen, ?_⟩⟩
      · dsimp only [rangeSplit]
        rw [← ha.2.2.2.2]
        exact (listTake_take_of_le_rs k r.len (a.bytes.drop r.start) hk).symm
      · dsimp only [rangeSplit]
        rw [hEnd]
        exact ha.2.2.1
      · dsimp only [rangeSplit]
        rw [← ha.2.2.2.2, ← listDrop_drop_rs r.start k a.bytes]
        exact (listDrop_take_rs k r.len (a.bytes.drop r.start)).symm
  · intro hPair
    cases hPair.1 with
    | intro aL haL =>
      cases hPair.2 with
      | intro aR haR =>
        dsimp only [rangeSplit] at haL haR
        have hFindEq : some aL = some aR := Eq.trans haL.1.symm haR.1
        injection hFindEq with hAeq
        rw [← hAeq] at haR
        have hBsLen : bs.length = r.len := by
          rw [← listSplit_take_drop_rs k bs, List.length_append,
            haL.2.2.2.1, haR.2.2.2.1, natSub_add_cancel_rs hk]
        refine ⟨aL, haL.1, haL.2.1, ?_, hBsLen, ?_⟩
        · rw [← hEnd]
          exact haR.2.2.1
        · have hSplitSlice :
              (aL.bytes.drop r.start).take r.len =
                (aL.bytes.drop r.start).take k ++
                  ((aL.bytes.drop r.start).drop k).take (r.len - k) := by
            have hT := listTake_add_rs k (r.len - k) (aL.bytes.drop r.start)
            rw [natSub_add_cancel_rs hk] at hT
            exact hT
          rw [hSplitSlice, listDrop_drop_rs r.start k aL.bytes,
            haL.2.2.2.2, haR.2.2.2.2, listSplit_take_drop_rs k bs]

private theorem findV2026Alloc_id_eq_rs :
    ∀ (xs : List V2026ByteAlloc) (aid : AllocId) (a : V2026ByteAlloc),
      findV2026Alloc aid xs = some a → a.allocId = aid
  | [], _, _, h => nomatch h
  | hd :: tl, aid, a, h => by
    unfold findV2026Alloc at h
    cases hb : Nat.beq hd.allocId aid with
    | true =>
      rw [hb, ite_eq_left (rfl : true = true)] at h
      injection h with hEq
      rw [← hEq]
      exact natEq_of_beq_rs hb
    | false =>
      rw [hb, ite_eq_right Bool.false_ne_true] at h
      exact findV2026Alloc_id_eq_rs tl aid a h

private theorem findV2026Alloc_replace_eq_rs (a' : V2026ByteAlloc) :
    ∀ {xs : List V2026ByteAlloc} {a : V2026ByteAlloc},
      findV2026Alloc a'.allocId xs = some a →
      findV2026Alloc a'.allocId (replaceV2026Alloc a' xs) = some a'
  | [], _, h => nomatch h
  | hd :: tl, a, h => by
    unfold findV2026Alloc at h
    unfold replaceV2026Alloc
    cases hb : Nat.beq hd.allocId a'.allocId with
    | true =>
      rw [ite_eq_left (rfl : true = true)]
      unfold findV2026Alloc
      rw [natBeq_refl_rs a'.allocId, ite_eq_left (rfl : true = true)]
    | false =>
      rw [hb, ite_eq_right Bool.false_ne_true] at h
      rw [ite_eq_right Bool.false_ne_true]
      unfold findV2026Alloc
      rw [hb, ite_eq_right Bool.false_ne_true]
      exact findV2026Alloc_replace_eq_rs a' h

private theorem findV2026Alloc_replace_ne_rs :
    ∀ (xs : List V2026ByteAlloc) (a' : V2026ByteAlloc) (otherId : AllocId),
      otherId ≠ a'.allocId →
      findV2026Alloc otherId (replaceV2026Alloc a' xs) = findV2026Alloc otherId xs
  | [], _, _, _ => rfl
  | hd :: tl, a', otherId, hNe => by
    unfold replaceV2026Alloc
    cases hb : Nat.beq hd.allocId a'.allocId with
    | true =>
      rw [ite_eq_left (rfl : true = true)]
      have hEq : hd.allocId = a'.allocId := natEq_of_beq_rs hb
      have hNe1 : Nat.beq a'.allocId otherId = false := by
        cases h2 : Nat.beq a'.allocId otherId with
        | false => rfl
        | true => exact False.elim (hNe (natEq_of_beq_rs h2).symm)
      have hNe2 : Nat.beq hd.allocId otherId = false := by rw [hEq]; exact hNe1
      unfold findV2026Alloc
      rw [hNe1, hNe2, ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      unfold findV2026Alloc
      cases hb2 : Nat.beq hd.allocId otherId with
      | true => rw [ite_eq_left (rfl : true = true), ite_eq_left (rfl : true = true)]
      | false =>
        rw [ite_eq_right Bool.false_ne_true, ite_eq_right Bool.false_ne_true]
        exact findV2026Alloc_replace_ne_rs tl a' otherId hNe

/-- Unconditional disjoint-range write frame law over `SpatialMemV2026.writeV2026Bytes`
(`[]` zero axioms / `[propext]` only): covers BOTH cross-allocation writes AND same-allocation
disjoint sub-ranges! -/
theorem allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint
    {bm bm' : V2026ByteMem} {rW rF : ByteRange} {reqAlign : Nat}
    {newBytes bsF : List AbstractByte}
    (hLenW : newBytes.length = rW.len)
    (hDisj : RangeDisjoint rW rF)
    (hWrite : writeV2026Bytes bm ⟨rW.allocId, rW.start⟩ reqAlign newBytes = some bm')
    (hFrame : AllocBytesAtByteMem bm rF bsF) :
    AllocBytesAtByteMem bm' rF bsF := by
  unfold writeV2026Bytes at hWrite
  cases hEmp : newBytes.isEmpty with
  | true =>
    rw [hEmp, ite_eq_left (rfl : true = true)] at hWrite
    nomatch hWrite
  | false =>
    rw [hEmp, ite_eq_right Bool.false_ne_true] at hWrite
    cases hFindW : findV2026Alloc rW.allocId bm.allocs with
    | none => rw [hFindW] at hWrite; nomatch hWrite
    | some aW =>
      rw [hFindW] at hWrite
      dsimp only at hWrite
      cases hLiveW : aW.live with
      | false =>
        rw [hLiveW] at hWrite
        dsimp only [Bool.not, Bool.or] at hWrite
        rw [ite_eq_left (rfl : true = true)] at hWrite
        nomatch hWrite
      | true =>
        rw [hLiveW] at hWrite
        cases hMutW : aW.mutability with
        | not =>
          rw [hMutW] at hWrite
          dsimp only [Bool.not, Bool.or] at hWrite
          rw [ite_eq_left (rfl : true = true)] at hWrite
          nomatch hWrite
        | «mut» =>
          rw [hMutW] at hWrite
          cases hBndW : v2026InBounds aW rW.start newBytes.length with
          | false =>
            rw [hBndW] at hWrite
            dsimp only [Bool.not, Bool.or] at hWrite
            rw [ite_eq_left (rfl : true = true)] at hWrite
            nomatch hWrite
          | true =>
            rw [hBndW] at hWrite
            cases hAlW : v2026Aligned aW rW.start reqAlign with
            | false =>
              rw [hAlW] at hWrite
              dsimp only [Bool.not, Bool.or] at hWrite
              rw [ite_eq_left (rfl : true = true)] at hWrite
              nomatch hWrite
            | true =>
              rw [hAlW] at hWrite
              dsimp only [Bool.not, Bool.or] at hWrite
              rw [ite_eq_right Bool.false_ne_true] at hWrite
              injection hWrite with hMeq
              let bytes' : List AbstractByte :=
                (aW.bytes.take rW.start ++ newBytes) ++
                  aW.bytes.drop (rW.start + newBytes.length)
              let aW' : V2026ByteAlloc := { aW with bytes := bytes' }
              have hM'Alloc : bm'.allocs = replaceV2026Alloc aW' bm.allocs := by
                rw [← hMeq]
                dsimp only [aW', bytes']
                cases aW
                dsimp only at hMutW hLiveW ⊢
                rw [hMutW, hLiveW]
              have hAwId : aW.allocId = rW.allocId :=
                findV2026Alloc_id_eq_rs bm.allocs rW.allocId aW hFindW
              cases hFrame with
              | intro aF haF =>
                cases hIdEq : Nat.beq rW.allocId rF.allocId with
                | false =>
                  have hNeId : rW.allocId ≠ rF.allocId := fun h => by
                    rw [h, natBeq_refl_rs] at hIdEq
                    exact Bool.noConfusion hIdEq
                  have hFNe : rF.allocId ≠ aW'.allocId := by
                    dsimp only [aW']
                    rw [hAwId]
                    exact fun h => hNeId h.symm
                  refine ⟨aF, ?_, haF.2.1, haF.2.2.1, haF.2.2.2.1, haF.2.2.2.2⟩
                  rw [hM'Alloc, findV2026Alloc_replace_ne_rs bm.allocs aW' rF.allocId hFNe]
                  exact haF.1
                | true =>
                  have hIdSame : rW.allocId = rF.allocId := natEq_of_beq_rs hIdEq
                  have hInt : rW.start + rW.len ≤ rF.start ∨ rF.start + rF.len ≤ rW.start := by
                    cases hDisj with
                    | inl hNe => exact False.elim (hNe hIdSame)
                    | inr hI => exact hI
                  have hFindSame : some aW = some aF := by
                    rw [← hFindW, hIdSame, haF.1]
                  injection hFindSame with hAeq
                  rw [← hAeq] at haF
                  have hLeBoundsW : rW.start + newBytes.length ≤ aW.bytes.length :=
                    natLe_of_ble_rs hBndW
                  have hWStartLe : rW.start ≤ aW.bytes.length :=
                    Nat.le_trans (Nat.le_add_right rW.start newBytes.length) hLeBoundsW
                  have hBytesLenEq : bytes'.length = aW.bytes.length := by
                    dsimp only [bytes']
                    rw [List.length_append, List.length_append,
                      listLength_take_of_le_rs rW.start aW.bytes hWStartLe,
                      listLength_drop_rs, Nat.add_sub_of_le hLeBoundsW]
                  have hFind' : findV2026Alloc rF.allocId bm'.allocs = some aW' := by
                    rw [hM'Alloc, ← hIdSame, ← hAwId]
                    exact findV2026Alloc_replace_eq_rs aW'
                      (by dsimp only [aW']; rw [hAwId]; exact hFindW)
                  refine ⟨aW', hFind', hLiveW, ?_, haF.2.2.2.1, ?_⟩
                  · dsimp only [aW']
                    rw [hBytesLenEq]
                    exact haF.2.2.1
                  · dsimp only [aW', bytes']
                    cases hInt with
                    | inl hAfter =>
                      rw [listSlice_splice_right aW.bytes newBytes hWStartLe
                        (by rw [hLenW]; exact hAfter)]
                      exact haF.2.2.2.2
                    | inr hBefore =>
                      rw [listSlice_splice_left aW.bytes newBytes hWStartLe hBefore]
                      exact haF.2.2.2.2

private theorem listSlice_splice_self {α : Type} (xs mid : List α)
    {wStart : Nat} (hWLe : wStart ≤ xs.length) :
    (((xs.take wStart ++ mid) ++
        xs.drop (wStart + mid.length)).drop wStart).take mid.length = mid := by
  have hTakeLen : (xs.take wStart).length = wStart :=
    listLength_take_of_le_rs wStart xs hWLe
  rw [List.append_assoc,
    listDrop_append_ge_rs (xs.take wStart) (mid ++ xs.drop (wStart + mid.length))
      (by rw [hTakeLen]; exact Nat.le_refl wStart),
    hTakeLen, Nat.sub_self]
  exact listTake_append_prefix_rs mid (xs.drop (wStart + mid.length))

/-- General read-after-write ownership law for `SpatialMemV2026.writeV2026Bytes`
(`[propext]` only): after `writeV2026Bytes bm ⟨rW.allocId, rW.start⟩ reqAlign newBytes = some bm'`
with `newBytes.length = rW.len`, `AllocBytesAtByteMem bm' rW newBytes` holds AND
`readV2026Bytes bm' ⟨rW.allocId, rW.start⟩ newBytes.length reqAlign = some newBytes`. -/
theorem allocBytesAtByteMem_of_writeV2026Bytes_self
    {bm bm' : V2026ByteMem} {rW : ByteRange} {reqAlign : Nat}
    {newBytes : List AbstractByte}
    (hLenW : newBytes.length = rW.len)
    (hWrite : writeV2026Bytes bm ⟨rW.allocId, rW.start⟩ reqAlign newBytes = some bm') :
    AllocBytesAtByteMem bm' rW newBytes ∧
    readV2026Bytes bm' ⟨rW.allocId, rW.start⟩ newBytes.length reqAlign = some newBytes := by
  unfold writeV2026Bytes at hWrite
  cases hEmp : newBytes.isEmpty with
  | true =>
    rw [hEmp, ite_eq_left (rfl : true = true)] at hWrite
    nomatch hWrite
  | false =>
    rw [hEmp, ite_eq_right Bool.false_ne_true] at hWrite
    cases hFindW : findV2026Alloc rW.allocId bm.allocs with
    | none => rw [hFindW] at hWrite; nomatch hWrite
    | some aW =>
      rw [hFindW] at hWrite
      dsimp only at hWrite
      cases hLiveW : aW.live with
      | false =>
        rw [hLiveW] at hWrite
        dsimp only [Bool.not, Bool.or] at hWrite
        rw [ite_eq_left (rfl : true = true)] at hWrite
        nomatch hWrite
      | true =>
        rw [hLiveW] at hWrite
        cases hMutW : aW.mutability with
        | not =>
          rw [hMutW] at hWrite
          dsimp only [Bool.not, Bool.or] at hWrite
          rw [ite_eq_left (rfl : true = true)] at hWrite
          nomatch hWrite
        | «mut» =>
          rw [hMutW] at hWrite
          cases hBndW : v2026InBounds aW rW.start newBytes.length with
          | false =>
            rw [hBndW] at hWrite
            dsimp only [Bool.not, Bool.or] at hWrite
            rw [ite_eq_left (rfl : true = true)] at hWrite
            nomatch hWrite
          | true =>
            rw [hBndW] at hWrite
            cases hAlW : v2026Aligned aW rW.start reqAlign with
            | false =>
              rw [hAlW] at hWrite
              dsimp only [Bool.not, Bool.or] at hWrite
              rw [ite_eq_left (rfl : true = true)] at hWrite
              nomatch hWrite
            | true =>
              rw [hAlW] at hWrite
              dsimp only [Bool.not, Bool.or] at hWrite
              rw [ite_eq_right Bool.false_ne_true] at hWrite
              injection hWrite with hMeq
              let bytes' : List AbstractByte :=
                (aW.bytes.take rW.start ++ newBytes) ++
                  aW.bytes.drop (rW.start + newBytes.length)
              let aW' : V2026ByteAlloc := { aW with bytes := bytes' }
              have hM'Alloc : bm'.allocs = replaceV2026Alloc aW' bm.allocs := by
                rw [← hMeq]
                dsimp only [aW', bytes']
                cases aW
                dsimp only at hMutW hLiveW ⊢
                rw [hMutW, hLiveW]
              have hAwId : aW.allocId = rW.allocId :=
                findV2026Alloc_id_eq_rs bm.allocs rW.allocId aW hFindW
              have hLeBoundsW : rW.start + newBytes.length ≤ aW.bytes.length :=
                natLe_of_ble_rs hBndW
              have hWStartLe : rW.start ≤ aW.bytes.length :=
                Nat.le_trans (Nat.le_add_right rW.start newBytes.length) hLeBoundsW
              have hBytesLenEq : bytes'.length = aW.bytes.length := by
                dsimp only [bytes']
                rw [List.length_append, List.length_append,
                  listLength_take_of_le_rs rW.start aW.bytes hWStartLe,
                  listLength_drop_rs, Nat.add_sub_of_le hLeBoundsW]
              have hFind' : findV2026Alloc rW.allocId bm'.allocs = some aW' := by
                rw [hM'Alloc, ← hAwId]
                exact findV2026Alloc_replace_eq_rs aW'
                  (by dsimp only [aW']; rw [hAwId]; exact hFindW)
              have hSliceSelf : (aW'.bytes.drop rW.start).take newBytes.length = newBytes := by
                dsimp only [aW', bytes']
                exact listSlice_splice_self aW.bytes newBytes hWStartLe
              refine ⟨⟨aW', hFind', hLiveW, ?_, hLenW, ?_⟩, ?_⟩
              · dsimp only [aW']
                rw [hBytesLenEq, ← hLenW]
                exact hLeBoundsW
              · rw [← hLenW]
                exact hSliceSelf
              · unfold readV2026Bytes
                rw [hFind']
                dsimp only
                have hIb' : v2026InBounds aW' rW.start newBytes.length = true := by
                  unfold v2026InBounds at hBndW ⊢
                  dsimp only [aW']
                  rw [hBytesLenEq]
                  exact hBndW
                have hAl' : v2026Aligned aW' rW.start reqAlign = true := hAlW
                have hLive' : aW'.live = true := hLiveW
                rw [hLive', hIb', hAl']
                dsimp only [Bool.not, Bool.or]
                rw [ite_eq_right Bool.false_ne_true, hSliceSelf]

/-- Reading a slice from `V2026ByteMem` via `readV2026Bytes` returns `some bs` whenever
`AllocBytesAtByteMem bm r bs` holds and alignment is satisfied (`reqAlign = 1`, `a.alignBytes ≥ 1`). -/
theorem readV2026Bytes_of_allocBytesAtByteMem
    {bm : V2026ByteMem} {r : ByteRange} {bs : List AbstractByte}
    (hAt : AllocBytesAtByteMem bm r bs)
    (hAlign : ∀ a, findV2026Alloc r.allocId bm.allocs = some a → 1 ≤ a.alignBytes) :
    readV2026Bytes bm ⟨r.allocId, r.start⟩ r.len 1 = some bs := by
  cases hAt with
  | intro a ha =>
    unfold readV2026Bytes
    rw [ha.1]
    dsimp only
    have hIb : v2026InBounds a r.start r.len = true := natBle_of_le_rs ha.2.2.1
    have hAl : v2026Aligned a r.start 1 = true := by
      unfold v2026Aligned
      have hA1 : Nat.ble 1 a.alignBytes = true := natBle_of_le_rs (hAlign a ha.1)
      have hMod : Nat.beq (r.start % 1) 0 = true := by rw [Nat.mod_one]; rfl
      have hNz : (1 == 0) = false := rfl
      rw [hNz, ite_eq_right Bool.false_ne_true, hA1, hMod]
      rfl
    rw [ha.2.1, hIb, hAl, ha.2.2.2.2]
    rfl

private theorem findV2026Alloc_map_captured :
    ∀ (globals : List CapturedAllocation) (aid : AllocId),
      findV2026Alloc aid (globals.map capturedAllocToByteAlloc) =
        (lookupGlobalAlloc globals aid).map capturedAllocToByteAlloc
  | [], _ => rfl
  | a :: rest, aid => by
    unfold lookupGlobalAlloc List.map findV2026Alloc capturedAllocToByteAlloc
    cases hb : Nat.beq a.allocId aid with
    | true =>
      rw [ite_eq_left (rfl : true = true)]
      rfl
    | false =>
      rw [ite_eq_right Bool.false_ne_true]
      exact findV2026Alloc_map_captured rest aid

private theorem globalAllocBytesAux_total_exists
    (bytes : List (Option UInt8)) (relocs : List (Nat × ProvenancePtr)) :
    ∀ (start len : Nat), start + len ≤ bytes.length →
      ∃ out : List AbstractByte,
        globalAllocBytesAux bytes relocs start len = some out ∧ out.length = len
  | _, 0, _ => ⟨[], rfl, rfl⟩
  | start, len + 1, hLe => by
    have hStLt : start < bytes.length :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le (Nat.lt_succ_self start)
        (Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le len)) start)) hLe
    have hNextLe : (start + 1) + len ≤ bytes.length := by
      rw [Nat.add_assoc, Nat.add_comm 1 len]; exact hLe
    cases globalAllocBytesAux_total_exists bytes relocs (start + 1) len hNextLe with
    | intro rest hRest =>
      have hGetSome : ∃ optB, Trusted.Sequence.get? bytes start = some optB := by
        have hAux : ∀ (xs : List (Option UInt8)) (i : Nat),
            i < xs.length → ∃ v, Trusted.Sequence.get? xs i = some v := by
          intro xs
          induction xs with
          | nil => intro _ h; nomatch h
          | cons hd tl ih =>
            intro i hi
            cases i with
            | zero => exact ⟨hd, rfl⟩
            | succ k => exact ih k (Nat.lt_of_succ_lt_succ hi)
        exact hAux bytes start hStLt
      cases hGetSome with
      | intro optB hGet =>
        let absB : AbstractByte :=
          match optB with
          | .none => AbstractByte.uninit
          | .some b =>
            let prov :=
              match lookupRelocAllocId relocs start with
              | .some targetPtr => .some (targetPtr.allocId, targetPtr.tag)
              | .none => .none
            AbstractByte.init b prov
        refine ⟨absB :: rest, ?_, congrArg Nat.succ hRest.2⟩
        unfold globalAllocBytesAux
        rw [hGet]
        dsimp only
        rw [hRest.1]
        dsimp only [absB]
        cases optB <;> rfl

/-- Exact bridge from `AllocBytesAtV2026` on unmodified `V2026_06_01.MirSemantics.Memory`
to `AllocBytesAtByteMem` on `SpatialMemV2026.memGlobalsToByteMem m` (`[propext]` only). -/
theorem allocBytesAtByteMem_of_allocBytesAtV2026
    {m : Memory} {r : ByteRange} {bs : List AbstractByte}
    (hAt : AllocBytesAtV2026 m r bs) :
    AllocBytesAtByteMem (memGlobalsToByteMem m) r bs := by
  cases hAt with
  | intro a ha =>
    have hFindMap :
        findV2026Alloc r.allocId (memGlobalsToByteMem m).allocs =
          some (capturedAllocToByteAlloc a) := by
      unfold memGlobalsToByteMem
      rw [findV2026Alloc_map_captured m.globals r.allocId, ha.1]
      rfl
    cases globalAllocBytesAux_total_exists a.bytes a.relocations 0 a.bytes.length
        (by rw [Nat.zero_add]; exact Nat.le_refl _) with
    | intro fullOut hFull =>
      have hGlobFull : globalAllocSliceToAbstractBytes a 0 a.bytes.length = some fullOut := by
        unfold globalAllocSliceToAbstractBytes
        exact hFull.1
      have hBytesEq : (capturedAllocToByteAlloc a).bytes = fullOut := by
        unfold capturedAllocToByteAlloc
        rw [hGlobFull]
        rfl
      have hStartLe : r.start ≤ a.bytes.length :=
        Nat.le_trans (Nat.le_add_right r.start r.len) ha.2.1
      have hFullSplit1 :
          globalAllocBytesAux a.bytes a.relocations 0
            (r.start + (a.bytes.length - r.start)) = some fullOut := by
        rw [natSub_add_cancel_rs hStartLe]; exact hFull.1
      cases (globalAllocBytesAux_split a.bytes a.relocations r.start
          (a.bytes.length - r.start) 0 fullOut).mp hFullSplit1 with
      | intro preBs hSp1 =>
        cases hSp1 with
        | intro sufBs hC1 =>
          have hPreLen : preBs.length = r.start :=
            globalAllocBytesAux_length_rs a.bytes a.relocations 0 r.start preBs hC1.1
          have hDropEq : fullOut.drop r.start = sufBs := by
            rw [hC1.2.2, ← hPreLen, listDrop_append_ge_rs preBs sufBs (Nat.le_refl preBs.length),
              Nat.sub_self]
            rfl
          have hRemLe : r.len ≤ a.bytes.length - r.start := by
            have hS := Nat.sub_le_sub_right ha.2.1 r.start
            rw [Nat.add_sub_cancel_left] at hS
            exact hS
          have hSufAux :
              globalAllocBytesAux a.bytes a.relocations r.start
                (r.len + ((a.bytes.length - r.start) - r.len)) = some sufBs := by
            rw [natSub_add_cancel_rs hRemLe]
            have h0 := hC1.2.1
            rw [Nat.zero_add] at h0
            exact h0
          cases (globalAllocBytesAux_split a.bytes a.relocations r.len
              ((a.bytes.length - r.start) - r.len) r.start sufBs).mp hSufAux with
          | intro midBs hSp2 =>
            cases hSp2 with
            | intro tailBs hC2 =>
              have hMidLen : midBs.length = r.len :=
                globalAllocBytesAux_length_rs a.bytes a.relocations r.start r.len midBs hC2.1
              have hTakeEq : sufBs.take r.len = midBs := by
                rw [hC2.2.2, ← hMidLen]
                exact listTake_append_prefix_rs midBs tailBs
              have hOrig := ha.2.2.2
              unfold globalAllocSliceToAbstractBytes at hOrig
              have hBleSt : Nat.ble r.start (Trusted.Sequence.length a.bytes) = true :=
                natBle_of_le_rs hStartLe
              rw [hBleSt] at hOrig
              have hMidEqBs : some midBs = some bs := Eq.trans hC2.1.symm hOrig
              injection hMidEqBs with hMidEq
              refine ⟨capturedAllocToByteAlloc a, hFindMap, rfl, ?_, ha.2.2.1, ?_⟩
              · rw [hBytesEq, hFull.2]; exact ha.2.1
              · rw [hBytesEq, hDropEq, hTakeEq, hMidEq]

/-- Direct framing on unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.{sliceAbstractBytes,
writeAbstractBytesAt}` (`[propext]` only): overwriting `patch` at `wOff` preserves any
disjoint `sliceAbstractBytes` at `(fOff, fLen)`. -/
private theorem writeAbstractBytesAt_splice_of_le :
    ∀ (buf patch : List AbstractByte) (off : Nat) (out : List AbstractByte),
      off ≤ buf.length →
      writeAbstractBytesAt buf off patch = some out →
      off + patch.length ≤ buf.length ∧
      out = (buf.take off ++ patch) ++ buf.drop (off + patch.length)
  | buf, [], off, out, hOffLe, h => by
    unfold writeAbstractBytesAt at h
    injection h with hEq
    dsimp only [List.length]
    rw [Nat.add_zero]
    refine ⟨hOffLe, ?_⟩
    rw [← hEq, List.append_nil, listSplit_take_drop_rs off buf]
  | [], _ :: _, _, _, _, h => by
    unfold writeAbstractBytesAt at h; nomatch h
  | _ :: bufRest, w :: wRest, 0, out, _, h => by
    unfold writeAbstractBytesAt at h
    cases hSub : writeAbstractBytesAt bufRest 0 wRest with
    | none => rw [hSub] at h; nomatch h
    | some tail' =>
      rw [hSub] at h
      injection h with hEq
      have ih := writeAbstractBytesAt_splice_of_le bufRest wRest 0 tail' (Nat.zero_le _) hSub
      refine ⟨Nat.succ_le_succ ih.1, ?_⟩
      rw [← hEq, ih.2]
      change w :: (wRest ++ List.drop (0 + wRest.length) bufRest) =
        w :: wRest ++ List.drop (0 + (wRest.length + 1) - 1) bufRest
      rw [Nat.zero_add, Nat.zero_add, Nat.add_sub_cancel]
      rfl
  | b :: bufRest, w :: wRest, off + 1, out, hOffLe, h => by
    unfold writeAbstractBytesAt at h
    cases hSub : writeAbstractBytesAt bufRest off (w :: wRest) with
    | none => rw [hSub] at h; nomatch h
    | some tail' =>
      rw [hSub] at h
      injection h with hEq
      have ih := writeAbstractBytesAt_splice_of_le bufRest (w :: wRest) off tail'
        (Nat.le_of_succ_le_succ hOffLe) hSub
      refine ⟨?_, ?_⟩
      · rw [Nat.succ_add]; exact Nat.succ_le_succ ih.1
      · rw [← hEq, ih.2, Nat.succ_add]
        rfl

private theorem takeAbstractBytes_eq_rs : ∀ (n : Nat) (bs : List AbstractByte),
    takeAbstractBytes n bs = bs.take n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, b :: bs => congrArg (List.cons b) (takeAbstractBytes_eq_rs n bs)

private theorem dropAbstractBytes_eq_rs : ∀ (n : Nat) (bs : List AbstractByte),
    dropAbstractBytes n bs = bs.drop n
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, _ :: bs => dropAbstractBytes_eq_rs n bs

/-- Direct framing on unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.{sliceAbstractBytes,
writeAbstractBytesAt}` (`[propext]` only): overwriting `patch` at `wOff` (`wOff ≤ buf.length`)
preserves `sliceAbstractBytes` at any disjoint range `(fOff, fLen)`. -/
theorem sliceAbstractBytes_writeAbstractBytesAt_disjoint
    {buf buf' patch : List AbstractByte} {wOff fOff fLen : Nat}
    (hWLe : wOff ≤ buf.length)
    (hDisj : wOff + patch.length ≤ fOff ∨ fOff + fLen ≤ wOff)
    (hWrite : writeAbstractBytesAt buf wOff patch = some buf') :
    sliceAbstractBytes buf' fOff fLen = sliceAbstractBytes buf fOff fLen := by
  have hSp := writeAbstractBytesAt_splice_of_le buf patch wOff buf' hWLe hWrite
  have hLenEq : buf'.length = buf.length := by
    rw [hSp.2, List.length_append, List.length_append,
      listLength_take_of_le_rs wOff buf hWLe, listLength_drop_rs,
      Nat.add_sub_of_le hSp.1]
  unfold sliceAbstractBytes
  have hL : Trusted.Sequence.length buf' = Trusted.Sequence.length buf := hLenEq
  rw [hL]
  cases Nat.ble (Nat.add fOff fLen) (Trusted.Sequence.length buf) with
  | false => rfl
  | true =>
    rw [takeAbstractBytes_eq_rs, dropAbstractBytes_eq_rs,
      takeAbstractBytes_eq_rs, dropAbstractBytes_eq_rs, hSp.2]
    cases hDisj with
    | inl hAfter =>
      rw [listSlice_splice_right buf patch hWLe hAfter]
    | inr hBefore =>
      rw [listSlice_splice_left buf patch hWLe hBefore]

/-! ## Part IV: Reflective ACU `SepACULaws` over `V2026_06_01` Byte-Range Assertions -/

/-- Pointwise byte-ownership footprint `(allocId, offset) ↦ Prop`. -/
def ByteFootprint : Type :=
  AllocId → Nat → Prop

/-- Disjointness between two `ByteFootprint`s. -/
def fpDisjoint (fp₁ fp₂ : ByteFootprint) : Prop :=
  ∀ (aid : AllocId) (off : Nat), ¬ (fp₁ aid off ∧ fp₂ aid off)

/-- Extensional equivalence between two `ByteFootprint`s (zero `funext` needed). -/
def fpEquiv (fp₁ fp₂ : ByteFootprint) : Prop :=
  ∀ (aid : AllocId) (off : Nat), fp₁ aid off ↔ fp₂ aid off

/-- Separation-logic assertion over unmodified `Trusted.Rustc.V2026_06_01.MirSemantics.Memory`
indexed by an extensional `ByteFootprint`. -/
structure V2026RangeProp where
  pred : Memory → ByteFootprint → Prop
  fpExt : ∀ (m : Memory) (fp₁ fp₂ : ByteFootprint),
    fpEquiv fp₁ fp₂ → pred m fp₁ → pred m fp₂

/-- Entailment between `V2026RangeProp` assertions. -/
def V2026RangeEntails (P Q : V2026RangeProp) : Prop :=
  ∀ (m : Memory) (fp : ByteFootprint), P.pred m fp → Q.pred m fp

/-- Empty byte-footprint assertion over `V2026_06_01.MirSemantics.Memory`. -/
def v2026RangeEmp : V2026RangeProp where
  pred _ fp := ∀ aid off, ¬ fp aid off
  fpExt _ _ _ hEq hEmp aid off h2 := hEmp aid off ((hEq aid off).mpr h2)

/-- Exact byte-range ownership assertion `r ↦ bs` over unmodified `Memory`. -/
def v2026RangePointsTo (r : ByteRange) (bs : List AbstractByte) : V2026RangeProp where
  pred m fp :=
    AllocBytesAtV2026 m r bs ∧
    ∀ aid off, fp aid off ↔ InRange r aid off
  fpExt _ _ _ hEq hPt :=
    ⟨hPt.1, fun aid off => Iff.trans (Iff.symm (hEq aid off)) (hPt.2 aid off)⟩

/-- Separating conjunction over `V2026RangeProp`. -/
def v2026RangeSepConj (P Q : V2026RangeProp) : V2026RangeProp where
  pred m fp :=
    ∃ fp₁ fp₂ : ByteFootprint,
      fpDisjoint fp₁ fp₂ ∧
      (∀ aid off, fp aid off ↔ fp₁ aid off ∨ fp₂ aid off) ∧
      P.pred m fp₁ ∧ Q.pred m fp₂
  fpExt _ _ _ hEq hSep := by
    cases hSep with
    | intro fp₁ hR =>
      cases hR with
      | intro fp₂ hC =>
        exact ⟨fp₁, fp₂, hC.1,
          fun aid off => Iff.trans (Iff.symm (hEq aid off)) (hC.2.1 aid off),
          hC.2.2.1, hC.2.2.2⟩

/-- `V2026RangeProp` satisfies the complete `Anneal.SepAC.SepACULaws` contract (`[]` zero
axioms), enabling reflective ACU normalization and `cancelAtoms` framing directly on
`V2026_06_01` `Memory` byte-range assertions! -/
theorem v2026RangeProp_sepACULaws :
    SepACULaws v2026RangeSepConj v2026RangeEmp V2026RangeEntails := by
  refine ⟨fun _ _ _ h => h, fun _ _ _ h12 h23 m fp hp => h23 m fp (h12 m fp hp),
    ?_, ?_, ?_, ?_⟩
  · intro F P Q hPQ m fp hSep
    cases hSep with
    | intro fp₁ hR =>
      cases hR with
      | intro fp₂ hC =>
        exact ⟨fp₁, fp₂, hC.1, hC.2.1, hC.2.2.1, hPQ m fp₂ hC.2.2.2⟩
  · intro P Q R
    refine ⟨?_, ?_⟩
    · intro m fp hL
      cases hL with
      | intro fp12 hR1 =>
        cases hR1 with
        | intro fp3 hC1 =>
          cases hC1.2.2.1 with
          | intro fp1 hR2 =>
            cases hR2 with
            | intro fp2 hC2 =>
              let fp23 : ByteFootprint := fun aid off => fp2 aid off ∨ fp3 aid off
              refine ⟨fp1, fp23, ?_, ?_, hC2.2.2.1, ⟨fp2, fp3, ?_, ?_, hC2.2.2.2, hC1.2.2.2⟩⟩
              · intro aid off hBoth
                cases hBoth.2 with
                | inl h2 => exact hC2.1 aid off ⟨hBoth.1, h2⟩
                | inr h3 => exact hC1.1 aid off ⟨(hC2.2.1 aid off).mpr (Or.inl hBoth.1), h3⟩
              · intro aid off
                refine ⟨fun h => ?_, fun h => ?_⟩
                · cases (hC1.2.1 aid off).mp h with
                  | inl h12 =>
                    cases (hC2.2.1 aid off).mp h12 with
                    | inl h1 => exact Or.inl h1
                    | inr h2 => exact Or.inr (Or.inl h2)
                  | inr h3 => exact Or.inr (Or.inr h3)
                · cases h with
                  | inl h1 => exact (hC1.2.1 aid off).mpr (Or.inl ((hC2.2.1 aid off).mpr (Or.inl h1)))
                  | inr h23 =>
                    cases h23 with
                    | inl h2 => exact (hC1.2.1 aid off).mpr (Or.inl ((hC2.2.1 aid off).mpr (Or.inr h2)))
                    | inr h3 => exact (hC1.2.1 aid off).mpr (Or.inr h3)
              · intro aid off hBoth
                exact hC1.1 aid off ⟨(hC2.2.1 aid off).mpr (Or.inr hBoth.1), hBoth.2⟩
              · intro _ _; exact Iff.rfl
    · intro m fp hR
      cases hR with
      | intro fp1 hR1 =>
        cases hR1 with
        | intro fp23 hC1 =>
          cases hC1.2.2.2 with
          | intro fp2 hR2 =>
            cases hR2 with
            | intro fp3 hC2 =>
              let fp12 : ByteFootprint := fun aid off => fp1 aid off ∨ fp2 aid off
              refine ⟨fp12, fp3, ?_, ?_, ⟨fp1, fp2, ?_, ?_, hC1.2.2.1, hC2.2.2.1⟩, hC2.2.2.2⟩
              · intro aid off hBoth
                cases hBoth.1 with
                | inl h1 => exact hC1.1 aid off ⟨h1, (hC2.2.1 aid off).mpr (Or.inr hBoth.2)⟩
                | inr h2 => exact hC2.1 aid off ⟨h2, hBoth.2⟩
              · intro aid off
                refine ⟨fun h => ?_, fun h => ?_⟩
                · cases (hC1.2.1 aid off).mp h with
                  | inl h1 => exact Or.inl (Or.inl h1)
                  | inr h23 =>
                    cases (hC2.2.1 aid off).mp h23 with
                    | inl h2 => exact Or.inl (Or.inr h2)
                    | inr h3 => exact Or.inr h3
                · cases h with
                  | inl h12 =>
                    cases h12 with
                    | inl h1 => exact (hC1.2.1 aid off).mpr (Or.inl h1)
                    | inr h2 => exact (hC1.2.1 aid off).mpr (Or.inr ((hC2.2.1 aid off).mpr (Or.inl h2)))
                  | inr h3 => exact (hC1.2.1 aid off).mpr (Or.inr ((hC2.2.1 aid off).mpr (Or.inr h3)))
              · intro aid off hBoth
                exact hC1.1 aid off ⟨hBoth.1, (hC2.2.1 aid off).mpr (Or.inl hBoth.2)⟩
              · intro _ _; exact Iff.rfl
  · intro P Q
    have hDir : ∀ A B, V2026RangeEntails (v2026RangeSepConj A B) (v2026RangeSepConj B A) := by
      intro A B m fp hAB
      cases hAB with
      | intro fp1 hR =>
        cases hR with
        | intro fp2 hC =>
          refine ⟨fp2, fp1, fun aid off hb => hC.1 aid off ⟨hb.2, hb.1⟩, ?_, hC.2.2.2, hC.2.2.1⟩
          intro aid off
          exact Iff.trans (hC.2.1 aid off) ⟨fun o => o.elim Or.inr Or.inl, fun o => o.elim Or.inr Or.inl⟩
    exact ⟨hDir P Q, hDir Q P⟩
  · intro P
    refine ⟨?_, ?_⟩
    · intro m fp hPE
      cases hPE with
      | intro fp1 hR =>
        cases hR with
        | intro fp2 hC =>
          apply P.fpExt m fp1 fp _ hC.2.2.1
          intro aid off
          refine ⟨fun h1 => (hC.2.1 aid off).mpr (Or.inl h1), fun h => ?_⟩
          cases (hC.2.1 aid off).mp h with
          | inl h1 => exact h1
          | inr h2 => exact False.elim (hC.2.2.2 aid off h2)
    · intro m fp hP
      refine ⟨fp, fun _ _ => False, fun _ _ hb => hb.2, ?_, hP, fun _ _ hf => hf⟩
      intro aid off
      exact ⟨Or.inl, fun o => o.elim (fun h => h) False.elim⟩

/-- Exact symbolic `split_at_mut` bientailment inside `V2026RangeProp` (`[propext]` only):
`r ↦ bs ⊣⊢ rL ↦ bs.take k ∗ rR ↦ bs.drop k` for every `k ≤ r.len`. -/
theorem v2026RangePointsTo_split_bientails (r : ByteRange) (bs : List AbstractByte)
    {k : Nat} (hk : k ≤ r.len) :
    Bientails V2026RangeEntails
      (v2026RangePointsTo r bs)
      (v2026RangeSepConj
        (v2026RangePointsTo (rangeSplit r k).1 (bs.take k))
        (v2026RangePointsTo (rangeSplit r k).2 (bs.drop k))) := by
  refine ⟨?_, ?_⟩
  · intro m fp hPt
    have hSp := (ownRange_split_iff m r bs hk).mp hPt.1
    refine ⟨InRange (rangeSplit r k).1, InRange (rangeSplit r k).2, ?_, ?_,
      ⟨hSp.1, fun _ _ => Iff.rfl⟩, ⟨hSp.2, fun _ _ => Iff.rfl⟩⟩
    · intro aid off hb
      exact rangeDisjoint_no_shared_offset (rangeSplit_disjoint r k) hb.1 hb.2
    · intro aid off
      exact Iff.trans (hPt.2 aid off) (rangeSplit_covers_iff r hk aid off)
  · intro m fp hSep
    cases hSep with
    | intro fp1 hR =>
      cases hR with
      | intro fp2 hC =>
        have hAll := (ownRange_split_iff m r bs hk).mpr ⟨hC.2.2.1.1, hC.2.2.2.1⟩
        refine ⟨hAll, fun aid off => ?_⟩
        refine Iff.trans (hC.2.1 aid off) ?_
        refine Iff.trans ?_ (Iff.symm (rangeSplit_covers_iff r hk aid off))
        exact ⟨fun o => o.elim (fun h1 => Or.inl ((hC.2.2.1.2 aid off).mp h1))
                               (fun h2 => Or.inr ((hC.2.2.2.2 aid off).mp h2)),
               fun o => o.elim (fun h1 => Or.inl ((hC.2.2.1.2 aid off).mpr h1))
                               (fun h2 => Or.inr ((hC.2.2.2.2 aid off).mpr h2))⟩

/-- `V2026RangeProp` is strictly linear (not affine): owning a non-empty `ByteRange` does not
entail `v2026RangeEmp` (`[propext]` only). -/
theorem not_affineEntails_v2026RangeProp :
    ¬ AffineEntails v2026RangeEmp V2026RangeEntails := by
  intro hAff
  let a0 : CapturedAllocation :=
    { allocId := 0
      align := ⟨1⟩
      mutability := .mut
      bytes := [some 0xAA]
      relocations := [] }
  let m0 : Memory := { emptyMemory with nextAllocId := 1, globals := [a0] }
  let r0 : ByteRange := ⟨0, 0, 1⟩
  have hAt : AllocBytesAtV2026 m0 r0 [.init 0xAA none] :=
    ⟨a0, rfl, Nat.le_refl 1, rfl, rfl⟩
  have hEmp := hAff (v2026RangePointsTo r0 [.init 0xAA none]) m0 (InRange r0)
    ⟨hAt, fun _ _ => Iff.rfl⟩
  exact hEmp 0 0 ⟨rfl, Nat.le_refl 0, Nat.lt_succ_self 0⟩

/-- Reflective ACU frame cancellation on `V2026RangeProp` (`[]` zero axioms). -/
theorem v2026Range_frame_cancel (env : Nat → V2026RangeProp)
    {fuel : Nat} {lhs rhs : SepExpr}
    (hRes :
      V2026RangeEntails
        (evalAtomList v2026RangeSepConj v2026RangeEmp env
          (cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).1)
        (evalAtomList v2026RangeSepConj v2026RangeEmp env
          (cancelAtoms (normSepFuel fuel lhs) (normSepFuel fuel rhs)).2)) :
    V2026RangeEntails
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp env fuel lhs)
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp env fuel rhs) :=
  sepAC_entails_of_cancelAtoms v2026RangeProp_sepACULaws env hRes

/-! ## Part V: Concrete Positive & Fail-Closed Negative Witnesses -/

/-- Scrambled 6-atom `SepExpr` with nested `.emp` units. -/
def rsExpr6Lhs : SepExpr :=
  .sep (.sep (.atom 4) (.sep .emp (.atom 1)))
    (.sep (.sep (.atom 5) (.atom 0)) (.sep (.atom 2) (.sep (.atom 3) .emp)))

/-- Right scrambled 6-atom `SepExpr` denoting `{0..5}`. -/
def rsExpr6Rhs : SepExpr :=
  .sep (.atom 0)
    (.sep (.sep (.atom 3) (.atom 5))
      (.sep (.atom 1) (.sep (.atom 4) (.atom 2))))

/-- Balanced 16-atom forward `SepExpr` (`0..15`). -/
def rsRev16Lhs : SepExpr :=
  .sep
    (.sep (.sep (.sep (.atom 0) (.atom 1)) (.sep (.atom 2) (.atom 3)))
      (.sep (.sep (.atom 4) (.atom 5)) (.sep (.atom 6) (.atom 7))))
    (.sep (.sep (.sep (.atom 8) (.atom 9)) (.sep (.atom 10) (.atom 11)))
      (.sep (.sep (.atom 12) (.atom 13)) (.sep (.atom 14) (.atom 15))))

/-- Balanced 16-atom reversed `SepExpr` (`15..0`). -/
def rsRev16Rhs : SepExpr :=
  .sep
    (.sep (.sep (.sep (.atom 15) (.atom 14)) (.sep (.atom 13) (.atom 12)))
      (.sep (.sep (.atom 11) (.atom 10)) (.sep (.atom 9) (.atom 8))))
    (.sep (.sep (.sep (.atom 7) (.atom 6)) (.sep (.atom 5) (.atom 4)))
      (.sep (.sep (.atom 3) (.atom 2)) (.sep (.atom 1) (.atom 0))))

/-- Positive witness 1 (`[]` zero axioms): reflective ACU bientailments by `rfl` on BOTH
`PHeapProp Nat` and `V2026RangeProp`, plus `frame_cancel` and `v2026Range_frame_cancel`
cancelling 3 shared atoms down to 1 residual entailment! -/
theorem witness_reflective_acu_and_frame_cancel
    (envP : Nat → PHeapProp Nat) (hResP : PHeapEntails (envP 0) (envP 3))
    (envR : Nat → V2026RangeProp) (hResR : V2026RangeEntails (envR 0) (envR 3)) :
    Bientails (@PHeapEntails Nat)
      (evalSepExprFuel pheapSepConj pheapEmp envP 8 rsExpr6Lhs)
      (evalSepExprFuel pheapSepConj pheapEmp envP 8 rsExpr6Rhs) ∧
    Bientails (@PHeapEntails Nat)
      (evalSepExprFuel pheapSepConj pheapEmp envP 6 rsRev16Lhs)
      (evalSepExprFuel pheapSepConj pheapEmp envP 6 rsRev16Rhs) ∧
    PHeapEntails
      (evalSepExprFuel pheapSepConj pheapEmp envP 8
        (.sep (.atom 2) (.sep (.atom 0) (.sep (.atom 5) (.atom 1)))))
      (evalSepExprFuel pheapSepConj pheapEmp envP 8
        (.sep (.atom 1) (.sep (.atom 3) (.sep (.atom 2) (.atom 5))))) ∧
    Bientails V2026RangeEntails
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp envR 8 rsExpr6Lhs)
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp envR 8 rsExpr6Rhs) ∧
    V2026RangeEntails
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp envR 8
        (.sep (.atom 2) (.sep (.atom 0) (.sep (.atom 5) (.atom 1)))))
      (evalSepExprFuel v2026RangeSepConj v2026RangeEmp envR 8
        (.sep (.atom 1) (.sep (.atom 3) (.sep (.atom 2) (.atom 5))))) := by
  have hLP := pheapProp_sepACULaws Nat
  have hLR := v2026RangeProp_sepACULaws
  refine ⟨frame_bientails_of_norm_eq envP (fuel := 8) rfl,
    frame_bientails_of_norm_eq envP (fuel := 6) rfl, ?_,
    sepAC_bientails_of_norm_eq hLR envR (fuel := 8) rfl, ?_⟩
  · apply frame_cancel envP (fuel := 8)
    change PHeapEntails (pheapSepConj (envP 0) pheapEmp) (pheapSepConj (envP 3) pheapEmp)
    exact hLP.trans _ (envP 0) _ (hLP.rightUnit (envP 0)).1
      (hLP.trans _ (envP 3) _ hResP (hLP.rightUnit (envP 3)).2)
  · apply v2026Range_frame_cancel envR (fuel := 8)
    change V2026RangeEntails
      (v2026RangeSepConj (envR 0) v2026RangeEmp)
      (v2026RangeSepConj (envR 3) v2026RangeEmp)
    exact hLR.trans _ (envR 0) _ (hLR.rightUnit (envR 0)).1
      (hLR.trans _ (envR 3) _ hResR (hLR.rightUnit (envR 3)).2)

/-- 16-entry `PTree Nat` built via computable `ptreeTabulate` (`i ↦ i * 10 + 1`). -/
def rsCtx16 : PTree Nat :=
  ptreeTabulate 5 (fun i => cond (Nat.blt i 16) (some (i * 10 + 1)) none)

/-- 2-key required footprint (`key 3 ↦ 31`, `key 11 ↦ 111`). -/
def rsReq2 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 then some 31
    else if Nat.beq i 11 then some 111
    else none)

/-- 2-key updated postcondition (`key 3 ↦ 300`, `key 11 ↦ 1100`). -/
def rsPost2 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 then some 300
    else if Nat.beq i 11 then some 1100
    else none)

/-- Disjoint 1-key second footprint (`key 7 ↦ 700`). -/
def rsPostOther : PTree Nat :=
  ptreeTabulate 5 (fun i => if Nat.beq i 7 then some 700 else none)

/-- Expected 14-key remainder after subtracting `rsReq2` from `rsCtx16`. -/
def rsRem14 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 || Nat.beq i 11 then none
    else cond (Nat.blt i 16) (some (i * 10 + 1)) none)

/-- Expected 13-key remainder (excluding `3, 7, 11`). -/
def rsRem13 : PTree Nat :=
  ptreeTabulate 5 (fun i =>
    if Nat.beq i 3 || Nat.beq i 7 || Nat.beq i 11 then none
    else cond (Nat.blt i 16) (some (i * 10 + 1)) none)

/-- Missing-key requirement (`key 20 ↦ 1`) for fail-closed regression. -/
def rsBadMissing : PTree Nat :=
  ptreeTabulate 6 (fun i => if Nat.beq i 20 then some 1 else none)

/-- Mismatched-value requirement (`key 3 ↦ 999`) for fail-closed regression. -/
def rsBadValue : PTree Nat :=
  ptreeTabulate 5 (fun i => if Nat.beq i 3 then some 999 else none)

/-- Positive + fail-closed Lithium `PTree` framing & diamond-join witness (`[propext]` only). -/
theorem witness_lithium_ptree_framing_and_diamond :
    (∃ step : PTree Nat → Option (PTree Nat),
      LithiumTriple rsReq2 rsPost2 step ∧
      PTree.DisjointProp rsReq2 rsRem14 ∧
      PTree.DisjointProp rsPost2 rsRem14 ∧
      step rsCtx16 = some (PTree.union rsPost2 rsRem14)) ∧
    ((PTree.union rsPost2 rsRem14).get (natToPosAt 5 3) = some 300 ∧
      (PTree.union rsPost2 rsRem14).get (natToPosAt 5 11) = some 1100 ∧
      (PTree.union rsPost2 rsRem14).get (natToPosAt 5 7) = some 71) ∧
    (PTree.union rsPost2 (PTree.union rsPostOther rsRem13) =
      PTree.union rsPostOther (PTree.union rsPost2 rsRem13)) ∧
    PTree.diffWith Nat.beq rsCtx16 rsBadMissing = none ∧
    PTree.diffWith Nat.beq rsCtx16 rsBadValue = none := by
  have hDiffOk : PTree.diffWith Nat.beq rsCtx16 rsReq2 = some rsRem14 := rfl
  have hDPostOther : PTree.DisjointProp rsPost2 rsPostOther := by
    have hD : PTree.diffWith Nat.beq (PTree.union rsPost2 rsPostOther) rsPost2 =
        some rsPostOther := rfl
    exact (ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true hD).1
  have hReqEq :
      rsReq2 = PTree.union (PTree.singleton (natToPosAt 5 3) 31)
        (PTree.singleton (natToPosAt 5 11) 111) := rfl
  have hPostEq :
      rsPost2 = PTree.union (PTree.singleton (natToPosAt 5 3) 300)
        (PTree.singleton (natToPosAt 5 11) 1100) := rfl
  have hD311 :
      PTree.DisjointProp (PTree.singleton (natToPosAt 5 3) 31)
        (PTree.singleton (natToPosAt 5 11) 111) := by
    have hD : PTree.diffWith Nat.beq rsReq2 (PTree.singleton (natToPosAt 5 3) 31) =
        some (PTree.singleton (natToPosAt 5 11) 111) := rfl
    exact (ptree_diffWith_sound Nat.beq Nat.eq_of_beq_eq_true hD).1
  cases ptree_set_lithiumTriple_exists Nat.beq natBeq_refl_rs (natToPosAt 5 3) 31 300 with
  | intro s1 hs1 =>
    cases ptree_set_lithiumTriple_exists Nat.beq natBeq_refl_rs (natToPosAt 5 11) 111 1100 with
    | intro s2 hs2 =>
      have hTr : LithiumTriple rsReq2 rsPost2 (ptreeBindStep s1 s2) := by
        rw [hReqEq, hPostEq]
        exact lithiumTriple_union_disjoint hD311 hs1 hs2
      have hFr := lithiumFrame_of_diffWith Nat.beq Nat.eq_of_beq_eq_true hDiffOk hTr
      exact ⟨⟨ptreeBindStep s1 s2, hTr, hFr.1, hFr.2.1, hFr.2.2⟩,
        ⟨rfl, rfl, rfl⟩, lithiumFrame_diamond_comm hDPostOther, rfl, rfl⟩

/-- $O(1)$ `1_000_000`-byte 3-way `split_at_mut` witness (`[]` zero axioms). -/
theorem witness_rangeSplit_one_million_bytes_O1 :
    let rAll : ByteRange := ⟨7, 0, 1000000⟩
    let sp1 := rangeSplit rAll 345678
    let sp2 := rangeSplit sp1.2 400000
    RangeDisjoint sp1.1 sp2.1 ∧
    RangeDisjoint sp1.1 sp2.2 ∧
    RangeDisjoint sp2.1 sp2.2 ∧
    byteRangesOverlapBool sp1.1.start sp1.1.len sp2.1.start sp2.1.len = false ∧
    rangeMerge sp1.1 (rangeMerge sp2.1 sp2.2) = rAll ∧
    (∀ aid off,
      InRange rAll aid off ↔
        InRange sp1.1 aid off ∨ InRange sp2.1 aid off ∨ InRange sp2.2 aid off) ∧
    (∀ aid off, InRange sp1.1 aid off → ¬ InRange sp2.2 aid off) := by
  intro rAll sp1 sp2
  have hk1 : 345678 ≤ 1000000 := natLe_of_ble_rs rfl
  have hk2 : 400000 ≤ 1000000 - 345678 := natLe_of_ble_rs rfl
  have hD1BoolEq : rangeDisjointBool sp1.1 sp2.1 = true := by
    dsimp only [rAll, sp1, sp2, rangeSplit, rangeDisjointBool]
    rfl
  have hD1Bool : RangeDisjoint sp1.1 sp2.1 :=
    (rangeDisjointBool_iff sp1.1 sp2.1).mp hD1BoolEq
  have hD1Sym : RangeDisjoint sp1.2 sp1.1 :=
    rangeDisjoint_symm (rangeSplit_disjoint rAll 345678)
  have hSub := rangeDisjoint_of_subrange hk2 hD1Sym
  have hD2 : RangeDisjoint sp2.1 sp2.2 := rangeSplit_disjoint sp1.2 400000
  have hMergeAll : rangeMerge sp1.1 (rangeMerge sp2.1 sp2.2) = rAll := by
    rw [rangeMerge_split sp1.2 hk2]
    exact rangeMerge_split rAll hk1
  have hCov :
      ∀ aid off,
        InRange rAll aid off ↔
          InRange sp1.1 aid off ∨ InRange sp2.1 aid off ∨ InRange sp2.2 aid off := by
    intro aid off
    have hC1 := rangeSplit_covers_iff rAll hk1 aid off
    have hC2 := rangeSplit_covers_iff sp1.2 hk2 aid off
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases hC1.mp h with
      | inl hL => exact Or.inl hL
      | inr hR => exact Or.inr (hC2.mp hR)
    · cases h with
      | inl hL => exact hC1.mpr (Or.inl hL)
      | inr hR => exact hC1.mpr (Or.inr (hC2.mpr hR))
  exact ⟨hD1Bool, rangeDisjoint_symm hSub.2, hD2,
    byteRangesOverlapBool_false_of_sameAlloc_rangeDisjoint rfl hD1Bool,
    hMergeAll, hCov,
    fun _ _ h1 h2 => rangeDisjoint_no_shared_offset (rangeDisjoint_symm hSub.2) h1 h2⟩

/-- Concrete 2-allocation unmodified `V2026_06_01.MirSemantics.Memory` fixture:
immutable 4-byte allocation `0` (`0xCC`) and mutable 16-byte allocation `1` (`0x11`). -/
def rsInitMemoryV2026 : Memory :=
  { emptyMemory with
    nextAllocId := 2
    globals :=
      [{ allocId := 0
         align := ⟨1⟩
         mutability := .not
         bytes := List.replicate 4 (some 0xCC)
         relocations := [] },
       { allocId := 1
         align := ⟨4⟩
         mutability := .mut
         bytes := List.replicate 16 (some 0x11)
         relocations := [] }] }

/-- 4-byte write payload into `[6..10)` of allocation `1`. -/
def rsPatchBytes : List (Option UInt8) :=
  [some 0xA0, some 0xA1, some 0xA2, some 0xA3]

/-- Corresponding 4 `AbstractByte`s for `[6..10)`. -/
def rsPatchAbsBytes : List AbstractByte :=
  [.init 0xA0 none, .init 0xA1 none, .init 0xA2 none, .init 0xA3 none]

/-- End-to-end `V2026_06_01.MirSemantics.Memory` & `SpatialMemV2026.V2026ByteMem`
same-allocation + cross-allocation `split_at_mut` write-frame witness (`[propext]` only). -/
theorem witness_v2026_sameAlloc_and_crossAlloc_write_frame :
    let rAlloc0 : ByteRange := ⟨0, 0, 4⟩
    let rAll1 : ByteRange := ⟨1, 0, 16⟩
    let rPre : ByteRange := (rangeSplit rAll1 6).1
    let rTail := (rangeSplit rAll1 6).2
    let rMid : ByteRange := (rangeSplit rTail 4).1
    let rPost : ByteRange := (rangeSplit rTail 4).2
    (∃ m' : Memory,
      writeMemoryBytesV2026 rsInitMemoryV2026 rMid rsPatchBytes = some m' ∧
      AllocBytesAtV2026 m' rPre (List.replicate 6 (.init 0x11 none)) ∧
      AllocBytesAtV2026 m' rPost (List.replicate 6 (.init 0x11 none)) ∧
      AllocBytesAtV2026 m' rAlloc0 (List.replicate 4 (.init 0xCC none)) ∧
      AllocBytesAtV2026 m' rMid rsPatchAbsBytes) ∧
    (∃ bm' : V2026ByteMem,
      writeV2026Bytes (memGlobalsToByteMem rsInitMemoryV2026) ⟨rMid.allocId, rMid.start⟩ 2
        rsPatchAbsBytes = some bm' ∧
      AllocBytesAtByteMem bm' rPre (List.replicate 6 (.init 0x11 none)) ∧
      AllocBytesAtByteMem bm' rPost (List.replicate 6 (.init 0x11 none)) ∧
      AllocBytesAtByteMem bm' rAlloc0 (List.replicate 4 (.init 0xCC none)) ∧
      readV2026Bytes bm' ⟨rMid.allocId, rMid.start⟩ 4 2 = some rsPatchAbsBytes) := by
  intro rAlloc0 rAll1 rPre rTail rMid rPost
  have hInit1 : AllocBytesAtV2026 rsInitMemoryV2026 rAll1
      (List.replicate 16 (.init 0x11 none)) :=
    ⟨{ allocId := 1, align := ⟨4⟩, mutability := .mut,
       bytes := List.replicate 16 (some 0x11), relocations := [] },
      rfl, Nat.le_refl 16, rfl, rfl⟩
  have hInit0 : AllocBytesAtV2026 rsInitMemoryV2026 rAlloc0
      (List.replicate 4 (.init 0xCC none)) :=
    ⟨{ allocId := 0, align := ⟨1⟩, mutability := .not,
       bytes := List.replicate 4 (some 0xCC), relocations := [] },
      rfl, Nat.le_refl 4, rfl, rfl⟩
  have hSp1 := (ownRange_split_iff rsInitMemoryV2026 rAll1
    (List.replicate 16 (.init 0x11 none)) (k := 6) (natLe_of_ble_rs rfl)).mp hInit1
  have hSp2 := (ownRange_split_iff rsInitMemoryV2026 rTail
    ((List.replicate 16 (.init 0x11 none)).drop 6) (k := 4) (natLe_of_ble_rs rfl)).mp hSp1.2
  have hDPre : RangeDisjoint rMid rPre := (rangeDisjointBool_iff rMid rPre).mp rfl
  have hDPost : RangeDisjoint rMid rPost := (rangeDisjointBool_iff rMid rPost).mp rfl
  have hD0 : RangeDisjoint rMid rAlloc0 := (rangeDisjointBool_iff rMid rAlloc0).mp rfl
  refine ⟨?_, ?_⟩
  · cases hW : writeMemoryBytesV2026 rsInitMemoryV2026 rMid rsPatchBytes with
    | none => nomatch hW
    | some m' =>
      have hFrPre := allocBytesAtV2026_frame_of_write_disjoint hDPre hW hSp1.1
      have hFrPost := allocBytesAtV2026_frame_of_write_disjoint hDPost hW hSp2.2
      have hFr0 := allocBytesAtV2026_frame_of_write_disjoint hD0 hW hInit0
      have hMid : AllocBytesAtV2026 m' rMid rsPatchAbsBytes := by
        injection hW with hMeq
        rw [← hMeq]
        exact ⟨{ allocId := 1, align := ⟨4⟩, mutability := .mut,
                 bytes := ((List.replicate 16 (some 0x11)).take 6 ++ rsPatchBytes) ++
                   (List.replicate 16 (some 0x11)).drop 10,
                 relocations := [] },
          rfl, natLe_of_ble_rs rfl, rfl, rfl⟩
      exact ⟨m', rfl, hFrPre, hFrPost, hFr0, hMid⟩
  · have hBmPre := allocBytesAtByteMem_of_allocBytesAtV2026 hSp1.1
    have hBmPost := allocBytesAtByteMem_of_allocBytesAtV2026 hSp2.2
    have hBm0 := allocBytesAtByteMem_of_allocBytesAtV2026 hInit0
    cases hW : writeV2026Bytes (memGlobalsToByteMem rsInitMemoryV2026) ⟨1, 6⟩ 2
        rsPatchAbsBytes with
    | none => nomatch hW
    | some bm' =>
      have hFrPre :=
        allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint rfl hDPre hW hBmPre
      have hFrPost :=
        allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint rfl hDPost hW hBmPost
      have hFr0 :=
        allocBytesAtByteMem_frame_of_writeV2026Bytes_disjoint rfl hD0 hW hBm0
      have hSelf :=
        allocBytesAtByteMem_of_writeV2026Bytes_self (rW := rMid) rfl hW
      exact ⟨bm', hW, hFrPre, hFrPost, hFr0, hSelf.2⟩

/-- Fail-closed negative controls for `RangeSpanV2026` (`[propext]` only):
1. Overlapping ranges return `rangeDisjointBool = false`, `¬ RangeDisjoint`, and
   `byteRangesOverlapBool = true`;
2. `rangeMergeChecked` rejects non-adjacent same-allocation ranges and cross-allocation ranges;
3. Out-of-bounds and missing-allocation `AllocBytesAtV2026` are refuted (`¬ AllocBytesAtV2026`);
4. Writing to a read-only global allocation (`0`), an out-of-bounds slice, or a dead
   `V2026ByteMem` allocation fails closed (`none`);
5. Strict linearity (`¬ AffineEntails`) of both `PHeapProp` and `V2026RangeProp`. -/
theorem witness_rangespan_negative_controls :
    rangeDisjointBool ⟨7, 0, 10⟩ ⟨7, 5, 10⟩ = false ∧
    ¬ RangeDisjoint ⟨7, 0, 10⟩ ⟨7, 5, 10⟩ ∧
    byteRangesOverlapBool 0 10 5 10 = true ∧
    rangeMergeChecked ⟨1, 0, 4⟩ ⟨1, 5, 4⟩ = none ∧
    rangeMergeChecked ⟨1, 0, 4⟩ ⟨2, 4, 4⟩ = none ∧
    ¬ AllocBytesAtV2026 rsInitMemoryV2026 ⟨1, 14, 4⟩ rsPatchAbsBytes ∧
    ¬ AllocBytesAtV2026 rsInitMemoryV2026 ⟨99, 0, 4⟩ rsPatchAbsBytes ∧
    writeMemoryBytesV2026 rsInitMemoryV2026 ⟨0, 0, 4⟩ rsPatchBytes = none ∧
    writeMemoryBytesV2026 rsInitMemoryV2026 ⟨1, 14, 4⟩ rsPatchBytes = none ∧
    (let deadBm : V2026ByteMem :=
      { nextAllocId := 2
        allocs := [{ allocId := 1, alignBytes := 4, mutability := .mut,
                     bytes := List.replicate 16 (.init 0x11 none), live := false }] }
     writeV2026Bytes deadBm ⟨1, 0⟩ 1 rsPatchAbsBytes = none) ∧
    ¬ AffineEntails (@pheapEmp Nat) (@PHeapEntails Nat) ∧
    ¬ AffineEntails v2026RangeEmp V2026RangeEntails := by
  refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_, rfl, rfl, rfl,
    not_affineEntails_pheapProp 0, not_affineEntails_v2026RangeProp⟩
  · intro hD
    have hT := (rangeDisjointBool_iff ⟨7, 0, 10⟩ ⟨7, 5, 10⟩).mpr hD
    exact Bool.noConfusion hT
  · intro hOob
    cases hOob with
    | intro a ha =>
      let aExp : CapturedAllocation :=
        { allocId := 1, align := ⟨4⟩, mutability := .mut,
          bytes := List.replicate 16 (some 0x11), relocations := [] }
      have hEq : some a = some aExp := ha.1.symm
      injection hEq with hA
      have hLe := ha.2.1
      rw [hA] at hLe
      have hF : Nat.ble 18 16 = true := natBle_of_le_rs hLe
      exact Bool.noConfusion hF
  · intro hMiss
    cases hMiss with
    | intro _ ha =>
      nomatch ha.1

/-- Pointer-bearing mutable 16-byte global allocation `3` in unmodified `V2026_06_01` form:
an 8-byte pointer relocation at `[0, 8)` targeting allocation `1` followed by 8 bytes of plain
data at `[8, 16)` (a `struct { p: *const u8, data: [u8; 8] }` static). -/
def rsPtrAlloc3 : CapturedAllocation :=
  { allocId := 3
    align := ⟨8⟩
    mutability := .mut
    bytes := List.replicate 16 (some 0x00)
    relocations := [(0, { allocId := 1, offsetBytes := 0 })] }

/-- Single-allocation `Memory` holding `rsPtrAlloc3`. -/
def rsPtrMemoryV2026 : Memory :=
  { emptyMemory with nextAllocId := 4, globals := [rsPtrAlloc3] }

/-- Provenance-carrying pointer bytes of `rsPtrAlloc3` (`(allocId, tag) = (1, 1)`). -/
def rsPtrAbsBytes : List AbstractByte :=
  List.replicate 8 (.init 0x00 (some (1, 1)))

/-- **Relocation/provenance guard witness (`[propext]` only)** on a satisfiable pointer-bearing
`V2026_06_01` allocation:
1. the pointer bytes `[0, 8)` genuinely carry provenance under unmodified
   `globalAllocSliceToAbstractBytes` (`abstractBytesHaveProv = true`);
2. a same-allocation data write into the disjoint `[8, 12)` succeeds, reads back
   provenance-free via the GENERAL `allocBytesAtV2026_of_write_self`, and frames the
   provenance-carrying pointer bytes via `allocBytesAtV2026_frame_of_write_disjoint`;
3. raw-data writes overlapping the relocation span (`[4, 8)`, `[0, 4)`, `[6, 10)`) fail
   closed, so plain bytes can never be read back with forged pointer provenance. -/
theorem witness_v2026_relocation_provenance_guard :
    AllocBytesAtV2026 rsPtrMemoryV2026 ⟨3, 0, 8⟩ rsPtrAbsBytes ∧
    abstractBytesHaveProv rsPtrAbsBytes = true ∧
    (∃ m' : Memory,
      writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 8, 4⟩ rsPatchBytes = some m' ∧
      AllocBytesAtV2026 m' ⟨3, 8, 4⟩ rsPatchAbsBytes ∧
      abstractBytesHaveProv rsPatchAbsBytes = false ∧
      AllocBytesAtV2026 m' ⟨3, 0, 8⟩ rsPtrAbsBytes ∧
      AllocBytesAtV2026 m' ⟨3, 0, 12⟩ (rsPtrAbsBytes ++ rsPatchAbsBytes)) ∧
    writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 4, 0⟩ [] = some rsPtrMemoryV2026 ∧
    writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 4, 4⟩ rsPatchBytes = none ∧
    writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 0, 4⟩ rsPatchBytes = none ∧
    writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 6, 4⟩ rsPatchBytes = none := by
  have hPtr : AllocBytesAtV2026 rsPtrMemoryV2026 ⟨3, 0, 8⟩ rsPtrAbsBytes :=
    ⟨rsPtrAlloc3, rfl, natLe_of_ble_rs rfl, rfl, rfl⟩
  refine ⟨hPtr, rfl, ?_, rfl, rfl, rfl, rfl⟩
  cases hW : writeMemoryBytesV2026 rsPtrMemoryV2026 ⟨3, 8, 4⟩ rsPatchBytes with
  | none => nomatch hW
  | some m' =>
    have hD : RangeDisjoint ⟨3, 8, 4⟩ ⟨3, 0, 8⟩ := (rangeDisjointBool_iff _ _).mp rfl
    have hSelf := allocBytesAtV2026_of_write_self hW
    have hFr := allocBytesAtV2026_frame_of_write_disjoint hD hW hPtr
    have hMerged := ownRange_of_rangeMergeChecked hFr hSelf rfl
    exact ⟨m', rfl, hSelf, rfl, hFr, hMerged⟩

end Anneal.SepAC.RangeSpanV2026
