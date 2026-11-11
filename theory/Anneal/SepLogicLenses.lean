-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

import Anneal.SepLogic
import Anneal.FunctionalTranslation
import Anneal.MirLiftCore
import Anneal.MirFuelFree

namespace Anneal.SepLogicLenses

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.VerificationResult

open Anneal.UnsafeObligations
open Anneal.SepLogic
open Anneal.FunctionalTranslation
open Anneal.MirLiftCore
open Anneal.MirFuelFree
open Anneal.Rustc.V2026_06_01.SymbolicEval (mirNormalPost)

@[simp]
private theorem endsWithSubslice_norm_field (idx : FieldIdx) (ty : Ty) :
    endsWithSubslice (normalizeSubsliceProjections (stripTransparentProjections [.field idx ty])) =
      false := rfl

private theorem resolveDerefWriteFullProj_nil_nil
    {il tl cl : List LocalSlot} {ptrVal : ProvenancePtr} {sz : Nat} {entry : BorrowEntry}
    (hP : entry.targetProjection = []) :
    resolveDerefWriteFullProj il tl (.ptr ptrVal sz) entry [] cl = [] := by
  unfold resolveDerefWriteFullProj; dsimp only; rw [hP]; rfl

private theorem resolveDerefWriteFullProj_nil_field
    {il tl cl : List LocalSlot} {ptrVal : ProvenancePtr} {sz : Nat} {entry : BorrowEntry}
    {subIdx : FieldIdx} {subTy : Ty}
    (hP : entry.targetProjection = []) :
    resolveDerefWriteFullProj il tl (.ptr ptrVal sz) entry [.field subIdx subTy] cl =
      [.field subIdx subTy] := by
  unfold resolveDerefWriteFullProj; dsimp only; rw [hP]; rfl

private theorem resolveDerefWriteFullProj_field_nil
    {il tl cl : List LocalSlot} {ptrVal : ProvenancePtr} {sz : Nat} {entry : BorrowEntry}
    {outerIdx : FieldIdx} {outerTy : Ty}
    (hP : entry.targetProjection = [.field outerIdx outerTy])
    (hOff : ptrVal.offsetBytes = 0) :
    resolveDerefWriteFullProj il tl (.ptr ptrVal sz) entry [] cl =
      [.field outerIdx outerTy] := by
  unfold resolveDerefWriteFullProj; dsimp only; rw [hP, hOff]; rfl

private theorem resolveDerefWriteFullProj_field_field
    {il tl cl : List LocalSlot} {ptrVal : ProvenancePtr} {sz : Nat} {entry : BorrowEntry}
    {outerIdx subIdx : FieldIdx} {outerTy subTy : Ty}
    (hP : entry.targetProjection = [.field outerIdx outerTy])
    (hOff : ptrVal.offsetBytes = 0) :
    resolveDerefWriteFullProj il tl (.ptr ptrVal sz) entry [.field subIdx subTy] cl =
      [.field outerIdx outerTy, .field subIdx subTy] := by
  unfold resolveDerefWriteFullProj; dsimp only; rw [hP, hOff]; rfl

/-!
# Separation-Logic-Backed Mutable Lenses & Pure Deref Lifting (`FF-4.1`)

This module connects Anneal's separation logic (`SepProp`, `sepConj`,
`DisjointFootprints`, `ActiveTypedMutBorrow`, `FieldPointsTo`,
`ActiveTypedFieldMutBorrow`, `AgreeOnSubplaceFootprint`, `SubplaceLocalSepProp`,
`FieldMutBorrowBinding`, `sepConjFieldBindings`) and functional lens layer
(`MutLens`, `LawfulMutLens`, `memoryPtrMutLens`, `treeMemoryPtrMutLens`,
`treeFieldMemoryPtrMutLens`, `subplaceTreeMutLens`) to fuel-free `ITree` weakest
preconditions (`MirWpConverges`, `StatefulVerificationResult`,
`TotalVerificationResult`) over the `I-10` Tree Borrows and 12-field `Memory`
model. No proof here destructures the `Memory` record.

1. **Section 1 (lens algebra).** `IndependentLenses`, `prodMutLens`,
   `PairwiseIndependentLenses`, and the generic restriction lemmas
   `LawfulMutLens.of_sub_agree` and `IndependentLenses.of_sub_agree`, which
   derive the lens laws and pairwise independence of `memoryPtrMutLens` (under
   `ExclusiveActiveBorrow`), `treeMemoryPtrMutLens` (under
   `TreeExclusiveBorrow`), and the sub-allocation aggregate field lens
   `treeFieldMemoryPtrMutLens` (under `TreeFieldExclusiveBorrow`) from
   `rawPtrMutLens` and `rawFieldMutLens`, together with the separation-logic
   bridges `sepConj_entails_independentLenses`,
   `sepConj_entails_independentTreeLenses`,
   `sepConj_entails_independentTreeFieldLenses`, and `k`-ary
   `sepConjFieldBindings_entails_independentTreeFieldLensFamily` /
   `sepConjFieldBindings_entails_pairwiseIndependentTreeFieldLenses` (over
   `FieldPointsTo` and `ActiveTypedFieldMutBorrow`).
2. **Section 2 (lifting).** Both whole-allocation (`SepLensStateInv`,
   `LensFramePreserved`, `mirWpConverges_of_sepLenses`) and sub-place /
   field-granular (`BorrowSubplace`, `SepSubplaceLensStateInv`,
   `SubplaceLensFramePreserved`, `mirWpConverges_of_sepSubplaceLenses`,
   `verifyStatefulMir_of_sepSubplaceLenses`,
   `verifyTotalMir_of_sepSubplaceLenses`,
   `verifyStatefulMir_of_sepSubplaceLenses_supportedFrame`,
   `verifyTotalMir_of_sepSubplaceLenses_supportedFrame`) lifting soundness for
   `LiftDerefRead`, `LiftDerefFieldRead`, `LiftDerefWrite` (root `*p = rv` and
   projected field `((*p).f) = rv`), `LiftRetag`, `LiftLensOperands`,
   `LiftLensRvalue` (`use`, `use_deref_field`, `copyForDeref`, scalar `BinOp`,
   `unaryOp_not`, `unaryOp_neg`, `cast_intToInt`, and tuple/ADT `aggregate`
   constructors), `LiftLensStmts`, and `LiftLensBlock` (`return_`, `goto`,
   `assert`, `switchInt`, and `drop_local`). Single-statement and whole-CFG
   lens-view state-passing theorems
   (`LiftDerefWrite.evalStmt_treeLens_putGet_and_frame`,
   `LiftDerefWrite.evalStmt_treeFieldLens_putGet_and_frame`,
   `LiftDerefRead.evalOperand_eq_treeFieldLens_readView_and_step`,
   `LiftLensStmt.evalStmt_treeLens_views_and_frame`,
   `LiftLensStmt.evalStmt_subplaceTreeLens_views_and_frame`,
   `mirWpConverges_of_sepLenses_treeLens_views`,
   `mirWpConverges_of_sepSubplaceLenses_treeLens_views`), `k`-ary
   `sepConjBindings` and `sepConjFieldBindings` entry/exit/family bridges,
   unrestricted sub-place frame locality (`AgreeOnSubplaceFootprint`,
   `SubplaceLocalSepProp`,
   `sepConj_activeTypedFieldMutBorrow_preserved_one_subplace`,
   `sepConj_activeTypedFieldMutBorrow_preserved_two_subplace`), and
   `SupportedBy` frame preservation
   (`treeMemoryPtrMutLens_writeBack_supportedBy_family`,
   `treeFieldMemoryPtrMutLens_writeBack_supportedBy`,
   `supportedBy_of_subplaceLensFramePreserved`,
   `verifyStatefulMir_of_sepLenses_supportedFrame`,
   `verifyTotalMir_of_sepLenses_supportedFrame`).
3. **Section 3 (witnesses).** `MirWpConverges`, `StatefulVerificationResult`,
   and `TotalVerificationResult` for `add_assign` (wrapping, overflow-checked,
   retagged, field-reborrow retagged at field `0`, and field-reborrow retagged
   at arbitrary `fieldIdx`), `swap_u32` (both distinct allocations and sibling
   field reborrows `&mut s.0` / `&mut s.1` on a shared struct allocation),
   `max_assign_u32`, `not_assign`, `widen_assign`, `neg_assign_i32`,
   `drop_temp_assign`, `swap_pair_u32`, `swap_pair_tuple_rvalue`
   (`aggregate_tuple`), and `step_fib_pair_adt` (`aggregate_adt`), plus concrete
   `I-10` non-vacuity witnesses including a 4-tag struct hierarchy where both
   `swap_u32(&mut s.0, &mut s.1)` and `add_assign_retag(&mut s.1, d)` execute
   while preserving the active parent `&mut s` and active sibling field borrows
   (`&mut s.0` at field `0` and `&mut s.2` at field `2`) in `R_frame`.
-/

/-! ## 0. Elementary List & Borrow-Table Helpers -/

theorem get?_eq_none_of_le {α : Type u} {xs : List α} {i : Nat}
    (h : xs.length ≤ i) : get? xs i = .none := by
  unfold get?
  exact List.getElem?_eq_none h

theorem list_set_getElem?_self {α : Type u} {xs : List α} {i : Nat} {x : α}
    (h : get? xs i = .some x) : xs.set i x = xs := by
  unfold get? at h
  induction xs generalizing i with
  | nil => nomatch h
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
    | succ i =>
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set, ih h]

theorem list_set_set_self {α : Type u} (xs : List α) (i : Nat) (x y : α) :
    (xs.set i x).set i y = xs.set i y := by
  induction xs generalizing i with
  | nil => rfl
  | cons hd tl ih =>
    cases i with
    | zero => rfl
    | succ i => simp only [List.set, ih i]

theorem list_set_comm {α : Type u} (xs : List α) {i j : Nat}
    (hNe : i ≠ j) (x y : α) :
    (xs.set i x).set j y = (xs.set j y).set i x := by
  induction xs generalizing i j with
  | nil => rfl
  | cons hd tl ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl hNe
      | succ j => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j =>
        simp only [List.set]
        exact congrArg (hd :: ·) (ih (fun h => hNe (congrArg Nat.succ h)))

theorem lookupBorrow_mem_and_tag
    {borrows : List BorrowEntry} {tag : Nat} {entry : BorrowEntry}
    (h : lookupBorrow borrows tag = .some entry) :
    entry ∈ borrows ∧ entry.tag = tag := by
  induction borrows with
  | nil => nomatch h
  | cons hd tl ih =>
    unfold lookupBorrow at h
    cases hEq : Nat.beq hd.tag tag with
    | false =>
      rw [hEq] at h
      rcases ih h with ⟨hMem, hTag⟩
      exact ⟨List.Mem.tail hd hMem, hTag⟩
    | true =>
      rw [hEq] at h
      injection h with hHd
      subst hHd
      exact ⟨List.Mem.head tl, Nat.eq_of_beq_eq_true hEq⟩

theorem isBorrowDescendantOrSelf_self
    (borrows : List BorrowEntry) (tag : Nat) :
    isBorrowDescendantOrSelf borrows tag tag = true := by
  unfold isBorrowDescendantOrSelf
  cases length borrows <;> simp [isBorrowDescendantOrSelfAux]

theorem resolveTreeBorrowWriterTag_self
    (borrows : List BorrowEntry) (entry : BorrowEntry) :
    resolveTreeBorrowWriterTag borrows entry (.some entry.tag) =
      .some entry.tag := by
  unfold resolveTreeBorrowWriterTag
  simp only [isBorrowDescendantOrSelf_self]

theorem borrowEntry_disabled_eta {entry : BorrowEntry}
    (h : entry.perm = .disabled) :
    { entry with perm := .disabled } = entry := by
  rw [← h]

/-! ## 1. From `sepConj` and `DisjointFootprints` to `IndependentLenses` -/

/--
Two mutable lenses `L₁ : MutLens Carrier α` and `L₂ : MutLens Carrier β` are
independent on states satisfying `Valid : Carrier → Prop` when:
1. Writing through either lens preserves `Valid`.
2. Writing through `L₁` leaves `L₂.readView` unchanged (and vice versa).
3. Writing through `L₁` and `L₂` commutes on all `Valid` states.
-/
structure IndependentLenses {Carrier α β : Type}
    (L₁ : MutLens Carrier α) (L₂ : MutLens Carrier β)
    (Valid : Carrier → Prop) : Prop where
  valid_writeBack_left : ∀ a c, Valid c → Valid (L₁.writeBack a c)
  valid_writeBack_right : ∀ b c, Valid c → Valid (L₂.writeBack b c)
  readView_right_of_writeBack_left :
    ∀ a c, Valid c → L₂.readView (L₁.writeBack a c) = L₂.readView c
  readView_left_of_writeBack_right :
    ∀ b c, Valid c → L₁.readView (L₂.writeBack b c) = L₁.readView c
  writeBack_comm :
    ∀ a b c, Valid c →
      L₂.writeBack b (L₁.writeBack a c) = L₁.writeBack a (L₂.writeBack b c)

/-- Symmetry of `IndependentLenses`. -/
theorem IndependentLenses.symm {Carrier α β : Type}
    {L₁ : MutLens Carrier α} {L₂ : MutLens Carrier β}
    {Valid : Carrier → Prop}
    (h : IndependentLenses L₁ L₂ Valid) :
    IndependentLenses L₂ L₁ Valid where
  valid_writeBack_left := h.valid_writeBack_right
  valid_writeBack_right := h.valid_writeBack_left
  readView_right_of_writeBack_left := h.readView_left_of_writeBack_right
  readView_left_of_writeBack_right := h.readView_right_of_writeBack_left
  writeBack_comm b a c hc := (h.writeBack_comm a b c hc).symm

/--
Product of two mutable lenses on a shared carrier `Carrier`, reading `(L₁, L₂)`
in parallel and writing back sequentially via `L₁.writeBack` then
`L₂.writeBack`.
-/
def prodMutLens {Carrier α β : Type}
    (L₁ : MutLens Carrier α) (L₂ : MutLens Carrier β) :
    MutLens Carrier (α × β) where
  readView c := (L₁.readView c, L₂.readView c)
  writeBack p c := L₂.writeBack p.2 (L₁.writeBack p.1 c)

/--
When `L₁` and `L₂` are lawful and independent on `Valid`, their product lens
`prodMutLens L₁ L₂` is a `LawfulMutLens` on `Valid`.
-/
theorem prodMutLens_lawful {Carrier α β : Type}
    {L₁ : MutLens Carrier α} {L₂ : MutLens Carrier β}
    {Valid : Carrier → Prop}
    (hL₁ : LawfulMutLens L₁ Valid)
    (hL₂ : LawfulMutLens L₂ Valid)
    (hInd : IndependentLenses L₁ L₂ Valid) :
    LawfulMutLens (prodMutLens L₁ L₂) Valid where
  valid_writeBack p c hc :=
    hL₂.valid_writeBack p.2 (L₁.writeBack p.1 c) (hL₁.valid_writeBack p.1 c hc)
  readView_writeBack p c hc := by
    rcases p with ⟨a, b⟩
    dsimp only [prodMutLens]
    have hc₁ : Valid (L₁.writeBack a c) := hL₁.valid_writeBack a c hc
    rw [hInd.readView_left_of_writeBack_right b (L₁.writeBack a c) hc₁]
    rw [hL₁.readView_writeBack a c hc]
    rw [hL₂.readView_writeBack b (L₁.writeBack a c) hc₁]
  writeBack_readView c hc := by
    dsimp only [prodMutLens]
    rw [hL₁.writeBack_readView c hc]
    exact hL₂.writeBack_readView c hc
  writeBack_writeBack p₁ p₂ c hc := by
    rcases p₁ with ⟨a₁, b₁⟩
    rcases p₂ with ⟨a₂, b₂⟩
    dsimp only [prodMutLens]
    have hc₁ : Valid (L₁.writeBack a₁ c) := hL₁.valid_writeBack a₁ c hc
    rw [← hInd.writeBack_comm a₂ b₁ (L₁.writeBack a₁ c) hc₁]
    rw [hL₁.writeBack_writeBack a₁ a₂ c hc]
    have hc₂ : Valid (L₁.writeBack a₂ c) := hL₁.valid_writeBack a₂ c hc
    exact hL₂.writeBack_writeBack b₁ b₂ (L₁.writeBack a₂ c) hc₂

/--
Inductive pairwise independence of a homogeneous list of lenses
`List (MutLens Carrier α)` on states satisfying `Valid`.
-/
inductive PairwiseIndependentLenses {Carrier α : Type}
    (Valid : Carrier → Prop) : List (MutLens Carrier α) → Prop where
  | nil : PairwiseIndependentLenses Valid []
  | cons {L : MutLens Carrier α} {rest : List (MutLens Carrier α)} :
      LawfulMutLens L Valid →
      (∀ L' ∈ rest, IndependentLenses L L' Valid) →
      PairwiseIndependentLenses Valid rest →
      PairwiseIndependentLenses Valid (L :: rest)

/--
Transferring `LawfulMutLens` from a larger validity domain `V₁` to a subdomain
`V₂` (`∀ c, V₂ c → V₁ c`) closed under `L₂.writeBack` whenever `L₂` agrees with
`L₁` on `readView` and `writeBack` over `V₂`.
-/
theorem LawfulMutLens.of_sub_agree {Carrier α : Type}
    {L₁ L₂ : MutLens Carrier α} {V₁ V₂ : Carrier → Prop}
    (hLaw : LawfulMutLens L₁ V₁)
    (hSub : ∀ c, V₂ c → V₁ c)
    (hValid : ∀ a c, V₂ c → V₂ (L₂.writeBack a c))
    (hRead : ∀ c, V₂ c → L₂.readView c = L₁.readView c)
    (hWrite : ∀ a c, V₂ c → L₂.writeBack a c = L₁.writeBack a c) :
    LawfulMutLens L₂ V₂ where
  valid_writeBack := hValid
  readView_writeBack a c hc := by
    rw [hRead _ (hValid a c hc), hWrite a c hc]
    exact hLaw.readView_writeBack a c (hSub c hc)
  writeBack_readView c hc := by
    rw [hRead c hc, hWrite _ c hc]
    exact hLaw.writeBack_readView c (hSub c hc)
  writeBack_writeBack a₁ a₂ c hc := by
    have hc₁ : V₂ (L₂.writeBack a₁ c) := hValid a₁ c hc
    rw [hWrite a₂ _ hc₁, hWrite a₁ c hc, hWrite a₂ c hc]
    exact hLaw.writeBack_writeBack a₁ a₂ c (hSub c hc)

/--
Transferring `IndependentLenses` from a larger validity domain `V₁` to a
subdomain `V₂` (`∀ c, V₂ c → V₁ c`) closed under `L₂.writeBack` and
`R₂.writeBack` whenever `(L₂, R₂)` agree with `(L₁, R₁)` on `readView` and
`writeBack` over `V₂`.
-/
theorem IndependentLenses.of_sub_agree {Carrier α β : Type}
    {L₁ L₂ : MutLens Carrier α} {R₁ R₂ : MutLens Carrier β}
    {V₁ V₂ : Carrier → Prop}
    (hInd : IndependentLenses L₁ R₁ V₁)
    (hSub : ∀ c, V₂ c → V₁ c)
    (hValidL : ∀ a c, V₂ c → V₂ (L₂.writeBack a c))
    (hValidR : ∀ b c, V₂ c → V₂ (R₂.writeBack b c))
    (hReadL : ∀ c, V₂ c → L₂.readView c = L₁.readView c)
    (hReadR : ∀ c, V₂ c → R₂.readView c = R₁.readView c)
    (hWriteL : ∀ a c, V₂ c → L₂.writeBack a c = L₁.writeBack a c)
    (hWriteR : ∀ b c, V₂ c → R₂.writeBack b c = R₁.writeBack b c) :
    IndependentLenses L₂ R₂ V₂ where
  valid_writeBack_left := hValidL
  valid_writeBack_right := hValidR
  readView_right_of_writeBack_left a c hc := by
    rw [hReadR _ (hValidL a c hc), hReadR c hc, hWriteL a c hc]
    exact hInd.readView_right_of_writeBack_left a c (hSub c hc)
  readView_left_of_writeBack_right b c hc := by
    rw [hReadL _ (hValidR b c hc), hReadL c hc, hWriteR b c hc]
    exact hInd.readView_left_of_writeBack_right b c (hSub c hc)
  writeBack_comm a b c hc := by
    have hcL : V₂ (L₂.writeBack a c) := hValidL a c hc
    have hcR : V₂ (R₂.writeBack b c) := hValidR b c hc
    rw [hWriteR b _ hcL, hWriteL a c hc, hWriteL a _ hcR, hWriteR b c hc]
    exact hInd.writeBack_comm a b c (hSub c hc)

/--
General commutativity of `updateBorrowPerm` on distinct target allocations
`loc₁ ≠ loc₂` for arbitrary writer tags `w₁, w₂`.
-/
theorem updateBorrowPerm_comm
    (entry : BorrowEntry) {loc₁ loc₂ : Local} (hNe : loc₁ ≠ loc₂)
    (w₁ w₂ : Option Nat) :
    updateBorrowPerm (updateBorrowPerm entry loc₁ w₁) loc₂ w₂ =
      updateBorrowPerm (updateBorrowPerm entry loc₂ w₂) loc₁ w₁ := by
  cases entry; rename_i tag targetLocal targetProjection perm rangeOffset rangeLen protector parentTag
  unfold updateBorrowPerm
  cases h₁ : Nat.beq targetLocal loc₁ <;> dsimp only
  · cases h₂ : Nat.beq targetLocal loc₂ <;> dsimp only
    · simp only [h₁]
    · cases w₂ <;> cases w₁ <;> dsimp only
      · cases perm <;> simp only [h₁]
      · rename_i tag1; cases hTag1 : Nat.beq tag tag1 <;> cases perm <;> simp only [h₁]
      · rename_i tag2; cases hTag2 : Nat.beq tag tag2 <;> dsimp only <;> cases perm <;> simp only [h₁]
      · rename_i tag2 tag1; cases hTag1 : Nat.beq tag tag1 <;> cases hTag2 : Nat.beq tag tag2 <;> dsimp only <;> cases perm <;> simp only [h₁]
  · have hEq₁ : targetLocal = loc₁ := Nat.eq_of_beq_eq_true h₁
    have h₂ : Nat.beq targetLocal loc₂ = false := by
      cases h : Nat.beq targetLocal loc₂
      · rfl
      · exact False.elim (hNe (hEq₁.symm.trans (Nat.eq_of_beq_eq_true h)))
    cases w₂ <;> cases w₁ <;> dsimp only
    · cases perm <;> simp only [h₁, h₂]
    · rename_i tag1; cases hTag1 : Nat.beq tag tag1 <;> cases perm <;> simp only [h₁, h₂, hTag1]
    · rename_i tag2; cases hTag2 : Nat.beq tag tag2 <;> cases perm <;> simp only [h₁, h₂]
    · rename_i tag2 tag1; cases hTag1 : Nat.beq tag tag1 <;> cases hTag2 : Nat.beq tag tag2 <;> cases perm <;> simp only [h₁, h₂, hTag1]
/--
General commutativity of `invalidateConflictingBorrows` on distinct target
allocations `loc₁ ≠ loc₂`.
-/
theorem invalidateConflictingBorrows_comm
    (borrows : List BorrowEntry) {loc₁ loc₂ : Local} (hNe : loc₁ ≠ loc₂)
    (w₁ w₂ : Option Nat) :
    invalidateConflictingBorrows
      (invalidateConflictingBorrows borrows loc₁ w₁) loc₂ w₂ =
    invalidateConflictingBorrows
      (invalidateConflictingBorrows borrows loc₂ w₂) loc₁ w₁ := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    simp only [invalidateConflictingBorrows_cons,
      updateBorrowPerm_comm hd hNe w₁ w₂, ih]

/--
Exclusive active Tree Borrows invariant for a root mutable borrow `rp` in `m`:
1. `rp.offset = 0` (root of allocation `rp.allocId`).
2. `lookupBorrow m.borrows rp.tag` resolves to an `.active` whole-allocation
   entry targeting `rp.allocId`.
3. Any entry in `m.borrows` targeting `rp.allocId` is either this active borrow
   on `rp.tag` or is already `.disabled`.
-/
structure ExclusiveActiveBorrow (rp : RawPtrVal) (m : Memory) : Prop where
  offset_zero : rp.offset = 0
  lookup_active :
    ∃ entry,
      lookupBorrow m.borrows rp.tag = .some entry ∧
      entry.targetLocal = rp.allocId ∧
      entry.targetProjection = [] ∧
      entry.perm = .active ∧
      entry.rangeOffset = 0 ∧
      entry.rangeLen = 0
  exclusive_on_alloc :
    ∀ b ∈ m.borrows,
      b.targetLocal = rp.allocId →
        (b.tag = rp.tag ∧
          b.perm = .active ∧
          b.targetProjection = [] ∧
          b.rangeOffset = 0 ∧
          b.rangeLen = 0) ∨
        b.perm = .disabled

theorem ExclusiveActiveBorrow.of_borrows_eq
    {rp : RawPtrVal} {m₁ m₂ : Memory}
    (h : ExclusiveActiveBorrow rp m₁)
    (hBorrows : m₂.borrows = m₁.borrows) :
    ExclusiveActiveBorrow rp m₂ where
  offset_zero := h.offset_zero
  lookup_active := by rw [hBorrows]; exact h.lookup_active
  exclusive_on_alloc := by rw [hBorrows]; exact h.exclusive_on_alloc

theorem invalidateConflictingBorrows_eq_self_of_exclusive
    {borrows : List BorrowEntry} {allocId tag : Nat}
    (hExcl :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (b.tag = tag ∧
            b.perm = .active ∧
            b.targetProjection = [] ∧
            b.rangeOffset = 0 ∧
            b.rangeLen = 0) ∨
          b.perm = .disabled) :
    invalidateConflictingBorrows borrows allocId (.some tag) = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail :
        invalidateConflictingBorrows tl allocId (.some tag) = tl :=
      ih (fun b hb => hExcl b (List.Mem.tail hd hb))
    simp only [invalidateConflictingBorrows_cons, hTail]
    unfold updateBorrowPerm
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hExcl hd (List.Mem.head tl) hTargetEq with
        ⟨hTag, hPerm, _, _, _⟩ | hDis
      · subst hTag
        simp [hPerm]
      · cases hTag : hd.tag.beq tag with
        | true => dsimp only; rw [hTag]; simp [hDis]
        | false => dsimp only; rw [hTag]; exact congrArg (· :: tl) (borrowEntry_disabled_eta hDis)

theorem invalidateConflictingBorrowsAtProj_eq_self_of_exclusive
    {borrows : List BorrowEntry} {allocId tag : Nat}
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hExcl :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (b.tag = tag ∧ b.perm = .active) ∨ b.perm = .disabled) :
    invalidateConflictingBorrowsAtProj
      borrows allocId (.some tag) writeProj writeRangeOff writeRangeLen =
      borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail :
        invalidateConflictingBorrowsAtProj
          tl allocId (.some tag) writeProj writeRangeOff writeRangeLen = tl :=
      ih (fun b hb => hExcl b (List.Mem.tail hd hb))
    simp only [invalidateConflictingBorrowsAtProj_cons, hTail]
    unfold updateBorrowPermAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hExcl hd (List.Mem.head tl) hTargetEq with
        ⟨hTag, hPerm⟩ | hDis
      · subst hTag
        simp [hPerm]
      · cases hTag : hd.tag.beq tag with
        | true => dsimp only; rw [hTag]; simp [hDis]
        | false =>
          dsimp only
          rw [hTag]
          dsimp only
          cases borrowEntryOverlapsWrite hd writeProj writeRangeOff writeRangeLen with
          | false => rfl
          | true =>
            dsimp only
            exact congrArg (· :: tl) (borrowEntry_disabled_eta hDis)

theorem stepTreeBorrowAccess_write_eq_some_self_of_exclusive
    {rp : RawPtrVal} {m : Memory}
    (hExcl : ExclusiveActiveBorrow rp m) :
    stepTreeBorrowAccess? m rp true = .some m := by
  rcases hExcl.lookup_active with ⟨entry, hLook, hTarget, _, hPerm, _, _⟩
  unfold stepTreeBorrowAccess?
  rw [hLook]
  dsimp only
  rw [hPerm, hTarget]
  simp only [
    invalidateConflictingBorrows_eq_self_of_exclusive hExcl.exclusive_on_alloc]

/-
The `updateMemoryLocals` helper lemmas below case-split only on the
`m.callStack` field (the one field `updateMemoryLocals` inspects) and rely on
structure eta for everything else, so they never destructure the 12-field
`Memory` record and keep holding if `Memory` gains fields.
-/

theorem memoryLocals_updateMemoryLocals (m : Memory) (locals' : List LocalValue) :
    memoryLocals (updateMemoryLocals m locals') = locals' :=
  Anneal.FunctionalTranslation.memoryLocals_updateMemoryLocals m locals'

theorem updateMemoryLocals_borrows (m : Memory) (locals' : List LocalValue) :
    (updateMemoryLocals m locals').borrows = m.borrows := by
  unfold updateMemoryLocals
  cases m.callStack <;> rfl

theorem updateMemoryLocals_self (m : Memory) :
    updateMemoryLocals m (memoryLocals m) = m := by
  unfold updateMemoryLocals
  split
  · rename_i head tail hStack
    have hLoc : memoryLocals m = head.frame.locals := by
      unfold memoryLocals
      rw [hStack]
    rw [hLoc]
    show { m with callStack := head :: tail } = m
    rw [← hStack]
  · rename_i hStack
    have hLoc : memoryLocals m = m.callerLocals := by
      unfold memoryLocals
      rw [hStack]
    rw [hLoc]

theorem updateMemoryLocals_updateMemoryLocals
    (m : Memory) (l₁ l₂ : List LocalValue) :
    updateMemoryLocals (updateMemoryLocals m l₁) l₂ =
      updateMemoryLocals m l₂ := by
  unfold updateMemoryLocals
  cases m.callStack <;> rfl

/--
`memoryPtrMutLens rp codec` reads back `a` from any memory whose pointee slot
holds `codec.encode a`.
-/
theorem memoryPtrMutLens_readView_of_readAllocAt
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {m : Memory}
    (h_read : readAllocAt? (memoryLocals m) rp = some (codec.encode a)) :
    (memoryPtrMutLens rp codec).readView m = a := by
  unfold memoryPtrMutLens
  dsimp only
  rw [h_read]
  dsimp only
  rw [codec.decode_encode]
  rfl

/--
Under `ExclusiveActiveBorrow rp m` and an initialized pointee slot,
`(memoryPtrMutLens rp codec).writeBack a m` leaves `m.borrows` unchanged and
directly updates `memoryLocals m` at `rp.allocId` to `.init (codec.encode a)`.
-/
theorem memoryPtrMutLens_writeBack_eq_of_exclusive
    {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α)
    {m : Memory} {v₀ : Value}
    (hPts : readAllocAt? (memoryLocals m) rp = some v₀)
    (hExcl : ExclusiveActiveBorrow rp m) :
    (memoryPtrMutLens rp codec).writeBack a m =
      updateMemoryLocals
        m
        ((memoryLocals m).set rp.allocId (.init (codec.encode a))) := by
  unfold memoryPtrMutLens
  dsimp only
  rw [stepTreeBorrowAccess_write_eq_some_self_of_exclusive hExcl]
  dsimp only [Option.getD]
  unfold readAllocAt? at hPts
  rw [hExcl.offset_zero] at hPts
  unfold writeAllocAt?
  rw [hExcl.offset_zero]
  cases hGet : get? (memoryLocals m) rp.allocId with
  | none => rw [hGet] at hPts; nomatch hPts
  | some slot =>
    rw [hGet] at hPts
    cases slot with
    | dead => nomatch hPts
    | uninit => nomatch hPts
    | init _ =>
      have hLt : rp.allocId < (memoryLocals m).length :=
        (List.getElem?_eq_some_iff.mp hGet).1
      unfold set?
      simp [hLt]

/--
Borrow-agnostic mutable lens into caller/frame slot `rp.allocId` at offset `0`:
reads via `memoryPtrMutLens` and writes `.init (codec.encode a)` directly into
`memoryLocals m` without modifying `m.borrows`. Both `memoryPtrMutLens` (under
`ExclusiveActiveBorrow`) and `treeMemoryPtrMutLens` (under
`TreeExclusiveBorrow`) reduce to `rawPtrMutLens` on their respective validity
domains.
-/
def rawPtrMutLens {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) :
    MutLens Memory α where
  readView m := (memoryPtrMutLens rp codec).readView m
  writeBack a m :=
    updateMemoryLocals
      m
      ((memoryLocals m).set rp.allocId (.init (codec.encode a)))

/--
Domain validity predicate for `rawPtrMutLens rp codec`: the pointee slot holds
an encoded value `codec.encode a` and `rp` sits at offset `0`.
-/
structure ValidRawPtrLens {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) (m : Memory) : Prop where
  has_typed_pointee :
    ∃ a : α, readAllocAt? (memoryLocals m) rp = some (codec.encode a)
  offset_zero : rp.offset = 0

theorem pointsTo_updateMemoryLocals_set_self {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {v₀ : Value} {m : Memory}
    (a : α) (hOff : rp.offset = 0)
    (hPts : readAllocAt? (memoryLocals m) rp = some v₀) :
    readAllocAt?
      (memoryLocals
        (updateMemoryLocals
          m
          ((memoryLocals m).set rp.allocId (.init (codec.encode a)))))
      rp = some (codec.encode a) := by
  unfold readAllocAt? at hPts ⊢
  rw [memoryLocals_updateMemoryLocals, hOff]
  rw [hOff] at hPts
  cases hGet : get? (memoryLocals m) rp.allocId with
  | none => rw [hGet] at hPts; nomatch hPts
  | some slot =>
    have hLt : rp.allocId < (memoryLocals m).length :=
      (List.getElem?_eq_some_iff.mp hGet).1
    unfold get?
    rw [List.getElem?_set_self hLt]

private theorem pointsTo_updateMemoryLocals_set_ne
    {rp₁ rp₂ : RawPtrVal} {v₂ newVal : Value} {m : Memory}
    (hNe : rp₁.allocId ≠ rp₂.allocId)
    (hOff₂ : rp₂.offset = 0)
    (hPts₂ : readAllocAt? (memoryLocals m) rp₂ = some v₂) :
    readAllocAt?
      (memoryLocals
        (updateMemoryLocals
          m
          ((memoryLocals m).set rp₁.allocId (.init newVal))))
      rp₂ = some v₂ := by
  unfold readAllocAt? at hPts₂ ⊢
  rw [memoryLocals_updateMemoryLocals, hOff₂]
  rw [hOff₂] at hPts₂
  unfold get? at hPts₂ ⊢
  rw [List.getElem?_set_ne hNe]
  exact hPts₂

/--
`rawPtrMutLens rp codec` is a `LawfulMutLens` on `ValidRawPtrLens rp codec`.
-/
theorem rawPtrMutLens_lawful {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) :
    LawfulMutLens (rawPtrMutLens rp codec) (ValidRawPtrLens rp codec) where
  valid_writeBack a _ hm := by
    rcases hm with ⟨⟨_, hPts⟩, hOff⟩
    exact ⟨⟨a, pointsTo_updateMemoryLocals_set_self a hOff hPts⟩, hOff⟩
  readView_writeBack a _ hm := by
    rcases hm with ⟨⟨_, hPts⟩, hOff⟩
    exact memoryPtrMutLens_readView_of_readAllocAt
      (pointsTo_updateMemoryLocals_set_self a hOff hPts)
  writeBack_readView m hm := by
    rcases hm with ⟨⟨a₀, hPts⟩, hOff⟩
    have hRead : (rawPtrMutLens rp codec).readView m = a₀ :=
      memoryPtrMutLens_readView_of_readAllocAt hPts
    rw [hRead]
    dsimp only [rawPtrMutLens]
    unfold readAllocAt? at hPts
    rw [hOff] at hPts
    cases hGet : get? (memoryLocals m) rp.allocId with
    | none => rw [hGet] at hPts; nomatch hPts
    | some slot =>
      rw [hGet] at hPts
      cases slot with
      | dead => nomatch hPts
      | uninit => nomatch hPts
      | init v =>
        injection hPts with hV
        subst hV
        rw [list_set_getElem?_self hGet, updateMemoryLocals_self]
  writeBack_writeBack _ _ _ _ := by
    dsimp only [rawPtrMutLens]
    rw [memoryLocals_updateMemoryLocals, list_set_set_self,
      updateMemoryLocals_updateMemoryLocals]

/--
Domain validity predicate for a pair of `rawPtrMutLens` instances on distinct
allocations.
-/
structure ValidRawPtrLensPair {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β)
    (m : Memory) : Prop where
  valid_left : ValidRawPtrLens rp₁ codec₁ m
  valid_right : ValidRawPtrLens rp₂ codec₂ m
  ne_alloc : rp₁.allocId ≠ rp₂.allocId

/--
Two `rawPtrMutLens` instances on distinct allocations satisfy
`IndependentLenses` on `ValidRawPtrLensPair rp₁ rp₂ codec₁ codec₂`.
-/
theorem rawPtrMutLens_independent_of_ne_alloc {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    IndependentLenses
      (rawPtrMutLens rp₁ codec₁)
      (rawPtrMutLens rp₂ codec₂)
      (ValidRawPtrLensPair rp₁ rp₂ codec₁ codec₂) where
  valid_writeBack_left a m hm := by
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hOff₂⟩
    exact ⟨(rawPtrMutLens_lawful rp₁ codec₁).valid_writeBack a m hm.valid_left,
      ⟨⟨b₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc hOff₂ hPts₂⟩, hOff₂⟩,
      hm.ne_alloc⟩
  valid_writeBack_right b m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hOff₁⟩
    exact ⟨
      ⟨⟨a₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm hOff₁ hPts₁⟩,
        hOff₁⟩,
      (rawPtrMutLens_lawful rp₂ codec₂).valid_writeBack b m hm.valid_right,
      hm.ne_alloc⟩
  readView_right_of_writeBack_left a _ hm := by
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hOff₂⟩
    exact (memoryPtrMutLens_readView_of_readAllocAt
      (pointsTo_updateMemoryLocals_set_ne hm.ne_alloc hOff₂ hPts₂)).trans
      (memoryPtrMutLens_readView_of_readAllocAt hPts₂).symm
  readView_left_of_writeBack_right b _ hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hOff₁⟩
    exact (memoryPtrMutLens_readView_of_readAllocAt
      (pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm hOff₁ hPts₁)).trans
      (memoryPtrMutLens_readView_of_readAllocAt hPts₁).symm
  writeBack_comm _ _ m hm := by
    dsimp only [rawPtrMutLens]
    rw [memoryLocals_updateMemoryLocals, memoryLocals_updateMemoryLocals,
      updateMemoryLocals_updateMemoryLocals,
      updateMemoryLocals_updateMemoryLocals,
      list_set_comm (memoryLocals m) hm.ne_alloc]

/--
Domain validity predicate for a single separation-logic-backed mutable borrow
lens `memoryPtrMutLens rp codec`.
-/
structure ValidMutBorrowLens {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) (m : Memory) : Prop where
  has_typed_pointee : ∃ a : α, readAllocAt? (memoryLocals m) rp = some (codec.encode a)
  exclusive : ExclusiveActiveBorrow rp m

theorem ValidMutBorrowLens.toRaw {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {m : Memory}
    (hm : ValidMutBorrowLens rp codec m) :
    ValidRawPtrLens rp codec m :=
  ⟨hm.has_typed_pointee, hm.exclusive.offset_zero⟩

theorem ValidMutBorrowLens.writeBack {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {m : Memory}
    (a : α) (hm : ValidMutBorrowLens rp codec m) :
    ValidMutBorrowLens rp codec ((memoryPtrMutLens rp codec).writeBack a m) := by
  rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
  rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a hPts hExcl]
  exact ⟨⟨a, pointsTo_updateMemoryLocals_set_self a hExcl.offset_zero hPts⟩,
    ExclusiveActiveBorrow.of_borrows_eq hExcl (updateMemoryLocals_borrows _ _)⟩

/--
`memoryPtrMutLens rp codec` is a `LawfulMutLens` on
`ValidMutBorrowLens rp codec`, transferred from `rawPtrMutLens_lawful` via
`LawfulMutLens.of_sub_agree`.
-/
theorem memoryPtrMutLens_lawful {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) :
    LawfulMutLens (memoryPtrMutLens rp codec) (ValidMutBorrowLens rp codec) :=
  LawfulMutLens.of_sub_agree (rawPtrMutLens_lawful rp codec)
    (fun _ hm => hm.toRaw)
    (fun a _ hm => hm.writeBack a)
    (fun _ _ => rfl)
    (fun a _ ⟨⟨_, hPts⟩, hExcl⟩ =>
      memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a hPts hExcl)

/--
Domain validity predicate for a pair of separation-logic-backed mutable borrow
lenses `memoryPtrMutLens rp₁ codec₁` and `memoryPtrMutLens rp₂ codec₂`.
-/
structure ValidMutBorrowLensPair {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β)
    (m : Memory) : Prop where
  valid_left : ValidMutBorrowLens rp₁ codec₁ m
  valid_right : ValidMutBorrowLens rp₂ codec₂ m
  ne_alloc : rp₁.allocId ≠ rp₂.allocId

/--
Two `memoryPtrMutLens` instances on distinct allocations
(`rp₁.allocId ≠ rp₂.allocId`) satisfy `IndependentLenses` on
`ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂`, transferred from
`rawPtrMutLens_independent_of_ne_alloc` via `IndependentLenses.of_sub_agree`.
-/
theorem memoryPtrMutLens_independent_of_ne_alloc {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    IndependentLenses
      (memoryPtrMutLens rp₁ codec₁)
      (memoryPtrMutLens rp₂ codec₂)
      (ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) :=
  (rawPtrMutLens_independent_of_ne_alloc rp₁ rp₂ codec₁ codec₂).of_sub_agree
    (fun _ hm => ⟨hm.valid_left.toRaw, hm.valid_right.toRaw, hm.ne_alloc⟩)
    (fun a m hm => by
      rcases hm.valid_left with ⟨⟨_, hPts₁⟩, hExcl₁⟩
      rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
      refine ⟨hm.valid_left.writeBack a, ?_, hm.ne_alloc⟩
      rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁ hExcl₁]
      exact ⟨
        ⟨b₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc hExcl₂.offset_zero hPts₂⟩,
        ExclusiveActiveBorrow.of_borrows_eq hExcl₂
          (updateMemoryLocals_borrows _ _)⟩)
    (fun b m hm => by
      rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
      rcases hm.valid_right with ⟨⟨_, hPts₂⟩, hExcl₂⟩
      refine ⟨?_, hm.valid_right.writeBack b, hm.ne_alloc⟩
      rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂ hExcl₂]
      exact ⟨
        ⟨a₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
          hExcl₁.offset_zero hPts₁⟩,
        ExclusiveActiveBorrow.of_borrows_eq hExcl₁
          (updateMemoryLocals_borrows _ _)⟩)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun a _ hm => by
      rcases hm.valid_left with ⟨⟨_, hPts₁⟩, hExcl₁⟩
      exact memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁ hExcl₁)
    (fun b _ hm => by
      rcases hm.valid_right with ⟨⟨_, hPts₂⟩, hExcl₂⟩
      exact memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂ hExcl₂)

/-! ### Sub-Allocation Field Lenses on Aggregate Slots (`rawFieldMutLens`) -/

/--
Read field `fieldIdx` of a variant-`0` aggregate (`Value.aggregate 0 elems`) at
slot `allocId` in `locals`.
-/
def readFieldAt?
    (locals : List LocalValue) (allocId : Local) (fieldIdx : FieldIdx) :
    Option Value :=
  match get? locals allocId with
  | some (.init (.aggregate .zero elems)) => get? elems fieldIdx
  | _ => none

/--
Write `v` into field `fieldIdx` of a variant-`0` aggregate at slot `allocId` in
`locals`, leaving `locals` unchanged when `allocId` does not hold a variant-`0`
aggregate.
-/
def writeFieldAt?
    (locals : List LocalValue) (allocId : Local) (fieldIdx : FieldIdx)
    (v : Value) : List LocalValue :=
  match get? locals allocId with
  | some (.init (.aggregate .zero elems)) =>
    locals.set allocId (.init (.aggregate 0 (elems.set fieldIdx v)))
  | _ => locals

/--
Borrow-agnostic mutable lens into field `fieldIdx` of a variant-`0` aggregate at
slot `allocId` in `memoryLocals m`.
-/
def rawFieldMutLens {α : Type}
    (allocId : Local) (fieldIdx : FieldIdx) (codec : ValueCodec α) :
    MutLens Memory α where
  readView m :=
    match readFieldAt? (memoryLocals m) allocId fieldIdx with
    | some v => (codec.decode v).getD codec.default
    | none => codec.default
  writeBack a m :=
    updateMemoryLocals m
      (writeFieldAt? (memoryLocals m) allocId fieldIdx (codec.encode a))

/--
Domain validity predicate for `rawFieldMutLens allocId fieldIdx codec`: slot
`allocId` holds a variant-`0` aggregate whose field `fieldIdx` encodes a typed
value `codec.encode a`.
-/
structure ValidRawFieldLens {α : Type}
    (allocId : Local) (fieldIdx : FieldIdx) (codec : ValueCodec α)
    (m : Memory) : Prop where
  has_typed_field :
    ∃ a : α,
      readFieldAt? (memoryLocals m) allocId fieldIdx = some (codec.encode a)

theorem rawFieldMutLens_readView_of_readFieldAt {α : Type}
    {allocId : Local} {fieldIdx : FieldIdx} {codec : ValueCodec α}
    {a : α} {m : Memory}
    (hRead :
      readFieldAt? (memoryLocals m) allocId fieldIdx = some (codec.encode a)) :
    (rawFieldMutLens allocId fieldIdx codec).readView m = a := by
  unfold rawFieldMutLens
  dsimp only
  rw [hRead]
  dsimp only
  rw [codec.decode_encode]
  rfl

theorem readFieldAt_updateMemoryLocals_writeFieldAt_self {α : Type}
    {allocId : Local} {fieldIdx : FieldIdx} {codec : ValueCodec α}
    {v₀ : Value} {m : Memory} (a : α)
    (hField : readFieldAt? (memoryLocals m) allocId fieldIdx = some v₀) :
    readFieldAt?
      (memoryLocals
        (updateMemoryLocals m
          (writeFieldAt? (memoryLocals m) allocId fieldIdx (codec.encode a))))
      allocId fieldIdx = some (codec.encode a) := by
  unfold readFieldAt? at hField ⊢
  rw [memoryLocals_updateMemoryLocals]
  unfold writeFieldAt?
  cases hGet : get? (memoryLocals m) allocId with
  | none => rw [hGet] at hField; nomatch hField
  | some slot =>
    rw [hGet] at hField
    cases slot with
    | dead => nomatch hField
    | uninit => nomatch hField
    | init val =>
      cases val with
      | unit => nomatch hField
      | scalar _ => nomatch hField
      | ptr _ _ => nomatch hField
      | aggregate varIdx elems =>
        cases varIdx with
        | succ _ => nomatch hField
        | zero =>
          have hLtAlloc : allocId < (memoryLocals m).length :=
            (List.getElem?_eq_some_iff.mp hGet).1
          have hLtField : fieldIdx < elems.length :=
            (List.getElem?_eq_some_iff.mp hField).1
          unfold get?
          rw [List.getElem?_set_self hLtAlloc]
          dsimp only
          exact List.getElem?_set_self hLtField

theorem readFieldAt_updateMemoryLocals_writeFieldAt_ne
    {allocId : Local} {fieldIdx₁ fieldIdx₂ : FieldIdx}
    {v₁ v₂ newVal : Value} {m : Memory}
    (hNe : fieldIdx₁ ≠ fieldIdx₂)
    (hField₁ : readFieldAt? (memoryLocals m) allocId fieldIdx₁ = some v₁)
    (hField₂ : readFieldAt? (memoryLocals m) allocId fieldIdx₂ = some v₂) :
    readFieldAt?
      (memoryLocals
        (updateMemoryLocals m
          (writeFieldAt? (memoryLocals m) allocId fieldIdx₁ newVal)))
      allocId fieldIdx₂ = some v₂ := by
  unfold readFieldAt? at hField₁ hField₂ ⊢
  rw [memoryLocals_updateMemoryLocals]
  unfold writeFieldAt?
  cases hGet : get? (memoryLocals m) allocId with
  | none => rw [hGet] at hField₁; nomatch hField₁
  | some slot =>
    rw [hGet] at hField₁ hField₂
    cases slot with
    | dead => nomatch hField₁
    | uninit => nomatch hField₁
    | init val =>
      cases val with
      | unit => nomatch hField₁
      | scalar _ => nomatch hField₁
      | ptr _ _ => nomatch hField₁
      | aggregate varIdx elems =>
        cases varIdx with
        | succ _ => nomatch hField₁
        | zero =>
          have hLtAlloc : allocId < (memoryLocals m).length :=
            (List.getElem?_eq_some_iff.mp hGet).1
          unfold get? at hField₂ ⊢
          rw [List.getElem?_set_self hLtAlloc]
          dsimp only
          rw [List.getElem?_set_ne hNe]
          exact hField₂

/--
`rawFieldMutLens allocId fieldIdx codec` is a `LawfulMutLens` on
`ValidRawFieldLens allocId fieldIdx codec`.
-/
theorem rawFieldMutLens_lawful {α : Type}
    (allocId : Local) (fieldIdx : FieldIdx) (codec : ValueCodec α) :
    LawfulMutLens (rawFieldMutLens allocId fieldIdx codec)
      (ValidRawFieldLens allocId fieldIdx codec) where
  valid_writeBack a _ hm := by
    rcases hm with ⟨⟨_, hField⟩⟩
    exact ⟨⟨a, readFieldAt_updateMemoryLocals_writeFieldAt_self a hField⟩⟩
  readView_writeBack a _ hm := by
    rcases hm with ⟨⟨_, hField⟩⟩
    exact rawFieldMutLens_readView_of_readFieldAt
      (readFieldAt_updateMemoryLocals_writeFieldAt_self a hField)
  writeBack_readView m hm := by
    rcases hm with ⟨⟨a₀, hField⟩⟩
    have hRead : (rawFieldMutLens allocId fieldIdx codec).readView m = a₀ :=
      rawFieldMutLens_readView_of_readFieldAt hField
    rw [hRead]
    dsimp only [rawFieldMutLens]
    unfold readFieldAt? at hField
    unfold writeFieldAt?
    cases hGet : get? (memoryLocals m) allocId with
    | none => rw [hGet] at hField; nomatch hField
    | some slot =>
      rw [hGet] at hField
      cases slot with
      | dead => nomatch hField
      | uninit => nomatch hField
      | init val =>
        cases val with
        | unit => nomatch hField
        | scalar _ => nomatch hField
        | ptr _ _ => nomatch hField
        | aggregate varIdx elems =>
          cases varIdx with
          | succ _ => nomatch hField
          | zero =>
            dsimp only at hField ⊢
            rw [list_set_getElem?_self hField,
              list_set_getElem?_self hGet,
              updateMemoryLocals_self]
  writeBack_writeBack _ _ m hm := by
    rcases hm with ⟨⟨_, hField⟩⟩
    dsimp only [rawFieldMutLens]
    rw [memoryLocals_updateMemoryLocals, updateMemoryLocals_updateMemoryLocals]
    unfold readFieldAt? at hField
    unfold writeFieldAt?
    cases hGet : get? (memoryLocals m) allocId with
    | none => rw [hGet] at hField; nomatch hField
    | some slot =>
      rw [hGet] at hField
      cases slot with
      | dead => nomatch hField
      | uninit => nomatch hField
      | init val =>
        cases val with
        | unit => nomatch hField
        | scalar _ => nomatch hField
        | ptr _ _ => nomatch hField
        | aggregate varIdx elems =>
          cases varIdx with
          | succ _ => nomatch hField
          | zero =>
            have hLtAlloc : allocId < (memoryLocals m).length :=
              (List.getElem?_eq_some_iff.mp hGet).1
            unfold get?
            rw [List.getElem?_set_self hLtAlloc]
            dsimp only
            rw [list_set_set_self, list_set_set_self]

/--
Domain validity predicate for a pair of `rawFieldMutLens` instances targeting
distinct fields `fieldIdx₁ ≠ fieldIdx₂` of the same aggregate slot `allocId`.
-/
structure ValidRawFieldLensPair {α β : Type}
    (allocId : Local) (fieldIdx₁ fieldIdx₂ : FieldIdx)
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) (m : Memory) : Prop where
  valid_left : ValidRawFieldLens allocId fieldIdx₁ codec₁ m
  valid_right : ValidRawFieldLens allocId fieldIdx₂ codec₂ m
  ne_field : fieldIdx₁ ≠ fieldIdx₂

/--
Two `rawFieldMutLens` instances on distinct fields (`fieldIdx₁ ≠ fieldIdx₂`) of
the same aggregate allocation `allocId` satisfy `IndependentLenses` on
`ValidRawFieldLensPair allocId fieldIdx₁ fieldIdx₂ codec₁ codec₂`.
-/
theorem rawFieldMutLens_independent_of_ne_field {α β : Type}
    (allocId : Local) (fieldIdx₁ fieldIdx₂ : FieldIdx)
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    IndependentLenses
      (rawFieldMutLens allocId fieldIdx₁ codec₁)
      (rawFieldMutLens allocId fieldIdx₂ codec₂)
      (ValidRawFieldLensPair allocId fieldIdx₁ fieldIdx₂ codec₁ codec₂) where
  valid_writeBack_left a m hm := by
    rcases hm.valid_left with ⟨⟨_, hField₁⟩⟩
    rcases hm.valid_right with ⟨⟨b₀, hField₂⟩⟩
    exact ⟨
      (rawFieldMutLens_lawful allocId fieldIdx₁ codec₁).valid_writeBack a m
        ⟨⟨_, hField₁⟩⟩,
      ⟨⟨b₀, readFieldAt_updateMemoryLocals_writeFieldAt_ne hm.ne_field
        hField₁ hField₂⟩⟩,
      hm.ne_field⟩
  valid_writeBack_right b m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hField₁⟩⟩
    rcases hm.valid_right with ⟨⟨_, hField₂⟩⟩
    exact ⟨
      ⟨⟨a₀, readFieldAt_updateMemoryLocals_writeFieldAt_ne hm.ne_field.symm
        hField₂ hField₁⟩⟩,
      (rawFieldMutLens_lawful allocId fieldIdx₂ codec₂).valid_writeBack b m
        ⟨⟨_, hField₂⟩⟩,
      hm.ne_field⟩
  readView_right_of_writeBack_left a _ hm := by
    rcases hm.valid_left with ⟨⟨_, hField₁⟩⟩
    rcases hm.valid_right with ⟨⟨b₀, hField₂⟩⟩
    exact (rawFieldMutLens_readView_of_readFieldAt
      (readFieldAt_updateMemoryLocals_writeFieldAt_ne hm.ne_field
        hField₁ hField₂)).trans
      (rawFieldMutLens_readView_of_readFieldAt hField₂).symm
  readView_left_of_writeBack_right b _ hm := by
    rcases hm.valid_left with ⟨⟨a₀, hField₁⟩⟩
    rcases hm.valid_right with ⟨⟨_, hField₂⟩⟩
    exact (rawFieldMutLens_readView_of_readFieldAt
      (readFieldAt_updateMemoryLocals_writeFieldAt_ne hm.ne_field.symm
        hField₂ hField₁)).trans
      (rawFieldMutLens_readView_of_readFieldAt hField₁).symm
  writeBack_comm a b m hm := by
    rcases hm.valid_left with ⟨⟨_, hField₁⟩⟩
    dsimp only [rawFieldMutLens]
    rw [memoryLocals_updateMemoryLocals, memoryLocals_updateMemoryLocals,
      updateMemoryLocals_updateMemoryLocals,
      updateMemoryLocals_updateMemoryLocals]
    unfold readFieldAt? at hField₁
    unfold writeFieldAt?
    cases hGet : get? (memoryLocals m) allocId with
    | none => rw [hGet] at hField₁; nomatch hField₁
    | some slot =>
      rw [hGet] at hField₁
      cases slot with
      | dead => nomatch hField₁
      | uninit => nomatch hField₁
      | init val =>
        cases val with
        | unit => nomatch hField₁
        | scalar _ => nomatch hField₁
        | ptr _ _ => nomatch hField₁
        | aggregate varIdx elems =>
          cases varIdx with
          | succ _ => nomatch hField₁
          | zero =>
            have hLtAlloc : allocId < (memoryLocals m).length :=
              (List.getElem?_eq_some_iff.mp hGet).1
            unfold get?
            rw [List.getElem?_set_self hLtAlloc, List.getElem?_set_self hLtAlloc]
            dsimp only
            rw [list_set_set_self, list_set_set_self,
              list_set_comm elems hm.ne_field]

theorem readAllocAt_succ_eq_readFieldAt
    (locals : List LocalValue) (allocId k tag : Nat) :
    readAllocAt? locals { allocId := allocId, offset := k + 1, tag := tag } =
      readFieldAt? locals allocId (k + 1) := by
  unfold readAllocAt? readFieldAt?
  cases get? locals allocId with
  | none => rfl
  | some slot =>
    cases slot with
    | dead => rfl
    | uninit => rfl
    | init v =>
      cases v with
      | unit => rfl
      | scalar _ => rfl
      | ptr _ _ => rfl
      | aggregate varIdx _ =>
        cases varIdx <;> rfl

theorem readFieldAt_writeFieldAt_ne_eq
    (locals : List LocalValue) (allocId : Local)
    {fieldIdx₁ fieldIdx₂ : FieldIdx} (newVal : Value)
    (hNe : fieldIdx₁ ≠ fieldIdx₂) :
    readFieldAt? (writeFieldAt? locals allocId fieldIdx₁ newVal)
      allocId fieldIdx₂ =
      readFieldAt? locals allocId fieldIdx₂ := by
  unfold writeFieldAt? readFieldAt?
  cases hGet : get? locals allocId with
  | none => simp [hGet]
  | some slot =>
    cases slot with
    | dead => simp [hGet]
    | uninit => simp [hGet]
    | init val =>
      cases val with
      | unit => simp [hGet]
      | scalar _ => simp [hGet]
      | ptr _ _ => simp [hGet]
      | aggregate varIdx elems =>
        cases varIdx with
        | succ _ => simp [hGet]
        | zero =>
          have hLt : allocId < locals.length :=
            (List.getElem?_eq_some_iff.mp hGet).1
          dsimp only
          unfold get?
          rw [List.getElem?_set_self hLt]
          dsimp only
          exact List.getElem?_set_ne hNe

theorem get?_writeFieldAt_ne_alloc
    (locals : List LocalValue) {allocId₁ allocId₂ : Local}
    (fieldIdx : FieldIdx) (newVal : Value)
    (hNe : allocId₂ ≠ allocId₁) :
    get? (writeFieldAt? locals allocId₁ fieldIdx newVal) allocId₂ =
      get? locals allocId₂ := by
  unfold writeFieldAt?
  cases hGet : get? locals allocId₁ with
  | none => rfl
  | some slot =>
    cases slot with
    | dead => rfl
    | uninit => rfl
    | init val =>
      cases val with
      | unit => rfl
      | scalar _ => rfl
      | ptr _ _ => rfl
      | aggregate varIdx _ =>
        cases varIdx with
        | succ _ => rfl
        | zero =>
          dsimp only
          unfold get?
          exact List.getElem?_set_ne hNe.symm

/--
A separating conjunction of two `ActiveTypedMutBorrow` assertions with an
arbitrary frame `R_frame` automatically entails disjoint footprints
`(rp₁.allocId, rp₁.offset) ≠ (rp₂.allocId, rp₂.offset)` and `rp₁.tag ≠ rp₂.tag`
(and, when `rp₁.offset = rp₂.offset`, `rp₁.allocId ≠ rp₂.allocId` and
`rp₁ ≠ rp₂`).
-/
theorem sepConj_activeTypedMutBorrow_disjoint {α β : Type}
    {rp₁ rp₂ : RawPtrVal} {codec₁ : ValueCodec α} {codec₂ : ValueCodec β}
    {a₁ : α} {a₂ : β} {R_frame : SepProp} {m : Memory}
    (hSep : SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁) (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)) m) :
    (rp₁.allocId, rp₁.offset) ≠ (rp₂.allocId, rp₂.offset) ∧
    rp₁.tag ≠ rp₂.tag ∧
    (rp₁.offset = rp₂.offset → rp₁.allocId ≠ rp₂.allocId ∧ rp₁ ≠ rp₂) := by
  rcases hSep with ⟨fp, h₁, h₂_3, ⟨_, _, h_disj1, h_addrs1, h_tags1⟩, h_atm1, h_atm2_3⟩
  rcases h_atm1 with ⟨h₁_pts, h₁_tok, ⟨_, _, _, h_addrs1_atm, h_tags1_atm⟩, ⟨_, h_pts1_fp⟩, ⟨_, h_tok1_fp⟩⟩
  rcases h_atm2_3 with ⟨h₂, h₃, ⟨_, _, _, h_addrs2, h_tags2⟩, h_atm2, h_frame⟩
  rcases h_atm2 with ⟨h₂_pts, h₂_tok, ⟨_, _, _, h_addrs2_atm, h_tags2_atm⟩, ⟨_, h_pts2_fp⟩, ⟨_, h_tok2_fp⟩⟩

  have h_addr1 : (rp₁.allocId, rp₁.offset) ∈ h₁.footprint.addrs := by
    apply (h_addrs1_atm (rp₁.allocId, rp₁.offset)).mpr
    left
    simp [h_pts1_fp]

  have h_addr2 : (rp₂.allocId, rp₂.offset) ∈ h₂_3.footprint.addrs := by
    apply (h_addrs2 (rp₂.allocId, rp₂.offset)).mpr
    left
    apply (h_addrs2_atm (rp₂.allocId, rp₂.offset)).mpr
    left
    simp [h_pts2_fp]

  have h_neq_addr : (rp₁.allocId, rp₁.offset) ≠ (rp₂.allocId, rp₂.offset) := by
    intro h_eq
    rw [← h_eq] at h_addr2
    exact h_disj1.1 (rp₁.allocId, rp₁.offset) h_addr1 h_addr2

  have h_tag1 : rp₁.tag ∈ h₁.footprint.tags := by
    apply (h_tags1_atm rp₁.tag).mpr
    right
    simp [h_tok1_fp]

  have h_tag2 : rp₂.tag ∈ h₂_3.footprint.tags := by
    apply (h_tags2 rp₂.tag).mpr
    left
    apply (h_tags2_atm rp₂.tag).mpr
    right
    simp [h_tok2_fp]

  have h_neq_tag : rp₁.tag ≠ rp₂.tag := by
    intro h_eq
    rw [← h_eq] at h_tag2
    exact h_disj1.2 rp₁.tag h_tag1 h_tag2

  refine ⟨h_neq_addr, h_neq_tag, ?_⟩
  intro h_off_eq
  constructor
  · intro h_alloc_eq
    apply h_neq_addr
    rw [h_alloc_eq, h_off_eq]
  · intro h_rp_eq
    apply h_neq_addr
    rw [h_rp_eq]


theorem holdsIn_of_sepConj_left {P Q : SepProp} {m : Memory}
    (h_holds : SepProp.holdsIn (sepConj P Q) m) : SepProp.holdsIn P m := by
  rcases h_holds with ⟨fp, h₁, h₂, hSplit, hP, hQ⟩
  refine ⟨h₁.footprint, ?_⟩
  have heq : h₁.state = m := hSplit.1
  exact heq ▸ hP

theorem holdsIn_of_sepConj_right {P Q : SepProp} {m : Memory}
    (h_holds : SepProp.holdsIn (sepConj P Q) m) : SepProp.holdsIn Q m := by
  rcases h_holds with ⟨fp, h₁, h₂, hSplit, hP, hQ⟩
  refine ⟨h₂.footprint, ?_⟩
  have heq : h₂.state = m := hSplit.2.1
  exact heq ▸ hQ

theorem readAllocAt_of_activeTypedMutBorrow_holdsIn
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {m : Memory}
    (h_holds : SepProp.holdsIn (ActiveTypedMutBorrow rp codec a) m) :
    readAllocAt? (memoryLocals m) rp = some (codec.encode a) := by
  rcases h_holds with ⟨fp, h₁, h₂, hSplit, ⟨hPts, _⟩, _⟩
  have heq : h₁.state = m := hSplit.1
  rw [←heq]
  exact hPts

theorem sepConj_entails_independentLenses {α β : Type}
    {rp₁ rp₂ : RawPtrVal} {codec₁ : ValueCodec α} {codec₂ : ValueCodec β}
    {a₁ : α} {a₂ : β} {R_frame : SepProp} {m : Memory}
    (hSep :
      SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁)
          (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)) m)
    (hExcl₁ : ExclusiveActiveBorrow rp₁ m)
    (hExcl₂ : ExclusiveActiveBorrow rp₂ m) :
    rp₁.allocId ≠ rp₂.allocId ∧
    rp₁.tag ≠ rp₂.tag ∧
    ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂ m ∧
    IndependentLenses
      (memoryPtrMutLens rp₁ codec₁)
      (memoryPtrMutLens rp₂ codec₂)
      (ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) ∧
    LawfulMutLens
      (prodMutLens (memoryPtrMutLens rp₁ codec₁) (memoryPtrMutLens rp₂ codec₂))
      (ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) := by
  have hDisj := sepConj_activeTypedMutBorrow_disjoint hSep
  have hOffEq : rp₁.offset = rp₂.offset :=
    hExcl₁.offset_zero.trans hExcl₂.offset_zero.symm
  have hAllocNe : rp₁.allocId ≠ rp₂.allocId := (hDisj.2.2 hOffEq).1
  have hTagNe : rp₁.tag ≠ rp₂.tag := hDisj.2.1

  have hPts₁ : readAllocAt? (memoryLocals m) rp₁ = some (codec₁.encode a₁) :=
    readAllocAt_of_activeTypedMutBorrow_holdsIn (holdsIn_of_sepConj_left hSep)
  have hPts₂ : readAllocAt? (memoryLocals m) rp₂ = some (codec₂.encode a₂) :=
    readAllocAt_of_activeTypedMutBorrow_holdsIn (holdsIn_of_sepConj_left (holdsIn_of_sepConj_right hSep))
  have hL₁ : ValidMutBorrowLens rp₁ codec₁ m :=
    ⟨⟨a₁, hPts₁⟩, hExcl₁⟩
  have hL₂ : ValidMutBorrowLens rp₂ codec₂ m :=
    ⟨⟨a₂, hPts₂⟩, hExcl₂⟩

  have hValidPair : ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂ m :=
    ⟨hL₁, hL₂, hAllocNe⟩
  have hInd := memoryPtrMutLens_independent_of_ne_alloc rp₁ rp₂ codec₁ codec₂
  have hLaw₁ :
      LawfulMutLens
        (memoryPtrMutLens rp₁ codec₁)
        (ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) := {
    valid_writeBack := hInd.valid_writeBack_left
    readView_writeBack := fun a c hc =>
      (memoryPtrMutLens_lawful rp₁ codec₁).readView_writeBack a c hc.valid_left
    writeBack_readView := fun c hc =>
      (memoryPtrMutLens_lawful rp₁ codec₁).writeBack_readView c hc.valid_left
    writeBack_writeBack := fun a₁' a₂' c hc =>
      (memoryPtrMutLens_lawful rp₁ codec₁).writeBack_writeBack a₁' a₂' c
        hc.valid_left
  }
  have hLaw₂ :
      LawfulMutLens
        (memoryPtrMutLens rp₂ codec₂)
        (ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) := {
    valid_writeBack := hInd.valid_writeBack_right
    readView_writeBack := fun b c hc =>
      (memoryPtrMutLens_lawful rp₂ codec₂).readView_writeBack b c hc.valid_right
    writeBack_readView := fun c hc =>
      (memoryPtrMutLens_lawful rp₂ codec₂).writeBack_readView c hc.valid_right
    writeBack_writeBack := fun b₁' b₂' c hc =>
      (memoryPtrMutLens_lawful rp₂ codec₂).writeBack_writeBack b₁' b₂' c
        hc.valid_right
  }
  refine ⟨hAllocNe, hTagNe, hValidPair, hInd,
    prodMutLens_lawful hLaw₁ hLaw₂ hInd⟩

/-! ## 2. Pure Lens-State Lifting Rules -/

/--
Project a `RawPtrVal` to a `MirAst.ProvenancePtr` whose `allocId` field
carries the provenance tag `rp.tag`, as `MirSemantics` pointers do.
-/
@[reducible]
def _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr (rp : RawPtrVal) : ProvenancePtr :=
  { allocId := rp.tag, offsetBytes := rp.offset }

/-- Encode a `RawPtrVal` as an 8-byte thin pointer `Value.ptr`. -/
@[reducible]
def _root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue (rp : RawPtrVal) : Value :=
  .ptr rp.toMirPtr 8

/-- Look up the current pointee `Value` of `rp` in the lens bindings. -/
@[reducible]
def lookupLensVal?
    (entries : List (RawPtrVal × Value)) (rp : RawPtrVal) : Option Value :=
  match entries with
  | [] => .none
  | (k, v) :: rest =>
    if k = rp then .some v else lookupLensVal? rest rp

/-- Functionally update the pointee `Value` of `rp` in `entries` to `newVal`. -/
@[reducible]
def updateLensVal
    (entries : List (RawPtrVal × Value)) (rp : RawPtrVal) (newVal : Value) :
    List (RawPtrVal × Value) :=
  match entries with
  | [] => []
  | (k, v) :: rest =>
    if k = rp then (k, newVal) :: rest else (k, v) :: updateLensVal rest rp newVal

theorem lookupLensVal?_mem
    {entries : List (RawPtrVal × Value)} {rp : RawPtrVal} {v : Value}
    (h : lookupLensVal? entries rp = .some v) :
    (rp, v) ∈ entries := by
  induction entries with
  | nil => nomatch h
  | cons hd tl ih =>
    rcases hd with ⟨k, w⟩
    unfold lookupLensVal? at h
    by_cases hEq : k = rp
    · simp only [hEq, ite_true, Option.some.injEq] at h
      subst hEq h
      exact List.Mem.head tl
    · simp only [hEq, ite_false] at h
      exact List.Mem.tail _ (ih h)

theorem updateLensVal_map_fst
    (entries : List (RawPtrVal × Value)) (rp : RawPtrVal) (newVal : Value) :
    (updateLensVal entries rp newVal).map Prod.fst = entries.map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨k, w⟩
    unfold updateLensVal
    by_cases hEq : k = rp
    · simp [hEq]
    · simp [hEq, ih]

theorem mem_updateLensVal_raw
    {entries : List (RawPtrVal × Value)} {rp k : RawPtrVal} {newVal v : Value}
    (hPairwise :
      List.Pairwise
        (fun k₁ k₂ => k₁.allocId ≠ k₂.allocId ∧ k₁.tag ≠ k₂.tag)
        (entries.map Prod.fst))
    (hMem : (k, v) ∈ updateLensVal entries rp newVal) :
    (k = rp ∧ v = newVal) ∨ (k ≠ rp ∧ (k, v) ∈ entries) := by
  induction entries with
  | nil => nomatch hMem
  | cons hd tl ih =>
    rcases hd with ⟨k₀, w₀⟩
    simp only [List.map_cons, List.pairwise_cons] at hPairwise
    rcases hPairwise with ⟨hHdNotInTl, hTlPairwise⟩
    unfold updateLensVal at hMem
    by_cases hEq : k₀ = rp
    · subst hEq
      simp only [ite_true, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · injection hHead with hK hV
        exact Or.inl ⟨hK, hV⟩
      · have hKInTl : k ∈ tl.map Prod.fst :=
          List.mem_map.mpr ⟨(k, v), hTail, rfl⟩
        have hDisj := hHdNotInTl k hKInTl
        have hNe : k ≠ k₀ := fun h => hDisj.1 (congrArg RawPtrVal.allocId h.symm)
        exact Or.inr ⟨hNe, List.Mem.tail _ hTail⟩
    · simp only [hEq, ite_false, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · injection hHead with hK hV
        subst hK hV
        exact Or.inr ⟨hEq, List.Mem.head tl⟩
      · rcases ih hTlPairwise hTail with hLeft | ⟨hNe, hInTl⟩
        · exact Or.inl hLeft
        · exact Or.inr ⟨hNe, List.Mem.tail _ hInTl⟩

theorem pairwise_disjoint_of_mem_ne
    {entries : List (RawPtrVal × Value)} {rp k : RawPtrVal} {v₁ v₂ : Value}
    (hPairwise :
      List.Pairwise
        (fun k₁ k₂ => k₁.allocId ≠ k₂.allocId ∧ k₁.tag ≠ k₂.tag)
        (entries.map Prod.fst))
    (hMem₁ : (rp, v₁) ∈ entries)
    (hMem₂ : (k, v₂) ∈ entries)
    (hNe : k ≠ rp) :
    k.allocId ≠ rp.allocId ∧ k.tag ≠ rp.tag := by
  induction entries with
  | nil => nomatch hMem₁
  | cons hd tl ih =>
    rcases hd with ⟨k₀, w₀⟩
    simp only [List.map_cons, List.pairwise_cons] at hPairwise
    rcases hPairwise with ⟨hHd, hTl⟩
    simp only [List.mem_cons] at hMem₁ hMem₂
    rcases hMem₁ with h₁ | h₁ <;> rcases hMem₂ with h₂ | h₂
    · injection h₁ with hK₁ _
      injection h₂ with hK₂ _
      exact absurd (hK₂.trans hK₁.symm) hNe
    · injection h₁ with hK₁ _
      subst hK₁
      have hIn : k ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(k, v₂), h₂, rfl⟩
      exact ⟨(hHd k hIn).1.symm, (hHd k hIn).2.symm⟩
    · injection h₂ with hK₂ _
      subst hK₂
      have hIn : rp ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(rp, v₁), h₁, rfl⟩
      exact hHd rp hIn
    · exact ih hTl h₁ h₂

/-! ### Tree Borrows Parent/Child Exclusivity (`I-10`) -/

/--
`resolveTreeBorrowWriterTag` normalizes a writer tag to `entry.tag` whenever
the writer descends from (or is) `entry` in the `I-10` parent/child hierarchy.
-/
theorem resolveTreeBorrowWriterTag_of_descendant
    {borrows : List BorrowEntry} {entry : BorrowEntry} {tag : Nat}
    (h : isBorrowDescendantOrSelf borrows tag entry.tag = true) :
    resolveTreeBorrowWriterTag borrows entry (.some tag) = .some entry.tag := by
  unfold resolveTreeBorrowWriterTag
  dsimp only
  rw [h]

/--
Tree-Borrows-aware exclusivity of a root mutable borrow `rp` in `m` under the
`I-10` parent/child hierarchy (`BorrowEntry.parentTag`).

It relaxes `ExclusiveActiveBorrow` in one way. Besides `rp.tag`'s own entry,
an entry targeting `rp.allocId` may remain `.active` when it is an ancestor of
`rp.tag` (`isBorrowDescendantOrSelf m.borrows rp.tag b.tag = true`), as when a
callee receives the reborrow `&mut *r` of a caller reference `r`. Reads and
writes through `rp.tag` are local (child) accesses for such ancestors, so
`freezeTreeBorrowsOnReadAtProj`, `invalidateTreeBorrowsAtProj`, and
`hasProtectedTreeWriteConflict` leave them untouched. Every other entry on the
allocation must already be `.disabled`.
-/
structure TreeExclusiveBorrow (rp : RawPtrVal) (m : Memory) : Prop where
  offset_zero : rp.offset = 0
  lookup_active :
    ∃ entry,
      lookupBorrow m.borrows rp.tag = .some entry ∧
      entry.targetLocal = rp.allocId ∧
      entry.targetProjection = [] ∧
      entry.perm = .active ∧
      entry.rangeOffset = 0 ∧
      entry.rangeLen = 0
  ancestors_active_or_disabled :
    ∀ b ∈ m.borrows,
      b.targetLocal = rp.allocId →
        (isBorrowDescendantOrSelf m.borrows rp.tag b.tag = true ∧
          b.perm = .active) ∨
        b.perm = .disabled

/-- The strict exclusivity invariant is the ancestor-free special case. -/
theorem ExclusiveActiveBorrow.toTree {rp : RawPtrVal} {m : Memory}
    (h : ExclusiveActiveBorrow rp m) : TreeExclusiveBorrow rp m where
  offset_zero := h.offset_zero
  lookup_active := h.lookup_active
  ancestors_active_or_disabled b hb hTarget := by
    rcases h.exclusive_on_alloc b hb hTarget with ⟨hTag, hPerm, _⟩ | hDis
    · left
      rw [hTag]
      exact ⟨isBorrowDescendantOrSelf_self _ _, hPerm⟩
    · exact Or.inr hDis

theorem TreeExclusiveBorrow.of_borrows_eq
    {rp : RawPtrVal} {m₁ m₂ : Memory}
    (h : TreeExclusiveBorrow rp m₁)
    (hBorrows : m₂.borrows = m₁.borrows) :
    TreeExclusiveBorrow rp m₂ where
  offset_zero := h.offset_zero
  lookup_active := by rw [hBorrows]; exact h.lookup_active
  ancestors_active_or_disabled := by
    rw [hBorrows]; exact h.ancestors_active_or_disabled

/--
Separation-logic lens-state invariant connecting a pure local slot environment
of length `frameLen` and pure lens bindings `entries : List (RawPtrVal × Value)`
to the concrete 12-field `Memory` state `m`. Each tracked pointer must satisfy
the `I-10` parent/child exclusivity invariant `TreeExclusiveBorrow`.
-/
structure SepLensStateInv
    (frameLen : Nat)
    (entries : List (RawPtrVal × Value))
    (m : Memory) : Prop where
  callStack_nil : m.callStack = []
  activeCallee_none : m.activeCallee = .none
  borrows_above_frame : ∀ b ∈ m.borrows, frameLen ≤ b.targetLocal
  entries_valid :
    ∀ rp v, (rp, v) ∈ entries →
      rp.offset = 0 ∧
      frameLen ≤ rp.allocId ∧
      get? m.callerLocals rp.allocId = .some (.init v) ∧
      TreeExclusiveBorrow rp m
  pairwise_disjoint :
    List.Pairwise
      (fun k₁ k₂ => k₁.allocId ≠ k₂.allocId ∧ k₁.tag ≠ k₂.tag)
      (entries.map Prod.fst)

/-- Extract the Tree Borrows permission of a pointer. -/
def hasBorrowPerm (borrows : List BorrowEntry) (rp : RawPtrVal) : Option TreeBorrowPerm :=
  (lookupBorrow borrows rp.tag).map BorrowEntry.perm

/--
Relational invariant between initial memory `m₀` (with initial lens bindings
`entries₀`) and current memory `m`: every caller allocation outside the tracked
allocations of `entries₀`, and every borrow-table entry whose tag is not a
tracked tag, is unchanged.
-/
structure LensFramePreserved
    (entries₀ : List (RawPtrVal × Value)) (m₀ m : Memory) : Prop where
  locals_unchanged_outside :
    ∀ allocId : Nat,
      (∀ e ∈ entries₀, allocId ≠ e.1.allocId) →
        get? m.callerLocals allocId = get? m₀.callerLocals allocId
  borrows_unchanged_outside :
    ∀ tag : Nat,
      (∀ e ∈ entries₀, tag ≠ e.1.tag) →
        lookupBorrow m.borrows tag = lookupBorrow m₀.borrows tag

theorem LensFramePreserved.refl
    (entries₀ : List (RawPtrVal × Value)) (m₀ : Memory) :
    LensFramePreserved entries₀ m₀ m₀ where
  locals_unchanged_outside _ _ := rfl
  borrows_unchanged_outside _ _ := rfl

/-! ### Borrow-Table Identities for Retags, Deref Accesses, and Local Writes -/

theorem mem_attachBorrowProtector
    {borrows : List BorrowEntry} {tag pid : Nat} {b : BorrowEntry}
    (h : b ∈ attachBorrowProtector borrows tag pid) :
    ∃ b₀ ∈ borrows,
      b.tag = b₀.tag ∧
      b.targetLocal = b₀.targetLocal ∧
      b.targetProjection = b₀.targetProjection ∧
      b.perm = b₀.perm ∧
      b.rangeOffset = b₀.rangeOffset ∧
      b.rangeLen = b₀.rangeLen := by
  induction borrows with
  | nil => nomatch h
  | cons hd tl ih =>
    simp only [attachBorrowProtector] at h
    cases hTag : hd.tag.beq tag
    · simp only [hTag] at h
      rcases List.mem_cons.mp h with rfl | hTail
      · exact ⟨_, List.Mem.head tl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rcases ih hTail with ⟨b₀, hMem, hF⟩
        exact ⟨b₀, List.Mem.tail hd hMem, hF⟩
    · simp only [hTag] at h
      rcases List.mem_cons.mp h with rfl | hTail
      · exact ⟨_, List.Mem.head tl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · rcases ih hTail with ⟨b₀, hMem, hF⟩
        exact ⟨b₀, List.Mem.tail hd hMem, hF⟩

theorem lookupBorrow_attachBorrowProtector_ne
    (borrows : List BorrowEntry) (tag pid q : Nat) (hNe : tag ≠ q) :
    lookupBorrow (attachBorrowProtector borrows tag pid) q =
    lookupBorrow borrows q := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    simp only [attachBorrowProtector]
    cases hTag : hd.tag.beq tag <;> dsimp only
    · cases hQ : hd.tag.beq q
      · simp [lookupBorrow, hQ, ih]
      · simp [lookupBorrow, hQ]
    · cases hQ : hd.tag.beq q
      · simp [lookupBorrow, hQ, ih]
      · have hEq₁ := Nat.eq_of_beq_eq_true hTag
        have hEq₂ := Nat.eq_of_beq_eq_true hQ
        subst hEq₁; subst hEq₂
        contradiction

theorem lookupBorrow_attachBorrowProtector_perm
    (borrows : List BorrowEntry) (tag pid q : Nat) :
    (lookupBorrow (attachBorrowProtector borrows tag pid) q).map
      BorrowEntry.perm =
    (lookupBorrow borrows q).map BorrowEntry.perm := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    simp only [attachBorrowProtector]
    cases hTag : hd.tag.beq tag <;> dsimp only
    · cases hQ : hd.tag.beq q
      · simp [lookupBorrow, hQ, ih]
      · simp [lookupBorrow, hQ]
    · cases hQ : hd.tag.beq q
      · simp [lookupBorrow, hQ, ih]
      · simp [lookupBorrow, hQ]

theorem hasBorrowPerm_attachBorrowProtector
    (borrows : List BorrowEntry) (tag pid : Nat) (rp : RawPtrVal) :
    hasBorrowPerm (attachBorrowProtector borrows tag pid) rp =
      hasBorrowPerm borrows rp := by
  unfold hasBorrowPerm
  have h := lookupBorrow_attachBorrowProtector_perm borrows tag pid rp.tag
  simp [h]

theorem lookupBorrow_attachBorrowProtector_some
    {borrows : List BorrowEntry} {tag pid q : Nat} {entry : BorrowEntry}
    (h : lookupBorrow borrows q = .some entry) :
    ∃ entry',
      lookupBorrow (attachBorrowProtector borrows tag pid) q = .some entry' ∧
      entry'.targetLocal = entry.targetLocal ∧
      entry'.targetProjection = entry.targetProjection ∧
      entry'.perm = entry.perm ∧
      entry'.rangeOffset = entry.rangeOffset ∧
      entry'.rangeLen = entry.rangeLen := by
  induction borrows with
  | nil => nomatch h
  | cons hd tl ih =>
    unfold lookupBorrow at h
    unfold attachBorrowProtector
    cases hEqQ : Nat.beq hd.tag q with
    | false =>
      rw [hEqQ] at h
      cases Nat.beq hd.tag tag <;>
        simp only [lookupBorrow, hEqQ] <;>
        exact ih h
    | true =>
      rw [hEqQ] at h
      injection h with hHd
      subst hHd
      cases hTag : Nat.beq hd.tag tag <;>
        dsimp only <;>
        simp only [lookupBorrow, hEqQ] <;>
        exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
Exact characterization of lookups after `attachBorrowProtector`: the entry
found for `q` is unchanged except for its `protector` field.
-/
theorem lookupBorrow_attachBorrowProtector
    (borrows : List BorrowEntry) (tag pid q : Nat) :
    lookupBorrow (attachBorrowProtector borrows tag pid) q =
      (lookupBorrow borrows q).map (fun e =>
        match Nat.beq e.tag tag with
        | true => { e with protector := .some pid }
        | false => e) := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    unfold attachBorrowProtector
    cases hTag : Nat.beq hd.tag tag <;>
      cases hQ : Nat.beq hd.tag q <;>
      simp [lookupBorrow, hTag, hQ, ih]

theorem length_attachBorrowProtector
    (borrows : List BorrowEntry) (tag pid : Nat) :
    length (attachBorrowProtector borrows tag pid) = length borrows := by
  unfold length
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    unfold attachBorrowProtector
    cases Nat.beq hd.tag tag <;> simp [ih]

theorem isBorrowDescendantOrSelfAux_attachBorrowProtector
    (fuel : Nat) (borrows : List BorrowEntry) (tag pid c a : Nat) :
    isBorrowDescendantOrSelfAux fuel (attachBorrowProtector borrows tag pid) c a =
      isBorrowDescendantOrSelfAux fuel borrows c a := by
  induction fuel generalizing c with
  | zero => rfl
  | succ fuel ih =>
    simp only [isBorrowDescendantOrSelfAux, lookupBorrow_attachBorrowProtector]
    cases Nat.beq c a with
    | true => rfl
    | false =>
      dsimp only
      cases lookupBorrow borrows c with
      | none => rfl
      | some e =>
        dsimp only [Option.map]
        cases Nat.beq e.tag tag <;> dsimp only <;> cases e.parentTag <;>
          first | rfl | exact ih _

/--
Attaching a function-entry protector never changes the `I-10` parent/child
hierarchy: `isBorrowDescendantOrSelf` only follows `tag` and `parentTag`.
-/
theorem isBorrowDescendantOrSelf_attachBorrowProtector
    (borrows : List BorrowEntry) (tag pid c a : Nat) :
    isBorrowDescendantOrSelf (attachBorrowProtector borrows tag pid) c a =
      isBorrowDescendantOrSelf borrows c a := by
  unfold isBorrowDescendantOrSelf
  rw [length_attachBorrowProtector]
  exact isBorrowDescendantOrSelfAux_attachBorrowProtector _ _ _ _ _ _

theorem SepLensStateInv.attachProtector
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    (hInv : SepLensStateInv frameLen entries m)
    (tag protId : Nat) :
    SepLensStateInv frameLen entries {
      m with
      borrows := attachBorrowProtector m.borrows tag protId
      activeProtectors := protId :: m.activeProtectors
      nextProtector := Nat.add protId 1
    } where
  callStack_nil := hInv.callStack_nil
  activeCallee_none := hInv.activeCallee_none
  borrows_above_frame b hb := by
    rcases mem_attachBorrowProtector hb with ⟨b₀, hb₀, _, hTarget, _⟩
    rw [hTarget]
    exact hInv.borrows_above_frame b₀ hb₀
  entries_valid rp v hMem := by
    rcases hInv.entries_valid rp v hMem with
      ⟨hOff, hAbove, hCaller, ⟨_, hLook, hTree⟩⟩
    rcases hLook with ⟨entry, hLookEq, hT, hP, hPerm, hRO, hRL⟩
    rcases lookupBorrow_attachBorrowProtector_some
        (tag := tag) (pid := protId) hLookEq with
      ⟨entry', hLook', hT', hP', hPerm', hRO', hRL'⟩
    refine ⟨hOff, hAbove, hCaller, ⟨hOff,
      ⟨entry', hLook', hT'.trans hT, hP'.trans hP, hPerm'.trans hPerm,
        hRO'.trans hRO, hRL'.trans hRL⟩, ?_⟩⟩
    intro b hb hTargetB
    rcases mem_attachBorrowProtector hb with
      ⟨b₀, hb₀, hTagB, hTargetB₀, _, hPermB, _, _⟩
    dsimp only
    rw [isBorrowDescendantOrSelf_attachBorrowProtector, hTagB, hPermB]
    exact hTree b₀ hb₀ (hTargetB₀.symm.trans hTargetB)
  pairwise_disjoint := hInv.pairwise_disjoint

/--
`I-10` deref-read freezing is the identity on a borrow table whose entries on
the read allocation are active ancestors-or-self of the reader tag or are
already disabled: every such read is a local (child) read.
-/
theorem freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat}
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    freezeTreeBorrowsOnReadAtProj
      allBorrows borrows allocId (.some tag)
      readProj readRangeOff readRangeLen = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold freezeTreeBorrowsOnReadAtProj
    rw [hTail]
    unfold updateBorrowPermOnReadAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      cases borrowEntryOverlapsWrite hd readProj readRangeOff readRangeLen with
      | false => rfl
      | true =>
        dsimp only
        rcases hTree hd (List.Mem.head tl) hTargetEq with ⟨hDesc, _⟩ | hDis
        · rw [hDesc]
        · cases isBorrowDescendantOrSelf allBorrows tag hd.tag with
          | true => rfl
          | false =>
            dsimp only
            rw [hDis]

/--
No protected entry conflicts with an `I-10` write whose allocation entries are
active ancestors-or-self of the writer tag or are already disabled.
-/
theorem hasProtectedTreeWriteConflict_eq_false_of_tree
    (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    {allocId tag : Nat}
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    hasProtectedTreeWriteConflict
      allBorrows borrows activeProtectors allocId (.some tag)
      writeProj writeRangeOff writeRangeLen = false := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold hasProtectedTreeWriteConflict
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false =>
      simp [hTail]
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      have hNoConflict :
          borrowEntryWriteConflicts
            hd
            (resolveTreeBorrowWriterTag allBorrows hd (.some tag)) = false := by
        rcases hTree hd (List.Mem.head tl) hTargetEq with ⟨hDesc, _⟩ | hDis
        · rw [resolveTreeBorrowWriterTag_of_descendant hDesc]
          unfold borrowEntryWriteConflicts
          simp
        · unfold borrowEntryWriteConflicts
          cases resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
          | none => simp [hDis]
          | some wTag =>
            cases hEq : Nat.beq hd.tag wTag <;> simp [hEq, hDis]
      simp [hNoConflict, hTail]

/--
`I-10` deref-write invalidation is the identity on a borrow table whose entries
on the written allocation are active ancestors-or-self of the writer tag (local
writes keep them `.active`) or are already disabled.
-/
theorem invalidateTreeBorrowsAtProj_eq_self_of_tree
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat}
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    invalidateTreeBorrowsAtProj
      allBorrows borrows allocId (.some tag)
      writeProj writeRangeOff writeRangeLen = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold invalidateTreeBorrowsAtProj
    rw [hTail]
    unfold updateBorrowPermTreeAtProj
    unfold updateBorrowPermAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      dsimp only
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hTree hd (List.Mem.head tl) hTargetEq with ⟨hDesc, hPerm⟩ | hDis
      · rw [resolveTreeBorrowWriterTag_of_descendant hDesc]
        dsimp only
        have hEq : Nat.beq hd.tag hd.tag = true := by simp
        rw [hEq]
        simp [hPerm]
      · cases hWriter : resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
        | none =>
          dsimp only
          cases hOverlap :
              borrowEntryOverlapsWrite hd writeProj writeRangeOff writeRangeLen <;>
            simp [hDis]
        | some wTag =>
          dsimp only
          cases hEq : Nat.beq hd.tag wTag with
          | true => simp [hDis]
          | false =>
            dsimp only
            cases hOverlap :
                borrowEntryOverlapsWrite hd writeProj writeRangeOff writeRangeLen with
            | false => rfl
            | true =>
              dsimp only
              rw [borrowEntry_disabled_eta hDis]


theorem hasProtectedWriteConflict_eq_false_of_lt_frame
    {borrows : List BorrowEntry} {frameLen dstLoc : Nat}
    (activeProtectors : List Nat)
    (hAbove : ∀ b ∈ borrows, frameLen ≤ b.targetLocal)
    (hLt : dstLoc < frameLen) :
    hasProtectedWriteConflict borrows activeProtectors dstLoc .none .nil =
      false := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hHdAbove : frameLen ≤ hd.targetLocal :=
      hAbove hd (List.Mem.head tl)
    have hNe : hd.targetLocal ≠ dstLoc := Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt hHdAbove)
    have hBeq : Nat.beq hd.targetLocal dstLoc = false := by
      cases h : Nat.beq hd.targetLocal dstLoc with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true h))
    unfold hasProtectedWriteConflict
    simp [hBeq, ih (fun b hb => hAbove b (List.Mem.tail hd hb))]

/--
No borrow-table entry targets a local `loc` of the current frame when every
entry targets a caller-owned slot at or above `env.length` and
`get? env loc = .some slot`.
-/
theorem targetLocal_ne_of_lt_frame
    {borrows : List BorrowEntry} {env : List LocalSlot} {loc : Local} {slot : LocalSlot}
    (hAbove : ∀ b ∈ borrows, env.length ≤ b.targetLocal)
    (hGet : get? env loc = .some slot) :
    ∀ b ∈ borrows, b.targetLocal ≠ loc := by
  have hLt : loc < env.length := (List.getElem?_eq_some_iff.mp hGet).1
  intro b hb hEq
  have hLe := hAbove b hb
  rw [hEq] at hLe
  exact Nat.lt_irrefl loc (Nat.lt_of_lt_of_le hLt hLe)

theorem invalidateConflictingBorrows_eq_self_of_lt_frame
    {borrows : List BorrowEntry} {frameLen dstLoc : Nat}
    (hAbove : ∀ b ∈ borrows, frameLen ≤ b.targetLocal)
    (hLt : dstLoc < frameLen) :
    invalidateConflictingBorrows borrows dstLoc .none = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hHdAbove : frameLen ≤ hd.targetLocal :=
      hAbove hd (List.Mem.head tl)
    have hNe : hd.targetLocal ≠ dstLoc := Nat.ne_of_gt (Nat.lt_of_lt_of_le hLt hHdAbove)
    have hBeq : Nat.beq hd.targetLocal dstLoc = false := by
      cases h : Nat.beq hd.targetLocal dstLoc with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true h))
    simp [invalidateConflictingBorrows_cons, updateBorrowPerm, hBeq,
      ih (fun b hb => hAbove b (List.Mem.tail hd hb))]

/-! ### Variable-Headed Pure Lens-State Lifting Judgments -/

/--
Variable-headed pure operand evaluation on a local slot environment
`env : PureEnv`, including single-field projections such as `move (_3.0: u32)`
that read one component of a checked-arithmetic pair.
-/
inductive LiftLensOperand
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    PureEnv → Operand → Value → PureEnv → Prop where
  | copy_local {env : PureEnv} {loc : Local} {v : Value} :
      get? env loc = .some (.init v) →
      LiftLensOperand localDecls layouts env (.copy { local_ := loc, projection := [] }) v env
  | move_local {env env' : PureEnv} {loc : Local} {v : Value} :
      get? env loc = .some (.init v) →
      set? env loc .uninit = .some env' →
      LiftLensOperand localDecls layouts env (.move { local_ := loc, projection := [] }) v env'
  | copy_field {env : PureEnv} {loc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
      {rootVal v : Value} :
      get? env loc = .some (.init rootVal) →
      placeTouchesUnion localDecls layouts
        { local_ := loc, projection := [.field fieldIdx fieldTy] } = false →
      readProjectedValue env rootVal [.field fieldIdx fieldTy] = .ok v →
      LiftLensOperand localDecls layouts env
        (.copy { local_ := loc, projection := [.field fieldIdx fieldTy] }) v env
  | move_field {env : PureEnv} {loc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
      {rootVal v : Value} :
      get? env loc = .some (.init rootVal) →
      placeTouchesUnion localDecls layouts
        { local_ := loc, projection := [.field fieldIdx fieldTy] } = false →
      readProjectedValue env rootVal [.field fieldIdx fieldTy] = .ok v →
      LiftLensOperand localDecls layouts env
        (.move { local_ := loc, projection := [.field fieldIdx fieldTy] }) v env
  | const_scalar {env : PureEnv} {ty : Ty} {sc : ScalarInt} :
      LiftLensOperand localDecls layouts
        env
        (.constant { ty := ty, val := .scalar (.int sc) })
        (.scalar sc)
        env
  | const_zeroSized {env : PureEnv} {ty : Ty} :
      LiftLensOperand localDecls layouts
        env
        (.constant { ty := ty, val := .zeroSized })
        .unit
        env

/--
Variable-headed pure dereference read rule (`LiftDerefRead`) reading `*ptrLoc`
from the pure lens environment `entries` without inspecting or unfolding
`Memory`.
-/
inductive LiftDerefRead :
    PureEnv → List (RawPtrVal × Value) → Operand → Value → PureEnv → Prop where
  | copy_deref
      {env : PureEnv} {entries : List (RawPtrVal × Value)}
      {ptrLoc : Local} {rp : RawPtrVal} {v : Value} :
      get? env ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some v →
      LiftDerefRead
        env entries (.copy { local_ := ptrLoc, projection := [.deref] }) v env
  | move_deref
      {env : PureEnv} {entries : List (RawPtrVal × Value)}
      {ptrLoc : Local} {rp : RawPtrVal} {v : Value} :
      get? env ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some v →
      LiftDerefRead
        env entries (.move { local_ := ptrLoc, projection := [.deref] }) v env

/--
Variable-headed pure projected dereference field read (`LiftDerefFieldRead`)
lifting `copy ((*ptrLoc).fieldIdx)` and `move ((*ptrLoc).fieldIdx)` against an
aggregate pointee in the pure lens environment `entries`.
-/
inductive LiftDerefFieldRead :
    PureEnv → List (RawPtrVal × Value) → Operand → Value → PureEnv → Prop where
  | copy_deref_field
      {env : PureEnv} {entries : List (RawPtrVal × Value)}
      {ptrLoc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
      {rp : RawPtrVal} {aggVal v : Value} :
      get? env ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some aggVal →
      readProjectedValue env aggVal [.field fieldIdx fieldTy] = .ok v →
      LiftDerefFieldRead
        env entries
        (.copy { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] })
        v env
  | move_deref_field
      {env : PureEnv} {entries : List (RawPtrVal × Value)}
      {ptrLoc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
      {rp : RawPtrVal} {aggVal v : Value} :
      get? env ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some aggVal →
      readProjectedValue env aggVal [.field fieldIdx fieldTy] = .ok v →
      LiftDerefFieldRead
        env entries
        (.move { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] })
        v env

/--
Unified operand lifting: a pure local or constant operand (`LiftLensOperand`),
a separation-logic lens dereference read (`LiftDerefRead`), or a projected
dereference field read (`LiftDerefFieldRead`). It lets compound rvalues such as
`Add(copy (*_1), copy _2)` or `Add(copy ((*_1).0), copy ((*_1).1))` read
pointees and pointee fields directly.
-/
inductive LiftLensOperandAny
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    PureEnv → List (RawPtrVal × Value) → Operand → Value → PureEnv → Prop where
  | pure {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftLensOperand localDecls layouts env op v env' →
      LiftLensOperandAny localDecls layouts env entries op v env'
  | deref {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftDerefRead env entries op v env' →
      LiftLensOperandAny localDecls layouts env entries op v env'
  | deref_field {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftDerefFieldRead env entries op v env' →
      LiftLensOperandAny localDecls layouts env entries op v env'

/--
Left-to-right operand-list lifting (`LiftLensOperands`) matching
`evalOperands` for aggregate construction (`Rvalue.aggregate`).
-/
inductive LiftLensOperands
    (localDecls : List LocalDecl := .nil) (layouts : LayoutTable := emptyLayoutTable) :
    PureEnv → List (RawPtrVal × Value) → List Operand → List Value →
    PureEnv → Prop where
  | nil {env : PureEnv} {entries : List (RawPtrVal × Value)} :
      LiftLensOperands localDecls layouts env entries [] [] env
  | cons
      {env env₁ env₂ : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {ops : List Operand} {v : Value} {vs : List Value} :
      LiftLensOperandAny localDecls layouts env entries op v env₁ →
      LiftLensOperands localDecls layouts env₁ entries ops vs env₂ →
      LiftLensOperands localDecls layouts env entries (op :: ops) (v :: vs) env₂

/--
Variable-headed pure rvalue evaluation (`LiftLensRvalue`) combining pure local
operands and separation-logic lens dereference reads.

`binaryOp` covers every scalar `BinOp` whose operands lift through
`LiftLensOperandAny`: the side condition asks `evalScalarBinOp` to succeed with
the signedness `evalRvalue` derives from `localDecls`, independently of the
memory it threads through unchanged.
-/
inductive LiftLensRvalue
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    PureEnv → List (RawPtrVal × Value) → Rvalue → Value → PureEnv → Prop where
  | use_pure
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftLensOperand localDecls layouts env op v env' →
      validateLoadedValue layouts localDecls op v = true →
      LiftLensRvalue localDecls layouts env entries (.use op) v env'
  | use_deref
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftDerefRead env entries op v env' →
      validateLoadedValue layouts localDecls op v = true →
      LiftLensRvalue localDecls layouts env entries (.use op) v env'
  | use_deref_field
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftDerefFieldRead env entries op v env' →
      validateLoadedValue layouts localDecls op v = true →
      LiftLensRvalue localDecls layouts env entries (.use op) v env'
  | copyForDeref_deref
      {env : PureEnv} {entries : List (RawPtrVal × Value)}
      {ptrLoc : Local} {rp : RawPtrVal} {v : Value} :
      get? env ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some v →
      LiftLensRvalue localDecls layouts env entries
        (.copyForDeref { local_ := ptrLoc, projection := [.deref] }) v env
  | binaryOp
      {env env₁ env₂ : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : BinOp} {lhsOp rhsOp : Operand} {lhs rhs : ScalarInt} {v : Value} :
      LiftLensOperandAny localDecls layouts env entries lhsOp (.scalar lhs) env₁ →
      LiftLensOperandAny localDecls layouts env₁ entries rhsOp (.scalar rhs) env₂ →
      (∀ mem : Memory,
        evalScalarBinOp op lhs rhs env₂ mem
            (operandIsSigned localDecls lhsOp layouts) =
          .ok v env₂ mem) →
      LiftLensRvalue localDecls layouts env entries
        (.binaryOp op lhsOp rhsOp) v env₂
  | unaryOp_not
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {sc : ScalarInt} {v : Value} :
      LiftLensOperandAny localDecls layouts env entries op (.scalar sc) env' →
      (∀ mem : Memory,
        evalUnaryNot sc (operandTy localDecls layouts op) env' mem =
          .ok v env' mem) →
      LiftLensRvalue localDecls layouts env entries
        (.unaryOp .not op) v env'
  | unaryOp_neg
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {sc : ScalarInt} :
      LiftLensOperandAny localDecls layouts env entries op (.scalar sc) env' →
      Nat.beq sc.sizeBytes 0 = false →
      LiftLensRvalue localDecls layouts env entries
        (.unaryOp .neg op)
        (.scalar ⟨wrapScalarBits
          (Nat.sub (scalarModulus sc.sizeBytes)
            (wrapScalarBits sc.bits (scalarModulus sc.sizeBytes)))
          (scalarModulus sc.sizeBytes), sc.sizeBytes⟩)
        env'
  | cast_intToInt
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {targetTy : Ty} {sc : ScalarInt} {targetBytes : Nat} :
      LiftLensOperandAny localDecls layouts env entries op (.scalar sc) env' →
      Nat.beq sc.sizeBytes 0 = false →
      intCastTargetBytes targetTy.kind = .some targetBytes →
      LiftLensRvalue localDecls layouts env entries
        (.cast .intToInt op targetTy)
        (.scalar ⟨match operandIsSigned localDecls op layouts with
          | false => wrapScalarBits sc.bits (scalarModulus targetBytes)
          | true =>
            match Nat.ble targetBytes sc.sizeBytes with
            | true => wrapScalarBits sc.bits (scalarModulus targetBytes)
            | false => signExtendBits sc.bits sc.sizeBytes targetBytes,
          targetBytes⟩)
        env'
  | tuple_nil
      {env : PureEnv} {entries : List (RawPtrVal × Value)} :
      LiftLensRvalue localDecls layouts env entries
        (.aggregate .tuple []) (.aggregate 0 []) env
  | aggregate_tuple
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {ops : List Operand} {vals : List Value} :
      LiftLensOperands localDecls layouts env entries ops vals env' →
      LiftLensRvalue localDecls layouts env entries
        (.aggregate .tuple ops) (.aggregate 0 vals) env'
  | aggregate_adt
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {defPath : DefPath} {variantIdx : VariantIdx}
      {ops : List Operand} {vals : List Value} :
      LiftLensOperands localDecls layouts env entries ops vals env' →
      LiftLensRvalue localDecls layouts env entries
        (.aggregate (.adt defPath variantIdx .none) ops)
        (.aggregate variantIdx vals) env'

/--
Wrapping `Add` instance of `LiftLensRvalue.binaryOp` at any non-zero scalar
width, with either operand possibly a lens dereference read.
-/
theorem LiftLensRvalue.binaryOp_add
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env₁ env₂ : PureEnv} {entries : List (RawPtrVal × Value)}
    {lhsOp rhsOp : Operand} {a b sz : Nat}
    (hSz : sz ≠ 0)
    (hLhs : LiftLensOperandAny localDecls layouts env entries lhsOp (.scalar ⟨a, sz⟩) env₁)
    (hRhs : LiftLensOperandAny localDecls layouts env₁ entries rhsOp (.scalar ⟨b, sz⟩) env₂) :
    LiftLensRvalue localDecls layouts env entries
      (.binaryOp .add lhsOp rhsOp)
      (.scalar ⟨wrapScalarBits (Nat.add a b) (scalarModulus sz), sz⟩)
      env₂ := by
  refine .binaryOp hLhs hRhs (fun mem => ?_)
  have hZero : Nat.beq sz 0 = false := by
    cases sz with
    | zero => exact absurd rfl hSz
    | succ _ => rfl
  unfold evalScalarBinOp
  simp only [hZero, Nat.beq_refl]

/--
Variable-headed pure `StatementKind.retag` rule (`LiftRetag`) validating a
pointer local against the active lens table `entries`.
-/
inductive LiftRetag
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    PureEnv → List (RawPtrVal × Value) → Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | mk
      {env : PureEnv} {entries : List (RawPtrVal × Value)}
      {retagKind : RetagKind} {ptrLoc : Local} {rp : RawPtrVal} {v : Value} :
      get? env ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some v →
      LiftRetag localDecls layouts env entries
        { kind := .retag retagKind { local_ := ptrLoc, projection := [] }, span := _ }
        env entries

/--
Variable-headed pure dereference write rule (`LiftDerefWrite`) updating
`*ptrLoc` or `(*ptrLoc).fieldIdx` in the pure lens environment `entries` via
`updateLensVal`.
-/
inductive LiftDerefWrite
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    PureEnv → List (RawPtrVal × Value) → Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | mk
      {env env₁ : PureEnv} {entries : List (RawPtrVal × Value)}
      {ptrLoc : Local} {rv : Rvalue} {rp : RawPtrVal}
      {oldVal newVal : Value} :
      LiftLensRvalue localDecls layouts env entries rv newVal env₁ →
      get? env₁ ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some oldVal →
      LiftDerefWrite localDecls layouts env entries
        { kind := .assign { local_ := ptrLoc, projection := [.deref] } rv, span := _ }
        env₁ (updateLensVal entries rp newVal)
  | field
      {env env₁ : PureEnv} {entries : List (RawPtrVal × Value)}
      {ptrLoc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
      {rv : Rvalue} {rp : RawPtrVal}
      {oldAgg fieldVal newAgg : Value} :
      LiftLensRvalue localDecls layouts env entries rv fieldVal env₁ →
      get? env₁ ptrLoc = .some (.init rp.toMirValue) →
      lookupLensVal? entries rp = .some oldAgg →
      writeProjectedValue env₁ oldAgg [.field fieldIdx fieldTy] fieldVal =
        .ok newAgg →
      LiftDerefWrite localDecls layouts env entries
        { kind :=
            .assign
              { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
              rv,
          span := _ }
        env₁ (updateLensVal entries rp newAgg)

/--
Variable-headed pure local assignment rule (`LiftPureAssign`) writing to a root
local slot `dstLoc` in `env`.
-/
inductive LiftPureAssign
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    PureEnv → List (RawPtrVal × Value) → Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | mk
      {env env₁ env₂ : PureEnv} {entries : List (RawPtrVal × Value)}
      {dstLoc : Local} {rv : Rvalue} {val : Value} {oldSlot : LocalSlot} :
      LiftLensRvalue localDecls layouts env entries rv val env₁ →
      get? env₁ dstLoc = .some oldSlot →
      oldSlot ≠ .dead →
      set? env₁ dstLoc (.init val) = .some env₂ →
      LiftPureAssign localDecls layouts env entries
        { kind := .assign { local_ := dstLoc, projection := [] } rv, span := _ }
        env₂ entries

/-- Variable-headed pure `StatementKind.storageLive` rule. -/
inductive LiftStorageLive :
    PureEnv → List (RawPtrVal × Value) → Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | mk
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {loc : Local} {oldSlot : LocalSlot} :
      get? env loc = .some oldSlot →
      set? env loc .uninit = .some env' →
      LiftStorageLive env entries { kind := .storageLive loc, span := _ } env' entries

/-- Variable-headed pure `StatementKind.storageDead` rule. -/
inductive LiftStorageDead :
    PureEnv → List (RawPtrVal × Value) → Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | mk
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {loc : Local} {oldSlot : LocalSlot} :
      get? env loc = .some oldSlot →
      set? env loc .dead = .some env' →
      LiftStorageDead env entries { kind := .storageDead loc, span := _ } env' entries

/-- Variable-headed pure `StatementKind.nop` rule. -/
inductive LiftNop :
    PureEnv → List (RawPtrVal × Value) → Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | mk {env : PureEnv} {entries : List (RawPtrVal × Value)} :
      LiftNop env entries { kind := .nop, span := _ } env entries

/--
Unified single-statement pure lens-lifting judgment (`LiftLensStmt`).
-/
inductive LiftLensStmt
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    PureEnv → List (RawPtrVal × Value) → Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | retag {env env' entries entries' stmt} :
      LiftRetag localDecls layouts env entries stmt env' entries' →
      LiftLensStmt localDecls layouts env entries stmt env' entries'
  | derefWrite {env env' entries entries' stmt} :
      LiftDerefWrite localDecls layouts env entries stmt env' entries' →
      LiftLensStmt localDecls layouts env entries stmt env' entries'
  | pureAssign {env env' entries entries' stmt} :
      LiftPureAssign localDecls layouts env entries stmt env' entries' →
      LiftLensStmt localDecls layouts env entries stmt env' entries'
  | storageLive {env env' entries entries' stmt} :
      LiftStorageLive env entries stmt env' entries' →
      LiftLensStmt localDecls layouts env entries stmt env' entries'
  | storageDead {env env' entries entries' stmt} :
      LiftStorageDead env entries stmt env' entries' →
      LiftLensStmt localDecls layouts env entries stmt env' entries'
  | nop {env env' entries entries' stmt} :
      LiftNop env entries stmt env' entries' →
      LiftLensStmt localDecls layouts env entries stmt env' entries'

/--
Statement-list pure lens-lifting judgment (`LiftLensStmts`) threading
`(env, entries)` across a basic block's statement sequence.
-/
inductive LiftLensStmts
    (localDecls : List LocalDecl) (layouts : LayoutTable) :
    PureEnv → List (RawPtrVal × Value) → List Statement →
    PureEnv → List (RawPtrVal × Value) → Prop where
  | nil {env : PureEnv} {entries : List (RawPtrVal × Value)} :
      LiftLensStmts localDecls layouts env entries [] env entries
  | cons
      {env env₁ env₂ : PureEnv}
      {entries entries₁ entries₂ : List (RawPtrVal × Value)}
      {stmt : Statement} {rest : List Statement} :
      LiftLensStmt localDecls layouts env entries stmt env₁ entries₁ →
      LiftLensStmts localDecls layouts env₁ entries₁ rest env₂ entries₂ →
      LiftLensStmts localDecls layouts env entries (stmt :: rest) env₂ entries₂

/--
Scalar bit that an `assert` condition must produce for execution to continue
at the success target (`expected` encoded as `0` or `1`, matching
`evalTerminator`).
-/
def assertBit (expected : Bool) : Nat :=
  match expected with
  | true => 1
  | false => 0

/--
True when `phase` is an executable runtime MIR phase (`runtimePostCleanup` or
`runtimeOptimized`) accepted by `stepMirFn` (as opposed to `.other _`).
-/
def isRuntimeMirPhase : MirPhaseTag → Bool
  | .runtimePostCleanup => true
  | .runtimeOptimized => true
  | .other _ => false

theorem stepMirFn_of_isRuntimeMirPhase (body : CapturedMir)
    (bbIdx : BasicBlockIdx) (stmtIdx : Nat) (locals : PureEnv) (m : Memory)
    (hCallee : m.activeCallee = .none)
    (hPhase : isRuntimeMirPhase body.phase = true)
    {bb : BasicBlockData} (hBb : get? body.basicBlocks bbIdx = .some bb) :
    stepMirFn body
      { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }
        memory := m } =
      match get? bb.statements stmtIdx with
      | .some stmt =>
        evalStmt
          { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }
            memory := m }
          stmt body.localDecls body.layouts
      | .none =>
        if (stmtIdx == length bb.statements) = true then
          evalTerminator
            { frame := { blockIdx := bbIdx, stmtIdx := stmtIdx, locals := locals }
              memory := m }
            bb.terminator (.some body)
        else
          .fail .ub := by
  unfold stepMirFn
  change
    let currentBody := m.activeCallee.getD body
    _ = _
  rw [hCallee]
  dsimp only [Option.getD]
  cases hP : body.phase with
  | runtimePostCleanup => simp only [hBb]; rfl
  | runtimeOptimized => simp only [hBb]; rfl
  | other _ => rw [hP] at hPhase; nomatch hPhase

/--
Control-flow-graph lens-lifting judgment (`LiftLensBlock`): executing `body`
from basic block `bbIdx` with locals `env` and pure lens bindings `entries`
returns `retVal` (read from `_0`) with final lens bindings `entries'`.

Each constructor lifts the block's statements and then one terminator:
`return_` ends the derivation, `goto` continues at its target, `assert`
continues at its success target after its condition operand lifts to the
expected bit, `switchInt` continues at the target selected by
`lookupSwitchTarget` on the discriminant's bits, and `drop_local` marks a root
local slot `.uninit` and continues at its normal target. Derivations are finite,
so every lifted path is acyclic.
-/
inductive LiftLensBlock (body : CapturedMir) :
    BasicBlockIdx → PureEnv → List (RawPtrVal × Value) →
    Value → List (RawPtrVal × Value) → Prop where
  | return_
      {bbIdx : BasicBlockIdx} {bb : BasicBlockData} {env env' : PureEnv}
      {entries entries' : List (RawPtrVal × Value)} {retVal : Value} :
      isRuntimeMirPhase body.phase = true →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .return_ →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env' entries' →
      get? env' 0 = .some (.init retVal) →
      LiftLensBlock body bbIdx env entries retVal entries'
  | goto
      {bbIdx target : BasicBlockIdx} {bb : BasicBlockData} {env env₁ : PureEnv}
      {entries entries₁ entries' : List (RawPtrVal × Value)} {retVal : Value} :
      isRuntimeMirPhase body.phase = true →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .goto target →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env₁ entries₁ →
      LiftLensBlock body target env₁ entries₁ retVal entries' →
      LiftLensBlock body bbIdx env entries retVal entries'
  | assert
      {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
      {cond : Operand} {expected : Bool} {unwind : UnwindAction}
      {env env₁ env₂ : PureEnv} {sc : ScalarInt}
      {entries entries₁ entries' : List (RawPtrVal × Value)} {retVal : Value} :
      isRuntimeMirPhase body.phase = true →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .assert cond expected target unwind →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env₁ entries₁ →
      LiftLensOperandAny .nil body.layouts env₁ entries₁ cond (.scalar sc) env₂ →
      sc.bits = assertBit expected →
      LiftLensBlock body target env₂ entries₁ retVal entries' →
      LiftLensBlock body bbIdx env entries retVal entries'
  | switchInt
      {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
      {discr : Operand} {targets : SwitchTargets}
      {env env₁ env₂ : PureEnv} {sc : ScalarInt}
      {entries entries₁ entries' : List (RawPtrVal × Value)} {retVal : Value} :
      isRuntimeMirPhase body.phase = true →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .switchInt discr targets →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env₁ entries₁ →
      LiftLensOperandAny .nil body.layouts env₁ entries₁ discr (.scalar sc) env₂ →
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = target →
      LiftLensBlock body target env₂ entries₁ retVal entries' →
      LiftLensBlock body bbIdx env entries retVal entries'
  | drop_local
      {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
      {loc : Local} {unwind : UnwindAction} {oldSlot : LocalSlot}
      {env env₁ env₂ : PureEnv}
      {entries entries₁ entries' : List (RawPtrVal × Value)} {retVal : Value} :
      isRuntimeMirPhase body.phase = true →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind =
        .drop { local_ := loc, projection := [] } target unwind →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env₁ entries₁ →
      get? env₁ loc = .some oldSlot →
      oldSlot ≠ .dead →
      set? env₁ loc .uninit = .some env₂ →
      LiftLensBlock body target env₂ entries₁ retVal entries' →
      LiftLensBlock body bbIdx env entries retVal entries'

/-! ### Soundness of Operand, Rvalue, and Statement Lifting -/

theorem set?_length_eq {α : Type u} {xs ys : List α} {i : Nat} {v : α}
    (h : set? xs i v = .some ys) : ys.length = xs.length := by
  unfold set? at h
  split at h
  · injection h with hYs
    subst hYs
    exact List.length_set
  · nomatch h

theorem LiftLensOperand.evalOperand_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {op : Operand} {v : Value}
    (h : LiftLensOperand localDecls layouts env op v env')
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot) :
    evalOperand env op borrows globals layouts callerLocals localDecls = .ok v env' ∧
    env'.length = env.length := by
  cases h with
  | copy_local hGet =>
    refine ⟨?_, rfl⟩
    simp [evalOperand, hGet, readProjectedValue]
  | move_local hGet hSet =>
    refine ⟨?_, set?_length_eq hSet⟩
    simp [evalOperand, hGet, hSet]
  | copy_field hGet hNoUnion hRead =>
    refine ⟨?_, rfl⟩
    unfold evalOperand
    dsimp only
    rw [hGet, hNoUnion]
    dsimp only
    rw [hRead]
  | move_field hGet hNoUnion hRead =>
    refine ⟨?_, rfl⟩
    unfold evalOperand
    dsimp only
    rw [hGet, hNoUnion]
    dsimp only
    rw [hRead]
  | const_scalar =>
    exact ⟨rfl, rfl⟩
  | const_zeroSized =>
    exact ⟨rfl, rfl⟩

theorem LiftLensOperand.not_deref
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {op : Operand} {v : Value}
    (h : LiftLensOperand localDecls layouts env op v env')
    (borrows : List BorrowEntry) (m : Memory) :
    (match op, borrows with
    | .copy { local_ := ptrLoc, projection := .deref :: restProj },
      b₁ :: b₂ :: restBorrows =>
      RvalueEvalResult.ok v env'
        { m with
          borrows :=
            freezeDerefReadBorrowsAt env ptrLoc restProj
              (b₁ :: b₂ :: restBorrows) }
    | .move { local_ := ptrLoc, projection := .deref :: restProj },
      b₁ :: b₂ :: restBorrows =>
      RvalueEvalResult.ok v env'
        { m with
          borrows :=
            freezeDerefReadBorrowsAt env ptrLoc restProj
              (b₁ :: b₂ :: restBorrows) }
    | _, _ => RvalueEvalResult.ok v env' m) = .ok v env' m := by
  cases h <;> cases borrows <;> rfl

theorem LiftDerefRead.evalOperand_and_freeze_eq
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value} {m : Memory}
    (h : LiftDerefRead env entries op v env')
    (hInv : SepLensStateInv env.length entries m)
    (layouts : LayoutTable)
    (localDecls : List LocalDecl := .nil) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals localDecls = .ok v env' ∧
    env' = env ∧
    (∀ ptrLoc restProj,
      (op = .copy { local_ := ptrLoc, projection := .deref :: restProj } ∨
       op = .move { local_ := ptrLoc, projection := .deref :: restProj }) →
      freezeDerefReadBorrowsAt env ptrLoc restProj m.borrows = m.borrows) := by
  cases h with
  | copy_deref hGetPtr hLookVal =>
    rename_i ptrLoc rp
    have hMem := lookupLensVal?_mem hLookVal
    rcases hInv.entries_valid rp v hMem with
      ⟨hOff, hAbove, hCaller, ⟨_, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩, hExcl⟩⟩
    have hEnvNone : get? env entry.targetLocal = .none := by
      rw [hT]
      exact get?_eq_none_of_le hAbove
    refine ⟨?_, rfl, ?_⟩
    · cases localDecls <;>
      · unfold evalOperand
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        simp [ProvenancePtr.tag, hLookB, hPerm, hP]
        rw [hEnvNone, hT, hCaller]
        rfl
    · intro pLoc rProj hOpEq
      rcases hOpEq with hCopy | hMove
      · injection hCopy with hPlace
        injection hPlace with hLoc hProj
        injection hProj with _ hRest
        subst hLoc hRest
        unfold freezeDerefReadBorrowsAt
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        dsimp only [ProvenancePtr.tag]
        rw [hLookB]
        dsimp only
        rw [hT]
        exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
          m.borrows m.borrows _ _ _ hExcl
      · nomatch hMove
  | move_deref hGetPtr hLookVal =>
    rename_i ptrLoc rp
    have hMem := lookupLensVal?_mem hLookVal
    rcases hInv.entries_valid rp v hMem with
      ⟨hOff, hAbove, hCaller, ⟨_, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩, hExcl⟩⟩
    have hEnvNone : get? env entry.targetLocal = .none := by
      rw [hT]
      exact get?_eq_none_of_le hAbove
    refine ⟨?_, rfl, ?_⟩
    · cases localDecls <;>
      · unfold evalOperand
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        simp [ProvenancePtr.tag, hLookB, hPerm, hP]
        rw [hEnvNone, hT, hCaller]
        rfl
    · intro pLoc rProj hOpEq
      rcases hOpEq with hCopy | hMove
      · nomatch hCopy
      · injection hMove with hPlace
        injection hPlace with hLoc hProj
        injection hProj with _ hRest
        subst hLoc hRest
        unfold freezeDerefReadBorrowsAt
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        dsimp only [ProvenancePtr.tag]
        rw [hLookB]
        dsimp only
        rw [hT]
        exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
          m.borrows m.borrows _ _ _ hExcl

theorem LiftDerefFieldRead.evalOperand_and_freeze_eq
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value} {m : Memory}
    (h : LiftDerefFieldRead env entries op v env')
    (hInv : SepLensStateInv env.length entries m)
    (layouts : LayoutTable)
    (localDecls : List LocalDecl := .nil) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals localDecls = .ok v env' ∧
    env' = env ∧
    (∀ ptrLoc restProj,
      (op = .copy { local_ := ptrLoc, projection := .deref :: restProj } ∨
       op = .move { local_ := ptrLoc, projection := .deref :: restProj }) →
      freezeDerefReadBorrowsAt env ptrLoc restProj m.borrows = m.borrows) := by
  cases h with
  | copy_deref_field hGetPtr hLookVal hRead =>
    rename_i ptrLoc fieldIdx fieldTy rp aggVal
    have hMem := lookupLensVal?_mem hLookVal
    rcases hInv.entries_valid rp aggVal hMem with
      ⟨hOff, hAbove, hCaller, ⟨_, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩, hExcl⟩⟩
    have hEnvNone : get? env entry.targetLocal = .none := by
      rw [hT]
      exact get?_eq_none_of_le hAbove
    refine ⟨?_, rfl, ?_⟩
    · cases localDecls <;>
      · unfold evalOperand
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        simp [ProvenancePtr.tag, hLookB, hPerm, hP]
        rw [hEnvNone, hT, hCaller]
        dsimp only
        rw [hRead]
    · intro pLoc rProj hOpEq
      rcases hOpEq with hCopy | hMove
      · injection hCopy with hPlace
        injection hPlace with hLoc hProj
        injection hProj with _ hRest
        subst hLoc hRest
        unfold freezeDerefReadBorrowsAt
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        dsimp only [ProvenancePtr.tag]
        rw [hLookB]
        dsimp only
        rw [hT]
        exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
          m.borrows m.borrows _ _ _ hExcl
      · nomatch hMove
  | move_deref_field hGetPtr hLookVal hRead =>
    rename_i ptrLoc fieldIdx fieldTy rp aggVal
    have hMem := lookupLensVal?_mem hLookVal
    rcases hInv.entries_valid rp aggVal hMem with
      ⟨hOff, hAbove, hCaller, ⟨_, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩, hExcl⟩⟩
    have hEnvNone : get? env entry.targetLocal = .none := by
      rw [hT]
      exact get?_eq_none_of_le hAbove
    refine ⟨?_, rfl, ?_⟩
    · cases localDecls <;>
      · unfold evalOperand
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        simp [ProvenancePtr.tag, hLookB, hPerm, hP]
        rw [hEnvNone, hT, hCaller]
        dsimp only
        rw [hRead]
    · intro pLoc rProj hOpEq
      rcases hOpEq with hCopy | hMove
      · nomatch hCopy
      · injection hMove with hPlace
        injection hPlace with hLoc hProj
        injection hProj with _ hRest
        subst hLoc hRest
        unfold freezeDerefReadBorrowsAt
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        dsimp only [ProvenancePtr.tag]
        rw [hLookB]
        dsimp only
        rw [hT]
        exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
          m.borrows m.borrows _ _ _ hExcl

/--
Soundness of unified operand lifting: under `SepLensStateInv`, the lifted
operand evaluates to its lifted value against the real borrow table, globals,
and caller locals, without changing the local environment's length.
-/
theorem LiftLensOperandAny.evalOperand_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value} {m : Memory}
    (h : LiftLensOperandAny localDecls layouts env entries op v env')
    (hInv : SepLensStateInv env.length entries m) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals localDecls = .ok v env' ∧
    env'.length = env.length := by
  cases h with
  | pure hOp => exact hOp.evalOperand_eq m.borrows m.globals m.callerLocals
  | deref hDeref =>
    rcases hDeref.evalOperand_and_freeze_eq hInv layouts localDecls with ⟨hEval, hEnvEq, _⟩
    subst hEnvEq
    exact ⟨hEval, rfl⟩
  | deref_field hField =>
    rcases hField.evalOperand_and_freeze_eq hInv layouts localDecls with ⟨hEval, hEnvEq, _⟩
    subst hEnvEq
    exact ⟨hEval, rfl⟩

theorem LiftLensOperands.evalOperands_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {ops : List Operand} {vs : List Value} {m : Memory}
    (h : LiftLensOperands localDecls layouts env entries ops vs env')
    (hInv : SepLensStateInv env.length entries m) :
    evalOperands env ops m.borrows m.globals layouts m.callerLocals localDecls = .ok vs env' ∧
    env'.length = env.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hOp _ ih =>
    rcases hOp.evalOperand_eq hInv with ⟨hEval₁, hLen₁⟩
    rcases ih (by rw [hLen₁]; exact hInv) with ⟨hEval₂, hLen₂⟩
    refine ⟨?_, hLen₂.trans hLen₁⟩
    unfold evalOperands
    rw [hEval₁]
    dsimp only
    rw [hEval₂]

theorem LiftLensRvalue.evalRvalue_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {rv : Rvalue} {v : Value} {m : Memory}
    (h : LiftLensRvalue localDecls layouts env entries rv v env')
    (hInv : SepLensStateInv env.length entries m) :
    evalRvalue env rv m localDecls layouts = .ok v env' m ∧
    env'.length = env.length := by
  cases h with
  | use_pure hOp hVal =>
    rcases hOp.evalOperand_eq m.borrows m.globals m.callerLocals with
      ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    simp only [hEval]
    rw [hVal]
    dsimp only
    exact hOp.not_deref m.borrows m
  | use_deref hDeref hVal =>
    rcases hDeref.evalOperand_and_freeze_eq hInv layouts localDecls with
      ⟨hEval, hEnvEq, hFreeze⟩
    subst hEnvEq
    refine ⟨?_, rfl⟩
    unfold evalRvalue
    simp only [hEval]
    rw [hVal]
    dsimp only
    cases hDeref with
    | copy_deref _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ [] (Or.inl rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
    | move_deref _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ [] (Or.inr rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
  | use_deref_field hField hVal =>
    rcases hField.evalOperand_and_freeze_eq hInv layouts localDecls with
      ⟨hEval, hEnvEq, hFreeze⟩
    subst hEnvEq
    refine ⟨?_, rfl⟩
    unfold evalRvalue
    simp only [hEval]
    rw [hVal]
    dsimp only
    cases hField with
    | copy_deref_field _ _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ _ (Or.inl rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
    | move_deref_field _ _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ _ (Or.inr rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
  | copyForDeref_deref hGetPtr hLookVal =>
    have hDeref :
        LiftDerefRead env entries
          (.copy { local_ := _, projection := [.deref] }) v env :=
      .copy_deref hGetPtr hLookVal
    rcases hDeref.evalOperand_and_freeze_eq hInv layouts localDecls with
      ⟨hEval, _, hFreeze⟩
    refine ⟨?_, rfl⟩
    unfold evalRvalue
    simp [hEval]
    cases hB : m.borrows with
    | nil => rfl
    | cons b₁ tl =>
      cases tl with
      | nil => rfl
      | cons b₂ rest =>
        have hFr := hFreeze _ [] (Or.inl rfl)
        rw [hB] at hFr
        dsimp only
        rw [hFr, ← hB]
  | binaryOp hLhs hRhs hEvalOp =>
    rcases hLhs.evalOperand_eq hInv with ⟨hEval₁, hLen₁⟩
    rcases hRhs.evalOperand_eq (by rw [hLen₁]; exact hInv) with
      ⟨hEval₂, hLen₂⟩
    refine ⟨?_, hLen₂.trans hLen₁⟩
    unfold evalRvalue
    dsimp only
    rw [hEval₁]
    dsimp only
    rw [hEval₂]
    dsimp only
    split
    · have hBad := hEvalOp m
      unfold evalScalarBinOp at hBad
      repeat' split at hBad
      all_goals contradiction
    · exact hEvalOp m
  | unaryOp_not hOp hNot =>
    rcases hOp.evalOperand_eq hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    exact hNot m
  | unaryOp_neg hOp hSz =>
    rcases hOp.evalOperand_eq hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    dsimp only
    rw [hSz]
  | cast_intToInt hOp hSz hTarget =>
    rcases hOp.evalOperand_eq hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    dsimp only
    rw [hSz, hTarget]
    rfl
  | tuple_nil =>
    exact ⟨rfl, rfl⟩
  | aggregate_tuple hOps =>
    rcases hOps.evalOperands_eq hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
  | aggregate_adt hOps =>
    rcases hOps.evalOperands_eq hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue evalAggregateAdt
    dsimp only
    rw [hEval]

theorem SepLensStateInv.updateDeref
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp : RawPtrVal} {oldVal newVal : Value}
    (hInv : SepLensStateInv frameLen entries m)
    (hLook : lookupLensVal? entries rp = .some oldVal) :
    SepLensStateInv frameLen (updateLensVal entries rp newVal)
      { m with callerLocals := m.callerLocals.set rp.allocId (.init newVal) } where
  callStack_nil := hInv.callStack_nil
  activeCallee_none := hInv.activeCallee_none
  borrows_above_frame := hInv.borrows_above_frame
  entries_valid k v hMemNew := by
    have hMemRp : (rp, oldVal) ∈ entries := lookupLensVal?_mem hLook
    rcases hInv.entries_valid rp oldVal hMemRp with
      ⟨hOffRp, hAboveRp, hCallerRp, hExclRp⟩
    have hLtRp : rp.allocId < m.callerLocals.length :=
      (List.getElem?_eq_some_iff.mp hCallerRp).1
    rcases mem_updateLensVal_raw hInv.pairwise_disjoint hMemNew with
      ⟨rfl, rfl⟩ | ⟨hNe, hMemOld⟩
    · refine ⟨hOffRp, hAboveRp, ?_,
        TreeExclusiveBorrow.of_borrows_eq hExclRp rfl⟩
      unfold get?
      exact List.getElem?_set_self hLtRp
    · rcases hInv.entries_valid k v hMemOld with
        ⟨hOffK, hAboveK, hCallerK, hExclK⟩
      have hDisj :=
        pairwise_disjoint_of_mem_ne hInv.pairwise_disjoint hMemRp hMemOld hNe
      refine ⟨hOffK, hAboveK, ?_,
        TreeExclusiveBorrow.of_borrows_eq hExclK rfl⟩
      unfold get? at hCallerK ⊢
      rw [List.getElem?_set_ne hDisj.1.symm]
      exact hCallerK
  pairwise_disjoint := by
    rw [updateLensVal_map_fst]
    exact hInv.pairwise_disjoint

private theorem hasProtectedWriteConflict_singleton_eq_false
    {b₁ entry : BorrowEntry} {tag : Nat}
    {activeProtectors : List Nat} {targetLocal : Local}
    {proj : List ProjectionElem} {off len : Nat}
    (hLook : lookupBorrow [b₁] tag = .some entry) :
    hasProtectedWriteConflict [b₁] activeProtectors targetLocal (.some tag)
      proj off len = false := by
  rcases lookupBorrow_mem_and_tag hLook with ⟨hMem, hTag⟩
  rcases List.mem_singleton.mp hMem with rfl
  unfold hasProtectedWriteConflict borrowEntryWriteConflicts
  simp [hTag]
  rfl

/--
Explicit-memory soundness of projected dereference field writes
`((*ptrLoc).fieldIdx) = rv` (`LiftDerefWrite.field`): under `SepLensStateInv`,
`evalStmt` steps to the memory whose caller slot `rp.allocId` holds `newAgg`.
-/
theorem LiftDerefWrite.evalStmt_field_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {ptrLoc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {rv : Rvalue} {sp : String} {rp : RawPtrVal}
    {oldAgg fieldVal newAgg : Value} {s : MachineState}
    (hRv : LiftLensRvalue localDecls layouts env entries rv fieldVal env')
    (hGetPtr : get? env' ptrLoc = .some (.init rp.toMirValue))
    (hLookVal : lookupLensVal? entries rp = .some oldAgg)
    (hWriteProj :
      writeProjectedValue env' oldAgg [.field fieldIdx fieldTy] fieldVal =
        .ok newAgg)
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory) :
    env'.length = env.length ∧
    evalStmt s
      { kind :=
          .assign
            { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
            rv,
        span := sp }
      localDecls layouts =
      MirStepNode.step (advanceStmt s env'
        { s.memory with
          callerLocals :=
            s.memory.callerLocals.set rp.allocId (.init newAgg) }) := by
  rcases hRv.evalRvalue_eq hInv with ⟨hEvalRv, hLen₁⟩
  have hMem := lookupLensVal?_mem hLookVal
  rcases hInv.entries_valid rp oldAgg hMem with
    ⟨hOff, hAbove, hCaller, hExcl⟩
  rcases hExcl.lookup_active with
    ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩
  have hEnv₁None : get? env' entry.targetLocal = .none := by
    rw [hT]
    exact get?_eq_none_of_le (by rw [hLen₁]; exact hAbove)
  have hWriteLocalUb :
      writePlaceValue
        env'
        s.memory.borrows
        { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
        fieldVal
        localDecls
        layouts = .ub := by
    unfold writePlaceValue
    simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
      _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
    cases localDecls with
    | nil =>
      simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hP]
      rw [hEnv₁None]
    | cons _ _ =>
      simp only [hGetPtr, ProvenancePtr.tag, hLookB, hPerm]
      unfold writeStackThinPtrTypedDeref
      dsimp only
      rw [hEnv₁None]
      split <;> rfl
  have hEvalPlaceWriteUb :
      evalPlaceWrite
        env'
        s.memory.borrows
        { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
        fieldVal
        s.memory.activeProtectors
        localDecls
        layouts = .ub := by
    unfold evalPlaceWrite
    cases s.memory.activeProtectors with
    | nil => exact hWriteLocalUb
    | cons pHead pTail =>
      dsimp only
      rw [hWriteLocalUb]
      split <;> rfl
  have hLtCaller : rp.allocId < s.memory.callerLocals.length :=
    (List.getElem?_eq_some_iff.mp hCaller).1
  have hSetCaller :
      set? s.memory.callerLocals rp.allocId (.init newAgg) =
        .some (s.memory.callerLocals.set rp.allocId (.init newAgg)) := by
    unfold set?
    simp [hLtCaller]
  have hWriteCallerOk :
      writeCallerPlaceValue
        env'
        s.memory.callerLocals
        s.memory.borrows
        { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
        fieldVal =
        .ok (s.memory.callerLocals.set rp.allocId (.init newAgg)) := by
    unfold writeCallerPlaceValue
    simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
      _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
    simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hEnv₁None, hP]
    rw [hT, hCaller]
    dsimp only
    rw [hWriteProj]
    dsimp only
    rw [hSetCaller]
  have hEvalCallerOk :
      evalCallerPlaceWrite
        env'
        s.memory.callerLocals
        s.memory.borrows
        { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
        fieldVal
        s.memory.activeProtectors =
        .ok (s.memory.callerLocals.set rp.allocId (.init newAgg)) := by
    unfold evalCallerPlaceWrite
    cases s.memory.activeProtectors with
    | nil => exact hWriteCallerOk
    | cons pHead pTail =>
      simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
        _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
      rw [hGetPtr]
      dsimp only [ProvenancePtr.tag]
      rw [hLookB]
      cases hB : s.memory.borrows with
      | nil =>
        have hLookNil := hLookB
        rw [hB] at hLookNil
        nomatch hLookNil
      | cons b₁ tl =>
        cases tl with
        | nil =>
          have hLookSingle := hLookB
          rw [hB] at hLookSingle
          dsimp only
          rw [hasProtectedWriteConflict_singleton_eq_false hLookSingle]
          dsimp only
          rw [← hB]
          exact hWriteCallerOk
        | cons b₂ rest =>
          dsimp only
          rw [resolveDerefWriteFullProj_nil_field hP]
          have hNoConflict :
              hasProtectedTreeWriteConflict
                (b₁ :: b₂ :: rest)
                (b₁ :: b₂ :: rest)
                (pHead :: pTail)
                entry.targetLocal
                (.some rp.tag)
                [.field fieldIdx fieldTy]
                entry.rangeOffset
                entry.rangeLen = false := by
            rw [hT, ← hB]
            exact hasProtectedTreeWriteConflict_eq_false_of_tree
              s.memory.borrows s.memory.borrows (pHead :: pTail) _ _ _
              hExcl.ancestors_active_or_disabled
          rw [hNoConflict]
          dsimp only
          rw [← hB]
          exact hWriteCallerOk
  have hInvalEq :
      invalidateDerefWriteBorrows
        env'
        s.memory.borrows
        { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
        [.field fieldIdx fieldTy]
        s.memory.callerLocals = s.memory.borrows := by
    unfold invalidateDerefWriteBorrows
    simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
      _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
    cases hB : s.memory.borrows with
    | nil => rfl
    | cons b₁ tl =>
      cases tl with
      | nil =>
        have hLookSingle := hLookB
        rw [hB] at hLookSingle
        rw [hGetPtr]
        dsimp only [ProvenancePtr.tag]
        rw [hLookSingle]
        dsimp only
        rw [resolveDerefWriteFullProj_nil_field hP]
        dsimp only
        have hExclSingle :
            ∀ b ∈ [b₁],
              b.targetLocal = rp.allocId →
                (b.tag = rp.tag ∧ b.perm = .active) ∨
                b.perm = .disabled := by
          intro b hb _
          rcases lookupBorrow_mem_and_tag hLookSingle with ⟨hMemE, hTagE⟩
          have hbEq : b = b₁ := List.mem_singleton.mp hb
          have heEq : entry = b₁ := List.mem_singleton.mp hMemE
          subst hbEq
          rw [← heEq]
          exact Or.inl ⟨hTagE, hPerm⟩
        rw [hT]
        exact invalidateConflictingBorrowsAtProj_eq_self_of_exclusive
          _ _ _ hExclSingle
      | cons b₂ rest =>
        have hLookMany := hLookB
        rw [hB] at hLookMany
        rw [hGetPtr]
        dsimp only [ProvenancePtr.tag]
        rw [hLookMany]
        dsimp only
        rw [resolveDerefWriteFullProj_nil_field hP, hT, ← hB]
        exact invalidateTreeBorrowsAtProj_eq_self_of_tree
          s.memory.borrows s.memory.borrows _ _ _
          hExcl.ancestors_active_or_disabled
  refine ⟨hLen₁, ?_⟩
  unfold evalStmt
  dsimp only
  rw [hEnv, hEvalRv]
  dsimp only
  rw [hEvalPlaceWriteUb]
  dsimp only
  cases hCL : s.memory.callerLocals with
  | nil => rw [hCL] at hCaller; nomatch hCaller
  | cons cHead cTail =>
    dsimp only
    rw [← hCL, hEvalCallerOk, hInvalEq]

/--
Explicit-memory soundness of `LiftDerefWrite`: under `SepLensStateInv`, the
lifted assignment `*p = rv` steps `evalStmt` to the memory whose caller slot
`rp.allocId` holds the new value, leaving the borrow table and every other
`Memory` field unchanged, and updates the lens state by `updateLensVal`.
-/
theorem LiftDerefWrite.evalStmt_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState}
    (hWrite : LiftDerefWrite localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory) :
    ∃ (rp : RawPtrVal) (oldVal newVal : Value),
      lookupLensVal? entries rp = .some oldVal ∧
      entries' = updateLensVal entries rp newVal ∧
      env'.length = env.length ∧
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env'
          { s.memory with
            callerLocals :=
              s.memory.callerLocals.set rp.allocId (.init newVal) }) := by
  cases hWrite with
  | mk hRv hGetPtr hLookVal =>
    rename_i _ ptrLoc rv rp oldVal newVal
    rcases hRv.evalRvalue_eq hInv with ⟨hEvalRv, hLen₁⟩
    have hMem := lookupLensVal?_mem hLookVal
    rcases hInv.entries_valid rp oldVal hMem with
      ⟨hOff, hAbove, hCaller, hExcl⟩
    rcases hExcl.lookup_active with
      ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩
    have hEnv₁None : get? env' entry.targetLocal = .none := by
      rw [hT]
      exact get?_eq_none_of_le (by rw [hLen₁]; exact hAbove)
    have hWriteLocalUb :
        writePlaceValue
          env'
          s.memory.borrows
          { local_ := ptrLoc, projection := [.deref] }
          newVal
          localDecls
          layouts = .ub := by
      unfold writePlaceValue
      simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
      cases localDecls with
      | nil =>
        simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hP]
        rw [hEnv₁None]
      | cons _ _ =>
        simp only [hGetPtr, ProvenancePtr.tag, hLookB, hPerm]
        unfold writeStackThinPtrTypedDeref
        dsimp only
        rw [hEnv₁None]
        split
        · rfl
        · cases newVal <;> rfl
    have hEvalPlaceWriteUb :
        evalPlaceWrite
          env'
          s.memory.borrows
          { local_ := ptrLoc, projection := [.deref] }
          newVal
          s.memory.activeProtectors
          localDecls
          layouts = .ub := by
      unfold evalPlaceWrite
      cases s.memory.activeProtectors with
      | nil => exact hWriteLocalUb
      | cons pHead pTail =>
        dsimp only
        rw [hWriteLocalUb]
        split <;> rfl
    have hLtCaller : rp.allocId < s.memory.callerLocals.length :=
      (List.getElem?_eq_some_iff.mp hCaller).1
    have hSetCaller :
        set? s.memory.callerLocals rp.allocId (.init newVal) =
          .some (s.memory.callerLocals.set rp.allocId (.init newVal)) := by
      unfold set?
      simp [hLtCaller]
    have hWriteCallerOk :
        writeCallerPlaceValue
          env'
          s.memory.callerLocals
          s.memory.borrows
          { local_ := ptrLoc, projection := [.deref] }
          newVal =
          .ok (s.memory.callerLocals.set rp.allocId (.init newVal)) := by
      unfold writeCallerPlaceValue
      simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
      simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hEnv₁None, hP]
      rw [hT, hCaller, hSetCaller]
    have hEvalCallerOk :
        evalCallerPlaceWrite
          env'
          s.memory.callerLocals
          s.memory.borrows
          { local_ := ptrLoc, projection := [.deref] }
          newVal
          s.memory.activeProtectors =
          .ok (s.memory.callerLocals.set rp.allocId (.init newVal)) := by
      unfold evalCallerPlaceWrite
      cases s.memory.activeProtectors with
      | nil => exact hWriteCallerOk
      | cons pHead pTail =>
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        rw [hGetPtr]
        dsimp only [ProvenancePtr.tag]
        rw [hLookB]
        cases hB : s.memory.borrows with
        | nil =>
          have hLookNil := hLookB
          rw [hB] at hLookNil
          nomatch hLookNil
        | cons b₁ tl =>
          cases tl with
          | nil =>
            have hLookSingle := hLookB
            rw [hB] at hLookSingle
            dsimp only
            rw [hasProtectedWriteConflict_singleton_eq_false hLookSingle]
            dsimp only
            rw [← hB]
            exact hWriteCallerOk
          | cons b₂ rest =>
            dsimp only
            rw [resolveDerefWriteFullProj_nil_nil hP]
            have hNoConflict :
                hasProtectedTreeWriteConflict
                  (b₁ :: b₂ :: rest)
                  (b₁ :: b₂ :: rest)
                  (pHead :: pTail)
                  entry.targetLocal
                  (.some rp.tag)
                  []
                  entry.rangeOffset
                  entry.rangeLen = false := by
              rw [hT, ← hB]
              exact hasProtectedTreeWriteConflict_eq_false_of_tree
                s.memory.borrows s.memory.borrows (pHead :: pTail) _ _ _
                hExcl.ancestors_active_or_disabled
            rw [hNoConflict]
            dsimp only
            rw [← hB]
            exact hWriteCallerOk
    have hInvalEq :
        invalidateDerefWriteBorrows
          env'
          s.memory.borrows
          { local_ := ptrLoc, projection := [.deref] }
          []
          s.memory.callerLocals = s.memory.borrows := by
      unfold invalidateDerefWriteBorrows
      simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
      cases hB : s.memory.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil =>
          have hLookSingle := hLookB
          rw [hB] at hLookSingle
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookSingle]
          dsimp only
          rw [resolveDerefWriteFullProj_nil_nil hP, hRL]
          dsimp only
          -- With a single borrow-table entry, `lookupBorrow` forces that
          -- entry to be `rp.tag`'s own active whole-allocation entry, so the
          -- non-tree `invalidateConflictingBorrows` path is the identity.
          have hExclSingle :
              ∀ b ∈ [b₁],
                b.targetLocal = rp.allocId →
                  (b.tag = rp.tag ∧
                    b.perm = .active ∧
                    b.targetProjection = [] ∧
                    b.rangeOffset = 0 ∧
                    b.rangeLen = 0) ∨
                  b.perm = .disabled := by
            intro b hb _
            rcases lookupBorrow_mem_and_tag hLookSingle with ⟨hMemE, hTagE⟩
            have hbEq : b = b₁ := List.mem_singleton.mp hb
            have heEq : entry = b₁ := List.mem_singleton.mp hMemE
            subst hbEq
            rw [← heEq]
            exact Or.inl ⟨hTagE, hPerm, hP, hRO, hRL⟩
          rw [hT]
          exact invalidateConflictingBorrows_eq_self_of_exclusive hExclSingle
        | cons b₂ rest =>
          have hLookMany := hLookB
          rw [hB] at hLookMany
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookMany]
          dsimp only
          rw [resolveDerefWriteFullProj_nil_nil hP, hT, ← hB]
          exact invalidateTreeBorrowsAtProj_eq_self_of_tree
            s.memory.borrows s.memory.borrows _ _ _
            hExcl.ancestors_active_or_disabled
    refine ⟨rp, oldVal, newVal, hLookVal, rfl, hLen₁, ?_⟩
    unfold evalStmt
    dsimp only
    rw [hEnv, hEvalRv]
    dsimp only
    rw [hEvalPlaceWriteUb]
    dsimp only
    cases hCL : s.memory.callerLocals with
    | nil => rw [hCL] at hCaller; nomatch hCaller
    | cons cHead cTail =>
      dsimp only
      rw [← hCL, hEvalCallerOk, hInvalEq]
  | field hRv hGetPtr hLookVal hWriteProj =>
    rcases LiftDerefWrite.evalStmt_field_eq
        hRv hGetPtr hLookVal hWriteProj hEnv hInv with
      ⟨hLen₁, hStep⟩
    exact ⟨_, _, _, hLookVal, rfl, hLen₁, hStep⟩

theorem LiftLensStmt.evalStmt_step
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries₀ entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState} {m₀ : Memory}
    (hStmt : LiftLensStmt localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory)
    (hFrame : LensFramePreserved entries₀ m₀ s.memory)
    (hKeys : entries.map Prod.fst = entries₀.map Prod.fst) :
    ∃ m' : Memory,
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env' m') ∧
      env'.length = env.length ∧
      SepLensStateInv env'.length entries' m' ∧
      LensFramePreserved entries₀ m₀ m' ∧
      entries'.map Prod.fst = entries₀.map Prod.fst := by
  cases hStmt with
  | retag hRetag =>
    cases hRetag with
    | mk hGetPtr hLookVal =>
      rename_i _ retagKind ptrLoc rp v
      have hMem := lookupLensVal?_mem hLookVal
      rcases hInv.entries_valid rp v hMem with
        ⟨hOff, _, _, ⟨_, ⟨entry, hLookB, _, _, hPerm, _, _⟩, _⟩⟩
      unfold evalStmt
      simp [hEnv, evalOperand, readProjectedValue, hGetPtr, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr, ProvenancePtr.tag]
      rw [hLookB]
      dsimp only
      rw [hPerm]
      dsimp only
      cases retagKind <;>
        (try exact ⟨s.memory, rfl, hInv, hFrame, hKeys⟩)
      · refine ⟨{
          s.memory with
          borrows :=
            attachBorrowProtector s.memory.borrows rp.tag s.memory.nextProtector
          activeProtectors :=
            s.memory.nextProtector :: s.memory.activeProtectors
          nextProtector := Nat.add s.memory.nextProtector 1
        }, rfl, hInv.attachProtector rp.tag s.memory.nextProtector, ?_, hKeys⟩
        refine ⟨hFrame.locals_unchanged_outside, fun q hOut => ?_⟩
        have hRpInFst : rp ∈ entries.map Prod.fst :=
          List.mem_map.mpr ⟨(rp, v), hMem, rfl⟩
        rw [hKeys] at hRpInFst
        rcases List.mem_map.mp hRpInFst with ⟨⟨k₀, v₀⟩, hMem₀, hK₀⟩
        dsimp only at hK₀
        subst k₀
        have hTagNe : rp.tag ≠ q := by
          intro hEq
          subst hEq
          exact hOut (rp, v₀) hMem₀ rfl
        rw [lookupBorrow_attachBorrowProtector_ne _ _ _ _ hTagNe]
        exact hFrame.borrows_unchanged_outside q hOut
  | derefWrite hWrite =>
    rcases hWrite.evalStmt_eq hEnv hInv with
      ⟨rp, oldVal, newVal, hLookVal, rfl, hLen₁, hEvalStmt⟩
    have hMem := lookupLensVal?_mem hLookVal
    refine ⟨
      { s.memory with
        callerLocals := s.memory.callerLocals.set rp.allocId (.init newVal) },
      hEvalStmt, hLen₁,
      (by rw [hLen₁]; exact hInv.updateDeref hLookVal),
      ?_,
      (updateLensVal_map_fst entries rp newVal).trans hKeys⟩
    · refine ⟨fun allocId hOut => ?_, hFrame.borrows_unchanged_outside⟩
      have hRpInFst : rp ∈ entries.map Prod.fst :=
        List.mem_map.mpr ⟨(rp, oldVal), hMem, rfl⟩
      rw [hKeys] at hRpInFst
      rcases List.mem_map.mp hRpInFst with ⟨⟨k₀, v₀⟩, hMem₀, hK₀⟩
      dsimp only at hK₀
      subst k₀
      have hAllocNe : allocId ≠ rp.allocId := hOut (rp, v₀) hMem₀
      unfold get?
      rw [List.getElem?_set_ne hAllocNe.symm]
      exact hFrame.locals_unchanged_outside allocId hOut
  | pureAssign hPure =>
    cases hPure with
    | mk hRv hGetDst hNotDead hSetDst =>
      rename_i _ env1_ dstLoc_ rv val oldSlot
      rcases hRv.evalRvalue_eq hInv with ⟨hEvalRv, hLen₁⟩
      have hLen₂ : env'.length = env1_.length := set?_length_eq hSetDst
      have hLtFrame : dstLoc_ < env.length := by
        rw [← hLen₁]
        exact (List.getElem?_eq_some_iff.mp hGetDst).1
      have hInval :
          invalidateConflictingBorrows s.memory.borrows dstLoc_ .none =
            s.memory.borrows :=
        invalidateConflictingBorrows_eq_self_of_lt_frame
          hInv.borrows_above_frame hLtFrame
      refine ⟨s.memory, ?_, hLen₂.trans hLen₁,
        (by rw [hLen₂, hLen₁]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      dsimp only
      rw [hEnv, hEvalRv]
      dsimp only
      rw [hGetDst]
      cases oldSlot with
      | dead => exact absurd rfl hNotDead
      | uninit =>
        dsimp only
        rw [hSetDst]
        dsimp only
        cases hAP : s.memory.activeProtectors with
        | nil => simp [hInval, ← hAP]
        | cons pHead pTail =>
          dsimp only
          rw [hasProtectedWriteConflict_eq_false_of_lt_frame
            (pHead :: pTail) hInv.borrows_above_frame hLtFrame]
          simp [hInval, ← hAP]
      | init _ =>
        dsimp only
        rw [hSetDst]
        dsimp only
        cases hAP : s.memory.activeProtectors with
        | nil => simp [hInval, ← hAP]
        | cons pHead pTail =>
          dsimp only
          rw [hasProtectedWriteConflict_eq_false_of_lt_frame
            (pHead :: pTail) hInv.borrows_above_frame hLtFrame]
          simp [hInval, ← hAP]
  | storageLive hLive =>
    cases hLive with
    | mk hGet hSet =>
      have hLen : env'.length = env.length := set?_length_eq hSet
      have hNe := targetLocal_ne_of_lt_frame hInv.borrows_above_frame hGet
      have hDisable := disableLocalBorrows_eq_self_of_forall_ne _ _ hNe
      have hProt := fun ap => hasProtectedLocalBorrow_eq_false_of_forall_ne _ ap _ hNe
      refine ⟨s.memory, ?_, hLen, (by rw [hLen]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      cases hAP : s.memory.activeProtectors with
      | nil => simp [hEnv, hGet, hSet, hDisable]
      | cons pHead pTail => simp [hEnv, hGet, hSet, hDisable, hProt, ← hAP]
  | storageDead hDead =>
    cases hDead with
    | mk hGet hSet =>
      have hLen : env'.length = env.length := set?_length_eq hSet
      have hNe := targetLocal_ne_of_lt_frame hInv.borrows_above_frame hGet
      have hDisable := disableLocalBorrows_eq_self_of_forall_ne _ _ hNe
      have hProt := fun ap => hasProtectedLocalBorrow_eq_false_of_forall_ne _ ap _ hNe
      refine ⟨s.memory, ?_, hLen, (by rw [hLen]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      cases hAP : s.memory.activeProtectors with
      | nil => simp [hEnv, hGet, hSet, hDisable]
      | cons pHead pTail => simp [hEnv, hGet, hSet, hDisable, hProt, ← hAP]
  | nop hNop =>
    cases hNop with
    | mk =>
      refine ⟨s.memory, ?_, rfl, hInv, hFrame, hKeys⟩
      unfold evalStmt
      simp [hEnv]

/-! ### Fuel-Free `MirWpConverges` Soundness (`mirWpConverges_of_sepLenses`) -/

/--
Statement-sequence soundness in continuation form: if the remaining statements
`stmts` of block `bbIdx` lift from `(env, entries)` to `(env', entries')`, then
execution reaches the block's terminator (`stmtIdx = bb.statements.length`)
with locals `env'` and a memory satisfying the invariant, the frame relation,
and the key invariant; any continuation established there extends to the
current statement.
-/
theorem mirWpConverges_of_liftLensStmts
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    {stmts : List Statement}
    {env env' : PureEnv}
    {entries₀ entries entries' : List (RawPtrVal × Value)}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hStmts :
      LiftLensStmts body.localDecls body.layouts
        env entries stmts env' entries') :
    ∀ (prefixStmts : List Statement) (m₀ m : Memory)
      (Φ : MirOutcome → Prop),
      bb.statements = prefixStmts ++ stmts →
      SepLensStateInv env.length entries m →
      LensFramePreserved entries₀ m₀ m →
      entries.map Prod.fst = entries₀.map Prod.fst →
      (∀ m' : Memory,
        SepLensStateInv env'.length entries' m' →
        LensFramePreserved entries₀ m₀ m' →
        entries'.map Prod.fst = entries₀.map Prod.fst →
        MirWpConverges body
          { frame := {
              blockIdx := bbIdx
              stmtIdx := bb.statements.length
              locals := env'
            }
            memory := m' }
          Φ) →
      MirWpConverges body
        { frame := {
            blockIdx := bbIdx
            stmtIdx := prefixStmts.length
            locals := env
          }
          memory := m }
        Φ := by
  induction hStmts with
  | @nil env entries =>
    intro prefixStmts m₀ m Φ hBbStmts hInv hFrame hKeys hCont
    have hStmtLen : bb.statements.length = prefixStmts.length := by
      rw [hBbStmts, List.append_nil]
    rw [← hStmtLen]
    exact hCont m hInv hFrame hKeys
  | cons hFirst hRest ih =>
    rename_i env_ env1_ env2_ entries_ entries1_ entries2_ stmt rest
    intro prefixStmts m₀ m Φ hBbStmts hInv hFrame hKeys hCont
    let s : MachineState := {
      frame := {
        blockIdx := bbIdx
        stmtIdx := prefixStmts.length
        locals := env_
      }
      memory := m
    }
    rcases hFirst.evalStmt_step (s := s) rfl hInv hFrame hKeys with
      ⟨m₁, hStepStmt, hLen₁, hInv₁, hFrame₁, hKeys₁⟩
    apply MirWpConverges.step_tau (s' := advanceStmt s env1_ m₁)
    · rw [stepMirFn_of_isRuntimeMirPhase body bbIdx prefixStmts.length env_ m
        hInv.activeCallee_none hPhase hBb]
      have hGetStmt : get? bb.statements prefixStmts.length = .some stmt := by
        rw [hBbStmts]
        unfold get?
        rw [List.getElem?_append_right (Nat.le_refl _)]
        simp
      simp only [hGetStmt]
      exact hStepStmt
    · have hAppend :
          bb.statements = (prefixStmts ++ [stmt]) ++ rest := by
        rw [List.append_assoc, List.singleton_append]
        exact hBbStmts
      have hPrefixLen :
          (prefixStmts ++ [stmt]).length = Nat.add prefixStmts.length 1 := by
        simp
      unfold advanceStmt
      dsimp only [s]
      rw [← hPrefixLen]
      exact ih (prefixStmts ++ [stmt]) m₀ m₁ Φ hAppend hInv₁ hFrame₁ hKeys₁ hCont

/-- A root-frame `return_` terminator halts with `_0`'s value and the memory. -/
theorem mirWpConverges_return_of_lens
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    {env : PureEnv} {m : Memory} {retVal : Value} {Φ : MirOutcome → Prop}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hTerm : bb.terminator.kind = .return_)
    (hRet : get? env 0 = .some (.init retVal))
    (hStack : m.callStack = [])
    (hCallee : m.activeCallee = .none)
    (hPost : Φ (.normal (retVal, m))) :
    MirWpConverges body
      { frame := {
          blockIdx := bbIdx
          stmtIdx := bb.statements.length
          locals := env
        }
        memory := m }
      Φ := by
  refine MirWpConverges.ret_of_step ?_ hPost
  rw [stepMirFn_of_isRuntimeMirPhase body bbIdx bb.statements.length env m
    hCallee hPhase hBb]
  have hGetNone : get? bb.statements bb.statements.length = .none :=
    get?_eq_none_of_le (Nat.le_refl _)
  simp only [hGetNone]
  unfold length
  simp only [beq_self_eq_true, ↓reduceIte]
  unfold evalTerminator
  rw [hTerm, hRet, hStack]
  rfl

/-- A `goto` terminator continues at the first statement of its target. -/
theorem mirWpConverges_goto_of_lens
    {body : CapturedMir} {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
    {env : PureEnv} {m : Memory} {Φ : MirOutcome → Prop}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hTerm : bb.terminator.kind = .goto target)
    (hCallee : m.activeCallee = .none)
    (hNext :
      MirWpConverges body
        { frame := { blockIdx := target, stmtIdx := 0, locals := env }
          memory := m }
        Φ) :
    MirWpConverges body
      { frame := {
          blockIdx := bbIdx
          stmtIdx := bb.statements.length
          locals := env
        }
        memory := m }
      Φ := by
  refine MirWpConverges.step_tau ?_ hNext
  rw [stepMirFn_of_isRuntimeMirPhase body bbIdx bb.statements.length env m
    hCallee hPhase hBb]
  have hGetNone : get? bb.statements bb.statements.length = .none :=
    get?_eq_none_of_le (Nat.le_refl _)
  simp only [hGetNone]
  unfold length
  simp only [beq_self_eq_true, ↓reduceIte]
  unfold evalTerminator
  rw [hTerm]
  rfl

/--
An `assert` terminator whose condition evaluates to the expected bit continues
at its success target with the locals left by the condition operand.
-/
theorem mirWpConverges_assert_of_lens
    {body : CapturedMir} {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
    {cond : Operand} {expected : Bool} {unwind : UnwindAction}
    {env env' : PureEnv} {sc : ScalarInt} {m : Memory} {Φ : MirOutcome → Prop}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hTerm : bb.terminator.kind = .assert cond expected target unwind)
    (hCallee : m.activeCallee = .none)
    (hEval :
      evalOperand env cond m.borrows m.globals body.layouts m.callerLocals =
        .ok (.scalar sc) env')
    (hBit : sc.bits = assertBit expected)
    (hNext :
      MirWpConverges body
        { frame := { blockIdx := target, stmtIdx := 0, locals := env' }
          memory := m }
        Φ) :
    MirWpConverges body
      { frame := {
          blockIdx := bbIdx
          stmtIdx := bb.statements.length
          locals := env
        }
        memory := m }
      Φ := by
  refine MirWpConverges.step_tau ?_ hNext
  rw [stepMirFn_of_isRuntimeMirPhase body bbIdx bb.statements.length env m
    hCallee hPhase hBb]
  have hGetNone : get? bb.statements bb.statements.length = .none :=
    get?_eq_none_of_le (Nat.le_refl _)
  simp only [hGetNone]
  unfold length
  simp only [beq_self_eq_true, ↓reduceIte]
  unfold evalTerminator
  rw [hTerm]
  dsimp only
  rw [hEval]
  dsimp only
  rw [hBit]
  cases expected <;> rfl

/--
A `switchInt` terminator whose discriminant evaluates to scalar `sc` emits the
branch observation `.event sc.bits` and continues at the target selected by
`lookupSwitchTarget sc.bits targets.branches targets.otherwise`.
-/
theorem mirWpConverges_switchInt_of_lens
    {body : CapturedMir} {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
    {discr : Operand} {targets : SwitchTargets}
    {env env' : PureEnv} {sc : ScalarInt} {m : Memory} {Φ : MirOutcome → Prop}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hTerm : bb.terminator.kind = .switchInt discr targets)
    (hCallee : m.activeCallee = .none)
    (hEval :
      evalOperand env discr m.borrows m.globals body.layouts m.callerLocals =
        .ok (.scalar sc) env')
    (hTarget : lookupSwitchTarget sc.bits targets.branches targets.otherwise = target)
    (hNext :
      MirWpConverges body
        { frame := { blockIdx := target, stmtIdx := 0, locals := env' }
          memory := m }
        Φ) :
    MirWpConverges body
      { frame := {
          blockIdx := bbIdx
          stmtIdx := bb.statements.length
          locals := env
        }
        memory := m }
      Φ := by
  refine MirWpConverges.step_emit (obs := .event sc.bits) ?_ hNext
  rw [stepMirFn_of_isRuntimeMirPhase body bbIdx bb.statements.length env m
    hCallee hPhase hBb]
  have hGetNone : get? bb.statements bb.statements.length = .none :=
    get?_eq_none_of_le (Nat.le_refl _)
  simp only [hGetNone]
  unfold length
  simp only [beq_self_eq_true, ↓reduceIte]
  unfold evalTerminator
  rw [hTerm]
  dsimp only
  rw [hEval]
  dsimp only
  rw [hTarget]

/--
A `drop` terminator on a non-dead root local slot `loc` marks the slot
`.uninit` and continues at its normal target.
-/
theorem mirWpConverges_drop_of_lens
    {body : CapturedMir} {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
    {loc : Local} {unwind : UnwindAction} {oldSlot : LocalSlot}
    {env env' : PureEnv} {m : Memory} {Φ : MirOutcome → Prop}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hTerm :
      bb.terminator.kind =
        .drop { local_ := loc, projection := [] } target unwind)
    (hCallee : m.activeCallee = .none)
    (hGet : get? env loc = .some oldSlot)
    (hNotDead : oldSlot ≠ .dead)
    (hSet : set? env loc .uninit = .some env')
    (hNext :
      MirWpConverges body
        { frame := { blockIdx := target, stmtIdx := 0, locals := env' }
          memory := m }
        Φ) :
    MirWpConverges body
      { frame := {
          blockIdx := bbIdx
          stmtIdx := bb.statements.length
          locals := env
        }
        memory := m }
      Φ := by
  refine MirWpConverges.step_tau ?_ hNext
  rw [stepMirFn_of_isRuntimeMirPhase body bbIdx bb.statements.length env m
    hCallee hPhase hBb]
  have hGetNone : get? bb.statements bb.statements.length = .none :=
    get?_eq_none_of_le (Nat.le_refl _)
  simp only [hGetNone]
  unfold length
  simp only [beq_self_eq_true, ↓reduceIte]
  unfold evalTerminator
  rw [hTerm]
  dsimp only
  rw [hGet]
  cases oldSlot with
  | dead => exact absurd rfl hNotDead
  | uninit =>
    dsimp only
    rw [hSet]
    rfl
  | init _ =>
    dsimp only
    rw [hSet]
    rfl


/-- Pure operand lifting preserves the length of the local slot environment. -/
theorem LiftLensOperand.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {op : Operand} {v : Value}
    (h : LiftLensOperand localDecls layouts env op v env') :
    env'.length = env.length := by
  cases h with
  | copy_local _ => rfl
  | move_local _ hSet => exact set?_length_eq hSet
  | copy_field _ _ _ => rfl
  | move_field _ _ _ => rfl
  | const_scalar => rfl
  | const_zeroSized => rfl

/-- Unified operand lifting preserves the local slot environment's length. -/
theorem LiftLensOperandAny.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value}
    (h : LiftLensOperandAny localDecls layouts env entries op v env') :
    env'.length = env.length := by
  cases h with
  | pure hOp => exact hOp.length_eq
  | deref hDeref => cases hDeref <;> rfl
  | deref_field hField => cases hField <;> rfl

theorem LiftLensOperands.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {ops : List Operand} {vs : List Value}
    (h : LiftLensOperands localDecls layouts env entries ops vs env') :
    env'.length = env.length := by
  induction h with
  | nil => rfl
  | cons hOp _ ih => exact ih.trans hOp.length_eq

theorem LiftLensRvalue.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {rv : Rvalue} {v : Value}
    (h : LiftLensRvalue localDecls layouts env entries rv v env') :
    env'.length = env.length := by
  cases h with
  | use_pure hOp _ => exact hOp.length_eq
  | use_deref hDeref _ => cases hDeref <;> rfl
  | use_deref_field hField _ => cases hField <;> rfl
  | copyForDeref_deref _ _ => rfl
  | binaryOp hLhs hRhs _ => exact hRhs.length_eq.trans hLhs.length_eq
  | unaryOp_not hOp _ => exact hOp.length_eq
  | unaryOp_neg hOp _ => exact hOp.length_eq
  | cast_intToInt hOp _ _ => exact hOp.length_eq
  | tuple_nil => rfl
  | aggregate_tuple hOps => exact hOps.length_eq
  | aggregate_adt hOps => exact hOps.length_eq

theorem LiftLensStmt.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement}
    (h : LiftLensStmt localDecls layouts env entries stmt env' entries') :
    env'.length = env.length := by
  cases h with
  | retag hR => cases hR; rfl
  | derefWrite hW =>
    cases hW with
    | mk hRv _ _ => exact hRv.length_eq
    | field hRv _ _ _ => exact hRv.length_eq
  | pureAssign hP =>
    cases hP with
    | mk hRv _ _ hSet => exact (set?_length_eq hSet).trans hRv.length_eq
  | storageLive hL => cases hL with | mk _ hSet => exact set?_length_eq hSet
  | storageDead hD => cases hD with | mk _ hSet => exact set?_length_eq hSet
  | nop hN => cases hN; rfl

theorem LiftLensStmts.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmts : List Statement}
    (h : LiftLensStmts localDecls layouts env entries stmts env' entries') :
    env'.length = env.length := by
  induction h with
  | nil => rfl
  | cons hFirst _ ih => exact ih.trans hFirst.length_eq

/--
Control-flow soundness of `LiftLensBlock` by induction on the derivation: each
block's statements step through `mirWpConverges_of_liftLensStmts`, and its
terminator (`return_`, `goto`, `assert`, `switchInt`, or `drop_local`) steps
through the matching terminator lemma, threading `SepLensStateInv`,
`LensFramePreserved`, and the lens keys across blocks.
-/
theorem mirWpConverges_of_liftLensBlock
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {env : PureEnv}
    {entries entries' : List (RawPtrVal × Value)} {retVal : Value}
    (hBlock : LiftLensBlock body bbIdx env entries retVal entries') :
    ∀ (entries₀ : List (RawPtrVal × Value)) (m₀ m : Memory)
      (Φ : MirOutcome → Prop),
      SepLensStateInv env.length entries m →
      LensFramePreserved entries₀ m₀ m →
      entries.map Prod.fst = entries₀.map Prod.fst →
      (∀ m_final : Memory,
        SepLensStateInv env.length entries' m_final →
        LensFramePreserved entries₀ m₀ m_final →
        Φ (.normal (retVal, m_final))) →
      MirWpConverges body
        { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := env }
          memory := m }
        Φ := by
  induction hBlock with
  | return_ hPhase hBb hTerm hStmts hRet =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen := hStmts.length_eq
    exact mirWpConverges_of_liftLensStmts hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' _ =>
        mirWpConverges_return_of_lens hPhase hBb hTerm hRet
          hInv'.callStack_nil hInv'.activeCallee_none
          (hPost m' (by rw [← hLen]; exact hInv') hFrame'))
  | goto hPhase hBb hTerm hStmts _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen := hStmts.length_eq
    exact mirWpConverges_of_liftLensStmts hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' =>
        mirWpConverges_goto_of_lens hPhase hBb hTerm hInv'.activeCallee_none
          (ih entries₀ m₀ m' Φ hInv' hFrame' hKeys'
            (fun m_final hInvF hFrameF =>
              hPost m_final (by rw [← hLen]; exact hInvF) hFrameF)))
  | assert hPhase hBb hTerm hStmts hCond hBit _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen := hStmts.length_eq
    refine mirWpConverges_of_liftLensStmts hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' => ?_)
    rcases hCond.evalOperand_eq hInv' with ⟨hEval, hLen₂⟩
    exact mirWpConverges_assert_of_lens hPhase hBb hTerm
      hInv'.activeCallee_none hEval hBit
      (ih entries₀ m₀ m' Φ (by rw [hLen₂]; exact hInv') hFrame' hKeys'
        (fun m_final hInvF hFrameF =>
          hPost m_final (by rw [← hLen, ← hLen₂]; exact hInvF) hFrameF))
  | switchInt hPhase hBb hTerm hStmts hDiscr hTarget _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen := hStmts.length_eq
    refine mirWpConverges_of_liftLensStmts hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' => ?_)
    rcases hDiscr.evalOperand_eq hInv' with ⟨hEval, hLen₂⟩
    exact mirWpConverges_switchInt_of_lens hPhase hBb hTerm
      hInv'.activeCallee_none hEval hTarget
      (ih entries₀ m₀ m' Φ (by rw [hLen₂]; exact hInv') hFrame' hKeys'
        (fun m_final hInvF hFrameF =>
          hPost m_final (by rw [← hLen, ← hLen₂]; exact hInvF) hFrameF))
  | drop_local hPhase hBb hTerm hStmts hGet hNotDead hSet _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen := hStmts.length_eq
    have hLen₂ := set?_length_eq hSet
    refine mirWpConverges_of_liftLensStmts hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' => ?_)
    exact mirWpConverges_drop_of_lens hPhase hBb hTerm
      hInv'.activeCallee_none hGet hNotDead hSet
      (ih entries₀ m₀ m' Φ (by rw [hLen₂]; exact hInv') hFrame' hKeys'
        (fun m_final hInvF hFrameF =>
          hPost m_final (by rw [← hLen, ← hLen₂]; exact hInvF) hFrameF))

/--
Fuel-Free Separation-Logic Lens Lifting Theorem (`mirWpConverges_of_sepLenses`):
given a `LiftLensBlock body bbIdx env entries₀ retVal entries'` derivation over
the body's control-flow graph and an initial memory `m₀` satisfying
`SepLensStateInv env.length entries₀ m₀`, `MirWpConverges` holds fuel-freely
from `{ blockIdx := bbIdx, stmtIdx := 0, locals := env }` to a normal return of
`retVal` in a final memory satisfying `SepLensStateInv env.length entries'` and
`LensFramePreserved entries₀ m₀`.
-/
theorem mirWpConverges_of_sepLenses
    {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {entries₀ entries' : List (RawPtrVal × Value)}
    {retVal : Value} {m₀ : Memory} {Φ : MirOutcome → Prop}
    (hBlock : LiftLensBlock body bbIdx env entries₀ retVal entries')
    (hInv₀ : SepLensStateInv env.length entries₀ m₀)
    (hPost :
      ∀ m_final : Memory,
        SepLensStateInv env.length entries' m_final →
        LensFramePreserved entries₀ m₀ m_final →
        Φ (.normal (retVal, m_final))) :
    MirWpConverges body
      { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := env }
        memory := m₀ }
      Φ :=
  mirWpConverges_of_liftLensBlock hBlock entries₀ m₀ m₀ Φ hInv₀
    (LensFramePreserved.refl entries₀ m₀) rfl hPost


/--
Bridge from `mirWpConverges_of_sepLenses` to `StatefulVerificationResult`.
-/
theorem verifyStatefulMir_of_sepLenses
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepLensStateInv env₀.length entries₀ m₀ ∧
          ∀ m_final : Memory,
            SepLensStateInv env₀.length entries' m_final →
            LensFramePreserved entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    StatefulVerificationResult { body := body, pre := Pre, post := Post } := by
  refine verifyStatefulMirNoPanic_of_wpConverges { body := body, pre := Pre, post := Post } ?_
  intro args m₀ hPre
  rcases hStep args m₀ hPre with
    ⟨entries₀, entries', retVal, hBlock, hInv₀, hPost⟩
  exact mirWpConverges_of_sepLenses hBlock hInv₀ hPost

/--
Bridge from `mirWpConverges_of_sepLenses` to `TotalVerificationResult`.
-/
theorem verifyTotalMir_of_sepLenses
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepLensStateInv env₀.length entries₀ m₀ ∧
          ∀ m_final : Memory,
            SepLensStateInv env₀.length entries' m_final →
            LensFramePreserved entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    TotalVerificationResult { body := body, pre := Pre, post := Post } := by
  refine verifyTotalMir_of_wpConverges { body := body, pre := Pre, post := Post } ?_
  intro args m₀ hPre
  rcases hStep args m₀ hPre with
    ⟨entries₀, entries', retVal, hBlock, hInv₀, hPost⟩
  exact mirWpConverges_of_sepLenses hBlock hInv₀ hPost

/-! ### Connecting `sepConj` / `ActiveTypedMutBorrow` to `SepLensStateInv` -/

/--
Per-pointer MIR frame well-formedness for a single mutable borrow `rp` at
entry to a callee with `frameLen` local slots. Note that this structure refers
ONLY to a single pointer `rp` and never assumes non-aliasing between distinct
pointers; multi-pointer disjointness is derived automatically from `sepConj`.
-/
structure WfSingleMutBorrow
    (frameLen : Nat) (rp : RawPtrVal) (m : Memory) : Prop where
  callStack_nil : m.callStack = []
  activeCallee_none : m.activeCallee = .none
  borrows_above_frame : ∀ b ∈ m.borrows, frameLen ≤ b.targetLocal
  alloc_above_frame : frameLen ≤ rp.allocId
  exclusive : TreeExclusiveBorrow rp m

theorem callerLocals_get?_of_pointsTo
    {rp : RawPtrVal} {v : Value} {m : Memory}
    (hStack : m.callStack = [])
    (hOff : rp.offset = 0)
    (hPts : readAllocAt? (memoryLocals m) rp = some v) :
    get? m.callerLocals rp.allocId = .some (.init v) := by
  unfold readAllocAt? memoryLocals at hPts
  rw [hStack, hOff] at hPts
  cases hGet : get? m.callerLocals rp.allocId with
  | none => rw [hGet] at hPts; nomatch hPts
  | some slot =>
    rw [hGet] at hPts
    cases slot with
    | dead => nomatch hPts
    | uninit => nomatch hPts
    | init val =>
      injection hPts with hV
      subst hV
      rfl

theorem activeTypedMutBorrow_of_sepLensEntry {α : Type}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α}
    (hInv : SepLensStateInv frameLen entries m)
    (hMem : (rp, codec.encode a) ∈ entries) :
    SepProp.holdsIn (ActiveTypedMutBorrow rp codec a) m ∧
    (memoryPtrMutLens rp codec).readView m = a := by
  rcases hInv.entries_valid rp (codec.encode a) hMem with
    ⟨hOff, _, hCaller, hExcl⟩
  rcases hExcl.lookup_active with ⟨entry, hLook, hT, hP, hPerm, _, _⟩
  have hPts : readAllocAt? (memoryLocals m) rp = some (codec.encode a) := by
    unfold readAllocAt? memoryLocals
    rw [hInv.callStack_nil, hOff, hCaller]
  have hTok : ∃ entry, lookupBorrow m.borrows rp.tag = some entry ∧ entry.targetLocal = rp.allocId ∧ entry.perm = .active :=
    ⟨entry, hLook, hT, hPerm⟩
  exact ⟨⟨mutBorrowFootprint rp, activeTypedMutBorrow_intro hPts hTok⟩,
    memoryPtrMutLens_readView_of_readAllocAt hPts⟩

/-! ### General `List` / Indexed Composition of Typed Mutable Borrows -/

/--
A typed mutable-borrow binding: pointer `rp`, value codec `codec`, and current
logical pointee value `val`. Heterogeneous binding lists model the `k`-ary
separating conjunction `ATMB rp₁ codec₁ a₁ ∗ ⋯ ∗ ATMB rpₖ codecₖ aₖ ∗ R_frame`,
where `ATMB` abbreviates `ActiveTypedMutBorrow`.
-/
structure MutBorrowBinding : Type 1 where
  α : Type
  rp : RawPtrVal
  codec : ValueCodec α
  val : α

/-- Build a `MutBorrowBinding`, inferring the pointee type from `codec`. -/
def MutBorrowBinding.bind {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) (val : α) : MutBorrowBinding :=
  ⟨α, rp, codec, val⟩

/-- `ActiveTypedMutBorrow b.rp b.codec b.val`. -/
def MutBorrowBinding.toSepProp (b : MutBorrowBinding) : SepProp :=
  ActiveTypedMutBorrow b.rp b.codec b.val

/-- Pure lens-state entry `(b.rp, b.codec.encode b.val)`. -/
def MutBorrowBinding.entry (b : MutBorrowBinding) : RawPtrVal × Value :=
  (b.rp, b.codec.encode b.val)

/-- Address cell `(allocId, offset)` owned by the binding's `PointsTo`. -/
def MutBorrowBinding.cell (b : MutBorrowBinding) : Nat × Nat :=
  (b.rp.allocId, b.rp.offset)

/-- Iterated separating conjunction `P₁ ∗ (P₂ ∗ (⋯ ∗ (Pₖ ∗ R)))`. -/
def sepConjList : List SepProp → SepProp → SepProp
  | [], R => R
  | P :: Ps, R => sepConj P (sepConjList Ps R)

/--
`ATMB b₁ ∗ ⋯ ∗ ATMB bₖ ∗ R`, right-nested exactly like the binary forms, so
`sepConjBindings [b₁, b₂] R` unfolds definitionally to
`sepConj (ATMB b₁) (sepConj (ATMB b₂) R)`.
-/
def sepConjBindings (bs : List MutBorrowBinding) (R : SepProp) : SepProp :=
  sepConjList (bs.map MutBorrowBinding.toSepProp) R

/-- Combined footprint of a binding list: its cells and its tags. -/
def bindingsFootprint (bs : List MutBorrowBinding) : Footprint :=
  { addrs := bs.map MutBorrowBinding.cell, tags := bs.map (·.rp.tag) }

/-- Pointer-level facts carried by one `ActiveTypedMutBorrow` at `h`. -/
theorem activeTypedMutBorrow_facts {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {h : PartialHeap}
    (hA : ActiveTypedMutBorrow rp codec a h) :
    readAllocAt? (memoryLocals h.state) rp = some (codec.encode a) ∧
    (∃ entry,
      lookupBorrow h.state.borrows rp.tag = some entry ∧
      entry.targetLocal = rp.allocId ∧
      entry.perm = .active) ∧
    (rp.allocId, rp.offset) ∈ h.footprint.addrs ∧
    rp.tag ∈ h.footprint.tags := by
  rcases hA with
    ⟨h₁, h₂, ⟨hs₁, hs₂, _, hAddrs, hTags⟩, ⟨hPts, hfp₁⟩, ⟨hTok, hfp₂⟩⟩
  refine ⟨hs₁ ▸ hPts, hs₂ ▸ hTok, ?_, ?_⟩
  · apply (hAddrs _).mpr
    left
    rw [hfp₁]
    exact List.mem_singleton.mpr rfl
  · apply (hTags _).mpr
    right
    rw [hfp₂]
    exact List.mem_singleton.mpr rfl

/--
Decomposition of `sepConjBindings bs R` at `h`: every binding's pointee and
active borrow token are present in `h.state`, binding cells and tags are
pairwise distinct and owned by `h`, and the frame `R` holds at a footprint
`fpR ⊆ h.footprint` that is disjoint from every binding.
-/
theorem sepConjBindings_split
    {bs : List MutBorrowBinding} {R : SepProp} {h : PartialHeap}
    (hSep : sepConjBindings bs R h) :
    (∀ b ∈ bs,
      readAllocAt? (memoryLocals h.state) b.rp = some (b.codec.encode b.val) ∧
      ∃ entry,
        lookupBorrow h.state.borrows b.rp.tag = some entry ∧
        entry.targetLocal = b.rp.allocId ∧
        entry.perm = .active) ∧
    bs.Pairwise (fun b₁ b₂ => b₁.cell ≠ b₂.cell ∧ b₁.rp.tag ≠ b₂.rp.tag) ∧
    (∀ b ∈ bs, b.cell ∈ h.footprint.addrs ∧ b.rp.tag ∈ h.footprint.tags) ∧
    ∃ fpR : Footprint,
      R ⟨h.state, fpR⟩ ∧
      (∀ b ∈ bs, b.cell ∉ fpR.addrs ∧ b.rp.tag ∉ fpR.tags) ∧
      (∀ a ∈ fpR.addrs, a ∈ h.footprint.addrs) ∧
      (∀ t ∈ fpR.tags, t ∈ h.footprint.tags) := by
  induction bs generalizing h with
  | nil =>
    refine ⟨?_, List.Pairwise.nil, ?_, h.footprint, hSep, ?_, ?_, ?_⟩
    · intro _ hb
      nomatch hb
    · intro _ hb
      nomatch hb
    · intro _ hb
      nomatch hb
    · intro _ ha
      exact ha
    · intro _ ht
      exact ht
  | cons b rest ih =>
    rcases hSep with ⟨h₁, h₂, ⟨hs₁, hs₂, hDisj, hAddrs, hTags⟩, hB, hRest⟩
    rcases activeTypedMutBorrow_facts hB with ⟨hPts, hTok, hCell, hTag⟩
    rcases ih hRest with ⟨hBind, hPair, hOwn, fpR, hR, hDisjR, hSubA, hSubT⟩
    refine ⟨?_, ?_, ?_, fpR, ?_, ?_, ?_, ?_⟩
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · rw [← hs₁]
        exact ⟨hPts, hTok⟩
      · rw [← hs₂]
        exact hBind b' hb'
    · refine List.pairwise_cons.mpr ⟨fun b' hb' => ⟨?_, ?_⟩, hPair⟩
      · intro hEq
        apply hDisj.1 _ hCell
        have hIn := (hOwn b' hb').1
        rw [← hEq] at hIn
        exact hIn
      · intro hEq
        apply hDisj.2 _ hTag
        have hIn := (hOwn b' hb').2
        rw [← hEq] at hIn
        exact hIn
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact ⟨(hAddrs _).mpr (Or.inl hCell), (hTags _).mpr (Or.inl hTag)⟩
      · exact ⟨(hAddrs _).mpr (Or.inr (hOwn b' hb').1),
          (hTags _).mpr (Or.inr (hOwn b' hb').2)⟩
    · rw [← hs₂]
      exact hR
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact ⟨fun hIn => hDisj.1 _ hCell (hSubA _ hIn),
          fun hIn => hDisj.2 _ hTag (hSubT _ hIn)⟩
      · exact hDisjR b' hb'
    · intro a ha
      exact (hAddrs a).mpr (Or.inr (hSubA a ha))
    · intro t ht
      exact (hTags t).mpr (Or.inr (hSubT t ht))

/--
Converse of `sepConjBindings_split`: pairwise-disjoint bindings that are each
present in `m`, together with a frame `R` at a footprint disjoint from all of
them, compose into `sepConjBindings bs R` at their union footprint.
-/
theorem sepConjBindings_intro
    {bs : List MutBorrowBinding} {R : SepProp} {m : Memory} {fpR : Footprint}
    (hBind :
      ∀ b ∈ bs,
        readAllocAt? (memoryLocals m) b.rp = some (b.codec.encode b.val) ∧
        ∃ entry,
          lookupBorrow m.borrows b.rp.tag = some entry ∧
          entry.targetLocal = b.rp.allocId ∧
          entry.perm = .active)
    (hPair :
      bs.Pairwise (fun b₁ b₂ => b₁.cell ≠ b₂.cell ∧ b₁.rp.tag ≠ b₂.rp.tag))
    (hR : R ⟨m, fpR⟩)
    (hDisjR : ∀ b ∈ bs, b.cell ∉ fpR.addrs ∧ b.rp.tag ∉ fpR.tags) :
    sepConjBindings bs R ⟨m, (bindingsFootprint bs).union fpR⟩ := by
  induction bs with
  | nil => exact hR
  | cons b rest ih =>
    rcases List.pairwise_cons.mp hPair with ⟨hHead, hTail⟩
    have hRest :=
      ih (fun b' hb' => hBind b' (List.Mem.tail b hb')) hTail
        (fun b' hb' => hDisjR b' (List.Mem.tail b hb'))
    rcases hBind b (List.Mem.head rest) with ⟨hPts, hTok⟩
    refine ⟨⟨m, mutBorrowFootprint b.rp⟩,
      ⟨m, (bindingsFootprint rest).union fpR⟩,
      ⟨rfl, rfl, ⟨?_, ?_⟩, ?_, ?_⟩,
      activeTypedMutBorrow_intro hPts hTok, hRest⟩
    · intro a ha hb
      simp only [mutBorrowFootprint, List.mem_singleton] at ha
      subst ha
      simp only [bindingsFootprint, Footprint.union, List.mem_append,
        List.mem_map] at hb
      rcases hb with ⟨b', hb', hEq⟩ | hInR
      · exact (hHead b' hb').1 hEq.symm
      · exact (hDisjR b (List.Mem.head rest)).1 hInR
    · intro t ht hb
      simp only [mutBorrowFootprint, List.mem_singleton] at ht
      subst ht
      simp only [bindingsFootprint, Footprint.union, List.mem_append,
        List.mem_map] at hb
      rcases hb with ⟨b', hb', hEq⟩ | hInR
      · exact (hHead b' hb').2 hEq.symm
      · exact (hDisjR b (List.Mem.head rest)).2 hInR
    · intro a
      simp only [bindingsFootprint, Footprint.union, mutBorrowFootprint,
        MutBorrowBinding.cell, List.map_cons, List.cons_append, List.mem_cons,
        List.not_mem_nil, or_false, List.mem_append, List.mem_map]
    · intro t
      simp only [bindingsFootprint, Footprint.union, mutBorrowFootprint,
        List.map_cons, List.cons_append, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_append, List.mem_map]

/--
The binding footprints of a `k`-ary separating conjunction are pairwise
`DisjointFootprints`: their `(allocId, offset)` cells and their tags are
pairwise distinct.
-/
theorem sepConjBindings_pairwise_disjointFootprints
    {bs : List MutBorrowBinding} {R : SepProp} {m : Memory}
    (hSep : SepProp.holdsIn (sepConjBindings bs R) m) :
    bs.Pairwise (fun b₁ b₂ =>
      DisjointFootprints (mutBorrowFootprint b₁.rp) (mutBorrowFootprint b₂.rp)) := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split hSep with ⟨_, hPair, _⟩
  refine hPair.imp ?_
  intro b₁ b₂ hNe
  refine ⟨fun a ha₁ ha₂ => ?_, fun t ht₁ ht₂ => ?_⟩
  · simp only [mutBorrowFootprint, List.mem_singleton] at ha₁ ha₂
    exact hNe.1 (ha₁.symm.trans ha₂)
  · simp only [mutBorrowFootprint, List.mem_singleton] at ht₁ ht₂
    exact hNe.2 (ht₁.symm.trans ht₂)

/--
Distinct bindings of a `k`-ary separating conjunction whose pointers sit at
offset `0` are backed by borrow entries targeting distinct caller locals
(`targetLocal`).
-/
theorem sepConjBindings_targetLocal_pairwise_ne
    {bs : List MutBorrowBinding} {R : SepProp} {m : Memory}
    (hSep : SepProp.holdsIn (sepConjBindings bs R) m)
    (hOff : ∀ b ∈ bs, b.rp.offset = 0) :
    bs.Pairwise (fun b₁ b₂ =>
      ∀ e₁ e₂,
        lookupBorrow m.borrows b₁.rp.tag = some e₁ →
        lookupBorrow m.borrows b₂.rp.tag = some e₂ →
        e₁.targetLocal ≠ e₂.targetLocal) := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split hSep with ⟨hBind, hPair, _⟩
  refine List.Pairwise.imp_of_mem ?_ hPair
  intro b₁ b₂ hb₁ hb₂ hNe e₁ e₂ hL₁ hL₂ hTarget
  rcases (hBind b₁ hb₁).2 with ⟨f₁, hF₁, hT₁, _⟩
  rcases (hBind b₂ hb₂).2 with ⟨f₂, hF₂, hT₂, _⟩
  have hE₁ : e₁ = f₁ := Option.some.inj (hL₁.symm.trans hF₁)
  have hE₂ : e₂ = f₂ := Option.some.inj (hL₂.symm.trans hF₂)
  apply hNe.1
  show (b₁.rp.allocId, b₁.rp.offset) = (b₂.rp.allocId, b₂.rp.offset)
  rw [hOff b₁ hb₁, hOff b₂ hb₂, ← hT₁, ← hT₂, ← hE₁, ← hE₂, hTarget]

/--
Pointer-independent MIR frame well-formedness at function entry: the caller
has no saved frames, no callee is active, and every borrow targets a caller
allocation above the callee's `frameLen` local slots.
-/
structure WfLensFrame (frameLen : Nat) (m : Memory) : Prop where
  callStack_nil : m.callStack = []
  activeCallee_none : m.activeCallee = .none
  borrows_above_frame : ∀ b ∈ m.borrows, frameLen ≤ b.targetLocal

theorem WfSingleMutBorrow.toWfLensFrame
    {frameLen : Nat} {rp : RawPtrVal} {m : Memory}
    (h : WfSingleMutBorrow frameLen rp m) : WfLensFrame frameLen m :=
  ⟨h.callStack_nil, h.activeCallee_none, h.borrows_above_frame⟩

/--
`k`-Lens Entry Bridge: a `k`-ary separating conjunction of typed mutable borrows
with an arbitrary frame establishes `SepLensStateInv` for all `k` lens entries.
The hypotheses `hPtr` are per pointer; pairwise disjointness of allocations and
tags is derived from `sepConj`.
-/
theorem sepLensStateInv_of_sepConjBindings
    {frameLen : Nat} {bs : List MutBorrowBinding} {R : SepProp} {m : Memory}
    (hSep : SepProp.holdsIn (sepConjBindings bs R) m)
    (hFrame : WfLensFrame frameLen m)
    (hPtr : ∀ b ∈ bs, frameLen ≤ b.rp.allocId ∧ TreeExclusiveBorrow b.rp m) :
    SepLensStateInv frameLen (bs.map MutBorrowBinding.entry) m := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split hSep with ⟨hBind, hPair, _, _⟩
  refine ⟨hFrame.callStack_nil, hFrame.activeCallee_none,
    hFrame.borrows_above_frame, ?_, ?_⟩
  · intro rp v hMem
    rcases List.mem_map.mp hMem with ⟨b, hb, hEq⟩
    simp only [MutBorrowBinding.entry, Prod.mk.injEq] at hEq
    rcases hEq with ⟨rfl, rfl⟩
    rcases hPtr b hb with ⟨hAbove, hExcl⟩
    exact ⟨hExcl.offset_zero, hAbove,
      callerLocals_get?_of_pointsTo hFrame.callStack_nil hExcl.offset_zero
        (hBind b hb).1,
      hExcl⟩
  · rw [List.map_map]
    apply List.pairwise_map.mpr
    refine List.Pairwise.imp_of_mem ?_ hPair
    intro b₁ b₂ hb₁ hb₂ hNe
    refine ⟨fun hAlloc => hNe.1 ?_, hNe.2⟩
    show (b₁.rp.allocId, b₁.rp.offset) = (b₂.rp.allocId, b₂.rp.offset)
    have hAlloc' : b₁.rp.allocId = b₂.rp.allocId := hAlloc
    rw [hAlloc', (hPtr b₁ hb₁).2.offset_zero, (hPtr b₂ hb₂).2.offset_zero]

/--
Reading past offset `0` of a slot whose value is not a variant-`0` aggregate
yields `none`; such cells are therefore unaffected by whole-slot writes.
-/
theorem readAllocAt_succ_of_not_aggregate
    {locals : List LocalValue} {allocId k tag : Nat} {v : Value}
    (hGet : get? locals allocId = some (.init v))
    (hNotAgg : ∀ elems, v ≠ .aggregate 0 elems) :
    readAllocAt? locals { allocId := allocId, offset := k + 1, tag := tag } =
      none := by
  unfold readAllocAt?
  rw [hGet]
  dsimp only
  cases v with
  | aggregate variant elems =>
    cases variant with
    | zero => exact absurd rfl (hNotAgg elems)
    | succ _ => rfl
  | unit => rfl
  | scalar _ => rfl
  | ptr _ _ => rfl

theorem memoryLocals_of_callStack_nil {m : Memory}
    (h : m.callStack = []) : memoryLocals m = m.callerLocals := by
  unfold memoryLocals
  rw [h]

/--
`k`-Lens Exit Bridge: if `ATMB b₁ ∗ ⋯ ∗ ATMB bₖ ∗ R_frame` held initially, the
final memory satisfies `SepLensStateInv` for the updated bindings `bs'` (same
pointers, new values), and every caller allocation and borrow tag outside the
lens footprint is unchanged (`LensFramePreserved`), then
`ATMB b'₁ ∗ ⋯ ∗ ATMB b'ₖ ∗ R_frame` holds finally for every footprint-local
frame `R_frame`.

The non-aggregate hypotheses rule out frames that own a sub-field cell
`(allocId, k + 1)` of a tracked aggregate pointee, which a whole-slot write
would change.
-/
theorem sepConjBindings_preserved
    {frameLen : Nat} {bs bs' : List MutBorrowBinding} {R : SepProp}
    {m₀ m : Memory}
    (hSep : SepProp.holdsIn (sepConjBindings bs R) m₀)
    (hStack₀ : m₀.callStack = [])
    (hOff₀ : ∀ b ∈ bs, b.rp.offset = 0)
    (hKeys : bs'.map (·.rp) = bs.map (·.rp))
    (hInv : SepLensStateInv frameLen (bs'.map MutBorrowBinding.entry) m)
    (hPres : LensFramePreserved (bs.map MutBorrowBinding.entry) m₀ m)
    (hR : LocalSepProp R)
    (hNotAgg₀ : ∀ b ∈ bs, ∀ elems, b.codec.encode b.val ≠ .aggregate 0 elems)
    (hNotAgg : ∀ b ∈ bs', ∀ elems, b.codec.encode b.val ≠ .aggregate 0 elems) :
    SepProp.holdsIn (sepConjBindings bs' R) m := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split hSep with
    ⟨hBind₀, hPair, _, fpR, hR₀, hDisjR, _, _⟩
  have hML₀ : memoryLocals m₀ = m₀.callerLocals :=
    memoryLocals_of_callStack_nil hStack₀
  have hML : memoryLocals m = m.callerLocals :=
    memoryLocals_of_callStack_nil hInv.callStack_nil
  -- Every updated binding shares its pointer with an initial binding.
  have hSameRp :
      ∀ b' ∈ bs', ∃ b ∈ bs, b.rp = b'.rp := by
    intro b' hb'
    have hIn : b'.rp ∈ bs.map (·.rp) := by
      rw [← hKeys]
      exact List.mem_map.mpr ⟨b', hb', rfl⟩
    rcases List.mem_map.mp hIn with ⟨b, hb, hEq⟩
    exact ⟨b, hb, hEq⟩
  have hFinal :
      ∀ b' ∈ bs',
        get? m.callerLocals b'.rp.allocId =
            some (.init (b'.codec.encode b'.val)) ∧
          TreeExclusiveBorrow b'.rp m := by
    intro b' hb'
    have hMemE : b'.entry ∈ bs'.map MutBorrowBinding.entry :=
      List.mem_map.mpr ⟨b', hb', rfl⟩
    rcases hInv.entries_valid _ _ hMemE with ⟨_, _, hCaller, hExcl⟩
    exact ⟨hCaller, hExcl⟩
  -- (1) The frame footprint `fpR` agrees between `m₀` and `m`.
  have hAgree : AgreeOnFootprint fpR m₀ m := by
    refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
    · rw [hML₀, hML]
      by_cases hTracked : ∃ b ∈ bs, b.rp.allocId = allocId
      · rcases hTracked with ⟨b, hb, hAlloc⟩
        have hOffNe : offset ≠ 0 := by
          intro hZ
          apply (hDisjR b hb).1
          show (b.rp.allocId, b.rp.offset) ∈ fpR.addrs
          rw [hAlloc, hOff₀ b hb, ← hZ]
          exact hIn
        obtain ⟨k, rfl⟩ : ∃ k, offset = k + 1 :=
          Nat.exists_eq_succ_of_ne_zero hOffNe
        have hRpIn : b.rp ∈ bs'.map (·.rp) := by
          rw [hKeys]
          exact List.mem_map.mpr ⟨b, hb, rfl⟩
        rcases List.mem_map.mp hRpIn with ⟨b', hb', hRpEq⟩
        have hOld :
            get? m₀.callerLocals allocId =
              some (.init (b.codec.encode b.val)) := by
          rw [← hAlloc]
          exact callerLocals_get?_of_pointsTo hStack₀ (hOff₀ b hb)
            (hBind₀ b hb).1
        have hNew :
            get? m.callerLocals allocId =
              some (.init (b'.codec.encode b'.val)) := by
          rw [← hAlloc, ← hRpEq]
          exact (hFinal b' hb').1
        rw [readAllocAt_succ_of_not_aggregate hOld (hNotAgg₀ b hb),
          readAllocAt_succ_of_not_aggregate hNew (hNotAgg b' hb')]
      · have hOut :
            ∀ e ∈ bs.map MutBorrowBinding.entry, allocId ≠ e.1.allocId := by
          intro e he hEq
          rcases List.mem_map.mp he with ⟨b, hb, rfl⟩
          exact hTracked ⟨b, hb, hEq.symm⟩
        unfold readAllocAt?
        rw [hPres.locals_unchanged_outside allocId hOut]
    · have hOut :
          ∀ e ∈ bs.map MutBorrowBinding.entry, tag ≠ e.1.tag := by
        intro e he hEq
        rcases List.mem_map.mp he with ⟨b, hb, rfl⟩
        have hEq' : tag = b.rp.tag := hEq
        apply (hDisjR b hb).2
        rw [← hEq']
        exact hIn
      exact (hPres.borrows_unchanged_outside tag hOut).symm
  -- (2) The footprint-local frame therefore still holds in `m`.
  have hRm : R ⟨m, fpR⟩ := hR fpR m₀ m hAgree hR₀
  -- (3) Recompose the updated bindings with the preserved frame.
  have hBind' :
      ∀ b ∈ bs',
        readAllocAt? (memoryLocals m) b.rp = some (b.codec.encode b.val) ∧
        ∃ entry,
          lookupBorrow m.borrows b.rp.tag = some entry ∧
          entry.targetLocal = b.rp.allocId ∧
          entry.perm = .active := by
    intro b' hb'
    rcases hFinal b' hb' with ⟨hCaller, hExcl⟩
    rcases hExcl.lookup_active with ⟨entry, hLook, hT, _, hPerm, _⟩
    refine ⟨?_, entry, hLook, hT, hPerm⟩
    rw [hML]
    unfold readAllocAt?
    rw [hCaller, hExcl.offset_zero]
  have hPairRp :
      (bs.map (·.rp)).Pairwise
        (fun r₁ r₂ => (r₁.allocId, r₁.offset) ≠ (r₂.allocId, r₂.offset) ∧
          r₁.tag ≠ r₂.tag) :=
    List.pairwise_map.mpr hPair
  have hPair' :
      bs'.Pairwise (fun b₁ b₂ => b₁.cell ≠ b₂.cell ∧ b₁.rp.tag ≠ b₂.rp.tag) := by
    rw [← hKeys] at hPairRp
    exact List.pairwise_map.mp hPairRp
  have hDisjR' : ∀ b ∈ bs', b.cell ∉ fpR.addrs ∧ b.rp.tag ∉ fpR.tags := by
    intro b' hb'
    rcases hSameRp b' hb' with ⟨b, hb, hEq⟩
    have hCellEq : b'.cell = b.cell := by
      unfold MutBorrowBinding.cell
      rw [hEq]
    rw [hCellEq, ← hEq]
    exact hDisjR b hb
  exact ⟨_, sepConjBindings_intro hBind' hPair' hRm hDisjR'⟩

/--
A separation-logic proposition `R` is root-allocation-addressed
(`RootAllocSepProp R`) when every address cell `(allocId, offset)` in the
footprint of any partial heap satisfying `R` sits at `offset = 0`.

This holds for `emp`, `BorrowToken`, root `PointsTo` (`rp.offset = 0`), root
`ActiveTypedMutBorrow` (`rp.offset = 0`), and is closed under `sepConj`. When a
frame `R` satisfies `RootAllocSepProp R`, disjointness from `(b.rp.allocId, 0)`
automatically guarantees disjointness from every cell `(b.rp.allocId, offset)`
of `b.rp.allocId`, so `sepConjBindings_preserved_of_rootAlloc` preserves
`sepConjBindings bs' R` even when the tracked pointees are tuples or structs
(`.aggregate 0 elems`).
-/
def RootAllocSepProp (R : SepProp) : Prop :=
  ∀ h : PartialHeap, R h →
    ∀ allocId offset, (allocId, offset) ∈ h.footprint.addrs → offset = 0

theorem rootAllocSepProp_emp : RootAllocSepProp emp := by
  intro h hEmp allocId offset hIn
  rw [hEmp] at hIn
  nomatch hIn

theorem rootAllocSepProp_borrowToken (rp : RawPtrVal) (perm : TreeBorrowPerm) :
    RootAllocSepProp (BorrowToken rp perm) := by
  intro h ⟨_, hFp⟩ allocId offset hIn
  rw [hFp] at hIn
  nomatch hIn

theorem rootAllocSepProp_pointsTo {rp : RawPtrVal} (v : Value)
    (hOff : rp.offset = 0) :
    RootAllocSepProp (PointsTo rp v) := by
  intro h ⟨_, hFp⟩ allocId offset hIn
  rw [hFp] at hIn
  have hEq := List.mem_singleton.mp hIn
  injection hEq with _ hO
  exact hO.trans hOff

theorem rootAllocSepProp_activeTypedMutBorrow {α : Type} {rp : RawPtrVal}
    (codec : ValueCodec α) (a : α) (hOff : rp.offset = 0) :
    RootAllocSepProp (ActiveTypedMutBorrow rp codec a) := by
  intro h ⟨h₁, h₂, ⟨_, _, _, hAddrs, _⟩, ⟨_, hFp₁⟩, ⟨_, hFp₂⟩⟩ allocId offset hIn
  rcases (hAddrs (allocId, offset)).mp hIn with hIn₁ | hIn₂
  · rw [hFp₁] at hIn₁
    have hEq := List.mem_singleton.mp hIn₁
    injection hEq with _ hO
    exact hO.trans hOff
  · rw [hFp₂] at hIn₂
    nomatch hIn₂

theorem rootAllocSepProp_sepConj {P Q : SepProp}
    (hP : RootAllocSepProp P) (hQ : RootAllocSepProp Q) :
    RootAllocSepProp (sepConj P Q) := by
  intro h ⟨h₁, h₂, ⟨_, _, _, hAddrs, _⟩, hP₁, hQ₂⟩ allocId offset hIn
  rcases (hAddrs (allocId, offset)).mp hIn with hIn₁ | hIn₂
  · exact hP h₁ hP₁ allocId offset hIn₁
  · exact hQ h₂ hQ₂ allocId offset hIn₂

/--
Aggregate-capable `k`-Lens Exit Bridge: when the frame `R` satisfies
`RootAllocSepProp R` (in addition to `LocalSepProp R`), `sepConjBindings bs' R`
is preserved across `LensFramePreserved` for arbitrary pointee codecs—including
tuples and structs whose encoded values have the form `.aggregate 0 elems`.
-/
theorem sepConjBindings_preserved_of_rootAlloc
    {frameLen : Nat} {bs bs' : List MutBorrowBinding} {R : SepProp}
    {m₀ m : Memory}
    (hSep : SepProp.holdsIn (sepConjBindings bs R) m₀)
    (hStack₀ : m₀.callStack = [])
    (hOff₀ : ∀ b ∈ bs, b.rp.offset = 0)
    (hKeys : bs'.map (·.rp) = bs.map (·.rp))
    (hInv : SepLensStateInv frameLen (bs'.map MutBorrowBinding.entry) m)
    (hPres : LensFramePreserved (bs.map MutBorrowBinding.entry) m₀ m)
    (hR : LocalSepProp R)
    (hRootR : RootAllocSepProp R) :
    SepProp.holdsIn (sepConjBindings bs' R) m := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split hSep with
    ⟨_, hPair, _, fpR, hR₀, hDisjR, _, _⟩
  have hML₀ : memoryLocals m₀ = m₀.callerLocals :=
    memoryLocals_of_callStack_nil hStack₀
  have hML : memoryLocals m = m.callerLocals :=
    memoryLocals_of_callStack_nil hInv.callStack_nil
  have hSameRp :
      ∀ b' ∈ bs', ∃ b ∈ bs, b.rp = b'.rp := by
    intro b' hb'
    have hIn : b'.rp ∈ bs.map (·.rp) := by
      rw [← hKeys]
      exact List.mem_map.mpr ⟨b', hb', rfl⟩
    rcases List.mem_map.mp hIn with ⟨b, hb, hEq⟩
    exact ⟨b, hb, hEq⟩
  have hFinal :
      ∀ b' ∈ bs',
        get? m.callerLocals b'.rp.allocId =
            some (.init (b'.codec.encode b'.val)) ∧
          TreeExclusiveBorrow b'.rp m := by
    intro b' hb'
    have hMemE : b'.entry ∈ bs'.map MutBorrowBinding.entry :=
      List.mem_map.mpr ⟨b', hb', rfl⟩
    rcases hInv.entries_valid _ _ hMemE with ⟨_, _, hCaller, hExcl⟩
    exact ⟨hCaller, hExcl⟩
  have hAgree : AgreeOnFootprint fpR m₀ m := by
    refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
    · rw [hML₀, hML]
      have hOffZ : offset = 0 := hRootR ⟨m₀, fpR⟩ hR₀ allocId offset hIn
      have hOut :
          ∀ e ∈ bs.map MutBorrowBinding.entry, allocId ≠ e.1.allocId := by
        intro e he hEq
        rcases List.mem_map.mp he with ⟨b, hb, rfl⟩
        apply (hDisjR b hb).1
        show (b.rp.allocId, b.rp.offset) ∈ fpR.addrs
        have hAllocEq : b.rp.allocId = allocId := hEq.symm
        rw [hAllocEq, hOff₀ b hb, ← hOffZ]
        exact hIn
      unfold readAllocAt?
      rw [hPres.locals_unchanged_outside allocId hOut]
    · have hOut :
          ∀ e ∈ bs.map MutBorrowBinding.entry, tag ≠ e.1.tag := by
        intro e he hEq
        rcases List.mem_map.mp he with ⟨b, hb, rfl⟩
        have hEq' : tag = b.rp.tag := hEq
        apply (hDisjR b hb).2
        rw [← hEq']
        exact hIn
      exact (hPres.borrows_unchanged_outside tag hOut).symm
  have hRm : R ⟨m, fpR⟩ := hR fpR m₀ m hAgree hR₀
  have hBind' :
      ∀ b ∈ bs',
        readAllocAt? (memoryLocals m) b.rp = some (b.codec.encode b.val) ∧
        ∃ entry,
          lookupBorrow m.borrows b.rp.tag = some entry ∧
          entry.targetLocal = b.rp.allocId ∧
          entry.perm = .active := by
    intro b' hb'
    rcases hFinal b' hb' with ⟨hCaller, hExcl⟩
    rcases hExcl.lookup_active with ⟨entry, hLook, hT, _, hPerm, _⟩
    refine ⟨?_, entry, hLook, hT, hPerm⟩
    rw [hML]
    unfold readAllocAt?
    rw [hCaller, hExcl.offset_zero]
  have hPairRp :
      (bs.map (·.rp)).Pairwise
        (fun r₁ r₂ => (r₁.allocId, r₁.offset) ≠ (r₂.allocId, r₂.offset) ∧
          r₁.tag ≠ r₂.tag) :=
    List.pairwise_map.mpr hPair
  have hPair' :
      bs'.Pairwise (fun b₁ b₂ => b₁.cell ≠ b₂.cell ∧ b₁.rp.tag ≠ b₂.rp.tag) := by
    rw [← hKeys] at hPairRp
    exact List.pairwise_map.mp hPairRp
  have hDisjR' : ∀ b ∈ bs', b.cell ∉ fpR.addrs ∧ b.rp.tag ∉ fpR.tags := by
    intro b' hb'
    rcases hSameRp b' hb' with ⟨b, hb, hEq⟩
    have hCellEq : b'.cell = b.cell := by
      unfold MutBorrowBinding.cell
      rw [hEq]
    rw [hCellEq, ← hEq]
    exact hDisjR b hb
  exact ⟨_, sepConjBindings_intro hBind' hPair' hRm hDisjR'⟩

/-! ### Indexed Families of Pairwise-Independent Lawful Lenses -/

/--
Validity domain shared by a whole family of binding lenses: every binding's
lens is individually valid and the bindings occupy pairwise distinct
allocations.
-/
structure ValidMutBorrowFamily (bs : List MutBorrowBinding) (m : Memory) :
    Prop where
  valid : ∀ b ∈ bs, ValidMutBorrowLens b.rp b.codec m
  pairwise_alloc : bs.Pairwise (fun b₁ b₂ => b₁.rp.allocId ≠ b₂.rp.allocId)

theorem eq_of_pairwise_ne_of_mem {β : Type u} {γ : Type v} {f : β → γ} :
    ∀ {xs : List β} {x y : β},
      xs.Pairwise (fun a b => f a ≠ f b) → x ∈ xs → y ∈ xs → f x = f y →
        x = y
  | [], _, _, _, hx, _, _ => nomatch hx
  | z :: zs, x, y, hP, hx, hy, hEq => by
    rcases List.pairwise_cons.mp hP with ⟨hHead, hTail⟩
    rcases List.mem_cons.mp hx with hxz | hx'
    · rcases List.mem_cons.mp hy with hyz | hy'
      · rw [hxz, hyz]
      · rw [hxz] at hEq
        exact absurd hEq (hHead y hy')
    · rcases List.mem_cons.mp hy with hyz | hy'
      · rw [hyz] at hEq
        exact absurd hEq.symm (hHead x hx')
      · exact eq_of_pairwise_ne_of_mem hTail hx' hy' hEq

/--
Writing through one member lens preserves the validity of the whole family:
the written pointee keeps a typed value, and every other member's pointee and
the borrow table are unchanged.
-/
theorem ValidMutBorrowFamily.writeBack
    {bs : List MutBorrowBinding} {m : Memory} {b : MutBorrowBinding}
    (hb : b ∈ bs) (hValid : ValidMutBorrowFamily bs m) (a : b.α) :
    ValidMutBorrowFamily bs ((memoryPtrMutLens b.rp b.codec).writeBack a m) := by
  refine ⟨fun b' hb' => ?_, hValid.pairwise_alloc⟩
  by_cases hEq : b'.rp.allocId = b.rp.allocId
  · have hSame : b' = b :=
      eq_of_pairwise_ne_of_mem hValid.pairwise_alloc hb' hb hEq
    subst hSame
    exact (memoryPtrMutLens_lawful b'.rp b'.codec).valid_writeBack a m
      (hValid.valid b' hb')
  · rcases hValid.valid b hb with ⟨⟨a₀, hPts⟩, hExcl⟩
    rcases hValid.valid b' hb' with ⟨⟨a₀', hPts'⟩, hExcl'⟩
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive b.rp b.codec a hPts hExcl]
    exact ⟨⟨a₀', pointsTo_updateMemoryLocals_set_ne (Ne.symm hEq)
        hExcl'.offset_zero hPts'⟩,
      ExclusiveActiveBorrow.of_borrows_eq hExcl'
        (updateMemoryLocals_borrows _ _)⟩

/-- Each member lens of a valid family is a `LawfulMutLens` on the family. -/
theorem memoryPtrMutLens_lawful_family
    {bs : List MutBorrowBinding} {b : MutBorrowBinding} (hb : b ∈ bs) :
    LawfulMutLens (memoryPtrMutLens b.rp b.codec) (ValidMutBorrowFamily bs) where
  valid_writeBack a _ hm := hm.writeBack hb a
  readView_writeBack a m hm :=
    (memoryPtrMutLens_lawful b.rp b.codec).readView_writeBack a m (hm.valid b hb)
  writeBack_readView m hm :=
    (memoryPtrMutLens_lawful b.rp b.codec).writeBack_readView m (hm.valid b hb)
  writeBack_writeBack a₁ a₂ m hm :=
    (memoryPtrMutLens_lawful b.rp b.codec).writeBack_writeBack a₁ a₂ m
      (hm.valid b hb)

/-- Two member lenses on distinct allocations are independent on the family. -/
theorem memoryPtrMutLens_independent_family
    {bs : List MutBorrowBinding} {b₁ b₂ : MutBorrowBinding}
    (hb₁ : b₁ ∈ bs) (hb₂ : b₂ ∈ bs) (hNe : b₁.rp.allocId ≠ b₂.rp.allocId) :
    IndependentLenses
      (memoryPtrMutLens b₁.rp b₁.codec)
      (memoryPtrMutLens b₂.rp b₂.codec)
      (ValidMutBorrowFamily bs) := by
  have hPair :=
    memoryPtrMutLens_independent_of_ne_alloc b₁.rp b₂.rp b₁.codec b₂.codec
  have toPair :
      ∀ m, ValidMutBorrowFamily bs m →
        ValidMutBorrowLensPair b₁.rp b₂.rp b₁.codec b₂.codec m :=
    fun m hm => ⟨hm.valid b₁ hb₁, hm.valid b₂ hb₂, hNe⟩
  exact {
    valid_writeBack_left := fun a m hm => hm.writeBack hb₁ a
    valid_writeBack_right := fun a m hm => hm.writeBack hb₂ a
    readView_right_of_writeBack_left := fun a m hm =>
      hPair.readView_right_of_writeBack_left a m (toPair m hm)
    readView_left_of_writeBack_right := fun a m hm =>
      hPair.readView_left_of_writeBack_right a m (toPair m hm)
    writeBack_comm := fun a a' m hm => hPair.writeBack_comm a a' m (toPair m hm)
  }

/--
`k`-ary (indexed-family) separation-to-lens bridge: a `k`-ary separating
conjunction of typed mutable borrows whose pointers are exclusive yields a
valid lens family in which every member lens is lawful and every pair of
distinct indices is independent.
-/
theorem sepConjBindings_entails_independentLensFamily
    {bs : List MutBorrowBinding} {R : SepProp} {m : Memory}
    (hSep : SepProp.holdsIn (sepConjBindings bs R) m)
    (hExcl : ∀ b ∈ bs, ExclusiveActiveBorrow b.rp m) :
    ValidMutBorrowFamily bs m ∧
    (∀ (i : Nat) (hi : i < bs.length),
      LawfulMutLens
        (memoryPtrMutLens bs[i].rp bs[i].codec) (ValidMutBorrowFamily bs)) ∧
    (∀ (i j : Nat) (hi : i < bs.length) (hj : j < bs.length), i ≠ j →
      IndependentLenses
        (memoryPtrMutLens bs[i].rp bs[i].codec)
        (memoryPtrMutLens bs[j].rp bs[j].codec)
        (ValidMutBorrowFamily bs)) := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split hSep with ⟨hBind, hPair, _, _⟩
  have hPairAlloc :
      bs.Pairwise (fun b₁ b₂ => b₁.rp.allocId ≠ b₂.rp.allocId) := by
    refine List.Pairwise.imp_of_mem ?_ hPair
    intro b₁ b₂ hb₁ hb₂ hNe hAlloc
    apply hNe.1
    show (b₁.rp.allocId, b₁.rp.offset) = (b₂.rp.allocId, b₂.rp.offset)
    rw [hAlloc, (hExcl b₁ hb₁).offset_zero, (hExcl b₂ hb₂).offset_zero]
  have hValid : ValidMutBorrowFamily bs m :=
    ⟨fun b hb => ⟨⟨b.val, (hBind b hb).1⟩, hExcl b hb⟩, hPairAlloc⟩
  refine ⟨hValid, fun i hi => memoryPtrMutLens_lawful_family
    (List.getElem_mem hi), fun i j hi hj hNe => ?_⟩
  refine memoryPtrMutLens_independent_family
    (List.getElem_mem hi) (List.getElem_mem hj) ?_
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
  · exact List.pairwise_iff_getElem.mp hPairAlloc i j hi hj hLt
  · exact Ne.symm (List.pairwise_iff_getElem.mp hPairAlloc j i hj hi hGt)

/--
Homogeneous `List` form of the family bridge: for a single pointee type `α` and
codec, the lens list is `PairwiseIndependentLenses` on the family domain.
-/
theorem sepConjBindings_entails_pairwiseIndependentLenses
    {α : Type} {codec : ValueCodec α} {ptrs : List (RawPtrVal × α)}
    {R : SepProp} {m : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConjBindings (ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2) R)
        m)
    (hExcl : ∀ p ∈ ptrs, ExclusiveActiveBorrow p.1 m) :
    ValidMutBorrowFamily
        (ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2) m ∧
    PairwiseIndependentLenses
      (ValidMutBorrowFamily
        (ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2))
      (ptrs.map fun p => memoryPtrMutLens p.1 codec) := by
  let bs := ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2
  have hExcl' : ∀ b ∈ bs, ExclusiveActiveBorrow b.rp m := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
    exact hExcl p hp
  rcases sepConjBindings_entails_independentLensFamily hSep hExcl' with
    ⟨hValid, _, _⟩
  refine ⟨hValid, ?_⟩
  have hPairPtr :
      ptrs.Pairwise (fun p₁ p₂ => p₁.1.allocId ≠ p₂.1.allocId) := by
    have h := hValid.pairwise_alloc
    rw [List.pairwise_map] at h
    exact h
  -- Induct over every suffix of `ptrs`, keeping the family domain fixed.
  have hSuffix :
      ∀ sfx : List (RawPtrVal × α),
        (∀ p ∈ sfx, p ∈ ptrs) →
        sfx.Pairwise (fun p₁ p₂ => p₁.1.allocId ≠ p₂.1.allocId) →
        PairwiseIndependentLenses (ValidMutBorrowFamily bs)
          (sfx.map fun p => memoryPtrMutLens p.1 codec) := by
    intro sfx
    induction sfx with
    | nil => intro _ _; exact .nil
    | cons p rest ih =>
      intro hSub hPairSfx
      rcases List.pairwise_cons.mp hPairSfx with ⟨hHead, hTail⟩
      have hp : MutBorrowBinding.bind p.1 codec p.2 ∈ bs :=
        List.mem_map.mpr ⟨p, hSub p (List.Mem.head rest), rfl⟩
      refine .cons (memoryPtrMutLens_lawful_family hp) ?_
        (ih (fun q hq => hSub q (List.Mem.tail p hq)) hTail)
      intro L hL
      rcases List.mem_map.mp hL with ⟨q, hq, rfl⟩
      have hq' : MutBorrowBinding.bind q.1 codec q.2 ∈ bs :=
        List.mem_map.mpr ⟨q, hSub q (List.Mem.tail p hq), rfl⟩
      exact memoryPtrMutLens_independent_family hp hq' (hHead q hq)
  exact hSuffix ptrs (fun _ h => h) hPairPtr

/-! ### `I-10`-Aware Mutable Borrow Lenses (`treeMemoryPtrMutLens`) -/

/--
`I-10`-aware Tree Borrows access step for `rp` on `m`. Unlike
`stepTreeBorrowAccess?` (which uses the flat `invalidateConflictingBorrows`
helper and never freezes on reads), a read applies the `I-10` foreign-read
transition `freezeTreeBorrowsOnReadAtProj` and a write applies the `I-10`
parent/child invalidation `invalidateTreeBorrowsAtProj`, mirroring the MIR
deref-read and deref-write paths, so active ancestors of `rp.tag` stay
`.active` under child accesses.
-/
def stepTreeBorrowHierarchyAccess?
    (m : Memory) (rp : RawPtrVal) (isWrite : Bool) : Option Memory :=
  match lookupBorrow m.borrows rp.tag with
  | .some entry =>
    match entry.perm, isWrite with
    | .disabled, _ => .none
    | .frozen, true => .none
    | _, false =>
      .some { m with
        borrows :=
          freezeTreeBorrowsOnReadAtProj m.borrows m.borrows entry.targetLocal
            (.some rp.tag) entry.targetProjection entry.rangeOffset
            entry.rangeLen }
    | .active, true | .reserved, true =>
      .some { m with
        borrows :=
          invalidateTreeBorrowsAtProj m.borrows m.borrows entry.targetLocal
            (.some rp.tag) entry.targetProjection entry.rangeOffset
            entry.rangeLen }
  | .none => .none

/--
`I-10`-aware `MutLens Memory α` backed by an active Tree Borrows pointer `rp`:
identical to `memoryPtrMutLens rp codec` on reads and pointee updates, except
that `writeBack` steps the borrow table via `stepTreeBorrowHierarchyAccess?` so
that `I-10` parent/child reborrow chains (`TreeExclusiveBorrow`) satisfy all
algebraic lens laws without requiring the ancestor-free `ExclusiveActiveBorrow`.
-/
def treeMemoryPtrMutLens (rp : RawPtrVal) (codec : ValueCodec α) :
    MutLens Memory α where
  readView m := (memoryPtrMutLens rp codec).readView m
  writeBack a m :=
    let m₁ := (stepTreeBorrowHierarchyAccess? m rp true).getD m
    match writeAllocAt? (memoryLocals m₁) rp (codec.encode a) with
    | some locals' => updateMemoryLocals m₁ locals'
    | none => m₁

theorem stepTreeBorrowHierarchyAccess_write_eq_some_self_of_tree
    {rp : RawPtrVal} {m : Memory}
    (hExcl : TreeExclusiveBorrow rp m) :
    stepTreeBorrowHierarchyAccess? m rp true = .some m := by
  rcases hExcl.lookup_active with
    ⟨entry, hLook, hTarget, hProj, hPerm, hRO, hRL⟩
  unfold stepTreeBorrowHierarchyAccess?
  rw [hLook]
  dsimp only
  rw [hPerm, hTarget, hProj, hRO, hRL]
  simp only [
    invalidateTreeBorrowsAtProj_eq_self_of_tree m.borrows m.borrows [] 0 0
      hExcl.ancestors_active_or_disabled]

/-- Under `TreeExclusiveBorrow`, an `I-10` read through `rp` freezes nothing. -/
theorem stepTreeBorrowHierarchyAccess_read_eq_some_self_of_tree
    {rp : RawPtrVal} {m : Memory}
    (hExcl : TreeExclusiveBorrow rp m) :
    stepTreeBorrowHierarchyAccess? m rp false = .some m := by
  rcases hExcl.lookup_active with
    ⟨entry, hLook, hTarget, hProj, hPerm, hRO, hRL⟩
  unfold stepTreeBorrowHierarchyAccess?
  rw [hLook]
  dsimp only
  rw [hPerm, hTarget, hProj, hRO, hRL]
  simp only [
    freezeTreeBorrowsOnReadAtProj_eq_self_of_tree m.borrows m.borrows [] 0 0
      hExcl.ancestors_active_or_disabled]

theorem treeMemoryPtrMutLens_readView_of_readAllocAt
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {m : Memory}
    (h_read : readAllocAt? (memoryLocals m) rp = some (codec.encode a)) :
    (treeMemoryPtrMutLens rp codec).readView m = a :=
  memoryPtrMutLens_readView_of_readAllocAt h_read

/--
Under `TreeExclusiveBorrow rp m` and an initialized pointee slot,
`(treeMemoryPtrMutLens rp codec).writeBack a m` leaves `m.borrows` (including
all active `I-10` ancestor tags) unchanged and updates `memoryLocals m` at
`rp.allocId` to `.init (codec.encode a)`.
-/
theorem treeMemoryPtrMutLens_writeBack_eq_of_tree
    {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α)
    {m : Memory} {v₀ : Value}
    (hPts : readAllocAt? (memoryLocals m) rp = some v₀)
    (hExcl : TreeExclusiveBorrow rp m) :
    (treeMemoryPtrMutLens rp codec).writeBack a m =
      updateMemoryLocals
        m
        ((memoryLocals m).set rp.allocId (.init (codec.encode a))) := by
  unfold treeMemoryPtrMutLens
  dsimp only
  rw [stepTreeBorrowHierarchyAccess_write_eq_some_self_of_tree hExcl]
  dsimp only [Option.getD]
  unfold readAllocAt? at hPts
  rw [hExcl.offset_zero] at hPts
  unfold writeAllocAt?
  rw [hExcl.offset_zero]
  cases hGet : get? (memoryLocals m) rp.allocId with
  | none => rw [hGet] at hPts; nomatch hPts
  | some slot =>
    rw [hGet] at hPts
    cases slot with
    | dead => nomatch hPts
    | uninit => nomatch hPts
    | init _ =>
      have hLt : rp.allocId < (memoryLocals m).length :=
        (List.getElem?_eq_some_iff.mp hGet).1
      unfold set?
      simp [hLt]

/--
On any memory satisfying the ancestor-free `ExclusiveActiveBorrow rp m`,
`treeMemoryPtrMutLens` and `memoryPtrMutLens` have equal write-backs; their
`readView`s are equal by definition.
-/
theorem treeMemoryPtrMutLens_writeBack_eq_memoryPtrMutLens_of_exclusive
    {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α)
    {m : Memory} {v₀ : Value}
    (hPts : readAllocAt? (memoryLocals m) rp = some v₀)
    (hExcl : ExclusiveActiveBorrow rp m) :
    (treeMemoryPtrMutLens rp codec).writeBack a m =
      (memoryPtrMutLens rp codec).writeBack a m := by
  rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a hPts hExcl.toTree,
    memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a hPts hExcl]

/-! ### MIR Dereference Accesses Are `treeMemoryPtrMutLens` Accesses -/

theorem updateMemoryLocals_of_callStack_nil {m : Memory}
    {locals' : List LocalValue} (h : m.callStack = []) :
    updateMemoryLocals m locals' = { m with callerLocals := locals' } := by
  unfold updateMemoryLocals
  rw [h]

/--
Every lens-state entry is the `I-10` lens view of memory: under
`SepLensStateInv`, the value bound to `rp` is the encoding of
`(treeMemoryPtrMutLens rp codec).readView m`.
-/
theorem SepLensStateInv.treeLens_readView {α : Type}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α}
    (hInv : SepLensStateInv frameLen entries m)
    (hMem : (rp, codec.encode a) ∈ entries) :
    (treeMemoryPtrMutLens rp codec).readView m = a := by
  rcases hInv.entries_valid rp (codec.encode a) hMem with ⟨hOff, _, hCaller, _⟩
  apply treeMemoryPtrMutLens_readView_of_readAllocAt
  rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
  unfold readAllocAt?
  rw [hCaller, hOff]

/--
Alias erasure for reads: a lifted dereference read `*p` of a lens entry that
encodes `a` evaluates, against the real borrow table and caller locals, to the
encoding of the `I-10` lens view `(treeMemoryPtrMutLens rp codec).readView m`,
which equals `a`.
-/
theorem LiftDerefRead.evalOperand_eq_treeLens_readView {α : Type}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {m : Memory} {codec : ValueCodec α} {a : α}
    (h : LiftDerefRead env entries op (codec.encode a) env')
    (hInv : SepLensStateInv env.length entries m)
    (layouts : LayoutTable) :
    ∃ rp : RawPtrVal,
      lookupLensVal? entries rp = .some (codec.encode a) ∧
      (treeMemoryPtrMutLens rp codec).readView m = a ∧
      evalOperand env op m.borrows m.globals layouts m.callerLocals =
        .ok (codec.encode ((treeMemoryPtrMutLens rp codec).readView m)) env' := by
  rcases (h.evalOperand_and_freeze_eq hInv layouts) with ⟨hEval, _, _⟩
  cases h with
  | @copy_deref _ rp _ _ hLook =>
    have hView := hInv.treeLens_readView (lookupLensVal?_mem hLook)
    exact ⟨rp, hLook, hView, by rw [hView]; exact hEval⟩
  | @move_deref _ rp _ _ hLook =>
    have hView := hInv.treeLens_readView (lookupLensVal?_mem hLook)
    exact ⟨rp, hLook, hView, by rw [hView]; exact hEval⟩

/--
Strengthened read alias-erasure and `I-10` read-step equivalence: a lifted
dereference read `*p` of a lens entry encoding `a` not only evaluates
`evalOperand` to `codec.encode ((treeMemoryPtrMutLens rp codec).readView m)`,
but also satisfies `stepTreeBorrowHierarchyAccess? m rp false = .some m` and
leaves `m.borrows` unchanged under `freezeDerefReadBorrowsAt`.
-/
theorem LiftDerefRead.evalOperand_eq_treeLens_readView_and_step {α : Type}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {m : Memory} {codec : ValueCodec α} {a : α}
    (h : LiftDerefRead env entries op (codec.encode a) env')
    (hInv : SepLensStateInv env.length entries m)
    (layouts : LayoutTable) :
    ∃ (ptrLoc : Local) (rp : RawPtrVal),
      lookupLensVal? entries rp = .some (codec.encode a) ∧
      stepTreeBorrowHierarchyAccess? m rp false = .some m ∧
      freezeDerefReadBorrowsAt env ptrLoc [] m.borrows = m.borrows ∧
      (treeMemoryPtrMutLens rp codec).readView m = a ∧
      evalOperand env op m.borrows m.globals layouts m.callerLocals =
        .ok (codec.encode ((treeMemoryPtrMutLens rp codec).readView m)) env' := by
  rcases h.evalOperand_and_freeze_eq hInv layouts with ⟨hEval, _, hFreeze⟩
  cases h with
  | @copy_deref ptrLoc rp _ _ hLook =>
    have hMem := lookupLensVal?_mem hLook
    have hView := hInv.treeLens_readView hMem
    rcases hInv.entries_valid rp (codec.encode a) hMem with ⟨_, _, _, hExcl⟩
    exact ⟨ptrLoc, rp, hLook,
      stepTreeBorrowHierarchyAccess_read_eq_some_self_of_tree hExcl,
      hFreeze ptrLoc [] (Or.inl rfl),
      hView, by rw [hView]; exact hEval⟩
  | @move_deref ptrLoc rp _ _ hLook =>
    have hMem := lookupLensVal?_mem hLook
    have hView := hInv.treeLens_readView hMem
    rcases hInv.entries_valid rp (codec.encode a) hMem with ⟨_, _, _, hExcl⟩
    exact ⟨ptrLoc, rp, hLook,
      stepTreeBorrowHierarchyAccess_read_eq_some_self_of_tree hExcl,
      hFreeze ptrLoc [] (Or.inr rfl),
      hView, by rw [hView]; exact hEval⟩

/--
Alias erasure for projected dereference field reads `(*p).fieldIdx`: when `rp`
points to a variant-`0` aggregate `aggVal = .aggregate 0 elems` in `entries`
and field `fieldIdx` encodes `a : α`, `evalOperand` evaluates to
`codec.encode ((rawFieldMutLens rp.allocId fieldIdx codec).readView m)` and the
`I-10` read step `stepTreeBorrowHierarchyAccess? m rp false` is `.some m`.
-/
theorem LiftDerefFieldRead.evalOperand_eq_rawFieldLens_readView {α : Type}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {m : Memory} {codec : ValueCodec α} {a : α}
    (h : LiftDerefFieldRead env entries op (codec.encode a) env')
    (hInv : SepLensStateInv env.length entries m)
    (hVarZero :
      ∀ rp aggVal,
        lookupLensVal? entries rp = .some aggVal →
        ∃ elems, aggVal = .aggregate 0 elems)
    (layouts : LayoutTable) :
    ∃ (rp : RawPtrVal) (fieldIdx : FieldIdx),
      stepTreeBorrowHierarchyAccess? m rp false = .some m ∧
      (rawFieldMutLens rp.allocId fieldIdx codec).readView m = a ∧
      evalOperand env op m.borrows m.globals layouts m.callerLocals =
        .ok
          (codec.encode
            ((rawFieldMutLens rp.allocId fieldIdx codec).readView m))
          env' := by
  have hEval :
      evalOperand env op m.borrows m.globals layouts m.callerLocals =
        .ok (codec.encode a) env' :=
    (h.evalOperand_and_freeze_eq hInv layouts).1
  cases h with
  | copy_deref_field hGetPtr hLook hRead =>
    rename_i ptrLoc fieldIdx fieldTy rp aggVal
    have hMem := lookupLensVal?_mem hLook
    rcases hInv.entries_valid rp aggVal hMem with ⟨_, _, hCaller, hExcl⟩
    rcases hVarZero rp aggVal hLook with ⟨elems, rfl⟩
    unfold readProjectedValue at hRead
    cases hGetF : get? elems fieldIdx with
    | none => rw [hGetF] at hRead; nomatch hRead
    | some fVal =>
      rw [hGetF] at hRead
      dsimp only [readProjectedValue] at hRead
      injection hRead with hFVal
      subst hFVal
      have hFieldAt :
          readFieldAt? (memoryLocals m) rp.allocId fieldIdx =
            .some (codec.encode a) := by
        rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
        unfold readFieldAt?
        rw [hCaller]
        exact hGetF
      have hView :
          (rawFieldMutLens rp.allocId fieldIdx codec).readView m = a :=
        rawFieldMutLens_readView_of_readFieldAt hFieldAt
      exact ⟨rp, fieldIdx,
        stepTreeBorrowHierarchyAccess_read_eq_some_self_of_tree hExcl,
        hView, by rw [hView]; exact hEval⟩
  | move_deref_field hGetPtr hLook hRead =>
    rename_i ptrLoc fieldIdx fieldTy rp aggVal
    have hMem := lookupLensVal?_mem hLook
    rcases hInv.entries_valid rp aggVal hMem with ⟨_, _, hCaller, hExcl⟩
    rcases hVarZero rp aggVal hLook with ⟨elems, rfl⟩
    unfold readProjectedValue at hRead
    cases hGetF : get? elems fieldIdx with
    | none => rw [hGetF] at hRead; nomatch hRead
    | some fVal =>
      rw [hGetF] at hRead
      dsimp only [readProjectedValue] at hRead
      injection hRead with hFVal
      subst hFVal
      have hFieldAt :
          readFieldAt? (memoryLocals m) rp.allocId fieldIdx =
            .some (codec.encode a) := by
        rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
        unfold readFieldAt?
        rw [hCaller]
        exact hGetF
      have hView :
          (rawFieldMutLens rp.allocId fieldIdx codec).readView m = a :=
        rawFieldMutLens_readView_of_readFieldAt hFieldAt
      exact ⟨rp, fieldIdx,
        stepTreeBorrowHierarchyAccess_read_eq_some_self_of_tree hExcl,
        hView, by rw [hView]; exact hEval⟩

/--
Alias erasure for projected dereference field writes `((*p).fieldIdx) = rv`:
when `rp` points to an initialized variant-`0` aggregate `.aggregate 0 elems`
with an in-bounds field `fieldIdx` and `rv` lifts to `codec.encode a`,
`evalStmt` steps to `m' = (rawFieldMutLens rp.allocId fieldIdx codec).writeBack
a s.memory`, preserving `ValidRawFieldLens`, reading back `a` (`PutGet`), and
leaving every sibling field `fieldIdx₂ ≠ fieldIdx` on `rp.allocId` untouched.
-/
theorem LiftDerefWrite.field_evalStmt_eq_rawFieldLens_writeBack {α : Type}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {ptrLoc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {rv : Rvalue} {sp : String} {rp : RawPtrVal}
    {elems : List Value} {oldFieldVal newAgg : Value}
    {codec : ValueCodec α} {a : α} {s : MachineState}
    (hRv :
      LiftLensRvalue localDecls layouts env entries rv (codec.encode a) env')
    (hGetPtr : get? env' ptrLoc = .some (.init rp.toMirValue))
    (hLookVal : lookupLensVal? entries rp = .some (.aggregate 0 elems))
    (hElem : get? elems fieldIdx = .some oldFieldVal)
    (hWriteProj :
      writeProjectedValue env' (.aggregate 0 elems)
        [.field fieldIdx fieldTy] (codec.encode a) = .ok newAgg)
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory) :
    let m' := (rawFieldMutLens rp.allocId fieldIdx codec).writeBack a s.memory
    evalStmt s
      { kind :=
          .assign
            { local_ := ptrLoc, projection := [.deref, .field fieldIdx fieldTy] }
            rv,
        span := sp }
      localDecls layouts =
      MirStepNode.step (advanceStmt s env' m') ∧
    ValidRawFieldLens rp.allocId fieldIdx codec m' ∧
    (rawFieldMutLens rp.allocId fieldIdx codec).readView m' = a ∧
    (∀ {β : Type} (fieldIdx₂ : FieldIdx) (codec₂ : ValueCodec β),
      fieldIdx ≠ fieldIdx₂ →
      ValidRawFieldLens rp.allocId fieldIdx₂ codec₂ s.memory →
      ValidRawFieldLens rp.allocId fieldIdx₂ codec₂ m' ∧
      (rawFieldMutLens rp.allocId fieldIdx₂ codec₂).readView m' =
        (rawFieldMutLens rp.allocId fieldIdx₂ codec₂).readView s.memory) := by
  have hStep :=
    (LiftDerefWrite.evalStmt_field_eq (sp := sp)
      hRv hGetPtr hLookVal hWriteProj hEnv hInv).2
  rcases hInv.entries_valid rp (.aggregate 0 elems)
      (lookupLensVal?_mem hLookVal) with
    ⟨_, _, hCaller, _⟩
  have hLtF : fieldIdx < elems.length :=
    (List.getElem?_eq_some_iff.mp hElem).1
  have hSetElem :
      set? elems fieldIdx (codec.encode a) =
        .some (elems.set fieldIdx (codec.encode a)) := by
    unfold set?
    simp [hLtF]
  have hNewAgg : newAgg = .aggregate 0 (elems.set fieldIdx (codec.encode a)) := by
    unfold writeProjectedValue at hWriteProj
    rw [hElem] at hWriteProj
    dsimp only [writeProjectedValue] at hWriteProj
    rw [hSetElem] at hWriteProj
    injection hWriteProj with hEq
    exact hEq.symm
  have hFieldAt :
      readFieldAt? (memoryLocals s.memory) rp.allocId fieldIdx =
        .some oldFieldVal := by
    rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
    unfold readFieldAt?
    rw [hCaller]
    exact hElem
  have hMemEq :
      (rawFieldMutLens rp.allocId fieldIdx codec).writeBack a s.memory =
        { s.memory with
          callerLocals :=
            s.memory.callerLocals.set rp.allocId (.init newAgg) } := by
    unfold rawFieldMutLens
    dsimp only
    rw [updateMemoryLocals_of_callStack_nil hInv.callStack_nil,
      memoryLocals_of_callStack_nil hInv.callStack_nil]
    unfold writeFieldAt?
    rw [hCaller, hNewAgg]
  refine ⟨by rw [hMemEq]; exact hStep, ?_, ?_, ?_⟩
  · exact ⟨⟨a,
      readFieldAt_updateMemoryLocals_writeFieldAt_self a hFieldAt⟩⟩
  · exact rawFieldMutLens_readView_of_readFieldAt
      (readFieldAt_updateMemoryLocals_writeFieldAt_self a hFieldAt)
  · intro β fieldIdx₂ codec₂ hNe ⟨⟨b₀, hField₂⟩⟩
    have hField₂' :
        readFieldAt?
          (memoryLocals
            ((rawFieldMutLens rp.allocId fieldIdx codec).writeBack a s.memory))
          rp.allocId fieldIdx₂ = .some (codec₂.encode b₀) :=
      readFieldAt_updateMemoryLocals_writeFieldAt_ne hNe hFieldAt hField₂
    exact ⟨⟨⟨b₀, hField₂'⟩⟩,
      (rawFieldMutLens_readView_of_readFieldAt hField₂').trans
        (rawFieldMutLens_readView_of_readFieldAt hField₂).symm⟩

/--
Alias erasure for writes: a lifted dereference write `*p = rv` steps
`evalStmt` to exactly `(treeMemoryPtrMutLens rp codec).writeBack a s.memory`
for any codec value `a` encoding the new pointee value: the MIR write is the
`I-10` lens write-back at the written pointer.
-/
theorem LiftDerefWrite.evalStmt_eq_treeLens_writeBack
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState}
    (hWrite : LiftDerefWrite localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory) :
    ∃ (rp : RawPtrVal) (newVal : Value),
      entries' = updateLensVal entries rp newVal ∧
      ∀ {α : Type} (codec : ValueCodec α) (a : α),
        codec.encode a = newVal →
        evalStmt s stmt localDecls layouts =
          MirStepNode.step
            (advanceStmt s env'
              ((treeMemoryPtrMutLens rp codec).writeBack a s.memory)) := by
  rcases hWrite.evalStmt_eq hEnv hInv with
    ⟨rp, oldVal, newVal, hLook, hEntries, _, hEval⟩
  refine ⟨rp, newVal, hEntries, fun codec a hEnc => ?_⟩
  rcases hInv.entries_valid rp oldVal (lookupLensVal?_mem hLook) with
    ⟨hOff, _, hCaller, hExcl⟩
  have hPts : readAllocAt? (memoryLocals s.memory) rp = some oldVal := by
    rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
    unfold readAllocAt?
    rw [hCaller, hOff]
  rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a hPts hExcl,
    updateMemoryLocals_of_callStack_nil hInv.callStack_nil,
    memoryLocals_of_callStack_nil hInv.callStack_nil, hEnc]
  exact hEval

/--
Domain validity predicate for an `I-10`-aware mutable borrow lens
`treeMemoryPtrMutLens rp codec`.
-/
structure ValidTreeMutBorrowLens {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) (m : Memory) : Prop where
  has_typed_pointee : ∃ a : α, readAllocAt? (memoryLocals m) rp = some (codec.encode a)
  exclusive : TreeExclusiveBorrow rp m

theorem ValidTreeMutBorrowLens.toRaw {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {m : Memory}
    (hm : ValidTreeMutBorrowLens rp codec m) :
    ValidRawPtrLens rp codec m :=
  ⟨hm.has_typed_pointee, hm.exclusive.offset_zero⟩

theorem ValidMutBorrowLens.toTree {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {m : Memory}
    (h : ValidMutBorrowLens rp codec m) :
    ValidTreeMutBorrowLens rp codec m :=
  ⟨h.has_typed_pointee, h.exclusive.toTree⟩

theorem ValidTreeMutBorrowLens.writeBack {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {m : Memory}
    (a : α) (hm : ValidTreeMutBorrowLens rp codec m) :
    ValidTreeMutBorrowLens rp codec
      ((treeMemoryPtrMutLens rp codec).writeBack a m) := by
  rcases hm with ⟨⟨_, hPts⟩, hExcl⟩
  rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a hPts hExcl]
  exact ⟨⟨a, pointsTo_updateMemoryLocals_set_self a hExcl.offset_zero hPts⟩,
    TreeExclusiveBorrow.of_borrows_eq hExcl (updateMemoryLocals_borrows _ _)⟩

/--
`treeMemoryPtrMutLens rp codec` is a `LawfulMutLens` on
`ValidTreeMutBorrowLens rp codec` (admitting active `I-10` parent/child
reborrow chains), transferred from `rawPtrMutLens_lawful` via
`LawfulMutLens.of_sub_agree`.
-/
theorem treeMemoryPtrMutLens_lawful {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) :
    LawfulMutLens (treeMemoryPtrMutLens rp codec)
      (ValidTreeMutBorrowLens rp codec) :=
  LawfulMutLens.of_sub_agree (rawPtrMutLens_lawful rp codec)
    (fun _ hm => hm.toRaw)
    (fun a _ hm => hm.writeBack a)
    (fun _ _ => rfl)
    (fun a _ ⟨⟨_, hPts⟩, hExcl⟩ =>
      treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a hPts hExcl)

/--
Domain validity predicate for a pair of `I-10`-aware mutable borrow lenses
`treeMemoryPtrMutLens rp₁ codec₁` and `treeMemoryPtrMutLens rp₂ codec₂`.
-/
structure ValidTreeMutBorrowLensPair {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β)
    (m : Memory) : Prop where
  valid_left : ValidTreeMutBorrowLens rp₁ codec₁ m
  valid_right : ValidTreeMutBorrowLens rp₂ codec₂ m
  ne_alloc : rp₁.allocId ≠ rp₂.allocId

/--
Two `treeMemoryPtrMutLens` instances on distinct allocations satisfy
`IndependentLenses` on `ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂`,
transferred from `rawPtrMutLens_independent_of_ne_alloc` via
`IndependentLenses.of_sub_agree`.
-/
theorem treeMemoryPtrMutLens_independent_of_ne_alloc {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    IndependentLenses
      (treeMemoryPtrMutLens rp₁ codec₁)
      (treeMemoryPtrMutLens rp₂ codec₂)
      (ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) :=
  (rawPtrMutLens_independent_of_ne_alloc rp₁ rp₂ codec₁ codec₂).of_sub_agree
    (fun _ hm => ⟨hm.valid_left.toRaw, hm.valid_right.toRaw, hm.ne_alloc⟩)
    (fun a m hm => by
      rcases hm.valid_left with ⟨⟨_, hPts₁⟩, hExcl₁⟩
      rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
      refine ⟨hm.valid_left.writeBack a, ?_, hm.ne_alloc⟩
      rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁ hExcl₁]
      exact ⟨
        ⟨b₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc
          hExcl₂.offset_zero hPts₂⟩,
        TreeExclusiveBorrow.of_borrows_eq hExcl₂
          (updateMemoryLocals_borrows _ _)⟩)
    (fun b m hm => by
      rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
      rcases hm.valid_right with ⟨⟨_, hPts₂⟩, hExcl₂⟩
      refine ⟨?_, hm.valid_right.writeBack b, hm.ne_alloc⟩
      rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂ hExcl₂]
      exact ⟨
        ⟨a₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
          hExcl₁.offset_zero hPts₁⟩,
        TreeExclusiveBorrow.of_borrows_eq hExcl₁
          (updateMemoryLocals_borrows _ _)⟩)
    (fun _ _ => rfl)
    (fun _ _ => rfl)
    (fun a _ hm => by
      rcases hm.valid_left with ⟨⟨_, hPts₁⟩, hExcl₁⟩
      exact treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁ hExcl₁)
    (fun b _ hm => by
      rcases hm.valid_right with ⟨⟨_, hPts₂⟩, hExcl₂⟩
      exact treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂ hExcl₂)

/-! ### Field-Granular `I-10` Borrow Lenses (`treeFieldMemoryPtrMutLens`) -/

/--
`I-10` Tree Borrows exclusivity for a field-granular mutable reborrow `rp`
(`&mut s.f` or `&mut (*r).f`) targeting projection `[.field fieldIdx fieldTy]`
within aggregate slot `rp.allocId`.

Every borrow entry `b ∈ m.borrows` on `rp.allocId` is either:
1. An `.active` `I-10` ancestor-or-self of `rp.tag` (such as the parent struct
   borrow `&mut s` at `targetProjection = []`, or `rp` itself),
2. An `.active` sub-allocation borrow whose projection does not overlap
   `[.field fieldIdx fieldTy]` (`borrowEntryOverlapsWrite = false`, such as a
   sibling field reborrow `&mut s.g` with `g ≠ fieldIdx`), or
3. Already `.disabled`.
-/
structure TreeFieldExclusiveBorrow
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty) (m : Memory) :
    Prop where
  offset_zero : rp.offset = 0
  lookup_active :
    ∃ entry,
      lookupBorrow m.borrows rp.tag = .some entry ∧
      entry.targetLocal = rp.allocId ∧
      entry.targetProjection = [.field fieldIdx fieldTy] ∧
      entry.perm = .active ∧
      entry.rangeOffset = 0 ∧
      entry.rangeLen = 0
  ancestors_disjoint_or_disabled :
    ∀ b ∈ m.borrows,
      b.targetLocal = rp.allocId →
        (isBorrowDescendantOrSelf m.borrows rp.tag b.tag = true ∧
          b.perm = .active) ∨
        (borrowEntryOverlapsWrite b [.field fieldIdx fieldTy] 0 0 = false ∧
          b.perm = .active) ∨
        b.perm = .disabled

theorem TreeFieldExclusiveBorrow.of_borrows_eq
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty} {m₁ m₂ : Memory}
    (h : TreeFieldExclusiveBorrow rp fieldIdx fieldTy m₁)
    (hBorrows : m₂.borrows = m₁.borrows) :
    TreeFieldExclusiveBorrow rp fieldIdx fieldTy m₂ where
  offset_zero := h.offset_zero
  lookup_active := by rw [hBorrows]; exact h.lookup_active
  ancestors_disjoint_or_disabled := by
    rw [hBorrows]; exact h.ancestors_disjoint_or_disabled

theorem freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat} {fieldIdx : FieldIdx} {fieldTy : Ty}
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          (borrowEntryOverlapsWrite b [.field fieldIdx fieldTy] 0 0 = false ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    freezeTreeBorrowsOnReadAtProj
      allBorrows borrows allocId (.some tag)
      [.field fieldIdx fieldTy] 0 0 = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold freezeTreeBorrowsOnReadAtProj
    rw [hTail]
    unfold updateBorrowPermOnReadAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hTree hd (List.Mem.head tl) hTargetEq with
        ⟨hDesc, _⟩ | ⟨hNoOverlap, _⟩ | hDis
      · cases borrowEntryOverlapsWrite hd [.field fieldIdx fieldTy] 0 0 with
        | false => rfl
        | true => dsimp only; rw [hDesc]
      · rw [hNoOverlap]
      · cases borrowEntryOverlapsWrite hd [.field fieldIdx fieldTy] 0 0 with
        | false => rfl
        | true =>
          dsimp only
          cases isBorrowDescendantOrSelf allBorrows tag hd.tag with
          | true => rfl
          | false => dsimp only; rw [hDis]

theorem invalidateTreeBorrowsAtProj_eq_self_of_treeField
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat} {fieldIdx : FieldIdx} {fieldTy : Ty}
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          (borrowEntryOverlapsWrite b [.field fieldIdx fieldTy] 0 0 = false ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    invalidateTreeBorrowsAtProj
      allBorrows borrows allocId (.some tag)
      [.field fieldIdx fieldTy] 0 0 = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold invalidateTreeBorrowsAtProj
    rw [hTail]
    unfold updateBorrowPermTreeAtProj
    unfold updateBorrowPermAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      dsimp only
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hTree hd (List.Mem.head tl) hTargetEq with
        ⟨hDesc, hPerm⟩ | ⟨hNoOverlap, hPerm⟩ | hDis
      · rw [resolveTreeBorrowWriterTag_of_descendant hDesc]
        dsimp only
        have hEq : Nat.beq hd.tag hd.tag = true := by simp
        rw [hEq, hPerm]
      · cases resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
        | none => rw [hNoOverlap]
        | some wTag =>
          dsimp only
          cases Nat.beq hd.tag wTag with
          | true => rw [hPerm]
          | false => rw [hNoOverlap]
      · cases resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
        | none =>
          dsimp only
          cases borrowEntryOverlapsWrite hd [.field fieldIdx fieldTy] 0 0 <;>
            simp [hDis]
        | some wTag =>
          dsimp only
          cases Nat.beq hd.tag wTag with
          | true => simp [hDis]
          | false =>
            dsimp only
            cases borrowEntryOverlapsWrite hd [.field fieldIdx fieldTy] 0 0 with
            | false => rfl
            | true =>
              dsimp only
              rw [borrowEntry_disabled_eta hDis]

theorem stepTreeBorrowHierarchyAccess_write_eq_some_self_of_treeField
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty} {m : Memory}
    (hExcl : TreeFieldExclusiveBorrow rp fieldIdx fieldTy m) :
    stepTreeBorrowHierarchyAccess? m rp true = .some m := by
  rcases hExcl.lookup_active with
    ⟨entry, hLook, hTarget, hProj, hPerm, hRO, hRL⟩
  unfold stepTreeBorrowHierarchyAccess?
  rw [hLook]
  dsimp only
  rw [hPerm, hTarget, hProj, hRO, hRL]
  simp only [
    invalidateTreeBorrowsAtProj_eq_self_of_treeField m.borrows m.borrows
      hExcl.ancestors_disjoint_or_disabled]

theorem stepTreeBorrowHierarchyAccess_read_eq_some_self_of_treeField
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty} {m : Memory}
    (hExcl : TreeFieldExclusiveBorrow rp fieldIdx fieldTy m) :
    stepTreeBorrowHierarchyAccess? m rp false = .some m := by
  rcases hExcl.lookup_active with
    ⟨entry, hLook, hTarget, hProj, hPerm, hRO, hRL⟩
  unfold stepTreeBorrowHierarchyAccess?
  rw [hLook]
  dsimp only
  rw [hPerm, hTarget, hProj, hRO, hRL]
  simp only [
    freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField m.borrows m.borrows
      hExcl.ancestors_disjoint_or_disabled]

/--
`I-10`-aware mutable lens into field `fieldIdx` of an aggregate allocation
backed by a field-granular Tree Borrows pointer `rp` (`&mut s.f`): steps the
borrow table via `stepTreeBorrowHierarchyAccess? m rp true` (preserving both
active `I-10` parent struct borrows and active sibling field borrows) and
updates field `fieldIdx` of `rp.allocId` via `writeFieldAt?`.
-/
def treeFieldMemoryPtrMutLens {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (codec : ValueCodec α) :
    MutLens Memory α where
  readView m := (rawFieldMutLens rp.allocId fieldIdx codec).readView m
  writeBack a m :=
    let m₁ := (stepTreeBorrowHierarchyAccess? m rp true).getD m
    updateMemoryLocals m₁
      (writeFieldAt? (memoryLocals m₁) rp.allocId fieldIdx (codec.encode a))

theorem treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (codec : ValueCodec α) (a : α) {m : Memory}
    (hExcl : TreeFieldExclusiveBorrow rp fieldIdx fieldTy m) :
    (treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a m =
      (rawFieldMutLens rp.allocId fieldIdx codec).writeBack a m := by
  unfold treeFieldMemoryPtrMutLens rawFieldMutLens
  dsimp only
  rw [stepTreeBorrowHierarchyAccess_write_eq_some_self_of_treeField hExcl]
  rfl

/--
Domain validity predicate for `treeFieldMemoryPtrMutLens rp fieldIdx codec` at
field type `fieldTy`.
-/
structure ValidTreeFieldMutBorrowLens {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (codec : ValueCodec α) (m : Memory) : Prop where
  valid_raw : ValidRawFieldLens rp.allocId fieldIdx codec m
  exclusive : TreeFieldExclusiveBorrow rp fieldIdx fieldTy m

theorem ValidTreeFieldMutBorrowLens.writeBack {α : Type}
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {m : Memory}
    (a : α) (hm : ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec m) :
    ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec
      ((treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a m) := by
  rw [treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
    rp fieldIdx fieldTy codec a hm.exclusive]
  exact ⟨
    (rawFieldMutLens_lawful rp.allocId fieldIdx codec).valid_writeBack a m
      hm.valid_raw,
    TreeFieldExclusiveBorrow.of_borrows_eq hm.exclusive
      (updateMemoryLocals_borrows _ _)⟩

/--
`treeFieldMemoryPtrMutLens rp fieldIdx codec` is a `LawfulMutLens` on
`ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec`, transferred from
`rawFieldMutLens_lawful` via `LawfulMutLens.of_sub_agree`.
-/
theorem treeFieldMemoryPtrMutLens_lawful {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (codec : ValueCodec α) :
    LawfulMutLens (treeFieldMemoryPtrMutLens rp fieldIdx codec)
      (ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec) :=
  LawfulMutLens.of_sub_agree (rawFieldMutLens_lawful rp.allocId fieldIdx codec)
    (fun _ hm => hm.valid_raw)
    (fun a _ hm => hm.writeBack a)
    (fun _ _ => rfl)
    (fun a _ hm =>
      treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
        rp fieldIdx fieldTy codec a hm.exclusive)

/--
Domain validity predicate for a pair of sibling field-granular mutable borrow
lenses `treeFieldMemoryPtrMutLens rp₁ fieldIdx₁ codec₁` and
`treeFieldMemoryPtrMutLens rp₂ fieldIdx₂ codec₂` targeting distinct fields
(`fieldIdx₁ ≠ fieldIdx₂`) of the **same** aggregate slot
(`rp₁.allocId = rp₂.allocId`).
-/
structure ValidTreeFieldMutBorrowLensPair {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (fieldIdx₁ fieldIdx₂ : FieldIdx)
    (fieldTy₁ fieldTy₂ : Ty)
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) (m : Memory) : Prop where
  valid_left : ValidTreeFieldMutBorrowLens rp₁ fieldIdx₁ fieldTy₁ codec₁ m
  valid_right : ValidTreeFieldMutBorrowLens rp₂ fieldIdx₂ fieldTy₂ codec₂ m
  same_alloc : rp₁.allocId = rp₂.allocId
  ne_field : fieldIdx₁ ≠ fieldIdx₂

/--
Two sibling field-granular `treeFieldMemoryPtrMutLens` instances on distinct
fields (`fieldIdx₁ ≠ fieldIdx₂`) of a shared aggregate allocation
(`rp₁.allocId = rp₂.allocId`) satisfy `IndependentLenses`, transferred from
`rawFieldMutLens_independent_of_ne_field` via `IndependentLenses.of_sub_agree`.
-/
theorem treeFieldMemoryPtrMutLens_independent_of_ne_field {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (fieldIdx₁ fieldIdx₂ : FieldIdx)
    (fieldTy₁ fieldTy₂ : Ty)
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    IndependentLenses
      (treeFieldMemoryPtrMutLens rp₁ fieldIdx₁ codec₁)
      (treeFieldMemoryPtrMutLens rp₂ fieldIdx₂ codec₂)
      (ValidTreeFieldMutBorrowLensPair
        rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂) :=
  (rawFieldMutLens_independent_of_ne_field
      rp₁.allocId fieldIdx₁ fieldIdx₂ codec₁ codec₂).of_sub_agree
    (fun _ hm =>
      ⟨hm.valid_left.valid_raw,
        hm.same_alloc ▸ hm.valid_right.valid_raw,
        hm.ne_field⟩)
    (fun a m hm => by
      refine ⟨hm.valid_left.writeBack a, ?_, hm.same_alloc, hm.ne_field⟩
      rw [treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
        rp₁ fieldIdx₁ fieldTy₁ codec₁ a hm.valid_left.exclusive]
      have hRawPair :
          ValidRawFieldLensPair rp₁.allocId fieldIdx₁ fieldIdx₂ codec₁ codec₂ m :=
        ⟨hm.valid_left.valid_raw,
          hm.same_alloc ▸ hm.valid_right.valid_raw,
          hm.ne_field⟩
      have hRightRaw :=
        ((rawFieldMutLens_independent_of_ne_field
            rp₁.allocId fieldIdx₁ fieldIdx₂ codec₁ codec₂).valid_writeBack_left
          a m hRawPair).valid_right
      exact ⟨hm.same_alloc.symm ▸ hRightRaw,
        TreeFieldExclusiveBorrow.of_borrows_eq hm.valid_right.exclusive
          (updateMemoryLocals_borrows _ _)⟩)
    (fun b m hm => by
      refine ⟨?_, hm.valid_right.writeBack b, hm.same_alloc, hm.ne_field⟩
      rw [treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
        rp₂ fieldIdx₂ fieldTy₂ codec₂ b hm.valid_right.exclusive]
      have hRawPair :
          ValidRawFieldLensPair rp₁.allocId fieldIdx₁ fieldIdx₂ codec₁ codec₂ m :=
        ⟨hm.valid_left.valid_raw,
          hm.same_alloc ▸ hm.valid_right.valid_raw,
          hm.ne_field⟩
      have hLeftRaw :
          ValidRawFieldLens rp₁.allocId fieldIdx₁ codec₁
            ((rawFieldMutLens rp₂.allocId fieldIdx₂ codec₂).writeBack b m) := by
        rw [← hm.same_alloc]
        exact ((rawFieldMutLens_independent_of_ne_field
            rp₁.allocId fieldIdx₁ fieldIdx₂ codec₁ codec₂).valid_writeBack_right
          b m hRawPair).valid_left
      exact ⟨hLeftRaw,
        TreeFieldExclusiveBorrow.of_borrows_eq hm.valid_left.exclusive
          (updateMemoryLocals_borrows _ _)⟩)
    (fun _ _ => rfl)
    (fun m hm => by
      dsimp only [treeFieldMemoryPtrMutLens]
      rw [hm.same_alloc])
    (fun a _ hm =>
      treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
        rp₁ fieldIdx₁ fieldTy₁ codec₁ a hm.valid_left.exclusive)
    (fun b _ hm => by
      rw [treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
        rp₂ fieldIdx₂ fieldTy₂ codec₂ b hm.valid_right.exclusive,
        hm.same_alloc])

/--
Sub-allocation field points-to assertion (`FieldPointsTo rp fieldIdx v`):
field `fieldIdx` of the variant-`0` aggregate at `rp.allocId` holds `v` in
`memoryLocals h.state`, with singleton cell footprint
`[(rp.allocId, fieldIdx)]`.
-/
def FieldPointsTo
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (v : Value) : SepProp :=
  fun h =>
    readFieldAt? (memoryLocals h.state) rp.allocId fieldIdx = some v ∧
    h.footprint = { addrs := [(rp.allocId, fieldIdx)], tags := [] }

theorem localSepProp_fieldPointsTo
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (v : Value) :
    LocalSepProp (FieldPointsTo rp fieldIdx v) := by
  intro fp m₁ m₂ hAgree ⟨hField₁, hFp⟩
  dsimp only at hFp
  refine ⟨?_, hFp⟩
  have hIn : (rp.allocId, fieldIdx) ∈ fp.addrs := by
    rw [hFp]
    exact List.Mem.head []
  have hEq := hAgree.1 rp.allocId fieldIdx hIn
  cases fieldIdx with
  | zero =>
    unfold readFieldAt? at hField₁ ⊢
    unfold readAllocAt? at hEq
    dsimp only at hEq
    cases hGet₁ : get? (memoryLocals m₁) rp.allocId with
    | none => rw [hGet₁] at hField₁; nomatch hField₁
    | some slot₁ =>
      rw [hGet₁] at hField₁ hEq
      cases slot₁ with
      | dead => nomatch hField₁
      | uninit => nomatch hField₁
      | init val₁ =>
        cases val₁ with
        | unit => nomatch hField₁
        | scalar _ => nomatch hField₁
        | ptr _ _ => nomatch hField₁
        | aggregate var₁ elems₁ =>
          cases var₁ with
          | succ _ => nomatch hField₁
          | zero =>
            dsimp only at hEq
            cases hGet₂ : get? (memoryLocals m₂) rp.allocId with
            | none => rw [hGet₂] at hEq; nomatch hEq
            | some slot₂ =>
              rw [hGet₂] at hEq
              cases slot₂ with
              | dead => nomatch hEq
              | uninit => nomatch hEq
              | init val₂ =>
                dsimp only at hEq
                injection hEq with hValEq
                rw [← hValEq]
                exact hField₁
  | succ k =>
    rw [readAllocAt_succ_eq_readFieldAt, readAllocAt_succ_eq_readFieldAt] at hEq
    dsimp only
    rw [← hEq]
    exact hField₁

/--
Typed field-granular mutable borrow assertion (`&mut s.fieldIdx`): combines
`FieldPointsTo rp fieldIdx (codec.encode a)` with `BorrowToken rp .active`.
-/
def ActiveTypedFieldMutBorrow {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (codec : ValueCodec α) (a : α) :
    SepProp :=
  sepConj (FieldPointsTo rp fieldIdx (codec.encode a)) (BorrowToken rp .active)

theorem localSepProp_activeTypedFieldMutBorrow {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (codec : ValueCodec α) (a : α) :
    LocalSepProp (ActiveTypedFieldMutBorrow rp fieldIdx codec a) :=
  localSepProp_sepConj
    (localSepProp_fieldPointsTo rp fieldIdx (codec.encode a))
    (localSepProp_borrowToken rp .active)

/--
Canonical spatial footprint of `ActiveTypedFieldMutBorrow rp fieldIdx _ _`.
-/
def fieldMutBorrowFootprint (rp : RawPtrVal) (fieldIdx : FieldIdx) :
    Footprint :=
  { addrs := [(rp.allocId, fieldIdx)], tags := [rp.tag] }

theorem activeTypedFieldMutBorrow_intro {α : Type}
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {codec : ValueCodec α} {a : α}
    {m : Memory}
    (hField : readFieldAt? (memoryLocals m) rp.allocId fieldIdx =
      some (codec.encode a))
    (hTok :
      ∃ entry,
        lookupBorrow m.borrows rp.tag = some entry ∧
        entry.targetLocal = rp.allocId ∧
        entry.perm = .active) :
    ActiveTypedFieldMutBorrow rp fieldIdx codec a
      ⟨m, fieldMutBorrowFootprint rp fieldIdx⟩ :=
  ⟨⟨m, { addrs := [(rp.allocId, fieldIdx)], tags := [] }⟩,
    ⟨m, { addrs := [], tags := [rp.tag] }⟩,
    ⟨rfl, rfl, ⟨(fun _ _ h => nomatch h), (fun _ h => nomatch h)⟩,
      fun addr => by simp [fieldMutBorrowFootprint],
      fun tag => by simp [fieldMutBorrowFootprint]⟩,
    ⟨hField, rfl⟩,
    ⟨hTok, rfl⟩⟩

theorem activeTypedFieldMutBorrow_facts {α : Type}
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {codec : ValueCodec α} {a : α}
    {h : PartialHeap}
    (hA : ActiveTypedFieldMutBorrow rp fieldIdx codec a h) :
    readFieldAt? (memoryLocals h.state) rp.allocId fieldIdx =
      some (codec.encode a) ∧
    (∃ entry,
      lookupBorrow h.state.borrows rp.tag = some entry ∧
      entry.targetLocal = rp.allocId ∧
      entry.perm = .active) ∧
    (rp.allocId, fieldIdx) ∈ h.footprint.addrs ∧
    rp.tag ∈ h.footprint.tags := by
  rcases hA with
    ⟨h₁, h₂, ⟨hs₁, hs₂, _, hAddrs, hTags⟩, ⟨hFld, hfp₁⟩, ⟨hTok, hfp₂⟩⟩
  refine ⟨hs₁ ▸ hFld, hs₂ ▸ hTok, ?_, ?_⟩
  · apply (hAddrs _).mpr
    left
    rw [hfp₁]
    exact List.Mem.head []
  · apply (hTags _).mpr
    right
    rw [hfp₂]
    exact List.Mem.head []

/--
Field-granular `I-10` separation-to-lens bridge: two separated
`ActiveTypedFieldMutBorrow` assertions on the same aggregate allocation
(`rp₁.allocId = rp₂.allocId`) automatically target distinct fields
(`fieldIdx₁ ≠ fieldIdx₂`) with distinct provenance tags (`rp₁.tag ≠ rp₂.tag`)
and yield lawful, independent `treeFieldMemoryPtrMutLens` instances whose
product `prodMutLens` is a `LawfulMutLens`.
-/
theorem sepConj_entails_independentTreeFieldLenses {α β : Type}
    {rp₁ rp₂ : RawPtrVal} {fieldIdx₁ fieldIdx₂ : FieldIdx}
    {fieldTy₁ fieldTy₂ : Ty}
    {codec₁ : ValueCodec α} {codec₂ : ValueCodec β}
    {a₁ : α} {a₂ : β} {R_frame : SepProp} {m : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a₁)
          (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ a₂) R_frame))
        m)
    (hSameAlloc : rp₁.allocId = rp₂.allocId)
    (hExcl₁ : TreeFieldExclusiveBorrow rp₁ fieldIdx₁ fieldTy₁ m)
    (hExcl₂ : TreeFieldExclusiveBorrow rp₂ fieldIdx₂ fieldTy₂ m) :
    fieldIdx₁ ≠ fieldIdx₂ ∧
    rp₁.tag ≠ rp₂.tag ∧
    ValidTreeFieldMutBorrowLensPair
      rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂ m ∧
    IndependentLenses
      (treeFieldMemoryPtrMutLens rp₁ fieldIdx₁ codec₁)
      (treeFieldMemoryPtrMutLens rp₂ fieldIdx₂ codec₂)
      (ValidTreeFieldMutBorrowLensPair
        rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂) ∧
    LawfulMutLens
      (prodMutLens
        (treeFieldMemoryPtrMutLens rp₁ fieldIdx₁ codec₁)
        (treeFieldMemoryPtrMutLens rp₂ fieldIdx₂ codec₂))
      (ValidTreeFieldMutBorrowLensPair
        rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂) := by
  rcases hSep with ⟨fp, h₁, h₂₃, ⟨hs₁, hs₂₃, hDisj, _, _⟩, hA₁,
    h₂, _, ⟨hs₂, _, _, hAddrs₂₃, hTags₂₃⟩, hA₂, _⟩
  rcases activeTypedFieldMutBorrow_facts hA₁ with
    ⟨hFld₁, _, hCell₁, hTag₁⟩
  rcases activeTypedFieldMutBorrow_facts hA₂ with
    ⟨hFld₂, _, hCell₂, hTag₂⟩
  dsimp only at hs₁ hs₂ hs₂₃
  have hFld₁' :
      readFieldAt? (memoryLocals m) rp₁.allocId fieldIdx₁ =
        some (codec₁.encode a₁) := hs₁ ▸ hFld₁
  have hFld₂' :
      readFieldAt? (memoryLocals m) rp₂.allocId fieldIdx₂ =
        some (codec₂.encode a₂) := (hs₂.trans hs₂₃) ▸ hFld₂
  have hNeField : fieldIdx₁ ≠ fieldIdx₂ := by
    intro hEq
    apply hDisj.1 (rp₁.allocId, fieldIdx₁) hCell₁
    apply (hAddrs₂₃ _).mpr
    left
    rw [hSameAlloc, hEq]
    exact hCell₂
  have hNeTag : rp₁.tag ≠ rp₂.tag := by
    intro hEq
    apply hDisj.2 rp₁.tag hTag₁
    apply (hTags₂₃ _).mpr
    left
    rw [hEq]
    exact hTag₂
  have hValidPair :
      ValidTreeFieldMutBorrowLensPair
        rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂ m :=
    ⟨⟨⟨⟨a₁, hFld₁'⟩⟩, hExcl₁⟩, ⟨⟨⟨a₂, hFld₂'⟩⟩, hExcl₂⟩,
      hSameAlloc, hNeField⟩
  have hInd :=
    treeFieldMemoryPtrMutLens_independent_of_ne_field
      rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂
  have hLaw₁ :
      LawfulMutLens
        (treeFieldMemoryPtrMutLens rp₁ fieldIdx₁ codec₁)
        (ValidTreeFieldMutBorrowLensPair
          rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂) := {
    valid_writeBack := hInd.valid_writeBack_left
    readView_writeBack := fun a c hc =>
      (treeFieldMemoryPtrMutLens_lawful rp₁ fieldIdx₁ fieldTy₁ codec₁
        ).readView_writeBack a c hc.valid_left
    writeBack_readView := fun c hc =>
      (treeFieldMemoryPtrMutLens_lawful rp₁ fieldIdx₁ fieldTy₁ codec₁
        ).writeBack_readView c hc.valid_left
    writeBack_writeBack := fun a₁' a₂' c hc =>
      (treeFieldMemoryPtrMutLens_lawful rp₁ fieldIdx₁ fieldTy₁ codec₁
        ).writeBack_writeBack a₁' a₂' c hc.valid_left
  }
  have hLaw₂ :
      LawfulMutLens
        (treeFieldMemoryPtrMutLens rp₂ fieldIdx₂ codec₂)
        (ValidTreeFieldMutBorrowLensPair
          rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ codec₁ codec₂) := {
    valid_writeBack := hInd.valid_writeBack_right
    readView_writeBack := fun b c hc =>
      (treeFieldMemoryPtrMutLens_lawful rp₂ fieldIdx₂ fieldTy₂ codec₂
        ).readView_writeBack b c hc.valid_right
    writeBack_readView := fun c hc =>
      (treeFieldMemoryPtrMutLens_lawful rp₂ fieldIdx₂ fieldTy₂ codec₂
        ).writeBack_readView c hc.valid_right
    writeBack_writeBack := fun b₁' b₂' c hc =>
      (treeFieldMemoryPtrMutLens_lawful rp₂ fieldIdx₂ fieldTy₂ codec₂
        ).writeBack_writeBack b₁' b₂' c hc.valid_right
  }
  exact ⟨hNeField, hNeTag, hValidPair, hInd,
    prodMutLens_lawful hLaw₁ hLaw₂ hInd⟩

/--
Frame agreement for `treeFieldMemoryPtrMutLens.writeBack`: writing field
`fieldIdx` of `rp.allocId` leaves the `I-10` borrow table unchanged and agrees
with `m` on every frame cell `(allocId, offset)` that either sits on another
allocation (`allocId ≠ rp.allocId`) or sits at a distinct non-root field index
(`offset ≠ 0 ∧ offset ≠ fieldIdx`) of `rp.allocId`.
-/
theorem treeFieldMemoryPtrMutLens_writeBack_agreeOnFootprint {α : Type}
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {m : Memory} (a : α)
    (hm : ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec m)
    {fp_frame : Footprint}
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        allocId ≠ rp.allocId ∨ (offset ≠ 0 ∧ offset ≠ fieldIdx)) :
    AgreeOnFootprint fp_frame m
      ((treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a m) := by
  rw [treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
    rp fieldIdx fieldTy codec a hm.exclusive]
  dsimp only [rawFieldMutLens]
  refine ⟨fun allocId offset hIn => ?_, fun _ _ => ?_⟩
  · rw [memoryLocals_updateMemoryLocals]
    by_cases hEqAlloc : allocId = rp.allocId
    · subst hEqAlloc
      rcases hAddrs rp.allocId offset hIn with hNeAlloc | ⟨hNeZero, hNeFld⟩
      · exact absurd rfl hNeAlloc
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNeZero
        rw [readAllocAt_succ_eq_readFieldAt, readAllocAt_succ_eq_readFieldAt,
          readFieldAt_writeFieldAt_ne_eq _ _ _ hNeFld.symm]
    · unfold readAllocAt?
      rw [get?_writeFieldAt_ne_alloc _ _ _ hEqAlloc]
  · rw [updateMemoryLocals_borrows]

/--
Arbitrary `SupportedBy R_frame fp_frame` heap-predicate frames survive any
`treeFieldMemoryPtrMutLens` write-back whose written field avoids `fp_frame`.
-/
theorem treeFieldMemoryPtrMutLens_writeBack_supportedBy {α : Type}
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {m : Memory} (a : α)
    (hm : ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec m)
    {R_frame : HeapPred} {fp_frame : Footprint}
    (hSupp : SupportedBy R_frame fp_frame)
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        allocId ≠ rp.allocId ∨ (offset ≠ 0 ∧ offset ≠ fieldIdx))
    (hR : R_frame m) :
    R_frame ((treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a m) :=
  hSupp m _
    (treeFieldMemoryPtrMutLens_writeBack_agreeOnFootprint a hm hAddrs) hR

/--
Every lens-state entry under `SepLensStateInv` satisfies the `I-10`-aware
domain validity predicate `ValidTreeMutBorrowLens`.
-/
theorem SepLensStateInv.validTreeMutBorrowLens {α : Type}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α}
    (hInv : SepLensStateInv frameLen entries m)
    (hMem : (rp, codec.encode a) ∈ entries) :
    ValidTreeMutBorrowLens rp codec m := by
  rcases hInv.entries_valid rp (codec.encode a) hMem with
    ⟨hOff, _, hCaller, hExcl⟩
  refine ⟨⟨a, ?_⟩, hExcl⟩
  rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
  unfold readAllocAt?
  rw [hCaller, hOff]

/--
Any two distinct pointer entries under `SepLensStateInv` satisfy
`ValidTreeMutBorrowLensPair`, so their `treeMemoryPtrMutLens` instances are
lawful and independent on `m`.
-/
theorem SepLensStateInv.validTreeMutBorrowLensPair {α β : Type}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp₁ rp₂ : RawPtrVal} {codec₁ : ValueCodec α} {codec₂ : ValueCodec β}
    {a₁ : α} {a₂ : β}
    (hInv : SepLensStateInv frameLen entries m)
    (hMem₁ : (rp₁, codec₁.encode a₁) ∈ entries)
    (hMem₂ : (rp₂, codec₂.encode a₂) ∈ entries)
    (hNe : rp₁ ≠ rp₂) :
    ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂ m := by
  have hDisj :=
    pairwise_disjoint_of_mem_ne hInv.pairwise_disjoint hMem₁ hMem₂ hNe.symm
  exact ⟨hInv.validTreeMutBorrowLens hMem₁,
    hInv.validTreeMutBorrowLens hMem₂, hDisj.1.symm⟩

/--
Strengthened write alias-erasure theorem: when `LiftDerefWrite` writes
`codec.encode a` to a tracked pointer `rp` with
`(rp, codec.encode a₀) ∈ entries`, `evalStmt` steps to
`m' = (treeMemoryPtrMutLens rp codec).writeBack a s.memory`,
`ValidTreeMutBorrowLens rp codec m'` holds, PutGet recovers
`(treeMemoryPtrMutLens rp codec).readView m' = a`, and every sibling lens
`(rp₂, codec₂.encode b) ∈ entries` with `rp₂ ≠ rp` has its view
`(treeMemoryPtrMutLens rp₂ codec₂).readView m' = b` preserved via
`IndependentLenses`.
-/
theorem LiftDerefWrite.evalStmt_treeLens_putGet_and_frame
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState}
    (hWrite : LiftDerefWrite localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory) :
    ∃ (rp : RawPtrVal) (oldVal newVal : Value),
      lookupLensVal? entries rp = .some oldVal ∧
      entries' = updateLensVal entries rp newVal ∧
      ∀ {α : Type} (codec : ValueCodec α) (a₀ a : α),
        codec.encode a₀ = oldVal →
        codec.encode a = newVal →
        let m' := (treeMemoryPtrMutLens rp codec).writeBack a s.memory
        evalStmt s stmt localDecls layouts =
          MirStepNode.step (advanceStmt s env' m') ∧
        ValidTreeMutBorrowLens rp codec m' ∧
        (treeMemoryPtrMutLens rp codec).readView m' = a ∧
        ∀ {β : Type} (rp₂ : RawPtrVal) (codec₂ : ValueCodec β) (b : β),
          (rp₂, codec₂.encode b) ∈ entries →
          rp₂ ≠ rp →
          (treeMemoryPtrMutLens rp₂ codec₂).readView m' = b := by
  rcases hWrite.evalStmt_eq hEnv hInv with
    ⟨rp, oldVal, newVal, hLook, hEntries, _, hEval⟩
  refine ⟨rp, oldVal, newVal, hLook, hEntries,
    fun codec a₀ a hEnc₀ hEnc => ?_⟩
  have hMem₁ : (rp, codec.encode a₀) ∈ entries := by
    rw [hEnc₀]
    exact lookupLensVal?_mem hLook
  have hValid₁ : ValidTreeMutBorrowLens rp codec s.memory :=
    hInv.validTreeMutBorrowLens hMem₁
  rcases hValid₁ with ⟨⟨_, hPts⟩, hExcl⟩
  have hStep :
      evalStmt s stmt localDecls layouts =
        MirStepNode.step
          (advanceStmt s env'
            ((treeMemoryPtrMutLens rp codec).writeBack a s.memory)) := by
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a hPts hExcl,
      updateMemoryLocals_of_callStack_nil hInv.callStack_nil,
      memoryLocals_of_callStack_nil hInv.callStack_nil, hEnc]
    exact hEval
  refine ⟨hStep,
    (treeMemoryPtrMutLens_lawful rp codec).valid_writeBack a s.memory
      ⟨⟨_, hPts⟩, hExcl⟩,
    (treeMemoryPtrMutLens_lawful rp codec).readView_writeBack a s.memory
      ⟨⟨_, hPts⟩, hExcl⟩,
    fun rp₂ codec₂ b hMem₂ hNe => ?_⟩
  have hPair : ValidTreeMutBorrowLensPair rp rp₂ codec codec₂ s.memory :=
    hInv.validTreeMutBorrowLensPair hMem₁ hMem₂ hNe.symm
  have hIndep :=
    treeMemoryPtrMutLens_independent_of_ne_alloc rp rp₂ codec codec₂
  rw [hIndep.readView_right_of_writeBack_left a s.memory hPair]
  exact hInv.treeLens_readView hMem₂

/--
Every lifted statement is pure `MutLens` state passing: `evalStmt` steps to a
memory `m'` whose `I-10` lens views are exactly the post lens state
`entries'`, and every entry of `entries'` is a valid `treeMemoryPtrMutLens`
domain point of `m'`. This covers lifted dereference reads and writes, pure
assignments, `StorageLive`/`StorageDead`, `Nop`, and Tree Borrows retags.
-/
theorem LiftLensStmt.evalStmt_treeLens_views
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries₀ entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState} {m₀ : Memory}
    (hStmt : LiftLensStmt localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory)
    (hFrame : LensFramePreserved entries₀ m₀ s.memory)
    (hKeys : entries.map Prod.fst = entries₀.map Prod.fst) :
    ∃ m' : Memory,
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env' m') ∧
      ∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
        (rp, codec.encode a) ∈ entries' →
        ValidTreeMutBorrowLens rp codec m' ∧
        (treeMemoryPtrMutLens rp codec).readView m' = a := by
  rcases hStmt.evalStmt_step hEnv hInv hFrame hKeys with
    ⟨m', hEval, _, hInv', _, _⟩
  exact ⟨m', hEval, fun _ _ _ hMem =>
    ⟨hInv'.validTreeMutBorrowLens hMem, hInv'.treeLens_readView hMem⟩⟩

/--
Tree Borrows retags are the identity on the lens state. A lifted `Retag(_p)`
leaves `env` and `entries` unchanged, and `evalStmt` steps to a memory `m'`
(which may attach a function-entry protector in the borrow table) on which
every tracked pointer keeps a valid `I-10` lens with the same view as before.
-/
theorem LiftRetag.evalStmt_treeLens_views
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState}
    (hRetag : LiftRetag localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory) :
    env' = env ∧ entries' = entries ∧
    ∃ m' : Memory,
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env m') ∧
      ∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
        (rp, codec.encode a) ∈ entries →
        ValidTreeMutBorrowLens rp codec m' ∧
        (treeMemoryPtrMutLens rp codec).readView m' =
          (treeMemoryPtrMutLens rp codec).readView s.memory := by
  have hGen := (LiftLensStmt.retag hRetag).evalStmt_treeLens_views hEnv hInv
    (LensFramePreserved.refl entries s.memory) rfl
  cases hRetag
  rcases hGen with ⟨m', hEval, hViews⟩
  refine ⟨rfl, rfl, m', hEval, fun rp codec a hMem => ?_⟩
  rw [hInv.treeLens_readView hMem]
  exact hViews rp codec a hMem

/--
Compositional single-statement `MutLens` state-passing theorem: strengthens
`LiftLensStmt.evalStmt_treeLens_views` with the inductive invariants
(`SepLensStateInv`, `LensFramePreserved`, and key preservation) so consecutive
statements compose across basic blocks and CFGs.
-/
theorem LiftLensStmt.evalStmt_treeLens_views_and_frame
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries₀ entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState} {m₀ : Memory}
    (hStmt : LiftLensStmt localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepLensStateInv env.length entries s.memory)
    (hFrame : LensFramePreserved entries₀ m₀ s.memory)
    (hKeys : entries.map Prod.fst = entries₀.map Prod.fst) :
    ∃ m' : Memory,
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env' m') ∧
      env'.length = env.length ∧
      SepLensStateInv env'.length entries' m' ∧
      LensFramePreserved entries₀ m₀ m' ∧
      entries'.map Prod.fst = entries₀.map Prod.fst ∧
      ∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
        (rp, codec.encode a) ∈ entries' →
        ValidTreeMutBorrowLens rp codec m' ∧
        (treeMemoryPtrMutLens rp codec).readView m' = a := by
  rcases hStmt.evalStmt_step hEnv hInv hFrame hKeys with
    ⟨m', hEval, hLen, hInv', hFrame', hKeys'⟩
  exact ⟨m', hEval, hLen, hInv', hFrame', hKeys', fun _ _ _ hMem =>
    ⟨hInv'.validTreeMutBorrowLens hMem, hInv'.treeLens_readView hMem⟩⟩

/--
Multi-statement `MutLens` state-passing composition across a basic block's
statement list (`LiftLensStmts`): executing `stmts` from `(env, entries)` steps
to the block's terminator with a memory `m'` on which every entry
`(rp, codec.encode a) ∈ entries'` is a valid `treeMemoryPtrMutLens` domain
point whose `readView` equals `a`, while preserving `SepLensStateInv` and
`LensFramePreserved`.
-/
theorem LiftLensStmts.mirWpConverges_treeLens_views
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    {stmts prefixStmts : List Statement}
    {env env' : PureEnv}
    {entries₀ entries entries' : List (RawPtrVal × Value)}
    {m₀ m : Memory} {Φ : MirOutcome → Prop}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hStmts :
      LiftLensStmts body.localDecls body.layouts
        env entries stmts env' entries')
    (hBbStmts : bb.statements = prefixStmts ++ stmts)
    (hInv : SepLensStateInv env.length entries m)
    (hFrame : LensFramePreserved entries₀ m₀ m)
    (hKeys : entries.map Prod.fst = entries₀.map Prod.fst)
    (hCont :
      ∀ m' : Memory,
        SepLensStateInv env'.length entries' m' →
        LensFramePreserved entries₀ m₀ m' →
        entries'.map Prod.fst = entries₀.map Prod.fst →
        (∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
          (rp, codec.encode a) ∈ entries' →
          ValidTreeMutBorrowLens rp codec m' ∧
          (treeMemoryPtrMutLens rp codec).readView m' = a) →
        MirWpConverges body
          { frame := {
              blockIdx := bbIdx
              stmtIdx := bb.statements.length
              locals := env'
            }
            memory := m' }
          Φ) :
    MirWpConverges body
      { frame := {
          blockIdx := bbIdx
          stmtIdx := prefixStmts.length
          locals := env
        }
        memory := m }
      Φ :=
  mirWpConverges_of_liftLensStmts hPhase hBb hStmts prefixStmts m₀ m Φ
    hBbStmts hInv hFrame hKeys (fun m' hInv' hFrame' hKeys' =>
      hCont m' hInv' hFrame' hKeys' (fun _ _ _ hMem =>
        ⟨hInv'.validTreeMutBorrowLens hMem, hInv'.treeLens_readView hMem⟩))

/--
Whole-CFG `MutLens` state-passing theorem
(`mirWpConverges_of_sepLenses_treeLens_views`):
composes `LiftLensBlock` across basic blocks and terminators so that the final
memory `m_final` satisfies `ValidTreeMutBorrowLens rp codec m_final` and
`(treeMemoryPtrMutLens rp codec).readView m_final = a` for every final lens
binding `(rp, codec.encode a) ∈ entries'`, together with `SepLensStateInv` and
`LensFramePreserved`.
-/
theorem mirWpConverges_of_sepLenses_treeLens_views
    {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {entries₀ entries' : List (RawPtrVal × Value)}
    {retVal : Value} {m₀ : Memory} {Φ : MirOutcome → Prop}
    (hBlock : LiftLensBlock body bbIdx env entries₀ retVal entries')
    (hInv₀ : SepLensStateInv env.length entries₀ m₀)
    (hPost :
      ∀ m_final : Memory,
        SepLensStateInv env.length entries' m_final →
        LensFramePreserved entries₀ m₀ m_final →
        (∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
          (rp, codec.encode a) ∈ entries' →
          ValidTreeMutBorrowLens rp codec m_final ∧
          (treeMemoryPtrMutLens rp codec).readView m_final = a) →
        Φ (.normal (retVal, m_final))) :
    MirWpConverges body
      { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := env }
        memory := m₀ }
      Φ :=
  mirWpConverges_of_sepLenses hBlock hInv₀ (fun m_final hInvF hPresF =>
    hPost m_final hInvF hPresF (fun _ _ _ hMem =>
      ⟨hInvF.validTreeMutBorrowLens hMem, hInvF.treeLens_readView hMem⟩))

/--
`I-10`-aware binary separation-to-lens bridge under `TreeExclusiveBorrow`.
-/
theorem sepConj_entails_independentTreeLenses {α β : Type}
    {rp₁ rp₂ : RawPtrVal} {codec₁ : ValueCodec α} {codec₂ : ValueCodec β}
    {a₁ : α} {a₂ : β} {R_frame : SepProp} {m : Memory}
    (hSep :
      SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁)
          (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)) m)
    (hExcl₁ : TreeExclusiveBorrow rp₁ m)
    (hExcl₂ : TreeExclusiveBorrow rp₂ m) :
    rp₁.allocId ≠ rp₂.allocId ∧
    rp₁.tag ≠ rp₂.tag ∧
    ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂ m ∧
    IndependentLenses
      (treeMemoryPtrMutLens rp₁ codec₁)
      (treeMemoryPtrMutLens rp₂ codec₂)
      (ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) ∧
    LawfulMutLens
      (prodMutLens
        (treeMemoryPtrMutLens rp₁ codec₁)
        (treeMemoryPtrMutLens rp₂ codec₂))
      (ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) := by
  have hDisj := sepConj_activeTypedMutBorrow_disjoint hSep
  have hOffEq : rp₁.offset = rp₂.offset :=
    hExcl₁.offset_zero.trans hExcl₂.offset_zero.symm
  have hAllocNe : rp₁.allocId ≠ rp₂.allocId := (hDisj.2.2 hOffEq).1
  have hTagNe : rp₁.tag ≠ rp₂.tag := hDisj.2.1
  have hPts₁ : readAllocAt? (memoryLocals m) rp₁ = some (codec₁.encode a₁) :=
    readAllocAt_of_activeTypedMutBorrow_holdsIn (holdsIn_of_sepConj_left hSep)
  have hPts₂ : readAllocAt? (memoryLocals m) rp₂ = some (codec₂.encode a₂) :=
    readAllocAt_of_activeTypedMutBorrow_holdsIn
      (holdsIn_of_sepConj_left (holdsIn_of_sepConj_right hSep))
  have hValidPair : ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂ m :=
    ⟨⟨⟨a₁, hPts₁⟩, hExcl₁⟩, ⟨⟨a₂, hPts₂⟩, hExcl₂⟩, hAllocNe⟩
  have hInd := treeMemoryPtrMutLens_independent_of_ne_alloc rp₁ rp₂ codec₁ codec₂
  have hLaw₁ :
      LawfulMutLens
        (treeMemoryPtrMutLens rp₁ codec₁)
        (ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) := {
    valid_writeBack := hInd.valid_writeBack_left
    readView_writeBack := fun a c hc =>
      (treeMemoryPtrMutLens_lawful rp₁ codec₁).readView_writeBack a c
        hc.valid_left
    writeBack_readView := fun c hc =>
      (treeMemoryPtrMutLens_lawful rp₁ codec₁).writeBack_readView c
        hc.valid_left
    writeBack_writeBack := fun a₁' a₂' c hc =>
      (treeMemoryPtrMutLens_lawful rp₁ codec₁).writeBack_writeBack a₁' a₂' c
        hc.valid_left
  }
  have hLaw₂ :
      LawfulMutLens
        (treeMemoryPtrMutLens rp₂ codec₂)
        (ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) := {
    valid_writeBack := hInd.valid_writeBack_right
    readView_writeBack := fun b c hc =>
      (treeMemoryPtrMutLens_lawful rp₂ codec₂).readView_writeBack b c
        hc.valid_right
    writeBack_readView := fun c hc =>
      (treeMemoryPtrMutLens_lawful rp₂ codec₂).writeBack_readView c
        hc.valid_right
    writeBack_writeBack := fun b₁' b₂' c hc =>
      (treeMemoryPtrMutLens_lawful rp₂ codec₂).writeBack_writeBack b₁' b₂' c
        hc.valid_right
  }
  refine ⟨hAllocNe, hTagNe, hValidPair, hInd,
    prodMutLens_lawful hLaw₁ hLaw₂ hInd⟩

/--
Validity domain shared by an `I-10`-aware family of binding lenses under
`TreeExclusiveBorrow`.
-/
structure ValidTreeMutBorrowFamily
    (bs : List MutBorrowBinding) (m : Memory) : Prop where
  valid : ∀ b ∈ bs, ValidTreeMutBorrowLens b.rp b.codec m
  pairwise_alloc : bs.Pairwise (fun b₁ b₂ => b₁.rp.allocId ≠ b₂.rp.allocId)

theorem ValidTreeMutBorrowFamily.writeBack
    {bs : List MutBorrowBinding} {m : Memory} {b : MutBorrowBinding}
    (hb : b ∈ bs) (hValid : ValidTreeMutBorrowFamily bs m) (a : b.α) :
    ValidTreeMutBorrowFamily bs
      ((treeMemoryPtrMutLens b.rp b.codec).writeBack a m) := by
  refine ⟨fun b' hb' => ?_, hValid.pairwise_alloc⟩
  by_cases hEq : b'.rp.allocId = b.rp.allocId
  · have hSame : b' = b :=
      eq_of_pairwise_ne_of_mem hValid.pairwise_alloc hb' hb hEq
    subst hSame
    exact (treeMemoryPtrMutLens_lawful b'.rp b'.codec).valid_writeBack a m
      (hValid.valid b' hb')
  · rcases hValid.valid b hb with ⟨⟨a₀, hPts⟩, hExcl⟩
    rcases hValid.valid b' hb' with ⟨⟨a₀', hPts'⟩, hExcl'⟩
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree b.rp b.codec a hPts hExcl]
    exact ⟨⟨a₀', pointsTo_updateMemoryLocals_set_ne (Ne.symm hEq)
        hExcl'.offset_zero hPts'⟩,
      TreeExclusiveBorrow.of_borrows_eq hExcl'
        (updateMemoryLocals_borrows _ _)⟩

theorem treeMemoryPtrMutLens_lawful_family
    {bs : List MutBorrowBinding} {b : MutBorrowBinding} (hb : b ∈ bs) :
    LawfulMutLens (treeMemoryPtrMutLens b.rp b.codec)
      (ValidTreeMutBorrowFamily bs) where
  valid_writeBack a _ hm := hm.writeBack hb a
  readView_writeBack a m hm :=
    (treeMemoryPtrMutLens_lawful b.rp b.codec).readView_writeBack a m
      (hm.valid b hb)
  writeBack_readView m hm :=
    (treeMemoryPtrMutLens_lawful b.rp b.codec).writeBack_readView m
      (hm.valid b hb)
  writeBack_writeBack a₁ a₂ m hm :=
    (treeMemoryPtrMutLens_lawful b.rp b.codec).writeBack_writeBack a₁ a₂ m
      (hm.valid b hb)

theorem treeMemoryPtrMutLens_independent_family
    {bs : List MutBorrowBinding} {b₁ b₂ : MutBorrowBinding}
    (hb₁ : b₁ ∈ bs) (hb₂ : b₂ ∈ bs) (hNe : b₁.rp.allocId ≠ b₂.rp.allocId) :
    IndependentLenses
      (treeMemoryPtrMutLens b₁.rp b₁.codec)
      (treeMemoryPtrMutLens b₂.rp b₂.codec)
      (ValidTreeMutBorrowFamily bs) := by
  have hPair :=
    treeMemoryPtrMutLens_independent_of_ne_alloc b₁.rp b₂.rp b₁.codec b₂.codec
  have toPair :
      ∀ m, ValidTreeMutBorrowFamily bs m →
        ValidTreeMutBorrowLensPair b₁.rp b₂.rp b₁.codec b₂.codec m :=
    fun m hm => ⟨hm.valid b₁ hb₁, hm.valid b₂ hb₂, hNe⟩
  exact {
    valid_writeBack_left := fun a m hm => hm.writeBack hb₁ a
    valid_writeBack_right := fun a m hm => hm.writeBack hb₂ a
    readView_right_of_writeBack_left := fun a m hm =>
      hPair.readView_right_of_writeBack_left a m (toPair m hm)
    readView_left_of_writeBack_right := fun a m hm =>
      hPair.readView_left_of_writeBack_right a m (toPair m hm)
    writeBack_comm := fun a a' m hm => hPair.writeBack_comm a a' m (toPair m hm)
  }

/--
`k`-ary `I-10`-aware separation-to-lens bridge: a `k`-ary separating conjunction
of typed mutable borrows satisfying `TreeExclusiveBorrow` (not requiring the
strict ancestor-free `ExclusiveActiveBorrow`) yields a valid lens family in
which every member `treeMemoryPtrMutLens` is lawful and every pair of distinct
indices is independent.
-/
theorem sepConjBindings_entails_independentTreeLensFamily
    {bs : List MutBorrowBinding} {R : SepProp} {m : Memory}
    (hSep : SepProp.holdsIn (sepConjBindings bs R) m)
    (hExcl : ∀ b ∈ bs, TreeExclusiveBorrow b.rp m) :
    ValidTreeMutBorrowFamily bs m ∧
    (∀ (i : Nat) (hi : i < bs.length),
      LawfulMutLens
        (treeMemoryPtrMutLens bs[i].rp bs[i].codec)
        (ValidTreeMutBorrowFamily bs)) ∧
    (∀ (i j : Nat) (hi : i < bs.length) (hj : j < bs.length), i ≠ j →
      IndependentLenses
        (treeMemoryPtrMutLens bs[i].rp bs[i].codec)
        (treeMemoryPtrMutLens bs[j].rp bs[j].codec)
        (ValidTreeMutBorrowFamily bs)) := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split hSep with ⟨hBind, hPair, _, _⟩
  have hPairAlloc :
      bs.Pairwise (fun b₁ b₂ => b₁.rp.allocId ≠ b₂.rp.allocId) := by
    refine List.Pairwise.imp_of_mem ?_ hPair
    intro b₁ b₂ hb₁ hb₂ hNe hAlloc
    apply hNe.1
    show (b₁.rp.allocId, b₁.rp.offset) = (b₂.rp.allocId, b₂.rp.offset)
    rw [hAlloc, (hExcl b₁ hb₁).offset_zero, (hExcl b₂ hb₂).offset_zero]
  have hValid : ValidTreeMutBorrowFamily bs m :=
    ⟨fun b hb => ⟨⟨b.val, (hBind b hb).1⟩, hExcl b hb⟩, hPairAlloc⟩
  refine ⟨hValid, fun i hi => treeMemoryPtrMutLens_lawful_family
    (List.getElem_mem hi), fun i j hi hj hNe => ?_⟩
  refine treeMemoryPtrMutLens_independent_family
    (List.getElem_mem hi) (List.getElem_mem hj) ?_
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
  · exact List.pairwise_iff_getElem.mp hPairAlloc i j hi hj hLt
  · exact Ne.symm (List.pairwise_iff_getElem.mp hPairAlloc j i hj hi hGt)

/--
Homogeneous `List` form of the `I-10`-aware family bridge under
`TreeExclusiveBorrow`.
-/
theorem sepConjBindings_entails_pairwiseIndependentTreeLenses
    {α : Type} {codec : ValueCodec α} {ptrs : List (RawPtrVal × α)}
    {R : SepProp} {m : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConjBindings (ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2) R)
        m)
    (hExcl : ∀ p ∈ ptrs, TreeExclusiveBorrow p.1 m) :
    ValidTreeMutBorrowFamily
        (ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2) m ∧
    PairwiseIndependentLenses
      (ValidTreeMutBorrowFamily
        (ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2))
      (ptrs.map fun p => treeMemoryPtrMutLens p.1 codec) := by
  let bs := ptrs.map fun p => MutBorrowBinding.bind p.1 codec p.2
  have hExcl' : ∀ b ∈ bs, TreeExclusiveBorrow b.rp m := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
    exact hExcl p hp
  rcases sepConjBindings_entails_independentTreeLensFamily hSep hExcl' with
    ⟨hValid, _, _⟩
  refine ⟨hValid, ?_⟩
  have hPairPtr :
      ptrs.Pairwise (fun p₁ p₂ => p₁.1.allocId ≠ p₂.1.allocId) := by
    have h := hValid.pairwise_alloc
    rw [List.pairwise_map] at h
    exact h
  have hSuffix :
      ∀ sfx : List (RawPtrVal × α),
        (∀ p ∈ sfx, p ∈ ptrs) →
        sfx.Pairwise (fun p₁ p₂ => p₁.1.allocId ≠ p₂.1.allocId) →
        PairwiseIndependentLenses (ValidTreeMutBorrowFamily bs)
          (sfx.map fun p => treeMemoryPtrMutLens p.1 codec) := by
    intro sfx
    induction sfx with
    | nil => intro _ _; exact .nil
    | cons p rest ih =>
      intro hSub hPairSfx
      rcases List.pairwise_cons.mp hPairSfx with ⟨hHead, hTail⟩
      have hp : MutBorrowBinding.bind p.1 codec p.2 ∈ bs :=
        List.mem_map.mpr ⟨p, hSub p (List.Mem.head rest), rfl⟩
      refine .cons (treeMemoryPtrMutLens_lawful_family hp) ?_
        (ih (fun q hq => hSub q (List.Mem.tail p hq)) hTail)
      intro L hL
      rcases List.mem_map.mp hL with ⟨q, hq, rfl⟩
      have hq' : MutBorrowBinding.bind q.1 codec q.2 ∈ bs :=
        List.mem_map.mpr ⟨q, hSub q (List.Mem.tail p hq), rfl⟩
      exact treeMemoryPtrMutLens_independent_family hp hq' (hHead q hq)
  exact hSuffix ptrs (fun _ h => h) hPairPtr

/-! ### `SupportedBy` Heap-Predicate Frames via `AgreeOnFootprint` -/

theorem ValidMutBorrowFamily.toTree
    {bs : List MutBorrowBinding} {m : Memory}
    (hValid : ValidMutBorrowFamily bs m) :
    ValidTreeMutBorrowFamily bs m :=
  ⟨fun b hb => (hValid.valid b hb).toTree, hValid.pairwise_alloc⟩

/--
An `I-10`-aware family write-back through member `b` under
`ValidTreeMutBorrowFamily` agrees with the original memory on every frame
footprint whose cells avoid `b`'s allocation: it rewrites one caller slot and
leaves the borrow table (including active `I-10` ancestors) unchanged.
-/
theorem treeMemoryPtrMutLens_writeBack_agreeOnFootprint_family
    {bs : List MutBorrowBinding} {m : Memory} {b : MutBorrowBinding}
    (hb : b ∈ bs) (hValid : ValidTreeMutBorrowFamily bs m) (a : b.α)
    {fp_frame : Footprint}
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        allocId ≠ b.rp.allocId) :
    AgreeOnFootprint fp_frame m
      ((treeMemoryPtrMutLens b.rp b.codec).writeBack a m) := by
  rcases hValid.valid b hb with ⟨⟨_, hPts⟩, hExcl⟩
  rw [treeMemoryPtrMutLens_writeBack_eq_of_tree b.rp b.codec a hPts hExcl]
  refine ⟨fun allocId offset hIn => ?_, fun tag _ => ?_⟩
  · rw [memoryLocals_updateMemoryLocals]
    unfold readAllocAt?
    unfold get?
    rw [List.getElem?_set_ne (Ne.symm (hAddrs allocId offset hIn))]
  · rw [updateMemoryLocals_borrows]

/--
Arbitrary `SupportedBy R_frame fp_frame` heap-predicate frames survive any
`I-10`-aware family write-back whose cells avoid `fp_frame`.
-/
theorem treeMemoryPtrMutLens_writeBack_supportedBy_family
    {bs : List MutBorrowBinding} {m : Memory} {b : MutBorrowBinding}
    (hb : b ∈ bs) (hValid : ValidTreeMutBorrowFamily bs m) (a : b.α)
    {R_frame : HeapPred} {fp_frame : Footprint}
    (hSupp : SupportedBy R_frame fp_frame)
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        allocId ≠ b.rp.allocId)
    (hR : R_frame m) :
    R_frame ((treeMemoryPtrMutLens b.rp b.codec).writeBack a m) :=
  hSupp m _
    (treeMemoryPtrMutLens_writeBack_agreeOnFootprint_family hb hValid a hAddrs)
    hR

/--
A family write-back through member `b` under the strict `ValidMutBorrowFamily`
agrees with the original memory on every frame footprint whose cells avoid `b`'s
allocation, transferred from
`treeMemoryPtrMutLens_writeBack_agreeOnFootprint_family`.
-/
theorem memoryPtrMutLens_writeBack_agreeOnFootprint_family
    {bs : List MutBorrowBinding} {m : Memory} {b : MutBorrowBinding}
    (hb : b ∈ bs) (hValid : ValidMutBorrowFamily bs m) (a : b.α)
    {fp_frame : Footprint}
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        allocId ≠ b.rp.allocId) :
    AgreeOnFootprint fp_frame m
      ((memoryPtrMutLens b.rp b.codec).writeBack a m) := by
  rcases hValid.valid b hb with ⟨⟨_, hPts⟩, hExcl⟩
  rw [← treeMemoryPtrMutLens_writeBack_eq_memoryPtrMutLens_of_exclusive
    b.rp b.codec a hPts hExcl]
  exact treeMemoryPtrMutLens_writeBack_agreeOnFootprint_family
    hb hValid.toTree a hAddrs

/--
Arbitrary `SupportedBy R_frame fp_frame` heap-predicate frames survive any
family write-back whose cells avoid `fp_frame`.
-/
theorem memoryPtrMutLens_writeBack_supportedBy_family
    {bs : List MutBorrowBinding} {m : Memory} {b : MutBorrowBinding}
    (hb : b ∈ bs) (hValid : ValidMutBorrowFamily bs m) (a : b.α)
    {R_frame : HeapPred} {fp_frame : Footprint}
    (hSupp : SupportedBy R_frame fp_frame)
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        allocId ≠ b.rp.allocId)
    (hR : R_frame m) :
    R_frame ((memoryPtrMutLens b.rp b.codec).writeBack a m) :=
  hSupp m _
    (memoryPtrMutLens_writeBack_agreeOnFootprint_family hb hValid a hAddrs) hR

/--
MIR-level frame agreement: whenever `LensFramePreserved entries₀ m₀ m` holds
(as `mirWpConverges_of_sepLenses` guarantees), `m₀` and `m` agree on every
footprint whose cells avoid the tracked allocations and whose tags avoid the
tracked tags.
-/
theorem agreeOnFootprint_of_lensFramePreserved
    {entries₀ : List (RawPtrVal × Value)} {m₀ m : Memory}
    (hPres : LensFramePreserved entries₀ m₀ m)
    (hStack₀ : m₀.callStack = []) (hStack : m.callStack = [])
    {fp : Footprint}
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp.addrs →
        ∀ e ∈ entries₀, allocId ≠ e.1.allocId)
    (hTags : ∀ tag ∈ fp.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag) :
    AgreeOnFootprint fp m₀ m := by
  refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
  · rw [memoryLocals_of_callStack_nil hStack₀,
      memoryLocals_of_callStack_nil hStack]
    unfold readAllocAt?
    rw [hPres.locals_unchanged_outside allocId (hAddrs allocId offset hIn)]
  · exact (hPres.borrows_unchanged_outside tag (hTags tag hIn)).symm

/-- `SupportedBy` frames disjoint from the lens footprint survive execution. -/
theorem supportedBy_of_lensFramePreserved
    {entries₀ : List (RawPtrVal × Value)} {m₀ m : Memory}
    (hPres : LensFramePreserved entries₀ m₀ m)
    (hStack₀ : m₀.callStack = []) (hStack : m.callStack = [])
    {R_frame : HeapPred} {fp_frame : Footprint}
    (hSupp : SupportedBy R_frame fp_frame)
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        ∀ e ∈ entries₀, allocId ≠ e.1.allocId)
    (hTags : ∀ tag ∈ fp_frame.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag)
    (hR : R_frame m₀) :
    R_frame m :=
  hSupp m₀ m
    (agreeOnFootprint_of_lensFramePreserved hPres hStack₀ hStack hAddrs hTags)
    hR

/--
Framed bridge from `mirWpConverges_of_sepLenses` to
`StatefulVerificationResult`: any `SupportedBy R_frame fp_frame` heap predicate
whose footprint avoids the lens footprint is conjoined onto both the pre- and
postcondition (`frameStatefulClaim`) without re-verifying the body.
-/
theorem verifyStatefulMir_of_sepLenses_supportedFrame
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (R_frame : HeapPred) (fp_frame : Footprint)
    (hSupp : SupportedBy R_frame fp_frame)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepLensStateInv env₀.length entries₀ m₀ ∧
          (∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
            ∀ e ∈ entries₀, allocId ≠ e.1.allocId) ∧
          (∀ tag ∈ fp_frame.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag) ∧
          ∀ m_final : Memory,
            SepLensStateInv env₀.length entries' m_final →
            LensFramePreserved entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    StatefulVerificationResult
      (frameStatefulClaim { body := body, pre := Pre, post := Post } R_frame) := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  intro args m₀ ⟨hPre, hR₀⟩
  rcases hStep args m₀ hPre with
    ⟨entries₀, entries', retVal, hBlock, hInv₀, hAddrs, hTags, hPost⟩
  exact mirWpConverges_of_sepLenses hBlock hInv₀ (fun m_final hInvF hPresF =>
    ⟨hPost m_final hInvF hPresF,
      supportedBy_of_lensFramePreserved hPresF hInv₀.callStack_nil
        hInvF.callStack_nil hSupp hAddrs hTags hR₀⟩)

/-- Conjoin a frame predicate `frame : HeapPred` onto a `TotalClaim`. -/
def frameTotalClaim (c : TotalClaim) (frame : HeapPred) : TotalClaim where
  body := c.body
  pre args mem := c.pre args mem ∧ frame mem
  post args mem retVal mem' := c.post args mem retVal mem' ∧ frame mem'

/--
Framed bridge from `mirWpConverges_of_sepLenses` to `TotalVerificationResult`:
any `SupportedBy R_frame fp_frame` heap predicate whose footprint avoids the
lens footprint is conjoined onto both the pre- and postcondition
(`frameTotalClaim`) with total termination.
-/
theorem verifyTotalMir_of_sepLenses_supportedFrame
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (R_frame : HeapPred) (fp_frame : Footprint)
    (hSupp : SupportedBy R_frame fp_frame)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepLensStateInv env₀.length entries₀ m₀ ∧
          (∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
            ∀ e ∈ entries₀, allocId ≠ e.1.allocId) ∧
          (∀ tag ∈ fp_frame.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag) ∧
          ∀ m_final : Memory,
            SepLensStateInv env₀.length entries' m_final →
            LensFramePreserved entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    TotalVerificationResult
      (frameTotalClaim { body := body, pre := Pre, post := Post } R_frame) := by
  refine verifyTotalMir_of_wpConverges _ ?_
  intro args m₀ ⟨hPre, hR₀⟩
  rcases hStep args m₀ hPre with
    ⟨entries₀, entries', retVal, hBlock, hInv₀, hAddrs, hTags, hPost⟩
  exact mirWpConverges_of_sepLenses hBlock hInv₀ (fun m_final hInvF hPresF =>
    ⟨hPost m_final hInvF hPresF,
      supportedBy_of_lensFramePreserved hPresF hInv₀.callStack_nil
        hInvF.callStack_nil hSupp hAddrs hTags hR₀⟩)

/-! ### Binary and Unary Instances of the General Bridges -/

/--
1-Lens Entry Bridge: `sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁) R_frame m₀`
together with `WfSingleMutBorrow frameLen rp₁ m₀` establishes
`SepLensStateInv frameLen [(rp₁, codec₁.encode a₁)] m₀`.
-/
theorem sepLensStateInv_of_sepConj_one {α : Type}
    {frameLen : Nat} {rp₁ : RawPtrVal} {codec₁ : ValueCodec α} {a₁ : α}
    {R_frame : SepProp} {m₀ : Memory}
    (hSep :
      SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁) R_frame) m₀)
    (hWf₁ : WfSingleMutBorrow frameLen rp₁ m₀) :
    SepLensStateInv frameLen [(rp₁, codec₁.encode a₁)] m₀ :=
  sepLensStateInv_of_sepConjBindings
    (bs := [MutBorrowBinding.bind rp₁ codec₁ a₁]) hSep hWf₁.toWfLensFrame
    (fun b hb => by
      rw [List.mem_singleton.mp hb]
      exact ⟨hWf₁.alloc_above_frame, hWf₁.exclusive⟩)

theorem sepConj_activeTypedMutBorrow_preserved_one {α : Type}
    {frameLen : Nat} {rp₁ : RawPtrVal} {codec₁ : ValueCodec α} {a_old a_new : α}
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_old) R_frame) m₀)
    (hInv_final : SepLensStateInv frameLen [(rp₁, codec₁.encode a_new)] m_final)
    (hWf : WfSingleMutBorrow frameLen rp₁ m₀)
    (hPres : LensFramePreserved [(rp₁, codec₁.encode a_old)] m₀ m_final)
    (h_R : LocalSepProp R_frame)
    (h_not_agg : ∀ a : α, ∀ elems, codec₁.encode a ≠ .aggregate 0 elems) :
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_new) R_frame) m_final :=
  sepConjBindings_preserved
    (bs := [MutBorrowBinding.bind rp₁ codec₁ a_old])
    (bs' := [MutBorrowBinding.bind rp₁ codec₁ a_new])
    hSep hWf.callStack_nil
    (fun b hb => by
      rw [List.mem_singleton.mp hb]
      exact hWf.exclusive.offset_zero)
    rfl hInv_final hPres h_R
    (fun b hb => by
      rw [List.mem_singleton.mp hb]
      exact h_not_agg a_old)
    (fun b hb => by
      rw [List.mem_singleton.mp hb]
      exact h_not_agg a_new)

/--
Aggregate-capable 1-Lens Exit Bridge: preserves
`sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_new) R_frame` for arbitrary pointee
codecs (including tuple and struct codecs) whenever `R_frame` satisfies
`LocalSepProp` and `RootAllocSepProp`.
-/
theorem sepConj_activeTypedMutBorrow_preserved_one_of_rootAlloc {α : Type}
    {frameLen : Nat} {rp₁ : RawPtrVal} {codec₁ : ValueCodec α} {a_old a_new : α}
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_old) R_frame) m₀)
    (hInv_final : SepLensStateInv frameLen [(rp₁, codec₁.encode a_new)] m_final)
    (hWf : WfSingleMutBorrow frameLen rp₁ m₀)
    (hPres : LensFramePreserved [(rp₁, codec₁.encode a_old)] m₀ m_final)
    (h_R : LocalSepProp R_frame)
    (h_rootR : RootAllocSepProp R_frame) :
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_new) R_frame) m_final :=
  sepConjBindings_preserved_of_rootAlloc
    (bs := [MutBorrowBinding.bind rp₁ codec₁ a_old])
    (bs' := [MutBorrowBinding.bind rp₁ codec₁ a_new])
    hSep hWf.callStack_nil
    (fun b hb => by
      rw [List.mem_singleton.mp hb]
      exact hWf.exclusive.offset_zero)
    rfl hInv_final hPres h_R h_rootR

/--
2-Lens Entry Bridge, now heterogeneous in the two pointee types: the binary
separating conjunction derives allocation and tag disjointness of the two
pointers instead of assuming it.
-/
theorem sepLensStateInv_of_sepConj_two {α β : Type}
    {frameLen : Nat} {rp₁ rp₂ : RawPtrVal}
    {codec₁ : ValueCodec α} {codec₂ : ValueCodec β} {a₁ : α} {a₂ : β}
    {R_frame : SepProp} {m₀ : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁)
          (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)) m₀)
    (hWf₁ : WfSingleMutBorrow frameLen rp₁ m₀)
    (hWf₂ : WfSingleMutBorrow frameLen rp₂ m₀) :
    SepLensStateInv frameLen
      [(rp₁, codec₁.encode a₁), (rp₂, codec₂.encode a₂)] m₀ :=
  sepLensStateInv_of_sepConjBindings
    (bs := [MutBorrowBinding.bind rp₁ codec₁ a₁,
      MutBorrowBinding.bind rp₂ codec₂ a₂])
    hSep hWf₁.toWfLensFrame
    (fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hWf₁.alloc_above_frame, hWf₁.exclusive⟩
      · rw [List.mem_singleton.mp hb]
        exact ⟨hWf₂.alloc_above_frame, hWf₂.exclusive⟩)

theorem sepConj_activeTypedMutBorrow_preserved_two {α β : Type}
    {frameLen : Nat} (rp₁ rp₂ : RawPtrVal)
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β)
    (a_old a_new : α) (b_old b_new : β)
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_old)
          (sepConj (ActiveTypedMutBorrow rp₂ codec₂ b_old) R_frame)) m₀)
    (hInv_final :
      SepLensStateInv frameLen
        [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] m_final)
    (hWf₁ : WfSingleMutBorrow frameLen rp₁ m₀)
    (hWf₂ : WfSingleMutBorrow frameLen rp₂ m₀)
    (hPres :
      LensFramePreserved
        [(rp₁, codec₁.encode a_old), (rp₂, codec₂.encode b_old)] m₀ m_final)
    (h_R : LocalSepProp R_frame)
    (h_not_agg : ∀ a : α, ∀ elems, codec₁.encode a ≠ .aggregate 0 elems)
    (h_not_agg2 : ∀ b : β, ∀ elems, codec₂.encode b ≠ .aggregate 0 elems) :
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_new)
        (sepConj (ActiveTypedMutBorrow rp₂ codec₂ b_new) R_frame)) m_final :=
  sepConjBindings_preserved
    (bs := [MutBorrowBinding.bind rp₁ codec₁ a_old,
      MutBorrowBinding.bind rp₂ codec₂ b_old])
    (bs' := [MutBorrowBinding.bind rp₁ codec₁ a_new,
      MutBorrowBinding.bind rp₂ codec₂ b_new])
    hSep hWf₁.callStack_nil
    (fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hWf₁.exclusive.offset_zero
      · rw [List.mem_singleton.mp hb]
        exact hWf₂.exclusive.offset_zero)
    rfl hInv_final hPres h_R
    (fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h_not_agg a_old
      · rw [List.mem_singleton.mp hb]
        exact h_not_agg2 b_old)
    (fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact h_not_agg a_new
      · rw [List.mem_singleton.mp hb]
        exact h_not_agg2 b_new)

/--
Binary separating conjunctions of typed mutable borrows have distinct pointers
(a consequence of the derived tag disjointness).
-/
theorem pairwise_disjoint_of_sepConj_two_ne {α β : Type}
    {rp₁ rp₂ : RawPtrVal} {codec₁ : ValueCodec α} {codec₂ : ValueCodec β}
    {a₁ : α} {a₂ : β} {R_frame : SepProp} {m₀ : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁)
          (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)) m₀) :
    rp₁ ≠ rp₂ := by
  intro hEq
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjBindings_split
      (bs := [MutBorrowBinding.bind rp₁ codec₁ a₁,
        MutBorrowBinding.bind rp₂ codec₂ a₂]) hSep with ⟨_, hPair, _⟩
  rcases List.pairwise_cons.mp hPair with ⟨hHead, _⟩
  exact (hHead _ (List.Mem.head _)).2 (congrArg RawPtrVal.tag hEq)

/-! ### Sub-Place MIR Execution Over Field-Granular Reborrows -/

theorem projectionsOverlapAux_nil_right (xs : List ProjectionElem) :
    projectionsOverlapAux xs [] = true := by
  cases xs <;> rfl

theorem projectionsOverlapAux_field_prefix_eq_false
    {normB tailNorm : List ProjectionElem}
    {outerIdx : FieldIdx} {outerTy : Ty}
    (h : projectionsOverlapAux normB [.field outerIdx outerTy] = false) :
    projectionsOverlapAux normB (.field outerIdx outerTy :: tailNorm) =
      false := by
  cases normB with
  | nil => nomatch h
  | cons elem restB =>
    cases elem with
    | field idxB tyB =>
      unfold projectionsOverlapAux at h ⊢
      cases hEq : Nat.beq idxB outerIdx with
      | false => rfl
      | true =>
        rw [hEq, projectionsOverlapAux_nil_right] at h
        nomatch h
    | _ => nomatch h

theorem borrowEntryOverlapsWrite_field_prefix_eq_false
    {b : BorrowEntry} {outerIdx : FieldIdx} {outerTy : Ty}
    {tailProj : List ProjectionElem}
    (h : borrowEntryOverlapsWrite b [.field outerIdx outerTy] 0 0 = false) :
    borrowEntryOverlapsWrite b (.field outerIdx outerTy :: tailProj) 0 0 =
      false := by
  unfold borrowEntryOverlapsWrite projectionsOverlap at h ⊢
  dsimp only [Nat.beq, Bool.not, Bool.and, stripTransparentProjections] at h ⊢
  exact projectionsOverlapAux_field_prefix_eq_false h

theorem borrowEntryOverlapsWrite_eq_of_proj_range
    {b₁ b₂ : BorrowEntry}
    (hProj : b₁.targetProjection = b₂.targetProjection)
    (hRO : b₁.rangeOffset = b₂.rangeOffset)
    (hRL : b₁.rangeLen = b₂.rangeLen)
    (writeProj : List ProjectionElem) (off len : Nat) :
    borrowEntryOverlapsWrite b₁ writeProj off len =
      borrowEntryOverlapsWrite b₂ writeProj off len := by
  unfold borrowEntryOverlapsWrite
  rw [hProj, hRO, hRL]

theorem TreeFieldExclusiveBorrow.attachProtector
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty} {m : Memory}
    (hExcl : TreeFieldExclusiveBorrow rp fieldIdx fieldTy m)
    (tag protId : Nat) :
    TreeFieldExclusiveBorrow rp fieldIdx fieldTy {
      m with
      borrows := attachBorrowProtector m.borrows tag protId
      activeProtectors := protId :: m.activeProtectors
      nextProtector := Nat.add protId 1
    } where
  offset_zero := hExcl.offset_zero
  lookup_active := by
    rcases hExcl.lookup_active with
      ⟨entry, hLook, hT, hP, hPerm, hRO, hRL⟩
    rcases lookupBorrow_attachBorrowProtector_some
        (tag := tag) (pid := protId) hLook with
      ⟨entry', hLook', hT', hP', hPerm', hRO', hRL'⟩
    exact ⟨entry', hLook', hT'.trans hT, hP'.trans hP, hPerm'.trans hPerm,
      hRO'.trans hRO, hRL'.trans hRL⟩
  ancestors_disjoint_or_disabled b hb hTargetB := by
    rcases mem_attachBorrowProtector hb with
      ⟨b₀, hb₀, hTagB, hTargetB₀, hProjB, hPermB, hROB, hRLB⟩
    dsimp only
    rw [isBorrowDescendantOrSelf_attachBorrowProtector, hTagB, hPermB,
      borrowEntryOverlapsWrite_eq_of_proj_range hProjB hROB hRLB]
    exact hExcl.ancestors_disjoint_or_disabled b₀ hb₀
      (hTargetB₀.symm.trans hTargetB)

theorem freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField_prefix
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat} {fieldIdx : FieldIdx} {fieldTy : Ty}
    (tailProj : List ProjectionElem)
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          (borrowEntryOverlapsWrite b [.field fieldIdx fieldTy] 0 0 = false ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    freezeTreeBorrowsOnReadAtProj
      allBorrows borrows allocId (.some tag)
      (.field fieldIdx fieldTy :: tailProj) 0 0 = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold freezeTreeBorrowsOnReadAtProj
    rw [hTail]
    unfold updateBorrowPermOnReadAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hTree hd (List.Mem.head tl) hTargetEq with
        ⟨hDesc, _⟩ | ⟨hNoOverlap, _⟩ | hDis
      · cases borrowEntryOverlapsWrite hd
            (.field fieldIdx fieldTy :: tailProj) 0 0 with
        | false => rfl
        | true => dsimp only; rw [hDesc]
      · rw [borrowEntryOverlapsWrite_field_prefix_eq_false hNoOverlap]
      · cases borrowEntryOverlapsWrite hd
            (.field fieldIdx fieldTy :: tailProj) 0 0 with
        | false => rfl
        | true =>
          dsimp only
          cases isBorrowDescendantOrSelf allBorrows tag hd.tag with
          | true => rfl
          | false => dsimp only; rw [hDis]

theorem invalidateTreeBorrowsAtProj_eq_self_of_treeField_prefix
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat} {fieldIdx : FieldIdx} {fieldTy : Ty}
    (tailProj : List ProjectionElem)
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          (borrowEntryOverlapsWrite b [.field fieldIdx fieldTy] 0 0 = false ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    invalidateTreeBorrowsAtProj
      allBorrows borrows allocId (.some tag)
      (.field fieldIdx fieldTy :: tailProj) 0 0 = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold invalidateTreeBorrowsAtProj
    rw [hTail]
    unfold updateBorrowPermTreeAtProj updateBorrowPermAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      dsimp only
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hTree hd (List.Mem.head tl) hTargetEq with
        ⟨hDesc, hPerm⟩ | ⟨hNoOverlap, hPerm⟩ | hDis
      · rw [resolveTreeBorrowWriterTag_of_descendant hDesc]
        dsimp only
        have hEq : Nat.beq hd.tag hd.tag = true := by simp
        rw [hEq, hPerm]
      · have hNoPfx :=
          borrowEntryOverlapsWrite_field_prefix_eq_false (tailProj := tailProj)
            hNoOverlap
        cases resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
        | none => rw [hNoPfx]
        | some wTag =>
          dsimp only
          cases Nat.beq hd.tag wTag with
          | true => rw [hPerm]
          | false => rw [hNoPfx]
      · cases resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
        | none =>
          dsimp only
          cases borrowEntryOverlapsWrite hd
              (.field fieldIdx fieldTy :: tailProj) 0 0 <;>
            simp [hDis]
        | some wTag =>
          dsimp only
          cases Nat.beq hd.tag wTag with
          | true => simp [hDis]
          | false =>
            dsimp only
            cases borrowEntryOverlapsWrite hd
                (.field fieldIdx fieldTy :: tailProj) 0 0 with
            | false => rfl
            | true =>
              dsimp only
              rw [borrowEntry_disabled_eta hDis]

theorem hasProtectedTreeWriteConflict_eq_false_of_treeField_prefix
    (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    {allocId tag : Nat} {fieldIdx : FieldIdx} {fieldTy : Ty}
    (tailProj : List ProjectionElem)
    (hTree :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (isBorrowDescendantOrSelf allBorrows tag b.tag = true ∧
            b.perm = .active) ∨
          (borrowEntryOverlapsWrite b [.field fieldIdx fieldTy] 0 0 = false ∧
            b.perm = .active) ∨
          b.perm = .disabled) :
    hasProtectedTreeWriteConflict
      allBorrows borrows activeProtectors allocId (.some tag)
      (.field fieldIdx fieldTy :: tailProj) 0 0 = false := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hTree b (List.Mem.tail hd hb))
    unfold hasProtectedTreeWriteConflict
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => simp [hTail]
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hTree hd (List.Mem.head tl) hTargetEq with
        ⟨hDesc, _⟩ | ⟨hNoOverlap, _⟩ | hDis
      · have hNoConflict :
            borrowEntryWriteConflicts hd
              (resolveTreeBorrowWriterTag allBorrows hd (.some tag)) = false := by
          rw [resolveTreeBorrowWriterTag_of_descendant hDesc]
          unfold borrowEntryWriteConflicts
          simp
        simp [hNoConflict, hTail]
      · have hNoPfx :=
          borrowEntryOverlapsWrite_field_prefix_eq_false (tailProj := tailProj)
            hNoOverlap
        simp [hNoPfx, hTail]
      · have hNoConflict :
            borrowEntryWriteConflicts hd
              (resolveTreeBorrowWriterTag allBorrows hd (.some tag)) = false := by
          unfold borrowEntryWriteConflicts
          cases resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
          | none => simp [hDis]
          | some wTag =>
            cases hEq : Nat.beq hd.tag wTag <;> simp [hEq, hDis]
        simp [hNoConflict, hTail]

theorem eq_aggregate_of_readFieldAt_some
    {locals : List LocalValue} {allocId : Local}
    {fieldIdx : FieldIdx} {v : Value}
    (h : readFieldAt? locals allocId fieldIdx = .some v) :
    ∃ elems : List Value,
      get? locals allocId = .some (.init (.aggregate 0 elems)) ∧
      get? elems fieldIdx = .some v := by
  unfold readFieldAt? at h
  cases hGet : get? locals allocId with
  | none => rw [hGet] at h; nomatch h
  | some slot =>
    rw [hGet] at h
    cases slot with
    | dead => nomatch h
    | uninit => nomatch h
    | init val =>
      cases val with
      | unit => nomatch h
      | scalar _ => nomatch h
      | ptr _ _ => nomatch h
      | aggregate varIdx elems =>
        cases varIdx with
        | succ _ => nomatch h
        | zero => exact ⟨elems, rfl, h⟩

theorem readFieldAt_writeFieldAt_self
    {locals : List LocalValue} {allocId : Local}
    {fieldIdx : FieldIdx} {oldVal newVal : Value}
    (h : readFieldAt? locals allocId fieldIdx = .some oldVal) :
    readFieldAt? (writeFieldAt? locals allocId fieldIdx newVal)
      allocId fieldIdx = .some newVal := by
  rcases eq_aggregate_of_readFieldAt_some h with ⟨elems, hGet, hElem⟩
  have hLtAlloc : allocId < locals.length :=
    (List.getElem?_eq_some_iff.mp hGet).1
  have hLtField : fieldIdx < elems.length :=
    (List.getElem?_eq_some_iff.mp hElem).1
  unfold writeFieldAt? readFieldAt?
  rw [hGet]
  dsimp only
  unfold get?
  rw [List.getElem?_set_self hLtAlloc]
  dsimp only
  exact List.getElem?_set_self hLtField

/--
Target sub-place of a tracked mutable borrow pointer: either a whole caller
allocation (`.root`, `targetProjection = []`) or a single field of a caller
variant-`0` aggregate (`.field fieldIdx fieldTy`,
`targetProjection = [.field fieldIdx fieldTy]`).
-/
inductive BorrowSubplace where
  | root
  | field (fieldIdx : FieldIdx) (fieldTy : Ty)

/--
Pairwise disjointness of two tracked pointers under `subplaceOf`: distinct
provenance tags, and either distinct allocations or distinct fields on a shared
aggregate allocation.
-/
def BorrowSubplace.disjointOn
    (subplaceOf : RawPtrVal → BorrowSubplace)
    (k₁ k₂ : RawPtrVal) : Prop :=
  k₁.tag ≠ k₂.tag ∧
  (k₁.allocId ≠ k₂.allocId ∨
    ∃ f₁ ty₁ f₂ ty₂,
      subplaceOf k₁ = .field f₁ ty₁ ∧
      subplaceOf k₂ = .field f₂ ty₂ ∧
      f₁ ≠ f₂)

theorem BorrowSubplace.disjointOn_symm
    {subplaceOf : RawPtrVal → BorrowSubplace} {k₁ k₂ : RawPtrVal}
    (h : BorrowSubplace.disjointOn subplaceOf k₁ k₂) :
    BorrowSubplace.disjointOn subplaceOf k₂ k₁ := by
  refine ⟨h.1.symm, ?_⟩
  rcases h.2 with hAlloc | ⟨f₁, ty₁, f₂, ty₂, hS₁, hS₂, hNe⟩
  · exact Or.inl hAlloc.symm
  · exact Or.inr ⟨f₂, ty₂, f₁, ty₁, hS₂, hS₁, hNe.symm⟩

/-- Write `newVal` into `rp`'s tracked sub-place inside `locals`. -/
def writeSubplaceAt
    (subplaceOf : RawPtrVal → BorrowSubplace)
    (locals : List LocalSlot) (rp : RawPtrVal) (newVal : Value) :
    List LocalSlot :=
  match subplaceOf rp with
  | .root => locals.set rp.allocId (.init newVal)
  | .field fieldIdx _ => writeFieldAt? locals rp.allocId fieldIdx newVal

/-- Validity of a single pure lens binding `(rp, v)` under `subplaceOf`. -/
def BorrowSubplace.entryValid
    (subplaceOf : RawPtrVal → BorrowSubplace)
    (frameLen : Nat) (rp : RawPtrVal) (v : Value) (m : Memory) : Prop :=
  rp.offset = 0 ∧
  frameLen ≤ rp.allocId ∧
  match subplaceOf rp with
  | .root =>
    get? m.callerLocals rp.allocId = .some (.init v) ∧
    TreeExclusiveBorrow rp m
  | .field fieldIdx fieldTy =>
    readFieldAt? m.callerLocals rp.allocId fieldIdx = .some v ∧
    TreeFieldExclusiveBorrow rp fieldIdx fieldTy m

/--
Sub-place separation-logic lens-state invariant (`SepSubplaceLensStateInv`):
generalizes `SepLensStateInv` so tracked mutable borrows may target either root
caller slots (`.root`) or sibling fields of a shared aggregate allocation
(`.field fieldIdx fieldTy`), enabling `LiftLensBlock` MIR execution of
`swap_u32(&mut s.0, &mut s.1)` and `add_assign_retag(&mut s.0, d)` without
changing any pure lifting rule.
-/
structure SepSubplaceLensStateInv
    (subplaceOf : RawPtrVal → BorrowSubplace)
    (frameLen : Nat)
    (entries : List (RawPtrVal × Value))
    (m : Memory) : Prop where
  callStack_nil : m.callStack = []
  activeCallee_none : m.activeCallee = .none
  borrows_above_frame : ∀ b ∈ m.borrows, frameLen ≤ b.targetLocal
  entries_valid :
    ∀ rp v, (rp, v) ∈ entries →
      BorrowSubplace.entryValid subplaceOf frameLen rp v m
  pairwise_disjoint :
    List.Pairwise (BorrowSubplace.disjointOn subplaceOf)
      (entries.map Prod.fst)

theorem SepLensStateInv.toSubplace
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    (hInv : SepLensStateInv frameLen entries m) :
    SepSubplaceLensStateInv (fun _ => .root) frameLen entries m where
  callStack_nil := hInv.callStack_nil
  activeCallee_none := hInv.activeCallee_none
  borrows_above_frame := hInv.borrows_above_frame
  entries_valid rp v hMem := hInv.entries_valid rp v hMem
  pairwise_disjoint :=
    List.Pairwise.imp (fun h => ⟨h.2, Or.inl h.1⟩) hInv.pairwise_disjoint

theorem mem_updateLensVal_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {entries : List (RawPtrVal × Value)} {rp k : RawPtrVal} {newVal v : Value}
    (hPairwise :
      List.Pairwise (BorrowSubplace.disjointOn subplaceOf)
        (entries.map Prod.fst))
    (hMem : (k, v) ∈ updateLensVal entries rp newVal) :
    (k = rp ∧ v = newVal) ∨ (k ≠ rp ∧ (k, v) ∈ entries) := by
  induction entries with
  | nil => nomatch hMem
  | cons hd tl ih =>
    rcases hd with ⟨k₀, w₀⟩
    simp only [List.map_cons, List.pairwise_cons] at hPairwise
    rcases hPairwise with ⟨hHdNotInTl, hTlPairwise⟩
    unfold updateLensVal at hMem
    by_cases hEq : k₀ = rp
    · subst hEq
      simp only [ite_true, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · injection hHead with hK hV
        exact Or.inl ⟨hK, hV⟩
      · have hKInTl : k ∈ tl.map Prod.fst :=
          List.mem_map.mpr ⟨(k, v), hTail, rfl⟩
        have hDisj := hHdNotInTl k hKInTl
        have hNe : k ≠ k₀ := fun h => hDisj.1 (congrArg RawPtrVal.tag h.symm)
        exact Or.inr ⟨hNe, List.Mem.tail _ hTail⟩
    · simp only [hEq, ite_false, List.mem_cons] at hMem
      rcases hMem with hHead | hTail
      · injection hHead with hK hV
        subst hK hV
        exact Or.inr ⟨hEq, List.Mem.head tl⟩
      · rcases ih hTlPairwise hTail with hLeft | ⟨hNe, hInTl⟩
        · exact Or.inl hLeft
        · exact Or.inr ⟨hNe, List.Mem.tail _ hInTl⟩

theorem pairwise_subplace_of_mem_ne
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {entries : List (RawPtrVal × Value)} {rp k : RawPtrVal} {v₁ v₂ : Value}
    (hPairwise :
      List.Pairwise (BorrowSubplace.disjointOn subplaceOf)
        (entries.map Prod.fst))
    (hMem₁ : (rp, v₁) ∈ entries)
    (hMem₂ : (k, v₂) ∈ entries)
    (hNe : k ≠ rp) :
    BorrowSubplace.disjointOn subplaceOf k rp := by
  induction entries with
  | nil => nomatch hMem₁
  | cons hd tl ih =>
    rcases hd with ⟨k₀, w₀⟩
    simp only [List.map_cons, List.pairwise_cons] at hPairwise
    rcases hPairwise with ⟨hHd, hTl⟩
    simp only [List.mem_cons] at hMem₁ hMem₂
    rcases hMem₁ with h₁ | h₁ <;> rcases hMem₂ with h₂ | h₂
    · injection h₁ with hK₁ _
      injection h₂ with hK₂ _
      exact absurd (hK₂.trans hK₁.symm) hNe
    · injection h₁ with hK₁ _
      subst hK₁
      have hIn : k ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(k, v₂), h₂, rfl⟩
      exact BorrowSubplace.disjointOn_symm (hHd k hIn)
    · injection h₂ with hK₂ _
      subst hK₂
      have hIn : rp ∈ tl.map Prod.fst := List.mem_map.mpr ⟨(rp, v₁), h₁, rfl⟩
      exact hHd rp hIn
    · exact ih hTl h₁ h₂

/--
Sub-place relational frame preservation (`SubplaceLensFramePreserved`): tracks
preservation of untouched caller allocations, untouched sibling fields on
partially borrowed caller aggregates, and untouched borrow-table tags.
-/
structure SubplaceLensFramePreserved
    (subplaceOf : RawPtrVal → BorrowSubplace)
    (entries₀ : List (RawPtrVal × Value))
    (m₀ m : Memory) : Prop where
  locals_unchanged_outside :
    ∀ allocId : Nat,
      (∀ e ∈ entries₀, allocId ≠ e.1.allocId) →
        get? m.callerLocals allocId = get? m₀.callerLocals allocId
  fields_unchanged_outside :
    ∀ (allocId : Nat) (fieldIdx : FieldIdx),
      (∀ e ∈ entries₀, e.1.allocId = allocId →
        ∃ f ty, subplaceOf e.1 = .field f ty ∧ f ≠ fieldIdx) →
        readFieldAt? m.callerLocals allocId fieldIdx =
          readFieldAt? m₀.callerLocals allocId fieldIdx
  borrows_unchanged_outside :
    ∀ tag : Nat,
      (∀ e ∈ entries₀, tag ≠ e.1.tag) →
        lookupBorrow m.borrows tag = lookupBorrow m₀.borrows tag

theorem SubplaceLensFramePreserved.refl
    (subplaceOf : RawPtrVal → BorrowSubplace)
    (entries₀ : List (RawPtrVal × Value)) (m₀ : Memory) :
    SubplaceLensFramePreserved subplaceOf entries₀ m₀ m₀ where
  locals_unchanged_outside _ _ := rfl
  fields_unchanged_outside _ _ _ := rfl
  borrows_unchanged_outside _ _ := rfl

theorem SubplaceLensFramePreserved.toLensFramePreserved
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {entries₀ : List (RawPtrVal × Value)} {m₀ m : Memory}
    (h : SubplaceLensFramePreserved subplaceOf entries₀ m₀ m) :
    LensFramePreserved entries₀ m₀ m :=
  ⟨h.locals_unchanged_outside, h.borrows_unchanged_outside⟩

theorem SepSubplaceLensStateInv.attachProtector
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    (hInv : SepSubplaceLensStateInv subplaceOf frameLen entries m)
    (tag protId : Nat) :
    SepSubplaceLensStateInv subplaceOf frameLen entries {
      m with
      borrows := attachBorrowProtector m.borrows tag protId
      activeProtectors := protId :: m.activeProtectors
      nextProtector := Nat.add protId 1
    } where
  callStack_nil := hInv.callStack_nil
  activeCallee_none := hInv.activeCallee_none
  borrows_above_frame b hb := by
    rcases mem_attachBorrowProtector hb with ⟨b₀, hb₀, _, hTarget, _⟩
    rw [hTarget]
    exact hInv.borrows_above_frame b₀ hb₀
  entries_valid rp v hMem := by
    have hVal := hInv.entries_valid rp v hMem
    unfold BorrowSubplace.entryValid at hVal ⊢
    rcases hVal with ⟨hOff, hAbove, hRest⟩
    refine ⟨hOff, hAbove, ?_⟩
    cases hSub : subplaceOf rp with
    | root =>
      rw [hSub] at hRest
      rcases hRest with ⟨hCaller, hExcl⟩
      have hSingle : SepLensStateInv frameLen [(rp, v)] m := {
        callStack_nil := hInv.callStack_nil
        activeCallee_none := hInv.activeCallee_none
        borrows_above_frame := hInv.borrows_above_frame
        entries_valid := fun k w hK => by
          rcases List.mem_singleton.mp hK with ⟨rfl, rfl⟩
          exact ⟨hOff, hAbove, hCaller, hExcl⟩
        pairwise_disjoint := by simp
      }
      have hAtt := hSingle.attachProtector tag protId
      exact ⟨hCaller,
        (hAtt.entries_valid rp v (List.Mem.head [])).2.2.2⟩
    | field fieldIdx fieldTy =>
      rw [hSub] at hRest
      exact ⟨hRest.1, hRest.2.attachProtector tag protId⟩
  pairwise_disjoint := hInv.pairwise_disjoint

theorem SepSubplaceLensStateInv.updateSubplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp : RawPtrVal} {oldVal newVal : Value}
    (hInv : SepSubplaceLensStateInv subplaceOf frameLen entries m)
    (hLook : lookupLensVal? entries rp = .some oldVal) :
    SepSubplaceLensStateInv subplaceOf frameLen
      (updateLensVal entries rp newVal)
      { m with
        callerLocals :=
          writeSubplaceAt subplaceOf m.callerLocals rp newVal } where
  callStack_nil := hInv.callStack_nil
  activeCallee_none := hInv.activeCallee_none
  borrows_above_frame := hInv.borrows_above_frame
  entries_valid k v hMemNew := by
    have hMemRp : (rp, oldVal) ∈ entries := lookupLensVal?_mem hLook
    have hValRp := hInv.entries_valid rp oldVal hMemRp
    unfold BorrowSubplace.entryValid at hValRp ⊢
    rcases hValRp with ⟨hOffRp, hAboveRp, hRestRp⟩
    rcases mem_updateLensVal_subplace hInv.pairwise_disjoint hMemNew with
      ⟨rfl, rfl⟩ | ⟨hNe, hMemOld⟩
    · refine ⟨hOffRp, hAboveRp, ?_⟩
      unfold writeSubplaceAt
      cases hSub : subplaceOf k with
      | root =>
        rw [hSub] at hRestRp
        have hLtRp : k.allocId < m.callerLocals.length :=
          (List.getElem?_eq_some_iff.mp hRestRp.1).1
        refine ⟨?_, TreeExclusiveBorrow.of_borrows_eq hRestRp.2 rfl⟩
        unfold get?
        exact List.getElem?_set_self hLtRp
      | field fieldIdx fieldTy =>
        rw [hSub] at hRestRp
        exact ⟨readFieldAt_writeFieldAt_self hRestRp.1,
          TreeFieldExclusiveBorrow.of_borrows_eq hRestRp.2 rfl⟩
    · have hValK := hInv.entries_valid k v hMemOld
      unfold BorrowSubplace.entryValid at hValK
      rcases hValK with ⟨hOffK, hAboveK, hRestK⟩
      have hDisj :=
        pairwise_subplace_of_mem_ne hInv.pairwise_disjoint hMemRp hMemOld hNe
      refine ⟨hOffK, hAboveK, ?_⟩
      unfold writeSubplaceAt
      rcases hDisj.2 with hNeAlloc | ⟨fK, tyK, fRp, tyRp, hSubK, hSubRp, hNeF⟩
      · cases hSubRp : subplaceOf rp with
        | root =>
          cases hSubK : subplaceOf k with
          | root =>
            rw [hSubK] at hRestK
            refine ⟨?_, TreeExclusiveBorrow.of_borrows_eq hRestK.2 rfl⟩
            unfold get? at hRestK ⊢
            rw [List.getElem?_set_ne hNeAlloc.symm]
            exact hRestK.1
          | field fK tyK =>
            rw [hSubK] at hRestK
            refine ⟨?_, TreeFieldExclusiveBorrow.of_borrows_eq hRestK.2 rfl⟩
            unfold readFieldAt?
            unfold get?
            rw [List.getElem?_set_ne hNeAlloc.symm]
            exact hRestK.1
        | field fRp tyRp =>
          cases hSubK : subplaceOf k with
          | root =>
            rw [hSubK] at hRestK
            refine ⟨?_, TreeExclusiveBorrow.of_borrows_eq hRestK.2 rfl⟩
            rw [get?_writeFieldAt_ne_alloc _ _ _ hNeAlloc]
            exact hRestK.1
          | field fK tyK =>
            rw [hSubK] at hRestK
            refine ⟨?_, TreeFieldExclusiveBorrow.of_borrows_eq hRestK.2 rfl⟩
            unfold readFieldAt?
            rw [get?_writeFieldAt_ne_alloc _ _ _ hNeAlloc]
            exact hRestK.1
      · rw [hSubRp, hSubK]
        rw [hSubK] at hRestK
        dsimp only
        refine ⟨?_, TreeFieldExclusiveBorrow.of_borrows_eq hRestK.2 rfl⟩
        by_cases hSameAlloc : k.allocId = rp.allocId
        · rw [hSameAlloc, readFieldAt_writeFieldAt_ne_eq _ _ _ hNeF.symm]
          rw [← hSameAlloc]
          exact hRestK.1
        · unfold readFieldAt?
          rw [get?_writeFieldAt_ne_alloc _ _ _ hSameAlloc]
          exact hRestK.1
  pairwise_disjoint := by
    rw [updateLensVal_map_fst]
    exact hInv.pairwise_disjoint

theorem LiftDerefRead.evalOperand_and_freeze_eq_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value} {m : Memory}
    (h : LiftDerefRead env entries op v env')
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries m)
    (layouts : LayoutTable)
    (localDecls : List LocalDecl := .nil) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals localDecls =
      .ok v env' ∧
    env' = env ∧
    (∀ ptrLoc restProj,
      (op = .copy { local_ := ptrLoc, projection := .deref :: restProj } ∨
       op = .move { local_ := ptrLoc, projection := .deref :: restProj }) →
      freezeDerefReadBorrowsAt env ptrLoc restProj m.borrows = m.borrows) := by
  cases h with
  | copy_deref hGetPtr hLookVal =>
    rename_i ptrLoc rp
    have hVal := hInv.entries_valid rp v (lookupLensVal?_mem hLookVal)
    unfold BorrowSubplace.entryValid at hVal
    rcases hVal with ⟨hOff, hAbove, hRest⟩
    cases hSub : subplaceOf rp with
    | root =>
      rw [hSub] at hRest
      rcases hRest with ⟨hCaller, _, ⟨entry, hLookB, hT, hP, hPerm, _, _⟩,
        hExcl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP]
          rw [hEnvNone, hT, hCaller]
          rfl
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · injection hCopy with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
            m.borrows m.borrows _ _ _ hExcl
        · nomatch hMove
    | field fieldIdx fieldTy =>
      rw [hSub] at hRest
      rcases hRest with ⟨hField, _, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩,
        hExcl⟩
      rcases eq_aggregate_of_readFieldAt_some hField with ⟨elems, hCaller, hEl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP, hOff]
          rw [hEnvNone, hT, hCaller]
          dsimp only [appendProjections, readProjectedValue]
          rw [hEl]
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · injection hCopy with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT, hP, hRO, hRL]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField
            m.borrows m.borrows hExcl
        · nomatch hMove
  | move_deref hGetPtr hLookVal =>
    rename_i ptrLoc rp
    have hVal := hInv.entries_valid rp v (lookupLensVal?_mem hLookVal)
    unfold BorrowSubplace.entryValid at hVal
    rcases hVal with ⟨hOff, hAbove, hRest⟩
    cases hSub : subplaceOf rp with
    | root =>
      rw [hSub] at hRest
      rcases hRest with ⟨hCaller, _, ⟨entry, hLookB, hT, hP, hPerm, _, _⟩,
        hExcl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP]
          rw [hEnvNone, hT, hCaller]
          rfl
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · nomatch hCopy
        · injection hMove with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
            m.borrows m.borrows _ _ _ hExcl
    | field fieldIdx fieldTy =>
      rw [hSub] at hRest
      rcases hRest with ⟨hField, _, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩,
        hExcl⟩
      rcases eq_aggregate_of_readFieldAt_some hField with ⟨elems, hCaller, hEl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP, hOff]
          rw [hEnvNone, hT, hCaller]
          dsimp only [appendProjections, readProjectedValue]
          rw [hEl]
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · nomatch hCopy
        · injection hMove with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT, hP, hRO, hRL]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField
            m.borrows m.borrows hExcl

theorem LiftDerefFieldRead.evalOperand_and_freeze_eq_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value} {m : Memory}
    (h : LiftDerefFieldRead env entries op v env')
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries m)
    (layouts : LayoutTable)
    (localDecls : List LocalDecl := .nil) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals localDecls =
      .ok v env' ∧
    env' = env ∧
    (∀ ptrLoc restProj,
      (op = .copy { local_ := ptrLoc, projection := .deref :: restProj } ∨
       op = .move { local_ := ptrLoc, projection := .deref :: restProj }) →
      freezeDerefReadBorrowsAt env ptrLoc restProj m.borrows = m.borrows) := by
  cases h with
  | copy_deref_field hGetPtr hLookVal hRead =>
    rename_i ptrLoc subIdx subTy rp aggVal
    have hVal := hInv.entries_valid rp aggVal (lookupLensVal?_mem hLookVal)
    unfold BorrowSubplace.entryValid at hVal
    rcases hVal with ⟨hOff, hAbove, hRest⟩
    cases hSub : subplaceOf rp with
    | root =>
      rw [hSub] at hRest
      rcases hRest with ⟨hCaller, _, ⟨entry, hLookB, hT, hP, hPerm, _, _⟩,
        hExcl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP]
          rw [hEnvNone, hT, hCaller]
          dsimp only
          rw [hRead]
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · injection hCopy with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
            m.borrows m.borrows _ _ _ hExcl
        · nomatch hMove
    | field outerIdx outerTy =>
      rw [hSub] at hRest
      rcases hRest with ⟨hField, _, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩,
        hExcl⟩
      rcases eq_aggregate_of_readFieldAt_some hField with ⟨elems, hCaller, hEl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP, hOff]
          rw [hEnvNone, hT, hCaller]
          dsimp only [appendProjections, readProjectedValue]
          rw [hEl]
          dsimp only [readProjectedValue]
          rw [hRead]
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · injection hCopy with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT, hP, hRO, hRL]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField_prefix
            m.borrows m.borrows [.field subIdx subTy] hExcl
        · nomatch hMove
  | move_deref_field hGetPtr hLookVal hRead =>
    rename_i ptrLoc subIdx subTy rp aggVal
    have hVal := hInv.entries_valid rp aggVal (lookupLensVal?_mem hLookVal)
    unfold BorrowSubplace.entryValid at hVal
    rcases hVal with ⟨hOff, hAbove, hRest⟩
    cases hSub : subplaceOf rp with
    | root =>
      rw [hSub] at hRest
      rcases hRest with ⟨hCaller, _, ⟨entry, hLookB, hT, hP, hPerm, _, _⟩,
        hExcl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP]
          rw [hEnvNone, hT, hCaller]
          dsimp only
          rw [hRead]
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · nomatch hCopy
        · injection hMove with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_tree
            m.borrows m.borrows _ _ _ hExcl
    | field outerIdx outerTy =>
      rw [hSub] at hRest
      rcases hRest with ⟨hField, _, ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩,
        hExcl⟩
      rcases eq_aggregate_of_readFieldAt_some hField with ⟨elems, hCaller, hEl⟩
      have hEnvNone : get? env entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le hAbove
      refine ⟨?_, rfl, ?_⟩
      · cases localDecls <;>
        · unfold evalOperand
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          simp [ProvenancePtr.tag, hLookB, hPerm, hP, hOff]
          rw [hEnvNone, hT, hCaller]
          dsimp only [appendProjections, readProjectedValue]
          rw [hEl]
          dsimp only [readProjectedValue]
          rw [hRead]
      · intro pLoc rProj hOpEq
        rcases hOpEq with hCopy | hMove
        · nomatch hCopy
        · injection hMove with hPlace
          injection hPlace with hLoc hProj
          injection hProj with _ hR
          subst hLoc hR
          unfold freezeDerefReadBorrowsAt
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          dsimp only
          rw [hT, hP, hRO, hRL]
          exact freezeTreeBorrowsOnReadAtProj_eq_self_of_treeField_prefix
            m.borrows m.borrows [.field subIdx subTy] hExcl

theorem LiftLensOperandAny.evalOperand_eq_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value} {m : Memory}
    (h : LiftLensOperandAny localDecls layouts env entries op v env')
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries m) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals localDecls =
      .ok v env' ∧
    env'.length = env.length := by
  cases h with
  | pure hOp =>
    exact hOp.evalOperand_eq m.borrows m.globals m.callerLocals
  | deref hDeref =>
    rcases hDeref.evalOperand_and_freeze_eq_subplace hInv layouts localDecls with
      ⟨hEval, hEnvEq, _⟩
    subst hEnvEq
    exact ⟨hEval, rfl⟩
  | deref_field hField =>
    rcases hField.evalOperand_and_freeze_eq_subplace hInv layouts localDecls with
      ⟨hEval, hEnvEq, _⟩
    subst hEnvEq
    exact ⟨hEval, rfl⟩

theorem LiftLensOperands.evalOperands_eq_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {ops : List Operand} {vs : List Value} {m : Memory}
    (h : LiftLensOperands localDecls layouts env entries ops vs env')
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries m) :
    evalOperands env ops m.borrows m.globals layouts m.callerLocals localDecls =
      .ok vs env' ∧
    env'.length = env.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | cons hOp _ ih =>
    rcases hOp.evalOperand_eq_subplace hInv with ⟨hEval₁, hLen₁⟩
    rcases ih (by rw [hLen₁]; exact hInv) with ⟨hEval₂, hLen₂⟩
    refine ⟨?_, hLen₂.trans hLen₁⟩
    unfold evalOperands
    rw [hEval₁]
    dsimp only
    rw [hEval₂]

theorem LiftLensRvalue.evalRvalue_eq_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {rv : Rvalue} {v : Value} {m : Memory}
    (h : LiftLensRvalue localDecls layouts env entries rv v env')
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries m) :
    evalRvalue env rv m localDecls layouts = .ok v env' m ∧
    env'.length = env.length := by
  cases h with
  | use_pure hOp hVal =>
    rcases hOp.evalOperand_eq m.borrows m.globals m.callerLocals with
      ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    simp only [hEval]
    rw [hVal]
    dsimp only
    exact hOp.not_deref m.borrows m
  | use_deref hDeref hVal =>
    rcases hDeref.evalOperand_and_freeze_eq_subplace hInv layouts localDecls with
      ⟨hEval, hEnvEq, hFreeze⟩
    subst hEnvEq
    refine ⟨?_, rfl⟩
    unfold evalRvalue
    simp only [hEval]
    rw [hVal]
    dsimp only
    cases hDeref with
    | copy_deref _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ [] (Or.inl rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
    | move_deref _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ [] (Or.inr rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
  | use_deref_field hField hVal =>
    rcases hField.evalOperand_and_freeze_eq_subplace hInv layouts localDecls with
      ⟨hEval, hEnvEq, hFreeze⟩
    subst hEnvEq
    refine ⟨?_, rfl⟩
    unfold evalRvalue
    simp only [hEval]
    rw [hVal]
    dsimp only
    cases hField with
    | copy_deref_field _ _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ _ (Or.inl rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
    | move_deref_field _ _ _ =>
      cases hB : m.borrows with
      | nil => rfl
      | cons b₁ tl =>
        cases tl with
        | nil => rfl
        | cons b₂ rest =>
          have hFr := hFreeze _ _ (Or.inr rfl)
          rw [hB] at hFr
          dsimp only
          rw [hFr, ← hB]
  | copyForDeref_deref hGetPtr hLookVal =>
    have hDeref :
        LiftDerefRead env entries
          (.copy { local_ := _, projection := [.deref] }) v env :=
      .copy_deref hGetPtr hLookVal
    rcases hDeref.evalOperand_and_freeze_eq_subplace hInv layouts localDecls with
      ⟨hEval, _, hFreeze⟩
    refine ⟨?_, rfl⟩
    unfold evalRvalue
    simp [hEval]
    cases hB : m.borrows with
    | nil => rfl
    | cons b₁ tl =>
      cases tl with
      | nil => rfl
      | cons b₂ rest =>
        have hFr := hFreeze _ [] (Or.inl rfl)
        rw [hB] at hFr
        dsimp only
        rw [hFr, ← hB]
  | binaryOp hLhs hRhs hEvalOp =>
    rcases hLhs.evalOperand_eq_subplace hInv with ⟨hEval₁, hLen₁⟩
    rcases hRhs.evalOperand_eq_subplace (by rw [hLen₁]; exact hInv)
      with ⟨hEval₂, hLen₂⟩
    refine ⟨?_, hLen₂.trans hLen₁⟩
    unfold evalRvalue
    dsimp only
    rw [hEval₁]
    dsimp only
    rw [hEval₂]
    dsimp only
    split
    · have hBad := hEvalOp m
      unfold evalScalarBinOp at hBad
      repeat' split at hBad
      all_goals contradiction
    · exact hEvalOp m
  | unaryOp_not hOp hNot =>
    rcases hOp.evalOperand_eq_subplace hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    exact hNot m
  | unaryOp_neg hOp hSz =>
    rcases hOp.evalOperand_eq_subplace hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    dsimp only
    rw [hSz]
  | cast_intToInt hOp hSz hTarget =>
    rcases hOp.evalOperand_eq_subplace hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    dsimp only
    rw [hSz, hTarget]
    rfl
  | tuple_nil => exact ⟨rfl, rfl⟩
  | aggregate_tuple hOps =>
    rcases hOps.evalOperands_eq_subplace hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
  | aggregate_adt hOps =>
    rcases hOps.evalOperands_eq_subplace hInv with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue evalAggregateAdt
    dsimp only
    rw [hEval]

theorem LiftDerefWrite.evalStmt_eq_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState}
    (hWrite : LiftDerefWrite localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries s.memory) :
    ∃ (rp : RawPtrVal) (oldVal newVal : Value),
      lookupLensVal? entries rp = .some oldVal ∧
      entries' = updateLensVal entries rp newVal ∧
      env'.length = env.length ∧
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env'
          { s.memory with
            callerLocals :=
              writeSubplaceAt subplaceOf s.memory.callerLocals rp newVal }) := by
  cases hWrite with
  | mk hRv hGetPtr hLookVal =>
    rename_i _ ptrLoc rv rp oldVal newVal
    rcases hRv.evalRvalue_eq_subplace hInv with ⟨hEvalRv, hLen₁⟩
    have hVal := hInv.entries_valid rp oldVal (lookupLensVal?_mem hLookVal)
    unfold BorrowSubplace.entryValid at hVal
    rcases hVal with ⟨hOff, hAbove, hRest⟩
    unfold writeSubplaceAt
    cases hSub : subplaceOf rp with
    | root =>
      rw [hSub] at hRest
      rcases hRest with ⟨hCaller, hExcl⟩
      have hSingle : SepLensStateInv env'.length [(rp, oldVal)] s.memory := {
        callStack_nil := hInv.callStack_nil
        activeCallee_none := hInv.activeCallee_none
        borrows_above_frame := by
          rw [hLen₁]; exact hInv.borrows_above_frame
        entries_valid := fun k w hK => by
          rcases List.mem_singleton.mp hK with ⟨rfl, rfl⟩
          exact ⟨hOff, hLen₁ ▸ hAbove, hCaller, hExcl⟩
        pairwise_disjoint := by simp
      }
      -- Reuse root write logic directly via the evaluated rvalue.
      rcases hExcl.lookup_active with
        ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩
      have hEnv₁None : get? env' entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le (by rw [hLen₁]; exact hAbove)
      have hWriteLocalUb :
          writePlaceValue env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal
            localDecls layouts = .ub := by
        unfold writePlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases localDecls with
        | nil =>
          simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hP]
          rw [hEnv₁None]
        | cons _ _ =>
          simp only [hGetPtr, ProvenancePtr.tag, hLookB, hPerm]
          unfold writeStackThinPtrTypedDeref
          dsimp only
          rw [hEnv₁None]
          split
          · rfl
          · cases newVal <;> rfl
      have hEvalPlaceWriteUb :
          evalPlaceWrite env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal
            s.memory.activeProtectors localDecls layouts = .ub := by
        unfold evalPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteLocalUb
        | cons pHead pTail =>
          dsimp only; rw [hWriteLocalUb]; split <;> rfl
      have hLtCaller : rp.allocId < s.memory.callerLocals.length :=
        (List.getElem?_eq_some_iff.mp hCaller).1
      have hSetCaller :
          set? s.memory.callerLocals rp.allocId (.init newVal) =
            .some (s.memory.callerLocals.set rp.allocId (.init newVal)) := by
        unfold set?; simp [hLtCaller]
      have hWriteCallerOk :
          writeCallerPlaceValue env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal =
            .ok (s.memory.callerLocals.set rp.allocId (.init newVal)) := by
        unfold writeCallerPlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hEnv₁None, hP]
        rw [hT, hCaller, hSetCaller]
      have hEvalCallerOk :
          evalCallerPlaceWrite env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal
            s.memory.activeProtectors =
            .ok (s.memory.callerLocals.set rp.allocId (.init newVal)) := by
        unfold evalCallerPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteCallerOk
        | cons pHead pTail =>
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          cases hB : s.memory.borrows with
          | nil =>
            have hLookNil := hLookB; rw [hB] at hLookNil; nomatch hLookNil
          | cons b₁ tl =>
            cases tl with
            | nil =>
              have hLookSingle := hLookB; rw [hB] at hLookSingle
              dsimp only
              rw [hasProtectedWriteConflict_singleton_eq_false hLookSingle]
              dsimp only; rw [← hB]; exact hWriteCallerOk
            | cons b₂ rest =>
              dsimp only; rw [resolveDerefWriteFullProj_nil_nil hP]
              have hNoConflict :
                  hasProtectedTreeWriteConflict
                    (b₁ :: b₂ :: rest) (b₁ :: b₂ :: rest) (pHead :: pTail)
                    entry.targetLocal (.some rp.tag) []
                    entry.rangeOffset entry.rangeLen = false := by
                rw [hT, ← hB]
                exact hasProtectedTreeWriteConflict_eq_false_of_tree
                  s.memory.borrows s.memory.borrows (pHead :: pTail) _ _ _
                  hExcl.ancestors_active_or_disabled
              rw [hNoConflict]; dsimp only; rw [← hB]
              exact hWriteCallerOk
      have hInvalEq :
          invalidateDerefWriteBorrows env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } []
            s.memory.callerLocals =
            s.memory.borrows := by
        unfold invalidateDerefWriteBorrows
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases hB : s.memory.borrows with
        | nil => rfl
        | cons b₁ tl =>
          cases tl with
          | nil =>
            have hLookSingle := hLookB
            rw [hB] at hLookSingle
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag]
            rw [hLookSingle]
            dsimp only
            rw [resolveDerefWriteFullProj_nil_nil hP, hRL]
            dsimp only
            have hExclSingle :
                ∀ b ∈ [b₁], b.targetLocal = rp.allocId →
                  (b.tag = rp.tag ∧ b.perm = .active ∧
                    b.targetProjection = [] ∧ b.rangeOffset = 0 ∧
                    b.rangeLen = 0) ∨ b.perm = .disabled := by
              intro b hb _
              rcases lookupBorrow_mem_and_tag hLookSingle with ⟨hMemE, hTagE⟩
              rcases List.mem_singleton.mp hb with rfl
              rw [← List.mem_singleton.mp hMemE]
              exact Or.inl ⟨hTagE, hPerm, hP, hRO, hRL⟩
            rw [hT]
            exact invalidateConflictingBorrows_eq_self_of_exclusive hExclSingle
          | cons b₂ rest =>
            have hLookMany := hLookB
            rw [hB] at hLookMany
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag]
            rw [hLookMany]
            dsimp only
            rw [resolveDerefWriteFullProj_nil_nil hP, hT, ← hB]
            exact invalidateTreeBorrowsAtProj_eq_self_of_tree
              s.memory.borrows s.memory.borrows _ _ _
              hExcl.ancestors_active_or_disabled
      refine ⟨rp, oldVal, newVal, hLookVal, rfl, hLen₁, ?_⟩
      unfold evalStmt
      dsimp only
      rw [hEnv, hEvalRv]
      dsimp only
      rw [hEvalPlaceWriteUb]
      dsimp only
      cases hCL : s.memory.callerLocals with
      | nil => rw [hCL] at hCaller; nomatch hCaller
      | cons _ _ =>
        dsimp only; rw [← hCL, hEvalCallerOk, hInvalEq, hSub]
    | field outerIdx outerTy =>
      rw [hSub] at hRest
      rcases hRest with ⟨hField, hExcl⟩
      rcases eq_aggregate_of_readFieldAt_some hField with ⟨elems, hCaller, hEl⟩
      rcases hExcl.lookup_active with
        ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩
      have hEnv₁None : get? env' entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le (by rw [hLen₁]; exact hAbove)
      have hWriteLocalUb :
          writePlaceValue env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal
            localDecls layouts = .ub := by
        unfold writePlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases localDecls with
        | nil =>
          simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hP, hOff, hEnv₁None]
        | cons _ _ =>
          simp only [hGetPtr, ProvenancePtr.tag, hLookB, hPerm]
          unfold writeStackThinPtrTypedDeref
          dsimp only
          rw [hEnv₁None]
          split
          · rfl
          · cases newVal <;> rfl
      have hEvalPlaceWriteUb :
          evalPlaceWrite env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal
            s.memory.activeProtectors localDecls layouts = .ub := by
        unfold evalPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteLocalUb
        | cons pHead pTail =>
          dsimp only; rw [hWriteLocalUb]; split <;> rfl
      have hLtCaller : rp.allocId < s.memory.callerLocals.length :=
        (List.getElem?_eq_some_iff.mp hCaller).1
      have hLtField : outerIdx < elems.length :=
        (List.getElem?_eq_some_iff.mp hEl).1
      have hSetField :
          set? elems outerIdx newVal =
            .some (elems.set outerIdx newVal) := by
        unfold set?; simp [hLtField]
      have hWriteFieldEq :
          writeFieldAt? s.memory.callerLocals rp.allocId outerIdx newVal =
            s.memory.callerLocals.set rp.allocId
              (.init (.aggregate 0 (elems.set outerIdx newVal))) := by
        unfold writeFieldAt?; rw [hCaller]
      have hSetCaller :
          set? s.memory.callerLocals rp.allocId
            (.init (.aggregate 0 (elems.set outerIdx newVal))) =
            .some
              (writeFieldAt? s.memory.callerLocals rp.allocId outerIdx
                newVal) := by
        rw [hWriteFieldEq]; unfold set?; simp [hLtCaller]
      have hWriteCallerOk :
          writeCallerPlaceValue env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal =
            .ok
              (writeFieldAt? s.memory.callerLocals rp.allocId outerIdx
                newVal) := by
        unfold writeCallerPlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hEnv₁None, hP, hOff,
          appendProjections]
        rw [hT, hCaller]
        dsimp only [writeProjectedValue]
        rw [hEl]
        dsimp only [writeProjectedValue]
        rw [hSetField]
        dsimp only
        rw [hSetCaller]
      have hEvalCallerOk :
          evalCallerPlaceWrite env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } newVal
            s.memory.activeProtectors =
            .ok
              (writeFieldAt? s.memory.callerLocals rp.allocId outerIdx
                newVal) := by
        unfold evalCallerPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteCallerOk
        | cons pHead pTail =>
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag, ProvenancePtr.offsetBytes]
          rw [hLookB]
          cases hB : s.memory.borrows with
          | nil =>
            have hLookNil := hLookB; rw [hB] at hLookNil; nomatch hLookNil
          | cons b₁ tl =>
            cases tl with
            | nil =>
              have hLookSingle := hLookB; rw [hB] at hLookSingle
              dsimp only
              rw [hasProtectedWriteConflict_singleton_eq_false hLookSingle]
              dsimp only; rw [← hB]; exact hWriteCallerOk
            | cons b₂ rest =>
              dsimp only
              rw [resolveDerefWriteFullProj_field_nil hP hOff]
              have hNoConflict :
                  hasProtectedTreeWriteConflict
                    (b₁ :: b₂ :: rest) (b₁ :: b₂ :: rest) (pHead :: pTail)
                    entry.targetLocal (.some rp.tag)
                    [.field outerIdx outerTy]
                    entry.rangeOffset entry.rangeLen = false := by
                rw [hRO, hRL, hT, ← hB]
                exact hasProtectedTreeWriteConflict_eq_false_of_treeField_prefix
                  s.memory.borrows s.memory.borrows (pHead :: pTail) []
                  hExcl.ancestors_disjoint_or_disabled
              rw [hNoConflict]; dsimp only; rw [← hB]
              exact hWriteCallerOk
      have hInvalEq :
          invalidateDerefWriteBorrows env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] } []
            s.memory.callerLocals =
            s.memory.borrows := by
        unfold invalidateDerefWriteBorrows
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases hB : s.memory.borrows with
        | nil => rfl
        | cons b₁ tl =>
          cases tl with
          | nil =>
            have hLookSingle := hLookB
            rw [hB] at hLookSingle
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag, ProvenancePtr.offsetBytes]
            rw [hLookSingle]
            dsimp only
            rw [resolveDerefWriteFullProj_field_nil hP hOff, hRO, hRL]
            dsimp only
            have hExclSingle :
                ∀ b ∈ [b₁], b.targetLocal = rp.allocId →
                  (b.tag = rp.tag ∧ b.perm = .active) ∨ b.perm = .disabled := by
              intro b hb _
              rcases lookupBorrow_mem_and_tag hLookSingle with ⟨hMemE, hTagE⟩
              rcases List.mem_singleton.mp hb with rfl
              rw [← List.mem_singleton.mp hMemE]
              exact Or.inl ⟨hTagE, hPerm⟩
            rw [hT]
            exact invalidateConflictingBorrowsAtProj_eq_self_of_exclusive
              _ _ _ hExclSingle
          | cons b₂ rest =>
            have hLookMany := hLookB
            rw [hB] at hLookMany
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag, ProvenancePtr.offsetBytes]
            rw [hLookMany]
            dsimp only
            rw [resolveDerefWriteFullProj_field_nil hP hOff, hRO, hRL, hT, ← hB]
            exact invalidateTreeBorrowsAtProj_eq_self_of_treeField
              s.memory.borrows s.memory.borrows
              hExcl.ancestors_disjoint_or_disabled
      refine ⟨rp, oldVal, newVal, hLookVal, rfl, hLen₁, ?_⟩
      unfold evalStmt
      dsimp only
      rw [hEnv, hEvalRv]
      dsimp only
      rw [hEvalPlaceWriteUb]
      dsimp only
      cases hCL : s.memory.callerLocals with
      | nil => rw [hCL] at hCaller; nomatch hCaller
      | cons _ _ =>
        dsimp only; rw [← hCL, hEvalCallerOk, hInvalEq, hSub]
  | field hRv hGetPtr hLookVal hWriteProj =>
    rename_i _ ptrLoc subIdx subTy rv rp oldAgg fieldVal newAgg
    rcases hRv.evalRvalue_eq_subplace hInv with ⟨hEvalRv, hLen₁⟩
    have hVal := hInv.entries_valid rp oldAgg (lookupLensVal?_mem hLookVal)
    unfold BorrowSubplace.entryValid at hVal
    rcases hVal with ⟨hOff, hAbove, hRest⟩
    unfold writeSubplaceAt
    cases hSub : subplaceOf rp with
    | root =>
      rw [hSub] at hRest
      rcases hRest with ⟨hCaller, hExcl⟩
      rcases hExcl.lookup_active with
        ⟨entry, hLookB, hT, hP, hPerm, _, _⟩
      have hEnv₁None : get? env' entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le (by rw [hLen₁]; exact hAbove)
      have hWriteLocalUb :
          writePlaceValue env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal localDecls layouts = .ub := by
        unfold writePlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases localDecls with
        | nil =>
          simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hP]
          rw [hEnv₁None]
        | cons _ _ =>
          simp only [hGetPtr, ProvenancePtr.tag, hLookB, hPerm]
          unfold writeStackThinPtrTypedDeref
          dsimp only
          rw [hEnv₁None]
          split <;> rfl
      have hEvalPlaceWriteUb :
          evalPlaceWrite env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal s.memory.activeProtectors localDecls layouts = .ub := by
        unfold evalPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteLocalUb
        | cons _ _ => dsimp only; rw [hWriteLocalUb]; split <;> rfl
      have hLtCaller : rp.allocId < s.memory.callerLocals.length :=
        (List.getElem?_eq_some_iff.mp hCaller).1
      have hSetCaller :
          set? s.memory.callerLocals rp.allocId (.init newAgg) =
            .some (s.memory.callerLocals.set rp.allocId (.init newAgg)) := by
        unfold set?; simp [hLtCaller]
      have hWriteCallerOk :
          writeCallerPlaceValue env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal =
            .ok (s.memory.callerLocals.set rp.allocId (.init newAgg)) := by
        unfold writeCallerPlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hEnv₁None, hP]
        rw [hT, hCaller]; dsimp only; rw [hWriteProj]; dsimp only
        rw [hSetCaller]
      have hEvalCallerOk :
          evalCallerPlaceWrite env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal s.memory.activeProtectors =
            .ok (s.memory.callerLocals.set rp.allocId (.init newAgg)) := by
        unfold evalCallerPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteCallerOk
        | cons pHead pTail =>
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag]
          rw [hLookB]
          cases hB : s.memory.borrows with
          | nil =>
            have hLookNil := hLookB; rw [hB] at hLookNil; nomatch hLookNil
          | cons b₁ tl =>
            cases tl with
            | nil =>
              have hLookSingle := hLookB; rw [hB] at hLookSingle
              dsimp only
              rw [hasProtectedWriteConflict_singleton_eq_false hLookSingle]
              dsimp only; rw [← hB]; exact hWriteCallerOk
            | cons b₂ rest =>
              dsimp only; rw [resolveDerefWriteFullProj_nil_field hP]
              have hNoConflict :
                  hasProtectedTreeWriteConflict
                    (b₁ :: b₂ :: rest) (b₁ :: b₂ :: rest) (pHead :: pTail)
                    entry.targetLocal (.some rp.tag)
                    [.field subIdx subTy]
                    entry.rangeOffset entry.rangeLen = false := by
                rw [hT, ← hB]
                exact hasProtectedTreeWriteConflict_eq_false_of_tree
                  s.memory.borrows s.memory.borrows (pHead :: pTail) _ _ _
                  hExcl.ancestors_active_or_disabled
              rw [hNoConflict]; dsimp only; rw [← hB]
              exact hWriteCallerOk
      have hInvalEq :
          invalidateDerefWriteBorrows env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            [.field subIdx subTy]
            s.memory.callerLocals = s.memory.borrows := by
        unfold invalidateDerefWriteBorrows
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases hB : s.memory.borrows with
        | nil => rfl
        | cons b₁ tl =>
          cases tl with
          | nil =>
            have hLookSingle := hLookB
            rw [hB] at hLookSingle
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag]
            rw [hLookSingle]
            dsimp only
            rw [resolveDerefWriteFullProj_nil_field hP]
            dsimp only
            have hExclSingle :
                ∀ b ∈ [b₁], b.targetLocal = rp.allocId →
                  (b.tag = rp.tag ∧ b.perm = .active) ∨ b.perm = .disabled := by
              intro b hb _
              rcases lookupBorrow_mem_and_tag hLookSingle with ⟨hMemE, hTagE⟩
              rcases List.mem_singleton.mp hb with rfl
              rw [← List.mem_singleton.mp hMemE]
              exact Or.inl ⟨hTagE, hPerm⟩
            rw [hT]
            exact invalidateConflictingBorrowsAtProj_eq_self_of_exclusive
              _ _ _ hExclSingle
          | cons b₂ rest =>
            have hLookMany := hLookB
            rw [hB] at hLookMany
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag]
            rw [hLookMany]
            dsimp only
            rw [resolveDerefWriteFullProj_nil_field hP, hT, ← hB]
            exact invalidateTreeBorrowsAtProj_eq_self_of_tree
              s.memory.borrows s.memory.borrows _ _ _
              hExcl.ancestors_active_or_disabled
      refine ⟨rp, oldAgg, newAgg, hLookVal, rfl, hLen₁, ?_⟩
      unfold evalStmt
      dsimp only; rw [hEnv, hEvalRv]; dsimp only; rw [hEvalPlaceWriteUb]
      dsimp only
      cases hCL : s.memory.callerLocals with
      | nil => rw [hCL] at hCaller; nomatch hCaller
      | cons _ _ =>
        dsimp only; rw [← hCL, hEvalCallerOk, hInvalEq, hSub]
    | field outerIdx outerTy =>
      rw [hSub] at hRest
      rcases hRest with ⟨hField, hExcl⟩
      rcases eq_aggregate_of_readFieldAt_some hField with ⟨elems, hCaller, hEl⟩
      rcases hExcl.lookup_active with
        ⟨entry, hLookB, hT, hP, hPerm, hRO, hRL⟩
      have hEnv₁None : get? env' entry.targetLocal = .none := by
        rw [hT]; exact get?_eq_none_of_le (by rw [hLen₁]; exact hAbove)
      have hWriteLocalUb :
          writePlaceValue env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal localDecls layouts = .ub := by
        unfold writePlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases localDecls with
        | nil =>
          simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hP, hOff, hEnv₁None]
        | cons _ _ =>
          simp only [hGetPtr, ProvenancePtr.tag, hLookB, hPerm]
          unfold writeStackThinPtrTypedDeref
          dsimp only
          rw [hEnv₁None]
          split <;> rfl
      have hEvalPlaceWriteUb :
          evalPlaceWrite env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal s.memory.activeProtectors localDecls layouts = .ub := by
        unfold evalPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteLocalUb
        | cons _ _ => dsimp only; rw [hWriteLocalUb]; split <;> rfl
      have hLtCaller : rp.allocId < s.memory.callerLocals.length :=
        (List.getElem?_eq_some_iff.mp hCaller).1
      have hLtField : outerIdx < elems.length :=
        (List.getElem?_eq_some_iff.mp hEl).1
      have hSetField :
          set? elems outerIdx newAgg =
            .some (elems.set outerIdx newAgg) := by
        unfold set?; simp [hLtField]
      have hWriteFieldEq :
          writeFieldAt? s.memory.callerLocals rp.allocId outerIdx newAgg =
            s.memory.callerLocals.set rp.allocId
              (.init (.aggregate 0 (elems.set outerIdx newAgg))) := by
        unfold writeFieldAt?; rw [hCaller]
      have hSetCaller :
          set? s.memory.callerLocals rp.allocId
            (.init (.aggregate 0 (elems.set outerIdx newAgg))) =
            .some
              (writeFieldAt? s.memory.callerLocals rp.allocId outerIdx
                newAgg) := by
        rw [hWriteFieldEq]; unfold set?; simp [hLtCaller]
      have hWriteCallerOk :
          writeCallerPlaceValue env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal =
            .ok
              (writeFieldAt? s.memory.callerLocals rp.allocId outerIdx
                newAgg) := by
        unfold writeCallerPlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hEnv₁None, hP, hOff,
          appendProjections]
        rw [hT, hCaller]
        dsimp only [writeProjectedValue]
        rw [hEl]
        dsimp only [writeProjectedValue]
        rw [hWriteProj]
        dsimp only
        rw [hSetField]
        dsimp only
        rw [hSetCaller]
      have hEvalCallerOk :
          evalCallerPlaceWrite env' s.memory.callerLocals s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            fieldVal s.memory.activeProtectors =
            .ok
              (writeFieldAt? s.memory.callerLocals rp.allocId outerIdx
                newAgg) := by
        unfold evalCallerPlaceWrite
        cases s.memory.activeProtectors with
        | nil => exact hWriteCallerOk
        | cons pHead pTail =>
          simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
            _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
          rw [hGetPtr]
          dsimp only [ProvenancePtr.tag, ProvenancePtr.offsetBytes]
          rw [hLookB]
          cases hB : s.memory.borrows with
          | nil =>
            have hLookNil := hLookB; rw [hB] at hLookNil; nomatch hLookNil
          | cons b₁ tl =>
            cases tl with
            | nil =>
              have hLookSingle := hLookB; rw [hB] at hLookSingle
              dsimp only
              rw [hasProtectedWriteConflict_singleton_eq_false hLookSingle]
              dsimp only; rw [← hB]; exact hWriteCallerOk
            | cons b₂ rest =>
              dsimp only
              rw [resolveDerefWriteFullProj_field_field hP hOff]
              have hNoConflict :
                  hasProtectedTreeWriteConflict
                    (b₁ :: b₂ :: rest) (b₁ :: b₂ :: rest) (pHead :: pTail)
                    entry.targetLocal (.some rp.tag)
                    [.field outerIdx outerTy, .field subIdx subTy]
                    entry.rangeOffset entry.rangeLen = false := by
                rw [hRO, hRL, hT, ← hB]
                exact hasProtectedTreeWriteConflict_eq_false_of_treeField_prefix
                  s.memory.borrows s.memory.borrows (pHead :: pTail)
                  [.field subIdx subTy] hExcl.ancestors_disjoint_or_disabled
              rw [hNoConflict]; dsimp only; rw [← hB]
              exact hWriteCallerOk
      have hInvalEq :
          invalidateDerefWriteBorrows env' s.memory.borrows
            { local_ := ptrLoc, projection := [.deref, .field subIdx subTy] }
            [.field subIdx subTy]
            s.memory.callerLocals = s.memory.borrows := by
        unfold invalidateDerefWriteBorrows
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
          _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        cases hB : s.memory.borrows with
        | nil => rfl
        | cons b₁ tl =>
          cases tl with
          | nil =>
            have hLookSingle := hLookB
            rw [hB] at hLookSingle
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag, ProvenancePtr.offsetBytes]
            rw [hLookSingle]
            dsimp only
            rw [resolveDerefWriteFullProj_field_field hP hOff, hRO, hRL]
            dsimp only
            have hExclSingle :
                ∀ b ∈ [b₁], b.targetLocal = rp.allocId →
                  (b.tag = rp.tag ∧ b.perm = .active) ∨ b.perm = .disabled := by
              intro b hb _
              rcases lookupBorrow_mem_and_tag hLookSingle with ⟨hMemE, hTagE⟩
              rcases List.mem_singleton.mp hb with rfl
              rw [← List.mem_singleton.mp hMemE]
              exact Or.inl ⟨hTagE, hPerm⟩
            rw [hT]
            exact invalidateConflictingBorrowsAtProj_eq_self_of_exclusive
              _ _ _ hExclSingle
          | cons b₂ rest =>
            have hLookMany := hLookB
            rw [hB] at hLookMany
            rw [hGetPtr]
            dsimp only [ProvenancePtr.tag, ProvenancePtr.offsetBytes]
            rw [hLookMany]
            dsimp only
            rw [resolveDerefWriteFullProj_field_field hP hOff, hRO, hRL, hT, ← hB]
            exact invalidateTreeBorrowsAtProj_eq_self_of_treeField_prefix
              s.memory.borrows s.memory.borrows [.field subIdx subTy]
              hExcl.ancestors_disjoint_or_disabled
      refine ⟨rp, oldAgg, newAgg, hLookVal, rfl, hLen₁, ?_⟩
      unfold evalStmt
      dsimp only; rw [hEnv, hEvalRv]; dsimp only; rw [hEvalPlaceWriteUb]
      dsimp only
      cases hCL : s.memory.callerLocals with
      | nil => rw [hCL] at hCaller; nomatch hCaller
      | cons _ _ =>
        dsimp only; rw [← hCL, hEvalCallerOk, hInvalEq, hSub]

/--
Field-granular `I-10` write alias-erasure theorem: under
`SepSubplaceLensStateInv`, when `LiftDerefWrite` updates a field-reborrow
pointer `rp` (`subplaceOf rp = .field fieldIdx fieldTy`), `evalStmt` steps to
`m' = (treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a s.memory`,
preserving `ValidTreeFieldMutBorrowLens`, reading back `a` (`PutGet`), and
leaving every sibling field-reborrow lens view
`(rp₂, codec₂.encode b) ∈ entries` (`rp₂ ≠ rp`) unchanged via
`IndependentLenses` / `SubplaceLensFramePreserved`.
-/
theorem LiftDerefWrite.evalStmt_treeFieldLens_putGet_and_frame
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState}
    (hWrite : LiftDerefWrite localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries s.memory) :
    ∃ (rp : RawPtrVal) (oldVal newVal : Value),
      lookupLensVal? entries rp = .some oldVal ∧
      entries' = updateLensVal entries rp newVal ∧
      ∀ {α : Type} (fieldIdx : FieldIdx) (fieldTy : Ty)
        (codec : ValueCodec α) (a₀ a : α),
        subplaceOf rp = .field fieldIdx fieldTy →
        codec.encode a₀ = oldVal →
        codec.encode a = newVal →
        let m' :=
          (treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a s.memory
        evalStmt s stmt localDecls layouts =
          MirStepNode.step (advanceStmt s env' m') ∧
        ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec m' ∧
        (treeFieldMemoryPtrMutLens rp fieldIdx codec).readView m' = a ∧
        ∀ {β : Type} (rp₂ : RawPtrVal) (fieldIdx₂ : FieldIdx) (fieldTy₂ : Ty)
          (codec₂ : ValueCodec β) (b : β),
          (rp₂, codec₂.encode b) ∈ entries →
          rp₂ ≠ rp →
          subplaceOf rp₂ = .field fieldIdx₂ fieldTy₂ →
          (treeFieldMemoryPtrMutLens rp₂ fieldIdx₂ codec₂).readView m' = b := by
  rcases hWrite.evalStmt_eq_subplace hEnv hInv with
    ⟨rp, oldVal, newVal, hLook, hEntries, _, hEval⟩
  refine ⟨rp, oldVal, newVal, hLook, hEntries,
    fun fieldIdx fieldTy codec a₀ a hSub hEnc₀ hEnc => ?_⟩
  have hMem₁ : (rp, codec.encode a₀) ∈ entries := by
    rw [hEnc₀]; exact lookupLensVal?_mem hLook
  have hVal₁ := hInv.entries_valid rp (codec.encode a₀) hMem₁
  unfold BorrowSubplace.entryValid at hVal₁
  rcases hVal₁ with ⟨_, _, hRest₁⟩
  rw [hSub] at hRest₁
  rcases hRest₁ with ⟨hField₁, hExcl₁⟩
  have hFieldML₁ :
      readFieldAt? (memoryLocals s.memory) rp.allocId fieldIdx =
        .some (codec.encode a₀) := by
    rw [memoryLocals_of_callStack_nil hInv.callStack_nil]; exact hField₁
  have hValid₁ :
      ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec s.memory :=
    ⟨⟨⟨a₀, hFieldML₁⟩⟩, hExcl₁⟩
  have hWbEq :
      (treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a s.memory =
        { s.memory with
          callerLocals :=
            writeSubplaceAt subplaceOf s.memory.callerLocals rp newVal } := by
    rw [treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
      rp fieldIdx fieldTy codec a hExcl₁]
    unfold rawFieldMutLens writeSubplaceAt
    dsimp only
    rw [hSub, updateMemoryLocals_of_callStack_nil hInv.callStack_nil,
      memoryLocals_of_callStack_nil hInv.callStack_nil, hEnc]
  refine ⟨by rw [hWbEq]; exact hEval,
    (treeFieldMemoryPtrMutLens_lawful rp fieldIdx fieldTy codec).valid_writeBack
      a s.memory hValid₁,
    (treeFieldMemoryPtrMutLens_lawful rp fieldIdx fieldTy codec
      ).readView_writeBack a s.memory hValid₁,
    fun rp₂ fieldIdx₂ fieldTy₂ codec₂ b hMem₂ hNe hSub₂ => ?_⟩
  have hVal₂ := hInv.entries_valid rp₂ (codec₂.encode b) hMem₂
  unfold BorrowSubplace.entryValid at hVal₂
  rcases hVal₂ with ⟨_, _, hRest₂⟩
  rw [hSub₂] at hRest₂
  rcases hRest₂ with ⟨hField₂, hExcl₂⟩
  have hDisj :=
    pairwise_subplace_of_mem_ne hInv.pairwise_disjoint hMem₁ hMem₂ hNe
  change
    (treeFieldMemoryPtrMutLens rp₂ fieldIdx₂ codec₂).readView
      ((treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a s.memory) = b
  rw [hWbEq]
  dsimp only [treeFieldMemoryPtrMutLens]
  apply rawFieldMutLens_readView_of_readFieldAt
  rw [memoryLocals_of_callStack_nil
    (m := { s.memory with
      callerLocals :=
        writeSubplaceAt subplaceOf s.memory.callerLocals rp newVal })
    hInv.callStack_nil]
  dsimp only [writeSubplaceAt]
  rw [hSub, ← hEnc]
  rcases hDisj.2 with hNeAlloc | ⟨f₂, _, f₁, _, hS₂, hS₁, hNeF⟩
  · unfold readFieldAt?
    rw [get?_writeFieldAt_ne_alloc _ _ _ hNeAlloc]
    exact hField₂
  · rw [hSub₂] at hS₂; injection hS₂ with hF₂ _
    rw [hSub] at hS₁; injection hS₁ with hF₁ _
    subst hF₂ hF₁
    by_cases hSameAlloc : rp₂.allocId = rp.allocId
    · rw [hSameAlloc, readFieldAt_writeFieldAt_ne_eq _ _ _ hNeF.symm]
      rw [← hSameAlloc]
      exact hField₂
    · unfold readFieldAt?
      rw [get?_writeFieldAt_ne_alloc _ _ _ hSameAlloc]
      exact hField₂

theorem LiftLensStmt.evalStmt_step_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries₀ entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState} {m₀ : Memory}
    (hStmt : LiftLensStmt localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries s.memory)
    (hFrame : SubplaceLensFramePreserved subplaceOf entries₀ m₀ s.memory)
    (hKeys : entries.map Prod.fst = entries₀.map Prod.fst) :
    ∃ m' : Memory,
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env' m') ∧
      env'.length = env.length ∧
      SepSubplaceLensStateInv subplaceOf env'.length entries' m' ∧
      SubplaceLensFramePreserved subplaceOf entries₀ m₀ m' ∧
      entries'.map Prod.fst = entries₀.map Prod.fst := by
  cases hStmt with
  | retag hRetag =>
    cases hRetag with
    | mk hGetPtr hLookVal =>
      rename_i _ retagKind ptrLoc rp v
      have hMem := lookupLensVal?_mem hLookVal
      have hVal := hInv.entries_valid rp v hMem
      unfold BorrowSubplace.entryValid at hVal
      rcases hVal with ⟨_, _, hRest⟩
      have hLookPerm :
          ∃ entry,
            lookupBorrow s.memory.borrows rp.tag = .some entry ∧
            entry.perm = .active := by
        cases hSub : subplaceOf rp with
        | root =>
          rw [hSub] at hRest
          rcases hRest.2.lookup_active with ⟨e, hL, _, _, hPm, _, _⟩
          exact ⟨e, hL, hPm⟩
        | field _ _ =>
          rw [hSub] at hRest
          rcases hRest.2.lookup_active with ⟨e, hL, _, _, hPm, _, _⟩
          exact ⟨e, hL, hPm⟩
      rcases hLookPerm with ⟨entry, hLookB, hPerm⟩
      unfold evalStmt
      simp [hEnv, evalOperand, readProjectedValue, hGetPtr,
        _root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue,
        _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr, ProvenancePtr.tag]
      rw [hLookB]
      dsimp only
      rw [hPerm]
      dsimp only
      cases retagKind <;>
        (try exact ⟨s.memory, rfl, hInv, hFrame, hKeys⟩)
      · refine ⟨{
          s.memory with
          borrows :=
            attachBorrowProtector s.memory.borrows rp.tag s.memory.nextProtector
          activeProtectors :=
            s.memory.nextProtector :: s.memory.activeProtectors
          nextProtector := Nat.add s.memory.nextProtector 1
        }, rfl, hInv.attachProtector rp.tag s.memory.nextProtector, ?_, hKeys⟩
        refine ⟨hFrame.locals_unchanged_outside,
          hFrame.fields_unchanged_outside, fun q hOut => ?_⟩
        have hRpInFst : rp ∈ entries.map Prod.fst :=
          List.mem_map.mpr ⟨(rp, v), hMem, rfl⟩
        rw [hKeys] at hRpInFst
        rcases List.mem_map.mp hRpInFst with ⟨⟨k₀, v₀⟩, hMem₀, hK₀⟩
        dsimp only at hK₀
        subst k₀
        have hTagNe : rp.tag ≠ q := fun hEq => hOut (rp, v₀) hMem₀ hEq.symm
        rw [lookupBorrow_attachBorrowProtector_ne _ _ _ _ hTagNe]
        exact hFrame.borrows_unchanged_outside q hOut
  | derefWrite hWrite =>
    rcases hWrite.evalStmt_eq_subplace hEnv hInv with
      ⟨rp, oldVal, newVal, hLookVal, rfl, hLen₁, hEvalStmt⟩
    have hMem := lookupLensVal?_mem hLookVal
    have hRpInFst : rp ∈ entries.map Prod.fst :=
      List.mem_map.mpr ⟨(rp, oldVal), hMem, rfl⟩
    rw [hKeys] at hRpInFst
    rcases List.mem_map.mp hRpInFst with ⟨⟨k₀, v₀⟩, hMem₀, hK₀⟩
    dsimp only at hK₀
    subst k₀
    refine ⟨
      { s.memory with
        callerLocals :=
          writeSubplaceAt subplaceOf s.memory.callerLocals rp newVal },
      hEvalStmt, hLen₁,
      (by rw [hLen₁]; exact hInv.updateSubplace hLookVal),
      ?_,
      (updateLensVal_map_fst entries rp newVal).trans hKeys⟩
    refine ⟨fun allocId hOut => ?_, fun allocId fieldIdx hOutF => ?_,
      hFrame.borrows_unchanged_outside⟩
    · have hAllocNe : allocId ≠ rp.allocId := hOut (rp, v₀) hMem₀
      unfold writeSubplaceAt
      cases subplaceOf rp with
      | root =>
        unfold get?
        rw [List.getElem?_set_ne hAllocNe.symm]
        exact hFrame.locals_unchanged_outside allocId hOut
      | field fRp _ =>
        rw [get?_writeFieldAt_ne_alloc _ _ _ hAllocNe]
        exact hFrame.locals_unchanged_outside allocId hOut
    · unfold writeSubplaceAt
      by_cases hEqAlloc : rp.allocId = allocId
      · rcases hOutF (rp, v₀) hMem₀ hEqAlloc with ⟨f, ty, hSubRp, hNeF⟩
        rw [hSubRp, hEqAlloc, readFieldAt_writeFieldAt_ne_eq _ _ _ hNeF]
        exact hFrame.fields_unchanged_outside allocId fieldIdx hOutF
      · have hNeAlloc : allocId ≠ rp.allocId := fun h => hEqAlloc h.symm
        cases subplaceOf rp with
        | root =>
          unfold readFieldAt?
          unfold get?
          rw [List.getElem?_set_ne hNeAlloc.symm]
          exact hFrame.fields_unchanged_outside allocId fieldIdx hOutF
        | field fRp _ =>
          unfold readFieldAt?
          rw [get?_writeFieldAt_ne_alloc _ _ _ hNeAlloc]
          exact hFrame.fields_unchanged_outside allocId fieldIdx hOutF
  | pureAssign hPure =>
    cases hPure with
    | mk hRv hGetDst hNotDead hSetDst =>
      rename_i _ env1_ dstLoc_ rv val oldSlot
      rcases hRv.evalRvalue_eq_subplace hInv with ⟨hEvalRv, hLen₁⟩
      have hLen₂ : env'.length = env1_.length := set?_length_eq hSetDst
      have hLtFrame : dstLoc_ < env.length := by
        rw [← hLen₁]
        exact (List.getElem?_eq_some_iff.mp hGetDst).1
      have hInval :
          invalidateConflictingBorrows s.memory.borrows dstLoc_ .none =
            s.memory.borrows :=
        invalidateConflictingBorrows_eq_self_of_lt_frame
          hInv.borrows_above_frame hLtFrame
      refine ⟨s.memory, ?_, hLen₂.trans hLen₁,
        (by rw [hLen₂, hLen₁]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      dsimp only; rw [hEnv, hEvalRv]; dsimp only; rw [hGetDst]
      cases oldSlot with
      | dead => exact absurd rfl hNotDead
      | uninit =>
        dsimp only; rw [hSetDst]; dsimp only
        cases hAP : s.memory.activeProtectors with
        | nil => simp [hInval, ← hAP]
        | cons pHead pTail =>
          dsimp only
          rw [hasProtectedWriteConflict_eq_false_of_lt_frame
            (pHead :: pTail) hInv.borrows_above_frame hLtFrame]
          simp [hInval, ← hAP]
      | init _ =>
        dsimp only; rw [hSetDst]; dsimp only
        cases hAP : s.memory.activeProtectors with
        | nil => simp [hInval, ← hAP]
        | cons pHead pTail =>
          dsimp only
          rw [hasProtectedWriteConflict_eq_false_of_lt_frame
            (pHead :: pTail) hInv.borrows_above_frame hLtFrame]
          simp [hInval, ← hAP]
  | storageLive hLive =>
    cases hLive with
    | mk hGet hSet =>
      have hLen : env'.length = env.length := set?_length_eq hSet
      have hNe := targetLocal_ne_of_lt_frame hInv.borrows_above_frame hGet
      have hDisable := disableLocalBorrows_eq_self_of_forall_ne _ _ hNe
      have hProt := fun ap => hasProtectedLocalBorrow_eq_false_of_forall_ne _ ap _ hNe
      refine ⟨s.memory, ?_, hLen, (by rw [hLen]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      cases hAP : s.memory.activeProtectors with
      | nil => simp [hEnv, hGet, hSet, hDisable]
      | cons pHead pTail => simp [hEnv, hGet, hSet, hDisable, hProt, ← hAP]
  | storageDead hDead =>
    cases hDead with
    | mk hGet hSet =>
      have hLen : env'.length = env.length := set?_length_eq hSet
      have hNe := targetLocal_ne_of_lt_frame hInv.borrows_above_frame hGet
      have hDisable := disableLocalBorrows_eq_self_of_forall_ne _ _ hNe
      have hProt := fun ap => hasProtectedLocalBorrow_eq_false_of_forall_ne _ ap _ hNe
      refine ⟨s.memory, ?_, hLen, (by rw [hLen]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      cases hAP : s.memory.activeProtectors with
      | nil => simp [hEnv, hGet, hSet, hDisable]
      | cons pHead pTail => simp [hEnv, hGet, hSet, hDisable, hProt, ← hAP]
  | nop hNop =>
    cases hNop with
    | mk =>
      refine ⟨s.memory, ?_, rfl, hInv, hFrame, hKeys⟩
      unfold evalStmt; simp [hEnv]

theorem mirWpConverges_of_liftLensStmts_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    {stmts : List Statement}
    {env env' : PureEnv}
    {entries₀ entries entries' : List (RawPtrVal × Value)}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hStmts :
      LiftLensStmts body.localDecls body.layouts
        env entries stmts env' entries') :
    ∀ (prefixStmts : List Statement) (m₀ m : Memory)
      (Φ : MirOutcome → Prop),
      bb.statements = prefixStmts ++ stmts →
      SepSubplaceLensStateInv subplaceOf env.length entries m →
      SubplaceLensFramePreserved subplaceOf entries₀ m₀ m →
      entries.map Prod.fst = entries₀.map Prod.fst →
      (∀ m' : Memory,
        SepSubplaceLensStateInv subplaceOf env'.length entries' m' →
        SubplaceLensFramePreserved subplaceOf entries₀ m₀ m' →
        entries'.map Prod.fst = entries₀.map Prod.fst →
        MirWpConverges body
          { frame := {
              blockIdx := bbIdx
              stmtIdx := bb.statements.length
              locals := env'
            }
            memory := m' }
          Φ) →
      MirWpConverges body
        { frame := {
            blockIdx := bbIdx
            stmtIdx := prefixStmts.length
            locals := env
          }
          memory := m }
        Φ := by
  induction hStmts with
  | @nil env entries =>
    intro prefixStmts m₀ m Φ hBbStmts hInv hFrame hKeys hCont
    have hStmtLen : bb.statements.length = prefixStmts.length := by
      rw [hBbStmts, List.append_nil]
    rw [← hStmtLen]
    exact hCont m hInv hFrame hKeys
  | cons hFirst hRest ih =>
    rename_i env_ env1_ env2_ entries_ entries1_ entries2_ stmt rest
    intro prefixStmts m₀ m Φ hBbStmts hInv hFrame hKeys hCont
    let s : MachineState := {
      frame := {
        blockIdx := bbIdx
        stmtIdx := prefixStmts.length
        locals := env_
      }
      memory := m
    }
    rcases hFirst.evalStmt_step_subplace (s := s) rfl hInv hFrame hKeys with
      ⟨m₁, hStepStmt, _, hInv₁, hFrame₁, hKeys₁⟩
    apply MirWpConverges.step_tau (s' := advanceStmt s env1_ m₁)
    · rw [stepMirFn_of_isRuntimeMirPhase body bbIdx prefixStmts.length env_ m
        hInv.activeCallee_none hPhase hBb]
      have hGetStmt : get? bb.statements prefixStmts.length = .some stmt := by
        rw [hBbStmts]
        unfold get?
        rw [List.getElem?_append_right (Nat.le_refl _)]
        simp
      simp only [hGetStmt]
      exact hStepStmt
    · have hAppend :
          bb.statements = (prefixStmts ++ [stmt]) ++ rest := by
        rw [List.append_assoc, List.singleton_append]
        exact hBbStmts
      have hPrefixLen :
          (prefixStmts ++ [stmt]).length = Nat.add prefixStmts.length 1 := by
        simp
      unfold advanceStmt
      dsimp only [s]
      rw [← hPrefixLen]
      exact ih (prefixStmts ++ [stmt]) m₀ m₁ Φ hAppend hInv₁ hFrame₁ hKeys₁
        hCont

theorem mirWpConverges_of_liftLensBlock_subplace
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {env : PureEnv}
    {entries entries' : List (RawPtrVal × Value)} {retVal : Value}
    (hBlock : LiftLensBlock body bbIdx env entries retVal entries') :
    ∀ (entries₀ : List (RawPtrVal × Value)) (m₀ m : Memory)
      (Φ : MirOutcome → Prop),
      SepSubplaceLensStateInv subplaceOf env.length entries m →
      SubplaceLensFramePreserved subplaceOf entries₀ m₀ m →
      entries.map Prod.fst = entries₀.map Prod.fst →
      (∀ m_final : Memory,
        SepSubplaceLensStateInv subplaceOf env.length entries' m_final →
        SubplaceLensFramePreserved subplaceOf entries₀ m₀ m_final →
        Φ (.normal (retVal, m_final))) →
      MirWpConverges body
        { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := env }
          memory := m }
        Φ := by
  induction hBlock with
  | return_ hPhase hBb hTerm hStmts hRet =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen := hStmts.length_eq
    exact mirWpConverges_of_liftLensStmts_subplace hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' _ =>
        mirWpConverges_return_of_lens hPhase hBb hTerm hRet
          hInv'.callStack_nil hInv'.activeCallee_none
          (hPost m' (by rw [← hLen]; exact hInv') hFrame'))
  | goto hPhase hBb hTerm hStmts _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen := hStmts.length_eq
    exact mirWpConverges_of_liftLensStmts_subplace hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' =>
        mirWpConverges_goto_of_lens hPhase hBb hTerm hInv'.activeCallee_none
          (ih entries₀ m₀ m' Φ hInv' hFrame' hKeys'
            (fun m_final hInvF hFrameF =>
              hPost m_final (by rw [← hLen]; exact hInvF) hFrameF)))
  | assert hPhase hBb hTerm hStmts hCond hBit _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen₁ := hStmts.length_eq
    have hLen₂ := hCond.length_eq
    exact mirWpConverges_of_liftLensStmts_subplace hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' => by
        rcases hCond.evalOperand_eq_subplace hInv' with ⟨hEval, _⟩
        exact mirWpConverges_assert_of_lens hPhase hBb hTerm
          hInv'.activeCallee_none hEval hBit
          (ih entries₀ m₀ m' Φ (by rw [hLen₂]; exact hInv') hFrame' hKeys'
            (fun m_final hInvF hFrameF =>
              hPost m_final (by rw [← hLen₁, ← hLen₂]; exact hInvF) hFrameF)))
  | switchInt hPhase hBb hTerm hStmts hDiscr hTarget _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen₁ := hStmts.length_eq
    have hLen₂ := hDiscr.length_eq
    exact mirWpConverges_of_liftLensStmts_subplace hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' => by
        rcases hDiscr.evalOperand_eq_subplace hInv' with
          ⟨hEval, _⟩
        exact mirWpConverges_switchInt_of_lens hPhase hBb hTerm
          hInv'.activeCallee_none hEval hTarget
          (ih entries₀ m₀ m' Φ (by rw [hLen₂]; exact hInv') hFrame' hKeys'
            (fun m_final hInvF hFrameF =>
              hPost m_final (by rw [← hLen₁, ← hLen₂]; exact hInvF) hFrameF)))
  | drop_local hPhase hBb hTerm hStmts hGet hNotDead hSet _ ih =>
    intro entries₀ m₀ m Φ hInv hFrame hKeys hPost
    have hLen₁ := hStmts.length_eq
    have hLen₂ := set?_length_eq hSet
    exact mirWpConverges_of_liftLensStmts_subplace hPhase hBb hStmts [] m₀ m Φ
      (List.nil_append _).symm hInv hFrame hKeys
      (fun m' hInv' hFrame' hKeys' =>
        mirWpConverges_drop_of_lens hPhase hBb hTerm hInv'.activeCallee_none
          hGet hNotDead hSet
          (ih entries₀ m₀ m' Φ (by rw [hLen₂]; exact hInv') hFrame' hKeys'
            (fun m_final hInvF hFrameF =>
              hPost m_final (by rw [← hLen₁, ← hLen₂]; exact hInvF) hFrameF)))

/--
Whole-CFG fuel-free `MirWpConverges` soundness over sub-place mutable borrows
(`mirWpConverges_of_sepSubplaceLenses`): executes any `LiftLensBlock` body over
a mix of root caller-slot borrows and sibling field-granular reborrows on shared
aggregate allocations without inspecting `Memory` fields.
-/
theorem mirWpConverges_of_sepSubplaceLenses
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {entries₀ entries' : List (RawPtrVal × Value)}
    {retVal : Value} {m₀ : Memory} {Φ : MirOutcome → Prop}
    (hBlock : LiftLensBlock body bbIdx env entries₀ retVal entries')
    (hInv₀ : SepSubplaceLensStateInv subplaceOf env.length entries₀ m₀)
    (hPost :
      ∀ m_final : Memory,
        SepSubplaceLensStateInv subplaceOf env.length entries' m_final →
        SubplaceLensFramePreserved subplaceOf entries₀ m₀ m_final →
        Φ (.normal (retVal, m_final))) :
    MirWpConverges body
      { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := env }
        memory := m₀ }
      Φ :=
  mirWpConverges_of_liftLensBlock_subplace hBlock entries₀ m₀ m₀ Φ hInv₀
    (SubplaceLensFramePreserved.refl subplaceOf entries₀ m₀) rfl hPost

theorem verifyStatefulMir_of_sepSubplaceLenses
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (subplaceOf : RawPtrVal → BorrowSubplace)
          (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepSubplaceLensStateInv subplaceOf env₀.length entries₀ m₀ ∧
          ∀ m_final : Memory,
            SepSubplaceLensStateInv subplaceOf env₀.length entries' m_final →
            SubplaceLensFramePreserved subplaceOf entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    StatefulVerificationResult { body := body, pre := Pre, post := Post } := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  intro args m₀ hPre
  rcases hStep args m₀ hPre with
    ⟨subplaceOf, entries₀, entries', retVal, hBlock, hInv₀, hPost⟩
  exact mirWpConverges_of_sepSubplaceLenses hBlock hInv₀ hPost

theorem verifyTotalMir_of_sepSubplaceLenses
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (subplaceOf : RawPtrVal → BorrowSubplace)
          (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepSubplaceLensStateInv subplaceOf env₀.length entries₀ m₀ ∧
          ∀ m_final : Memory,
            SepSubplaceLensStateInv subplaceOf env₀.length entries' m_final →
            SubplaceLensFramePreserved subplaceOf entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    TotalVerificationResult { body := body, pre := Pre, post := Post } := by
  refine verifyTotalMir_of_wpConverges _ ?_
  intro args m₀ hPre
  rcases hStep args m₀ hPre with
    ⟨subplaceOf, entries₀, entries', retVal, hBlock, hInv₀, hPost⟩
  exact mirWpConverges_of_sepSubplaceLenses hBlock hInv₀ hPost

/--
Well-formedness of a single field-granular mutable borrow `rp` (`&mut s.f`) at
function entry with callee frame length `frameLen`.
-/
structure WfSingleFieldMutBorrow
    (frameLen : Nat) (rp : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (m : Memory) : Prop where
  callStack_nil : m.callStack = []
  activeCallee_none : m.activeCallee = .none
  borrows_above_frame : ∀ b ∈ m.borrows, frameLen ≤ b.targetLocal
  alloc_above_frame : frameLen ≤ rp.allocId
  exclusive : TreeFieldExclusiveBorrow rp fieldIdx fieldTy m

/-- Canonical `subplaceOf` map for a single field-granular borrow `rp`. -/
def singleFieldSubplace
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty) :
    RawPtrVal → BorrowSubplace :=
  fun k => if k = rp then .field fieldIdx fieldTy else .root

/-- Canonical `subplaceOf` map for a pair of field-granular borrows. -/
def pairFieldSubplace
    (rp₁ rp₂ : RawPtrVal) (fieldIdx₁ fieldIdx₂ : FieldIdx)
    (fieldTy₁ fieldTy₂ : Ty) : RawPtrVal → BorrowSubplace :=
  fun k =>
    if k = rp₁ then .field fieldIdx₁ fieldTy₁
    else if k = rp₂ then .field fieldIdx₂ fieldTy₂
    else .root

/--
1-Field Entry Bridge: `sepConj (ActiveTypedFieldMutBorrow rp fieldIdx codec a)
R_frame` together with `WfSingleFieldMutBorrow` establishes
`SepSubplaceLensStateInv` for `[(rp, codec.encode a)]`.
-/
theorem sepSubplaceLensStateInv_of_sepConj_one_field {α : Type}
    {frameLen : Nat} {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {a : α} {R_frame : SepProp} {m₀ : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp fieldIdx codec a) R_frame) m₀)
    (hWf : WfSingleFieldMutBorrow frameLen rp fieldIdx fieldTy m₀) :
    SepSubplaceLensStateInv (singleFieldSubplace rp fieldIdx fieldTy)
      frameLen [(rp, codec.encode a)] m₀ := by
  rcases hSep with ⟨fp, h₁, _, ⟨hs₁, _, _, _, _⟩, hA₁, _⟩
  dsimp only at hs₁
  rcases activeTypedFieldMutBorrow_facts hA₁ with ⟨hFld₁, _, _, _⟩
  have hFldCaller :
      readFieldAt? m₀.callerLocals rp.allocId fieldIdx =
        some (codec.encode a) := by
    rw [← memoryLocals_of_callStack_nil hWf.callStack_nil]
    exact hs₁ ▸ hFld₁
  refine {
    callStack_nil := hWf.callStack_nil
    activeCallee_none := hWf.activeCallee_none
    borrows_above_frame := hWf.borrows_above_frame
    entries_valid := fun k v hMem => by
      rcases List.mem_singleton.mp hMem with ⟨rfl, rfl⟩
      unfold BorrowSubplace.entryValid singleFieldSubplace
      simp only [ite_true]
      exact ⟨hWf.exclusive.offset_zero, hWf.alloc_above_frame,
        hFldCaller, hWf.exclusive⟩
    pairwise_disjoint := by simp
  }

/--
1-Field Exit Bridge: preserves `sepConj (ActiveTypedFieldMutBorrow rp fieldIdx
codec a_new) R_frame` across `SubplaceLensFramePreserved`. When `fieldIdx = 0`
(e.g., `&mut s.0`), `Or.inl rfl` discharges `hRootFree` unconditionally for
every `LocalSepProp R_frame` (including active parent `BorrowToken` and active
sibling `ActiveTypedFieldMutBorrow` assertions on the same struct allocation).
-/
theorem sepConj_activeTypedFieldMutBorrow_preserved_one {α : Type}
    {frameLen : Nat} {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {a_old a_new : α}
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp fieldIdx codec a_old) R_frame)
        m₀)
    (hInv_final :
      SepSubplaceLensStateInv (singleFieldSubplace rp fieldIdx fieldTy)
        frameLen [(rp, codec.encode a_new)] m_final)
    (hWf : WfSingleFieldMutBorrow frameLen rp fieldIdx fieldTy m₀)
    (hPres :
      SubplaceLensFramePreserved (singleFieldSubplace rp fieldIdx fieldTy)
        [(rp, codec.encode a_old)] m₀ m_final)
    (h_R : LocalSepProp R_frame)
    (hRootFree :
      fieldIdx = 0 ∨
        ∀ h : PartialHeap, R_frame h →
          (rp.allocId, 0) ∉ h.footprint.addrs) :
    SepProp.holdsIn
      (sepConj (ActiveTypedFieldMutBorrow rp fieldIdx codec a_new) R_frame)
      m_final := by
  rcases hSep with ⟨fp, h₁, hR₀, ⟨_, hsR, hDisj, _, _⟩, hA₁, hR_holds₀⟩
  dsimp only at hsR
  rcases activeTypedFieldMutBorrow_facts hA₁ with ⟨_, _, hCell₁, hTag₁⟩
  have hValF := hInv_final.entries_valid rp (codec.encode a_new)
    (List.Mem.head [])
  unfold BorrowSubplace.entryValid singleFieldSubplace at hValF
  simp only [ite_true] at hValF
  rcases hValF with ⟨_, _, hFldF, hExclF⟩
  have hAgree : AgreeOnFootprint hR₀.footprint m₀ m_final := by
    refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
    · rw [memoryLocals_of_callStack_nil hWf.callStack_nil,
        memoryLocals_of_callStack_nil hInv_final.callStack_nil]
      by_cases hEqAlloc : allocId = rp.allocId
      · subst hEqAlloc
        have hOffNeZero : offset ≠ 0 := by
          intro hZ
          subst hZ
          rcases hRootFree with hFZ | hNoRoot
          · subst hFZ
            exact hDisj.1 (rp.allocId, 0) hCell₁ hIn
          · exact hNoRoot hR₀ hR_holds₀ hIn
        have hOffNeFld : offset ≠ fieldIdx := by
          intro hEqF
          subst hEqF
          exact hDisj.1 (rp.allocId, offset) hCell₁ hIn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hOffNeZero
        rw [readAllocAt_succ_eq_readFieldAt, readAllocAt_succ_eq_readFieldAt]
        refine (hPres.fields_unchanged_outside rp.allocId (k + 1) ?_).symm
        intro e he _
        rw [List.mem_singleton.mp he]
        exact ⟨fieldIdx, fieldTy, by simp [singleFieldSubplace],
          hOffNeFld.symm⟩
      · unfold readAllocAt?
        refine (hPres.locals_unchanged_outside allocId ?_) ▸ rfl
        intro e he
        rw [List.mem_singleton.mp he]
        exact hEqAlloc
    · refine (hPres.borrows_unchanged_outside tag ?_).symm
      intro e he hEqT
      rw [List.mem_singleton.mp he] at hEqT
      subst hEqT
      exact hDisj.2 rp.tag hTag₁ hIn
  have hR_m₀ : R_frame ⟨m₀, hR₀.footprint⟩ := by
    have hEqH : hR₀ = ⟨m₀, hR₀.footprint⟩ := by
      cases hR₀; dsimp only at hsR ⊢; subst hsR; rfl
    exact hEqH ▸ hR_holds₀
  have hR_final : R_frame ⟨m_final, hR₀.footprint⟩ :=
    h_R hR₀.footprint m₀ m_final hAgree hR_m₀
  have hFldML :
      readFieldAt? (memoryLocals m_final) rp.allocId fieldIdx =
        some (codec.encode a_new) := by
    rw [memoryLocals_of_callStack_nil hInv_final.callStack_nil]
    exact hFldF
  rcases hExclF.lookup_active with ⟨entryF, hLookF, hTF, _, hPermF, _, _⟩
  have hA₁_final :
      ActiveTypedFieldMutBorrow rp fieldIdx codec a_new
        ⟨m_final, fieldMutBorrowFootprint rp fieldIdx⟩ :=
    activeTypedFieldMutBorrow_intro hFldML ⟨entryF, hLookF, hTF, hPermF⟩
  let fpTotal : Footprint := {
    addrs := (rp.allocId, fieldIdx) :: hR₀.footprint.addrs
    tags := rp.tag :: hR₀.footprint.tags
  }
  refine ⟨fpTotal,
    ⟨m_final, fieldMutBorrowFootprint rp fieldIdx⟩,
    ⟨m_final, hR₀.footprint⟩,
    ⟨rfl, rfl, ⟨?_, ?_⟩, ?_, ?_⟩,
    hA₁_final, hR_final⟩
  · intro cell hIn₁ hInR
    rw [List.mem_singleton.mp hIn₁] at hInR
    exact hDisj.1 (rp.allocId, fieldIdx) hCell₁ hInR
  · intro t hIn₁ hInR
    rw [List.mem_singleton.mp hIn₁] at hInR
    exact hDisj.2 rp.tag hTag₁ hInR
  · intro addr; simp [fpTotal, fieldMutBorrowFootprint]
  · intro tag; simp [fpTotal, fieldMutBorrowFootprint]

/--
2-Field Entry Bridge: `sepConj (ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁
a₁) (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ a₂) R_frame)`
derives both `rp₁.tag ≠ rp₂.tag` and sub-place disjointness (either distinct
allocations OR `fieldIdx₁ ≠ fieldIdx₂` on a shared aggregate allocation) and
establishes `SepSubplaceLensStateInv`.
-/
theorem sepSubplaceLensStateInv_of_sepConj_two_fields {α β : Type}
    {frameLen : Nat} {rp₁ rp₂ : RawPtrVal}
    {fieldIdx₁ fieldIdx₂ : FieldIdx} {fieldTy₁ fieldTy₂ : Ty}
    {codec₁ : ValueCodec α} {codec₂ : ValueCodec β}
    {a₁ : α} {a₂ : β} {R_frame : SepProp} {m₀ : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a₁)
          (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ a₂)
            R_frame))
        m₀)
    (hWf₁ : WfSingleFieldMutBorrow frameLen rp₁ fieldIdx₁ fieldTy₁ m₀)
    (hWf₂ : WfSingleFieldMutBorrow frameLen rp₂ fieldIdx₂ fieldTy₂ m₀) :
    SepSubplaceLensStateInv
      (pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂)
      frameLen [(rp₁, codec₁.encode a₁), (rp₂, codec₂.encode a₂)] m₀ := by
  rcases hSep with ⟨fp, h₁, h₂₃, ⟨hs₁, hs₂₃, hDisj, _, _⟩, hA₁,
    h₂, _, ⟨hs₂, _, _, hAddrs₂₃, hTags₂₃⟩, hA₂, _⟩
  dsimp only at hs₁ hs₂₃ hs₂
  rcases activeTypedFieldMutBorrow_facts hA₁ with
    ⟨hFld₁, _, hCell₁, hTag₁⟩
  rcases activeTypedFieldMutBorrow_facts hA₂ with
    ⟨hFld₂, _, hCell₂, hTag₂⟩
  have hNeTag : rp₁.tag ≠ rp₂.tag := by
    intro hEq
    apply hDisj.2 rp₁.tag hTag₁
    apply (hTags₂₃ _).mpr; left; rw [hEq]; exact hTag₂
  have hNePtr : rp₁ ≠ rp₂ := fun hEq => hNeTag (congrArg RawPtrVal.tag hEq)
  have hSub₁ :
      pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ rp₁ =
        .field fieldIdx₁ fieldTy₁ := by
    simp [pairFieldSubplace]
  have hSub₂ :
      pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ rp₂ =
        .field fieldIdx₂ fieldTy₂ := by
    simp [pairFieldSubplace, hNePtr.symm]
  have hDisjSub :
      BorrowSubplace.disjointOn
        (pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂)
        rp₁ rp₂ := by
    refine ⟨hNeTag, ?_⟩
    by_cases hEqAlloc : rp₁.allocId = rp₂.allocId
    · right
      refine ⟨fieldIdx₁, fieldTy₁, fieldIdx₂, fieldTy₂, hSub₁, hSub₂, ?_⟩
      intro hEqF
      apply hDisj.1 (rp₁.allocId, fieldIdx₁) hCell₁
      apply (hAddrs₂₃ _).mpr; left
      rw [hEqAlloc, hEqF]; exact hCell₂
    · exact Or.inl hEqAlloc
  have hFldCaller₁ :
      readFieldAt? m₀.callerLocals rp₁.allocId fieldIdx₁ =
        some (codec₁.encode a₁) := by
    rw [← memoryLocals_of_callStack_nil hWf₁.callStack_nil]
    exact hs₁ ▸ hFld₁
  have hFldCaller₂ :
      readFieldAt? m₀.callerLocals rp₂.allocId fieldIdx₂ =
        some (codec₂.encode a₂) := by
    rw [← memoryLocals_of_callStack_nil hWf₁.callStack_nil]
    exact (hs₂.trans hs₂₃) ▸ hFld₂
  refine {
    callStack_nil := hWf₁.callStack_nil
    activeCallee_none := hWf₁.activeCallee_none
    borrows_above_frame := hWf₁.borrows_above_frame
    entries_valid := fun k v hMem => by
      rcases List.mem_cons.mp hMem with hHd | hTl
      · injection hHd with hK hV; subst hK hV
        unfold BorrowSubplace.entryValid; rw [hSub₁]
        exact ⟨hWf₁.exclusive.offset_zero, hWf₁.alloc_above_frame,
          hFldCaller₁, hWf₁.exclusive⟩
      · rcases List.mem_singleton.mp hTl with ⟨rfl, rfl⟩
        unfold BorrowSubplace.entryValid; rw [hSub₂]
        exact ⟨hWf₂.exclusive.offset_zero, hWf₂.alloc_above_frame,
          hFldCaller₂, hWf₂.exclusive⟩
    pairwise_disjoint := by
      dsimp only [List.map]
      refine List.pairwise_cons.mpr
        ⟨fun k hk => by rw [List.mem_singleton.mp hk]; exact hDisjSub,
          List.pairwise_singleton _ _⟩
  }

/--
2-Field Exit Bridge: preserves `sepConj (ActiveTypedFieldMutBorrow rp₁
fieldIdx₁ codec₁ a_new) (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂
codec₂ b_new) R_frame)` across `SubplaceLensFramePreserved`. On a shared
aggregate (`rp₁.allocId = rp₂.allocId`) where either `fieldIdx₁ = 0` or
`fieldIdx₂ = 0` (such as `swap_u32(&mut s.0, &mut s.1)`), both `hRootFree₁` and
`hRootFree₂` hold automatically with no restriction on `R_frame` beyond
`LocalSepProp R_frame`.
-/
theorem sepConj_activeTypedFieldMutBorrow_preserved_two {α β : Type}
    {frameLen : Nat} (rp₁ rp₂ : RawPtrVal)
    (fieldIdx₁ fieldIdx₂ : FieldIdx) (fieldTy₁ fieldTy₂ : Ty)
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β)
    (a_old a_new : α) (b_old b_new : β)
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a_old)
          (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_old)
            R_frame))
        m₀)
    (hInv_final :
      SepSubplaceLensStateInv
        (pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂)
        frameLen [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)]
        m_final)
    (hWf₁ : WfSingleFieldMutBorrow frameLen rp₁ fieldIdx₁ fieldTy₁ m₀)
    (hPres :
      SubplaceLensFramePreserved
        (pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂)
        [(rp₁, codec₁.encode a_old), (rp₂, codec₂.encode b_old)] m₀ m_final)
    (h_R : LocalSepProp R_frame)
    (hRootFree₁ :
      fieldIdx₁ = 0 ∨ (rp₁.allocId = rp₂.allocId ∧ fieldIdx₂ = 0) ∨
        ∀ h : PartialHeap, R_frame h →
          (rp₁.allocId, 0) ∉ h.footprint.addrs)
    (hRootFree₂ :
      fieldIdx₂ = 0 ∨ (rp₂.allocId = rp₁.allocId ∧ fieldIdx₁ = 0) ∨
        ∀ h : PartialHeap, R_frame h →
          (rp₂.allocId, 0) ∉ h.footprint.addrs) :
    SepProp.holdsIn
      (sepConj (ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a_new)
        (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_new)
          R_frame))
      m_final := by
  rcases hSep with ⟨fp, h₁, h₂₃, ⟨_, hs₂₃, hDisj₁, _, _⟩, hA₁,
    h₂, hR₀, ⟨_, hsR, hDisj₂, hAddrs₂₃, hTags₂₃⟩, hA₂, hR_holds₀⟩
  dsimp only at hs₂₃ hsR
  rcases activeTypedFieldMutBorrow_facts hA₁ with ⟨_, _, hCell₁, hTag₁⟩
  rcases activeTypedFieldMutBorrow_facts hA₂ with ⟨_, _, hCell₂, hTag₂⟩
  have hNeTag : rp₁.tag ≠ rp₂.tag := by
    intro hEq
    apply hDisj₁.2 rp₁.tag hTag₁
    apply (hTags₂₃ _).mpr; left; rw [hEq]; exact hTag₂
  have hNePtr : rp₁ ≠ rp₂ := fun hEq => hNeTag (congrArg RawPtrVal.tag hEq)
  have hNeCell₁₂ : (rp₁.allocId, fieldIdx₁) ≠ (rp₂.allocId, fieldIdx₂) := by
    intro hEq
    apply hDisj₁.1 (rp₁.allocId, fieldIdx₁) hCell₁
    apply (hAddrs₂₃ _).mpr; left; rw [hEq]; exact hCell₂
  have hDisj₁R_addrs :
      ∀ cell, cell ∈ h₁.footprint.addrs → cell ∉ hR₀.footprint.addrs := by
    intro cell hc₁ hcR
    exact hDisj₁.1 cell hc₁ ((hAddrs₂₃ cell).mpr (Or.inr hcR))
  have hDisj₁R_tags :
      ∀ t, t ∈ h₁.footprint.tags → t ∉ hR₀.footprint.tags := by
    intro t ht₁ htR
    exact hDisj₁.2 t ht₁ ((hTags₂₃ t).mpr (Or.inr htR))
  have hSub₁ :
      pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ rp₁ =
        .field fieldIdx₁ fieldTy₁ := by
    simp [pairFieldSubplace]
  have hSub₂ :
      pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ rp₂ =
        .field fieldIdx₂ fieldTy₂ := by
    simp [pairFieldSubplace, hNePtr.symm]
  have hR_m₀ : R_frame ⟨m₀, hR₀.footprint⟩ := by
    have hEqH : hR₀ = ⟨m₀, hR₀.footprint⟩ := by
      cases hR₀; dsimp only at hsR hs₂₃ ⊢
      have hS := hsR.trans hs₂₃; subst hS; rfl
    exact hEqH ▸ hR_holds₀
  have hAgree : AgreeOnFootprint hR₀.footprint m₀ m_final := by
    refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
    · rw [memoryLocals_of_callStack_nil hWf₁.callStack_nil,
        memoryLocals_of_callStack_nil hInv_final.callStack_nil]
      by_cases hTracked : allocId = rp₁.allocId ∨ allocId = rp₂.allocId
      · have hOffNeZero : offset ≠ 0 := by
          intro hZ; subst hZ
          rcases hTracked with rfl | rfl
          · rcases hRootFree₁ with hZ₁ | ⟨hAEq, hZ₂⟩ | hNoR₁
            · subst hZ₁; exact hDisj₁R_addrs _ hCell₁ hIn
            · rw [hAEq] at hIn; subst hZ₂; exact hDisj₂.1 _ hCell₂ hIn
            · exact hNoR₁ ⟨m₀, hR₀.footprint⟩ hR_m₀ hIn
          · rcases hRootFree₂ with hZ₂ | ⟨hAEq, hZ₁⟩ | hNoR₂
            · subst hZ₂; exact hDisj₂.1 _ hCell₂ hIn
            · rw [hAEq] at hIn; subst hZ₁; exact hDisj₁R_addrs _ hCell₁ hIn
            · exact hNoR₂ ⟨m₀, hR₀.footprint⟩ hR_m₀ hIn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hOffNeZero
        rw [readAllocAt_succ_eq_readFieldAt, readAllocAt_succ_eq_readFieldAt]
        refine (hPres.fields_unchanged_outside allocId (k + 1) ?_).symm
        intro e he hEA
        rcases List.mem_cons.mp he with rfl | hTl
        · refine ⟨fieldIdx₁, fieldTy₁, hSub₁, ?_⟩
          intro hEqF
          dsimp only at hEA
          change (allocId, k + 1) ∈ hR₀.footprint.addrs at hIn
          rw [← hEA, ← hEqF] at hIn
          exact hDisj₁R_addrs _ hCell₁ hIn
        · rw [List.mem_singleton.mp hTl] at hEA ⊢
          refine ⟨fieldIdx₂, fieldTy₂, hSub₂, ?_⟩
          intro hEqF
          dsimp only at hEA
          change (allocId, k + 1) ∈ hR₀.footprint.addrs at hIn
          rw [← hEA, ← hEqF] at hIn
          exact hDisj₂.1 _ hCell₂ hIn
      · unfold readAllocAt?
        refine (hPres.locals_unchanged_outside allocId ?_) ▸ rfl
        intro e he hEqA
        rcases List.mem_cons.mp he with rfl | hTl
        · exact hTracked (Or.inl hEqA)
        · rw [List.mem_singleton.mp hTl] at hEqA
          exact hTracked (Or.inr hEqA)
    · refine (hPres.borrows_unchanged_outside tag ?_).symm
      intro e he hEqT
      rcases List.mem_cons.mp he with rfl | hTl
      · dsimp only at hEqT; subst hEqT
        exact hDisj₁R_tags _ hTag₁ hIn
      · rw [List.mem_singleton.mp hTl] at hEqT
        dsimp only at hEqT; subst hEqT
        exact hDisj₂.2 _ hTag₂ hIn
  have hR_final : R_frame ⟨m_final, hR₀.footprint⟩ :=
    h_R hR₀.footprint m₀ m_final hAgree hR_m₀
  have hVal₁ := hInv_final.entries_valid rp₁ (codec₁.encode a_new)
    (List.Mem.head _)
  have hVal₂ := hInv_final.entries_valid rp₂ (codec₂.encode b_new)
    (List.Mem.tail _ (List.Mem.head []))
  unfold BorrowSubplace.entryValid at hVal₁ hVal₂
  rw [hSub₁] at hVal₁
  rw [hSub₂] at hVal₂
  rcases hVal₁ with ⟨_, _, hFldF₁, hExclF₁⟩
  rcases hVal₂ with ⟨_, _, hFldF₂, hExclF₂⟩
  rcases hExclF₁.lookup_active with ⟨e₁, hL₁, hT₁, _, hP₁, _, _⟩
  rcases hExclF₂.lookup_active with ⟨e₂, hL₂, hT₂, _, hP₂, _, _⟩
  have hAF₁ :
      ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a_new
        ⟨m_final, fieldMutBorrowFootprint rp₁ fieldIdx₁⟩ :=
    activeTypedFieldMutBorrow_intro
      (by rw [memoryLocals_of_callStack_nil hInv_final.callStack_nil]
          exact hFldF₁)
      ⟨e₁, hL₁, hT₁, hP₁⟩
  have hAF₂ :
      ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_new
        ⟨m_final, fieldMutBorrowFootprint rp₂ fieldIdx₂⟩ :=
    activeTypedFieldMutBorrow_intro
      (by rw [memoryLocals_of_callStack_nil hInv_final.callStack_nil]
          exact hFldF₂)
      ⟨e₂, hL₂, hT₂, hP₂⟩
  let fp₂R : Footprint := {
    addrs := (rp₂.allocId, fieldIdx₂) :: hR₀.footprint.addrs
    tags := rp₂.tag :: hR₀.footprint.tags
  }
  have hSep₂R :
      sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_new) R_frame
        ⟨m_final, fp₂R⟩ := by
    refine ⟨⟨m_final, fieldMutBorrowFootprint rp₂ fieldIdx₂⟩,
      ⟨m_final, hR₀.footprint⟩, ⟨rfl, rfl, ⟨?_, ?_⟩, ?_, ?_⟩, hAF₂, hR_final⟩
    · intro cell hc₂ hcR
      rw [List.mem_singleton.mp hc₂] at hcR
      exact hDisj₂.1 _ hCell₂ hcR
    · intro t ht₂ htR
      rw [List.mem_singleton.mp ht₂] at htR
      exact hDisj₂.2 _ hTag₂ htR
    · intro addr; simp [fp₂R, fieldMutBorrowFootprint]
    · intro tag; simp [fp₂R, fieldMutBorrowFootprint]
  let fpTotal : Footprint := {
    addrs := (rp₁.allocId, fieldIdx₁) :: fp₂R.addrs
    tags := rp₁.tag :: fp₂R.tags
  }
  refine ⟨fpTotal,
    ⟨m_final, fieldMutBorrowFootprint rp₁ fieldIdx₁⟩,
    ⟨m_final, fp₂R⟩,
    ⟨rfl, rfl, ⟨?_, ?_⟩, ?_, ?_⟩,
    hAF₁, hSep₂R⟩
  · intro cell hc₁ hc₂R
    rw [List.mem_singleton.mp hc₁] at hc₂R
    rcases List.mem_cons.mp hc₂R with hEq₁₂ | hcR
    · exact hNeCell₁₂ hEq₁₂
    · exact hDisj₁R_addrs _ hCell₁ hcR
  · intro t ht₁ ht₂R
    rw [List.mem_singleton.mp ht₁] at ht₂R
    rcases List.mem_cons.mp ht₂R with hEqT | htR
    · exact hNeTag hEqT
    · exact hDisj₁R_tags _ hTag₁ htR
  · intro addr; simp [fpTotal, fieldMutBorrowFootprint]
  · intro tag; simp [fpTotal, fieldMutBorrowFootprint]

/-! ### Unrestricted Sub-Place Frame Locality (`AgreeOnSubplaceFootprint`) -/

/--
Sub-place footprint agreement (`AgreeOnSubplaceFootprint fp m₁ m₂`): `m₁` and
`m₂` agree on `readFieldAt?` at every `(allocId, fieldIdx) ∈ fp.addrs`, on
whole-slot `get?` at `(allocId, 0) ∈ fp.addrs` whenever `allocId` is not a
variant-`0` aggregate in `m₁`, and on `lookupBorrow` at every `tag ∈ fp.tags`.

Unlike `AgreeOnFootprint` (whose `readAllocAt?` at `offset = 0` inspects the
entire aggregate value `.aggregate 0 elems` and therefore changes whenever any
sibling field `fieldIdx > 0` is mutated), `AgreeOnSubplaceFootprint` inspects
field `0` via `readFieldAt?`, so mutating `&mut s.1` preserves
`ActiveTypedFieldMutBorrow` on `&mut s.0` in `R_frame` with no `hRootFree`
side condition.
-/
def AgreeOnSubplaceFootprint (fp : Footprint) (m₁ m₂ : Memory) : Prop :=
  (∀ allocId fieldIdx, (allocId, fieldIdx) ∈ fp.addrs →
    readFieldAt? (memoryLocals m₁) allocId fieldIdx =
      readFieldAt? (memoryLocals m₂) allocId fieldIdx ∧
    (fieldIdx = 0 →
      (∀ elems,
        get? (memoryLocals m₁) allocId ≠ .some (.init (.aggregate 0 elems))) →
      get? (memoryLocals m₁) allocId = get? (memoryLocals m₂) allocId)) ∧
  (∀ tag, tag ∈ fp.tags →
    lookupBorrow m₁.borrows tag = lookupBorrow m₂.borrows tag)

/--
A `SepProp` is sub-place local (`SubplaceLocalSepProp P`) when its truth on
`⟨m, fp⟩` is invariant under `AgreeOnSubplaceFootprint fp m₁ m₂`.
-/
def SubplaceLocalSepProp (P : SepProp) : Prop :=
  ∀ (fp : Footprint) (m₁ m₂ : Memory),
    AgreeOnSubplaceFootprint fp m₁ m₂ → P ⟨m₁, fp⟩ → P ⟨m₂, fp⟩

theorem subplaceLocalSepProp_emp : SubplaceLocalSepProp emp := by
  intro _ _ _ _ hEmp
  exact hEmp

theorem subplaceLocalSepProp_borrowToken
    (rp : RawPtrVal) (perm : TreeBorrowPerm) :
    SubplaceLocalSepProp (BorrowToken rp perm) := by
  intro fp m₁ m₂ hAgree ⟨⟨entry, hLook, hT, hP⟩, hFp⟩
  dsimp only at hFp
  have hTagIn : rp.tag ∈ fp.tags := by
    rw [hFp]
    exact List.Mem.head []
  refine ⟨⟨entry, ?_, hT, hP⟩, hFp⟩
  rw [← hAgree.2 rp.tag hTagIn]
  exact hLook

theorem subplaceLocalSepProp_fieldPointsTo
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (v : Value) :
    SubplaceLocalSepProp (FieldPointsTo rp fieldIdx v) := by
  intro fp m₁ m₂ hAgree ⟨hFld, hFp⟩
  dsimp only at hFp
  have hIn : (rp.allocId, fieldIdx) ∈ fp.addrs := by
    rw [hFp]
    exact List.Mem.head []
  refine ⟨?_, hFp⟩
  rw [← (hAgree.1 rp.allocId fieldIdx hIn).1]
  exact hFld

theorem subplaceLocalSepProp_activeTypedFieldMutBorrow {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (codec : ValueCodec α) (a : α) :
    SubplaceLocalSepProp (ActiveTypedFieldMutBorrow rp fieldIdx codec a) := by
  intro fp m₁ m₂ hAgree ⟨h₁, h₂, ⟨hs₁, hs₂, hDisj, hAddrs, hTags⟩, hP, hQ⟩
  dsimp only at hs₁ hs₂
  refine ⟨⟨m₂, h₁.footprint⟩, ⟨m₂, h₂.footprint⟩,
    ⟨rfl, rfl, hDisj, hAddrs, hTags⟩, ?_, ?_⟩
  · apply subplaceLocalSepProp_fieldPointsTo rp fieldIdx (codec.encode a)
      h₁.footprint m₁ m₂
    · refine ⟨fun allocId f hIn =>
        hAgree.1 allocId f ((hAddrs _).mpr (Or.inl hIn)),
        fun tag hIn => hAgree.2 tag ((hTags _).mpr (Or.inl hIn))⟩
    · have hEq : h₁ = ⟨m₁, h₁.footprint⟩ := by
        cases h₁; dsimp only at hs₁ ⊢; subst hs₁; rfl
      exact hEq ▸ hP
  · apply subplaceLocalSepProp_borrowToken rp .active h₂.footprint m₁ m₂
    · refine ⟨fun allocId f hIn =>
        hAgree.1 allocId f ((hAddrs _).mpr (Or.inr hIn)),
        fun tag hIn => hAgree.2 tag ((hTags _).mpr (Or.inr hIn))⟩
    · have hEq : h₂ = ⟨m₁, h₂.footprint⟩ := by
        cases h₂; dsimp only at hs₂ ⊢; subst hs₂; rfl
      exact hEq ▸ hQ

theorem subplaceLocalSepProp_pointsTo_of_not_agg
    (rp : RawPtrVal) (v : Value) (hOff : rp.offset = 0)
    (hNotAgg : ∀ elems, v ≠ .aggregate 0 elems) :
    SubplaceLocalSepProp (PointsTo rp v) := by
  intro fp m₁ m₂ hAgree ⟨hPts, hFp⟩
  dsimp only at hFp
  have hIn : (rp.allocId, 0) ∈ fp.addrs := by
    rw [hFp, ← hOff]
    exact List.Mem.head []
  refine ⟨?_, hFp⟩
  unfold readAllocAt? at hPts ⊢
  rw [hOff] at hPts ⊢
  cases hGet₁ : get? (memoryLocals m₁) rp.allocId with
  | none => rw [hGet₁] at hPts; nomatch hPts
  | some slot₁ =>
    rw [hGet₁] at hPts
    cases slot₁ with
    | dead => nomatch hPts
    | uninit => nomatch hPts
    | init val₁ =>
      dsimp only at hPts
      injection hPts with hValEq
      subst hValEq
      have hNoAgg :
          ∀ elems,
            get? (memoryLocals m₁) rp.allocId ≠
              .some (.init (.aggregate 0 elems)) := by
        intro elems hEq
        rw [hGet₁] at hEq
        injection hEq with hSlotEq
        injection hSlotEq with hVEq
        exact hNotAgg elems hVEq
      have hGetEq := (hAgree.1 rp.allocId 0 hIn).2 rfl hNoAgg
      rw [← hGetEq, hGet₁]

theorem subplaceLocalSepProp_sepConj {P Q : SepProp}
    (hP : SubplaceLocalSepProp P) (hQ : SubplaceLocalSepProp Q) :
    SubplaceLocalSepProp (sepConj P Q) := by
  intro fp m₁ m₂ hAgree ⟨h₁, h₂, ⟨hs₁, hs₂, hDisj, hAddrs, hTags⟩, hp, hq⟩
  dsimp only at hs₁ hs₂
  refine ⟨⟨m₂, h₁.footprint⟩, ⟨m₂, h₂.footprint⟩,
    ⟨rfl, rfl, hDisj, hAddrs, hTags⟩, ?_, ?_⟩
  · apply hP h₁.footprint m₁ m₂
    · refine ⟨fun allocId f hIn =>
        hAgree.1 allocId f ((hAddrs _).mpr (Or.inl hIn)),
        fun tag hIn => hAgree.2 tag ((hTags _).mpr (Or.inl hIn))⟩
    · have hEq : h₁ = ⟨m₁, h₁.footprint⟩ := by
        cases h₁; dsimp only at hs₁ ⊢; subst hs₁; rfl
      exact hEq ▸ hp
  · apply hQ h₂.footprint m₁ m₂
    · refine ⟨fun allocId f hIn =>
        hAgree.1 allocId f ((hAddrs _).mpr (Or.inr hIn)),
        fun tag hIn => hAgree.2 tag ((hTags _).mpr (Or.inr hIn))⟩
    · have hEq : h₂ = ⟨m₁, h₂.footprint⟩ := by
        cases h₂; dsimp only at hs₂ ⊢; subst hs₂; rfl
      exact hEq ▸ hq

theorem subplaceLocalSepProp_activeTypedMutBorrow_of_not_agg {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) (a : α) (hOff : rp.offset = 0)
    (hNotAgg : ∀ elems, codec.encode a ≠ .aggregate 0 elems) :
    SubplaceLocalSepProp (ActiveTypedMutBorrow rp codec a) :=
  subplaceLocalSepProp_sepConj
    (subplaceLocalSepProp_pointsTo_of_not_agg rp (codec.encode a) hOff hNotAgg)
    (subplaceLocalSepProp_borrowToken rp .active)

/--
Sub-place footprint agreement for `treeFieldMemoryPtrMutLens.writeBack`: writing
field `fieldIdx` of `rp.allocId` agrees with `m` on `AgreeOnSubplaceFootprint`
for any `fp_frame` whose cells avoid `(rp.allocId, fieldIdx)` (including when
`fp_frame` owns `(rp.allocId, 0)` and `fieldIdx > 0`).
-/
theorem treeFieldMemoryPtrMutLens_writeBack_agreeOnSubplaceFootprint
    {α : Type} {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {m : Memory} (a : α)
    (hm : ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec m)
    {fp_frame : Footprint}
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        allocId ≠ rp.allocId ∨ offset ≠ fieldIdx) :
    AgreeOnSubplaceFootprint fp_frame m
      ((treeFieldMemoryPtrMutLens rp fieldIdx codec).writeBack a m) := by
  rw [treeFieldMemoryPtrMutLens_writeBack_eq_of_treeField
    rp fieldIdx fieldTy codec a hm.exclusive]
  rcases hm.valid_raw with ⟨⟨a₀, hFld₀⟩⟩
  rcases eq_aggregate_of_readFieldAt_some hFld₀ with ⟨elems, hGet₀, _⟩
  dsimp only [rawFieldMutLens]
  refine ⟨fun allocId offset hIn => ?_, fun _ _ => ?_⟩
  · rw [memoryLocals_updateMemoryLocals]
    by_cases hEqAlloc : allocId = rp.allocId
    · subst hEqAlloc
      rcases hAddrs rp.allocId offset hIn with hNeAlloc | hNeFld
      · exact absurd rfl hNeAlloc
      · refine ⟨(readFieldAt_writeFieldAt_ne_eq _ _ _ hNeFld.symm).symm,
          fun _ hNoAgg => absurd hGet₀ (hNoAgg elems)⟩
    · refine ⟨?_, fun _ _ =>
        (get?_writeFieldAt_ne_alloc _ _ _ hEqAlloc).symm⟩
      unfold readFieldAt?
      rw [get?_writeFieldAt_ne_alloc _ _ _ hEqAlloc]
  · rw [updateMemoryLocals_borrows]

/--
Unrestricted 1-Field Exit Bridge
(`sepConj_activeTypedFieldMutBorrow_preserved_one_subplace`):
preserves `sepConj (ActiveTypedFieldMutBorrow rp fieldIdx codec a_new) R_frame`
for **any** `fieldIdx : FieldIdx` (including `fieldIdx > 0` when sibling field
`0` is held in `R_frame`) whenever `SubplaceLocalSepProp R_frame` holds, with
no `hRootFree` side condition.
-/
theorem sepConj_activeTypedFieldMutBorrow_preserved_one_subplace {α : Type}
    {frameLen : Nat} {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {a_old a_new : α}
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp fieldIdx codec a_old) R_frame)
        m₀)
    (hInv_final :
      SepSubplaceLensStateInv (singleFieldSubplace rp fieldIdx fieldTy)
        frameLen [(rp, codec.encode a_new)] m_final)
    (hWf : WfSingleFieldMutBorrow frameLen rp fieldIdx fieldTy m₀)
    (hPres :
      SubplaceLensFramePreserved (singleFieldSubplace rp fieldIdx fieldTy)
        [(rp, codec.encode a_old)] m₀ m_final)
    (h_R : SubplaceLocalSepProp R_frame) :
    SepProp.holdsIn
      (sepConj (ActiveTypedFieldMutBorrow rp fieldIdx codec a_new) R_frame)
      m_final := by
  rcases hSep with ⟨fp, h₁, hR₀, ⟨hs₁, hsR, hDisj, _, _⟩, hA₁, hR_holds₀⟩
  dsimp only at hs₁ hsR
  rcases activeTypedFieldMutBorrow_facts hA₁ with ⟨hFld₀, _, hCell₁, hTag₁⟩
  have hFld₀_m₀ :
      readFieldAt? (memoryLocals m₀) rp.allocId fieldIdx =
        some (codec.encode a_old) := hs₁ ▸ hFld₀
  rcases eq_aggregate_of_readFieldAt_some hFld₀_m₀ with ⟨elems₀, hGet₀, _⟩
  have hValF := hInv_final.entries_valid rp (codec.encode a_new)
    (List.Mem.head [])
  unfold BorrowSubplace.entryValid singleFieldSubplace at hValF
  simp only [ite_true] at hValF
  rcases hValF with ⟨_, _, hFldF, hExclF⟩
  have hAgree : AgreeOnSubplaceFootprint hR₀.footprint m₀ m_final := by
    refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
    · rw [memoryLocals_of_callStack_nil hWf.callStack_nil,
        memoryLocals_of_callStack_nil hInv_final.callStack_nil]
      by_cases hEqAlloc : allocId = rp.allocId
      · subst hEqAlloc
        have hOffNeFld : offset ≠ fieldIdx := by
          intro hEqF
          subst hEqF
          exact hDisj.1 (rp.allocId, offset) hCell₁ hIn
        refine ⟨(hPres.fields_unchanged_outside rp.allocId offset ?_).symm,
          fun _ hNoAgg => ?_⟩
        · intro e he _
          rw [List.mem_singleton.mp he]
          exact ⟨fieldIdx, fieldTy, by simp [singleFieldSubplace],
            hOffNeFld.symm⟩
        · rw [memoryLocals_of_callStack_nil hWf.callStack_nil] at hGet₀
          exact absurd hGet₀ (hNoAgg elems₀)
      · have hLocEq :
            get? m_final.callerLocals allocId =
              get? m₀.callerLocals allocId := by
          refine hPres.locals_unchanged_outside allocId ?_
          intro e he
          rw [List.mem_singleton.mp he]
          exact hEqAlloc
        refine ⟨?_, fun _ _ => hLocEq.symm⟩
        unfold readFieldAt?
        rw [hLocEq]
    · refine (hPres.borrows_unchanged_outside tag ?_).symm
      intro e he hEqT
      rw [List.mem_singleton.mp he] at hEqT
      subst hEqT
      exact hDisj.2 rp.tag hTag₁ hIn
  have hR_m₀ : R_frame ⟨m₀, hR₀.footprint⟩ := by
    have hEqH : hR₀ = ⟨m₀, hR₀.footprint⟩ := by
      cases hR₀; dsimp only at hsR ⊢; subst hsR; rfl
    exact hEqH ▸ hR_holds₀
  have hR_final : R_frame ⟨m_final, hR₀.footprint⟩ :=
    h_R hR₀.footprint m₀ m_final hAgree hR_m₀
  have hFldML :
      readFieldAt? (memoryLocals m_final) rp.allocId fieldIdx =
        some (codec.encode a_new) := by
    rw [memoryLocals_of_callStack_nil hInv_final.callStack_nil]
    exact hFldF
  rcases hExclF.lookup_active with ⟨entryF, hLookF, hTF, _, hPermF, _, _⟩
  have hA₁_final :
      ActiveTypedFieldMutBorrow rp fieldIdx codec a_new
        ⟨m_final, fieldMutBorrowFootprint rp fieldIdx⟩ :=
    activeTypedFieldMutBorrow_intro hFldML ⟨entryF, hLookF, hTF, hPermF⟩
  let fpTotal : Footprint := {
    addrs := (rp.allocId, fieldIdx) :: hR₀.footprint.addrs
    tags := rp.tag :: hR₀.footprint.tags
  }
  refine ⟨fpTotal,
    ⟨m_final, fieldMutBorrowFootprint rp fieldIdx⟩,
    ⟨m_final, hR₀.footprint⟩,
    ⟨rfl, rfl, ⟨?_, ?_⟩, ?_, ?_⟩,
    hA₁_final, hR_final⟩
  · intro cell hIn₁ hInR
    rw [List.mem_singleton.mp hIn₁] at hInR
    exact hDisj.1 (rp.allocId, fieldIdx) hCell₁ hInR
  · intro t hIn₁ hInR
    rw [List.mem_singleton.mp hIn₁] at hInR
    exact hDisj.2 rp.tag hTag₁ hInR
  · intro addr; simp [fpTotal, fieldMutBorrowFootprint]
  · intro tag; simp [fpTotal, fieldMutBorrowFootprint]

/--
Unrestricted 2-Field Exit Bridge
(`sepConj_activeTypedFieldMutBorrow_preserved_two_subplace`):
preserves two separated `ActiveTypedFieldMutBorrow` assertions with an arbitrary
`SubplaceLocalSepProp R_frame` across `SubplaceLensFramePreserved` for any
`fieldIdx₁, fieldIdx₂ : FieldIdx` (even when neither is `0`), with no
`hRootFree` side condition.
-/
theorem sepConj_activeTypedFieldMutBorrow_preserved_two_subplace {α β : Type}
    {frameLen : Nat} (rp₁ rp₂ : RawPtrVal)
    (fieldIdx₁ fieldIdx₂ : FieldIdx) (fieldTy₁ fieldTy₂ : Ty)
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β)
    (a_old a_new : α) (b_old b_new : β)
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a_old)
          (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_old)
            R_frame))
        m₀)
    (hInv_final :
      SepSubplaceLensStateInv
        (pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂)
        frameLen [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)]
        m_final)
    (hWf₁ : WfSingleFieldMutBorrow frameLen rp₁ fieldIdx₁ fieldTy₁ m₀)
    (hPres :
      SubplaceLensFramePreserved
        (pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂)
        [(rp₁, codec₁.encode a_old), (rp₂, codec₂.encode b_old)] m₀ m_final)
    (h_R : SubplaceLocalSepProp R_frame) :
    SepProp.holdsIn
      (sepConj (ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a_new)
        (sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_new)
          R_frame))
      m_final := by
  rcases hSep with ⟨fp, h₁, h₂₃, ⟨hs₁, hs₂₃, hDisj₁, _, _⟩, hA₁,
    h₂, hR₀, ⟨hs₂, hsR, hDisj₂, hAddrs₂₃, hTags₂₃⟩, hA₂, hR_holds₀⟩
  dsimp only at hs₁ hs₂ hs₂₃ hsR
  rcases activeTypedFieldMutBorrow_facts hA₁ with ⟨hFld₀₁, _, hCell₁, hTag₁⟩
  rcases activeTypedFieldMutBorrow_facts hA₂ with ⟨hFld₀₂, _, hCell₂, hTag₂⟩
  have hFld₁_m₀ :
      readFieldAt? (memoryLocals m₀) rp₁.allocId fieldIdx₁ =
        some (codec₁.encode a_old) := hs₁ ▸ hFld₀₁
  have hFld₂_m₀ :
      readFieldAt? (memoryLocals m₀) rp₂.allocId fieldIdx₂ =
        some (codec₂.encode b_old) := (hs₂.trans hs₂₃) ▸ hFld₀₂
  rcases eq_aggregate_of_readFieldAt_some hFld₁_m₀ with ⟨elems₁, hGet₀₁, _⟩
  rcases eq_aggregate_of_readFieldAt_some hFld₂_m₀ with ⟨elems₂, hGet₀₂, _⟩
  have hNeTag : rp₁.tag ≠ rp₂.tag := by
    intro hEq
    apply hDisj₁.2 rp₁.tag hTag₁
    apply (hTags₂₃ _).mpr; left; rw [hEq]; exact hTag₂
  have hNePtr : rp₁ ≠ rp₂ := fun hEq => hNeTag (congrArg RawPtrVal.tag hEq)
  have hNeCell₁₂ : (rp₁.allocId, fieldIdx₁) ≠ (rp₂.allocId, fieldIdx₂) := by
    intro hEq
    apply hDisj₁.1 (rp₁.allocId, fieldIdx₁) hCell₁
    apply (hAddrs₂₃ _).mpr; left; rw [hEq]; exact hCell₂
  have hDisj₁R_addrs :
      ∀ cell, cell ∈ h₁.footprint.addrs → cell ∉ hR₀.footprint.addrs := by
    intro cell hc₁ hcR
    exact hDisj₁.1 cell hc₁ ((hAddrs₂₃ cell).mpr (Or.inr hcR))
  have hDisj₁R_tags :
      ∀ t, t ∈ h₁.footprint.tags → t ∉ hR₀.footprint.tags := by
    intro t ht₁ htR
    exact hDisj₁.2 t ht₁ ((hTags₂₃ t).mpr (Or.inr htR))
  have hSub₁ :
      pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ rp₁ =
        .field fieldIdx₁ fieldTy₁ := by
    simp [pairFieldSubplace]
  have hSub₂ :
      pairFieldSubplace rp₁ rp₂ fieldIdx₁ fieldIdx₂ fieldTy₁ fieldTy₂ rp₂ =
        .field fieldIdx₂ fieldTy₂ := by
    simp [pairFieldSubplace, hNePtr.symm]
  have hR_m₀ : R_frame ⟨m₀, hR₀.footprint⟩ := by
    have hEqH : hR₀ = ⟨m₀, hR₀.footprint⟩ := by
      cases hR₀; dsimp only at hsR hs₂₃ ⊢
      have hS := hsR.trans hs₂₃; subst hS; rfl
    exact hEqH ▸ hR_holds₀
  have hAgree : AgreeOnSubplaceFootprint hR₀.footprint m₀ m_final := by
    refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
    · rw [memoryLocals_of_callStack_nil hWf₁.callStack_nil,
        memoryLocals_of_callStack_nil hInv_final.callStack_nil]
      by_cases hTracked : allocId = rp₁.allocId ∨ allocId = rp₂.allocId
      · refine ⟨(hPres.fields_unchanged_outside allocId offset ?_).symm,
          fun _ hNoAgg => ?_⟩
        · intro e he hEA
          rcases List.mem_cons.mp he with rfl | hTl
          · refine ⟨fieldIdx₁, fieldTy₁, hSub₁, ?_⟩
            intro hEqF
            dsimp only at hEA
            rw [← hEA, ← hEqF] at hIn
            exact hDisj₁R_addrs _ hCell₁ hIn
          · rw [List.mem_singleton.mp hTl] at hEA ⊢
            refine ⟨fieldIdx₂, fieldTy₂, hSub₂, ?_⟩
            intro hEqF
            dsimp only at hEA
            rw [← hEA, ← hEqF] at hIn
            exact hDisj₂.1 _ hCell₂ hIn
        · rw [memoryLocals_of_callStack_nil hWf₁.callStack_nil] at hGet₀₁ hGet₀₂
          rcases hTracked with rfl | rfl
          · exact absurd hGet₀₁ (hNoAgg elems₁)
          · exact absurd hGet₀₂ (hNoAgg elems₂)
      · have hLocEq :
            get? m_final.callerLocals allocId =
              get? m₀.callerLocals allocId := by
          refine hPres.locals_unchanged_outside allocId ?_
          intro e he hEqA
          rcases List.mem_cons.mp he with rfl | hTl
          · exact hTracked (Or.inl hEqA)
          · rw [List.mem_singleton.mp hTl] at hEqA
            exact hTracked (Or.inr hEqA)
        refine ⟨?_, fun _ _ => hLocEq.symm⟩
        unfold readFieldAt?
        rw [hLocEq]
    · refine (hPres.borrows_unchanged_outside tag ?_).symm
      intro e he hEqT
      rcases List.mem_cons.mp he with rfl | hTl
      · dsimp only at hEqT; subst hEqT
        exact hDisj₁R_tags _ hTag₁ hIn
      · rw [List.mem_singleton.mp hTl] at hEqT
        dsimp only at hEqT; subst hEqT
        exact hDisj₂.2 _ hTag₂ hIn
  have hR_final : R_frame ⟨m_final, hR₀.footprint⟩ :=
    h_R hR₀.footprint m₀ m_final hAgree hR_m₀
  have hVal₁ := hInv_final.entries_valid rp₁ (codec₁.encode a_new)
    (List.Mem.head _)
  have hVal₂ := hInv_final.entries_valid rp₂ (codec₂.encode b_new)
    (List.Mem.tail _ (List.Mem.head []))
  unfold BorrowSubplace.entryValid at hVal₁ hVal₂
  rw [hSub₁] at hVal₁
  rw [hSub₂] at hVal₂
  rcases hVal₁ with ⟨_, _, hFldF₁, hExclF₁⟩
  rcases hVal₂ with ⟨_, _, hFldF₂, hExclF₂⟩
  rcases hExclF₁.lookup_active with ⟨e₁, hL₁, hT₁, _, hP₁, _, _⟩
  rcases hExclF₂.lookup_active with ⟨e₂, hL₂, hT₂, _, hP₂, _, _⟩
  have hAF₁ :
      ActiveTypedFieldMutBorrow rp₁ fieldIdx₁ codec₁ a_new
        ⟨m_final, fieldMutBorrowFootprint rp₁ fieldIdx₁⟩ :=
    activeTypedFieldMutBorrow_intro
      (by rw [memoryLocals_of_callStack_nil hInv_final.callStack_nil]
          exact hFldF₁)
      ⟨e₁, hL₁, hT₁, hP₁⟩
  have hAF₂ :
      ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_new
        ⟨m_final, fieldMutBorrowFootprint rp₂ fieldIdx₂⟩ :=
    activeTypedFieldMutBorrow_intro
      (by rw [memoryLocals_of_callStack_nil hInv_final.callStack_nil]
          exact hFldF₂)
      ⟨e₂, hL₂, hT₂, hP₂⟩
  let fp₂R : Footprint := {
    addrs := (rp₂.allocId, fieldIdx₂) :: hR₀.footprint.addrs
    tags := rp₂.tag :: hR₀.footprint.tags
  }
  have hSep₂R :
      sepConj (ActiveTypedFieldMutBorrow rp₂ fieldIdx₂ codec₂ b_new) R_frame
        ⟨m_final, fp₂R⟩ := by
    refine ⟨⟨m_final, fieldMutBorrowFootprint rp₂ fieldIdx₂⟩,
      ⟨m_final, hR₀.footprint⟩, ⟨rfl, rfl, ⟨?_, ?_⟩, ?_, ?_⟩, hAF₂, hR_final⟩
    · intro cell hc₂ hcR
      rw [List.mem_singleton.mp hc₂] at hcR
      exact hDisj₂.1 _ hCell₂ hcR
    · intro t ht₂ htR
      rw [List.mem_singleton.mp ht₂] at htR
      exact hDisj₂.2 _ hTag₂ htR
    · intro addr; simp [fp₂R, fieldMutBorrowFootprint]
    · intro tag; simp [fp₂R, fieldMutBorrowFootprint]
  let fpTotal : Footprint := {
    addrs := (rp₁.allocId, fieldIdx₁) :: fp₂R.addrs
    tags := rp₁.tag :: fp₂R.tags
  }
  refine ⟨fpTotal,
    ⟨m_final, fieldMutBorrowFootprint rp₁ fieldIdx₁⟩,
    ⟨m_final, fp₂R⟩,
    ⟨rfl, rfl, ⟨?_, ?_⟩, ?_, ?_⟩,
    hAF₁, hSep₂R⟩
  · intro cell hc₁ hc₂R
    rw [List.mem_singleton.mp hc₁] at hc₂R
    rcases List.mem_cons.mp hc₂R with hEq₁₂ | hcR
    · exact hNeCell₁₂ hEq₁₂
    · exact hDisj₁R_addrs _ hCell₁ hcR
  · intro t ht₁ ht₂R
    rw [List.mem_singleton.mp ht₁] at ht₂R
    rcases List.mem_cons.mp ht₂R with hEqT | htR
    · exact hNeTag hEqT
    · exact hDisj₁R_tags _ hTag₁ htR
  · intro addr; simp [fpTotal, fieldMutBorrowFootprint]
  · intro tag; simp [fpTotal, fieldMutBorrowFootprint]

/-! ### `k`-Ary Field-Granular Lens Families & `SupportedBy` Bridges -/

/--
A typed field-granular mutable-borrow binding (`&mut s.fieldIdx`): pointer `rp`,
field index `fieldIdx`, field type `fieldTy`, value codec `codec`, and current
logical field value `val`.
-/
structure FieldMutBorrowBinding : Type 1 where
  α : Type
  rp : RawPtrVal
  fieldIdx : FieldIdx
  fieldTy : Ty
  codec : ValueCodec α
  val : α

/--
Build a `FieldMutBorrowBinding`, inferring the field type `α` from `codec`.
-/
def FieldMutBorrowBinding.bind {α : Type}
    (rp : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (codec : ValueCodec α) (val : α) : FieldMutBorrowBinding :=
  ⟨α, rp, fieldIdx, fieldTy, codec, val⟩

/-- `ActiveTypedFieldMutBorrow b.rp b.fieldIdx b.codec b.val`. -/
def FieldMutBorrowBinding.toSepProp (b : FieldMutBorrowBinding) : SepProp :=
  ActiveTypedFieldMutBorrow b.rp b.fieldIdx b.codec b.val

/-- Pure lens-state entry `(b.rp, b.codec.encode b.val)`. -/
def FieldMutBorrowBinding.entry
    (b : FieldMutBorrowBinding) : RawPtrVal × Value :=
  (b.rp, b.codec.encode b.val)

/-- Address cell `(allocId, fieldIdx)` owned by `b`'s `FieldPointsTo`. -/
def FieldMutBorrowBinding.cell (b : FieldMutBorrowBinding) : Nat × Nat :=
  (b.rp.allocId, b.fieldIdx)

/--
`k`-ary separating conjunction of field-granular mutable borrows
`ATFMB b₁ ∗ ⋯ ∗ ATFMB bₖ ∗ R`, right-nested like the binary form.
-/
def sepConjFieldBindings
    (bs : List FieldMutBorrowBinding) (R : SepProp) : SepProp :=
  sepConjList (bs.map FieldMutBorrowBinding.toSepProp) R

/-- Combined footprint of a field-binding list. -/
def fieldBindingsFootprint (bs : List FieldMutBorrowBinding) : Footprint :=
  { addrs := bs.map FieldMutBorrowBinding.cell, tags := bs.map (·.rp.tag) }

/--
Decomposition of `sepConjFieldBindings bs R` at `h`: every binding's field value
and active borrow token are present in `h.state`, binding `(allocId, fieldIdx)`
cells and tags are pairwise distinct and owned by `h`, and the frame `R` holds
at a footprint `fpR ⊆ h.footprint` disjoint from every binding.
-/
theorem sepConjFieldBindings_split
    {bs : List FieldMutBorrowBinding} {R : SepProp} {h : PartialHeap}
    (hSep : sepConjFieldBindings bs R h) :
    (∀ b ∈ bs,
      readFieldAt? (memoryLocals h.state) b.rp.allocId b.fieldIdx =
        some (b.codec.encode b.val) ∧
      ∃ entry,
        lookupBorrow h.state.borrows b.rp.tag = some entry ∧
        entry.targetLocal = b.rp.allocId ∧
        entry.perm = .active) ∧
    bs.Pairwise (fun b₁ b₂ => b₁.cell ≠ b₂.cell ∧ b₁.rp.tag ≠ b₂.rp.tag) ∧
    (∀ b ∈ bs, b.cell ∈ h.footprint.addrs ∧ b.rp.tag ∈ h.footprint.tags) ∧
    ∃ fpR : Footprint,
      R ⟨h.state, fpR⟩ ∧
      (∀ b ∈ bs, b.cell ∉ fpR.addrs ∧ b.rp.tag ∉ fpR.tags) ∧
      (∀ a ∈ fpR.addrs, a ∈ h.footprint.addrs) ∧
      (∀ t ∈ fpR.tags, t ∈ h.footprint.tags) := by
  induction bs generalizing h with
  | nil =>
    refine ⟨?_, List.Pairwise.nil, ?_, h.footprint, hSep, ?_,
      fun _ ha => ha, fun _ ht => ht⟩
    · intro _ hb; nomatch hb
    · intro _ hb; nomatch hb
    · intro _ hb; nomatch hb
  | cons b rest ih =>
    rcases hSep with ⟨h₁, h₂, ⟨hs₁, hs₂, hDisj, hAddrs, hTags⟩, hB, hRest⟩
    rcases activeTypedFieldMutBorrow_facts hB with
      ⟨hFld, hTok, hCell, hTag⟩
    rcases ih hRest with ⟨hBind, hPair, hOwn, fpR, hR, hDisjR, hSubA, hSubT⟩
    refine ⟨?_, ?_, ?_, fpR, ?_, ?_, ?_, ?_⟩
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · rw [← hs₁]; exact ⟨hFld, hTok⟩
      · rw [← hs₂]; exact hBind b' hb'
    · refine List.pairwise_cons.mpr ⟨fun b' hb' => ⟨?_, ?_⟩, hPair⟩
      · intro hEq
        apply hDisj.1 _ hCell
        have hIn := (hOwn b' hb').1
        rw [← hEq] at hIn
        exact hIn
      · intro hEq
        apply hDisj.2 _ hTag
        have hIn := (hOwn b' hb').2
        rw [← hEq] at hIn
        exact hIn
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact ⟨(hAddrs _).mpr (Or.inl hCell), (hTags _).mpr (Or.inl hTag)⟩
      · exact ⟨(hAddrs _).mpr (Or.inr (hOwn b' hb').1),
          (hTags _).mpr (Or.inr (hOwn b' hb').2)⟩
    · rw [← hs₂]; exact hR
    · intro b' hb'
      rcases List.mem_cons.mp hb' with rfl | hb'
      · exact ⟨fun hIn => hDisj.1 _ hCell (hSubA _ hIn),
          fun hIn => hDisj.2 _ hTag (hSubT _ hIn)⟩
      · exact hDisjR b' hb'
    · intro a ha; exact (hAddrs a).mpr (Or.inr (hSubA a ha))
    · intro t ht; exact (hTags t).mpr (Or.inr (hSubT t ht))

/--
Validity domain shared by a `k`-ary family of sibling field-granular `I-10`
reborrow lenses on aggregate allocation `allocId`.
-/
structure ValidTreeFieldMutBorrowFamily
    (bs : List FieldMutBorrowBinding) (allocId : Local) (m : Memory) :
    Prop where
  valid :
    ∀ b ∈ bs,
      b.rp.allocId = allocId ∧
      ValidTreeFieldMutBorrowLens b.rp b.fieldIdx b.fieldTy b.codec m
  pairwise_field : bs.Pairwise (fun b₁ b₂ => b₁.fieldIdx ≠ b₂.fieldIdx)

theorem ValidTreeFieldMutBorrowFamily.writeBack
    {bs : List FieldMutBorrowBinding} {allocId : Local} {m : Memory}
    {b : FieldMutBorrowBinding} (hb : b ∈ bs)
    (hValid : ValidTreeFieldMutBorrowFamily bs allocId m) (a : b.α) :
    ValidTreeFieldMutBorrowFamily bs allocId
      ((treeFieldMemoryPtrMutLens b.rp b.fieldIdx b.codec).writeBack a m) := by
  refine ⟨fun b' hb' => ?_, hValid.pairwise_field⟩
  rcases hValid.valid b hb with ⟨hAllocB, hValB⟩
  rcases hValid.valid b' hb' with ⟨hAllocB', hValB'⟩
  refine ⟨hAllocB', ?_⟩
  by_cases hEq : b'.fieldIdx = b.fieldIdx
  · have hSame : b' = b :=
      eq_of_pairwise_ne_of_mem hValid.pairwise_field hb' hb hEq
    subst hSame
    exact
      (treeFieldMemoryPtrMutLens_lawful b'.rp b'.fieldIdx b'.fieldTy
        b'.codec).valid_writeBack a m hValB'
  · have hPair :
        ValidTreeFieldMutBorrowLensPair
          b.rp b'.rp b.fieldIdx b'.fieldIdx b.fieldTy b'.fieldTy
          b.codec b'.codec m :=
      ⟨hValB, hValB', hAllocB.trans hAllocB'.symm, Ne.symm hEq⟩
    exact
      ((treeFieldMemoryPtrMutLens_independent_of_ne_field
        b.rp b'.rp b.fieldIdx b'.fieldIdx b.fieldTy b'.fieldTy
        b.codec b'.codec).valid_writeBack_left a m hPair).valid_right

theorem treeFieldMemoryPtrMutLens_lawful_family
    {bs : List FieldMutBorrowBinding} {allocId : Local}
    {b : FieldMutBorrowBinding} (hb : b ∈ bs) :
    LawfulMutLens (treeFieldMemoryPtrMutLens b.rp b.fieldIdx b.codec)
      (ValidTreeFieldMutBorrowFamily bs allocId) where
  valid_writeBack a _ hm := hm.writeBack hb a
  readView_writeBack a m hm :=
    (treeFieldMemoryPtrMutLens_lawful b.rp b.fieldIdx b.fieldTy
      b.codec).readView_writeBack a m (hm.valid b hb).2
  writeBack_readView m hm :=
    (treeFieldMemoryPtrMutLens_lawful b.rp b.fieldIdx b.fieldTy
      b.codec).writeBack_readView m (hm.valid b hb).2
  writeBack_writeBack a₁ a₂ m hm :=
    (treeFieldMemoryPtrMutLens_lawful b.rp b.fieldIdx b.fieldTy
      b.codec).writeBack_writeBack a₁ a₂ m (hm.valid b hb).2

theorem treeFieldMemoryPtrMutLens_independent_family
    {bs : List FieldMutBorrowBinding} {allocId : Local}
    {b₁ b₂ : FieldMutBorrowBinding}
    (hb₁ : b₁ ∈ bs) (hb₂ : b₂ ∈ bs) (hNe : b₁.fieldIdx ≠ b₂.fieldIdx) :
    IndependentLenses
      (treeFieldMemoryPtrMutLens b₁.rp b₁.fieldIdx b₁.codec)
      (treeFieldMemoryPtrMutLens b₂.rp b₂.fieldIdx b₂.codec)
      (ValidTreeFieldMutBorrowFamily bs allocId) := by
  have hPair :=
    treeFieldMemoryPtrMutLens_independent_of_ne_field
      b₁.rp b₂.rp b₁.fieldIdx b₂.fieldIdx b₁.fieldTy b₂.fieldTy
      b₁.codec b₂.codec
  have toPair :
      ∀ m, ValidTreeFieldMutBorrowFamily bs allocId m →
        ValidTreeFieldMutBorrowLensPair
          b₁.rp b₂.rp b₁.fieldIdx b₂.fieldIdx b₁.fieldTy b₂.fieldTy
          b₁.codec b₂.codec m :=
    fun m hm =>
      ⟨(hm.valid b₁ hb₁).2, (hm.valid b₂ hb₂).2,
        (hm.valid b₁ hb₁).1.trans (hm.valid b₂ hb₂).1.symm, hNe⟩
  exact {
    valid_writeBack_left := fun a m hm => hm.writeBack hb₁ a
    valid_writeBack_right := fun a m hm => hm.writeBack hb₂ a
    readView_right_of_writeBack_left := fun a m hm =>
      hPair.readView_right_of_writeBack_left a m (toPair m hm)
    readView_left_of_writeBack_right := fun a m hm =>
      hPair.readView_left_of_writeBack_right a m (toPair m hm)
    writeBack_comm := fun a a' m hm => hPair.writeBack_comm a a' m (toPair m hm)
  }

/--
`k`-ary field-granular `I-10` separation-to-lens bridge: a `k`-ary separating
conjunction of `ActiveTypedFieldMutBorrow` bindings on the same aggregate
allocation `allocId` automatically has pairwise distinct field indices and
yields a `ValidTreeFieldMutBorrowFamily` in which every
`treeFieldMemoryPtrMutLens` is lawful and every pair of distinct indices is
independent.
-/
theorem sepConjFieldBindings_entails_independentTreeFieldLensFamily
    {bs : List FieldMutBorrowBinding} {allocId : Local}
    {R : SepProp} {m : Memory}
    (hSep : SepProp.holdsIn (sepConjFieldBindings bs R) m)
    (hAlloc : ∀ b ∈ bs, b.rp.allocId = allocId)
    (hExcl :
      ∀ b ∈ bs, TreeFieldExclusiveBorrow b.rp b.fieldIdx b.fieldTy m) :
    ValidTreeFieldMutBorrowFamily bs allocId m ∧
    (∀ (i : Nat) (hi : i < bs.length),
      LawfulMutLens
        (treeFieldMemoryPtrMutLens bs[i].rp bs[i].fieldIdx bs[i].codec)
        (ValidTreeFieldMutBorrowFamily bs allocId)) ∧
    (∀ (i j : Nat) (hi : i < bs.length) (hj : j < bs.length), i ≠ j →
      IndependentLenses
        (treeFieldMemoryPtrMutLens bs[i].rp bs[i].fieldIdx bs[i].codec)
        (treeFieldMemoryPtrMutLens bs[j].rp bs[j].fieldIdx bs[j].codec)
        (ValidTreeFieldMutBorrowFamily bs allocId)) := by
  rcases hSep with ⟨fp, hSep⟩
  rcases sepConjFieldBindings_split hSep with ⟨hBind, hPair, _, _⟩
  have hPairField :
      bs.Pairwise (fun b₁ b₂ => b₁.fieldIdx ≠ b₂.fieldIdx) := by
    refine List.Pairwise.imp_of_mem ?_ hPair
    intro b₁ b₂ hb₁ hb₂ hNe hEqF
    apply hNe.1
    show (b₁.rp.allocId, b₁.fieldIdx) = (b₂.rp.allocId, b₂.fieldIdx)
    rw [hAlloc b₁ hb₁, hAlloc b₂ hb₂, hEqF]
  have hValid : ValidTreeFieldMutBorrowFamily bs allocId m :=
    ⟨fun b hb => ⟨hAlloc b hb, ⟨⟨⟨b.val, (hBind b hb).1⟩⟩, hExcl b hb⟩⟩,
      hPairField⟩
  refine ⟨hValid, fun i hi => treeFieldMemoryPtrMutLens_lawful_family
    (List.getElem_mem hi), fun i j hi hj hNe => ?_⟩
  refine treeFieldMemoryPtrMutLens_independent_family
    (List.getElem_mem hi) (List.getElem_mem hj) ?_
  rcases Nat.lt_or_gt_of_ne hNe with hLt | hGt
  · exact List.pairwise_iff_getElem.mp hPairField i j hi hj hLt
  · exact Ne.symm (List.pairwise_iff_getElem.mp hPairField j i hj hi hGt)

/--
Homogeneous `List` form of the `k`-ary field-granular `I-10` lens family bridge
yielding `PairwiseIndependentLenses`.
-/
theorem sepConjFieldBindings_entails_pairwiseIndependentTreeFieldLenses
    {α : Type} {codec : ValueCodec α} {fieldTy : Ty} {allocId : Local}
    {ptrs : List (RawPtrVal × FieldIdx × α)} {R : SepProp} {m : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConjFieldBindings
          (ptrs.map fun p =>
            FieldMutBorrowBinding.bind p.1 p.2.1 fieldTy codec p.2.2) R)
        m)
    (hAlloc : ∀ p ∈ ptrs, p.1.allocId = allocId)
    (hExcl :
      ∀ p ∈ ptrs, TreeFieldExclusiveBorrow p.1 p.2.1 fieldTy m) :
    ValidTreeFieldMutBorrowFamily
      (ptrs.map fun p =>
        FieldMutBorrowBinding.bind p.1 p.2.1 fieldTy codec p.2.2)
      allocId m ∧
    PairwiseIndependentLenses
      (ValidTreeFieldMutBorrowFamily
        (ptrs.map fun p =>
          FieldMutBorrowBinding.bind p.1 p.2.1 fieldTy codec p.2.2)
        allocId)
      (ptrs.map fun p => treeFieldMemoryPtrMutLens p.1 p.2.1 codec) := by
  let bs :=
    ptrs.map fun p => FieldMutBorrowBinding.bind p.1 p.2.1 fieldTy codec p.2.2
  have hAlloc' : ∀ b ∈ bs, b.rp.allocId = allocId := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
    exact hAlloc p hp
  have hExcl' :
      ∀ b ∈ bs, TreeFieldExclusiveBorrow b.rp b.fieldIdx b.fieldTy m := by
    intro b hb
    rcases List.mem_map.mp hb with ⟨p, hp, rfl⟩
    exact hExcl p hp
  rcases sepConjFieldBindings_entails_independentTreeFieldLensFamily
      hSep hAlloc' hExcl' with
    ⟨hValid, _, _⟩
  refine ⟨hValid, ?_⟩
  have hPairPtr :
      ptrs.Pairwise (fun p₁ p₂ => p₁.2.1 ≠ p₂.2.1) := by
    have h := hValid.pairwise_field
    rw [List.pairwise_map] at h
    exact h
  have hSuffix :
      ∀ sfx : List (RawPtrVal × FieldIdx × α),
        (∀ p ∈ sfx, p ∈ ptrs) →
        sfx.Pairwise (fun p₁ p₂ => p₁.2.1 ≠ p₂.2.1) →
        PairwiseIndependentLenses (ValidTreeFieldMutBorrowFamily bs allocId)
          (sfx.map fun p => treeFieldMemoryPtrMutLens p.1 p.2.1 codec) := by
    intro sfx
    induction sfx with
    | nil => intro _ _; exact .nil
    | cons p rest ih =>
      intro hSub hPairSfx
      rcases List.pairwise_cons.mp hPairSfx with ⟨hHead, hTail⟩
      have hp :
          FieldMutBorrowBinding.bind p.1 p.2.1 fieldTy codec p.2.2 ∈ bs :=
        List.mem_map.mpr ⟨p, hSub p (List.Mem.head rest), rfl⟩
      refine .cons (treeFieldMemoryPtrMutLens_lawful_family hp) ?_
        (ih (fun q hq => hSub q (List.Mem.tail p hq)) hTail)
      intro L hL
      rcases List.mem_map.mp hL with ⟨q, hq, rfl⟩
      have hq' :
          FieldMutBorrowBinding.bind q.1 q.2.1 fieldTy codec q.2.2 ∈ bs :=
        List.mem_map.mpr ⟨q, hSub q (List.Mem.tail p hq), rfl⟩
      exact treeFieldMemoryPtrMutLens_independent_family hp hq' (hHead q hq)
  exact hSuffix ptrs (fun _ h => h) hPairPtr

/--
MIR-level sub-place `AgreeOnFootprint` bridge: when
`SubplaceLensFramePreserved subplaceOf entries₀ m₀ m` holds, `m₀` and `m`
satisfy `AgreeOnFootprint fp m₀ m` for any footprint `fp` whose cells either
avoid the tracked allocations or sit at non-root field offsets (`offset ≠ 0`)
outside the tracked field indices.
-/
theorem agreeOnFootprint_of_subplaceLensFramePreserved
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {entries₀ : List (RawPtrVal × Value)} {m₀ m : Memory}
    (hPres : SubplaceLensFramePreserved subplaceOf entries₀ m₀ m)
    (hStack₀ : m₀.callStack = []) (hStack : m.callStack = [])
    {fp : Footprint}
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp.addrs →
        (∀ e ∈ entries₀, allocId ≠ e.1.allocId) ∨
        (offset ≠ 0 ∧
          ∀ e ∈ entries₀, e.1.allocId = allocId →
            ∃ f ty, subplaceOf e.1 = .field f ty ∧ f ≠ offset))
    (hTags : ∀ tag ∈ fp.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag) :
    AgreeOnFootprint fp m₀ m := by
  refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
  · rw [memoryLocals_of_callStack_nil hStack₀,
      memoryLocals_of_callStack_nil hStack]
    rcases hAddrs allocId offset hIn with hOutAlloc | ⟨hNeZero, hOutFld⟩
    · unfold readAllocAt?
      rw [hPres.locals_unchanged_outside allocId hOutAlloc]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hNeZero
      rw [readAllocAt_succ_eq_readFieldAt, readAllocAt_succ_eq_readFieldAt]
      exact (hPres.fields_unchanged_outside allocId (k + 1) hOutFld).symm
  · exact (hPres.borrows_unchanged_outside tag (hTags tag hIn)).symm

/--
`SupportedBy R_frame fp_frame` heap predicates disjoint from the tracked
sub-place footprint survive `SubplaceLensFramePreserved`.
-/
theorem supportedBy_of_subplaceLensFramePreserved
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {entries₀ : List (RawPtrVal × Value)} {m₀ m : Memory}
    (hPres : SubplaceLensFramePreserved subplaceOf entries₀ m₀ m)
    (hStack₀ : m₀.callStack = []) (hStack : m.callStack = [])
    {R_frame : HeapPred} {fp_frame : Footprint}
    (hSupp : SupportedBy R_frame fp_frame)
    (hAddrs :
      ∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
        (∀ e ∈ entries₀, allocId ≠ e.1.allocId) ∨
        (offset ≠ 0 ∧
          ∀ e ∈ entries₀, e.1.allocId = allocId →
            ∃ f ty, subplaceOf e.1 = .field f ty ∧ f ≠ offset))
    (hTags : ∀ tag ∈ fp_frame.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag)
    (hR : R_frame m₀) :
    R_frame m :=
  hSupp m₀ m
    (agreeOnFootprint_of_subplaceLensFramePreserved hPres hStack₀ hStack
      hAddrs hTags)
    hR

/--
Framed bridge from `mirWpConverges_of_sepSubplaceLenses` to
`StatefulVerificationResult`: conjoins any `SupportedBy R_frame fp_frame` heap
predicate avoiding the sub-place lens footprint onto the claim via
`frameStatefulClaim`.
-/
theorem verifyStatefulMir_of_sepSubplaceLenses_supportedFrame
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (R_frame : HeapPred) (fp_frame : Footprint)
    (hSupp : SupportedBy R_frame fp_frame)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (subplaceOf : RawPtrVal → BorrowSubplace)
          (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepSubplaceLensStateInv subplaceOf env₀.length entries₀ m₀ ∧
          (∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
            (∀ e ∈ entries₀, allocId ≠ e.1.allocId) ∨
            (offset ≠ 0 ∧
              ∀ e ∈ entries₀, e.1.allocId = allocId →
                ∃ f ty, subplaceOf e.1 = .field f ty ∧ f ≠ offset)) ∧
          (∀ tag ∈ fp_frame.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag) ∧
          ∀ m_final : Memory,
            SepSubplaceLensStateInv subplaceOf env₀.length entries' m_final →
            SubplaceLensFramePreserved subplaceOf entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    StatefulVerificationResult
      (frameStatefulClaim { body := body, pre := Pre, post := Post } R_frame) := by
  refine verifyStatefulMirNoPanic_of_wpConverges _ ?_
  intro args m₀ ⟨hPre, hR₀⟩
  rcases hStep args m₀ hPre with
    ⟨subplaceOf, entries₀, entries', retVal, hBlock, hInv₀, hAddrs, hTags,
      hPost⟩
  exact mirWpConverges_of_sepSubplaceLenses hBlock hInv₀
    (fun m_final hInvF hPresF =>
      ⟨hPost m_final hInvF hPresF,
        supportedBy_of_subplaceLensFramePreserved hPresF hInv₀.callStack_nil
          hInvF.callStack_nil hSupp hAddrs hTags hR₀⟩)

/--
Framed bridge from `mirWpConverges_of_sepSubplaceLenses` to
`TotalVerificationResult` via `frameTotalClaim`.
-/
theorem verifyTotalMir_of_sepSubplaceLenses_supportedFrame
    (body : CapturedMir)
    (Pre : List Value → Memory → Prop)
    (Post : List Value → Memory → Value → Memory → Prop)
    (R_frame : HeapPred) (fp_frame : Footprint)
    (hSupp : SupportedBy R_frame fp_frame)
    (hStep :
      ∀ args m₀,
        Pre args m₀ →
        ∃ (subplaceOf : RawPtrVal → BorrowSubplace)
          (entries₀ entries' : List (RawPtrVal × Value)) (retVal : Value),
          let env₀ := (initMachineState body args).frame.locals
          LiftLensBlock body 0 env₀ entries₀ retVal entries' ∧
          SepSubplaceLensStateInv subplaceOf env₀.length entries₀ m₀ ∧
          (∀ allocId offset, (allocId, offset) ∈ fp_frame.addrs →
            (∀ e ∈ entries₀, allocId ≠ e.1.allocId) ∨
            (offset ≠ 0 ∧
              ∀ e ∈ entries₀, e.1.allocId = allocId →
                ∃ f ty, subplaceOf e.1 = .field f ty ∧ f ≠ offset)) ∧
          (∀ tag ∈ fp_frame.tags, ∀ e ∈ entries₀, tag ≠ e.1.tag) ∧
          ∀ m_final : Memory,
            SepSubplaceLensStateInv subplaceOf env₀.length entries' m_final →
            SubplaceLensFramePreserved subplaceOf entries₀ m₀ m_final →
            Post args m₀ retVal m_final) :
    TotalVerificationResult
      (frameTotalClaim { body := body, pre := Pre, post := Post } R_frame) := by
  refine verifyTotalMir_of_wpConverges _ ?_
  intro args m₀ ⟨hPre, hR₀⟩
  rcases hStep args m₀ hPre with
    ⟨subplaceOf, entries₀, entries', retVal, hBlock, hInv₀, hAddrs, hTags,
      hPost⟩
  exact mirWpConverges_of_sepSubplaceLenses hBlock hInv₀
    (fun m_final hInvF hPresF =>
      ⟨hPost m_final hInvF hPresF,
        supportedBy_of_subplaceLensFramePreserved hPresF hInv₀.callStack_nil
          hInvF.callStack_nil hSupp hAddrs hTags hR₀⟩)

/-! ### Unified Sub-Place `MutLens` View-Passing (`subplaceTreeMutLens`) -/

/--
Unified `I-10`-aware mutable lens for a tracked pointer `rp` under `subplaceOf`:
dispatches to `treeMemoryPtrMutLens rp codec` when `subplaceOf rp = .root` and
to `treeFieldMemoryPtrMutLens rp fieldIdx codec` when
`subplaceOf rp = .field fieldIdx fieldTy`.
-/
def subplaceTreeMutLens {α : Type}
    (subplaceOf : RawPtrVal → BorrowSubplace)
    (rp : RawPtrVal) (codec : ValueCodec α) : MutLens Memory α :=
  match subplaceOf rp with
  | .root => treeMemoryPtrMutLens rp codec
  | .field fieldIdx _ => treeFieldMemoryPtrMutLens rp fieldIdx codec

/--
Every lens-state binding `(rp, codec.encode a) ∈ entries` under
`SepSubplaceLensStateInv` equals the `subplaceTreeMutLens` view of memory `m`.
-/
theorem SepSubplaceLensStateInv.subplaceTreeLens_readView {α : Type}
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp : RawPtrVal} {codec : ValueCodec α} {a : α}
    (hInv : SepSubplaceLensStateInv subplaceOf frameLen entries m)
    (hMem : (rp, codec.encode a) ∈ entries) :
    (subplaceTreeMutLens subplaceOf rp codec).readView m = a := by
  have hVal := hInv.entries_valid rp (codec.encode a) hMem
  unfold BorrowSubplace.entryValid at hVal
  rcases hVal with ⟨hOff, _, hRest⟩
  unfold subplaceTreeMutLens
  cases hSub : subplaceOf rp with
  | root =>
    rw [hSub] at hRest
    dsimp only [treeMemoryPtrMutLens]
    apply memoryPtrMutLens_readView_of_readAllocAt
    rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
    unfold readAllocAt?
    rw [hRest.1, hOff]
  | field fieldIdx fieldTy =>
    rw [hSub] at hRest
    dsimp only [treeFieldMemoryPtrMutLens]
    apply rawFieldMutLens_readView_of_readFieldAt
    rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
    exact hRest.1

/--
Every field-reborrow binding `(rp, codec.encode a) ∈ entries` with
`subplaceOf rp = .field fieldIdx fieldTy` under `SepSubplaceLensStateInv`
satisfies `ValidTreeFieldMutBorrowLens` and reads back `a` via
`treeFieldMemoryPtrMutLens`.
-/
theorem SepSubplaceLensStateInv.treeFieldLens_readView {α : Type}
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {frameLen : Nat} {entries : List (RawPtrVal × Value)} {m : Memory}
    {rp : RawPtrVal} {fieldIdx : FieldIdx} {fieldTy : Ty}
    {codec : ValueCodec α} {a : α}
    (hInv : SepSubplaceLensStateInv subplaceOf frameLen entries m)
    (hMem : (rp, codec.encode a) ∈ entries)
    (hSub : subplaceOf rp = .field fieldIdx fieldTy) :
    ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec m ∧
    (treeFieldMemoryPtrMutLens rp fieldIdx codec).readView m = a := by
  have hVal := hInv.entries_valid rp (codec.encode a) hMem
  unfold BorrowSubplace.entryValid at hVal
  rcases hVal with ⟨_, _, hRest⟩
  rw [hSub] at hRest
  have hFld :
      readFieldAt? (memoryLocals m) rp.allocId fieldIdx =
        some (codec.encode a) := by
    rw [memoryLocals_of_callStack_nil hInv.callStack_nil]
    exact hRest.1
  exact ⟨⟨⟨⟨a, hFld⟩⟩, hRest.2⟩,
    rawFieldMutLens_readView_of_readFieldAt hFld⟩

/--
Read-side alias erasure for field-granular reborrows (`&mut s.fieldIdx`): under
`SepSubplaceLensStateInv`, a lifted deref read `copy/move (*p)` on a pointer
`rp` with `subplaceOf rp = .field fieldIdx fieldTy` leaves the `I-10` borrow
table unchanged (`stepTreeBorrowHierarchyAccess? m rp false = .some m`),
satisfies `ValidTreeFieldMutBorrowLens`, and returns
`codec.encode ((treeFieldMemoryPtrMutLens rp fieldIdx codec).readView m)`.
-/
theorem LiftDerefRead.evalOperand_eq_treeFieldLens_readView_and_step
    {α : Type} {subplaceOf : RawPtrVal → BorrowSubplace}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {m : Memory} {codec : ValueCodec α} {a : α}
    (h : LiftDerefRead env entries op (codec.encode a) env')
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries m)
    (layouts : LayoutTable) :
    ∃ rp : RawPtrVal,
      (rp, codec.encode a) ∈ entries ∧
      (subplaceTreeMutLens subplaceOf rp codec).readView m = a ∧
      evalOperand env op m.borrows m.globals layouts m.callerLocals =
        .ok
          (codec.encode
            ((subplaceTreeMutLens subplaceOf rp codec).readView m))
          env' ∧
      ∀ fieldIdx fieldTy,
        subplaceOf rp = .field fieldIdx fieldTy →
        stepTreeBorrowHierarchyAccess? m rp false = .some m ∧
        ValidTreeFieldMutBorrowLens rp fieldIdx fieldTy codec m ∧
        (treeFieldMemoryPtrMutLens rp fieldIdx codec).readView m = a := by
  have hEval := (h.evalOperand_and_freeze_eq_subplace hInv layouts).1
  cases h with
  | @copy_deref _ rp _ hGetPtr hLook =>
    have hMem := lookupLensVal?_mem hLook
    have hView := hInv.subplaceTreeLens_readView hMem
    refine ⟨rp, hMem, hView, by rw [hView]; exact hEval,
      fun fieldIdx fieldTy hSub => ?_⟩
    rcases hInv.treeFieldLens_readView hMem hSub with ⟨hValid, hFView⟩
    exact ⟨stepTreeBorrowHierarchyAccess_read_eq_some_self_of_treeField
      hValid.exclusive, hValid, hFView⟩
  | @move_deref _ rp _ hGetPtr hLook =>
    have hMem := lookupLensVal?_mem hLook
    have hView := hInv.subplaceTreeLens_readView hMem
    refine ⟨rp, hMem, hView, by rw [hView]; exact hEval,
      fun fieldIdx fieldTy hSub => ?_⟩
    rcases hInv.treeFieldLens_readView hMem hSub with ⟨hValid, hFView⟩
    exact ⟨stepTreeBorrowHierarchyAccess_read_eq_some_self_of_treeField
      hValid.exclusive, hValid, hFView⟩

/--
Statement-level sub-place `MutLens` state-passing theorem with frame
preservation (`LiftLensStmt.evalStmt_subplaceTreeLens_views_and_frame`): every
lifted statement steps `evalStmt` to a post-state `m'` satisfying
`SepSubplaceLensStateInv`, `SubplaceLensFramePreserved`, and
`(subplaceTreeMutLens subplaceOf rp codec).readView m' = a` for every
`(rp, codec.encode a) ∈ entries'`.
-/
theorem LiftLensStmt.evalStmt_subplaceTreeLens_views_and_frame
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries₀ entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement} {s : MachineState} {m₀ : Memory}
    (hStmt : LiftLensStmt localDecls layouts env entries stmt env' entries')
    (hEnv : s.frame.locals = env)
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries s.memory)
    (hFrame : SubplaceLensFramePreserved subplaceOf entries₀ m₀ s.memory)
    (hKeys : entries.map Prod.fst = entries₀.map Prod.fst) :
    ∃ m' : Memory,
      evalStmt s stmt localDecls layouts =
        MirStepNode.step (advanceStmt s env' m') ∧
      env'.length = env.length ∧
      SepSubplaceLensStateInv subplaceOf env'.length entries' m' ∧
      SubplaceLensFramePreserved subplaceOf entries₀ m₀ m' ∧
      entries'.map Prod.fst = entries₀.map Prod.fst ∧
      ∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
        (rp, codec.encode a) ∈ entries' →
        (subplaceTreeMutLens subplaceOf rp codec).readView m' = a := by
  rcases hStmt.evalStmt_step_subplace hEnv hInv hFrame hKeys with
    ⟨m', hEval, hLen, hInv', hFrame', hKeys'⟩
  exact ⟨m', hEval, hLen, hInv', hFrame', hKeys',
    fun _ _ _ hMem => hInv'.subplaceTreeLens_readView hMem⟩

/--
Multi-statement sub-place `MutLens` state-passing theorem
(`LiftLensStmts.mirWpConverges_subplaceTreeLens_views`).
-/
theorem LiftLensStmts.mirWpConverges_subplaceTreeLens_views
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    {prefixStmts stmts : List Statement}
    {env env' : PureEnv}
    {entries₀ entries entries' : List (RawPtrVal × Value)}
    {m₀ m : Memory} {Φ : MirOutcome → Prop}
    (hPhase : isRuntimeMirPhase body.phase = true)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hStmts :
      LiftLensStmts body.localDecls body.layouts
        env entries stmts env' entries')
    (hBbStmts : bb.statements = prefixStmts ++ stmts)
    (hInv : SepSubplaceLensStateInv subplaceOf env.length entries m)
    (hFrame : SubplaceLensFramePreserved subplaceOf entries₀ m₀ m)
    (hKeys : entries.map Prod.fst = entries₀.map Prod.fst)
    (hCont :
      ∀ m' : Memory,
        SepSubplaceLensStateInv subplaceOf env'.length entries' m' →
        SubplaceLensFramePreserved subplaceOf entries₀ m₀ m' →
        entries'.map Prod.fst = entries₀.map Prod.fst →
        (∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
          (rp, codec.encode a) ∈ entries' →
          (subplaceTreeMutLens subplaceOf rp codec).readView m' = a) →
        MirWpConverges body
          { frame := {
              blockIdx := bbIdx
              stmtIdx := bb.statements.length
              locals := env'
            }
            memory := m' }
          Φ) :
    MirWpConverges body
      { frame := {
          blockIdx := bbIdx
          stmtIdx := prefixStmts.length
          locals := env
        }
        memory := m }
      Φ :=
  mirWpConverges_of_liftLensStmts_subplace hPhase hBb hStmts prefixStmts m₀ m Φ
    hBbStmts hInv hFrame hKeys (fun m' hInv' hFrame' hKeys' =>
      hCont m' hInv' hFrame' hKeys'
        (fun _ _ _ hMem => hInv'.subplaceTreeLens_readView hMem))

/--
Whole-CFG sub-place `MutLens` state-passing theorem
(`mirWpConverges_of_sepSubplaceLenses_treeLens_views`): composes `LiftLensBlock`
over `SepSubplaceLensStateInv` so that the final memory `m_final` satisfies
`(subplaceTreeMutLens subplaceOf rp codec).readView m_final = a` for every final
binding `(rp, codec.encode a) ∈ entries'` alongside `SepSubplaceLensStateInv`
and `SubplaceLensFramePreserved`.
-/
theorem mirWpConverges_of_sepSubplaceLenses_treeLens_views
    {subplaceOf : RawPtrVal → BorrowSubplace}
    {body : CapturedMir} {bbIdx : BasicBlockIdx}
    {env : PureEnv} {entries₀ entries' : List (RawPtrVal × Value)}
    {retVal : Value} {m₀ : Memory} {Φ : MirOutcome → Prop}
    (hBlock : LiftLensBlock body bbIdx env entries₀ retVal entries')
    (hInv₀ : SepSubplaceLensStateInv subplaceOf env.length entries₀ m₀)
    (hPost :
      ∀ m_final : Memory,
        SepSubplaceLensStateInv subplaceOf env.length entries' m_final →
        SubplaceLensFramePreserved subplaceOf entries₀ m₀ m_final →
        (∀ {α : Type} (rp : RawPtrVal) (codec : ValueCodec α) (a : α),
          (rp, codec.encode a) ∈ entries' →
          (subplaceTreeMutLens subplaceOf rp codec).readView m_final = a) →
        Φ (.normal (retVal, m_final))) :
    MirWpConverges body
      { frame := { blockIdx := bbIdx, stmtIdx := 0, locals := env }
        memory := m₀ }
      Φ :=
  mirWpConverges_of_sepSubplaceLenses hBlock hInv₀ (fun m_final hInvF hPresF =>
    hPost m_final hInvF hPresF
      (fun _ _ _ hMem => hInvF.subplaceTreeLens_readView hMem))

/-! ## 3. Concrete Witnesses: `add_assign` and `swap_u32` -/

def unitLayout : TypeLayout :=
  { size := { bytes := 0 }
    align := { bytes := 1 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def u32Layout : TypeLayout :=
  { size := { bytes := 4 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def u32MutPtrLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .scalar (.initialized (.pointer 0) { start := 0, end_ := 0 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

theorem lookupLensVal?_singleton_self (rp : RawPtrVal) (v : Value) :
    lookupLensVal? [(rp, v)] rp = .some v := by
  simp [lookupLensVal?]

theorem updateLensVal_singleton_self (rp : RawPtrVal) (v v' : Value) :
    updateLensVal [(rp, v)] rp v' = [(rp, v')] := by
  simp [updateLensVal]

theorem scalarNat_not_aggregate (sz a : Nat) (elems : List Value) :
    (ValueCodec.scalarNat sz).encode a ≠ .aggregate 0 elems := by
  intro hEq
  unfold ValueCodec.encode ValueCodec.scalarNat at hEq
  dsimp only at hEq
  injection hEq

/-! ### `add_assign(x: &mut u32, d: u32)` -/

/--
`Runtime(PostCleanup)` MIR of
`pub fn add_assign(x: &mut u32, d: u32) { *x += d; }` as rustc builds it without
overflow checks: the compound assignment reads and
writes the pointee in one statement, `(*_1) = Add(copy (*_1), copy _2)`, and the
unit return value is stored by `_0 = const ()`.
-/
def add_assign : CapturedMir where
  defPath := "demo::add_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 },
      debugName := some "x" },
    { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "d" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.binaryOp .add
              (.copy { local_ := 1, projection := [.deref] })
              (.copy { local_ := 2, projection := [] })),
          span := "add_assign" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "add_assign" }
      ],
      terminator := { kind := .return_, span := "add_assign" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32MutPtrLayout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout]
  }
  allocations := []

/--
Precondition of `add_assign`: `x` carries `x_ptr`, which owns an active,
Tree-Borrows-exclusive `u32` cell holding `x_old`, separated from an arbitrary
footprint-local frame `R_frame`.
-/
def addAssignPre (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩] ∧
    WfSingleMutBorrow 3 x_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) x_old) R_frame)
      m₀

/-- Postcondition of `add_assign`: unit result, wrapped sum behind `x_ptr`. -/
def addAssignPost (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4)
          (wrapScalarBits (x_old + d_val) (scalarModulus 4)))
        R_frame)
      m_final

/-- The pure lens-state derivation of the whole `add_assign` body. -/
theorem add_assign_lift (x_ptr : RawPtrVal) (x_old d_val : Nat) :
    LiftLensBlock add_assign 0
      (initMachineState add_assign
        [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      .unit
      (updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr
        (.scalar ⟨wrapScalarBits (Nat.add x_old d_val) (scalarModulus 4), 4⟩)) := by
  unfold initMachineState
  dsimp [add_assign, initLocalsAux]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨d_val, 4⟩)])
    rfl rfl rfl ?_ rfl
  refine .cons (.derefWrite (.mk (.binaryOp_add (by decide)
      (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
      (.pure (.copy_local rfl))) rfl (lookupLensVal?_singleton_self _ _))) ?_
  refine .cons (.pureAssign (.mk (.use_pure .const_zeroSized rfl) rfl
      (fun h => nomatch h) rfl)) ?_
  exact .nil

/--
Fuel-free convergence of `add_assign` from every memory satisfying the
separation-logic precondition, proved through `mirWpConverges_of_sepLenses`:
no step of the proof inspects a `Memory` field.
-/
theorem add_assign_mirWpConverges
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : addAssignPre x_ptr x_old d_val R_frame args m₀) :
    MirWpConverges add_assign (initMachineStateWithMemory add_assign args m₀)
      (mirNormalPost (addAssignPost x_ptr x_old d_val R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (add_assign_lift x_ptr x_old d_val)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 4)⟩

theorem add_assign_verified
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := add_assign,
      pre := addAssignPre x_ptr x_old d_val R_frame,
      post := addAssignPost x_ptr x_old d_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)

theorem add_assign_total
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := add_assign,
      pre := addAssignPre x_ptr x_old d_val R_frame,
      post := addAssignPost x_ptr x_old d_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)

/-! ### `add_assign` with Function-Entry Retags (`LiftRetag`) -/

/--
`add_assign` as rustc emits it under `-Zmir-emit-retag` (the Miri
configuration): `Retag([fn entry] _1)` attaches a function-entry protector to
`x`'s borrow before the compound assignment. Anneal's capture does not request
retag statements, so this body exists to exercise `LiftRetag` and the
protected-write paths of `LiftDerefWrite` end to end.
-/
def add_assign_retag : CapturedMir :=
  { add_assign with
    defPath := "demo::add_assign_retag"
    basicBlocks := [
      { statements := [
          { kind := .retag .fnEntry { local_ := 1, projection := [] },
            span := "add_assign_retag" },
          { kind := .assign { local_ := 1, projection := [.deref] }
              (.binaryOp .add
                (.copy { local_ := 1, projection := [.deref] })
                (.copy { local_ := 2, projection := [] })),
            span := "add_assign_retag" },
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.constant
                { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
            span := "add_assign_retag" }
        ],
        terminator := { kind := .return_, span := "add_assign_retag" },
        isCleanup := false
      }
    ] }

theorem add_assign_retag_lift (x_ptr : RawPtrVal) (x_old d_val : Nat) :
    LiftLensBlock add_assign_retag 0
      (initMachineState add_assign_retag
        [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      .unit
      (updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr
        (.scalar ⟨wrapScalarBits (Nat.add x_old d_val) (scalarModulus 4), 4⟩)) := by
  unfold initMachineState
  dsimp [add_assign_retag, add_assign, initLocalsAux]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨d_val, 4⟩)])
    rfl rfl rfl ?_ rfl
  refine .cons (.retag (.mk rfl (lookupLensVal?_singleton_self _ _))) ?_
  refine .cons (.derefWrite (.mk (.binaryOp_add (by decide)
      (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
      (.pure (.copy_local rfl))) rfl (lookupLensVal?_singleton_self _ _))) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit) (.use_pure .const_zeroSized rfl)
      rfl (fun h => nomatch h) rfl)) ?_
  exact .nil

/--
The retagged body satisfies the same contract as `add_assign`: after the
function-entry retag protects `x`'s borrow, the protected write through `x`
raises no protector conflict and the frame is preserved.
-/
theorem add_assign_retag_mirWpConverges
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : addAssignPre x_ptr x_old d_val R_frame args m₀) :
    MirWpConverges add_assign_retag
      (initMachineStateWithMemory add_assign_retag args m₀)
      (mirNormalPost (addAssignPost x_ptr x_old d_val R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (add_assign_retag_lift x_ptr x_old d_val)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 4)⟩

theorem add_assign_retag_verified
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := add_assign_retag,
      pre := addAssignPre x_ptr x_old d_val R_frame,
      post := addAssignPost x_ptr x_old d_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_retag_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)

theorem add_assign_retag_total
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := add_assign_retag,
      pre := addAssignPre x_ptr x_old d_val R_frame,
      post := addAssignPost x_ptr x_old d_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_retag_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)


/-! ### `swap_u32(a: &mut u32, b: &mut u32)` -/

/--
`Runtime(PostCleanup)` MIR of `swap_u32`, whose Rust source is
`fn swap_u32(a: &mut u32, b: &mut u32) { let tmp = *a; *a = *b; *b = tmp; }`.
-/
def swap_u32 : CapturedMir where
  defPath := "demo::swap_u32"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 },
      debugName := some "a" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 },
      debugName := some "b" },
    { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "tmp" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 3, span := "swap_u32" },
        { kind := .assign { local_ := 3, projection := [] }
            (.use (.copy { local_ := 1, projection := [.deref] })),
          span := "swap_u32" },
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.use (.copy { local_ := 2, projection := [.deref] })),
          span := "swap_u32" },
        { kind := .assign { local_ := 2, projection := [.deref] }
            (.use (.copy { local_ := 3, projection := [] })),
          span := "swap_u32" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "swap_u32" },
        { kind := .storageDead 3, span := "swap_u32" }
      ],
      terminator := { kind := .return_, span := "swap_u32" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32MutPtrLayout, mode := .direct },
      { layout := u32MutPtrLayout, mode := .direct }
    ]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout]
  }
  allocations := []

/--
Precondition of `swap_u32`: `a` and `b` carry pointers owning active,
Tree-Borrows-exclusive `u32` cells, separated from each other (which forces
distinct allocations and tags) and from an arbitrary frame `R_frame`.
-/
def swapU32Pre (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr a_ptr.toMirPtr 8, .ptr b_ptr.toMirPtr 8] ∧
    WfSingleMutBorrow 4 a_ptr m₀ ∧
    WfSingleMutBorrow 4 b_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow a_ptr (ValueCodec.scalarNat 4) a_old)
        (sepConj (ActiveTypedMutBorrow b_ptr (ValueCodec.scalarNat 4) b_old)
          R_frame))
      m₀

/-- Postcondition of `swap_u32`: unit result with the two pointees exchanged. -/
def swapU32Post (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow a_ptr (ValueCodec.scalarNat 4) b_old)
        (sepConj (ActiveTypedMutBorrow b_ptr (ValueCodec.scalarNat 4) a_old)
          R_frame))
      m_final

/--
The pure lens-state derivation of the whole `swap_u32` body; pointer
distinctness `a_ptr ≠ b_ptr` (derived from `sepConj` by the callers) is needed
only to resolve the second lens lookup.
-/
theorem swap_u32_lift (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat)
    (hNe : a_ptr ≠ b_ptr) :
    LiftLensBlock swap_u32 0
      (initMachineState swap_u32
        [.ptr a_ptr.toMirPtr 8, .ptr b_ptr.toMirPtr 8]).frame.locals
      [(a_ptr, (ValueCodec.scalarNat 4).encode a_old),
        (b_ptr, (ValueCodec.scalarNat 4).encode b_old)]
      .unit
      (updateLensVal
        (updateLensVal
          [(a_ptr, (ValueCodec.scalarNat 4).encode a_old),
            (b_ptr, (ValueCodec.scalarNat 4).encode b_old)]
          a_ptr (.scalar ⟨b_old, 4⟩))
        b_ptr (.scalar ⟨a_old, 4⟩)) := by
  unfold initMachineState
  dsimp [swap_u32, initLocalsAux]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr a_ptr.toMirPtr 8),
      .init (.ptr b_ptr.toMirPtr 8), .dead])
    rfl rfl rfl ?_ rfl
  refine .cons (.storageLive (.mk (oldSlot := .dead)
      (env' := [.uninit, .init (.ptr a_ptr.toMirPtr 8),
        .init (.ptr b_ptr.toMirPtr 8), .uninit]) rfl rfl)) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (env₂ := [.uninit, .init (.ptr a_ptr.toMirPtr 8),
        .init (.ptr b_ptr.toMirPtr 8), .init (.scalar ⟨a_old, 4⟩)])
      (.use_deref (.copy_deref rfl (by simp [lookupLensVal?]; rfl)) rfl)
      rfl (fun h => nomatch h) rfl)) ?_
  refine .cons (.derefWrite (.mk
      (.use_deref (.copy_deref rfl (by simp [lookupLensVal?, hNe]; rfl)) rfl)
      rfl (by simp [lookupLensVal?]; rfl))) ?_
  refine .cons (.derefWrite (.mk (.use_pure (.copy_local rfl) rfl) rfl
      (by simp [lookupLensVal?, updateLensVal, hNe]; rfl))) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (env₂ := [.init .unit, .init (.ptr a_ptr.toMirPtr 8),
        .init (.ptr b_ptr.toMirPtr 8), .init (.scalar ⟨a_old, 4⟩)])
      (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
  refine .cons (.storageDead (.mk (oldSlot := .init (.scalar ⟨a_old, 4⟩))
      (env' := [.init .unit, .init (.ptr a_ptr.toMirPtr 8),
        .init (.ptr b_ptr.toMirPtr 8), .dead]) rfl rfl)) ?_
  exact .nil

/--
Fuel-free convergence of `swap_u32` from every memory satisfying the
separation-logic precondition, proved through `mirWpConverges_of_sepLenses`.
-/
theorem swap_u32_mirWpConverges
    (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : swapU32Pre a_ptr b_ptr a_old b_old R_frame args m₀) :
    MirWpConverges swap_u32 (initMachineStateWithMemory swap_u32 args m₀)
      (mirNormalPost (swapU32Post a_ptr b_ptr a_old b_old R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf_a, hWf_b, hSep⟩
  have hNe : a_ptr ≠ b_ptr := pairwise_disjoint_of_sepConj_two_ne hSep
  refine mirWpConverges_of_sepLenses (swap_u32_lift a_ptr b_ptr a_old b_old hNe)
    (sepLensStateInv_of_sepConj_two hSep hWf_a hWf_b)
    (fun m_final hInv hPres => ?_)
  have hEq :
      updateLensVal
          (updateLensVal
            [(a_ptr, (ValueCodec.scalarNat 4).encode a_old),
              (b_ptr, (ValueCodec.scalarNat 4).encode b_old)]
            a_ptr (.scalar ⟨b_old, 4⟩))
          b_ptr (.scalar ⟨a_old, 4⟩) =
        [(a_ptr, (ValueCodec.scalarNat 4).encode b_old),
          (b_ptr, (ValueCodec.scalarNat 4).encode a_old)] := by
    simp [updateLensVal, ValueCodec.scalarNat, hNe]
  rw [hEq] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_two a_ptr b_ptr
    (ValueCodec.scalarNat 4) (ValueCodec.scalarNat 4) a_old b_old b_old a_old
    hSep hInv hWf_a hWf_b hPres h_R
    (scalarNat_not_aggregate 4) (scalarNat_not_aggregate 4)⟩

theorem swap_u32_verified
    (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := swap_u32,
      pre := swapU32Pre a_ptr b_ptr a_old b_old R_frame,
      post := swapU32Post a_ptr b_ptr a_old b_old R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    swap_u32_mirWpConverges a_ptr b_ptr a_old b_old R_frame h_R args m₀ hPre)

theorem swap_u32_total
    (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := swap_u32,
      pre := swapU32Pre a_ptr b_ptr a_old b_old R_frame,
      post := swapU32Post a_ptr b_ptr a_old b_old R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    swap_u32_mirWpConverges a_ptr b_ptr a_old b_old R_frame h_R args m₀ hPre)

/-! ### `add_assign` with Overflow Checks (Multi-Block `assert` CFG) -/

def boolLayout : TypeLayout :=
  { size := { bytes := 1 }
    align := { bytes := 1 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

def u32BoolPairLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/--
`Runtime(PostCleanup)` MIR of
`pub fn add_assign(x: &mut u32, d: u32) { *x += d; }` as rustc builds it with
overflow checks: `AddWithOverflow` reads the pointee
into the pair temporary `_3`, the `assert` on `!_3.1` guards the overflow
panic edge, and the success block writes `_3.0` back through `x`.
-/
def add_assign_checked : CapturedMir where
  defPath := "demo::add_assign_checked"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 },
      debugName := some "x" },
    { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "d" },
    { mutability := .mut, ty := { kind := .tuple [.uint .u32, .bool], layoutIdx := 3 },
      debugName := none }
  ]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 3, span := "add_assign_checked" },
        { kind := .assign { local_ := 3, projection := [] }
            (.binaryOp .addWithOverflow
              (.copy { local_ := 1, projection := [.deref] })
              (.copy { local_ := 2, projection := [] })),
          span := "add_assign_checked" }
      ],
      terminator := {
        kind := .assert
          (.move
            { local_ := 3
              projection := [.field 1 { kind := .bool, layoutIdx := 4 }] })
          false 1 .continue_,
        span := "add_assign_checked" },
      isCleanup := false
    },
    { statements := [
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.use (.move
              { local_ := 3
                projection := [.field 0 { kind := .uint .u32, layoutIdx := 1 }] })),
          span := "add_assign_checked" },
        { kind := .storageDead 3, span := "add_assign_checked" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "add_assign_checked" }
      ],
      terminator := { kind := .return_, span := "add_assign_checked" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32MutPtrLayout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := true
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout, u32BoolPairLayout, boolLayout]
  }
  allocations := []

/--
Precondition of the overflow-checked `add_assign`: the `add_assign`
separation-logic precondition plus the absence of `u32` overflow, without which
the `assert` takes the panic edge.
-/
def addAssignCheckedPre
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩] ∧
    x_old + d_val < scalarModulus 4 ∧
    WfSingleMutBorrow 4 x_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) x_old) R_frame)
      m₀

/-- Postcondition of the overflow-checked `add_assign`: the exact sum. -/
def addAssignCheckedPost
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) (x_old + d_val))
        R_frame)
      m_final

/--
`AddWithOverflow` result pair `(wrapped, overflowed)` for unsigned `u32`
operands, as `evalScalarBinOp` computes it.
-/
def u32AddWithOverflowPair (a b : Nat) : Value :=
  .aggregate 0
    [.scalar ⟨wrapScalarBits (Nat.add a b) (scalarModulus 4), 4⟩,
      .scalar ⟨match Nat.ble (scalarModulus 4) (Nat.add a b) with
        | true => 1
        | false => 0, 1⟩]

theorem ble_scalarModulus_eq_false {n sz : Nat} (h : n < scalarModulus sz) :
    Nat.ble (scalarModulus sz) n = false := by
  cases hBle : Nat.ble (scalarModulus sz) n with
  | false => rfl
  | true => exact absurd (Nat.le_of_ble_eq_true hBle) (Nat.not_le.mpr h)

/--
The pure lens-state derivation of the two-block overflow-checked body: the
`assert` edge is discharged from the no-overflow hypothesis, and the success
block writes the wrapped sum back through the lens.
-/
theorem add_assign_checked_lift (x_ptr : RawPtrVal) (x_old d_val : Nat)
    (hNo : x_old + d_val < scalarModulus 4) :
    LiftLensBlock add_assign_checked 0
      (initMachineState add_assign_checked
        [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      .unit
      (updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr
        (.scalar ⟨wrapScalarBits (Nat.add x_old d_val) (scalarModulus 4), 4⟩)) := by
  have hBle : Nat.ble (scalarModulus 4) (Nat.add x_old d_val) = false :=
    ble_scalarModulus_eq_false hNo
  unfold initMachineState
  dsimp [add_assign_checked, initLocalsAux]
  apply LiftLensBlock.assert (target := 1)
    (entries₁ := [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)])
    (env₁ := [.uninit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨d_val, 4⟩),
      .init (u32AddWithOverflowPair x_old d_val)])
  · rfl
  · rfl
  · rfl
  · refine .cons (.storageLive (.mk (oldSlot := .dead)
      (env' := [.uninit, .init (.ptr x_ptr.toMirPtr 8),
        .init (.scalar ⟨d_val, 4⟩), .uninit]) rfl rfl)) ?_
    refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (.binaryOp (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
        (.pure (.copy_local rfl)) (fun _ => rfl))
      rfl (fun h => nomatch h) rfl)) ?_
    exact .nil
  · exact .pure (.move_field rfl rfl rfl)
  · show (match Nat.ble (scalarModulus 4) (Nat.add x_old d_val) with
      | true => 1
      | false => 0) = 0
    rw [hBle]
  · refine LiftLensBlock.return_
      (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8),
        .init (.scalar ⟨d_val, 4⟩), .dead]) rfl rfl rfl ?_ rfl
    refine .cons (.derefWrite (.mk (.use_pure (.move_field rfl rfl rfl) rfl) rfl
      (lookupLensVal?_singleton_self _ _))) ?_
    refine .cons (.storageDead (.mk rfl rfl)) ?_
    refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
    exact .nil

/--
Fuel-free convergence of the overflow-checked `add_assign` (two blocks joined
by an `assert`) from every memory satisfying its precondition, proved through
`mirWpConverges_of_sepLenses`: the panic edge is unreachable and the pointee
ends at the exact sum.
-/
theorem add_assign_checked_mirWpConverges
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : addAssignCheckedPre x_ptr x_old d_val R_frame args m₀) :
    MirWpConverges add_assign_checked
      (initMachineStateWithMemory add_assign_checked args m₀)
      (mirNormalPost (addAssignCheckedPost x_ptr x_old d_val R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hNo, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (add_assign_checked_lift x_ptr x_old d_val hNo)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  have hWrap :
      wrapScalarBits (Nat.add x_old d_val) (scalarModulus 4) = x_old + d_val := by
    unfold wrapScalarBits
    rw [ble_scalarModulus_eq_false (n := Nat.add x_old d_val) hNo]
    rfl
  rw [updateLensVal_singleton_self, hWrap] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 4)⟩

theorem add_assign_checked_verified
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := add_assign_checked,
      pre := addAssignCheckedPre x_ptr x_old d_val R_frame,
      post := addAssignCheckedPost x_ptr x_old d_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_checked_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)

theorem add_assign_checked_total
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := add_assign_checked,
      pre := addAssignCheckedPre x_ptr x_old d_val R_frame,
      post := addAssignCheckedPost x_ptr x_old d_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_checked_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)


/-! ### Conditional Branching: `max_assign_u32(x: &mut u32, y: u32)` -/

/--
`Runtime(PostCleanup)` MIR of `max_assign_u32`, whose Rust source is
`fn max_assign_u32(x: &mut u32, y: u32) { if *x < y { *x = y; } }`: three basic
blocks joined by `TerminatorKind.switchInt` and `TerminatorKind.goto`.
- `bb0` (index `0`): `StorageLive(_3); _3 = Lt(copy (*_1), copy _2);`
  `switchInt(move _3) -> [0: bb2, otherwise: bb1]`
- `bb1` (index `1`): `(*_1) = copy _2; goto -> bb2`
- `bb2` (index `2`): `StorageDead(_3); _0 = const (); return`
-/
def max_assign_u32 : CapturedMir where
  defPath := "demo::max_assign_u32"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 },
      debugName := some "x" },
    { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "y" },
    { mutability := .mut, ty := { kind := .bool, layoutIdx := 3 },
      debugName := some "_3" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 3, span := "max_assign_u32" },
        { kind := .assign { local_ := 3, projection := [] }
            (.binaryOp .lt
              (.copy { local_ := 1, projection := [.deref] })
              (.copy { local_ := 2, projection := [] })),
          span := "max_assign_u32" }
      ],
      terminator := {
        kind := .switchInt
          (.move { local_ := 3, projection := [] })
          { branches := [(0, 2)], otherwise := 1 }
        span := "max_assign_u32"
      },
      isCleanup := false
    },
    { statements := [
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.use (.copy { local_ := 2, projection := [] })),
          span := "max_assign_u32" }
      ],
      terminator := { kind := .goto 2, span := "max_assign_u32" },
      isCleanup := false
    },
    { statements := [
        { kind := .storageDead 3, span := "max_assign_u32" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "max_assign_u32" }
      ],
      terminator := { kind := .return_, span := "max_assign_u32" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32MutPtrLayout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout, boolLayout]
  }
  allocations := []

/--
Precondition of `max_assign_u32`: `x` owns an active `&mut u32` holding
`x_old`.
-/
def maxAssignU32Pre (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨y_val, 4⟩] ∧
    WfSingleMutBorrow 4 x_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) x_old) R_frame)
      m₀

/--
Postcondition of `max_assign_u32`: unit result, and `x_ptr` holds
`if x_old < y_val then y_val else x_old`, with `R_frame` preserved.
-/
def maxAssignU32Post (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4)
          (if x_old < y_val then y_val else x_old))
        R_frame)
      m_final

/--
Pure lens-state derivation of the three-block `max_assign_u32` body across both
`switchInt` outcomes (`*x < y` takes `bb0 -> bb1 -> bb2`; `y ≤ *x` takes
`bb0 -> bb2`).
-/
theorem max_assign_u32_lift (x_ptr : RawPtrVal) (x_old y_val : Nat) :
    LiftLensBlock max_assign_u32 0
      (initMachineState max_assign_u32
        [.ptr x_ptr.toMirPtr 8, .scalar ⟨y_val, 4⟩]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      .unit
      [(x_ptr, (ValueCodec.scalarNat 4).encode
        (if x_old < y_val then y_val else x_old))] := by
  unfold initMachineState
  dsimp [max_assign_u32, initLocalsAux]
  by_cases hLt : x_old < y_val
  · have hBle : Nat.ble y_val x_old = false := by
      cases hB : Nat.ble y_val x_old with
      | false => rfl
      | true => exact absurd (Nat.le_of_ble_eq_true hB) (Nat.not_le.mpr hLt)
    simp only [hLt, ↓reduceIte]
    apply LiftLensBlock.switchInt (target := 1)
      (entries₁ := [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)])
      (env₁ := [.uninit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨y_val, 4⟩),
        .init (.scalar (boolToScalar (Bool.not (Nat.ble y_val x_old))))])
      (env₂ := [.uninit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨y_val, 4⟩),
        .uninit])
      (sc := boolToScalar (Bool.not (Nat.ble y_val x_old)))
    · rfl
    · rfl
    · rfl
    · refine .cons (.storageLive (.mk (oldSlot := .dead)
        (env' := [.uninit, .init (.ptr x_ptr.toMirPtr 8),
          .init (.scalar ⟨y_val, 4⟩), .uninit]) rfl rfl)) ?_
      refine .cons (.pureAssign (.mk (oldSlot := .uninit)
        (.binaryOp (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
          (.pure (.copy_local rfl)) (fun _ => rfl))
        rfl (fun h => nomatch h) rfl)) ?_
      exact .nil
    · exact .pure (.move_local rfl rfl)
    · rw [hBle]
      rfl
    · apply LiftLensBlock.goto (target := 2)
        (entries₁ := [(x_ptr, (ValueCodec.scalarNat 4).encode y_val)])
        (env₁ := [.uninit, .init (.ptr x_ptr.toMirPtr 8),
          .init (.scalar ⟨y_val, 4⟩), .uninit])
      · rfl
      · rfl
      · rfl
      · refine .cons (.derefWrite (.mk (.use_pure (.copy_local rfl) rfl) rfl
          (lookupLensVal?_singleton_self _ _))) ?_
        rw [updateLensVal_singleton_self]
        exact .nil
      · refine LiftLensBlock.return_
          (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8),
            .init (.scalar ⟨y_val, 4⟩), .dead]) rfl rfl rfl ?_ rfl
        refine .cons (.storageDead (.mk rfl rfl)) ?_
        refine .cons (.pureAssign (.mk (oldSlot := .uninit)
          (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
        exact .nil
  · have hLe : y_val ≤ x_old := Nat.le_of_not_lt hLt
    have hBle : Nat.ble y_val x_old = true := Nat.ble_eq_true_of_le hLe
    simp only [hLt, ↓reduceIte]
    apply LiftLensBlock.switchInt (target := 2)
      (entries₁ := [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)])
      (env₁ := [.uninit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨y_val, 4⟩),
        .init (.scalar (boolToScalar (Bool.not (Nat.ble y_val x_old))))])
      (env₂ := [.uninit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨y_val, 4⟩),
        .uninit])
      (sc := boolToScalar (Bool.not (Nat.ble y_val x_old)))
    · rfl
    · rfl
    · rfl
    · refine .cons (.storageLive (.mk (oldSlot := .dead)
        (env' := [.uninit, .init (.ptr x_ptr.toMirPtr 8),
          .init (.scalar ⟨y_val, 4⟩), .uninit]) rfl rfl)) ?_
      refine .cons (.pureAssign (.mk (oldSlot := .uninit)
        (.binaryOp (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
          (.pure (.copy_local rfl)) (fun _ => rfl))
        rfl (fun h => nomatch h) rfl)) ?_
      exact .nil
    · exact .pure (.move_local rfl rfl)
    · rw [hBle]
      rfl
    · refine LiftLensBlock.return_
        (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8),
          .init (.scalar ⟨y_val, 4⟩), .dead]) rfl rfl rfl ?_ rfl
      refine .cons (.storageDead (.mk rfl rfl)) ?_
      refine .cons (.pureAssign (.mk (oldSlot := .uninit)
        (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
      exact .nil

/--
Fuel-free convergence of `max_assign_u32` across all three basic blocks and both
`switchInt` outcomes, proved through `mirWpConverges_of_sepLenses` with zero
`Memory` destructuring.
-/
theorem max_assign_u32_mirWpConverges
    (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : maxAssignU32Pre x_ptr x_old y_val R_frame args m₀) :
    MirWpConverges max_assign_u32
      (initMachineStateWithMemory max_assign_u32 args m₀)
      (mirNormalPost (maxAssignU32Post x_ptr x_old y_val R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (max_assign_u32_lift x_ptr x_old y_val)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 4)⟩

theorem max_assign_u32_verified
    (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := max_assign_u32,
      pre := maxAssignU32Pre x_ptr x_old y_val R_frame,
      post := maxAssignU32Post x_ptr x_old y_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    max_assign_u32_mirWpConverges x_ptr x_old y_val R_frame h_R args m₀ hPre)

theorem max_assign_u32_total
    (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := max_assign_u32,
      pre := maxAssignU32Pre x_ptr x_old y_val R_frame,
      post := maxAssignU32Post x_ptr x_old y_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    max_assign_u32_mirWpConverges x_ptr x_old y_val R_frame h_R args m₀ hPre)


/-! ### Unary-Operator and Cast Witnesses (`not_assign`, `widen_assign`) -/

/--
`Runtime(PostCleanup)` MIR of `pub fn not_assign(x: &mut u32) { *x = !*x; }`:
`(*_1) = Not(copy (*_1))` exercises `LiftLensRvalue.unaryOp_not` on a lens
dereference operand.
-/
def not_assign : CapturedMir where
  defPath := "demo::not_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 },
      debugName := some "x" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.unaryOp .not (.copy { local_ := 1, projection := [.deref] })),
          span := "not_assign" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "not_assign" }
      ],
      terminator := { kind := .return_, span := "not_assign" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := u32MutPtrLayout, mode := .direct }]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout]
  }
  allocations := []

/-- Bitwise complement of a `u32` value, as `evalUnaryNot` computes it. -/
def u32Not (x : Nat) : Nat :=
  Nat.sub (Nat.sub (scalarModulus 4) 1) (wrapScalarBits x (scalarModulus 4))

def notAssignPre (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8] ∧
    WfSingleMutBorrow 2 x_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) x_old) R_frame)
      m₀

def notAssignPost (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) (u32Not x_old))
        R_frame)
      m_final

theorem not_assign_lift (x_ptr : RawPtrVal) (x_old : Nat) :
    LiftLensBlock not_assign 0
      (initMachineState not_assign [.ptr x_ptr.toMirPtr 8]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      .unit
      (updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr
        (.scalar ⟨u32Not x_old, 4⟩)) := by
  unfold initMachineState
  dsimp [not_assign, initLocalsAux]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8)]) rfl rfl rfl ?_ rfl
  refine .cons (.derefWrite (.mk
    (.unaryOp_not (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
      (fun _ => rfl))
    rfl (lookupLensVal?_singleton_self _ _))) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
  exact .nil

theorem not_assign_mirWpConverges
    (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : notAssignPre x_ptr x_old R_frame args m₀) :
    MirWpConverges not_assign (initMachineStateWithMemory not_assign args m₀)
      (mirNormalPost (notAssignPost x_ptr x_old R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (not_assign_lift x_ptr x_old)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 4)⟩

theorem not_assign_verified
    (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := not_assign,
      pre := notAssignPre x_ptr x_old R_frame,
      post := notAssignPost x_ptr x_old R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    not_assign_mirWpConverges x_ptr x_old R_frame h_R args m₀ hPre)

theorem not_assign_total
    (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := not_assign,
      pre := notAssignPre x_ptr x_old R_frame,
      post := notAssignPost x_ptr x_old R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    not_assign_mirWpConverges x_ptr x_old R_frame h_R args m₀ hPre)

def u64Layout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/--
`Runtime(PostCleanup)` MIR of
`pub fn widen_assign(x: &mut u64, y: u32) { *x = y as u64; }`:
`(*_1) = copy _2 as u64 (IntToInt)` exercises `LiftLensRvalue.cast_intToInt`
(zero-extension of an unsigned source) feeding a lens write.
-/
def widen_assign : CapturedMir where
  defPath := "demo::widen_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u64), layoutIdx := 2 },
      debugName := some "x" },
    { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "y" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.cast .intToInt (.copy { local_ := 2, projection := [] })
              { kind := .uint .u64, layoutIdx := 3 }),
          span := "widen_assign" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "widen_assign" }
      ],
      terminator := { kind := .return_, span := "widen_assign" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32MutPtrLayout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout, u64Layout]
  }
  allocations := []

def widenAssignPre (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨y_val, 4⟩] ∧
    WfSingleMutBorrow 3 x_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 8) x_old) R_frame)
      m₀

def widenAssignPost (x_ptr : RawPtrVal) (y_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 8)
          (wrapScalarBits y_val (scalarModulus 8)))
        R_frame)
      m_final

theorem widen_assign_lift (x_ptr : RawPtrVal) (x_old y_val : Nat) :
    LiftLensBlock widen_assign 0
      (initMachineState widen_assign
        [.ptr x_ptr.toMirPtr 8, .scalar ⟨y_val, 4⟩]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 8).encode x_old)]
      .unit
      (updateLensVal [(x_ptr, (ValueCodec.scalarNat 8).encode x_old)] x_ptr
        (.scalar ⟨wrapScalarBits y_val (scalarModulus 8), 8⟩)) := by
  unfold initMachineState
  dsimp [widen_assign, initLocalsAux]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨y_val, 4⟩)])
    rfl rfl rfl ?_ rfl
  refine .cons (.derefWrite (.mk
    (.cast_intToInt (targetBytes := 8) (.pure (.copy_local rfl)) rfl rfl)
    rfl (lookupLensVal?_singleton_self _ _))) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
  exact .nil

theorem widen_assign_mirWpConverges
    (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : widenAssignPre x_ptr x_old y_val R_frame args m₀) :
    MirWpConverges widen_assign (initMachineStateWithMemory widen_assign args m₀)
      (mirNormalPost (widenAssignPost x_ptr y_val R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (widen_assign_lift x_ptr x_old y_val)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 8)⟩

theorem widen_assign_verified
    (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := widen_assign,
      pre := widenAssignPre x_ptr x_old y_val R_frame,
      post := widenAssignPost x_ptr y_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    widen_assign_mirWpConverges x_ptr x_old y_val R_frame h_R args m₀ hPre)

theorem widen_assign_total
    (x_ptr : RawPtrVal) (x_old y_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := widen_assign,
      pre := widenAssignPre x_ptr x_old y_val R_frame,
      post := widenAssignPost x_ptr y_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    widen_assign_mirWpConverges x_ptr x_old y_val R_frame h_R args m₀ hPre)

/--
`Runtime(PostCleanup)` MIR of release-mode
`pub fn neg_assign_i32(x: &mut i32) { *x = -*x; }`:
`(*_1) = Neg(copy (*_1))` exercises `LiftLensRvalue.unaryOp_neg` on a signed
32-bit lens dereference operand.
-/
def neg_assign_i32 : CapturedMir where
  defPath := "demo::neg_assign_i32"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.int .i32), layoutIdx := 2 },
      debugName := some "x" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.unaryOp .neg (.copy { local_ := 1, projection := [.deref] })),
          span := "neg_assign_i32" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "neg_assign_i32" }
      ],
      terminator := { kind := .return_, span := "neg_assign_i32" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := u32MutPtrLayout, mode := .direct }]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout]
  }
  allocations := []

/--
Two's-complement 32-bit negation of `x`, as `evalRvalue (.unaryOp .neg _)`
computes it.
-/
def i32NegBits (x : Nat) : Nat :=
  wrapScalarBits
    (Nat.sub (scalarModulus 4) (wrapScalarBits x (scalarModulus 4)))
    (scalarModulus 4)

/--
`i32NegBits` is two's-complement negation: it is canonical and adding the
original bits gives `0` modulo `2^32`, so `negAssignI32Post` states that `*x`
ends as the wrapping negation of `x_old`.
-/
theorem i32NegBits_spec (x : Nat) :
    i32NegBits x < 4294967296 ∧ (i32NegBits x + x) % 4294967296 = 0 := by
  have hM : scalarModulus 4 = 4294967296 := rfl
  simp only [i32NegBits, Anneal.Scalars.wrapScalarBits_eq_mod_modulus, hM,
    Nat.sub_eq]
  omega

def negAssignI32Pre (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8] ∧
    WfSingleMutBorrow 2 x_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) x_old) R_frame)
      m₀

def negAssignI32Post (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) (i32NegBits x_old))
        R_frame)
      m_final

theorem neg_assign_i32_lift (x_ptr : RawPtrVal) (x_old : Nat) :
    LiftLensBlock neg_assign_i32 0
      (initMachineState neg_assign_i32 [.ptr x_ptr.toMirPtr 8]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      .unit
      (updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr
        (.scalar ⟨i32NegBits x_old, 4⟩)) := by
  unfold initMachineState
  dsimp [neg_assign_i32, initLocalsAux]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8)]) rfl rfl rfl ?_ rfl
  refine .cons (.derefWrite (.mk
    (.unaryOp_neg (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
      rfl)
    rfl (lookupLensVal?_singleton_self _ _))) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
  exact .nil

theorem neg_assign_i32_mirWpConverges
    (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : negAssignI32Pre x_ptr x_old R_frame args m₀) :
    MirWpConverges neg_assign_i32
      (initMachineStateWithMemory neg_assign_i32 args m₀)
      (mirNormalPost (negAssignI32Post x_ptr x_old R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (neg_assign_i32_lift x_ptr x_old)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 4)⟩

theorem neg_assign_i32_verified
    (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := neg_assign_i32,
      pre := negAssignI32Pre x_ptr x_old R_frame,
      post := negAssignI32Post x_ptr x_old R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    neg_assign_i32_mirWpConverges x_ptr x_old R_frame h_R args m₀ hPre)

theorem neg_assign_i32_total
    (x_ptr : RawPtrVal) (x_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := neg_assign_i32,
      pre := negAssignI32Pre x_ptr x_old R_frame,
      post := negAssignI32Post x_ptr x_old R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    neg_assign_i32_mirWpConverges x_ptr x_old R_frame h_R args m₀ hPre)

/--
Two-block `Runtime(PostCleanup)` MIR body exercising `LiftLensBlock.drop_local`
and `mirWpConverges_drop_of_lens`:
- `bb0` (index `0`): `StorageLive(_3); _3 = copy _2;
  (*_1) = Add(copy (*_1), copy _3); drop(_3) -> bb1`
- `bb1` (index `1`): `StorageDead(_3); _0 = const (); return`

This body is hand-written, not captured: rustc elaborates away `drop` of
locals without drop glue such as `u32`, so no captured body reaches the
`drop_local` rule with a `u32` temporary.
-/
def drop_temp_assign : CapturedMir where
  defPath := "demo::drop_temp_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not, ty := { kind := .ref .mut (.uint .u32), layoutIdx := 2 },
      debugName := some "x" },
    { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "d" },
    { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "_3" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 3, span := "drop_temp_assign" },
        { kind := .assign { local_ := 3, projection := [] }
            (.use (.copy { local_ := 2, projection := [] })),
          span := "drop_temp_assign" },
        { kind := .assign { local_ := 1, projection := [.deref] }
            (.binaryOp .add
              (.copy { local_ := 1, projection := [.deref] })
              (.copy { local_ := 3, projection := [] })),
          span := "drop_temp_assign" }
      ],
      terminator := {
        kind := .drop { local_ := 3, projection := [] } 1 .continue_
        span := "drop_temp_assign"
      },
      isCleanup := false
    },
    { statements := [
        { kind := .storageDead 3, span := "drop_temp_assign" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "drop_temp_assign" }
      ],
      terminator := { kind := .return_, span := "drop_temp_assign" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [
      { layout := u32MutPtrLayout, mode := .direct },
      { layout := u32Layout, mode := .direct }
    ]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, u32MutPtrLayout]
  }
  allocations := []

def dropTempAssignPre
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩] ∧
    WfSingleMutBorrow 4 x_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) x_old) R_frame)
      m₀

theorem drop_temp_assign_lift (x_ptr : RawPtrVal) (x_old d_val : Nat) :
    LiftLensBlock drop_temp_assign 0
      (initMachineState drop_temp_assign
        [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩]).frame.locals
      [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      .unit
      (updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr
        (.scalar ⟨wrapScalarBits (Nat.add x_old d_val) (scalarModulus 4), 4⟩)) := by
  unfold initMachineState
  dsimp [drop_temp_assign, initLocalsAux]
  apply LiftLensBlock.drop_local (target := 1) (loc := 3) (unwind := .continue_)
    (oldSlot := .init (.scalar ⟨d_val, 4⟩))
    (entries₁ := updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
      x_ptr (.scalar ⟨wrapScalarBits (Nat.add x_old d_val) (scalarModulus 4), 4⟩))
    (env₁ := [.uninit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨d_val, 4⟩),
      .init (.scalar ⟨d_val, 4⟩)])
    (env₂ := [.uninit, .init (.ptr x_ptr.toMirPtr 8), .init (.scalar ⟨d_val, 4⟩),
      .uninit])
  · rfl
  · rfl
  · rfl
  · refine .cons (.storageLive (.mk (oldSlot := .dead)
      (env' := [.uninit, .init (.ptr x_ptr.toMirPtr 8),
        .init (.scalar ⟨d_val, 4⟩), .uninit]) rfl rfl)) ?_
    refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (.use_pure (.copy_local rfl) rfl) rfl (fun h => nomatch h) rfl)) ?_
    refine .cons (.derefWrite (.mk
      (.binaryOp_add (by decide)
        (.deref (.copy_deref rfl (lookupLensVal?_singleton_self _ _)))
        (.pure (.copy_local rfl)))
      rfl (lookupLensVal?_singleton_self _ _))) ?_
    exact .nil
  · rfl
  · intro h; nomatch h
  · rfl
  · refine LiftLensBlock.return_
      (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8),
        .init (.scalar ⟨d_val, 4⟩), .dead]) rfl rfl rfl ?_ rfl
    refine .cons (.storageDead (.mk rfl rfl)) ?_
    refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
    exact .nil

theorem drop_temp_assign_mirWpConverges
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (args : List Value) (m₀ : Memory)
    (hPre : dropTempAssignPre x_ptr x_old d_val R_frame args m₀) :
    MirWpConverges drop_temp_assign
      (initMachineStateWithMemory drop_temp_assign args m₀)
      (mirNormalPost (addAssignPost x_ptr x_old d_val R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (drop_temp_assign_lift x_ptr x_old d_val)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep hInv hWf hPres h_R
    (scalarNat_not_aggregate 4)⟩

theorem drop_temp_assign_verified
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := drop_temp_assign,
      pre := dropTempAssignPre x_ptr x_old d_val R_frame,
      post := addAssignPost x_ptr x_old d_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    drop_temp_assign_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)

theorem drop_temp_assign_total
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := drop_temp_assign,
      pre := dropTempAssignPre x_ptr x_old d_val R_frame,
      post := addAssignPost x_ptr x_old d_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    drop_temp_assign_mirWpConverges x_ptr x_old d_val R_frame h_R args m₀ hPre)


/-! ### Non-Vacuity: Concrete `I-10` Reborrow Chains -/

/-- Child tag `2` of `x` (the callee's reborrow `&mut *r`). -/
def demoChildPtr : RawPtrVal := { allocId := 3, offset := 0, tag := 2 }

/-- Parent tag `1` of the caller reference `r` the child was reborrowed from. -/
def demoParentPtr : RawPtrVal := { allocId := 3, offset := 0, tag := 1 }

/--
Caller memory for `add_assign`: caller slot `3` (above the 3-slot callee frame)
holds `x_old`, borrowed by the active parent tag `1` and its active child tag
`2` (`parentTag := some 1`). The strict `ExclusiveActiveBorrow` rejects this
table (the parent is neither disabled nor `x`'s own tag), while
`TreeExclusiveBorrow` accepts it.
-/
def addAssignDemoMem (x_old : Nat) : Memory :=
  { borrows := [
      { tag := 2, targetLocal := 3, targetProjection := [], perm := .active,
        parentTag := some 1 },
      { tag := 1, targetLocal := 3, targetProjection := [], perm := .active } ]
    callerLocals := [.dead, .dead, .dead, .init (.scalar ⟨x_old, 4⟩)] }

/--
The reborrow-chain memory lies outside the strict exclusivity invariant: the
active parent entry is neither `x`'s own tag nor disabled. Only the `I-10`
parent/child relaxation `TreeExclusiveBorrow` admits it.
-/
theorem addAssignDemoMem_not_strictExclusive (x_old : Nat) :
    ¬ ExclusiveActiveBorrow demoChildPtr (addAssignDemoMem x_old) := by
  intro h
  have hParent :
      ({ tag := 1, targetLocal := 3, targetProjection := [], perm := .active } :
        BorrowEntry) ∈ (addAssignDemoMem x_old).borrows :=
    List.Mem.tail _ (List.Mem.head _)
  rcases h.exclusive_on_alloc _ hParent rfl with ⟨hTag, _⟩ | hDis
  · exact absurd hTag (by decide)
  · exact nomatch hDis

/--
Even though `addAssignDemoMem x_old` fails the strict `ExclusiveActiveBorrow`
invariant (`addAssignDemoMem_not_strictExclusive`), it satisfies
`ValidTreeMutBorrowLens` for the `I-10`-aware lens `treeMemoryPtrMutLens`,
making `treeMemoryPtrMutLens demoChildPtr (ValueCodec.scalarNat 4)` a lawful
PutGet / GetPut / PutPut lens on the concrete parent/child reborrow chain.
-/
theorem validTreeMutBorrowLens_addAssignDemoMem (x_old : Nat) :
    ValidTreeMutBorrowLens demoChildPtr (ValueCodec.scalarNat 4)
      (addAssignDemoMem x_old) where
  has_typed_pointee := ⟨x_old, rfl⟩
  exclusive := by
    refine ⟨rfl, ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    intro b hb _
    simp only [addAssignDemoMem, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl <;> exact Or.inl ⟨rfl, rfl⟩

/--
Concrete PutGet on `addAssignDemoMem x_old`: writing `x_new` through
`treeMemoryPtrMutLens` on the child reborrow and reading back recovers `x_new`,
even though the active parent tag remains in the borrow table.
-/
theorem treeMemoryPtrMutLens_putGet_addAssignDemoMem (x_old x_new : Nat) :
    (treeMemoryPtrMutLens demoChildPtr (ValueCodec.scalarNat 4)).readView
      ((treeMemoryPtrMutLens demoChildPtr (ValueCodec.scalarNat 4)).writeBack
        x_new (addAssignDemoMem x_old)) = x_new :=
  (treeMemoryPtrMutLens_lawful demoChildPtr (ValueCodec.scalarNat 4)).readView_writeBack
    x_new (addAssignDemoMem x_old) (validTreeMutBorrowLens_addAssignDemoMem x_old)

theorem add_assign_demo_pre (x_old d_val : Nat) :
    addAssignPre demoChildPtr x_old d_val (BorrowToken demoParentPtr .active)
      [.ptr demoChildPtr.toMirPtr 8, .scalar ⟨d_val, 4⟩]
      (addAssignDemoMem x_old) := by
  refine ⟨rfl, ⟨rfl, rfl, ?_, by decide, ⟨rfl, ?_, ?_⟩⟩, ?_⟩
  · intro b hb
    simp only [addAssignDemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl <;> decide
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b hb _
    simp only [addAssignDemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
  · refine ⟨_, sepConjBindings_intro
      (bs := [MutBorrowBinding.bind demoChildPtr (ValueCodec.scalarNat 4) x_old])
      (fpR := { addrs := [], tags := [1] }) ?_ (List.pairwise_singleton _ _)
      ⟨⟨_, rfl, rfl, rfl⟩, rfl⟩ ?_⟩
    · intro b hb
      rw [List.mem_singleton.mp hb]
      exact ⟨rfl, _, rfl, rfl, rfl⟩
    · intro b hb
      rw [List.mem_singleton.mp hb]
      refine ⟨(fun h => nomatch h), ?_⟩
      show ¬ ((2 : Nat) ∈ [1])
      decide

/--
`add_assign` runs to completion from the concrete reborrow-chain memory, and
the caller's parent tag stays active: the child write is a local write for the
`I-10` ancestor, which `R_frame := BorrowToken demoParentPtr .active` records.
-/
theorem add_assign_demo_runs (x_old d_val : Nat) :
    MirWpConverges add_assign
      (initMachineStateWithMemory add_assign
        [.ptr demoChildPtr.toMirPtr 8, .scalar ⟨d_val, 4⟩]
        (addAssignDemoMem x_old))
      (mirNormalPost
        (addAssignPost demoChildPtr x_old d_val
          (BorrowToken demoParentPtr .active)
          [.ptr demoChildPtr.toMirPtr 8, .scalar ⟨d_val, 4⟩]
          (addAssignDemoMem x_old))) :=
  add_assign_mirWpConverges demoChildPtr x_old d_val _
    (localSepProp_borrowToken demoParentPtr .active) _ _
    (add_assign_demo_pre x_old d_val)

/--
Caller memory for `swap_u32`: caller slots `4` and `5` (above the 4-slot callee
frame) hold `a_old` and `b_old` under root tags `1` and `2`.
-/
def swapU32DemoMem (a_old b_old : Nat) : Memory :=
  { borrows := [
      { tag := 1, targetLocal := 4, targetProjection := [], perm := .active },
      { tag := 2, targetLocal := 5, targetProjection := [], perm := .active } ]
    callerLocals :=
      [.dead, .dead, .dead, .dead, .init (.scalar ⟨a_old, 4⟩),
        .init (.scalar ⟨b_old, 4⟩)] }

def swapDemoA : RawPtrVal := { allocId := 4, offset := 0, tag := 1 }

def swapDemoB : RawPtrVal := { allocId := 5, offset := 0, tag := 2 }

theorem swap_u32_demo_pre (a_old b_old : Nat) :
    swapU32Pre swapDemoA swapDemoB a_old b_old emp
      [.ptr swapDemoA.toMirPtr 8, .ptr swapDemoB.toMirPtr 8]
      (swapU32DemoMem a_old b_old) := by
  have hAbove :
      ∀ b ∈ (swapU32DemoMem a_old b_old).borrows, 4 ≤ b.targetLocal := by
    intro b hb
    simp only [swapU32DemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl <;> decide
  refine ⟨rfl, ⟨rfl, rfl, hAbove, by decide, ⟨rfl, ?_, ?_⟩⟩,
    ⟨rfl, rfl, hAbove, by decide, ⟨rfl, ?_, ?_⟩⟩, ?_⟩
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b hb hT
    simp only [swapU32DemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact absurd hT (by decide)
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b hb hT
    simp only [swapU32DemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl
    · exact absurd hT (by decide)
    · exact Or.inl ⟨rfl, rfl⟩
  · refine ⟨_, sepConjBindings_intro
      (bs := [MutBorrowBinding.bind swapDemoA (ValueCodec.scalarNat 4) a_old,
        MutBorrowBinding.bind swapDemoB (ValueCodec.scalarNat 4) b_old])
      (fpR := Footprint.empty) ?_ ?_ rfl ?_⟩
    · intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · exact ⟨rfl, _, rfl, rfl, rfl⟩
      · exact ⟨rfl, _, rfl, rfl, rfl⟩
    · refine List.pairwise_cons.mpr ⟨?_, List.pairwise_singleton _ _⟩
      intro b hb
      rw [List.mem_singleton.mp hb]
      refine ⟨?_, ?_⟩
      · show ((4 : Nat), (0 : Nat)) ≠ (5, 0)
        decide
      · show (1 : Nat) ≠ 2
        decide
    · intro b _
      exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-- `swap_u32` runs to completion and swaps on the concrete two-cell memory. -/
theorem swap_u32_demo_runs (a_old b_old : Nat) :
    MirWpConverges swap_u32
      (initMachineStateWithMemory swap_u32
        [.ptr swapDemoA.toMirPtr 8, .ptr swapDemoB.toMirPtr 8]
        (swapU32DemoMem a_old b_old))
      (mirNormalPost
        (swapU32Post swapDemoA swapDemoB a_old b_old emp
          [.ptr swapDemoA.toMirPtr 8, .ptr swapDemoB.toMirPtr 8]
          (swapU32DemoMem a_old b_old))) :=
  swap_u32_mirWpConverges swapDemoA swapDemoB a_old b_old emp localSepProp_emp
    _ _ (swap_u32_demo_pre a_old b_old)


/-! ### Projected Field Accesses & `swap_pair_u32(p: &mut (u32, u32))` -/

/--
Product codec encoding `(α × β)` as a 2-element variant-`0` aggregate
`.aggregate 0 [codec₁.encode p.1, codec₂.encode p.2]`.
-/
def ValueCodec.prod {α β : Type}
    (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    ValueCodec (α × β) where
  encode p := .aggregate 0 [codec₁.encode p.1, codec₂.encode p.2]
  decode
    | .aggregate 0 [v₁, v₂] =>
      match codec₁.decode v₁, codec₂.decode v₂ with
      | some a, some b => some (a, b)
      | _, _ => none
    | _ => none
  default := (codec₁.default, codec₂.default)
  decode_encode p := by
    rcases p with ⟨a, b⟩
    simp

/-- Codec for a 2-tuple `(u32, u32)` of 32-bit unsigned scalars. -/
abbrev ValueCodec.pairU32 : ValueCodec (Nat × Nat) :=
  ValueCodec.prod (ValueCodec.scalarNat 4) (ValueCodec.scalarNat 4)

def pairU32Layout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 4 }
    backendRepr := .memory
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
    variants := .single 0
    isUninhabited := false }

def pairU32MutPtrLayout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .scalar (.initialized (.pointer 0) { start := 0, end_ := 0 })
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/--
`Runtime(PostCleanup)` MIR for `fn swap_pair_u32(p: &mut (u32, u32))`:
```
_2 = copy ((*_1).0);
_3 = copy ((*_1).1);
((*_1).0) = move _3;
((*_1).1) = move _2;
_0 = const ();
return;
```
Exercises `LiftDerefFieldRead` (`copy ((*_1).0)` and `copy ((*_1).1)`) and
`LiftDerefWrite.field` (`((*_1).0) = move _3` and `((*_1).1) = move _2`) on a
2-field aggregate pointee.
-/
def swap_pair_u32 : CapturedMir where
  defPath := "demo::swap_pair_u32"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 1
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
      debugName := some "_0" },
    { mutability := .not,
      ty := { kind := .ref .mut (.tuple [.uint .u32, .uint .u32]), layoutIdx := 3 },
      debugName := some "p" },
    { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "tmp0" },
    { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 1 },
      debugName := some "tmp1" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 2, span := "swap_pair_u32" },
        { kind := .assign { local_ := 2, projection := [] }
            (.use (.copy {
              local_ := 1,
              projection := [.deref, .field 0 { kind := .uint .u32, layoutIdx := 1 }]
            })),
          span := "swap_pair_u32" },
        { kind := .storageLive 3, span := "swap_pair_u32" },
        { kind := .assign { local_ := 3, projection := [] }
            (.use (.copy {
              local_ := 1,
              projection := [.deref, .field 1 { kind := .uint .u32, layoutIdx := 1 }]
            })),
          span := "swap_pair_u32" },
        { kind := .assign {
              local_ := 1,
              projection := [.deref, .field 0 { kind := .uint .u32, layoutIdx := 1 }]
            }
            (.use (.move { local_ := 3, projection := [] })),
          span := "swap_pair_u32" },
        { kind := .storageDead 3, span := "swap_pair_u32" },
        { kind := .assign {
              local_ := 1,
              projection := [.deref, .field 1 { kind := .uint .u32, layoutIdx := 1 }]
            }
            (.use (.move { local_ := 2, projection := [] })),
          span := "swap_pair_u32" },
        { kind := .storageDead 2, span := "swap_pair_u32" },
        { kind := .assign { local_ := 0, projection := [] }
            (.use (.constant
              { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })),
          span := "swap_pair_u32" }
      ],
      terminator := { kind := .return_, span := "swap_pair_u32" },
      isCleanup := false
    }
  ]
  fnAbi := {
    args := [{ layout := pairU32MutPtrLayout, mode := .direct }]
    ret := { layout := unitLayout, mode := .direct }
    conv := .rust
    canUnwind := false
  }
  layouts := {
    pointerBits := 64
    isLittleEndian := true
    entries := [unitLayout, u32Layout, pairU32Layout, pairU32MutPtrLayout]
  }
  allocations := []

def swapPairU32Pre
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr p_ptr.toMirPtr 8] ∧
    WfSingleMutBorrow 4 p_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow p_ptr ValueCodec.pairU32 (a_old, b_old))
        R_frame)
      m₀

def swapPairU32Post
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow p_ptr ValueCodec.pairU32 (b_old, a_old))
        R_frame)
      m_final

theorem swap_pair_u32_lift (p_ptr : RawPtrVal) (a_old b_old : Nat) :
    LiftLensBlock swap_pair_u32 0
      (initMachineState swap_pair_u32 [.ptr p_ptr.toMirPtr 8]).frame.locals
      [(p_ptr, ValueCodec.pairU32.encode (a_old, b_old))]
      .unit
      [(p_ptr, ValueCodec.pairU32.encode (b_old, a_old))] := by
  unfold initMachineState
  dsimp [swap_pair_u32, initLocalsAux, ValueCodec.pairU32, ValueCodec.prod,
    ValueCodec.scalarNat]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr p_ptr.toMirPtr 8), .dead, .dead])
    rfl rfl rfl ?_ rfl
  refine .cons (.storageLive (.mk (oldSlot := .dead)
    (env' := [.uninit, .init (.ptr p_ptr.toMirPtr 8), .uninit, .dead])
    rfl rfl)) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_deref_field (.copy_deref_field rfl
      (lookupLensVal?_singleton_self _ _) rfl) rfl)
    rfl (fun h => nomatch h) rfl)) ?_
  refine .cons (.storageLive (.mk (oldSlot := .dead)
    (env' := [.uninit, .init (.ptr p_ptr.toMirPtr 8),
      .init (.scalar ⟨a_old, 4⟩), .uninit])
    rfl rfl)) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_deref_field (.copy_deref_field rfl
      (lookupLensVal?_singleton_self _ _) rfl) rfl)
    rfl (fun h => nomatch h) rfl)) ?_
  refine .cons (.derefWrite (.field
    (.use_pure (.move_local rfl rfl) rfl)
    rfl (lookupLensVal?_singleton_self _ _) rfl)) ?_
  rw [updateLensVal_singleton_self]
  refine .cons (.storageDead (.mk rfl rfl)) ?_
  refine .cons (.derefWrite (.field
    (.use_pure (.move_local rfl rfl) rfl)
    rfl (lookupLensVal?_singleton_self _ _) rfl)) ?_
  rw [updateLensVal_singleton_self]
  refine .cons (.storageDead (.mk rfl rfl)) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
  exact .nil

theorem swap_pair_u32_mirWpConverges
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame)
    (args : List Value) (m₀ : Memory)
    (hPre : swapPairU32Pre p_ptr a_old b_old R_frame args m₀) :
    MirWpConverges swap_pair_u32
      (initMachineStateWithMemory swap_pair_u32 args m₀)
      (mirNormalPost (swapPairU32Post p_ptr a_old b_old R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses (swap_pair_u32_lift p_ptr a_old b_old)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one_of_rootAlloc
    hSep hInv hWf hPres h_R h_rootR⟩

theorem swap_pair_u32_verified
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame) :
    StatefulVerificationResult {
      body := swap_pair_u32,
      pre := swapPairU32Pre p_ptr a_old b_old R_frame,
      post := swapPairU32Post p_ptr a_old b_old R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    swap_pair_u32_mirWpConverges p_ptr a_old b_old R_frame h_R h_rootR
      args m₀ hPre)

theorem swap_pair_u32_total
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame) :
    TotalVerificationResult {
      body := swap_pair_u32,
      pre := swapPairU32Pre p_ptr a_old b_old R_frame,
      post := swapPairU32Post p_ptr a_old b_old R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    swap_pair_u32_mirWpConverges p_ptr a_old b_old R_frame h_R h_rootR
      args m₀ hPre)

/--
Caller memory for `swap_pair_u32`: caller slot `4` (above the 4-slot callee
frame) holds `(a_old, b_old)` under an active child reborrow tag `2` of active
parent tag `1` (`parentTag := some 1`).
-/
def swapPairU32DemoMem (a_old b_old : Nat) : Memory :=
  { borrows := [
      { tag := 2, targetLocal := 4, targetProjection := [], perm := .active,
        parentTag := some 1 },
      { tag := 1, targetLocal := 4, targetProjection := [], perm := .active } ]
    callerLocals := [
      .dead, .dead, .dead, .dead,
      .init (ValueCodec.pairU32.encode (a_old, b_old)) ] }

def swapPairChildPtr : RawPtrVal := { allocId := 4, offset := 0, tag := 2 }
def swapPairParentPtr : RawPtrVal := { allocId := 4, offset := 0, tag := 1 }

theorem swap_pair_u32_demo_pre (a_old b_old : Nat) :
    swapPairU32Pre swapPairChildPtr a_old b_old
      (BorrowToken swapPairParentPtr .active)
      [.ptr swapPairChildPtr.toMirPtr 8]
      (swapPairU32DemoMem a_old b_old) := by
  refine ⟨rfl, ⟨rfl, rfl, ?_, by decide, ⟨rfl, ?_, ?_⟩⟩, ?_⟩
  · intro b hb
    simp only [swapPairU32DemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl <;> decide
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b hb _
    simp only [swapPairU32DemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl <;> exact Or.inl ⟨rfl, rfl⟩
  · refine ⟨_, sepConjBindings_intro
      (bs := [MutBorrowBinding.bind swapPairChildPtr ValueCodec.pairU32
        (a_old, b_old)])
      (fpR := { addrs := [], tags := [1] }) ?_ (List.pairwise_singleton _ _)
      ⟨⟨_, rfl, rfl, rfl⟩, rfl⟩ ?_⟩
    · intro b hb
      rw [List.mem_singleton.mp hb]
      exact ⟨rfl, _, rfl, rfl, rfl⟩
    · intro b hb
      rw [List.mem_singleton.mp hb]
      refine ⟨(fun h => nomatch h), ?_⟩
      show ¬ ((2 : Nat) ∈ [1])
      decide

/--
`swap_pair_u32` runs to completion from the concrete `I-10` reborrow-chain
memory, swaps `(a_old, b_old)` to `(b_old, a_old)`, and preserves the caller's
active parent borrow token `BorrowToken swapPairParentPtr .active`.
-/
theorem swap_pair_u32_demo_runs (a_old b_old : Nat) :
    MirWpConverges swap_pair_u32
      (initMachineStateWithMemory swap_pair_u32
        [.ptr swapPairChildPtr.toMirPtr 8]
        (swapPairU32DemoMem a_old b_old))
      (mirNormalPost
        (swapPairU32Post swapPairChildPtr a_old b_old
          (BorrowToken swapPairParentPtr .active)
          [.ptr swapPairChildPtr.toMirPtr 8]
          (swapPairU32DemoMem a_old b_old))) :=
  swap_pair_u32_mirWpConverges swapPairChildPtr a_old b_old _
    (localSepProp_borrowToken swapPairParentPtr .active)
    (rootAllocSepProp_borrowToken swapPairParentPtr .active)
    _ _ (swap_pair_u32_demo_pre a_old b_old)

/--
Concrete memory witnessing two sibling field-granular `I-10` reborrows
`&mut s.0` (tag `2`) and `&mut s.1` (tag `3`) of an active parent struct borrow
`&mut s` (tag `1`) on caller slot `4`.
-/
def siblingFieldDemoMem (a_old b_old : Nat) : Memory :=
  { borrows := [
      { tag := 2, targetLocal := 4,
        targetProjection := [.field 0 { kind := .uint .u32, layoutIdx := 1 }],
        perm := .active, parentTag := some 1 },
      { tag := 3, targetLocal := 4,
        targetProjection := [.field 1 { kind := .uint .u32, layoutIdx := 1 }],
        perm := .active, parentTag := some 1 },
      { tag := 1, targetLocal := 4, targetProjection := [], perm := .active } ]
    callerLocals := [
      .dead, .dead, .dead, .dead,
      .init (ValueCodec.pairU32.encode (a_old, b_old)) ] }

def demoField0Ptr : RawPtrVal := { allocId := 4, offset := 0, tag := 2 }
def demoField1Ptr : RawPtrVal := { allocId := 4, offset := 0, tag := 3 }

/--
Non-vacuity of `ValidTreeFieldMutBorrowLensPair`: the concrete 3-tag borrow
table with parent `&mut s` (tag `1`) and sibling field reborrows `&mut s.0`
(tag `2`) and `&mut s.1` (tag `3`) on the **same** allocation `4` satisfies
`ValidTreeFieldMutBorrowLensPair`, so `treeFieldMemoryPtrMutLens` on field `0`
and field `1` are lawful and independent.
-/
theorem validTreeFieldMutBorrowLensPair_siblingFieldDemoMem
    (a_old b_old : Nat) :
    ValidTreeFieldMutBorrowLensPair
      demoField0Ptr demoField1Ptr 0 1
      { kind := .uint .u32, layoutIdx := 1 }
      { kind := .uint .u32, layoutIdx := 1 }
      (ValueCodec.scalarNat 4) (ValueCodec.scalarNat 4)
      (siblingFieldDemoMem a_old b_old) where
  valid_left := {
    valid_raw := ⟨a_old, rfl⟩
    exclusive := by
      refine ⟨rfl, ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
      intro b hb _
      simp only [siblingFieldDemoMem, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
  }
  valid_right := {
    valid_raw := ⟨b_old, rfl⟩
    exclusive := by
      refine ⟨rfl, ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
      intro b hb _
      simp only [siblingFieldDemoMem, List.mem_cons, List.not_mem_nil,
        or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
  }
  same_alloc := rfl
  ne_field := by decide

/-! ### Sibling Field Reborrows (`&mut s.0`, `&mut s.1`) & Aggregate Rvalues -/

theorem ne_of_sepConj_activeTypedFieldMutBorrow_two {α β : Type}
    {rp₁ rp₂ : RawPtrVal} {f₁ f₂ : FieldIdx}
    {c₁ : ValueCodec α} {c₂ : ValueCodec β}
    {a₁ : α} {a₂ : β} {R : SepProp} {m : Memory}
    (hSep :
      SepProp.holdsIn
        (sepConj (ActiveTypedFieldMutBorrow rp₁ f₁ c₁ a₁)
          (sepConj (ActiveTypedFieldMutBorrow rp₂ f₂ c₂ a₂) R))
        m) :
    rp₁ ≠ rp₂ := by
  rcases hSep with ⟨_, _, _, ⟨_, _, hDisj, _, _⟩, hA₁,
    _, _, ⟨_, _, _, _, hTags₂₃⟩, hA₂, _⟩
  rcases activeTypedFieldMutBorrow_facts hA₁ with ⟨_, _, _, hTag₁⟩
  rcases activeTypedFieldMutBorrow_facts hA₂ with ⟨_, _, _, hTag₂⟩
  intro hEq
  subst hEq
  exact hDisj.2 rp₁.tag hTag₁ ((hTags₂₃ _).mpr (Or.inl hTag₂))

/--
Precondition for `swap_u32` called with two sibling field-granular `I-10`
reborrows `&mut s.0` (`a_ptr`) and `&mut s.1` (`b_ptr`) on the **same** caller
aggregate allocation (`a_ptr.allocId = b_ptr.allocId`), separated from an
arbitrary `LocalSepProp` frame `R_frame`.
-/
def swapU32SiblingFieldsPre
    (a_ptr b_ptr : RawPtrVal) (fieldTy₀ fieldTy₁ : Ty)
    (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr a_ptr.toMirPtr 8, .ptr b_ptr.toMirPtr 8] ∧
    a_ptr.allocId = b_ptr.allocId ∧
    WfSingleFieldMutBorrow 4 a_ptr 0 fieldTy₀ m₀ ∧
    WfSingleFieldMutBorrow 4 b_ptr 1 fieldTy₁ m₀ ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedFieldMutBorrow a_ptr 0 (ValueCodec.scalarNat 4) a_old)
        (sepConj
          (ActiveTypedFieldMutBorrow b_ptr 1 (ValueCodec.scalarNat 4) b_old)
          R_frame))
      m₀

/--
Postcondition of `swap_u32` on sibling field reborrows `&mut s.0`, `&mut s.1`.
-/
def swapU32SiblingFieldsPost
    (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedFieldMutBorrow a_ptr 0 (ValueCodec.scalarNat 4) b_old)
        (sepConj
          (ActiveTypedFieldMutBorrow b_ptr 1 (ValueCodec.scalarNat 4) a_old)
          R_frame))
      m_final

/--
Fuel-free convergence of the unchanged `swap_u32` body when invoked with two
sibling field reborrows `&mut s.0` and `&mut s.1` on the same caller struct
allocation, proved by reusing `swap_u32_lift` directly through
`mirWpConverges_of_sepSubplaceLenses`.
-/
theorem swap_u32_sibling_fields_mirWpConverges
    (a_ptr b_ptr : RawPtrVal) (fieldTy₀ fieldTy₁ : Ty)
    (a_old b_old : Nat) (R_frame : SepProp) (h_R : LocalSepProp R_frame)
    (args : List Value) (m₀ : Memory)
    (hPre :
      swapU32SiblingFieldsPre a_ptr b_ptr fieldTy₀ fieldTy₁ a_old b_old
        R_frame args m₀) :
    MirWpConverges swap_u32 (initMachineStateWithMemory swap_u32 args m₀)
      (mirNormalPost
        (swapU32SiblingFieldsPost a_ptr b_ptr a_old b_old R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hSameAlloc, hWf₀, hWf₁, hSep⟩
  have hNe : a_ptr ≠ b_ptr :=
    ne_of_sepConj_activeTypedFieldMutBorrow_two hSep
  refine mirWpConverges_of_sepSubplaceLenses
    (swap_u32_lift a_ptr b_ptr a_old b_old hNe)
    (sepSubplaceLensStateInv_of_sepConj_two_fields hSep hWf₀ hWf₁)
    (fun m_final hInv hPres => ?_)
  have hEq :
      updateLensVal
          (updateLensVal
            [(a_ptr, (ValueCodec.scalarNat 4).encode a_old),
              (b_ptr, (ValueCodec.scalarNat 4).encode b_old)]
            a_ptr (.scalar ⟨b_old, 4⟩))
          b_ptr (.scalar ⟨a_old, 4⟩) =
        [(a_ptr, (ValueCodec.scalarNat 4).encode b_old),
          (b_ptr, (ValueCodec.scalarNat 4).encode a_old)] := by
    simp [updateLensVal, ValueCodec.scalarNat, hNe]
  rw [hEq] at hInv
  exact ⟨rfl, sepConj_activeTypedFieldMutBorrow_preserved_two a_ptr b_ptr
    0 1 fieldTy₀ fieldTy₁ (ValueCodec.scalarNat 4) (ValueCodec.scalarNat 4)
    a_old b_old b_old a_old hSep hInv hWf₀ hPres h_R
    (Or.inl rfl) (Or.inr (Or.inl ⟨hSameAlloc.symm, rfl⟩))⟩

theorem swap_u32_sibling_fields_verified
    (a_ptr b_ptr : RawPtrVal) (fieldTy₀ fieldTy₁ : Ty)
    (a_old b_old : Nat) (R_frame : SepProp) (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := swap_u32,
      pre := swapU32SiblingFieldsPre a_ptr b_ptr fieldTy₀ fieldTy₁
        a_old b_old R_frame,
      post := swapU32SiblingFieldsPost a_ptr b_ptr a_old b_old R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    swap_u32_sibling_fields_mirWpConverges a_ptr b_ptr fieldTy₀ fieldTy₁
      a_old b_old R_frame h_R args m₀ hPre)

theorem swap_u32_sibling_fields_total
    (a_ptr b_ptr : RawPtrVal) (fieldTy₀ fieldTy₁ : Ty)
    (a_old b_old : Nat) (R_frame : SepProp) (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := swap_u32,
      pre := swapU32SiblingFieldsPre a_ptr b_ptr fieldTy₀ fieldTy₁
        a_old b_old R_frame,
      post := swapU32SiblingFieldsPost a_ptr b_ptr a_old b_old R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    swap_u32_sibling_fields_mirWpConverges a_ptr b_ptr fieldTy₀ fieldTy₁
      a_old b_old R_frame h_R args m₀ hPre)

/--
Concrete 4-tag `I-10` caller memory on caller slot `4`: an active parent borrow
`&mut s` (tag `1`) over a 3-field aggregate `(a_old, b_old, c_old)` has three
simultaneously active field-granular child reborrows `&mut s.0` (tag `2`),
`&mut s.1` (tag `3`), and `&mut s.2` (tag `4`).
-/
def swapSiblingFieldsDemoMem (a_old b_old c_old : Nat) : Memory :=
  { borrows := [
      { tag := 2, targetLocal := 4,
        targetProjection := [.field 0 { kind := .uint .u32, layoutIdx := 1 }],
        perm := .active, parentTag := some 1 },
      { tag := 3, targetLocal := 4,
        targetProjection := [.field 1 { kind := .uint .u32, layoutIdx := 1 }],
        perm := .active, parentTag := some 1 },
      { tag := 4, targetLocal := 4,
        targetProjection := [.field 2 { kind := .uint .u32, layoutIdx := 1 }],
        perm := .active, parentTag := some 1 },
      { tag := 1, targetLocal := 4, targetProjection := [], perm := .active } ]
    callerLocals := [
      .dead, .dead, .dead, .dead,
      .init (.aggregate 0 [
        .scalar ⟨a_old, 4⟩,
        .scalar ⟨b_old, 4⟩,
        .scalar ⟨c_old, 4⟩
      ]) ] }

def demoField2Ptr : RawPtrVal := { allocId := 4, offset := 0, tag := 4 }

theorem swap_u32_sibling_fields_demo_pre (a_old b_old c_old : Nat) :
    swapU32SiblingFieldsPre demoField0Ptr demoField1Ptr
      { kind := .uint .u32, layoutIdx := 1 }
      { kind := .uint .u32, layoutIdx := 1 }
      a_old b_old
      (sepConj
        (BorrowToken swapPairParentPtr .active)
        (ActiveTypedFieldMutBorrow demoField2Ptr 2
          (ValueCodec.scalarNat 4) c_old))
      [.ptr demoField0Ptr.toMirPtr 8, .ptr demoField1Ptr.toMirPtr 8]
      (swapSiblingFieldsDemoMem a_old b_old c_old) := by
  let m := swapSiblingFieldsDemoMem a_old b_old c_old
  have hAbove : ∀ b ∈ m.borrows, 4 ≤ b.targetLocal := by
    intro b hb
    simp only [m, swapSiblingFieldsDemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide
  refine ⟨rfl, rfl, ⟨rfl, rfl, hAbove, by decide, ⟨rfl, ?_, ?_⟩⟩,
    ⟨rfl, rfl, hAbove, by decide, ⟨rfl, ?_, ?_⟩⟩, ?_⟩
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b hb _
    simp only [swapSiblingFieldsDemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b hb _
    simp only [swapSiblingFieldsDemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
  · let fpR : Footprint := { addrs := [(4, 2)], tags := [1, 4] }
    let fp1R : Footprint := { addrs := [(4, 1), (4, 2)], tags := [3, 1, 4] }
    let fp01R : Footprint :=
      { addrs := [(4, 0), (4, 1), (4, 2)], tags := [2, 3, 1, 4] }
    have hR :
        sepConj (BorrowToken swapPairParentPtr .active)
          (ActiveTypedFieldMutBorrow demoField2Ptr 2
            (ValueCodec.scalarNat 4) c_old)
          ⟨m, fpR⟩ := by
      refine ⟨⟨m, { addrs := [], tags := [1] }⟩,
        ⟨m, fieldMutBorrowFootprint demoField2Ptr 2⟩,
        ⟨rfl, rfl,
          by unfold DisjointFootprints fieldMutBorrowFootprint demoField2Ptr
             dsimp only; decide,
          ?_, ?_⟩,
        ⟨⟨_, rfl, rfl, rfl⟩, rfl⟩,
        activeTypedFieldMutBorrow_intro rfl ⟨_, rfl, rfl, rfl⟩⟩
      · intro a; simp [fpR, fieldMutBorrowFootprint, demoField2Ptr]
      · intro t; simp [fpR, fieldMutBorrowFootprint, demoField2Ptr]
    have h1R :
        sepConj
          (ActiveTypedFieldMutBorrow demoField1Ptr 1
            (ValueCodec.scalarNat 4) b_old)
          (sepConj (BorrowToken swapPairParentPtr .active)
            (ActiveTypedFieldMutBorrow demoField2Ptr 2
              (ValueCodec.scalarNat 4) c_old))
          ⟨m, fp1R⟩ := by
      refine ⟨⟨m, fieldMutBorrowFootprint demoField1Ptr 1⟩,
        ⟨m, fpR⟩,
        ⟨rfl, rfl,
          by unfold DisjointFootprints fieldMutBorrowFootprint demoField1Ptr
             dsimp only [fpR]; decide,
          ?_, ?_⟩,
        activeTypedFieldMutBorrow_intro rfl ⟨_, rfl, rfl, rfl⟩, hR⟩
      · intro a; simp [fp1R, fpR, fieldMutBorrowFootprint, demoField1Ptr]
      · intro t; simp [fp1R, fpR, fieldMutBorrowFootprint, demoField1Ptr]
    refine ⟨fp01R, ⟨m, fieldMutBorrowFootprint demoField0Ptr 0⟩,
      ⟨m, fp1R⟩,
      ⟨rfl, rfl,
        by unfold DisjointFootprints fieldMutBorrowFootprint demoField0Ptr
           dsimp only [fp1R]; decide,
        ?_, ?_⟩,
      activeTypedFieldMutBorrow_intro rfl ⟨_, rfl, rfl, rfl⟩, h1R⟩
    · intro a; simp [fp01R, fp1R, fieldMutBorrowFootprint, demoField0Ptr]
    · intro t; simp [fp01R, fp1R, fieldMutBorrowFootprint, demoField0Ptr]

/--
`swap_u32(&mut s.0, &mut s.1)` runs to completion on the concrete 4-tag struct
memory, exchanging `s.0` and `s.1` while preserving both the active parent
borrow `&mut s` (tag `1`) and the active third sibling borrow `&mut s.2`
(tag `4`, still holding `c_old`) in `R_frame`.
-/
theorem swap_u32_sibling_fields_demo_runs (a_old b_old c_old : Nat) :
    MirWpConverges swap_u32
      (initMachineStateWithMemory swap_u32
        [.ptr demoField0Ptr.toMirPtr 8, .ptr demoField1Ptr.toMirPtr 8]
        (swapSiblingFieldsDemoMem a_old b_old c_old))
      (mirNormalPost
        (swapU32SiblingFieldsPost demoField0Ptr demoField1Ptr a_old b_old
          (sepConj
            (BorrowToken swapPairParentPtr .active)
            (ActiveTypedFieldMutBorrow demoField2Ptr 2
              (ValueCodec.scalarNat 4) c_old))
          [.ptr demoField0Ptr.toMirPtr 8, .ptr demoField1Ptr.toMirPtr 8]
          (swapSiblingFieldsDemoMem a_old b_old c_old))) :=
  swap_u32_sibling_fields_mirWpConverges demoField0Ptr demoField1Ptr
    { kind := .uint .u32, layoutIdx := 1 }
    { kind := .uint .u32, layoutIdx := 1 }
    a_old b_old _
    (localSepProp_sepConj
      (localSepProp_borrowToken swapPairParentPtr .active)
      (localSepProp_activeTypedFieldMutBorrow demoField2Ptr 2
        (ValueCodec.scalarNat 4) c_old))
    _ _ (swap_u32_sibling_fields_demo_pre a_old b_old c_old)

/--
Precondition for `add_assign_retag` invoked on a field-granular reborrow
`&mut s.0` (`x_ptr`), exercising `LiftRetag` protector attachment and protected
dereference writes over `SepSubplaceLensStateInv`.
-/
def addAssignRetagFieldPre
    (x_ptr : RawPtrVal) (fieldTy : Ty) (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩] ∧
    WfSingleFieldMutBorrow 3 x_ptr 0 fieldTy m₀ ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedFieldMutBorrow x_ptr 0 (ValueCodec.scalarNat 4) x_old)
        R_frame)
      m₀

def addAssignRetagFieldPost
    (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedFieldMutBorrow x_ptr 0 (ValueCodec.scalarNat 4)
          (wrapScalarBits (x_old + d_val) (scalarModulus 4)))
        R_frame)
      m_final

theorem add_assign_retag_field_mirWpConverges
    (x_ptr : RawPtrVal) (fieldTy : Ty) (x_old d_val : Nat)
    (R_frame : SepProp) (h_R : LocalSepProp R_frame)
    (args : List Value) (m₀ : Memory)
    (hPre : addAssignRetagFieldPre x_ptr fieldTy x_old d_val R_frame args m₀) :
    MirWpConverges add_assign_retag
      (initMachineStateWithMemory add_assign_retag args m₀)
      (mirNormalPost
        (addAssignRetagFieldPost x_ptr x_old d_val R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepSubplaceLenses
    (add_assign_retag_lift x_ptr x_old d_val)
    (sepSubplaceLensStateInv_of_sepConj_one_field hSep hWf)
    (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedFieldMutBorrow_preserved_one
    hSep hInv hWf hPres h_R (Or.inl rfl)⟩

theorem add_assign_retag_field_verified
    (x_ptr : RawPtrVal) (fieldTy : Ty) (x_old d_val : Nat)
    (R_frame : SepProp) (h_R : LocalSepProp R_frame) :
    StatefulVerificationResult {
      body := add_assign_retag,
      pre := addAssignRetagFieldPre x_ptr fieldTy x_old d_val R_frame,
      post := addAssignRetagFieldPost x_ptr x_old d_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_retag_field_mirWpConverges x_ptr fieldTy x_old d_val R_frame h_R
      args m₀ hPre)

theorem add_assign_retag_field_total
    (x_ptr : RawPtrVal) (fieldTy : Ty) (x_old d_val : Nat)
    (R_frame : SepProp) (h_R : LocalSepProp R_frame) :
    TotalVerificationResult {
      body := add_assign_retag,
      pre := addAssignRetagFieldPre x_ptr fieldTy x_old d_val R_frame,
      post := addAssignRetagFieldPost x_ptr x_old d_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_retag_field_mirWpConverges x_ptr fieldTy x_old d_val R_frame h_R
      args m₀ hPre)

/--
Precondition for `add_assign_retag` invoked on a field-granular reborrow
`&mut s.f` (`x_ptr`) at an arbitrary field index `fieldIdx : FieldIdx`,
exercising `LiftRetag` protector attachment and protected dereference writes
over `SepSubplaceLensStateInv` with unrestricted `SubplaceLocalSepProp` frame
preservation (preserving sibling field borrows at `fieldIdx' = 0` even when
`fieldIdx > 0`).
-/
def addAssignRetagFieldAnyPre
    (x_ptr : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (x_old d_val : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩] ∧
    WfSingleFieldMutBorrow 3 x_ptr fieldIdx fieldTy m₀ ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedFieldMutBorrow x_ptr fieldIdx (ValueCodec.scalarNat 4) x_old)
        R_frame)
      m₀

def addAssignRetagFieldAnyPost
    (x_ptr : RawPtrVal) (fieldIdx : FieldIdx) (x_old d_val : Nat)
    (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedFieldMutBorrow x_ptr fieldIdx (ValueCodec.scalarNat 4)
          (wrapScalarBits (x_old + d_val) (scalarModulus 4)))
        R_frame)
      m_final

theorem add_assign_retag_field_any_mirWpConverges
    (x_ptr : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (x_old d_val : Nat)
    (R_frame : SepProp) (h_R : SubplaceLocalSepProp R_frame)
    (args : List Value) (m₀ : Memory)
    (hPre : addAssignRetagFieldAnyPre x_ptr fieldIdx fieldTy x_old d_val
      R_frame args m₀) :
    MirWpConverges add_assign_retag
      (initMachineStateWithMemory add_assign_retag args m₀)
      (mirNormalPost
        (addAssignRetagFieldAnyPost x_ptr fieldIdx x_old d_val R_frame
          args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepSubplaceLenses
    (add_assign_retag_lift x_ptr x_old d_val)
    (sepSubplaceLensStateInv_of_sepConj_one_field hSep hWf)
    (fun m_final hInv hPres => ?_)
  rw [updateLensVal_singleton_self] at hInv
  exact ⟨rfl, sepConj_activeTypedFieldMutBorrow_preserved_one_subplace
    hSep hInv hWf hPres h_R⟩

theorem add_assign_retag_field_any_verified
    (x_ptr : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (x_old d_val : Nat)
    (R_frame : SepProp) (h_R : SubplaceLocalSepProp R_frame) :
    StatefulVerificationResult {
      body := add_assign_retag,
      pre := addAssignRetagFieldAnyPre x_ptr fieldIdx fieldTy x_old d_val
        R_frame,
      post := addAssignRetagFieldAnyPost x_ptr fieldIdx x_old d_val R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_retag_field_any_mirWpConverges x_ptr fieldIdx fieldTy x_old d_val
      R_frame h_R args m₀ hPre)

theorem add_assign_retag_field_any_total
    (x_ptr : RawPtrVal) (fieldIdx : FieldIdx) (fieldTy : Ty)
    (x_old d_val : Nat)
    (R_frame : SepProp) (h_R : SubplaceLocalSepProp R_frame) :
    TotalVerificationResult {
      body := add_assign_retag,
      pre := addAssignRetagFieldAnyPre x_ptr fieldIdx fieldTy x_old d_val
        R_frame,
      post := addAssignRetagFieldAnyPost x_ptr fieldIdx x_old d_val R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    add_assign_retag_field_any_mirWpConverges x_ptr fieldIdx fieldTy x_old d_val
      R_frame h_R args m₀ hPre)

theorem add_assign_retag_field1_demo_pre (a_old b_old c_old d_val : Nat) :
    addAssignRetagFieldAnyPre demoField1Ptr 1
      { kind := .uint .u32, layoutIdx := 1 }
      b_old d_val
      (sepConj
        (ActiveTypedFieldMutBorrow demoField0Ptr 0
          (ValueCodec.scalarNat 4) a_old)
        (sepConj
          (BorrowToken swapPairParentPtr .active)
          (ActiveTypedFieldMutBorrow demoField2Ptr 2
            (ValueCodec.scalarNat 4) c_old)))
      [.ptr demoField1Ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩]
      (swapSiblingFieldsDemoMem a_old b_old c_old) := by
  let m := swapSiblingFieldsDemoMem a_old b_old c_old
  have hAbove : ∀ b ∈ m.borrows, 3 ≤ b.targetLocal := by
    intro b hb
    simp only [m, swapSiblingFieldsDemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide
  refine ⟨rfl, ⟨rfl, rfl, hAbove, by decide, ⟨rfl, ?_, ?_⟩⟩, ?_⟩
  · exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro b hb _
    simp only [swapSiblingFieldsDemoMem, List.mem_cons, List.not_mem_nil,
      or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inl ⟨rfl, rfl⟩
  · let fpR : Footprint := { addrs := [(4, 2)], tags := [1, 4] }
    let fp0R : Footprint := { addrs := [(4, 0), (4, 2)], tags := [2, 1, 4] }
    let fp10R : Footprint :=
      { addrs := [(4, 1), (4, 0), (4, 2)], tags := [3, 2, 1, 4] }
    have hR :
        sepConj (BorrowToken swapPairParentPtr .active)
          (ActiveTypedFieldMutBorrow demoField2Ptr 2
            (ValueCodec.scalarNat 4) c_old)
          ⟨m, fpR⟩ := by
      refine ⟨⟨m, { addrs := [], tags := [1] }⟩,
        ⟨m, fieldMutBorrowFootprint demoField2Ptr 2⟩,
        ⟨rfl, rfl,
          by unfold DisjointFootprints fieldMutBorrowFootprint demoField2Ptr
             dsimp only; decide,
          ?_, ?_⟩,
        ⟨⟨_, rfl, rfl, rfl⟩, rfl⟩,
        activeTypedFieldMutBorrow_intro rfl ⟨_, rfl, rfl, rfl⟩⟩
      · intro a; simp [fpR, fieldMutBorrowFootprint, demoField2Ptr]
      · intro t; simp [fpR, fieldMutBorrowFootprint, demoField2Ptr]
    have h0R :
        sepConj
          (ActiveTypedFieldMutBorrow demoField0Ptr 0
            (ValueCodec.scalarNat 4) a_old)
          (sepConj (BorrowToken swapPairParentPtr .active)
            (ActiveTypedFieldMutBorrow demoField2Ptr 2
              (ValueCodec.scalarNat 4) c_old))
          ⟨m, fp0R⟩ := by
      refine ⟨⟨m, fieldMutBorrowFootprint demoField0Ptr 0⟩,
        ⟨m, fpR⟩,
        ⟨rfl, rfl,
          by unfold DisjointFootprints fieldMutBorrowFootprint demoField0Ptr
             dsimp only [fpR]; decide,
          ?_, ?_⟩,
        activeTypedFieldMutBorrow_intro rfl ⟨_, rfl, rfl, rfl⟩, hR⟩
      · intro a; simp [fp0R, fpR, fieldMutBorrowFootprint, demoField0Ptr]
      · intro t; simp [fp0R, fpR, fieldMutBorrowFootprint, demoField0Ptr]
    refine ⟨fp10R, ⟨m, fieldMutBorrowFootprint demoField1Ptr 1⟩,
      ⟨m, fp0R⟩,
      ⟨rfl, rfl,
        by unfold DisjointFootprints fieldMutBorrowFootprint demoField1Ptr
           dsimp only [fp0R]; decide,
        ?_, ?_⟩,
      activeTypedFieldMutBorrow_intro rfl ⟨_, rfl, rfl, rfl⟩, h0R⟩
    · intro a; simp [fp10R, fp0R, fieldMutBorrowFootprint, demoField1Ptr]
    · intro t; simp [fp10R, fp0R, fieldMutBorrowFootprint, demoField1Ptr]

/--
`add_assign_retag(&mut s.1, d_val)` runs to completion on the concrete 4-tag
struct memory `swapSiblingFieldsDemoMem a_old b_old c_old`, mutating field `1`
(`&mut s.1`, tag `3`) under a function-entry protector retag while preserving
the sibling borrow on field `0` (`&mut s.0`, tag `2`, whose footprint contains
`(4, 0)`), the active parent borrow `&mut s` (tag `1`), and the sibling borrow
on field `2` (`&mut s.2`, tag `4`) in `R_frame`.
-/
theorem add_assign_retag_field1_demo_runs (a_old b_old c_old d_val : Nat) :
    MirWpConverges add_assign_retag
      (initMachineStateWithMemory add_assign_retag
        [.ptr demoField1Ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩]
        (swapSiblingFieldsDemoMem a_old b_old c_old))
      (mirNormalPost
        (addAssignRetagFieldAnyPost demoField1Ptr 1 b_old d_val
          (sepConj
            (ActiveTypedFieldMutBorrow demoField0Ptr 0
              (ValueCodec.scalarNat 4) a_old)
            (sepConj
              (BorrowToken swapPairParentPtr .active)
              (ActiveTypedFieldMutBorrow demoField2Ptr 2
                (ValueCodec.scalarNat 4) c_old)))
          [.ptr demoField1Ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩]
          (swapSiblingFieldsDemoMem a_old b_old c_old))) :=
  add_assign_retag_field_any_mirWpConverges demoField1Ptr 1
    { kind := .uint .u32, layoutIdx := 1 }
    b_old d_val _
    (subplaceLocalSepProp_sepConj
      (subplaceLocalSepProp_activeTypedFieldMutBorrow demoField0Ptr 0
        (ValueCodec.scalarNat 4) a_old)
      (subplaceLocalSepProp_sepConj
        (subplaceLocalSepProp_borrowToken swapPairParentPtr .active)
        (subplaceLocalSepProp_activeTypedFieldMutBorrow demoField2Ptr 2
          (ValueCodec.scalarNat 4) c_old)))
    _ _ (add_assign_retag_field1_demo_pre a_old b_old c_old d_val)

/--
`Runtime(PostCleanup)` MIR of
`pub fn swap_pair_tuple_rvalue(p: &mut (u32, u32)) { *p = ((*p).1, (*p).0); }`:
exercises `LiftLensRvalue.aggregate_tuple`, `LiftLensOperands`, and
`LiftLensOperandAny.deref_field` directly inside a single aggregate assignment
`(*_1) = (copy ((*_1).1), copy ((*_1).0))`.
-/
def swap_pair_tuple_rvalue : CapturedMir :=
  { swap_pair_u32 with
    defPath := "demo::swap_pair_tuple_rvalue"
    localDecls := [
      { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
        debugName := some "_0" },
      { mutability := .not,
        ty := {
          kind := .ref .mut (.tuple [.uint .u32, .uint .u32]),
          layoutIdx := 3
        },
        debugName := some "p" }
    ]
    basicBlocks := [
      { statements := [
          { kind := .assign { local_ := 1, projection := [.deref] }
              (.aggregate .tuple [
                .copy {
                  local_ := 1,
                  projection := [
                    .deref,
                    .field 1 { kind := .uint .u32, layoutIdx := 1 }
                  ]
                },
                .copy {
                  local_ := 1,
                  projection := [
                    .deref,
                    .field 0 { kind := .uint .u32, layoutIdx := 1 }
                  ]
                }
              ]),
            span := "swap_pair_tuple_rvalue" },
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.constant {
                ty := { kind := .tuple [], layoutIdx := 0 },
                val := .zeroSized
              })),
            span := "swap_pair_tuple_rvalue" }
        ],
        terminator := { kind := .return_, span := "swap_pair_tuple_rvalue" },
        isCleanup := false
      }
    ] }

def swapPairTupleRvaluePre
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr p_ptr.toMirPtr 8] ∧
    WfSingleMutBorrow 2 p_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow p_ptr ValueCodec.pairU32 (a_old, b_old))
        R_frame)
      m₀

theorem swap_pair_tuple_rvalue_lift (p_ptr : RawPtrVal) (a_old b_old : Nat) :
    LiftLensBlock swap_pair_tuple_rvalue 0
      (initMachineState swap_pair_tuple_rvalue
        [.ptr p_ptr.toMirPtr 8]).frame.locals
      [(p_ptr, ValueCodec.pairU32.encode (a_old, b_old))]
      .unit
      [(p_ptr, ValueCodec.pairU32.encode (b_old, a_old))] := by
  unfold initMachineState
  dsimp [swap_pair_tuple_rvalue, swap_pair_u32, initLocalsAux,
    ValueCodec.pairU32, ValueCodec.prod, ValueCodec.scalarNat]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr p_ptr.toMirPtr 8)])
    rfl rfl rfl ?_ rfl
  refine .cons (.derefWrite (.mk
    (.aggregate_tuple
      (.cons (.deref_field (.copy_deref_field rfl
        (lookupLensVal?_singleton_self _ _) rfl))
      (.cons (.deref_field (.copy_deref_field rfl
        (lookupLensVal?_singleton_self _ _) rfl))
      .nil)))
    rfl (lookupLensVal?_singleton_self _ _))) ?_
  rw [updateLensVal_singleton_self]
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
  exact .nil

theorem swap_pair_tuple_rvalue_mirWpConverges
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame)
    (args : List Value) (m₀ : Memory)
    (hPre : swapPairTupleRvaluePre p_ptr a_old b_old R_frame args m₀) :
    MirWpConverges swap_pair_tuple_rvalue
      (initMachineStateWithMemory swap_pair_tuple_rvalue args m₀)
      (mirNormalPost (swapPairU32Post p_ptr a_old b_old R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses
    (swap_pair_tuple_rvalue_lift p_ptr a_old b_old)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one_of_rootAlloc
    hSep hInv hWf hPres h_R h_rootR⟩

theorem swap_pair_tuple_rvalue_verified
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame) :
    StatefulVerificationResult {
      body := swap_pair_tuple_rvalue,
      pre := swapPairTupleRvaluePre p_ptr a_old b_old R_frame,
      post := swapPairU32Post p_ptr a_old b_old R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    swap_pair_tuple_rvalue_mirWpConverges p_ptr a_old b_old R_frame h_R h_rootR
      args m₀ hPre)

theorem swap_pair_tuple_rvalue_total
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame) :
    TotalVerificationResult {
      body := swap_pair_tuple_rvalue,
      pre := swapPairTupleRvaluePre p_ptr a_old b_old R_frame,
      post := swapPairU32Post p_ptr a_old b_old R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    swap_pair_tuple_rvalue_mirWpConverges p_ptr a_old b_old R_frame h_R h_rootR
      args m₀ hPre)

/--
`Runtime(PostCleanup)` MIR of
`pub fn step_fib_pair_adt(p: &mut PairU32) { let next = p.a.wrapping_add(p.b);
*p = PairU32 { a: p.b, b: next }; }`: exercises `LiftLensRvalue.binaryOp_add`
over two `LiftLensOperandAny.deref_field` operands together with
`LiftLensRvalue.aggregate_adt` (`AggregateKind.adt "demo::PairU32" 0 none`) and
`LiftLensOperands` mixing deref-field and moved local operands.
-/
def step_fib_pair_adt : CapturedMir :=
  { swap_pair_u32 with
    defPath := "demo::step_fib_pair_adt"
    localDecls := [
      { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 },
        debugName := some "_0" },
      { mutability := .not,
        ty := {
          kind := .ref .mut (.adt "demo::PairU32" []),
          layoutIdx := 3
        },
        debugName := some "p" },
      { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 1 },
        debugName := some "next" }
    ]
    basicBlocks := [
      { statements := [
          { kind := .storageLive 2, span := "step_fib_pair_adt" },
          { kind := .assign { local_ := 2, projection := [] }
              (.binaryOp .add
                (.copy {
                  local_ := 1,
                  projection := [
                    .deref,
                    .field 0 { kind := .uint .u32, layoutIdx := 1 }
                  ]
                })
                (.copy {
                  local_ := 1,
                  projection := [
                    .deref,
                    .field 1 { kind := .uint .u32, layoutIdx := 1 }
                  ]
                })),
            span := "step_fib_pair_adt" },
          { kind := .assign { local_ := 1, projection := [.deref] }
              (.aggregate (.adt "demo::PairU32" 0 none) [
                .copy {
                  local_ := 1,
                  projection := [
                    .deref,
                    .field 1 { kind := .uint .u32, layoutIdx := 1 }
                  ]
                },
                .move { local_ := 2, projection := [] }
              ]),
            span := "step_fib_pair_adt" },
          { kind := .storageDead 2, span := "step_fib_pair_adt" },
          { kind := .assign { local_ := 0, projection := [] }
              (.use (.constant {
                ty := { kind := .tuple [], layoutIdx := 0 },
                val := .zeroSized
              })),
            span := "step_fib_pair_adt" }
        ],
        terminator := { kind := .return_, span := "step_fib_pair_adt" },
        isCleanup := false
      }
    ] }

def stepFibPairAdtPre
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Prop :=
  fun args m₀ =>
    args = [.ptr p_ptr.toMirPtr 8] ∧
    WfSingleMutBorrow 3 p_ptr m₀ ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow p_ptr ValueCodec.pairU32 (a_old, b_old))
        R_frame)
      m₀

def stepFibPairAdtPost
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) :
    List Value → Memory → Value → Memory → Prop :=
  fun _ _ retVal m_final =>
    retVal = .unit ∧
    SepProp.holdsIn
      (sepConj
        (ActiveTypedMutBorrow p_ptr ValueCodec.pairU32
          (b_old, wrapScalarBits (a_old + b_old) (scalarModulus 4)))
        R_frame)
      m_final

theorem step_fib_pair_adt_lift (p_ptr : RawPtrVal) (a_old b_old : Nat) :
    LiftLensBlock step_fib_pair_adt 0
      (initMachineState step_fib_pair_adt
        [.ptr p_ptr.toMirPtr 8]).frame.locals
      [(p_ptr, ValueCodec.pairU32.encode (a_old, b_old))]
      .unit
      [(p_ptr, ValueCodec.pairU32.encode
        (b_old, wrapScalarBits (Nat.add a_old b_old) (scalarModulus 4)))] := by
  unfold initMachineState
  dsimp [step_fib_pair_adt, swap_pair_u32, initLocalsAux,
    ValueCodec.pairU32, ValueCodec.prod, ValueCodec.scalarNat]
  refine LiftLensBlock.return_
    (env' := [.init .unit, .init (.ptr p_ptr.toMirPtr 8), .dead])
    rfl rfl rfl ?_ rfl
  refine .cons (.storageLive (.mk (oldSlot := .dead)
    (env' := [.uninit, .init (.ptr p_ptr.toMirPtr 8), .uninit])
    rfl rfl)) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.binaryOp_add (by decide)
      (.deref_field (.copy_deref_field rfl
        (lookupLensVal?_singleton_self _ _) rfl))
      (.deref_field (.copy_deref_field rfl
        (lookupLensVal?_singleton_self _ _) rfl)))
    rfl (fun h => nomatch h) rfl)) ?_
  refine .cons (.derefWrite (.mk
    (.aggregate_adt
      (.cons (.deref_field (.copy_deref_field rfl
        (lookupLensVal?_singleton_self _ _) rfl))
      (.cons (.pure (.move_local rfl rfl))
      .nil)))
    rfl (lookupLensVal?_singleton_self _ _))) ?_
  rw [updateLensVal_singleton_self]
  refine .cons (.storageDead (.mk rfl rfl)) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
    (.use_pure .const_zeroSized rfl) rfl (fun h => nomatch h) rfl)) ?_
  exact .nil

theorem step_fib_pair_adt_mirWpConverges
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame)
    (args : List Value) (m₀ : Memory)
    (hPre : stepFibPairAdtPre p_ptr a_old b_old R_frame args m₀) :
    MirWpConverges step_fib_pair_adt
      (initMachineStateWithMemory step_fib_pair_adt args m₀)
      (mirNormalPost (stepFibPairAdtPost p_ptr a_old b_old R_frame args m₀)) := by
  rcases hPre with ⟨rfl, hWf, hSep⟩
  refine mirWpConverges_of_sepLenses
    (step_fib_pair_adt_lift p_ptr a_old b_old)
    (sepLensStateInv_of_sepConj_one hSep hWf) (fun m_final hInv hPres => ?_)
  exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one_of_rootAlloc
    hSep hInv hWf hPres h_R h_rootR⟩

theorem step_fib_pair_adt_verified
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame) :
    StatefulVerificationResult {
      body := step_fib_pair_adt,
      pre := stepFibPairAdtPre p_ptr a_old b_old R_frame,
      post := stepFibPairAdtPost p_ptr a_old b_old R_frame
    } :=
  verifyStatefulMirNoPanic_of_wpConverges _ (fun args m₀ hPre =>
    step_fib_pair_adt_mirWpConverges p_ptr a_old b_old R_frame h_R h_rootR
      args m₀ hPre)

theorem step_fib_pair_adt_total
    (p_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp)
    (h_R : LocalSepProp R_frame) (h_rootR : RootAllocSepProp R_frame) :
    TotalVerificationResult {
      body := step_fib_pair_adt,
      pre := stepFibPairAdtPre p_ptr a_old b_old R_frame,
      post := stepFibPairAdtPost p_ptr a_old b_old R_frame
    } :=
  verifyTotalMir_of_wpConverges _ (fun args m₀ hPre =>
    step_fib_pair_adt_mirWpConverges p_ptr a_old b_old R_frame h_R h_rootR
      args m₀ hPre)


end Anneal.SepLogicLenses

