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

/-!
# Separation-Logic-Backed Mutable Lenses & Pure Deref Lifting (`FF-4.1`)

This module connects Anneal's separation logic (`SepProp`, `sepConj`,
`DisjointFootprints`, `ActiveTypedMutBorrow`) and functional lens layer
(`MutLens`, `LawfulMutLens`, `memoryPtrMutLens`) to fuel-free `ITree` weakest
preconditions (`MirWpConverges`, `StatefulVerificationResult`,
`TotalVerificationResult`) over the `I-10` Tree Borrows and 12-field `Memory`
model. No proof here destructures the `Memory` record.

1. **Section 1 (lens algebra).** `IndependentLenses`, `prodMutLens`, and
   `PairwiseIndependentLenses`, with the binary bridge
   `sepConj_entails_independentLenses`: two separated active typed mutable
   borrows have distinct allocations and tags and lawful, independent lenses.
2. **Section 2 (lifting).** The lens-state invariant `SepLensStateInv` (whose
   per-pointer exclusivity `TreeExclusiveBorrow` admits active `I-10`
   ancestors), the frame relation `LensFramePreserved`, and the lifting
   judgments `LiftDerefRead`, `LiftDerefWrite`, `LiftRetag`, `LiftLensRvalue`
   (any scalar `BinOp` over pure or deref operands), `LiftLensStmts`, and the
   control-flow judgment `LiftLensBlock` (`return_`, `goto`, `assert`). The
   theorem `mirWpConverges_of_sepLenses` turns a lifting derivation into
   fuel-free convergence on real memory. The `k`-ary bridges over
   `sepConjBindings` (`sepLensStateInv_of_sepConjBindings`,
   `sepConjBindings_preserved`, `sepConjBindings_entails_independentLensFamily`)
   generalize the unary and binary ones, and
   `verifyStatefulMir_of_sepLenses_supportedFrame` frames any
   `SupportedBy R_frame fp_frame` heap predicate.
3. **Section 3 (witnesses).** `MirWpConverges`, `StatefulVerificationResult`,
   and `TotalVerificationResult` for `Runtime(PostCleanup)` MIR of
   `add_assign(x: &mut u32, d: u32)` (wrapping, overflow-checked with an
   `assert` edge, and retagged variants) and
   `swap_u32(a: &mut u32, b: &mut u32)`, plus non-vacuity witnesses on concrete
   memories, including an `I-10` reborrow chain whose parent tag stays active.
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
Domain validity predicate for a single separation-logic-backed mutable borrow
lens `memoryPtrMutLens rp codec`.
-/
structure ValidMutBorrowLens {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) (m : Memory) : Prop where
  has_typed_pointee : ∃ a : α, readAllocAt? (memoryLocals m) rp = some (codec.encode a)
  exclusive : ExclusiveActiveBorrow rp m

/--
`memoryPtrMutLens rp codec` is a `LawfulMutLens` on
`ValidMutBorrowLens rp codec`.
-/
theorem memoryPtrMutLens_lawful {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) :
    LawfulMutLens (memoryPtrMutLens rp codec) (ValidMutBorrowLens rp codec) where
  valid_writeBack a m hm := by
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a hPts hExcl]
    refine ⟨⟨a, ?_⟩,
      ExclusiveActiveBorrow.of_borrows_eq hExcl (updateMemoryLocals_borrows _ _)⟩
    unfold readAllocAt?
    rw [memoryLocals_updateMemoryLocals, hExcl.offset_zero]
    unfold readAllocAt? at hPts
    rw [hExcl.offset_zero] at hPts
    cases hGet : get? (memoryLocals m) rp.allocId with
    | none => rw [hGet] at hPts; nomatch hPts
    | some slot =>
      have hLt : rp.allocId < (memoryLocals m).length :=
        (List.getElem?_eq_some_iff.mp hGet).1
      unfold get?
      rw [List.getElem?_set_self hLt]
  readView_writeBack a m hm := by
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a hPts hExcl]
    unfold memoryPtrMutLens
    dsimp only
    unfold readAllocAt?
    rw [memoryLocals_updateMemoryLocals, hExcl.offset_zero]
    unfold readAllocAt? at hPts
    rw [hExcl.offset_zero] at hPts
    cases hGet : get? (memoryLocals m) rp.allocId with
    | none => rw [hGet] at hPts; nomatch hPts
    | some slot =>
      have hLt : rp.allocId < (memoryLocals m).length :=
        (List.getElem?_eq_some_iff.mp hGet).1
      unfold get?
      rw [List.getElem?_set_self hLt]
      simp
  writeBack_readView m hm := by
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    have hRead : (memoryPtrMutLens rp codec).readView m = a₀ :=
      memoryPtrMutLens_readView_of_readAllocAt hPts
    rw [hRead]
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a₀ hPts hExcl]
    unfold readAllocAt? at hPts
    rw [hExcl.offset_zero] at hPts
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
  writeBack_writeBack a₁ a₂ m hm := by
    have hm₁ : ValidMutBorrowLens rp codec
        ((memoryPtrMutLens rp codec).writeBack a₁ m) := by
      rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
      rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a₁ hPts hExcl]
      refine ⟨⟨a₁, ?_⟩,
        ExclusiveActiveBorrow.of_borrows_eq hExcl
          (updateMemoryLocals_borrows _ _)⟩
      unfold readAllocAt?
      rw [memoryLocals_updateMemoryLocals, hExcl.offset_zero]
      unfold readAllocAt? at hPts
      rw [hExcl.offset_zero] at hPts
      cases hGet : get? (memoryLocals m) rp.allocId with
      | none => rw [hGet] at hPts; nomatch hPts
      | some slot =>
        have hLt : rp.allocId < (memoryLocals m).length :=
          (List.getElem?_eq_some_iff.mp hGet).1
        unfold get?
        rw [List.getElem?_set_self hLt]
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    rcases hm₁ with ⟨⟨a₁', hPts₁⟩, hExcl₁⟩
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a₂ hPts₁ hExcl₁]
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a₁ hPts hExcl]
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp codec a₂ hPts hExcl]
    rw [memoryLocals_updateMemoryLocals, list_set_set_self,
      updateMemoryLocals_updateMemoryLocals]

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

private theorem pointsTo_updateMemoryLocals_set_ne
    {rp₁ rp₂ : RawPtrVal} {v₂ newVal : Value} {m : Memory}
    (hNe : rp₁.allocId ≠ rp₂.allocId)
    (hOff₂ : rp₂.offset = 0)
    (hPts₂ : readAllocAt? (memoryLocals m) rp₂ = some v₂) :
    readAllocAt? (memoryLocals (updateMemoryLocals m ((memoryLocals m).set rp₁.allocId (.init newVal))) ) rp₂ = some v₂:= by
  unfold readAllocAt? at hPts₂ ⊢
  rw [memoryLocals_updateMemoryLocals, hOff₂]
  rw [hOff₂] at hPts₂
  unfold get? at hPts₂ ⊢
  rw [List.getElem?_set_ne hNe]
  exact hPts₂

/--
Two `memoryPtrMutLens` instances on distinct allocations
(`rp₁.allocId ≠ rp₂.allocId`) satisfy `IndependentLenses` on
`ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂`.
-/
theorem memoryPtrMutLens_independent_of_ne_alloc {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    IndependentLenses
      (memoryPtrMutLens rp₁ codec₁)
      (memoryPtrMutLens rp₂ codec₂)
      (ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) where
  valid_writeBack_left a m hm := by
    refine ⟨
      (memoryPtrMutLens_lawful rp₁ codec₁).valid_writeBack a m hm.valid_left,
      ?_, hm.ne_alloc⟩
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁ hExcl₁]
    exact ⟨
      ⟨b₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc hExcl₂.offset_zero hPts₂⟩,
      ExclusiveActiveBorrow.of_borrows_eq hExcl₂
        (updateMemoryLocals_borrows _ _)⟩
  valid_writeBack_right b m hm := by
    refine ⟨?_,
      (memoryPtrMutLens_lawful rp₂ codec₂).valid_writeBack b m hm.valid_right,
      hm.ne_alloc⟩
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂ hExcl₂]
    exact ⟨
      ⟨a₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
        hExcl₁.offset_zero hPts₁⟩,
      ExclusiveActiveBorrow.of_borrows_eq hExcl₁
        (updateMemoryLocals_borrows _ _)⟩
  readView_right_of_writeBack_left a m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [memoryPtrMutLens_readView_of_readAllocAt hPts₂]
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁ hExcl₁]
    exact memoryPtrMutLens_readView_of_readAllocAt
      (pointsTo_updateMemoryLocals_set_ne hm.ne_alloc hExcl₂.offset_zero hPts₂)
  readView_left_of_writeBack_right b m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [memoryPtrMutLens_readView_of_readAllocAt hPts₁]
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂ hExcl₂]
    exact memoryPtrMutLens_readView_of_readAllocAt
      (pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
        hExcl₁.offset_zero hPts₁)
  writeBack_comm a b m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    have hPts₂' :
        readAllocAt? (memoryLocals ((memoryPtrMutLens rp₁ codec₁).writeBack a m)) rp₂ =
          some (codec₂.encode b₀) := by
      rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁ hExcl₁]
      exact pointsTo_updateMemoryLocals_set_ne hm.ne_alloc
        hExcl₂.offset_zero hPts₂
    have hExcl₂' :
        ExclusiveActiveBorrow rp₂
          ((memoryPtrMutLens rp₁ codec₁).writeBack a m) := by
      rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁ hExcl₁]
      exact ExclusiveActiveBorrow.of_borrows_eq hExcl₂
        (updateMemoryLocals_borrows _ _)
    have hPts₁' :
        readAllocAt? (memoryLocals ((memoryPtrMutLens rp₂ codec₂).writeBack b m)) rp₁ =
          some (codec₁.encode a₀) := by
      rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂ hExcl₂]
      exact pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
        hExcl₁.offset_zero hPts₁
    have hExcl₁' :
        ExclusiveActiveBorrow rp₁
          ((memoryPtrMutLens rp₂ codec₂).writeBack b m) := by
      rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂ hExcl₂]
      exact ExclusiveActiveBorrow.of_borrows_eq hExcl₁
        (updateMemoryLocals_borrows _ _)
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂' hExcl₂']
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁' hExcl₁']
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₁ codec₁ a hPts₁ hExcl₁]
    rw [memoryPtrMutLens_writeBack_eq_of_exclusive rp₂ codec₂ b hPts₂ hExcl₂]
    rw [memoryLocals_updateMemoryLocals, memoryLocals_updateMemoryLocals]
    rw [updateMemoryLocals_updateMemoryLocals,
      updateMemoryLocals_updateMemoryLocals]
    rw [list_set_comm (memoryLocals m) hm.ne_alloc]

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
inductive LiftLensOperand :
    PureEnv → Operand → Value → PureEnv → Prop where
  | copy_local {env : PureEnv} {loc : Local} {v : Value} :
      get? env loc = .some (.init v) →
      LiftLensOperand env (.copy { local_ := loc, projection := [] }) v env
  | move_local {env env' : PureEnv} {loc : Local} {v : Value} :
      get? env loc = .some (.init v) →
      set? env loc .uninit = .some env' →
      LiftLensOperand env (.move { local_ := loc, projection := [] }) v env'
  | copy_field {env : PureEnv} {loc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
      {rootVal v : Value} :
      get? env loc = .some (.init rootVal) →
      readProjectedValue env rootVal [.field fieldIdx fieldTy] = .ok v →
      LiftLensOperand env
        (.copy { local_ := loc, projection := [.field fieldIdx fieldTy] }) v env
  | move_field {env : PureEnv} {loc : Local} {fieldIdx : FieldIdx} {fieldTy : Ty}
      {rootVal v : Value} :
      get? env loc = .some (.init rootVal) →
      readProjectedValue env rootVal [.field fieldIdx fieldTy] = .ok v →
      LiftLensOperand env
        (.move { local_ := loc, projection := [.field fieldIdx fieldTy] }) v env
  | const_scalar {env : PureEnv} {ty : Ty} {sc : ScalarInt} :
      LiftLensOperand
        env
        (.constant { ty := ty, val := .scalar (.int sc) })
        (.scalar sc)
        env
  | const_zeroSized {env : PureEnv} {ty : Ty} :
      LiftLensOperand
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
Unified operand lifting: a pure local or constant operand (`LiftLensOperand`)
or a separation-logic lens dereference read (`LiftDerefRead`). It lets compound
rvalues such as `Add(copy (*_1), copy _2)` read pointees directly, as rustc
emits them for `*x += d`.
-/
inductive LiftLensOperandAny :
    PureEnv → List (RawPtrVal × Value) → Operand → Value → PureEnv → Prop where
  | pure {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftLensOperand env op v env' →
      LiftLensOperandAny env entries op v env'
  | deref {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftDerefRead env entries op v env' →
      LiftLensOperandAny env entries op v env'

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
      LiftLensOperand env op v env' →
      LiftLensRvalue localDecls layouts env entries (.use op) v env'
  | use_deref
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {v : Value} :
      LiftDerefRead env entries op v env' →
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
      LiftLensOperandAny env entries lhsOp (.scalar lhs) env₁ →
      LiftLensOperandAny env₁ entries rhsOp (.scalar rhs) env₂ →
      (∀ mem : Memory,
        evalScalarBinOp op lhs rhs env₂ mem
            (operandIsSigned localDecls lhsOp layouts) =
          .ok v env₂ mem) →
      LiftLensRvalue localDecls layouts env entries
        (.binaryOp op lhsOp rhsOp) v env₂
  | unaryOp_not
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {sc : ScalarInt} {v : Value} :
      LiftLensOperandAny env entries op (.scalar sc) env' →
      (∀ mem : Memory,
        evalUnaryNot sc (operandTy localDecls layouts op) env' mem =
          .ok v env' mem) →
      LiftLensRvalue localDecls layouts env entries
        (.unaryOp .not op) v env'
  | unaryOp_neg
      {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
      {op : Operand} {sc : ScalarInt} :
      LiftLensOperandAny env entries op (.scalar sc) env' →
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
      LiftLensOperandAny env entries op (.scalar sc) env' →
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

/--
Wrapping `Add` instance of `LiftLensRvalue.binaryOp` at any non-zero scalar
width, with either operand possibly a lens dereference read.
-/
theorem LiftLensRvalue.binaryOp_add
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env₁ env₂ : PureEnv} {entries : List (RawPtrVal × Value)}
    {lhsOp rhsOp : Operand} {a b sz : Nat}
    (hSz : sz ≠ 0)
    (hLhs : LiftLensOperandAny env entries lhsOp (.scalar ⟨a, sz⟩) env₁)
    (hRhs : LiftLensOperandAny env₁ entries rhsOp (.scalar ⟨b, sz⟩) env₂) :
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
`*ptrLoc` in the pure lens environment `entries` via `updateLensVal`.
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
      body.phase = .runtimePostCleanup →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .return_ →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env' entries' →
      get? env' 0 = .some (.init retVal) →
      LiftLensBlock body bbIdx env entries retVal entries'
  | goto
      {bbIdx target : BasicBlockIdx} {bb : BasicBlockData} {env env₁ : PureEnv}
      {entries entries₁ entries' : List (RawPtrVal × Value)} {retVal : Value} :
      body.phase = .runtimePostCleanup →
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
      body.phase = .runtimePostCleanup →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .assert cond expected target unwind →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env₁ entries₁ →
      LiftLensOperandAny env₁ entries₁ cond (.scalar sc) env₂ →
      sc.bits = assertBit expected →
      LiftLensBlock body target env₂ entries₁ retVal entries' →
      LiftLensBlock body bbIdx env entries retVal entries'
  | switchInt
      {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
      {discr : Operand} {targets : SwitchTargets}
      {env env₁ env₂ : PureEnv} {sc : ScalarInt}
      {entries entries₁ entries' : List (RawPtrVal × Value)} {retVal : Value} :
      body.phase = .runtimePostCleanup →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .switchInt discr targets →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env₁ entries₁ →
      LiftLensOperandAny env₁ entries₁ discr (.scalar sc) env₂ →
      lookupSwitchTarget sc.bits targets.branches targets.otherwise = target →
      LiftLensBlock body target env₂ entries₁ retVal entries' →
      LiftLensBlock body bbIdx env entries retVal entries'
  | drop_local
      {bbIdx target : BasicBlockIdx} {bb : BasicBlockData}
      {loc : Local} {unwind : UnwindAction} {oldSlot : LocalSlot}
      {env env₁ env₂ : PureEnv}
      {entries entries₁ entries' : List (RawPtrVal × Value)} {retVal : Value} :
      body.phase = .runtimePostCleanup →
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
    {env env' : PureEnv} {op : Operand} {v : Value}
    (h : LiftLensOperand env op v env')
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    (callerLocals : List LocalSlot) :
    evalOperand env op borrows globals layouts callerLocals = .ok v env' ∧
    env'.length = env.length := by
  cases h with
  | copy_local hGet =>
    refine ⟨?_, rfl⟩
    simp [evalOperand, hGet, readProjectedValue]
  | move_local hGet hSet =>
    refine ⟨?_, set?_length_eq hSet⟩
    simp [evalOperand, hGet, hSet]
  | copy_field hGet hRead =>
    refine ⟨?_, rfl⟩
    unfold evalOperand
    dsimp only
    rw [hGet]
    dsimp only
    rw [hRead]
  | move_field hGet hRead =>
    refine ⟨?_, rfl⟩
    unfold evalOperand
    dsimp only
    rw [hGet]
    dsimp only
    rw [hRead]
  | const_scalar =>
    exact ⟨rfl, rfl⟩
  | const_zeroSized =>
    exact ⟨rfl, rfl⟩

theorem LiftLensOperand.not_deref
    {env env' : PureEnv} {op : Operand} {v : Value}
    (h : LiftLensOperand env op v env')
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
    (layouts : LayoutTable) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals = .ok v env' ∧
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

/--
Soundness of unified operand lifting: under `SepLensStateInv`, the lifted
operand evaluates to its lifted value against the real borrow table, globals,
and caller locals, without changing the local environment's length.
-/
theorem LiftLensOperandAny.evalOperand_eq
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value} {m : Memory}
    (h : LiftLensOperandAny env entries op v env')
    (hInv : SepLensStateInv env.length entries m)
    (layouts : LayoutTable) :
    evalOperand env op m.borrows m.globals layouts m.callerLocals = .ok v env' ∧
    env'.length = env.length := by
  cases h with
  | pure hOp => exact hOp.evalOperand_eq m.borrows m.globals layouts m.callerLocals
  | deref hDeref =>
    rcases hDeref.evalOperand_and_freeze_eq hInv layouts with ⟨hEval, hEnvEq, _⟩
    subst hEnvEq
    exact ⟨hEval, rfl⟩

theorem LiftLensRvalue.evalRvalue_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {rv : Rvalue} {v : Value} {m : Memory}
    (h : LiftLensRvalue localDecls layouts env entries rv v env')
    (hInv : SepLensStateInv env.length entries m) :
    evalRvalue env rv m localDecls layouts = .ok v env' m ∧
    env'.length = env.length := by
  cases h with
  | use_pure hOp =>
    rcases hOp.evalOperand_eq m.borrows m.globals layouts m.callerLocals with
      ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    simp [hEval]
    exact hOp.not_deref m.borrows m
  | use_deref hDeref =>
    rcases hDeref.evalOperand_and_freeze_eq hInv layouts with
      ⟨hEval, hEnvEq, hFreeze⟩
    subst hEnvEq
    refine ⟨?_, rfl⟩
    unfold evalRvalue
    simp [hEval]
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
  | copyForDeref_deref hGetPtr hLookVal =>
    have hDeref :
        LiftDerefRead env entries
          (.copy { local_ := _, projection := [.deref] }) v env :=
      .copy_deref hGetPtr hLookVal
    rcases hDeref.evalOperand_and_freeze_eq hInv layouts with
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
    rcases hLhs.evalOperand_eq hInv layouts with ⟨hEval₁, hLen₁⟩
    rcases hRhs.evalOperand_eq (by rw [hLen₁]; exact hInv) layouts with
      ⟨hEval₂, hLen₂⟩
    refine ⟨?_, hLen₂.trans hLen₁⟩
    unfold evalRvalue
    dsimp only
    rw [hEval₁]
    dsimp only
    rw [hEval₂]
    exact hEvalOp m
  | unaryOp_not hOp hNot =>
    rcases hOp.evalOperand_eq hInv layouts with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    exact hNot m
  | unaryOp_neg hOp hSz =>
    rcases hOp.evalOperand_eq hInv layouts with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    dsimp only
    rw [hSz]
  | cast_intToInt hOp hSz hTarget =>
    rcases hOp.evalOperand_eq hInv layouts with ⟨hEval, hLen⟩
    refine ⟨?_, hLen⟩
    unfold evalRvalue
    dsimp only
    rw [hEval]
    dsimp only
    rw [hSz, hTarget]
    rfl
  | tuple_nil =>
    exact ⟨rfl, rfl⟩

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
            newVal = .ub := by
        unfold writePlaceValue
        simp only [_root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue, _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr] at hGetPtr ⊢
        simp [hGetPtr, ProvenancePtr.tag, hLookB, hPerm, hP]
        rw [hEnv₁None]
      have hEvalPlaceWriteUb :
          evalPlaceWrite
            env'
            s.memory.borrows
            { local_ := ptrLoc, projection := [.deref] }
            newVal
            s.memory.activeProtectors = .ub := by
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
          dsimp only [extractDerefPtrVal?, ProvenancePtr.tag]
          rw [hLookB]
          cases hB : s.memory.borrows with
          | nil =>
            dsimp only
            rw [← hB]
            exact hWriteCallerOk
          | cons b₁ tl =>
            cases tl with
            | nil =>
              dsimp only
              rw [← hB]
              exact hWriteCallerOk
            | cons b₂ rest =>
              have hNoConflict :
                  hasProtectedTreeWriteConflict
                    (b₁ :: b₂ :: rest)
                    (b₁ :: b₂ :: rest)
                    (pHead :: pTail)
                    entry.targetLocal
                    (.some rp.tag)
                    (resolveDerefWriteFullProj
                      env' s.memory.callerLocals
                      (.ptr { allocId := rp.tag, offsetBytes := rp.offset } 8)
                      entry [])
                    entry.rangeOffset
                    entry.rangeLen = false := by
                rw [hT, ← hB]
                exact hasProtectedTreeWriteConflict_eq_false_of_tree
                  s.memory.borrows s.memory.borrows (pHead :: pTail) _ _ _
                  hExcl.ancestors_active_or_disabled
              dsimp only
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
            dsimp only [extractDerefPtrVal?, ProvenancePtr.tag]
            rw [hLookSingle]
            dsimp only
            unfold resolveDerefWriteFullProj
            rw [hP, hRL]
            dsimp only [
              resolveBorrowProjectionElems,
              needsThinPtrElemResolution,
              stripTransparentProjections,
              normalizeSubsliceProjections]
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
            dsimp only [extractDerefPtrVal?, ProvenancePtr.tag]
            rw [hLookMany]
            dsimp only
            rw [hT, ← hB]
            exact invalidateTreeBorrowsAtProj_eq_self_of_tree
              s.memory.borrows s.memory.borrows _ _ _
              hExcl.ancestors_active_or_disabled
      refine ⟨
        { s.memory with
          callerLocals := s.memory.callerLocals.set rp.allocId (.init newVal) },
        ?_, hLen₁,
        (by rw [hLen₁]; exact hInv.updateDeref hLookVal),
        ?_,
        (updateLensVal_map_fst entries rp newVal).trans hKeys⟩
      · unfold evalStmt
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
      refine ⟨s.memory, ?_, hLen, (by rw [hLen]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      simp [hEnv, hGet, hSet]
  | storageDead hDead =>
    cases hDead with
    | mk hGet hSet =>
      have hLen : env'.length = env.length := set?_length_eq hSet
      refine ⟨s.memory, ?_, hLen, (by rw [hLen]; exact hInv), hFrame, hKeys⟩
      unfold evalStmt
      simp [hEnv, hGet, hSet]
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
    (hPhase : body.phase = .runtimePostCleanup)
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
    apply MirWpConverges.step_tau
    · unfold stepMirFn
      change
        let currentBody := s.memory.activeCallee.getD body
        _ = MirStepNode.step (advanceStmt s env1_ m₁)
      rw [hInv.activeCallee_none]
      dsimp only [Option.getD]
      simp only [hPhase, hBb]
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
    (hPhase : body.phase = .runtimePostCleanup)
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
  unfold stepMirFn
  rw [hCallee]
  dsimp only [Option.getD]
  simp only [hPhase, hBb]
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
    (hPhase : body.phase = .runtimePostCleanup)
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
  unfold stepMirFn
  rw [hCallee]
  dsimp only [Option.getD]
  simp only [hPhase, hBb]
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
    (hPhase : body.phase = .runtimePostCleanup)
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
  unfold stepMirFn
  rw [hCallee]
  dsimp only [Option.getD]
  simp only [hPhase, hBb]
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
    (hPhase : body.phase = .runtimePostCleanup)
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
  unfold stepMirFn
  rw [hCallee]
  dsimp only [Option.getD]
  simp only [hPhase, hBb]
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
    (hPhase : body.phase = .runtimePostCleanup)
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
  unfold stepMirFn
  rw [hCallee]
  dsimp only [Option.getD]
  simp only [hPhase, hBb]
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
    {env env' : PureEnv} {op : Operand} {v : Value}
    (h : LiftLensOperand env op v env') :
    env'.length = env.length := by
  cases h with
  | copy_local _ => rfl
  | move_local _ hSet => exact set?_length_eq hSet
  | copy_field _ _ => rfl
  | move_field _ _ => rfl
  | const_scalar => rfl
  | const_zeroSized => rfl

/-- Unified operand lifting preserves the local slot environment's length. -/
theorem LiftLensOperandAny.length_eq
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {op : Operand} {v : Value}
    (h : LiftLensOperandAny env entries op v env') :
    env'.length = env.length := by
  cases h with
  | pure hOp => exact hOp.length_eq
  | deref hDeref => cases hDeref <;> rfl

theorem LiftLensRvalue.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries : List (RawPtrVal × Value)}
    {rv : Rvalue} {v : Value}
    (h : LiftLensRvalue localDecls layouts env entries rv v env') :
    env'.length = env.length := by
  cases h with
  | use_pure hOp => exact hOp.length_eq
  | use_deref hDeref => cases hDeref <;> rfl
  | copyForDeref_deref _ _ => rfl
  | binaryOp hLhs hRhs _ => exact hRhs.length_eq.trans hLhs.length_eq
  | unaryOp_not hOp _ => exact hOp.length_eq
  | unaryOp_neg hOp _ => exact hOp.length_eq
  | cast_intToInt hOp _ _ => exact hOp.length_eq
  | tuple_nil => rfl

theorem LiftLensStmt.length_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {env env' : PureEnv} {entries entries' : List (RawPtrVal × Value)}
    {stmt : Statement}
    (h : LiftLensStmt localDecls layouts env entries stmt env' entries') :
    env'.length = env.length := by
  cases h with
  | retag hR => cases hR; rfl
  | derefWrite hW => cases hW with | mk hRv _ _ => exact hRv.length_eq
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
    rcases hCond.evalOperand_eq hInv' body.layouts with ⟨hEval, hLen₂⟩
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
    rcases hDiscr.evalOperand_eq hInv' body.layouts with ⟨hEval, hLen₂⟩
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
`I-10`-aware Tree Borrows access step for `rp` on `m`: unlike
`stepTreeBorrowAccess?` (which uses the flat `invalidateConflictingBorrows`
helper), a write access updates permissions with the `I-10` parent/child
invalidation `invalidateTreeBorrowsAtProj`, so active ancestor tags of `rp.tag`
remain `.active` under child writes.
-/
def stepTreeBorrowHierarchyAccess?
    (m : Memory) (rp : RawPtrVal) (isWrite : Bool) : Option Memory :=
  match lookupBorrow m.borrows rp.tag with
  | .some entry =>
    match entry.perm, isWrite with
    | .disabled, _ => .none
    | .frozen, true => .none
    | _, false => .some m
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
`treeMemoryPtrMutLens` and `memoryPtrMutLens` coincide on both `readView` and
`writeBack`.
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

/--
Domain validity predicate for an `I-10`-aware mutable borrow lens
`treeMemoryPtrMutLens rp codec`.
-/
structure ValidTreeMutBorrowLens {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) (m : Memory) : Prop where
  has_typed_pointee : ∃ a : α, readAllocAt? (memoryLocals m) rp = some (codec.encode a)
  exclusive : TreeExclusiveBorrow rp m

theorem ValidMutBorrowLens.toTree {α : Type}
    {rp : RawPtrVal} {codec : ValueCodec α} {m : Memory}
    (h : ValidMutBorrowLens rp codec m) :
    ValidTreeMutBorrowLens rp codec m :=
  ⟨h.has_typed_pointee, h.exclusive.toTree⟩

/--
`treeMemoryPtrMutLens rp codec` is a `LawfulMutLens` on
`ValidTreeMutBorrowLens rp codec` (admitting active `I-10` parent/child
reborrow chains).
-/
theorem treeMemoryPtrMutLens_lawful {α : Type}
    (rp : RawPtrVal) (codec : ValueCodec α) :
    LawfulMutLens (treeMemoryPtrMutLens rp codec)
      (ValidTreeMutBorrowLens rp codec) where
  valid_writeBack a m hm := by
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a hPts hExcl]
    refine ⟨⟨a, ?_⟩,
      TreeExclusiveBorrow.of_borrows_eq hExcl (updateMemoryLocals_borrows _ _)⟩
    unfold readAllocAt?
    rw [memoryLocals_updateMemoryLocals, hExcl.offset_zero]
    unfold readAllocAt? at hPts
    rw [hExcl.offset_zero] at hPts
    cases hGet : get? (memoryLocals m) rp.allocId with
    | none => rw [hGet] at hPts; nomatch hPts
    | some slot =>
      have hLt : rp.allocId < (memoryLocals m).length :=
        (List.getElem?_eq_some_iff.mp hGet).1
      unfold get?
      rw [List.getElem?_set_self hLt]
  readView_writeBack a m hm := by
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a hPts hExcl]
    unfold treeMemoryPtrMutLens memoryPtrMutLens
    dsimp only
    unfold readAllocAt?
    rw [memoryLocals_updateMemoryLocals, hExcl.offset_zero]
    unfold readAllocAt? at hPts
    rw [hExcl.offset_zero] at hPts
    cases hGet : get? (memoryLocals m) rp.allocId with
    | none => rw [hGet] at hPts; nomatch hPts
    | some slot =>
      have hLt : rp.allocId < (memoryLocals m).length :=
        (List.getElem?_eq_some_iff.mp hGet).1
      unfold get?
      rw [List.getElem?_set_self hLt]
      simp
  writeBack_readView m hm := by
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    have hRead : (treeMemoryPtrMutLens rp codec).readView m = a₀ :=
      treeMemoryPtrMutLens_readView_of_readAllocAt hPts
    rw [hRead]
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a₀ hPts hExcl]
    unfold readAllocAt? at hPts
    rw [hExcl.offset_zero] at hPts
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
  writeBack_writeBack a₁ a₂ m hm := by
    have hm₁ : ValidTreeMutBorrowLens rp codec
        ((treeMemoryPtrMutLens rp codec).writeBack a₁ m) := by
      rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
      rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a₁ hPts hExcl]
      refine ⟨⟨a₁, ?_⟩,
        TreeExclusiveBorrow.of_borrows_eq hExcl
          (updateMemoryLocals_borrows _ _)⟩
      unfold readAllocAt?
      rw [memoryLocals_updateMemoryLocals, hExcl.offset_zero]
      unfold readAllocAt? at hPts
      rw [hExcl.offset_zero] at hPts
      cases hGet : get? (memoryLocals m) rp.allocId with
      | none => rw [hGet] at hPts; nomatch hPts
      | some slot =>
        have hLt : rp.allocId < (memoryLocals m).length :=
          (List.getElem?_eq_some_iff.mp hGet).1
        unfold get?
        rw [List.getElem?_set_self hLt]
    rcases hm with ⟨⟨a₀, hPts⟩, hExcl⟩
    rcases hm₁ with ⟨⟨a₁', hPts₁⟩, hExcl₁⟩
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a₂ hPts₁ hExcl₁]
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a₁ hPts hExcl]
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp codec a₂ hPts hExcl]
    rw [memoryLocals_updateMemoryLocals, list_set_set_self,
      updateMemoryLocals_updateMemoryLocals]

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
`IndependentLenses` on `ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂`.
-/
theorem treeMemoryPtrMutLens_independent_of_ne_alloc {α β : Type}
    (rp₁ rp₂ : RawPtrVal) (codec₁ : ValueCodec α) (codec₂ : ValueCodec β) :
    IndependentLenses
      (treeMemoryPtrMutLens rp₁ codec₁)
      (treeMemoryPtrMutLens rp₂ codec₂)
      (ValidTreeMutBorrowLensPair rp₁ rp₂ codec₁ codec₂) where
  valid_writeBack_left a m hm := by
    refine ⟨
      (treeMemoryPtrMutLens_lawful rp₁ codec₁).valid_writeBack a m hm.valid_left,
      ?_, hm.ne_alloc⟩
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁ hExcl₁]
    exact ⟨
      ⟨b₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc hExcl₂.offset_zero hPts₂⟩,
      TreeExclusiveBorrow.of_borrows_eq hExcl₂
        (updateMemoryLocals_borrows _ _)⟩
  valid_writeBack_right b m hm := by
    refine ⟨?_,
      (treeMemoryPtrMutLens_lawful rp₂ codec₂).valid_writeBack b m hm.valid_right,
      hm.ne_alloc⟩
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂ hExcl₂]
    exact ⟨
      ⟨a₀, pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
        hExcl₁.offset_zero hPts₁⟩,
      TreeExclusiveBorrow.of_borrows_eq hExcl₁
        (updateMemoryLocals_borrows _ _)⟩
  readView_right_of_writeBack_left a m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [treeMemoryPtrMutLens_readView_of_readAllocAt hPts₂]
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁ hExcl₁]
    exact treeMemoryPtrMutLens_readView_of_readAllocAt
      (pointsTo_updateMemoryLocals_set_ne hm.ne_alloc hExcl₂.offset_zero hPts₂)
  readView_left_of_writeBack_right b m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    rw [treeMemoryPtrMutLens_readView_of_readAllocAt hPts₁]
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂ hExcl₂]
    exact treeMemoryPtrMutLens_readView_of_readAllocAt
      (pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
        hExcl₁.offset_zero hPts₁)
  writeBack_comm a b m hm := by
    rcases hm.valid_left with ⟨⟨a₀, hPts₁⟩, hExcl₁⟩
    rcases hm.valid_right with ⟨⟨b₀, hPts₂⟩, hExcl₂⟩
    have hPts₂' :
        readAllocAt?
          (memoryLocals ((treeMemoryPtrMutLens rp₁ codec₁).writeBack a m)) rp₂ =
          some (codec₂.encode b₀) := by
      rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁ hExcl₁]
      exact pointsTo_updateMemoryLocals_set_ne hm.ne_alloc
        hExcl₂.offset_zero hPts₂
    have hExcl₂' :
        TreeExclusiveBorrow rp₂
          ((treeMemoryPtrMutLens rp₁ codec₁).writeBack a m) := by
      rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁ hExcl₁]
      exact TreeExclusiveBorrow.of_borrows_eq hExcl₂
        (updateMemoryLocals_borrows _ _)
    have hPts₁' :
        readAllocAt?
          (memoryLocals ((treeMemoryPtrMutLens rp₂ codec₂).writeBack b m)) rp₁ =
          some (codec₁.encode a₀) := by
      rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂ hExcl₂]
      exact pointsTo_updateMemoryLocals_set_ne hm.ne_alloc.symm
        hExcl₁.offset_zero hPts₁
    have hExcl₁' :
        TreeExclusiveBorrow rp₁
          ((treeMemoryPtrMutLens rp₂ codec₂).writeBack b m) := by
      rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂ hExcl₂]
      exact TreeExclusiveBorrow.of_borrows_eq hExcl₁
        (updateMemoryLocals_borrows _ _)
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂' hExcl₂']
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁' hExcl₁']
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₁ codec₁ a hPts₁ hExcl₁]
    rw [treeMemoryPtrMutLens_writeBack_eq_of_tree rp₂ codec₂ b hPts₂ hExcl₂]
    rw [memoryLocals_updateMemoryLocals, memoryLocals_updateMemoryLocals]
    rw [updateMemoryLocals_updateMemoryLocals,
      updateMemoryLocals_updateMemoryLocals]
    rw [list_set_comm (memoryLocals m) hm.ne_alloc]

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

/--
A family write-back through member `b` agrees with the original memory on
every frame footprint whose cells avoid `b`'s allocation: it rewrites one
caller slot and leaves the borrow table unchanged.
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
  rcases hValid.valid b hb with ⟨⟨a₀, hPts⟩, hExcl⟩
  rw [memoryPtrMutLens_writeBack_eq_of_exclusive b.rp b.codec a hPts hExcl]
  refine ⟨fun allocId offset hIn => ?_, fun tag _ => ?_⟩
  · rw [memoryLocals_updateMemoryLocals]
    unfold readAllocAt?
    unfold get?
    rw [List.getElem?_set_ne (Ne.symm (hAddrs allocId offset hIn))]
  · rw [updateMemoryLocals_borrows]

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
  refine .cons (.pureAssign (.mk (.use_pure .const_zeroSized) rfl
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
  refine .cons (.pureAssign (.mk (oldSlot := .uninit) (.use_pure .const_zeroSized)
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
      (.use_deref (.copy_deref rfl (by simp [lookupLensVal?]; rfl)))
      rfl (fun h => nomatch h) rfl)) ?_
  refine .cons (.derefWrite (.mk
      (.use_deref (.copy_deref rfl (by simp [lookupLensVal?, hNe]; rfl)))
      rfl (by simp [lookupLensVal?]; rfl))) ?_
  refine .cons (.derefWrite (.mk (.use_pure (.copy_local rfl)) rfl
      (by simp [lookupLensVal?, updateLensVal, hNe]; rfl))) ?_
  refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (env₂ := [.init .unit, .init (.ptr a_ptr.toMirPtr 8),
        .init (.ptr b_ptr.toMirPtr 8), .init (.scalar ⟨a_old, 4⟩)])
      (.use_pure .const_zeroSized) rfl (fun h => nomatch h) rfl)) ?_
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
  · exact .pure (.move_field rfl rfl)
  · show (match Nat.ble (scalarModulus 4) (Nat.add x_old d_val) with
      | true => 1
      | false => 0) = 0
    rw [hBle]
  · refine LiftLensBlock.return_
      (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8),
        .init (.scalar ⟨d_val, 4⟩), .dead]) rfl rfl rfl ?_ rfl
    refine .cons (.derefWrite (.mk (.use_pure (.move_field rfl rfl)) rfl
      (lookupLensVal?_singleton_self _ _))) ?_
    refine .cons (.storageDead (.mk rfl rfl)) ?_
    refine .cons (.pureAssign (.mk (oldSlot := .uninit)
      (.use_pure .const_zeroSized) rfl (fun h => nomatch h) rfl)) ?_
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


/-! ### Multi-Block Conditional Branching: `max_assign_u32(x: &mut u32, y: u32)` -/

/--
`Runtime(PostCleanup)` MIR of `max_assign_u32(x: &mut u32, y: u32) { if *x < y { *x = y; } }`:
three basic blocks joined by `TerminatorKind.switchInt` and `TerminatorKind.goto`.
- `bb0` (index `0`): `StorageLive(_3); _3 = Lt(copy (*_1), copy _2); switchInt(move _3) -> [0: bb2, otherwise: bb1]`
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

/-- Precondition of `max_assign_u32`: `x` owns an active `&mut u32` holding `x_old`. -/
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
      · refine .cons (.derefWrite (.mk (.use_pure (.copy_local rfl)) rfl
          (lookupLensVal?_singleton_self _ _))) ?_
        rw [updateLensVal_singleton_self]
        exact .nil
      · refine LiftLensBlock.return_
          (env' := [.init .unit, .init (.ptr x_ptr.toMirPtr 8),
            .init (.scalar ⟨y_val, 4⟩), .dead]) rfl rfl rfl ?_ rfl
        refine .cons (.storageDead (.mk rfl rfl)) ?_
        refine .cons (.pureAssign (.mk (oldSlot := .uninit)
          (.use_pure .const_zeroSized) rfl (fun h => nomatch h) rfl)) ?_
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
        (.use_pure .const_zeroSized) rfl (fun h => nomatch h) rfl)) ?_
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


end Anneal.SepLogicLenses

