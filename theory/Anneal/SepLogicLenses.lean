-- Copyright 2026 The Fuchsia Authors
--
-- Use of this source code is governed by a BSD-style license that can be
-- found in the LICENSE file or at https://opensource.org/licenses/BSD-3-Clause

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

/-!
# Separation-Logic-Backed Mutable Lenses & Pure Deref Lifting (`FF-4.1`)

This module connects Anneal's separation logic (`SepProp`, `sepConj`,
`DisjointFootprints`, `ActiveTypedMutBorrow`) and functional lens layer
(`MutLens`, `LawfulMutLens`, `memoryPtrMutLens`) to the variable-headed pure
lifting judgment layer (`MirLiftCore`) and fuel-free `ITree` weakest
preconditions (`MirWpConverges`, `StatefulVerificationResult`,
`TotalVerificationResult`) under the `I-10` Tree Borrows and 12-field `Memory`
model:

1. **Section 1 — Connecting `sepConj` (`*`) & `DisjointFootprints` to
   `IndependentLenses` (`MutLens`)**:
   Defines `IndependentLenses`, `IndependentLenses.symm`, `prodMutLens`,
   `prodMutLens_lawful`, and `PairwiseIndependentLenses`, and proves that a
   separating conjunction of active typed mutable borrows
   `sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁) (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)`
   automatically derives pointer/allocation/tag non-aliasing
   (`rp₁.allocId ≠ rp₂.allocId`, `rp₁.tag ≠ rp₂.tag`, `rp₁ ≠ rp₂`), lens
   lawfulness (`LawfulMutLens`), lens independence (`IndependentLenses`), and
   preservation of arbitrary `LocalSepProp` frame assertions `R_frame`.
2. **Section 2 — Pure Lens-State Lifting Rules (`LiftDerefRead`,
   `LiftDerefWrite`, `LiftRetag`, `mirWpConverges_of_sepLenses`)**:
   Defines the separation-logic lens-state invariant `SepLensStateInv` and
   frame preservation relation `LensFramePreserved`, together with variable-headed
   pure lifting judgments (`LiftLensOperand`, `LiftLensRvalue`, `LiftDerefRead`,
   `LiftDerefWrite`, `LiftRetag`, `LiftPureAssign`, `LiftStorageLive`,
   `LiftStorageDead`, `LiftNop`, `LiftLensStmt`, `LiftLensStmts`,
   `LiftLensBlock`) over `(PureEnv × List (RawPtrVal × Value))`. Proves that
   every lifted block converges fuel-freely (`mirWpConverges_of_sepLenses`,
   `verifyStatefulMir_of_sepLenses`, `verifyTotalMir_of_sepLenses`) without
   manual `Memory` record destructuring.
3. **Section 3 — Concrete Stateful Reference Witnesses (`add_assign` &
   `swap_u32`)**:
   Discharges fuel-free `MirWpConverges`, `StatefulVerificationResult`,
   `TotalVerificationResult`, and non-vacuity theorems for realistic
   `Runtime(PostCleanup)` MIR bodies of `add_assign(x: &mut u32, d: u32)` and
   `swap_u32(a: &mut u32, b: &mut u32)` via `mirWpConverges_of_sepLenses`.
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
  cases entry
  dsimp only at h
  subst h
  rfl

/-! ## 1. Connecting `sepConj` (`*`) & `DisjointFootprints` to `IndependentLenses` -/

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
in parallel and writing back sequentially via `L₁.writeBack` then `L₂.writeBack`.
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

theorem memoryLocals_updateMemoryLocals (m : Memory) (locals' : List LocalValue) :
    memoryLocals (updateMemoryLocals m locals') = locals' := by
  cases m
  unfold memoryLocals updateMemoryLocals
  rename_i f1 f2 f3 f4 f5 f6 callStack f8 f9 f10 f11 f12
  cases callStack <;> rfl

theorem updateMemoryLocals_borrows (m : Memory) (locals' : List LocalValue) :
    (updateMemoryLocals m locals').borrows = m.borrows := by
  cases m
  unfold updateMemoryLocals
  rename_i f1 f2 f3 f4 f5 f6 callStack f8 f9 f10 f11 f12
  cases callStack <;> rfl

theorem updateMemoryLocals_self (m : Memory) :
    updateMemoryLocals m (memoryLocals m) = m := by
  cases m
  unfold updateMemoryLocals memoryLocals
  rename_i f1 f2 f3 f4 f5 f6 callStack f8 f9 f10 f11 f12
  cases callStack <;> rfl

theorem updateMemoryLocals_updateMemoryLocals
    (m : Memory) (l₁ l₂ : List LocalValue) :
    updateMemoryLocals (updateMemoryLocals m l₁) l₂ =
      updateMemoryLocals m l₂ := by
  cases m
  unfold updateMemoryLocals
  rename_i f1 f2 f3 f4 f5 f6 callStack f8 f9 f10 f11 f12
  cases callStack <;> rfl

/--
Under `ExclusiveActiveBorrow rp m` and an initialized pointee slot
`PointsTo rp v₀ m`, `(memoryPtrMutLens rp codec).writeBack a m` leaves
`m.borrows` unchanged and directly updates `memoryLocals m` at `rp.allocId` to
`.init (codec.encode a)`.
-/

theorem memoryPtrMutLens_readView_of_readAllocAt {rp : RawPtrVal} {codec : ValueCodec α} {a : α} {m : Memory}
    (h_read : readAllocAt? (memoryLocals m) rp = some (codec.encode a)) :
    (memoryPtrMutLens rp codec).readView m = a := by
  unfold memoryPtrMutLens
  dsimp only
  rw [h_read]
  dsimp only
  rw [codec.decode_encode]
  rfl

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
`memoryPtrMutLens rp codec` is a `LawfulMutLens` on `ValidMutBorrowLens rp codec`.
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
Two `memoryPtrMutLens` instances on distinct allocations (`rp₁.allocId ≠ rp₂.allocId`)
satisfy `IndependentLenses` on `ValidMutBorrowLensPair rp₁ rp₂ codec₁ codec₂`.
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

/-! ## 2. Pure Lens-State Lifting Rules (`LiftDerefRead`, `LiftDerefWrite`, `LiftRetag`) -/

/-- Project a `RawPtrVal` to a `MirAst.ProvenancePtr` carrying `rp.tag` as its provenance ID. -/
@[reducible]
def _root_.Anneal.UnsafeObligations.RawPtrVal.toMirPtr (rp : RawPtrVal) : ProvenancePtr :=
  { allocId := rp.tag, offsetBytes := rp.offset }

/-- Encode a `RawPtrVal` as an 8-byte thin pointer `Value.ptr`. -/
@[reducible]
def _root_.Anneal.UnsafeObligations.RawPtrVal.toMirValue (rp : RawPtrVal) : Value :=
  .ptr rp.toMirPtr 8

/-- Look up the current pointee `Value` of `rp` in the pure lens environment `entries`. -/
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

/--
Separation-logic lens-state invariant connecting a pure local slot environment
of length `frameLen` and pure lens bindings `entries : List (RawPtrVal × Value)`
to the concrete 12-field `Memory` state `m`.
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
      ExclusiveActiveBorrow rp m
  pairwise_disjoint :
    List.Pairwise
      (fun k₁ k₂ => k₁.allocId ≠ k₂.allocId ∧ k₁.tag ≠ k₂.tag)
      (entries.map Prod.fst)

/-- Extract the Tree Borrows permission of a pointer. -/
def hasBorrowPerm (borrows : List BorrowEntry) (rp : RawPtrVal) : Option TreeBorrowPerm :=
  (lookupBorrow borrows rp.tag).map BorrowEntry.perm

/--
Relational invariant between initial memory `m₀` (with initial lens bindings
`entries₀`) and current memory `m`, ensuring that all caller allocations
outside `entries₀` and all Tree Borrows permission states `hasBorrowPerm` are
preserved across `.retag` and `.deref` writes.
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

/-! ### Borrow-Table Preservation Lemmas for `Retag`, `DerefRead`, `DerefWrite`, and Local Writes -/

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
      ⟨hOff, hAbove, hCaller, ⟨_, hLook, hExcl⟩⟩
    rcases hLook with ⟨entry, hLookEq, hT, hP, hPerm, hRO, hRL⟩
    rcases lookupBorrow_attachBorrowProtector_some
        (tag := tag) (pid := protId) hLookEq with
      ⟨entry', hLook', hT', hP', hPerm', hRO', hRL'⟩
    refine ⟨hOff, hAbove, hCaller, ⟨hOff,
      ⟨entry', hLook', hT'.trans hT, hP'.trans hP, hPerm'.trans hPerm,
        hRO'.trans hRO, hRL'.trans hRL⟩, ?_⟩⟩
    intro b hb hTargetB
    rcases mem_attachBorrowProtector hb with
      ⟨b₀, hb₀, hTagB, hTargetB₀, hProjB, hPermB, hROB, hRLB⟩
    rcases hExcl b₀ hb₀ (hTargetB₀.symm.trans hTargetB) with
      ⟨hTag₀, hPerm₀, hProj₀, hRO₀, hRL₀⟩ | hDis₀
    · exact Or.inl ⟨hTagB.trans hTag₀, hPermB.trans hPerm₀,
        hProjB.trans hProj₀, hROB.trans hRO₀, hRLB.trans hRL₀⟩
    · exact Or.inr (hPermB.trans hDis₀)
  pairwise_disjoint := hInv.pairwise_disjoint

theorem freezeTreeBorrowsOnReadAtProj_eq_self_of_exclusive
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat}
    (readProj : List ProjectionElem)
    (readRangeOff readRangeLen : Nat)
    (hExcl :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (b.tag = tag ∧
            b.perm = .active ∧
            b.targetProjection = [] ∧
            b.rangeOffset = 0 ∧
            b.rangeLen = 0) ∨
          b.perm = .disabled) :
    freezeTreeBorrowsOnReadAtProj
      allBorrows borrows allocId (.some tag)
      readProj readRangeOff readRangeLen = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail :=
      ih (fun b hb => hExcl b (List.Mem.tail hd hb))
    unfold freezeTreeBorrowsOnReadAtProj
    rw [hTail]
    unfold updateBorrowPermOnReadAtProj
    cases hTarget : Nat.beq hd.targetLocal allocId with
    | false => rfl
    | true =>
      have hTargetEq : hd.targetLocal = allocId :=
        Nat.eq_of_beq_eq_true hTarget
      rcases hExcl hd (List.Mem.head tl) hTargetEq with
        ⟨hTag, _, _, _, _⟩ | hDis
      · subst hTag
        cases borrowEntryOverlapsWrite hd readProj readRangeOff readRangeLen with
        | false => rfl
        | true =>
          simp_all [isBorrowDescendantOrSelf_self]
      · cases borrowEntryOverlapsWrite hd readProj readRangeOff readRangeLen with
        | false => rfl
        | true =>
          cases hDesc : isBorrowDescendantOrSelf allBorrows tag hd.tag <;>
            simp_all

theorem hasProtectedTreeWriteConflict_eq_false_of_exclusive
    (allBorrows borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    {allocId tag : Nat}
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hExcl :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (b.tag = tag ∧
            b.perm = .active ∧
            b.targetProjection = [] ∧
            b.rangeOffset = 0 ∧
            b.rangeLen = 0) ∨
          b.perm = .disabled) :
    hasProtectedTreeWriteConflict
      allBorrows borrows activeProtectors allocId (.some tag)
      writeProj writeRangeOff writeRangeLen = false := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hExcl b (List.Mem.tail hd hb))
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
        rcases hExcl hd (List.Mem.head tl) hTargetEq with
          ⟨hTag, hPerm, _, _, _⟩ | hDis
        · subst hTag
          rw [resolveTreeBorrowWriterTag_self]
          unfold borrowEntryWriteConflicts
          simp
        · unfold borrowEntryWriteConflicts
          cases resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
          | none => simp [hDis]
          | some wTag =>
            cases hEq : Nat.beq hd.tag wTag <;> simp [hEq, hDis]
      simp [hNoConflict, hTail]

theorem updateBorrowPermAtProj_eq_self_of_exclusive
    (entry : BorrowEntry)
    {allocId tag : Nat}
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hExcl :
      entry.targetLocal = allocId →
        (entry.tag = tag ∧
          entry.perm = .active ∧
          entry.targetProjection = [] ∧
          entry.rangeOffset = 0 ∧
          entry.rangeLen = 0) ∨
        entry.perm = .disabled) :
    updateBorrowPermAtProj
      entry allocId (.some tag) writeProj writeRangeOff writeRangeLen = entry := by
  unfold updateBorrowPermAtProj
  cases hTarget : Nat.beq entry.targetLocal allocId with
  | false => rfl
  | true =>
    dsimp only
    have hTargetEq : entry.targetLocal = allocId :=
      Nat.eq_of_beq_eq_true hTarget
    rcases hExcl hTargetEq with ⟨hTag, hPerm, _, _, _⟩ | hDis
    · subst hTag
      simp [hPerm]
    · cases hEq : Nat.beq entry.tag tag with
      | true => simp [hDis]
      | false =>
        dsimp only
        cases hOverlap : borrowEntryOverlapsWrite entry writeProj writeRangeOff writeRangeLen with
        | false => rfl
        | true => exact borrowEntry_disabled_eta hDis

theorem invalidateTreeBorrowsAtProj_eq_self_of_exclusive
    (allBorrows borrows : List BorrowEntry)
    {allocId tag : Nat}
    (writeProj : List ProjectionElem)
    (writeRangeOff writeRangeLen : Nat)
    (hExcl :
      ∀ b ∈ borrows,
        b.targetLocal = allocId →
          (b.tag = tag ∧
            b.perm = .active ∧
            b.targetProjection = [] ∧
            b.rangeOffset = 0 ∧
            b.rangeLen = 0) ∨
          b.perm = .disabled) :
    invalidateTreeBorrowsAtProj
      allBorrows borrows allocId (.some tag)
      writeProj writeRangeOff writeRangeLen = borrows := by
  induction borrows with
  | nil => rfl
  | cons hd tl ih =>
    have hTail := ih (fun b hb => hExcl b (List.Mem.tail hd hb))
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
      rcases hExcl hd (List.Mem.head tl) hTargetEq with
        ⟨hTag, hPerm, _, _, _⟩ | hDis
      · subst hTag
        rw [resolveTreeBorrowWriterTag_self]
        dsimp only
        have hEq : Nat.beq hd.tag hd.tag = true := by simp
        rw [hEq]
        simp [hPerm]
      · cases hWriter : resolveTreeBorrowWriterTag allBorrows hd (.some tag) with
        | none =>
          dsimp only
          cases hOverlap : borrowEntryOverlapsWrite hd writeProj writeRangeOff writeRangeLen <;>
            simp [hDis]
        | some wTag =>
          dsimp only
          cases hEq : Nat.beq hd.tag wTag with
          | true => simp [hDis]
          | false =>
            dsimp only
            cases hOverlap : borrowEntryOverlapsWrite hd writeProj writeRangeOff writeRangeLen with
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
Variable-headed pure operand evaluation on a local slot environment `env : PureEnv`.
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
Variable-headed pure rvalue evaluation (`LiftLensRvalue`) combining pure local
operands and separation-logic lens dereference reads.
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
  | binaryOp_add_u32
      {env env₁ env₂ : PureEnv} {entries : List (RawPtrVal × Value)}
      {lhsOp rhsOp : Operand} {a b : Nat} :
      LiftLensOperand env lhsOp (.scalar ⟨a, 4⟩) env₁ →
      LiftLensOperand env₁ rhsOp (.scalar ⟨b, 4⟩) env₂ →
      LiftLensRvalue localDecls layouts env entries
        (.binaryOp .add lhsOp rhsOp)
        (.scalar ⟨wrapScalarBits (Nat.add a b) (scalarModulus 4), 4⟩)
        env₂
  | tuple_nil
      {env : PureEnv} {entries : List (RawPtrVal × Value)} :
      LiftLensRvalue localDecls layouts env entries
        (.aggregate .tuple []) (.aggregate 0 []) env

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
Variable-headed pure dereference write rule (`LiftDerefWrite`) updating `*ptrLoc`
in the pure lens environment `entries` via `updateLensVal`.
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
Statement-list pure lens-lifting judgment (`LiftLensStmts`) threading `(env, entries)`
across a basic block's statement sequence.
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
Whole-block pure lens-lifting judgment (`LiftLensBlock`) for a basic block
terminating with `TerminatorKind.return_`, extracting return value `retVal`
from local `_0` and final pure lens bindings `entries'`.
-/
inductive LiftLensBlock (body : CapturedMir) (bbIdx : BasicBlockIdx) :
    PureEnv → List (RawPtrVal × Value) →
    Value → List (RawPtrVal × Value) → Prop where
  | return_
      {bb : BasicBlockData} {env env' : PureEnv}
      {entries entries' : List (RawPtrVal × Value)} {retVal : Value} :
      body.phase = .runtimePostCleanup →
      get? body.basicBlocks bbIdx = .some bb →
      bb.terminator.kind = .return_ →
      LiftLensStmts body.localDecls body.layouts
        env entries bb.statements env' entries' →
      get? env' 0 = .some (.init retVal) →
      LiftLensBlock body bbIdx env entries retVal entries'

/-! ### Soundness of Operand, Rvalue, and Statement Lifting under `SepLensStateInv` -/

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
        exact freezeTreeBorrowsOnReadAtProj_eq_self_of_exclusive
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
        exact freezeTreeBorrowsOnReadAtProj_eq_self_of_exclusive
          m.borrows m.borrows _ _ _ hExcl

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
    try { exact hOp.not_deref m.borrows m }
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
  | binaryOp_add_u32 hLhs hRhs =>
    rcases hLhs.evalOperand_eq m.borrows m.globals layouts m.callerLocals with
      ⟨hEval₁, hLen₁⟩
    rcases hRhs.evalOperand_eq m.borrows m.globals layouts m.callerLocals with
      ⟨hEval₂, hLen₂⟩
    refine ⟨?_, hLen₂.trans hLen₁⟩
    unfold evalRvalue
    simp [hEval₁, hEval₂]
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
        ExclusiveActiveBorrow.of_borrows_eq hExclRp rfl⟩
      unfold get?
      exact List.getElem?_set_self hLtRp
    · rcases hInv.entries_valid k v hMemOld with
        ⟨hOffK, hAboveK, hCallerK, hExclK⟩
      have hDisj :=
        pairwise_disjoint_of_mem_ne hInv.pairwise_disjoint hMemRp hMemOld hNe
      refine ⟨hOffK, hAboveK, ?_,
        ExclusiveActiveBorrow.of_borrows_eq hExclK rfl⟩
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
                exact hasProtectedTreeWriteConflict_eq_false_of_exclusive
                  s.memory.borrows s.memory.borrows (pHead :: pTail) _ _ _
                  hExcl.exclusive_on_alloc
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
            have hExclSingle := hExcl.exclusive_on_alloc
            rw [hB] at hExclSingle
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
            exact invalidateTreeBorrowsAtProj_eq_self_of_exclusive
              s.memory.borrows s.memory.borrows _ _ _ hExcl.exclusive_on_alloc
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

theorem mirWpConverges_of_liftLensStmts
    {body : CapturedMir} {bbIdx : BasicBlockIdx} {bb : BasicBlockData}
    {stmts : List Statement}
    {env env' : PureEnv}
    {entries₀ entries entries' : List (RawPtrVal × Value)}
    {retVal : Value}
    (hPhase : body.phase = .runtimePostCleanup)
    (hBb : get? body.basicBlocks bbIdx = .some bb)
    (hTerm : bb.terminator.kind = .return_)
    (hStmts :
      LiftLensStmts body.localDecls body.layouts
        env entries stmts env' entries')
    (hRet : get? env' 0 = .some (.init retVal)) :
    ∀ (prefixStmts : List Statement) (m₀ m : Memory)
      (Φ : MirOutcome → Prop),
      bb.statements = prefixStmts ++ stmts →
      SepLensStateInv env.length entries m →
      LensFramePreserved entries₀ m₀ m →
      entries.map Prod.fst = entries₀.map Prod.fst →
      (∀ m_final : Memory,
        SepLensStateInv env'.length entries' m_final →
        LensFramePreserved entries₀ m₀ m_final →
        entries'.map Prod.fst = entries₀.map Prod.fst →
        Φ (.normal (retVal, m_final))) →
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
    intro prefixStmts m₀ m Φ hBbStmts hInv hFrame hKeys hPost
    apply MirWpConverges.ret_of_step
    · unfold stepMirFn
      rw [hInv.activeCallee_none]
      dsimp only [Option.getD]
      simp only [hPhase, hBb]
      have hStmtLen : bb.statements.length = prefixStmts.length := by
        rw [hBbStmts, List.append_nil]
      have hGetNone : get? bb.statements prefixStmts.length = .none :=
        get?_eq_none_of_le (Nat.le_of_eq hStmtLen)
      simp only [hGetNone]
      unfold length
      simp only [← hStmtLen, beq_self_eq_true, ↓reduceIte]
      unfold evalTerminator
      rw [hTerm, hRet, hInv.callStack_nil]
      rfl
    · exact hPost m hInv hFrame hKeys
  | cons hFirst hRest ih =>
    rename_i env_ env1_ env2_ entries_ entries1_ entries2_ stmt rest
    intro prefixStmts m₀ m Φ hBbStmts hInv hFrame hKeys hPost
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
      exact ih hRet (prefixStmts ++ [stmt]) m₀ m₁ Φ
        hAppend hInv₁ hFrame₁ hKeys₁ hPost

/--
Fuel-Free Separation-Logic Lens Lifting Theorem (`mirWpConverges_of_sepLenses`):
Given a `LiftLensBlock body bbIdx env entries₀ retVal entries'` derivation and
an initial memory `m₀` satisfying `SepLensStateInv env.length entries₀ m₀`,
`MirWpConverges` holds fuel-freely from `{ blockIdx := bbIdx, stmtIdx := 0, locals := env }`
to a final memory `m_final` satisfying `SepLensStateInv env.length entries' m_final`
and `LensFramePreserved entries₀ m₀ m_final`.
-/
theorem LiftLensOperand.length_eq
    {env env' : PureEnv} {op : Operand} {v : Value}
    (h : LiftLensOperand env op v env') :
    env'.length = env.length := by
  cases h with
  | copy_local _ => rfl
  | move_local _ hSet => exact set?_length_eq hSet
  | const_scalar => rfl
  | const_zeroSized => rfl

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
  | binaryOp_add_u32 hLhs hRhs => exact hRhs.length_eq.trans hLhs.length_eq
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
Fuel-Free Separation-Logic Lens Lifting Theorem (`mirWpConverges_of_sepLenses`):
Given a `LiftLensBlock body bbIdx env entries₀ retVal entries'` derivation and
an initial memory `m₀` satisfying `SepLensStateInv env.length entries₀ m₀`,
`MirWpConverges` holds fuel-freely from `{ blockIdx := bbIdx, stmtIdx := 0, locals := env }`
to a final memory `m_final` satisfying `SepLensStateInv env.length entries' m_final`
and `LensFramePreserved entries₀ m₀ m_final`.
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
      Φ := by
  cases hBlock with
  | @return_ bb _ env' _ _ _ hPhase hBb hTerm hStmts hRet =>
    have hLenEq : env'.length = env.length := hStmts.length_eq
    exact mirWpConverges_of_liftLensStmts hPhase hBb hTerm hStmts hRet
      [] m₀ m₀ Φ (List.nil_append _).symm hInv₀
      (LensFramePreserved.refl entries₀ m₀) rfl
      (fun m_final hInvF hFrameF _ => hPost m_final (hLenEq ▸ hInvF) hFrameF)

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
  exclusive : ExclusiveActiveBorrow rp m

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
    SepLensStateInv frameLen [(rp₁, codec₁.encode a₁)] m₀ where
  callStack_nil := hWf₁.callStack_nil
  activeCallee_none := hWf₁.activeCallee_none
  borrows_above_frame := hWf₁.borrows_above_frame
  entries_valid rp' v' hMem := by
    simp only [List.mem_singleton, Prod.mk.injEq] at hMem
    rcases hMem with ⟨rfl, rfl⟩
    have hPts₁ : readAllocAt? (memoryLocals m₀) rp' = some (codec₁.encode a₁) :=
      readAllocAt_of_activeTypedMutBorrow_holdsIn (holdsIn_of_sepConj_left hSep)
    exact ⟨hWf₁.exclusive.offset_zero, hWf₁.alloc_above_frame,
      callerLocals_get?_of_pointsTo
        hWf₁.callStack_nil hWf₁.exclusive.offset_zero hPts₁,
      hWf₁.exclusive⟩
  pairwise_disjoint := by simp

theorem sepConj_activeTypedMutBorrow_preserved_one {α : Type}
    {frameLen : Nat} {rp₁ : RawPtrVal} {codec₁ : ValueCodec α} {a_old a_new : α}
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep : SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_old) R_frame) m₀)
    (hInv_final : SepLensStateInv frameLen [(rp₁, codec₁.encode a_new)] m_final)
    (hWf : WfSingleMutBorrow frameLen rp₁ m₀)
    (hPres : LensFramePreserved [(rp₁, codec₁.encode a_old)] m₀ m_final)
    (h_R : LocalSepProp R_frame)
    (h_not_agg : ∀ a : α, ∀ elems, codec₁.encode a ≠ .aggregate 0 elems) :
    SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_new) R_frame) m_final := by
  rcases hSep with ⟨fp, h₁, h₂, hsplit, hActive, hR⟩
  exists fp, { state := m_final, footprint := h₁.footprint }, { state := m_final, footprint := h₂.footprint }
  refine ⟨⟨rfl, rfl, hsplit.2.2.1, hsplit.2.2.2.1, hsplit.2.2.2.2⟩, ?_, ?_⟩
  · rcases hActive with ⟨h₁a, h₁b, hsplit_ab, hpts, htok⟩
    have hOff : rp₁.offset = 0 := hWf.exclusive.offset_zero
    have hPtsFinal : readAllocAt? (memoryLocals m_final) rp₁ = some (codec₁.encode a_new) := by
      have hMem : (rp₁, codec₁.encode a_new) ∈ [(rp₁, codec₁.encode a_new)] := List.mem_singleton.mpr rfl
      rcases hInv_final.entries_valid rp₁ (codec₁.encode a_new) hMem with ⟨_, _, hCaller, _⟩
      unfold readAllocAt? memoryLocals
      rw [hInv_final.callStack_nil, hOff, hCaller]
    have hTokFinal : ∃ entry, lookupBorrow m_final.borrows rp₁.tag = some entry ∧ entry.targetLocal = rp₁.allocId ∧ entry.perm = .active := by
      have hMem : (rp₁, codec₁.encode a_new) ∈ [(rp₁, codec₁.encode a_new)] := List.mem_singleton.mpr rfl
      rcases hInv_final.entries_valid rp₁ (codec₁.encode a_new) hMem with ⟨_, _, _, hExcl⟩
      rcases hExcl.lookup_active with ⟨entry, hLook, hT, hP, hPerm, _⟩
      exact ⟨entry, hLook, hT, hPerm⟩
    unfold ActiveTypedMutBorrow sepConj
    exists { state := m_final, footprint := h₁a.footprint }
    exists { state := m_final, footprint := h₁b.footprint }
    refine ⟨⟨rfl, rfl, hsplit_ab.2.2.1, hsplit_ab.2.2.2.1, hsplit_ab.2.2.2.2⟩, ⟨hPtsFinal, hpts.2⟩, ⟨hTokFinal, htok.2⟩⟩
  · have h₂_eq : h₂ = { state := m₀, footprint := h₂.footprint } := by cases h₂; dsimp; congr; exact hsplit.2.1
    have hR' : R_frame.atFootprint h₂.footprint m₀ := by
      unfold SepProp.atFootprint
      have h_eq : ({ state := m₀, footprint := h₂.footprint } : PartialHeap) = h₂ := by cases h₂; dsimp; congr; exact Eq.symm hsplit.2.1
      exact h_eq ▸ hR
    apply h_R h₂.footprint m₀ m_final ?_ hR'
    refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
    · rcases hActive with ⟨h₁a, h₁b, hsplit_ab, hpts, htok⟩
      have h₁a_fp : h₁a.footprint = { addrs := [(rp₁.allocId, rp₁.offset)], tags := [] } := hpts.2
      have hIn₁ : (rp₁.allocId, rp₁.offset) ∈ h₁.footprint.addrs := by
        apply (hsplit_ab.2.2.2.1 _).mpr
        rw [h₁a_fp]
        exact Or.inl (List.mem_singleton.mpr rfl)
      cases hEqAlloc : Nat.beq allocId rp₁.allocId
      · have hAllocNe : allocId ≠ rp₁.allocId := Nat.ne_of_beq_eq_false hEqAlloc
        have hOut : ∀ e ∈ [(rp₁, codec₁.encode a_old)], allocId ≠ e.1.allocId := by
          intro e hE
          cases List.mem_singleton.mp hE
          exact hAllocNe
        have hGetEq := hPres.locals_unchanged_outside allocId hOut
        unfold readAllocAt? memoryLocals
        rw [hInv_final.callStack_nil, hWf.callStack_nil, hGetEq]
      · have hAllocEq : allocId = rp₁.allocId := Nat.eq_of_beq_eq_true hEqAlloc
        subst hAllocEq
        have hOffNe : rp₁.offset ≠ offset := by
          intro hEq
          subst hEq
          exact hsplit.2.2.1.1 (rp₁.allocId, rp₁.offset) hIn₁ hIn
        have hOffZero : rp₁.offset = 0 := hWf.exclusive.offset_zero
        have hOffsetPos : offset ≠ 0 := fun hZ => hOffNe (hZ ▸ hOffZero)
        have hNone₀ : readAllocAt? (memoryLocals m₀) { allocId := rp₁.allocId, offset := offset, tag := rp₁.allocId } = none := by
          have hPts₀ : readAllocAt? (memoryLocals m₀) rp₁ = some (codec₁.encode a_old) := by
            have h_eq : h₁a.state = m₀ := Eq.trans hsplit_ab.1 hsplit.1
            exact h_eq ▸ hpts.1
          unfold readAllocAt? memoryLocals at hPts₀ ⊢
          rw [hWf.callStack_nil]
          rw [hWf.callStack_nil, hOffZero] at hPts₀
          dsimp only at hPts₀ ⊢
          cases hGet : get? m₀.callerLocals rp₁.allocId with
          | none => rfl
          | some slot =>
            cases slot with
            | dead => rfl
            | uninit => rfl
            | init val =>
              rw [hGet] at hPts₀
              dsimp only at hPts₀
              injection hPts₀ with hV
              subst hV
              cases offset with
              | zero => contradiction
              | succ k =>
                cases hVal : codec₁.encode a_old with
                | aggregate m elems =>
                  cases m with
                  | zero =>
                    exfalso
                    exact h_not_agg a_old elems hVal
                  | succ m => rfl
                | _ => rfl
        have hNone_final : readAllocAt? (memoryLocals m_final) { allocId := rp₁.allocId, offset := offset, tag := rp₁.allocId } = none := by
          have hMem : (rp₁, codec₁.encode a_new) ∈ [(rp₁, codec₁.encode a_new)] := List.mem_singleton.mpr rfl
          rcases hInv_final.entries_valid rp₁ (codec₁.encode a_new) hMem with ⟨_, _, hCaller, _⟩
          unfold readAllocAt? memoryLocals
          rw [hInv_final.callStack_nil, hCaller]
          cases offset with
          | zero => contradiction
          | succ k =>
            cases hVal : codec₁.encode a_new with
            | aggregate m elems =>
              cases m with
              | zero =>
                exfalso
                exact h_not_agg a_new elems hVal
              | succ m => rfl
            | _ => rfl
        rw [hNone₀, hNone_final]
    · rcases hActive with ⟨h₁a, h₁b, hsplit_ab, hpts, htok⟩
      have h₁b_fp : h₁b.footprint = { addrs := [], tags := [rp₁.tag] } := htok.2
      have hIn₁ : rp₁.tag ∈ h₁.footprint.tags := by
        apply (hsplit_ab.2.2.2.2 _).mpr
        rw [h₁b_fp]
        exact Or.inr (List.mem_singleton.mpr rfl)
      have hNe : tag ≠ rp₁.tag := by
        intro hEq
        subst hEq
        exact hsplit.2.2.1.2 rp₁.tag hIn₁ hIn
      have hEq := hPres.borrows_unchanged_outside tag (by
        intro e hE
        cases List.mem_singleton.mp hE
        exact hNe)
      exact Eq.symm hEq

theorem sepLensStateInv_of_sepConj_two {α : Type}
    {frameLen : Nat} {rp₁ rp₂ : RawPtrVal} {codec₁ codec₂ : ValueCodec α} {a₁ a₂ : α}
    {R_frame : SepProp} {m₀ : Memory}
    (hSep : SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁) (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)) m₀)
    (hWf₁ : WfSingleMutBorrow frameLen rp₁ m₀)
    (hWf₂ : WfSingleMutBorrow frameLen rp₂ m₀) :
    SepLensStateInv frameLen [(rp₁, codec₁.encode a₁), (rp₂, codec₂.encode a₂)] m₀ where
  callStack_nil := hWf₁.callStack_nil
  activeCallee_none := hWf₁.activeCallee_none
  borrows_above_frame := hWf₁.borrows_above_frame
  entries_valid := by
    intro rp' v' hMem
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hMem
    rcases hMem with hEq1 | hEq2
    · have hPts1 : readAllocAt? (memoryLocals m₀) rp' = some v' := by
        rw [hEq1.1, hEq1.2]
        exact readAllocAt_of_activeTypedMutBorrow_holdsIn (holdsIn_of_sepConj_left hSep)
      have hOff : rp'.offset = 0 := by rw [hEq1.1]; exact hWf₁.exclusive.offset_zero
      exact ⟨hOff, by rw [hEq1.1]; exact hWf₁.alloc_above_frame,
        callerLocals_get?_of_pointsTo hWf₁.callStack_nil hOff hPts1,
        by rw [hEq1.1]; exact hWf₁.exclusive⟩
    · have hPts2 : readAllocAt? (memoryLocals m₀) rp' = some v' := by
        rw [hEq2.1, hEq2.2]
        exact readAllocAt_of_activeTypedMutBorrow_holdsIn (holdsIn_of_sepConj_left (holdsIn_of_sepConj_right hSep))
      have hOff : rp'.offset = 0 := by rw [hEq2.1]; exact hWf₂.exclusive.offset_zero
      exact ⟨hOff, by rw [hEq2.1]; exact hWf₂.alloc_above_frame,
        callerLocals_get?_of_pointsTo hWf₂.callStack_nil hOff hPts2,
        by rw [hEq2.1]; exact hWf₂.exclusive⟩
  pairwise_disjoint := by
    apply List.Pairwise.cons
    · intro k hIn
      cases hIn with
      | head _ =>
        rcases hSep with ⟨fp, h₁, h₂_3, hsplit_a, hActive_a, hSep_b⟩
        rcases hSep_b with ⟨h₂, h₃, hsplit_b, hActive_b, hR_b⟩
        rcases hActive_a with ⟨w1a, w2a, hsplit_wa, hpts_a, htok_a⟩
        rcases hActive_b with ⟨w1b, w2b, hsplit_wb, hpts_b, htok_b⟩
        have hIn_tag1 : rp₁.tag ∈ h₁.footprint.tags := by
          apply (hsplit_wa.2.2.2.2 _).mpr
          rw [htok_a.2]
          exact Or.inr (List.mem_singleton.mpr rfl)
        have hIn_tag2 : rp₂.tag ∈ h₂.footprint.tags := by
          apply (hsplit_wb.2.2.2.2 _).mpr
          rw [htok_b.2]
          exact Or.inr (List.mem_singleton.mpr rfl)
        have hDisjTags : rp₁.tag ≠ rp₂.tag := by
          intro hEq
          have hIn_tag2_subst : rp₁.tag ∈ h₂.footprint.tags := hEq ▸ hIn_tag2
          exact hsplit_a.2.2.1.2 _ hIn_tag1 (by apply (hsplit_b.2.2.2.2 _).mpr; exact Or.inl hIn_tag2_subst)
        have hIn_addr1 : (rp₁.allocId, rp₁.offset) ∈ h₁.footprint.addrs := by
          apply (hsplit_wa.2.2.2.1 _).mpr
          rw [hpts_a.2]
          exact Or.inl (List.mem_singleton.mpr rfl)
        have hIn_addr2 : (rp₂.allocId, rp₂.offset) ∈ h₂.footprint.addrs := by
          apply (hsplit_wb.2.2.2.1 _).mpr
          rw [hpts_b.2]
          exact Or.inl (List.mem_singleton.mpr rfl)
        have hDisjAlloc : rp₁.allocId ≠ rp₂.allocId := by
          intro hEq
          have hIn_addr2_subst : (rp₁.allocId, rp₁.offset) ∈ h₂.footprint.addrs := by
            have hEqOff : rp₂.offset = rp₁.offset := by rw [hWf₂.exclusive.offset_zero, hWf₁.exclusive.offset_zero]
            rw [←hEq, hEqOff] at hIn_addr2
            exact hIn_addr2
          exact hsplit_a.2.2.1.1 _ hIn_addr1 (by apply (hsplit_b.2.2.2.1 _).mpr; exact Or.inl hIn_addr2_subst)
        exact ⟨hDisjAlloc, hDisjTags⟩
      | tail _ hTail => nomatch hTail
    · apply List.Pairwise.cons
      · intro k hIn
        nomatch hIn
      · exact List.Pairwise.nil

theorem sepConj_activeTypedMutBorrow_preserved_two {α : Type}
    {frameLen : Nat} (rp₁ rp₂ : RawPtrVal) (codec₁ codec₂ : ValueCodec α) (a_old a_new b_old b_new : α)
    {R_frame : SepProp} {m₀ m_final : Memory}
    (hSep : SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_old) (sepConj (ActiveTypedMutBorrow rp₂ codec₂ b_old) R_frame)) m₀)
    (hInv_final : SepLensStateInv frameLen [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] m_final)
    (hWf₁ : WfSingleMutBorrow frameLen rp₁ m₀)
    (hWf₂ : WfSingleMutBorrow frameLen rp₂ m₀)
    (hPres : LensFramePreserved [(rp₁, codec₁.encode a_old), (rp₂, codec₂.encode b_old)] m₀ m_final)
    (h_R : LocalSepProp R_frame)
    (h_not_agg : ∀ a : α, ∀ elems, codec₁.encode a ≠ .aggregate 0 elems)
    (h_not_agg2 : ∀ a : α, ∀ elems, codec₂.encode a ≠ .aggregate 0 elems) :
    SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a_new) (sepConj (ActiveTypedMutBorrow rp₂ codec₂ b_new) R_frame)) m_final := by
  rcases hSep with ⟨fp, h₁, h₂_3, hsplit, hActive₁, hSep₂_3⟩
  rcases hSep₂_3 with ⟨h₂, h₃, hsplit₂, hActive₂, hR⟩
  exists fp, { state := m_final, footprint := h₁.footprint }, { state := m_final, footprint := h₂_3.footprint }
  refine ⟨⟨rfl, rfl, hsplit.2.2.1, hsplit.2.2.2.1, hsplit.2.2.2.2⟩, ?_, ?_⟩
  · rcases hActive₁ with ⟨h₁a, h₁b, hsplit_ab, hpts, htok⟩
    have hOff : rp₁.offset = 0 := hWf₁.exclusive.offset_zero
    have hPtsFinal : readAllocAt? (memoryLocals m_final) rp₁ = some (codec₁.encode a_new) := by
      have hMem : (rp₁, codec₁.encode a_new) ∈ [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] := by simp only [List.mem_cons]; exact Or.inl trivial
      rcases hInv_final.entries_valid rp₁ (codec₁.encode a_new) hMem with ⟨_, _, hCaller, _⟩
      unfold readAllocAt? memoryLocals
      rw [hInv_final.callStack_nil, hOff, hCaller]
    have hTokFinal : ∃ entry, lookupBorrow m_final.borrows rp₁.tag = some entry ∧ entry.targetLocal = rp₁.allocId ∧ entry.perm = .active := by
      have hMem : (rp₁, codec₁.encode a_new) ∈ [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] := by simp only [List.mem_cons]; exact Or.inl trivial
      rcases hInv_final.entries_valid rp₁ (codec₁.encode a_new) hMem with ⟨_, _, _, hExcl⟩
      rcases hExcl.lookup_active with ⟨entry, hLook, hT, hP, hPerm, _⟩
      exact ⟨entry, hLook, hT, hPerm⟩
    let h₁a_final : PartialHeap := { state := m_final, footprint := h₁a.footprint }
    let h₁b_final : PartialHeap := { state := m_final, footprint := h₁b.footprint }
    have hsplit_ab_final : PartialHeapSplit { state := m_final, footprint := h₁.footprint } h₁a_final h₁b_final :=
      ⟨rfl, rfl, hsplit_ab.2.2.1, hsplit_ab.2.2.2.1, hsplit_ab.2.2.2.2⟩
    unfold ActiveTypedMutBorrow sepConj
    exact ⟨h₁a_final, h₁b_final, hsplit_ab_final, ⟨hPtsFinal, hpts.2⟩, ⟨hTokFinal, htok.2⟩⟩
  · exists { state := m_final, footprint := h₂.footprint }, { state := m_final, footprint := h₃.footprint }
    refine ⟨⟨rfl, rfl, hsplit₂.2.2.1, hsplit₂.2.2.2.1, hsplit₂.2.2.2.2⟩, ?_, ?_⟩
    · rcases hActive₂ with ⟨h₂a, h₂b, hsplit₂_ab, hpts₂, htok₂⟩
      have hOff : rp₂.offset = 0 := hWf₂.exclusive.offset_zero
      have hPtsFinal : readAllocAt? (memoryLocals m_final) rp₂ = some (codec₂.encode b_new) := by
        have hMem : (rp₂, codec₂.encode b_new) ∈ [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] := by simp only [List.mem_cons]; exact Or.inr (Or.inl trivial)
        rcases hInv_final.entries_valid rp₂ (codec₂.encode b_new) hMem with ⟨_, _, hCaller, _⟩
        unfold readAllocAt? memoryLocals
        rw [hInv_final.callStack_nil, hOff, hCaller]
      have hTokFinal : ∃ entry, lookupBorrow m_final.borrows rp₂.tag = some entry ∧ entry.targetLocal = rp₂.allocId ∧ entry.perm = .active := by
        have hMem : (rp₂, codec₂.encode b_new) ∈ [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] := by simp only [List.mem_cons]; exact Or.inr (Or.inl trivial)
        rcases hInv_final.entries_valid rp₂ (codec₂.encode b_new) hMem with ⟨_, _, _, hExcl⟩
        rcases hExcl.lookup_active with ⟨entry, hLook, hT, hP, hPerm, _⟩
        exact ⟨entry, hLook, hT, hPerm⟩
      let h₂a_final : PartialHeap := { state := m_final, footprint := h₂a.footprint }
      let h₂b_final : PartialHeap := { state := m_final, footprint := h₂b.footprint }
      have hsplit₂_ab_final : PartialHeapSplit { state := m_final, footprint := h₂.footprint } h₂a_final h₂b_final :=
        ⟨rfl, rfl, hsplit₂_ab.2.2.1, hsplit₂_ab.2.2.2.1, hsplit₂_ab.2.2.2.2⟩
      unfold ActiveTypedMutBorrow sepConj
      exact ⟨h₂a_final, h₂b_final, hsplit₂_ab_final, ⟨hPtsFinal, hpts₂.2⟩, ⟨hTokFinal, htok₂.2⟩⟩
    · have h₃_eq : h₃ = { state := m₀, footprint := h₃.footprint } := by cases h₃; dsimp; congr; exact Eq.trans hsplit₂.2.1 hsplit.2.1
      have hR' : R_frame.atFootprint h₃.footprint m₀ := by
        unfold SepProp.atFootprint
        have h_eq : ({ state := m₀, footprint := h₃.footprint } : PartialHeap) = h₃ := by cases h₃; dsimp; congr; exact Eq.symm (Eq.trans hsplit₂.2.1 hsplit.2.1)
        exact h_eq ▸ hR
      apply h_R h₃.footprint m₀ m_final ?_ hR'
      refine ⟨fun allocId offset hIn => ?_, fun tag hIn => ?_⟩
      · rcases hActive₁ with ⟨h₁a, h₁b, hsplit_ab, hpts, htok⟩
        rcases hActive₂ with ⟨h₂a, h₂b, hsplit₂_ab, hpts₂, htok₂⟩
        have h₁a_fp : h₁a.footprint = { addrs := [(rp₁.allocId, rp₁.offset)], tags := [] } := hpts.2
        have hIn₁ : (rp₁.allocId, rp₁.offset) ∈ h₁.footprint.addrs := by
          apply (hsplit_ab.2.2.2.1 _).mpr
          rw [h₁a_fp]
          exact Or.inl (List.mem_singleton.mpr rfl)
        have h₂a_fp : h₂a.footprint = { addrs := [(rp₂.allocId, rp₂.offset)], tags := [] } := hpts₂.2
        have hIn₂ : (rp₂.allocId, rp₂.offset) ∈ h₂.footprint.addrs := by
          apply (hsplit₂_ab.2.2.2.1 _).mpr
          rw [h₂a_fp]
          exact Or.inl (List.mem_singleton.mpr rfl)
        cases hEqAlloc : Nat.beq allocId rp₁.allocId
        · have hAllocNe : allocId ≠ rp₁.allocId := Nat.ne_of_beq_eq_false hEqAlloc
          cases hEqAlloc2 : Nat.beq allocId rp₂.allocId
          · have hAllocNe2 : allocId ≠ rp₂.allocId := Nat.ne_of_beq_eq_false hEqAlloc2
            have hOut : ∀ e ∈ [(rp₁, codec₁.encode a_old), (rp₂, codec₂.encode b_old)], allocId ≠ e.1.allocId := by
              intro e hE
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
              rcases hE with rfl | rfl
              · exact hAllocNe
              · exact hAllocNe2
            have hGetEq := hPres.locals_unchanged_outside allocId hOut
            unfold readAllocAt? memoryLocals
            rw [hInv_final.callStack_nil, hWf₁.callStack_nil, hGetEq]
          · have hAllocEq2 : allocId = rp₂.allocId := Nat.eq_of_beq_eq_true hEqAlloc2
            subst hAllocEq2
            have hOffNe : rp₂.offset ≠ offset := by
              intro hEq
              subst hEq
              exact hsplit₂.2.2.1.1 (rp₂.allocId, rp₂.offset) hIn₂ hIn
            have hOffZero : rp₂.offset = 0 := hWf₂.exclusive.offset_zero
            have hOffsetPos : offset ≠ 0 := fun hZ => hOffNe (hZ ▸ hOffZero)
            have hNone₀ : readAllocAt? (memoryLocals m₀) { allocId := rp₂.allocId, offset := offset, tag := rp₂.allocId } = none := by
              have hPts₀ : readAllocAt? (memoryLocals m₀) rp₂ = some (codec₂.encode b_old) := by
                have h_eq : h₂a.state = m₀ := Eq.trans hsplit₂_ab.1 (Eq.trans hsplit₂.1 hsplit.2.1)
                exact h_eq ▸ hpts₂.1
              unfold readAllocAt? memoryLocals at hPts₀ ⊢
              rw [hWf₂.callStack_nil]
              rw [hWf₂.callStack_nil, hOffZero] at hPts₀
              dsimp only at hPts₀ ⊢
              cases hGet : get? m₀.callerLocals rp₂.allocId with
              | none => rfl
              | some slot =>
                cases slot with
                | dead => rfl
                | uninit => rfl
                | init val =>
                  rw [hGet] at hPts₀
                  dsimp only at hPts₀
                  injection hPts₀ with hV
                  subst hV
                  cases offset with
                  | zero => contradiction
                  | succ k =>
                    cases hVal : codec₂.encode b_old with
                    | aggregate m elems =>
                      cases m with
                      | zero => exfalso; exact h_not_agg2 b_old elems hVal
                      | succ m => rfl
                    | _ => rfl
            have hNone_final : readAllocAt? (memoryLocals m_final) { allocId := rp₂.allocId, offset := offset, tag := rp₂.allocId } = none := by
              have hMem : (rp₂, codec₂.encode b_new) ∈ [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] := by simp only [List.mem_cons]; exact Or.inr (Or.inl trivial)
              rcases hInv_final.entries_valid rp₂ (codec₂.encode b_new) hMem with ⟨_, _, hCaller, _⟩
              unfold readAllocAt? memoryLocals
              rw [hInv_final.callStack_nil, hCaller]
              cases offset with
              | zero => contradiction
              | succ k =>
                cases hVal : codec₂.encode b_new with
                | aggregate m elems =>
                  cases m with
                  | zero => exfalso; exact h_not_agg2 b_new elems hVal
                  | succ m => rfl
                | _ => rfl
            rw [hNone₀, hNone_final]
        · have hAllocEq : allocId = rp₁.allocId := Nat.eq_of_beq_eq_true hEqAlloc
          subst hAllocEq
          have hOffNe : rp₁.offset ≠ offset := by
            intro hEq
            subst hEq
            have hIn_h₂_3 : (rp₁.allocId, rp₁.offset) ∈ h₂_3.footprint.addrs := by apply (hsplit₂.2.2.2.1 _).mpr; exact Or.inr hIn
            exact hsplit.2.2.1.1 (rp₁.allocId, rp₁.offset) hIn₁ hIn_h₂_3
          have hOffZero : rp₁.offset = 0 := hWf₁.exclusive.offset_zero
          have hOffsetPos : offset ≠ 0 := fun hZ => hOffNe (hZ ▸ hOffZero)
          have hNone₀ : readAllocAt? (memoryLocals m₀) { allocId := rp₁.allocId, offset := offset, tag := rp₁.allocId } = none := by
            have hPts₀ : readAllocAt? (memoryLocals m₀) rp₁ = some (codec₁.encode a_old) := by
              have h_eq : h₁a.state = m₀ := Eq.trans hsplit_ab.1 hsplit.1
              exact h_eq ▸ hpts.1
            unfold readAllocAt? memoryLocals at hPts₀ ⊢
            rw [hWf₁.callStack_nil]
            rw [hWf₁.callStack_nil, hOffZero] at hPts₀
            dsimp only at hPts₀ ⊢
            cases hGet : get? m₀.callerLocals rp₁.allocId with
            | none => rfl
            | some slot =>
              cases slot with
              | dead => rfl
              | uninit => rfl
              | init val =>
                rw [hGet] at hPts₀
                dsimp only at hPts₀
                injection hPts₀ with hV
                subst hV
                cases offset with
                | zero => contradiction
                | succ k =>
                  cases hVal : codec₁.encode a_old with
                  | aggregate m elems =>
                    cases m with
                    | zero => exfalso; exact h_not_agg a_old elems hVal
                    | succ m => rfl
                  | _ => rfl
          have hNone_final : readAllocAt? (memoryLocals m_final) { allocId := rp₁.allocId, offset := offset, tag := rp₁.allocId } = none := by
            have hMem : (rp₁, codec₁.encode a_new) ∈ [(rp₁, codec₁.encode a_new), (rp₂, codec₂.encode b_new)] := by simp only [List.mem_cons]; exact Or.inl trivial
            rcases hInv_final.entries_valid rp₁ (codec₁.encode a_new) hMem with ⟨_, _, hCaller, _⟩
            unfold readAllocAt? memoryLocals
            rw [hInv_final.callStack_nil, hCaller]
            cases offset with
            | zero => contradiction
            | succ k =>
              cases hVal : codec₁.encode a_new with
              | aggregate m elems =>
                cases m with
                | zero => exfalso; exact h_not_agg a_new elems hVal
                | succ m => rfl
              | _ => rfl
          rw [hNone₀, hNone_final]
      · rcases hActive₁ with ⟨h₁a, h₁b, hsplit_ab, hpts, htok⟩
        rcases hActive₂ with ⟨h₂a, h₂b, hsplit₂_ab, hpts₂, htok₂⟩
        have h₁b_fp : h₁b.footprint = { addrs := [], tags := [rp₁.tag] } := htok.2
        have hIn₁ : rp₁.tag ∈ h₁.footprint.tags := by
          apply (hsplit_ab.2.2.2.2 _).mpr
          rw [h₁b_fp]
          exact Or.inr (List.mem_singleton.mpr rfl)
        have h₂b_fp : h₂b.footprint = { addrs := [], tags := [rp₂.tag] } := htok₂.2
        have hIn₂ : rp₂.tag ∈ h₂.footprint.tags := by
          apply (hsplit₂_ab.2.2.2.2 _).mpr
          rw [h₂b_fp]
          exact Or.inr (List.mem_singleton.mpr rfl)
        cases hEqTag : Nat.beq tag rp₁.tag
        · have hTagNe : tag ≠ rp₁.tag := Nat.ne_of_beq_eq_false hEqTag
          cases hEqTag2 : Nat.beq tag rp₂.tag
          · have hTagNe2 : tag ≠ rp₂.tag := Nat.ne_of_beq_eq_false hEqTag2
            have hEq := hPres.borrows_unchanged_outside tag (by
              intro e hE
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hE
              rcases hE with rfl | rfl
              · exact hTagNe
              · exact hTagNe2)
            exact Eq.symm hEq
          · have hTagEq2 : tag = rp₂.tag := Nat.eq_of_beq_eq_true hEqTag2
            subst hTagEq2
            have hIn_h₂_3 : rp₂.tag ∈ h₂_3.footprint.tags := by apply (hsplit₂.2.2.2.2 _).mpr; exact Or.inl hIn₂
            exact False.elim (hsplit₂.2.2.1.2 rp₂.tag hIn₂ hIn)
        · have hTagEq : tag = rp₁.tag := Nat.eq_of_beq_eq_true hEqTag
          subst hTagEq
          have hIn_h₂_3 : rp₁.tag ∈ h₂_3.footprint.tags := by apply (hsplit₂.2.2.2.2 _).mpr; exact Or.inr hIn
          exact False.elim (hsplit.2.2.1.2 rp₁.tag hIn₁ hIn_h₂_3)

theorem pairwise_disjoint_of_sepConj_two_ne {α : Type}
    {rp₁ rp₂ : RawPtrVal} {codec₁ codec₂ : ValueCodec α} {a₁ a₂ : α}
    {R_frame : SepProp} {m₀ : Memory}
    (hSep : SepProp.holdsIn (sepConj (ActiveTypedMutBorrow rp₁ codec₁ a₁) (sepConj (ActiveTypedMutBorrow rp₂ codec₂ a₂) R_frame)) m₀) :
    rp₁ ≠ rp₂ := by
  intro hEq
  rcases hSep with ⟨fp, h₁, h₂_3, hsplit_a, hActive_a, hSep_b⟩
  rcases hSep_b with ⟨h₂, h₃, hsplit_b, hActive_b, hR_b⟩
  rcases hActive_a with ⟨w1a, w2a, hsplit_wa, hpts_a, htok_a⟩
  rcases hActive_b with ⟨w1b, w2b, hsplit_wb, hpts_b, htok_b⟩
  have hIn_tag1 : rp₁.tag ∈ h₁.footprint.tags := by
    apply (hsplit_wa.2.2.2.2 _).mpr
    rw [htok_a.2]
    exact Or.inr (List.mem_singleton.mpr rfl)
  have hIn_tag2 : rp₂.tag ∈ h₂.footprint.tags := by
    apply (hsplit_wb.2.2.2.2 _).mpr
    rw [htok_b.2]
    exact Or.inr (List.mem_singleton.mpr rfl)
  have hIn_tag2_subst : rp₁.tag ∈ h₂.footprint.tags := hEq ▸ hIn_tag2
  exact hsplit_a.2.2.1.2 _ hIn_tag1 (by apply (hsplit_b.2.2.2.2 _).mpr; exact Or.inl hIn_tag2_subst)

/-! ## 3. Concrete Separation-Logic Lens Witnesses (`add_assign` & `swap_u32`) -/

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

def add_assign : CapturedMir where
  defPath := "demo::add_assign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 2 }, debugName := some "x" },
    { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 1 }, debugName := some "d" },
    { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 1 }, debugName := some "tmp" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 3, span := "add_assign" },
        { kind := .assign { local_ := 3, projection := [] } (.use (.copy { local_ := 1, projection := [.deref] })), span := "add_assign" },
        { kind := .assign { local_ := 1, projection := [.deref] } (.binaryOp .add (.copy { local_ := 3, projection := [] }) (.copy { local_ := 2, projection := [] })), span := "add_assign" },
        { kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })), span := "add_assign" },
        { kind := .storageDead 3, span := "add_assign" }
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

theorem add_assign_verified (x_ptr : RawPtrVal) (x_old d_val : Nat) (R_frame : SepProp) (h_R : LocalSepProp R_frame) :
  StatefulVerificationResult {
    body := add_assign,
    pre := fun args m₀ =>
      args = [.ptr x_ptr.toMirPtr 8, .scalar ⟨d_val, 4⟩] ∧
      WfSingleMutBorrow 4 x_ptr m₀ ∧
      SepProp.holdsIn (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) x_old) R_frame) m₀,
    post := fun _args _m₀ retVal m_final =>
      retVal = .unit ∧
      SepProp.holdsIn (sepConj (ActiveTypedMutBorrow x_ptr (ValueCodec.scalarNat 4) (wrapScalarBits (x_old + d_val) (scalarModulus 4))) R_frame) m_final
  } := by
  apply verifyStatefulMir_of_sepLenses
  intro args m₀ hPre
  rcases hPre with ⟨rfl, hWf, hSep⟩
  exists [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)]
  exists updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr (.scalar ⟨wrapScalarBits (x_old + d_val : Nat) (scalarModulus 4), 4⟩)
  exists Value.unit
  refine And.intro ?_ (And.intro ?_ ?_)
  · unfold initMachineState
    dsimp [add_assign, initLocals, initLocalsAux, List.length, List.append, Value.ptr, Rvalue.binaryOp]
    apply LiftLensBlock.return_ (env' := [.init .unit, .init (Value.ptr x_ptr.toMirPtr 8), .init (Value.scalar ⟨d_val, 4⟩), .dead])
    · rfl
    · rfl
    · rfl
    · apply LiftLensStmts.cons
      · apply LiftLensStmt.storageLive
        apply LiftStorageLive.mk (env' := [.uninit, .init (Value.ptr x_ptr.toMirPtr 8), .init (Value.scalar ⟨d_val, 4⟩), .uninit])
        · exact rfl
        · exact rfl
      · apply LiftLensStmts.cons
        · apply LiftLensStmt.pureAssign
          apply LiftPureAssign.mk (env₂ := [.uninit, .init (Value.ptr x_ptr.toMirPtr 8), .init (Value.scalar ⟨d_val, 4⟩), .init (Value.scalar ⟨x_old, 4⟩)])
          · apply LiftLensRvalue.use_deref
            apply LiftDerefRead.copy_deref
            · exact rfl
            · simp [lookupLensVal?]; rfl
          · exact rfl
          · exact fun h => nomatch h
          · exact rfl
        · apply LiftLensStmts.cons
          · apply LiftLensStmt.derefWrite
            apply LiftDerefWrite.mk
            · apply LiftLensRvalue.binaryOp_add_u32
              · apply LiftLensOperand.copy_local
                exact rfl
              · apply LiftLensOperand.copy_local
                exact rfl
            · exact rfl
            · simp [lookupLensVal?]; rfl
          · apply LiftLensStmts.cons
            · apply LiftLensStmt.pureAssign
              apply LiftPureAssign.mk (env₂ := [.init .unit, .init (Value.ptr x_ptr.toMirPtr 8), .init (Value.scalar ⟨d_val, 4⟩), .init (Value.scalar ⟨x_old, 4⟩)])
              · apply LiftLensRvalue.use_pure
                apply LiftLensOperand.const_zeroSized
              · exact rfl
              · exact fun h => nomatch h
              · exact rfl
            · apply LiftLensStmts.cons
              · apply LiftLensStmt.storageDead
                apply LiftStorageDead.mk (env' := [.init .unit, .init (Value.ptr x_ptr.toMirPtr 8), .init (Value.scalar ⟨d_val, 4⟩), .dead])
                · exact rfl
                · exact rfl
              · exact @LiftLensStmts.nil add_assign.localDecls add_assign.layouts [.init .unit, .init (Value.ptr x_ptr.toMirPtr 8), .init (Value.scalar ⟨d_val, 4⟩), .dead] _
    · rfl
  · exact sepLensStateInv_of_sepConj_one hSep hWf
  · intro m_final hInv hPres
    have hEq : updateLensVal [(x_ptr, (ValueCodec.scalarNat 4).encode x_old)] x_ptr (Value.scalar ⟨wrapScalarBits (x_old + d_val : Nat) (scalarModulus 4), 4⟩) = [(x_ptr, (ValueCodec.scalarNat 4).encode (wrapScalarBits (x_old + d_val : Nat) (scalarModulus 4)))] := by
      simp [updateLensVal, ValueCodec.scalarNat]
    have h_not_agg : ∀ a : Nat, ∀ elems, (ValueCodec.scalarNat 4).encode a ≠ .aggregate 0 elems := by
      intro a elems hEqAgg
      unfold ValueCodec.encode ValueCodec.scalarNat at hEqAgg
      dsimp only at hEqAgg
      injection hEqAgg
    exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_one hSep (hEq ▸ hInv) hWf hPres h_R h_not_agg⟩

def swap_u32 : CapturedMir where
  defPath := "demo::swap_u32"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [
    { mutability := .mut, ty := { kind := .tuple [], layoutIdx := 0 }, debugName := some "_0" },
    { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 2 }, debugName := some "a" },
    { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 2 }, debugName := some "b" },
    { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 1 }, debugName := some "tmp" }
  ]
  basicBlocks := [
    { statements := [
        { kind := .storageLive 3, span := "swap_u32" },
        { kind := .assign { local_ := 3, projection := [] } (.use (.copy { local_ := 1, projection := [.deref] })), span := "swap_u32" },
        { kind := .assign { local_ := 1, projection := [.deref] } (.use (.copy { local_ := 2, projection := [.deref] })), span := "swap_u32" },
        { kind := .assign { local_ := 2, projection := [.deref] } (.use (.copy { local_ := 3, projection := [] })), span := "swap_u32" },
        { kind := .assign { local_ := 0, projection := [] } (.use (.constant { ty := { kind := .tuple [], layoutIdx := 0 }, val := .zeroSized })), span := "swap_u32" },
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

theorem swap_u32_verified (a_ptr b_ptr : RawPtrVal) (a_old b_old : Nat) (R_frame : SepProp) (h_R : LocalSepProp R_frame) :
  StatefulVerificationResult {
    body := swap_u32,
    pre := fun args m₀ =>
      args = [.ptr a_ptr.toMirPtr 8, .ptr b_ptr.toMirPtr 8] ∧
      WfSingleMutBorrow 4 a_ptr m₀ ∧
      WfSingleMutBorrow 4 b_ptr m₀ ∧
      SepProp.holdsIn (sepConj (ActiveTypedMutBorrow a_ptr (ValueCodec.scalarNat 4) a_old) (sepConj (ActiveTypedMutBorrow b_ptr (ValueCodec.scalarNat 4) b_old) R_frame)) m₀,
    post := fun _args _m₀ retVal m_final =>
      retVal = .unit ∧
      SepProp.holdsIn (sepConj (ActiveTypedMutBorrow a_ptr (ValueCodec.scalarNat 4) b_old) (sepConj (ActiveTypedMutBorrow b_ptr (ValueCodec.scalarNat 4) a_old) R_frame)) m_final
  } := by
  apply verifyStatefulMir_of_sepLenses
  intro args m₀ hPre
  rcases hPre with ⟨rfl, hWf_a, hWf_b, hSep⟩
  have hNe : a_ptr ≠ b_ptr := pairwise_disjoint_of_sepConj_two_ne hSep
  exists [(a_ptr, (ValueCodec.scalarNat 4).encode a_old), (b_ptr, (ValueCodec.scalarNat 4).encode b_old)]
  exists updateLensVal (updateLensVal [(a_ptr, (ValueCodec.scalarNat 4).encode a_old), (b_ptr, (ValueCodec.scalarNat 4).encode b_old)] a_ptr (.scalar ⟨b_old, 4⟩)) b_ptr (.scalar ⟨a_old, 4⟩)
  exists Value.unit
  refine And.intro ?_ (And.intro ?_ ?_)
  · unfold initMachineState
    dsimp [swap_u32, initLocals, initLocalsAux, List.length, List.append, Value.ptr, Rvalue.binaryOp]
    apply LiftLensBlock.return_ (env' := [.init .unit, .init (Value.ptr a_ptr.toMirPtr 8), .init (Value.ptr b_ptr.toMirPtr 8), .dead])
    · rfl
    · rfl
    · rfl
    · apply LiftLensStmts.cons
      · apply LiftLensStmt.storageLive
        apply LiftStorageLive.mk (env' := [.uninit, .init (Value.ptr a_ptr.toMirPtr 8), .init (Value.ptr b_ptr.toMirPtr 8), .uninit])
        · exact rfl
        · exact rfl
      · apply LiftLensStmts.cons
        · apply LiftLensStmt.pureAssign
          apply LiftPureAssign.mk (env₂ := [.uninit, .init (Value.ptr a_ptr.toMirPtr 8), .init (Value.ptr b_ptr.toMirPtr 8), .init (Value.scalar ⟨a_old, 4⟩)])
          · apply LiftLensRvalue.use_deref
            apply LiftDerefRead.copy_deref
            · exact rfl
            · simp [lookupLensVal?]; rfl
          · exact rfl
          · exact fun h => nomatch h
          · exact rfl
        · apply LiftLensStmts.cons
          · apply LiftLensStmt.derefWrite
            apply LiftDerefWrite.mk
            · apply LiftLensRvalue.use_deref
              apply LiftDerefRead.copy_deref
              · exact rfl
              · simp [lookupLensVal?, hNe]; rfl
            · exact rfl
            · simp [lookupLensVal?]; rfl
          · apply LiftLensStmts.cons
            · apply LiftLensStmt.derefWrite
              apply LiftDerefWrite.mk
              · apply LiftLensRvalue.use_pure
                apply LiftLensOperand.copy_local
                · exact rfl
              · exact rfl
              · simp [lookupLensVal?, updateLensVal, hNe]; rfl
            · apply LiftLensStmts.cons
              · apply LiftLensStmt.pureAssign
                apply LiftPureAssign.mk (env₂ := [.init .unit, .init (Value.ptr a_ptr.toMirPtr 8), .init (Value.ptr b_ptr.toMirPtr 8), .init (Value.scalar ⟨a_old, 4⟩)])
                · apply LiftLensRvalue.use_pure
                  apply LiftLensOperand.const_zeroSized
                · exact rfl
                · exact fun h => nomatch h
                · exact rfl
              · apply LiftLensStmts.cons
                · apply LiftLensStmt.storageDead
                  apply LiftStorageDead.mk (env' := [.init .unit, .init (Value.ptr a_ptr.toMirPtr 8), .init (Value.ptr b_ptr.toMirPtr 8), .dead])
                  · exact rfl
                  · exact rfl
                · exact @LiftLensStmts.nil swap_u32.localDecls swap_u32.layouts [.init .unit, .init (Value.ptr a_ptr.toMirPtr 8), .init (Value.ptr b_ptr.toMirPtr 8), .dead] _
    · rfl
  · exact sepLensStateInv_of_sepConj_two hSep hWf_a hWf_b
  · intro m_final hInv hPres
    have hEq : updateLensVal (updateLensVal [(a_ptr, (ValueCodec.scalarNat 4).encode a_old), (b_ptr, (ValueCodec.scalarNat 4).encode b_old)] a_ptr (Value.scalar ⟨b_old, 4⟩)) b_ptr (Value.scalar ⟨a_old, 4⟩) = [(a_ptr, (ValueCodec.scalarNat 4).encode b_old), (b_ptr, (ValueCodec.scalarNat 4).encode a_old)] := by
      simp [updateLensVal, ValueCodec.scalarNat, hNe]
    have h_not_agg : ∀ a : Nat, ∀ elems, (ValueCodec.scalarNat 4).encode a ≠ .aggregate 0 elems := by
      intro a elems hEqAgg
      unfold ValueCodec.encode ValueCodec.scalarNat at hEqAgg
      dsimp only at hEqAgg
      injection hEqAgg
    exact ⟨rfl, sepConj_activeTypedMutBorrow_preserved_two a_ptr b_ptr (ValueCodec.scalarNat 4) (ValueCodec.scalarNat 4) a_old b_old b_old a_old hSep (hEq ▸ hInv) hWf_a hWf_b hPres h_R h_not_agg h_not_agg⟩

end Anneal.SepLogicLenses

