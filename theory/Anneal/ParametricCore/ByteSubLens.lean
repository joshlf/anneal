-- Copyright 2026 The Fuchsia Authors
--
-- Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
-- <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
-- license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
-- This file may not be copied, modified, or distributed except according to
-- those terms.

prelude
import Init.Core
import Init.NotationExtra
import Init.Data.Nat.Basic
import Init.Data.Nat.Div.Basic
import Init.Data.List.Basic
import Init.Data.Option.Basic
import Init.Data.BitVec.BasicAux
import Init.Data.UInt.BasicAux
import Init.Data.Fin.Basic
import Anneal.BitVec
import Anneal.LeBytes
import Anneal.ListChunks
import Anneal.ParametricCore.LoopInv

universe u v w x y z a b

namespace Anneal.ParametricCore

/-!
# Memory-Model-Parametric Byte Sub-Lenses and Mutation Summaries
(`Anneal.ParametricCore.ByteSubLens`)

This module restates the sub-allocation byte lenses and `&mut` call summaries
of `Anneal.ByteSubLens.{Lens,MutSummary}` (`#4120`) over a thin byte-store
interface, `ByteStoreOps Mem Addr`, instead of one fixed memory model.

1. **Byte-store interface (`ByteStoreOps`, `LawfulByteStoreOps`):** slice
   reads and writes over an abstract memory, address and byte type, with the
   read/write laws that make every slice a lawful lens.
2. **Canonical table model (`AllocView`, `tableRead`, `tableWrite`,
   `SliceStore`):** a list of allocations looked up by first match. It
   satisfies every law without assuming that allocation identifiers are
   unique, and `ByteStoreOps.ofTable` turns any memory type with an
   allocation-table field into a lawful byte store.
3. **Byte sub-lenses (`ByteSubLens`):** `get`, `set`, footprint, the four lens
   and frame laws, commuting disjoint writes, hierarchical containment
   (`zoom`), split-borrow disjointness, and fail-closed rejection of
   zero-length, wrong-length and out-of-bounds accesses.
4. **Typed views:** little-endian `BitVec`, `UInt16`, `UInt32` and `UInt64`
   views through a byte codec (`Anneal.LeBytes`, `Anneal.BitVec`), and a
   chunked array view (`Anneal.ListChunks`).
5. **Mutation summaries (`MutSummary`, `MutSummaryCut`):** a computable
   summary of a callee that mutates one sub-lens, its realization over a
   `MirWpOps` step interface, a zero-`Prop`-argument `@[irreducible]` cut
   sealing the realization proof, and chained summaries with a frame theorem
   for every disjoint lens.
-/

/-! ## Part I: `Nat`, `Bool` and `List` Slice Helpers -/

/-- `Nat.beq` returning `false` is symmetric. -/
theorem natBeq_false_symm {a b : Nat} (h : Nat.beq a b = false) :
    Nat.beq b a = false := by
  cases hb : Nat.beq b a with
  | false => rfl
  | true =>
    have hEq : b = a := Nat.eq_of_beq_eq_true hb
    exact False.elim (Nat.ne_of_beq_eq_false h hEq.symm)

/-- `Nat.beq` returns `false` on distinct numbers. -/
theorem natBeq_false_of_not_eq {a b : Nat} (h : ¬ a = b) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (Nat.eq_of_beq_eq_true hb))

/-- `Nat.ble` returns `false` when the order fails. -/
theorem natBle_false_of_not_le {a b : Nat} (h : ¬ a ≤ b) :
    Nat.ble a b = false := by
  cases hb : Nat.ble a b with
  | false => rfl
  | true => exact False.elim (h (Nat.le_of_ble_eq_true hb))

/-- A conjunction of booleans is `true` when both are. -/
theorem boolAnd_intro {a b : Bool} (ha : a = true) (hb : b = true) :
    (a && b) = true := by
  rw [ha, hb]
  rfl

/-- The left conjunct of a `true` boolean conjunction. -/
theorem boolAnd_left {a b : Bool} (h : (a && b) = true) : a = true := by
  cases a with
  | false => cases h
  | true => rfl

/-- The right conjunct of a `true` boolean conjunction. -/
theorem boolAnd_right {a b : Bool} (h : (a && b) = true) : b = true := by
  cases a with
  | false => cases h
  | true => exact h

section ListSlices

variable {α : Type u}

/-- Taking at most the whole list has the requested length. -/
theorem listTake_length_of_le :
    ∀ (n : Nat) (xs : List α), n ≤ xs.length → (xs.take n).length = n
  | 0, _, _ => rfl
  | n + 1, [], h => False.elim (Nat.not_succ_le_zero n h)
  | n + 1, _ :: tl, h =>
    congrArg Nat.succ
      (listTake_length_of_le n tl (Nat.le_of_succ_le_succ h))

/-- Taking the whole list is the identity. -/
theorem listTake_length_self : ∀ (xs : List α), xs.take xs.length = xs
  | [] => rfl
  | hd :: tl => congrArg (List.cons hd) (listTake_length_self tl)

/-- A list is its prefix followed by the rest. -/
theorem listTake_append_drop :
    ∀ (n : Nat) (xs : List α), xs.take n ++ xs.drop n = xs
  | 0, _ => rfl
  | _ + 1, [] => rfl
  | n + 1, hd :: tl => congrArg (List.cons hd) (listTake_append_drop n tl)

/-- Length of a dropped list. -/
theorem listDrop_length :
    ∀ (n : Nat) (xs : List α), (xs.drop n).length = xs.length - n
  | 0, _ => rfl
  | n + 1, [] => (Nat.zero_sub (n + 1)).symm
  | n + 1, _ :: tl => by
    change (tl.drop n).length = (tl.length + 1) - (n + 1)
    rw [Nat.succ_sub_succ]
    exact listDrop_length n tl

/-- Dropping `a + b` elements is dropping `a` and then `b`. -/
theorem listDrop_add (a b : Nat) (xs : List α) :
    xs.drop (a + b) = (xs.drop a).drop b := by
  induction a generalizing xs with
  | zero => exact congrArg (fun k => xs.drop k) (Nat.zero_add b)
  | succ a ih =>
    rw [Nat.succ_add]
    cases xs with
    | nil =>
      have hNil : ∀ k, List.drop k ([] : List α) = [] := fun _ =>
        List.drop_nil
      rw [hNil (Nat.succ (a + b)), hNil (a + 1), hNil b]
    | cons _ tl => exact ih tl

/-- Dropping exactly a prefix leaves the suffix. -/
theorem listDrop_append_exact (xs ys : List α) :
    (xs ++ ys).drop xs.length = ys := by
  induction xs with
  | nil => rfl
  | cons _ tl ih => exact ih

/-- Taking exactly a prefix returns it. -/
theorem listTake_append_exact (xs ys : List α) :
    (xs ++ ys).take xs.length = xs := by
  induction xs with
  | nil => rfl
  | cons hd tl ih => exact congrArg (List.cons hd) ih

/-- Dropping a prefix of known length leaves the suffix. -/
theorem listDrop_append_of_len (n : Nat) (xs ys : List α)
    (h : xs.length = n) : (xs ++ ys).drop n = ys := by
  rw [← h]
  exact listDrop_append_exact xs ys

/-- Taking a prefix of known length returns it. -/
theorem listTake_append_of_len (n : Nat) (xs ys : List α)
    (h : xs.length = n) : (xs ++ ys).take n = xs := by
  rw [← h]
  exact listTake_append_exact xs ys

/-- Dropping within the first part of an append. -/
theorem listDrop_append_of_le :
    ∀ (n : Nat) (xs ys : List α), n ≤ xs.length →
      (xs ++ ys).drop n = xs.drop n ++ ys
  | 0, _, _, _ => rfl
  | n + 1, [], _, h => False.elim (Nat.not_succ_le_zero n h)
  | n + 1, _ :: tl, ys, h =>
    listDrop_append_of_le n tl ys (Nat.le_of_succ_le_succ h)

/-- Taking within the first part of an append. -/
theorem listTake_append_of_le :
    ∀ (n : Nat) (xs ys : List α), n ≤ xs.length →
      (xs ++ ys).take n = xs.take n
  | 0, _, _, _ => rfl
  | n + 1, [], _, h => False.elim (Nat.not_succ_le_zero n h)
  | n + 1, hd :: tl, ys, h =>
    congrArg (List.cons hd)
      (listTake_append_of_le n tl ys (Nat.le_of_succ_le_succ h))

/-- Dropping past the first part of an append. -/
theorem listDrop_append_of_ge :
    ∀ (n : Nat) (xs ys : List α), xs.length ≤ n →
      (xs ++ ys).drop n = ys.drop (n - xs.length)
  | _, [], _, _ => rfl
  | 0, _ :: _, _, h => False.elim (Nat.not_succ_le_zero _ h)
  | n + 1, _ :: tl, ys, h => by
    change (tl ++ ys).drop n = ys.drop ((n + 1) - (tl.length + 1))
    rw [Nat.succ_sub_succ]
    exact listDrop_append_of_ge n tl ys (Nat.le_of_succ_le_succ h)

/-- Taking a shorter prefix of a prefix. -/
theorem listTake_take_of_le :
    ∀ (sz n : Nat) (xs : List α), sz ≤ n → (xs.take n).take sz = xs.take sz
  | 0, _, _, _ => rfl
  | sz + 1, 0, _, h => False.elim (Nat.not_succ_le_zero sz h)
  | _ + 1, _ + 1, [], _ => rfl
  | sz + 1, n + 1, hd :: tl, h =>
    congrArg (List.cons hd)
      (listTake_take_of_le sz n tl (Nat.le_of_succ_le_succ h))

/-- A slice that ends within a prefix is a slice of the whole list. -/
theorem listDrop_take_comm_le :
    ∀ (off sz n : Nat) (xs : List α), off + sz ≤ n →
      ((xs.take n).drop off).take sz = (xs.drop off).take sz
  | 0, sz, n, xs, h =>
    listTake_take_of_le sz n xs (Nat.le_trans (Nat.le_add_left sz 0) h)
  | off + 1, sz, 0, _, h =>
    False.elim (Nat.not_succ_le_zero (off + sz)
      (Nat.le_trans (Nat.le_of_eq (Nat.succ_add off sz).symm) h))
  | _ + 1, _, _ + 1, [], _ => rfl
  | off + 1, sz, n + 1, _ :: tl, h =>
    listDrop_take_comm_le off sz n tl
      (Nat.le_of_succ_le_succ
        (Nat.le_trans (Nat.le_of_eq (Nat.succ_add off sz).symm) h))

/-- An in-bounds slice has the requested length. -/
theorem listSlice_length (xs : List α) (off len : Nat)
    (h : off + len ≤ xs.length) : ((xs.drop off).take len).length = len := by
  refine listTake_length_of_le len (xs.drop off) ?_
  rw [listDrop_length]
  refine Nat.le_sub_of_add_le ?_
  rw [Nat.add_comm len off]
  exact h

/-- A sub-slice of a slice is a slice of the whole list. -/
theorem listSlice_slice (xs : List α) (off len rel k : Nat)
    (h : rel + k ≤ len) :
    (((xs.drop off).take len).drop rel).take k =
      (xs.drop (off + rel)).take k := by
  rw [listDrop_take_comm_le rel k len (xs.drop off) h, listDrop_add]

/-- Replaces the slice of `xs` that starts at `off` by `mid`. -/
def listSplice (xs : List α) (off : Nat) (mid : List α) : List α :=
  xs.take off ++ mid ++ xs.drop (off + mid.length)

/-- An in-bounds splice preserves the length. -/
theorem listSplice_length (xs : List α) (off : Nat) (mid : List α)
    (h : off + mid.length ≤ xs.length) :
    (listSplice xs off mid).length = xs.length := by
  have hOff : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off mid.length) h
  unfold listSplice
  rw [List.length_append, List.length_append,
    listTake_length_of_le off xs hOff, listDrop_length]
  exact Nat.add_sub_of_le h

/-- The prefix before a splice is unchanged. -/
theorem listSplice_take_prefix (xs : List α) (off : Nat) (mid : List α)
    (h : off + mid.length ≤ xs.length) :
    (listSplice xs off mid).take off = xs.take off := by
  have hOff : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off mid.length) h
  unfold listSplice
  rw [List.append_assoc]
  exact listTake_append_of_len off (xs.take off) _
    (listTake_length_of_le off xs hOff)

/-- The suffix after a splice is unchanged. -/
theorem listSplice_drop_suffix (xs : List α) (off : Nat) (mid : List α)
    (h : off + mid.length ≤ xs.length) :
    (listSplice xs off mid).drop (off + mid.length) =
      xs.drop (off + mid.length) := by
  have hOff : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off mid.length) h
  have hPreLen : (xs.take off ++ mid).length = off + mid.length := by
    rw [List.length_append, listTake_length_of_le off xs hOff]
  unfold listSplice
  exact listDrop_append_of_len (off + mid.length) (xs.take off ++ mid)
    (xs.drop (off + mid.length)) hPreLen

/-- Reading back a splice returns the spliced slice. -/
theorem listSplice_read_same (xs : List α) (off : Nat) (mid : List α)
    (h : off + mid.length ≤ xs.length) :
    ((listSplice xs off mid).drop off).take mid.length = mid := by
  have hOff : off ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off mid.length) h
  unfold listSplice
  rw [List.append_assoc,
    listDrop_append_of_len off (xs.take off) _
      (listTake_length_of_le off xs hOff)]
  exact listTake_append_exact mid (xs.drop (off + mid.length))

/-- Splicing a slice back into its own position is the identity. -/
theorem listSplice_self (xs : List α) (off len : Nat)
    (h : off + len ≤ xs.length) :
    listSplice xs off ((xs.drop off).take len) = xs := by
  unfold listSplice
  rw [listSlice_length xs off len h, List.append_assoc, listDrop_add off len xs,
    listTake_append_drop len (xs.drop off)]
  exact listTake_append_drop off xs

/-- A second splice of the same length at the same offset overwrites the
first. -/
theorem listSplice_overwrite (xs : List α) (off : Nat) (mid₁ mid₂ : List α)
    (h : off + mid₁.length ≤ xs.length) (hLen : mid₂.length = mid₁.length) :
    listSplice (listSplice xs off mid₁) off mid₂ = listSplice xs off mid₂ := by
  have hPre := listSplice_take_prefix xs off mid₁ h
  have hSuf := listSplice_drop_suffix xs off mid₁ h
  unfold listSplice at hPre hSuf
  unfold listSplice
  rw [hLen, hPre, hSuf]

/-- A slice disjoint from a splice is unchanged by it. -/
theorem listSplice_read_disjoint (xs : List α) (off₁ : Nat) (mid : List α)
    (off₂ sz₂ : Nat) (h : off₁ + mid.length ≤ xs.length)
    (hDisj : off₁ + mid.length ≤ off₂ ∨ off₂ + sz₂ ≤ off₁) :
    ((listSplice xs off₁ mid).drop off₂).take sz₂ =
      (xs.drop off₂).take sz₂ := by
  have hOff : off₁ ≤ xs.length :=
    Nat.le_trans (Nat.le_add_right off₁ mid.length) h
  cases hDisj with
  | inl hLeft =>
    have hPreLen : (xs.take off₁ ++ mid).length = off₁ + mid.length := by
      rw [List.length_append, listTake_length_of_le off₁ xs hOff]
    have hDrop : (listSplice xs off₁ mid).drop off₂ = xs.drop off₂ := by
      unfold listSplice
      rw [listDrop_append_of_ge off₂ (xs.take off₁ ++ mid)
          (xs.drop (off₁ + mid.length))
          (Nat.le_trans (Nat.le_of_eq hPreLen) hLeft),
        hPreLen, ← listDrop_add (off₁ + mid.length) _ xs,
        Nat.add_sub_of_le hLeft]
    rw [hDrop]
  | inr hRight =>
    rw [← listDrop_take_comm_le off₂ sz₂ off₁ (listSplice xs off₁ mid) hRight,
      listSplice_take_prefix xs off₁ mid h]
    exact listDrop_take_comm_le off₂ sz₂ off₁ xs hRight

/-- A splice inside the first part of an append stays inside it. -/
theorem listSplice_append_right (pre rest : List α) (off : Nat)
    (mid : List α) (h : off + mid.length ≤ pre.length) :
    listSplice (pre ++ rest) off mid = listSplice pre off mid ++ rest := by
  have hOff : off ≤ pre.length :=
    Nat.le_trans (Nat.le_add_right off mid.length) h
  unfold listSplice
  rw [listTake_append_of_le off pre rest hOff,
    listDrop_append_of_le (off + mid.length) pre rest h]
  exact (List.append_assoc _ _ _).symm

/-- A splice one position into a cons is a splice of the tail. -/
theorem listSplice_cons_succ (hd : α) (xs : List α) (off : Nat)
    (mid : List α) :
    listSplice (hd :: xs) (off + 1) mid = hd :: listSplice xs off mid := by
  have hIdx : off + 1 + mid.length = (off + mid.length) + 1 :=
    Nat.succ_add off mid.length
  unfold listSplice
  rw [hIdx]
  rfl

/-- A splice past the first part of an append is a splice of the second
part. -/
theorem listSplice_append_left (pre rest : List α) (off : Nat)
    (mid : List α) :
    listSplice (pre ++ rest) (pre.length + off) mid =
      pre ++ listSplice rest off mid := by
  induction pre with
  | nil =>
    change listSplice rest (0 + off) mid = listSplice rest off mid
    rw [Nat.zero_add]
  | cons hd tl ih =>
    change listSplice (hd :: (tl ++ rest)) (tl.length + 1 + off) mid =
      hd :: (tl ++ listSplice rest off mid)
    rw [Nat.succ_add tl.length off, listSplice_cons_succ, ih]

/-- Splices on either side of an append boundary commute. -/
theorem listSplice_comm_append (pre rest : List α) (off₁ : Nat)
    (mid₁ : List α) (off₂ : Nat) (mid₂ : List α)
    (h₁ : off₁ + mid₁.length ≤ pre.length) :
    listSplice (listSplice (pre ++ rest) off₁ mid₁) (pre.length + off₂) mid₂ =
      listSplice (listSplice (pre ++ rest) (pre.length + off₂) mid₂) off₁
        mid₁ := by
  have hLen : (listSplice pre off₁ mid₁).length = pre.length :=
    listSplice_length pre off₁ mid₁ h₁
  rw [listSplice_append_right pre rest off₁ mid₁ h₁,
    listSplice_append_left pre rest off₂ mid₂,
    listSplice_append_right pre (listSplice rest off₂ mid₂) off₁ mid₁ h₁,
    ← hLen]
  exact listSplice_append_left (listSplice pre off₁ mid₁) rest off₂ mid₂

/-- Splices of separated ranges commute. -/
theorem listSplice_comm (xs : List α) (off₁ : Nat) (mid₁ : List α)
    (off₂ : Nat) (mid₂ : List α) (hSep : off₁ + mid₁.length ≤ off₂)
    (hOff₂ : off₂ ≤ xs.length) :
    listSplice (listSplice xs off₁ mid₁) off₂ mid₂ =
      listSplice (listSplice xs off₂ mid₂) off₁ mid₁ := by
  have hLen : (xs.take off₂).length = off₂ :=
    listTake_length_of_le off₂ xs hOff₂
  have hKey := listSplice_comm_append (xs.take off₂) (xs.drop off₂) off₁ mid₁
    0 mid₂ (Nat.le_trans hSep (Nat.le_of_eq hLen.symm))
  rw [listTake_append_drop off₂ xs, hLen, Nat.add_zero] at hKey
  exact hKey

end ListSlices

/-! ## Part II: First-Match Allocation Tables (`AllocView`, `tableRead`) -/

/-- View of an allocation record `A` as an identified, guarded byte buffer.
`allocId` names the allocation, `bytes` and `setBytes` read and replace its
contents, and `writable` gates every access through a byte lens (for example
"live and mutable"). -/
structure AllocView (A : Type u) (Byte : Type v) where
  /-- Identifier of the allocation. -/
  allocId : A → Nat
  /-- Contents of the allocation. -/
  bytes : A → List Byte
  /-- Replaces the contents of the allocation. -/
  setBytes : A → List Byte → A
  /-- Whether a byte lens may access the allocation. -/
  writable : A → Bool

/-- Laws of an `AllocView`: `setBytes` changes the contents and nothing else,
and it is a lens over `bytes`. -/
structure AllocView.Lawful {A : Type u} {Byte : Type v}
    (view : AllocView A Byte) : Prop where
  /-- `setBytes` keeps the identifier. -/
  allocId_setBytes : ∀ (a : A) (bs : List Byte),
    view.allocId (view.setBytes a bs) = view.allocId a
  /-- `bytes` after `setBytes` returns the written contents. -/
  bytes_setBytes : ∀ (a : A) (bs : List Byte),
    view.bytes (view.setBytes a bs) = bs
  /-- `setBytes` keeps the access guard. -/
  writable_setBytes : ∀ (a : A) (bs : List Byte),
    view.writable (view.setBytes a bs) = view.writable a
  /-- Writing back the current contents is the identity. -/
  setBytes_bytes : ∀ (a : A), view.setBytes a (view.bytes a) = a
  /-- A second `setBytes` overwrites the first. -/
  setBytes_setBytes : ∀ (a : A) (bs₁ bs₂ : List Byte),
    view.setBytes (view.setBytes a bs₁) bs₂ = view.setBytes a bs₂

section Table

variable {A : Type u} {Byte : Type v}

/-- First allocation of `allocs` whose identifier is `id` (`0`
`noncomputable`, `0` `._unsafe_rec`). -/
def tableFind (view : AllocView A Byte) (id : Nat) (allocs : List A) :
    Option A :=
  List.foldr
    (fun a rest =>
      match Nat.beq (view.allocId a) id with
      | true => some a
      | false => rest)
    none allocs

/-- Replaces the first allocation of `allocs` that has the identifier of
`aNew` by `aNew`, and leaves `allocs` unchanged when there is none (`0`
`noncomputable`, `0` `._unsafe_rec`). -/
def tableReplace (view : AllocView A Byte) (aNew : A) (allocs : List A) :
    List A :=
  @Nat.rec (fun _ => List A → List A)
    (fun l => l)
    (fun _ ih l =>
      match l with
      | [] => []
      | a :: rest =>
        match Nat.beq (view.allocId a) (view.allocId aNew) with
        | true => aNew :: rest
        | false => a :: ih rest)
    allocs.length allocs

/-- `tableFind` on a table whose head has the requested identifier. -/
theorem tableFind_cons_of_beq {view : AllocView A Byte} {id : Nat} {a : A}
    {rest : List A} (h : Nat.beq (view.allocId a) id = true) :
    tableFind view id (a :: rest) = some a := by
  change (match Nat.beq (view.allocId a) id with
    | true => some a
    | false => tableFind view id rest) = some a
  rw [h]

/-- `tableFind` on a table whose head has another identifier. -/
theorem tableFind_cons_of_not_beq {view : AllocView A Byte} {id : Nat}
    {a : A} {rest : List A} (h : Nat.beq (view.allocId a) id = false) :
    tableFind view id (a :: rest) = tableFind view id rest := by
  change (match Nat.beq (view.allocId a) id with
    | true => some a
    | false => tableFind view id rest) = tableFind view id rest
  rw [h]

/-- `tableReplace` on a table whose head has the identifier of `aNew`. -/
theorem tableReplace_cons_of_beq {view : AllocView A Byte} {aNew a : A}
    {rest : List A}
    (h : Nat.beq (view.allocId a) (view.allocId aNew) = true) :
    tableReplace view aNew (a :: rest) = aNew :: rest := by
  change (match Nat.beq (view.allocId a) (view.allocId aNew) with
    | true => aNew :: rest
    | false => a :: tableReplace view aNew rest) = aNew :: rest
  rw [h]

/-- `tableReplace` on a table whose head has another identifier. -/
theorem tableReplace_cons_of_not_beq {view : AllocView A Byte} {aNew a : A}
    {rest : List A}
    (h : Nat.beq (view.allocId a) (view.allocId aNew) = false) :
    tableReplace view aNew (a :: rest) = a :: tableReplace view aNew rest := by
  change (match Nat.beq (view.allocId a) (view.allocId aNew) with
    | true => aNew :: rest
    | false => a :: tableReplace view aNew rest) =
    a :: tableReplace view aNew rest
  rw [h]

/-- A found allocation has the requested identifier. -/
theorem tableFind_allocId {view : AllocView A Byte} {id : Nat}
    {allocs : List A} {a : A} (h : tableFind view id allocs = some a) :
    view.allocId a = id := by
  induction allocs with
  | nil => cases h
  | cons hd rest ih =>
    cases hEq : Nat.beq (view.allocId hd) id with
    | true =>
      rw [tableFind_cons_of_beq hEq] at h
      have hA : hd = a := Option.some.inj h
      rw [← hA]
      exact Nat.eq_of_beq_eq_true hEq
    | false =>
      rw [tableFind_cons_of_not_beq hEq] at h
      exact ih h

/-- Writing back the first-matching allocation is the identity on the table.
No uniqueness of identifiers is needed. -/
theorem tableReplace_self {view : AllocView A Byte} {id : Nat}
    {allocs : List A} {a : A} (h : tableFind view id allocs = some a) :
    tableReplace view a allocs = allocs := by
  have hId := tableFind_allocId h
  induction allocs with
  | nil => cases h
  | cons hd rest ih =>
    cases hEq : Nat.beq (view.allocId hd) id with
    | true =>
      rw [tableFind_cons_of_beq hEq] at h
      have hA : hd = a := Option.some.inj h
      rw [← hA]
      exact tableReplace_cons_of_beq (Nat.beq_refl (view.allocId hd))
    | false =>
      rw [tableFind_cons_of_not_beq hEq] at h
      have hNe : Nat.beq (view.allocId hd) (view.allocId a) = false := by
        rw [hId]
        exact hEq
      rw [tableReplace_cons_of_not_beq hNe]
      exact congrArg (List.cons hd) (ih h)

/-- Looking up the identifier of a replaced allocation returns the new
allocation. -/
theorem tableFind_replace_same {view : AllocView A Byte} {allocs : List A}
    {aOld aNew : A}
    (hFind : tableFind view (view.allocId aOld) allocs = some aOld)
    (hSameId : view.allocId aNew = view.allocId aOld) :
    tableFind view (view.allocId aOld) (tableReplace view aNew allocs) =
      some aNew := by
  induction allocs with
  | nil => cases hFind
  | cons hd rest ih =>
    cases hEq : Nat.beq (view.allocId hd) (view.allocId aOld) with
    | true =>
      have hEq' : Nat.beq (view.allocId hd) (view.allocId aNew) = true := by
        rw [hSameId]
        exact hEq
      have hNew : Nat.beq (view.allocId aNew) (view.allocId aOld) = true := by
        rw [hSameId]
        exact Nat.beq_refl (view.allocId aOld)
      rw [tableReplace_cons_of_beq hEq']
      exact tableFind_cons_of_beq hNew
    | false =>
      have hEq' : Nat.beq (view.allocId hd) (view.allocId aNew) = false := by
        rw [hSameId]
        exact hEq
      rw [tableFind_cons_of_not_beq hEq] at hFind
      rw [tableReplace_cons_of_not_beq hEq', tableFind_cons_of_not_beq hEq]
      exact ih hFind

/-- Replacing an allocation preserves lookups at every other identifier. -/
theorem tableFind_replace_ne {view : AllocView A Byte} {otherId : Nat}
    {allocs : List A} {aNew : A}
    (hNe : Nat.beq (view.allocId aNew) otherId = false) :
    tableFind view otherId (tableReplace view aNew allocs) =
      tableFind view otherId allocs := by
  induction allocs with
  | nil => rfl
  | cons hd rest ih =>
    cases hEq : Nat.beq (view.allocId hd) (view.allocId aNew) with
    | true =>
      have hHd : view.allocId hd = view.allocId aNew :=
        Nat.eq_of_beq_eq_true hEq
      have hHdNe : Nat.beq (view.allocId hd) otherId = false := by
        rw [hHd]
        exact hNe
      rw [tableReplace_cons_of_beq hEq, tableFind_cons_of_not_beq hNe,
        tableFind_cons_of_not_beq hHdNe]
    | false =>
      rw [tableReplace_cons_of_not_beq hEq]
      cases hOther : Nat.beq (view.allocId hd) otherId with
      | true =>
        rw [tableFind_cons_of_beq hOther, tableFind_cons_of_beq hOther]
      | false =>
        rw [tableFind_cons_of_not_beq hOther,
          tableFind_cons_of_not_beq hOther]
        exact ih

/-- Replacing twice at the same identifier keeps the second allocation. -/
theorem tableReplace_replace_same {view : AllocView A Byte}
    {allocs : List A} {a1 a2 : A}
    (hSame : view.allocId a2 = view.allocId a1) :
    tableReplace view a2 (tableReplace view a1 allocs) =
      tableReplace view a2 allocs := by
  induction allocs with
  | nil => rfl
  | cons hd rest ih =>
    cases hEq : Nat.beq (view.allocId hd) (view.allocId a1) with
    | true =>
      have hEq2 : Nat.beq (view.allocId hd) (view.allocId a2) = true := by
        rw [hSame]
        exact hEq
      have hSelf : Nat.beq (view.allocId a1) (view.allocId a2) = true := by
        rw [hSame]
        exact Nat.beq_refl (view.allocId a1)
      rw [tableReplace_cons_of_beq hEq, tableReplace_cons_of_beq hSelf,
        tableReplace_cons_of_beq hEq2]
    | false =>
      have hEq2 : Nat.beq (view.allocId hd) (view.allocId a2) = false := by
        rw [hSame]
        exact hEq
      rw [tableReplace_cons_of_not_beq hEq, tableReplace_cons_of_not_beq hEq2,
        tableReplace_cons_of_not_beq hEq2]
      exact congrArg (List.cons hd) ih

/-- Replacements at distinct identifiers commute. -/
theorem tableReplace_comm {view : AllocView A Byte} {allocs : List A}
    {a1 a2 : A}
    (hNe : Nat.beq (view.allocId a1) (view.allocId a2) = false) :
    tableReplace view a1 (tableReplace view a2 allocs) =
      tableReplace view a2 (tableReplace view a1 allocs) := by
  have hNe' : Nat.beq (view.allocId a2) (view.allocId a1) = false :=
    natBeq_false_symm hNe
  induction allocs with
  | nil => rfl
  | cons hd rest ih =>
    cases h1 : Nat.beq (view.allocId hd) (view.allocId a1) with
    | true =>
      have hHd : view.allocId hd = view.allocId a1 :=
        Nat.eq_of_beq_eq_true h1
      have h2 : Nat.beq (view.allocId hd) (view.allocId a2) = false := by
        rw [hHd]
        exact hNe
      rw [tableReplace_cons_of_not_beq h2, tableReplace_cons_of_beq h1,
        tableReplace_cons_of_beq h1, tableReplace_cons_of_not_beq hNe]
    | false =>
      cases h2 : Nat.beq (view.allocId hd) (view.allocId a2) with
      | true =>
        rw [tableReplace_cons_of_beq h2, tableReplace_cons_of_not_beq hNe',
          tableReplace_cons_of_not_beq h1, tableReplace_cons_of_beq h2]
      | false =>
        rw [tableReplace_cons_of_not_beq h2, tableReplace_cons_of_not_beq h1,
          tableReplace_cons_of_not_beq h1, tableReplace_cons_of_not_beq h2]
        exact congrArg (List.cons hd) ih

/-- Reads the slice `[off, off + len)` of the first allocation with
identifier `id`. Fails closed when there is no such allocation, when the
allocation is not `writable`, or when the slice is out of bounds. -/
def tableRead (view : AllocView A Byte) (allocs : List A) (id off len : Nat) :
    Option (List Byte) :=
  match tableFind view id allocs with
  | none => none
  | some a =>
    match view.writable a && Nat.ble (off + len) (view.bytes a).length with
    | true => some (((view.bytes a).drop off).take len)
    | false => none

/-- Overwrites the slice `[off, off + bs.length)` of the first allocation with
identifier `id` by `bs`. Fails closed under the same conditions as
`tableRead`. -/
def tableWrite (view : AllocView A Byte) (allocs : List A) (id off : Nat)
    (bs : List Byte) : Option (List A) :=
  match tableFind view id allocs with
  | none => none
  | some a =>
    match view.writable a &&
        Nat.ble (off + bs.length) (view.bytes a).length with
    | true =>
      some (tableReplace view
        (view.setBytes a (listSplice (view.bytes a) off bs)) allocs)
    | false => none

/-- A read of a found, writable allocation within bounds returns its slice. -/
theorem tableRead_of_find {view : AllocView A Byte} {allocs : List A}
    {id off len : Nat} {a : A} (hFind : tableFind view id allocs = some a)
    (hW : view.writable a = true)
    (hB : off + len ≤ (view.bytes a).length) :
    tableRead view allocs id off len =
      some (((view.bytes a).drop off).take len) := by
  unfold tableRead
  rw [hFind]
  change (match view.writable a &&
      Nat.ble (off + len) (view.bytes a).length with
    | true => some (((view.bytes a).drop off).take len)
    | false => none) = some (((view.bytes a).drop off).take len)
  rw [boolAnd_intro hW (Nat.ble_eq_true_of_le hB)]

/-- A write to a found, writable allocation within bounds replaces it. -/
theorem tableWrite_of_find {view : AllocView A Byte} {allocs : List A}
    {id off : Nat} {bs : List Byte} {a : A}
    (hFind : tableFind view id allocs = some a)
    (hW : view.writable a = true)
    (hB : off + bs.length ≤ (view.bytes a).length) :
    tableWrite view allocs id off bs =
      some (tableReplace view
        (view.setBytes a (listSplice (view.bytes a) off bs)) allocs) := by
  unfold tableWrite
  rw [hFind]
  change (match view.writable a &&
      Nat.ble (off + bs.length) (view.bytes a).length with
    | true =>
      some (tableReplace view
        (view.setBytes a (listSplice (view.bytes a) off bs)) allocs)
    | false => none) =
    some (tableReplace view
      (view.setBytes a (listSplice (view.bytes a) off bs)) allocs)
  rw [boolAnd_intro hW (Nat.ble_eq_true_of_le hB)]

/-- Inversion of a successful `tableRead`. -/
theorem tableRead_inv {view : AllocView A Byte} {allocs : List A}
    {id off len : Nat} {bs : List Byte}
    (h : tableRead view allocs id off len = some bs) :
    ∃ a, tableFind view id allocs = some a ∧ view.writable a = true ∧
      off + len ≤ (view.bytes a).length ∧
      bs = ((view.bytes a).drop off).take len := by
  unfold tableRead at h
  cases hFind : tableFind view id allocs with
  | none =>
    rw [hFind] at h
    cases h
  | some a =>
    rw [hFind] at h
    cases hGuard : (view.writable a &&
        Nat.ble (off + len) (view.bytes a).length) with
    | false =>
      have h' : (match view.writable a &&
          Nat.ble (off + len) (view.bytes a).length with
        | true => some (((view.bytes a).drop off).take len)
        | false => none) = some bs := h
      rw [hGuard] at h'
      cases h'
    | true =>
      have h' : (match view.writable a &&
          Nat.ble (off + len) (view.bytes a).length with
        | true => some (((view.bytes a).drop off).take len)
        | false => none) = some bs := h
      rw [hGuard] at h'
      exact ⟨a, rfl, boolAnd_left hGuard,
        Nat.le_of_ble_eq_true (boolAnd_right hGuard),
        (Option.some.inj h').symm⟩

/-- Inversion of a successful `tableWrite`. -/
theorem tableWrite_inv {view : AllocView A Byte} {allocs allocs' : List A}
    {id off : Nat} {bs : List Byte}
    (h : tableWrite view allocs id off bs = some allocs') :
    ∃ a, tableFind view id allocs = some a ∧ view.writable a = true ∧
      off + bs.length ≤ (view.bytes a).length ∧
      allocs' = tableReplace view
        (view.setBytes a (listSplice (view.bytes a) off bs)) allocs := by
  unfold tableWrite at h
  cases hFind : tableFind view id allocs with
  | none =>
    rw [hFind] at h
    cases h
  | some a =>
    rw [hFind] at h
    cases hGuard : (view.writable a &&
        Nat.ble (off + bs.length) (view.bytes a).length) with
    | false =>
      have h' : (match view.writable a &&
          Nat.ble (off + bs.length) (view.bytes a).length with
        | true =>
          some (tableReplace view
            (view.setBytes a (listSplice (view.bytes a) off bs)) allocs)
        | false => none) = some allocs' := h
      rw [hGuard] at h'
      cases h'
    | true =>
      have h' : (match view.writable a &&
          Nat.ble (off + bs.length) (view.bytes a).length with
        | true =>
          some (tableReplace view
            (view.setBytes a (listSplice (view.bytes a) off bs)) allocs)
        | false => none) = some allocs' := h
      rw [hGuard] at h'
      exact ⟨a, rfl, boolAnd_left hGuard,
        Nat.le_of_ble_eq_true (boolAnd_right hGuard),
        (Option.some.inj h').symm⟩

/-- A read of a missing allocation fails closed. -/
theorem tableRead_none_of_missing {view : AllocView A Byte}
    {allocs : List A} {id : Nat} (off len : Nat)
    (hFind : tableFind view id allocs = none) :
    tableRead view allocs id off len = none := by
  unfold tableRead
  rw [hFind]

/-- A write to a missing allocation fails closed. -/
theorem tableWrite_none_of_missing {view : AllocView A Byte}
    {allocs : List A} {id : Nat} (off : Nat) (bs : List Byte)
    (hFind : tableFind view id allocs = none) :
    tableWrite view allocs id off bs = none := by
  unfold tableWrite
  rw [hFind]

/-- A read of an allocation that is not `writable` fails closed. -/
theorem tableRead_none_of_not_writable {view : AllocView A Byte}
    {allocs : List A} {id : Nat} {a : A} (off len : Nat)
    (hFind : tableFind view id allocs = some a)
    (hW : view.writable a = false) :
    tableRead view allocs id off len = none := by
  cases hRead : tableRead view allocs id off len with
  | none => rfl
  | some bs =>
    let ⟨a', hFind', hW', _, _⟩ := tableRead_inv hRead
    rw [hFind] at hFind'
    have hEq : a = a' := Option.some.inj hFind'
    rw [hEq, hW'] at hW
    cases hW

/-- A write to an allocation that is not `writable` fails closed. -/
theorem tableWrite_none_of_not_writable {view : AllocView A Byte}
    {allocs : List A} {id : Nat} {a : A} (off : Nat) (bs : List Byte)
    (hFind : tableFind view id allocs = some a)
    (hW : view.writable a = false) :
    tableWrite view allocs id off bs = none := by
  cases hWrite : tableWrite view allocs id off bs with
  | none => rfl
  | some allocs' =>
    let ⟨a', hFind', hW', _, _⟩ := tableWrite_inv hWrite
    rw [hFind] at hFind'
    have hEq : a = a' := Option.some.inj hFind'
    rw [hEq, hW'] at hW
    cases hW

/-- An out-of-bounds read fails closed. -/
theorem tableRead_none_of_out_of_bounds {view : AllocView A Byte}
    {allocs : List A} {id off len : Nat} {a : A}
    (hFind : tableFind view id allocs = some a)
    (hOob : (view.bytes a).length < off + len) :
    tableRead view allocs id off len = none := by
  cases hRead : tableRead view allocs id off len with
  | none => rfl
  | some bs =>
    let ⟨a', hFind', _, hB, _⟩ := tableRead_inv hRead
    rw [hFind] at hFind'
    have hEq : a = a' := Option.some.inj hFind'
    rw [← hEq] at hB
    exact False.elim (Nat.not_le_of_gt hOob hB)

/-- An out-of-bounds write fails closed. -/
theorem tableWrite_none_of_out_of_bounds {view : AllocView A Byte}
    {allocs : List A} {id off : Nat} {bs : List Byte} {a : A}
    (hFind : tableFind view id allocs = some a)
    (hOob : (view.bytes a).length < off + bs.length) :
    tableWrite view allocs id off bs = none := by
  cases hWrite : tableWrite view allocs id off bs with
  | none => rfl
  | some allocs' =>
    let ⟨a', hFind', _, hB, _⟩ := tableWrite_inv hWrite
    rw [hFind] at hFind'
    have hEq : a = a' := Option.some.inj hFind'
    rw [← hEq] at hB
    exact False.elim (Nat.not_le_of_gt hOob hB)

/-- A successful read returns exactly `len` bytes. -/
theorem tableRead_len {view : AllocView A Byte} {allocs : List A}
    {id off len : Nat} {bs : List Byte}
    (h : tableRead view allocs id off len = some bs) : bs.length = len := by
  let ⟨a, _, _, hB, hBs⟩ := tableRead_inv h
  rw [hBs]
  exact listSlice_length (view.bytes a) off len hB

/-- Reading a sub-range of a successful read returns the sub-slice. -/
theorem tableRead_sub {view : AllocView A Byte} {allocs : List A}
    {id off len rel k : Nat} {bs : List Byte}
    (h : tableRead view allocs id off len = some bs) (hSub : rel + k ≤ len) :
    tableRead view allocs id (off + rel) k = some ((bs.drop rel).take k) := by
  let ⟨a, hFind, hW, hB, hBs⟩ := tableRead_inv h
  have hB' : off + rel + k ≤ (view.bytes a).length := by
    rw [Nat.add_assoc]
    exact Nat.le_trans (Nat.add_le_add_left hSub off) hB
  rw [tableRead_of_find hFind hW hB', hBs,
    listSlice_slice (view.bytes a) off len rel k hSub]

/-- A slice that can be read can be overwritten with any bytes of its
length. -/
theorem tableWrite_isSome_of_read {view : AllocView A Byte}
    {allocs : List A} {id off len : Nat} {old : List Byte} (bs : List Byte)
    (h : tableRead view allocs id off len = some old)
    (hLen : bs.length = len) :
    ∃ allocs', tableWrite view allocs id off bs = some allocs' := by
  let ⟨a, hFind, hW, hB, _⟩ := tableRead_inv h
  have hB' : off + bs.length ≤ (view.bytes a).length := by
    rw [hLen]
    exact hB
  exact ⟨_, tableWrite_of_find hFind hW hB'⟩

/-- Read-after-write: a successful write is read back unchanged. -/
theorem tableRead_tableWrite_same {view : AllocView A Byte}
    (hV : view.Lawful) {allocs allocs' : List A} {id off : Nat}
    {bs : List Byte} (h : tableWrite view allocs id off bs = some allocs') :
    tableRead view allocs' id off bs.length = some bs := by
  let ⟨a, hFind, hW, hB, hAllocs⟩ := tableWrite_inv h
  have hId : view.allocId a = id := tableFind_allocId hFind
  have hFindA : tableFind view (view.allocId a) allocs = some a := by
    rw [hId]
    exact hFind
  have hFind' : tableFind view id allocs' =
      some (view.setBytes a (listSplice (view.bytes a) off bs)) := by
    rw [hAllocs, ← hId]
    exact tableFind_replace_same hFindA (hV.allocId_setBytes a _)
  have hW' : view.writable
      (view.setBytes a (listSplice (view.bytes a) off bs)) = true := by
    rw [hV.writable_setBytes]
    exact hW
  have hB' : off + bs.length ≤ (view.bytes
      (view.setBytes a (listSplice (view.bytes a) off bs))).length := by
    rw [hV.bytes_setBytes, listSplice_length (view.bytes a) off bs hB]
    exact hB
  rw [tableRead_of_find hFind' hW' hB', hV.bytes_setBytes,
    listSplice_read_same (view.bytes a) off bs hB]

/-- Write-after-read: writing back what was read leaves the table unchanged.
No uniqueness of identifiers is needed. -/
theorem tableWrite_tableRead_same {view : AllocView A Byte}
    (hV : view.Lawful) {allocs : List A} {id off len : Nat} {bs : List Byte}
    (h : tableRead view allocs id off len = some bs) :
    tableWrite view allocs id off bs = some allocs := by
  let ⟨a, hFind, hW, hB, hBs⟩ := tableRead_inv h
  have hLen : bs.length = len := tableRead_len h
  have hB' : off + bs.length ≤ (view.bytes a).length := by
    rw [hLen]
    exact hB
  rw [tableWrite_of_find hFind hW hB', hBs,
    listSplice_self (view.bytes a) off len hB, hV.setBytes_bytes,
    tableReplace_self hFind]

/-- Write-after-write: a second write of the same length at the same place
overwrites the first. -/
theorem tableWrite_tableWrite_same {view : AllocView A Byte}
    (hV : view.Lawful) {allocs allocs₁ : List A} {id off : Nat}
    {bs₁ bs₂ : List Byte}
    (h : tableWrite view allocs id off bs₁ = some allocs₁)
    (hLen : bs₂.length = bs₁.length) :
    tableWrite view allocs₁ id off bs₂ = tableWrite view allocs id off bs₂ := by
  let ⟨a, hFind, hW, hB, hAllocs⟩ := tableWrite_inv h
  have hId : view.allocId a = id := tableFind_allocId hFind
  have hFindA : tableFind view (view.allocId a) allocs = some a := by
    rw [hId]
    exact hFind
  have hFind₁ : tableFind view id allocs₁ =
      some (view.setBytes a (listSplice (view.bytes a) off bs₁)) := by
    rw [hAllocs, ← hId]
    exact tableFind_replace_same hFindA (hV.allocId_setBytes a _)
  have hW₁ : view.writable
      (view.setBytes a (listSplice (view.bytes a) off bs₁)) = true := by
    rw [hV.writable_setBytes]
    exact hW
  have hB₂ : off + bs₂.length ≤ (view.bytes a).length := by
    rw [hLen]
    exact hB
  have hB₁' : off + bs₂.length ≤ (view.bytes
      (view.setBytes a (listSplice (view.bytes a) off bs₁))).length := by
    rw [hV.bytes_setBytes, listSplice_length (view.bytes a) off bs₁ hB]
    exact hB₂
  have hSameId : view.allocId
      (view.setBytes a (listSplice (view.bytes a) off bs₂)) =
      view.allocId (view.setBytes a (listSplice (view.bytes a) off bs₁)) := by
    rw [hV.allocId_setBytes, hV.allocId_setBytes]
  rw [tableWrite_of_find hFind₁ hW₁ hB₁', tableWrite_of_find hFind hW hB₂,
    hV.bytes_setBytes, hV.setBytes_setBytes,
    listSplice_overwrite (view.bytes a) off bs₁ bs₂ hB hLen, hAllocs,
    tableReplace_replace_same hSameId]

/-- Frame law: a write leaves every separated slice unchanged. Two slices are
separated when they live in allocations with different identifiers or their
ranges do not overlap. -/
theorem tableRead_tableWrite_disjoint {view : AllocView A Byte}
    (hV : view.Lawful) {allocs allocs' : List A} {id off : Nat}
    {bs : List Byte} {id' off' len' : Nat}
    (hSep : id ≠ id' ∨ off + bs.length ≤ off' ∨ off' + len' ≤ off)
    (h : tableWrite view allocs id off bs = some allocs') :
    tableRead view allocs' id' off' len' =
      tableRead view allocs id' off' len' := by
  let ⟨a, hFind, hW, hB, hAllocs⟩ := tableWrite_inv h
  have hId : view.allocId a = id := tableFind_allocId hFind
  cases Nat.decEq id id' with
  | isFalse hNe =>
    have hBeq : Nat.beq (view.allocId
        (view.setBytes a (listSplice (view.bytes a) off bs))) id' = false := by
      rw [hV.allocId_setBytes, hId]
      exact natBeq_false_of_not_eq hNe
    unfold tableRead
    rw [hAllocs, tableFind_replace_ne hBeq]
  | isTrue hEq =>
    have hRanges : off + bs.length ≤ off' ∨ off' + len' ≤ off := by
      cases hSep with
      | inl hNe => exact False.elim (hNe hEq)
      | inr hR => exact hR
    have hFindA : tableFind view (view.allocId a) allocs = some a := by
      rw [hId]
      exact hFind
    have hFind' : tableFind view id' allocs' =
        some (view.setBytes a (listSplice (view.bytes a) off bs)) := by
      rw [hAllocs, ← hEq, ← hId]
      exact tableFind_replace_same hFindA (hV.allocId_setBytes a _)
    have hFindOld : tableFind view id' allocs = some a := by
      rw [← hEq]
      exact hFind
    unfold tableRead
    rw [hFind', hFindOld]
    change (match view.writable
          (view.setBytes a (listSplice (view.bytes a) off bs)) &&
        Nat.ble (off' + len') (view.bytes
          (view.setBytes a (listSplice (view.bytes a) off bs))).length with
      | true => some (((view.bytes
          (view.setBytes a (listSplice (view.bytes a) off bs))).drop
            off').take len')
      | false => none) =
      (match view.writable a &&
        Nat.ble (off' + len') (view.bytes a).length with
      | true => some (((view.bytes a).drop off').take len')
      | false => none)
    rw [hV.writable_setBytes, hV.bytes_setBytes,
      listSplice_length (view.bytes a) off bs hB,
      listSplice_read_disjoint (view.bytes a) off bs off' len' hB hRanges]

/-- Writes to separated slices commute: each succeeds after the other, and
both orders give the same table. -/
theorem tableWrite_tableWrite_comm {view : AllocView A Byte}
    (hV : view.Lawful) {allocs allocs₁ allocs₂ : List A} {id off : Nat}
    {bs : List Byte} {id' off' : Nat} {bs' : List Byte}
    (hSep : id ≠ id' ∨ off + bs.length ≤ off' ∨ off' + bs'.length ≤ off)
    (h₁ : tableWrite view allocs id off bs = some allocs₁)
    (h₂ : tableWrite view allocs id' off' bs' = some allocs₂) :
    ∃ allocs₃, tableWrite view allocs₁ id' off' bs' = some allocs₃ ∧
      tableWrite view allocs₂ id off bs = some allocs₃ := by
  let ⟨a, hFind, hW, hB, hAllocs₁⟩ := tableWrite_inv h₁
  let ⟨a', hFind', hW', hB', hAllocs₂⟩ := tableWrite_inv h₂
  have hId : view.allocId a = id := tableFind_allocId hFind
  have hId' : view.allocId a' = id' := tableFind_allocId hFind'
  cases Nat.decEq id id' with
  | isFalse hNe =>
    have hBeq : Nat.beq (view.allocId
        (view.setBytes a (listSplice (view.bytes a) off bs))) id' = false := by
      rw [hV.allocId_setBytes, hId]
      exact natBeq_false_of_not_eq hNe
    have hBeq' : Nat.beq (view.allocId
        (view.setBytes a' (listSplice (view.bytes a') off' bs'))) id =
        false := by
      rw [hV.allocId_setBytes, hId']
      exact natBeq_false_of_not_eq (fun hEq => hNe hEq.symm)
    have hFind₁ : tableFind view id' allocs₁ = some a' := by
      rw [hAllocs₁, tableFind_replace_ne hBeq]
      exact hFind'
    have hFind₂ : tableFind view id allocs₂ = some a := by
      rw [hAllocs₂, tableFind_replace_ne hBeq']
      exact hFind
    have hNeNew : Nat.beq
        (view.allocId
          (view.setBytes a' (listSplice (view.bytes a') off' bs')))
        (view.allocId (view.setBytes a (listSplice (view.bytes a) off bs))) =
        false := by
      rw [hV.allocId_setBytes, hV.allocId_setBytes, hId, hId']
      exact natBeq_false_of_not_eq (fun hEq => hNe hEq.symm)
    refine ⟨tableReplace view
      (view.setBytes a' (listSplice (view.bytes a') off' bs')) allocs₁,
      tableWrite_of_find hFind₁ hW' hB', ?_⟩
    rw [tableWrite_of_find hFind₂ hW hB, hAllocs₁, hAllocs₂,
      tableReplace_comm hNeNew]
  | isTrue hEq =>
    have hRanges : off + bs.length ≤ off' ∨ off' + bs'.length ≤ off := by
      cases hSep with
      | inl hNe => exact False.elim (hNe hEq)
      | inr hR => exact hR
    have hSame : a' = a := by
      rw [← hEq, hFind] at hFind'
      exact (Option.some.inj hFind').symm
    rw [hSame] at hB' hAllocs₂
    have hFindA : tableFind view (view.allocId a) allocs = some a := by
      rw [hId]
      exact hFind
    have hFind₁ : tableFind view id' allocs₁ =
        some (view.setBytes a (listSplice (view.bytes a) off bs)) := by
      rw [hAllocs₁, ← hEq, ← hId]
      exact tableFind_replace_same hFindA (hV.allocId_setBytes a _)
    have hFind₂ : tableFind view id allocs₂ =
        some (view.setBytes a (listSplice (view.bytes a) off' bs')) := by
      rw [hAllocs₂, ← hId]
      exact tableFind_replace_same hFindA (hV.allocId_setBytes a _)
    have hW₁ : view.writable
        (view.setBytes a (listSplice (view.bytes a) off bs)) = true := by
      rw [hV.writable_setBytes]
      exact hW
    have hW₂ : view.writable
        (view.setBytes a (listSplice (view.bytes a) off' bs')) = true := by
      rw [hV.writable_setBytes]
      exact hW
    have hB₁ : off' + bs'.length ≤ (view.bytes
        (view.setBytes a (listSplice (view.bytes a) off bs))).length := by
      rw [hV.bytes_setBytes, listSplice_length (view.bytes a) off bs hB]
      exact hB'
    have hB₂ : off + bs.length ≤ (view.bytes
        (view.setBytes a (listSplice (view.bytes a) off' bs'))).length := by
      rw [hV.bytes_setBytes, listSplice_length (view.bytes a) off' bs' hB']
      exact hB
    have hSameId₁ : view.allocId
        (view.setBytes a
          (listSplice (listSplice (view.bytes a) off bs) off' bs')) =
        view.allocId (view.setBytes a (listSplice (view.bytes a) off bs)) := by
      rw [hV.allocId_setBytes, hV.allocId_setBytes]
    have hSameId₂ : view.allocId
        (view.setBytes a
          (listSplice (listSplice (view.bytes a) off' bs') off bs)) =
        view.allocId
          (view.setBytes a (listSplice (view.bytes a) off' bs')) := by
      rw [hV.allocId_setBytes, hV.allocId_setBytes]
    have hComm : listSplice (listSplice (view.bytes a) off bs) off' bs' =
        listSplice (listSplice (view.bytes a) off' bs') off bs := by
      cases hRanges with
      | inl hLeft =>
        exact listSplice_comm (view.bytes a) off bs off' bs' hLeft
          (Nat.le_trans (Nat.le_add_right off' bs'.length) hB')
      | inr hRight =>
        exact (listSplice_comm (view.bytes a) off' bs' off bs hRight
          (Nat.le_trans (Nat.le_add_right off bs.length) hB)).symm
    refine ⟨tableReplace view
      (view.setBytes a
        (listSplice (listSplice (view.bytes a) off bs) off' bs')) allocs,
      ?_, ?_⟩
    · rw [tableWrite_of_find hFind₁ hW₁ hB₁, hV.bytes_setBytes,
        hV.setBytes_setBytes, hAllocs₁, tableReplace_replace_same hSameId₁]
    · rw [tableWrite_of_find hFind₂ hW₂ hB₂, hV.bytes_setBytes,
        hV.setBytes_setBytes, hAllocs₂, tableReplace_replace_same hSameId₂,
        hComm]

end Table

/-! ## Part III: The Byte-Store Interface (`ByteStoreOps`) -/

/-- Byte-slice store interface over a memory `Mem` addressed by `Addr`.

`Byte` is the type of one stored byte slot: raw `UInt8`, `Option UInt8` for
possibly uninitialized bytes, a provenance-carrying abstract byte, and so on.
`readBytes? m a off len` reads the slice `[off, off + len)` of the object at
`a`, `writeBytes? m a off bs` overwrites the slice `[off, off + bs.length)`,
and both fail closed with `none`. `addrDisjoint a off len a' off' len'` states
that two slices do not interfere.

A read through this interface is the read side of a byte lens, so it is
expected to succeed exactly where a write of the same slice would: an object
that cannot be written (dead, immutable) is not readable through it either
(`LawfulByteStoreOps.write_read_same`). -/
class ByteStoreOps (Mem : Type u) (Addr : Type v) where
  /-- One stored byte slot. -/
  Byte : Type w
  /-- Reads `len` bytes at offset `off` of the object at `a`. -/
  readBytes? : Mem → Addr → Nat → Nat → Option (List Byte)
  /-- Overwrites `bs.length` bytes at offset `off` of the object at `a`. -/
  writeBytes? : Mem → Addr → Nat → List Byte → Option Mem
  /-- The slices `(a, off, len)` and `(a', off', len')` do not interfere. -/
  addrDisjoint : Addr → Nat → Nat → Addr → Nat → Nat → Prop

/-- Laws of a byte store: every slice is a lawful lens, writes frame and
commute across non-interfering slices, and geometrically separated slices do
not interfere. -/
class LawfulByteStoreOps (Mem : Type u) (Addr : Type v)
    [ops : ByteStoreOps.{u, v, w} Mem Addr] : Prop where
  /-- A successful read returns exactly `len` bytes. -/
  read_len : ∀ {m : Mem} {a : Addr} {off len : Nat} {bs : List ops.Byte},
    ops.readBytes? m a off len = some bs → bs.length = len
  /-- A sub-range of a successful read reads the corresponding sub-slice. -/
  read_sub : ∀ {m : Mem} {a : Addr} {off len rel k : Nat}
    {bs : List ops.Byte},
    ops.readBytes? m a off len = some bs → rel + k ≤ len →
    ops.readBytes? m a (off + rel) k = some ((bs.drop rel).take k)
  /-- Read-after-write returns the written bytes. -/
  read_write_same : ∀ {m m' : Mem} {a : Addr} {off : Nat}
    {bs : List ops.Byte},
    ops.writeBytes? m a off bs = some m' →
    ops.readBytes? m' a off bs.length = some bs
  /-- Write-after-read of the same bytes leaves the memory unchanged. -/
  write_read_same : ∀ {m : Mem} {a : Addr} {off len : Nat}
    {bs : List ops.Byte},
    ops.readBytes? m a off len = some bs →
    ops.writeBytes? m a off bs = some m
  /-- A slice that can be read can be overwritten with any bytes of its
  length: whether a write succeeds depends on the slice, not on the bytes. -/
  write_of_read : ∀ {m : Mem} {a : Addr} {off len : Nat}
    {old : List ops.Byte} (bs : List ops.Byte),
    ops.readBytes? m a off len = some old → bs.length = len →
    ∃ m', ops.writeBytes? m a off bs = some m'
  /-- A second write of the same length at the same place overwrites the
  first. -/
  write_write_same : ∀ {m m₁ : Mem} {a : Addr} {off : Nat}
    {bs₁ bs₂ : List ops.Byte},
    ops.writeBytes? m a off bs₁ = some m₁ → bs₂.length = bs₁.length →
    ops.writeBytes? m₁ a off bs₂ = ops.writeBytes? m a off bs₂
  /-- A write leaves every non-interfering slice unchanged. -/
  read_write_disjoint : ∀ {m m' : Mem} {a : Addr} {off : Nat}
    {bs : List ops.Byte} {a' : Addr} {off' len' : Nat},
    ops.addrDisjoint a off bs.length a' off' len' →
    ops.writeBytes? m a off bs = some m' →
    ops.readBytes? m' a' off' len' = ops.readBytes? m a' off' len'
  /-- Writes to non-interfering slices commute. -/
  write_write_comm : ∀ {m m₁ m₂ : Mem} {a : Addr} {off : Nat}
    {bs : List ops.Byte} {a' : Addr} {off' : Nat} {bs' : List ops.Byte},
    ops.addrDisjoint a off bs.length a' off' bs'.length →
    ops.writeBytes? m a off bs = some m₁ →
    ops.writeBytes? m a' off' bs' = some m₂ →
    ∃ m₃, ops.writeBytes? m₁ a' off' bs' = some m₃ ∧
      ops.writeBytes? m₂ a off bs = some m₃
  /-- Slices at different addresses, or with non-overlapping ranges, do not
  interfere. -/
  addrDisjoint_of_separated : ∀ {a a' : Addr} {off len off' len' : Nat},
    (a ≠ a' ∨ off + len ≤ off' ∨ off' + len' ≤ off) →
    ops.addrDisjoint a off len a' off' len'

/-- Byte store of any memory type that holds a first-match allocation table:
`getTable` and `setTable` read and replace the table, and addresses are
allocation identifiers. -/
@[reducible] def ByteStoreOps.ofTable {Mem : Type u} {A : Type x}
    {Byte : Type w} (view : AllocView A Byte) (getTable : Mem → List A)
    (setTable : Mem → List A → Mem) : ByteStoreOps.{u, 0, w} Mem Nat where
  Byte := Byte
  readBytes? m id off len := tableRead view (getTable m) id off len
  writeBytes? m id off bs :=
    match tableWrite view (getTable m) id off bs with
    | none => none
    | some t => some (setTable m t)
  addrDisjoint id off len id' off' len' :=
    id ≠ id' ∨ off + len ≤ off' ∨ off' + len' ≤ off

section OfTable

variable {Mem : Type u} {A : Type x} {Byte : Type w}
  {view : AllocView A Byte} {getTable : Mem → List A}
  {setTable : Mem → List A → Mem}

/-- Inversion of a successful write of `ByteStoreOps.ofTable`. -/
theorem ofTable_write_inv {m m' : Mem} {id off : Nat} {bs : List Byte}
    (h : (ByteStoreOps.ofTable view getTable setTable).writeBytes? m id off
      bs = some m') :
    ∃ t, tableWrite view (getTable m) id off bs = some t ∧
      m' = setTable m t := by
  have h' : (match tableWrite view (getTable m) id off bs with
    | none => none
    | some t => some (setTable m t)) = some m' := h
  cases hW : tableWrite view (getTable m) id off bs with
  | none =>
    rw [hW] at h'
    cases h'
  | some t =>
    rw [hW] at h'
    exact ⟨t, rfl, (Option.some.inj h').symm⟩

/-- A successful table write is a successful write of
`ByteStoreOps.ofTable`. -/
theorem ofTable_write_of {m : Mem} {id off : Nat} {bs : List Byte}
    {t : List A} (h : tableWrite view (getTable m) id off bs = some t) :
    (ByteStoreOps.ofTable view getTable setTable).writeBytes? m id off bs =
      some (setTable m t) := by
  change (match tableWrite view (getTable m) id off bs with
    | none => none
    | some t => some (setTable m t)) = some (setTable m t)
  rw [h]

end OfTable

/-- `ByteStoreOps.ofTable` is lawful for every lawful allocation view and
every lawful table lens `getTable` / `setTable`. Allocation identifiers need
not be unique. -/
theorem LawfulByteStoreOps.ofTable {Mem : Type u} {A : Type x}
    {Byte : Type w} {view : AllocView A Byte} (hV : view.Lawful)
    {getTable : Mem → List A} {setTable : Mem → List A → Mem}
    (hGetSet : ∀ (m : Mem) (t : List A), getTable (setTable m t) = t)
    (hSetGet : ∀ (m : Mem), setTable m (getTable m) = m)
    (hSetSet : ∀ (m : Mem) (t₁ t₂ : List A),
      setTable (setTable m t₁) t₂ = setTable m t₂) :
    @LawfulByteStoreOps Mem Nat
      (ByteStoreOps.ofTable view getTable setTable) := by
  refine @LawfulByteStoreOps.mk Mem Nat
    (ByteStoreOps.ofTable view getTable setTable) ?read_len ?read_sub
    ?read_write_same ?write_read_same ?write_of_read ?write_write_same
    ?read_write_disjoint ?write_write_comm ?addrDisjoint_of_separated
  case read_len =>
    intro m a off len bs h
    exact tableRead_len h
  case read_sub =>
    intro m a off len rel k bs h hSub
    exact tableRead_sub h hSub
  case read_write_same =>
    intro m m' a off bs h
    let ⟨t, hT, hM⟩ := ofTable_write_inv h
    rw [hM]
    change tableRead view (getTable (setTable m t)) a off bs.length = some bs
    rw [hGetSet]
    exact tableRead_tableWrite_same hV hT
  case write_read_same =>
    intro m a off len bs h
    exact (ofTable_write_of (tableWrite_tableRead_same hV h)).trans
      (congrArg some (hSetGet m))
  case write_of_read =>
    intro m a off len old bs h hLen
    let ⟨t, hT⟩ := tableWrite_isSome_of_read bs h hLen
    exact ⟨setTable m t, ofTable_write_of hT⟩
  case write_write_same =>
    intro m m₁ a off bs₁ bs₂ h hLen
    let ⟨t₁, hT₁, hM₁⟩ := ofTable_write_inv h
    rw [hM₁]
    change (match tableWrite view (getTable (setTable m t₁)) a off bs₂ with
      | none => none
      | some t => some (setTable (setTable m t₁) t)) =
      (match tableWrite view (getTable m) a off bs₂ with
      | none => none
      | some t => some (setTable m t))
    rw [hGetSet, tableWrite_tableWrite_same hV hT₁ hLen]
    cases tableWrite view (getTable m) a off bs₂ with
    | none => rfl
    | some t => exact congrArg some (hSetSet m t₁ t)
  case read_write_disjoint =>
    intro m m' a off bs a' off' len' hDisj h
    let ⟨t, hT, hM⟩ := ofTable_write_inv h
    rw [hM]
    change tableRead view (getTable (setTable m t)) a' off' len' =
      tableRead view (getTable m) a' off' len'
    rw [hGetSet]
    exact tableRead_tableWrite_disjoint hV hDisj hT
  case write_write_comm =>
    intro m m₁ m₂ a off bs a' off' bs' hDisj h₁ h₂
    let ⟨t₁, hT₁, hM₁⟩ := ofTable_write_inv h₁
    let ⟨t₂, hT₂, hM₂⟩ := ofTable_write_inv h₂
    let ⟨t₃, hA, hB⟩ := tableWrite_tableWrite_comm hV hDisj hT₁ hT₂
    refine ⟨setTable m t₃, ?_, ?_⟩
    · rw [hM₁]
      have hA' : tableWrite view (getTable (setTable m t₁)) a' off' bs' =
          some t₃ := by
        rw [hGetSet]
        exact hA
      exact (ofTable_write_of hA').trans (congrArg some (hSetSet m t₁ t₃))
    · rw [hM₂]
      have hB' : tableWrite view (getTable (setTable m t₂)) a off bs =
          some t₃ := by
        rw [hGetSet]
        exact hB
      exact (ofTable_write_of hB').trans (congrArg some (hSetSet m t₂ t₃))
  case addrDisjoint_of_separated =>
    intro a a' off len off' len' h
    exact h

/-- Allocation record of the canonical store: an identifier, a byte buffer and
an access guard. -/
structure SliceAlloc (Byte : Type u) where
  /-- Identifier of the allocation. -/
  allocId : Nat
  /-- Contents of the allocation. -/
  bytes : List Byte
  /-- Whether a byte lens may access the allocation. -/
  writable : Bool

/-- `AllocView` of `SliceAlloc`. -/
def SliceAlloc.view (Byte : Type u) : AllocView (SliceAlloc Byte) Byte where
  allocId := SliceAlloc.allocId
  bytes := SliceAlloc.bytes
  setBytes := fun a bs =>
    { allocId := a.allocId, bytes := bs, writable := a.writable }
  writable := SliceAlloc.writable

/-- The `SliceAlloc` view is lawful. -/
theorem SliceAlloc.view_lawful (Byte : Type u) :
    (SliceAlloc.view Byte).Lawful where
  allocId_setBytes := fun _ _ => rfl
  bytes_setBytes := fun _ _ => rfl
  writable_setBytes := fun _ _ => rfl
  setBytes_bytes := fun a => by
    cases a
    rfl
  setBytes_setBytes := fun _ _ _ => rfl

/-- Canonical concrete byte store: a list of `SliceAlloc` records looked up by
first match. Identifiers need not be unique. -/
structure SliceStore (Byte : Type u) where
  /-- Allocation table. -/
  allocs : List (SliceAlloc Byte)

/-- Byte-store interface of `SliceStore`, addressed by allocation
identifier. -/
instance SliceStore.instByteStoreOps (Byte : Type u) :
    ByteStoreOps (SliceStore Byte) Nat :=
  ByteStoreOps.ofTable (SliceAlloc.view Byte) SliceStore.allocs
    (fun _ t => { allocs := t })

/-- `SliceStore` satisfies every byte-store law unconditionally. -/
instance SliceStore.instLawfulByteStoreOps (Byte : Type u) :
    LawfulByteStoreOps (SliceStore Byte) Nat :=
  LawfulByteStoreOps.ofTable (SliceAlloc.view_lawful Byte)
    (fun _ _ => rfl)
    (fun m => by
      cases m
      rfl)
    (fun _ _ _ => rfl)

/-! ## Part IV: Byte Sub-Lenses (`ByteSubLens`) -/

/-- Byte sub-lens: the slice `[offset, offset + len)` of the object at
`addr`. -/
structure ByteSubLens (Addr : Type v) where
  /-- Object that holds the slice. -/
  addr : Addr
  /-- Offset of the slice within the object. -/
  offset : Nat
  /-- Length of the slice in bytes. -/
  len : Nat

namespace ByteSubLens

variable {Mem : Type u} {Addr : Type v}

/-- Footprint of a lens: its object, offset and length. -/
def footprint (L : ByteSubLens Addr) : Addr × Nat × Nat :=
  (L.addr, L.offset, L.len)

/-- Reads the slice of a lens. Fails closed on a zero-length lens and whenever
the store rejects the read. -/
def get [ops : ByteStoreOps.{u, v, w} Mem Addr] (L : ByteSubLens Addr)
    (m : Mem) : Option (List ops.Byte) :=
  match Nat.blt 0 L.len with
  | false => none
  | true => ops.readBytes? m L.addr L.offset L.len

/-- Overwrites the slice of a lens with `bs`. Fails closed on a zero-length
lens, when `bs` does not have the length of the lens, and whenever the store
rejects the write. -/
def set [ops : ByteStoreOps.{u, v, w} Mem Addr] (L : ByteSubLens Addr)
    (m : Mem) (bs : List ops.Byte) : Option Mem :=
  match Nat.blt 0 L.len && Nat.beq bs.length L.len with
  | false => none
  | true => ops.writeBytes? m L.addr L.offset bs

/-- Store-level non-interference of two lenses over the memory `Mem`. -/
def Disjoint (Mem : Type u) [ops : ByteStoreOps.{u, v, w} Mem Addr]
    (L₁ L₂ : ByteSubLens Addr) : Prop :=
  ops.addrDisjoint L₁.addr L₁.offset L₁.len L₂.addr L₂.offset L₂.len

/-- Geometric separation of two lenses: different objects, or non-overlapping
ranges. -/
def Separated (L₁ L₂ : ByteSubLens Addr) : Prop :=
  L₁.addr ≠ L₂.addr ∨ L₁.offset + L₁.len ≤ L₂.offset ∨
    L₂.offset + L₂.len ≤ L₁.offset

/-- Hierarchical containment `child ⊆ parent`: same object, and the range of
`child` lies within the range of `parent`. -/
def ContainedIn (child parent : ByteSubLens Addr) : Prop :=
  child.addr = parent.addr ∧ parent.offset ≤ child.offset ∧
    child.offset + child.len ≤ parent.offset + parent.len

/-- Sub-lens of `L` that starts `rel` bytes into it and has length `k`. -/
def zoom (L : ByteSubLens Addr) (rel k : Nat) : ByteSubLens Addr :=
  { addr := L.addr, offset := L.offset + rel, len := k }

section Ops

variable [ops : ByteStoreOps.{u, v, w} Mem Addr]

/-- Inversion of a successful `get`. -/
theorem get_inv {L : ByteSubLens Addr} {m : Mem} {bs : List ops.Byte}
    (h : L.get m = some bs) :
    0 < L.len ∧ ops.readBytes? m L.addr L.offset L.len = some bs := by
  unfold get at h
  cases hPos : Nat.blt 0 L.len with
  | false =>
    rw [hPos] at h
    cases h
  | true =>
    rw [hPos] at h
    exact ⟨Nat.le_of_ble_eq_true hPos, h⟩

/-- `get` of a positive-length lens is the store read. -/
theorem get_of_pos {L : ByteSubLens Addr} (m : Mem) (hPos : 0 < L.len) :
    L.get m = ops.readBytes? m L.addr L.offset L.len := by
  have hBlt : Nat.blt 0 L.len = true := Nat.ble_eq_true_of_le hPos
  unfold get
  rw [hBlt]

/-- Inversion of a successful `set`. -/
theorem set_inv {L : ByteSubLens Addr} {m m' : Mem} {bs : List ops.Byte}
    (h : L.set m bs = some m') :
    0 < L.len ∧ bs.length = L.len ∧
      ops.writeBytes? m L.addr L.offset bs = some m' := by
  unfold set at h
  cases hGuard : (Nat.blt 0 L.len && Nat.beq bs.length L.len) with
  | false =>
    rw [hGuard] at h
    cases h
  | true =>
    rw [hGuard] at h
    exact ⟨Nat.le_of_ble_eq_true (boolAnd_left hGuard),
      Nat.eq_of_beq_eq_true (boolAnd_right hGuard), h⟩

/-- `set` of a positive-length lens with bytes of the right length is the
store write. -/
theorem set_of_pos {L : ByteSubLens Addr} (m : Mem) {bs : List ops.Byte}
    (hPos : 0 < L.len) (hLen : bs.length = L.len) :
    L.set m bs = ops.writeBytes? m L.addr L.offset bs := by
  have hGuard : (Nat.blt 0 L.len && Nat.beq bs.length L.len) = true := by
    refine boolAnd_intro (Nat.ble_eq_true_of_le hPos) ?_
    rw [hLen]
    exact Nat.beq_refl L.len
  unfold set
  rw [hGuard]

/-- A zero-length lens rejects every read. -/
theorem get_none_of_len_zero {L : ByteSubLens Addr} (m : Mem)
    (hZero : L.len = 0) : (L.get m : Option (List ops.Byte)) = none := by
  unfold get
  rw [hZero]
  rfl

/-- A zero-length lens rejects every write. -/
theorem set_none_of_len_zero {L : ByteSubLens Addr} (m : Mem)
    (bs : List ops.Byte) (hZero : L.len = 0) : L.set m bs = none := by
  unfold set
  rw [hZero]
  rfl

/-- A write of the wrong length is rejected. -/
theorem set_none_of_length_ne {L : ByteSubLens Addr} (m : Mem)
    {bs : List ops.Byte} (hNe : ¬ bs.length = L.len) : L.set m bs = none := by
  cases hSet : L.set m bs with
  | none => rfl
  | some m' => exact False.elim (hNe (set_inv hSet).2.1)

variable [LawfulByteStoreOps Mem Addr]

/-- A successful `get` returns exactly `L.len` bytes. -/
theorem get_len {L : ByteSubLens Addr} {m : Mem} {bs : List ops.Byte}
    (h : L.get m = some bs) : bs.length = L.len :=
  LawfulByteStoreOps.read_len (get_inv h).2

/-- Lens law `get_set`: reading after a write returns the written bytes. -/
theorem get_set {L : ByteSubLens Addr} {m m' : Mem} {bs : List ops.Byte}
    (h : L.set m bs = some m') : L.get m' = some bs := by
  let ⟨hPos, hLen, hWrite⟩ := set_inv h
  rw [get_of_pos m' hPos, ← hLen]
  exact LawfulByteStoreOps.read_write_same hWrite

/-- Lens law `set_get`: writing back what was read returns the same
memory. -/
theorem set_get {L : ByteSubLens Addr} {m : Mem} {bs : List ops.Byte}
    (h : L.get m = some bs) : L.set m bs = some m := by
  let ⟨hPos, hRead⟩ := get_inv h
  rw [set_of_pos m hPos (get_len h)]
  exact LawfulByteStoreOps.write_read_same hRead

/-- Lens law `set_set`: a second write overwrites the first. -/
theorem set_set {L : ByteSubLens Addr} {m m₁ : Mem} {bs₁ : List ops.Byte}
    (bs₂ : List ops.Byte) (h : L.set m bs₁ = some m₁) :
    L.set m₁ bs₂ = L.set m bs₂ := by
  let ⟨hPos, hLen₁, hWrite⟩ := set_inv h
  cases Nat.decEq bs₂.length L.len with
  | isTrue hLen₂ =>
    rw [set_of_pos m₁ hPos hLen₂, set_of_pos m hPos hLen₂]
    exact LawfulByteStoreOps.write_write_same hWrite (hLen₂.trans hLen₁.symm)
  | isFalse hNe =>
    rw [set_none_of_length_ne m₁ hNe, set_none_of_length_ne m hNe]

/-- A lens that can be read can be written with any bytes of its length. -/
theorem set_isSome_of_get {L : ByteSubLens Addr} {m : Mem}
    {old : List ops.Byte} (new : List ops.Byte) (h : L.get m = some old)
    (hLen : new.length = L.len) : ∃ m', L.set m new = some m' := by
  let ⟨hPos, hRead⟩ := get_inv h
  rw [set_of_pos m hPos hLen]
  exact LawfulByteStoreOps.write_of_read new hRead hLen

/-- Frame law `get_set_disjoint`: a write through one lens leaves every
non-interfering lens unchanged. -/
theorem get_set_disjoint {L₁ L₂ : ByteSubLens Addr} {m m' : Mem}
    {bs : List ops.Byte} (hDisj : Disjoint Mem L₁ L₂)
    (h : L₁.set m bs = some m') : L₂.get m' = L₂.get m := by
  let ⟨_, hLen, hWrite⟩ := set_inv h
  have hDisj' : ops.addrDisjoint L₁.addr L₁.offset bs.length L₂.addr
      L₂.offset L₂.len := by
    rw [hLen]
    exact hDisj
  have hRead := LawfulByteStoreOps.read_write_disjoint hDisj' hWrite
  unfold get
  rw [hRead]

/-- Commutation law `set_set_comm_disjoint`: writes through non-interfering
lenses commute. Each succeeds after the other, and both orders give the same
memory. -/
theorem set_set_comm_disjoint {L₁ L₂ : ByteSubLens Addr} {m m₁ m₂ : Mem}
    {b₁ b₂ : List ops.Byte} (hDisj : Disjoint Mem L₁ L₂)
    (h₁ : L₁.set m b₁ = some m₁) (h₂ : L₂.set m b₂ = some m₂) :
    ∃ m₃, L₂.set m₁ b₂ = some m₃ ∧ L₁.set m₂ b₁ = some m₃ := by
  let ⟨hPos₁, hLen₁, hWrite₁⟩ := set_inv h₁
  let ⟨hPos₂, hLen₂, hWrite₂⟩ := set_inv h₂
  have hDisj' : ops.addrDisjoint L₁.addr L₁.offset b₁.length L₂.addr
      L₂.offset b₂.length := by
    rw [hLen₁, hLen₂]
    exact hDisj
  let ⟨m₃, hA, hB⟩ :=
    LawfulByteStoreOps.write_write_comm hDisj' hWrite₁ hWrite₂
  refine ⟨m₃, ?_, ?_⟩
  · rw [set_of_pos m₁ hPos₂ hLen₂]
    exact hA
  · rw [set_of_pos m₂ hPos₁ hLen₁]
    exact hB

/-- Geometrically separated lenses do not interfere. -/
theorem disjoint_of_separated {L₁ L₂ : ByteSubLens Addr}
    (h : L₁.Separated L₂) : Disjoint Mem L₁ L₂ :=
  LawfulByteStoreOps.addrDisjoint_of_separated h

/-- Reading a sub-lens returns the corresponding sub-slice of the parent
read. -/
theorem zoom_get {L : ByteSubLens Addr} {m : Mem} {bs : List ops.Byte}
    {rel k : Nat} (h : L.get m = some bs) (hPos : 0 < k)
    (hSub : rel + k ≤ L.len) :
    (L.zoom rel k).get m = some ((bs.drop rel).take k) := by
  have hZoomPos : 0 < (L.zoom rel k).len := hPos
  rw [get_of_pos m hZoomPos]
  exact LawfulByteStoreOps.read_sub (get_inv h).2 hSub

end Ops

/-- Separation is symmetric. -/
theorem Separated.symm {L₁ L₂ : ByteSubLens Addr} (h : L₁.Separated L₂) :
    L₂.Separated L₁ := by
  cases h with
  | inl hNe => exact Or.inl (fun hEq => hNe hEq.symm)
  | inr hR =>
    cases hR with
    | inl hLeft => exact Or.inr (Or.inr hLeft)
    | inr hRight => exact Or.inr (Or.inl hRight)

/-- A positive-length lens overlaps itself: it is never separated from
itself. -/
theorem not_separated_self {L : ByteSubLens Addr} (hPos : 0 < L.len) :
    ¬ L.Separated L := by
  intro h
  have hLt : L.offset < L.offset + L.len := Nat.lt_add_of_pos_right hPos
  cases h with
  | inl hNe => exact hNe rfl
  | inr hR =>
    cases hR with
    | inl hLeft => exact Nat.not_le_of_gt hLt hLeft
    | inr hRight => exact Nat.not_le_of_gt hLt hRight

/-- Containment is reflexive. -/
theorem containedIn_refl (L : ByteSubLens Addr) : L.ContainedIn L :=
  ⟨rfl, Nat.le_refl L.offset, Nat.le_refl (L.offset + L.len)⟩

/-- Containment is transitive. -/
theorem containedIn_trans {a b c : ByteSubLens Addr}
    (hab : a.ContainedIn b) (hbc : b.ContainedIn c) : a.ContainedIn c :=
  ⟨hab.1.trans hbc.1, Nat.le_trans hbc.2.1 hab.2.1,
    Nat.le_trans hab.2.2 hbc.2.2⟩

/-- Separation is inherited by sub-lenses: sub-lenses of separated parents are
separated. -/
theorem separated_of_contained {c₁ p₁ c₂ p₂ : ByteSubLens Addr}
    (hc₁ : c₁.ContainedIn p₁) (hc₂ : c₂.ContainedIn p₂)
    (h : p₁.Separated p₂) : c₁.Separated c₂ := by
  cases h with
  | inl hNe =>
    exact Or.inl (fun hEq => hNe (hc₁.1.symm.trans (hEq.trans hc₂.1)))
  | inr hR =>
    cases hR with
    | inl hLeft =>
      exact Or.inr (Or.inl
        (Nat.le_trans hc₁.2.2 (Nat.le_trans hLeft hc₂.2.1)))
    | inr hRight =>
      exact Or.inr (Or.inr
        (Nat.le_trans hc₂.2.2 (Nat.le_trans hRight hc₁.2.1)))

/-- Store-level form of `separated_of_contained`: sub-lenses of separated
parents do not interfere. -/
theorem disjoint_of_contained [ops : ByteStoreOps.{u, v, w} Mem Addr]
    [LawfulByteStoreOps Mem Addr] {c₁ p₁ c₂ p₂ : ByteSubLens Addr}
    (hc₁ : c₁.ContainedIn p₁) (hc₂ : c₂.ContainedIn p₂)
    (h : p₁.Separated p₂) : Disjoint Mem c₁ c₂ :=
  disjoint_of_separated (separated_of_contained hc₁ hc₂ h)

/-- A sub-lens within the length of its parent is contained in it. -/
theorem zoom_containedIn (L : ByteSubLens Addr) {rel k : Nat}
    (h : rel + k ≤ L.len) : (L.zoom rel k).ContainedIn L := by
  refine ⟨rfl, Nat.le_add_right L.offset rel, ?_⟩
  change L.offset + rel + k ≤ L.offset + L.len
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left h L.offset

/-- Zooming twice is zooming once at the summed offset. -/
theorem zoom_zoom (L : ByteSubLens Addr) (r₁ k₁ r₂ k₂ : Nat) :
    (L.zoom r₁ k₁).zoom r₂ k₂ = L.zoom (r₁ + r₂) k₂ := by
  unfold zoom
  rw [Nat.add_assoc]

/-- Split borrow: sub-lenses with ordered ranges are separated. -/
theorem zoom_separated_of_le (L : ByteSubLens Addr) {r₁ k₁ r₂ : Nat}
    (k₂ : Nat) (h : r₁ + k₁ ≤ r₂) :
    (L.zoom r₁ k₁).Separated (L.zoom r₂ k₂) := by
  refine Or.inr (Or.inl ?_)
  change L.offset + r₁ + k₁ ≤ L.offset + r₂
  rw [Nat.add_assoc]
  exact Nat.add_le_add_left h L.offset

/-- Adjacent split: the sub-lenses `[rel, rel + k)` and
`[rel + k, rel + k + n)` are separated. -/
theorem zoom_separated_adjacent (L : ByteSubLens Addr) (rel k n : Nat) :
    (L.zoom rel k).Separated (L.zoom (rel + k) n) :=
  zoom_separated_of_le L n (Nat.le_refl (rel + k))

end ByteSubLens

/-- Hierarchical sub-slice containment under its `#4120` name. -/
abbrev subLensContained {Addr : Type v} (child parent : ByteSubLens Addr) :
    Prop :=
  child.ContainedIn parent

/-! ## Part V: Typed Views (Byte Codecs, Little-Endian Integers, Chunks) -/

/-- Codec between a stored byte slot and an initialized 8-bit value. `dec`
fails on a slot that holds no initialized value (for example an uninitialized
byte), and decoding an encoded value returns it. -/
structure ByteCodec (Byte : Type u) where
  /-- Stores an 8-bit value in a byte slot. -/
  enc : BitVec 8 → Byte
  /-- Reads the 8-bit value of a byte slot, if it holds one. -/
  dec : Byte → Option (BitVec 8)
  /-- Decoding an encoded value returns it. -/
  dec_enc : ∀ b : BitVec 8, dec (enc b) = some b

/-- Codec of raw `BitVec 8` byte slots. -/
def ByteCodec.bitVec8 : ByteCodec (BitVec 8) where
  enc := fun b => b
  dec := fun b => some b
  dec_enc := fun _ => rfl

/-- Codec of raw `UInt8` byte slots. -/
def ByteCodec.uint8 : ByteCodec UInt8 where
  enc := UInt8.ofBitVec
  dec := fun b => some b.toBitVec
  dec_enc := fun _ => rfl

/-- Codec of optional byte slots, where `none` is an uninitialized byte that
does not decode. -/
def ByteCodec.option {Byte : Type u} (c : ByteCodec Byte) :
    ByteCodec (Option Byte) where
  enc := fun b => some (c.enc b)
  dec := fun slot =>
    match slot with
    | none => none
    | some x => c.dec x
  dec_enc := fun b => c.dec_enc b

/-- Encodes a list of 8-bit values into byte slots. -/
def encodeBytes {Byte : Type u} (c : ByteCodec Byte) (xs : List (BitVec 8)) :
    List Byte :=
  List.foldr (fun x acc => c.enc x :: acc) [] xs

/-- Decodes a list of byte slots, failing when any slot does not decode. -/
def decodeBytes {Byte : Type u} (c : ByteCodec Byte) (bs : List Byte) :
    Option (List (BitVec 8)) :=
  List.foldr
    (fun b acc =>
      match c.dec b with
      | none => none
      | some x =>
        match acc with
        | none => none
        | some xs => some (x :: xs))
    (some []) bs

/-- Encoding preserves the length. -/
theorem encodeBytes_length {Byte : Type u} (c : ByteCodec Byte) :
    ∀ (xs : List (BitVec 8)), (encodeBytes c xs).length = xs.length
  | [] => rfl
  | _ :: tl => congrArg Nat.succ (encodeBytes_length c tl)

/-- Decoding encoded values returns them. -/
theorem decodeBytes_encodeBytes {Byte : Type u} (c : ByteCodec Byte)
    (xs : List (BitVec 8)) : decodeBytes c (encodeBytes c xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x tl ih =>
    change (match c.dec (c.enc x) with
      | none => none
      | some y =>
        match decodeBytes c (encodeBytes c tl) with
        | none => none
        | some ys => some (y :: ys)) = some (x :: tl)
    rw [c.dec_enc x, ih]

/-- A byte slot that does not decode makes the whole list fail to decode. -/
theorem decodeBytes_cons_none {Byte : Type u} (c : ByteCodec Byte) {b : Byte}
    (tl : List Byte) (h : c.dec b = none) : decodeBytes c (b :: tl) = none := by
  change (match c.dec b with
    | none => none
    | some y =>
      match decodeBytes c tl with
      | none => none
      | some ys => some (y :: ys)) = none
  rw [h]

/-- Concatenates a list of chunks (`List.foldr`, so it compiles without the
runtime definition of `List.flatten`). -/
def flattenChunks {α : Type u} (chunks : List (List α)) : List α :=
  List.foldr (fun chunk acc => chunk ++ acc) [] chunks

/-- `flattenChunks` is `List.flatten`. -/
theorem flattenChunks_eq_flatten {α : Type u} :
    ∀ (chunks : List (List α)), flattenChunks chunks = chunks.flatten
  | [] => rfl
  | chunk :: rest =>
    congrArg (fun acc => chunk ++ acc) (flattenChunks_eq_flatten rest)

/-- Re-encoding a bitvector from its own value is the identity. -/
theorem bitVec_ofNat_toNat {n : Nat} (x : BitVec n) :
    BitVec.ofNat n x.toNat = x :=
  Anneal.BitVec.eq_of_toNat_eq
    ((Anneal.BitVec.toNat_ofNat n x.toNat).trans (Nat.mod_eq_of_lt x.isLt))

namespace ByteSubLens

variable {Mem : Type u} {Addr : Type v}
  [ops : ByteStoreOps.{u, v, w} Mem Addr]

/-- Reads an `n`-byte little-endian integer through a lens of length `n`.
Fails closed when the lens has another length, when the read fails, or when a
byte does not decode. -/
def getLe (c : ByteCodec ops.Byte) (n : Nat) (L : ByteSubLens Addr)
    (m : Mem) : Option (BitVec (n * 8)) :=
  match Nat.beq L.len n with
  | false => none
  | true =>
    match L.get m with
    | none => none
    | some bs =>
      match decodeBytes c bs with
      | none => none
      | some raw => some (BitVec.ofNat (n * 8) (LeBytes.fromLeBytes raw))

/-- Writes an `n`-byte little-endian integer through a lens. The write is
rejected when the lens does not have length `n`. -/
def setLe (c : ByteCodec ops.Byte) (n : Nat) (L : ByteSubLens Addr)
    (m : Mem) (x : BitVec (n * 8)) : Option Mem :=
  L.set m (encodeBytes c (LeBytes.toLeBytes n x))

/-- The little-endian encoding of an `n`-byte integer has `n` byte slots. -/
theorem encodeBytes_toLeBytes_length (c : ByteCodec ops.Byte) (n : Nat)
    (x : BitVec (n * 8)) :
    (encodeBytes c (LeBytes.toLeBytes n x)).length = n :=
  (encodeBytes_length c (LeBytes.toLeBytes n x)).trans
    (LeBytes.toLeBytes_length n x)

/-- A successful little-endian write went through a lens of length `n`. -/
theorem setLe_len {c : ByteCodec ops.Byte} {n : Nat} {L : ByteSubLens Addr}
    {m m' : Mem} {x : BitVec (n * 8)} (h : L.setLe c n m x = some m') :
    L.len = n :=
  (set_inv h).2.1.symm.trans (encodeBytes_toLeBytes_length c n x)

/-- A little-endian write through a lens of another length is rejected. -/
theorem setLe_none_of_len_ne (c : ByteCodec ops.Byte) {n : Nat}
    {L : ByteSubLens Addr} (m : Mem) (x : BitVec (n * 8))
    (hNe : ¬ L.len = n) : L.setLe c n m x = none := by
  cases hSet : L.setLe c n m x with
  | none => rfl
  | some m' => exact False.elim (hNe (setLe_len hSet))

/-- A little-endian read through a lens of another length is rejected. -/
theorem getLe_none_of_len_ne (c : ByteCodec ops.Byte) {n : Nat}
    {L : ByteSubLens Addr} (m : Mem) (hNe : ¬ L.len = n) :
    L.getLe c n m = none := by
  unfold getLe
  rw [natBeq_false_of_not_eq hNe]

variable [LawfulByteStoreOps Mem Addr]

/-- Typed lens law: reading an integer after writing it returns it. -/
theorem getLe_setLe {c : ByteCodec ops.Byte} {n : Nat}
    {L : ByteSubLens Addr} {m m' : Mem} {x : BitVec (n * 8)}
    (h : L.setLe c n m x = some m') : L.getLe c n m' = some x := by
  have hLen : L.len = n := setLe_len h
  have hBeq : Nat.beq L.len n = true := by
    rw [hLen]
    exact Nat.beq_refl n
  have hGet : L.get m' = some (encodeBytes c (LeBytes.toLeBytes n x)) :=
    get_set h
  unfold getLe
  rw [hBeq, hGet]
  change (match decodeBytes c (encodeBytes c (LeBytes.toLeBytes n x)) with
    | none => none
    | some raw => some (BitVec.ofNat (n * 8) (LeBytes.fromLeBytes raw))) =
    some x
  rw [decodeBytes_encodeBytes c (LeBytes.toLeBytes n x)]
  change some (BitVec.ofNat (n * 8)
    (LeBytes.fromLeBytes (LeBytes.toLeBytes n x))) = some x
  rw [LeBytes.fromLeBytes_toLeBytes n x, bitVec_ofNat_toNat x]

/-- Typed lens law: a second integer write overwrites the first. -/
theorem setLe_setLe {c : ByteCodec ops.Byte} {n : Nat}
    {L : ByteSubLens Addr} {m m₁ : Mem} {x₁ : BitVec (n * 8)}
    (x₂ : BitVec (n * 8)) (h : L.setLe c n m x₁ = some m₁) :
    L.setLe c n m₁ x₂ = L.setLe c n m x₂ :=
  set_set (encodeBytes c (LeBytes.toLeBytes n x₂)) h

/-- Typed frame law: an integer write through one lens leaves the integer
read through every non-interfering lens unchanged, whatever its width. -/
theorem getLe_setLe_disjoint {c : ByteCodec ops.Byte} {n k : Nat}
    {L₁ L₂ : ByteSubLens Addr} {m m' : Mem} {x : BitVec (n * 8)}
    (hDisj : Disjoint Mem L₁ L₂) (h : L₁.setLe c n m x = some m') :
    L₂.getLe c k m' = L₂.getLe c k m := by
  unfold getLe
  rw [get_set_disjoint hDisj h]

/-- Raw frame law for a typed write: an integer write through one lens leaves
the bytes of every non-interfering lens unchanged. -/
theorem get_setLe_disjoint {c : ByteCodec ops.Byte} {n : Nat}
    {L₁ L₂ : ByteSubLens Addr} {m m' : Mem} {x : BitVec (n * 8)}
    (hDisj : Disjoint Mem L₁ L₂) (h : L₁.setLe c n m x = some m') :
    L₂.get m' = L₂.get m :=
  get_set_disjoint hDisj h

end ByteSubLens

namespace ByteSubLens

variable {Mem : Type u} {Addr : Type v}
  [ops : ByteStoreOps.{u, v, w} Mem Addr]

/-- Reads a little-endian `u16` (`BitVec 16`) through a 2-byte lens. -/
abbrev getU16 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem) :
    Option (BitVec 16) :=
  L.getLe c 2 m

/-- Writes a little-endian `u16` (`BitVec 16`) through a 2-byte lens. -/
abbrev setU16 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem)
    (x : BitVec 16) : Option Mem :=
  L.setLe c 2 m x

/-- Reads a little-endian `u32` (`BitVec 32`) through a 4-byte lens. -/
abbrev getU32 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem) :
    Option (BitVec 32) :=
  L.getLe c 4 m

/-- Writes a little-endian `u32` (`BitVec 32`) through a 4-byte lens. -/
abbrev setU32 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem)
    (x : BitVec 32) : Option Mem :=
  L.setLe c 4 m x

/-- Reads a little-endian `u64` (`BitVec 64`) through an 8-byte lens. -/
abbrev getU64 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem) :
    Option (BitVec 64) :=
  L.getLe c 8 m

/-- Writes a little-endian `u64` (`BitVec 64`) through an 8-byte lens. -/
abbrev setU64 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem)
    (x : BitVec 64) : Option Mem :=
  L.setLe c 8 m x

/-- Reads a little-endian `UInt16` through a 2-byte lens. -/
def getUInt16 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem) :
    Option UInt16 :=
  match L.getU16 c m with
  | none => none
  | some x => some (UInt16.ofBitVec x)

/-- Writes a little-endian `UInt16` through a 2-byte lens. -/
def setUInt16 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem)
    (x : UInt16) : Option Mem :=
  L.setU16 c m x.toBitVec

/-- Reads a little-endian `UInt32` through a 4-byte lens. -/
def getUInt32 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem) :
    Option UInt32 :=
  match L.getU32 c m with
  | none => none
  | some x => some (UInt32.ofBitVec x)

/-- Writes a little-endian `UInt32` through a 4-byte lens. -/
def setUInt32 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem)
    (x : UInt32) : Option Mem :=
  L.setU32 c m x.toBitVec

/-- Reads a little-endian `UInt64` through an 8-byte lens. -/
def getUInt64 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem) :
    Option UInt64 :=
  match L.getU64 c m with
  | none => none
  | some x => some (UInt64.ofBitVec x)

/-- Writes a little-endian `UInt64` through an 8-byte lens. -/
def setUInt64 (c : ByteCodec ops.Byte) (L : ByteSubLens Addr) (m : Mem)
    (x : UInt64) : Option Mem :=
  L.setU64 c m x.toBitVec

/-- Reads a lens as an array of `k`-byte elements (the last element is
shorter when `k` does not divide the length). -/
def getChunks (k : Nat) (L : ByteSubLens Addr) (m : Mem) :
    Option (List (List ops.Byte)) :=
  match L.get m with
  | none => none
  | some bs => some (ListChunks.chunksOf k bs)

/-- Writes an array of byte chunks through a lens. -/
def setChunks (L : ByteSubLens Addr) (m : Mem)
    (chunks : List (List ops.Byte)) : Option Mem :=
  L.set m (flattenChunks chunks)

variable [LawfulByteStoreOps Mem Addr]

/-- `UInt16` lens law: reading after a write returns the written value. -/
theorem getUInt16_setUInt16 {c : ByteCodec ops.Byte} {L : ByteSubLens Addr}
    {m m' : Mem} {x : UInt16} (h : L.setUInt16 c m x = some m') :
    L.getUInt16 c m' = some x := by
  have hGet : L.getU16 c m' = some x.toBitVec := getLe_setLe h
  unfold getUInt16
  rw [hGet]

/-- `UInt32` lens law: reading after a write returns the written value. -/
theorem getUInt32_setUInt32 {c : ByteCodec ops.Byte} {L : ByteSubLens Addr}
    {m m' : Mem} {x : UInt32} (h : L.setUInt32 c m x = some m') :
    L.getUInt32 c m' = some x := by
  have hGet : L.getU32 c m' = some x.toBitVec := getLe_setLe h
  unfold getUInt32
  rw [hGet]

/-- `UInt64` lens law: reading after a write returns the written value. -/
theorem getUInt64_setUInt64 {c : ByteCodec ops.Byte} {L : ByteSubLens Addr}
    {m m' : Mem} {x : UInt64} (h : L.setUInt64 c m x = some m') :
    L.getUInt64 c m' = some x := by
  have hGet : L.getU64 c m' = some x.toBitVec := getLe_setLe h
  unfold getUInt64
  rw [hGet]

/-- `UInt32` frame law: a `UInt32` write through one lens leaves the `UInt32`
read through every non-interfering lens unchanged. -/
theorem getUInt32_setUInt32_disjoint {c : ByteCodec ops.Byte}
    {L₁ L₂ : ByteSubLens Addr} {m m' : Mem} {x : UInt32}
    (hDisj : Disjoint Mem L₁ L₂) (h : L₁.setUInt32 c m x = some m') :
    L₂.getUInt32 c m' = L₂.getUInt32 c m := by
  have hGet : L₂.getU32 c m' = L₂.getU32 c m := getLe_setLe_disjoint hDisj h
  unfold getUInt32
  rw [hGet]

/-- Chunked-array lens law: writing back the chunks that were read returns
the same memory. -/
theorem setChunks_getChunks {k : Nat} (hk : 0 < k) {L : ByteSubLens Addr}
    {m : Mem} {chunks : List (List ops.Byte)}
    (h : L.getChunks k m = some chunks) : L.setChunks m chunks = some m := by
  unfold getChunks at h
  cases hGet : L.get m with
  | none =>
    rw [hGet] at h
    cases h
  | some bs =>
    rw [hGet] at h
    have hChunks : chunks = ListChunks.chunksOf k bs :=
      (Option.some.inj h).symm
    unfold setChunks
    rw [hChunks, flattenChunks_eq_flatten,
      ListChunks.chunksOf_flatten hk bs]
    exact set_get hGet

/-- A chunked read of a lens of length `L.len` has `divCeil L.len k`
elements. -/
theorem getChunks_length {k : Nat} (hk : 0 < k) {L : ByteSubLens Addr}
    {m : Mem} {chunks : List (List ops.Byte)}
    (h : L.getChunks k m = some chunks) :
    chunks.length = ListChunks.divCeil L.len k := by
  unfold getChunks at h
  cases hGet : L.get m with
  | none =>
    rw [hGet] at h
    cases h
  | some bs =>
    rw [hGet] at h
    have hChunks : chunks = ListChunks.chunksOf k bs :=
      (Option.some.inj h).symm
    rw [hChunks, ListChunks.chunksOf_length hk bs, get_len hGet]

/-- Chunked-array frame law: a chunked write through one lens leaves every
non-interfering lens unchanged. -/
theorem get_setChunks_disjoint {L₁ L₂ : ByteSubLens Addr} {m m' : Mem}
    {chunks : List (List ops.Byte)} (hDisj : Disjoint Mem L₁ L₂)
    (h : L₁.setChunks m chunks = some m') : L₂.get m' = L₂.get m :=
  get_set_disjoint hDisj h

end ByteSubLens

/-! ## Part VI: Mutation Summaries and `@[irreducible]` Summary Cuts -/

/-- Computable summary of a callee that mutates one byte sub-lens: from the
old bytes of the slice and an argument it computes the new bytes and a return
value, or `none` when the summary does not apply. `len` is the length of the
slice the callee expects. -/
structure MutSummary (Byte : Type u) (Arg : Type a) (Ret : Type b) where
  /-- Length in bytes of the mutated slice. -/
  len : Nat
  /-- Old slice and argument to new slice and return value. -/
  summaryFn : List Byte → Arg → Option (List Byte × Ret)

section Summary

variable {Mem : Type u} {Addr : Type v}
  [ops : ByteStoreOps.{u, v, w} Mem Addr] {Arg : Type a} {Ret : Type b}

/-- Executes a mutation summary on the lens `L` of the memory `m`: read the
slice, apply the summary, write the result back. A caller evaluates this by
`rfl` instead of stepping through the callee. -/
def execMutSummary (sum : MutSummary ops.Byte Arg Ret) (L : ByteSubLens Addr)
    (m : Mem) (arg : Arg) : Option (Mem × Ret) :=
  match Nat.beq L.len sum.len with
  | false => none
  | true =>
    match L.get m with
    | none => none
    | some old =>
      match sum.summaryFn old arg with
      | none => none
      | some res =>
        match L.set m res.1 with
        | none => none
        | some m' => some (m', res.2)

/-- Inversion of a successful summary execution. -/
theorem execMutSummary_inv {sum : MutSummary ops.Byte Arg Ret}
    {L : ByteSubLens Addr} {m m' : Mem} {arg : Arg} {ret : Ret}
    (h : execMutSummary sum L m arg = some (m', ret)) :
    L.len = sum.len ∧ ∃ old new, L.get m = some old ∧
      sum.summaryFn old arg = some (new, ret) ∧ L.set m new = some m' := by
  unfold execMutSummary at h
  cases hLen : Nat.beq L.len sum.len with
  | false =>
    rw [hLen] at h
    cases h
  | true =>
    rw [hLen] at h
    dsimp only at h
    cases hGet : L.get m with
    | none =>
      rw [hGet] at h
      cases h
    | some old =>
      rw [hGet] at h
      dsimp only at h
      cases hSum : sum.summaryFn old arg with
      | none =>
        rw [hSum] at h
        cases h
      | some res =>
        cases res with
        | mk new r =>
          rw [hSum] at h
          dsimp only at h
          cases hSet : L.set m new with
          | none =>
            rw [hSet] at h
            cases h
          | some m₁ =>
            rw [hSet] at h
            have hPair : (m₁, r) = (m', ret) := Option.some.inj h
            have hM : m₁ = m' := congrArg Prod.fst hPair
            have hR : r = ret := congrArg Prod.snd hPair
            rw [← hM, ← hR]
            exact ⟨Nat.eq_of_beq_eq_true hLen, old, new, rfl, hSum, hSet⟩

/-- A summary execution succeeds when its three steps do. -/
theorem execMutSummary_of {sum : MutSummary ops.Byte Arg Ret}
    {L : ByteSubLens Addr} {m m' : Mem} {arg : Arg} {ret : Ret}
    {old new : List ops.Byte} (hLen : L.len = sum.len)
    (hGet : L.get m = some old)
    (hSum : sum.summaryFn old arg = some (new, ret))
    (hSet : L.set m new = some m') :
    execMutSummary sum L m arg = some (m', ret) := by
  have hBeq : Nat.beq L.len sum.len = true := by
    rw [hLen]
    exact Nat.beq_refl sum.len
  unfold execMutSummary
  rw [hBeq, hGet]
  dsimp only
  rw [hSum]
  dsimp only
  rw [hSet]

/-- A summary whose slice length differs from the lens is rejected. -/
theorem execMutSummary_none_of_len_ne (sum : MutSummary ops.Byte Arg Ret)
    {L : ByteSubLens Addr} (m : Mem) (arg : Arg)
    (hNe : ¬ L.len = sum.len) : execMutSummary sum L m arg = none := by
  unfold execMutSummary
  rw [natBeq_false_of_not_eq hNe]

variable [LawfulByteStoreOps Mem Addr]

/-- After a summary execution the target lens holds the new bytes computed by
the summary. -/
theorem execMutSummary_target {sum : MutSummary ops.Byte Arg Ret}
    {L : ByteSubLens Addr} {m m' : Mem} {arg : Arg} {ret : Ret}
    (h : execMutSummary sum L m arg = some (m', ret)) :
    ∃ old new, L.get m = some old ∧
      sum.summaryFn old arg = some (new, ret) ∧ L.set m new = some m' ∧
      L.get m' = some new := by
  let ⟨_, old, new, hGet, hSum, hSet⟩ := execMutSummary_inv h
  exact ⟨old, new, hGet, hSum, hSet, ByteSubLens.get_set hSet⟩

/-- Frame of one summary execution: every lens that does not interfere with
the target lens is unchanged. -/
theorem execMutSummary_frame_disjoint {sum : MutSummary ops.Byte Arg Ret}
    {L other : ByteSubLens Addr} {m m' : Mem} {arg : Arg} {ret : Ret}
    (hDisj : ByteSubLens.Disjoint Mem L other)
    (h : execMutSummary sum L m arg = some (m', ret)) :
    other.get m' = other.get m := by
  let ⟨_, _, _, _, _, hSet⟩ := execMutSummary_inv h
  exact ByteSubLens.get_set_disjoint hDisj hSet

end Summary

section Realization

variable {State : Type x} [wops : MirWpOps.{x, y, z} State]
  {Mem : Type u} {Addr : Type v} [ops : ByteStoreOps.{u, v, w} Mem Addr]
  {Arg : Type a} {Ret : Type b}

/-- A callee realizes a mutation summary inside a machine with step interface
`MirWpOps State`.

`memOf` projects the byte memory out of a machine state, `atEntry L arg s`
says that `s` is a callee entry state for the lens `L` and argument `arg`, and
`atExit ret s s'` says that `s'` is the return state for the entry state `s`
with return value `ret`. Whenever the summary applies to the entry memory, the
write of the new bytes is defined, and every execution from the entry state
reaches a return state whose memory is exactly the result of that write,
without terminating or faulting on the way. -/
def CalleeRealizesMutSummary (memOf : State → Mem)
    (atEntry : ByteSubLens Addr → Arg → State → Prop)
    (atExit : Ret → State → State → Prop)
    (sum : MutSummary ops.Byte Arg Ret) : Prop :=
  ∀ (L : ByteSubLens Addr) (arg : Arg) (s : State) (old new : List ops.Byte)
    (ret : Ret),
    L.len = sum.len → atEntry L arg s → L.get (memOf s) = some old →
    sum.summaryFn old arg = some (new, ret) →
    ∃ m', L.set (memOf s) new = some m' ∧
      wpReach (ops := wops) (fun s' => memOf s' = m' ∧ atExit ret s s') s

/-- Zero-`Prop`-argument cutpoint sealing a verified callee summary. Its
arguments are the memory projection, the entry and exit relations and the
summary; the realization proof, with the callee's intermediate states, is
hidden behind the `@[irreducible]` constant. -/
def MutSummaryCut (memOf : State → Mem)
    (atEntry : ByteSubLens Addr → Arg → State → Prop)
    (atExit : Ret → State → State → Prop)
    (sum : MutSummary ops.Byte Arg Ret) : Prop :=
  CalleeRealizesMutSummary memOf atEntry atExit sum

/-- Seals a callee realization proof into a `MutSummaryCut`. -/
theorem seal_mutSummaryCut {memOf : State → Mem}
    {atEntry : ByteSubLens Addr → Arg → State → Prop}
    {atExit : Ret → State → State → Prop}
    {sum : MutSummary ops.Byte Arg Ret}
    (h : CalleeRealizesMutSummary memOf atEntry atExit sum) :
    MutSummaryCut memOf atEntry atExit sum :=
  h

/-- Opens a `MutSummaryCut` back into the callee realization. -/
theorem open_mutSummaryCut {memOf : State → Mem}
    {atEntry : ByteSubLens Addr → Arg → State → Prop}
    {atExit : Ret → State → State → Prop}
    {sum : MutSummary ops.Byte Arg Ret}
    (h : MutSummaryCut memOf atEntry atExit sum) :
    CalleeRealizesMutSummary memOf atEntry atExit sum :=
  h

/-- Whole-execution form of `CalleeRealizesMutSummary`, for a callee that is
its own machine: `entry L m arg` is its initial state, and `outMem` and
`outRet` read the final memory and the return value off its outcome. -/
def CalleeRealizesMutSummaryOutcome
    (entry : ByteSubLens Addr → Mem → Arg → State)
    (outMem : wops.Out → Mem) (outRet : wops.Out → Ret)
    (sum : MutSummary ops.Byte Arg Ret) : Prop :=
  ∀ (L : ByteSubLens Addr) (m : Mem) (arg : Arg) (old new : List ops.Byte)
    (ret : Ret),
    L.len = sum.len → L.get m = some old →
    sum.summaryFn old arg = some (new, ret) →
    ∃ m', L.set m new = some m' ∧
      wpStateOk (ops := wops) (fun out => outMem out = m' ∧ outRet out = ret)
        (entry L m arg)

/-- Zero-`Prop`-argument cutpoint sealing a verified whole-execution callee
summary. -/
def MutSummaryOutcomeCut (entry : ByteSubLens Addr → Mem → Arg → State)
    (outMem : wops.Out → Mem) (outRet : wops.Out → Ret)
    (sum : MutSummary ops.Byte Arg Ret) : Prop :=
  CalleeRealizesMutSummaryOutcome entry outMem outRet sum

/-- Seals a whole-execution callee realization proof. -/
theorem seal_mutSummaryOutcomeCut
    {entry : ByteSubLens Addr → Mem → Arg → State}
    {outMem : wops.Out → Mem} {outRet : wops.Out → Ret}
    {sum : MutSummary ops.Byte Arg Ret}
    (h : CalleeRealizesMutSummaryOutcome entry outMem outRet sum) :
    MutSummaryOutcomeCut entry outMem outRet sum :=
  h

/-- Opens a `MutSummaryOutcomeCut` back into the callee realization. -/
theorem open_mutSummaryOutcomeCut
    {entry : ByteSubLens Addr → Mem → Arg → State}
    {outMem : wops.Out → Mem} {outRet : wops.Out → Ret}
    {sum : MutSummary ops.Byte Arg Ret}
    (h : MutSummaryOutcomeCut entry outMem outRet sum) :
    CalleeRealizesMutSummaryOutcome entry outMem outRet sum :=
  h

end Realization

attribute [irreducible] MutSummaryCut MutSummaryOutcomeCut

section Apply

variable {State : Type x} [wops : MirWpOps.{x, y, z} State]
  {Mem : Type u} {Addr : Type v} [ops : ByteStoreOps.{u, v, w} Mem Addr]
  [LawfulByteStoreOps Mem Addr] {Arg : Type a} {Ret : Type b}

/-- Caller composition rule for `MutSummaryCut`. Whenever the computable
`execMutSummary` returns `some (m', ret)` on the entry memory (for example by
`rfl`), the machine reaches a return state with memory `m'` and return value
`ret`, the target lens holds the new bytes computed by the summary, and every
lens that does not interfere with the target lens is unchanged. The callee is
never unfolded. -/
theorem apply_mutSummaryCut_sound {memOf : State → Mem}
    {atEntry : ByteSubLens Addr → Arg → State → Prop}
    {atExit : Ret → State → State → Prop}
    {sum : MutSummary ops.Byte Arg Ret}
    (hCut : MutSummaryCut memOf atEntry atExit sum)
    {L : ByteSubLens Addr} {arg : Arg} {s : State} {m' : Mem} {ret : Ret}
    (hEntry : atEntry L arg s)
    (hExec : execMutSummary sum L (memOf s) arg = some (m', ret)) :
    wpReach (ops := wops) (fun s' => memOf s' = m' ∧ atExit ret s s') s ∧
    (∃ old new : List ops.Byte,
      L.get (memOf s) = some old ∧
      sum.summaryFn old arg = some (new, ret) ∧
      L.set (memOf s) new = some m' ∧
      L.get m' = some new) ∧
    (∀ other : ByteSubLens Addr, ByteSubLens.Disjoint Mem L other →
      other.get m' = other.get (memOf s)) := by
  let ⟨hLen, old, new, hGet, hSum, hSet⟩ := execMutSummary_inv hExec
  let ⟨m₁, hSet₁, hReach⟩ :=
    open_mutSummaryCut hCut L arg s old new ret hLen hEntry hGet hSum
  have hEq : m₁ = m' := by
    rw [hSet] at hSet₁
    exact (Option.some.inj hSet₁).symm
  rw [hEq] at hReach
  exact ⟨hReach, ⟨old, new, hGet, hSum, hSet, ByteSubLens.get_set hSet⟩,
    fun other hDisj => ByteSubLens.get_set_disjoint hDisj hSet⟩

/-- Continuation form of `apply_mutSummaryCut_sound`: a caller that continues
correctly from every return state with the summarized memory is correct from
the entry state. -/
theorem apply_mutSummaryCut_wpUntil {memOf : State → Mem}
    {atEntry : ByteSubLens Addr → Arg → State → Prop}
    {atExit : Ret → State → State → Prop}
    {sum : MutSummary ops.Byte Arg Ret}
    (hCut : MutSummaryCut memOf atEntry atExit sum)
    {L : ByteSubLens Addr} {arg : Arg} {s : State} {m' : Mem} {ret : Ret}
    {stop : State → Prop} {onDone : wops.Out → Prop}
    {onFault : wops.Fault → Prop}
    (hEntry : atEntry L arg s)
    (hExec : execMutSummary sum L (memOf s) arg = some (m', ret))
    (hCont : ∀ s', memOf s' = m' → atExit ret s s' →
      wpUntil stop onDone onFault s') :
    wpUntil stop onDone onFault s :=
  wpUntil_bind
    (wpUntil_mono (fun _ hs => hs) (fun _ hf => False.elim hf)
      (fun _ hf => False.elim hf)
      (apply_mutSummaryCut_sound hCut hEntry hExec).1)
    (fun s' hs' => hCont s' hs'.1 hs'.2)

/-- Caller composition rule for `MutSummaryOutcomeCut`: a successful
`execMutSummary` gives a fault-free whole-execution proof of the callee with
the summarized final memory and return value, the new bytes of the target
lens, and the frame of every non-interfering lens. -/
theorem apply_mutSummaryOutcomeCut_sound
    {entry : ByteSubLens Addr → Mem → Arg → State}
    {outMem : wops.Out → Mem} {outRet : wops.Out → Ret}
    {sum : MutSummary ops.Byte Arg Ret}
    (hCut : MutSummaryOutcomeCut entry outMem outRet sum)
    {L : ByteSubLens Addr} {arg : Arg} {m m' : Mem} {ret : Ret}
    (hExec : execMutSummary sum L m arg = some (m', ret)) :
    wpStateOk (ops := wops) (fun out => outMem out = m' ∧ outRet out = ret)
      (entry L m arg) ∧
    (∃ old new : List ops.Byte,
      L.get m = some old ∧ sum.summaryFn old arg = some (new, ret) ∧
      L.set m new = some m' ∧ L.get m' = some new) ∧
    (∀ other : ByteSubLens Addr, ByteSubLens.Disjoint Mem L other →
      other.get m' = other.get m) := by
  let ⟨hLen, old, new, hGet, hSum, hSet⟩ := execMutSummary_inv hExec
  let ⟨m₁, hSet₁, hOutcome⟩ :=
    open_mutSummaryOutcomeCut hCut L m arg old new ret hLen hGet hSum
  have hEq : m₁ = m' := by
    rw [hSet] at hSet₁
    exact (Option.some.inj hSet₁).symm
  rw [hEq] at hOutcome
  exact ⟨hOutcome, ⟨old, new, hGet, hSum, hSet, ByteSubLens.get_set hSet⟩,
    fun other hDisj => ByteSubLens.get_set_disjoint hDisj hSet⟩

end Apply

/-- One call site of a mutation summary: the summary, the lens it mutates and
its argument. -/
structure MutSummaryCall (Byte : Type u) (Addr : Type v) (Arg : Type a)
    (Ret : Type b) where
  /-- Summary of the callee. -/
  sum : MutSummary Byte Arg Ret
  /-- Lens the callee mutates. -/
  lens : ByteSubLens Addr
  /-- Argument passed to the callee. -/
  arg : Arg

section Chain

variable {Mem : Type u} {Addr : Type v}
  [ops : ByteStoreOps.{u, v, w} Mem Addr] {Arg : Type a} {Ret : Type b}

/-- Executes a list of summary call sites left to right (`List.foldr`, `0`
`._unsafe_rec`), returning the final memory and the return values in call
order. The chain fails as soon as one call does. -/
def execMutSummaryChain (calls : List (MutSummaryCall ops.Byte Addr Arg Ret))
    (m : Mem) : Option (Mem × List Ret) :=
  List.foldr
    (fun (call : MutSummaryCall ops.Byte Addr Arg Ret)
        (k : Mem → Option (Mem × List Ret)) (mCur : Mem) =>
      match execMutSummary call.sum call.lens mCur call.arg with
      | none => none
      | some step =>
        match k step.1 with
        | none => none
        | some rest => some (rest.1, step.2 :: rest.2))
    (fun mCur => some (mCur, [])) calls m

/-- Every call site of the chain mutates a lens that does not interfere with
`other`. -/
def AllCallsDisjoint (Mem : Type u) [ops : ByteStoreOps.{u, v, w} Mem Addr]
    (other : ByteSubLens Addr)
    (calls : List (MutSummaryCall ops.Byte Addr Arg Ret)) : Prop :=
  List.foldr
    (fun (call : MutSummaryCall ops.Byte Addr Arg Ret) (acc : Prop) =>
      ByteSubLens.Disjoint Mem call.lens other ∧ acc)
    True calls

/-- The empty chain returns the memory unchanged. -/
theorem execMutSummaryChain_nil (m : Mem) :
    execMutSummaryChain ([] : List (MutSummaryCall ops.Byte Addr Arg Ret)) m =
      some (m, []) :=
  rfl

/-- Inversion of a successful non-empty chain: the first call succeeds and the
rest of the chain runs from its result. -/
theorem execMutSummaryChain_cons_inv
    {call : MutSummaryCall ops.Byte Addr Arg Ret}
    {rest : List (MutSummaryCall ops.Byte Addr Arg Ret)} {m m' : Mem}
    {rets : List Ret}
    (h : execMutSummaryChain (call :: rest) m = some (m', rets)) :
    ∃ m₁ r rs, execMutSummary call.sum call.lens m call.arg = some (m₁, r) ∧
      execMutSummaryChain rest m₁ = some (m', rs) ∧ rets = r :: rs := by
  have h' : (match execMutSummary call.sum call.lens m call.arg with
    | none => none
    | some step =>
      match execMutSummaryChain rest step.1 with
      | none => none
      | some tail => some (tail.1, step.2 :: tail.2)) = some (m', rets) := h
  cases hStep : execMutSummary call.sum call.lens m call.arg with
  | none =>
    rw [hStep] at h'
    cases h'
  | some step =>
    cases step with
    | mk m₁ r =>
      rw [hStep] at h'
      dsimp only at h'
      cases hRest : execMutSummaryChain rest m₁ with
      | none =>
        rw [hRest] at h'
        cases h'
      | some tail =>
        cases tail with
        | mk mF rs =>
          rw [hRest] at h'
          have hPair : (mF, r :: rs) = (m', rets) := Option.some.inj h'
          have hM : mF = m' := congrArg Prod.fst hPair
          have hR : r :: rs = rets := congrArg Prod.snd hPair
          rw [← hM]
          exact ⟨m₁, r, rs, rfl, hRest, hR.symm⟩

/-- A successful chain returns one value per call site. -/
theorem execMutSummaryChain_length
    (calls : List (MutSummaryCall ops.Byte Addr Arg Ret)) {m m' : Mem}
    {rets : List Ret} (h : execMutSummaryChain calls m = some (m', rets)) :
    rets.length = calls.length := by
  induction calls generalizing m rets with
  | nil =>
    have hPair : (m, ([] : List Ret)) = (m', rets) := Option.some.inj h
    have hRets : ([] : List Ret) = rets := congrArg Prod.snd hPair
    rw [← hRets]
    rfl
  | cons call rest ih =>
    let ⟨m₁, r, rs, _, hRest, hRets⟩ := execMutSummaryChain_cons_inv h
    rw [hRets]
    exact congrArg Nat.succ (ih hRest)

/-- Frame theorem for chained summaries: a lens that does not interfere with
any of the `N` mutated lenses of the chain is preserved by the whole chain. -/
theorem execMutSummaryChain_frame_disjoint [LawfulByteStoreOps Mem Addr]
    (other : ByteSubLens Addr)
    (calls : List (MutSummaryCall ops.Byte Addr Arg Ret)) {m m' : Mem}
    {rets : List Ret} (hDisj : AllCallsDisjoint Mem other calls)
    (h : execMutSummaryChain calls m = some (m', rets)) :
    other.get m' = other.get m := by
  induction calls generalizing m rets with
  | nil =>
    have hPair : (m, ([] : List Ret)) = (m', rets) := Option.some.inj h
    have hMem : m = m' := congrArg Prod.fst hPair
    rw [← hMem]
  | cons call rest ih =>
    let ⟨m₁, r, rs, hStep, hRest, _⟩ := execMutSummaryChain_cons_inv h
    have hHead : ByteSubLens.Disjoint Mem call.lens other := hDisj.1
    have hTail : AllCallsDisjoint Mem other rest := hDisj.2
    rw [ih hTail hRest]
    exact execMutSummary_frame_disjoint hHead hStep

end Chain

/-! ## Part VII: Non-Vacuity Self-Tests on `SliceStore`

The canary store has a 12-byte buffer with identifier `7`, a second
allocation with the same identifier `7` (identifiers need not be unique), and
an allocation `9` that is not writable. -/

/-- Canary store over `Nat` byte slots. -/
def canaryStore : SliceStore Nat :=
  { allocs :=
      [{ allocId := 7, bytes := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
         writable := true },
       { allocId := 7, bytes := [0, 0], writable := true },
       { allocId := 9, bytes := [42, 43], writable := false }] }

/-- Header lens `[0, 4)` of allocation `7`. -/
def canaryHeader : ByteSubLens Nat := { addr := 7, offset := 0, len := 4 }

/-- Payload lens `[4, 12)` of allocation `7`. -/
def canaryPayload : ByteSubLens Nat := { addr := 7, offset := 4, len := 8 }

/-- Reads, a framed write and an overlapping write on the canary store,
evaluated by `rfl`: the payload survives a header write, a lens overlapping
the header sees it, and the duplicate allocation `7` is not touched. -/
theorem sliceStore_lens_canary :
    canaryHeader.get canaryStore = (some [1, 2, 3, 4] : Option (List Nat)) ∧
    canaryPayload.get canaryStore =
      (some [5, 6, 7, 8, 9, 10, 11, 12] : Option (List Nat)) ∧
    (match canaryHeader.set canaryStore ([90, 91, 92, 93] : List Nat) with
      | none => none
      | some m' => canaryPayload.get m') =
      (some [5, 6, 7, 8, 9, 10, 11, 12] : Option (List Nat)) ∧
    (match canaryHeader.set canaryStore ([90, 91, 92, 93] : List Nat) with
      | none => none
      | some m' => (ByteSubLens.mk 7 2 4).get m') =
      (some [92, 93, 5, 6] : Option (List Nat)) ∧
    (match canaryHeader.set canaryStore ([90, 91, 92, 93] : List Nat) with
      | none => none
      | some m' => some m'.allocs) =
      some
        [{ allocId := 7, bytes := [90, 91, 92, 93, 5, 6, 7, 8, 9, 10, 11, 12],
           writable := true },
         { allocId := 7, bytes := [0, 0], writable := true },
         { allocId := 9, bytes := [42, 43], writable := false }] :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Fail-closed rejections on the canary store, evaluated by `rfl`: a
zero-length lens, an out-of-bounds lens, a write of the wrong length, an
allocation that is not writable, and a missing allocation. -/
theorem sliceStore_reject_canary :
    (ByteSubLens.mk 7 0 0).get canaryStore = (none : Option (List Nat)) ∧
    (ByteSubLens.mk 7 8 8).get canaryStore = (none : Option (List Nat)) ∧
    canaryHeader.set canaryStore ([1, 2, 3] : List Nat) = none ∧
    (ByteSubLens.mk 7 8 8).set canaryStore
      ([1, 2, 3, 4, 5, 6, 7, 8] : List Nat) = none ∧
    (ByteSubLens.mk 9 0 2).get canaryStore = (none : Option (List Nat)) ∧
    (ByteSubLens.mk 9 0 2).set canaryStore ([1, 2] : List Nat) = none ∧
    (ByteSubLens.mk 5 0 1).get canaryStore = (none : Option (List Nat)) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canary store over `BitVec 8` byte slots holding the little-endian words
`0x12345678` and `0xBEEF`. -/
def canaryWordStore : SliceStore (BitVec 8) :=
  { allocs :=
      [{ allocId := 3,
         bytes := [BitVec.ofNat 8 0x78, BitVec.ofNat 8 0x56,
           BitVec.ofNat 8 0x34, BitVec.ofNat 8 0x12, BitVec.ofNat 8 0xEF,
           BitVec.ofNat 8 0xBE],
         writable := true }] }

/-- Typed little-endian views on the canary word store, evaluated by `rfl`: a
`u32` and a `u16` read, a `u32` write read back, and the `u16` neighbor
surviving the `u32` write. -/
theorem sliceStore_typed_canary :
    (ByteSubLens.mk 3 0 4).getU32 ByteCodec.bitVec8 canaryWordStore =
      some (BitVec.ofNat 32 0x12345678) ∧
    (ByteSubLens.mk 3 4 2).getU16 ByteCodec.bitVec8 canaryWordStore =
      some (BitVec.ofNat 16 0xBEEF) ∧
    (match (ByteSubLens.mk 3 0 4).setU32 ByteCodec.bitVec8 canaryWordStore
        (BitVec.ofNat 32 0xAABBCCDD) with
      | none => none
      | some m' => (ByteSubLens.mk 3 0 4).getU32 ByteCodec.bitVec8 m') =
      some (BitVec.ofNat 32 0xAABBCCDD) ∧
    (match (ByteSubLens.mk 3 0 4).setU32 ByteCodec.bitVec8 canaryWordStore
        (BitVec.ofNat 32 0xAABBCCDD) with
      | none => none
      | some m' => (ByteSubLens.mk 3 4 2).getU16 ByteCodec.bitVec8 m') =
      some (BitVec.ofNat 16 0xBEEF) ∧
    (ByteSubLens.mk 3 0 2).getU32 ByteCodec.bitVec8 canaryWordStore = none :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Summary of a callee that adds its argument to a one-byte counter and
returns the old counter value. -/
def canaryIncSummary : MutSummary Nat Nat Nat where
  len := 1
  summaryFn := fun old arg =>
    match old with
    | [b] => some ([b + arg], b)
    | _ => none

/-- The canary store after adding `5` to the first byte of allocation `7`. -/
def canaryStoreInc : SliceStore Nat :=
  { allocs :=
      [{ allocId := 7, bytes := [6, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12],
         writable := true },
       { allocId := 7, bytes := [0, 0], writable := true },
       { allocId := 9, bytes := [42, 43], writable := false }] }

/-- Summary execution and a two-call chain on the canary store, evaluated by
`rfl`; a summary on a lens of the wrong length is rejected. -/
theorem sliceStore_summary_canary :
    execMutSummary canaryIncSummary (ByteSubLens.mk 7 0 1) canaryStore 5 =
      some (canaryStoreInc, 1) ∧
    execMutSummary canaryIncSummary canaryHeader canaryStore 5 = none ∧
    (match execMutSummaryChain
        [{ sum := canaryIncSummary, lens := ByteSubLens.mk 7 0 1, arg := 5 },
         { sum := canaryIncSummary, lens := ByteSubLens.mk 7 1 1, arg := 7 }]
        canaryStore with
      | none => none
      | some res => some (res.2, canaryPayload.get res.1)) =
      some ([1, 2], (some [5, 6, 7, 8, 9, 10, 11, 12] : Option (List Nat))) :=
  ⟨rfl, rfl, rfl⟩

/-- `ByteSubLens.get` on `SliceStore Nat` with its byte type spelled `Nat`.
The bundled byte type `ByteStoreOps.Byte` is definitionally `Nat` here, but
instance resolution does not unfold it, so arithmetic on bytes read through
the interface needs this spelling. -/
def canaryRead (L : ByteSubLens Nat) (m : SliceStore Nat) :
    Option (List Nat) :=
  L.get m

/-- `ByteSubLens.set` on `SliceStore Nat` with its byte type spelled `Nat`. -/
def canaryWrite (L : ByteSubLens Nat) (m : SliceStore Nat) (bs : List Nat) :
    Option (SliceStore Nat) :=
  L.set m bs

/-- State of a toy callee that realizes `canaryIncSummary` over `SliceStore`:
a program counter, the lens and argument it was called with, the memory, and
the return register. -/
structure SummaryToyState where
  /-- Program counter: `0` at entry, `1` at the return point. -/
  pc : Nat
  /-- Lens the callee was called with. -/
  lens : ByteSubLens Nat
  /-- Argument the callee was called with. -/
  arg : Nat
  /-- Byte memory. -/
  mem : SliceStore Nat
  /-- Return register. -/
  ret : Nat

/-- One step of the toy callee: at entry it reads the one-byte counter through
its lens, writes the incremented value back and moves to the return point
with the old value in the return register. It faults when the read or the
write fails. -/
def summaryToyStep (s : SummaryToyState) :
    StepOutcome SummaryToyState Nat Unit :=
  match s.pc with
  | 0 =>
    match canaryRead s.lens s.mem with
    | some [b] =>
      match canaryWrite s.lens s.mem [b + s.arg] with
      | some m' =>
        .step { pc := 1, lens := s.lens, arg := s.arg, mem := m', ret := b }
      | none => .fault ()
    | _ => .fault ()
  | _ => .done s.ret

/-- Deterministic step interface of the toy callee. -/
@[reducible] def summaryToyOps : MirWpOps SummaryToyState :=
  MirWpOps.ofDetStep summaryToyStep

/-- Realization of `canaryIncSummary` by the toy callee, stated with the byte
type spelled `Nat`. -/
theorem summaryToy_realizes_nat (lens : ByteSubLens Nat) (sarg sret : Nat)
    (mem : SliceStore Nat) (old new : List Nat) (ret : Nat)
    (hLen : lens.len = 1) (hGet : canaryRead lens mem = some old)
    (hSum : canaryIncSummary.summaryFn old sarg = some (new, ret)) :
    ∃ m', canaryWrite lens mem new = some m' ∧
      wpReach (ops := summaryToyOps)
        (fun s' => s'.mem = m' ∧ s'.pc = 1 ∧ s'.ret = ret)
        { pc := 0, lens := lens, arg := sarg, mem := mem, ret := sret } := by
  cases old with
  | nil => cases hSum
  | cons b tl =>
    cases tl with
    | cons b' tl' => cases hSum
    | nil =>
      have hPair : ([b + sarg], b) = (new, ret) := Option.some.inj hSum
      have hNew : [b + sarg] = new := congrArg Prod.fst hPair
      have hRet : b = ret := congrArg Prod.snd hPair
      have hNewLen : new.length = lens.len := by
        rw [← hNew, hLen]
        rfl
      let ⟨m', hSet⟩ := ByteSubLens.set_isSome_of_get (L := lens) (m := mem)
        new hGet hNewLen
      have hSet' : canaryWrite lens mem [b + sarg] = some m' := by
        rw [hNew]
        exact hSet
      refine ⟨m', hSet, ?_⟩
      have hStep : summaryToyStep
          { pc := 0, lens := lens, arg := sarg, mem := mem, ret := sret } =
          .step
            { pc := 1, lens := lens, arg := sarg, mem := m', ret := b } := by
        change (match canaryRead lens mem with
          | some [c] =>
            match canaryWrite lens mem [c + sarg] with
            | some m'' =>
              (StepOutcome.step
                { pc := 1, lens := lens, arg := sarg, mem := m'', ret := c } :
                StepOutcome SummaryToyState Nat Unit)
            | none => StepOutcome.fault ()
          | _ => StepOutcome.fault ()) = _
        rw [hGet]
        dsimp only
        rw [hSet']
      exact wpUntil_det_step_eq (step := summaryToyStep) hStep
        (wpUntil_here (ops := summaryToyOps) ⟨rfl, rfl, hRet⟩)

/-- The toy callee realizes `canaryIncSummary` for every lens, argument and
memory: the realization is a universally quantified statement about the
machine, not a check on one store. -/
theorem summaryToy_realizes :
    CalleeRealizesMutSummary (wops := summaryToyOps)
      (fun s : SummaryToyState => s.mem)
      (fun L arg s => s.pc = 0 ∧ s.lens = L ∧ s.arg = arg)
      (fun ret _ s' => s'.pc = 1 ∧ s'.ret = ret) canaryIncSummary := by
  intro L arg s old new ret hLen hEntry hGet hSum
  cases s with
  | mk pc lens sarg mem sret =>
    have hPc : pc = 0 := hEntry.1
    have hLens : lens = L := hEntry.2.1
    have hArg : sarg = arg := hEntry.2.2
    subst hPc
    subst hLens
    subst hArg
    exact summaryToy_realizes_nat lens sarg sret mem old new ret hLen hGet hSum

/-- The toy callee sealed behind a `MutSummaryCut`. -/
theorem summaryToy_cut :
    MutSummaryCut (wops := summaryToyOps)
      (fun s : SummaryToyState => s.mem)
      (fun L arg s => s.pc = 0 ∧ s.lens = L ∧ s.arg = arg)
      (fun ret _ s' => s'.pc = 1 ∧ s'.ret = ret) canaryIncSummary :=
  seal_mutSummaryCut (wops := summaryToyOps) summaryToy_realizes

/-- End-to-end summary canary: a caller on the canary store applies the sealed
cut by evaluating `execMutSummary` by `rfl`. It obtains the machine run to the
return point with the incremented store and the old counter value `1`, and
the payload lens is framed without looking at the callee. -/
theorem summaryToy_apply_canary :
    wpReach (ops := summaryToyOps)
      (fun s' => s'.mem = canaryStoreInc ∧ s'.pc = 1 ∧ s'.ret = 1)
      { pc := 0, lens := ByteSubLens.mk 7 0 1, arg := 5, mem := canaryStore,
        ret := 0 } ∧
    canaryPayload.get canaryStoreInc =
      (some [5, 6, 7, 8, 9, 10, 11, 12] : Option (List Nat)) := by
  have hExec : execMutSummary canaryIncSummary (ByteSubLens.mk 7 0 1)
      canaryStore 5 = some (canaryStoreInc, 1) := rfl
  have hApply := apply_mutSummaryCut_sound (wops := summaryToyOps)
    summaryToy_cut
    (s := { pc := 0, lens := ByteSubLens.mk 7 0 1, arg := 5,
            mem := canaryStore, ret := 0 })
    ⟨rfl, rfl, rfl⟩ hExec
  refine ⟨hApply.1, ?_⟩
  have hSep : (ByteSubLens.mk 7 0 1).Separated canaryPayload :=
    Or.inr (Or.inl (Nat.le_of_ble_eq_true rfl))
  rw [hApply.2.2 canaryPayload (ByteSubLens.disjoint_of_separated hSep)]
  rfl

end Anneal.ParametricCore
