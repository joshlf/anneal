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

universe u v w

namespace Anneal.ParametricCore

/-!
# Logarithmic Radix-2 and Dense `Chunk8` Block Trees
(`Anneal.ParametricCore.BlockTree`)

This module restates the indexed lookup tables of `Anneal.Core.BlockTree`
(`#4069`) without any MIR model. It imports only `Init.*` modules of the
Pass-1 foundation lock, is universe-polymorphic in the element type, and is
total and LCNF-computable (`0` `noncomputable`, `0` `._unsafe_rec`).

1. **List reference semantics (`listGet?`, `listSet?`):** `List.foldr`-based
   lookup and `List.set`-based update, with `listGet? xs idx = xs[idx]?`.
2. **Radix-2 binary trie (`PTree α`, `BlockTree α`):** `O(log N)` lookup and
   single-pass functional update (`ptreeModifyAt`), `O(N log N)` direct list
   splitting (`ptreeFromListAt`) at depth `compLog2Depth`, and unconditional
   equivalence `(BlockTree.ofList xs).lookup? idx = listGet? xs idx` across
   both in-bounds and out-of-bounds indices.
3. **Dense 8-wide balanced spine (`Chunk8 α`, `Chunk8Tree α`,
   `Chunk8BlockTree α`, `MaskTree := Chunk8BlockTree Bool`):** packing 8
   contiguous elements per `Chunk8` leaf keeps spine depth `≤ 9` and tree
   height `≤ 10` at `N = 4,096` elements, supports `O(1)` 8-element batch
   chunk lookup (`lookupChunk`), and matches `listGet?` unconditionally.
4. **Parametric step adapters and cut evaluation:** any block-indexed step
   function gives the same result over `BlockTree.ofList blocks`,
   `Chunk8BlockTree.ofList blocks` and `listGet? blocks`, and
   `evalBlockTreeToCut` runs such a step function up to a set of cutpoint
   blocks without unfolding `blocks`.
-/

/-! ## Constructive Binary Arithmetic Helpers -/

private theorem boolFalseNeTrue : ¬ (false = true) :=
  fun h => Bool.noConfusion h

private theorem ite_bool_true {α : Type u} {b : Bool} {t e : α} (hb : b = true) :
    (if b then t else e) = t := by
  subst hb
  rfl

private theorem ite_bool_false {α : Type u} {b : Bool} {t e : α}
    (hb : b = false) :
    (if b then t else e) = e := by
  subst hb
  rfl

/-- Computable `2^n` via `@Nat.rec` (`0` `noncomputable`). -/
def pow2 (n : Nat) : Nat :=
  @Nat.rec (fun _ => Nat) 1 (fun _ ih => 2 * ih) n

/-- Base equation `pow2 0 = 1`. -/
theorem pow2_zero : pow2 0 = 1 := rfl

/-- Step equation `pow2 (n + 1) = 2 * pow2 n`. -/
theorem pow2_succ (n : Nat) : pow2 (n + 1) = 2 * pow2 n := rfl

/-- Strict positivity `0 < pow2 n`. -/
theorem pow2_pos (n : Nat) : 0 < pow2 n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ _ ih =>
    rw [pow2_succ]
    exact Nat.mul_pos (Nat.succ_pos 1) ih

/-- Exponential dominance `n < pow2 n`. -/
theorem id_lt_pow2 (n : Nat) : n < pow2 n := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ k ih =>
    rw [pow2_succ]
    have h1 : k + 1 ≤ pow2 k := ih
    have h2 : pow2 k + pow2 k = 2 * pow2 k := by
      have hm : (1 + 1) * pow2 k = 1 * pow2 k + 1 * pow2 k :=
        Nat.add_mul 1 1 (pow2 k)
      rw [Nat.one_mul] at hm
      exact hm.symm
    rw [← h2]
    have ha : (k + 1) + 0 < (k + 1) + pow2 k :=
      Nat.add_lt_add_left (pow2_pos k) (k + 1)
    rw [Nat.add_zero] at ha
    exact Nat.lt_of_lt_of_le ha (Nat.add_le_add_right h1 (pow2 k))

/-- Parity decomposition of `n` into `2 * (n / 2)` or `2 * (n / 2) + 1`. -/
theorem nat_div2_decomp (n : Nat) :
    if Nat.beq (Nat.mod n 2) 0 = true then
      2 * Nat.div n 2 = n
    else
      2 * Nat.div n 2 + 1 = n := by
  have hlt : Nat.mod n 2 < 2 := Nat.mod_lt n (Nat.succ_pos 1)
  have hdiv : 2 * Nat.div n 2 + Nat.mod n 2 = n := Nat.div_add_mod n 2
  cases hm : Nat.mod n 2 with
  | zero =>
    rw [hm] at hdiv
    rw [Nat.add_zero] at hdiv
    exact hdiv
  | succ r =>
    rw [hm] at hlt
    cases r with
    | zero =>
      rw [hm] at hdiv
      exact hdiv
    | succ r2 =>
      have hbad : ¬ (r2 + 2 < 2) := Nat.not_lt_of_ge (Nat.le_add_left 2 r2)
      exact False.elim (hbad hlt)

/-! ## List Reference Semantics (`listGet?`, `listSet?`) -/

/-- Looks up the element at 0-based `idx`, returning `none` when out of
bounds. Defined by `List.foldr`, so it unfolds by `rfl` on `[]` and on
`x :: xs` at `0` and `idx + 1`; `listGet?_eq_getElem?` identifies it with
`xs[idx]?`. -/
def listGet? {α : Type u} (xs : List α) : Nat → Option α :=
  List.foldr
    (fun x rest idx =>
      match idx with
      | 0 => some x
      | k + 1 => rest k)
    (fun _ => none) xs

/-- Functional point update at 0-based `idx`, returning `none` when `idx` is
out of bounds. -/
def listSet? {α : Type u} (xs : List α) (idx : Nat) (val : α) :
    Option (List α) :=
  if idx < xs.length then some (xs.set idx val) else none

/-- A propositional `if` whose condition holds is its `then` branch. -/
theorem ite_prop_pos {α : Sort u} {P : Prop} {inst : Decidable P} {t e : α}
    (h : P) : (@ite α P inst t e) = t := by
  cases inst with
  | isTrue _ => rfl
  | isFalse hn => exact False.elim (hn h)

/-- A propositional `if` whose condition fails is its `else` branch. -/
theorem ite_prop_neg {α : Sort u} {P : Prop} {inst : Decidable P} {t e : α}
    (h : ¬ P) : (@ite α P inst t e) = e := by
  cases inst with
  | isTrue hp => exact False.elim (h hp)
  | isFalse _ => rfl

/-- Lookup in the empty list fails. -/
theorem listGet?_nil {α : Type u} (idx : Nat) :
    listGet? ([] : List α) idx = none :=
  rfl

/-- Lookup at index `0` returns the head. -/
theorem listGet?_cons_zero {α : Type u} (x : α) (xs : List α) :
    listGet? (x :: xs) 0 = some x :=
  rfl

/-- Lookup at index `idx + 1` continues in the tail. -/
theorem listGet?_cons_succ {α : Type u} (x : α) (xs : List α) (idx : Nat) :
    listGet? (x :: xs) (idx + 1) = listGet? xs idx :=
  rfl

/-- `listGet?` is the standard list indexing `xs[idx]?`. -/
theorem listGet?_eq_getElem? {α : Type u} :
    ∀ (xs : List α) (idx : Nat), listGet? xs idx = xs[idx]?
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: tl, k + 1 => listGet?_eq_getElem? tl k

/-- Out-of-bounds lookup fails. -/
theorem listGet?_eq_none_of_le {α : Type u} :
    ∀ (xs : List α) (idx : Nat), xs.length ≤ idx → listGet? xs idx = none
  | [], _, _ => rfl
  | _ :: _, 0, h => False.elim (Nat.not_succ_le_zero _ h)
  | _ :: tl, k + 1, h =>
    listGet?_eq_none_of_le tl k (Nat.le_of_succ_le_succ h)

/-- In-bounds lookup succeeds. -/
theorem listGet?_isSome_of_lt {α : Type u} :
    ∀ (xs : List α) (idx : Nat), idx < xs.length →
      ∃ x, listGet? xs idx = some x
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | x :: _, 0, _ => ⟨x, rfl⟩
  | _ :: tl, k + 1, h =>
    listGet?_isSome_of_lt tl k (Nat.lt_of_succ_lt_succ h)

/-- A successful lookup is in bounds. -/
theorem listGet?_lt_of_eq_some {α : Type u} {xs : List α} {idx : Nat}
    {x : α} (h : listGet? xs idx = some x) : idx < xs.length := by
  cases Nat.lt_or_ge idx xs.length with
  | inl hLt => exact hLt
  | inr hGe =>
    rw [listGet?_eq_none_of_le xs idx hGe] at h
    cases h

/-- `List.set` preserves the length. -/
theorem listLength_set {α : Type u} :
    ∀ (xs : List α) (idx : Nat) (val : α),
      (xs.set idx val).length = xs.length
  | [], _, _ => rfl
  | _ :: _, 0, _ => rfl
  | _ :: tl, k + 1, val => congrArg Nat.succ (listLength_set tl k val)

/-- Reading an updated in-bounds index returns the written element. -/
theorem listGet?_set_same {α : Type u} :
    ∀ (xs : List α) (idx : Nat) (val : α), idx < xs.length →
      listGet? (xs.set idx val) idx = some val
  | [], _, _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: _, 0, _, _ => rfl
  | _ :: tl, k + 1, val, h =>
    listGet?_set_same tl k val (Nat.lt_of_succ_lt_succ h)

/-- Reading any other index is unaffected by an update. -/
theorem listGet?_set_ne {α : Type u} :
    ∀ (xs : List α) (idx j : Nat) (val : α), j ≠ idx →
      listGet? (xs.set idx val) j = listGet? xs j
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hNe => False.elim (hNe rfl)
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: tl, k + 1, m + 1, val, hNe =>
    listGet?_set_ne tl k m val (fun he => hNe (congrArg Nat.succ he))

/-- `listSet?` succeeds on an in-bounds index. -/
theorem listSet?_of_lt {α : Type u} {xs : List α} {idx : Nat} (val : α)
    (h : idx < xs.length) : listSet? xs idx val = some (xs.set idx val) :=
  ite_prop_pos h

/-- `listSet?` fails closed on an out-of-bounds index. -/
theorem listSet?_of_not_lt {α : Type u} {xs : List α} {idx : Nat} (val : α)
    (h : ¬ idx < xs.length) : listSet? xs idx val = none :=
  ite_prop_neg h

/-- Inversion of a successful `listSet?`. -/
theorem listSet?_lt_and_eq {α : Type u} {xs xs' : List α} {idx : Nat}
    {val : α} (hSet : listSet? xs idx val = some xs') :
    idx < xs.length ∧ xs' = xs.set idx val := by
  cases Nat.decLt idx xs.length with
  | isTrue h =>
    rw [listSet?_of_lt val h] at hSet
    injection hSet with hEq
    exact ⟨h, hEq.symm⟩
  | isFalse h =>
    rw [listSet?_of_not_lt val h] at hSet
    cases hSet

/-- A successful `listSet?` is in bounds and preserves the length. -/
theorem listSet?_lt_and_length {α : Type u} {xs xs' : List α} {idx : Nat}
    {val : α} (hSet : listSet? xs idx val = some xs') :
    idx < xs.length ∧ xs'.length = xs.length := by
  have h := listSet?_lt_and_eq hSet
  refine ⟨h.1, ?_⟩
  rw [h.2]
  exact listLength_set xs idx val

/-- Read-over-write at the same index for `listSet?`. -/
theorem listGet?_listSet?_same {α : Type u} {xs xs' : List α} {idx : Nat}
    {val : α} (hSet : listSet? xs idx val = some xs') :
    listGet? xs' idx = some val := by
  have h := listSet?_lt_and_eq hSet
  rw [h.2]
  exact listGet?_set_same xs idx val h.1

/-- Read-over-write at a different index for `listSet?`. -/
theorem listGet?_listSet?_ne {α : Type u} {xs xs' : List α} {idx j : Nat}
    {val : α} (hNe : j ≠ idx) (hSet : listSet? xs idx val = some xs') :
    listGet? xs' j = listGet? xs j := by
  rw [(listSet?_lt_and_eq hSet).2]
  exact listGet?_set_ne xs idx j val hNe

private theorem natEq_of_beq (a b : Nat) (h : Nat.beq a b = true) : a = b := by
  revert b
  induction a with
  | zero =>
    intro b h
    cases b with
    | zero => rfl
    | succ _ => exact False.elim (boolFalseNeTrue h)
  | succ _ ih =>
    intro b h
    cases b with
    | zero => exact False.elim (boolFalseNeTrue h)
    | succ b' => exact congrArg Nat.succ (ih b' h)

private theorem natBeq_refl (a : Nat) : Nat.beq a a = true := by
  induction a with
  | zero => rfl
  | succ _ ih => exact ih

private theorem natBeq_false_of_ne {a b : Nat} (h : a ≠ b) :
    Nat.beq a b = false := by
  cases hb : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (h (natEq_of_beq a b hb))

/-! ## Radix-2 Binary Trie (`PTree`) -/

/-- Radix-2 binary trie storing optional elements at leaves of a fixed depth. -/
inductive PTree (α : Type u) : Type u where
  | empty : PTree α
  | leaf : Option α → PTree α
  | node : PTree α → PTree α → PTree α

/-- Top-down strided radix-2 tabulation helper (`0` `noncomputable`). -/
def ptreeTabulateAt {α : Type u} (depth : Nat) :
    Nat → Nat → (Nat → Option α) → PTree α :=
  @Nat.rec (fun _ => Nat → Nat → (Nat → Option α) → PTree α)
    (fun offset _ f => PTree.leaf (f offset))
    (fun _ ih offset step f =>
      PTree.node (ih offset (2 * step) f) (ih (offset + step) (2 * step) f))
    depth

/-- Tabulates `f 0 .. f (2^depth - 1)` into a balanced radix-2 `PTree α`. -/
def ptreeTabulate {α : Type u} (f : Nat → Option α) (depth : Nat) : PTree α :=
  ptreeTabulateAt depth 0 1 f

/-- Looks up `idx` in a depth-`depth` `PTree α` in `O(depth)` bit steps. -/
def ptreeGetAt {α : Type u} (depth : Nat) : PTree α → Nat → Option α :=
  @Nat.rec (fun _ => PTree α → Nat → Option α)
    (fun t idx =>
      match t with
      | .empty => none
      | .leaf v => if Nat.beq idx 0 then v else none
      | .node _ _ => none)
    (fun _ ih t idx =>
      match t with
      | .empty => none
      | .leaf _ => none
      | .node l r =>
        if Nat.beq (Nat.mod idx 2) 0 then
          ih l (Nat.div idx 2)
        else
          ih r (Nat.div idx 2))
    depth

/-- Single-pass `O(depth)` functional update at `idx` in `PTree α`, allocating
missing interior spines on demand. -/
def ptreeModifyAt {α : Type u} (depth : Nat) :
    PTree α → Nat → Option α → PTree α :=
  @Nat.rec (fun _ => PTree α → Nat → Option α → PTree α)
    (fun t idx v =>
      if Nat.beq idx 0 then .leaf v else t)
    (fun _ ih t idx v =>
      let (l, r) : PTree α × PTree α :=
        match t with
        | .node l0 r0 => (l0, r0)
        | .empty | .leaf _ => (.empty, .empty)
      if Nat.beq (Nat.mod idx 2) 0 then
        .node (ih l (Nat.div idx 2) v) r
      else
        .node l (ih r (Nat.div idx 2) v))
    depth

/-- In-bounds lookup on `ptreeTabulateAt` (`idx < pow2 depth`). -/
theorem ptreeGetAt_ptreeTabulateAt_in {α : Type u}
    (depth idx offset step : Nat) (f : Nat → Option α)
    (hidx : idx < pow2 depth) :
    ptreeGetAt depth (ptreeTabulateAt depth offset step f) idx =
      f (offset + step * idx) := by
  revert idx offset step
  induction depth with
  | zero =>
    intro idx offset step hidx
    rw [pow2_zero] at hidx
    have h0 : idx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hidx)
    rw [h0, Nat.mul_zero, Nat.add_zero]
    rfl
  | succ d ih =>
    intro idx offset step hidx
    change (if Nat.beq (Nat.mod idx 2) 0 then
        ptreeGetAt d (ptreeTabulateAt d offset (2 * step) f) (Nat.div idx 2)
      else
        ptreeGetAt d (ptreeTabulateAt d (offset + step) (2 * step) f)
          (Nat.div idx 2)) =
      f (offset + step * idx)
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hidx
    have hhalf : Nat.div idx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hidx
    have hde := nat_div2_decomp idx
    cases hbeq : Nat.beq (Nat.mod idx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 = idx at hde
      rw [ite_bool_true rfl, ih (Nat.div idx 2) offset (2 * step) hhalf]
      have hmul : (2 * step) * Nat.div idx 2 = step * idx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div idx 2), hde]
      rw [hmul]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 + 1 = idx at hde
      rw [ite_bool_false rfl,
        ih (Nat.div idx 2) (offset + step) (2 * step) hhalf]
      have harith :
          (offset + step) + (2 * step) * Nat.div idx 2 =
            offset + step * idx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div idx 2),
          Nat.add_assoc offset step (step * (2 * Nat.div idx 2))]
        have hs1 :
            step + step * (2 * Nat.div idx 2) =
              step * (2 * Nat.div idx 2 + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        rw [hs1, hde]
      rw [harith]

/-- Out-of-bounds lookup on `ptreeTabulateAt` (`pow2 depth ≤ idx`). -/
theorem ptreeGetAt_ptreeTabulateAt_oob {α : Type u}
    (depth idx offset step : Nat) (f : Nat → Option α)
    (hoob : pow2 depth ≤ idx) :
    ptreeGetAt depth (ptreeTabulateAt depth offset step f) idx = none := by
  revert idx offset step
  induction depth with
  | zero =>
    intro idx _ _ hoob
    rw [pow2_zero] at hoob
    cases idx with
    | zero => exact False.elim (Nat.not_lt_of_ge hoob Nat.zero_lt_one)
    | succ _ => rfl
  | succ d ih =>
    intro idx offset step hoob
    change (if Nat.beq (Nat.mod idx 2) 0 then
        ptreeGetAt d (ptreeTabulateAt d offset (2 * step) f) (Nat.div idx 2)
      else
        ptreeGetAt d (ptreeTabulateAt d (offset + step) (2 * step) f)
          (Nat.div idx 2)) = none
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hoob
    have hhalf : pow2 d ≤ Nat.div idx 2 :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hoob
    cases Nat.beq (Nat.mod idx 2) 0 with
    | true =>
      rw [ite_bool_true rfl]
      exact ih (Nat.div idx 2) offset (2 * step) hhalf
    | false =>
      rw [ite_bool_false rfl]
      exact ih (Nat.div idx 2) (offset + step) (2 * step) hhalf

private theorem ptreeGetAt_empty {α : Type u} (depth idx : Nat) :
    ptreeGetAt depth (.empty : PTree α) idx = none := by
  cases depth <;> rfl

/-- Same-index read-after-modify law for `ptreeModifyAt` (`idx < pow2 depth`).
-/
theorem ptreeGetAt_ptreeModifyAt_same {α : Type u}
    (depth : Nat) (t : PTree α) (idx : Nat) (v : Option α)
    (hidx : idx < pow2 depth) :
    ptreeGetAt depth (ptreeModifyAt depth t idx v) idx = v := by
  revert t idx
  induction depth with
  | zero =>
    intro t idx hidx
    rw [pow2_zero] at hidx
    have h0 : idx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hidx)
    subst h0
    rfl
  | succ d ih =>
    intro t idx hidx
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hidx
    have hhalf : Nat.div idx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hidx
    cases t with
    | empty | leaf _ =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d .empty (Nat.div idx 2) v) .empty
           else
             PTree.node .empty (ptreeModifyAt d .empty (Nat.div idx 2) v))
          idx = v
      cases hpar : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v) (Nat.div idx 2)
          else ptreeGetAt d .empty (Nat.div idx 2)) = v
        rw [hpar, ite_bool_true rfl]
        exact ih .empty (Nat.div idx 2) hhalf
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d .empty (Nat.div idx 2)
          else
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v)
              (Nat.div idx 2)) = v
        rw [hpar, ite_bool_false rfl]
        exact ih .empty (Nat.div idx 2) hhalf
    | node l r =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d l (Nat.div idx 2) v) r
           else
             PTree.node l (ptreeModifyAt d r (Nat.div idx 2) v))
          idx = v
      cases hpar : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d (ptreeModifyAt d l (Nat.div idx 2) v) (Nat.div idx 2)
          else ptreeGetAt d r (Nat.div idx 2)) = v
        rw [hpar, ite_bool_true rfl]
        exact ih l (Nat.div idx 2) hhalf
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod idx 2) 0 then
            ptreeGetAt d l (Nat.div idx 2)
          else
            ptreeGetAt d (ptreeModifyAt d r (Nat.div idx 2) v)
              (Nat.div idx 2)) = v
        rw [hpar, ite_bool_false rfl]
        exact ih r (Nat.div idx 2) hhalf

/-- Frame law for `ptreeModifyAt` at any distinct index `j ≠ idx`. -/
theorem ptreeGetAt_ptreeModifyAt_ne {α : Type u}
    (depth : Nat) (t : PTree α) (idx j : Nat) (v : Option α)
    (hNe : j ≠ idx) :
    ptreeGetAt depth (ptreeModifyAt depth t idx v) j =
      ptreeGetAt depth t j := by
  revert t idx j
  induction depth with
  | zero =>
    intro t idx j hNe
    change ptreeGetAt 0 (if Nat.beq idx 0 then PTree.leaf v else t) j =
      ptreeGetAt 0 t j
    cases hIdx : Nat.beq idx 0 with
    | false => rw [ite_bool_false rfl]
    | true =>
      have h0 : idx = 0 := natEq_of_beq idx 0 hIdx
      subst h0
      have hj0 : Nat.beq j 0 = false := natBeq_false_of_ne hNe
      rw [ite_bool_true rfl]
      cases t with
      | empty =>
        change (if Nat.beq j 0 then v else none) = none
        rw [hj0, ite_bool_false rfl]
      | leaf w =>
        change (if Nat.beq j 0 then v else none) =
          (if Nat.beq j 0 then w else none)
        rw [hj0, ite_bool_false rfl, ite_bool_false rfl]
      | node _ _ =>
        change (if Nat.beq j 0 then v else none) = none
        rw [hj0, ite_bool_false rfl]
  | succ d ih =>
    intro t idx j hNe
    have hDivNe :
        Nat.beq (Nat.mod j 2) 0 = Nat.beq (Nat.mod idx 2) 0 →
        Nat.div j 2 ≠ Nat.div idx 2 := by
      intro hParEq hDivEq
      have hdj := nat_div2_decomp j
      have hdi := nat_div2_decomp idx
      cases hp : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [hp] at hParEq hdi
        rw [hParEq] at hdj
        change 2 * Nat.div j 2 = j at hdj
        change 2 * Nat.div idx 2 = idx at hdi
        rw [hDivEq, hdi] at hdj
        exact hNe hdj.symm
      | false =>
        rw [hp] at hParEq hdi
        rw [hParEq] at hdj
        change 2 * Nat.div j 2 + 1 = j at hdj
        change 2 * Nat.div idx 2 + 1 = idx at hdi
        rw [hDivEq, hdi] at hdj
        exact hNe hdj.symm
    cases t with
    | empty | leaf _ =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d .empty (Nat.div idx 2) v) .empty
           else
             PTree.node .empty (ptreeModifyAt d .empty (Nat.div idx 2) v))
          j = none
      cases hpi : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v) (Nat.div j 2)
          else ptreeGetAt d .empty (Nat.div j 2)) = none
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl,
            ih .empty (Nat.div idx 2) (Nat.div j 2)
              (hDivNe (hpj.trans hpi.symm))]
          exact ptreeGetAt_empty d (Nat.div j 2)
        | false =>
          rw [ite_bool_false rfl]
          exact ptreeGetAt_empty d (Nat.div j 2)
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d .empty (Nat.div j 2)
          else
            ptreeGetAt d (ptreeModifyAt d .empty (Nat.div idx 2) v)
              (Nat.div j 2)) = none
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl]
          exact ptreeGetAt_empty d (Nat.div j 2)
        | false =>
          rw [ite_bool_false rfl,
            ih .empty (Nat.div idx 2) (Nat.div j 2)
              (hDivNe (hpj.trans hpi.symm))]
          exact ptreeGetAt_empty d (Nat.div j 2)
    | node l r =>
      change ptreeGetAt (d + 1)
          (if Nat.beq (Nat.mod idx 2) 0 then
             PTree.node (ptreeModifyAt d l (Nat.div idx 2) v) r
           else
             PTree.node l (ptreeModifyAt d r (Nat.div idx 2) v))
          j =
        (if Nat.beq (Nat.mod j 2) 0 then
           ptreeGetAt d l (Nat.div j 2)
         else
           ptreeGetAt d r (Nat.div j 2))
      cases hpi : Nat.beq (Nat.mod idx 2) 0 with
      | true =>
        rw [ite_bool_true rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d (ptreeModifyAt d l (Nat.div idx 2) v) (Nat.div j 2)
          else ptreeGetAt d r (Nat.div j 2)) =
          (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d l (Nat.div j 2)
          else ptreeGetAt d r (Nat.div j 2))
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl, ite_bool_true rfl]
          exact ih l (Nat.div idx 2) (Nat.div j 2) (hDivNe (hpj.trans hpi.symm))
        | false =>
          rw [ite_bool_false rfl, ite_bool_false rfl]
      | false =>
        rw [ite_bool_false rfl]
        change (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d l (Nat.div j 2)
          else
            ptreeGetAt d (ptreeModifyAt d r (Nat.div idx 2) v) (Nat.div j 2)) =
          (if Nat.beq (Nat.mod j 2) 0 then
            ptreeGetAt d l (Nat.div j 2)
          else ptreeGetAt d r (Nat.div j 2))
        cases hpj : Nat.beq (Nat.mod j 2) 0 with
        | true =>
          rw [ite_bool_true rfl, ite_bool_true rfl]
        | false =>
          rw [ite_bool_false rfl, ite_bool_false rfl]
          exact ih r (Nat.div idx 2) (Nat.div j 2) (hDivNe (hpj.trans hpi.symm))

/-! ## Logarithmic Depth Bound, Direct List Splitting, and `BlockTree` -/

/-- Accumulator-passing logarithmic ceiling loop via `@Nat.rec`, terminating
reduction as soon as `n ≤ cap` (`O(log n)` reduction depth). -/
def compLog2DepthGo (n : Nat) : Nat → Nat → Nat → Nat :=
  @Nat.rec (fun _ => Nat → Nat → Nat)
    (fun depth _ => depth)
    (fun _ ih depth cap =>
      if Nat.ble n cap then depth
      else ih (depth + 1) (2 * cap))

/-- Smallest radix-2 tree depth covering `n` elements (`compLog2Depth 26 = 5`,
`compLog2Depth 64 = 6`). -/
def compLog2Depth (n : Nat) : Nat := compLog2DepthGo n n 0 1

private theorem compLog2DepthGo_bound (n : Nat) :
    ∀ (fuel depth cap : Nat),
      cap = pow2 depth →
      n ≤ depth + fuel →
      n ≤ pow2 (compLog2DepthGo n fuel depth cap)
  | 0, depth, _, _, hSum => by
    rw [Nat.add_zero] at hSum
    exact Nat.le_trans hSum (Nat.le_of_lt (id_lt_pow2 depth))
  | k + 1, depth, cap, hCap, hSum => by
    change n ≤ pow2
      (if Nat.ble n cap then depth
       else compLog2DepthGo n k (depth + 1) (2 * cap))
    cases hble : Nat.ble n cap with
    | true =>
      rw [ite_bool_true rfl, ← hCap]
      exact Nat.le_of_ble_eq_true hble
    | false =>
      rw [ite_bool_false rfl]
      have hCap' : 2 * cap = pow2 (depth + 1) := by
        rw [pow2_succ, hCap]
      have hSum' : n ≤ (depth + 1) + k := by
        rw [Nat.succ_add, ← Nat.add_succ]
        exact hSum
      exact compLog2DepthGo_bound n k (depth + 1) (2 * cap) hCap' hSum'

/-- `n ≤ pow2 (compLog2Depth n)` holds for all `n : Nat`. -/
theorem le_pow2_compLog2Depth (n : Nat) : n ≤ pow2 (compLog2Depth n) := by
  have hSum : n ≤ 0 + n := by
    rw [Nat.zero_add]
    exact Nat.le_refl n
  exact compLog2DepthGo_bound n n 0 1 rfl hSum

/-- Splits `xs` in one pass into `(evens, odds)` (`evens[k] = xs[2*k]`,
`odds[k] = xs[2*k + 1]`). -/
def unzipEvenOdd {α : Type u} (xs : List α) : List α × List α :=
  List.foldr (fun x eo => (x :: eo.2, eo.1)) ([], []) xs

private theorem getElem?_unzipEvenOdd {α : Type u} :
    ∀ (xs : List α) (k : Nat),
      (listGet? (unzipEvenOdd xs).1 k =
         listGet? xs (2 * k)) ∧
      (listGet? (unzipEvenOdd xs).2 k =
         listGet? xs (2 * k + 1))
  | [], k => by
    cases k <;> exact ⟨rfl, rfl⟩
  | x :: xs, k => by
    refine ⟨?_, (getElem?_unzipEvenOdd xs k).1⟩
    cases k with
    | zero => rfl
    | succ k' =>
      have hMul : 2 * (k' + 1) = (2 * k' + 1) + 1 := by
        rw [Nat.mul_succ]
      rw [hMul]
      exact (getElem?_unzipEvenOdd xs k').2

private theorem length_unzipEvenOdd_bounds {α : Type u} :
    ∀ (xs : List α),
      2 * (unzipEvenOdd xs).1.length ≤ xs.length + 1 ∧
      2 * (unzipEvenOdd xs).2.length ≤ xs.length
  | [] => ⟨Nat.zero_le 1, Nat.le_refl 0⟩
  | x :: xs => by
    have ih := length_unzipEvenOdd_bounds xs
    change 2 * ((unzipEvenOdd xs).2.length + 1) ≤ (xs.length + 1) + 1 ∧
      2 * (unzipEvenOdd xs).1.length ≤ xs.length + 1
    refine ⟨?_, ih.1⟩
    rw [Nat.mul_succ]
    exact Nat.add_le_add_right ih.2 2

/-- Builds a radix-2 `PTree α` of height `depth` directly from `xs` by
splitting even and odd indices at each level (`O(|xs| log |xs|)` total work,
pruning empty subtrees to `.empty` without per-leaf list rescans). -/
def ptreeFromListAt {α : Type u} (depth : Nat) : List α → PTree α :=
  @Nat.rec (fun _ => List α → PTree α)
    (fun xs =>
      match xs with
      | [] => .empty
      | x :: _ => .leaf (some x))
    (fun _ ih xs =>
      match xs with
      | [] => .empty
      | _ :: _ =>
        let eo := unzipEvenOdd xs
        .node (ih eo.1) (ih eo.2))
    depth

/-- Lookup equivalence for `ptreeFromListAt` across all `idx : Nat` whenever
`xs.length ≤ pow2 depth`. -/
theorem ptreeGetAt_ptreeFromListAt {α : Type u} :
    ∀ (depth : Nat) (xs : List α),
      xs.length ≤ pow2 depth →
      ∀ idx : Nat,
        ptreeGetAt depth (ptreeFromListAt depth xs) idx =
          listGet? xs idx
  | 0, [], _, idx => by
    cases idx <;> rfl
  | 0, [x], _, idx => by
    cases idx <;> rfl
  | 0, _ :: _ :: tl, hBound, _ => by
    rw [pow2_zero] at hBound
    exact False.elim
      (Nat.not_lt_of_ge hBound (Nat.succ_lt_succ (Nat.succ_pos tl.length)))
  | d + 1, [], _, idx => by
    change (none : Option α) = listGet? [] idx
    cases idx <;> rfl
  | d + 1, x :: tl, hBound, idx => by
    let xs := x :: tl
    have hLen := length_unzipEvenOdd_bounds xs
    rw [pow2_succ] at hBound
    have hSub2 : (unzipEvenOdd xs).2.length ≤ pow2 d := by
      have h2 : 2 * (unzipEvenOdd xs).2.length ≤ 2 * pow2 d :=
        Nat.le_trans hLen.2 hBound
      exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos 1)
    have hSub1 : (unzipEvenOdd xs).1.length ≤ pow2 d := by
      cases Nat.lt_or_ge (pow2 d) (unzipEvenOdd xs).1.length with
      | inr hle => exact hle
      | inl hgt =>
        have hGe1 : pow2 d + 1 ≤ (unzipEvenOdd xs).1.length := hgt
        have hMulGe : 2 * (pow2 d + 1) ≤ 2 * (unzipEvenOdd xs).1.length :=
          Nat.mul_le_mul_left 2 hGe1
        rw [Nat.mul_succ] at hMulGe
        have hUpper : 2 * (unzipEvenOdd xs).1.length ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hLen.1 (Nat.succ_le_succ hBound)
        have hContra : 2 * pow2 d + 2 ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hMulGe hUpper
        exact False.elim
          (Nat.not_lt_of_ge hContra (Nat.lt_succ_self (2 * pow2 d + 1)))
    change
      (if Nat.beq (Nat.mod idx 2) 0 then
         ptreeGetAt d (ptreeFromListAt d (unzipEvenOdd xs).1) (Nat.div idx 2)
       else
         ptreeGetAt d (ptreeFromListAt d (unzipEvenOdd xs).2)
           (Nat.div idx 2)) =
      listGet? xs idx
    have hde := nat_div2_decomp idx
    cases hbeq : Nat.beq (Nat.mod idx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 = idx at hde
      rw [ite_bool_true rfl,
        ptreeGetAt_ptreeFromListAt d (unzipEvenOdd xs).1 hSub1 (Nat.div idx 2),
        (getElem?_unzipEvenOdd xs (Nat.div idx 2)).1, hde]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div idx 2 + 1 = idx at hde
      rw [ite_bool_false rfl,
        ptreeGetAt_ptreeFromListAt d (unzipEvenOdd xs).2 hSub2 (Nat.div idx 2),
        (getElem?_unzipEvenOdd xs (Nat.div idx 2)).2, hde]

/-- Pure-data logarithmic lookup table over elements of type `α` (`0` `Prop`
fields so `BlockTree` reduces freely in computational positions). -/
structure BlockTree (α : Type u) where
  depth : Nat
  tree : PTree α

/-- Lazy right-fold list length (`O(k)` WHNF prefix inspection under `Nat.ble`,
avoiding `List.length`'s strict tail-recursive full-list scan during
elaboration). -/
def compListLength {α : Type u} (xs : List α) : Nat :=
  List.foldr (fun _ k => Nat.succ k) 0 xs

/-- Exact agreement between `compListLength` and `List.length`. -/
theorem compListLength_eq {α : Type u} :
    ∀ (xs : List α), compListLength xs = xs.length
  | [] => rfl
  | _ :: tl => congrArg Nat.succ (compListLength_eq tl)

/-- Tabulates `xs` into a `BlockTree α` at explicit depth `depth` via
single-pass even/odd list splitting (`ptreeFromListAt`). -/
def BlockTree.ofListAt {α : Type u} (xs : List α) (depth : Nat) : BlockTree α :=
  { depth := depth, tree := ptreeFromListAt depth xs }

/-- Tabulates `xs` into a `BlockTree α` at depth
`compLog2Depth (compListLength xs)`. -/
def BlockTree.ofList {α : Type u} (xs : List α) : BlockTree α :=
  BlockTree.ofListAt xs (compLog2Depth (compListLength xs))

/-- Looks up index `idx` in `bt` in `O(bt.depth)` trie steps. -/
def BlockTree.lookup? {α : Type u} (bt : BlockTree α) (idx : Nat) : Option α :=
  ptreeGetAt bt.depth bt.tree idx

/-- Functionally updates index `idx` in `bt` in `O(bt.depth)` trie steps. -/
def BlockTree.modify {α : Type u} (bt : BlockTree α) (idx : Nat) (v : Option α) :
    BlockTree α :=
  { depth := bt.depth, tree := ptreeModifyAt bt.depth bt.tree idx v }

/-- Validity predicate tying a pure-data `BlockTree α` back to `xs`. -/
def ValidBlockTree {α : Type u} (xs : List α) (bt : BlockTree α) : Prop :=
  xs.length ≤ pow2 bt.depth ∧
  ∀ idx : Nat, bt.lookup? idx = listGet? xs idx

/-- `BlockTree.ofListAt xs depth` is valid whenever `xs.length ≤ pow2 depth`. -/
theorem valid_blockTree_ofListAt {α : Type u} (xs : List α) (depth : Nat)
    (hBound : xs.length ≤ pow2 depth) :
    ValidBlockTree xs (BlockTree.ofListAt xs depth) :=
  ⟨hBound, ptreeGetAt_ptreeFromListAt depth xs hBound⟩

/-- `BlockTree.ofList xs` is unconditionally valid for every `xs : List α`. -/
theorem valid_blockTree_ofList {α : Type u} (xs : List α) :
    ValidBlockTree xs (BlockTree.ofList xs) := by
  have hBound : xs.length ≤ pow2 (compLog2Depth (compListLength xs)) := by
    rw [compListLength_eq xs]
    exact le_pow2_compLog2Depth xs.length
  exact valid_blockTree_ofListAt xs (compLog2Depth (compListLength xs)) hBound

/-- Exact equivalence between `BlockTree.lookup?` and
`listGet?` across both in-bounds and out-of-bounds indices.
-/
theorem BlockTree.lookup_eq_getElem? {α : Type u} {xs : List α}
    {bt : BlockTree α} (hValid : ValidBlockTree xs bt) (idx : Nat) :
    bt.lookup? idx = listGet? xs idx :=
  hValid.2 idx

/-- Premise-free lookup equivalence for `BlockTree.ofList xs`. -/
theorem BlockTree.ofList_lookup_eq {α : Type u} (xs : List α) (idx : Nat) :
    (BlockTree.ofList xs).lookup? idx = listGet? xs idx :=
  BlockTree.lookup_eq_getElem? (valid_blockTree_ofList xs) idx

/-- Same-index read-after-modify law for `BlockTree.modify` (`idx < pow2
bt.depth`). -/
theorem BlockTree.lookup_modify_same {α : Type u} (bt : BlockTree α)
    (idx : Nat) (v : Option α) (hidx : idx < pow2 bt.depth) :
    (bt.modify idx v).lookup? idx = v :=
  ptreeGetAt_ptreeModifyAt_same bt.depth bt.tree idx v hidx

/-- Frame law for `BlockTree.modify` at any distinct index `j ≠ idx`. -/
theorem BlockTree.lookup_modify_ne {α : Type u} (bt : BlockTree α)
    (idx j : Nat) (v : Option α) (hNe : j ≠ idx) :
    (bt.modify idx v).lookup? j = bt.lookup? j :=
  ptreeGetAt_ptreeModifyAt_ne bt.depth bt.tree idx j v hNe

/-- `BlockTree.modify idx (some val)` preserves `ValidBlockTree` across
`listSet?`. -/
theorem BlockTree.valid_modify_of_setElem? {α : Type u} {xs xs' : List α}
    {bt : BlockTree α} {idx : Nat} {val : α}
    (hValid : ValidBlockTree xs bt)
    (hSet : listSet? xs idx val = some xs') :
    ValidBlockTree xs' (bt.modify idx (some val)) := by
  have hLtLen := listSet?_lt_and_length hSet
  have hIdxPow2 : idx < pow2 bt.depth := Nat.lt_of_lt_of_le hLtLen.1 hValid.1
  refine ⟨?_, fun j => ?_⟩
  · unfold BlockTree.modify
    dsimp only
    rw [hLtLen.2]
    exact hValid.1
  · cases hBeq : Nat.beq j idx with
    | true =>
      have hEq : j = idx := natEq_of_beq j idx hBeq
      subst hEq
      rw [BlockTree.lookup_modify_same bt j (some val) hIdxPow2,
        listGet?_listSet?_same hSet]
    | false =>
      have hNe : j ≠ idx := fun hEq => by
        subst hEq
        rw [natBeq_refl j] at hBeq
        exact boolFalseNeTrue hBeq.symm
      rw [BlockTree.lookup_modify_ne bt idx j (some val) hNe,
        hValid.2 j, listGet?_listSet?_ne hNe hSet]

/-! ## Dense 8-Wide Balanced Spine (`Chunk8`, `Chunk8BlockTree`, `MaskTree`) -/

/-- Fixed-width 8-slot leaf chunk storing `Option α` entries at offsets `0..7`.

Grouping 8 contiguous indices per leaf shrinks the binary spine by 3 levels so
`N = 4,096` elements fit in `512 = 2^9` chunks (spine depth `9`, tree height
`≤ 10`, total constructor depth `≤ 11` vs. `4,097` for `List.cons`). -/
structure Chunk8 (α : Type u) where
  e0 : Option α
  e1 : Option α
  e2 : Option α
  e3 : Option α
  e4 : Option α
  e5 : Option α
  e6 : Option α
  e7 : Option α

/-- All-`none` `Chunk8 α`. -/
def Chunk8.empty {α : Type u} : Chunk8 α :=
  ⟨none, none, none, none, none, none, none, none⟩

/-- Constant-time `O(1)` slot lookup in `Chunk8 α` (returns `none` for
`r ≥ 8`). -/
def Chunk8.get {α : Type u} (c : Chunk8 α) (r : Nat) : Option α :=
  match r with
  | 0 => c.e0
  | 1 => c.e1
  | 2 => c.e2
  | 3 => c.e3
  | 4 => c.e4
  | 5 => c.e5
  | 6 => c.e6
  | 7 => c.e7
  | _ => none

/-- Constant-time `O(1)` slot update in `Chunk8 α`.

Destructures `c` once into flat constructor fields instead of using record
update projections so repeated updates do not build nested projection chains in
kernel WHNF. -/
def Chunk8.set {α : Type u} (c : Chunk8 α) (r : Nat) (v : Option α) : Chunk8 α :=
  match c with
  | ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩ =>
    match r with
    | 0 => ⟨v, e1, e2, e3, e4, e5, e6, e7⟩
    | 1 => ⟨e0, v, e2, e3, e4, e5, e6, e7⟩
    | 2 => ⟨e0, e1, v, e3, e4, e5, e6, e7⟩
    | 3 => ⟨e0, e1, e2, v, e4, e5, e6, e7⟩
    | 4 => ⟨e0, e1, e2, e3, v, e5, e6, e7⟩
    | 5 => ⟨e0, e1, e2, e3, e4, v, e6, e7⟩
    | 6 => ⟨e0, e1, e2, e3, e4, e5, v, e7⟩
    | 7 => ⟨e0, e1, e2, e3, e4, e5, e6, v⟩
    | _ => ⟨e0, e1, e2, e3, e4, e5, e6, e7⟩

/-- Lookup on `Chunk8.empty` is always `none`. -/
theorem Chunk8.get_empty {α : Type u} (r : Nat) :
    (Chunk8.empty : Chunk8 α).get r = none := by
  cases r with
  | zero => rfl
  | succ r1 =>
    cases r1 with
    | zero => rfl
    | succ r2 =>
      cases r2 with
      | zero => rfl
      | succ r3 =>
        cases r3 with
        | zero => rfl
        | succ r4 =>
          cases r4 with
          | zero => rfl
          | succ r5 =>
            cases r5 with
            | zero => rfl
            | succ r6 =>
              cases r6 with
              | zero => rfl
              | succ r7 =>
                cases r7 <;> rfl

private theorem nat_ge8_contra {r : Nat} (h : r + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 < 8) :
    False :=
  Nat.not_lt_of_ge (Nat.le_add_left 8 r) h

private theorem chunk8_get_ge8 {α : Type u} (c : Chunk8 α) (r : Nat) :
    c.get (r + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = none := rfl

private theorem chunk8_get_set_ge8 {α : Type u} (c : Chunk8 α) (r j : Nat)
    (v : Option α) :
    (c.set r v).get (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) =
      c.get (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) := by
  rw [chunk8_get_ge8, chunk8_get_ge8]

/-- Same-slot read-after-write law for `Chunk8.set` (`r < 8`). -/
theorem Chunk8.get_set_same {α : Type u} (c : Chunk8 α) {r : Nat}
    (v : Option α) (hr : r < 8) :
    (c.set r v).get r = v := by
  cases c with
  | mk e0 e1 e2 e3 e4 e5 e6 e7 =>
    cases r with
    | zero => rfl
    | succ r1 =>
      cases r1 with
      | zero => rfl
      | succ r2 =>
        cases r2 with
        | zero => rfl
        | succ r3 =>
          cases r3 with
          | zero => rfl
          | succ r4 =>
            cases r4 with
            | zero => rfl
            | succ r5 =>
              cases r5 with
              | zero => rfl
              | succ r6 =>
                cases r6 with
                | zero => rfl
                | succ r7 =>
                  cases r7 with
                  | zero => rfl
                  | succ r8 => exact False.elim (nat_ge8_contra hr)

private theorem chunk8_get_set_ne_lt8 {α : Type u} (c : Chunk8 α) {r j : Nat}
    (v : Option α) (hNe : j ≠ r) :
    (c.set r v).get j = c.get j := by
  cases j with
  | zero =>
    cases r with
    | zero => exact False.elim (hNe rfl)
    | succ r1 =>
      cases r1 with
      | zero => cases c; rfl
      | succ r2 =>
        cases r2 with
        | zero => cases c; rfl
        | succ r3 =>
          cases r3 with
          | zero => cases c; rfl
          | succ r4 =>
            cases r4 with
            | zero => cases c; rfl
            | succ r5 =>
              cases r5 with
              | zero => cases c; rfl
              | succ r6 =>
                cases r6 with
                | zero => cases c; rfl
                | succ r7 =>
                  cases r7 with
                  | zero => cases c; rfl
                  | succ _ => cases c; rfl
  | succ j1 =>
    cases j1 with
    | zero =>
      cases r with
      | zero => cases c; rfl
      | succ r1 =>
        cases r1 with
        | zero => exact False.elim (hNe rfl)
        | succ r2 =>
          cases r2 with
          | zero => cases c; rfl
          | succ r3 =>
            cases r3 with
            | zero => cases c; rfl
            | succ r4 =>
              cases r4 with
              | zero => cases c; rfl
              | succ r5 =>
                cases r5 with
                | zero => cases c; rfl
                | succ r6 =>
                  cases r6 with
                  | zero => cases c; rfl
                  | succ r7 =>
                    cases r7 with
                    | zero => cases c; rfl
                    | succ _ => cases c; rfl
    | succ j2 =>
      cases j2 with
      | zero =>
        cases r with
        | zero => cases c; rfl
        | succ r1 =>
          cases r1 with
          | zero => cases c; rfl
          | succ r2 =>
            cases r2 with
            | zero => exact False.elim (hNe rfl)
            | succ r3 =>
              cases r3 with
              | zero => cases c; rfl
              | succ r4 =>
                cases r4 with
                | zero => cases c; rfl
                | succ r5 =>
                  cases r5 with
                  | zero => cases c; rfl
                  | succ r6 =>
                    cases r6 with
                    | zero => cases c; rfl
                    | succ r7 =>
                      cases r7 with
                      | zero => cases c; rfl
                      | succ _ => cases c; rfl
      | succ j3 =>
        cases j3 with
        | zero =>
          cases r with
          | zero => cases c; rfl
          | succ r1 =>
            cases r1 with
            | zero => cases c; rfl
            | succ r2 =>
              cases r2 with
              | zero => cases c; rfl
              | succ r3 =>
                cases r3 with
                | zero => exact False.elim (hNe rfl)
                | succ r4 =>
                  cases r4 with
                  | zero => cases c; rfl
                  | succ r5 =>
                    cases r5 with
                    | zero => cases c; rfl
                    | succ r6 =>
                      cases r6 with
                      | zero => cases c; rfl
                      | succ r7 =>
                        cases r7 with
                        | zero => cases c; rfl
                        | succ _ => cases c; rfl
        | succ j4 =>
          cases j4 with
          | zero =>
            cases r with
            | zero => cases c; rfl
            | succ r1 =>
              cases r1 with
              | zero => cases c; rfl
              | succ r2 =>
                cases r2 with
                | zero => cases c; rfl
                | succ r3 =>
                  cases r3 with
                  | zero => cases c; rfl
                  | succ r4 =>
                    cases r4 with
                    | zero => exact False.elim (hNe rfl)
                    | succ r5 =>
                      cases r5 with
                      | zero => cases c; rfl
                      | succ r6 =>
                        cases r6 with
                        | zero => cases c; rfl
                        | succ r7 =>
                          cases r7 with
                          | zero => cases c; rfl
                          | succ _ => cases c; rfl
          | succ j5 =>
            cases j5 with
            | zero =>
              cases r with
              | zero => cases c; rfl
              | succ r1 =>
                cases r1 with
                | zero => cases c; rfl
                | succ r2 =>
                  cases r2 with
                  | zero => cases c; rfl
                  | succ r3 =>
                    cases r3 with
                    | zero => cases c; rfl
                    | succ r4 =>
                      cases r4 with
                      | zero => cases c; rfl
                      | succ r5 =>
                        cases r5 with
                        | zero => exact False.elim (hNe rfl)
                        | succ r6 =>
                          cases r6 with
                          | zero => cases c; rfl
                          | succ r7 =>
                            cases r7 with
                            | zero => cases c; rfl
                            | succ _ => cases c; rfl
            | succ j6 =>
              cases j6 with
              | zero =>
                cases r with
                | zero => cases c; rfl
                | succ r1 =>
                  cases r1 with
                  | zero => cases c; rfl
                  | succ r2 =>
                    cases r2 with
                    | zero => cases c; rfl
                    | succ r3 =>
                      cases r3 with
                      | zero => cases c; rfl
                      | succ r4 =>
                        cases r4 with
                        | zero => cases c; rfl
                        | succ r5 =>
                          cases r5 with
                          | zero => cases c; rfl
                          | succ r6 =>
                            cases r6 with
                            | zero => exact False.elim (hNe rfl)
                            | succ r7 =>
                              cases r7 with
                              | zero => cases c; rfl
                              | succ _ => cases c; rfl
              | succ j7 =>
                cases j7 with
                | zero =>
                  cases r with
                  | zero => cases c; rfl
                  | succ r1 =>
                    cases r1 with
                    | zero => cases c; rfl
                    | succ r2 =>
                      cases r2 with
                      | zero => cases c; rfl
                      | succ r3 =>
                        cases r3 with
                        | zero => cases c; rfl
                        | succ r4 =>
                          cases r4 with
                          | zero => cases c; rfl
                          | succ r5 =>
                            cases r5 with
                            | zero => cases c; rfl
                            | succ r6 =>
                              cases r6 with
                              | zero => cases c; rfl
                              | succ r7 =>
                                cases r7 with
                                | zero => exact False.elim (hNe rfl)
                                | succ _ => cases c; rfl
                | succ j8 => exact chunk8_get_set_ge8 c r j8 v

/-- Distinct-slot frame law for `Chunk8.set` (`j ≠ r`). -/
theorem Chunk8.get_set_ne {α : Type u} (c : Chunk8 α) {r j : Nat}
    (v : Option α) (hNe : j ≠ r) :
    (c.set r v).get j = c.get j :=
  chunk8_get_set_ne_lt8 c v hNe

/-- Extracts the leading up-to-8 elements of `xs` into a `Chunk8 α` and returns
the remaining suffix (`0` `noncomputable`). -/
def takeChunk8 {α : Type u} (xs : List α) : Chunk8 α × List α :=
  match xs with
  | [] => (Chunk8.empty, [])
  | [x0] => (⟨some x0, none, none, none, none, none, none, none⟩, [])
  | [x0, x1] => (⟨some x0, some x1, none, none, none, none, none, none⟩, [])
  | [x0, x1, x2] =>
    (⟨some x0, some x1, some x2, none, none, none, none, none⟩, [])
  | [x0, x1, x2, x3] =>
    (⟨some x0, some x1, some x2, some x3, none, none, none, none⟩, [])
  | [x0, x1, x2, x3, x4] =>
    (⟨some x0, some x1, some x2, some x3, some x4, none, none, none⟩, [])
  | [x0, x1, x2, x3, x4, x5] =>
    (⟨some x0, some x1, some x2, some x3, some x4, some x5, none, none⟩, [])
  | [x0, x1, x2, x3, x4, x5, x6] =>
    (⟨some x0, some x1, some x2, some x3, some x4, some x5, some x6, none⟩, [])
  | x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest =>
    (⟨some x0, some x1, some x2, some x3, some x4, some x5, some x6, some x7⟩,
      rest)

/-- Fuel-bounded single-pass chunk packer via `@Nat.rec` (`0` `noncomputable`,
`0` `brecOn`), terminating immediately on `[]`. -/
def packChunk8Fuel {α : Type u} (fuel : Nat) : List α → List (Chunk8 α) :=
  @Nat.rec (fun _ => List α → List (Chunk8 α))
    (fun _ => [])
    (fun _ ih xs =>
      match xs with
      | [] => []
      | _ :: _ =>
        let p := takeChunk8 xs
        p.1 :: ih p.2)
    fuel

/-- Packs `xs` into `⌈xs.length / 8⌉` `Chunk8 α` leaves in one linear pass. -/
def packChunk8 {α : Type u} (xs : List α) : List (Chunk8 α) :=
  packChunk8Fuel (Nat.div (compListLength xs + 7) 8) xs

private theorem nat_le_eight_mul_div_add7 (n : Nat) :
    n ≤ 8 * Nat.div (n + 7) 8 := by
  have hdiv : 8 * Nat.div (n + 7) 8 + Nat.mod (n + 7) 8 = n + 7 :=
    Nat.div_add_mod (n + 7) 8
  have hmod : Nat.mod (n + 7) 8 ≤ 7 :=
    Nat.le_of_lt_succ (Nat.mod_lt (n + 7) (Nat.succ_pos 7))
  have hle : 8 * Nat.div (n + 7) 8 + Nat.mod (n + 7) 8 ≤
      8 * Nat.div (n + 7) 8 + 7 :=
    Nat.add_le_add_left hmod (8 * Nat.div (n + 7) 8)
  rw [hdiv] at hle
  exact Nat.le_of_add_le_add_right hle

private theorem packChunk8Fuel_nil {α : Type u} (k : Nat) :
    packChunk8Fuel k ([] : List α) = [] := by
  cases k <;> rfl

private theorem packChunk8Fuel_length_le {α : Type u} :
    ∀ (fuel : Nat) (xs : List α), (packChunk8Fuel fuel xs).length ≤ fuel
  | 0, _ => Nat.le_refl 0
  | _ + 1, [] => Nat.zero_le _
  | k + 1, x :: tl =>
    Nat.succ_le_succ (packChunk8Fuel_length_le k (takeChunk8 (x :: tl)).2)

private theorem nat_div8_eq_zero_iff (idx : Nat) :
    Nat.div idx 8 = 0 → idx = Nat.mod idx 8 := by
  intro hq
  have h : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
  rw [hq, Nat.mul_zero, Nat.zero_add] at h
  exact h.symm

private theorem nat_div8_succ_decomp (idx q : Nat)
    (hq : Nat.div idx 8 = q + 1) :
    idx = (8 * q + Nat.mod idx 8) + 8 ∧
    Nat.div (8 * q + Nat.mod idx 8) 8 = q ∧
    Nat.mod (8 * q + Nat.mod idx 8) 8 = Nat.mod idx 8 := by
  have h : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
  rw [hq, Nat.mul_succ] at h
  have hmod : Nat.mod idx 8 < 8 := Nat.mod_lt idx (Nat.succ_pos 7)
  have hEq : idx = (8 * q + Nat.mod idx 8) + 8 := by
    have hSwap : (8 * q + Nat.mod idx 8) + 8 = 8 * q + 8 + Nat.mod idx 8 := by
      rw [Nat.add_assoc, Nat.add_comm (Nat.mod idx 8) 8, ← Nat.add_assoc]
    exact h.symm.trans hSwap.symm
  have hq' : Nat.div (8 * q + Nat.mod idx 8) 8 = q := by
    have h1 : Nat.div (Nat.mod idx 8 + 8 * q) 8 =
        Nat.div (Nat.mod idx 8) 8 + q := by
      rw [Nat.mul_comm 8 q]
      exact Nat.add_mul_div_right (Nat.mod idx 8) q (Nat.succ_pos 7)
    have hDivZero : Nat.div (Nat.mod idx 8) 8 = 0 := Nat.div_eq_of_lt hmod
    rw [Nat.add_comm (8 * q) (Nat.mod idx 8), h1, hDivZero, Nat.zero_add]
  have hr' : Nat.mod (8 * q + Nat.mod idx 8) 8 = Nat.mod idx 8 := by
    have hdm :
        8 * Nat.div (8 * q + Nat.mod idx 8) 8 +
          Nat.mod (8 * q + Nat.mod idx 8) 8 =
        8 * q + Nat.mod idx 8 :=
      Nat.div_add_mod (8 * q + Nat.mod idx 8) 8
    rw [hq'] at hdm
    exact Nat.add_left_cancel hdm
  exact ⟨hEq, hq', hr'⟩

private theorem takeChunk8_get_lt8 {α : Type u} (xs : List α) (r : Nat)
    (hr : r < 8) :
    (takeChunk8 xs).1.get r = listGet? xs r := by
  cases r with
  | zero =>
    cases xs with
    | nil => rfl
    | cons _ tl =>
      cases tl with
      | nil => rfl
      | cons _ tl2 =>
        cases tl2 with
        | nil => rfl
        | cons _ tl3 =>
          cases tl3 with
          | nil => rfl
          | cons _ tl4 =>
            cases tl4 with
            | nil => rfl
            | cons _ tl5 =>
              cases tl5 with
              | nil => rfl
              | cons _ tl6 =>
                cases tl6 with
                | nil => rfl
                | cons _ tl7 =>
                  cases tl7 <;> rfl
  | succ r1 =>
    cases r1 with
    | zero =>
      cases xs with
      | nil => rfl
      | cons _ tl =>
        cases tl with
        | nil => rfl
        | cons _ tl2 =>
          cases tl2 with
          | nil => rfl
          | cons _ tl3 =>
            cases tl3 with
            | nil => rfl
            | cons _ tl4 =>
              cases tl4 with
              | nil => rfl
              | cons _ tl5 =>
                cases tl5 with
                | nil => rfl
                | cons _ tl6 =>
                  cases tl6 with
                  | nil => rfl
                  | cons _ tl7 => cases tl7 <;> rfl
    | succ r2 =>
      cases r2 with
      | zero =>
        cases xs with
        | nil => rfl
        | cons _ tl =>
          cases tl with
          | nil => rfl
          | cons _ tl2 =>
            cases tl2 with
            | nil => rfl
            | cons _ tl3 =>
              cases tl3 with
              | nil => rfl
              | cons _ tl4 =>
                cases tl4 with
                | nil => rfl
                | cons _ tl5 =>
                  cases tl5 with
                  | nil => rfl
                  | cons _ tl6 =>
                    cases tl6 with
                    | nil => rfl
                    | cons _ tl7 => cases tl7 <;> rfl
      | succ r3 =>
        cases r3 with
        | zero =>
          cases xs with
          | nil => rfl
          | cons _ tl =>
            cases tl with
            | nil => rfl
            | cons _ tl2 =>
              cases tl2 with
              | nil => rfl
              | cons _ tl3 =>
                cases tl3 with
                | nil => rfl
                | cons _ tl4 =>
                  cases tl4 with
                  | nil => rfl
                  | cons _ tl5 =>
                    cases tl5 with
                    | nil => rfl
                    | cons _ tl6 =>
                      cases tl6 with
                      | nil => rfl
                      | cons _ tl7 => cases tl7 <;> rfl
        | succ r4 =>
          cases r4 with
          | zero =>
            cases xs with
            | nil => rfl
            | cons _ tl =>
              cases tl with
              | nil => rfl
              | cons _ tl2 =>
                cases tl2 with
                | nil => rfl
                | cons _ tl3 =>
                  cases tl3 with
                  | nil => rfl
                  | cons _ tl4 =>
                    cases tl4 with
                    | nil => rfl
                    | cons _ tl5 =>
                      cases tl5 with
                      | nil => rfl
                      | cons _ tl6 =>
                        cases tl6 with
                        | nil => rfl
                        | cons _ tl7 => cases tl7 <;> rfl
          | succ r5 =>
            cases r5 with
            | zero =>
              cases xs with
              | nil => rfl
              | cons _ tl =>
                cases tl with
                | nil => rfl
                | cons _ tl2 =>
                  cases tl2 with
                  | nil => rfl
                  | cons _ tl3 =>
                    cases tl3 with
                    | nil => rfl
                    | cons _ tl4 =>
                      cases tl4 with
                      | nil => rfl
                      | cons _ tl5 =>
                        cases tl5 with
                        | nil => rfl
                        | cons _ tl6 =>
                          cases tl6 with
                          | nil => rfl
                          | cons _ tl7 => cases tl7 <;> rfl
            | succ r6 =>
              cases r6 with
              | zero =>
                cases xs with
                | nil => rfl
                | cons _ tl =>
                  cases tl with
                  | nil => rfl
                  | cons _ tl2 =>
                    cases tl2 with
                    | nil => rfl
                    | cons _ tl3 =>
                      cases tl3 with
                      | nil => rfl
                      | cons _ tl4 =>
                        cases tl4 with
                        | nil => rfl
                        | cons _ tl5 =>
                          cases tl5 with
                          | nil => rfl
                          | cons _ tl6 =>
                            cases tl6 with
                            | nil => rfl
                            | cons _ tl7 => cases tl7 <;> rfl
              | succ r7 =>
                cases r7 with
                | zero =>
                  cases xs with
                  | nil => rfl
                  | cons _ tl =>
                    cases tl with
                    | nil => rfl
                    | cons _ tl2 =>
                      cases tl2 with
                      | nil => rfl
                      | cons _ tl3 =>
                        cases tl3 with
                        | nil => rfl
                        | cons _ tl4 =>
                          cases tl4 with
                          | nil => rfl
                          | cons _ tl5 =>
                            cases tl5 with
                            | nil => rfl
                            | cons _ tl6 =>
                              cases tl6 with
                              | nil => rfl
                              | cons _ tl7 => cases tl7 <;> rfl
                | succ r8 => exact False.elim (nat_ge8_contra hr)

private theorem getElem?_packChunk8Fuel {α : Type u} :
    ∀ (fuel : Nat) (xs : List α),
      xs.length ≤ 8 * fuel →
      ∀ idx : Nat,
        (match listGet? (packChunk8Fuel fuel xs)
            (Nat.div idx 8) with
         | some c => c.get (Nat.mod idx 8)
         | none => none) =
        listGet? xs idx
  | 0, [], _, idx => by
    cases idx <;> rfl
  | 0, _ :: _, hBound, _ =>
    False.elim (Nat.not_lt_of_ge hBound (Nat.succ_pos _))
  | k + 1, [], _, idx => by
    cases idx <;> rfl
  | k + 1, x :: tl, hBound, idx => by
    let xs := x :: tl
    cases hq : Nat.div idx 8 with
    | zero =>
      have hidx := nat_div8_eq_zero_iff idx hq
      have hr : Nat.mod idx 8 < 8 := Nat.mod_lt idx (Nat.succ_pos 7)
      change (takeChunk8 xs).1.get (Nat.mod idx 8) =
        listGet? xs idx
      rw [takeChunk8_get_lt8 xs (Nat.mod idx 8) hr, ← hidx]
    | succ q' =>
      have hd := nat_div8_succ_decomp idx q' hq
      cases tl with
      | nil =>
        change (match listGet? (packChunk8Fuel k []) q' with
            | some c => c.get (Nat.mod idx 8)
            | none => none) = listGet? [x] idx
        rw [packChunk8Fuel_nil k, hd.1]; rfl
      | cons x1 tl1 =>
        cases tl1 with
        | nil =>
          change (match listGet? (packChunk8Fuel k []) q' with
              | some c => c.get (Nat.mod idx 8)
              | none => none) = listGet? [x, x1] idx
          rw [packChunk8Fuel_nil k, hd.1]; rfl
        | cons x2 tl2 =>
          cases tl2 with
          | nil =>
            change (match listGet? (packChunk8Fuel k []) q' with
                | some c => c.get (Nat.mod idx 8)
                | none => none) =
              listGet? [x, x1, x2] idx
            rw [packChunk8Fuel_nil k, hd.1]; rfl
          | cons x3 tl3 =>
            cases tl3 with
            | nil =>
              change (match listGet? (packChunk8Fuel k []) q' with
                  | some c => c.get (Nat.mod idx 8)
                  | none => none) =
                listGet? [x, x1, x2, x3] idx
              rw [packChunk8Fuel_nil k, hd.1]; rfl
            | cons x4 tl4 =>
              cases tl4 with
              | nil =>
                change (match listGet? (packChunk8Fuel k []) q' with
                    | some c => c.get (Nat.mod idx 8)
                    | none => none) =
                  listGet? [x, x1, x2, x3, x4] idx
                rw [packChunk8Fuel_nil k, hd.1]; rfl
              | cons x5 tl5 =>
                cases tl5 with
                | nil =>
                  change (match listGet? (packChunk8Fuel k []) q' with
                      | some c => c.get (Nat.mod idx 8)
                      | none => none) =
                    listGet? [x, x1, x2, x3, x4, x5] idx
                  rw [packChunk8Fuel_nil k, hd.1]; rfl
                | cons x6 tl6 =>
                  cases tl6 with
                  | nil =>
                    change (match listGet? (packChunk8Fuel k []) q' with
                        | some c => c.get (Nat.mod idx 8)
                        | none => none) =
                      listGet?
                        [x, x1, x2, x3, x4, x5, x6] idx
                    rw [packChunk8Fuel_nil k, hd.1]; rfl
                  | cons x7 rest =>
                    have hRestBound : rest.length ≤ 8 * k := by
                      have hLen :
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest).length =
                            rest.length + 8 := rfl
                      rw [hLen, Nat.mul_succ] at hBound
                      exact Nat.le_of_add_le_add_right hBound
                    have ih := getElem?_packChunk8Fuel k rest hRestBound
                      (8 * q' + Nat.mod idx 8)
                    rw [hd.2.1, hd.2.2] at ih
                    change (match listGet?
                        (packChunk8Fuel k rest) q' with
                        | some c => c.get (Nat.mod idx 8)
                        | none => none) =
                      listGet?
                        (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) idx
                    have hStep8 :
                        listGet?
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
                          ((8 * q' + Nat.mod idx 8) + 8) =
                        listGet? rest
                          (8 * q' + Nat.mod idx 8) := rfl
                    have hRhs :
                        listGet?
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest)
                          idx =
                        listGet? rest
                          (8 * q' + Nat.mod idx 8) :=
                      (congrArg
                        (listGet?
                          (x :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest))
                        hd.1).trans hStep8
                    rw [hRhs]
                    exact ih

/-- Balanced dense binary spine storing `Chunk8 α` leaves (`0` `Option` leaf
wrapper overhead). -/
inductive Chunk8Tree (α : Type u) : Type u where
  | empty : Chunk8Tree α
  | leaf : Chunk8 α → Chunk8Tree α
  | node : Chunk8Tree α → Chunk8Tree α → Chunk8Tree α

private def natMax2 (a b : Nat) : Nat :=
  cond (Nat.ble a b) b a

private theorem natMax2_le {a b c : Nat} (ha : a ≤ c) (hb : b ≤ c) :
    natMax2 a b ≤ c := by
  unfold natMax2
  cases Nat.ble a b with
  | true => exact hb
  | false => exact ha

/-- Fuel-bounded constructor height of a `Chunk8Tree α` via `@Nat.rec` (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`). -/
def Chunk8Tree.heightAt {α : Type u} (fuel : Nat) : Chunk8Tree α → Nat :=
  @Nat.rec (fun _ => Chunk8Tree α → Nat)
    (fun _ => 0)
    (fun _ ih t =>
      match t with
      | .empty => 0
      | .leaf _ => 1
      | .node l r => natMax2 (ih l) (ih r) + 1)
    fuel

/-- Builds a balanced `Chunk8Tree α` of spine depth `depth` directly from a
packed `List (Chunk8 α)` via single-pass even/odd splitting (`0`
`noncomputable`, `0` `._unsafe_rec`, `hasIR = true`). -/
def chunk8TreeFromChunksAt {α : Type u} (depth : Nat) :
    List (Chunk8 α) → Chunk8Tree α :=
  @Nat.rec (fun _ => List (Chunk8 α) → Chunk8Tree α)
    (fun cs =>
      match cs with
      | [] => .empty
      | c :: _ => .leaf c)
    (fun _ ih cs =>
      match cs with
      | [] => .empty
      | _ :: _ =>
        let eo := unzipEvenOdd cs
        .node (ih eo.1) (ih eo.2))
    depth

/-- Height of `chunk8TreeFromChunksAt depth cs` is bounded unconditionally by
`depth + 1` at every fuel budget `fuel`. -/
theorem chunk8TreeFromChunksAt_height_le {α : Type u} :
    ∀ (fuel depth : Nat) (cs : List (Chunk8 α)),
      (chunk8TreeFromChunksAt depth cs).heightAt fuel ≤ depth + 1
  | 0, depth, _ => Nat.zero_le (depth + 1)
  | _ + 1, 0, [] => Nat.zero_le 1
  | _ + 1, 0, _ :: _ => Nat.le_refl 1
  | _ + 1, d + 1, [] => Nat.zero_le (d + 2)
  | f + 1, d + 1, c :: tl => by
    change natMax2
        ((chunk8TreeFromChunksAt d (unzipEvenOdd (c :: tl)).1).heightAt f)
        ((chunk8TreeFromChunksAt d (unzipEvenOdd (c :: tl)).2).heightAt f) + 1 ≤
      (d + 1) + 1
    exact Nat.succ_le_succ
      (natMax2_le
        (chunk8TreeFromChunksAt_height_le f d (unzipEvenOdd (c :: tl)).1)
        (chunk8TreeFromChunksAt_height_le f d (unzipEvenOdd (c :: tl)).2))

/-- Looks up an entire `Chunk8 α` leaf at `chunkIdx` in `O(depth)` spine steps
using `cond` (zero `@ite`/`Decidable` overhead). -/
def chunk8TreeLookupChunkAt {α : Type u} (depth : Nat) :
    Chunk8Tree α → Nat → Option (Chunk8 α) :=
  @Nat.rec (fun _ => Chunk8Tree α → Nat → Option (Chunk8 α))
    (fun t chunkIdx =>
      match t with
      | .empty => none
      | .leaf c => cond (Nat.beq chunkIdx 0) (some c) none
      | .node _ _ => none)
    (fun _ ih t chunkIdx =>
      match t with
      | .empty => none
      | .leaf _ => none
      | .node l r =>
        cond (Nat.beq (Nat.mod chunkIdx 2) 0)
          (ih l (Nat.div chunkIdx 2))
          (ih r (Nat.div chunkIdx 2)))
    depth

private theorem chunk8TreeLookupChunkAt_empty {α : Type u} (depth chunkIdx : Nat) :
    chunk8TreeLookupChunkAt depth (.empty : Chunk8Tree α) chunkIdx = none := by
  cases depth <;> rfl

/-- Exact chunk lookup equivalence between `chunk8TreeLookupChunkAt` and
`listGet? cs chunkIdx` whenever `cs.length ≤ pow2 depth`.
-/
theorem chunk8TreeLookupChunkAt_fromChunksAt {α : Type u} :
    ∀ (depth : Nat) (cs : List (Chunk8 α)),
      cs.length ≤ pow2 depth →
      ∀ chunkIdx : Nat,
        chunk8TreeLookupChunkAt depth (chunk8TreeFromChunksAt depth cs)
            chunkIdx =
          listGet? cs chunkIdx
  | 0, [], _, chunkIdx => by
    cases chunkIdx <;> rfl
  | 0, [c], _, chunkIdx => by
    cases chunkIdx <;> rfl
  | 0, _ :: _ :: tl, hBound, _ => by
    rw [pow2_zero] at hBound
    exact False.elim
      (Nat.not_lt_of_ge hBound (Nat.succ_lt_succ (Nat.succ_pos tl.length)))
  | d + 1, [], _, chunkIdx => by
    change (none : Option (Chunk8 α)) =
      listGet? [] chunkIdx
    cases chunkIdx <;> rfl
  | d + 1, c :: tl, hBound, chunkIdx => by
    let cs := c :: tl
    have hLen := length_unzipEvenOdd_bounds cs
    rw [pow2_succ] at hBound
    have hSub2 : (unzipEvenOdd cs).2.length ≤ pow2 d := by
      have h2 : 2 * (unzipEvenOdd cs).2.length ≤ 2 * pow2 d :=
        Nat.le_trans hLen.2 hBound
      exact Nat.le_of_mul_le_mul_left h2 (Nat.succ_pos 1)
    have hSub1 : (unzipEvenOdd cs).1.length ≤ pow2 d := by
      cases Nat.lt_or_ge (pow2 d) (unzipEvenOdd cs).1.length with
      | inr hle => exact hle
      | inl hgt =>
        have hMulGe : 2 * (pow2 d + 1) ≤ 2 * (unzipEvenOdd cs).1.length :=
          Nat.mul_le_mul_left 2 hgt
        rw [Nat.mul_succ] at hMulGe
        have hUpper : 2 * (unzipEvenOdd cs).1.length ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hLen.1 (Nat.succ_le_succ hBound)
        have hContra : 2 * pow2 d + 2 ≤ 2 * pow2 d + 1 :=
          Nat.le_trans hMulGe hUpper
        exact False.elim
          (Nat.not_lt_of_ge hContra (Nat.lt_succ_self (2 * pow2 d + 1)))
    change
      cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (chunk8TreeLookupChunkAt d
          (chunk8TreeFromChunksAt d (unzipEvenOdd cs).1) (Nat.div chunkIdx 2))
        (chunk8TreeLookupChunkAt d
          (chunk8TreeFromChunksAt d (unzipEvenOdd cs).2) (Nat.div chunkIdx 2)) =
      listGet? cs chunkIdx
    have hde := nat_div2_decomp chunkIdx
    cases hbeq : Nat.beq (Nat.mod chunkIdx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 = chunkIdx at hde
      dsimp only [cond]
      rw [chunk8TreeLookupChunkAt_fromChunksAt d (unzipEvenOdd cs).1 hSub1
            (Nat.div chunkIdx 2),
          (getElem?_unzipEvenOdd cs (Nat.div chunkIdx 2)).1, hde]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 + 1 = chunkIdx at hde
      dsimp only [cond]
      rw [chunk8TreeLookupChunkAt_fromChunksAt d (unzipEvenOdd cs).2 hSub2
            (Nat.div chunkIdx 2),
          (getElem?_unzipEvenOdd cs (Nat.div chunkIdx 2)).2, hde]

/-- Single-pass `O(depth)` functional update of slot `(chunkIdx, rem)` in a
`Chunk8Tree α`, allocating missing spine nodes and `Chunk8.empty` leaves on
demand (`0` `noncomputable`). -/
def chunk8TreeModifyAt {α : Type u} (depth : Nat) :
    Chunk8Tree α → Nat → Nat → Option α → Chunk8Tree α :=
  @Nat.rec (fun _ => Chunk8Tree α → Nat → Nat → Option α → Chunk8Tree α)
    (fun t chunkIdx rem v =>
      cond (Nat.beq chunkIdx 0)
        (let c := match t with | .leaf c0 => c0 | .empty | .node _ _ => Chunk8.empty
         .leaf (c.set rem v))
        t)
    (fun _ ih t chunkIdx rem v =>
      let (l, r) : Chunk8Tree α × Chunk8Tree α :=
        match t with
        | .node l0 r0 => (l0, r0)
        | .empty | .leaf _ => (.empty, .empty)
      cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (.node (ih l (Nat.div chunkIdx 2) rem v) r)
        (.node l (ih r (Nat.div chunkIdx 2) rem v)))
    depth

/-- Looks up element `idx` inside a depth-`depth` `Chunk8Tree α` in
`O(depth)` spine steps plus one `O(1)` `Chunk8.get` dispatch. -/
def chunk8TreeGetAt {α : Type u} (depth : Nat) (t : Chunk8Tree α) (idx : Nat) :
    Option α :=
  match chunk8TreeLookupChunkAt depth t (Nat.div idx 8) with
  | some c => c.get (Nat.mod idx 8)
  | none => none

private theorem chunk8TreeLookupChunkAt_modify_same {α : Type u}
    (depth : Nat) (t : Chunk8Tree α) (chunkIdx rem : Nat) (v : Option α)
    (hc : chunkIdx < pow2 depth) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeModifyAt depth t chunkIdx rem v) chunkIdx =
      some ((match chunk8TreeLookupChunkAt depth t chunkIdx with
             | some c0 => c0
             | none => Chunk8.empty).set rem v) := by
  revert t chunkIdx
  induction depth with
  | zero =>
    intro t chunkIdx hc
    rw [pow2_zero] at hc
    have h0 : chunkIdx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hc)
    subst h0
    cases t <;> rfl
  | succ d ih =>
    intro t chunkIdx hc
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hc
    have hhalf : Nat.div chunkIdx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hc
    cases t with
    | empty | leaf _ =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              .empty)
            (.node .empty
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)))
          chunkIdx = some (Chunk8.empty.set rem v)
      cases hpar : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d .empty (Nat.div chunkIdx 2)) =
          some (Chunk8.empty.set rem v)
        rw [hpar]
        dsimp only [cond]
        rw [ih .empty (Nat.div chunkIdx 2) hhalf,
          chunk8TreeLookupChunkAt_empty d (Nat.div chunkIdx 2)]
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d .empty (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2)) =
          some (Chunk8.empty.set rem v)
        rw [hpar]
        dsimp only [cond]
        rw [ih .empty (Nat.div chunkIdx 2) hhalf,
          chunk8TreeLookupChunkAt_empty d (Nat.div chunkIdx 2)]
    | node l r =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v) r)
            (.node l (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v)))
          chunkIdx =
        some ((match cond (Nat.beq (Nat.mod chunkIdx 2) 0)
                  (chunk8TreeLookupChunkAt d l (Nat.div chunkIdx 2))
                  (chunk8TreeLookupChunkAt d r (Nat.div chunkIdx 2)) with
               | some c0 => c0
               | none => Chunk8.empty).set rem v)
      cases hpar : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d r (Nat.div chunkIdx 2)) = _
        rw [hpar]
        dsimp only [cond]
        exact ih l (Nat.div chunkIdx 2) hhalf
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (chunk8TreeLookupChunkAt d l (Nat.div chunkIdx 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v)
              (Nat.div chunkIdx 2)) = _
        rw [hpar]
        dsimp only [cond]
        exact ih r (Nat.div chunkIdx 2) hhalf

private theorem chunk8TreeLookupChunkAt_modify_ne {α : Type u}
    (depth : Nat) (t : Chunk8Tree α) (chunkIdx q rem : Nat) (v : Option α)
    (hNe : q ≠ chunkIdx) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeModifyAt depth t chunkIdx rem v) q =
      chunk8TreeLookupChunkAt depth t q := by
  revert t chunkIdx q
  induction depth with
  | zero =>
    intro t chunkIdx q hNe
    change chunk8TreeLookupChunkAt 0
        (cond (Nat.beq chunkIdx 0)
          (.leaf ((match t with | .leaf c0 => c0 | .empty | .node _ _ => Chunk8.empty).set rem v))
          t) q =
      chunk8TreeLookupChunkAt 0 t q
    cases hIdx : Nat.beq chunkIdx 0 with
    | false => rfl
    | true =>
      have h0 : chunkIdx = 0 := natEq_of_beq chunkIdx 0 hIdx
      subst h0
      have hq0 : Nat.beq q 0 = false := natBeq_false_of_ne hNe
      dsimp only [cond]
      cases t with
      | empty =>
        change cond (Nat.beq q 0) _ none = none
        rw [hq0]; rfl
      | leaf c0 =>
        change cond (Nat.beq q 0) _ none = cond (Nat.beq q 0) (some c0) none
        rw [hq0]; rfl
      | node _ _ =>
        change cond (Nat.beq q 0) _ none = none
        rw [hq0]; rfl
  | succ d ih =>
    intro t chunkIdx q hNe
    have hDivNe :
        Nat.beq (Nat.mod q 2) 0 = Nat.beq (Nat.mod chunkIdx 2) 0 →
        Nat.div q 2 ≠ Nat.div chunkIdx 2 := by
      intro hParEq hDivEq
      have hdq := nat_div2_decomp q
      have hdc := nat_div2_decomp chunkIdx
      cases hp : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        rw [hp] at hParEq hdc
        rw [hParEq] at hdq
        change 2 * Nat.div q 2 = q at hdq
        change 2 * Nat.div chunkIdx 2 = chunkIdx at hdc
        rw [hDivEq, hdc] at hdq
        exact hNe hdq.symm
      | false =>
        rw [hp] at hParEq hdc
        rw [hParEq] at hdq
        change 2 * Nat.div q 2 + 1 = q at hdq
        change 2 * Nat.div chunkIdx 2 + 1 = chunkIdx at hdc
        rw [hDivEq, hdc] at hdq
        exact hNe hdq.symm
    cases t with
    | empty | leaf _ =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              .empty)
            (.node .empty
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v))) q =
        none
      cases hpi : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2))
            (chunk8TreeLookupChunkAt d .empty (Nat.div q 2)) = none
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true =>
          dsimp only [cond]
          rw [ih .empty (Nat.div chunkIdx 2) (Nat.div q 2)
                (hDivNe (hpq.trans hpi.symm)),
              chunk8TreeLookupChunkAt_empty]
        | false =>
          dsimp only [cond]
          exact chunk8TreeLookupChunkAt_empty d (Nat.div q 2)
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d .empty (Nat.div q 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d .empty (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2)) = none
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true =>
          dsimp only [cond]
          exact chunk8TreeLookupChunkAt_empty d (Nat.div q 2)
        | false =>
          dsimp only [cond]
          rw [ih .empty (Nat.div chunkIdx 2) (Nat.div q 2)
                (hDivNe (hpq.trans hpi.symm)),
              chunk8TreeLookupChunkAt_empty]
    | node l r =>
      change chunk8TreeLookupChunkAt (d + 1)
          (cond (Nat.beq (Nat.mod chunkIdx 2) 0)
            (.node (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v) r)
            (.node l (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v))) q =
        cond (Nat.beq (Nat.mod q 2) 0)
          (chunk8TreeLookupChunkAt d l (Nat.div q 2))
          (chunk8TreeLookupChunkAt d r (Nat.div q 2))
      cases hpi : Nat.beq (Nat.mod chunkIdx 2) 0 with
      | true =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d l (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2))
            (chunk8TreeLookupChunkAt d r (Nat.div q 2)) = _
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true =>
          dsimp only [cond]
          exact ih l (Nat.div chunkIdx 2) (Nat.div q 2)
            (hDivNe (hpq.trans hpi.symm))
        | false => rfl
      | false =>
        dsimp only [cond]
        change cond (Nat.beq (Nat.mod q 2) 0)
            (chunk8TreeLookupChunkAt d l (Nat.div q 2))
            (chunk8TreeLookupChunkAt d
              (chunk8TreeModifyAt d r (Nat.div chunkIdx 2) rem v)
              (Nat.div q 2)) = _
        cases hpq : Nat.beq (Nat.mod q 2) 0 with
        | true => rfl
        | false =>
          dsimp only [cond]
          exact ih r (Nat.div chunkIdx 2) (Nat.div q 2)
            (hDivNe (hpq.trans hpi.symm))

/-- Pure-data dense `Chunk8` balanced lookup table (`0` `Prop` fields) unifying
dense block tables, chunked binary trees, and boolean live-local masks. -/
structure Chunk8BlockTree (α : Type u) where
  depth : Nat
  tree : Chunk8Tree α

/-- Tabulates `xs` into a `Chunk8BlockTree α` at explicit spine depth `depth`.
-/
def Chunk8BlockTree.ofListAt {α : Type u} (xs : List α) (depth : Nat) :
    Chunk8BlockTree α :=
  { depth := depth, tree := chunk8TreeFromChunksAt depth (packChunk8 xs) }

/-- Tabulates `xs` into a `Chunk8BlockTree α` at minimal logarithmic spine
depth `compLog2Depth (Nat.div (compListLength xs + 7) 8)`. -/
def Chunk8BlockTree.ofList {α : Type u} (xs : List α) : Chunk8BlockTree α :=
  let chunks := packChunk8 xs
  { depth := compLog2Depth (compListLength chunks)
    tree := chunk8TreeFromChunksAt (compLog2Depth (compListLength chunks))
      chunks }

/-- Looks up an entire 8-element `Chunk8 α` leaf at `chunkIdx` in one spine
traversal (`O(bt.depth)`), enabling stride-8 batch inspection. -/
def Chunk8BlockTree.lookupChunk {α : Type u} (bt : Chunk8BlockTree α)
    (chunkIdx : Nat) : Option (Chunk8 α) :=
  chunk8TreeLookupChunkAt bt.depth bt.tree chunkIdx

/-- Looks up element `idx` in `bt` in `O(bt.depth)` spine steps plus one `O(1)`
`Chunk8.get` dispatch. -/
def Chunk8BlockTree.lookup? {α : Type u} (bt : Chunk8BlockTree α) (idx : Nat) :
    Option α :=
  chunk8TreeGetAt bt.depth bt.tree idx

/-- Functionally updates element `idx` in `bt` in `O(bt.depth)` spine steps. -/
def Chunk8BlockTree.modify {α : Type u} (bt : Chunk8BlockTree α) (idx : Nat)
    (v : Option α) : Chunk8BlockTree α :=
  { depth := bt.depth
    tree := chunk8TreeModifyAt bt.depth bt.tree (Nat.div idx 8)
      (Nat.mod idx 8) v }

/-- Validity predicate tying a pure-data `Chunk8BlockTree α` back to `xs`. -/
def ValidChunk8BlockTree {α : Type u} (xs : List α) (bt : Chunk8BlockTree α) :
    Prop :=
  xs.length ≤ 8 * pow2 bt.depth ∧
  ∀ idx : Nat, bt.lookup? idx = listGet? xs idx

private theorem getElem?_ne_none_of_lt {α : Type u} :
    ∀ (xs : List α) (k : Nat),
      k < xs.length → listGet? xs k ≠ none
  | [], _, h => False.elim (Nat.not_lt_zero _ h)
  | _ :: _, 0, _ => fun h => by cases h
  | _ :: tl, k + 1, h => getElem?_ne_none_of_lt tl k (Nat.lt_of_succ_lt_succ h)

/-- `Chunk8BlockTree.ofListAt xs depth` is valid whenever
`(packChunk8 xs).length ≤ pow2 depth`. -/
theorem valid_chunk8BlockTree_ofListAt {α : Type u} (xs : List α) (depth : Nat)
    (hChunks : (packChunk8 xs).length ≤ pow2 depth) :
    ValidChunk8BlockTree xs (Chunk8BlockTree.ofListAt xs depth) := by
  have hFuelBound : xs.length ≤ 8 * Nat.div (compListLength xs + 7) 8 := by
    rw [compListLength_eq xs]
    exact nat_le_eight_mul_div_add7 xs.length
  have hLen : xs.length ≤ 8 * pow2 depth := by
    have hPackLe : xs.length ≤ 8 * (packChunk8 xs).length := by
      cases Nat.lt_or_ge (8 * (packChunk8 xs).length) xs.length with
      | inr hle => exact hle
      | inl hlt =>
        have hGet := getElem?_packChunk8Fuel (Nat.div (compListLength xs + 7) 8)
          xs hFuelBound (8 * (packChunk8 xs).length)
        have hDiv : Nat.div (8 * (packChunk8 xs).length) 8 =
            (packChunk8 xs).length := by
          have hMul : Nat.div ((packChunk8 xs).length * 8) 8 =
              (packChunk8 xs).length :=
            Nat.mul_div_cancel (packChunk8 xs).length (Nat.succ_pos 7)
          rw [Nat.mul_comm 8 _]
          exact hMul
        change (match listGet? (packChunk8 xs)
            (Nat.div (8 * (packChunk8 xs).length) 8) with
          | some c => c.get (Nat.mod (8 * (packChunk8 xs).length) 8)
          | none => none) =
          listGet? xs (8 * (packChunk8 xs).length) at hGet
        rw [hDiv, listGet?_eq_none_of_le (packChunk8 xs) _ (Nat.le_refl _)]
          at hGet
        exact False.elim (getElem?_ne_none_of_lt xs _ hlt hGet.symm)
    exact Nat.le_trans hPackLe (Nat.mul_le_mul_left 8 hChunks)
  refine ⟨hLen, fun idx => ?_⟩
  unfold Chunk8BlockTree.lookup? Chunk8BlockTree.ofListAt chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_fromChunksAt depth (packChunk8 xs) hChunks
    (Nat.div idx 8)]
  exact getElem?_packChunk8Fuel (Nat.div (compListLength xs + 7) 8) xs
    hFuelBound idx

/-- `Chunk8BlockTree.ofList xs` is unconditionally valid for every `xs`. -/
theorem valid_chunk8BlockTree_ofList {α : Type u} (xs : List α) :
    ValidChunk8BlockTree xs (Chunk8BlockTree.ofList xs) := by
  have hChunks :
      (packChunk8 xs).length ≤ pow2 (compLog2Depth (compListLength (packChunk8 xs))) := by
    rw [compListLength_eq (packChunk8 xs)]
    exact le_pow2_compLog2Depth (packChunk8 xs).length
  exact valid_chunk8BlockTree_ofListAt xs
    (compLog2Depth (compListLength (packChunk8 xs))) hChunks

/-- Premise-free lookup equivalence for `Chunk8BlockTree.ofList xs`. -/
theorem Chunk8BlockTree.ofList_lookup_eq {α : Type u} (xs : List α) (idx : Nat) :
    (Chunk8BlockTree.ofList xs).lookup? idx =
      listGet? xs idx :=
  (valid_chunk8BlockTree_ofList xs).2 idx

/-- Spine height bound for `Chunk8BlockTree.ofList xs`:
`(Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤ depth + 1` for every `fuel`.
-/
theorem Chunk8BlockTree.ofList_height_le {α : Type u} (xs : List α) (fuel : Nat) :
    (Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤
      (Chunk8BlockTree.ofList xs).depth + 1 :=
  chunk8TreeFromChunksAt_height_le fuel _ (packChunk8 xs)

/-- Same-index read-after-modify law for `Chunk8BlockTree.modify`
(`idx < 8 * pow2 bt.depth`). -/
theorem Chunk8BlockTree.lookup_modify_same {α : Type u}
    (bt : Chunk8BlockTree α) (idx : Nat) (v : Option α)
    (hidx : idx < 8 * pow2 bt.depth) :
    (bt.modify idx v).lookup? idx = v := by
  have hc : Nat.div idx 8 < pow2 bt.depth := by
    rw [Nat.mul_comm 8 (pow2 bt.depth)] at hidx
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos 7)).mpr hidx
  unfold Chunk8BlockTree.lookup? Chunk8BlockTree.modify chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_modify_same bt.depth bt.tree (Nat.div idx 8)
    (Nat.mod idx 8) v hc]
  exact Chunk8.get_set_same _ v (Nat.mod_lt idx (Nat.succ_pos 7))

/-- Distinct-index frame law for `Chunk8BlockTree.modify` (`j ≠ idx`). -/
theorem Chunk8BlockTree.lookup_modify_ne {α : Type u}
    (bt : Chunk8BlockTree α) (idx j : Nat) (v : Option α) (hNe : j ≠ idx) :
    (bt.modify idx v).lookup? j = bt.lookup? j := by
  unfold Chunk8BlockTree.lookup? Chunk8BlockTree.modify chunk8TreeGetAt
  dsimp only
  cases hq : Nat.beq (Nat.div j 8) (Nat.div idx 8) with
  | false =>
    have hqNe : Nat.div j 8 ≠ Nat.div idx 8 := fun hEq => by
      rw [hEq, natBeq_refl] at hq
      exact boolFalseNeTrue hq.symm
    rw [chunk8TreeLookupChunkAt_modify_ne bt.depth bt.tree (Nat.div idx 8)
      (Nat.div j 8) (Nat.mod idx 8) v hqNe]
  | true =>
    have hqEq : Nat.div j 8 = Nat.div idx 8 := natEq_of_beq _ _ hq
    have hrNe : Nat.mod j 8 ≠ Nat.mod idx 8 := fun hrEq => by
      have hj : 8 * Nat.div j 8 + Nat.mod j 8 = j := Nat.div_add_mod j 8
      have hi : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
      rw [hqEq, hrEq, hi] at hj
      exact hNe hj.symm
    cases Nat.lt_or_ge (Nat.div idx 8) (pow2 bt.depth) with
    | inl hc =>
      rw [hqEq,
        chunk8TreeLookupChunkAt_modify_same bt.depth bt.tree (Nat.div idx 8)
          (Nat.mod idx 8) v hc]
      dsimp only
      rw [Chunk8.get_set_ne _ v hrNe]
      cases chunk8TreeLookupChunkAt bt.depth bt.tree (Nat.div idx 8) with
      | some _ => rfl
      | none => exact Chunk8.get_empty (Nat.mod j 8)
    | inr hge =>
      -- Out-of-bounds chunks beyond `pow2 bt.depth` evaluate to `none`.
      have hModOob :
          ∀ (d : Nat) (t : Chunk8Tree α) (ci r : Nat),
            pow2 d ≤ ci →
            chunk8TreeLookupChunkAt d (chunk8TreeModifyAt d t ci r v) ci =
              chunk8TreeLookupChunkAt d t ci := by
        intro d
        induction d with
        | zero =>
          intro t ci r hOob
          rw [pow2_zero] at hOob
          cases ci with
          | zero => exact False.elim (Nat.not_lt_of_ge hOob Nat.zero_lt_one)
          | succ _ => rfl
        | succ d' ih =>
          intro t ci r hOob
          rw [pow2_succ, Nat.mul_comm 2 (pow2 d')] at hOob
          have hhalf : pow2 d' ≤ Nat.div ci 2 :=
            (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hOob
          cases t with
          | empty | leaf _ =>
            change chunk8TreeLookupChunkAt (d' + 1)
                (cond (Nat.beq (Nat.mod ci 2) 0)
                  (.node (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v)
                    .empty)
                  (.node .empty
                    (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v))) ci =
              none
            cases hpar : Nat.beq (Nat.mod ci 2) 0 with
            | true =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v)
                    (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d' .empty (Nat.div ci 2)) = none
              rw [hpar]
              dsimp only [cond]
              rw [ih .empty (Nat.div ci 2) r hhalf,
                chunk8TreeLookupChunkAt_empty]
            | false =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d' .empty (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' .empty (Nat.div ci 2) r v)
                    (Nat.div ci 2)) = none
              rw [hpar]
              dsimp only [cond]
              rw [ih .empty (Nat.div ci 2) r hhalf,
                chunk8TreeLookupChunkAt_empty]
          | node l r0 =>
            change chunk8TreeLookupChunkAt (d' + 1)
                (cond (Nat.beq (Nat.mod ci 2) 0)
                  (.node (chunk8TreeModifyAt d' l (Nat.div ci 2) r v) r0)
                  (.node l (chunk8TreeModifyAt d' r0 (Nat.div ci 2) r v))) ci =
              cond (Nat.beq (Nat.mod ci 2) 0)
                (chunk8TreeLookupChunkAt d' l (Nat.div ci 2))
                (chunk8TreeLookupChunkAt d' r0 (Nat.div ci 2))
            cases hpar : Nat.beq (Nat.mod ci 2) 0 with
            | true =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' l (Nat.div ci 2) r v) (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d' r0 (Nat.div ci 2)) = _
              rw [hpar]
              dsimp only [cond]
              exact ih l (Nat.div ci 2) r hhalf
            | false =>
              dsimp only [cond]
              change cond (Nat.beq (Nat.mod ci 2) 0)
                  (chunk8TreeLookupChunkAt d' l (Nat.div ci 2))
                  (chunk8TreeLookupChunkAt d'
                    (chunk8TreeModifyAt d' r0 (Nat.div ci 2) r v) (Nat.div ci 2)) = _
              rw [hpar]
              dsimp only [cond]
              exact ih r0 (Nat.div ci 2) r hhalf
      rw [hqEq, hModOob bt.depth bt.tree (Nat.div idx 8) (Nat.mod idx 8) hge]

/-- `Chunk8BlockTree.modify idx (some val)` preserves `ValidChunk8BlockTree`
across `listSet?`. -/
theorem Chunk8BlockTree.valid_modify_of_setElem? {α : Type u} {xs xs' : List α}
    {bt : Chunk8BlockTree α} {idx : Nat} {val : α}
    (hValid : ValidChunk8BlockTree xs bt)
    (hSet : listSet? xs idx val = some xs') :
    ValidChunk8BlockTree xs' (bt.modify idx (some val)) := by
  have hLtLen := listSet?_lt_and_length hSet
  have hIdxBound : idx < 8 * pow2 bt.depth :=
    Nat.lt_of_lt_of_le hLtLen.1 hValid.1
  refine ⟨?_, fun j => ?_⟩
  · unfold Chunk8BlockTree.modify
    dsimp only
    rw [hLtLen.2]
    exact hValid.1
  · cases hBeq : Nat.beq j idx with
    | true =>
      have hEq : j = idx := natEq_of_beq j idx hBeq
      subst hEq
      rw [Chunk8BlockTree.lookup_modify_same bt j (some val) hIdxBound,
        listGet?_listSet?_same hSet]
    | false =>
      have hNe : j ≠ idx := fun hEq => by
        subst hEq
        rw [natBeq_refl j] at hBeq
        exact boolFalseNeTrue hBeq.symm
      rw [Chunk8BlockTree.lookup_modify_ne bt idx j (some val) hNe,
        hValid.2 j, listGet?_listSet?_ne hNe hSet]

/-- Dense boolean mask table unified onto `Chunk8BlockTree Bool` (subsuming
standalone radix-8 `MaskTree` implementations). -/
abbrev MaskTree : Type := Chunk8BlockTree Bool

/-- Builds a `MaskTree` from a boolean list. -/
def MaskTree.ofList (xs : List Bool) : MaskTree :=
  Chunk8BlockTree.ofList xs

/-- Looks up boolean mask bit `idx` (`false` when out of bounds). -/
def MaskTree.get (mt : MaskTree) (idx : Nat) : Bool :=
  match mt.lookup? idx with
  | some b => b
  | none => false

/-- Exact lookup equivalence for `MaskTree.ofList`. -/
theorem MaskTree.get_ofList (xs : List Bool) (idx : Nat) :
    (MaskTree.ofList xs).get idx =
      match listGet? xs idx with
      | some b => b
      | none => false := by
  unfold MaskTree.get MaskTree.ofList
  rw [Chunk8BlockTree.ofList_lookup_eq xs idx]

private theorem compLog2DepthGo_le_of_le (n : Nat) :
    ∀ (fuel depth cap bound : Nat),
      n ≤ cap * pow2 bound →
      compLog2DepthGo n fuel depth cap ≤ depth + bound
  | 0, depth, _, bound, _ => Nat.le_add_right depth bound
  | k + 1, depth, cap, 0, hCap => by
    rw [pow2_zero, Nat.mul_one] at hCap
    change (if Nat.ble n cap then depth
      else compLog2DepthGo n k (depth + 1) (2 * cap)) ≤ depth + 0
    rw [Nat.ble_eq_true_of_le hCap, ite_bool_true rfl, Nat.add_zero]
    exact Nat.le_refl depth
  | k + 1, depth, cap, bound + 1, hCap => by
    change (if Nat.ble n cap then depth
      else compLog2DepthGo n k (depth + 1) (2 * cap)) ≤ depth + (bound + 1)
    cases hble : Nat.ble n cap with
    | true =>
      rw [ite_bool_true rfl]
      exact Nat.le_add_right depth (bound + 1)
    | false =>
      rw [ite_bool_false rfl]
      have hCap' : n ≤ (2 * cap) * pow2 bound := by
        rw [pow2_succ] at hCap
        rw [Nat.mul_comm 2 cap, Nat.mul_assoc cap 2 (pow2 bound)]
        exact hCap
      have hRec := compLog2DepthGo_le_of_le n k (depth + 1) (2 * cap) bound hCap'
      rw [Nat.succ_add, ← Nat.add_succ] at hRec
      exact hRec

/-- Logarithmic upper bound: `n ≤ pow2 bound → compLog2Depth n ≤ bound`. -/
theorem compLog2Depth_le_of_le_pow2 {n bound : Nat} (h : n ≤ pow2 bound) :
    compLog2Depth n ≤ bound := by
  have h1 : n ≤ 1 * pow2 bound := by
    rw [Nat.one_mul]
    exact h
  have h0 := compLog2DepthGo_le_of_le n n 0 1 bound h1
  rw [Nat.zero_add] at h0
  exact h0

/-- For any list of length `≤ 4,096`, `Chunk8BlockTree.ofList xs` has spine
depth `≤ 9` and tree height `≤ 10` (`≤ 11` including the `Chunk8` leaf payload)
at every fuel budget `fuel`. -/
theorem Chunk8BlockTree.ofList_height_le_10_of_le_4096 {α : Type u}
    (xs : List α) (hLen : xs.length ≤ 4096) (fuel : Nat) :
    (Chunk8BlockTree.ofList xs).depth ≤ 9 ∧
    (Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤ 10 := by
  have hDiv : Nat.div (xs.length + 7) 8 ≤ 512 := by
    have hLt : xs.length + 7 < 513 * 8 :=
      Nat.lt_of_le_of_lt (Nat.add_le_add_right hLen 7) (by decide)
    have hDivLt : Nat.div (xs.length + 7) 8 < 513 :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 7)).mpr hLt
    exact Nat.le_of_lt_succ hDivLt
  have hChunks : (packChunk8 xs).length ≤ pow2 9 := by
    unfold packChunk8
    have hp := packChunk8Fuel_length_le (Nat.div (compListLength xs + 7) 8) xs
    rw [compListLength_eq xs] at hp
    rw [compListLength_eq xs]
    exact Nat.le_trans hp hDiv
  have hDepth : (Chunk8BlockTree.ofList xs).depth ≤ 9 := by
    unfold Chunk8BlockTree.ofList
    dsimp only
    rw [compListLength_eq (packChunk8 xs)]
    exact compLog2Depth_le_of_le_pow2 hChunks
  have hHeight : (Chunk8BlockTree.ofList xs).tree.heightAt fuel ≤ 10 :=
    Nat.le_trans (Chunk8BlockTree.ofList_height_le xs fuel)
      (Nat.succ_le_succ hDepth)
  exact ⟨hDepth, hHeight⟩

/-- Concrete spine-depth check at `N = 4,096` (`depth = 9`) and `N = 256`
(`depth = 5`). -/
theorem chunk8_depth_4096_canary :
    compLog2Depth (Nat.div (4096 + 7) 8) = 9 ∧
    compLog2Depth (Nat.div (256 + 7) 8) = 5 :=
  ⟨rfl, rfl⟩

private def mkChunk8Range : Nat → Nat → List Nat :=
  @Nat.rec (fun _ => Nat → List Nat)
    (fun _ => [])
    (fun _ ih start => start :: ih (start + 1))

/-- Top-down strided tabulation directly into a `Chunk8Tree α` (`O(depth)` WHNF
path forcing on surgical lookups, avoiding intermediate `List` construction). -/
def chunk8TreeTabulateAt {α : Type u} (depth : Nat) :
    Nat → Nat → (Nat → Option α) → Chunk8Tree α :=
  @Nat.rec (fun _ => Nat → Nat → (Nat → Option α) → Chunk8Tree α)
    (fun chunkOff _ f =>
      let b := 8 * chunkOff
      .leaf ⟨f b, f (b + 1), f (b + 2), f (b + 3),
             f (b + 4), f (b + 5), f (b + 6), f (b + 7)⟩)
    (fun _ ih chunkOff step f =>
      .node (ih chunkOff (2 * step) f) (ih (chunkOff + step) (2 * step) f))
    depth

/-- Top-down `Chunk8BlockTree α` tabulation covering indices `0 .. 8*2^depth-1`
in spine depth `depth` (`depth = 5` covers `256` elements; `depth = 9` covers
`4,096` elements with tree height `10 ≤ 11`). -/
def Chunk8BlockTree.tabulate {α : Type u} (depth : Nat) (f : Nat → Option α) :
    Chunk8BlockTree α :=
  { depth := depth, tree := chunk8TreeTabulateAt depth 0 1 f }

private theorem chunk8TreeLookupChunkAt_tabulateAt_in {α : Type u}
    (depth chunkIdx chunkOff step : Nat) (f : Nat → Option α)
    (hc : chunkIdx < pow2 depth) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeTabulateAt depth chunkOff step f) chunkIdx =
      let b := 8 * (chunkOff + step * chunkIdx)
      some ⟨f b, f (b + 1), f (b + 2), f (b + 3),
            f (b + 4), f (b + 5), f (b + 6), f (b + 7)⟩ := by
  revert chunkIdx chunkOff step
  induction depth with
  | zero =>
    intro chunkIdx chunkOff step hc
    rw [pow2_zero] at hc
    have h0 : chunkIdx = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hc)
    rw [h0, Nat.mul_zero, Nat.add_zero]
    rfl
  | succ d ih =>
    intro chunkIdx chunkOff step hc
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hc
    have hhalf : Nat.div chunkIdx 2 < pow2 d :=
      (Nat.div_lt_iff_lt_mul (Nat.succ_pos 1)).mpr hc
    change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d chunkOff (2 * step) f) (Nat.div chunkIdx 2))
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d (chunkOff + step) (2 * step) f)
          (Nat.div chunkIdx 2)) = _
    have hde := nat_div2_decomp chunkIdx
    cases hbeq : Nat.beq (Nat.mod chunkIdx 2) 0 with
    | true =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 = chunkIdx at hde
      dsimp only [cond]
      rw [ih (Nat.div chunkIdx 2) chunkOff (2 * step) hhalf]
      have hmul : (2 * step) * Nat.div chunkIdx 2 = step * chunkIdx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div chunkIdx 2), hde]
      rw [hmul]
    | false =>
      rw [hbeq] at hde
      change 2 * Nat.div chunkIdx 2 + 1 = chunkIdx at hde
      dsimp only [cond]
      rw [ih (Nat.div chunkIdx 2) (chunkOff + step) (2 * step) hhalf]
      have harith :
          (chunkOff + step) + (2 * step) * Nat.div chunkIdx 2 =
            chunkOff + step * chunkIdx := by
        rw [Nat.mul_comm 2 step, Nat.mul_assoc step 2 (Nat.div chunkIdx 2),
          Nat.add_assoc chunkOff step (step * (2 * Nat.div chunkIdx 2))]
        have hs1 :
            step + step * (2 * Nat.div chunkIdx 2) =
              step * (2 * Nat.div chunkIdx 2 + 1) := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
        rw [hs1, hde]
      rw [harith]

private theorem chunk8TreeLookupChunkAt_tabulateAt_oob {α : Type u}
    (depth chunkIdx chunkOff step : Nat) (f : Nat → Option α)
    (hoob : pow2 depth ≤ chunkIdx) :
    chunk8TreeLookupChunkAt depth
        (chunk8TreeTabulateAt depth chunkOff step f) chunkIdx = none := by
  revert chunkIdx chunkOff step
  induction depth with
  | zero =>
    intro chunkIdx _ _ hoob
    rw [pow2_zero] at hoob
    cases chunkIdx with
    | zero => exact False.elim (Nat.not_lt_of_ge hoob Nat.zero_lt_one)
    | succ _ => rfl
  | succ d ih =>
    intro chunkIdx chunkOff step hoob
    rw [pow2_succ, Nat.mul_comm 2 (pow2 d)] at hoob
    have hhalf : pow2 d ≤ Nat.div chunkIdx 2 :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos 1)).mpr hoob
    change cond (Nat.beq (Nat.mod chunkIdx 2) 0)
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d chunkOff (2 * step) f) (Nat.div chunkIdx 2))
        (chunk8TreeLookupChunkAt d
          (chunk8TreeTabulateAt d (chunkOff + step) (2 * step) f)
          (Nat.div chunkIdx 2)) = none
    cases Nat.beq (Nat.mod chunkIdx 2) 0 with
    | true =>
      dsimp only [cond]
      exact ih (Nat.div chunkIdx 2) chunkOff (2 * step) hhalf
    | false =>
      dsimp only [cond]
      exact ih (Nat.div chunkIdx 2) (chunkOff + step) (2 * step) hhalf

/-- Exact in-bounds lookup law for `Chunk8BlockTree.tabulate depth f`
(`idx < 8 * pow2 depth`). -/
theorem Chunk8BlockTree.lookup_tabulate_in {α : Type u} (depth : Nat)
    (f : Nat → Option α) {idx : Nat} (hidx : idx < 8 * pow2 depth) :
    (Chunk8BlockTree.tabulate depth f).lookup? idx = f idx := by
  have hc : Nat.div idx 8 < pow2 depth := by
    rw [Nat.mul_comm 8 (pow2 depth)] at hidx
    exact (Nat.div_lt_iff_lt_mul (Nat.succ_pos 7)).mpr hidx
  unfold Chunk8BlockTree.lookup? Chunk8BlockTree.tabulate chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_tabulateAt_in depth (Nat.div idx 8) 0 1 f hc]
  dsimp only
  rw [Nat.one_mul, Nat.zero_add]
  have hde : 8 * Nat.div idx 8 + Nat.mod idx 8 = idx := Nat.div_add_mod idx 8
  have hr : Nat.mod idx 8 < 8 := Nat.mod_lt idx (Nat.succ_pos 7)
  cases hm : Nat.mod idx 8 with
  | zero =>
    rw [hm, Nat.add_zero] at hde
    dsimp only [Chunk8.get]
    exact congrArg f hde
  | succ r1 =>
    cases r1 with
    | zero =>
      rw [hm] at hde
      dsimp only [Chunk8.get]
      exact congrArg f hde
    | succ r2 =>
      cases r2 with
      | zero =>
        rw [hm] at hde
        dsimp only [Chunk8.get]
        exact congrArg f hde
      | succ r3 =>
        cases r3 with
        | zero =>
          rw [hm] at hde
          dsimp only [Chunk8.get]
          exact congrArg f hde
        | succ r4 =>
          cases r4 with
          | zero =>
            rw [hm] at hde
            dsimp only [Chunk8.get]
            exact congrArg f hde
          | succ r5 =>
            cases r5 with
            | zero =>
              rw [hm] at hde
              dsimp only [Chunk8.get]
              exact congrArg f hde
            | succ r6 =>
              cases r6 with
              | zero =>
                rw [hm] at hde
                dsimp only [Chunk8.get]
                exact congrArg f hde
              | succ r7 =>
                cases r7 with
                | zero =>
                  rw [hm] at hde
                  dsimp only [Chunk8.get]
                  exact congrArg f hde
                | succ r8 =>
                  rw [hm] at hr
                  exact False.elim (nat_ge8_contra hr)

/-- Exact out-of-bounds lookup law for `Chunk8BlockTree.tabulate depth f`
(`8 * pow2 depth ≤ idx`). -/
theorem Chunk8BlockTree.lookup_tabulate_oob {α : Type u} (depth : Nat)
    (f : Nat → Option α) {idx : Nat} (hoob : 8 * pow2 depth ≤ idx) :
    (Chunk8BlockTree.tabulate depth f).lookup? idx = none := by
  have hc : pow2 depth ≤ Nat.div idx 8 := by
    rw [Nat.mul_comm 8 (pow2 depth)] at hoob
    exact (Nat.le_div_iff_mul_le (Nat.succ_pos 7)).mpr hoob
  unfold Chunk8BlockTree.lookup? Chunk8BlockTree.tabulate chunk8TreeGetAt
  dsimp only
  rw [chunk8TreeLookupChunkAt_tabulateAt_oob depth (Nat.div idx 8) 0 1 f hc]

/-- Exact height of `Chunk8BlockTree.tabulate depth f` at fuel `depth + 1`
equals `depth + 1` (so `depth = 9` for `4,096` elements has height `10 ≤ 11`).
-/
theorem Chunk8BlockTree.tabulate_height {α : Type u} (depth : Nat)
    (f : Nat → Option α) :
    (Chunk8BlockTree.tabulate depth f).tree.heightAt (depth + 1) = depth + 1 := by
  unfold Chunk8BlockTree.tabulate
  dsimp only
  have hAt :
      ∀ (d off step : Nat),
        (chunk8TreeTabulateAt d off step f).heightAt (d + 1) = d + 1 := by
    intro d
    induction d with
    | zero => intro _ _; rfl
    | succ d' ih =>
      intro off step
      change natMax2
          ((chunk8TreeTabulateAt d' off (2 * step) f).heightAt (d' + 1))
          ((chunk8TreeTabulateAt d' (off + step) (2 * step) f).heightAt (d' + 1)) + 1 =
        (d' + 1) + 1
      rw [ih off (2 * step), ih (off + step) (2 * step)]
      unfold natMax2
      cases Nat.ble (d' + 1) (d' + 1) <;> rfl
  exact hAt depth 0 1

/-- 256-element and 4,096-element `Chunk8BlockTree.tabulate` plus 128-element
`Chunk8BlockTree.ofList` and `MaskTree` scaling canaries discharged by `rfl`
under default elaborator options. -/
theorem chunk8BlockTree_scaling_canary :
    let bt256 := Chunk8BlockTree.tabulate 5 (fun i => some i)
    let bt4096 := Chunk8BlockTree.tabulate 9 (fun i => some i)
    let bt128 := Chunk8BlockTree.ofList (mkChunk8Range 128 0)
    let mt := MaskTree.ofList [true, false, true, true, false, false, false, false, true]
    bt256.depth = 5 ∧
    bt256.lookup? 0 = some 0 ∧
    bt256.lookup? 127 = some 127 ∧
    bt256.lookup? 255 = some 255 ∧
    bt256.lookup? 256 = none ∧
    (bt256.modify 200 (some 999)).lookup? 200 = some 999 ∧
    (bt256.modify 200 (some 999)).lookup? 199 = some 199 ∧
    bt4096.depth = 9 ∧
    bt4096.lookup? 0 = some 0 ∧
    bt4096.lookup? 2048 = some 2048 ∧
    bt4096.lookup? 4095 = some 4095 ∧
    bt4096.lookup? 4096 = none ∧
    bt128.depth = 4 ∧
    bt128.lookup? 0 = some 0 ∧
    bt128.lookup? 127 = some 127 ∧
    bt128.lookup? 128 = none ∧
    mt.get 0 = true ∧
    mt.get 1 = false ∧
    mt.get 8 = true ∧
    mt.get 9 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
   rfl, rfl, rfl, rfl, rfl⟩


/-! ## Free-Function Names (`PTree.get?`, `chunk8Get`, `chunk8Set`) -/

/-- Looks up `idx` in a depth-`depth` `PTree α`; `ptreeGetAt` with the tree
first. -/
abbrev PTree.get? {α : Type u} (t : PTree α) (depth idx : Nat) : Option α :=
  ptreeGetAt depth t idx

/-- Constant-time slot lookup in a `Chunk8 α` leaf (`Chunk8.get`). -/
abbrev chunk8Get {α : Type u} (c : Chunk8 α) (r : Nat) : Option α :=
  c.get r

/-- Constant-time slot update in a `Chunk8 α` leaf (`Chunk8.set`). -/
abbrev chunk8Set {α : Type u} (c : Chunk8 α) (r : Nat) (v : Option α) :
    Chunk8 α :=
  c.set r v

/-- Read-over-write at the same slot of a `Chunk8 α` leaf. -/
theorem chunk8Get_chunk8Set_same {α : Type u} (c : Chunk8 α) {r : Nat}
    (hr : r < 8) (v : Option α) : chunk8Get (chunk8Set c r v) r = v :=
  Chunk8.get_set_same c v hr

/-- Read-over-write at a different slot of a `Chunk8 α` leaf. -/
theorem chunk8Get_chunk8Set_ne {α : Type u} (c : Chunk8 α) {r j : Nat}
    (hNe : j ≠ r) (v : Option α) :
    chunk8Get (chunk8Set c r v) j = chunk8Get c j :=
  Chunk8.get_set_ne c v hNe

/-- Read-over-write at the same index of a `PTree α` (`idx < pow2 depth`). -/
theorem PTree.get?_modify_same {α : Type u} (t : PTree α)
    (depth idx : Nat) (v : Option α) (hidx : idx < pow2 depth) :
    (ptreeModifyAt depth t idx v).get? depth idx = v :=
  ptreeGetAt_ptreeModifyAt_same depth t idx v hidx

/-- Read-over-write at a different index of a `PTree α`. -/
theorem PTree.get?_modify_other {α : Type u} (t : PTree α)
    (depth idx j : Nat) (v : Option α) (hNe : j ≠ idx) :
    (ptreeModifyAt depth t idx v).get? depth j = t.get? depth j :=
  ptreeGetAt_ptreeModifyAt_ne depth t idx j v hNe

/-! ## Parametric Block-Lookup Step Adapters

A MIR-style step function reads its basic blocks through a lookup function
`Nat → Option BB`. The theorems below show that such a step function gives the
same result over a `BlockTree`, over a `Chunk8BlockTree`, and over the plain
list lookup `listGet?`, for every state and without any assumption on the step
function. The result type `Res` is arbitrary, so the adapters apply to
`StepOutcome State Out Fault`, to a coalgebraic step node, or to any other
step result. -/

/-- Standard-notation form of `BlockTree.ofList_lookup_eq`. -/
theorem BlockTree.ofList_lookup?_eq_getElem? {α : Type u} (xs : List α)
    (idx : Nat) : (BlockTree.ofList xs).lookup? idx = xs[idx]? := by
  rw [BlockTree.ofList_lookup_eq, listGet?_eq_getElem?]

/-- Standard-notation form of `Chunk8BlockTree.ofList_lookup_eq`. -/
theorem Chunk8BlockTree.ofList_lookup?_eq_getElem? {α : Type u}
    (xs : List α) (idx : Nat) :
    (Chunk8BlockTree.ofList xs).lookup? idx = xs[idx]? := by
  rw [Chunk8BlockTree.ofList_lookup_eq, listGet?_eq_getElem?]

/-- A valid `BlockTree` and `listGet?` are the same lookup function. -/
theorem BlockTree.lookup?_eq_fun {α : Type u} {xs : List α}
    {bt : BlockTree α} (hValid : ValidBlockTree xs bt) :
    bt.lookup? = listGet? xs :=
  funext hValid.2

/-- A valid `Chunk8BlockTree` and `listGet?` are the same lookup function. -/
theorem Chunk8BlockTree.lookup?_eq_fun {α : Type u} {xs : List α}
    {bt : Chunk8BlockTree α} (hValid : ValidChunk8BlockTree xs bt) :
    bt.lookup? = listGet? xs :=
  funext hValid.2

/-- Any block-indexed step function gives the same result over a valid
`BlockTree` as over the list it tabulates. -/
theorem stepWith_validBlockTree_eq {BB : Type u} {State : Sort v}
    {Res : Sort w} (stepWith : (Nat → Option BB) → State → Res)
    {blocks : List BB} {bt : BlockTree BB}
    (hValid : ValidBlockTree blocks bt) (s : State) :
    stepWith bt.lookup? s = stepWith (listGet? blocks) s := by
  rw [BlockTree.lookup?_eq_fun hValid]

/-- Any block-indexed step function gives the same result over
`BlockTree.ofList blocks` as over `listGet? blocks`. -/
theorem stepWith_blockTree_eq {BB : Type u} {State : Sort v} {Res : Sort w}
    (stepWith : (Nat → Option BB) → State → Res) (blocks : List BB)
    (s : State) :
    stepWith (BlockTree.ofList blocks).lookup? s =
      stepWith (listGet? blocks) s :=
  stepWith_validBlockTree_eq stepWith (valid_blockTree_ofList blocks) s

/-- Any block-indexed step function gives the same result over a valid
`Chunk8BlockTree` as over the list it tabulates. -/
theorem stepWith_validChunk8BlockTree_eq {BB : Type u} {State : Sort v}
    {Res : Sort w} (stepWith : (Nat → Option BB) → State → Res)
    {blocks : List BB} {bt : Chunk8BlockTree BB}
    (hValid : ValidChunk8BlockTree blocks bt) (s : State) :
    stepWith bt.lookup? s = stepWith (listGet? blocks) s := by
  rw [Chunk8BlockTree.lookup?_eq_fun hValid]

/-- Any block-indexed step function gives the same result over
`Chunk8BlockTree.ofList blocks` as over `listGet? blocks`. -/
theorem stepWith_chunk8BlockTree_eq {BB : Type u} {State : Sort v}
    {Res : Sort w} (stepWith : (Nat → Option BB) → State → Res)
    (blocks : List BB) (s : State) :
    stepWith (Chunk8BlockTree.ofList blocks).lookup? s =
      stepWith (listGet? blocks) s :=
  stepWith_validChunk8BlockTree_eq stepWith
    (valid_chunk8BlockTree_ofList blocks) s

/-- Axiom-free form of `stepWith_blockTree_eq` for a step function that
respects pointwise-equal lookups, which every step function that only applies
its lookup argument does. -/
theorem stepWith_blockTree_eq_of_pointwise {BB : Type u} {State : Sort v}
    {Res : Sort w} (stepWith : (Nat → Option BB) → State → Res)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : State),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    (blocks : List BB) (s : State) :
    stepWith (BlockTree.ofList blocks).lookup? s =
      stepWith (listGet? blocks) s :=
  hPointwise _ _ s (BlockTree.ofList_lookup_eq blocks)

/-- Axiom-free form of `stepWith_chunk8BlockTree_eq` for a step function that
respects pointwise-equal lookups. -/
theorem stepWith_chunk8BlockTree_eq_of_pointwise {BB : Type u}
    {State : Sort v} {Res : Sort w}
    (stepWith : (Nat → Option BB) → State → Res)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : State),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    (blocks : List BB) (s : State) :
    stepWith (Chunk8BlockTree.ofList blocks).lookup? s =
      stepWith (listGet? blocks) s :=
  hPointwise _ _ s (Chunk8BlockTree.ofList_lookup_eq blocks)

/-- Axiom-free adapter for a step function that reads only the block of the
current state: the `BlockTree` and the list hand it the same block. -/
theorem stepAt_blockTree_eq {BB : Type u} {State : Sort v} {Res : Sort w}
    (blockOf : State → Nat) (stepAt : Option BB → State → Res)
    (blocks : List BB) (s : State) :
    stepAt ((BlockTree.ofList blocks).lookup? (blockOf s)) s =
      stepAt (listGet? blocks (blockOf s)) s := by
  rw [BlockTree.ofList_lookup_eq]

/-- Axiom-free adapter for a step function that reads only the block of the
current state, over `Chunk8BlockTree.ofList`. -/
theorem stepAt_chunk8BlockTree_eq {BB : Type u} {State : Sort v}
    {Res : Sort w} (blockOf : State → Nat)
    (stepAt : Option BB → State → Res) (blocks : List BB) (s : State) :
    stepAt ((Chunk8BlockTree.ofList blocks).lookup? (blockOf s)) s =
      stepAt (listGet? blocks (blockOf s)) s := by
  rw [Chunk8BlockTree.ofList_lookup_eq]

/-! ## Numeral Forcing for Elaborator-Level Evaluation (`natForce`)

`ptreeGetAt` and the `Chunk8` spine index with `Nat.div` and `Nat.mod`. The
kernel evaluates these on numerals, but the elaborator's definitional
unfolding only folds them when the argument is a closed numeral term: an index
such as the block field of a state record that also holds symbolic values is
left stuck, and a `rfl` proof about a symbolic state fails before the kernel
ever sees it. `natForce` pattern-matches on the index first, which reduces it
to a numeral, and only then hands it to the lookup. -/

/-- Reduces `n` to a numeral and passes it to `k`. Propositionally it is
`k n` (`natForce_eq`); its purpose is to make `k` see a closed numeral during
elaborator-level evaluation. -/
def natForce {α : Sort u} (n : Nat) (k : Nat → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (m + 1)

/-- `natForce n k` is `k n`. -/
theorem natForce_eq {α : Sort u} (n : Nat) (k : Nat → α) :
    natForce n k = k n := by
  cases n with
  | zero => rfl
  | succ m => rfl

/-- `BlockTree` lookup that forces its index to a numeral first. -/
def BlockTree.lookupForced? {α : Type u} (bt : BlockTree α) (idx : Nat) :
    Option α :=
  natForce idx bt.lookup?

/-- `Chunk8BlockTree` lookup that forces its index to a numeral first. -/
def Chunk8BlockTree.lookupForced? {α : Type u} (bt : Chunk8BlockTree α)
    (idx : Nat) : Option α :=
  natForce idx bt.lookup?

/-- `MaskTree` lookup that forces its index to a numeral first. -/
def MaskTree.getForced (mt : MaskTree) (idx : Nat) : Bool :=
  natForce idx mt.get

/-- The forcing `BlockTree` lookup is the plain lookup. -/
theorem BlockTree.lookupForced?_eq {α : Type u} (bt : BlockTree α)
    (idx : Nat) : bt.lookupForced? idx = bt.lookup? idx :=
  natForce_eq idx bt.lookup?

/-- The forcing `Chunk8BlockTree` lookup is the plain lookup. -/
theorem Chunk8BlockTree.lookupForced?_eq {α : Type u}
    (bt : Chunk8BlockTree α) (idx : Nat) :
    bt.lookupForced? idx = bt.lookup? idx :=
  natForce_eq idx bt.lookup?

/-- The forcing `MaskTree` lookup is the plain lookup. -/
theorem MaskTree.getForced_eq (mt : MaskTree) (idx : Nat) :
    mt.getForced idx = mt.get idx :=
  natForce_eq idx mt.get

/-- A valid `BlockTree` under the forcing lookup and `listGet?` are the same
lookup function. -/
theorem BlockTree.lookupForced?_eq_fun {α : Type u} {xs : List α}
    {bt : BlockTree α} (hValid : ValidBlockTree xs bt) :
    bt.lookupForced? = listGet? xs :=
  funext (fun idx => (bt.lookupForced?_eq idx).trans (hValid.2 idx))

/-- A valid `Chunk8BlockTree` under the forcing lookup and `listGet?` are the
same lookup function. -/
theorem Chunk8BlockTree.lookupForced?_eq_fun {α : Type u} {xs : List α}
    {bt : Chunk8BlockTree α} (hValid : ValidChunk8BlockTree xs bt) :
    bt.lookupForced? = listGet? xs :=
  funext (fun idx => (bt.lookupForced?_eq idx).trans (hValid.2 idx))

/-- Any block-indexed step function gives the same result over the forcing
lookup of `BlockTree.ofList blocks` as over `listGet? blocks`. This is the
form to evaluate by `rfl` on a state with symbolic fields. -/
theorem stepWith_blockTree_forced_eq {BB : Type u} {State : Sort v}
    {Res : Sort w} (stepWith : (Nat → Option BB) → State → Res)
    (blocks : List BB) (s : State) :
    stepWith (BlockTree.ofList blocks).lookupForced? s =
      stepWith (listGet? blocks) s := by
  rw [BlockTree.lookupForced?_eq_fun (valid_blockTree_ofList blocks)]

/-- Any block-indexed step function gives the same result over the forcing
lookup of `Chunk8BlockTree.ofList blocks` as over `listGet? blocks`. -/
theorem stepWith_chunk8BlockTree_forced_eq {BB : Type u} {State : Sort v}
    {Res : Sort w} (stepWith : (Nat → Option BB) → State → Res)
    (blocks : List BB) (s : State) :
    stepWith (Chunk8BlockTree.ofList blocks).lookupForced? s =
      stepWith (listGet? blocks) s := by
  rw [Chunk8BlockTree.lookupForced?_eq_fun
    (valid_chunk8BlockTree_ofList blocks)]

/-! ## Fuel-Bounded Execution to a Cutpoint (`runToCut`, `evalBlockTreeToCut`) -/

/-- Result of running a step function towards a cutpoint. -/
inductive CutRun (State : Type u) (Res : Type v) : Type (max u v) where
  /-- Execution reached the cutpoint state `s`. -/
  | cut (s : State) : CutRun State Res
  /-- The step at `s` produced the result `r`, which has no successor state:
  execution terminated or faulted before a cutpoint. -/
  | halt (s : State) (r : Res) : CutRun State Res
  /-- The step budget ran out at `s` before a cutpoint. -/
  | timeout (s : State) : CutRun State Res

/-- Runs `step` from `s` until a state satisfies `isCut`, for at most `fuel`
steps (`0` `noncomputable`, `0` `._unsafe_rec`). `next?` extracts the successor
state of a step result. A state that already satisfies `isCut` is returned
without stepping. -/
def runToCut {State : Type u} {Res : Type v} (step : State → Res)
    (next? : Res → Option State) (isCut : State → Bool) (fuel : Nat)
    (s : State) : CutRun State Res :=
  @Nat.rec (fun _ => State → CutRun State Res)
    (fun st =>
      match isCut st with
      | true => .cut st
      | false => .timeout st)
    (fun _ ih st =>
      match isCut st with
      | true => .cut st
      | false =>
        match next? (step st) with
        | some st' => ih st'
        | none => .halt st (step st))
    fuel s

/-- Takes one step from `s` and then runs to a cutpoint. This is the form for
a stage that starts at a cutpoint, such as a loop header. -/
def runFromCut {State : Type u} {Res : Type v} (step : State → Res)
    (next? : Res → Option State) (isCut : State → Bool) (fuel : Nat)
    (s : State) : CutRun State Res :=
  match next? (step s) with
  | some s' => runToCut step next? isCut fuel s'
  | none => .halt s (step s)

section RunToCut

variable {State : Type u} {Res : Type v} {step : State → Res}
  {next? : Res → Option State} {isCut : State → Bool}

/-- A cutpoint state is returned at once, at every budget. -/
theorem runToCut_of_isCut {s : State} (h : isCut s = true) (fuel : Nat) :
    runToCut step next? isCut fuel s = .cut s := by
  cases fuel with
  | zero =>
    change (match isCut s with
      | true => CutRun.cut s
      | false => CutRun.timeout s) = CutRun.cut s
    rw [h]
  | succ fuel =>
    change (match isCut s with
      | true => CutRun.cut s
      | false =>
        match next? (step s) with
        | some st' => runToCut step next? isCut fuel st'
        | none => CutRun.halt s (step s)) = CutRun.cut s
    rw [h]

/-- With no budget left, a state outside the cutpoints times out. -/
theorem runToCut_zero_of_not_isCut {s : State} (h : isCut s = false) :
    runToCut step next? isCut 0 s = .timeout s := by
  change (match isCut s with
    | true => CutRun.cut s
    | false => CutRun.timeout s) = CutRun.timeout s
  rw [h]

/-- A state outside the cutpoints with successor `s'` continues at `s'`. -/
theorem runToCut_succ_of_next {s s' : State} (h : isCut s = false)
    (hNext : next? (step s) = some s') (fuel : Nat) :
    runToCut step next? isCut (fuel + 1) s =
      runToCut step next? isCut fuel s' := by
  change (match isCut s with
    | true => CutRun.cut s
    | false =>
      match next? (step s) with
      | some st' => runToCut step next? isCut fuel st'
      | none => CutRun.halt s (step s)) = runToCut step next? isCut fuel s'
  rw [h, hNext]

/-- A state outside the cutpoints without successor halts the run. -/
theorem runToCut_succ_of_halt {s : State} (h : isCut s = false)
    (hNext : next? (step s) = none) (fuel : Nat) :
    runToCut step next? isCut (fuel + 1) s = .halt s (step s) := by
  change (match isCut s with
    | true => CutRun.cut s
    | false =>
      match next? (step s) with
      | some st' => runToCut step next? isCut fuel st'
      | none => CutRun.halt s (step s)) = CutRun.halt s (step s)
  rw [h, hNext]

/-- A run that ends at a cutpoint ends in a state satisfying `isCut`. -/
theorem runToCut_cut_isCut {fuel : Nat} {s s' : State}
    (h : runToCut step next? isCut fuel s = .cut s') : isCut s' = true := by
  induction fuel generalizing s with
  | zero =>
    cases hCut : isCut s with
    | true =>
      rw [runToCut_of_isCut hCut 0] at h
      injection h with hEq
      rw [← hEq]
      exact hCut
    | false =>
      rw [runToCut_zero_of_not_isCut hCut] at h
      cases h
  | succ fuel ih =>
    cases hCut : isCut s with
    | true =>
      rw [runToCut_of_isCut hCut (fuel + 1)] at h
      injection h with hEq
      rw [← hEq]
      exact hCut
    | false =>
      cases hNext : next? (step s) with
      | none =>
        rw [runToCut_succ_of_halt hCut hNext fuel] at h
        cases h
      | some st' =>
        rw [runToCut_succ_of_next hCut hNext fuel] at h
        exact ih h

/-- Fuel monotonicity: a run that reaches a cutpoint within `f₁` steps reaches
the same cutpoint state within any larger budget. -/
theorem runToCut_cut_fuel_mono {f₁ f₂ : Nat} {s s' : State} (hLe : f₁ ≤ f₂)
    (h : runToCut step next? isCut f₁ s = .cut s') :
    runToCut step next? isCut f₂ s = .cut s' := by
  induction f₁ generalizing f₂ s with
  | zero =>
    cases hCut : isCut s with
    | true =>
      rw [runToCut_of_isCut hCut 0] at h
      rw [runToCut_of_isCut hCut f₂]
      exact h
    | false =>
      rw [runToCut_zero_of_not_isCut hCut] at h
      cases h
  | succ f₁ ih =>
    cases f₂ with
    | zero => exact False.elim (Nat.not_succ_le_zero f₁ hLe)
    | succ f₂ =>
      cases hCut : isCut s with
      | true =>
        rw [runToCut_of_isCut hCut (f₁ + 1)] at h
        rw [runToCut_of_isCut hCut (f₂ + 1)]
        exact h
      | false =>
        cases hNext : next? (step s) with
        | none =>
          rw [runToCut_succ_of_halt hCut hNext f₁] at h
          cases h
        | some st' =>
          rw [runToCut_succ_of_next hCut hNext f₁] at h
          rw [runToCut_succ_of_next hCut hNext f₂]
          exact ih (Nat.le_of_succ_le_succ hLe) h

/-- Pointwise congruence in the step function, without function
extensionality. -/
theorem runToCut_congr_step {step₁ step₂ : State → Res}
    (hEq : ∀ s : State, step₁ s = step₂ s) (fuel : Nat) (s : State) :
    runToCut step₁ next? isCut fuel s = runToCut step₂ next? isCut fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    change (match isCut s with
      | true => CutRun.cut s
      | false =>
        match next? (step₁ s) with
        | some st' => runToCut step₁ next? isCut fuel st'
        | none => CutRun.halt s (step₁ s)) =
      (match isCut s with
      | true => CutRun.cut s
      | false =>
        match next? (step₂ s) with
        | some st' => runToCut step₂ next? isCut fuel st'
        | none => CutRun.halt s (step₂ s))
    rw [hEq s]
    cases isCut s with
    | true => rfl
    | false =>
      cases next? (step₂ s) with
      | none => rfl
      | some st' => exact ih st'

end RunToCut

/-- Runs a block-indexed step function over a `BlockTree` up to a set of
cutpoint blocks (`0` `noncomputable`, `0` `._unsafe_rec`). `blockOf` reads the
current block of a state and `cuts` marks the cutpoint blocks. The block list
never appears: each step costs one `O(bt.depth)` trie lookup. Lookups force
their index (`natForce`), so the run also evaluates by `rfl` on a state with
symbolic fields. -/
def evalBlockTreeToCut {BB : Type u} {State : Type v} {Res : Type w}
    (bt : BlockTree BB) (stepWith : (Nat → Option BB) → State → Res)
    (next? : Res → Option State) (blockOf : State → Nat) (cuts : MaskTree)
    (fuel : Nat) (s : State) : CutRun State Res :=
  runToCut (stepWith bt.lookupForced?) next?
    (fun st => cuts.getForced (blockOf st)) fuel s

/-- `evalBlockTreeToCut` after one mandatory step, for a stage that starts at
a cutpoint block. -/
def evalBlockTreeFromCut {BB : Type u} {State : Type v} {Res : Type w}
    (bt : BlockTree BB) (stepWith : (Nat → Option BB) → State → Res)
    (next? : Res → Option State) (blockOf : State → Nat) (cuts : MaskTree)
    (fuel : Nat) (s : State) : CutRun State Res :=
  runFromCut (stepWith bt.lookupForced?) next?
    (fun st => cuts.getForced (blockOf st)) fuel s

/-- `evalBlockTreeToCut` over a `Chunk8BlockTree`. -/
def evalChunk8BlockTreeToCut {BB : Type u} {State : Type v} {Res : Type w}
    (bt : Chunk8BlockTree BB) (stepWith : (Nat → Option BB) → State → Res)
    (next? : Res → Option State) (blockOf : State → Nat) (cuts : MaskTree)
    (fuel : Nat) (s : State) : CutRun State Res :=
  runToCut (stepWith bt.lookupForced?) next?
    (fun st => cuts.getForced (blockOf st)) fuel s

/-- The forcing cutpoint test is the plain cutpoint test. -/
theorem MaskTree.getForced_comp_eq_fun {State : Type v} (cuts : MaskTree)
    (blockOf : State → Nat) :
    (fun st => cuts.getForced (blockOf st)) =
      (fun st => cuts.get (blockOf st)) :=
  funext (fun st => cuts.getForced_eq (blockOf st))

/-- Cut execution over a valid `BlockTree` is cut execution over the list it
tabulates. -/
theorem evalBlockTreeToCut_eq_of_valid {BB : Type u} {State : Type v}
    {Res : Type w} {blocks : List BB} {bt : BlockTree BB}
    (hValid : ValidBlockTree blocks bt)
    (stepWith : (Nat → Option BB) → State → Res)
    (next? : Res → Option State) (blockOf : State → Nat) (cuts : MaskTree)
    (fuel : Nat) (s : State) :
    evalBlockTreeToCut bt stepWith next? blockOf cuts fuel s =
      runToCut (stepWith (listGet? blocks)) next?
        (fun st => cuts.get (blockOf st)) fuel s := by
  unfold evalBlockTreeToCut
  rw [BlockTree.lookupForced?_eq_fun hValid,
    MaskTree.getForced_comp_eq_fun cuts blockOf]

/-- Cut execution over `BlockTree.ofList blocks` is cut execution over
`listGet? blocks`. -/
theorem evalBlockTreeToCut_ofList_eq {BB : Type u} {State : Type v}
    {Res : Type w} (blocks : List BB)
    (stepWith : (Nat → Option BB) → State → Res)
    (next? : Res → Option State) (blockOf : State → Nat) (cuts : MaskTree)
    (fuel : Nat) (s : State) :
    evalBlockTreeToCut (BlockTree.ofList blocks) stepWith next? blockOf cuts
      fuel s =
      runToCut (stepWith (listGet? blocks)) next?
        (fun st => cuts.get (blockOf st)) fuel s :=
  evalBlockTreeToCut_eq_of_valid (valid_blockTree_ofList blocks) stepWith
    next? blockOf cuts fuel s

/-- Stage execution from a cutpoint over `BlockTree.ofList blocks` is stage
execution over `listGet? blocks`. -/
theorem evalBlockTreeFromCut_ofList_eq {BB : Type u} {State : Type v}
    {Res : Type w} (blocks : List BB)
    (stepWith : (Nat → Option BB) → State → Res)
    (next? : Res → Option State) (blockOf : State → Nat) (cuts : MaskTree)
    (fuel : Nat) (s : State) :
    evalBlockTreeFromCut (BlockTree.ofList blocks) stepWith next? blockOf
      cuts fuel s =
      runFromCut (stepWith (listGet? blocks)) next?
        (fun st => cuts.get (blockOf st)) fuel s := by
  unfold evalBlockTreeFromCut
  rw [BlockTree.lookupForced?_eq_fun (valid_blockTree_ofList blocks),
    MaskTree.getForced_comp_eq_fun cuts blockOf]

/-- Cut execution over `Chunk8BlockTree.ofList blocks` is cut execution over
`listGet? blocks`. -/
theorem evalChunk8BlockTreeToCut_ofList_eq {BB : Type u} {State : Type v}
    {Res : Type w} (blocks : List BB)
    (stepWith : (Nat → Option BB) → State → Res)
    (next? : Res → Option State) (blockOf : State → Nat) (cuts : MaskTree)
    (fuel : Nat) (s : State) :
    evalChunk8BlockTreeToCut (Chunk8BlockTree.ofList blocks) stepWith next?
      blockOf cuts fuel s =
      runToCut (stepWith (listGet? blocks)) next?
        (fun st => cuts.get (blockOf st)) fuel s := by
  unfold evalChunk8BlockTreeToCut
  rw [Chunk8BlockTree.lookupForced?_eq_fun
      (valid_chunk8BlockTree_ofList blocks),
    MaskTree.getForced_comp_eq_fun cuts blockOf]

/-- A cut execution that ends at a cutpoint ends at a marked block. -/
theorem evalBlockTreeToCut_cut_marked {BB : Type u} {State : Type v}
    {Res : Type w} {bt : BlockTree BB}
    {stepWith : (Nat → Option BB) → State → Res}
    {next? : Res → Option State} {blockOf : State → Nat} {cuts : MaskTree}
    {fuel : Nat} {s s' : State}
    (h : evalBlockTreeToCut bt stepWith next? blockOf cuts fuel s =
      .cut s') :
    cuts.get (blockOf s') = true := by
  rw [← cuts.getForced_eq (blockOf s')]
  exact runToCut_cut_isCut
    (isCut := fun st => cuts.getForced (blockOf st)) h

/-- Cut-execution canary on a five-block chain `0 → 1 → 2 → 3 → 4 → 5`, where
block `5` is missing: with block `3` marked the run stops there, with no
marked block it halts at the missing block, and with too little fuel it times
out. Every case is discharged by `rfl` through the `BlockTree`. -/
theorem evalBlockTreeToCut_canary :
    let bt := BlockTree.ofList [1, 2, 3, 4, 5]
    let stepWith := fun (look : Nat → Option Nat) (s : Nat) => look s
    let cuts := MaskTree.ofList [false, false, false, true]
    evalBlockTreeToCut bt stepWith (fun r => r) (fun s => s) cuts 8 0 =
      .cut 3 ∧
    evalBlockTreeFromCut bt stepWith (fun r => r) (fun s => s) cuts 8 3 =
      .halt 5 none ∧
    evalBlockTreeToCut bt stepWith (fun r => r) (fun s => s)
      (MaskTree.ofList []) 8 0 = .halt 5 none ∧
    evalBlockTreeToCut bt stepWith (fun r => r) (fun s => s) cuts 2 0 =
      .timeout 2 ∧
    evalChunk8BlockTreeToCut (Chunk8BlockTree.ofList [1, 2, 3, 4, 5])
      stepWith (fun r => r) (fun s => s) cuts 8 0 = .cut 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Anneal.ParametricCore
