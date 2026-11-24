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
import Anneal.Firewall
import Anneal.ParametricCore.LoopInv
import Anneal.ParametricCore.BlockTree
import Anneal.ParametricCore.StageCut

universe u v w x y

namespace Anneal.ParametricCore

/-!
# Checked-Arithmetic Diamond Joins & `intToInt` Cast Stage Cuts
(`Anneal.ParametricCore.OverflowCastJoin`)

Zero-TCB, MIR-parametric, fully LCNF-computable (`0`
`._unsafe_rec`) checked-arithmetic, narrowing/widening `intToInt` cast, and
interval-guarded unchecked-arithmetic stage-cut library over
`Anneal.ParametricCore.{LoopInv,BlockTree,StageCut}` and
`Anneal.Firewall.IndexedCut`:

1. **Total Slot Table (`listSetAt`, `StageLocalIds`):** `List.foldr`-based
   computable total local-slot update with length preservation, same-index
   lookup, distinct-index framing, overwrite/commutation laws, and
   `BlockTree` / `Chunk8BlockTree` compatibility.
2. **Width-Parametric Cast & Overflow Algebra (`ScalarWidth`, `intToIntCast`,
   `addWithOverflowU`, `subWithOverflowU`, `mulWithOverflowU`,
   `shlWithOverflowU`, `addUncheckedU`, `subUncheckedU`, `mulUncheckedU`):**
   Covers `u8`, `u16`, `u32`, `u64`, `u128` (`8, 16, 32, 64, 128` bits),
   narrowing truncation, unsigned zero-extension, signed two's-complement
   sign-extension, exact no-overflow equivalences, widening-then-narrowing
   round-trips, narrowing-under-bound exactness, and fail-closed overflow
   rejection.
3. **Zero-`Prop`-Argument `@[irreducible] OvfCastStageCut`:** Parametric state
   interface `OvfCastFrameOps`, interval cutpoint invariant
   `StageIntervalStateInv`, narrowing/widening/checked-diamond/unchecked
   stage rules, $O(m)$ sequential composition across $m$ diamonds without $2^m$
   path explosion, `BlockTree` / `Chunk8BlockTree` lifting, `StageCut` /
   `wpOutcome` / `Anneal.Firewall.IndexedCut` interop, and fail-closed negative
   boundary theorems.
4. **Canaries:** Concrete 8-stage (`256`-path) `BlockTree`-backed multi-diamond
   pipeline verified in $O(m)$ cuts, checked-diamond early-return & saturate
   arms, signed sign-extension round-trips, bystander local framing, and
   negative overflow / alias rejection guards.
-/

/-! ## Part I: Constructive Total Slot-Update Algebra (`listSetAt`, `StageLocalIds`) -/

section ListSetAt

variable {α : Type u}

private def listSetAtAux (xs : List α) (v : α) : List α × (Nat → List α) :=
  List.foldr
    (fun (x : α) (acc : List α × (Nat → List α)) =>
      (x :: acc.1,
       fun n =>
         match n with
         | 0 => v :: acc.1
         | k + 1 => x :: acc.2 k))
    ([], fun _ => [])
    xs

private theorem listSetAtAux_fst (xs : List α) (v : α) :
    (listSetAtAux xs v).1 = xs := by
  induction xs with
  | nil => rfl
  | cons x _ ih => exact congrArg (List.cons x) ih

/-- Total computable list update via `List.foldr` (`0`
`._unsafe_rec`): replaces index `idx` with `v` when `idx < xs.length` and
leaves `xs` unchanged when `xs.length ≤ idx`. -/
def listSetAt (xs : List α) (idx : Nat) (v : α) : List α :=
  (listSetAtAux xs v).2 idx

/-- Empty-list equation for `listSetAt`. -/
theorem listSetAt_nil (idx : Nat) (v : α) :
    listSetAt ([] : List α) idx v = [] :=
  rfl

/-- Zero-index equation for `listSetAt` on `x :: tl`. -/
theorem listSetAt_cons_zero (x : α) (tl : List α) (v : α) :
    listSetAt (x :: tl) 0 v = v :: tl :=
  congrArg (List.cons v) (listSetAtAux_fst tl v)

/-- Successor-index equation for `listSetAt` on `x :: tl`. -/
theorem listSetAt_cons_succ (x : α) (tl : List α) (k : Nat) (v : α) :
    listSetAt (x :: tl) (k + 1) v = x :: listSetAt tl k v :=
  rfl

/-- `listSetAt` preserves `List.length`. -/
theorem listSetAt_length (xs : List α) (idx : Nat) (v : α) :
    (listSetAt xs idx v).length = xs.length := by
  induction xs generalizing idx with
  | nil => rfl
  | cons _ tl ih =>
    cases idx with
    | zero =>
      rw [listSetAt_cons_zero]
      rfl
    | succ k =>
      rw [listSetAt_cons_succ]
      exact congrArg Nat.succ (ih k)

/-- Same-index lookup law for `listSetAt` when `idx < xs.length`. -/
theorem listGet?_listSetAt_same {xs : List α} {idx : Nat} (v : α)
    (hLt : idx < xs.length) :
    listGet? (listSetAt xs idx v) idx = some v := by
  induction xs generalizing idx with
  | nil => exact False.elim (Nat.not_lt_zero idx hLt)
  | cons _ tl ih =>
    cases idx with
    | zero =>
      rw [listSetAt_cons_zero]
      rfl
    | succ k =>
      rw [listSetAt_cons_succ]
      exact ih (Nat.lt_of_succ_lt_succ hLt)

/-- Distinct-index frame law for `listSetAt` (`j ≠ idx`). -/
theorem listGet?_listSetAt_ne (xs : List α) {idx j : Nat} (v : α)
    (hNe : j ≠ idx) :
    listGet? (listSetAt xs idx v) j = listGet? xs j := by
  induction xs generalizing idx j with
  | nil => rfl
  | cons _ tl ih =>
    cases idx with
    | zero =>
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ _ =>
        rw [listSetAt_cons_zero]
        rfl
    | succ k =>
      cases j with
      | zero =>
        rw [listSetAt_cons_succ]
        rfl
      | succ m =>
        rw [listSetAt_cons_succ]
        exact ih (fun hEq => hNe (congrArg Nat.succ hEq))

/-- Out-of-bounds `listSetAt` leaves `xs` unchanged. -/
theorem listSetAt_eq_of_oob (xs : List α) {idx : Nat} (v : α)
    (hGe : xs.length ≤ idx) :
    listSetAt xs idx v = xs := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x tl ih =>
    cases idx with
    | zero => exact False.elim (Nat.not_succ_le_zero tl.length hGe)
    | succ k =>
      rw [listSetAt_cons_succ]
      exact congrArg (List.cons x) (ih (Nat.le_of_succ_le_succ hGe))

/-- `listSetAt` equals `List.set`. -/
theorem listSetAt_eq_listSet (xs : List α) (idx : Nat) (v : α) :
    listSetAt xs idx v = xs.set idx v := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x tl ih =>
    cases idx with
    | zero =>
      rw [listSetAt_cons_zero]
      rfl
    | succ k =>
      rw [listSetAt_cons_succ]
      exact congrArg (List.cons x) (ih k)

/-- Agreement between `BlockTree.listSet?` and `some (listSetAt xs idx v)` when
`idx < xs.length`. -/
theorem listSet?_eq_some_listSetAt {xs : List α} {idx : Nat} (v : α)
    (hLt : idx < xs.length) :
    listSet? xs idx v = some (listSetAt xs idx v) := by
  rw [listSet?_of_lt v hLt, listSetAt_eq_listSet]

/-- Overwriting the same index twice collapses to the second write. -/
theorem listSetAt_overwrite (xs : List α) (idx : Nat) (v₁ v₂ : α) :
    listSetAt (listSetAt xs idx v₁) idx v₂ = listSetAt xs idx v₂ := by
  induction xs generalizing idx with
  | nil => rfl
  | cons x tl ih =>
    cases idx with
    | zero =>
      rw [listSetAt_cons_zero, listSetAt_cons_zero, listSetAt_cons_zero]
    | succ k =>
      rw [listSetAt_cons_succ, listSetAt_cons_succ, listSetAt_cons_succ]
      exact congrArg (List.cons x) (ih k)

/-- Updates at distinct indices commute under `listSetAt`. -/
theorem listSetAt_comm (xs : List α) {i j : Nat} (v₁ v₂ : α) (hNe : i ≠ j) :
    listSetAt (listSetAt xs i v₁) j v₂ =
      listSetAt (listSetAt xs j v₂) i v₁ := by
  induction xs generalizing i j with
  | nil => rfl
  | cons x tl ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact False.elim (hNe rfl)
      | succ _ =>
        rw [listSetAt_cons_zero, listSetAt_cons_succ, listSetAt_cons_succ,
          listSetAt_cons_zero]
    | succ _ =>
      cases j with
      | zero =>
        rw [listSetAt_cons_succ, listSetAt_cons_zero, listSetAt_cons_zero,
          listSetAt_cons_succ]
      | succ _ =>
        rw [listSetAt_cons_succ, listSetAt_cons_succ, listSetAt_cons_succ,
          listSetAt_cons_succ]
        exact congrArg (List.cons x)
          (ih (fun hEq => hNe (congrArg Nat.succ hEq)))

/-- `BlockTree.ofList` same-index lookup compatibility with `listSetAt`. -/
theorem blockTree_ofList_listSetAt_same {xs : List α} {idx : Nat} (v : α)
    (hLt : idx < xs.length) :
    (BlockTree.ofList (listSetAt xs idx v)).lookup? idx = some v := by
  rw [BlockTree.ofList_lookup_eq]
  exact listGet?_listSetAt_same v hLt

/-- `BlockTree.ofList` distinct-index frame compatibility with `listSetAt`. -/
theorem blockTree_ofList_listSetAt_ne (xs : List α) {idx j : Nat} (v : α)
    (hNe : j ≠ idx) :
    (BlockTree.ofList (listSetAt xs idx v)).lookup? j =
      (BlockTree.ofList xs).lookup? j := by
  rw [BlockTree.ofList_lookup_eq, BlockTree.ofList_lookup_eq]
  exact listGet?_listSetAt_ne xs v hNe

/-- `BlockTree.ofList` forced lookup compatibility with `listSetAt`. -/
theorem blockTree_ofList_forced_listSetAt_same {xs : List α} {idx : Nat}
    (v : α) (hLt : idx < xs.length) :
    (BlockTree.ofList (listSetAt xs idx v)).lookupForced? idx = some v := by
  rw [BlockTree.lookupForced?_eq]
  exact blockTree_ofList_listSetAt_same v hLt

/-- `Chunk8BlockTree.ofList` same-index lookup compatibility with `listSetAt`. -/
theorem chunk8BlockTree_ofList_listSetAt_same {xs : List α} {idx : Nat}
    (v : α) (hLt : idx < xs.length) :
    (Chunk8BlockTree.ofList (listSetAt xs idx v)).lookup? idx = some v := by
  rw [Chunk8BlockTree.ofList_lookup_eq]
  exact listGet?_listSetAt_same v hLt

/-- `Chunk8BlockTree.ofList` distinct-index frame compatibility with
`listSetAt`. -/
theorem chunk8BlockTree_ofList_listSetAt_ne (xs : List α) {idx j : Nat}
    (v : α) (hNe : j ≠ idx) :
    (Chunk8BlockTree.ofList (listSetAt xs idx v)).lookup? j =
      (Chunk8BlockTree.ofList xs).lookup? j := by
  rw [Chunk8BlockTree.ofList_lookup_eq, Chunk8BlockTree.ofList_lookup_eq]
  exact listGet?_listSetAt_ne xs v hNe

end ListSetAt

/-- Four local-slot indices `(accId, tmpId, ovfMulId, ovfAddId)` used by an
overflow-cast diamond stage. -/
structure StageLocalIds where
  /-- Accumulator local slot index. -/
  accId : Nat
  /-- Narrowed/scratch local slot index. -/
  tmpId : Nat
  /-- First checked-arithmetic `(wrapped, overflowed)` local slot index. -/
  ovfMulId : Nat
  /-- Second checked-arithmetic `(wrapped, overflowed)` local slot index. -/
  ovfAddId : Nat

namespace StageLocalIds

/-- Decidable well-formedness check ensuring all four stage local indices lie
strictly below `numLocals` and are pairwise distinct. -/
def wf (ids : StageLocalIds) (numLocals : Nat) : Bool :=
  Nat.blt ids.accId numLocals &&
    Nat.blt ids.tmpId numLocals &&
    Nat.blt ids.ovfMulId numLocals &&
    Nat.blt ids.ovfAddId numLocals &&
    !(Nat.beq ids.accId ids.tmpId) &&
    !(Nat.beq ids.accId ids.ovfMulId) &&
    !(Nat.beq ids.accId ids.ovfAddId) &&
    !(Nat.beq ids.tmpId ids.ovfMulId) &&
    !(Nat.beq ids.tmpId ids.ovfAddId) &&
    !(Nat.beq ids.ovfMulId ids.ovfAddId)

/-- Unpacked propositional witness of `StageLocalIds.wf ids numLocals = true`. -/
structure Unpacked (ids : StageLocalIds) (numLocals : Nat) : Prop where
  accLt : ids.accId < numLocals
  tmpLt : ids.tmpId < numLocals
  mulLt : ids.ovfMulId < numLocals
  addLt : ids.ovfAddId < numLocals
  accNeTmp : ids.accId ≠ ids.tmpId
  accNeMul : ids.accId ≠ ids.ovfMulId
  accNeAdd : ids.accId ≠ ids.ovfAddId
  tmpNeMul : ids.tmpId ≠ ids.ovfMulId
  tmpNeAdd : ids.tmpId ≠ ids.ovfAddId
  mulNeAdd : ids.ovfMulId ≠ ids.ovfAddId

private theorem and_elim {a b : Bool} (h : (a && b) = true) :
    a = true ∧ b = true := by
  cases a with
  | false => cases h
  | true =>
    cases b with
    | false => cases h
    | true => exact ⟨rfl, rfl⟩

private theorem ne_of_not_beq {a b : Nat} (h : (!(Nat.beq a b)) = true) :
    a ≠ b := by
  intro hEq
  rw [hEq, Nat.beq_refl b] at h
  cases h

/-- Unpacks `ids.wf numLocals = true` into all 4 bounds and 6 inequalities. -/
theorem wf_unpack {ids : StageLocalIds} {numLocals : Nat}
    (h : ids.wf numLocals = true) : Unpacked ids numLocals := by
  unfold wf at h
  let ⟨h1, hMulNeAdd⟩ := and_elim h
  let ⟨h2, hTmpNeAdd⟩ := and_elim h1
  let ⟨h3, hTmpNeMul⟩ := and_elim h2
  let ⟨h4, hAccNeAdd⟩ := and_elim h3
  let ⟨h5, hAccNeMul⟩ := and_elim h4
  let ⟨h6, hAccNeTmp⟩ := and_elim h5
  let ⟨h7, hAddLt⟩ := and_elim h6
  let ⟨h8, hMulLt⟩ := and_elim h7
  let ⟨hAccLt, hTmpLt⟩ := and_elim h8
  exact {
    accLt := Nat.le_of_ble_eq_true hAccLt
    tmpLt := Nat.le_of_ble_eq_true hTmpLt
    mulLt := Nat.le_of_ble_eq_true hMulLt
    addLt := Nat.le_of_ble_eq_true hAddLt
    accNeTmp := ne_of_not_beq hAccNeTmp
    accNeMul := ne_of_not_beq hAccNeMul
    accNeAdd := ne_of_not_beq hAccNeAdd
    tmpNeMul := ne_of_not_beq hTmpNeMul
    tmpNeAdd := ne_of_not_beq hTmpNeAdd
    mulNeAdd := ne_of_not_beq hMulNeAdd
  }

/-- Fail-closed: aliasing `accId = tmpId` makes `wf = false`. -/
theorem wf_false_of_acc_eq_tmp {ids : StageLocalIds} {numLocals : Nat}
    (hEq : ids.accId = ids.tmpId) : ids.wf numLocals = false := by
  cases hW : ids.wf numLocals with
  | false => rfl
  | true => exact False.elim ((wf_unpack hW).accNeTmp hEq)

/-- Fail-closed: an out-of-bounds `accId` makes `wf = false`. -/
theorem wf_false_of_acc_oob {ids : StageLocalIds} {numLocals : Nat}
    (hOob : numLocals ≤ ids.accId) : ids.wf numLocals = false := by
  cases hW : ids.wf numLocals with
  | false => rfl
  | true => exact False.elim (Nat.not_lt_of_ge hOob (wf_unpack hW).accLt)

/-- Decidable check that index `j` is distinct from all four stage slots. -/
def isBystander (ids : StageLocalIds) (j : Nat) : Bool :=
  !(Nat.beq j ids.accId) &&
    !(Nat.beq j ids.tmpId) &&
    !(Nat.beq j ids.ovfMulId) &&
    !(Nat.beq j ids.ovfAddId)

/-- Unpacks `ids.isBystander j = true` into the four distinctness proofs. -/
theorem isBystander_unpack {ids : StageLocalIds} {j : Nat}
    (h : ids.isBystander j = true) :
    j ≠ ids.accId ∧ j ≠ ids.tmpId ∧ j ≠ ids.ovfMulId ∧ j ≠ ids.ovfAddId := by
  unfold isBystander at h
  let ⟨h1, h4⟩ := and_elim h
  let ⟨h2, h3⟩ := and_elim h1
  let ⟨hA, hT⟩ := and_elim h2
  exact ⟨ne_of_not_beq hA, ne_of_not_beq hT, ne_of_not_beq h3, ne_of_not_beq h4⟩

end StageLocalIds

/-! ## Part II: Width-Parametric `intToInt` Cast & Checked/Unchecked Arithmetic -/

/-- Fixed-width integer width descriptor (`8, 16, 32, 64, 128` bits). -/
inductive ScalarWidth : Type where
  | u8 : ScalarWidth
  | u16 : ScalarWidth
  | u32 : ScalarWidth
  | u64 : ScalarWidth
  | u128 : ScalarWidth

namespace ScalarWidth

/-- Bit-width of a `ScalarWidth` (`8, 16, 32, 64, 128`). -/
def bits (w : ScalarWidth) : Nat :=
  match w with
  | .u8 => 8
  | .u16 => 16
  | .u32 => 32
  | .u64 => 64
  | .u128 => 128

/-- Unsigned modulus `2 ^ w.bits` via `ParametricCore.pow2`. -/
def modulus (w : ScalarWidth) : Nat :=
  pow2 w.bits

/-- Signed sign-bit threshold `2 ^ (w.bits - 1)` (`128, 32768, ...`). -/
def halfModulus (w : ScalarWidth) : Nat :=
  pow2 (w.bits - 1)

/-- Decidable equality on `ScalarWidth`. -/
def beq (w₁ w₂ : ScalarWidth) : Bool :=
  match w₁, w₂ with
  | .u8, .u8 => true
  | .u16, .u16 => true
  | .u32, .u32 => true
  | .u64, .u64 => true
  | .u128, .u128 => true
  | _, _ => false

/-- `ScalarWidth.beq` reflects equality. -/
theorem eq_of_beq {w₁ w₂ : ScalarWidth} (h : w₁.beq w₂ = true) : w₁ = w₂ := by
  cases w₁ <;> cases w₂ <;> first | rfl | cases h

/-- Reflexivity of `ScalarWidth.beq`. -/
theorem beq_refl (w : ScalarWidth) : w.beq w = true := by
  cases w <;> rfl

/-- Every `ScalarWidth` has positive bit-width. -/
theorem bits_pos (w : ScalarWidth) : 0 < w.bits := by
  cases w <;> exact Nat.zero_lt_succ _

/-- Every `ScalarWidth` has positive modulus. -/
theorem modulus_pos (w : ScalarWidth) : 0 < w.modulus :=
  pow2_pos w.bits

/-- `modulus w = 2 * halfModulus w`. -/
theorem modulus_eq_two_mul_half (w : ScalarWidth) :
    w.modulus = 2 * w.halfModulus := by
  cases w <;> rfl

/-- `halfModulus w < modulus w`. -/
theorem halfModulus_lt_modulus (w : ScalarWidth) :
    w.halfModulus < w.modulus := by
  rw [modulus_eq_two_mul_half]
  have hPos : 0 < w.halfModulus := pow2_pos (w.bits - 1)
  have hEq : 2 * w.halfModulus = w.halfModulus + w.halfModulus := by
    have h := Nat.add_mul 1 1 w.halfModulus
    rw [Nat.one_mul] at h
    exact h
  rw [hEq]
  exact Nat.lt_add_of_pos_right hPos

end ScalarWidth

/-- `pow2 (a + b) = pow2 a * pow2 b`. -/
theorem pow2_add (a b : Nat) : pow2 (a + b) = pow2 a * pow2 b := by
  induction a with
  | zero =>
    rw [Nat.zero_add, pow2_zero, Nat.one_mul]
  | succ k ih =>
    rw [Nat.succ_add, pow2_succ, pow2_succ, ih, Nat.mul_assoc]

/-- Monotonicity of `pow2`: `a ≤ b → pow2 a ≤ pow2 b`. -/
theorem pow2_le_pow2 {a b : Nat} (h : a ≤ b) : pow2 a ≤ pow2 b := by
  have hSplit : a + (b - a) = b := Nat.add_sub_of_le h
  rw [← hSplit, pow2_add]
  have hPos : 1 ≤ pow2 (b - a) := pow2_pos (b - a)
  have hMul := Nat.mul_le_mul_left (pow2 a) hPos
  rw [Nat.mul_one] at hMul
  exact hMul

/-- Strict monotonicity of `pow2`: `a < b → pow2 a < pow2 b`. -/
theorem pow2_lt_pow2 {a b : Nat} (h : a < b) : pow2 a < pow2 b := by
  have hSucc : pow2 (a + 1) ≤ pow2 b := pow2_le_pow2 h
  rw [pow2_succ] at hSucc
  have hLt : pow2 a < 2 * pow2 a := by
    have hEq : 2 * pow2 a = pow2 a + pow2 a := by
      have hm := Nat.add_mul 1 1 (pow2 a)
      rw [Nat.one_mul] at hm
      exact hm
    rw [hEq]
    exact Nat.lt_add_of_pos_right (pow2_pos a)
  exact Nat.lt_of_lt_of_le hLt hSucc

/-- Factor decomposition: `a ≤ b → pow2 b = pow2 a * pow2 (b - a)`. -/
theorem pow2_factor_of_le {a b : Nat} (h : a ≤ b) :
    pow2 b = pow2 a * pow2 (b - a) := by
  rw [← pow2_add, Nat.add_sub_of_le h]

/-- Modular reduction through a larger power of two: for `a ≤ b`,
`(x % pow2 b) % pow2 a = x % pow2 a`. -/
theorem mod_pow2_mod_pow2_of_le (x : Nat) {a b : Nat} (h : a ≤ b) :
    (x % pow2 b) % pow2 a = x % pow2 a := by
  have hFac : pow2 b = pow2 a * pow2 (b - a) := pow2_factor_of_le h
  have h1 : x = pow2 a * (pow2 (b - a) * (x / pow2 b)) + x % pow2 b := by
    rw [← Nat.mul_assoc, ← hFac]
    exact (Nat.div_add_mod x (pow2 b)).symm
  conv => rhs; rw [h1]
  rw [Nat.add_comm (pow2 a * (pow2 (b - a) * (x / pow2 b))) (x % pow2 b),
    Nat.add_mul_mod_self_left]

/-- Adding a multiple of `pow2 a` does not change `mod (pow2 a)`. -/
theorem add_pow2_sub_mod_pow2 (x : Nat) {a b : Nat} (h : a ≤ b) :
    ((pow2 b - pow2 a) + x) % pow2 a = x % pow2 a := by
  have hSub : pow2 b - pow2 a = pow2 a * (pow2 (b - a) - 1) := by
    rw [pow2_factor_of_le h, Nat.mul_sub_left_distrib, Nat.mul_one]
  rw [hSub, Nat.add_comm, Nat.add_mul_mod_self_left]

/-- Fixed-width `intToInt` bit-pattern cast from `(srcW, srcSigned)` to `dstW`:
normalizes `x` to `srcW` bits (`raw = x % srcW.modulus`), then:
- if `dstW.bits ≤ srcW.bits`: modular narrowing truncation `raw % dstW.modulus`;
- if `srcW.bits < dstW.bits` and `srcSigned = true` and `srcW.halfModulus ≤ raw`:
  signed two's-complement sign-extension `(dstW.modulus - srcW.modulus) + raw`;
- otherwise: zero-extension `raw`. -/
def intToIntCast (srcW : ScalarWidth) (srcSigned : Bool) (dstW : ScalarWidth)
    (x : Nat) : Nat :=
  let raw := x % srcW.modulus
  match Nat.ble dstW.bits srcW.bits with
  | true => raw % dstW.modulus
  | false =>
    match srcSigned && Nat.ble srcW.halfModulus raw with
    | true => (dstW.modulus - srcW.modulus) + raw
    | false => raw

/-- Every `intToIntCast` output fits strictly below `dstW.modulus`. -/
theorem intToIntCast_lt_modulus (srcW : ScalarWidth) (srcSigned : Bool)
    (dstW : ScalarWidth) (x : Nat) :
    intToIntCast srcW srcSigned dstW x < dstW.modulus := by
  unfold intToIntCast
  dsimp only
  cases hLe : Nat.ble dstW.bits srcW.bits with
  | true => exact Nat.mod_lt _ dstW.modulus_pos
  | false =>
    have hLtBits : srcW.bits < dstW.bits := by
      cases Nat.lt_or_ge srcW.bits dstW.bits with
      | inl hLt => exact hLt
      | inr hGe =>
        rw [Nat.ble_eq_true_of_le hGe] at hLe
        cases hLe
    have hRawLt : x % srcW.modulus < srcW.modulus :=
      Nat.mod_lt x srcW.modulus_pos
    have hModLe : srcW.modulus ≤ dstW.modulus :=
      pow2_le_pow2 (Nat.le_of_lt hLtBits)
    cases (srcSigned && Nat.ble srcW.halfModulus (x % srcW.modulus)) with
    | false => exact Nat.lt_of_lt_of_le hRawLt hModLe
    | true =>
      have hAdd :
          (dstW.modulus - srcW.modulus) + x % srcW.modulus <
            (dstW.modulus - srcW.modulus) + srcW.modulus :=
        Nat.add_lt_add_left hRawLt (dstW.modulus - srcW.modulus)
      rw [Nat.sub_add_cancel hModLe] at hAdd
      exact hAdd

/-- Narrowing `intToIntCast` (`dstW.bits ≤ srcW.bits`) equals direct modular
truncation `x % dstW.modulus`. -/
theorem intToIntCast_narrow_eq_mod (srcW : ScalarWidth) (srcSigned : Bool)
    (dstW : ScalarWidth) (x : Nat) (hLe : dstW.bits ≤ srcW.bits) :
    intToIntCast srcW srcSigned dstW x = x % dstW.modulus := by
  unfold intToIntCast
  dsimp only
  rw [Nat.ble_eq_true_of_le hLe]
  exact mod_pow2_mod_pow2_of_le x hLe

/-- Narrowing under bound is exact: when `dstW.bits ≤ srcW.bits` and
`x < dstW.modulus`, `intToIntCast srcW srcSigned dstW x = x`. -/
theorem intToIntCast_narrow_exact (srcW : ScalarWidth) (srcSigned : Bool)
    (dstW : ScalarWidth) {x : Nat} (hLe : dstW.bits ≤ srcW.bits)
    (hx : x < dstW.modulus) :
    intToIntCast srcW srcSigned dstW x = x := by
  rw [intToIntCast_narrow_eq_mod srcW srcSigned dstW x hLe]
  exact Nat.mod_eq_of_lt hx

/-- Unsigned widening (or same-width cast) is exact for `x < srcW.modulus`. -/
theorem intToIntCast_widen_unsigned_exact (srcW dstW : ScalarWidth) {x : Nat}
    (hLe : srcW.bits ≤ dstW.bits) (hx : x < srcW.modulus) :
    intToIntCast srcW false dstW x = x := by
  unfold intToIntCast
  dsimp only
  rw [Nat.mod_eq_of_lt hx]
  cases hRev : Nat.ble dstW.bits srcW.bits with
  | false => rfl
  | true =>
    have hEqBits : dstW.bits = srcW.bits :=
      Nat.le_antisymm (Nat.le_of_ble_eq_true hRev) hLe
    have hEqMod : dstW.modulus = srcW.modulus := by
      unfold ScalarWidth.modulus
      rw [hEqBits]
    rw [hEqMod]
    exact Nat.mod_eq_of_lt hx

/-- Signed widening preserves non-negative values (`x < srcW.halfModulus`). -/
theorem intToIntCast_widen_signed_nonneg (srcW dstW : ScalarWidth) {x : Nat}
    (hLt : srcW.bits < dstW.bits) (hx : x < srcW.halfModulus) :
    intToIntCast srcW true dstW x = x := by
  have hMod : x < srcW.modulus := Nat.lt_trans hx srcW.halfModulus_lt_modulus
  have hNotLe : Nat.ble dstW.bits srcW.bits = false := by
    cases hB : Nat.ble dstW.bits srcW.bits with
    | false => rfl
    | true => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_ble_eq_true hB) hLt)
  have hNotNeg : Nat.ble srcW.halfModulus x = false := by
    cases hB : Nat.ble srcW.halfModulus x with
    | false => rfl
    | true => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_ble_eq_true hB) hx)
  unfold intToIntCast
  dsimp only
  rw [Nat.mod_eq_of_lt hMod, hNotLe, hNotNeg]
  rfl

/-- Signed widening sign-extends negative two's-complement bit patterns
(`srcW.halfModulus ≤ x < srcW.modulus`), preserving the negative magnitude
`dstW.modulus - out = srcW.modulus - x`. -/
theorem intToIntCast_widen_signed_neg (srcW dstW : ScalarWidth) {x : Nat}
    (hLt : srcW.bits < dstW.bits)
    (hNeg : srcW.halfModulus ≤ x) (hx : x < srcW.modulus) :
    intToIntCast srcW true dstW x = (dstW.modulus - srcW.modulus) + x ∧
    dstW.modulus - intToIntCast srcW true dstW x = srcW.modulus - x := by
  have hNotLe : Nat.ble dstW.bits srcW.bits = false := by
    cases hB : Nat.ble dstW.bits srcW.bits with
    | false => rfl
    | true => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_ble_eq_true hB) hLt)
  have hEq : intToIntCast srcW true dstW x = (dstW.modulus - srcW.modulus) + x := by
    unfold intToIntCast
    dsimp only
    rw [Nat.mod_eq_of_lt hx, hNotLe, Nat.ble_eq_true_of_le hNeg]
    rfl
  refine ⟨hEq, ?_⟩
  rw [hEq]
  have hModLe : srcW.modulus ≤ dstW.modulus :=
    pow2_le_pow2 (Nat.le_of_lt hLt)
  have hSum :
      ((dstW.modulus - srcW.modulus) + x) + (srcW.modulus - x) = dstW.modulus := by
    rw [Nat.add_assoc, Nat.add_sub_of_le (Nat.le_of_lt hx),
      Nat.sub_add_cancel hModLe]
  have hCancel := congrArg (fun k => k - ((dstW.modulus - srcW.modulus) + x)) hSum
  rw [Nat.add_sub_cancel_left] at hCancel
  exact hCancel.symm

/-- Universal widening-then-narrowing round-trip for BOTH unsigned and signed
`intToIntCast`: whenever `srcW.bits ≤ dstW.bits` and `x < srcW.modulus`,
widening to `dstW` and narrowing back to `srcW` recovers `x` identically. -/
theorem intToIntCast_widen_narrow_roundtrip (srcW dstW : ScalarWidth)
    (srcSigned dstSigned : Bool) {x : Nat}
    (hLe : srcW.bits ≤ dstW.bits) (hx : x < srcW.modulus) :
    intToIntCast dstW dstSigned srcW (intToIntCast srcW srcSigned dstW x) = x := by
  rw [intToIntCast_narrow_eq_mod dstW dstSigned srcW _ hLe]
  unfold intToIntCast
  dsimp only
  rw [Nat.mod_eq_of_lt hx]
  cases hRev : Nat.ble dstW.bits srcW.bits with
  | true =>
    have hEqBits : dstW.bits = srcW.bits :=
      Nat.le_antisymm (Nat.le_of_ble_eq_true hRev) hLe
    have hEqMod : dstW.modulus = srcW.modulus := by
      unfold ScalarWidth.modulus; rw [hEqBits]
    rw [hEqMod, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hx]
  | false =>
    cases (srcSigned && Nat.ble srcW.halfModulus x) with
    | false => exact Nat.mod_eq_of_lt hx
    | true =>
      dsimp only
      unfold ScalarWidth.modulus
      rw [add_pow2_sub_mod_pow2 x hLe]
      exact Nat.mod_eq_of_lt hx

/-- Signed widening keeps the sign bit set: a negative two's-complement bit
pattern (`srcW.halfModulus ≤ x < srcW.modulus`) sign-extends to a `dstW` bit
pattern that is still negative (`dstW.halfModulus ≤ out`). -/
theorem intToIntCast_widen_signed_neg_sign (srcW dstW : ScalarWidth) {x : Nat}
    (hLt : srcW.bits < dstW.bits)
    (hNeg : srcW.halfModulus ≤ x) (hx : x < srcW.modulus) :
    dstW.halfModulus ≤ intToIntCast srcW true dstW x := by
  have hS : srcW.modulus ≤ dstW.halfModulus :=
    pow2_le_pow2 (Nat.le_sub_one_of_lt hLt)
  have hD : dstW.modulus = dstW.halfModulus + dstW.halfModulus := by
    rw [dstW.modulus_eq_two_mul_half, Nat.two_mul]
  have hSub : dstW.halfModulus ≤ dstW.modulus - srcW.modulus := by
    rw [hD]
    exact Nat.le_sub_of_add_le (Nat.add_le_add_left hS _)
  rw [(intToIntCast_widen_signed_neg srcW dstW hLt hNeg hx).1]
  exact Nat.le_trans hSub (Nat.le_add_right _ _)

/-- Signed narrowing of an in-range negative value is exact: when
`dstW.bits ≤ srcW.bits` and `x` is a negative `srcW` bit pattern whose signed
value fits `dstW` (`srcW.modulus - dstW.halfModulus ≤ x < srcW.modulus`), the
truncated `dstW` bit pattern drops exactly the `srcW.modulus - dstW.modulus`
sign-extension bits, is still negative (`dstW.halfModulus ≤ out`), and
preserves the negative magnitude `dstW.modulus - out = srcW.modulus - x`. -/
theorem intToIntCast_narrow_signed_neg (srcW : ScalarWidth) (srcSigned : Bool)
    (dstW : ScalarWidth) {x : Nat} (hLe : dstW.bits ≤ srcW.bits)
    (hLo : srcW.modulus - dstW.halfModulus ≤ x) (hx : x < srcW.modulus) :
    (srcW.modulus - dstW.modulus) + intToIntCast srcW srcSigned dstW x = x ∧
    dstW.halfModulus ≤ intToIntCast srcW srcSigned dstW x ∧
    dstW.modulus - intToIntCast srcW srcSigned dstW x = srcW.modulus - x := by
  have hDS : dstW.modulus ≤ srcW.modulus := pow2_le_pow2 hLe
  have hD : dstW.modulus = dstW.halfModulus + dstW.halfModulus := by
    rw [dstW.modulus_eq_two_mul_half, Nat.two_mul]
  have hBase : srcW.modulus - dstW.modulus ≤ x :=
    Nat.le_trans
      (Nat.sub_le_sub_left (Nat.le_of_lt dstW.halfModulus_lt_modulus)
        srcW.modulus) hLo
  have hXeq :
      (srcW.modulus - dstW.modulus) + (x - (srcW.modulus - dstW.modulus)) = x :=
    Nat.add_sub_of_le hBase
  have hYlt : x - (srcW.modulus - dstW.modulus) < dstW.modulus := by
    have h1 :
        (srcW.modulus - dstW.modulus) + (x - (srcW.modulus - dstW.modulus)) <
          (srcW.modulus - dstW.modulus) + dstW.modulus := by
      rw [hXeq, Nat.sub_add_cancel hDS]
      exact hx
    cases Nat.lt_or_ge (x - (srcW.modulus - dstW.modulus)) dstW.modulus with
    | inl hLtD => exact hLtD
    | inr hGeD =>
      exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_left hGeD _))
  have hCast : intToIntCast srcW srcSigned dstW x =
      x - (srcW.modulus - dstW.modulus) := by
    rw [intToIntCast_narrow_eq_mod srcW srcSigned dstW x hLe]
    have hMod' :
        ((srcW.modulus - dstW.modulus) +
            (x - (srcW.modulus - dstW.modulus))) % dstW.modulus =
          (x - (srcW.modulus - dstW.modulus)) % dstW.modulus :=
      add_pow2_sub_mod_pow2 (x - (srcW.modulus - dstW.modulus)) hLe
    rw [hXeq, Nat.mod_eq_of_lt hYlt] at hMod'
    exact hMod'
  have hSplit : srcW.modulus - dstW.halfModulus =
      (srcW.modulus - dstW.modulus) + dstW.halfModulus := by
    apply Nat.sub_eq_of_eq_add
    rw [Nat.add_assoc, ← hD, Nat.sub_add_cancel hDS]
  have hYge : dstW.halfModulus ≤ x - (srcW.modulus - dstW.modulus) := by
    have h2 :
        (srcW.modulus - dstW.modulus) + dstW.halfModulus ≤
          (srcW.modulus - dstW.modulus) + (x - (srcW.modulus - dstW.modulus)) := by
      rw [hXeq, ← hSplit]
      exact hLo
    exact Nat.le_of_add_le_add_left h2
  have hMag : dstW.modulus - (x - (srcW.modulus - dstW.modulus)) =
      srcW.modulus - x := by
    have h3 : srcW.modulus -
        ((srcW.modulus - dstW.modulus) + (x - (srcW.modulus - dstW.modulus))) =
          dstW.modulus - (x - (srcW.modulus - dstW.modulus)) := by
      rw [Nat.sub_add_eq,
        Nat.sub_eq_of_eq_add (Nat.add_sub_of_le hDS).symm]
    rw [hXeq] at h3
    exact h3.symm
  rw [hCast]
  exact ⟨hXeq, hYge, hMag⟩

/-- Checked unsigned addition `(wrappedBits, overflowed)` at width `w`. -/
def addWithOverflowU (w : ScalarWidth) (a b : Nat) : Nat × Bool :=
  let sum := a + b
  (sum % w.modulus, Nat.ble w.modulus sum)

/-- Checked unsigned subtraction `(wrappedBits, overflowed)` at width `w`:
overflows iff `a < b` (underflow) or either operand is out of width range. -/
def subWithOverflowU (w : ScalarWidth) (a b : Nat) : Nat × Bool :=
  let a' := a % w.modulus
  let b' := b % w.modulus
  let wrapped := (a' + w.modulus - b') % w.modulus
  let ovf := Nat.blt a b || Nat.ble w.modulus a || Nat.ble w.modulus b
  (wrapped, ovf)

/-- Checked unsigned multiplication `(wrappedBits, overflowed)` at width `w`. -/
def mulWithOverflowU (w : ScalarWidth) (a b : Nat) : Nat × Bool :=
  let prod := a * b
  (prod % w.modulus, Nat.ble w.modulus prod)

/-- Checked unsigned left-shift `(wrappedBits, overflowed)` at width `w`
(matching Rust `overflowing_shl`: masks shift amount modulo `w.bits`, and sets
`overflowed = true` iff `w.bits ≤ shift`). -/
def shlWithOverflowU (w : ScalarWidth) (a shift : Nat) : Nat × Bool :=
  let masked := shift % w.bits
  ((a * pow2 masked) % w.modulus, Nat.ble w.bits shift)

/-- Interval-guarded unchecked unsigned addition (`none` on overflow). -/
def addUncheckedU (w : ScalarWidth) (a b : Nat) : Option Nat :=
  let r := addWithOverflowU w a b
  match r.2 with
  | true => none
  | false => some r.1

/-- Interval-guarded unchecked unsigned subtraction (`none` on underflow/OOB). -/
def subUncheckedU (w : ScalarWidth) (a b : Nat) : Option Nat :=
  let r := subWithOverflowU w a b
  match r.2 with
  | true => none
  | false => some r.1

/-- Interval-guarded unchecked unsigned multiplication (`none` on overflow). -/
def mulUncheckedU (w : ScalarWidth) (a b : Nat) : Option Nat :=
  let r := mulWithOverflowU w a b
  match r.2 with
  | true => none
  | false => some r.1

/-- Interval-guarded unchecked unsigned left-shift (`none` when
`w.bits ≤ shift`). -/
def shlUncheckedU (w : ScalarWidth) (a shift : Nat) : Option Nat :=
  let r := shlWithOverflowU w a shift
  match r.2 with
  | true => none
  | false => some r.1

private theorem nat_ble_false_iff_lt {a b : Nat} :
    Nat.ble a b = false ↔ b < a := by
  constructor
  · intro hF
    cases Nat.lt_or_ge b a with
    | inl hLt => exact hLt
    | inr hGe =>
      rw [Nat.ble_eq_true_of_le hGe] at hF
      cases hF
  · intro hLt
    cases hB : Nat.ble a b with
    | false => rfl
    | true => exact False.elim (Nat.not_lt_of_ge (Nat.le_of_ble_eq_true hB) hLt)

/-- Exact no-overflow equivalence for `addWithOverflowU`. -/
theorem addWithOverflowU_no_overflow_iff (w : ScalarWidth) (a b : Nat) :
    (addWithOverflowU w a b).2 = false ↔ a + b < w.modulus :=
  nat_ble_false_iff_lt

/-- Exact evaluation of `addWithOverflowU` under `a + b < w.modulus`. -/
theorem addWithOverflowU_of_lt (w : ScalarWidth) {a b : Nat}
    (h : a + b < w.modulus) :
    addWithOverflowU w a b = (a + b, false) := by
  unfold addWithOverflowU
  dsimp only
  rw [Nat.mod_eq_of_lt h, nat_ble_false_iff_lt.mpr h]

/-- Fail-closed negative lemma: out-of-range sum sets `overflowed = true`. -/
theorem addWithOverflowU_overflow_of_ge (w : ScalarWidth) {a b : Nat}
    (h : w.modulus ≤ a + b) :
    (addWithOverflowU w a b).2 = true :=
  Nat.ble_eq_true_of_le h

/-- Exact no-overflow equivalence for `subWithOverflowU`. -/
theorem subWithOverflowU_no_overflow_iff (w : ScalarWidth) (a b : Nat) :
    (subWithOverflowU w a b).2 = false ↔
      a < w.modulus ∧ b < w.modulus ∧ b ≤ a := by
  unfold subWithOverflowU
  dsimp only
  constructor
  · intro hF
    cases h1 : Nat.blt a b with
    | true => rw [h1] at hF; cases hF
    | false =>
      cases h2 : Nat.ble w.modulus a with
      | true => rw [h1, h2] at hF; cases hF
      | false =>
        cases h3 : Nat.ble w.modulus b with
        | true => rw [h1, h2, h3] at hF; cases hF
        | false =>
          have hBa : b ≤ a := by
            cases Nat.lt_or_ge a b with
            | inl hLt =>
              have hBlt : Nat.blt a b = true := Nat.ble_eq_true_of_le hLt
              rw [hBlt] at h1
              cases h1
            | inr hGe => exact hGe
          exact ⟨nat_ble_false_iff_lt.mp h2, nat_ble_false_iff_lt.mp h3, hBa⟩
  · intro ⟨hA, hB, hLe⟩
    have h1 : Nat.blt a b = false := nat_ble_false_iff_lt.mpr (Nat.lt_succ_of_le hLe)
    rw [h1, nat_ble_false_iff_lt.mpr hA, nat_ble_false_iff_lt.mpr hB]
    rfl

/-- Exact evaluation of `subWithOverflowU` when `b ≤ a < w.modulus`. -/
theorem subWithOverflowU_of_le (w : ScalarWidth) {a b : Nat}
    (hA : a < w.modulus) (hLe : b ≤ a) :
    subWithOverflowU w a b = (a - b, false) := by
  have hB : b < w.modulus := Nat.lt_of_le_of_lt hLe hA
  have hOvf : (subWithOverflowU w a b).2 = false :=
    (subWithOverflowU_no_overflow_iff w a b).mpr ⟨hA, hB, hLe⟩
  have hSubAdd : a + w.modulus - b = (a - b) + w.modulus := by
    rw [Nat.add_comm a w.modulus, Nat.add_sub_assoc hLe w.modulus, Nat.add_comm]
  have hVal : (subWithOverflowU w a b).1 = a - b := by
    unfold subWithOverflowU
    dsimp only
    rw [Nat.mod_eq_of_lt hA, Nat.mod_eq_of_lt hB, hSubAdd,
      Nat.add_mod_right, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le a b) hA)]
  cases hR : subWithOverflowU w a b with
  | mk x fl =>
    rw [hR] at hVal hOvf
    dsimp only at hVal hOvf
    rw [hVal, hOvf]

/-- Fail-closed negative lemma: underflow (`a < b`) sets `overflowed = true`. -/
theorem subWithOverflowU_overflow_of_lt (w : ScalarWidth) {a b : Nat}
    (hLt : a < b) :
    (subWithOverflowU w a b).2 = true := by
  unfold subWithOverflowU
  dsimp only
  have hBlt : Nat.blt a b = true := Nat.ble_eq_true_of_le hLt
  rw [hBlt]
  rfl

/-- Exact no-overflow equivalence for `mulWithOverflowU`. -/
theorem mulWithOverflowU_no_overflow_iff (w : ScalarWidth) (a b : Nat) :
    (mulWithOverflowU w a b).2 = false ↔ a * b < w.modulus :=
  nat_ble_false_iff_lt

/-- Exact evaluation of `mulWithOverflowU` under `a * b < w.modulus`. -/
theorem mulWithOverflowU_of_lt (w : ScalarWidth) {a b : Nat}
    (h : a * b < w.modulus) :
    mulWithOverflowU w a b = (a * b, false) := by
  unfold mulWithOverflowU
  dsimp only
  rw [Nat.mod_eq_of_lt h, nat_ble_false_iff_lt.mpr h]

/-- Fail-closed negative lemma: out-of-range product sets `overflowed = true`. -/
theorem mulWithOverflowU_overflow_of_ge (w : ScalarWidth) {a b : Nat}
    (h : w.modulus ≤ a * b) :
    (mulWithOverflowU w a b).2 = true :=
  Nat.ble_eq_true_of_le h

/-- Exact no-overflow equivalence for `shlWithOverflowU`. -/
theorem shlWithOverflowU_no_overflow_iff (w : ScalarWidth) (a shift : Nat) :
    (shlWithOverflowU w a shift).2 = false ↔ shift < w.bits :=
  nat_ble_false_iff_lt

/-- Exact evaluation of `shlWithOverflowU` when `shift < w.bits` and
`a * pow2 shift < w.modulus`. -/
theorem shlWithOverflowU_of_lt (w : ScalarWidth) {a shift : Nat}
    (hShift : shift < w.bits) (hVal : a * pow2 shift < w.modulus) :
    shlWithOverflowU w a shift = (a * pow2 shift, false) := by
  unfold shlWithOverflowU
  dsimp only
  rw [Nat.mod_eq_of_lt hShift, Nat.mod_eq_of_lt hVal,
    nat_ble_false_iff_lt.mpr hShift]

/-- Fail-closed negative lemma: `w.bits ≤ shift` sets `overflowed = true`. -/
theorem shlWithOverflowU_overflow_of_ge (w : ScalarWidth) (a : Nat)
    {shift : Nat} (h : w.bits ≤ shift) :
    (shlWithOverflowU w a shift).2 = true :=
  Nat.ble_eq_true_of_le h

/-- Exact equivalence for `addUncheckedU`. -/
theorem addUncheckedU_eq_some_iff (w : ScalarWidth) (a b res : Nat) :
    addUncheckedU w a b = some res ↔ a + b < w.modulus ∧ res = a + b := by
  unfold addUncheckedU
  dsimp only
  cases hOvf : (addWithOverflowU w a b).2 with
  | true =>
    constructor
    · intro h; cases h
    · intro ⟨hLt, _⟩
      rw [(addWithOverflowU_no_overflow_iff w a b).mpr hLt] at hOvf
      cases hOvf
  | false =>
    have hLt := (addWithOverflowU_no_overflow_iff w a b).mp hOvf
    have hEq := addWithOverflowU_of_lt w hLt
    rw [hEq]
    constructor
    · intro h; exact ⟨hLt, (Option.some.inj h).symm⟩
    · intro ⟨_, hRes⟩; rw [hRes]

/-- Exact equivalence for `subUncheckedU`. -/
theorem subUncheckedU_eq_some_iff (w : ScalarWidth) (a b res : Nat) :
    subUncheckedU w a b = some res ↔
      a < w.modulus ∧ b < w.modulus ∧ b ≤ a ∧ res = a - b := by
  unfold subUncheckedU
  dsimp only
  cases hOvf : (subWithOverflowU w a b).2 with
  | true =>
    constructor
    · intro h; cases h
    · intro ⟨hA, hB, hLe, _⟩
      rw [(subWithOverflowU_no_overflow_iff w a b).mpr ⟨hA, hB, hLe⟩] at hOvf
      cases hOvf
  | false =>
    have ⟨hA, hB, hLe⟩ := (subWithOverflowU_no_overflow_iff w a b).mp hOvf
    have hEq := subWithOverflowU_of_le w hA hLe
    rw [hEq]
    constructor
    · intro h; exact ⟨hA, hB, hLe, (Option.some.inj h).symm⟩
    · intro ⟨_, _, _, hRes⟩; rw [hRes]

/-- Exact equivalence for `mulUncheckedU`. -/
theorem mulUncheckedU_eq_some_iff (w : ScalarWidth) (a b res : Nat) :
    mulUncheckedU w a b = some res ↔ a * b < w.modulus ∧ res = a * b := by
  unfold mulUncheckedU
  dsimp only
  cases hOvf : (mulWithOverflowU w a b).2 with
  | true =>
    constructor
    · intro h; cases h
    · intro ⟨hLt, _⟩
      rw [(mulWithOverflowU_no_overflow_iff w a b).mpr hLt] at hOvf
      cases hOvf
  | false =>
    have hLt := (mulWithOverflowU_no_overflow_iff w a b).mp hOvf
    have hEq := mulWithOverflowU_of_lt w hLt
    rw [hEq]
    constructor
    · intro h; exact ⟨hLt, (Option.some.inj h).symm⟩
    · intro ⟨_, hRes⟩; rw [hRes]

/-- Exact equivalence for `shlUncheckedU` (matches Rust `overflowing_shl`:
succeeds iff `shift < w.bits`, returning `(a * pow2 shift) % w.modulus`). -/
theorem shlUncheckedU_eq_some_iff (w : ScalarWidth) (a shift res : Nat) :
    shlUncheckedU w a shift = some res ↔
      shift < w.bits ∧ res = (a * pow2 shift) % w.modulus := by
  unfold shlUncheckedU
  dsimp only
  cases hOvf : (shlWithOverflowU w a shift).2 with
  | true =>
    constructor
    · intro h; cases h
    · intro ⟨hLt, _⟩
      rw [(shlWithOverflowU_no_overflow_iff w a shift).mpr hLt] at hOvf
      cases hOvf
  | false =>
    have hLt := (shlWithOverflowU_no_overflow_iff w a shift).mp hOvf
    have hVal : (shlWithOverflowU w a shift).1 = (a * pow2 shift) % w.modulus := by
      unfold shlWithOverflowU
      dsimp only
      rw [Nat.mod_eq_of_lt hLt]
    rw [hVal]
    constructor
    · intro h; exact ⟨hLt, (Option.some.inj h).symm⟩
    · intro ⟨_, hRes⟩; rw [hRes]

/-- Fail-closed: `addUncheckedU` returns `none` on overflow. -/
theorem addUncheckedU_none_of_ge (w : ScalarWidth) {a b : Nat}
    (h : w.modulus ≤ a + b) : addUncheckedU w a b = none := by
  unfold addUncheckedU
  dsimp only
  rw [addWithOverflowU_overflow_of_ge w h]

/-- Fail-closed: `subUncheckedU` returns `none` on underflow. -/
theorem subUncheckedU_none_of_lt (w : ScalarWidth) {a b : Nat} (h : a < b) :
    subUncheckedU w a b = none := by
  unfold subUncheckedU
  dsimp only
  rw [subWithOverflowU_overflow_of_lt w h]

/-- Fail-closed: `mulUncheckedU` returns `none` on overflow. -/
theorem mulUncheckedU_none_of_ge (w : ScalarWidth) {a b : Nat}
    (h : w.modulus ≤ a * b) : mulUncheckedU w a b = none := by
  unfold mulUncheckedU
  dsimp only
  rw [mulWithOverflowU_overflow_of_ge w h]

/-- Fail-closed: `shlUncheckedU` returns `none` when `w.bits ≤ shift`. -/
theorem shlUncheckedU_none_of_ge (w : ScalarWidth) (a : Nat) {shift : Nat}
    (h : w.bits ≤ shift) : shlUncheckedU w a shift = none := by
  unfold shlUncheckedU
  dsimp only
  rw [shlWithOverflowU_overflow_of_ge w a h]

/-! ### Signed Two's-Complement Checked & Unchecked Arithmetic (`*WithOverflowS`, `*UncheckedS`) -/

/-- Order-preserving bijection (`toBiased w x = (x % M + H) % M`) mapping
two's-complement bit patterns `x < w.modulus` monotonically from signed values
`[-H, H - 1]` onto `[0, M - 1]` (`INT_MIN ↦ 0`, `-1 ↦ H - 1`, `0 ↦ H`,
`INT_MAX ↦ M - 1`). -/
def toBiased (w : ScalarWidth) (x : Nat) : Nat :=
  (x % w.modulus + w.halfModulus) % w.modulus

/-- Every `toBiased` value lies strictly below `w.modulus`. -/
theorem toBiased_lt_modulus (w : ScalarWidth) (x : Nat) :
    toBiased w x < w.modulus :=
  Nat.mod_lt _ w.modulus_pos

/-- For non-negative two's-complement values (`x < w.halfModulus`),
`toBiased w x = x + w.halfModulus`. -/
theorem toBiased_nonneg (w : ScalarWidth) {x : Nat} (hx : x < w.halfModulus) :
    toBiased w x = x + w.halfModulus := by
  have hMod : x < w.modulus := Nat.lt_trans hx w.halfModulus_lt_modulus
  have hSumLt : x + w.halfModulus < w.modulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
    exact Nat.add_lt_add_right hx w.halfModulus
  unfold toBiased
  rw [Nat.mod_eq_of_lt hMod, Nat.mod_eq_of_lt hSumLt]

/-- For negative two's-complement values (`w.halfModulus ≤ x < w.modulus`),
`toBiased w x = x - w.halfModulus`. -/
theorem toBiased_neg (w : ScalarWidth) {x : Nat}
    (hNeg : w.halfModulus ≤ x) (hx : x < w.modulus) :
    toBiased w x = x - w.halfModulus := by
  have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
  have hSubLt : x - w.halfModulus < w.halfModulus := by
    have h1 : w.halfModulus + (x - w.halfModulus) < w.halfModulus + w.halfModulus := by
      rw [Nat.add_sub_of_le hNeg, ← hModEq]
      exact hx
    cases Nat.lt_or_ge (x - w.halfModulus) w.halfModulus with
    | inl hLt => exact hLt
    | inr hGe => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_left hGe _))
  have hSubLtM : x - w.halfModulus < w.modulus :=
    Nat.lt_trans hSubLt w.halfModulus_lt_modulus
  have hSplit : x + w.halfModulus = (x - w.halfModulus) + w.modulus := by
    rw [hModEq, ← Nat.add_assoc, Nat.sub_add_cancel hNeg]
  unfold toBiased
  rw [Nat.mod_eq_of_lt hx, hSplit, Nat.add_mod_right, Nat.mod_eq_of_lt hSubLtM]

private theorem add_mod_left_eq (a b m : Nat) :
    (a % m + b) % m = (a + b) % m := by
  have h1 : a + b = (a % m + b) + m * (a / m) := by
    conv => lhs; rw [← Nat.div_add_mod a m]
    rw [Nat.add_assoc (m * (a / m)) (a % m) b, Nat.add_comm]
  rw [h1, Nat.add_mul_mod_self_left]

private theorem add_mod_right_eq (a b m : Nat) :
    (a + b % m) % m = (a + b) % m := by
  rw [Nat.add_comm a (b % m), add_mod_left_eq, Nat.add_comm]

private theorem sub_add_comm_nat {a b c : Nat} (h : b ≤ a) :
    (a - b) + c = (a + c) - b := by
  have h1 : ((a - b) + c) + b = a + c := by
    rw [Nat.add_assoc, Nat.add_comm c b, ← Nat.add_assoc, Nat.sub_add_cancel h]
  have h2 := congrArg (fun k => k - b) h1
  rw [Nat.add_sub_cancel] at h2
  exact h2

/-- `toBiased w` is an involution on canonical `w`-bit patterns (`x < w.modulus`). -/
theorem toBiased_involutive (w : ScalarWidth) (x : Nat) :
    toBiased w (toBiased w x) = x % w.modulus := by
  have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
  unfold toBiased
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ w.modulus_pos),
    add_mod_left_eq, Nat.add_assoc, ← hModEq, Nat.add_mod_right,
    Nat.mod_eq_of_lt (Nat.mod_lt x w.modulus_pos)]

/-- `toBiased w` is injective on canonical `w`-bit patterns. -/
theorem toBiased_injective (w : ScalarWidth) {a b : Nat}
    (ha : a < w.modulus) (hb : b < w.modulus)
    (hEq : toBiased w a = toBiased w b) : a = b := by
  have h1 := congrArg (toBiased w) hEq
  rw [toBiased_involutive, toBiased_involutive,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
  exact h1

/-- Checked signed two's-complement addition `(wrappedBits, overflowed)` at
width `w` (matching Rust `iN::overflowing_add`, failing closed if either raw
input `≥ w.modulus`). -/
def addWithOverflowS (w : ScalarWidth) (a b : Nat) : Nat × Bool :=
  let a' := a % w.modulus
  let b' := b % w.modulus
  let wrapped := (a' + b') % w.modulus
  let ba := toBiased w a'
  let bb := toBiased w b'
  let ovf := Nat.ble w.modulus a || Nat.ble w.modulus b ||
    Nat.blt (ba + bb) w.halfModulus ||
    Nat.ble (w.modulus + w.halfModulus) (ba + bb)
  (wrapped, ovf)

/-- Checked signed two's-complement subtraction `(wrappedBits, overflowed)` at
width `w` (matching Rust `iN::overflowing_sub`, failing closed if either raw
input `≥ w.modulus`). -/
def subWithOverflowS (w : ScalarWidth) (a b : Nat) : Nat × Bool :=
  let a' := a % w.modulus
  let b' := b % w.modulus
  let wrapped := (a' + w.modulus - b') % w.modulus
  let ba := toBiased w a'
  let bb := toBiased w b'
  let ovf := Nat.ble w.modulus a || Nat.ble w.modulus b ||
    Nat.blt (ba + w.halfModulus) bb ||
    Nat.ble (bb + w.modulus) (ba + w.halfModulus)
  (wrapped, ovf)

/-- Checked signed two's-complement multiplication `(wrappedBits, overflowed)`
at width `w` (matching Rust `iN::overflowing_mul`, including `INT_MIN * 1`
succeeding and `INT_MIN * (-1)` overflowing, failing closed if either raw input
`≥ w.modulus`). -/
def mulWithOverflowS (w : ScalarWidth) (a b : Nat) : Nat × Bool :=
  let a' := a % w.modulus
  let b' := b % w.modulus
  let wrapped := (a' * b') % w.modulus
  let sa := Nat.ble w.halfModulus a'
  let sb := Nat.ble w.halfModulus b'
  let magA := if sa then w.modulus - a' else a'
  let magB := if sb then w.modulus - b' else b'
  let prodMag := magA * magB
  let negRes := sa != sb
  let rangeOvf :=
    match negRes with
    | true => Nat.blt w.halfModulus prodMag
    | false => Nat.ble w.halfModulus prodMag
  let ovf := Nat.ble w.modulus a || Nat.ble w.modulus b || rangeOvf
  (wrapped, ovf)

/-- Checked signed left-shift `(wrappedBits, overflowed)` at width `w`
(matching Rust `iN::overflowing_shl`: masks shift modulo `w.bits` and sets
`overflowed = true` iff `w.bits ≤ shift` or raw input `w.modulus ≤ a`). -/
def shlWithOverflowS (w : ScalarWidth) (a shift : Nat) : Nat × Bool :=
  let a' := a % w.modulus
  let masked := shift % w.bits
  ((a' * pow2 masked) % w.modulus, Nat.ble w.modulus a || Nat.ble w.bits shift)

/-- Interval-guarded unchecked signed addition (`none` on signed overflow). -/
def addUncheckedS (w : ScalarWidth) (a b : Nat) : Option Nat :=
  let r := addWithOverflowS w a b
  match r.2 with
  | true => none
  | false => some r.1

/-- Interval-guarded unchecked signed subtraction (`none` on signed overflow). -/
def subUncheckedS (w : ScalarWidth) (a b : Nat) : Option Nat :=
  let r := subWithOverflowS w a b
  match r.2 with
  | true => none
  | false => some r.1

/-- Interval-guarded unchecked signed multiplication (`none` on signed overflow). -/
def mulUncheckedS (w : ScalarWidth) (a b : Nat) : Option Nat :=
  let r := mulWithOverflowS w a b
  match r.2 with
  | true => none
  | false => some r.1

/-- Interval-guarded unchecked signed left-shift (`none` on shift overflow). -/
def shlUncheckedS (w : ScalarWidth) (a shift : Nat) : Option Nat :=
  let r := shlWithOverflowS w a shift
  match r.2 with
  | true => none
  | false => some r.1

private theorem nat_blt_false_iff_ge {a b : Nat} :
    Nat.blt a b = false ↔ b ≤ a := by
  unfold Nat.blt
  constructor
  · intro hF
    have hLt : b < a + 1 := nat_ble_false_iff_lt.mp hF
    exact Nat.le_of_lt_succ hLt
  · intro hGe
    exact nat_ble_false_iff_lt.mpr (Nat.lt_succ_of_le hGe)

private theorem nat_blt_true_of_lt {a b : Nat} (h : a < b) :
    Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

/-- Exact no-overflow equivalence for `addWithOverflowS`: no overflow iff both
inputs are canonical `w`-bit patterns and their biased sum fits in
`[H, M + H)`. -/
theorem addWithOverflowS_no_overflow_iff (w : ScalarWidth) (a b : Nat) :
    (addWithOverflowS w a b).2 = false ↔
      a < w.modulus ∧ b < w.modulus ∧
      w.halfModulus ≤ toBiased w a + toBiased w b ∧
      toBiased w a + toBiased w b < w.modulus + w.halfModulus := by
  unfold addWithOverflowS
  dsimp only
  constructor
  · intro h
    cases h1 : Nat.ble w.modulus a with
    | true => rw [h1] at h; cases h
    | false =>
      cases h2 : Nat.ble w.modulus b with
      | true => rw [h1, h2] at h; cases h
      | false =>
        rw [h1, h2] at h
        have ha : a < w.modulus := nat_ble_false_iff_lt.mp h1
        have hb : b < w.modulus := nat_ble_false_iff_lt.mp h2
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
        cases h3 : Nat.blt (toBiased w a + toBiased w b) w.halfModulus with
        | true => rw [h3] at h; cases h
        | false =>
          rw [h3] at h
          exact ⟨ha, hb, nat_blt_false_iff_ge.mp h3, nat_ble_false_iff_lt.mp h⟩
  · intro ⟨ha, hb, hLo, hHi⟩
    rw [nat_ble_false_iff_lt.mpr ha, nat_ble_false_iff_lt.mpr hb,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      nat_blt_false_iff_ge.mpr hLo, nat_ble_false_iff_lt.mpr hHi]
    rfl

/-- Exact biased-value identity for non-overflowing signed addition:
`toBiased w (addWithOverflowS w a b).1 = toBiased w a + toBiased w b - H`. -/
theorem toBiased_addWithOverflowS_of_no_overflow (w : ScalarWidth) {a b : Nat}
    (hNo : (addWithOverflowS w a b).2 = false) :
    toBiased w (addWithOverflowS w a b).1 =
      toBiased w a + toBiased w b - w.halfModulus := by
  let ⟨ha, hb, hLo, hHi⟩ := (addWithOverflowS_no_overflow_iff w a b).mp hNo
  have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
  have hDiffLt : toBiased w a + toBiased w b - w.halfModulus < w.modulus := by
    have h1 : (toBiased w a + toBiased w b - w.halfModulus) + w.halfModulus <
        w.modulus + w.halfModulus := by
      rw [Nat.sub_add_cancel hLo]
      exact hHi
    cases Nat.lt_or_ge (toBiased w a + toBiased w b - w.halfModulus) w.modulus with
    | inl hLt => exact hLt
    | inr hGe => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_right hGe _))
  have hAddM :
      toBiased w a + toBiased w b + w.halfModulus =
        (toBiased w a + toBiased w b - w.halfModulus) + w.modulus := by
    rw [hModEq, ← Nat.add_assoc, Nat.sub_add_cancel hLo]
  have hCong :
      (toBiased w a + toBiased w b + w.halfModulus) % w.modulus =
        toBiased w (addWithOverflowS w a b).1 := by
    unfold addWithOverflowS toBiased
    dsimp only
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (Nat.mod_lt _ w.modulus_pos),
      add_mod_left_eq (a + b) w.halfModulus w.modulus]
    rw [← add_mod_left_eq ((a + w.halfModulus) % w.modulus + (b + w.halfModulus) % w.modulus)
        w.halfModulus w.modulus,
      add_mod_left_eq (a + w.halfModulus) ((b + w.halfModulus) % w.modulus) w.modulus,
      add_mod_right_eq (a + w.halfModulus) (b + w.halfModulus) w.modulus,
      add_mod_left_eq ((a + w.halfModulus) + (b + w.halfModulus)) w.halfModulus w.modulus]
    have hRearr :
        (a + w.halfModulus) + (b + w.halfModulus) + w.halfModulus =
          (a + b + w.halfModulus) + w.modulus := by
      rw [hModEq]
      rw [Nat.add_assoc a w.halfModulus (b + w.halfModulus),
        Nat.add_comm w.halfModulus (b + w.halfModulus),
        Nat.add_assoc b w.halfModulus w.halfModulus,
        ← Nat.add_assoc a b (w.halfModulus + w.halfModulus),
        Nat.add_assoc (a + b) (w.halfModulus + w.halfModulus) w.halfModulus,
        Nat.add_comm (w.halfModulus + w.halfModulus) w.halfModulus,
        ← Nat.add_assoc (a + b) w.halfModulus (w.halfModulus + w.halfModulus)]
    rw [hRearr, Nat.add_mod_right]
  rw [← hCong, hAddM, Nat.add_mod_right, Nat.mod_eq_of_lt hDiffLt]

/-- Signed addition of two non-negative operands (`a + b < w.halfModulus`)
never overflows and equals exact `a + b`. -/
theorem addWithOverflowS_nonneg_of_lt (w : ScalarWidth) {a b : Nat}
    (hLt : a + b < w.halfModulus) :
    addWithOverflowS w a b = (a + b, false) := by
  have haH : a < w.halfModulus := Nat.lt_of_le_of_lt (Nat.le_add_right a b) hLt
  have hbH : b < w.halfModulus := Nat.lt_of_le_of_lt (Nat.le_add_left b a) hLt
  have haM : a < w.modulus := Nat.lt_trans haH w.halfModulus_lt_modulus
  have hbM : b < w.modulus := Nat.lt_trans hbH w.halfModulus_lt_modulus
  have hSumM : a + b < w.modulus := Nat.lt_trans hLt w.halfModulus_lt_modulus
  have hNo : (addWithOverflowS w a b).2 = false := by
    rw [addWithOverflowS_no_overflow_iff, toBiased_nonneg w haH, toBiased_nonneg w hbH]
    refine ⟨haM, hbM, ?_, ?_⟩
    · exact Nat.le_trans (Nat.le_add_left w.halfModulus a) (Nat.le_add_right _ _)
    · have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
        rw [w.modulus_eq_two_mul_half, Nat.two_mul]
      have hRearr : (a + w.halfModulus) + (b + w.halfModulus) =
          (a + b) + (w.halfModulus + w.halfModulus) := by
        rw [Nat.add_assoc a w.halfModulus (b + w.halfModulus),
          Nat.add_comm w.halfModulus (b + w.halfModulus),
          Nat.add_assoc b w.halfModulus w.halfModulus,
          ← Nat.add_assoc a b (w.halfModulus + w.halfModulus)]
      rw [hRearr, ← hModEq, Nat.add_comm w.modulus w.halfModulus]
      exact Nat.add_lt_add_right hLt w.modulus
  have hFst : (addWithOverflowS w a b).1 = a + b := by
    unfold addWithOverflowS
    dsimp only
    rw [Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hbM, Nat.mod_eq_of_lt hSumM]
  cases h : addWithOverflowS w a b with
  | mk fst snd =>
    rw [h] at hFst hNo
    dsimp only at hFst hNo
    rw [hFst, hNo]

/-- Signed addition of a negative operand (`H ≤ a < M`) and a non-negative
operand (`b < H`) NEVER overflows; if `a + b < M` it stays negative with exact
wrapped bits `a + b`. -/
theorem addWithOverflowS_neg_plus_nonneg_of_lt (w : ScalarWidth) {a b : Nat}
    (hNeg : w.halfModulus ≤ a) (hb : b < w.halfModulus)
    (hSumLt : a + b < w.modulus) :
    addWithOverflowS w a b = (a + b, false) := by
  have haM : a < w.modulus := Nat.lt_of_le_of_lt (Nat.le_add_right a b) hSumLt
  have hbM : b < w.modulus := Nat.lt_trans hb w.halfModulus_lt_modulus
  have hNo : (addWithOverflowS w a b).2 = false := by
    rw [addWithOverflowS_no_overflow_iff, toBiased_neg w hNeg haM, toBiased_nonneg w hb]
    refine ⟨haM, hbM, ?_, ?_⟩
    · exact Nat.le_trans (Nat.le_add_left w.halfModulus b) (Nat.le_add_left _ _)
    · have hEq : (a - w.halfModulus) + (b + w.halfModulus) = a + b := by
        rw [Nat.add_comm b w.halfModulus, ← Nat.add_assoc,
          Nat.sub_add_cancel hNeg]
      rw [hEq]
      exact Nat.lt_of_lt_of_le hSumLt (Nat.le_add_right w.modulus w.halfModulus)
  have hFst : (addWithOverflowS w a b).1 = a + b := by
    unfold addWithOverflowS
    dsimp only
    rw [Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hbM, Nat.mod_eq_of_lt hSumLt]
  cases h : addWithOverflowS w a b with
  | mk fst snd =>
    rw [h] at hFst hNo
    dsimp only at hFst hNo
    rw [hFst, hNo]

/-- Fail-closed: signed addition of two non-negative operands whose sum reaches
`w.halfModulus` overflows (`(addWithOverflowS w a b).2 = true`). -/
theorem addWithOverflowS_overflow_of_pos_ge (w : ScalarWidth) {a b : Nat}
    (ha : a < w.halfModulus) (hb : b < w.halfModulus)
    (hGe : w.halfModulus ≤ a + b) :
    (addWithOverflowS w a b).2 = true := by
  cases h : (addWithOverflowS w a b).2 with
  | true => rfl
  | false =>
    let ⟨_, _, _, hHi⟩ := (addWithOverflowS_no_overflow_iff w a b).mp h
    rw [toBiased_nonneg w ha, toBiased_nonneg w hb] at hHi
    have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
      rw [w.modulus_eq_two_mul_half, Nat.two_mul]
    have hRearr : (a + w.halfModulus) + (b + w.halfModulus) =
        (a + b) + w.modulus := by
      rw [hModEq, Nat.add_assoc a w.halfModulus (b + w.halfModulus),
        Nat.add_comm w.halfModulus (b + w.halfModulus),
        Nat.add_assoc b w.halfModulus w.halfModulus,
        ← Nat.add_assoc a b (w.halfModulus + w.halfModulus)]
    rw [hRearr, Nat.add_comm w.modulus w.halfModulus] at hHi
    exact absurd hHi (Nat.not_lt_of_ge (Nat.add_le_add_right hGe w.modulus))

/-- Exact no-overflow equivalence for `subWithOverflowS`: no overflow iff both
inputs are canonical `w`-bit patterns and `toBiased w b ≤ toBiased w a + H <
toBiased w b + M`. -/
theorem subWithOverflowS_no_overflow_iff (w : ScalarWidth) (a b : Nat) :
    (subWithOverflowS w a b).2 = false ↔
      a < w.modulus ∧ b < w.modulus ∧
      toBiased w b ≤ toBiased w a + w.halfModulus ∧
      toBiased w a + w.halfModulus < toBiased w b + w.modulus := by
  unfold subWithOverflowS
  dsimp only
  constructor
  · intro h
    cases h1 : Nat.ble w.modulus a with
    | true => rw [h1] at h; cases h
    | false =>
      cases h2 : Nat.ble w.modulus b with
      | true => rw [h1, h2] at h; cases h
      | false =>
        rw [h1, h2] at h
        have ha : a < w.modulus := nat_ble_false_iff_lt.mp h1
        have hb : b < w.modulus := nat_ble_false_iff_lt.mp h2
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
        cases h3 : Nat.blt (toBiased w a + w.halfModulus) (toBiased w b) with
        | true => rw [h3] at h; cases h
        | false =>
          rw [h3] at h
          exact ⟨ha, hb, nat_blt_false_iff_ge.mp h3, nat_ble_false_iff_lt.mp h⟩
  · intro ⟨ha, hb, hLo, hHi⟩
    rw [nat_ble_false_iff_lt.mpr ha, nat_ble_false_iff_lt.mpr hb,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      nat_blt_false_iff_ge.mpr hLo, nat_ble_false_iff_lt.mpr hHi]
    rfl

/-- Exact biased-value identity for non-overflowing signed subtraction:
`toBiased w (subWithOverflowS w a b).1 = toBiased w a + H - toBiased w b`. -/
theorem toBiased_subWithOverflowS_of_no_overflow (w : ScalarWidth) {a b : Nat}
    (hNo : (subWithOverflowS w a b).2 = false) :
    toBiased w (subWithOverflowS w a b).1 =
      toBiased w a + w.halfModulus - toBiased w b := by
  let ⟨ha, hb, hLo, hHi⟩ := (subWithOverflowS_no_overflow_iff w a b).mp hNo
  have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
  have hDiffLt : toBiased w a + w.halfModulus - toBiased w b < w.modulus := by
    have h1 : (toBiased w a + w.halfModulus - toBiased w b) + toBiased w b <
        w.modulus + toBiased w b := by
      rw [Nat.sub_add_cancel hLo, Nat.add_comm w.modulus (toBiased w b)]
      exact hHi
    cases Nat.lt_or_ge (toBiased w a + w.halfModulus - toBiased w b) w.modulus with
    | inl hLt => exact hLt
    | inr hGe => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_right hGe _))
  have hBLeM : toBiased w b ≤ w.modulus := Nat.le_of_lt (toBiased_lt_modulus w b)
  have hSubAdd :
      (toBiased w a + w.halfModulus - toBiased w b) + w.modulus =
        toBiased w a + w.halfModulus + (w.modulus - toBiased w b) := by
    have h1 := Nat.add_sub_assoc hBLeM (toBiased w a + w.halfModulus)
    have h2 : (toBiased w a + w.halfModulus + w.modulus) - toBiased w b =
        (toBiased w a + w.halfModulus - toBiased w b) + w.modulus :=
      (sub_add_comm_nat hLo).symm
    exact h2.symm.trans h1
  have hSumB : (b + w.halfModulus + (w.modulus - toBiased w b)) % w.modulus = 0 := by
    rw [← add_mod_left_eq (b + w.halfModulus) (w.modulus - toBiased w b) w.modulus]
    have hTb : (b + w.halfModulus) % w.modulus = toBiased w b := by
      unfold toBiased; rw [Nat.mod_eq_of_lt hb]
    rw [hTb, Nat.add_sub_of_le hBLeM, Nat.mod_self]
  have hTarget :
      toBiased w (subWithOverflowS w a b).1 =
        (toBiased w a + w.halfModulus + (w.modulus - toBiased w b)) % w.modulus := by
    unfold subWithOverflowS toBiased
    dsimp only
    rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
      Nat.mod_eq_of_lt (Nat.mod_lt _ w.modulus_pos),
      add_mod_left_eq (a + w.modulus - b) w.halfModulus w.modulus]
    have hLhsAdd :
        ((a + w.modulus - b + w.halfModulus) +
          (b + w.halfModulus + (w.modulus - toBiased w b))) % w.modulus =
          (a + w.modulus - b + w.halfModulus) % w.modulus := by
      rw [← add_mod_right_eq (a + w.modulus - b + w.halfModulus), hSumB,
        Nat.add_zero]
    rw [← hLhsAdd]
    have hCancel :
        (a + w.modulus - b + w.halfModulus) +
            (b + w.halfModulus + (w.modulus - toBiased w b)) =
          (a + w.halfModulus + w.halfModulus + (w.modulus - toBiased w b)) +
            w.modulus := by
      have hbLe : b ≤ a + w.modulus :=
        Nat.le_trans (Nat.le_of_lt hb) (Nat.le_add_left w.modulus a)
      rw [Nat.add_assoc (a + w.modulus - b) w.halfModulus _,
        Nat.add_assoc b w.halfModulus _,
        ← Nat.add_assoc w.halfModulus b _,
        Nat.add_comm w.halfModulus b,
        Nat.add_assoc b w.halfModulus _,
        ← Nat.add_assoc (a + w.modulus - b) b _,
        Nat.sub_add_cancel hbLe]
      rw [Nat.add_assoc a w.modulus _,
        Nat.add_comm w.modulus (w.halfModulus + (w.halfModulus + (w.modulus - toBiased w b))),
        ← Nat.add_assoc a _ w.modulus,
        ← Nat.add_assoc a w.halfModulus _,
        ← Nat.add_assoc (a + w.halfModulus) w.halfModulus (w.modulus - toBiased w b)]
    rw [hCancel, Nat.add_mod_right]
    have hTb : toBiased w b = (b + w.halfModulus) % w.modulus := by
      unfold toBiased; rw [Nat.mod_eq_of_lt hb]
    rw [hTb,
      ← add_mod_left_eq ((a + w.halfModulus) % w.modulus + w.halfModulus)
          (w.modulus - (b + w.halfModulus) % w.modulus) w.modulus,
      add_mod_left_eq (a + w.halfModulus) w.halfModulus w.modulus,
      add_mod_left_eq (a + w.halfModulus + w.halfModulus)
          (w.modulus - (b + w.halfModulus) % w.modulus) w.modulus]
  rw [hTarget, ← hSubAdd, Nat.add_mod_right, Nat.mod_eq_of_lt hDiffLt]

/-- Exact no-overflow equivalence for `mulWithOverflowS`: no overflow iff both
inputs are canonical `w`-bit patterns and the exact signed magnitude fits in
`[-H, H - 1]` (allowing `INT_MIN * 1 = -H` while rejecting `INT_MIN * (-1) = +H`). -/
theorem mulWithOverflowS_no_overflow_iff (w : ScalarWidth) (a b : Nat) :
    (mulWithOverflowS w a b).2 = false ↔
      a < w.modulus ∧ b < w.modulus ∧
      let sa := Nat.ble w.halfModulus a
      let sb := Nat.ble w.halfModulus b
      let magA := if sa then w.modulus - a else a
      let magB := if sb then w.modulus - b else b
      match sa != sb with
      | true => magA * magB ≤ w.halfModulus
      | false => magA * magB < w.halfModulus := by
  unfold mulWithOverflowS
  dsimp only
  constructor
  · intro h
    cases h1 : Nat.ble w.modulus a with
    | true => rw [h1] at h; cases h
    | false =>
      cases h2 : Nat.ble w.modulus b with
      | true => rw [h1, h2] at h; cases h
      | false =>
        rw [h1, h2] at h
        have ha : a < w.modulus := nat_ble_false_iff_lt.mp h1
        have hb : b < w.modulus := nat_ble_false_iff_lt.mp h2
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h
        refine ⟨ha, hb, ?_⟩
        cases hNeg : (Nat.ble w.halfModulus a != Nat.ble w.halfModulus b) with
        | true =>
          rw [hNeg] at h
          exact nat_blt_false_iff_ge.mp h
        | false =>
          rw [hNeg] at h
          exact nat_ble_false_iff_lt.mp h
  · intro ⟨ha, hb, hMag⟩
    rw [nat_ble_false_iff_lt.mpr ha, nat_ble_false_iff_lt.mpr hb,
      Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
    cases hNeg : (Nat.ble w.halfModulus a != Nat.ble w.halfModulus b) with
    | true =>
      rw [hNeg] at hMag
      exact nat_blt_false_iff_ge.mpr hMag
    | false =>
      rw [hNeg] at hMag
      exact nat_ble_false_iff_lt.mpr hMag

/-- Exact `INT_MIN * (-1)` signed multiplication overflow boundary theorem:
multiplying `w.halfModulus` (`INT_MIN`) by `w.modulus - 1` (`-1`) ALWAYS
overflows at every `ScalarWidth` (`i8..i128`). -/
theorem mulWithOverflowS_overflow_of_min_mul_neg_one (w : ScalarWidth) :
    (mulWithOverflowS w w.halfModulus (w.modulus - 1)).2 = true := by
  cases h : (mulWithOverflowS w w.halfModulus (w.modulus - 1)).2 with
  | true => rfl
  | false =>
    let ⟨_, _, hMag⟩ :=
      (mulWithOverflowS_no_overflow_iff w w.halfModulus (w.modulus - 1)).mp h
    have hHalfLe : w.halfModulus ≤ w.modulus - 1 := by
      have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
        rw [w.modulus_eq_two_mul_half, Nat.two_mul]
      have hHPos : 0 < w.halfModulus := by
        cases w <;> exact Nat.zero_lt_succ _
      rw [hModEq, Nat.add_sub_assoc hHPos]
      exact Nat.le_add_right _ _
    rw [Nat.ble_eq_true_of_le (Nat.le_refl w.halfModulus),
      Nat.ble_eq_true_of_le hHalfLe] at hMag
    dsimp only at hMag
    have hSubH : w.modulus - w.halfModulus = w.halfModulus := by
      have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
        rw [w.modulus_eq_two_mul_half, Nat.two_mul]
      rw [hModEq, Nat.add_sub_cancel]
    have hSub1 : w.modulus - (w.modulus - 1) = 1 := by
      have hPos : 1 ≤ w.modulus := w.modulus_pos
      have hEq : (w.modulus - 1) + 1 = w.modulus := Nat.sub_add_cancel hPos
      have hC := congrArg (fun k => k - (w.modulus - 1)) hEq
      rw [Nat.add_sub_cancel_left] at hC
      exact hC.symm
    rw [hSubH, hSub1] at hMag
    change w.halfModulus * 1 < w.halfModulus at hMag
    rw [Nat.mul_one] at hMag
    exact False.elim (Nat.lt_irrefl w.halfModulus hMag)

/-- Exact no-overflow equivalence for `shlWithOverflowS`. -/
theorem shlWithOverflowS_no_overflow_iff (w : ScalarWidth) (a shift : Nat) :
    (shlWithOverflowS w a shift).2 = false ↔
      a < w.modulus ∧ shift < w.bits := by
  unfold shlWithOverflowS
  dsimp only
  constructor
  · intro h
    cases h1 : Nat.ble w.modulus a with
    | true => rw [h1] at h; cases h
    | false =>
      rw [h1] at h
      exact ⟨nat_ble_false_iff_lt.mp h1, nat_ble_false_iff_lt.mp h⟩
  · intro ⟨ha, hS⟩
    rw [nat_ble_false_iff_lt.mpr ha, nat_ble_false_iff_lt.mpr hS]
    rfl

/-- Soundness equivalence for `addUncheckedS`. -/
theorem addUncheckedS_eq_some_iff (w : ScalarWidth) (a b res : Nat) :
    addUncheckedS w a b = some res ↔
      (addWithOverflowS w a b).2 = false ∧ (addWithOverflowS w a b).1 = res := by
  unfold addUncheckedS
  dsimp only
  cases h : (addWithOverflowS w a b).2 with
  | true =>
    constructor
    · intro hc; cases hc
    · intro ⟨hF, _⟩; cases hF
  | false =>
    constructor
    · intro hEq; exact ⟨rfl, Option.some.inj hEq⟩
    · intro ⟨_, hRes⟩; rw [hRes]

/-- Soundness equivalence for `subUncheckedS`. -/
theorem subUncheckedS_eq_some_iff (w : ScalarWidth) (a b res : Nat) :
    subUncheckedS w a b = some res ↔
      (subWithOverflowS w a b).2 = false ∧ (subWithOverflowS w a b).1 = res := by
  unfold subUncheckedS
  dsimp only
  cases h : (subWithOverflowS w a b).2 with
  | true =>
    constructor
    · intro hc; cases hc
    · intro ⟨hF, _⟩; cases hF
  | false =>
    constructor
    · intro hEq; exact ⟨rfl, Option.some.inj hEq⟩
    · intro ⟨_, hRes⟩; rw [hRes]

/-- Soundness equivalence for `mulUncheckedS`. -/
theorem mulUncheckedS_eq_some_iff (w : ScalarWidth) (a b res : Nat) :
    mulUncheckedS w a b = some res ↔
      (mulWithOverflowS w a b).2 = false ∧ (mulWithOverflowS w a b).1 = res := by
  unfold mulUncheckedS
  dsimp only
  cases h : (mulWithOverflowS w a b).2 with
  | true =>
    constructor
    · intro hc; cases hc
    · intro ⟨hF, _⟩; cases hF
  | false =>
    constructor
    · intro hEq; exact ⟨rfl, Option.some.inj hEq⟩
    · intro ⟨_, hRes⟩; rw [hRes]

/-- Soundness equivalence for `shlUncheckedS`. -/
theorem shlUncheckedS_eq_some_iff (w : ScalarWidth) (a shift res : Nat) :
    shlUncheckedS w a shift = some res ↔
      a < w.modulus ∧ shift < w.bits ∧ (a * pow2 shift) % w.modulus = res := by
  unfold shlUncheckedS
  dsimp only
  cases h : (shlWithOverflowS w a shift).2 with
  | true =>
    constructor
    · intro hc; cases hc
    · intro ⟨ha, hS, _⟩
      have hF := (shlWithOverflowS_no_overflow_iff w a shift).mpr ⟨ha, hS⟩
      rw [h] at hF
      cases hF
  | false =>
    let ⟨ha, hS⟩ := (shlWithOverflowS_no_overflow_iff w a shift).mp h
    have hFst : (shlWithOverflowS w a shift).1 = (a * pow2 shift) % w.modulus := by
      unfold shlWithOverflowS
      dsimp only
      rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hS]
    rw [hFst]
    constructor
    · intro hEq; exact ⟨ha, hS, Option.some.inj hEq⟩
    · intro ⟨_, _, hRes⟩; rw [hRes]

/-- Fail-closed: `addUncheckedS` returns `none` when signed addition overflows. -/
theorem addUncheckedS_none_of_overflow (w : ScalarWidth) {a b : Nat}
    (hOvf : (addWithOverflowS w a b).2 = true) :
    addUncheckedS w a b = none := by
  unfold addUncheckedS; dsimp only; rw [hOvf]

/-- Fail-closed: `subUncheckedS` returns `none` when signed subtraction overflows. -/
theorem subUncheckedS_none_of_overflow (w : ScalarWidth) {a b : Nat}
    (hOvf : (subWithOverflowS w a b).2 = true) :
    subUncheckedS w a b = none := by
  unfold subUncheckedS; dsimp only; rw [hOvf]

/-- Fail-closed: `mulUncheckedS` returns `none` when signed multiplication overflows. -/
theorem mulUncheckedS_none_of_overflow (w : ScalarWidth) {a b : Nat}
    (hOvf : (mulWithOverflowS w a b).2 = true) :
    mulUncheckedS w a b = none := by
  unfold mulUncheckedS; dsimp only; rw [hOvf]

/-- Fail-closed: `shlUncheckedS` returns `none` when `w.bits ≤ shift`. -/
theorem shlUncheckedS_none_of_ge (w : ScalarWidth) (a : Nat) {shift : Nat}
    (h : w.bits ≤ shift) : shlUncheckedS w a shift = none := by
  unfold shlUncheckedS shlWithOverflowS
  dsimp only
  rw [Nat.ble_eq_true_of_le h]
  cases Nat.ble w.modulus a <;> rfl

/-! ## Part III: Parametric Frame Interface, Intervals, & `@[irreducible] OvfCastStageCut` -/

/-- Parametric machine-state and local-slot interface (`0` `Prop` fields)
connecting `OverflowCastJoin` to any MIR operational semantics (including
`V2026_06_01.MirSemantics.MachineState`). -/
structure OvfCastFrameOps (S : Type u) (Val : Type v) where
  /-- Current CFG basic-block index of state `s`. -/
  blockOf : S → Nat
  /-- Current local-slot table of state `s`. -/
  localsOf : S → List Val
  /-- Replaces the block index and local-slot table while framing external
  state (such as memory or call stack). -/
  withBlockLocals : S → Nat → List Val → S
  /-- Encodes an unsigned scalar value at width `w` into `Val`. -/
  mkScalar : ScalarWidth → Nat → Val
  /-- Decodes an unsigned scalar value at width `w` from `Val`. -/
  asScalar? : ScalarWidth → Val → Option Nat
  /-- Encodes a checked-arithmetic `(wrapped, overflowed)` tuple into `Val`. -/
  mkOvfTuple : ScalarWidth → Nat → Bool → Val

/-- Laws of `OvfCastFrameOps`. -/
structure OvfCastFrameOps.Lawful {S : Type u} {Val : Type v}
    (fops : OvfCastFrameOps S Val) : Prop where
  blockOf_withBlockLocals : ∀ (s : S) (bb : Nat) (locs : List Val),
    fops.blockOf (fops.withBlockLocals s bb locs) = bb
  localsOf_withBlockLocals : ∀ (s : S) (bb : Nat) (locs : List Val),
    fops.localsOf (fops.withBlockLocals s bb locs) = locs
  asScalar?_mkScalar : ∀ (w : ScalarWidth) (n : Nat),
    n < w.modulus → fops.asScalar? w (fops.mkScalar w n) = some n

/-- Signed (biased-coordinate) view of an `OvfCastFrameOps`. The tracked
accumulator `n` is the order-preserving biased coordinate of a two's-complement
bit pattern: `signedView.mkScalar w n` stores the bit pattern `toBiased w n`,
whose signed value is `n - w.halfModulus`. A raw `StageIntervalSpec` `[lo, hi]`
over `fops.signedView` is therefore exactly the signed interval
`[lo - halfModulus, hi - halfModulus]`, including intervals that cross zero.
Over raw bit patterns those intervals have no tight encoding: `i8 ∈ [-5, 5]`
is the bit-pattern set `{251..255} ∪ {0..5}`. -/
def OvfCastFrameOps.signedView {S : Type u} {Val : Type v}
    (fops : OvfCastFrameOps S Val) : OvfCastFrameOps S Val where
  blockOf := fops.blockOf
  localsOf := fops.localsOf
  withBlockLocals := fops.withBlockLocals
  mkScalar w n := fops.mkScalar w (toBiased w n)
  asScalar? w v :=
    match fops.asScalar? w v with
    | none => none
    | some x => some (toBiased w x)
  mkOvfTuple := fops.mkOvfTuple

/-- `OvfCastFrameOps.signedView` preserves lawfulness (since `toBiased w` is an
involution on canonical `w`-bit patterns). -/
theorem OvfCastFrameOps.signedView_lawful {S : Type u} {Val : Type v}
    {fops : OvfCastFrameOps S Val} (hLaw : fops.Lawful) :
    fops.signedView.Lawful where
  blockOf_withBlockLocals := hLaw.blockOf_withBlockLocals
  localsOf_withBlockLocals := hLaw.localsOf_withBlockLocals
  asScalar?_mkScalar w n hn := by
    show (match fops.asScalar? w (fops.mkScalar w (toBiased w n)) with
      | none => none
      | some x => some (toBiased w x)) = some n
    rw [hLaw.asScalar?_mkScalar w _ (toBiased_lt_modulus w n)]
    show some (toBiased w (toBiased w n)) = some n
    rw [toBiased_involutive, Nat.mod_eq_of_lt hn]

/-- Tightened signed join interval in biased coordinates: if the accumulator
bit pattern is `toBiased w accB` with `accB ∈ [lo, hi]` and the checked signed
addition of `c` takes the `overflowed = false` arm with result `r`, then the
result's biased coordinate is exactly `accB + toBiased w c - halfModulus`
(stated without truncated subtraction) and lies in
`[lo + toBiased w c - halfModulus, hi + toBiased w c - halfModulus]`. -/
theorem addWithOverflowS_biased_false_interval (w : ScalarWidth)
    {lo hi accB c r : Nat} (hAcc : accB < w.modulus)
    (hLo : lo ≤ accB) (hHi : accB ≤ hi)
    (h : addWithOverflowS w (toBiased w accB) c = (r, false)) :
    toBiased w r + w.halfModulus = accB + toBiased w c ∧
    lo + toBiased w c ≤ toBiased w r + w.halfModulus ∧
    toBiased w r + w.halfModulus ≤ hi + toBiased w c ∧
    r < w.modulus := by
  have hNo : (addWithOverflowS w (toBiased w accB) c).2 = false :=
    congrArg Prod.snd h
  have hR : (addWithOverflowS w (toBiased w accB) c).1 = r := congrArg Prod.fst h
  have hInv : toBiased w (toBiased w accB) = accB := by
    rw [toBiased_involutive, Nat.mod_eq_of_lt hAcc]
  let ⟨hA, _, hBiLo, _⟩ := (addWithOverflowS_no_overflow_iff w _ c).mp hNo
  rw [hInv] at hBiLo
  have hEq := toBiased_addWithOverflowS_of_no_overflow w hNo
  rw [hR, hInv] at hEq
  have hSum : toBiased w r + w.halfModulus = accB + toBiased w c := by
    rw [hEq, Nat.sub_add_cancel hBiLo]
  have hRlt : r < w.modulus := by
    rw [← hR]
    unfold addWithOverflowS
    exact Nat.mod_lt _ w.modulus_pos
  refine ⟨hSum, ?_, ?_, hRlt⟩
  · rw [hSum]; exact Nat.add_le_add_right hLo _
  · rw [hSum]; exact Nat.add_le_add_right hHi _

/-- Fail-closed signed interval certificate: a biased sum outside
`[halfModulus, modulus + halfModulus)` (signed result outside the width's
range) forces `overflowed = true`, so it can never reach a false-branch join. -/
theorem addWithOverflowS_biased_overflow_of_out_of_range (w : ScalarWidth)
    {accB c : Nat} (hAcc : accB < w.modulus)
    (hOut : accB + toBiased w c < w.halfModulus ∨
      w.modulus + w.halfModulus ≤ accB + toBiased w c) :
    (addWithOverflowS w (toBiased w accB) c).2 = true := by
  have hInv : toBiased w (toBiased w accB) = accB := by
    rw [toBiased_involutive, Nat.mod_eq_of_lt hAcc]
  cases hF : (addWithOverflowS w (toBiased w accB) c).2 with
  | true => rfl
  | false =>
    let ⟨_, _, hBiLo, hBiHi⟩ := (addWithOverflowS_no_overflow_iff w _ c).mp hF
    rw [hInv] at hBiLo hBiHi
    cases hOut with
    | inl hBelow => exact absurd hBiLo (Nat.not_le_of_gt hBelow)
    | inr hAbove => exact absurd hBiHi (Nat.not_lt_of_ge hAbove)

/-- Tightened signed join interval for checked subtraction in biased
coordinates: if the accumulator bit pattern is `toBiased w accB` with
`accB ∈ [lo, hi]` and `subWithOverflowS w (toBiased w accB) c = (r, false)`,
then `toBiased w r + toBiased w c = accB + w.halfModulus`, placing `toBiased w r`
in the tightened signed join interval without truncated subtraction. -/
theorem subWithOverflowS_biased_false_interval (w : ScalarWidth)
    {lo hi accB c r : Nat} (hAcc : accB < w.modulus)
    (hLo : lo ≤ accB) (hHi : accB ≤ hi)
    (h : subWithOverflowS w (toBiased w accB) c = (r, false)) :
    toBiased w r + toBiased w c = accB + w.halfModulus ∧
    lo + w.halfModulus ≤ toBiased w r + toBiased w c ∧
    toBiased w r + toBiased w c ≤ hi + w.halfModulus ∧
    r < w.modulus := by
  have hNo : (subWithOverflowS w (toBiased w accB) c).2 = false :=
    congrArg Prod.snd h
  have hR : (subWithOverflowS w (toBiased w accB) c).1 = r := congrArg Prod.fst h
  have hInv : toBiased w (toBiased w accB) = accB := by
    rw [toBiased_involutive, Nat.mod_eq_of_lt hAcc]
  let ⟨_, _, hBiLo, _⟩ := (subWithOverflowS_no_overflow_iff w _ c).mp hNo
  rw [hInv] at hBiLo
  have hEq := toBiased_subWithOverflowS_of_no_overflow w hNo
  rw [hR, hInv] at hEq
  have hSum : toBiased w r + toBiased w c = accB + w.halfModulus := by
    rw [hEq, Nat.sub_add_cancel hBiLo]
  have hRlt : r < w.modulus := by
    rw [← hR]
    unfold subWithOverflowS
    exact Nat.mod_lt _ w.modulus_pos
  refine ⟨hSum, ?_, ?_, hRlt⟩
  · rw [hSum]; exact Nat.add_le_add_right hLo _
  · rw [hSum]; exact Nat.add_le_add_right hHi _

/-- Fail-closed signed subtraction overflow certificate in biased coordinates. -/
theorem subWithOverflowS_biased_overflow_of_out_of_range (w : ScalarWidth)
    {accB c : Nat} (hAcc : accB < w.modulus)
    (hOut : accB + w.halfModulus < toBiased w c ∨
      toBiased w c + w.modulus ≤ accB + w.halfModulus) :
    (subWithOverflowS w (toBiased w accB) c).2 = true := by
  have hInv : toBiased w (toBiased w accB) = accB := by
    rw [toBiased_involutive, Nat.mod_eq_of_lt hAcc]
  cases hF : (subWithOverflowS w (toBiased w accB) c).2 with
  | true => rfl
  | false =>
    let ⟨_, _, hBiLo, hBiHi⟩ := (subWithOverflowS_no_overflow_iff w _ c).mp hF
    rw [hInv] at hBiLo hBiHi
    cases hOut with
    | inl hBelow => exact absurd hBiLo (Nat.not_le_of_gt hBelow)
    | inr hAbove => exact absurd hBiHi (Nat.not_lt_of_ge hAbove)

/-- Exact biased-coordinate identity for non-overflowing signed multiplication
by a non-negative multiplier `c < w.halfModulus` (valid on BOTH sides of zero):
`toBiased w r + w.halfModulus * c = accB * c + w.halfModulus`. -/
theorem toBiased_mulWithOverflowS_nonneg_mul (w : ScalarWidth)
    {accB c r : Nat} (hAcc : accB < w.modulus) (hc : c < w.halfModulus)
    (h : mulWithOverflowS w (toBiased w accB) c = (r, false)) :
    toBiased w r + w.halfModulus * c = accB * c + w.halfModulus ∧
    r < w.modulus := by
  have hNo : (mulWithOverflowS w (toBiased w accB) c).2 = false := congrArg Prod.snd h
  have hR : (mulWithOverflowS w (toBiased w accB) c).1 = r := congrArg Prod.fst h
  have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
  have hcM : c < w.modulus := Nat.lt_trans hc w.halfModulus_lt_modulus
  have haM : toBiased w accB < w.modulus := toBiased_lt_modulus w accB
  have hRlt : r < w.modulus := by
    rw [← hR]; unfold mulWithOverflowS; exact Nat.mod_lt _ w.modulus_pos
  have hRDef : r = (toBiased w accB * c) % w.modulus := by
    rw [← hR]; unfold mulWithOverflowS; dsimp only
    rw [Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hcM]
  let ⟨_, _, hMag⟩ := (mulWithOverflowS_no_overflow_iff w (toBiased w accB) c).mp hNo
  have hSb : Nat.ble w.halfModulus c = false := nat_ble_false_iff_lt.mpr hc
  refine ⟨?_, hRlt⟩
  cases Nat.lt_or_ge accB w.halfModulus with
  | inl hNegB =>
    have hA : toBiased w accB = accB + w.halfModulus := toBiased_nonneg w hNegB
    have hHLeA : w.halfModulus ≤ toBiased w accB := by
      rw [hA]; exact Nat.le_add_left w.halfModulus accB
    have hSa : Nat.ble w.halfModulus (toBiased w accB) = true :=
      Nat.ble_eq_true_of_le hHLeA
    rw [hSa, hSb] at hMag
    change (w.modulus - toBiased w accB) * c ≤ w.halfModulus at hMag
    have hMagA : w.modulus - toBiased w accB = w.halfModulus - accB := by
      rw [hA, hModEq]
      have h1 : (w.halfModulus - accB) + (accB + w.halfModulus) =
          w.halfModulus + w.halfModulus := by
        rw [← Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hNegB)]
      have h2 := congrArg (fun k => k - (accB + w.halfModulus)) h1
      rw [Nat.add_sub_cancel] at h2
      exact h2.symm
    rw [hMagA] at hMag
    let p := (w.halfModulus - accB) * c
    have hPAdd : p + accB * c = w.halfModulus * c := by
      change (w.halfModulus - accB) * c + accB * c = w.halfModulus * c
      rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hNegB)]
    have hMulAdd : toBiased w accB * c + p = w.modulus * c := by
      change toBiased w accB * c + (w.halfModulus - accB) * c = w.modulus * c
      rw [← Nat.add_mul, hA, Nat.add_comm accB w.halfModulus, Nat.add_assoc,
        Nat.add_sub_of_le (Nat.le_of_lt hNegB), ← hModEq]
    cases Nat.eq_zero_or_pos p with
    | inl hP0 =>
      rw [hP0, Nat.add_zero] at hMulAdd
      have hR0 : r = 0 := by
        rw [hRDef, hMulAdd, Nat.mul_mod_right]
      rw [hR0, toBiased_nonneg w (by cases w <;> exact Nat.zero_lt_succ _),
        Nat.zero_add, ← hPAdd, hP0, Nat.zero_add, Nat.add_comm]
    | inr hPPos =>
      have hcPos : 0 < c := by
        cases c with
        | zero =>
          change 0 < (w.halfModulus - accB) * 0 at hPPos
          rw [Nat.mul_zero] at hPPos
          exact False.elim (Nat.lt_irrefl 0 hPPos)
        | succ _ => exact Nat.zero_lt_succ _
      have hPLeM : p ≤ w.modulus :=
        Nat.le_trans hMag (Nat.le_of_lt w.halfModulus_lt_modulus)
      have hSubLtM : w.modulus - p < w.modulus := by
        have h1 : (w.modulus - p) + p = w.modulus := Nat.sub_add_cancel hPLeM
        have h2 : (w.modulus - p) + 0 < (w.modulus - p) + p :=
          Nat.add_lt_add_left hPPos (w.modulus - p)
        rw [Nat.add_zero, h1] at h2
        exact h2
      have hHLeSub : w.halfModulus ≤ w.modulus - p := by
        have h1 : w.halfModulus + p ≤ w.halfModulus + w.halfModulus :=
          Nat.add_le_add_left hMag w.halfModulus
        rw [← hModEq] at h1
        exact Nat.le_sub_of_add_le h1
      have hMulSplit :
          toBiased w accB * c = (w.modulus - p) + w.modulus * (c - 1) := by
        have h1 : ((w.modulus - p) + w.modulus * (c - 1)) + p = w.modulus * c := by
          rw [Nat.add_assoc, Nat.add_comm (w.modulus * (c - 1)) p,
            ← Nat.add_assoc, Nat.sub_add_cancel hPLeM,
            Nat.add_comm w.modulus (w.modulus * (c - 1)),
            ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hcPos]
        exact Nat.add_right_cancel (hMulAdd.trans h1.symm)
      have hREq : r = w.modulus - p := by
        rw [hRDef, hMulSplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSubLtM]
      have hBiR : toBiased w r = w.halfModulus - p := by
        rw [hREq, toBiased_neg w hHLeSub hSubLtM, hModEq]
        have h1 : (w.halfModulus - p) + w.halfModulus =
            (w.halfModulus + w.halfModulus) - p :=
          sub_add_comm_nat hMag
        have h2 := congrArg (fun k => k - w.halfModulus) h1
        rw [Nat.add_sub_cancel] at h2
        exact h2.symm
      rw [hBiR, ← hPAdd, ← Nat.add_assoc, Nat.sub_add_cancel hMag, Nat.add_comm]
  | inr hNonnegB =>
    have hA : toBiased w accB = accB - w.halfModulus := toBiased_neg w hNonnegB hAcc
    have hALtH : toBiased w accB < w.halfModulus := by
      have h1 : w.halfModulus + (accB - w.halfModulus) <
          w.halfModulus + w.halfModulus := by
        rw [Nat.add_sub_of_le hNonnegB, ← hModEq]
        exact hAcc
      rw [hA]
      cases Nat.lt_or_ge (accB - w.halfModulus) w.halfModulus with
      | inl hLt => exact hLt
      | inr hGe => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_left hGe _))
    have hSa : Nat.ble w.halfModulus (toBiased w accB) = false :=
      nat_ble_false_iff_lt.mpr hALtH
    rw [hSa, hSb] at hMag
    change toBiased w accB * c < w.halfModulus at hMag
    have hProdLtM : toBiased w accB * c < w.modulus :=
      Nat.lt_trans hMag w.halfModulus_lt_modulus
    have hREq : r = toBiased w accB * c := by
      rw [hRDef, Nat.mod_eq_of_lt hProdLtM]
    rw [hREq, toBiased_nonneg w hMag, hA,
      Nat.add_assoc ((accB - w.halfModulus) * c) w.halfModulus (w.halfModulus * c),
      Nat.add_comm w.halfModulus (w.halfModulus * c),
      ← Nat.add_assoc ((accB - w.halfModulus) * c) (w.halfModulus * c) w.halfModulus,
      ← Nat.add_mul, Nat.sub_add_cancel hNonnegB]

/-- Tightened signed join interval for checked multiplication by a non-negative
multiplier `c < w.halfModulus` in biased coordinates (works across zero). -/
theorem mulWithOverflowS_biased_false_interval_nonneg (w : ScalarWidth)
    {lo hi accB c r : Nat} (hAcc : accB < w.modulus) (hc : c < w.halfModulus)
    (hLo : lo ≤ accB) (hHi : accB ≤ hi)
    (h : mulWithOverflowS w (toBiased w accB) c = (r, false)) :
    toBiased w r + w.halfModulus * c = accB * c + w.halfModulus ∧
    lo * c + w.halfModulus ≤ toBiased w r + w.halfModulus * c ∧
    toBiased w r + w.halfModulus * c ≤ hi * c + w.halfModulus ∧
    r < w.modulus := by
  let ⟨hEq, hRlt⟩ := toBiased_mulWithOverflowS_nonneg_mul w hAcc hc h
  refine ⟨hEq, ?_, ?_, hRlt⟩
  · rw [hEq]; exact Nat.add_le_add_right (Nat.mul_le_mul_right c hLo) _
  · rw [hEq]; exact Nat.add_le_add_right (Nat.mul_le_mul_right c hHi) _

/-- Fail-closed signed multiplication overflow certificate for non-negative
multiplier `c < w.halfModulus` in biased coordinates. -/
theorem mulWithOverflowS_biased_overflow_of_out_of_range_nonneg (w : ScalarWidth)
    {accB c : Nat} (hAcc : accB < w.modulus) (hc : c < w.halfModulus)
    (hOut : accB * c + w.halfModulus < w.halfModulus * c ∨
      w.modulus + w.halfModulus * c ≤ accB * c + w.halfModulus) :
    (mulWithOverflowS w (toBiased w accB) c).2 = true := by
  cases hF : (mulWithOverflowS w (toBiased w accB) c).2 with
  | true => rfl
  | false =>
    have hPair :
        mulWithOverflowS w (toBiased w accB) c =
          ((mulWithOverflowS w (toBiased w accB) c).1, false) := by
      cases hP : mulWithOverflowS w (toBiased w accB) c with
      | mk fst snd =>
        rw [hP] at hF
        dsimp only at hF
        rw [hF]
    let ⟨hEq, _⟩ := toBiased_mulWithOverflowS_nonneg_mul w hAcc hc hPair
    cases hOut with
    | inl hBelow =>
      rw [← hEq] at hBelow
      exact absurd hBelow (Nat.not_lt_of_ge (Nat.le_add_left _ _))
    | inr hAbove =>
      rw [← hEq] at hAbove
      have hLt :
          toBiased w (mulWithOverflowS w (toBiased w accB) c).1 + w.halfModulus * c <
            w.modulus + w.halfModulus * c :=
        Nat.add_lt_add_right (toBiased_lt_modulus w _) _
      exact absurd hLt (Nat.not_lt_of_ge hAbove)

/-- Exact biased-coordinate identity for non-overflowing signed multiplication
by a negative multiplier `c` (`w.halfModulus ≤ c < w.modulus`, magnitude
`k = w.modulus - c`), valid on BOTH sides of zero:
`toBiased w r + accB * (w.modulus - c) = w.halfModulus * (w.modulus - c) + w.halfModulus`. -/
theorem toBiased_mulWithOverflowS_neg_mul (w : ScalarWidth)
    {accB c r : Nat} (hAcc : accB < w.modulus)
    (hCNeg : w.halfModulus ≤ c) (hcM : c < w.modulus)
    (h : mulWithOverflowS w (toBiased w accB) c = (r, false)) :
    toBiased w r + accB * (w.modulus - c) =
      w.halfModulus * (w.modulus - c) + w.halfModulus ∧
    r < w.modulus := by
  have hNo : (mulWithOverflowS w (toBiased w accB) c).2 = false := congrArg Prod.snd h
  have hR : (mulWithOverflowS w (toBiased w accB) c).1 = r := congrArg Prod.fst h
  have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
  have haM : toBiased w accB < w.modulus := toBiased_lt_modulus w accB
  have hRlt : r < w.modulus := by
    rw [← hR]; unfold mulWithOverflowS; exact Nat.mod_lt _ w.modulus_pos
  have hRDef : r = (toBiased w accB * c) % w.modulus := by
    rw [← hR]; unfold mulWithOverflowS; dsimp only
    rw [Nat.mod_eq_of_lt haM, Nat.mod_eq_of_lt hcM]
  let ⟨_, _, hMag⟩ := (mulWithOverflowS_no_overflow_iff w (toBiased w accB) c).mp hNo
  have hSb : Nat.ble w.halfModulus c = true := Nat.ble_eq_true_of_le hCNeg
  let k := w.modulus - c
  have hCK : c + k = w.modulus := Nat.add_sub_of_le (Nat.le_of_lt hcM)
  refine ⟨?_, hRlt⟩
  cases Nat.lt_or_ge accB w.halfModulus with
  | inl hNegB =>
    have hA : toBiased w accB = accB + w.halfModulus := toBiased_nonneg w hNegB
    have hHLeA : w.halfModulus ≤ toBiased w accB := by
      rw [hA]; exact Nat.le_add_left w.halfModulus accB
    have hSa : Nat.ble w.halfModulus (toBiased w accB) = true :=
      Nat.ble_eq_true_of_le hHLeA
    rw [hSa, hSb] at hMag
    change (w.modulus - toBiased w accB) * k < w.halfModulus at hMag
    have hMagA : w.modulus - toBiased w accB = w.halfModulus - accB := by
      rw [hA, hModEq]
      have h1 : (w.halfModulus - accB) + (accB + w.halfModulus) =
          w.halfModulus + w.halfModulus := by
        rw [← Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt hNegB)]
      have h2 := congrArg (fun j => j - (accB + w.halfModulus)) h1
      rw [Nat.add_sub_cancel] at h2
      exact h2.symm
    rw [hMagA] at hMag
    let p := (w.halfModulus - accB) * k
    have hMLeAC : w.modulus ≤ toBiased w accB + c := by
      rw [hModEq]; exact Nat.add_le_add hHLeA hCNeg
    have hACDecomp :
        toBiased w accB * c = p + w.modulus * (toBiased w accB + c - w.modulus) := by
      have hLeft : toBiased w accB * c + (w.modulus - toBiased w accB) * c =
          w.modulus * c := by
        rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt haM)]
      have hRight :
          (p + w.modulus * (toBiased w accB + c - w.modulus)) +
              (w.modulus - toBiased w accB) * c =
            w.modulus * c := by
        have hPK : p + (w.modulus - toBiased w accB) * c =
            w.modulus * (w.modulus - toBiased w accB) := by
          change (w.halfModulus - accB) * k + (w.modulus - toBiased w accB) * c = _
          rw [← hMagA, Nat.add_comm, ← Nat.mul_add, hCK, Nat.mul_comm]
        rw [Nat.add_assoc p _ _, Nat.add_comm (w.modulus * _) _, ← Nat.add_assoc p _ _,
          hPK, ← Nat.mul_add]
        have hSum :
            (w.modulus - toBiased w accB) + (toBiased w accB + c - w.modulus) = c := by
          have h1 :
              ((w.modulus - toBiased w accB) + (toBiased w accB + c - w.modulus)) +
                  w.modulus =
                c + w.modulus := by
            rw [Nat.add_assoc, Nat.sub_add_cancel hMLeAC,
              ← Nat.add_assoc, Nat.sub_add_cancel (Nat.le_of_lt haM),
              Nat.add_comm]
          exact Nat.add_right_cancel h1
        rw [hSum]
      exact Nat.add_right_cancel (hLeft.trans hRight.symm)
    have hPLtM : p < w.modulus := Nat.lt_trans hMag w.halfModulus_lt_modulus
    have hREq : r = p := by
      rw [hRDef, hACDecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hPLtM]
    rw [hREq, toBiased_nonneg w hMag,
      Nat.add_assoc p w.halfModulus (accB * k),
      Nat.add_comm w.halfModulus (accB * k),
      ← Nat.add_assoc p (accB * k) w.halfModulus]
    change (w.halfModulus - accB) * k + accB * k + w.halfModulus = _
    rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hNegB)]
  | inr hNonnegB =>
    have hA : toBiased w accB = accB - w.halfModulus := toBiased_neg w hNonnegB hAcc
    have hALtH : toBiased w accB < w.halfModulus := by
      have h1 : w.halfModulus + (accB - w.halfModulus) <
          w.halfModulus + w.halfModulus := by
        rw [Nat.add_sub_of_le hNonnegB, ← hModEq]
        exact hAcc
      rw [hA]
      cases Nat.lt_or_ge (accB - w.halfModulus) w.halfModulus with
      | inl hLt => exact hLt
      | inr hGe => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_left hGe _))
    have hSa : Nat.ble w.halfModulus (toBiased w accB) = false :=
      nat_ble_false_iff_lt.mpr hALtH
    rw [hSa, hSb] at hMag
    change toBiased w accB * k ≤ w.halfModulus at hMag
    let p := toBiased w accB * k
    have hMulAdd : toBiased w accB * c + p = toBiased w accB * w.modulus := by
      change toBiased w accB * c + toBiased w accB * k = toBiased w accB * w.modulus
      rw [← Nat.mul_add, hCK]
    have hAccK : accB * k = p + w.halfModulus * k := by
      change accB * k = toBiased w accB * k + w.halfModulus * k
      rw [hA, ← Nat.add_mul, Nat.sub_add_cancel hNonnegB]
    cases Nat.eq_zero_or_pos p with
    | inl hP0 =>
      rw [hP0, Nat.add_zero] at hMulAdd
      have hR0 : r = 0 := by
        rw [hRDef, hMulAdd, Nat.mul_mod_left]
      rw [hR0, toBiased_nonneg w (by cases w <;> exact Nat.zero_lt_succ _),
        Nat.zero_add, hAccK, hP0, Nat.zero_add, Nat.add_comm]
    | inr hPPos =>
      have haPos : 0 < toBiased w accB := by
        cases hZ : toBiased w accB with
        | zero =>
          change 0 < toBiased w accB * k at hPPos
          rw [hZ, Nat.zero_mul] at hPPos
          exact False.elim (Nat.lt_irrefl 0 hPPos)
        | succ _ => exact Nat.zero_lt_succ _
      have hPLeM : p ≤ w.modulus :=
        Nat.le_trans hMag (Nat.le_of_lt w.halfModulus_lt_modulus)
      have hSubLtM : w.modulus - p < w.modulus := by
        have h1 : (w.modulus - p) + p = w.modulus := Nat.sub_add_cancel hPLeM
        have h2 : (w.modulus - p) + 0 < (w.modulus - p) + p :=
          Nat.add_lt_add_left hPPos (w.modulus - p)
        rw [Nat.add_zero, h1] at h2
        exact h2
      have hHLeSub : w.halfModulus ≤ w.modulus - p := by
        have h1 : w.halfModulus + p ≤ w.halfModulus + w.halfModulus :=
          Nat.add_le_add_left hMag w.halfModulus
        rw [← hModEq] at h1
        exact Nat.le_sub_of_add_le h1
      have hMulSplit :
          toBiased w accB * c = (w.modulus - p) + w.modulus * (toBiased w accB - 1) := by
        have h1 : ((w.modulus - p) + w.modulus * (toBiased w accB - 1)) + p =
            toBiased w accB * w.modulus := by
          rw [Nat.add_assoc, Nat.add_comm (w.modulus * _) p,
            ← Nat.add_assoc, Nat.sub_add_cancel hPLeM,
            Nat.add_comm w.modulus (w.modulus * (toBiased w accB - 1)),
            ← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel haPos,
            Nat.mul_comm]
        exact Nat.add_right_cancel (hMulAdd.trans h1.symm)
      have hREq : r = w.modulus - p := by
        rw [hRDef, hMulSplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hSubLtM]
      have hBiR : toBiased w r = w.halfModulus - p := by
        rw [hREq, toBiased_neg w hHLeSub hSubLtM, hModEq]
        have h1 : (w.halfModulus - p) + w.halfModulus =
            (w.halfModulus + w.halfModulus) - p :=
          sub_add_comm_nat hMag
        have h2 := congrArg (fun j => j - w.halfModulus) h1
        rw [Nat.add_sub_cancel] at h2
        exact h2.symm
      rw [hBiR, hAccK, ← Nat.add_assoc, Nat.sub_add_cancel hMag, Nat.add_comm]

/-- Tightened reversed signed join interval for checked multiplication by a
negative multiplier `c` (`w.halfModulus ≤ c < w.modulus`, `k = w.modulus - c`)
in biased coordinates (works across zero). -/
theorem mulWithOverflowS_biased_false_interval_neg (w : ScalarWidth)
    {lo hi accB c r : Nat} (hAcc : accB < w.modulus)
    (hCNeg : w.halfModulus ≤ c) (hcM : c < w.modulus)
    (hLo : lo ≤ accB) (hHi : accB ≤ hi)
    (h : mulWithOverflowS w (toBiased w accB) c = (r, false)) :
    toBiased w r + accB * (w.modulus - c) =
      w.halfModulus * (w.modulus - c) + w.halfModulus ∧
    toBiased w r + lo * (w.modulus - c) ≤
      w.halfModulus * (w.modulus - c) + w.halfModulus ∧
    w.halfModulus * (w.modulus - c) + w.halfModulus ≤
      toBiased w r + hi * (w.modulus - c) ∧
    r < w.modulus := by
  let ⟨hEq, hRlt⟩ := toBiased_mulWithOverflowS_neg_mul w hAcc hCNeg hcM h
  refine ⟨hEq, ?_, ?_, hRlt⟩
  · rw [← hEq]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hLo) _
  · rw [← hEq]; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hHi) _

/-- Cross-zero signed widening in biased coordinates: for ANY `accB <
srcW.modulus` (negative, zero, OR positive!) and `srcW.bits ≤ dstW.bits`,
sign-extending `toBiased srcW accB` to `dstW` shifts its biased coordinate by
the exact constant `dstW.halfModulus - srcW.halfModulus`. -/
theorem toBiased_intToIntCast_widen_signed (srcW dstW : ScalarWidth)
    {accB : Nat} (hLe : srcW.bits ≤ dstW.bits) (hAcc : accB < srcW.modulus) :
    toBiased dstW (intToIntCast srcW true dstW (toBiased srcW accB)) =
      accB + (dstW.halfModulus - srcW.halfModulus) := by
  have hSMod : srcW.modulus = srcW.halfModulus + srcW.halfModulus := by
    rw [srcW.modulus_eq_two_mul_half, Nat.two_mul]
  have hDMod : dstW.modulus = dstW.halfModulus + dstW.halfModulus := by
    rw [dstW.modulus_eq_two_mul_half, Nat.two_mul]
  have hHLe : srcW.halfModulus ≤ dstW.halfModulus := by
    unfold ScalarWidth.halfModulus
    exact pow2_le_pow2 (Nat.sub_le_sub_right hLe 1)
  cases Nat.lt_or_eq_of_le hLe with
  | inr hBitsEq =>
    have hModEq : srcW.modulus = dstW.modulus := by
      unfold ScalarWidth.modulus; rw [hBitsEq]
    have hHalfEq : srcW.halfModulus = dstW.halfModulus := by
      unfold ScalarWidth.halfModulus; rw [hBitsEq]
    have hCast : intToIntCast srcW true dstW (toBiased srcW accB) =
        toBiased srcW accB := by
      rw [intToIntCast_narrow_exact srcW true dstW (Nat.le_of_eq hBitsEq.symm)]
      rw [← hModEq]
      exact toBiased_lt_modulus srcW accB
    rw [hCast, hHalfEq, Nat.sub_self, Nat.add_zero]
    unfold toBiased
    rw [← hModEq, ← hHalfEq]
    have hInv := toBiased_involutive srcW accB
    unfold toBiased at hInv
    rw [hInv, Nat.mod_eq_of_lt hAcc]
  | inl hLt =>
    have hModLe : srcW.modulus ≤ dstW.modulus := pow2_le_pow2 hLe
    cases Nat.lt_or_ge accB srcW.halfModulus with
    | inl hNegB =>
      have hX : toBiased srcW accB = accB + srcW.halfModulus :=
        toBiased_nonneg srcW hNegB
      have hXNeg : srcW.halfModulus ≤ toBiased srcW accB := by
        rw [hX]; exact Nat.le_add_left _ _
      have hXLt : toBiased srcW accB < srcW.modulus := toBiased_lt_modulus srcW accB
      have hY := (intToIntCast_widen_signed_neg srcW dstW hLt hXNeg hXLt).1
      have hYNeg := intToIntCast_widen_signed_neg_sign srcW dstW hLt hXNeg hXLt
      have hYLt := intToIntCast_lt_modulus srcW true dstW (toBiased srcW accB)
      rw [toBiased_neg dstW hYNeg hYLt, hY, hX]
      have h1 :
          (accB + (dstW.halfModulus - srcW.halfModulus)) + dstW.halfModulus + srcW.modulus =
            ((dstW.modulus - srcW.modulus) + (accB + srcW.halfModulus)) + srcW.modulus := by
        rw [Nat.add_assoc (dstW.modulus - srcW.modulus) _ _,
          Nat.add_comm (accB + srcW.halfModulus) srcW.modulus,
          ← Nat.add_assoc (dstW.modulus - srcW.modulus) srcW.modulus _,
          Nat.sub_add_cancel hModLe, hDMod, hSMod]
        rw [Nat.add_assoc accB (dstW.halfModulus - srcW.halfModulus) dstW.halfModulus,
          Nat.add_assoc accB _ (srcW.halfModulus + srcW.halfModulus),
          Nat.add_assoc (dstW.halfModulus - srcW.halfModulus) dstW.halfModulus _,
          ← Nat.add_assoc dstW.halfModulus srcW.halfModulus srcW.halfModulus,
          Nat.add_comm dstW.halfModulus srcW.halfModulus,
          Nat.add_assoc srcW.halfModulus dstW.halfModulus srcW.halfModulus,
          ← Nat.add_assoc (dstW.halfModulus - srcW.halfModulus) srcW.halfModulus _,
          Nat.sub_add_cancel hHLe]
        rw [← Nat.add_assoc dstW.halfModulus dstW.halfModulus srcW.halfModulus,
          Nat.add_comm accB (dstW.halfModulus + dstW.halfModulus + srcW.halfModulus),
          Nat.add_assoc (dstW.halfModulus + dstW.halfModulus) srcW.halfModulus accB,
          Nat.add_comm srcW.halfModulus accB]
      have h2 := Nat.add_right_cancel h1
      have h3 := congrArg (fun j => j - dstW.halfModulus) h2
      rw [Nat.add_sub_cancel] at h3
      exact h3.symm
    | inr hNonnegB =>
      have hX : toBiased srcW accB = accB - srcW.halfModulus :=
        toBiased_neg srcW hNonnegB hAcc
      have hXLtH : toBiased srcW accB < srcW.halfModulus := by
        have h1 : srcW.halfModulus + (accB - srcW.halfModulus) <
            srcW.halfModulus + srcW.halfModulus := by
          rw [Nat.add_sub_of_le hNonnegB, ← hSMod]; exact hAcc
        rw [hX]
        cases Nat.lt_or_ge (accB - srcW.halfModulus) srcW.halfModulus with
        | inl hL => exact hL
        | inr hG => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_left hG _))
      have hY := intToIntCast_widen_signed_nonneg srcW dstW hLt hXLtH
      have hYLtDH : toBiased srcW accB < dstW.halfModulus :=
        Nat.lt_of_lt_of_le hXLtH hHLe
      rw [hY, toBiased_nonneg dstW hYLtDH, hX]
      have h1 : (accB - srcW.halfModulus) + dstW.halfModulus + srcW.halfModulus =
          (accB + (dstW.halfModulus - srcW.halfModulus)) + srcW.halfModulus := by
        rw [Nat.add_assoc (accB - srcW.halfModulus) dstW.halfModulus srcW.halfModulus,
          Nat.add_comm dstW.halfModulus srcW.halfModulus,
          ← Nat.add_assoc (accB - srcW.halfModulus) srcW.halfModulus dstW.halfModulus,
          Nat.sub_add_cancel hNonnegB,
          Nat.add_assoc accB (dstW.halfModulus - srcW.halfModulus) srcW.halfModulus,
          Nat.sub_add_cancel hHLe]
      exact Nat.add_right_cancel h1

/-- Cross-zero signed narrowing in biased coordinates: when `dstW.bits ≤
srcW.bits` and `accB` lies inside the exact representable signed range of `dstW`
(`srcW.halfModulus - dstW.halfModulus ≤ accB < srcW.halfModulus +
dstW.halfModulus`), narrowing shifts the biased coordinate by
`-(srcW.halfModulus - dstW.halfModulus)` on BOTH sides of zero. -/
theorem toBiased_intToIntCast_narrow_signed (srcW : ScalarWidth)
    (srcSigned : Bool) (dstW : ScalarWidth) {accB : Nat}
    (hLe : dstW.bits ≤ srcW.bits)
    (hLo : srcW.halfModulus - dstW.halfModulus ≤ accB)
    (hHi : accB < srcW.halfModulus + dstW.halfModulus) :
    toBiased dstW (intToIntCast srcW srcSigned dstW (toBiased srcW accB)) =
      accB - (srcW.halfModulus - dstW.halfModulus) := by
  have hSMod : srcW.modulus = srcW.halfModulus + srcW.halfModulus := by
    rw [srcW.modulus_eq_two_mul_half, Nat.two_mul]
  have hDMod : dstW.modulus = dstW.halfModulus + dstW.halfModulus := by
    rw [dstW.modulus_eq_two_mul_half, Nat.two_mul]
  have hHLe : dstW.halfModulus ≤ srcW.halfModulus := by
    unfold ScalarWidth.halfModulus
    exact pow2_le_pow2 (Nat.sub_le_sub_right hLe 1)
  have hAccLt : accB < srcW.modulus := by
    rw [hSMod]
    exact Nat.lt_of_lt_of_le hHi (Nat.add_le_add_left hHLe _)
  cases Nat.lt_or_ge accB srcW.halfModulus with
  | inl hNegB =>
    have hX : toBiased srcW accB = accB + srcW.halfModulus :=
      toBiased_nonneg srcW hNegB
    have hXLt : toBiased srcW accB < srcW.modulus := toBiased_lt_modulus srcW accB
    have hXLo : srcW.modulus - dstW.halfModulus ≤ toBiased srcW accB := by
      rw [hX, hSMod]
      have h1 : (srcW.halfModulus + srcW.halfModulus) - dstW.halfModulus =
          (srcW.halfModulus - dstW.halfModulus) + srcW.halfModulus :=
        (sub_add_comm_nat hHLe).symm
      rw [h1]
      exact Nat.add_le_add_right hLo _
    let ⟨hCastEq, hYNeg, _⟩ :=
      intToIntCast_narrow_signed_neg srcW srcSigned dstW hLe hXLo hXLt
    have hYLt := intToIntCast_lt_modulus srcW srcSigned dstW (toBiased srcW accB)
    rw [toBiased_neg dstW hYNeg hYLt]
    have hModLe : dstW.modulus ≤ srcW.modulus := pow2_le_pow2 hLe
    have h1 :
        (intToIntCast srcW srcSigned dstW (toBiased srcW accB) - dstW.halfModulus) +
            (srcW.halfModulus - dstW.halfModulus) + srcW.modulus =
          accB + srcW.modulus := by
      have hYPlus :
          (intToIntCast srcW srcSigned dstW (toBiased srcW accB) - dstW.halfModulus) +
              (srcW.halfModulus - dstW.halfModulus) + dstW.modulus =
            intToIntCast srcW srcSigned dstW (toBiased srcW accB) + srcW.halfModulus := by
        rw [hDMod, Nat.add_assoc _ (srcW.halfModulus - dstW.halfModulus) _,
          ← Nat.add_assoc (srcW.halfModulus - dstW.halfModulus) dstW.halfModulus dstW.halfModulus,
          Nat.sub_add_cancel hHLe, Nat.add_comm srcW.halfModulus dstW.halfModulus,
          ← Nat.add_assoc _ dstW.halfModulus srcW.halfModulus,
          Nat.sub_add_cancel hYNeg]
      have hStep :
          (intToIntCast srcW srcSigned dstW (toBiased srcW accB) - dstW.halfModulus) +
              (srcW.halfModulus - dstW.halfModulus) + srcW.modulus =
            ((intToIntCast srcW srcSigned dstW (toBiased srcW accB) - dstW.halfModulus) +
                (srcW.halfModulus - dstW.halfModulus) + dstW.modulus) +
              (srcW.modulus - dstW.modulus) := by
        conv => rhs; rw [Nat.add_assoc _ dstW.modulus (srcW.modulus - dstW.modulus), Nat.add_sub_of_le hModLe]
      rw [hStep, hYPlus, Nat.add_assoc, Nat.add_comm srcW.halfModulus _,
        ← Nat.add_assoc, Nat.add_comm (intToIntCast _ _ _ _) _, hCastEq, hX,
        Nat.add_assoc, ← hSMod]
    have h2 := Nat.add_right_cancel h1
    have h3 := congrArg (fun j => j - (srcW.halfModulus - dstW.halfModulus)) h2
    rw [Nat.add_sub_cancel] at h3
    exact h3
  | inr hNonnegB =>
    have hX : toBiased srcW accB = accB - srcW.halfModulus :=
      toBiased_neg srcW hNonnegB hAccLt
    have hXLtDH : toBiased srcW accB < dstW.halfModulus := by
      rw [hX]
      have h1 : srcW.halfModulus + (accB - srcW.halfModulus) <
          srcW.halfModulus + dstW.halfModulus := by
        rw [Nat.add_sub_of_le hNonnegB]; exact hHi
      cases Nat.lt_or_ge (accB - srcW.halfModulus) dstW.halfModulus with
      | inl hL => exact hL
      | inr hG => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_left hG _))
    have hXLtDM : toBiased srcW accB < dstW.modulus :=
      Nat.lt_trans hXLtDH dstW.halfModulus_lt_modulus
    rw [intToIntCast_narrow_exact srcW srcSigned dstW hLe hXLtDM,
      toBiased_nonneg dstW hXLtDH, hX]
    have h1 :
        ((accB - srcW.halfModulus) + dstW.halfModulus) +
            (srcW.halfModulus - dstW.halfModulus) =
          accB := by
      rw [Nat.add_assoc, Nat.add_sub_of_le hHLe, Nat.sub_add_cancel hNonnegB]
    have h2 := congrArg (fun j => j - (srcW.halfModulus - dstW.halfModulus)) h1
    rw [Nat.add_sub_cancel] at h2
    exact h2

/-- Interval cutpoint specification at `blockIdx` for scalar width `width`:
constrains the active accumulator to `lo ≤ acc ≤ hi < width.modulus`. -/
structure StageIntervalSpec where
  /-- Basic-block cutpoint index. -/
  blockIdx : Nat
  /-- Width of the active accumulator local at this cutpoint. -/
  width : ScalarWidth
  /-- Inclusive lower bound on the accumulator value. -/
  lo : Nat
  /-- Inclusive upper bound on the accumulator value (`hi < width.modulus`). -/
  hi : Nat

namespace StageIntervalSpec

/-- Decidable certificate checking that `val` lies inside `[spec.lo, spec.hi]`
with `spec.hi < spec.width.modulus`. -/
def inRange (spec : StageIntervalSpec) (val : Nat) : Bool :=
  Nat.ble spec.lo val && Nat.ble val spec.hi &&
    Nat.blt spec.hi spec.width.modulus

private theorem nat_blt_eq_true_of_lt {a b : Nat} (h : a < b) :
    Nat.blt a b = true :=
  Nat.ble_eq_true_of_le h

/-- Soundness of `StageIntervalSpec.inRange`. -/
theorem inRange_iff (spec : StageIntervalSpec) (val : Nat) :
    spec.inRange val = true ↔
      spec.lo ≤ val ∧ val ≤ spec.hi ∧ spec.hi < spec.width.modulus := by
  unfold inRange
  constructor
  · intro h
    cases h1 : Nat.ble spec.lo val with
    | false => rw [h1] at h; cases h
    | true =>
      cases h2 : Nat.ble val spec.hi with
      | false => rw [h1, h2] at h; cases h
      | true =>
        rw [h1, h2] at h
        exact ⟨Nat.le_of_ble_eq_true h1, Nat.le_of_ble_eq_true h2,
          Nat.le_of_ble_eq_true h⟩
  · intro ⟨hLo, hHi, hMod⟩
    rw [Nat.ble_eq_true_of_le hLo, Nat.ble_eq_true_of_le hHi,
      nat_blt_eq_true_of_lt hMod]
    rfl

/-- Fail-closed: any out-of-width value (`spec.width.modulus ≤ val`) fails
`spec.inRange`. -/
theorem inRange_false_of_ge_modulus (spec : StageIntervalSpec) {val : Nat}
    (hGe : spec.width.modulus ≤ val) : spec.inRange val = false := by
  cases h : spec.inRange val with
  | false => rfl
  | true =>
    let ⟨_, hHi, hMod⟩ := (spec.inRange_iff val).mp h
    exact False.elim (Nat.not_lt_of_ge hGe (Nat.lt_of_le_of_lt hHi hMod))

end StageIntervalSpec

/-- Updates `(accId, tmpId, ovfMulId, ovfAddId)` on top of `baseLocals` via
`listSetAt`, framing every other local slot verbatim. -/
def applyStageSlots {Val : Type v} (baseLocals : List Val)
    (ids : StageLocalIds) (vAcc vTmp vMul vAdd : Val) : List Val :=
  listSetAt
    (listSetAt
      (listSetAt
        (listSetAt baseLocals ids.accId vAcc)
        ids.tmpId vTmp)
      ids.ovfMulId vMul)
    ids.ovfAddId vAdd

/-- `applyStageSlots` preserves the length of `baseLocals`. -/
theorem applyStageSlots_length {Val : Type v} (baseLocals : List Val)
    (ids : StageLocalIds) (vAcc vTmp vMul vAdd : Val) :
    (applyStageSlots baseLocals ids vAcc vTmp vMul vAdd).length =
      baseLocals.length := by
  unfold applyStageSlots
  rw [listSetAt_length, listSetAt_length, listSetAt_length, listSetAt_length]

/-- Reading `ids.accId` after `applyStageSlots` returns `some vAcc`. -/
theorem applyStageSlots_get_acc {Val : Type v} {baseLocals : List Val}
    {ids : StageLocalIds} (u : ids.Unpacked baseLocals.length)
    (vAcc vTmp vMul vAdd : Val) :
    listGet? (applyStageSlots baseLocals ids vAcc vTmp vMul vAdd) ids.accId =
      some vAcc := by
  unfold applyStageSlots
  rw [listGet?_listSetAt_ne _ _ u.accNeAdd,
    listGet?_listSetAt_ne _ _ u.accNeMul,
    listGet?_listSetAt_ne _ _ u.accNeTmp,
    listGet?_listSetAt_same _ u.accLt]

/-- Reading any bystander local outside `{accId, tmpId, ovfMulId, ovfAddId}`
after `applyStageSlots` recovers `listGet? baseLocals j`. -/
theorem applyStageSlots_get_other {Val : Type v} (baseLocals : List Val)
    (ids : StageLocalIds) (vAcc vTmp vMul vAdd : Val) {j : Nat}
    (h1 : j ≠ ids.accId) (h2 : j ≠ ids.tmpId)
    (h3 : j ≠ ids.ovfMulId) (h4 : j ≠ ids.ovfAddId) :
    listGet? (applyStageSlots baseLocals ids vAcc vTmp vMul vAdd) j =
      listGet? baseLocals j := by
  unfold applyStageSlots
  rw [listGet?_listSetAt_ne _ _ h4, listGet?_listSetAt_ne _ _ h3,
    listGet?_listSetAt_ne _ _ h2, listGet?_listSetAt_ne _ _ h1]

/-- Cutpoint state invariant: `s` sits at `spec.blockIdx`, its local table has
length `baseLocals.length`, its accumulator `ids.accId` holds an encoded scalar
`acc ∈ [spec.lo, spec.hi]` with `spec.hi < spec.width.modulus`, and every local
index outside `{accId, tmpId, ovfMulId, ovfAddId}` agrees with `baseLocals`. -/
def StageIntervalStateInv {S : Type u} {Val : Type v}
    (fops : OvfCastFrameOps S Val) (baseLocals : List Val)
    (ids : StageLocalIds) (spec : StageIntervalSpec) (s : S) : Prop :=
  fops.blockOf s = spec.blockIdx ∧
  (fops.localsOf s).length = baseLocals.length ∧
  (∃ acc : Nat,
    listGet? (fops.localsOf s) ids.accId = some (fops.mkScalar spec.width acc) ∧
    spec.lo ≤ acc ∧ acc ≤ spec.hi ∧ spec.hi < spec.width.modulus) ∧
  (∀ j : Nat,
    j ≠ ids.accId → j ≠ ids.tmpId → j ≠ ids.ovfMulId → j ≠ ids.ovfAddId →
    listGet? (fops.localsOf s) j = listGet? baseLocals j)

/-- Exact cutpoint bridge between raw unsigned intervals and `signedView`
biased intervals for non-negative ranges (`hi < w.halfModulus`): lets Episode 2
switch seamlessly between raw `fops` and `fops.signedView` at any non-negative
cutpoint without touching machine state. -/
theorem stageIntervalStateInv_signedView_nonneg_iff {S : Type u} {Val : Type v}
    (fops : OvfCastFrameOps S Val) (baseLocals : List Val)
    (ids : StageLocalIds) (bb : Nat) (w : ScalarWidth) {lo hi : Nat}
    (hHi : hi < w.halfModulus) (s : S) :
    StageIntervalStateInv fops baseLocals ids ⟨bb, w, lo, hi⟩ s ↔
      StageIntervalStateInv fops.signedView baseLocals ids
        ⟨bb, w, lo + w.halfModulus, hi + w.halfModulus⟩ s := by
  have hModEq : w.modulus = w.halfModulus + w.halfModulus := by
    rw [w.modulus_eq_two_mul_half, Nat.two_mul]
  have hHiBiLt : hi + w.halfModulus < w.modulus := by
    rw [hModEq]; exact Nat.add_lt_add_right hHi w.halfModulus
  constructor
  · intro ⟨hBb, hLen, ⟨acc, hGet, hALo, hAHi, _⟩, hFrame⟩
    refine ⟨hBb, hLen, ⟨acc + w.halfModulus, ?_, Nat.add_le_add_right hALo _,
      Nat.add_le_add_right hAHi _, hHiBiLt⟩, hFrame⟩
    have hAccH : acc < w.halfModulus := Nat.lt_of_le_of_lt hAHi hHi
    have hAccBiLt : acc + w.halfModulus < w.modulus := by
      rw [hModEq]; exact Nat.add_lt_add_right hAccH w.halfModulus
    show listGet? (fops.localsOf s) ids.accId =
      some (fops.mkScalar w (toBiased w (acc + w.halfModulus)))
    rw [toBiased_neg w (Nat.le_add_left _ _) hAccBiLt, Nat.add_sub_cancel]
    exact hGet
  · intro ⟨hBb, hLen, ⟨accB, hGet, hALo, hAHi, _⟩, hFrame⟩
    have hHLe : w.halfModulus ≤ accB :=
      Nat.le_trans (Nat.le_add_left w.halfModulus lo) hALo
    have hAccBLt : accB < w.modulus := Nat.lt_of_le_of_lt hAHi hHiBiLt
    refine ⟨hBb, hLen, ⟨accB - w.halfModulus, ?_, ?_, ?_,
      Nat.lt_trans hHi w.halfModulus_lt_modulus⟩, hFrame⟩
    · change listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar w (toBiased w accB)) at hGet
      rw [toBiased_neg w hHLe hAccBLt] at hGet
      exact hGet
    · exact Nat.le_sub_of_add_le hALo
    · have h1 : (accB - w.halfModulus) + w.halfModulus ≤ hi + w.halfModulus := by
        rw [Nat.sub_add_cancel hHLe]; exact hAHi
      exact Nat.le_of_add_le_add_right h1

/-- Any state built with `applyStageSlots` and an in-range accumulator
satisfies `StageIntervalStateInv`. -/
theorem applyStageSlots_satisfies_inv {S : Type u} {Val : Type v}
    {fops : OvfCastFrameOps S Val} (hLaw : fops.Lawful)
    {baseLocals : List Val} {ids : StageLocalIds}
    (hWf : ids.wf baseLocals.length = true)
    {spec : StageIntervalSpec} {s : S} {acc : Nat} {vTmp vMul vAdd : Val}
    (hLo : spec.lo ≤ acc) (hHi : acc ≤ spec.hi)
    (hMod : spec.hi < spec.width.modulus) :
    StageIntervalStateInv fops baseLocals ids spec
      (fops.withBlockLocals s spec.blockIdx
        (applyStageSlots baseLocals ids (fops.mkScalar spec.width acc)
          vTmp vMul vAdd)) := by
  have u := StageLocalIds.wf_unpack hWf
  refine ⟨hLaw.blockOf_withBlockLocals s _ _,
    (congrArg List.length (hLaw.localsOf_withBlockLocals s _ _)).trans
      (applyStageSlots_length baseLocals ids _ _ _ _),
    ⟨acc, ?_, hLo, hHi, hMod⟩, ?_⟩
  · rw [hLaw.localsOf_withBlockLocals]
    exact applyStageSlots_get_acc u _ _ _ _
  · intro j h1 h2 h3 h4
    rw [hLaw.localsOf_withBlockLocals]
    exact applyStageSlots_get_other baseLocals ids _ _ _ _ h1 h2 h3 h4

/-- Updating only `ids.accId` (or any subset of `{accId, tmpId, ovfMulId,
ovfAddId}`) preserves the bystander-frame property of `StageIntervalStateInv`. -/
theorem stageIntervalStateInv_set_acc {S : Type u} {Val : Type v}
    {fops : OvfCastFrameOps S Val} (hLaw : fops.Lawful)
    {baseLocals : List Val} {ids : StageLocalIds}
    {spec₁ spec₂ : StageIntervalSpec} {s : S} {acc' : Nat}
    (hWf : ids.wf baseLocals.length = true)
    (hInv : StageIntervalStateInv fops baseLocals ids spec₁ s)
    (hLo : spec₂.lo ≤ acc') (hHi : acc' ≤ spec₂.hi)
    (hMod : spec₂.hi < spec₂.width.modulus) :
    StageIntervalStateInv fops baseLocals ids spec₂
      (fops.withBlockLocals s spec₂.blockIdx
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar spec₂.width acc'))) := by
  have u := StageLocalIds.wf_unpack hWf
  have hLen : (fops.localsOf s).length = baseLocals.length := hInv.2.1
  refine ⟨hLaw.blockOf_withBlockLocals s _ _, ?_, ⟨acc', ?_, hLo, hHi, hMod⟩, ?_⟩
  · rw [hLaw.localsOf_withBlockLocals, listSetAt_length, hLen]
  · rw [hLaw.localsOf_withBlockLocals]
    exact listGet?_listSetAt_same _ (by rw [hLen]; exact u.accLt)
  · intro j h1 h2 h3 h4
    rw [hLaw.localsOf_withBlockLocals, listGet?_listSetAt_ne _ _ h1]
    exact hInv.2.2.2 j h1 h2 h3 h4

/-- Fail-closed negative lemma: if a state's accumulator slot holds an
unrepresentable scalar value rejected by `fops.asScalar? spec.width` (e.g. an
out-of-width value `spec.width.modulus ≤ val` when `asScalar?` enforces the
width bound), it CANNOT satisfy `StageIntervalStateInv`. -/
theorem not_stageIntervalStateInv_of_ge_modulus {S : Type u} {Val : Type v}
    {fops : OvfCastFrameOps S Val} (hLaw : fops.Lawful)
    {baseLocals : List Val} {ids : StageLocalIds}
    {spec : StageIntervalSpec} {s : S} {val : Nat}
    (hGet : listGet? (fops.localsOf s) ids.accId = some (fops.mkScalar spec.width val))
    (hAsNone : fops.asScalar? spec.width (fops.mkScalar spec.width val) = none) :
    ¬ StageIntervalStateInv fops baseLocals ids spec s := by
  intro hInv
  let ⟨acc, hAccGet, _, hAccHi, hHiMod⟩ := hInv.2.2.1
  have hEqVal : fops.mkScalar spec.width acc = fops.mkScalar spec.width val :=
    Option.some.inj (hAccGet.symm.trans hGet)
  have hSome : fops.asScalar? spec.width (fops.mkScalar spec.width acc) = some acc :=
    hLaw.asScalar?_mkScalar spec.width acc (Nat.lt_of_le_of_lt hAccHi hHiMod)
  rw [hEqVal, hAsNone] at hSome
  cases hSome

/-- Fail-closed negative lemma: a state at a different basic block
(`fops.blockOf s ≠ spec.blockIdx`) CANNOT satisfy `StageIntervalStateInv`. -/
theorem not_stageIntervalStateInv_of_block_ne {S : Type u} {Val : Type v}
    {fops : OvfCastFrameOps S Val} {baseLocals : List Val}
    {ids : StageLocalIds} {spec : StageIntervalSpec} {s : S}
    (hNe : fops.blockOf s ≠ spec.blockIdx) :
    ¬ StageIntervalStateInv fops baseLocals ids spec s :=
  fun hInv => hNe hInv.1

/-- Fail-closed negative lemma: a state whose bystander local `j` differs from
`baseLocals` CANNOT satisfy `StageIntervalStateInv`. -/
theorem not_stageIntervalStateInv_of_bystander_changed {S : Type u}
    {Val : Type v} {fops : OvfCastFrameOps S Val} {baseLocals : List Val}
    {ids : StageLocalIds} {spec : StageIntervalSpec} {s : S} {j : Nat}
    (hByst : ids.isBystander j = true)
    (hNe : listGet? (fops.localsOf s) j ≠ listGet? baseLocals j) :
    ¬ StageIntervalStateInv fops baseLocals ids spec s := by
  intro hInv
  have ⟨h1, h2, h3, h4⟩ := StageLocalIds.isBystander_unpack hByst
  exact hNe (hInv.2.2.2 j h1 h2 h3 h4)

/-- Fail-closed negative lemma: if `addWithOverflowU w a b` overflows
(`overflowed = true`), no `StageIntervalSpec` of width `w` can certify `a + b`
in-range. -/
theorem not_interval_cert_of_add_overflow (spec : StageIntervalSpec)
    {a b : Nat} (hOvf : (addWithOverflowU spec.width a b).2 = true) :
    spec.inRange (a + b) = false :=
  spec.inRange_false_of_ge_modulus (Nat.le_of_ble_eq_true hOvf)

/-- Fail-closed negative lemma: if `mulWithOverflowU w a b` overflows
(`overflowed = true`), no `StageIntervalSpec` of width `w` can certify `a * b`
in-range. -/
theorem not_interval_cert_of_mul_overflow (spec : StageIntervalSpec)
    {a b : Nat} (hOvf : (mulWithOverflowU spec.width a b).2 = true) :
    spec.inRange (a * b) = false :=
  spec.inRange_false_of_ge_modulus (Nat.le_of_ble_eq_true hOvf)

/-- Tightened false-branch join interval for a checked unsigned addition: when
`addWithOverflowU w a c` takes the `overflowed = false` arm with `a ∈ [lo, hi]`,
the wrapped result is the exact sum, lies in `[lo + c, hi + c]`, and fits the
width. -/
theorem addWithOverflowU_false_interval (w : ScalarWidth) {lo hi a c r : Nat}
    (hLo : lo ≤ a) (hHi : a ≤ hi) (h : addWithOverflowU w a c = (r, false)) :
    r = a + c ∧ lo + c ≤ r ∧ r ≤ hi + c ∧ r < w.modulus := by
  have hNo : (addWithOverflowU w a c).2 = false := congrArg Prod.snd h
  have hLt : a + c < w.modulus := (addWithOverflowU_no_overflow_iff w a c).mp hNo
  rw [addWithOverflowU_of_lt w hLt] at h
  have hR : a + c = r := congrArg Prod.fst h
  subst hR
  exact ⟨rfl, Nat.add_le_add_right hLo c, Nat.add_le_add_right hHi c, hLt⟩

/-- Tightened false-branch join interval for a checked unsigned subtraction:
when `subWithOverflowU w a c` takes the `overflowed = false` arm with
`a ∈ [lo, hi]`, there is no borrow (`c ≤ a`), the wrapped result is the exact
difference, lies in `[lo - c, hi - c]`, and fits the width. -/
theorem subWithOverflowU_false_interval (w : ScalarWidth) {lo hi a c r : Nat}
    (hLo : lo ≤ a) (hHi : a ≤ hi) (h : subWithOverflowU w a c = (r, false)) :
    r = a - c ∧ c ≤ a ∧ lo - c ≤ r ∧ r ≤ hi - c ∧ r < w.modulus := by
  have hNo : (subWithOverflowU w a c).2 = false := congrArg Prod.snd h
  let ⟨hA, _, hLe⟩ := (subWithOverflowU_no_overflow_iff w a c).mp hNo
  rw [subWithOverflowU_of_le w hA hLe] at h
  have hR : a - c = r := congrArg Prod.fst h
  subst hR
  exact ⟨rfl, hLe, Nat.sub_le_sub_right hLo c, Nat.sub_le_sub_right hHi c,
    Nat.lt_of_le_of_lt (Nat.sub_le a c) hA⟩

/-- Tightened false-branch join interval for a checked unsigned multiplication:
when `mulWithOverflowU w a c` takes the `overflowed = false` arm with
`a ∈ [lo, hi]`, the wrapped result is the exact product, lies in
`[lo * c, hi * c]`, and fits the width. -/
theorem mulWithOverflowU_false_interval (w : ScalarWidth) {lo hi a c r : Nat}
    (hLo : lo ≤ a) (hHi : a ≤ hi) (h : mulWithOverflowU w a c = (r, false)) :
    r = a * c ∧ lo * c ≤ r ∧ r ≤ hi * c ∧ r < w.modulus := by
  have hNo : (mulWithOverflowU w a c).2 = false := congrArg Prod.snd h
  have hLt : a * c < w.modulus := (mulWithOverflowU_no_overflow_iff w a c).mp hNo
  rw [mulWithOverflowU_of_lt w hLt] at h
  have hR : a * c = r := congrArg Prod.fst h
  subst hR
  exact ⟨rfl, Nat.mul_le_mul_right c hLo, Nat.mul_le_mul_right c hHi, hLt⟩

/-- Tightened false-branch join interval for a checked unsigned left-shift:
when `shlWithOverflowU w a shift` takes the `overflowed = false` arm with
`a ∈ [lo, hi]` and `hi * pow2 shift < w.modulus`, `shift < w.bits`, the result
is exact `a * pow2 shift`, lies in `[lo * pow2 shift, hi * pow2 shift]`, and
fits the width. -/
theorem shlWithOverflowU_false_interval (w : ScalarWidth)
    {lo hi a shift r : Nat}
    (hLo : lo ≤ a) (hHi : a ≤ hi) (hNoWrap : hi * pow2 shift < w.modulus)
    (h : shlWithOverflowU w a shift = (r, false)) :
    shift < w.bits ∧ r = a * pow2 shift ∧
    lo * pow2 shift ≤ r ∧ r ≤ hi * pow2 shift ∧ r < w.modulus := by
  have hNo : (shlWithOverflowU w a shift).2 = false := congrArg Prod.snd h
  have hShift : shift < w.bits := (shlWithOverflowU_no_overflow_iff w a shift).mp hNo
  have hVal : a * pow2 shift < w.modulus :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right (pow2 shift) hHi) hNoWrap
  rw [shlWithOverflowU_of_lt w hShift hVal] at h
  have hR : a * pow2 shift = r := congrArg Prod.fst h
  subst hR
  exact ⟨hShift, rfl, Nat.mul_le_mul_right (pow2 shift) hLo,
    Nat.mul_le_mul_right (pow2 shift) hHi, hVal⟩

/-- Fail-closed negative lemma: if a state's accumulator slot decodes (through
`fops.asScalar?`) to a value outside `[spec.lo, spec.hi]`, it CANNOT satisfy
`StageIntervalStateInv`. -/
theorem not_stageIntervalStateInv_of_decoded_out_of_range {S : Type u}
    {Val : Type v} {fops : OvfCastFrameOps S Val} (hLaw : fops.Lawful)
    {baseLocals : List Val} {ids : StageLocalIds}
    {spec : StageIntervalSpec} {s : S} {slot : Val} {n : Nat}
    (hGet : listGet? (fops.localsOf s) ids.accId = some slot)
    (hDec : fops.asScalar? spec.width slot = some n)
    (hOut : n < spec.lo ∨ spec.hi < n) :
    ¬ StageIntervalStateInv fops baseLocals ids spec s := by
  intro hInv
  let ⟨acc, hAccGet, hAccLo, hAccHi, hHiMod⟩ := hInv.2.2.1
  have hSlot : fops.mkScalar spec.width acc = slot :=
    Option.some.inj (hAccGet.symm.trans hGet)
  have hSome : fops.asScalar? spec.width (fops.mkScalar spec.width acc) = some acc :=
    hLaw.asScalar?_mkScalar spec.width acc (Nat.lt_of_le_of_lt hAccHi hHiMod)
  rw [hSlot, hDec] at hSome
  have hEq : n = acc := Option.some.inj hSome
  rw [hEq] at hOut
  cases hOut with
  | inl hBelow => exact Nat.not_lt_of_ge hAccLo hBelow
  | inr hAbove => exact Nat.not_lt_of_ge hAccHi hAbove

section OvfCut

variable {S : Type u} {Val : Type v} {Out : Type w} {Fault : Type x}

/-- Underlying unsealed specification of `OvfCastStageCut` (`0` `Prop`
arguments): every state satisfying `StageIntervalStateInv fops baseLocals ids
srcSpec` either reaches `StageIntervalStateInv fops baseLocals ids dstSpec`
within `fuel` steps of `step`, or terminates early with an outcome satisfying
`earlyOk o = true` (e.g., checked-arithmetic overflow early return), with zero
faults. -/
def denoteOvfCastStageCut (fops : OvfCastFrameOps S Val)
    (step : S → StepOutcome S Out Fault) (baseLocals : List Val)
    (ids : StageLocalIds) (earlyOk : Out → Bool)
    (srcSpec dstSpec : StageIntervalSpec) (fuel : Nat) : Prop :=
  ∀ s : S,
    StageIntervalStateInv fops baseLocals ids srcSpec s →
    wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (StageIntervalStateInv fops baseLocals ids dstSpec)
      (fun o => earlyOk o = true)
      (fun _ => False)
      fuel s

/-- Zero-`Prop`-argument Hoare-style stage-cut barrier for checked-arithmetic
diamonds, `intToInt` narrowing/widening casts, and interval-guarded unchecked
arithmetic. All arguments are pure computational data/functions; marked
`@[irreducible]` below after proving its seal, unseal, narrow, widen,
checked-diamond, unchecked, composition, `BlockTree`, `StageCut`, and
`wpOutcome` laws. -/
def OvfCastStageCut (fops : OvfCastFrameOps S Val)
    (step : S → StepOutcome S Out Fault) (baseLocals : List Val)
    (ids : StageLocalIds) (earlyOk : Out → Bool)
    (srcSpec dstSpec : StageIntervalSpec) (fuel : Nat) : Prop :=
  denoteOvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec fuel

/-- Seals a `denoteOvfCastStageCut` proof behind `OvfCastStageCut`. -/
theorem seal_ovfCastStageCut {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : denoteOvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fuel) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec fuel :=
  h

/-- Unseals `OvfCastStageCut` into `denoteOvfCastStageCut`. -/
theorem open_ovfCastStageCut {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : OvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fuel) :
    denoteOvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fuel :=
  h

/-- Reflexive zero-step `OvfCastStageCut`. -/
theorem ovfCastStageCut_refl (fops : OvfCastFrameOps S Val)
    (step : S → StepOutcome S Out Fault) (baseLocals : List Val)
    (ids : StageLocalIds) (earlyOk : Out → Bool)
    (spec : StageIntervalSpec) (fuel : Nat) :
    OvfCastStageCut fops step baseLocals ids earlyOk spec spec fuel :=
  fun _ hInv =>
    wpUntilFuel_here
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st))) hInv

/-- Fuel weakening `f₁ ≤ f₂` for `OvfCastStageCut`. -/
theorem ovfCastStageCut_fuel_mono {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {f₁ f₂ : Nat} (hLe : f₁ ≤ f₂)
    (h : OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec f₁) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec f₂ :=
  fun s hInv =>
    wpUntilFuel_mono
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      hLe (h s hInv)

/-- Pointwise step-function congruence for `OvfCastStageCut` (`0 Quot.sound`). -/
theorem ovfCastStageCut_congr_step {fops : OvfCastFrameOps S Val}
    {step₁ step₂ : S → StepOutcome S Out Fault}
    (hEq : ∀ s : S, step₁ s = step₂ s) {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : OvfCastStageCut fops step₁ baseLocals ids earlyOk
      srcSpec dstSpec fuel) :
    OvfCastStageCut fops step₂ baseLocals ids earlyOk srcSpec dstSpec fuel := by
  intro s hInv
  have hRun := h s hInv
  clear h hInv
  induction fuel generalizing s with
  | zero => exact hRun
  | succ k ih =>
    cases (wpUntilFuel_succ_iff
        (ops := MirWpOps.ofDetStep step₁ (fun st => some (fops.blockOf st)))).mp
        hRun with
    | inl hHere =>
      exact wpUntilFuel_here
        (ops := MirWpOps.ofDetStep step₂ (fun st => some (fops.blockOf st)))
        hHere
    | inr hStep =>
      refine wpUntilFuel_step
        (ops := MirWpOps.ofDetStep step₂ (fun st => some (fops.blockOf st))) ?_
      change (step₂ s).wp _ _ _
      rw [← hEq s]
      exact StepOutcome.wp_mono (fun s' h' => ih s' h') (fun _ ho => ho)
        (fun _ hf => hf) hStep

/-- $O(1)$ sequential composition of `OvfCastStageCut` stages (`f₁ + f₂` fuel),
collapsing $m$ sequential diamonds to $O(m)$ cuts without $2^m$ branching. -/
theorem ovfCastStageCut_compose {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {n₀ n₁ n₂ : StageIntervalSpec} {f₁ f₂ : Nat}
    (h₁ : OvfCastStageCut fops step baseLocals ids earlyOk n₀ n₁ f₁)
    (h₂ : OvfCastStageCut fops step baseLocals ids earlyOk n₁ n₂ f₂) :
    OvfCastStageCut fops step baseLocals ids earlyOk n₀ n₂ (f₁ + f₂) :=
  fun s hInv₀ =>
    wpUntilFuel_bind
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (h₁ s hInv₀) (fun st hInv₁ => h₂ st hInv₁)

/-- Narrowing `intToInt` cast stage cut (`dstW.bits ≤ srcW.bits`): when every
entry state with `acc ∈ [lo, hi]` steps to `dstBb` storing
`intToIntCast srcW srcSigned dstW acc` in `ids.accId` (framing bystanders),
seals the narrowing cast directly into `OvfCastStageCut` preserving `[lo, hi]`
under `hi < dstW.modulus`. -/
theorem ovfCastStageCut_narrow {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcBb dstBb lo hi : Nat} {srcW dstW : ScalarWidth} {srcSigned : Bool}
    (hWf : ids.wf baseLocals.length = true)
    (hBits : dstW.bits ≤ srcW.bits)
    (hHiDst : hi < dstW.modulus)
    (hStep : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids ⟨srcBb, srcW, lo, hi⟩ s →
      listGet? (fops.localsOf s) ids.accId = some (fops.mkScalar srcW acc) →
      lo ≤ acc → acc ≤ hi →
      step s = .step (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (intToIntCast srcW srcSigned dstW acc))))) :
    OvfCastStageCut fops step baseLocals ids earlyOk
      ⟨srcBb, srcW, lo, hi⟩ ⟨dstBb, dstW, lo, hi⟩ 1 := by
  intro s hInv
  let ⟨acc, hAccGet, hLo, hHi, _⟩ := hInv.2.2.1
  have hAccDst : acc < dstW.modulus := Nat.lt_of_le_of_lt hHi hHiDst
  have hCastEq : intToIntCast srcW srcSigned dstW acc = acc :=
    intToIntCast_narrow_exact srcW srcSigned dstW hBits hAccDst
  have hEv := hStep s acc hInv hAccGet hLo hHi
  rw [hCastEq] at hEv
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hEv]
  dsimp only [StepOutcome.wp]
  exact wpUntilFuel_here
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (stageIntervalStateInv_set_acc (spec₂ := ⟨dstBb, dstW, lo, hi⟩)
      hLaw hWf hInv hLo hHi hHiDst)

/-- Unsigned widening `intToInt` cast stage cut (`srcW.bits ≤ dstW.bits`):
preserves `[lo, hi]` across `srcW → dstW`. -/
theorem ovfCastStageCut_widen {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcBb dstBb lo hi : Nat} {srcW dstW : ScalarWidth}
    (hWf : ids.wf baseLocals.length = true)
    (hBits : srcW.bits ≤ dstW.bits)
    (hHiSrc : hi < srcW.modulus)
    (hStep : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids ⟨srcBb, srcW, lo, hi⟩ s →
      listGet? (fops.localsOf s) ids.accId = some (fops.mkScalar srcW acc) →
      lo ≤ acc → acc ≤ hi →
      step s = .step (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (intToIntCast srcW false dstW acc))))) :
    OvfCastStageCut fops step baseLocals ids earlyOk
      ⟨srcBb, srcW, lo, hi⟩ ⟨dstBb, dstW, lo, hi⟩ 1 := by
  intro s hInv
  let ⟨acc, hAccGet, hLo, hHi, _⟩ := hInv.2.2.1
  have hAccSrc : acc < srcW.modulus := Nat.lt_of_le_of_lt hHi hHiSrc
  have hHiDst : hi < dstW.modulus :=
    Nat.lt_of_lt_of_le hHiSrc (pow2_le_pow2 hBits)
  have hCastEq : intToIntCast srcW false dstW acc = acc :=
    intToIntCast_widen_unsigned_exact srcW dstW hBits hAccSrc
  have hEv := hStep s acc hInv hAccGet hLo hHi
  rw [hCastEq] at hEv
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hEv]
  dsimp only [StepOutcome.wp]
  exact wpUntilFuel_here
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (stageIntervalStateInv_set_acc (spec₂ := ⟨dstBb, dstW, lo, hi⟩)
      hLaw hWf hInv hLo hHi hHiDst)

/-- Checked `*WithOverflow` + `SwitchInt` diamond collapse: given any checked
operation `checkedOp : Nat → Nat × Bool`, when `overflowed = false` executes
the normal arm into `dstSpec` (within `armFuel` steps) and `overflowed = true`
executes an early-return/saturate/cleanup arm reaching EITHER `dstSpec` OR an
accepted early exit `earlyOk o = true` (within `armFuel` steps), collapses the
entire diamond into a single `OvfCastStageCut` of budget `1 + armFuel`. -/
theorem ovfCastStageCut_checked_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (checkedOp : Nat → Nat × Bool)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (checkedOp acc).1 (checkedOp acc).2))
    (hNoOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      checkedOp acc = (wrapped, false) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped false))
    (hOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      checkedOp acc = (wrapped, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) := by
  intro s hInv
  let ⟨acc, hAccGet, hLo, hHi, _⟩ := hInv.2.2.1
  have hDisp := hDispatch s acc hInv hAccGet hLo hHi
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hDisp]
  cases hOp : checkedOp acc with
  | mk wrapped ovf =>
    dsimp only
    cases ovf with
    | false => exact hNoOvfArm s acc wrapped hInv hLo hHi hOp
    | true => exact hOvfArm s acc wrapped hInv hLo hHi hOp

/-- Interval-guarded unchecked arithmetic stage cut: discharges safety of any
`uncheckedOp : Nat → Option Nat` (such as `addUncheckedU`, `subUncheckedU`,
`mulUncheckedU`) directly from `[srcSpec.lo, srcSpec.hi]` without branching. -/
theorem ovfCastStageCut_unchecked_of_interval {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec}
    (hWf : ids.wf baseLocals.length = true)
    (hWidthEq : dstSpec.width = srcSpec.width)
    (uncheckedOp : Nat → Option Nat)
    (hSafe : ∀ acc : Nat, srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      ∃ res : Nat, uncheckedOp acc = some res ∧
        dstSpec.lo ≤ res ∧ res ≤ dstSpec.hi ∧ dstSpec.hi < dstSpec.width.modulus)
    (hStep : ∀ (s : S) (acc res : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      uncheckedOp acc = some res →
      step s = .step (fops.withBlockLocals s dstSpec.blockIdx
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar srcSpec.width res)))) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec 1 := by
  intro s hInv
  let ⟨acc, hAccGet, hLo, hHi, _⟩ := hInv.2.2.1
  let ⟨res, hUnchk, hResLo, hResHi, hResMod⟩ := hSafe acc hLo hHi
  have hEv := hStep s acc res hInv hAccGet hUnchk
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hEv, ← hWidthEq]
  dsimp only [StepOutcome.wp]
  exact wpUntilFuel_here
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (stageIntervalStateInv_set_acc (spec₂ := dstSpec)
      hLaw hWf hInv hResLo hResHi hResMod)

/-- Checked unsigned-addition diamond with the join interval facts made
explicit: instantiates `ovfCastStageCut_checked_diamond` at
`addWithOverflowU w · c`, handing the `overflowed = false` arm the exact sum
`acc + c` together with `acc + c < w.modulus`, and the `overflowed = true` arm
the wrapped sum together with `w.modulus ≤ acc + c`. Neither arm has to
re-derive what the overflow flag means. -/
theorem ovfCastStageCut_checked_add_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (addWithOverflowU w acc c).1
        (addWithOverflowU w acc c).2))
    (hNoOvfArm : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      acc + c < w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s (acc + c) false))
    (hOvfArm : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      w.modulus ≤ acc + c →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s ((acc + c) % w.modulus) true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond (fun acc => addWithOverflowU w acc c)
    branchState hDispatch
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hI := addWithOverflowU_false_interval w hLo hHi hOp
      have hLt : acc + c < w.modulus :=
        (addWithOverflowU_no_overflow_iff w acc c).mp (congrArg Prod.snd hOp)
      rw [hI.1]
      exact hNoOvfArm s acc hInv hLo hHi hLt)
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hFlag : (addWithOverflowU w acc c).2 = true := congrArg Prod.snd hOp
      have hGe : w.modulus ≤ acc + c := Nat.le_of_ble_eq_true hFlag
      have hW : (acc + c) % w.modulus = wrapped := congrArg Prod.fst hOp
      rw [← hW]
      exact hOvfArm s acc hInv hLo hHi hGe)

/-- Checked unsigned-subtraction diamond with explicit join facts: hands the
`overflowed = false` arm `acc < w.modulus ∧ c < w.modulus ∧ c ≤ acc` with exact
difference `acc - c`, and the `overflowed = true` arm the wrapped bits with
`acc < c ∨ w.modulus ≤ acc ∨ w.modulus ≤ c`. -/
theorem ovfCastStageCut_checked_sub_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (subWithOverflowU w acc c).1
        (subWithOverflowU w acc c).2))
    (hNoOvfArm : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      acc < w.modulus → c < w.modulus → c ≤ acc →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s (acc - c) false))
    (hOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      (acc < c ∨ w.modulus ≤ acc ∨ w.modulus ≤ c) →
      subWithOverflowU w acc c = (wrapped, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond (fun acc => subWithOverflowU w acc c)
    branchState hDispatch
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hNo : (subWithOverflowU w acc c).2 = false := congrArg Prod.snd hOp
      let ⟨hA, hC, hLe⟩ := (subWithOverflowU_no_overflow_iff w acc c).mp hNo
      rw [subWithOverflowU_of_le w hA hLe] at hOp
      have hW : acc - c = wrapped := congrArg Prod.fst hOp
      rw [← hW]
      exact hNoOvfArm s acc hInv hLo hHi hA hC hLe)
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hFlag : (subWithOverflowU w acc c).2 = true := congrArg Prod.snd hOp
      have hBad : acc < c ∨ w.modulus ≤ acc ∨ w.modulus ≤ c := by
        cases Nat.lt_or_ge acc c with
        | inl hLt => exact Or.inl hLt
        | inr hGe =>
          cases Nat.lt_or_ge acc w.modulus with
          | inr hGeA => exact Or.inr (Or.inl hGeA)
          | inl hLtA =>
            cases Nat.lt_or_ge c w.modulus with
            | inr hGeC => exact Or.inr (Or.inr hGeC)
            | inl hLtC =>
              rw [(subWithOverflowU_no_overflow_iff w acc c).mpr ⟨hLtA, hLtC, hGe⟩]
                at hFlag
              cases hFlag
      exact hOvfArm s acc wrapped hInv hLo hHi hBad hOp)

/-- Checked unsigned-multiplication diamond with explicit join facts: hands the
`overflowed = false` arm exact product `acc * c` with `acc * c < w.modulus`,
and the `overflowed = true` arm `(acc * c) % w.modulus` with
`w.modulus ≤ acc * c`. -/
theorem ovfCastStageCut_checked_mul_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (mulWithOverflowU w acc c).1
        (mulWithOverflowU w acc c).2))
    (hNoOvfArm : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      acc * c < w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s (acc * c) false))
    (hOvfArm : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      w.modulus ≤ acc * c →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s ((acc * c) % w.modulus) true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond (fun acc => mulWithOverflowU w acc c)
    branchState hDispatch
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hI := mulWithOverflowU_false_interval w hLo hHi hOp
      have hLt : acc * c < w.modulus :=
        (mulWithOverflowU_no_overflow_iff w acc c).mp (congrArg Prod.snd hOp)
      rw [hI.1]
      exact hNoOvfArm s acc hInv hLo hHi hLt)
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hFlag : (mulWithOverflowU w acc c).2 = true := congrArg Prod.snd hOp
      have hGe : w.modulus ≤ acc * c := Nat.le_of_ble_eq_true hFlag
      have hW : (acc * c) % w.modulus = wrapped := congrArg Prod.fst hOp
      rw [← hW]
      exact hOvfArm s acc hInv hLo hHi hGe)

/-- Checked unsigned left-shift diamond with explicit join facts: hands the
`overflowed = false` arm `shift < w.bits` with `(acc * pow2 shift) % w.modulus`,
and the `overflowed = true` arm `w.bits ≤ shift`. -/
theorem ovfCastStageCut_checked_shl_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (shift : Nat)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (shlWithOverflowU w acc shift).1
        (shlWithOverflowU w acc shift).2))
    (hNoOvfArm : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      shift < w.bits →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s ((acc * pow2 shift) % w.modulus) false))
    (hOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      w.bits ≤ shift →
      shlWithOverflowU w acc shift = (wrapped, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond (fun acc => shlWithOverflowU w acc shift)
    branchState hDispatch
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hNo : (shlWithOverflowU w acc shift).2 = false := congrArg Prod.snd hOp
      have hLt : shift < w.bits := (shlWithOverflowU_no_overflow_iff w acc shift).mp hNo
      have hVal : (acc * pow2 shift) % w.modulus = wrapped := by
        have hFst := congrArg Prod.fst hOp
        unfold shlWithOverflowU at hFst
        dsimp only at hFst
        rw [Nat.mod_eq_of_lt hLt] at hFst
        exact hFst
      rw [← hVal]
      exact hNoOvfArm s acc hInv hLo hHi hLt)
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hFlag : (shlWithOverflowU w acc shift).2 = true := congrArg Prod.snd hOp
      have hGe : w.bits ≤ shift := Nat.le_of_ble_eq_true hFlag
      exact hOvfArm s acc wrapped hInv hLo hHi hGe hOp)

/-- Checked signed addition diamond (`addWithOverflowS`) with explicit biased
join facts: hands the `overflowed = false` arm exact non-overflow bounds on
`toBiased w acc + toBiased w c` and `toBiased w wrapped = toBiased w acc +
toBiased w c - w.halfModulus`, and the `overflowed = true` arm the overflow
certificate. -/
theorem ovfCastStageCut_checked_add_signed_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (addWithOverflowS w acc c).1
        (addWithOverflowS w acc c).2))
    (hNoOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      acc < w.modulus → c < w.modulus →
      w.halfModulus ≤ toBiased w acc + toBiased w c →
      toBiased w acc + toBiased w c < w.modulus + w.halfModulus →
      toBiased w wrapped = toBiased w acc + toBiased w c - w.halfModulus →
      wrapped = (acc + c) % w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped false))
    (hOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      addWithOverflowS w acc c = (wrapped, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond (fun acc => addWithOverflowS w acc c)
    branchState hDispatch
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hNo : (addWithOverflowS w acc c).2 = false := congrArg Prod.snd hOp
      have hW : (addWithOverflowS w acc c).1 = wrapped := congrArg Prod.fst hOp
      let ⟨ha, hc, hBiLo, hBiHi⟩ := (addWithOverflowS_no_overflow_iff w acc c).mp hNo
      have hBiEq : toBiased w wrapped =
          toBiased w acc + toBiased w c - w.halfModulus := by
        rw [← hW]
        exact toBiased_addWithOverflowS_of_no_overflow w hNo
      have hWrEq : wrapped = (acc + c) % w.modulus := by
        rw [← hW]
        unfold addWithOverflowS
        dsimp only
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]
      exact hNoOvfArm s acc wrapped hInv hLo hHi ha hc hBiLo hBiHi hBiEq hWrEq)
    (fun s acc wrapped hInv hLo hHi hOp =>
      hOvfArm s acc wrapped hInv hLo hHi hOp)

/-- Checked signed subtraction diamond (`subWithOverflowS`) with explicit biased
join facts. -/
theorem ovfCastStageCut_checked_sub_signed_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (subWithOverflowS w acc c).1
        (subWithOverflowS w acc c).2))
    (hNoOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      acc < w.modulus → c < w.modulus →
      toBiased w c ≤ toBiased w acc + w.halfModulus →
      toBiased w acc + w.halfModulus < toBiased w c + w.modulus →
      toBiased w wrapped = toBiased w acc + w.halfModulus - toBiased w c →
      wrapped = (acc + w.modulus - c) % w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped false))
    (hOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      subWithOverflowS w acc c = (wrapped, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond (fun acc => subWithOverflowS w acc c)
    branchState hDispatch
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hNo : (subWithOverflowS w acc c).2 = false := congrArg Prod.snd hOp
      have hW : (subWithOverflowS w acc c).1 = wrapped := congrArg Prod.fst hOp
      let ⟨ha, hc, hBiLo, hBiHi⟩ := (subWithOverflowS_no_overflow_iff w acc c).mp hNo
      have hBiEq : toBiased w wrapped =
          toBiased w acc + w.halfModulus - toBiased w c := by
        rw [← hW]
        exact toBiased_subWithOverflowS_of_no_overflow w hNo
      have hWrEq : wrapped = (acc + w.modulus - c) % w.modulus := by
        rw [← hW]
        unfold subWithOverflowS
        dsimp only
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]
      exact hNoOvfArm s acc wrapped hInv hLo hHi ha hc hBiLo hBiHi hBiEq hWrEq)
    (fun s acc wrapped hInv hLo hHi hOp =>
      hOvfArm s acc wrapped hInv hLo hHi hOp)

/-- Checked signed multiplication diamond (`mulWithOverflowS`) with explicit
signed-magnitude join facts. -/
theorem ovfCastStageCut_checked_mul_signed_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (mulWithOverflowS w acc c).1
        (mulWithOverflowS w acc c).2))
    (hNoOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      acc < w.modulus → c < w.modulus →
      (mulWithOverflowS w acc c).2 = false →
      wrapped = (acc * c) % w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped false))
    (hOvfArm : ∀ (s : S) (acc wrapped : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      mulWithOverflowS w acc c = (wrapped, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s wrapped true)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond (fun acc => mulWithOverflowS w acc c)
    branchState hDispatch
    (fun s acc wrapped hInv hLo hHi hOp => by
      have hNo : (mulWithOverflowS w acc c).2 = false := congrArg Prod.snd hOp
      have hW : (mulWithOverflowS w acc c).1 = wrapped := congrArg Prod.fst hOp
      let ⟨ha, hc, _⟩ := (mulWithOverflowS_no_overflow_iff w acc c).mp hNo
      have hWrEq : wrapped = (acc * c) % w.modulus := by
        rw [← hW]
        unfold mulWithOverflowS
        dsimp only
        rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hc]
      exact hNoOvfArm s acc wrapped hInv hLo hHi ha hc hNo hWrEq)
    (fun s acc wrapped hInv hLo hHi hOp =>
      hOvfArm s acc wrapped hInv hLo hHi hOp)

/-- Signed checked-addition diamond with a SIGNED interval cutpoint (via
`OvfCastFrameOps.signedView`): the accumulator is tracked in biased
coordinates, so `srcSpec = [lo, hi]` may be any signed interval (including one
that crosses zero). The `overflowed = false` arm receives the result `r`
together with its exact biased coordinate
`toBiased w r + halfModulus = acc + toBiased w c`, which places it in the
tightened signed join interval
`[lo + toBiased w c - halfModulus, hi + toBiased w c - halfModulus]`. -/
theorem ovfCastStageCut_checked_add_signed_interval
    {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat) (hW : srcSpec.width = w)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.signedView.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (addWithOverflowS w (toBiased w acc) c).1
        (addWithOverflowS w (toBiased w acc) c).2))
    (hNoOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      toBiased w r + w.halfModulus = acc + toBiased w c →
      srcSpec.lo + toBiased w c ≤ toBiased w r + w.halfModulus →
      toBiased w r + w.halfModulus ≤ srcSpec.hi + toBiased w c →
      r < w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r false))
    (hOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      addWithOverflowS w (toBiased w acc) c = (r, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r true)) :
    OvfCastStageCut fops.signedView step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond
    (fun acc => addWithOverflowS w (toBiased w acc) c)
    branchState hDispatch
    (fun s acc r hInv hLo hHi hOp => by
      have hAccLt : acc < w.modulus := by
        rw [← hW]
        let ⟨_, _, _, _, hHiMod⟩ := hInv.2.2.1
        exact Nat.lt_of_le_of_lt hHi hHiMod
      let ⟨hEq, hILo, hIHi, hRlt⟩ :=
        addWithOverflowS_biased_false_interval w hAccLt hLo hHi hOp
      exact hNoOvfArm s acc r hInv hLo hHi hEq hILo hIHi hRlt)
    (fun s acc r hInv hLo hHi hOp => hOvfArm s acc r hInv hLo hHi hOp)

/-- Signed checked-subtraction diamond with a SIGNED interval cutpoint over
`fops.signedView` (cross-zero capable). -/
theorem ovfCastStageCut_checked_sub_signed_interval
    {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat) (hW : srcSpec.width = w)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.signedView.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (subWithOverflowS w (toBiased w acc) c).1
        (subWithOverflowS w (toBiased w acc) c).2))
    (hNoOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      toBiased w r + toBiased w c = acc + w.halfModulus →
      srcSpec.lo + w.halfModulus ≤ toBiased w r + toBiased w c →
      toBiased w r + toBiased w c ≤ srcSpec.hi + w.halfModulus →
      r < w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r false))
    (hOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      subWithOverflowS w (toBiased w acc) c = (r, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r true)) :
    OvfCastStageCut fops.signedView step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond
    (fun acc => subWithOverflowS w (toBiased w acc) c)
    branchState hDispatch
    (fun s acc r hInv hLo hHi hOp => by
      have hAccLt : acc < w.modulus := by
        rw [← hW]
        let ⟨_, _, _, _, hHiMod⟩ := hInv.2.2.1
        exact Nat.lt_of_le_of_lt hHi hHiMod
      let ⟨hEq, hILo, hIHi, hRlt⟩ :=
        subWithOverflowS_biased_false_interval w hAccLt hLo hHi hOp
      exact hNoOvfArm s acc r hInv hLo hHi hEq hILo hIHi hRlt)
    (fun s acc r hInv hLo hHi hOp => hOvfArm s acc r hInv hLo hHi hOp)

/-- Signed checked-multiplication diamond (non-negative multiplier
`c < w.halfModulus`) with a SIGNED interval cutpoint over `fops.signedView`
(cross-zero capable). -/
theorem ovfCastStageCut_checked_mul_signed_interval_nonneg
    {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat) (hW : srcSpec.width = w)
    (hc : c < w.halfModulus)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.signedView.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (mulWithOverflowS w (toBiased w acc) c).1
        (mulWithOverflowS w (toBiased w acc) c).2))
    (hNoOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      toBiased w r + w.halfModulus * c = acc * c + w.halfModulus →
      srcSpec.lo * c + w.halfModulus ≤ toBiased w r + w.halfModulus * c →
      toBiased w r + w.halfModulus * c ≤ srcSpec.hi * c + w.halfModulus →
      r < w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r false))
    (hOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      mulWithOverflowS w (toBiased w acc) c = (r, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r true)) :
    OvfCastStageCut fops.signedView step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond
    (fun acc => mulWithOverflowS w (toBiased w acc) c)
    branchState hDispatch
    (fun s acc r hInv hLo hHi hOp => by
      have hAccLt : acc < w.modulus := by
        rw [← hW]
        let ⟨_, _, _, _, hHiMod⟩ := hInv.2.2.1
        exact Nat.lt_of_le_of_lt hHi hHiMod
      let ⟨hEq, hILo, hIHi, hRlt⟩ :=
        mulWithOverflowS_biased_false_interval_nonneg w hAccLt hc hLo hHi hOp
      exact hNoOvfArm s acc r hInv hLo hHi hEq hILo hIHi hRlt)
    (fun s acc r hInv hLo hHi hOp => hOvfArm s acc r hInv hLo hHi hOp)

/-- Signed checked-multiplication diamond (negative multiplier
`w.halfModulus ≤ c < w.modulus`) with a SIGNED interval cutpoint over
`fops.signedView` (cross-zero capable, reversing `[lo, hi]`). -/
theorem ovfCastStageCut_checked_mul_signed_interval_neg
    {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (w : ScalarWidth) (c : Nat) (hW : srcSpec.width = w)
    (hCNeg : w.halfModulus ≤ c) (hcM : c < w.modulus)
    (branchState : S → Nat → Bool → S)
    (hDispatch : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.signedView.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (branchState s (mulWithOverflowS w (toBiased w acc) c).1
        (mulWithOverflowS w (toBiased w acc) c).2))
    (hNoOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      toBiased w r + acc * (w.modulus - c) =
        w.halfModulus * (w.modulus - c) + w.halfModulus →
      toBiased w r + srcSpec.lo * (w.modulus - c) ≤
        w.halfModulus * (w.modulus - c) + w.halfModulus →
      w.halfModulus * (w.modulus - c) + w.halfModulus ≤
        toBiased w r + srcSpec.hi * (w.modulus - c) →
      r < w.modulus →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r false))
    (hOvfArm : ∀ (s : S) (acc r : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids srcSpec s →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      mulWithOverflowS w (toBiased w acc) c = (r, true) →
      wpUntilFuel (ops := MirWpOps.ofDetStep step
          (fun st => some (fops.signedView.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False)
        armFuel (branchState s r true)) :
    OvfCastStageCut fops.signedView step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) :=
  ovfCastStageCut_checked_diamond
    (fun acc => mulWithOverflowS w (toBiased w acc) c)
    branchState hDispatch
    (fun s acc r hInv hLo hHi hOp => by
      have hAccLt : acc < w.modulus := by
        rw [← hW]
        let ⟨_, _, _, _, hHiMod⟩ := hInv.2.2.1
        exact Nat.lt_of_le_of_lt hHi hHiMod
      let ⟨hEq, hILo, hIHi, hRlt⟩ :=
        mulWithOverflowS_biased_false_interval_neg w hAccLt hCNeg hcM hLo hHi hOp
      exact hNoOvfArm s acc r hInv hLo hHi hEq hILo hIHi hRlt)
    (fun s acc r hInv hLo hHi hOp => hOvfArm s acc r hInv hLo hHi hOp)

/-- Cross-zero signed widening stage cut over `fops.signedView`: widens any
signed interval `[lo, hi]` (negative, zero-crossing, or positive) from `srcW`
to `dstW` (`srcW.bits ≤ dstW.bits`), shifting biased bounds by
`dstW.halfModulus - srcW.halfModulus`. -/
theorem ovfCastStageCut_widen_signed_interval {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcBb dstBb : Nat} {srcW dstW : ScalarWidth} {lo hi : Nat}
    (hWf : ids.wf baseLocals.length = true)
    (hLe : srcW.bits ≤ dstW.bits)
    (hHi : hi < srcW.modulus)
    (hStep : ∀ (s : S) (accB : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids ⟨srcBb, srcW, lo, hi⟩ s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcW (toBiased srcW accB)) →
      lo ≤ accB → accB ≤ hi →
      step s = .step (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (intToIntCast srcW true dstW (toBiased srcW accB)))))) :
    OvfCastStageCut fops.signedView step baseLocals ids earlyOk
      ⟨srcBb, srcW, lo, hi⟩
      ⟨dstBb, dstW, lo + (dstW.halfModulus - srcW.halfModulus),
        hi + (dstW.halfModulus - srcW.halfModulus)⟩ 1 := by
  have hHLe : srcW.halfModulus ≤ dstW.halfModulus := by
    unfold ScalarWidth.halfModulus
    exact pow2_le_pow2 (Nat.sub_le_sub_right hLe 1)
  have hSMod : srcW.modulus = srcW.halfModulus + srcW.halfModulus := by
    rw [srcW.modulus_eq_two_mul_half, Nat.two_mul]
  have hDMod : dstW.modulus = dstW.halfModulus + dstW.halfModulus := by
    rw [dstW.modulus_eq_two_mul_half, Nat.two_mul]
  have hDstHi : hi + (dstW.halfModulus - srcW.halfModulus) < dstW.modulus := by
    have h1 : hi + (dstW.halfModulus - srcW.halfModulus) <
        srcW.modulus + (dstW.halfModulus - srcW.halfModulus) :=
      Nat.add_lt_add_right hHi _
    have h2 : srcW.modulus + (dstW.halfModulus - srcW.halfModulus) ≤ dstW.modulus := by
      rw [hSMod, hDMod, Nat.add_assoc, Nat.add_sub_of_le hHLe]
      exact Nat.add_le_add_right hHLe _
    exact Nat.lt_of_lt_of_le h1 h2
  refine seal_ovfCastStageCut (fun s hInv => ?_)
  let ⟨accB, hAccGet, hAccLo, hAccHi, _⟩ := hInv.2.2.1
  have hAccLt : accB < srcW.modulus := Nat.lt_of_le_of_lt hAccHi hHi
  have hSt := hStep s accB hInv hAccGet hAccLo hAccHi
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.signedView.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hSt]
  dsimp only [StepOutcome.wp]
  refine wpUntilFuel_here
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.signedView.blockOf st))) ?_
  have hCastBi :
      toBiased dstW (intToIntCast srcW true dstW (toBiased srcW accB)) =
        accB + (dstW.halfModulus - srcW.halfModulus) :=
    toBiased_intToIntCast_widen_signed srcW dstW hLe hAccLt
  have hInvDst :
      toBiased dstW (accB + (dstW.halfModulus - srcW.halfModulus)) =
        intToIntCast srcW true dstW (toBiased srcW accB) := by
    rw [← hCastBi, toBiased_involutive,
      Nat.mod_eq_of_lt (intToIntCast_lt_modulus srcW true dstW _)]
  have hGoal :=
    stageIntervalStateInv_set_acc (fops := fops.signedView)
      (OvfCastFrameOps.signedView_lawful hLaw) hWf
      (spec₂ := ⟨dstBb, dstW, lo + (dstW.halfModulus - srcW.halfModulus),
        hi + (dstW.halfModulus - srcW.halfModulus)⟩)
      hInv (Nat.add_le_add_right hAccLo _) (Nat.add_le_add_right hAccHi _) hDstHi
  change StageIntervalStateInv fops.signedView baseLocals ids _
      (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (toBiased dstW (accB + (dstW.halfModulus - srcW.halfModulus))))))
    at hGoal
  rw [hInvDst] at hGoal
  exact hGoal

/-- Cross-zero signed narrowing stage cut over `fops.signedView`: narrows any
signed interval `[lo, hi]` fitting in `dstW` (`srcW.halfModulus -
dstW.halfModulus ≤ lo` and `hi < srcW.halfModulus + dstW.halfModulus`) from
`srcW` to `dstW` (`dstW.bits ≤ srcW.bits`), shifting biased bounds by
`-(srcW.halfModulus - dstW.halfModulus)`. -/
theorem ovfCastStageCut_narrow_signed_interval {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcBb dstBb : Nat} {srcW dstW : ScalarWidth} (srcSigned : Bool)
    {lo hi : Nat}
    (hWf : ids.wf baseLocals.length = true)
    (hLe : dstW.bits ≤ srcW.bits)
    (hLoFit : srcW.halfModulus - dstW.halfModulus ≤ lo)
    (hHiFit : hi < srcW.halfModulus + dstW.halfModulus)
    (hStep : ∀ (s : S) (accB : Nat),
      StageIntervalStateInv fops.signedView baseLocals ids ⟨srcBb, srcW, lo, hi⟩ s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcW (toBiased srcW accB)) →
      lo ≤ accB → accB ≤ hi →
      step s = .step (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (intToIntCast srcW srcSigned dstW (toBiased srcW accB)))))) :
    OvfCastStageCut fops.signedView step baseLocals ids earlyOk
      ⟨srcBb, srcW, lo, hi⟩
      ⟨dstBb, dstW, lo - (srcW.halfModulus - dstW.halfModulus),
        hi - (srcW.halfModulus - dstW.halfModulus)⟩ 1 := by
  have hHLe : dstW.halfModulus ≤ srcW.halfModulus := by
    unfold ScalarWidth.halfModulus
    exact pow2_le_pow2 (Nat.sub_le_sub_right hLe 1)
  have hDMod : dstW.modulus = dstW.halfModulus + dstW.halfModulus := by
    rw [dstW.modulus_eq_two_mul_half, Nat.two_mul]
  have hDstHi : hi - (srcW.halfModulus - dstW.halfModulus) < dstW.modulus := by
    cases Nat.lt_or_ge hi (srcW.halfModulus - dstW.halfModulus) with
    | inl hSmall =>
      rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hSmall)]
      exact dstW.modulus_pos
    | inr hBig =>
      have h1 : (hi - (srcW.halfModulus - dstW.halfModulus)) +
          (srcW.halfModulus - dstW.halfModulus) <
          dstW.modulus + (srcW.halfModulus - dstW.halfModulus) := by
        rw [Nat.sub_add_cancel hBig, hDMod, Nat.add_assoc,
          Nat.add_sub_of_le hHLe, Nat.add_comm]
        exact hHiFit
      cases Nat.lt_or_ge (hi - (srcW.halfModulus - dstW.halfModulus)) dstW.modulus with
      | inl hLt => exact hLt
      | inr hGe => exact absurd h1 (Nat.not_lt_of_ge (Nat.add_le_add_right hGe _))
  refine seal_ovfCastStageCut (fun s hInv => ?_)
  let ⟨accB, hAccGet, hAccLo, hAccHi, _⟩ := hInv.2.2.1
  have hAccLoFit : srcW.halfModulus - dstW.halfModulus ≤ accB :=
    Nat.le_trans hLoFit hAccLo
  have hAccHiFit : accB < srcW.halfModulus + dstW.halfModulus :=
    Nat.lt_of_le_of_lt hAccHi hHiFit
  have hSt := hStep s accB hInv hAccGet hAccLo hAccHi
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.signedView.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hSt]
  dsimp only [StepOutcome.wp]
  refine wpUntilFuel_here
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.signedView.blockOf st))) ?_
  have hCastBi :
      toBiased dstW (intToIntCast srcW srcSigned dstW (toBiased srcW accB)) =
        accB - (srcW.halfModulus - dstW.halfModulus) :=
    toBiased_intToIntCast_narrow_signed srcW srcSigned dstW hLe hAccLoFit hAccHiFit
  have hInvDst :
      toBiased dstW (accB - (srcW.halfModulus - dstW.halfModulus)) =
        intToIntCast srcW srcSigned dstW (toBiased srcW accB) := by
    rw [← hCastBi, toBiased_involutive,
      Nat.mod_eq_of_lt (intToIntCast_lt_modulus srcW srcSigned dstW _)]
  have hGoal :=
    stageIntervalStateInv_set_acc (fops := fops.signedView)
      (OvfCastFrameOps.signedView_lawful hLaw) hWf
      (spec₂ := ⟨dstBb, dstW, lo - (srcW.halfModulus - dstW.halfModulus),
        hi - (srcW.halfModulus - dstW.halfModulus)⟩)
      hInv (Nat.sub_le_sub_right hAccLo _) (Nat.sub_le_sub_right hAccHi _) hDstHi
  change StageIntervalStateInv fops.signedView baseLocals ids _
      (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (toBiased dstW (accB - (srcW.halfModulus - dstW.halfModulus))))))
    at hGoal
  rw [hInvDst] at hGoal
  exact hGoal

/-- Generic single-step cast/transfer stage cut: when every entry state with
`acc ∈ [srcSpec.lo, srcSpec.hi]` steps to `dstSpec.blockIdx` storing
`castFn acc` (at `dstSpec.width`) in `ids.accId`, and `castFn` maps the source
interval into `[dstSpec.lo, dstSpec.hi]`, seals the step into
`OvfCastStageCut`. Signed widening casts move the interval (negative values
gain sign-extension bits), which the identity-interval `ovfCastStageCut_narrow`
and `ovfCastStageCut_widen` rules cannot express. -/
theorem ovfCastStageCut_cast_of_interval {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec}
    (hWf : ids.wf baseLocals.length = true)
    (castFn : Nat → Nat)
    (hRange : ∀ acc : Nat, srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      dstSpec.lo ≤ castFn acc ∧ castFn acc ≤ dstSpec.hi)
    (hDstMod : dstSpec.hi < dstSpec.width.modulus)
    (hStep : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      listGet? (fops.localsOf s) ids.accId =
        some (fops.mkScalar srcSpec.width acc) →
      srcSpec.lo ≤ acc → acc ≤ srcSpec.hi →
      step s = .step (fops.withBlockLocals s dstSpec.blockIdx
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstSpec.width (castFn acc))))) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec 1 := by
  intro s hInv
  let ⟨acc, hAccGet, hLo, hHi, _⟩ := hInv.2.2.1
  have hR := hRange acc hLo hHi
  have hEv := hStep s acc hInv hAccGet hLo hHi
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hEv]
  dsimp only [StepOutcome.wp]
  exact wpUntilFuel_here
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (stageIntervalStateInv_set_acc (spec₂ := dstSpec)
      hLaw hWf hInv hR.1 hR.2 hDstMod)

/-- Signed widening `intToInt` cast stage cut on a non-negative interval
(`hi < srcW.halfModulus`): sign-extension is the identity, so `[lo, hi]` is
preserved across `srcW → dstW`. -/
theorem ovfCastStageCut_widen_signed_nonneg {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcBb dstBb lo hi : Nat} {srcW dstW : ScalarWidth}
    (hWf : ids.wf baseLocals.length = true)
    (hBits : srcW.bits < dstW.bits)
    (hHiSrc : hi < srcW.halfModulus)
    (hStep : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids ⟨srcBb, srcW, lo, hi⟩ s →
      listGet? (fops.localsOf s) ids.accId = some (fops.mkScalar srcW acc) →
      lo ≤ acc → acc ≤ hi →
      step s = .step (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (intToIntCast srcW true dstW acc))))) :
    OvfCastStageCut fops step baseLocals ids earlyOk
      ⟨srcBb, srcW, lo, hi⟩ ⟨dstBb, dstW, lo, hi⟩ 1 :=
  ovfCastStageCut_cast_of_interval
    (srcSpec := ⟨srcBb, srcW, lo, hi⟩) (dstSpec := ⟨dstBb, dstW, lo, hi⟩)
    hLaw hWf (intToIntCast srcW true dstW)
    (fun acc hLo hHi => by
      rw [intToIntCast_widen_signed_nonneg srcW dstW hBits
        (Nat.lt_of_le_of_lt hHi hHiSrc)]
      exact ⟨hLo, hHi⟩)
    (Nat.lt_of_lt_of_le
      (Nat.lt_trans hHiSrc srcW.halfModulus_lt_modulus)
      (pow2_le_pow2 (Nat.le_of_lt hBits)))
    hStep

/-- Signed widening `intToInt` cast stage cut on a negative interval
(`srcW.halfModulus ≤ lo` and `hi < srcW.modulus`): two's-complement
sign-extension shifts `[lo, hi]` up by `dstW.modulus - srcW.modulus`. -/
theorem ovfCastStageCut_widen_signed_neg {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcBb dstBb lo hi : Nat} {srcW dstW : ScalarWidth}
    (hWf : ids.wf baseLocals.length = true)
    (hBits : srcW.bits < dstW.bits)
    (hLoNeg : srcW.halfModulus ≤ lo)
    (hHiSrc : hi < srcW.modulus)
    (hStep : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids ⟨srcBb, srcW, lo, hi⟩ s →
      listGet? (fops.localsOf s) ids.accId = some (fops.mkScalar srcW acc) →
      lo ≤ acc → acc ≤ hi →
      step s = .step (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (intToIntCast srcW true dstW acc))))) :
    OvfCastStageCut fops step baseLocals ids earlyOk
      ⟨srcBb, srcW, lo, hi⟩
      ⟨dstBb, dstW, (dstW.modulus - srcW.modulus) + lo,
        (dstW.modulus - srcW.modulus) + hi⟩ 1 :=
  ovfCastStageCut_cast_of_interval
    (srcSpec := ⟨srcBb, srcW, lo, hi⟩)
    (dstSpec := ⟨dstBb, dstW, (dstW.modulus - srcW.modulus) + lo,
      (dstW.modulus - srcW.modulus) + hi⟩)
    hLaw hWf (intToIntCast srcW true dstW)
    (fun acc hLo hHi => by
      rw [(intToIntCast_widen_signed_neg srcW dstW hBits
        (Nat.le_trans hLoNeg hLo) (Nat.lt_of_le_of_lt hHi hHiSrc)).1]
      exact ⟨Nat.add_le_add_left hLo _, Nat.add_le_add_left hHi _⟩)
    (by
      have hAdd := Nat.add_lt_add_left hHiSrc (dstW.modulus - srcW.modulus)
      have hModLe : srcW.modulus ≤ dstW.modulus :=
        pow2_le_pow2 (Nat.le_of_lt hBits)
      rw [Nat.sub_add_cancel hModLe] at hAdd
      exact hAdd)
    hStep

/-- Signed narrowing `intToInt` cast stage cut on an in-range negative interval
(`dstW.bits ≤ srcW.bits`, `srcW.modulus - dstW.halfModulus ≤ lo`, and
`hi < srcW.modulus`): drops the `srcW.modulus - dstW.modulus` sign-extension
bits, shifting `[lo, hi]` down to
`[lo - (srcW.modulus - dstW.modulus), hi - (srcW.modulus - dstW.modulus)]`. -/
theorem ovfCastStageCut_narrow_signed_neg {fops : OvfCastFrameOps S Val}
    (hLaw : fops.Lawful) {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcBb dstBb lo hi : Nat} {srcW dstW : ScalarWidth} {srcSigned : Bool}
    (hWf : ids.wf baseLocals.length = true)
    (hBits : dstW.bits ≤ srcW.bits)
    (hLoNeg : srcW.modulus - dstW.halfModulus ≤ lo)
    (hHiSrc : hi < srcW.modulus)
    (hStep : ∀ (s : S) (acc : Nat),
      StageIntervalStateInv fops baseLocals ids ⟨srcBb, srcW, lo, hi⟩ s →
      listGet? (fops.localsOf s) ids.accId = some (fops.mkScalar srcW acc) →
      lo ≤ acc → acc ≤ hi →
      step s = .step (fops.withBlockLocals s dstBb
        (listSetAt (fops.localsOf s) ids.accId
          (fops.mkScalar dstW (intToIntCast srcW srcSigned dstW acc))))) :
    OvfCastStageCut fops step baseLocals ids earlyOk
      ⟨srcBb, srcW, lo, hi⟩
      ⟨dstBb, dstW, lo - (srcW.modulus - dstW.modulus),
        hi - (srcW.modulus - dstW.modulus)⟩ 1 :=
  ovfCastStageCut_cast_of_interval
    (srcSpec := ⟨srcBb, srcW, lo, hi⟩)
    (dstSpec := ⟨dstBb, dstW, lo - (srcW.modulus - dstW.modulus),
      hi - (srcW.modulus - dstW.modulus)⟩)
    hLaw hWf (intToIntCast srcW srcSigned dstW)
    (fun acc hLo hHi => by
      have hN := intToIntCast_narrow_signed_neg srcW srcSigned dstW hBits
        (Nat.le_trans hLoNeg hLo) (Nat.lt_of_le_of_lt hHi hHiSrc)
      have hEq : intToIntCast srcW srcSigned dstW acc =
          acc - (srcW.modulus - dstW.modulus) := by
        have hSub := congrArg (fun k => k - (srcW.modulus - dstW.modulus)) hN.1
        rw [Nat.add_sub_cancel_left] at hSub
        exact hSub
      rw [hEq]
      exact ⟨Nat.sub_le_sub_right hLo _, Nat.sub_le_sub_right hHi _⟩)
    (by
      have hDS : dstW.modulus ≤ srcW.modulus := pow2_le_pow2 hBits
      cases Nat.lt_or_ge hi (srcW.modulus - dstW.modulus) with
      | inl hSm =>
        rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hSm)]
        exact dstW.modulus_pos
      | inr hGe =>
        have hAdd :
            (srcW.modulus - dstW.modulus) + (hi - (srcW.modulus - dstW.modulus)) <
              (srcW.modulus - dstW.modulus) + dstW.modulus := by
          rw [Nat.add_sub_of_le hGe, Nat.sub_add_cancel hDS]
          exact hHiSrc
        cases Nat.lt_or_ge (hi - (srcW.modulus - dstW.modulus)) dstW.modulus with
        | inl hLtD => exact hLtD
        | inr hGeD =>
          exact absurd hAdd (Nat.not_lt_of_ge (Nat.add_le_add_left hGeD _)))
    hStep

/-- Boolean-switched two-arm diamond join: collapses a `flag : Bool` branch
(e.g. `SwitchInt`) where both arms reach `dstSpec` within `armFuel` steps into
a single `OvfCastStageCut` of budget `armFuel + 1` (linear $O(m)$ composition
across $m$ diamonds without $2^m$ path explosion). -/
theorem ovfCastStageCut_bool_diamond {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {armFuel : Nat}
    (flag : Bool) (trueState falseState : S → S)
    (hSwitch : ∀ s : S,
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      step s = .step (if flag then trueState s else falseState s))
    (hTrueArm : ∀ s : S,
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False) armFuel (trueState s))
    (hFalseArm : ∀ s : S,
      StageIntervalStateInv fops baseLocals ids srcSpec s →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids dstSpec)
        (fun o => earlyOk o = true) (fun _ => False) armFuel (falseState s)) :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec
      (armFuel + 1) := by
  intro s hInv
  refine wpUntilFuel_step
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st))) ?_
  change (step s).wp _ _ _
  rw [hSwitch s hInv]
  cases flag with
  | true => exact hTrueArm s hInv
  | false => exact hFalseArm s hInv

/-- Lifts a `StepStageCut` family between `StageIntervalStateInv` cutpoints
into `OvfCastStageCut`. -/
theorem ovfCastStageCut_of_stepStageCut {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : ∀ s : S, StageIntervalStateInv fops baseLocals ids srcSpec s →
      ∃ s' : S, StepStageCut step fuel s s' ∧
        StageIntervalStateInv fops baseLocals ids dstSpec s') :
    OvfCastStageCut fops step baseLocals ids earlyOk srcSpec dstSpec fuel := by
  intro s hInv
  let ⟨s', hCut, hDst⟩ := h s hInv
  have hDet :=
    (stepStageCut_iff_wpUntilFuel
      (tag := fun st => some (fops.blockOf st))).mp hCut
  exact wpUntilFuel_weaken
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (fun st hEq => by rw [hEq]; exact hDst)
    (fun _ hf => False.elim hf)
    (fun _ hf => False.elim hf) hDet

/-- `0 Quot.sound` pointwise `BlockTree` transport: lifts an `OvfCastStageCut`
proved over a pre-built `ValidBlockTree` (using `lookupForced?`) directly to
the list-backed step function `stepWith (listGet? blocks)`. -/
theorem ovfCastStageCut_of_validBlockTree {BB : Type y}
    {blocks : List BB} {bt : BlockTree BB} (hValid : ValidBlockTree blocks bt)
    (fops : OvfCastFrameOps S Val)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : OvfCastStageCut fops (stepWith bt.lookupForced?) baseLocals ids
      earlyOk srcSpec dstSpec fuel) :
    OvfCastStageCut fops (stepWith (listGet? blocks)) baseLocals ids
      earlyOk srcSpec dstSpec fuel :=
  ovfCastStageCut_congr_step
    (fun s => hPointwise _ _ s (fun i =>
      (bt.lookupForced?_eq i).trans (hValid.2 i))) h

/-- `0 Quot.sound` pointwise `Chunk8BlockTree` transport to `listGet?`. -/
theorem ovfCastStageCut_of_validChunk8BlockTree {BB : Type y}
    {blocks : List BB} {bt : Chunk8BlockTree BB}
    (hValid : ValidChunk8BlockTree blocks bt)
    (fops : OvfCastFrameOps S Val)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : OvfCastStageCut fops (stepWith bt.lookupForced?) baseLocals ids
      earlyOk srcSpec dstSpec fuel) :
    OvfCastStageCut fops (stepWith (listGet? blocks)) baseLocals ids
      earlyOk srcSpec dstSpec fuel :=
  ovfCastStageCut_congr_step
    (fun s => hPointwise _ _ s (fun i =>
      (bt.lookupForced?_eq i).trans (hValid.2 i))) h

/-- Seals an `OvfCastStageCut` directly from `evalBlockTreeToCut` on a pre-built
`ValidBlockTree` (`0 Quot.sound`), connecting `BlockTree` kernel evaluation to
`OvfCastStageCut`. -/
theorem ovfCastStageCut_of_evalBlockTreeToCut {BB : Type y}
    {blocks : List BB} {bt : BlockTree BB} (hValid : ValidBlockTree blocks bt)
    (fops : OvfCastFrameOps S Val)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {cuts : MaskTree} {fuel : Nat}
    (hEval : ∀ s : S, StageIntervalStateInv fops baseLocals ids srcSpec s →
      ∃ s' : S,
        evalBlockTreeToCut bt stepWith StepOutcome.next? fops.blockOf cuts
          fuel s = .cut s' ∧
        StageIntervalStateInv fops baseLocals ids dstSpec s') :
    OvfCastStageCut fops (stepWith (listGet? blocks)) baseLocals ids earlyOk
      srcSpec dstSpec fuel :=
  ovfCastStageCut_of_stepStageCut (fun s hInv => by
    let ⟨s', hEv, hDst⟩ := hEval s hInv
    exact ⟨s',
      stageCut_of_validBlockTreeToCut_of_pointwise hValid stepWith hPointwise hEv,
      hDst⟩)

/-- Seals an `OvfCastStageCut` directly from `evalBlockTreeFromCut` on a
pre-built `ValidBlockTree` at budget `fuel + 1` (`0 Quot.sound`). -/
theorem ovfCastStageCut_of_evalBlockTreeFromCut {BB : Type y}
    {blocks : List BB} {bt : BlockTree BB} (hValid : ValidBlockTree blocks bt)
    (fops : OvfCastFrameOps S Val)
    (stepWith : (Nat → Option BB) → S → StepOutcome S Out Fault)
    (hPointwise : ∀ (f g : Nat → Option BB) (s : S),
      (∀ i, f i = g i) → stepWith f s = stepWith g s)
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {cuts : MaskTree} {fuel : Nat}
    (hEval : ∀ s : S, StageIntervalStateInv fops baseLocals ids srcSpec s →
      ∃ s' : S,
        evalBlockTreeFromCut bt stepWith StepOutcome.next? fops.blockOf cuts
          fuel s = .cut s' ∧
        StageIntervalStateInv fops baseLocals ids dstSpec s') :
    OvfCastStageCut fops (stepWith (listGet? blocks)) baseLocals ids earlyOk
      srcSpec dstSpec (fuel + 1) :=
  ovfCastStageCut_of_stepStageCut (fun s hInv => by
    let ⟨s', hEv, hDst⟩ := hEval s hInv
    exact ⟨s',
      stageCut_of_validBlockTreeFromCut_of_pointwise hValid stepWith hPointwise hEv,
      hDst⟩)

/-- Lifts a no-early-exit `OvfCastStageCut` (`∀ o, earlyOk o = false`) into a
fuel-free `DetStageCut` reachability family (for every entry state `s`, there
exists an exit state `s'` with `DetStageCut step s s'` and
`StageIntervalStateInv ... dstSpec s'`). -/
theorem ovfCastStageCut_to_detStageCut {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (hNoEarly : ∀ o : Out, earlyOk o = false)
    (h : OvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fuel)
    {s : S} (hEntry : StageIntervalStateInv fops baseLocals ids srcSpec s) :
    ∃ s' : S, DetStageCut step s s' ∧
      StageIntervalStateInv fops baseLocals ids dstSpec s' := by
  have hWp := h s hEntry
  clear h hEntry
  induction fuel generalizing s with
  | zero => exact ⟨s, DetStageCut.refl step s, hWp⟩
  | succ k ih =>
    cases (wpUntilFuel_succ_iff
        (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))).mp
        hWp with
    | inl hHere => exact ⟨s, DetStageCut.refl step s, hHere⟩
    | inr hStep =>
      change (step s).wp _ _ _ at hStep
      cases hS : step s with
      | step sNext =>
        rw [hS] at hStep
        let ⟨s', hDet, hDst⟩ := ih hStep
        exact ⟨s',
          DetStageCut.trans (DetStageCut.of_stepStageCut (StepStageCut.single hS))
            hDet, hDst⟩
      | done o =>
        rw [hS] at hStep
        have hEq : earlyOk o = true := hStep
        rw [hNoEarly o] at hEq
        cases hEq
      | fault _ =>
        rw [hS] at hStep
        exact False.elim hStep

/-- Lifts an `OvfCastStageCut` directly into a fuel-free
`ParametricCore.StageCut`. -/
theorem ovfCastStageCut_to_stageCut {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat}
    (h : OvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fuel) :
    StageCut (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (StageIntervalStateInv fops baseLocals ids srcSpec)
      (StageIntervalStateInv fops baseLocals ids dstSpec)
      (fun o => earlyOk o = true) (fun _ => False) :=
  StageCut.intro
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (fun s hInv =>
      wpUntil_of_wpUntilFuel
        (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (h s hInv))

/-- Joins an `OvfCastStageCut` with a bounded exit `wpOutcomeFuel` proof into
a bounded `wpOutcomeFuel` derivation (`fChain + fExit` fuel). -/
theorem ovfCastStageCut_to_wpOutcomeFuel {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fChain fExit : Nat}
    {s₀ : S} {post : Out → Prop}
    (hEntry : StageIntervalStateInv fops baseLocals ids srcSpec s₀)
    (hCut : OvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fChain)
    (hEarly : ∀ o : Out, earlyOk o = true → post o)
    (hExit : ∀ st : S, StageIntervalStateInv fops baseLocals ids dstSpec st →
      wpOutcomeFuel
        (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        post (fun _ => False) fExit st) :
    wpOutcomeFuel
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      post (fun _ => False) (fChain + fExit) s₀ :=
  wpUntilFuel_to_wpOutcomeFuel
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (wpUntilFuel_weaken
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (fun _ h => h) hEarly (fun _ hf => hf) (hCut s₀ hEntry))
    hExit

/-- Joins an `OvfCastStageCut` with a fuel-free exit `wpOutcome` proof into a
fuel-free `wpOutcome` derivation. -/
theorem ovfCastStageCut_to_wpOutcome {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fChain : Nat}
    {s₀ : S} {post : Out → Prop}
    (hEntry : StageIntervalStateInv fops baseLocals ids srcSpec s₀)
    (hCut : OvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fChain)
    (hEarly : ∀ o : Out, earlyOk o = true → post o)
    (hExit : ∀ st : S, StageIntervalStateInv fops baseLocals ids dstSpec st →
      wpOutcome
        (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        post (fun _ => False) st) :
    wpOutcome
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      post (fun _ => False) s₀ :=
  wpUntil_bind
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (wpUntil_mono
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (fun _ h => h) hEarly (fun _ hf => hf)
      (wpUntil_of_wpUntilFuel
        (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (hCut s₀ hEntry)))
    hExit

/-- Bystander-local framing extracted from `OvfCastStageCut`: any bystander
index `j` (outside `{accId, tmpId, ovfMulId, ovfAddId}`) retains its exact
baseline value `listGet? baseLocals j` at the destination cutpoint. -/
theorem ovfCastStageCut_frame_bystander {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {srcSpec dstSpec : StageIntervalSpec} {fuel : Nat} {s₀ : S} {j : Nat}
    (hEntry : StageIntervalStateInv fops baseLocals ids srcSpec s₀)
    (hCut : OvfCastStageCut fops step baseLocals ids earlyOk
      srcSpec dstSpec fuel)
    (hByst : ids.isBystander j = true) :
    wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (fun st =>
        StageIntervalStateInv fops baseLocals ids dstSpec st ∧
        listGet? (fops.localsOf st) j = listGet? baseLocals j)
      (fun o => earlyOk o = true) (fun _ => False) fuel s₀ := by
  have ⟨h1, h2, h3, h4⟩ := StageLocalIds.isBystander_unpack hByst
  exact wpUntilFuel_weaken
    (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
    (fun st hDst => ⟨hDst, hDst.2.2.2 j h1 h2 h3 h4⟩)
    (fun _ ho => ho) (fun _ hf => hf) (hCut s₀ hEntry)

end OvfCut

attribute [irreducible] OvfCastStageCut

/- Build-time regression guard for the `@[irreducible]` barrier: neither
`rfl` (default-transparency `isDefEq`) nor `simp` may unfold `OvfCastStageCut` into
`denoteOvfCastStageCut`; clients must go through `open_ovfCastStageCut`. -/
example : True := by
  fail_if_success
    have : @OvfCastStageCut = @denoteOvfCastStageCut := rfl
  fail_if_success
    have : @OvfCastStageCut = @denoteOvfCastStageCut := by simp only []
  trivial

/-! ### Mixed Unsigned/Signed View Composition -/

/-- Mixed-view composition (raw → signed): a raw-view `OvfCastStageCut` ending
at a non-negative interval `[lo, hi]` (`hi < halfModulus`) chains into a
`signedView` cut starting at the same values in biased coordinates
(`[lo + halfModulus, hi + halfModulus]`), with budgets adding. This is the
`u8 → … as i32 → signed arithmetic` pipeline shape; the two cuts carry
different `OvfCastFrameOps`, so `ovfCastStageCut_compose` cannot join them. -/
theorem ovfCastStageCut_compose_raw_to_signedView {S : Type u} {Val : Type v}
    {Out : Type w} {Fault : Type x}
    {fops : OvfCastFrameOps S Val} {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {n₀ n₂ : StageIntervalSpec} {bb lo hi : Nat} {wd : ScalarWidth}
    {f₁ f₂ : Nat} (hHi : hi < wd.halfModulus)
    (h₁ : OvfCastStageCut fops step baseLocals ids earlyOk n₀ ⟨bb, wd, lo, hi⟩ f₁)
    (h₂ : OvfCastStageCut fops.signedView step baseLocals ids earlyOk
      ⟨bb, wd, lo + wd.halfModulus, hi + wd.halfModulus⟩ n₂ f₂) :
    ∀ s : S, StageIntervalStateInv fops baseLocals ids n₀ s →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops.signedView baseLocals ids n₂)
        (fun o => earlyOk o = true) (fun _ => False) (f₁ + f₂) s :=
  fun s hInv₀ =>
    wpUntilFuel_bind
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (open_ovfCastStageCut h₁ s hInv₀)
      (fun st hInv₁ =>
        open_ovfCastStageCut h₂ st
          ((stageIntervalStateInv_signedView_nonneg_iff fops baseLocals ids bb wd
            hHi st).mp hInv₁))

/-- Mixed-view composition (signed → raw): a `signedView` cut ending at a
non-negative signed interval (biased `[lo + halfModulus, hi + halfModulus]`
with `hi < halfModulus`) chains into a raw-view cut starting at `[lo, hi]`,
with budgets adding (the `… as u32` after signed arithmetic proven
non-negative). -/
theorem ovfCastStageCut_compose_signedView_to_raw {S : Type u} {Val : Type v}
    {Out : Type w} {Fault : Type x}
    {fops : OvfCastFrameOps S Val} {step : S → StepOutcome S Out Fault}
    {baseLocals : List Val} {ids : StageLocalIds} {earlyOk : Out → Bool}
    {n₀ n₂ : StageIntervalSpec} {bb lo hi : Nat} {wd : ScalarWidth}
    {f₁ f₂ : Nat} (hHi : hi < wd.halfModulus)
    (h₁ : OvfCastStageCut fops.signedView step baseLocals ids earlyOk n₀
      ⟨bb, wd, lo + wd.halfModulus, hi + wd.halfModulus⟩ f₁)
    (h₂ : OvfCastStageCut fops step baseLocals ids earlyOk ⟨bb, wd, lo, hi⟩ n₂ f₂) :
    ∀ s : S, StageIntervalStateInv fops.signedView baseLocals ids n₀ s →
      wpUntilFuel (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
        (StageIntervalStateInv fops baseLocals ids n₂)
        (fun o => earlyOk o = true) (fun _ => False) (f₁ + f₂) s :=
  fun s hInv₀ =>
    wpUntilFuel_bind
      (ops := MirWpOps.ofDetStep step (fun st => some (fops.blockOf st)))
      (open_ovfCastStageCut h₁ s hInv₀)
      (fun st hInv₁ =>
        open_ovfCastStageCut h₂ st
          ((stageIntervalStateInv_signedView_nonneg_iff fops baseLocals ids bb wd
            hHi st).mpr hInv₁))

/-! ### `Anneal.Firewall.IndexedCut` Interop for `OvfCastStageCut` -/

/-- Indexed stage-cut family for `Anneal.Firewall.IndexedCut`: stage `k` holds
the sealed `OvfCastStageCut` from `specAt k` to `endSpec` with budget
`fuelAt k` (indexed by `st : Unit` or any carrier carrying the cutpoint state).
-/
def ovfCastIndexedCutFamily {S : Type u} {Val : Type v} {Out : Type w}
    {Fault : Type x} (fops : OvfCastFrameOps S Val)
    (step : S → StepOutcome S Out Fault) (baseLocals : List Val)
    (ids : StageLocalIds) (earlyOk : Out → Bool)
    (specAt : Nat → StageIntervalSpec) (fuelAt : Nat → Nat)
    (endSpec : StageIntervalSpec) (stage : Nat) (_st : Unit) : Prop :=
  OvfCastStageCut fops step baseLocals ids earlyOk
    (specAt stage) endSpec (fuelAt stage)

/-- Seals an `OvfCastStageCut` into `Anneal.Firewall.IndexedCut`. -/
theorem OvfCastStageCut.to_indexedCut {S : Type u} {Val : Type v}
    {Out : Type w} {Fault : Type x} {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {specAt : Nat → StageIntervalSpec} {fuelAt : Nat → Nat}
    {endSpec : StageIntervalSpec} {stage : Nat}
    (h : OvfCastStageCut fops step baseLocals ids earlyOk
      (specAt stage) endSpec (fuelAt stage)) :
    Anneal.Firewall.IndexedCut
      (ovfCastIndexedCutFamily fops step baseLocals ids earlyOk
        specAt fuelAt endSpec) stage () :=
  Anneal.Firewall.seal_cut h

/-- Prepends one `OvfCastStageCut` onto an `Anneal.Firewall.IndexedCut` via
`Anneal.Firewall.step_cut`. -/
theorem ovfCastIndexedCut_step {S : Type u} {Val : Type v} {Out : Type w}
    {Fault : Type x} {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {specAt : Nat → StageIntervalSpec} {fuelAt : Nat → Nat}
    {endSpec : StageIntervalSpec} {stage₁ stage₂ stepFuel : Nat}
    (hFuel : fuelAt stage₁ = stepFuel + fuelAt stage₂)
    (hStep : OvfCastStageCut fops step baseLocals ids earlyOk
      (specAt stage₁) (specAt stage₂) stepFuel)
    (hNext : Anneal.Firewall.IndexedCut
      (ovfCastIndexedCutFamily fops step baseLocals ids earlyOk
        specAt fuelAt endSpec) stage₂ ()) :
    Anneal.Firewall.IndexedCut
      (ovfCastIndexedCutFamily fops step baseLocals ids earlyOk
        specAt fuelAt endSpec) stage₁ () :=
  Anneal.Firewall.step_cut
    (fun hTail => by
      unfold ovfCastIndexedCutFamily
      rw [hFuel]
      exact ovfCastStageCut_compose hStep hTail)
    hNext

/-- Discharges a final goal from an `OvfCastStageCut` `IndexedCut` via
`Anneal.Firewall.finish_cut`. -/
theorem ovfCastIndexedCut_finish {S : Type u} {Val : Type v} {Out : Type w}
    {Fault : Type x} {fops : OvfCastFrameOps S Val}
    {step : S → StepOutcome S Out Fault} {baseLocals : List Val}
    {ids : StageLocalIds} {earlyOk : Out → Bool}
    {specAt : Nat → StageIntervalSpec} {fuelAt : Nat → Nat}
    {endSpec : StageIntervalSpec} {stage : Nat} {post : Prop}
    (hDone : OvfCastStageCut fops step baseLocals ids earlyOk
      (specAt stage) endSpec (fuelAt stage) → post)
    (hCut : Anneal.Firewall.IndexedCut
      (ovfCastIndexedCutFamily fops step baseLocals ids earlyOk
        specAt fuelAt endSpec) stage ()) :
    post :=
  Anneal.Firewall.finish_cut hDone hCut

/-! ## Part IV: Multi-Diamond `BlockTree` Pipeline & Fail-Closed Canaries -/

/-- Value domain for the self-contained multi-diamond CFG canary. -/
private inductive OcjVal : Type where
  | scalar (w : ScalarWidth) (bits : Nat)
  | flag (b : Bool)
  | ovfTuple (w : ScalarWidth) (bits : Nat) (overflowed : Bool)
  | uninit

/-- Machine state for the self-contained multi-diamond CFG canary. -/
private structure OcjState where
  bb : Nat
  locals : List OcjVal

/-- `OvfCastFrameOps` instance for `OcjState` / `OcjVal`. -/
private def ocjFrameOps : OvfCastFrameOps OcjState OcjVal where
  blockOf s := s.bb
  localsOf s := s.locals
  withBlockLocals _ bb locs := { bb := bb, locals := locs }
  mkScalar w n := .scalar w n
  asScalar? w v :=
    match v with
    | .scalar w' n =>
      if w.beq w' && Nat.blt n w.modulus then some n else none
    | _ => none
  mkOvfTuple w n b := .ovfTuple w n b

private theorem ocjFrameOps_lawful : ocjFrameOps.Lawful where
  blockOf_withBlockLocals _ _ _ := rfl
  localsOf_withBlockLocals _ _ _ := rfl
  asScalar?_mkScalar w n hLt := by
    unfold ocjFrameOps
    dsimp only
    rw [w.beq_refl, StageIntervalSpec.nat_blt_eq_true_of_lt hLt]
    rfl

/-- CFG block operations for the self-contained multi-diamond `BlockTree`
canary: boolean switch, affine `u32 -> u16 -> mulWithOverflow + mulUnchecked ->
addWithOverflow + addUnchecked -> u32` arm, checked-add early-return diamond,
and return. -/
private inductive OcjBlock : Type where
  | switchFlag (flagId trueBb falseBb : Nat)
  | affineArm (ids : StageLocalIds) (mulK addC joinBb : Nat)
  | checkedAddBranch (ids : StageLocalIds) (addC joinBb : Nat)
  | ret (accId : Nat)

/-- Block-indexed step function over an arbitrary lookup `look : Nat → Option
OcjBlock` (supporting zero-`Quot.sound` pointwise `BlockTree` transport). -/
private def ocjStepWith (look : Nat → Option OcjBlock) (s : OcjState) :
    StepOutcome OcjState (Option Nat) Unit :=
  match look s.bb with
  | none => .fault ()
  | some (.switchFlag flagId tBb fBb) =>
    match listGet? s.locals flagId with
    | some (.flag true) => .step { s with bb := tBb }
    | some (.flag false) => .step { s with bb := fBb }
    | _ => .fault ()
  | some (.affineArm ids mulK addC joinBb) =>
    match listGet? s.locals ids.accId with
    | some (.scalar .u32 acc) =>
      let narrowed := intToIntCast .u32 false .u16 acc
      let ovfMul := mulWithOverflowU .u16 narrowed mulK
      match mulUncheckedU .u16 narrowed mulK with
      | none => .fault ()
      | some prod =>
        let ovfAdd := addWithOverflowU .u16 prod addC
        match addUncheckedU .u16 prod addC with
        | none => .fault ()
        | some sum =>
          let widened := intToIntCast .u16 false .u32 sum
          let locs1 := listSetAt s.locals ids.tmpId (.scalar .u16 sum)
          let locs2 := listSetAt locs1 ids.ovfMulId (.ovfTuple .u16 ovfMul.1 ovfMul.2)
          let locs3 := listSetAt locs2 ids.ovfAddId (.ovfTuple .u16 ovfAdd.1 ovfAdd.2)
          let locs4 := listSetAt locs3 ids.accId (.scalar .u32 widened)
          .step { bb := joinBb, locals := locs4 }
    | _ => .fault ()
  | some (.checkedAddBranch ids addC joinBb) =>
    match listGet? s.locals ids.accId with
    | some (.scalar .u16 acc) =>
      let res := addWithOverflowU .u16 acc addC
      match res.2 with
      | true => .done none
      | false =>
        let locs1 := listSetAt s.locals ids.ovfAddId (.ovfTuple .u16 res.1 false)
        let locs2 := listSetAt locs1 ids.accId (.scalar .u16 res.1)
        .step { bb := joinBb, locals := locs2 }
    | _ => .fault ()
  | some (.ret accId) =>
    match listGet? s.locals accId with
    | some (.scalar _ v) => .done (some v)
    | _ => .fault ()

private theorem ocjStepWith_pointwise (f g : Nat → Option OcjBlock)
    (s : OcjState) (hEq : ∀ i, f i = g i) :
    ocjStepWith f s = ocjStepWith g s := by
  unfold ocjStepWith
  rw [hEq s.bb]

/-- Stage local indices for the 8-diamond (`256`-path) pipeline, leaving local
`0` (bystander sentinel) and locals `1..8` (8 boolean branch flags) untouched. -/
private def canaryIds8 : StageLocalIds :=
  { accId := 9, tmpId := 10, ovfMulId := 11, ovfAddId := 12 }

/-- 25-block CFG encoding 8 sequential affine `intToInt` + `*WithOverflow` +
`*Unchecked` diamonds (`2^8 = 256` paths), mapping `[1, 1]` to `[58, 1041]`. -/
private def canaryBlocks8 : List OcjBlock :=
  [ .switchFlag 1 1 2,
    .affineArm canaryIds8 2 1 3,
    .affineArm canaryIds8 1 1 3,
    .switchFlag 2 4 5,
    .affineArm canaryIds8 2 3 6,
    .affineArm canaryIds8 1 2 6,
    .switchFlag 3 7 8,
    .affineArm canaryIds8 2 5 9,
    .affineArm canaryIds8 1 4 9,
    .switchFlag 4 10 11,
    .affineArm canaryIds8 2 7 12,
    .affineArm canaryIds8 1 6 12,
    .switchFlag 5 13 14,
    .affineArm canaryIds8 2 11 15,
    .affineArm canaryIds8 1 8 15,
    .switchFlag 6 16 17,
    .affineArm canaryIds8 2 13 18,
    .affineArm canaryIds8 1 10 18,
    .switchFlag 7 19 20,
    .affineArm canaryIds8 2 17 21,
    .affineArm canaryIds8 1 12 21,
    .switchFlag 8 22 23,
    .affineArm canaryIds8 2 19 24,
    .affineArm canaryIds8 1 14 24,
    .ret 9 ]

private def canaryBt8 : BlockTree OcjBlock :=
  BlockTree.ofList canaryBlocks8

private def canaryBaseLocals8 (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) : List OcjVal :=
  [ .scalar .u32 0xDEAD,
    .flag b0, .flag b1, .flag b2, .flag b3,
    .flag b4, .flag b5, .flag b6, .flag b7,
    .scalar .u32 1, .uninit, .uninit, .uninit ]

/-- Generic 2-step diamond sealer for one stage of `canaryBt8` over `OvfCastStageCut`. -/
private theorem seal_canary_diamond
    (baseLocals : List OcjVal) (ids : StageLocalIds)
    {entryBb flagId tBb fBb joinBb tMul tAdd fMul fAdd lo hi loNext hiNext : Nat}
    {flagVal : Bool}
    (hWf : ids.wf baseLocals.length = true)
    (hFlagByst : ids.isBystander flagId = true)
    (hFlagBase : listGet? baseLocals flagId = some (.flag flagVal))
    (hEntry : canaryBt8.lookupForced? entryBb = some (.switchFlag flagId tBb fBb))
    (hTrue : canaryBt8.lookupForced? tBb = some (.affineArm ids tMul tAdd joinBb))
    (hFalse : canaryBt8.lookupForced? fBb = some (.affineArm ids fMul fAdd joinBb))
    (hHi16 : hi < 65536)
    (hTMul : hi * tMul < 65536) (hTHi : hi * tMul + tAdd ≤ hiNext)
    (hTLo : loNext ≤ lo * tMul + tAdd)
    (hFMul : hi * fMul < 65536) (hFHi : hi * fMul + fAdd ≤ hiNext)
    (hFLo : loNext ≤ lo * fMul + fAdd)
    (hHiNext : hiNext < 65536) :
    OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      baseLocals ids (fun _ => false)
      ⟨entryBb, .u32, lo, hi⟩ ⟨joinBb, .u32, loNext, hiNext⟩ 2 := by
  have u := StageLocalIds.wf_unpack hWf
  have ⟨hF1, hF2, hF3, hF4⟩ := StageLocalIds.isBystander_unpack hFlagByst
  have hArmStep :
      ∀ (armBb mulK addC : Nat)
        (hArm : canaryBt8.lookupForced? armBb = some (.affineArm ids mulK addC joinBb))
        (hMulB : hi * mulK < 65536) (hHiB : hi * mulK + addC ≤ hiNext)
        (hLoB : loNext ≤ lo * mulK + addC)
        (s : OcjState),
        StageIntervalStateInv ocjFrameOps baseLocals ids ⟨entryBb, .u32, lo, hi⟩ s →
        wpUntilFuel
          (ops := MirWpOps.ofDetStep (ocjStepWith canaryBt8.lookupForced?)
            (fun st => some st.bb))
          (StageIntervalStateInv ocjFrameOps baseLocals ids ⟨joinBb, .u32, loNext, hiNext⟩)
          (fun _ => false = true) (fun _ => False) 1 { s with bb := armBb } := by
    intro armBb mulK addC hArm hMulB hHiB hLoB s hInv
    let ⟨acc, hAccGet, hLoAcc, hAccHi, _⟩ := hInv.2.2.1
    have hLen : s.locals.length = baseLocals.length := hInv.2.1
    have hAcc16 : acc < ScalarWidth.u16.modulus :=
      Nat.lt_of_le_of_lt hAccHi hHi16
    have hProd16 : acc * mulK < ScalarWidth.u16.modulus :=
      Nat.lt_of_le_of_lt (Nat.mul_le_mul_right mulK hAccHi) hMulB
    have hResHi : acc * mulK + addC ≤ hiNext :=
      Nat.le_trans
        (Nat.add_le_add_right (Nat.mul_le_mul_right mulK hAccHi) addC) hHiB
    have hResLo : loNext ≤ acc * mulK + addC :=
      Nat.le_trans hLoB
        (Nat.add_le_add_right (Nat.mul_le_mul_right mulK hLoAcc) addC)
    have hRes16 : acc * mulK + addC < ScalarWidth.u16.modulus :=
      Nat.lt_of_le_of_lt hResHi hHiNext
    have hHiNext32 : hiNext < ScalarWidth.u32.modulus :=
      Nat.lt_trans hHiNext (pow2_lt_pow2 (a := 16) (b := 32) (Nat.le_of_ble_eq_true rfl))
    have hNarr : intToIntCast .u32 false .u16 acc = acc :=
      intToIntCast_narrow_exact .u32 false .u16 (Nat.le_of_ble_eq_true rfl) hAcc16
    have hMulU : mulUncheckedU .u16 acc mulK = some (acc * mulK) :=
      (mulUncheckedU_eq_some_iff .u16 acc mulK (acc * mulK)).mpr ⟨hProd16, rfl⟩
    have hAddU : addUncheckedU .u16 (acc * mulK) addC = some (acc * mulK + addC) :=
      (addUncheckedU_eq_some_iff .u16 (acc * mulK) addC (acc * mulK + addC)).mpr
        ⟨hRes16, rfl⟩
    have hWide : intToIntCast .u16 false .u32 (acc * mulK + addC) = acc * mulK + addC :=
      intToIntCast_widen_unsigned_exact .u16 .u32 (Nat.le_of_ble_eq_true rfl) hRes16
    refine wpUntilFuel_step
      (ops := MirWpOps.ofDetStep (ocjStepWith canaryBt8.lookupForced?)
        (fun st => some st.bb)) ?_
    change (ocjStepWith canaryBt8.lookupForced? { s with bb := armBb }).wp _ _ _
    unfold ocjStepWith
    dsimp only
    rw [hArm]
    dsimp only
    have hAccGet' : listGet? s.locals ids.accId = some (.scalar .u32 acc) := hAccGet
    rw [hAccGet']
    dsimp only
    rw [hNarr, hMulU]
    dsimp only
    rw [hAddU]
    dsimp only
    rw [hWide]
    dsimp only [StepOutcome.wp]
    refine wpUntilFuel_here
      (ops := MirWpOps.ofDetStep (ocjStepWith canaryBt8.lookupForced?)
        (fun st => some st.bb)) ?_
    refine ⟨rfl, ?_, ⟨acc * mulK + addC, ?_, hResLo, hResHi, hHiNext32⟩, ?_⟩
    · dsimp only [ocjFrameOps]
      rw [listSetAt_length, listSetAt_length, listSetAt_length, listSetAt_length, hLen]
    · dsimp only [ocjFrameOps]
      have hLen3 :
          (listSetAt (listSetAt (listSetAt s.locals ids.tmpId (.scalar .u16 (acc * mulK + addC)))
            ids.ovfMulId (.ovfTuple .u16 (mulWithOverflowU .u16 acc mulK).1
              (mulWithOverflowU .u16 acc mulK).2))
            ids.ovfAddId (.ovfTuple .u16 (addWithOverflowU .u16 (acc * mulK) addC).1
              (addWithOverflowU .u16 (acc * mulK) addC).2)).length =
            baseLocals.length := by
        rw [listSetAt_length, listSetAt_length, listSetAt_length, hLen]
      exact listGet?_listSetAt_same _ (by rw [hLen3]; exact u.accLt)
    · intro j h1 h2 h3 h4
      dsimp only [ocjFrameOps]
      rw [listGet?_listSetAt_ne _ _ h1, listGet?_listSetAt_ne _ _ h4,
        listGet?_listSetAt_ne _ _ h3, listGet?_listSetAt_ne _ _ h2]
      exact hInv.2.2.2 j h1 h2 h3 h4
  exact ovfCastStageCut_bool_diamond (armFuel := 1) flagVal
    (fun s => { s with bb := tBb }) (fun s => { s with bb := fBb })
    (fun s hInv => by
      have hBb : s.bb = entryBb := hInv.1
      have hFlagS : listGet? s.locals flagId = listGet? baseLocals flagId :=
        hInv.2.2.2 flagId hF1 hF2 hF3 hF4
      unfold ocjStepWith
      rw [hBb, hEntry]
      dsimp only
      rw [hFlagS, hFlagBase]
      cases flagVal <;> rfl)
    (fun s hInv => hArmStep tBb tMul tAdd hTrue hTMul hTHi hTLo s hInv)
    (fun s hInv => hArmStep fBb fMul fAdd hFalse hFMul hFHi hFLo s hInv)

/-- 8-stage (`2^8 = 256` paths) `BlockTree` multi-diamond pipeline verified in
$O(8)$ cuts via `ovfCastStageCut_compose`, transported to list-backed lookup
via `ovfCastStageCut_of_validBlockTree` (`0 Quot.sound`), and discharged into
`wpOutcome` with exact return interval `[58, 1041]` and bystander local `_0 =
0xDEAD` framed across all 256 paths. -/
theorem canary_ovfCast_8stage_256paths_blockTree
    (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    let base := canaryBaseLocals8 b0 b1 b2 b3 b4 b5 b6 b7
    let s0 : OcjState := { bb := 0, locals := base }
    wpOutcome (ops := MirWpOps.ofDetStep (ocjStepWith (listGet? canaryBlocks8))
      (fun st => some st.bb))
      (fun out => ∃ v : Nat, out = some v ∧ 58 ≤ v ∧ v ≤ 1041 ∧ v < 65536)
      (fun _ => False) s0 := by
  let base := canaryBaseLocals8 b0 b1 b2 b3 b4 b5 b6 b7
  have c0 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨0, .u32, 1, 1⟩ ⟨3, .u32, 2, 3⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b0)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c1 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨3, .u32, 2, 3⟩ ⟨6, .u32, 4, 9⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b1)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c2 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨6, .u32, 4, 9⟩ ⟨9, .u32, 8, 23⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b2)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c3 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨9, .u32, 8, 23⟩ ⟨12, .u32, 14, 53⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b3)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c4 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨12, .u32, 14, 53⟩ ⟨15, .u32, 22, 117⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b4)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c5 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨15, .u32, 22, 117⟩ ⟨18, .u32, 32, 247⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b5)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c6 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨18, .u32, 32, 247⟩ ⟨21, .u32, 44, 511⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b6)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c7 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨21, .u32, 44, 511⟩ ⟨24, .u32, 58, 1041⟩ 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b7)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have cAllBt : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false)
      ⟨0, .u32, 1, 1⟩ ⟨24, .u32, 58, 1041⟩ 16 :=
    ovfCastStageCut_compose
      (ovfCastStageCut_compose (ovfCastStageCut_compose c0 c1)
        (ovfCastStageCut_compose c2 c3))
      (ovfCastStageCut_compose (ovfCastStageCut_compose c4 c5)
        (ovfCastStageCut_compose c6 c7))
  have cAllList :
      OvfCastStageCut ocjFrameOps (ocjStepWith (listGet? canaryBlocks8))
        base canaryIds8 (fun _ => false)
        ⟨0, .u32, 1, 1⟩ ⟨24, .u32, 58, 1041⟩ 16 :=
    ovfCastStageCut_of_validBlockTree (valid_blockTree_ofList canaryBlocks8)
      ocjFrameOps ocjStepWith ocjStepWith_pointwise cAllBt
  have hEntry :
      StageIntervalStateInv ocjFrameOps base canaryIds8 ⟨0, .u32, 1, 1⟩
        { bb := 0, locals := base } :=
    ⟨rfl, rfl, ⟨1, rfl, Nat.le_refl 1, Nat.le_refl 1, Nat.le_of_ble_eq_true rfl⟩,
     fun _ _ _ _ _ => rfl⟩
  refine ovfCastStageCut_to_wpOutcome hEntry cAllList (fun _ hF => by cases hF) ?_
  intro st hInvEnd
  let ⟨acc, hAccGet, hLo, hHi, _⟩ := hInvEnd.2.2.1
  refine wpUntil_step
    (ops := MirWpOps.ofDetStep (ocjStepWith (listGet? canaryBlocks8))
      (fun s => some s.bb)) ?_
  change (ocjStepWith (listGet? canaryBlocks8) st).wp _ _ _
  have hBbEnd : st.bb = 24 := hInvEnd.1
  have hAccGet' : listGet? st.locals 9 = some (.scalar .u32 acc) := hAccGet
  have hLook24 : listGet? canaryBlocks8 24 = some (.ret 9) := rfl
  unfold ocjStepWith
  rw [hBbEnd, hLook24]
  dsimp only
  rw [hAccGet']
  exact ⟨acc, rfl, hLo, hHi, Nat.lt_of_le_of_lt hHi (Nat.le_of_ble_eq_true rfl)⟩

/-- Checked-arithmetic early-return diamond canary: for arbitrary `u16` input
`x ∈ [65400, 65500]`, `addWithOverflowU .u16 x 100` either returns `none` on
`overflowed = true` (`[65436..65500]`) or advances to `joinBb = 1` with
`acc ∈ [65500, 65535]` (`[65400..65435]`). -/
theorem canary_checked_diamond_early_return (x : Nat)
    (hLo : 65400 ≤ x) (hHi : x ≤ 65500) :
    let ids : StageLocalIds := { accId := 0, tmpId := 1, ovfMulId := 2, ovfAddId := 3 }
    let blocks : List OcjBlock := [.checkedAddBranch ids 100 1, .ret 0]
    let base : List OcjVal := [.scalar .u16 x, .uninit, .uninit, .uninit]
    wpOutcome (ops := MirWpOps.ofDetStep (ocjStepWith (listGet? blocks))
      (fun st => some st.bb))
      (fun out => out = none ∨ (∃ v, out = some v ∧ 65500 ≤ v ∧ v ≤ 65535))
      (fun _ => False) { bb := 0, locals := base } := by
  let ids : StageLocalIds := { accId := 0, tmpId := 1, ovfMulId := 2, ovfAddId := 3 }
  let blocks : List OcjBlock := [.checkedAddBranch ids 100 1, .ret 0]
  let base : List OcjVal := [.scalar .u16 x, .uninit, .uninit, .uninit]
  let earlyOk : Option Nat → Bool := fun o => match o with | none => true | some _ => false
  have hCut :
      OvfCastStageCut ocjFrameOps (ocjStepWith (listGet? blocks))
        base ids earlyOk
        ⟨0, .u16, 65400, 65500⟩ ⟨1, .u16, 65500, 65535⟩ 1 := by
    apply seal_ovfCastStageCut
    intro s hInv
    let ⟨acc, hAccGet, hAccLo, hAccHi, _⟩ := hInv.2.2.1
    refine wpUntilFuel_step
      (ops := MirWpOps.ofDetStep (ocjStepWith (listGet? blocks))
        (fun st => some st.bb)) ?_
    change (ocjStepWith (listGet? blocks) s).wp _ _ _
    have hBbS : s.bb = 0 := hInv.1
    have hLook0 : listGet? blocks 0 = some (.checkedAddBranch ids 100 1) := rfl
    have hAccGet' : listGet? s.locals ids.accId = some (.scalar .u16 acc) := hAccGet
    unfold ocjStepWith
    rw [hBbS, hLook0]
    dsimp only
    rw [hAccGet']
    dsimp only
    cases hOvf : (addWithOverflowU .u16 acc 100).2 with
    | true =>
      rfl
    | false =>
      have hLt : acc + 100 < ScalarWidth.u16.modulus :=
        (addWithOverflowU_no_overflow_iff .u16 acc 100).mp hOvf
      have hValEq : (addWithOverflowU .u16 acc 100).1 = acc + 100 := by
        rw [addWithOverflowU_of_lt .u16 hLt]
      rw [hValEq]
      dsimp only [StepOutcome.wp]
      refine wpUntilFuel_here
        (ops := MirWpOps.ofDetStep (ocjStepWith (listGet? blocks))
          (fun st => some st.bb)) ?_
      have hSumLo : 65500 ≤ acc + 100 := Nat.add_le_add_right hAccLo 100
      have hSumHi : acc + 100 ≤ 65535 := Nat.le_of_lt_succ hLt
      have hLen : s.locals.length = base.length := hInv.2.1
      refine ⟨rfl, ?_, ⟨acc + 100, ?_, hSumLo, hSumHi, Nat.le_of_ble_eq_true rfl⟩, ?_⟩
      · dsimp only [ocjFrameOps]
        rw [listSetAt_length, listSetAt_length, hLen]
      · dsimp only [ocjFrameOps]
        have hLen1 : (listSetAt s.locals ids.ovfAddId
            (.ovfTuple .u16 (acc + 100) false)).length = 4 := by
          rw [listSetAt_length, hLen]
          rfl
        exact listGet?_listSetAt_same _ (by rw [hLen1]; exact Nat.zero_lt_succ 3)
      · intro j h1 h2 h3 h4
        dsimp only [ocjFrameOps]
        rw [listGet?_listSetAt_ne _ _ h1, listGet?_listSetAt_ne _ _ h4]
        exact hInv.2.2.2 j h1 h2 h3 h4
  have hEntry :
      StageIntervalStateInv ocjFrameOps base ids ⟨0, .u16, 65400, 65500⟩
        { bb := 0, locals := base } :=
    ⟨rfl, rfl, ⟨x, rfl, hLo, hHi, Nat.le_of_ble_eq_true rfl⟩,
     fun _ _ _ _ _ => rfl⟩
  refine ovfCastStageCut_to_wpOutcome hEntry hCut
    (fun o ho => by
      cases o with
      | none => exact Or.inl rfl
      | some _ => cases ho) ?_
  intro st hDst
  let ⟨acc, hAccGet, hDstLo, hDstHi, _⟩ := hDst.2.2.1
  refine wpUntil_step
    (ops := MirWpOps.ofDetStep (ocjStepWith (listGet? blocks))
      (fun s => some s.bb)) ?_
  change (ocjStepWith (listGet? blocks) st).wp _ _ _
  have hBbDst : st.bb = 1 := hDst.1
  have hLook1 : listGet? blocks 1 = some (.ret 0) := rfl
  have hAccGet' : listGet? st.locals 0 = some (.scalar .u16 acc) := hAccGet
  unfold ocjStepWith
  rw [hBbDst, hLook1]
  dsimp only
  rw [hAccGet']
  exact Or.inr ⟨acc, rfl, hDstLo, hDstHi⟩

/-- Concrete signed two's-complement sign-extension, widening/narrowing
round-trip, and fail-closed overflow / `StageLocalIds.wf` rejection canary. -/
theorem canary_ovfCast_signed_and_negative_guards :
    intToIntCast .u8 true .u16 0xFF = 0xFFFF ∧
    intToIntCast .u8 true .u16 0x80 = 0xFF80 ∧
    intToIntCast .u16 true .u8 (intToIntCast .u8 true .u16 0x80) = 0x80 ∧
    intToIntCast .u8 false .u16 0xFF = 0x00FF ∧
    (addWithOverflowU .u16 65500 100).2 = true ∧
    addUncheckedU .u16 65500 100 = none ∧
    (mulWithOverflowU .u16 300 300).2 = true ∧
    mulUncheckedU .u16 300 300 = none ∧
    (subWithOverflowU .u16 10 20).2 = true ∧
    subUncheckedU .u16 10 20 = none ∧
    (shlWithOverflowU .u16 1 16).2 = true ∧
    shlUncheckedU .u16 1 16 = none ∧
    ({ accId := 2, tmpId := 2, ovfMulId := 3, ovfAddId := 4 } : StageLocalIds).wf 8 = false ∧
    ({ accId := 8, tmpId := 1, ovfMulId := 2, ovfAddId := 3 } : StageLocalIds).wf 8 = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `Anneal.Firewall.IndexedCut` + bystander-local framing canary over the
8-stage `BlockTree` pipeline: seals stage `0 -> 3 -> 6` via `ovfCastIndexedCut_step`
and extracts bystander local `_0 = 0xDEAD` framing via
`ovfCastStageCut_frame_bystander` + `ovfCastIndexedCut_finish`. -/
theorem canary_ovfCast_indexedCut_and_bystander_frame
    (b0 b1 b2 b3 b4 b5 b6 b7 : Bool) :
    let base := canaryBaseLocals8 b0 b1 b2 b3 b4 b5 b6 b7
    let s0 : OcjState := { bb := 0, locals := base }
    wpUntilFuel
      (ops := MirWpOps.ofDetStep (ocjStepWith (listGet? canaryBlocks8))
        (fun st => some st.bb))
      (fun st =>
        StageIntervalStateInv ocjFrameOps base canaryIds8 ⟨6, .u32, 4, 9⟩ st ∧
        listGet? st.locals 0 = some (.scalar .u32 0xDEAD))
      (fun _ => false = true) (fun _ => False) 4 s0 := by
  let base := canaryBaseLocals8 b0 b1 b2 b3 b4 b5 b6 b7
  let specAt : Nat → StageIntervalSpec := fun k =>
    match k with
    | 0 => ⟨0, .u32, 1, 1⟩
    | 1 => ⟨3, .u32, 2, 3⟩
    | _ => ⟨6, .u32, 4, 9⟩
  let fuelAt : Nat → Nat := fun k =>
    match k with
    | 0 => 4
    | 1 => 2
    | _ => 0
  have c0 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false) (specAt 0) (specAt 1) 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b0)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have c1 : OvfCastStageCut ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
      base canaryIds8 (fun _ => false) (specAt 1) (specAt 2) 2 :=
    seal_canary_diamond base canaryIds8 (flagVal := b1)
      rfl rfl rfl rfl rfl rfl
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
  have ic1 : Anneal.Firewall.IndexedCut
      (ovfCastIndexedCutFamily ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
        base canaryIds8 (fun _ => false) specAt fuelAt (specAt 2)) 1 () :=
    OvfCastStageCut.to_indexedCut (specAt := specAt) (fuelAt := fuelAt) (stage := 1) c1
  have ic0 : Anneal.Firewall.IndexedCut
      (ovfCastIndexedCutFamily ocjFrameOps (ocjStepWith canaryBt8.lookupForced?)
        base canaryIds8 (fun _ => false) specAt fuelAt (specAt 2)) 0 () :=
    ovfCastIndexedCut_step (stage₁ := 0) (stage₂ := 1) (stepFuel := 2) rfl c0 ic1
  have hEntry :
      StageIntervalStateInv ocjFrameOps base canaryIds8 ⟨0, .u32, 1, 1⟩
        { bb := 0, locals := base } :=
    ⟨rfl, rfl, ⟨1, rfl, Nat.le_refl 1, Nat.le_refl 1, Nat.le_of_ble_eq_true rfl⟩,
     fun _ _ _ _ _ => rfl⟩
  exact ovfCastIndexedCut_finish
    (fun hBt =>
      ovfCastStageCut_frame_bystander (j := 0) hEntry
        (ovfCastStageCut_of_validBlockTree (valid_blockTree_ofList canaryBlocks8)
          ocjFrameOps ocjStepWith ocjStepWith_pointwise hBt) rfl)
    ic0

/-- Concrete canary exercising `ovfCastStageCut_widen_signed_neg` (`i8 -> i16`
on negative interval `[0x80, 0xFF]`, shifting to `[0xFF80, 0xFFFF]`),
`ovfCastStageCut_narrow_signed_neg` (`i16 -> i8`, shifting back to
`[0x80, 0xFF]`), `ovfCastStageCut_compose`, `ovfCastStageCut_to_detStageCut`,
and `not_stageIntervalStateInv_of_decoded_out_of_range`. -/
theorem canary_ovfCast_signed_neg_stageCut_roundtrip (x : Nat)
    (hLo : 0x80 ≤ x) (hHi : x ≤ 0xFF) :
    let ids : StageLocalIds := { accId := 0, tmpId := 1, ovfMulId := 2, ovfAddId := 3 }
    let base : List OcjVal := [.scalar .u8 x, .uninit, .uninit, .uninit]
    let step : OcjState → StepOutcome OcjState Nat Unit := fun s =>
      match s.bb with
      | 0 =>
        match listGet? s.locals 0 with
        | some (.scalar .u8 a) =>
          .step { bb := 1,
                  locals := listSetAt s.locals 0 (.scalar .u16 (intToIntCast .u8 true .u16 a)) }
        | _ => .fault ()
      | 1 =>
        match listGet? s.locals 0 with
        | some (.scalar .u16 a) =>
          .step { bb := 2,
                  locals := listSetAt s.locals 0 (.scalar .u8 (intToIntCast .u16 true .u8 a)) }
        | _ => .fault ()
      | _ => .done 0
    (∃ sEnd : OcjState,
      DetStageCut step { bb := 0, locals := base } sEnd ∧
      StageIntervalStateInv ocjFrameOps base ids ⟨2, .u8, 0x80, 0xFF⟩ sEnd) ∧
    (¬ StageIntervalStateInv ocjFrameOps base ids ⟨0, .u8, 0x90, 0xFF⟩
        { bb := 0, locals := [.scalar .u8 0x80, .uninit, .uninit, .uninit] }) := by
  let ids : StageLocalIds := { accId := 0, tmpId := 1, ovfMulId := 2, ovfAddId := 3 }
  let base : List OcjVal := [.scalar .u8 x, .uninit, .uninit, .uninit]
  let step : OcjState → StepOutcome OcjState Nat Unit := fun s =>
    match s.bb with
    | 0 =>
      match listGet? s.locals 0 with
      | some (.scalar .u8 a) =>
        .step { bb := 1,
                locals := listSetAt s.locals 0 (.scalar .u16 (intToIntCast .u8 true .u16 a)) }
      | _ => .fault ()
    | 1 =>
      match listGet? s.locals 0 with
      | some (.scalar .u16 a) =>
        .step { bb := 2,
                locals := listSetAt s.locals 0 (.scalar .u8 (intToIntCast .u16 true .u8 a)) }
      | _ => .fault ()
    | _ => .done 0
  have hWide :
      OvfCastStageCut ocjFrameOps step base ids (fun _ => false)
        ⟨0, .u8, 0x80, 0xFF⟩ ⟨1, .u16, 0xFF80, 0xFFFF⟩ 1 :=
    ovfCastStageCut_widen_signed_neg (fops := ocjFrameOps) (step := step)
      ocjFrameOps_lawful (by rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_refl 0x80) (Nat.le_of_ble_eq_true rfl)
      (fun s acc hInv hAccGet _ _ => by
        have hBb : s.bb = 0 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u8 acc) := hAccGet
        dsimp only [step]
        rw [hBb, hGet]
        rfl)
  have hNarr :
      OvfCastStageCut ocjFrameOps step base ids (fun _ => false)
        ⟨1, .u16, 0xFF80, 0xFFFF⟩ ⟨2, .u8, 0x80, 0xFF⟩ 1 :=
    ovfCastStageCut_narrow_signed_neg (fops := ocjFrameOps) (step := step)
      (srcSigned := true) ocjFrameOps_lawful (by rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_refl 0xFF80) (Nat.le_of_ble_eq_true rfl)
      (fun s acc hInv hAccGet _ _ => by
        have hBb : s.bb = 1 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u16 acc) := hAccGet
        dsimp only [step]
        rw [hBb, hGet]
        rfl)
  have hBoth := ovfCastStageCut_compose hWide hNarr
  have hEntry :
      StageIntervalStateInv ocjFrameOps base ids ⟨0, .u8, 0x80, 0xFF⟩
        { bb := 0, locals := base } :=
    ⟨rfl, rfl, ⟨x, rfl, hLo, hHi, Nat.le_of_ble_eq_true rfl⟩,
     fun _ _ _ _ _ => rfl⟩
  refine ⟨ovfCastStageCut_to_detStageCut (fun _ => rfl) hBoth hEntry, ?_⟩
  exact not_stageIntervalStateInv_of_decoded_out_of_range
    (fops := ocjFrameOps) ocjFrameOps_lawful (slot := .scalar .u8 0x80) (n := 0x80)
    rfl rfl (Or.inl (Nat.le_of_ble_eq_true rfl))

/-- Signed two's-complement checked-arithmetic boundary & stage-cut canary:
1. Verifies all Rust `i8` overflow extremes (`127+1`, `-128+(-1)`, `-128-1`,
   `0-(-128)`, `-128*(-1)`, `16*8` overflow; `-64+(-64)`, `-1-(-128)`,
   `-16*8`, `-128*1`, `-128*0` succeed with exact bit patterns);
2. Composes an `ovfCastStageCut_checked_add_signed_diamond` (`i8` negative
   range `[-16..-4]` (`[240..252]`) `+ 2` -> `[-14..-2]` (`[242..254]`), with
   early-return overflow arm) directly into `ovfCastStageCut_widen_signed_neg`
   (`i8 -> i16`, `[0xFFF2..0xFFFE]`) and lowers to `wpOutcome`. -/
theorem canary_ovfCast_signed_checked_arithmetic_and_boundaries (x : Nat)
    (hLo : 240 ≤ x) (hHi : x ≤ 252) :
    -- Rust i8 boundary overflows:
    addWithOverflowS .u8 127 1 = (128, true) ∧
    addWithOverflowS .u8 128 255 = (127, true) ∧
    subWithOverflowS .u8 128 1 = (127, true) ∧
    subWithOverflowS .u8 0 128 = (128, true) ∧
    mulWithOverflowS .u8 128 255 = (128, true) ∧
    mulWithOverflowS .u8 16 8 = (128, true) ∧
    -- Rust i8 non-overflowing extremes:
    addWithOverflowS .u8 192 192 = (128, false) ∧
    subWithOverflowS .u8 255 128 = (127, false) ∧
    mulWithOverflowS .u8 240 8 = (128, false) ∧
    mulWithOverflowS .u8 128 1 = (128, false) ∧
    mulWithOverflowS .u8 128 0 = (0, false) ∧
    -- Stage-cut signed checked-add diamond + signed widening composition:
    (let base : List OcjVal := [.scalar .u8 x, .uninit, .uninit, .uninit]
     let step : OcjState → StepOutcome OcjState Nat Unit := fun s =>
       match s.bb with
       | 0 =>
         match listGet? s.locals 0 with
         | some (.scalar .u8 a) =>
           let r := addWithOverflowS .u8 a 2
           if r.2 then .step { bb := 99, locals := s.locals }
           else .step { bb := 1, locals := listSetAt s.locals 0 (.scalar .u8 r.1) }
         | _ => .fault ()
       | 1 =>
         match listGet? s.locals 0 with
         | some (.scalar .u8 a) =>
           .step { bb := 2,
                   locals := listSetAt s.locals 0 (.scalar .u16 (intToIntCast .u8 true .u16 a)) }
         | _ => .fault ()
       | 99 => .done 999
       | _ => .done 0
     wpOutcome (ops := MirWpOps.ofDetStep step (fun s => some s.bb))
       (fun o => o = 0 ∨ o = 999) (fun _ => False) { bb := 0, locals := base }) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  let ids : StageLocalIds := { accId := 0, tmpId := 1, ovfMulId := 2, ovfAddId := 3 }
  let base : List OcjVal := [.scalar .u8 x, .uninit, .uninit, .uninit]
  let step : OcjState → StepOutcome OcjState Nat Unit := fun s =>
    match s.bb with
    | 0 =>
      match listGet? s.locals 0 with
      | some (.scalar .u8 a) =>
        let r := addWithOverflowS .u8 a 2
        if r.2 then .step { bb := 99, locals := s.locals }
        else .step { bb := 1, locals := listSetAt s.locals 0 (.scalar .u8 r.1) }
      | _ => .fault ()
    | 1 =>
      match listGet? s.locals 0 with
      | some (.scalar .u8 a) =>
        .step { bb := 2,
                locals := listSetAt s.locals 0 (.scalar .u16 (intToIntCast .u8 true .u16 a)) }
      | _ => .fault ()
    | 99 => .done 999
    | _ => .done 0
  let branchState : OcjState → Nat → Bool → OcjState := fun s w b =>
    if b then { bb := 99, locals := s.locals }
    else { bb := 1, locals := listSetAt s.locals 0 (.scalar .u8 w) }
  have hDia :
      OvfCastStageCut ocjFrameOps step base ids (fun o => Nat.beq o 999)
        ⟨0, .u8, 240, 252⟩ ⟨1, .u8, 242, 254⟩ 2 :=
    ovfCastStageCut_checked_add_signed_diamond (fops := ocjFrameOps) (step := step)
      .u8 2 branchState
      (fun s acc hInv hAccGet _ _ => by
        have hBb : s.bb = 0 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u8 acc) := hAccGet
        dsimp only [step, branchState]
        rw [hBb, hGet]
        dsimp only
        cases (addWithOverflowS .u8 acc 2).2 <;> rfl)
      (fun s acc wrapped hInv hAccLo hAccHi _ _ _ _ _ hWrEq => by
        have hSumLt : acc + 2 < ScalarWidth.u8.modulus :=
          Nat.lt_of_le_of_lt (Nat.add_le_add_right hAccHi 2) (Nat.le_of_ble_eq_true rfl)
        have hWrap : wrapped = acc + 2 := by
          rw [hWrEq, Nat.mod_eq_of_lt hSumLt]
        dsimp only [branchState]
        refine wpUntilFuel_here (ops := MirWpOps.ofDetStep step (fun st => some st.bb)) ?_
        rw [hWrap]
        exact stageIntervalStateInv_set_acc ocjFrameOps_lawful (by rfl)
          (spec₂ := ⟨1, .u8, 242, 254⟩) hInv
          (Nat.add_le_add_right hAccLo 2) (Nat.add_le_add_right hAccHi 2)
          (Nat.le_of_ble_eq_true rfl))
      (fun s _ _ _ _ _ _ => by
        dsimp only [branchState]
        refine wpUntilFuel_step (ops := MirWpOps.ofDetStep step (fun st => some st.bb)) ?_
        change (StepOutcome.done (State := OcjState) (Fault := Unit) 999).wp _ _ _
        dsimp only [StepOutcome.wp]
        rfl)
  have hWide :
      OvfCastStageCut ocjFrameOps step base ids (fun o => Nat.beq o 999)
        ⟨1, .u8, 242, 254⟩ ⟨2, .u16, 0xFFF2, 0xFFFE⟩ 1 :=
    ovfCastStageCut_widen_signed_neg (fops := ocjFrameOps) (step := step)
      ocjFrameOps_lawful (by rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (fun s acc hInv hAccGet _ _ => by
        have hBb : s.bb = 1 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u8 acc) := hAccGet
        dsimp only [step]
        rw [hBb, hGet]
        rfl)
  have hComp := ovfCastStageCut_compose hDia hWide
  have hEntry :
      StageIntervalStateInv ocjFrameOps base ids ⟨0, .u8, 240, 252⟩
        { bb := 0, locals := base } :=
    ⟨rfl, rfl, ⟨x, rfl, hLo, hHi, Nat.le_of_ble_eq_true rfl⟩,
     fun _ _ _ _ _ => rfl⟩
  exact ovfCastStageCut_to_wpOutcome hEntry hComp
    (fun o hEq => Or.inr (Nat.eq_of_beq_eq_true hEq))
    (fun s hInv => by
      have hBb : s.bb = 2 := hInv.1
      refine wpUntil_step (ops := MirWpOps.ofDetStep step (fun st => some st.bb)) ?_
      change (step s).wp _ _ _
      dsimp only [step]
      rw [hBb]
      exact Or.inl rfl)

/-- Signed cross-zero interval canary (`i8`, biased coordinates via
`OvfCastFrameOps.signedView`):
1. biased interval `[123, 133]` is the signed interval `[-5, 5]`: its endpoints
   store bit patterns `251` (`-5`) and `5`, while `-128` (bit pattern `128`)
   has biased coordinate `0`, outside the interval;
2. a raw bit-pattern interval holding both `-5` (`251`) and `0` must also hold
   `-128` (`128`), so raw intervals cannot express `[-5, 5]`;
3. adding `3` to `-5` takes the no-overflow arm with result `-2` (bit pattern
   `254`, biased `126`), and `addWithOverflowS_biased_false_interval` places it
   in the tightened join interval `[126, 136]` (signed `[-2, 8]`);
4. adding `125` to `5` (signed `130 > 127`) is forced onto the overflow arm by
   `addWithOverflowS_biased_overflow_of_out_of_range`. -/
theorem canary_ovfCast_signed_cross_zero_interval :
    toBiased .u8 123 = 251 ∧ toBiased .u8 133 = 5 ∧ toBiased .u8 128 = 0 ∧
    (∀ lo hi : Nat, lo ≤ 0 → 251 ≤ hi → lo ≤ 128 ∧ 128 ≤ hi) ∧
    addWithOverflowS .u8 (toBiased .u8 123) 3 = (254, false) ∧
    toBiased .u8 254 = 126 ∧
    (123 + toBiased .u8 3 ≤ toBiased .u8 254 + ScalarWidth.u8.halfModulus ∧
      toBiased .u8 254 + ScalarWidth.u8.halfModulus ≤ 133 + toBiased .u8 3) ∧
    (addWithOverflowS .u8 (toBiased .u8 133) 125).2 = true := by
  have hAdd : addWithOverflowS .u8 (toBiased .u8 123) 3 = (254, false) := by
    decide
  have hI := addWithOverflowS_biased_false_interval .u8 (lo := 123) (hi := 133)
    (by decide) (Nat.le_refl 123) (by decide) hAdd
  refine ⟨by decide, by decide, by decide, ?_, hAdd, by decide,
    ⟨hI.2.1, hI.2.2.1⟩, ?_⟩
  · intro lo hi hLo hHi
    exact ⟨Nat.le_trans hLo (Nat.zero_le 128),
      Nat.le_trans (by decide) hHi⟩
  · exact addWithOverflowS_biased_overflow_of_out_of_range .u8 (by decide)
      (Or.inr (by decide))

/-- Concrete `BlockTree`-backed multi-diamond `signedView` pipeline canary
crossing zero TWICE:
- Entry: `i8 ∈ [-5, 5]` (biased `[123, 133]`), stored as real two's-complement
  bit pattern `toBiased .u8 accB`;
- Block 0 (`ovfCastStageCut_checked_add_signed_interval`): checked signed `+ 3`,
  tightening to `[-2, 8]` (biased `[126, 136]`), early-return `999` on overflow;
- Block 1 (`ovfCastStageCut_checked_sub_signed_interval`): checked signed `- 4`,
  crossing zero BACK into `[-6, 4]` (biased `[122, 132]`), early-return `999`;
- Block 2 (`ovfCastStageCut_checked_mul_signed_interval_nonneg`): checked signed
  `* 3`, expanding across zero to `[-18, 12]` (biased `[110, 140]`), early-return
  `999`;
- Block 3 (`ovfCastStageCut_widen_signed_interval`): signed widen `i8 → i16`
  across zero to `[-18, 12]` (biased `[32750, 32780]`);
- Composed via `ovfCastStageCut_compose`, transported from `bt.lookupForced?` to
  `listGet? blocks` via `ovfCastStageCut_of_validBlockTree`, and lowered to
  `wpOutcome` while framing untouched bystander local `4` (`some (.scalar .u32 42)`). -/
inductive SignedCrossZeroInstr where
  | addChecked (c nextBb ovfBb : Nat)
  | subChecked (c nextBb ovfBb : Nat)
  | mulChecked (c nextBb ovfBb : Nat)
  | widenI8ToI16 (nextBb : Nat)
  | ret (code : Nat)

private def signedCrossZeroStep (lookup : Nat → Option SignedCrossZeroInstr)
    (s : OcjState) : StepOutcome OcjState Nat Unit :=
  match lookup s.bb with
  | none => .fault ()
  | some (.addChecked c nextBb ovfBb) =>
    match listGet? s.locals 0 with
    | some (.scalar .u8 a) =>
      let r := addWithOverflowS .u8 a c
      if r.2 then .step { bb := ovfBb, locals := s.locals }
      else .step { bb := nextBb, locals := listSetAt s.locals 0 (.scalar .u8 r.1) }
    | _ => .fault ()
  | some (.subChecked c nextBb ovfBb) =>
    match listGet? s.locals 0 with
    | some (.scalar .u8 a) =>
      let r := subWithOverflowS .u8 a c
      if r.2 then .step { bb := ovfBb, locals := s.locals }
      else .step { bb := nextBb, locals := listSetAt s.locals 0 (.scalar .u8 r.1) }
    | _ => .fault ()
  | some (.mulChecked c nextBb ovfBb) =>
    match listGet? s.locals 0 with
    | some (.scalar .u8 a) =>
      let r := mulWithOverflowS .u8 a c
      if r.2 then .step { bb := ovfBb, locals := s.locals }
      else .step { bb := nextBb, locals := listSetAt s.locals 0 (.scalar .u8 r.1) }
    | _ => .fault ()
  | some (.widenI8ToI16 nextBb) =>
    match listGet? s.locals 0 with
    | some (.scalar .u8 a) =>
      .step { bb := nextBb,
              locals := listSetAt s.locals 0 (.scalar .u16 (intToIntCast .u8 true .u16 a)) }
    | _ => .fault ()
  | some (.ret code) => .done code

private def signedCrossZeroBlocks : List SignedCrossZeroInstr :=
  [ .addChecked 3 1 5,
    .subChecked 4 2 5,
    .mulChecked 3 3 5,
    .widenI8ToI16 4,
    .ret 0,
    .ret 999 ]

theorem canary_ovfCast_signedView_blockTree_cross_zero_pipeline (accB : Nat)
    (hLo : 123 ≤ accB) (hHi : accB ≤ 133) :
    let base : List OcjVal :=
      [.scalar .u8 (toBiased .u8 accB), .uninit, .uninit, .uninit, .scalar .u32 42]
    wpOutcome
      (ops := MirWpOps.ofDetStep (signedCrossZeroStep (listGet? signedCrossZeroBlocks))
        (fun s => some s.bb))
      (fun o => o = 0 ∨ o = 999) (fun _ => False) { bb := 0, locals := base } ∧
    (subWithOverflowS .u8 (toBiased .u8 0) 1).2 = true ∧
    (mulWithOverflowS .u8 (toBiased .u8 112) 9).2 = true := by
  let ids : StageLocalIds := { accId := 0, tmpId := 1, ovfMulId := 2, ovfAddId := 3 }
  let base : List OcjVal :=
    [.scalar .u8 (toBiased .u8 accB), .uninit, .uninit, .uninit, .scalar .u32 42]
  let bt := BlockTree.ofList signedCrossZeroBlocks
  have hValid : ValidBlockTree signedCrossZeroBlocks bt :=
    valid_blockTree_ofList signedCrossZeroBlocks
  let stepBt := signedCrossZeroStep bt.lookupForced?
  let branch (nextBb : Nat) : OcjState → Nat → Bool → OcjState := fun s w b =>
    if b then { bb := 5, locals := s.locals }
    else { bb := nextBb, locals := listSetAt s.locals 0 (.scalar .u8 w) }
  have hS0 :
      OvfCastStageCut ocjFrameOps.signedView stepBt base ids (fun o => Nat.beq o 999)
        ⟨0, .u8, 123, 133⟩ ⟨1, .u8, 126, 136⟩ 2 :=
    ovfCastStageCut_checked_add_signed_interval (fops := ocjFrameOps) (step := stepBt)
      .u8 3 rfl (branch 1)
      (fun s acc hInv hAccGet _ _ => by
        have hBb : s.bb = 0 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u8 (toBiased .u8 acc)) := hAccGet
        have hLook : bt.lookupForced? 0 = some (.addChecked 3 1 5) := rfl
        dsimp only [stepBt, signedCrossZeroStep, branch]
        rw [hBb, hLook, hGet]
        dsimp only
        cases (addWithOverflowS .u8 (toBiased .u8 acc) 3).2 <;> rfl)
      (fun s acc r hInv _ _ _ hILo hIHi hRlt => by
        dsimp only [branch]
        refine wpUntilFuel_here (ops := MirWpOps.ofDetStep stepBt (fun st => some st.bb)) ?_
        have hBiLo : 126 ≤ toBiased .u8 r :=
          Nat.le_of_add_le_add_right (show 126 + 128 ≤ toBiased .u8 r + 128 from hILo)
        have hBiHi : toBiased .u8 r ≤ 136 :=
          Nat.le_of_add_le_add_right (show toBiased .u8 r + 128 ≤ 136 + 128 from hIHi)
        have hInvR : toBiased .u8 (toBiased .u8 r) = r := by
          rw [toBiased_involutive, Nat.mod_eq_of_lt hRlt]
        have hGoal :=
          stageIntervalStateInv_set_acc (fops := ocjFrameOps.signedView)
            (OvfCastFrameOps.signedView_lawful ocjFrameOps_lawful) (by rfl)
            (spec₂ := ⟨1, .u8, 126, 136⟩) hInv hBiLo hBiHi (Nat.le_of_ble_eq_true rfl)
        change StageIntervalStateInv ocjFrameOps.signedView base ids ⟨1, .u8, 126, 136⟩
          { bb := 1, locals := listSetAt s.locals 0 (.scalar .u8 (toBiased .u8 (toBiased .u8 r))) }
          at hGoal
        rw [hInvR] at hGoal
        exact hGoal)
      (fun s _ _ _ _ _ _ => by
        dsimp only [branch]
        refine wpUntilFuel_step (ops := MirWpOps.ofDetStep stepBt (fun st => some st.bb)) ?_
        change (StepOutcome.done (State := OcjState) (Fault := Unit) 999).wp _ _ _
        dsimp only [StepOutcome.wp]
        rfl)
  have hS1 :
      OvfCastStageCut ocjFrameOps.signedView stepBt base ids (fun o => Nat.beq o 999)
        ⟨1, .u8, 126, 136⟩ ⟨2, .u8, 122, 132⟩ 2 :=
    ovfCastStageCut_checked_sub_signed_interval (fops := ocjFrameOps) (step := stepBt)
      .u8 4 rfl (branch 2)
      (fun s acc hInv hAccGet _ _ => by
        have hBb : s.bb = 1 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u8 (toBiased .u8 acc)) := hAccGet
        have hLook : bt.lookupForced? 1 = some (.subChecked 4 2 5) := rfl
        dsimp only [stepBt, signedCrossZeroStep, branch]
        rw [hBb, hLook, hGet]
        dsimp only
        cases (subWithOverflowS .u8 (toBiased .u8 acc) 4).2 <;> rfl)
      (fun s acc r hInv _ _ _ hILo hIHi hRlt => by
        dsimp only [branch]
        refine wpUntilFuel_here (ops := MirWpOps.ofDetStep stepBt (fun st => some st.bb)) ?_
        have hBiLo : 122 ≤ toBiased .u8 r :=
          Nat.le_of_add_le_add_right (show 122 + 132 ≤ toBiased .u8 r + 132 from hILo)
        have hBiHi : toBiased .u8 r ≤ 132 :=
          Nat.le_of_add_le_add_right (show toBiased .u8 r + 132 ≤ 132 + 132 from hIHi)
        have hInvR : toBiased .u8 (toBiased .u8 r) = r := by
          rw [toBiased_involutive, Nat.mod_eq_of_lt hRlt]
        have hGoal :=
          stageIntervalStateInv_set_acc (fops := ocjFrameOps.signedView)
            (OvfCastFrameOps.signedView_lawful ocjFrameOps_lawful) (by rfl)
            (spec₂ := ⟨2, .u8, 122, 132⟩) hInv hBiLo hBiHi (Nat.le_of_ble_eq_true rfl)
        change StageIntervalStateInv ocjFrameOps.signedView base ids ⟨2, .u8, 122, 132⟩
          { bb := 2, locals := listSetAt s.locals 0 (.scalar .u8 (toBiased .u8 (toBiased .u8 r))) }
          at hGoal
        rw [hInvR] at hGoal
        exact hGoal)
      (fun s _ _ _ _ _ _ => by
        dsimp only [branch]
        refine wpUntilFuel_step (ops := MirWpOps.ofDetStep stepBt (fun st => some st.bb)) ?_
        change (StepOutcome.done (State := OcjState) (Fault := Unit) 999).wp _ _ _
        dsimp only [StepOutcome.wp]
        rfl)
  have hS2 :
      OvfCastStageCut ocjFrameOps.signedView stepBt base ids (fun o => Nat.beq o 999)
        ⟨2, .u8, 122, 132⟩ ⟨3, .u8, 110, 140⟩ 2 :=
    ovfCastStageCut_checked_mul_signed_interval_nonneg (fops := ocjFrameOps) (step := stepBt)
      .u8 3 rfl (Nat.le_of_ble_eq_true rfl) (branch 3)
      (fun s acc hInv hAccGet _ _ => by
        have hBb : s.bb = 2 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u8 (toBiased .u8 acc)) := hAccGet
        have hLook : bt.lookupForced? 2 = some (.mulChecked 3 3 5) := rfl
        dsimp only [stepBt, signedCrossZeroStep, branch]
        rw [hBb, hLook, hGet]
        dsimp only
        cases (mulWithOverflowS .u8 (toBiased .u8 acc) 3).2 <;> rfl)
      (fun s acc r hInv _ _ _ hILo hIHi hRlt => by
        dsimp only [branch]
        refine wpUntilFuel_here (ops := MirWpOps.ofDetStep stepBt (fun st => some st.bb)) ?_
        have hBiLo : 110 ≤ toBiased .u8 r :=
          Nat.le_of_add_le_add_right (show 110 + 384 ≤ toBiased .u8 r + 384 from hILo)
        have hBiHi : toBiased .u8 r ≤ 140 :=
          Nat.le_of_add_le_add_right (show toBiased .u8 r + 384 ≤ 140 + 384 from hIHi)
        have hInvR : toBiased .u8 (toBiased .u8 r) = r := by
          rw [toBiased_involutive, Nat.mod_eq_of_lt hRlt]
        have hGoal :=
          stageIntervalStateInv_set_acc (fops := ocjFrameOps.signedView)
            (OvfCastFrameOps.signedView_lawful ocjFrameOps_lawful) (by rfl)
            (spec₂ := ⟨3, .u8, 110, 140⟩) hInv hBiLo hBiHi (Nat.le_of_ble_eq_true rfl)
        change StageIntervalStateInv ocjFrameOps.signedView base ids ⟨3, .u8, 110, 140⟩
          { bb := 3, locals := listSetAt s.locals 0 (.scalar .u8 (toBiased .u8 (toBiased .u8 r))) }
          at hGoal
        rw [hInvR] at hGoal
        exact hGoal)
      (fun s _ _ _ _ _ _ => by
        dsimp only [branch]
        refine wpUntilFuel_step (ops := MirWpOps.ofDetStep stepBt (fun st => some st.bb)) ?_
        change (StepOutcome.done (State := OcjState) (Fault := Unit) 999).wp _ _ _
        dsimp only [StepOutcome.wp]
        rfl)
  have hS3 :
      OvfCastStageCut ocjFrameOps.signedView stepBt base ids (fun o => Nat.beq o 999)
        ⟨3, .u8, 110, 140⟩ ⟨4, .u16, 32750, 32780⟩ 1 :=
    ovfCastStageCut_widen_signed_interval (fops := ocjFrameOps) (step := stepBt)
      ocjFrameOps_lawful (by rfl) (Nat.le_of_ble_eq_true rfl)
      (Nat.le_of_ble_eq_true rfl)
      (fun s accB hInv hAccGet _ _ => by
        have hBb : s.bb = 3 := hInv.1
        have hGet : listGet? s.locals 0 = some (.scalar .u8 (toBiased .u8 accB)) := hAccGet
        have hLook : bt.lookupForced? 3 = some (.widenI8ToI16 4) := rfl
        dsimp only [stepBt, signedCrossZeroStep]
        rw [hBb, hLook, hGet]
        rfl)
  have hAllBt := ovfCastStageCut_compose (ovfCastStageCut_compose (ovfCastStageCut_compose hS0 hS1) hS2) hS3
  have hAllList :=
    ovfCastStageCut_of_validBlockTree hValid ocjFrameOps.signedView signedCrossZeroStep
      (fun f g s hEq => by unfold signedCrossZeroStep; rw [hEq s.bb]) hAllBt
  have hEntry :
      StageIntervalStateInv ocjFrameOps.signedView base ids ⟨0, .u8, 123, 133⟩
        { bb := 0, locals := base } :=
    ⟨rfl, rfl, ⟨accB, rfl, hLo, hHi, Nat.le_of_ble_eq_true rfl⟩,
     fun _ _ _ _ _ => rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · exact ovfCastStageCut_to_wpOutcome hEntry hAllList
      (fun o hEq => Or.inr (Nat.eq_of_beq_eq_true hEq))
      (fun s hInv => by
        have hBb : s.bb = 4 := hInv.1
        refine wpUntil_step
          (ops := MirWpOps.ofDetStep (signedCrossZeroStep (listGet? signedCrossZeroBlocks))
            (fun st => some st.bb)) ?_
        change (signedCrossZeroStep (listGet? signedCrossZeroBlocks) s).wp _ _ _
        dsimp only [signedCrossZeroStep]
        rw [hBb]
        exact Or.inl rfl)
  · exact subWithOverflowS_biased_overflow_of_out_of_range .u8
      (Nat.le_of_ble_eq_true rfl) (Or.inl (Nat.le_of_ble_eq_true rfl))
  · exact mulWithOverflowS_biased_overflow_of_out_of_range_nonneg .u8
      (Nat.le_of_ble_eq_true rfl) (Nat.le_of_ble_eq_true rfl)
      (Or.inl (Nat.le_of_ble_eq_true rfl))

end Anneal.ParametricCore

