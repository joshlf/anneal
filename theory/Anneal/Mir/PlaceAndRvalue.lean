/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Sequence
import Trusted.MirAst
import Trusted.MirSemantics
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators

open Trusted.Sequence
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics

namespace Anneal.Mir.PlaceAndRvalue

/-!
# Anneal MIR Value-Tree Place Projections, `CharToInt`, `NullaryOp`, and Stateful Statement Semantics

This module formalizes the four semantic components lowered and evaluated in
`crates/anneal-mir` (`ws-mir-lower-place-proj-nullary-stmt`) and proves their
soundness invariants, lens laws, and step correspondence/refinement against
`Trusted.Rustc.V2026_06_01.MirSemantics`:

1. **Section 1 — Pure Value-Tree Projections & Lens Laws**:
   - Normalized value-tree projection evaluators (`evalConstantIndex`,
     `evalValueProjRead`, `evalValueProjWrite`) covering `.field`, `.downcast`
     (requiring an immediately following `.field` step), `.index`,
     `.constantIndex` (`fromEnd = false` and `fromEnd = true`), and `.subslice`
     (`fromEnd = false` and `fromEnd = true`), failing closed on `.deref`.
   - Full Get-Put (`evalValueProjWrite_read_same`), Put-Get
     (`evalValueProjRead_write_same`), Put-Put
     (`evalValueProjWrite_write_same`), and Disjoint-Field / Disjoint-Index
     commutativity lens laws over arbitrary projection paths.
   - Exact correspondence and refinement theorems linking `evalValueProjRead`
     and `evalValueProjWrite` to
     `Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue` and
     `writeProjectedValue`.

2. **Section 2 — `CastKind.charToInt` Formalization & `evalRvalue` Correspondence**:
   - Unicode scalar validity (`isValidUnicodeScalar`), equivalence to
     `Trusted.MirSemantics.isValidCharCode`, surrogate (`0xD800..=0xDFFF`) and
     out-of-range (`> 0x10FFFF`) rejection, `evalCharToInt` /
     `evalCharToIntByKind`, bitwidth bounds (`ScalarInt.inRange`), lossless
     identity for target widths `>= 4` bytes, low-bit truncation for `u8`/`i8`
     (`1` byte) and `u16`/`i16` (`2` bytes), and step correspondence with
     `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue` on
     `.cast .intToInt op targetTy` for unsigned 4-byte `char` operands.

3. **Section 3 — `Rvalue.nullaryOp` Formalization, Canonical Tuple `OffsetOf`, & Refinement**:
   - Alignment rounding (`alignUp`), canonical tuple field-offset resolution
     (`resolveTupleOffsetOf`), and `evalNullaryOp` (`.sizeOf`, `.alignOf`,
     `.offsetOf`, `.ubChecks`).
   - Arithmetic and layout invariants (non-zero tuple variant rejection,
     out-of-bounds field rejection, prefix offset monotonicity, field offset +
     field size bounded by tuple size, `ubChecks` evaluating to `⟨1, 1⟩`), plus
     unsupported-shrinking refinement against
     `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue (.nullaryOp op ty)` and
     agreement with `Terminators.lean`'s `.ubChecks` intrinsic.

4. **Section 4 — Stateful `LocalSlotState`, `D9` `PlaceMention`, `D13b` Partial Shells, `SetDiscriminant`, `Assume` & `Statements.lean` Correspondence**:
   - Per-field initialization slots (`FieldSlot`), partially initialized
     tuple/struct/enum shells (`PartialAggregate` with `discriminantSet` tag
     gating and `tryIntoValue?` promotion), and `LocalSlotState` (`dead`,
     `uninit`, `partialShell`, `init`).
   - Partial-shell soundness theorems: unwritten `()` sibling fields and tagless
     enum shells never promote (`tryIntoValue? = .none`) and fault on reads
     (eliminating `.unit`-placeholder false accepts), array element writes on
     `.uninit` fault (`c6d2ad74`), and full field + tag initialization promotes
     to `Value.aggregate variantIdx fields`.
   - Statement-level correspondence theorems with
     `Trusted.Rustc.V2026_06_01.MirSemantics` (`evalOperand` bare vs. projected
     `.move`, `placeMentionOperandsInit` / `evalStmt` `.placeMention`,
     `.intrinsic (.assume op)`, `.storageLive`, `.storageDead`,
     `.setDiscriminant`, and `D13b` `.assign`).
-/

/-! ## Section 1: Pure Value-Tree Projections, Lens Laws & `Places.lean` Correspondence -/

/-- Simplification bridge: `get? xs i` is `xs[i]?`. -/
@[simp]
theorem get?_eq_getElem? {α : Type} (xs : List α) (i : Nat) :
    get? xs i = xs[i]? := rfl

/-- Simplification bridge: `length xs` is `xs.length`. -/
@[simp]
theorem length_eq_list_length {α : Type} (xs : List α) :
    length xs = xs.length := rfl

/-- `appendValueList` is definitionally `List.append` (`++`). -/
@[simp]
theorem appendValueList_eq_append (xs ys : List Value) :
    appendValueList xs ys = xs ++ ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendValueList, ih]

/-- `takeValues` is definitionally `List.take`. -/
@[simp]
theorem takeValues_eq_take (n : Nat) (xs : List Value) :
    takeValues n xs = xs.take n := by
  induction n generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp [takeValues, ih]

/-- `dropValues` is definitionally `List.drop`. -/
@[simp]
theorem dropValues_eq_drop (n : Nat) (xs : List Value) :
    dropValues n xs = xs.drop n := by
  induction n generalizing xs with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs => simp [dropValues, ih]

/-- `set?` succeeds if and only if `i < xs.length` and `xs' = xs.set i v`. -/
theorem set?_eq_some_iff {α : Type} {xs : List α} {i : Nat} {v : α} {xs' : List α} :
    set? xs i v = .some xs' ↔ (i < xs.length ∧ xs.set i v = xs') := by
  unfold set?
  split
  · next h =>
    constructor
    · intro hEq
      injection hEq with hEq'
      exact ⟨h, hEq'⟩
    · rintro ⟨_, rfl⟩
      rfl
  · next h =>
    constructor
    · intro hEq; nomatch hEq
    · rintro ⟨hLt, _⟩; exact False.elim (h hLt)

/-- `set?` preserves list length. -/
theorem length_of_set? {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : set? xs i v = .some xs') :
    xs'.length = xs.length := by
  rcases set?_eq_some_iff.mp h with ⟨_, rfl⟩
  exact List.length_set

/-- Reading at index `i` after `set? xs i v = .some xs'` returns `.some v`. -/
theorem get?_of_set?_same {α : Type} {xs xs' : List α} {i : Nat} {v : α}
    (h : set? xs i v = .some xs') :
    get? xs' i = .some v := by
  rcases set?_eq_some_iff.mp h with ⟨hLt, rfl⟩
  simp [hLt]

/-- Reading at index `j ≠ i` after `set? xs i v = .some xs'` returns `get? xs j`. -/
theorem get?_of_set?_ne {α : Type} {xs xs' : List α} {i j : Nat} {v : α}
    (h : set? xs i v = .some xs') (hNe : i ≠ j) :
    get? xs' j = get? xs j := by
  rcases set?_eq_some_iff.mp h with ⟨_, rfl⟩
  simp [List.getElem?_set_ne hNe]

/-- Writing back the element read from `get? xs i = .some v` returns `.some xs`. -/
theorem set?_self_of_get?_eq {α : Type} {xs : List α} {i : Nat} {v : α}
    (h : get? xs i = .some v) :
    set? xs i v = .some xs := by
  simp only [get?_eq_getElem?] at h
  have hLt : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  have hVal : xs[i] = v := (List.getElem?_eq_some_iff.mp h).2
  exact set?_eq_some_iff.mpr ⟨hLt, by rw [← hVal, List.set_getElem_self]⟩

/-- Two consecutive `set?` updates at the same index `i` equal the second `set?`. -/
theorem set?_of_set?_same {α : Type} {xs xs1 xs2 : List α} {i : Nat} {v1 v2 : α}
    (h1 : set? xs i v1 = .some xs1)
    (h2 : set? xs1 i v2 = .some xs2) :
    set? xs i v2 = .some xs2 := by
  rcases set?_eq_some_iff.mp h1 with ⟨hLt1, rfl⟩
  rcases set?_eq_some_iff.mp h2 with ⟨_, rfl⟩
  rw [List.set_set]
  exact set?_eq_some_iff.mpr ⟨hLt1, rfl⟩

/-- Helper: `take n (xs ++ ys) = xs` whenever `xs.length = n`. -/
private theorem take_append_exact :
    ∀ (xs ys : List Value) (n : Nat),
      xs.length = n → (xs ++ ys).take n = xs
  | [], _, 0, _ => rfl
  | _ :: _, _, 0, h => nomatch h
  | [], _, _ + 1, h => nomatch h
  | x :: xs, ys, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [take_append_exact xs ys n h]

/-- Helper: `drop n (xs ++ ys) = ys` whenever `xs.length = n`. -/
private theorem drop_append_exact :
    ∀ (xs ys : List Value) (n : Nat),
      xs.length = n → (xs ++ ys).drop n = ys
  | [], _, 0, _ => rfl
  | _ :: _, _, 0, h => nomatch h
  | [], _, _ + 1, h => nomatch h
  | _ :: xs, ys, n + 1, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp [drop_append_exact xs ys n h]

/-- Compute the exclusive upper bound index of a `Subslice` projection on a list
of length `len`. -/
@[reducible]
def subsliceEndIdx (len toIdx : Nat) (fromEnd : Bool) : Nat :=
  match fromEnd with
  | true => Nat.sub len toIdx
  | false => toIdx

/-- When `toIdx <= len`, `subsliceEndIdx len toIdx fromEnd <= len`. -/
theorem subsliceEndIdx_le {len toIdx : Nat} {fromEnd : Bool} (hTo : toIdx ≤ len) :
    subsliceEndIdx len toIdx fromEnd ≤ len := by
  cases fromEnd <;> dsimp [subsliceEndIdx] <;> omega

/-- `extractSubslice` succeeds when `toIdx <= elems.length`, `fromIdx <= endIdx`,
and returns `(elems.drop fromIdx).take (endIdx - fromIdx)`. -/
theorem extractSubslice_eq_some_iff
    (elems : List Value)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool)
    (subElems : List Value) :
    let len := elems.length
    let endIdx := subsliceEndIdx len toIdx fromEnd
    extractSubslice elems fromIdx toIdx fromEnd = .some subElems ↔
      (toIdx ≤ len ∧ fromIdx ≤ endIdx ∧
       (elems.drop fromIdx).take (endIdx - fromIdx) = subElems) := by
  dsimp only
  unfold extractSubslice
  simp only [length_eq_list_length, takeValues_eq_take, dropValues_eq_drop]
  cases hTo : Nat.ble toIdx elems.length with
  | false =>
    have hNotTo : ¬ toIdx ≤ elems.length := by
      intro hLe
      have := Nat.ble_eq_true_of_le hLe
      rw [hTo] at this
      nomatch this
    simp [hNotTo]
  | true =>
    have hToLe : toIdx ≤ elems.length := Nat.le_of_ble_eq_true hTo
    dsimp only
    change (match Nat.ble fromIdx (subsliceEndIdx elems.length toIdx fromEnd) with
      | false => none
      | true => some (List.take (Nat.sub (subsliceEndIdx elems.length toIdx fromEnd) fromIdx) (List.drop fromIdx elems))) =
        some subElems ↔ _
    cases hFrom : Nat.ble fromIdx (subsliceEndIdx elems.length toIdx fromEnd) with
    | false =>
      have hNotFrom : ¬ fromIdx ≤ subsliceEndIdx elems.length toIdx fromEnd := by
        intro hLe
        have := Nat.ble_eq_true_of_le hLe
        rw [hFrom] at this
        nomatch this
      simp [hToLe, hNotFrom]
    | true =>
      have hFromLe : fromIdx ≤ subsliceEndIdx elems.length toIdx fromEnd :=
        Nat.le_of_ble_eq_true hFrom
      dsimp only
      constructor
      · intro hSome
        injection hSome with hEq
        exact ⟨hToLe, hFromLe, hEq⟩
      · rintro ⟨_, _, rfl⟩
        rfl

/-- Equivalence between Episode 1's `fromIdx + toIdx <= len` bound for
`Subslice { from, to, from_end: true }` and `extractSubslice`'s
`toIdx <= len ∧ fromIdx <= len - toIdx` check. -/
theorem subslice_fromEnd_bounds_iff (fromIdx toIdx len : Nat) :
    fromIdx + toIdx ≤ len ↔ (toIdx ≤ len ∧ fromIdx ≤ len - toIdx) := by
  omega

/-- `replaceSubslice` characterization in terms of `List.take` and `List.drop`. -/
theorem replaceSubslice_eq_some_iff
    (elems : List Value)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool)
    (newSubElems elems' : List Value) :
    let len := elems.length
    let endIdx := subsliceEndIdx len toIdx fromEnd
    replaceSubslice elems fromIdx toIdx fromEnd newSubElems = .some elems' ↔
      (toIdx ≤ len ∧ fromIdx ≤ endIdx ∧
       newSubElems.length = endIdx - fromIdx ∧
       elems.take fromIdx ++ (newSubElems ++ elems.drop endIdx) = elems') := by
  dsimp only
  unfold replaceSubslice
  simp only [length_eq_list_length, takeValues_eq_take, dropValues_eq_drop,
    appendValueList_eq_append]
  cases hTo : Nat.ble toIdx elems.length with
  | false =>
    have hNotTo : ¬ toIdx ≤ elems.length := by
      intro hLe
      have := Nat.ble_eq_true_of_le hLe
      rw [hTo] at this
      nomatch this
    simp [hNotTo]
  | true =>
    have hToLe : toIdx ≤ elems.length := Nat.le_of_ble_eq_true hTo
    dsimp only
    change (match Nat.ble fromIdx (subsliceEndIdx elems.length toIdx fromEnd) with
      | false => none
      | true =>
        match Nat.beq newSubElems.length (Nat.sub (subsliceEndIdx elems.length toIdx fromEnd) fromIdx) with
        | false => none
        | true =>
          some (List.take fromIdx elems ++ (newSubElems ++ List.drop (subsliceEndIdx elems.length toIdx fromEnd) elems))) =
        some elems' ↔ _
    cases hFrom : Nat.ble fromIdx (subsliceEndIdx elems.length toIdx fromEnd) with
    | false =>
      have hNotFrom : ¬ fromIdx ≤ subsliceEndIdx elems.length toIdx fromEnd := by
        intro hLe
        have := Nat.ble_eq_true_of_le hLe
        rw [hFrom] at this
        nomatch this
      simp [hToLe, hNotFrom]
    | true =>
      have hFromLe : fromIdx ≤ subsliceEndIdx elems.length toIdx fromEnd :=
        Nat.le_of_ble_eq_true hFrom
      dsimp only
      cases hLen : Nat.beq newSubElems.length
          (Nat.sub (subsliceEndIdx elems.length toIdx fromEnd) fromIdx) with
      | false =>
        have hNotLen : newSubElems.length ≠
            subsliceEndIdx elems.length toIdx fromEnd - fromIdx := by
          intro hEq
          have hBeq : Nat.beq newSubElems.length
              (Nat.sub (subsliceEndIdx elems.length toIdx fromEnd) fromIdx) = true :=
            Nat.beq_eq.mpr hEq
          rw [hLen] at hBeq
          nomatch hBeq
        simp [hToLe, hFromLe, hNotLen]
      | true =>
        have hLenEq : newSubElems.length =
            subsliceEndIdx elems.length toIdx fromEnd - fromIdx :=
          Nat.eq_of_beq_eq_true hLen
        dsimp only
        constructor
        · intro hSome
          injection hSome with hEq
          exact ⟨hToLe, hFromLe, hLenEq, hEq⟩
        · rintro ⟨_, _, _, rfl⟩
          rfl

/-- Replacing a subslice with the exact subslice extracted from `elems` returns `elems`. -/
theorem replaceSubslice_extractSubslice_self
    {elems subElems : List Value}
    {fromIdx toIdx : Nat}
    {fromEnd : Bool}
    (hExt : extractSubslice elems fromIdx toIdx fromEnd = .some subElems) :
    replaceSubslice elems fromIdx toIdx fromEnd subElems = .some elems := by
  rcases (extractSubslice_eq_some_iff elems fromIdx toIdx fromEnd subElems).mp hExt with
    ⟨hTo, hFrom, rfl⟩
  have hEndLe : subsliceEndIdx elems.length toIdx fromEnd ≤ elems.length :=
    subsliceEndIdx_le hTo
  have hSubLen :
      ((elems.drop fromIdx).take (subsliceEndIdx elems.length toIdx fromEnd - fromIdx)).length =
        subsliceEndIdx elems.length toIdx fromEnd - fromIdx := by
    rw [List.length_take, List.length_drop]
    omega
  have hDropDrop :
      (elems.drop fromIdx).drop (subsliceEndIdx elems.length toIdx fromEnd - fromIdx) =
        elems.drop (subsliceEndIdx elems.length toIdx fromEnd) := by
    rw [List.drop_drop]
    congr 1
    omega
  have hTail :
      (elems.drop fromIdx).take (subsliceEndIdx elems.length toIdx fromEnd - fromIdx) ++
          elems.drop (subsliceEndIdx elems.length toIdx fromEnd) =
        elems.drop fromIdx := by
    rw [← hDropDrop, List.take_append_drop]
  have hFull :
      elems.take fromIdx ++
          ((elems.drop fromIdx).take (subsliceEndIdx elems.length toIdx fromEnd - fromIdx) ++
            elems.drop (subsliceEndIdx elems.length toIdx fromEnd)) =
        elems := by
    rw [hTail, List.take_append_drop]
  exact (replaceSubslice_eq_some_iff elems fromIdx toIdx fromEnd _ elems).mpr
    ⟨hTo, hFrom, hSubLen, hFull⟩

/-- Extracting a subslice after `replaceSubslice` at the same bounds returns `newSubElems`. -/
theorem extractSubslice_replaceSubslice_same
    {elems newSubElems elems' : List Value}
    {fromIdx toIdx : Nat}
    {fromEnd : Bool}
    (hRep : replaceSubslice elems fromIdx toIdx fromEnd newSubElems = .some elems') :
    extractSubslice elems' fromIdx toIdx fromEnd = .some newSubElems := by
  rcases (replaceSubslice_eq_some_iff elems fromIdx toIdx fromEnd newSubElems elems').mp hRep with
    ⟨hTo, hFrom, hSubLen, rfl⟩
  have hEndLe : subsliceEndIdx elems.length toIdx fromEnd ≤ elems.length :=
    subsliceEndIdx_le hTo
  have hTakeLen : (elems.take fromIdx).length = fromIdx := by
    rw [List.length_take]
    omega
  have hTotalLen :
      (elems.take fromIdx ++
          (newSubElems ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd))).length =
        elems.length := by
    rw [List.length_append, List.length_append, hTakeLen, hSubLen, List.length_drop]
    omega
  have hDropPrefix :
      (elems.take fromIdx ++
          (newSubElems ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd))).drop fromIdx =
        newSubElems ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd) :=
    drop_append_exact (elems.take fromIdx) _ fromIdx hTakeLen
  have hTakeMid :
      (newSubElems ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd)).take
          (subsliceEndIdx elems.length toIdx fromEnd - fromIdx) =
        newSubElems :=
    take_append_exact newSubElems _ _ hSubLen
  apply (extractSubslice_eq_some_iff _ fromIdx toIdx fromEnd newSubElems).mpr
  rw [hTotalLen]
  exact ⟨hTo, hFrom, by rw [hDropPrefix, hTakeMid]⟩

/-- Two consecutive `replaceSubslice` updates at the same window equal the second `replaceSubslice`. -/
theorem replaceSubslice_replaceSubslice_same
    {elems sub1 sub2 elems1 elems2 : List Value}
    {fromIdx toIdx : Nat}
    {fromEnd : Bool}
    (h1 : replaceSubslice elems fromIdx toIdx fromEnd sub1 = .some elems1)
    (h2 : replaceSubslice elems1 fromIdx toIdx fromEnd sub2 = .some elems2) :
    replaceSubslice elems fromIdx toIdx fromEnd sub2 = .some elems2 := by
  rcases (replaceSubslice_eq_some_iff elems fromIdx toIdx fromEnd sub1 elems1).mp h1 with
    ⟨hTo1, hFrom1, hLen1, rfl⟩
  have hEndLe : subsliceEndIdx elems.length toIdx fromEnd ≤ elems.length :=
    subsliceEndIdx_le hTo1
  have hTakeLen : (elems.take fromIdx).length = fromIdx := by
    rw [List.length_take]
    omega
  have hTotalLen :
      (elems.take fromIdx ++
          (sub1 ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd))).length =
        elems.length := by
    rw [List.length_append, List.length_append, hTakeLen, hLen1, List.length_drop]
    omega
  rcases (replaceSubslice_eq_some_iff _ fromIdx toIdx fromEnd sub2 elems2).mp h2 with
    ⟨_, _, hLen2, rfl⟩
  rw [hTotalLen] at hLen2
  have hTakePrefix :
      (elems.take fromIdx ++
          (sub1 ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd))).take fromIdx =
        elems.take fromIdx :=
    take_append_exact (elems.take fromIdx) _ fromIdx hTakeLen
  have hDropPrefix :
      (elems.take fromIdx ++
          (sub1 ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd))).drop fromIdx =
        sub1 ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd) :=
    drop_append_exact (elems.take fromIdx) _ fromIdx hTakeLen
  have hDropSuffix :
      (elems.take fromIdx ++
          (sub1 ++ elems.drop (subsliceEndIdx elems.length toIdx fromEnd))).drop
          (subsliceEndIdx elems.length toIdx fromEnd) =
        elems.drop (subsliceEndIdx elems.length toIdx fromEnd) := by
    have hSplit :
        subsliceEndIdx elems.length toIdx fromEnd =
          fromIdx + (subsliceEndIdx elems.length toIdx fromEnd - fromIdx) := by omega
    conv =>
      lhs
      arg 1
      rw [hSplit]
    rw [← List.drop_drop, hDropPrefix]
    exact drop_append_exact sub1 _ _ hLen1
  apply (replaceSubslice_eq_some_iff elems fromIdx toIdx fromEnd sub2 _).mpr
  refine ⟨hTo1, hFrom1, hLen2, ?_⟩
  rw [hTotalLen, hTakePrefix, hDropSuffix]

/-- Check whether a projection list starts with `.field idx ty`, used to enforce
`rustc`'s MIR invariant (`compiler/rustc_middle/src/mir/syntax.rs`) and
Episode 1's `[adv A3]` rule that every `ProjectionElem.downcast` is immediately
followed by a `ProjectionElem.field`. -/
@[reducible]
def isFieldHead : List ProjectionElem → Bool
  | .field _ _ :: _ => true
  | _ => false

/-- Resolve a `ProjectionElem.constantIndex offset minLen fromEnd` against an
array or subslice window of length `len`, matching Episode 1's
`resolve_constant_index`:
- Requires `minLen <= len`.
- When `fromEnd = true`, requires `1 <= offset ∧ offset <= len` and returns
  `len - offset`.
- When `fromEnd = false`, requires `offset < len` and returns `offset`. -/
def evalConstantIndex (len offset minLen : Nat) (fromEnd : Bool) : Option Nat :=
  match Nat.ble minLen len with
  | false => .none
  | true =>
    match fromEnd with
    | true =>
      match Bool.and (Nat.ble 1 offset) (Nat.ble offset len) with
      | true => .some (Nat.sub len offset)
      | false => .none
    | false =>
      match Nat.ble (Nat.succ offset) len with
      | true => .some offset
      | false => .none

/-- Whenever `evalConstantIndex len offset minLen fromEnd = .some idx`,
`idx < len` and `minLen <= len`. -/
theorem evalConstantIndex_lt_len
    {len offset minLen idx : Nat}
    {fromEnd : Bool}
    (h : evalConstantIndex len offset minLen fromEnd = .some idx) :
    minLen ≤ len ∧ idx < len := by
  unfold evalConstantIndex at h
  cases hMin : Nat.ble minLen len with
  | false => rw [hMin] at h; nomatch h
  | true =>
    have hMinLe : minLen ≤ len := Nat.le_of_ble_eq_true hMin
    rw [hMin] at h
    dsimp only at h
    cases fromEnd with
    | false =>
      cases hOff : Nat.ble (Nat.succ offset) len with
      | false => rw [hOff] at h; nomatch h
      | true =>
        rw [hOff] at h
        injection h with hEq
        have hLt : offset < len := Nat.le_of_ble_eq_true hOff
        omega
    | true =>
      cases h1 : Nat.ble 1 offset with
      | false => rw [h1] at h; nomatch h
      | true =>
        cases h2 : Nat.ble offset len with
        | false => rw [h1, h2] at h; nomatch h
        | true =>
          rw [h1, h2] at h
          injection h with hEq
          change len - offset = idx at hEq
          have hGe1 : 1 ≤ offset := Nat.le_of_ble_eq_true h1
          have hLeLen : offset ≤ len := Nat.le_of_ble_eq_true h2
          omega

/-- Normalized pure value-tree projection read evaluator (`eval_place_read` /
`read_projected_mir_value` in `crates/anneal-mir/src/lower/rvalue.rs`):
- Traverses `.field`, `.downcast` (requiring an immediately following `.field`),
  `.index`, `.constantIndex` (`fromEnd = false/true`), and `.subslice`
  (`fromEnd = false/true`) over `Value.aggregate`.
- Rejects out-of-bounds fields/indices, variant mismatches, trailing or
  consecutive `Downcast` steps, and non-aggregate receivers with `.ub`.
- Fails closed with `.unsupported` on `.deref`, `.opaqueCast`, and
  `.unwrapUnsafeBinder`. -/
def evalValueProjRead
    (locals : List LocalSlot) :
    Value → List ProjectionElem → ProjReadResult
  | val, .nil => .ok val
  | .aggregate _ fields, .field idx _ :: rest =>
    match get? fields idx with
    | .some fieldVal => evalValueProjRead locals fieldVal rest
    | .none => .ub
  | _, .field _ _ :: _ => .ub
  | .aggregate actualVariant fields, .downcast _ variantIdx :: rest =>
    match Bool.and (isFieldHead rest) (Nat.beq actualVariant variantIdx) with
    | true => evalValueProjRead locals (.aggregate actualVariant fields) rest
    | false => .ub
  | _, .downcast _ _ :: _ => .ub
  | .aggregate .zero fields, .index idxLocal :: rest =>
    match get? locals idxLocal with
    | .some (.init (.scalar sc)) =>
      match get? fields sc.bits with
      | .some elemVal => evalValueProjRead locals elemVal rest
      | .none => .ub
    | _ => .ub
  | _, .index _ :: _ => .ub
  | .aggregate .zero fields, .constantIndex offset minLen fromEnd :: rest =>
    match evalConstantIndex (length fields) offset minLen fromEnd with
    | .some idx =>
      match get? fields idx with
      | .some elemVal => evalValueProjRead locals elemVal rest
      | .none => .ub
    | .none => .ub
  | _, .constantIndex _ _ _ :: _ => .ub
  | .aggregate .zero fields, .subslice fromIdx toIdx fromEnd :: rest =>
    match extractSubslice fields fromIdx toIdx fromEnd with
    | .some subElems =>
      evalValueProjRead locals (.aggregate .zero subElems) rest
    | .none => .ub
  | _, .subslice _ _ _ :: _ => .ub
  | _, _ :: _ => .unsupported

/-- Normalized pure value-tree projection write evaluator (`eval_place_write` /
`write_projected_mir_value` in `crates/anneal-mir/src/lower/rvalue.rs`):
- Updates the sub-value at `proj` inside `val` with `newVal` in place,
  requiring in-bounds `.field` indices (never extending with `.unit` padding),
  requiring `.downcast` to be immediately followed by `.field`, validating
  `.index`, `.constantIndex`, and `.subslice` bounds, and failing closed with
  `.unsupported` on `.deref`, `.opaqueCast`, and `.unwrapUnsafeBinder`. -/
def evalValueProjWrite
    (locals : List LocalSlot) :
    Value → List ProjectionElem → Value → ProjWriteResult
  | _, .nil, newVal => .ok newVal
  | .aggregate variantIdx fields, .field idx _ :: rest, newVal =>
    match get? fields idx with
    | .some oldFieldVal =>
      match evalValueProjWrite locals oldFieldVal rest newVal with
      | .ok updatedFieldVal =>
        match set? fields idx updatedFieldVal with
        | .some fields' => .ok (.aggregate variantIdx fields')
        | .none => .ub
      | .ub => .ub
      | .unsupported => .unsupported
    | .none => .ub
  | _, .field _ _ :: _, _ => .ub
  | .aggregate actualVariant fields, .downcast _ variantIdx :: rest, newVal =>
    match Bool.and (isFieldHead rest) (Nat.beq actualVariant variantIdx) with
    | true =>
      evalValueProjWrite locals (.aggregate actualVariant fields) rest newVal
    | false => .ub
  | _, .downcast _ _ :: _, _ => .ub
  | .aggregate .zero fields, .index idxLocal :: rest, newVal =>
    match get? locals idxLocal with
    | .some (.init (.scalar sc)) =>
      match get? fields sc.bits with
      | .some oldElemVal =>
        match evalValueProjWrite locals oldElemVal rest newVal with
        | .ok updatedElemVal =>
          match set? fields sc.bits updatedElemVal with
          | .some fields' => .ok (.aggregate .zero fields')
          | .none => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub
    | _ => .ub
  | _, .index _ :: _, _ => .ub
  | .aggregate .zero fields, .constantIndex offset minLen fromEnd :: rest, newVal =>
    match evalConstantIndex (length fields) offset minLen fromEnd with
    | .some idx =>
      match get? fields idx with
      | .some oldElemVal =>
        match evalValueProjWrite locals oldElemVal rest newVal with
        | .ok updatedElemVal =>
          match set? fields idx updatedElemVal with
          | .some fields' => .ok (.aggregate .zero fields')
          | .none => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub
    | .none => .ub
  | _, .constantIndex _ _ _ :: _, _ => .ub
  | .aggregate .zero fields, .subslice fromIdx toIdx fromEnd :: rest, newVal =>
    match extractSubslice fields fromIdx toIdx fromEnd with
    | .some subElems =>
      match evalValueProjWrite locals (.aggregate .zero subElems) rest newVal with
      | .ok (.aggregate .zero updatedSubElems) =>
        match replaceSubslice fields fromIdx toIdx fromEnd updatedSubElems with
        | .some fields' => .ok (.aggregate .zero fields')
        | .none => .ub
      | .ok _ => .ub
      | .ub => .ub
      | .unsupported => .unsupported
    | .none => .ub
  | _, .subslice _ _ _ :: _, _ => .ub
  | _, _ :: _, _ => .unsupported

/-- Writing along a path that begins with `.field` preserves the outer
`Value.aggregate` constructor and its `variantIdx`. -/
theorem evalValueProjWrite_preserves_aggregate_of_isFieldHead
    {locals : List LocalSlot}
    {variantIdx : VariantIdx}
    {fields : List Value}
    {proj : List ProjectionElem}
    {newVal val' : Value}
    (hHead : isFieldHead proj = true)
    (hWrite : evalValueProjWrite locals (.aggregate variantIdx fields) proj newVal = .ok val') :
    ∃ fields', val' = .aggregate variantIdx fields' ∧ fields'.length = fields.length := by
  cases proj with
  | nil => nomatch hHead
  | cons p rest =>
    cases p with
    | field idx ty =>
      dsimp only [evalValueProjWrite] at hWrite
      cases hGet : get? fields idx with
      | none => rw [hGet] at hWrite; nomatch hWrite
      | some oldFieldVal =>
        rw [hGet] at hWrite
        dsimp only at hWrite
        cases hRec : evalValueProjWrite locals oldFieldVal rest newVal with
        | ub => rw [hRec] at hWrite; nomatch hWrite
        | unsupported => rw [hRec] at hWrite; nomatch hWrite
        | ok updatedFieldVal =>
          rw [hRec] at hWrite
          dsimp only at hWrite
          cases hSet : set? fields idx updatedFieldVal with
          | none => rw [hSet] at hWrite; nomatch hWrite
          | some fields' =>
            rw [hSet] at hWrite
            injection hWrite with hEq
            exact ⟨fields', hEq.symm, length_of_set? hSet⟩
    | _ => nomatch hHead

/-- Rejecting trailing and consecutive `Downcast` projections: any path ending
in `.downcast` or containing `.downcast :: .downcast` fails with `.ub` on both
`evalValueProjRead` and `evalValueProjWrite`. -/
theorem evalValueProj_rejects_invalid_downcast
    (locals : List LocalSlot)
    (val newVal : Value)
    (vName1 vName2 : Option String)
    (v1 v2 : VariantIdx)
    (rest : List ProjectionElem) :
    evalValueProjRead locals val [.downcast vName1 v1] = .ub ∧
    evalValueProjWrite locals val [.downcast vName1 v1] newVal = .ub ∧
    evalValueProjRead locals val (.downcast vName1 v1 :: .downcast vName2 v2 :: rest) = .ub ∧
    evalValueProjWrite locals val (.downcast vName1 v1 :: .downcast vName2 v2 :: rest) newVal = .ub := by
  cases val <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Rejecting `.deref` in pure value-tree projection evaluation: any projection
starting with `.deref` returns `.unsupported` in both `evalValueProjRead` and
`evalValueProjWrite`. -/
theorem evalValueProj_deref_unsupported
    (locals : List LocalSlot)
    (val newVal : Value)
    (rest : List ProjectionElem) :
    evalValueProjRead locals val (.deref :: rest) = .unsupported ∧
    evalValueProjWrite locals val (.deref :: rest) newVal = .unsupported := by
  cases val <;> exact ⟨rfl, rfl⟩

/-- **Get-Put Lens Law (`evalValueProjWrite_read_same`)**:
For every projection path `proj`, local environment `locals`, root value `val`,
and projected value `subVal`, if reading `proj` from `val` yields `.ok subVal`,
then writing `subVal` back to `proj` in `val` yields `.ok val` unchanged. -/
theorem evalValueProjWrite_read_same :
    ∀ (proj : List ProjectionElem) (locals : List LocalSlot) (val subVal : Value),
      evalValueProjRead locals val proj = .ok subVal →
      evalValueProjWrite locals val proj subVal = .ok val := by
  intro proj
  induction proj with
  | nil =>
    intro locals val subVal hRead
    injection hRead with hEq
    subst hEq
    rfl
  | cons p rest ih =>
    intro locals val subVal hRead
    cases p with
    | field idx ty =>
      cases val with
      | aggregate variantIdx fields =>
        dsimp only [evalValueProjRead] at hRead
        dsimp only [evalValueProjWrite]
        cases hGet : get? fields idx with
        | none => rw [hGet] at hRead; nomatch hRead
        | some fieldVal =>
          rw [hGet] at hRead
          dsimp only at hRead ⊢
          rw [ih locals fieldVal subVal hRead]
          dsimp only
          rw [set?_self_of_get?_eq hGet]
      | _ => nomatch hRead
    | downcast vName variantIdx =>
      cases val with
      | aggregate actualVariant fields =>
        dsimp only [evalValueProjRead] at hRead
        dsimp only [evalValueProjWrite]
        cases hCond : Bool.and (isFieldHead rest) (Nat.beq actualVariant variantIdx) with
        | false => rw [hCond] at hRead; nomatch hRead
        | true =>
          rw [hCond] at hRead
          dsimp only at hRead ⊢
          exact ih locals (.aggregate actualVariant fields) subVal hRead
      | _ => nomatch hRead
    | index idxLocal =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          dsimp only [evalValueProjWrite]
          cases hLoc : get? locals idxLocal with
          | none => rw [hLoc] at hRead; nomatch hRead
          | some slot =>
            rw [hLoc] at hRead
            cases slot with
            | dead => nomatch hRead
            | uninit => nomatch hRead
            | init idxVal =>
              cases idxVal with
              | scalar sc =>
                dsimp only at hRead ⊢
                cases hElem : get? fields sc.bits with
                | none => rw [hElem] at hRead; nomatch hRead
                | some elemVal =>
                  rw [hElem] at hRead
                  dsimp only at hRead ⊢
                  rw [ih locals elemVal subVal hRead]
                  dsimp only
                  rw [set?_self_of_get?_eq hElem]
              | _ => nomatch hRead
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | constantIndex offset minLen fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          dsimp only [evalValueProjWrite]
          cases hIdx : evalConstantIndex (length fields) offset minLen fromEnd with
          | none => rw [hIdx] at hRead; nomatch hRead
          | some idx =>
            rw [hIdx] at hRead
            dsimp only at hRead ⊢
            cases hElem : get? fields idx with
            | none => rw [hElem] at hRead; nomatch hRead
            | some elemVal =>
              rw [hElem] at hRead
              dsimp only at hRead ⊢
              rw [ih locals elemVal subVal hRead]
              dsimp only
              rw [set?_self_of_get?_eq hElem]
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | subslice fromIdx toIdx fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          dsimp only [evalValueProjWrite]
          cases hExt : extractSubslice fields fromIdx toIdx fromEnd with
          | none => rw [hExt] at hRead; nomatch hRead
          | some subElems =>
            rw [hExt] at hRead
            dsimp only at hRead ⊢
            rw [ih locals (.aggregate .zero subElems) subVal hRead]
            dsimp only
            rw [replaceSubslice_extractSubslice_self hExt]
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | deref => cases val <;> nomatch hRead
    | opaqueCast _ => cases val <;> nomatch hRead
    | unwrapUnsafeBinder _ => cases val <;> nomatch hRead

/-- **Put-Get Lens Law (`evalValueProjRead_write_same`)**:
For every projection path `proj`, local environment `locals`, root value `val`,
written value `newVal`, and updated root value `val'`, if writing `newVal` to
`proj` in `val` succeeds with `.ok val'`, then reading `proj` back from `val'`
yields `.ok newVal`. -/
theorem evalValueProjRead_write_same :
    ∀ (proj : List ProjectionElem) (locals : List LocalSlot) (val newVal val' : Value),
      evalValueProjWrite locals val proj newVal = .ok val' →
      evalValueProjRead locals val' proj = .ok newVal := by
  intro proj
  induction proj with
  | nil =>
    intro locals val newVal val' hWrite
    injection hWrite with hEq
    subst hEq
    rfl
  | cons p rest ih =>
    intro locals val newVal val' hWrite
    cases p with
    | field idx ty =>
      cases val with
      | aggregate variantIdx fields =>
        dsimp only [evalValueProjWrite] at hWrite
        cases hGet : get? fields idx with
        | none => rw [hGet] at hWrite; nomatch hWrite
        | some oldFieldVal =>
          rw [hGet] at hWrite
          dsimp only at hWrite
          cases hRec : evalValueProjWrite locals oldFieldVal rest newVal with
          | ub => rw [hRec] at hWrite; nomatch hWrite
          | unsupported => rw [hRec] at hWrite; nomatch hWrite
          | ok updatedFieldVal =>
            rw [hRec] at hWrite
            dsimp only at hWrite
            cases hSet : set? fields idx updatedFieldVal with
            | none => rw [hSet] at hWrite; nomatch hWrite
            | some fields' =>
              rw [hSet] at hWrite
              injection hWrite with hEq
              subst hEq
              dsimp only [evalValueProjRead]
              rw [get?_of_set?_same hSet]
              exact ih locals oldFieldVal newVal updatedFieldVal hRec
      | _ => nomatch hWrite
    | downcast vName variantIdx =>
      cases val with
      | aggregate actualVariant fields =>
        dsimp only [evalValueProjWrite] at hWrite
        cases hCond : Bool.and (isFieldHead rest) (Nat.beq actualVariant variantIdx) with
        | false => rw [hCond] at hWrite; nomatch hWrite
        | true =>
          rw [hCond] at hWrite
          dsimp only at hWrite
          have hHead : isFieldHead rest = true := by
            cases hF : isFieldHead rest with
            | true => rfl
            | false => rw [hF] at hCond; nomatch hCond
          rcases evalValueProjWrite_preserves_aggregate_of_isFieldHead hHead hWrite with
            ⟨fields', rfl, _⟩
          dsimp only [evalValueProjRead]
          rw [hCond]
          exact ih locals (.aggregate actualVariant fields) newVal (.aggregate actualVariant fields') hWrite
      | _ => nomatch hWrite
    | index idxLocal =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite
          cases hLoc : get? locals idxLocal with
          | none => rw [hLoc] at hWrite; nomatch hWrite
          | some slot =>
            rw [hLoc] at hWrite
            cases slot with
            | dead => nomatch hWrite
            | uninit => nomatch hWrite
            | init idxVal =>
              cases idxVal with
              | scalar sc =>
                dsimp only at hWrite
                cases hElem : get? fields sc.bits with
                | none => rw [hElem] at hWrite; nomatch hWrite
                | some oldElemVal =>
                  rw [hElem] at hWrite
                  dsimp only at hWrite
                  cases hRec : evalValueProjWrite locals oldElemVal rest newVal with
                  | ub => rw [hRec] at hWrite; nomatch hWrite
                  | unsupported => rw [hRec] at hWrite; nomatch hWrite
                  | ok updatedElemVal =>
                    rw [hRec] at hWrite
                    dsimp only at hWrite
                    cases hSet : set? fields sc.bits updatedElemVal with
                    | none => rw [hSet] at hWrite; nomatch hWrite
                    | some fields' =>
                      rw [hSet] at hWrite
                      injection hWrite with hEq
                      subst hEq
                      dsimp only [evalValueProjRead]
                      rw [hLoc]
                      dsimp only
                      rw [get?_of_set?_same hSet]
                      exact ih locals oldElemVal newVal updatedElemVal hRec
              | _ => nomatch hWrite
        | succ _ => nomatch hWrite
      | _ => nomatch hWrite
    | constantIndex offset minLen fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite
          cases hIdx : evalConstantIndex (length fields) offset minLen fromEnd with
          | none => rw [hIdx] at hWrite; nomatch hWrite
          | some idx =>
            rw [hIdx] at hWrite
            dsimp only at hWrite
            cases hElem : get? fields idx with
            | none => rw [hElem] at hWrite; nomatch hWrite
            | some oldElemVal =>
              rw [hElem] at hWrite
              dsimp only at hWrite
              cases hRec : evalValueProjWrite locals oldElemVal rest newVal with
              | ub => rw [hRec] at hWrite; nomatch hWrite
              | unsupported => rw [hRec] at hWrite; nomatch hWrite
              | ok updatedElemVal =>
                rw [hRec] at hWrite
                dsimp only at hWrite
                cases hSet : set? fields idx updatedElemVal with
                | none => rw [hSet] at hWrite; nomatch hWrite
                | some fields' =>
                  rw [hSet] at hWrite
                  injection hWrite with hEq
                  subst hEq
                  have hLenEq : length fields' = length fields := length_of_set? hSet
                  dsimp only [evalValueProjRead]
                  rw [hLenEq, hIdx]
                  dsimp only
                  rw [get?_of_set?_same hSet]
                  exact ih locals oldElemVal newVal updatedElemVal hRec
        | succ _ => nomatch hWrite
      | _ => nomatch hWrite
    | subslice fromIdx toIdx fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite
          cases hExt : extractSubslice fields fromIdx toIdx fromEnd with
          | none => rw [hExt] at hWrite; nomatch hWrite
          | some subElems =>
            rw [hExt] at hWrite
            dsimp only at hWrite
            cases hRec : evalValueProjWrite locals (.aggregate .zero subElems) rest newVal with
            | ub => rw [hRec] at hWrite; nomatch hWrite
            | unsupported => rw [hRec] at hWrite; nomatch hWrite
            | ok updatedSubVal =>
              rw [hRec] at hWrite
              cases updatedSubVal with
              | aggregate subVar updatedSubElems =>
                cases subVar with
                | zero =>
                  dsimp only at hWrite
                  cases hRep : replaceSubslice fields fromIdx toIdx fromEnd updatedSubElems with
                  | none => rw [hRep] at hWrite; nomatch hWrite
                  | some fields' =>
                    rw [hRep] at hWrite
                    injection hWrite with hEq
                    subst hEq
                    dsimp only [evalValueProjRead]
                    rw [extractSubslice_replaceSubslice_same hRep]
                    exact ih locals (.aggregate .zero subElems) newVal (.aggregate .zero updatedSubElems) hRec
                | succ _ => nomatch hWrite
              | _ => nomatch hWrite
        | succ _ => nomatch hWrite
      | _ => nomatch hWrite
    | deref => cases val <;> nomatch hWrite
    | opaqueCast _ => cases val <;> nomatch hWrite
    | unwrapUnsafeBinder _ => cases val <;> nomatch hWrite

/-- **Put-Put Lens Law (`evalValueProjWrite_write_same`)**:
For every projection path `proj`, local environment `locals`, and root value
`val`, if writing `v1` to `proj` in `val` yields `.ok val1` and writing `v2` to
`proj` in `val1` yields `.ok val2`, then writing `v2` directly to `proj` in
`val` yields `.ok val2`. -/
theorem evalValueProjWrite_write_same :
    ∀ (proj : List ProjectionElem) (locals : List LocalSlot) (val v1 v2 val1 val2 : Value),
      evalValueProjWrite locals val proj v1 = .ok val1 →
      evalValueProjWrite locals val1 proj v2 = .ok val2 →
      evalValueProjWrite locals val proj v2 = .ok val2 := by
  intro proj
  induction proj with
  | nil =>
    intro locals val v1 v2 val1 val2 _ hWrite2
    exact hWrite2
  | cons p rest ih =>
    intro locals val v1 v2 val1 val2 hWrite1 hWrite2
    cases p with
    | field idx ty =>
      cases val with
      | aggregate variantIdx fields =>
        dsimp only [evalValueProjWrite] at hWrite1 ⊢
        cases hGet : get? fields idx with
        | none => rw [hGet] at hWrite1; nomatch hWrite1
        | some f0 =>
          rw [hGet] at hWrite1
          dsimp only at hWrite1 ⊢
          cases hRec1 : evalValueProjWrite locals f0 rest v1 with
          | ub => rw [hRec1] at hWrite1; nomatch hWrite1
          | unsupported => rw [hRec1] at hWrite1; nomatch hWrite1
          | ok f1 =>
            rw [hRec1] at hWrite1
            dsimp only at hWrite1
            cases hSet1 : set? fields idx f1 with
            | none => rw [hSet1] at hWrite1; nomatch hWrite1
            | some fields1 =>
              rw [hSet1] at hWrite1
              injection hWrite1 with hEq1
              subst hEq1
              dsimp only [evalValueProjWrite] at hWrite2
              rw [get?_of_set?_same hSet1] at hWrite2
              dsimp only at hWrite2
              cases hRec2 : evalValueProjWrite locals f1 rest v2 with
              | ub => rw [hRec2] at hWrite2; nomatch hWrite2
              | unsupported => rw [hRec2] at hWrite2; nomatch hWrite2
              | ok f2 =>
                rw [hRec2] at hWrite2
                dsimp only at hWrite2
                cases hSet2 : set? fields1 idx f2 with
                | none => rw [hSet2] at hWrite2; nomatch hWrite2
                | some fields2 =>
                  rw [hSet2] at hWrite2
                  injection hWrite2 with hEq2
                  subst hEq2
                  rw [ih locals f0 v1 v2 f1 f2 hRec1 hRec2]
                  dsimp only
                  rw [set?_of_set?_same hSet1 hSet2]
      | _ => nomatch hWrite1
    | downcast vName variantIdx =>
      cases val with
      | aggregate actualVariant fields =>
        dsimp only [evalValueProjWrite] at hWrite1 ⊢
        cases hCond : Bool.and (isFieldHead rest) (Nat.beq actualVariant variantIdx) with
        | false => rw [hCond] at hWrite1; nomatch hWrite1
        | true =>
          rw [hCond] at hWrite1
          dsimp only at hWrite1 ⊢
          have hHead : isFieldHead rest = true := by
            cases hF : isFieldHead rest with
            | true => rfl
            | false => rw [hF] at hCond; nomatch hCond
          rcases evalValueProjWrite_preserves_aggregate_of_isFieldHead hHead hWrite1 with
            ⟨fields1, rfl, _⟩
          dsimp only [evalValueProjWrite] at hWrite2
          rw [hCond] at hWrite2
          dsimp only at hWrite2
          exact ih locals (.aggregate actualVariant fields) v1 v2
            (.aggregate actualVariant fields1) val2 hWrite1 hWrite2
      | _ => nomatch hWrite1
    | index idxLocal =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite1 ⊢
          cases hLoc : get? locals idxLocal with
          | none => rw [hLoc] at hWrite1; nomatch hWrite1
          | some slot =>
            rw [hLoc] at hWrite1
            cases slot with
            | dead => nomatch hWrite1
            | uninit => nomatch hWrite1
            | init idxVal =>
              cases idxVal with
              | scalar sc =>
                dsimp only at hWrite1 ⊢
                cases hElem : get? fields sc.bits with
                | none => rw [hElem] at hWrite1; nomatch hWrite1
                | some e0 =>
                  rw [hElem] at hWrite1
                  dsimp only at hWrite1 ⊢
                  cases hRec1 : evalValueProjWrite locals e0 rest v1 with
                  | ub => rw [hRec1] at hWrite1; nomatch hWrite1
                  | unsupported => rw [hRec1] at hWrite1; nomatch hWrite1
                  | ok e1 =>
                    rw [hRec1] at hWrite1
                    dsimp only at hWrite1
                    cases hSet1 : set? fields sc.bits e1 with
                    | none => rw [hSet1] at hWrite1; nomatch hWrite1
                    | some fields1 =>
                      rw [hSet1] at hWrite1
                      injection hWrite1 with hEq1
                      subst hEq1
                      dsimp only [evalValueProjWrite] at hWrite2
                      rw [hLoc] at hWrite2
                      dsimp only at hWrite2
                      rw [get?_of_set?_same hSet1] at hWrite2
                      dsimp only at hWrite2
                      cases hRec2 : evalValueProjWrite locals e1 rest v2 with
                      | ub => rw [hRec2] at hWrite2; nomatch hWrite2
                      | unsupported => rw [hRec2] at hWrite2; nomatch hWrite2
                      | ok e2 =>
                        rw [hRec2] at hWrite2
                        dsimp only at hWrite2
                        cases hSet2 : set? fields1 sc.bits e2 with
                        | none => rw [hSet2] at hWrite2; nomatch hWrite2
                        | some fields2 =>
                          rw [hSet2] at hWrite2
                          injection hWrite2 with hEq2
                          subst hEq2
                          rw [ih locals e0 v1 v2 e1 e2 hRec1 hRec2]
                          dsimp only
                          rw [set?_of_set?_same hSet1 hSet2]
              | _ => nomatch hWrite1
        | succ _ => nomatch hWrite1
      | _ => nomatch hWrite1
    | constantIndex offset minLen fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite1 ⊢
          cases hIdx : evalConstantIndex (length fields) offset minLen fromEnd with
          | none => rw [hIdx] at hWrite1; nomatch hWrite1
          | some idx =>
            rw [hIdx] at hWrite1
            dsimp only at hWrite1 ⊢
            cases hElem : get? fields idx with
            | none => rw [hElem] at hWrite1; nomatch hWrite1
            | some e0 =>
              rw [hElem] at hWrite1
              dsimp only at hWrite1 ⊢
              cases hRec1 : evalValueProjWrite locals e0 rest v1 with
              | ub => rw [hRec1] at hWrite1; nomatch hWrite1
              | unsupported => rw [hRec1] at hWrite1; nomatch hWrite1
              | ok e1 =>
                rw [hRec1] at hWrite1
                dsimp only at hWrite1
                cases hSet1 : set? fields idx e1 with
                | none => rw [hSet1] at hWrite1; nomatch hWrite1
                | some fields1 =>
                  rw [hSet1] at hWrite1
                  injection hWrite1 with hEq1
                  subst hEq1
                  have hLenEq : length fields1 = length fields := length_of_set? hSet1
                  dsimp only [evalValueProjWrite] at hWrite2
                  rw [hLenEq, hIdx] at hWrite2
                  dsimp only at hWrite2
                  rw [get?_of_set?_same hSet1] at hWrite2
                  dsimp only at hWrite2
                  cases hRec2 : evalValueProjWrite locals e1 rest v2 with
                  | ub => rw [hRec2] at hWrite2; nomatch hWrite2
                  | unsupported => rw [hRec2] at hWrite2; nomatch hWrite2
                  | ok e2 =>
                    rw [hRec2] at hWrite2
                    dsimp only at hWrite2
                    cases hSet2 : set? fields1 idx e2 with
                    | none => rw [hSet2] at hWrite2; nomatch hWrite2
                    | some fields2 =>
                      rw [hSet2] at hWrite2
                      injection hWrite2 with hEq2
                      subst hEq2
                      rw [ih locals e0 v1 v2 e1 e2 hRec1 hRec2]
                      dsimp only
                      rw [set?_of_set?_same hSet1 hSet2]
        | succ _ => nomatch hWrite1
      | _ => nomatch hWrite1
    | subslice fromIdx toIdx fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite1 ⊢
          cases hExt : extractSubslice fields fromIdx toIdx fromEnd with
          | none => rw [hExt] at hWrite1; nomatch hWrite1
          | some sub0 =>
            rw [hExt] at hWrite1
            dsimp only at hWrite1 ⊢
            cases hRec1 : evalValueProjWrite locals (.aggregate .zero sub0) rest v1 with
            | ub => rw [hRec1] at hWrite1; nomatch hWrite1
            | unsupported => rw [hRec1] at hWrite1; nomatch hWrite1
            | ok subVal1 =>
              rw [hRec1] at hWrite1
              cases subVal1 with
              | aggregate subVar1 sub1 =>
                cases subVar1 with
                | zero =>
                  dsimp only at hWrite1
                  cases hRep1 : replaceSubslice fields fromIdx toIdx fromEnd sub1 with
                  | none => rw [hRep1] at hWrite1; nomatch hWrite1
                  | some fields1 =>
                    rw [hRep1] at hWrite1
                    injection hWrite1 with hEq1
                    subst hEq1
                    dsimp only [evalValueProjWrite] at hWrite2
                    rw [extractSubslice_replaceSubslice_same hRep1] at hWrite2
                    dsimp only at hWrite2
                    cases hRec2 : evalValueProjWrite locals (.aggregate .zero sub1) rest v2 with
                    | ub => rw [hRec2] at hWrite2; nomatch hWrite2
                    | unsupported => rw [hRec2] at hWrite2; nomatch hWrite2
                    | ok subVal2 =>
                      rw [hRec2] at hWrite2
                      cases subVal2 with
                      | aggregate subVar2 sub2 =>
                        cases subVar2 with
                        | zero =>
                          dsimp only at hWrite2
                          cases hRep2 : replaceSubslice fields1 fromIdx toIdx fromEnd sub2 with
                          | none => rw [hRep2] at hWrite2; nomatch hWrite2
                          | some fields2 =>
                            rw [hRep2] at hWrite2
                            injection hWrite2 with hEq2
                            subst hEq2
                            rw [ih locals (.aggregate .zero sub0) v1 v2
                              (.aggregate .zero sub1) (.aggregate .zero sub2) hRec1 hRec2]
                            dsimp only
                            rw [replaceSubslice_replaceSubslice_same hRep1 hRep2]
                        | succ _ => nomatch hWrite2
                      | _ => nomatch hWrite2
                | succ _ => nomatch hWrite1
              | _ => nomatch hWrite1
        | succ _ => nomatch hWrite1
      | _ => nomatch hWrite1
    | deref => cases val <;> nomatch hWrite1
    | opaqueCast _ => cases val <;> nomatch hWrite1
    | unwrapUnsafeBinder _ => cases val <;> nomatch hWrite1

/-- **Disjoint-Field Read-After-Write Commutativity (`evalValueProjRead_write_disjoint_field`)**:
Writing to `.field j tyJ :: restJ` leaves any read along `.field i tyI :: restI`
with `i ≠ j` completely unchanged. -/
theorem evalValueProjRead_write_disjoint_field
    (locals : List LocalSlot)
    (val newVal val' : Value)
    (i j : FieldIdx)
    (tyI tyJ : Ty)
    (restI restJ : List ProjectionElem)
    (hNe : j ≠ i)
    (hWrite : evalValueProjWrite locals val (.field j tyJ :: restJ) newVal = .ok val') :
    evalValueProjRead locals val' (.field i tyI :: restI) =
      evalValueProjRead locals val (.field i tyI :: restI) := by
  cases val with
  | aggregate variantIdx fields =>
    dsimp only [evalValueProjWrite] at hWrite
    cases hGetJ : get? fields j with
    | none => rw [hGetJ] at hWrite; nomatch hWrite
    | some oldJ =>
      rw [hGetJ] at hWrite
      dsimp only at hWrite
      cases hRec : evalValueProjWrite locals oldJ restJ newVal with
      | ub => rw [hRec] at hWrite; nomatch hWrite
      | unsupported => rw [hRec] at hWrite; nomatch hWrite
      | ok newJ =>
        rw [hRec] at hWrite
        dsimp only at hWrite
        cases hSet : set? fields j newJ with
        | none => rw [hSet] at hWrite; nomatch hWrite
        | some fields' =>
          rw [hSet] at hWrite
          injection hWrite with hEq
          subst hEq
          dsimp only [evalValueProjRead]
          rw [get?_of_set?_ne hSet hNe]
  | _ => nomatch hWrite

/-- **Disjoint-Index Read-After-Write Commutativity (`evalValueProjRead_write_disjoint_index`)**:
Writing to `.index locJ :: restJ` leaves any read along `.index locI :: restI`
unchanged whenever `locI` and `locJ` hold distinct scalar indices (`scJ.bits ≠ scI.bits`). -/
theorem evalValueProjRead_write_disjoint_index
    (locals : List LocalSlot)
    (val newVal val' : Value)
    (locI locJ : Local)
    (scI scJ : ScalarInt)
    (restI restJ : List ProjectionElem)
    (hLocI : get? locals locI = .some (.init (.scalar scI)))
    (hLocJ : get? locals locJ = .some (.init (.scalar scJ)))
    (hNe : scJ.bits ≠ scI.bits)
    (hWrite : evalValueProjWrite locals val (.index locJ :: restJ) newVal = .ok val') :
    evalValueProjRead locals val' (.index locI :: restI) =
      evalValueProjRead locals val (.index locI :: restI) := by
  cases val with
  | aggregate variantIdx fields =>
    cases variantIdx with
    | zero =>
      dsimp only [evalValueProjWrite] at hWrite
      rw [hLocJ] at hWrite
      dsimp only at hWrite
      cases hGetJ : get? fields scJ.bits with
      | none => rw [hGetJ] at hWrite; nomatch hWrite
      | some oldJ =>
        rw [hGetJ] at hWrite
        dsimp only at hWrite
        cases hRec : evalValueProjWrite locals oldJ restJ newVal with
        | ub => rw [hRec] at hWrite; nomatch hWrite
        | unsupported => rw [hRec] at hWrite; nomatch hWrite
        | ok newJ =>
          rw [hRec] at hWrite
          dsimp only at hWrite
          cases hSet : set? fields scJ.bits newJ with
          | none => rw [hSet] at hWrite; nomatch hWrite
          | some fields' =>
            rw [hSet] at hWrite
            injection hWrite with hEq
            subst hEq
            dsimp only [evalValueProjRead]
            rw [hLocI]
            dsimp only
            rw [get?_of_set?_ne hSet hNe]
    | succ _ => nomatch hWrite
  | _ => nomatch hWrite

/-- Definitional simplification equations for `readProjectedValue` and
`writeProjectedValue` on `.aggregate .zero fields`. -/
@[simp]
private theorem readProjectedValue_index_zero
    (locals : List LocalSlot)
    (fields : List Value)
    (idxLocal : Local)
    (rest : List ProjectionElem) :
    Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue
        locals (.aggregate .zero fields) (.index idxLocal :: rest) =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some elemVal =>
          Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue locals elemVal rest
        | .none => .ub
      | _ => .ub := rfl

@[simp]
private theorem readProjectedValue_constantIndex_zero
    (locals : List LocalSlot)
    (fields : List Value)
    (offset minLen : Nat)
    (fromEnd : Bool)
    (rest : List ProjectionElem) :
    Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue
        locals (.aggregate .zero fields) (.constantIndex offset minLen fromEnd :: rest) =
      let len := length fields
      match Nat.ble minLen len with
      | true =>
        let idx :=
          match fromEnd with
          | true => Nat.sub len offset
          | false => offset
        match get? fields idx with
        | .some elemVal =>
          Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue locals elemVal rest
        | .none => .ub
      | false => .ub := rfl

@[simp]
private theorem readProjectedValue_subslice_zero
    (locals : List LocalSlot)
    (fields : List Value)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool)
    (rest : List ProjectionElem) :
    Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue
        locals (.aggregate .zero fields) (.subslice fromIdx toIdx fromEnd :: rest) =
      match extractSubslice fields fromIdx toIdx fromEnd with
      | .some subElems =>
        Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue
          locals (.aggregate .zero subElems) rest
      | .none => .ub := rfl

@[simp]
private theorem writeProjectedValue_index_zero
    (locals : List LocalSlot)
    (fields : List Value)
    (idxLocal : Local)
    (rest : List ProjectionElem)
    (newVal : Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
        locals (.aggregate .zero fields) (.index idxLocal :: rest) newVal =
      match get? locals idxLocal with
      | .some (.init (.scalar sc)) =>
        match get? fields sc.bits with
        | .some oldElemVal =>
          match
            Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
              locals oldElemVal rest newVal
          with
          | .ok updatedElemVal =>
            match set? fields sc.bits updatedElemVal with
            | .some fields' => .ok (.aggregate .zero fields')
            | .none => .ub
          | .ub => .ub
          | .unsupported => .unsupported
        | .none => .ub
      | _ => .ub := rfl

@[simp]
private theorem writeProjectedValue_constantIndex_zero
    (locals : List LocalSlot)
    (fields : List Value)
    (offset minLen : Nat)
    (fromEnd : Bool)
    (rest : List ProjectionElem)
    (newVal : Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
        locals (.aggregate .zero fields) (.constantIndex offset minLen fromEnd :: rest) newVal =
      let len := length fields
      match Nat.ble minLen len with
      | true =>
        let idx :=
          match fromEnd with
          | true => Nat.sub len offset
          | false => offset
        match get? fields idx with
        | .some oldElemVal =>
          match
            Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
              locals oldElemVal rest newVal
          with
          | .ok updatedElemVal =>
            match set? fields idx updatedElemVal with
            | .some fields' => .ok (.aggregate .zero fields')
            | .none => .ub
          | .ub => .ub
          | .unsupported => .unsupported
        | .none => .ub
      | false => .ub := rfl

@[simp]
private theorem writeProjectedValue_subslice_zero
    (locals : List LocalSlot)
    (fields : List Value)
    (fromIdx toIdx : Nat)
    (fromEnd : Bool)
    (rest : List ProjectionElem)
    (newVal : Value) :
    Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
        locals (.aggregate .zero fields) (.subslice fromIdx toIdx fromEnd :: rest) newVal =
      match extractSubslice fields fromIdx toIdx fromEnd with
      | .some subElems =>
        match
          Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
            locals (.aggregate .zero subElems) rest newVal
        with
        | .ok (.aggregate 0 updatedSubElems) =>
          match replaceSubslice fields fromIdx toIdx fromEnd updatedSubElems with
          | .some fields' => .ok (.aggregate .zero fields')
          | .none => .ub
        | .ok _ => .ub
        | .ub => .ub
        | .unsupported => .unsupported
      | .none => .ub := rfl

/-- **Trusted Correspondence (`evalValueProjRead_refines_readProjectedValue`)**:
Every successful pure value-tree read `evalValueProjRead locals val proj = .ok outVal`
agrees identically with `Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue`:
`readProjectedValue locals val proj = .ok outVal`. -/
theorem evalValueProjRead_refines_readProjectedValue :
    ∀ (proj : List ProjectionElem) (locals : List LocalSlot) (val outVal : Value),
      evalValueProjRead locals val proj = .ok outVal →
      Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue locals val proj = .ok outVal := by
  intro proj
  induction proj with
  | nil =>
    intro locals val outVal hRead
    exact hRead
  | cons p rest ih =>
    intro locals val outVal hRead
    cases p with
    | field idx ty =>
      cases val with
      | aggregate variantIdx fields =>
        dsimp only [evalValueProjRead] at hRead
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue]
        cases hGet : get? fields idx with
        | none => rw [hGet] at hRead; nomatch hRead
        | some fieldVal =>
          rw [hGet] at hRead
          exact ih locals fieldVal outVal hRead
      | _ => nomatch hRead
    | downcast vName variantIdx =>
      cases val with
      | aggregate actualVariant fields =>
        dsimp only [evalValueProjRead] at hRead
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue]
        cases hHead : isFieldHead rest with
        | false => simp [hHead] at hRead
        | true =>
          cases hEq : Nat.beq actualVariant variantIdx with
          | false => simp [hHead, hEq] at hRead
          | true =>
            rw [hHead, hEq] at hRead
            dsimp only at hRead ⊢
            exact ih locals (.aggregate actualVariant fields) outVal hRead
      | _ => nomatch hRead
    | index idxLocal =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          rw [readProjectedValue_index_zero]
          cases hLoc : get? locals idxLocal with
          | none => rw [hLoc] at hRead; nomatch hRead
          | some slot =>
            rw [hLoc] at hRead
            cases slot with
            | dead => nomatch hRead
            | uninit => nomatch hRead
            | init idxVal =>
              cases idxVal with
              | scalar sc =>
                dsimp only at hRead ⊢
                cases hElem : get? fields sc.bits with
                | none => rw [hElem] at hRead; nomatch hRead
                | some elemVal =>
                  rw [hElem] at hRead
                  exact ih locals elemVal outVal hRead
              | _ => nomatch hRead
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | constantIndex offset minLen fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          rw [readProjectedValue_constantIndex_zero]
          dsimp only
          cases hIdx : evalConstantIndex (length fields) offset minLen fromEnd with
          | none => rw [hIdx] at hRead; nomatch hRead
          | some idx =>
            rw [hIdx] at hRead
            dsimp only at hRead
            unfold evalConstantIndex at hIdx
            cases hMin : Nat.ble minLen (length fields) with
            | false => rw [hMin] at hIdx; nomatch hIdx
            | true =>
              rw [hMin] at hIdx
              dsimp only at hIdx ⊢
              cases fromEnd with
              | false =>
                cases hOff : Nat.ble (Nat.succ offset) (length fields) with
                | false => rw [hOff] at hIdx; nomatch hIdx
                | true =>
                  rw [hOff] at hIdx
                  injection hIdx with hIdxEq
                  subst hIdxEq
                  cases hElem : get? fields offset with
                  | none => rw [hElem] at hRead; nomatch hRead
                  | some elemVal =>
                    rw [hElem] at hRead
                    exact ih locals elemVal outVal hRead
              | true =>
                cases hBounds : Bool.and (Nat.ble 1 offset) (Nat.ble offset (length fields)) with
                | false => rw [hBounds] at hIdx; nomatch hIdx
                | true =>
                  rw [hBounds] at hIdx
                  injection hIdx with hIdxEq
                  subst hIdxEq
                  cases hElem : get? fields (Nat.sub (length fields) offset) with
                  | none => rw [hElem] at hRead; nomatch hRead
                  | some elemVal =>
                    rw [hElem] at hRead
                    exact ih locals elemVal outVal hRead
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | subslice fromIdx toIdx fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          rw [readProjectedValue_subslice_zero]
          cases hExt : extractSubslice fields fromIdx toIdx fromEnd with
          | none => rw [hExt] at hRead; nomatch hRead
          | some subElems =>
            rw [hExt] at hRead
            exact ih locals (.aggregate .zero subElems) outVal hRead
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | deref => cases val <;> nomatch hRead
    | opaqueCast _ => cases val <;> nomatch hRead
    | unwrapUnsafeBinder _ => cases val <;> nomatch hRead

/-- **Trusted Correspondence (`evalValueProjWrite_refines_writeProjectedValue`)**:
Every successful pure value-tree write `evalValueProjWrite locals val proj newVal = .ok val'`
agrees identically with `Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue`:
`writeProjectedValue locals val proj newVal = .ok val'`. -/
theorem evalValueProjWrite_refines_writeProjectedValue :
    ∀ (proj : List ProjectionElem) (locals : List LocalSlot) (val newVal val' : Value),
      evalValueProjWrite locals val proj newVal = .ok val' →
      Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue locals val proj newVal = .ok val' := by
  intro proj
  induction proj with
  | nil =>
    intro locals val newVal val' hWrite
    exact hWrite
  | cons p rest ih =>
    intro locals val newVal val' hWrite
    cases p with
    | field idx ty =>
      cases val with
      | aggregate variantIdx fields =>
        dsimp only [evalValueProjWrite] at hWrite
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue]
        cases hGet : get? fields idx with
        | none => rw [hGet] at hWrite; nomatch hWrite
        | some oldFieldVal =>
          rw [hGet] at hWrite
          dsimp only at hWrite ⊢
          cases hRec : evalValueProjWrite locals oldFieldVal rest newVal with
          | ub => rw [hRec] at hWrite; nomatch hWrite
          | unsupported => rw [hRec] at hWrite; nomatch hWrite
          | ok updatedFieldVal =>
            rw [hRec] at hWrite
            rw [ih locals oldFieldVal newVal updatedFieldVal hRec]
            exact hWrite
      | _ => nomatch hWrite
    | downcast vName variantIdx =>
      cases val with
      | aggregate actualVariant fields =>
        dsimp only [evalValueProjWrite] at hWrite
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue]
        cases hHead : isFieldHead rest with
        | false => simp [hHead] at hWrite
        | true =>
          cases hEq : Nat.beq actualVariant variantIdx with
          | false => simp [hHead, hEq] at hWrite
          | true =>
            rw [hHead, hEq] at hWrite
            dsimp only at hWrite ⊢
            exact ih locals (.aggregate actualVariant fields) newVal val' hWrite
      | _ => nomatch hWrite
    | index idxLocal =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite
          rw [writeProjectedValue_index_zero]
          cases hLoc : get? locals idxLocal with
          | none => rw [hLoc] at hWrite; nomatch hWrite
          | some slot =>
            rw [hLoc] at hWrite
            cases slot with
            | dead => nomatch hWrite
            | uninit => nomatch hWrite
            | init idxVal =>
              cases idxVal with
              | scalar sc =>
                dsimp only at hWrite ⊢
                cases hElem : get? fields sc.bits with
                | none => rw [hElem] at hWrite; nomatch hWrite
                | some oldElemVal =>
                  rw [hElem] at hWrite
                  dsimp only at hWrite ⊢
                  cases hRec : evalValueProjWrite locals oldElemVal rest newVal with
                  | ub => rw [hRec] at hWrite; nomatch hWrite
                  | unsupported => rw [hRec] at hWrite; nomatch hWrite
                  | ok updatedElemVal =>
                    rw [hRec] at hWrite
                    rw [ih locals oldElemVal newVal updatedElemVal hRec]
                    exact hWrite
              | _ => nomatch hWrite
        | succ _ => nomatch hWrite
      | _ => nomatch hWrite
    | constantIndex offset minLen fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite
          rw [writeProjectedValue_constantIndex_zero]
          dsimp only
          cases hIdx : evalConstantIndex (length fields) offset minLen fromEnd with
          | none => rw [hIdx] at hWrite; nomatch hWrite
          | some idx =>
            rw [hIdx] at hWrite
            dsimp only at hWrite
            unfold evalConstantIndex at hIdx
            cases hMin : Nat.ble minLen (length fields) with
            | false => rw [hMin] at hIdx; nomatch hIdx
            | true =>
              rw [hMin] at hIdx
              dsimp only at hIdx ⊢
              cases fromEnd with
              | false =>
                cases hOff : Nat.ble (Nat.succ offset) (length fields) with
                | false => rw [hOff] at hIdx; nomatch hIdx
                | true =>
                  rw [hOff] at hIdx
                  injection hIdx with hIdxEq
                  subst hIdxEq
                  cases hElem : get? fields offset with
                  | none => rw [hElem] at hWrite; nomatch hWrite
                  | some oldElemVal =>
                    rw [hElem] at hWrite
                    dsimp only at hWrite ⊢
                    cases hRec : evalValueProjWrite locals oldElemVal rest newVal with
                    | ub => rw [hRec] at hWrite; nomatch hWrite
                    | unsupported => rw [hRec] at hWrite; nomatch hWrite
                    | ok updatedElemVal =>
                      rw [hRec] at hWrite
                      rw [ih locals oldElemVal newVal updatedElemVal hRec]
                      exact hWrite
              | true =>
                cases hBounds : Bool.and (Nat.ble 1 offset) (Nat.ble offset (length fields)) with
                | false => rw [hBounds] at hIdx; nomatch hIdx
                | true =>
                  rw [hBounds] at hIdx
                  injection hIdx with hIdxEq
                  subst hIdxEq
                  cases hElem : get? fields (Nat.sub (length fields) offset) with
                  | none => rw [hElem] at hWrite; nomatch hWrite
                  | some oldElemVal =>
                    rw [hElem] at hWrite
                    dsimp only at hWrite ⊢
                    cases hRec : evalValueProjWrite locals oldElemVal rest newVal with
                    | ub => rw [hRec] at hWrite; nomatch hWrite
                    | unsupported => rw [hRec] at hWrite; nomatch hWrite
                    | ok updatedElemVal =>
                      rw [hRec] at hWrite
                      rw [ih locals oldElemVal newVal updatedElemVal hRec]
                      exact hWrite
        | succ _ => nomatch hWrite
      | _ => nomatch hWrite
    | subslice fromIdx toIdx fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjWrite] at hWrite
          rw [writeProjectedValue_subslice_zero]
          cases hExt : extractSubslice fields fromIdx toIdx fromEnd with
          | none => rw [hExt] at hWrite; nomatch hWrite
          | some subElems =>
            rw [hExt] at hWrite
            dsimp only at hWrite ⊢
            cases hRec : evalValueProjWrite locals (.aggregate .zero subElems) rest newVal with
            | ub => rw [hRec] at hWrite; nomatch hWrite
            | unsupported => rw [hRec] at hWrite; nomatch hWrite
            | ok updatedSubVal =>
              rw [hRec] at hWrite
              rw [ih locals (.aggregate .zero subElems) newVal updatedSubVal hRec]
              cases updatedSubVal with
              | aggregate subVar updatedSubElems =>
                cases subVar <;> exact hWrite
              | _ => exact hWrite
        | succ _ => nomatch hWrite
      | _ => nomatch hWrite
    | deref => cases val <;> nomatch hWrite
    | opaqueCast _ => cases val <;> nomatch hWrite
    | unwrapUnsafeBinder _ => cases val <;> nomatch hWrite


/-! ## Section 2: `CastKind.charToInt` Formalization & `Trusted.MirSemantics.evalRvalue` Correspondence -/

/-- Test whether `bits` is a valid Unicode scalar value (`0x0000..=0xD7FF` or
`0xE000..=0x10FFFF`, i.e., `bits <= 55295 ∨ (57344 <= bits ∧ bits <= 1114111)`),
matching `ScalarTy::Char::is_valid_bits` in `crates/anneal-mir/src/ir.rs`. -/
@[reducible]
def isValidUnicodeScalar (bits : Nat) : Bool :=
  Bool.or
    (Nat.ble bits 55295)
    (Bool.and (Nat.ble 57344 bits) (Nat.ble bits 1114111))

/-- Propositional characterization of `isValidUnicodeScalar`. -/
theorem isValidUnicodeScalar_iff (bits : Nat) :
    isValidUnicodeScalar bits = true ↔
      (bits ≤ 55295 ∨ (57344 ≤ bits ∧ bits ≤ 1114111)) := by
  unfold isValidUnicodeScalar
  cases h1 : Nat.ble bits 55295 with
  | true =>
    have hLe : bits ≤ 55295 := Nat.le_of_ble_eq_true h1
    simp [hLe]
  | false =>
    have hNotLe : ¬ bits ≤ 55295 := by
      intro hLe
      have := Nat.ble_eq_true_of_le hLe
      rw [h1] at this
      nomatch this
    cases h2 : Nat.ble 57344 bits with
    | false =>
      have hNot2 : ¬ 57344 ≤ bits := by
        intro hLe
        have := Nat.ble_eq_true_of_le hLe
        rw [h2] at this
        nomatch this
      simp [hNotLe, hNot2]
    | true =>
      have hGe2 : 57344 ≤ bits := Nat.le_of_ble_eq_true h2
      cases h3 : Nat.ble bits 1114111 with
      | false =>
        have hNot3 : ¬ bits ≤ 1114111 := by
          intro hLe
          have := Nat.ble_eq_true_of_le hLe
          rw [h3] at this
          nomatch this
        simp [hNotLe, hGe2, hNot3]
      | true =>
        have hLe3 : bits ≤ 1114111 := Nat.le_of_ble_eq_true h3
        simp [hGe2, hLe3]

/-- Exact equivalence between `isValidUnicodeScalar` and
`Trusted.Rustc.V2026_06_01.MirSemantics.isValidCharCode`. -/
theorem isValidUnicodeScalar_eq_isValidCharCode (bits : Nat) :
    isValidUnicodeScalar bits = isValidCharCode bits := by
  unfold isValidUnicodeScalar isValidCharCode
  cases h1 : Nat.ble bits 55295 with
  | true =>
    have hLe : bits ≤ 55295 := Nat.le_of_ble_eq_true h1
    have hNot55296 : Nat.ble 55296 bits = false := by
      cases hB : Nat.ble 55296 bits with
      | false => rfl
      | true =>
        have := Nat.le_of_ble_eq_true hB
        omega
    simp [hNot55296]
  | false =>
    have hGt : 55296 ≤ bits := by
      cases hB : Nat.ble 55296 bits with
      | true => exact Nat.le_of_ble_eq_true hB
      | false =>
        have hLe : bits ≤ 55295 := by
          have : ¬ 55296 ≤ bits := by
            intro hGe
            have := Nat.ble_eq_true_of_le hGe
            rw [hB] at this
            nomatch this
          omega
        have := Nat.ble_eq_true_of_le hLe
        rw [h1] at this
        nomatch this
    have hYes55296 : Nat.ble 55296 bits = true := Nat.ble_eq_true_of_le hGt
    simp [hYes55296]

/-- Surrogate code points (`0xD800..=0xDFFF`, i.e. `55296..=57343`) are rejected
by `isValidUnicodeScalar`. -/
theorem isValidUnicodeScalar_surrogate_false
    (bits : Nat)
    (hLo : 55296 ≤ bits)
    (hHi : bits ≤ 57343) :
    isValidUnicodeScalar bits = false := by
  cases h : isValidUnicodeScalar bits with
  | false => rfl
  | true =>
    have hOr := (isValidUnicodeScalar_iff bits).mp h
    omega

/-- Code points above `0x10FFFF` (`1114111`) are rejected by `isValidUnicodeScalar`. -/
theorem isValidUnicodeScalar_gt_max_false
    (bits : Nat)
    (hGt : 1114111 < bits) :
    isValidUnicodeScalar bits = false := by
  cases h : isValidUnicodeScalar bits with
  | false => rfl
  | true =>
    have hOr := (isValidUnicodeScalar_iff bits).mp h
    omega

/-- Every valid Unicode scalar value fits strictly below `scalarModulus 4` (`2^32`). -/
theorem isValidUnicodeScalar_lt_scalarModulus_four
    (bits : Nat)
    (hValid : isValidUnicodeScalar bits = true) :
    bits < scalarModulus 4 := by
  have hOr := (isValidUnicodeScalar_iff bits).mp hValid
  have hMod4 : scalarModulus 4 = 4294967296 := rfl
  omega

@[simp] private theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[simp] private theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[simp] private theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl
@[simp] private theorem nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
@[simp] private theorem nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl

/-- `scalarModulus n` is strictly positive for all byte widths `n`. -/
theorem scalarModulus_pos : ∀ (n : Nat), 0 < scalarModulus n
  | 0 => by decide
  | n + 1 => by
    change 0 < 256 * scalarModulus n
    have ih := scalarModulus_pos n
    omega

/-- `scalarModulus` is monotonically non-decreasing in the byte width. -/
theorem scalarModulus_mono {m n : Nat} (h : m ≤ n) :
    scalarModulus m ≤ scalarModulus n := by
  induction n with
  | zero =>
    have hm : m = 0 := by omega
    subst hm
    exact Nat.le_refl _
  | succ k ih =>
    have hOr : m ≤ k ∨ m = k + 1 := by omega
    rcases hOr with hLe | rfl
    · have hStep : scalarModulus k ≤ scalarModulus (k + 1) := by
        change scalarModulus k ≤ 256 * scalarModulus k
        have hPos := scalarModulus_pos k
        omega
      exact Nat.le_trans (ih hLe) hStep
    · exact Nat.le_refl _

/-- `wrapScalarBits val modulus` is strictly less than `modulus` whenever `0 < modulus`. -/
theorem wrapScalarBits_lt_modulus
    (val modulus : Nat)
    (hPos : 0 < modulus) :
    wrapScalarBits val modulus < modulus := by
  unfold wrapScalarBits
  cases hBle : Nat.ble modulus val with
  | true => exact Nat.mod_lt val hPos
  | false =>
    dsimp only
    have hNotLe : ¬ modulus ≤ val := by
      intro hLe
      have := Nat.ble_eq_true_of_le hLe
      rw [hBle] at this
      nomatch this
    omega

/-- `wrapScalarBits val modulus` is the identity whenever `val < modulus`. -/
theorem wrapScalarBits_eq_self_of_lt
    {val modulus : Nat}
    (hLt : val < modulus) :
    wrapScalarBits val modulus = val := by
  unfold wrapScalarBits
  have hBle : Nat.ble modulus val = false := by
    cases h : Nat.ble modulus val with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      omega
  rw [hBle]

/-- `wrapScalarBits val modulus` equals `val % modulus` for all `val` and `modulus`. -/
theorem wrapScalarBits_eq_mod (val modulus : Nat) :
    wrapScalarBits val modulus = val % modulus := by
  unfold wrapScalarBits
  cases hBle : Nat.ble modulus val with
  | true => rfl
  | false =>
    dsimp only
    have hLt : val < modulus := by
      have : ¬ modulus ≤ val := by
        intro hLe
        have := Nat.ble_eq_true_of_le hLe
        rw [hBle] at this
        nomatch this
      omega
    exact (Nat.mod_eq_of_lt hLt).symm

/-- Evaluate `CastKind.charToInt` given a character codepoint `bits` and target
integer byte width `targetBytes` (`eval_char_to_int` in `crates/anneal-mir/src/lower/cast.rs`). -/
def evalCharToInt (bits targetBytes : Nat) : Option ScalarInt :=
  match isValidUnicodeScalar bits, Nat.beq targetBytes 0 with
  | true, false =>
    .some ⟨wrapScalarBits bits (scalarModulus targetBytes), targetBytes⟩
  | _, _ => .none

/-- Evaluate `CastKind.charToInt` given a character codepoint `bits` and target
`RigidTy` (`intCastTargetBytes targetKind`). -/
def evalCharToIntByKind (bits : Nat) (targetKind : RigidTy) : Option ScalarInt :=
  match isValidUnicodeScalar bits, intCastTargetBytes targetKind with
  | true, .some targetBytes =>
    .some ⟨wrapScalarBits bits (scalarModulus targetBytes), targetBytes⟩
  | _, _ => .none

/-- Any target byte width returned by `intCastTargetBytes` is non-zero. -/
theorem intCastTargetBytes_ne_zero
    {targetKind : RigidTy}
    {targetBytes : Nat}
    (hTarget : intCastTargetBytes targetKind = .some targetBytes) :
    Nat.beq targetBytes 0 = false := by
  cases targetKind with
  | uint u => cases u <;> (dsimp only [intCastTargetBytes] at hTarget; injection hTarget with h; subst h; rfl)
  | int i => cases i <;> (dsimp only [intCastTargetBytes] at hTarget; injection hTarget with h; subst h; rfl)
  | _ => dsimp only [intCastTargetBytes] at hTarget; nomatch hTarget

/-- When `intCastTargetBytes targetKind = .some targetBytes`, `evalCharToIntByKind`
agrees with `evalCharToInt bits targetBytes`. -/
theorem evalCharToIntByKind_eq_evalCharToInt
    (bits : Nat)
    (targetKind : RigidTy)
    (targetBytes : Nat)
    (hTarget : intCastTargetBytes targetKind = .some targetBytes) :
    evalCharToIntByKind bits targetKind = evalCharToInt bits targetBytes := by
  have hPos := intCastTargetBytes_ne_zero hTarget
  unfold evalCharToIntByKind evalCharToInt
  rw [hTarget, hPos]
  cases isValidUnicodeScalar bits <;> rfl

/-- Every `ScalarInt` produced by `evalCharToInt` has positive byte width
`targetBytes` and bits strictly within `scalarModulus targetBytes`. -/
theorem evalCharToInt_inRange
    {bits targetBytes : Nat}
    {sc : ScalarInt}
    (hEval : evalCharToInt bits targetBytes = .some sc) :
    sc.sizeBytes = targetBytes ∧
    0 < targetBytes ∧
    sc.bits < scalarModulus targetBytes := by
  unfold evalCharToInt at hEval
  cases hVal : isValidUnicodeScalar bits with
  | false => rw [hVal] at hEval; nomatch hEval
  | true =>
    cases hZero : Nat.beq targetBytes 0 with
    | true => rw [hVal, hZero] at hEval; nomatch hEval
    | false =>
      rw [hVal, hZero] at hEval
      injection hEval with hEq
      subst hEq
      have hPos : 0 < targetBytes := by
        have hNe : targetBytes ≠ 0 := by
          intro hZ
          subst hZ
          nomatch hZero
        omega
      have hLt :
          wrapScalarBits bits (scalarModulus targetBytes) < scalarModulus targetBytes :=
        wrapScalarBits_lt_modulus bits (scalarModulus targetBytes) (scalarModulus_pos targetBytes)
      exact ⟨rfl, hPos, hLt⟩

/-- **Lossless Identity for `>= 32`-Bit Targets (`evalCharToInt_lossless_of_ge_four`)**:
For every valid Unicode scalar value `bits` and target integer width
`targetBytes >= 4` (`u32`, `i32`, `u64`, `i64`, `u128`, `i128`, `usize`, `isize`),
`evalCharToInt` preserves `bits` without truncation. -/
theorem evalCharToInt_lossless_of_ge_four
    {bits targetBytes : Nat}
    (hValid : isValidUnicodeScalar bits = true)
    (hGe4 : 4 ≤ targetBytes) :
    evalCharToInt bits targetBytes = .some ⟨bits, targetBytes⟩ := by
  have hZero : Nat.beq targetBytes 0 = false := by
    cases h : Nat.beq targetBytes 0 with
    | false => rfl
    | true =>
      have := Nat.eq_of_beq_eq_true h
      omega
  have hLt4 : bits < scalarModulus 4 :=
    isValidUnicodeScalar_lt_scalarModulus_four bits hValid
  have hLeMod : scalarModulus 4 ≤ scalarModulus targetBytes :=
    scalarModulus_mono hGe4
  have hLtMod : bits < scalarModulus targetBytes :=
    Nat.lt_of_lt_of_le hLt4 hLeMod
  unfold evalCharToInt
  rw [hValid, hZero, wrapScalarBits_eq_self_of_lt hLtMod]

/-- **Low-Bit Truncation for Narrow Targets (`evalCharToInt_truncate_u8`, `evalCharToInt_truncate_u16`)**:
For `1`-byte (`u8`/`i8`) and `2`-byte (`u16`/`i16`) targets, `evalCharToInt`
truncates a valid Unicode scalar value `bits` modulo `256` and `65536` respectively. -/
theorem evalCharToInt_truncate_narrow
    {bits : Nat}
    (hValid : isValidUnicodeScalar bits = true) :
    evalCharToInt bits 1 = .some ⟨bits % 256, 1⟩ ∧
    evalCharToInt bits 2 = .some ⟨bits % 65536, 2⟩ := by
  have h1 : scalarModulus 1 = 256 := rfl
  have h2 : scalarModulus 2 = 65536 := rfl
  unfold evalCharToInt
  rw [hValid]
  dsimp only
  rw [wrapScalarBits_eq_mod bits (scalarModulus 1),
      wrapScalarBits_eq_mod bits (scalarModulus 2), h1, h2]
  exact ⟨rfl, rfl⟩

/-- **Invalid Codepoint Rejection (`evalCharToInt_rejects_invalid`)**:
Surrogates (`55296..=57343`) and values above `0x10FFFF` (`1114111`) are
rejected with `.none` by both `evalCharToInt` and `evalCharToIntByKind`. -/
theorem evalCharToInt_rejects_invalid
    (bits targetBytes : Nat)
    (targetKind : RigidTy) :
    (55296 ≤ bits → bits ≤ 57343 →
      evalCharToInt bits targetBytes = .none ∧
      evalCharToIntByKind bits targetKind = .none) ∧
    (1114111 < bits →
      evalCharToInt bits targetBytes = .none ∧
      evalCharToIntByKind bits targetKind = .none) := by
  refine ⟨?_, ?_⟩
  · intro hLo hHi
    have hFalse := isValidUnicodeScalar_surrogate_false bits hLo hHi
    simp [evalCharToInt, evalCharToIntByKind, hFalse]
  · intro hGt
    have hFalse := isValidUnicodeScalar_gt_max_false bits hGt
    simp [evalCharToInt, evalCharToIntByKind, hFalse]

/-- **Step Correspondence (`evalCharToInt_trusted_evalRvalue_correspondence`)**:
In `Runtime(PostCleanup)` MIR, `rustc` lowers `char as Int` to
`Rvalue.cast .intToInt op targetTy` on an unsigned 4-byte `RigidTy.char` operand.
Whenever `op` has type `.char` (`operandTy localDecls layouts op = .some { kind := .char, .. }`)
and evaluates to a valid 4-byte character scalar `.scalar ⟨bits, 4⟩` with
`isValidUnicodeScalar bits = true`:
1. If `evalCharToIntByKind bits targetTy.kind = .some outSc`, then
   `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue locals (.cast .intToInt op targetTy) mem localDecls layouts = .ok (.scalar outSc) locals' mem`.
2. Conversely, if `intCastTargetBytes targetTy.kind = .none`, then
   `evalCharToIntByKind bits targetTy.kind = .none` and `evalRvalue` returns `.unsupported`. -/
theorem evalCharToInt_trusted_evalRvalue_correspondence
    (locals locals' : List LocalSlot)
    (op : Operand)
    (targetTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (bits charLayoutIdx : Nat)
    (hOpEval :
      Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
        locals op mem.borrows mem.globals layouts mem.callerLocals =
        .ok (.scalar ⟨bits, 4⟩) locals')
    (hOpTy :
      Trusted.Rustc.V2026_06_01.MirSemantics.operandTy localDecls layouts op =
        .some { kind := .char, layoutIdx := charLayoutIdx })
    (hValid : isValidUnicodeScalar bits = true) :
    (∀ outSc : ScalarInt,
      evalCharToIntByKind bits targetTy.kind = .some outSc →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue
        locals (.cast .intToInt op targetTy) mem localDecls layouts =
        .ok (.scalar outSc) locals' mem) ∧
    (intCastTargetBytes targetTy.kind = .none →
      evalCharToIntByKind bits targetTy.kind = .none ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue
        locals (.cast .intToInt op targetTy) mem localDecls layouts =
        .unsupported) := by
  have hUnsigned : operandIsSigned localDecls op layouts = false := by
    simp [hOpTy]
  refine ⟨?_, ?_⟩
  · intro outSc hCharCast
    unfold evalCharToIntByKind at hCharCast
    rw [hValid] at hCharCast
    cases hTarget : intCastTargetBytes targetTy.kind with
    | none => rw [hTarget] at hCharCast; nomatch hCharCast
    | some targetBytes =>
      rw [hTarget] at hCharCast
      injection hCharCast with hOutEq
      subst hOutEq
      dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue]
      rw [hOpEval]
      dsimp only
      rw [hTarget]
      dsimp only
      rw [hUnsigned]
  · intro hNone
    refine ⟨?_, ?_⟩
    · unfold evalCharToIntByKind
      rw [hValid, hNone]
    · dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue]
      rw [hOpEval]
      dsimp only
      rw [hNone]


/-! ## Section 3: `Rvalue.nullaryOp`, Canonical Tuple `OffsetOf`, & Unsupported-Shrinking Refinement -/

/-- Round `offset` up to the nearest multiple of `align` (`roundUpToAlign`). -/
@[reducible]
def alignUp (offset align : Nat) : Nat :=
  roundUpToAlign offset align

/-- `alignUp offset align` is always `>= offset`. -/
theorem alignUp_ge (offset align : Nat) :
    offset ≤ alignUp offset align := by
  unfold alignUp roundUpToAlign
  cases Nat.beq (Nat.mod offset align) 0 <;> simp only [nat_add_eq, nat_sub_eq, nat_mod_eq] <;> omega

/-- When `offset % align = 0`, `alignUp offset align = offset`. -/
theorem alignUp_eq_self_of_mod_zero
    {offset align : Nat}
    (hMod : offset % align = 0) :
    alignUp offset align = offset := by
  unfold alignUp roundUpToAlign
  have hBeq : Nat.beq (Nat.mod offset align) 0 = true :=
    Nat.beq_eq.mpr hMod
  rw [hBeq]

/-- When `0 < align`, `alignUp offset align` is a multiple of `align`. -/
theorem alignUp_mod_eq_zero
    (offset align : Nat)
    (hPos : 0 < align) :
    alignUp offset align % align = 0 := by
  unfold alignUp roundUpToAlign
  cases hBeq : Nat.beq (Nat.mod offset align) 0 with
  | true => exact Nat.eq_of_beq_eq_true hBeq
  | false =>
    simp only [nat_add_eq, nat_sub_eq, nat_mod_eq]
    have hLt : offset % align < align := Nat.mod_lt offset hPos
    have hSplit : offset + (align - offset % align) = (offset / align + 1) * align := by
      have hDivMod := Nat.div_add_mod offset align
      have hComm : align * (offset / align) = (offset / align) * align := Nat.mul_comm _ _
      have hSuccMul : (offset / align + 1) * align = (offset / align) * align + align :=
        Nat.succ_mul (offset / align) align
      omega
    rw [hSplit, Nat.mul_mod_left]

/-- Sum the byte sizes of the first `fieldIdx` fields of `tupleFields`, returning
`.none` if `fieldIdx >= tupleFields.length` or if any preceding field has no known
byte size. -/
def sumPrefixFieldSizes
    (fieldByteSize : RigidTy → Option Nat) :
    List RigidTy → Nat → Option Nat
  | .nil, _ => .none
  | _ :: _, .zero => .some 0
  | k :: rest, .succ idx =>
    match fieldByteSize k, sumPrefixFieldSizes fieldByteSize rest idx with
    | .some sz, .some restOff => .some (Nat.add sz restOff)
    | _, _ => .none

/-- Resolve the byte offset of a `(variantIdx, fieldIdx)` projection chain inside
a canonical tuple type (`resolve_offset_of` in `crates/anneal-mir/src/lower/rvalue.rs`).
Fails closed (`.none`) if any container is not a tuple, if `variantIdx != 0`, or
if `fieldIdx` is out of bounds. -/
def resolveTupleOffsetOf
    (fieldByteSize : RigidTy → Option Nat) :
    RigidTy → List (VariantIdx × FieldIdx) → Option Nat
  | _, .nil => .some 0
  | .tuple tupleFields, (variantIdx, fieldIdx) :: rest =>
    match
      Nat.beq variantIdx 0,
      get? tupleFields fieldIdx,
      sumPrefixFieldSizes fieldByteSize tupleFields fieldIdx
    with
    | true, .some childKind, .some stepOff =>
      match resolveTupleOffsetOf fieldByteSize childKind rest with
      | .some tailOff => .some (Nat.add stepOff tailOff)
      | .none => .none
    | _, _, _ => .none
  | _, _ :: _ => .none

/-- Empty `OffsetOf` path resolves to byte offset `0`. -/
@[simp]
theorem resolveTupleOffsetOf_nil
    (fieldByteSize : RigidTy → Option Nat)
    (kind : RigidTy) :
    resolveTupleOffsetOf fieldByteSize kind .nil = .some 0 := by
  cases kind <;> rfl

/-- Any `OffsetOf` step on a tuple with a non-zero `variantIdx` fails closed (`.none`). -/
theorem resolveTupleOffsetOf_nonzero_variant_eq_none
    (fieldByteSize : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (variantIdx : VariantIdx)
    (fieldIdx : FieldIdx)
    (rest : List (VariantIdx × FieldIdx))
    (hNonZero : variantIdx ≠ 0) :
    resolveTupleOffsetOf fieldByteSize (.tuple tupleFields) ((variantIdx, fieldIdx) :: rest) =
      .none := by
  have hBeq : Nat.beq variantIdx 0 = false := by
    cases h : Nat.beq variantIdx 0 with
    | false => rfl
    | true => exact False.elim (hNonZero (Nat.eq_of_beq_eq_true h))
  unfold resolveTupleOffsetOf
  rw [hBeq]

/-- Any `OffsetOf` step with an out-of-bounds `fieldIdx` (`get? tupleFields fieldIdx = .none`)
fails closed (`.none`). -/
theorem resolveTupleOffsetOf_oob_field_eq_none
    (fieldByteSize : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (variantIdx : VariantIdx)
    (fieldIdx : FieldIdx)
    (rest : List (VariantIdx × FieldIdx))
    (hOob : get? tupleFields fieldIdx = .none) :
    resolveTupleOffsetOf fieldByteSize (.tuple tupleFields) ((variantIdx, fieldIdx) :: rest) =
      .none := by
  unfold resolveTupleOffsetOf
  rw [hOob]
  cases Nat.beq variantIdx 0 <;> rfl

/-- Any non-empty `OffsetOf` path on a non-tuple type fails closed (`.none`). -/
theorem resolveTupleOffsetOf_non_tuple_eq_none
    (fieldByteSize : RigidTy → Option Nat)
    (kind : RigidTy)
    (step : VariantIdx × FieldIdx)
    (rest : List (VariantIdx × FieldIdx))
    (hNotTuple : ∀ fs, kind ≠ .tuple fs) :
    resolveTupleOffsetOf fieldByteSize kind (step :: rest) = .none := by
  cases kind with
  | tuple fs => exact False.elim (hNotTuple fs rfl)
  | _ => rfl

/-- Prefix sum + selected field size is bounded by the total tuple field byte sum
(`tupleFieldsByteSum`). -/
theorem sumPrefixFieldSizes_add_field_le_tupleFieldsByteSum
    (fieldByteSize : RigidTy → Option Nat) :
    ∀ (tupleFields : List RigidTy) (fieldIdx : FieldIdx) (fieldKind : RigidTy)
      (off fieldSz totalSz : Nat),
      get? tupleFields fieldIdx = .some fieldKind →
      fieldByteSize fieldKind = .some fieldSz →
      sumPrefixFieldSizes fieldByteSize tupleFields fieldIdx = .some off →
      tupleFieldsByteSum fieldByteSize tupleFields = .some totalSz →
      off + fieldSz ≤ totalSz := by
  intro tupleFields
  induction tupleFields with
  | nil =>
    intro fieldIdx _ _ _ _ hGet
    nomatch hGet
  | cons k rest ih =>
    intro fieldIdx fieldKind off fieldSz totalSz hGet hFieldSz hPrefix hTotal
    unfold tupleFieldsByteSum at hTotal
    cases hK : fieldByteSize k with
    | none => rw [hK] at hTotal; nomatch hTotal
    | some szK =>
      cases hRestSum : tupleFieldsByteSum fieldByteSize rest with
      | none => rw [hK, hRestSum] at hTotal; nomatch hTotal
      | some restSz =>
        rw [hK, hRestSum] at hTotal
        injection hTotal with hTotalEq
        change szK + restSz = totalSz at hTotalEq
        cases fieldIdx with
        | zero =>
          simp only [get?_eq_getElem?, List.getElem?_cons_zero] at hGet
          injection hGet with hKindEq
          subst hKindEq
          rw [hK] at hFieldSz
          injection hFieldSz with hSzEq
          unfold sumPrefixFieldSizes at hPrefix
          injection hPrefix with hOffEq
          omega
        | succ idx =>
          simp only [get?_eq_getElem?, List.getElem?_cons_succ] at hGet
          unfold sumPrefixFieldSizes at hPrefix
          rw [hK] at hPrefix
          cases hRestPrefix : sumPrefixFieldSizes fieldByteSize rest idx with
          | none => rw [hRestPrefix] at hPrefix; nomatch hPrefix
          | some restOff =>
            rw [hRestPrefix] at hPrefix
            injection hPrefix with hOffEq
            change szK + restOff = off at hOffEq
            have hBound := ih idx fieldKind restOff fieldSz restSz hGet hFieldSz hRestPrefix hRestSum
            omega

/-- **Tuple `OffsetOf` Upper-Bound Invariant (`resolveTupleOffsetOf_single_step_bound`)**:
Whenever a 1-step `OffsetOf` query `[(0, fieldIdx)]` on `.tuple tupleFields`
resolves to `off`, the selected field has size `fieldSz`, and the tuple's
unpadded field sum is `totalUnpadded`, the entire field `[off, off + fieldSz)`
fits within the aligned tuple size `alignUp totalUnpadded align`. -/
theorem resolveTupleOffsetOf_single_step_bound
    (fieldByteSize : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (fieldIdx : FieldIdx)
    (fieldKind : RigidTy)
    (off fieldSz totalUnpadded align : Nat)
    (hResolve :
      resolveTupleOffsetOf fieldByteSize (.tuple tupleFields) [(0, fieldIdx)] = .some off)
    (hGet : get? tupleFields fieldIdx = .some fieldKind)
    (hFieldSz : fieldByteSize fieldKind = .some fieldSz)
    (hTotal : tupleFieldsByteSum fieldByteSize tupleFields = .some totalUnpadded) :
    off + fieldSz ≤ totalUnpadded ∧
    off + fieldSz ≤ alignUp totalUnpadded align := by
  unfold resolveTupleOffsetOf at hResolve
  rw [hGet] at hResolve
  cases hPref : sumPrefixFieldSizes fieldByteSize tupleFields fieldIdx with
  | none => rw [hPref] at hResolve; nomatch hResolve
  | some stepOff =>
    rw [hPref] at hResolve
    dsimp only at hResolve
    rw [resolveTupleOffsetOf_nil] at hResolve
    injection hResolve with hOffEq
    have hStepEq : off = stepOff := by
      change stepOff + 0 = off at hOffEq
      omega
    subst hStepEq
    have hLeUnpadded :=
      sumPrefixFieldSizes_add_field_le_tupleFieldsByteSum
        fieldByteSize tupleFields fieldIdx fieldKind off fieldSz totalUnpadded
        hGet hFieldSz hPref hTotal
    have hLeAligned := alignUp_ge totalUnpadded align
    exact ⟨hLeUnpadded, Nat.le_trans hLeUnpadded hLeAligned⟩

/-- Prefix field offsets are monotonically increasing in `fieldIdx`: if `i <= j`
and both `sumPrefixFieldSizes` calls succeed, then `offI <= offJ`. -/
theorem sumPrefixFieldSizes_monotone
    (fieldByteSize : RigidTy → Option Nat) :
    ∀ (tupleFields : List RigidTy) (i j offI offJ : Nat),
      i ≤ j →
      sumPrefixFieldSizes fieldByteSize tupleFields i = .some offI →
      sumPrefixFieldSizes fieldByteSize tupleFields j = .some offJ →
      offI ≤ offJ := by
  intro tupleFields
  induction tupleFields with
  | nil =>
    intro i _ _ _ _ hI _
    nomatch hI
  | cons k rest ih =>
    intro i j offI offJ hLe hI hJ
    cases i with
    | zero =>
      unfold sumPrefixFieldSizes at hI
      injection hI with hEq
      omega
    | succ i' =>
      cases j with
      | zero => omega
      | succ j' =>
        unfold sumPrefixFieldSizes at hI hJ
        cases hK : fieldByteSize k with
        | none => rw [hK] at hI; nomatch hI
        | some szK =>
          rw [hK] at hI hJ
          cases hRestI : sumPrefixFieldSizes fieldByteSize rest i' with
          | none => rw [hRestI] at hI; nomatch hI
          | some rI =>
            cases hRestJ : sumPrefixFieldSizes fieldByteSize rest j' with
            | none => rw [hRestJ] at hJ; nomatch hJ
            | some rJ =>
              rw [hRestI] at hI
              rw [hRestJ] at hJ
              injection hI with hEqI
              injection hJ with hEqJ
              change szK + rI = offI at hEqI
              change szK + rJ = offJ at hEqJ
              have hSub := ih i' j' rI rJ (by omega) hRestI hRestJ
              omega

/-- Evaluate `Rvalue.nullaryOp` (`eval_nullary_op` in `crates/anneal-mir/src/lower/rvalue.rs`):
- `.sizeOf`: resolves byte size via `intrinsicRigidTyByteSize`, checks `sz <= isize::MAX`,
  and returns `.ok (.scalar ⟨sz, ptrBytes⟩) locals mem`.
- `.alignOf`: resolves size and ABI alignment via `intrinsicRigidTyByteSize` and
  `intrinsicRigidTyAlign`, checks `sz <= isize::MAX` and `align > 0`, and returns
  `.ok (.scalar ⟨align, ptrBytes⟩) locals mem`.
- `.offsetOf fields`: resolves canonical tuple field offset via `resolveTupleOffsetOf`,
  checks `offset <= sz <= isize::MAX`, and returns `.ok (.scalar ⟨offset, ptrBytes⟩) locals mem`.
- `.ubChecks`: on `RigidTy.bool`, returns `.ok (.scalar ⟨1, 1⟩) locals mem` (`boolToScalar true`).
- Fails closed with `.unsupported` on unresolved layouts, overflow, or `.contractChecks`. -/
def evalNullaryOp
    (locals : List LocalSlot)
    (op : NullOp)
    (argTy : Ty)
    (mem : Memory := emptyMemory)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    RvalueEvalResult :=
  let ptrBytes := layoutPointerBytes layouts
  let maxObjSize := Nat.sub (Nat.div (scalarModulus ptrBytes) 2) 1
  match op with
  | .sizeOf =>
    match intrinsicRigidTyByteSize localDecls layouts argTy.kind with
    | .some sz =>
      match Nat.ble sz maxObjSize with
      | true => .ok (.scalar ⟨sz, ptrBytes⟩) locals mem
      | false => .unsupported
    | .none => .unsupported
  | .alignOf =>
    match
      intrinsicRigidTyByteSize localDecls layouts argTy.kind,
      intrinsicRigidTyAlign localDecls layouts argTy.kind
    with
    | .some sz, .some align =>
      match Bool.and (Nat.ble sz maxObjSize) (Bool.not (Nat.beq align 0)) with
      | true => .ok (.scalar ⟨align, ptrBytes⟩) locals mem
      | false => .unsupported
    | _, _ => .unsupported
  | .offsetOf fields =>
    match intrinsicRigidTyByteSize localDecls layouts argTy.kind with
    | .some sz =>
      match resolveTupleOffsetOf (intrinsicRigidTyByteSize localDecls layouts) argTy.kind fields with
      | .some offset =>
        match Bool.and (Nat.ble sz maxObjSize) (Nat.ble offset sz) with
        | true => .ok (.scalar ⟨offset, ptrBytes⟩) locals mem
        | false => .unsupported
      | .none => .unsupported
    | .none => .unsupported
  | .ubChecks =>
    match argTy.kind with
    | .bool => .ok (.scalar (boolToScalar true)) locals mem
    | _ => .unsupported
  | .contractChecks => .unsupported

/-- Unsupported-shrinking refinement relation on `RvalueEvalResult`:
`annealRes` refines `trustedRes` when `trustedRes = .unsupported` (shrinking the
unsupported fragment to a defined evaluation or keeping it unsupported) or when
`annealRes = trustedRes` on all defined outcomes. -/
def RvalueResultRefines (annealRes trustedRes : RvalueEvalResult) : Prop :=
  trustedRes = .unsupported ∨ annealRes = trustedRes

/-- `RvalueResultRefines` is reflexive and agrees identically whenever
`trustedRes ≠ .unsupported`. -/
theorem rvalueResultRefines_properties (a b : RvalueEvalResult) :
    RvalueResultRefines a a ∧
    (RvalueResultRefines a b → b ≠ .unsupported → a = b) := by
  refine ⟨Or.inr rfl, ?_⟩
  intro hRef hNe
  rcases hRef with hUnsup | hEq
  · exact False.elim (hNe hUnsup)
  · exact hEq

/-- In `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue`, `Rvalue.nullaryOp`
currently hits the catch-all `.unsupported` branch (`Places.lean:8854`). -/
@[simp]
theorem trusted_evalRvalue_nullaryOp_eq_unsupported
    (locals : List LocalSlot)
    (op : NullOp)
    (argTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue
      locals (.nullaryOp op argTy) mem localDecls layouts = .unsupported := rfl

/-- **Refinement Theorem (`evalNullaryOp_refines_trusted_evalRvalue`)**:
`evalNullaryOp` is a sound unsupported-shrinking refinement of
`Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue (.nullaryOp op argTy)` and
never introduces `.ub` on any input. -/
theorem evalNullaryOp_refines_trusted_evalRvalue
    (locals : List LocalSlot)
    (op : NullOp)
    (argTy : Ty)
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    RvalueResultRefines
      (evalNullaryOp locals op argTy mem localDecls layouts)
      (Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue
        locals (.nullaryOp op argTy) mem localDecls layouts) ∧
    evalNullaryOp locals op argTy mem localDecls layouts ≠ .ub := by
  refine ⟨Or.inl rfl, ?_⟩
  rcases argTy with ⟨kind, lIdx⟩
  unfold evalNullaryOp
  dsimp only
  cases op with
  | sizeOf =>
    cases intrinsicRigidTyByteSize localDecls layouts kind with
    | none => intro h; nomatch h
    | some sz =>
      dsimp only
      cases Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1) <;>
        (intro h; nomatch h)
  | alignOf =>
    cases intrinsicRigidTyByteSize localDecls layouts kind with
    | none => intro h; nomatch h
    | some sz =>
      cases intrinsicRigidTyAlign localDecls layouts kind with
      | none => intro h; nomatch h
      | some align =>
        dsimp only
        cases Bool.and
            (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
            (Bool.not (Nat.beq align 0)) <;>
          (intro h; nomatch h)
  | offsetOf fields =>
    cases intrinsicRigidTyByteSize localDecls layouts kind with
    | none => intro h; nomatch h
    | some sz =>
      dsimp only
      cases resolveTupleOffsetOf (intrinsicRigidTyByteSize localDecls layouts) kind fields with
      | none => intro h; nomatch h
      | some offset =>
        dsimp only
        cases Bool.and
            (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes layouts)) 2) 1))
            (Nat.ble offset sz) <;>
          (intro h; nomatch h)
  | ubChecks =>
    cases kind <;> (intro h; nomatch h)
  | contractChecks =>
    intro h; nomatch h

/-- **`UbChecks` Agreement With `Terminators.lean` (`evalNullaryOp_ubChecks_matches_intrinsic`)**:
Evaluating `NullOp.ubChecks` on `RigidTy.bool` yields `.ok (.scalar ⟨1, 1⟩) locals mem`,
and writing its return value via `writeIntrinsicReturn` agrees identically with
`Trusted.Rustc.V2026_06_01.MirSemantics.evalNonSelectIntrinsicCall .ubChecks`
(`Terminators.lean:1963`). -/
theorem evalNullaryOp_ubChecks_matches_intrinsic
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (lIdx : Nat) :
    evalNullaryOp locals' .ubChecks { kind := .bool, layoutIdx := lIdx }
      s.memory bodyLocalDecls bodyLayouts =
      .ok (.scalar ⟨1, 1⟩) locals' s.memory ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalNonSelectIntrinsicCall
      .ubChecks s target bodyLocalDecls bodyLayouts argOps .nil
      locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar ⟨1, 1⟩) := by
  exact ⟨rfl, rfl⟩


/-! ## Section 4: Stateful `LocalSlotState`, `D9` `PlaceMention`, `D13b` Partial Shells, `SetDiscriminant`, `Assume` & `Statements.lean` Correspondence -/

/-- Initialization state of a single field inside a [`PartialAggregate`] (`D13b`,
matching `FieldSlot` in `crates/anneal-mir/src/lower/rvalue.rs`).
Tracks uninitialized sibling fields explicitly so unwritten `()` (`Ty::Tuple([])`)
fields are never confused with initialized `Value.unit` values. -/
inductive FieldSlot : Type where
  /-- Field has not yet been written (or has been moved out of). -/
  | uninit : FieldSlot
  /-- Field is itself a partially initialized tuple or ADT shell. -/
  | nested
      (variantIdx : VariantIdx)
      (isAdt : Bool)
      (discriminantSet : Bool)
      (fields : List FieldSlot) : FieldSlot
  /-- Field holds a fully initialized `Value`. -/
  | init (val : Value) : FieldSlot

/-- Partially initialized tuple, struct, or enum variant shell (`D13b`,
matching `PartialAggregate` in `crates/anneal-mir/src/lower/rvalue.rs`). -/
structure PartialAggregate : Type where
  /-- Active variant index (`0` for tuples and single-variant structs; `v` for enum variants). -/
  variantIdx : VariantIdx
  /-- True when this shell represents an enum/ADT variant rather than a plain tuple. -/
  isAdt : Bool
  /-- True once `StatementKind.setDiscriminant` has written this shell's variant tag. -/
  discriminantSet : Bool
  /-- Per-field initialization states in declaration order. -/
  fields : List FieldSlot

/-- Per-local lifecycle and initialization state for statement-level MIR evaluation
(`LocalSlotState` in `crates/anneal-mir/src/lower/rvalue.rs`). -/
inductive LocalSlotState : Type where
  /-- Local storage is not live (`StorageDead`). -/
  | dead : LocalSlotState
  /-- Local storage is live (`StorageLive`) and completely uninitialized. -/
  | uninit : LocalSlotState
  /-- Local holds a partially initialized tuple or ADT shell (`D13b`). -/
  | partialShell (shell : PartialAggregate) : LocalSlotState
  /-- Local holds a fully initialized `Value`. -/
  | init (val : Value) : LocalSlotState

/-- Construct a list of `n` `.uninit` `FieldSlot`s. -/
def replicateUninitFieldSlots : Nat → List FieldSlot
  | .zero => .nil
  | .succ k => .uninit :: replicateUninitFieldSlots k

/-- Length of `replicateUninitFieldSlots n` is `n`. -/
@[simp]
theorem length_replicateUninitFieldSlots (n : Nat) :
    (replicateUninitFieldSlots n).length = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [replicateUninitFieldSlots, ih]

/-- Every element of `replicateUninitFieldSlots n` at `i < n` is `.uninit`. -/
theorem get?_replicateUninitFieldSlots
    {n i : Nat}
    (hLt : i < n) :
    get? (replicateUninitFieldSlots n) i = .some .uninit := by
  induction n generalizing i with
  | zero => omega
  | succ k ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      simp only [replicateUninitFieldSlots, get?_eq_getElem?, List.getElem?_cons_succ]
      exact ih (by omega)

/-- Create an all-uninitialized tuple/ADT shell with `fieldCount` fields and an
unwritten variant tag (`discriminantSet = false`). -/
def PartialAggregate.newUninit
    (fieldCount : Nat)
    (variantIdx : VariantIdx := 0)
    (isAdt : Bool := false) :
    PartialAggregate :=
  { variantIdx := variantIdx
    isAdt := isAdt
    discriminantSet := false
    fields := replicateUninitFieldSlots fieldCount }

/-- Extract a list of initialized `Value`s when every slot in `slots` is
`FieldSlot.init`, returning `.none` if any slot is `.uninit` or `.nested`. -/
def tryFieldsIntoValues? : List FieldSlot → Option (List Value)
  | .nil => .some .nil
  | .init v :: rest =>
    match tryFieldsIntoValues? rest with
    | .some vs => .some (v :: vs)
    | .none => .none
  | .uninit :: _ => .none
  | .nested _ _ _ _ :: _ => .none

/-- Promote a `PartialAggregate` shell to `Value.aggregate` if every field in
`shell.fields` is `FieldSlot.init` and, for an enum/ADT shell (`isAdt = true`),
the variant tag has been written by `SetDiscriminant` (`discriminantSet = true`),
matching `PartialAggregate::try_into_mir_value` in `crates/anneal-mir`. -/
def PartialAggregate.tryIntoValue? (shell : PartialAggregate) : Option Value :=
  match Bool.and shell.isAdt (Bool.not shell.discriminantSet) with
  | true => .none
  | false =>
    match tryFieldsIntoValues? shell.fields with
    | .some initFields =>
      let vIdx :=
        match shell.isAdt with
        | true => shell.variantIdx
        | false => 0
      .some (.aggregate vIdx initFields)
    | .none => .none

/-- Erase a `LocalSlotState` to `Trusted.MirSemantics.LocalSlot` when no
incomplete `PartialShell` is present. -/
def LocalSlotState.toTrustedSlot? : LocalSlotState → Option LocalSlot
  | .dead => .some .dead
  | .uninit => .some .uninit
  | .init v => .some (.init v)
  | .partialShell shell =>
    match shell.tryIntoValue? with
    | .some v => .some (.init v)
    | .none => .none

/-- If any slot in `slots` is `.uninit` (`get? slots i = .some .uninit`),
`tryFieldsIntoValues? slots` returns `.none`. -/
theorem tryFieldsIntoValues?_eq_none_of_get?_uninit :
    ∀ (slots : List FieldSlot) (i : Nat),
      get? slots i = .some .uninit →
      tryFieldsIntoValues? slots = .none := by
  intro slots
  induction slots with
  | nil =>
    intro i hGet
    nomatch hGet
  | cons hd tl ih =>
    intro i hGet
    cases i with
    | zero =>
      simp only [get?_eq_getElem?, List.getElem?_cons_zero] at hGet
      injection hGet with hEq
      subst hEq
      rfl
    | succ i' =>
      simp only [get?_eq_getElem?, List.getElem?_cons_succ] at hGet
      have hTl := ih i' hGet
      cases hd with
      | uninit => rfl
      | nested _ _ _ _ => rfl
      | init v =>
        unfold tryFieldsIntoValues?
        rw [hTl]

/-- **Soundness Theorem (`tryIntoValue?_eq_none_of_uninit_field`)**:
If any field `i` of a `PartialAggregate` shell is still `FieldSlot.uninit`
(including an unwritten `()` unit-typed sibling field), `shell.tryIntoValue?`
returns `.none` and never promotes to an initialized `Value`. -/
theorem tryIntoValue?_eq_none_of_uninit_field
    (shell : PartialAggregate)
    (i : Nat)
    (hUninit : get? shell.fields i = .some .uninit) :
    shell.tryIntoValue? = .none := by
  unfold PartialAggregate.tryIntoValue?
  rw [tryFieldsIntoValues?_eq_none_of_get?_uninit shell.fields i hUninit]
  cases Bool.and shell.isAdt (Bool.not shell.discriminantSet) <;> rfl

/-- **Soundness Theorem (`tryIntoValue?_eq_none_of_untagged_adt`)**:
An enum/ADT shell (`shell.isAdt = true`) whose discriminant tag has not yet been
written by `SetDiscriminant` (`shell.discriminantSet = false`) never promotes
(`shell.tryIntoValue? = .none`), even if every field of the variant has been
initialized. -/
theorem tryIntoValue?_eq_none_of_untagged_adt
    (shell : PartialAggregate)
    (hAdt : shell.isAdt = true)
    (hUntagged : shell.discriminantSet = false) :
    shell.tryIntoValue? = .none := by
  unfold PartialAggregate.tryIntoValue?
  rw [hAdt, hUntagged]
  rfl

/-- Mapping `FieldSlot.init` over a list of `Value`s succeeds in
`tryFieldsIntoValues?` and recovers the exact list of `Value`s. -/
@[simp]
theorem tryFieldsIntoValues?_map_init (vals : List Value) :
    tryFieldsIntoValues? (vals.map FieldSlot.init) = .some vals := by
  induction vals with
  | nil => rfl
  | cons v vs ih =>
    simp [tryFieldsIntoValues?, ih]

/-- **Full-Initialization Promotion Equivalence (`tryIntoValue?_of_all_init`)**:
Once every field of `shell` is initialized (`shell.fields = vals.map FieldSlot.init`)
and either `shell` is a tuple/struct (`shell.isAdt = false`) or its enum variant
tag has been written (`shell.discriminantSet = true`), `shell.tryIntoValue?`
promotes to `.some (.aggregate (if shell.isAdt then shell.variantIdx else 0) vals)`. -/
theorem tryIntoValue?_of_all_init
    (shell : PartialAggregate)
    (vals : List Value)
    (hFields : shell.fields = vals.map FieldSlot.init)
    (hTagOk : shell.isAdt = false ∨ shell.discriminantSet = true) :
    shell.tryIntoValue? =
      .some (.aggregate (match shell.isAdt with | true => shell.variantIdx | false => 0) vals) := by
  unfold PartialAggregate.tryIntoValue?
  rw [hFields, tryFieldsIntoValues?_map_init]
  rcases hTagOk with hNotAdt | hTagged
  · rw [hNotAdt]
    rfl
  · rw [hTagged]
    cases shell.isAdt <;> rfl

/-- Read a projected value from a `PartialAggregate` shell (`read_from_partial_shell`
in `crates/anneal-mir/src/lower/rvalue.rs`). -/
def readFromPartialShell
    (locals : List LocalSlot)
    (shell : PartialAggregate)
    (proj : List ProjectionElem) :
    ProjReadResult :=
  match proj with
  | .nil =>
    match shell.tryIntoValue? with
    | .some v => .ok v
    | .none => .ub
  | .downcast _ variantIdx :: rest =>
    let actual := match shell.isAdt with | true => shell.variantIdx | false => 0
    match Bool.and (isFieldHead rest) (Nat.beq actual variantIdx) with
    | true =>
      match rest with
      | .field idx _ :: tail =>
        match get? shell.fields idx with
        | .some (.init fieldVal) => evalValueProjRead locals fieldVal tail
        | .some .uninit => .ub
        | .some (.nested _ _ _ _) => .ub
        | .none => .ub
      | _ => .ub
    | false => .ub
  | .field idx _ :: rest =>
    let actual := match shell.isAdt with | true => shell.variantIdx | false => 0
    match Nat.beq actual 0 with
    | true =>
      match get? shell.fields idx with
      | .some (.init fieldVal) => evalValueProjRead locals fieldVal rest
      | .some .uninit => .ub
      | .some (.nested _ _ _ _) => .ub
      | .none => .ub
    | false => .ub
  | .index _ :: _ => .ub
  | .constantIndex _ _ _ :: _ => .ub
  | .subslice _ _ _ :: _ => .ub
  | _ :: _ => .unsupported

/-- **No False-Accept on Unwritten `()` Sibling Fields (`readFromPartialShell_uninit_sibling_ub`)**:
In `Trusted.MirSemantics.setOrExtendFields`, initializing field `1` of an
uninitialized pair `((), u32)` extends field `0` with `Value.unit`, which would
allow reading `_1.0` as `.ok .unit` even though `_1.0` was never written.
In `PartialAggregate`, field `0` remains `FieldSlot.uninit`, so both reading the
whole local (`proj = []`) and reading the unwritten sibling field
(`proj = .field uninitIdx ty :: rest`) fault with `.ub` (`UninitializedLocal`),
while reading the written field `initIdx` succeeds with `.ok v`! -/
theorem readFromPartialShell_uninit_sibling_soundness
    (locals : List LocalSlot)
    (shell : PartialAggregate)
    (uninitIdx initIdx : FieldIdx)
    (tyU tyI : Ty)
    (rest : List ProjectionElem)
    (v outVal : Value)
    (hTupleOrVariant0 : (match shell.isAdt with | true => shell.variantIdx | false => 0) = 0)
    (hUninitSlot : get? shell.fields uninitIdx = .some .uninit)
    (hInitSlot : get? shell.fields initIdx = .some (.init v))
    (hSubRead : evalValueProjRead locals v rest = .ok outVal) :
    readFromPartialShell locals shell .nil = .ub ∧
    readFromPartialShell locals shell (.field uninitIdx tyU :: rest) = .ub ∧
    readFromPartialShell locals shell (.field initIdx tyI :: rest) = .ok outVal := by
  have hWholeNone : shell.tryIntoValue? = .none :=
    tryIntoValue?_eq_none_of_uninit_field shell uninitIdx hUninitSlot
  refine ⟨?_, ?_, ?_⟩
  · unfold readFromPartialShell
    rw [hWholeNone]
  · unfold readFromPartialShell
    rw [hTupleOrVariant0]
    dsimp only
    rw [hUninitSlot]
  · unfold readFromPartialShell
    rw [hTupleOrVariant0]
    dsimp only
    rw [hInitSlot]
    exact hSubRead

/-- Apply `StatementKind.setDiscriminant` at the root of a `PartialAggregate`
shell, setting `variantIdx := variantIdx`, `isAdt := true`, and
`discriminantSet := true`, and promoting to `LocalSlotState.init` if all
variant fields are already initialized. -/
def setDiscriminantOnShell
    (shell : PartialAggregate)
    (variantIdx : VariantIdx) :
    LocalSlotState :=
  let updated : PartialAggregate :=
    { shell with
      variantIdx := variantIdx
      isAdt := true
      discriminantSet := true }
  match updated.tryIntoValue? with
  | .some fullVal => .init fullVal
  | .none => .partialShell updated

/-- **`SetDiscriminant` Promotion Theorem (`setDiscriminantOnShell_promotes_initialized_variant`)**:
In `rustc` MIR, enum initialization writes each payload field via
`((_1 as V).i) = v_i` (leaving `discriminantSet = false`, so premature whole-enum
reads fail with `.ub`) and then executes `discriminant(_1) = V`.
Once all fields are `.init` (`shell.fields = vals.map FieldSlot.init`),
`setDiscriminantOnShell shell variantIdx` promotes the shell to
`LocalSlotState.init (.aggregate variantIdx vals)` (including 0-field unit enum
variants when `vals = []`). -/
theorem setDiscriminantOnShell_promotes_initialized_variant
    (shell : PartialAggregate)
    (variantIdx : VariantIdx)
    (vals : List Value)
    (hFields : shell.fields = vals.map FieldSlot.init) :
    (shell.isAdt = true →
      shell.discriminantSet = false →
      readFromPartialShell .nil shell .nil = .ub) ∧
    setDiscriminantOnShell shell variantIdx =
      .init (.aggregate variantIdx vals) := by
  refine ⟨?_, ?_⟩
  · intro hAdt hUntagged
    unfold readFromPartialShell
    rw [tryIntoValue?_eq_none_of_untagged_adt shell hAdt hUntagged]
  · unfold setDiscriminantOnShell
    dsimp only
    have hProm :
        PartialAggregate.tryIntoValue?
          { variantIdx := variantIdx
            isAdt := true
            discriminantSet := true
            fields := shell.fields } =
          .some (.aggregate variantIdx vals) := by
      unfold PartialAggregate.tryIntoValue?
      dsimp only
      rw [hFields, tryFieldsIntoValues?_map_init]
      rfl
    rw [hProm]

/-- **Bare vs. Projected `Operand.move` Correspondence (`evalOperand_move_bare_vs_projected_correspondence`)**:
1. Moving a bare local (`p.projection = .nil`) reads `v` and transitions `p.local_`
   from `.init v` to `.uninit`.
2. Moving a projected non-`Deref` place (`p.projection = proj :: rest` with
   `proj ≠ .deref`) reads the projected sub-value `outVal` and leaves the root
   local `p.local_` initialized to `.init rootVal` (`locals` unchanged), matching
   Episode 1 `[adv B1]` (`ec5df9f4`). -/
theorem evalOperand_move_bare_vs_projected_correspondence
    (locals locals' : List LocalSlot)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (rootVal outVal : Value)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    (callerLocals : List LocalSlot) :
    (get? locals loc = .some (.init rootVal) →
      set? locals loc .uninit = .some locals' →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
        locals (.move ⟨loc, .nil⟩) borrows globals layouts callerLocals =
        .ok rootVal locals') ∧
    (proj ≠ .deref →
      get? locals loc = .some (.init rootVal) →
      evalValueProjRead locals rootVal (proj :: rest) = .ok outVal →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
        locals (.move ⟨loc, proj :: rest⟩) borrows globals layouts callerLocals =
        .ok outVal locals) := by
  refine ⟨?_, ?_⟩
  · intro hGet hSet
    dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
    rw [hGet]
    dsimp only
    rw [hSet]
  · intro hNotDeref hGet hProjRead
    have hTrustedRead :=
      evalValueProjRead_refines_readProjectedValue (proj :: rest) locals rootVal outVal hProjRead
    cases proj with
    | deref => exact False.elim (hNotDeref rfl)
    | _ =>
      dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
      rw [hGet]
      dsimp only
      rw [hTrustedRead]

/-- Statement-level evaluator for `StatementKind.placeMention` (`D9`). -/
def evalPlaceMention (s : MachineState) (place : Place) : MirStepNode :=
  match get? s.frame.locals place.local_ with
  | .none => MirStepNode.fail .ub
  | .some .dead => MirStepNode.fail .ub
  | .some rootSlot =>
    match placeMentionOperandsInit s.frame.locals rootSlot place.projection with
    | true => MirStepNode.step (advanceStmt s s.frame.locals)
    | false => MirStepNode.fail .ub

/-- **`D9` `PlaceMention` Correspondence (`evalPlaceMention_trusted_correspondence`)**:
`evalPlaceMention` agrees identically with
`Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt` on `StatementKind.placeMention`:
1. Exact definitional equality for all machine states `s` and places `place`.
2. On a non-dereferencing projection (`projectionHasDeref place.projection = false`),
   `evalPlaceMention` succeeds (preserving all locals and memory unchanged) on both
   `.uninit` and `.init` root locals if and only if all `.index idxLocal` operands
   along `place.projection` hold initialized scalars (`placeIndexLocalsInit = true`).
3. On a dead or out-of-bounds root local, or on `.deref` when the root local is
   `.uninit`, `evalPlaceMention` faults with `MirStepNode.fail .ub`. -/
theorem evalPlaceMention_trusted_correspondence
    (s : MachineState)
    (place : Place)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    evalPlaceMention s place =
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.placeMention place, span⟩ localDecls layouts ∧
    (∀ rootSlot : LocalSlot,
      get? s.frame.locals place.local_ = .some rootSlot →
      rootSlot ≠ .dead →
      projectionHasDeref place.projection = false →
      (Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
          s ⟨.placeMention place, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s s.frame.locals) ↔
        placeIndexLocalsInit s.frame.locals place.projection = true)) ∧
    (get? s.frame.locals place.local_ = .some .dead →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.placeMention place, span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro rootSlot hSlot hLive hNoDeref
    exact (evalStmt_placeMention_nonDeref_index_iff
      s place.local_ rootSlot place.projection span localDecls layouts
      hNoDeref hSlot hLive).1
  · intro hDead
    dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
    rw [hDead]

/-- Statement-level evaluator for `StatementKind.intrinsic (.assume op)`. -/
def evalAssume
    (s : MachineState)
    (op : Operand)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
      s.frame.locals
      op
      s.memory.borrows
      s.memory.globals
      layouts
      s.memory.callerLocals
  with
  | .ok (.scalar sc) locals' =>
    match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
    | true => MirStepNode.step (advanceStmt s locals')
    | false => MirStepNode.fail .ub
  | .ok _ _ => MirStepNode.fail .ub
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/-- **`Assume` Correspondence (`evalAssume_trusted_correspondence`)**:
`evalAssume` agrees identically with
`Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt` on `.intrinsic (.assume op)`:
- Evaluating boolean `true` (`.scalar ⟨1, 1⟩`) steps to `advanceStmt s locals'`.
- Evaluating boolean `false` (`.scalar ⟨0, 1⟩`) or any other bit pattern faults
  immediately with `MirStepNode.fail .ub`. -/
theorem evalAssume_trusted_correspondence
    (s : MachineState)
    (op : Operand)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals' : List LocalSlot) :
    evalAssume s op layouts =
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.intrinsic (.assume op), span⟩ localDecls layouts ∧
    (Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
        s.frame.locals op s.memory.borrows s.memory.globals layouts s.memory.callerLocals =
        .ok (.scalar ⟨1, 1⟩) locals' →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.intrinsic (.assume op), span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s locals')) ∧
    (Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
        s.frame.locals op s.memory.borrows s.memory.globals layouts s.memory.callerLocals =
        .ok (.scalar ⟨0, 1⟩) locals' →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.intrinsic (.assume op), span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro hTrue
    dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
    rw [hTrue]
    rfl
  · intro hFalse
    dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
    rw [hFalse]
    rfl

/-- **`SetDiscriminant` Bare & Projected Correspondence (`evalStmt_setDiscriminant_correspondence`)**:
1. On a bare local (`p.projection = .nil`) holding `.init (.aggregate oldVar fields)`,
   `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt` updates the local in place to
   `.init (.aggregate variantIdx fields)` (including 0-field unit enum variants where
   `fields = .nil`).
2. On a projected non-`Deref` place (`p.projection = proj :: rest`, `proj ≠ .deref`)
   where reading `proj :: rest` from `rootVal` yields `.aggregate oldVar fields`
   and writing `.aggregate variantIdx fields` back along `proj :: rest` yields `rootVal'`,
   `evalStmt` updates `p.local_` to `.init rootVal'` and steps. -/
theorem evalStmt_setDiscriminant_correspondence
    (s : MachineState)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (variantIdx oldVar : VariantIdx)
    (fields : List Value)
    (rootVal rootVal' : Value)
    (locals' : List LocalSlot)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    (get? s.frame.locals loc = .some (.init (.aggregate oldVar fields)) →
      set? s.frame.locals loc (.init (.aggregate variantIdx fields)) = .some locals' →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.setDiscriminant ⟨loc, .nil⟩ variantIdx, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s locals')) ∧
    (proj ≠ .deref →
      get? s.frame.locals loc = .some (.init rootVal) →
      evalValueProjRead s.frame.locals rootVal (proj :: rest) =
        .ok (.aggregate oldVar fields) →
      evalValueProjWrite s.frame.locals rootVal (proj :: rest)
        (.aggregate variantIdx fields) = .ok rootVal' →
      set? s.frame.locals loc (.init rootVal') = .some locals' →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.setDiscriminant ⟨loc, proj :: rest⟩ variantIdx, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s locals')) := by
  refine ⟨?_, ?_⟩
  · intro hGet hSet
    dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
    rw [hGet]
    dsimp only
    rw [hSet]
  · intro hNotDeref hGet hRead hWrite hSet
    have hTrustedRead :=
      evalValueProjRead_refines_readProjectedValue
        (proj :: rest) s.frame.locals rootVal (.aggregate oldVar fields) hRead
    have hTrustedWrite :=
      evalValueProjWrite_refines_writeProjectedValue
        (proj :: rest) s.frame.locals rootVal (.aggregate variantIdx fields) rootVal' hWrite
    cases proj with
    | deref => exact False.elim (hNotDeref rfl)
    | _ =>
      dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt,
        Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand,
        Trusted.Rustc.V2026_06_01.MirSemantics.writePlaceValue]
      rw [hGet]
      dsimp only
      rw [hTrustedRead]
      dsimp only
      rw [hGet]
      dsimp only
      rw [hTrustedWrite]
      dsimp only
      rw [hSet]

/-- **`D13b` Uninitialized Array Write Rejection (`evalStmt_assign_uninit_array_proj_ub`)**:
Writing to an element (`.index` or `.constantIndex`) or window (`.subslice`) of a
live but uninitialized array local (`get? locals₁ dstLoc = .some .uninit`)
always faults with `MirStepNode.fail .ub` (`c6d2ad74`). -/
theorem evalStmt_assign_uninit_array_proj_ub
    (s : MachineState)
    (dstLoc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (hRv :
      Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue
        s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hArrProj :
      (∃ idxLocal, proj = .index idxLocal) ∨
      (∃ offset minLen fromEnd, proj = .constantIndex offset minLen fromEnd) ∨
      (∃ fromIdx toIdx fromEnd, proj = .subslice fromIdx toIdx fromEnd)) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
      s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.fail .ub := by
  have hNotDeref : proj ≠ .deref := by
    rcases hArrProj with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> intro h <;> nomatch h
  have hNoShell : uninitFieldWriteShell? localDecls layouts dstLoc proj = .none := by
    rcases hArrProj with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  exact evalStmt_assign_uninit_non_aggregate_ub
    s dstLoc proj rest rv span localDecls layouts val locals₁ mem₁
    hNotDeref hRv hUninit hNoShell

/-- **`D13b` Two-Field Tuple/Struct Initialization Equivalence (`evalStmt_two_field_init_promotion_correspondence`)**:
When an uninitialized 2-field tuple or struct local `dstLoc` is initialized
field-by-field (`_1.0 = v0` followed by `_1.1 = v1`):
1. In `PartialAggregate`, after writing field `0` (`[FieldSlot.init v0, FieldSlot.uninit]`),
   the shell remains in `LocalSlotState.partialShell` (`tryIntoValue? = .none` and
   reading unwritten field `1` returns `.ub`), and after writing field `1`
   (`[FieldSlot.init v0, FieldSlot.init v1]`), `tryIntoValue?` promotes to
   `.some (.aggregate 0 [v0, v1])`.
2. In `Trusted.Rustc.V2026_06_01.MirSemantics`, writing `.field 0 ty0` into the
   `uninitFieldWriteShell?` shell `.aggregate 0 []` produces `.aggregate 0 [v0]`,
   and writing `.field 1 ty1` into `.aggregate 0 [v0]` produces the exact same
   final aggregate `.aggregate 0 [v0, v1]`! -/
theorem two_field_init_promotion_correspondence
    (locals : List LocalSlot)
    (ty0 ty1 : Ty)
    (v0 v1 : Value) :
    let shellAfter0 : PartialAggregate :=
      { variantIdx := 0, isAdt := false, discriminantSet := false,
        fields := [.init v0, .uninit] }
    let shellAfter01 : PartialAggregate :=
      { variantIdx := 0, isAdt := false, discriminantSet := false,
        fields := [.init v0, .init v1] }
    shellAfter0.tryIntoValue? = .none ∧
    readFromPartialShell locals shellAfter0 [.field 1 ty1] = .ub ∧
    readFromPartialShell locals shellAfter0 [.field 0 ty0] = .ok v0 ∧
    shellAfter01.tryIntoValue? = .some (.aggregate 0 [v0, v1]) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
      locals (.aggregate 0 .nil) [.field 0 ty0] v0 =
      .ok (.aggregate 0 [v0]) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
      locals (.aggregate 0 [v0]) [.field 1 ty1] v1 =
      .ok (.aggregate 0 [v0, v1]) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Anneal.Mir.PlaceAndRvalue
