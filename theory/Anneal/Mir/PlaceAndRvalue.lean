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
   - Alignment rounding (`alignUp`), Episode 1's canonical-byte-layout gate
     (`rigidTyHasCanonicalByteLayout`, mirroring `Ty::has_canonical_byte_layout`),
     canonical tuple field-offset resolution (`resolveTupleOffsetOf`), and
     `evalNullaryOp` (`.sizeOf`, `.alignOf`, `.offsetOf`, `.ubChecks`).
   - Arithmetic and layout invariants (non-zero tuple variant rejection,
     out-of-bounds field rejection, non-canonical layout rejection, prefix offset
     monotonicity, field offset + field size bounded by tuple size, field
     alignment dividing the field offset, `ubChecks` evaluating to `⟨1, 1⟩`).
   - Unsupported-shrinking refinement against
     `Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue (.nullaryOp op ty)`, and
     value-level agreement with the Trusted `size_of_val` / `align_of_val` /
     `ub_checks` intrinsics in `Terminators.lean`.

4. **Section 4 — Stateful `LocalSlotState`, `D9` `PlaceMention`, `D13b` Partial Shells, `SetDiscriminant`, `Assume` & `Statements.lean` Correspondence**:
   - Per-field initialization slots (`FieldSlot`), partially initialized
     tuple/struct/enum shells (`PartialAggregate` with `discriminantSet` tag
     gating and `tryIntoValue?` promotion), and `LocalSlotState` (`dead`,
     `uninit`, `partialShell`, `init`).
   - Partial-shell soundness theorems: unwritten `()` sibling fields and tagless
     enum shells never promote (`tryIntoValue? = .none`) and fault on reads
     (eliminating `.unit`-placeholder false accepts), `SetDiscriminant` to a
     different variant resets previously written payload fields (no variant
     reinterpretation), array element writes on `.uninit` fault (`c6d2ad74`),
     and full field + tag initialization promotes to
     `Value.aggregate variantIdx fields`.
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

/-- Well-formedness predicate for a pure value-tree read target `(val, proj)`
where `evalValueProjRead` and `Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue`
agree identically on all outcomes (`.ok`, `.ub`, `.unsupported`):
- No `.deref`, `.opaqueCast`, or `.unwrapUnsafeBinder` projections;
- Every `.downcast` is immediately followed by `.field` (`isFieldHead rest = true`);
- Every `.field` targets an `.aggregate` value (excluding transparent `.field 0` on
  `.scalar`, `.ptr`, or `.unit`);
- Every `fromEnd = true` `.constantIndex offset minLen true` satisfies `1 ≤ offset ≤ minLen`. -/
def WfValueReadTarget (locals : List LocalSlot) : Value → List ProjectionElem → Bool
  | _, .nil => true
  | .aggregate _ fields, .field idx _ :: rest =>
    match get? fields idx with
    | .some fieldVal => WfValueReadTarget locals fieldVal rest
    | .none => true
  | _, .field _ _ :: _ => false
  | .aggregate actualVariant fields, .downcast _ variantIdx :: rest =>
    Bool.and (isFieldHead rest)
      (match Nat.beq actualVariant variantIdx with
       | true => WfValueReadTarget locals (.aggregate actualVariant fields) rest
       | false => true)
  | _, .downcast _ _ :: _ => true
  | .aggregate .zero fields, .index idxLocal :: rest =>
    match get? locals idxLocal with
    | .some (.init (.scalar sc)) =>
      match get? fields sc.bits with
      | .some elemVal => WfValueReadTarget locals elemVal rest
      | .none => true
    | _ => true
  | _, .index _ :: _ => true
  | .aggregate .zero fields, .constantIndex offset minLen fromEnd :: rest =>
    let wfFromEnd :=
      match fromEnd with
      | true => Bool.and (Nat.ble 1 offset) (Nat.ble offset minLen)
      | false => true
    Bool.and wfFromEnd
      (match evalConstantIndex (length fields) offset minLen fromEnd with
       | .some idx =>
         match get? fields idx with
         | .some elemVal => WfValueReadTarget locals elemVal rest
         | .none => true
       | .none => true)
  | _, .constantIndex _ _ _ :: _ => true
  | .aggregate .zero fields, .subslice fromIdx toIdx fromEnd :: rest =>
    match extractSubslice fields fromIdx toIdx fromEnd with
    | .some subElems => WfValueReadTarget locals (.aggregate .zero subElems) rest
    | .none => true
  | _, .subslice _ _ _ :: _ => true
  | _, .deref :: _ => false
  | _, .opaqueCast _ :: _ => false
  | _, .unwrapUnsafeBinder _ :: _ => false

/-- **Read Completeness & Exact Outcome Agreement (`evalValueProjRead_eq_readProjectedValue_of_wf`)**:
Whenever `WfValueReadTarget locals val proj = true`, `evalValueProjRead` and
`Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue` produce the exact
same `ProjReadResult` (hence `evalValueProjRead locals val proj = .ok outVal ↔
readProjectedValue locals val proj = .ok outVal`). -/
theorem evalValueProjRead_eq_readProjectedValue_of_wf :
    ∀ (proj : List ProjectionElem) (locals : List LocalSlot) (val : Value),
      WfValueReadTarget locals val proj = true →
      evalValueProjRead locals val proj =
        Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue locals val proj := by
  intro proj
  induction proj with
  | nil =>
    intro locals val _
    rfl
  | cons p rest ih =>
    intro locals val hWf
    cases p with
    | field idx ty =>
      cases val with
      | aggregate variantIdx fields =>
        dsimp only [WfValueReadTarget] at hWf
        dsimp only [evalValueProjRead, Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue]
        cases hGet : get? fields idx with
        | none => rfl
        | some fieldVal =>
          rw [hGet] at hWf
          exact ih locals fieldVal hWf
      | _ => nomatch hWf
    | downcast vName variantIdx =>
      cases val with
      | aggregate actualVariant fields =>
        dsimp only [WfValueReadTarget] at hWf
        have ⟨hHead, hWfRest⟩ := Bool.and_eq_true_iff.mp hWf
        dsimp only [evalValueProjRead, Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue]
        rw [hHead]
        cases hEq : Nat.beq actualVariant variantIdx with
        | false => rfl
        | true =>
          rw [hEq] at hWfRest
          dsimp only
          exact ih locals (.aggregate actualVariant fields) hWfRest
      | _ => rfl
    | index idxLocal =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [WfValueReadTarget] at hWf
          dsimp only [evalValueProjRead]
          rw [readProjectedValue_index_zero]
          cases hLoc : get? locals idxLocal with
          | none => rfl
          | some slot =>
            rw [hLoc] at hWf
            cases slot with
            | dead => rfl
            | uninit => rfl
            | init idxVal =>
              cases idxVal with
              | scalar sc =>
                dsimp only at hWf ⊢
                cases hElem : get? fields sc.bits with
                | none => rfl
                | some elemVal =>
                  rw [hElem] at hWf
                  exact ih locals elemVal hWf
              | _ => rfl
        | succ _ => rfl
      | _ => rfl
    | constantIndex offset minLen fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [WfValueReadTarget] at hWf
          have ⟨hFromEndWf, hWfRest⟩ := Bool.and_eq_true_iff.mp hWf
          dsimp only [evalValueProjRead]
          rw [readProjectedValue_constantIndex_zero]
          dsimp only
          unfold evalConstantIndex at hWfRest ⊢
          cases hMin : Nat.ble minLen (length fields) with
          | false => rfl
          | true =>
            rw [hMin] at hWfRest
            dsimp only at hWfRest ⊢
            cases fromEnd with
            | false =>
              cases hOff : Nat.ble (Nat.succ offset) (length fields) with
              | false =>
                dsimp only
                have hNotLt : ¬ offset < fields.length := by
                  intro hLt
                  have hBle : Nat.ble (Nat.succ offset) (length fields) = true :=
                    Nat.ble_eq.mpr hLt
                  rw [hOff] at hBle
                  nomatch hBle
                have hGe : fields.length ≤ offset := Nat.le_of_not_lt hNotLt
                have hNone : get? fields offset = .none := by
                  simp [get?_eq_getElem?, List.getElem?_eq_none hGe]
                rw [hNone]
              | true =>
                rw [hOff] at hWfRest
                dsimp only at hWfRest ⊢
                cases hElem : get? fields offset with
                | none => rfl
                | some elemVal =>
                  rw [hElem] at hWfRest
                  exact ih locals elemVal hWfRest
            | true =>
              dsimp only at hFromEndWf
              have ⟨hGe1, hLeMin⟩ := Bool.and_eq_true_iff.mp hFromEndWf
              have hLeLen : Nat.ble offset (length fields) = true := by
                have h1 := Nat.le_of_ble_eq_true hLeMin
                have h2 := Nat.le_of_ble_eq_true hMin
                exact Nat.ble_eq.mpr (Nat.le_trans h1 h2)
              have hBounds : Bool.and (Nat.ble 1 offset) (Nat.ble offset (length fields)) = true := by
                rw [hGe1, hLeLen]; rfl
              rw [hBounds] at hWfRest ⊢
              dsimp only at hWfRest ⊢
              cases hElem : get? fields (Nat.sub (length fields) offset) with
              | none => rfl
              | some elemVal =>
                rw [hElem] at hWfRest
                exact ih locals elemVal hWfRest
        | succ _ => rfl
      | _ => rfl
    | subslice fromIdx toIdx fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [WfValueReadTarget] at hWf
          dsimp only [evalValueProjRead]
          rw [readProjectedValue_subslice_zero]
          cases hExt : extractSubslice fields fromIdx toIdx fromEnd with
          | none => rfl
          | some subElems =>
            rw [hExt] at hWf
            exact ih locals (.aggregate .zero subElems) hWf
        | succ _ => rfl
      | _ => rfl
    | deref => cases val <;> nomatch hWf
    | opaqueCast _ => cases val <;> nomatch hWf
    | unwrapUnsafeBinder _ => cases val <;> nomatch hWf

/-- **Write Completeness on Readable Paths (`evalValueProjWrite_iff_writeProjectedValue_of_read_ok`)**:
Whenever `proj` is a valid readable projection on `val`
(`evalValueProjRead locals val proj = .ok oldLeaf`), `evalValueProjWrite` and
`Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue` are **bidirectionally
equivalent** (`evalValueProjWrite = .ok val' ↔ writeProjectedValue = .ok val'`) for
every replacement value `newVal` and output value `val'`, with no additional
hypotheses. -/
theorem evalValueProjWrite_iff_writeProjectedValue_of_read_ok :
    ∀ (proj : List ProjectionElem) (locals : List LocalSlot) (val oldLeaf newVal val' : Value),
      evalValueProjRead locals val proj = .ok oldLeaf →
      (evalValueProjWrite locals val proj newVal = .ok val' ↔
        Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
          locals val proj newVal = .ok val') := by
  intro proj
  induction proj with
  | nil =>
    intro locals val _ newVal val' _
    exact Iff.rfl
  | cons p rest ih =>
    intro locals val oldLeaf newVal val' hRead
    refine ⟨evalValueProjWrite_refines_writeProjectedValue (p :: rest) locals val newVal val', ?_⟩
    intro hWrite
    cases p with
    | field idx ty =>
      cases val with
      | aggregate variantIdx fields =>
        dsimp only [evalValueProjRead] at hRead
        dsimp only [evalValueProjWrite]
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue] at hWrite
        cases hGet : get? fields idx with
        | none => rw [hGet] at hRead; nomatch hRead
        | some oldFieldVal =>
          rw [hGet] at hRead hWrite
          dsimp only at hWrite ⊢
          cases hSubT :
              Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
                locals oldFieldVal rest newVal with
          | ub => rw [hSubT] at hWrite; nomatch hWrite
          | unsupported => rw [hSubT] at hWrite; nomatch hWrite
          | ok updatedFieldVal =>
            rw [hSubT] at hWrite
            have hSubA : evalValueProjWrite locals oldFieldVal rest newVal = .ok updatedFieldVal :=
              (ih locals oldFieldVal oldLeaf newVal updatedFieldVal hRead).mpr hSubT
            rw [hSubA]
            exact hWrite
      | _ => nomatch hRead
    | downcast vName variantIdx =>
      cases val with
      | aggregate actualVariant fields =>
        dsimp only [evalValueProjRead] at hRead
        dsimp only [evalValueProjWrite]
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue] at hWrite
        cases hHead : isFieldHead rest with
        | false => simp [hHead] at hRead
        | true =>
          cases hEq : Nat.beq actualVariant variantIdx with
          | false => simp [hHead, hEq] at hRead
          | true =>
            rw [hHead, hEq] at hRead
            rw [hEq] at hWrite
            dsimp only at hRead hWrite ⊢
            exact (ih locals (.aggregate actualVariant fields) oldLeaf newVal val' hRead).mpr hWrite
      | _ => nomatch hRead
    | index idxLocal =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          dsimp only [evalValueProjWrite]
          rw [writeProjectedValue_index_zero] at hWrite
          cases hLoc : get? locals idxLocal with
          | none => rw [hLoc] at hRead; nomatch hRead
          | some slot =>
            rw [hLoc] at hRead hWrite
            cases slot with
            | dead => nomatch hRead
            | uninit => nomatch hRead
            | init idxVal =>
              cases idxVal with
              | scalar sc =>
                dsimp only at hRead hWrite ⊢
                cases hElem : get? fields sc.bits with
                | none => rw [hElem] at hRead; nomatch hRead
                | some oldElemVal =>
                  rw [hElem] at hRead hWrite
                  dsimp only at hWrite ⊢
                  cases hSubT :
                      Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
                        locals oldElemVal rest newVal with
                  | ub => rw [hSubT] at hWrite; nomatch hWrite
                  | unsupported => rw [hSubT] at hWrite; nomatch hWrite
                  | ok updatedElemVal =>
                    rw [hSubT] at hWrite
                    have hSubA : evalValueProjWrite locals oldElemVal rest newVal = .ok updatedElemVal :=
                      (ih locals oldElemVal oldLeaf newVal updatedElemVal hRead).mpr hSubT
                    rw [hSubA]
                    exact hWrite
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
          rw [writeProjectedValue_constantIndex_zero] at hWrite
          dsimp only at hWrite
          cases hIdx : evalConstantIndex (length fields) offset minLen fromEnd with
          | none => rw [hIdx] at hRead; nomatch hRead
          | some idx =>
            rw [hIdx] at hRead
            dsimp only at hRead ⊢
            unfold evalConstantIndex at hIdx
            cases hMin : Nat.ble minLen (length fields) with
            | false => rw [hMin] at hIdx; nomatch hIdx
            | true =>
              rw [hMin] at hIdx hWrite
              dsimp only at hIdx hWrite
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
                  | some oldElemVal =>
                    rw [hElem] at hRead hWrite
                    dsimp only at hWrite ⊢
                    cases hSubT :
                        Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
                          locals oldElemVal rest newVal with
                    | ub => rw [hSubT] at hWrite; nomatch hWrite
                    | unsupported => rw [hSubT] at hWrite; nomatch hWrite
                    | ok updatedElemVal =>
                      rw [hSubT] at hWrite
                      have hSubA : evalValueProjWrite locals oldElemVal rest newVal = .ok updatedElemVal :=
                        (ih locals oldElemVal oldLeaf newVal updatedElemVal hRead).mpr hSubT
                      rw [hSubA]
                      exact hWrite
              | true =>
                cases hBounds : Bool.and (Nat.ble 1 offset) (Nat.ble offset (length fields)) with
                | false => rw [hBounds] at hIdx; nomatch hIdx
                | true =>
                  rw [hBounds] at hIdx
                  injection hIdx with hIdxEq
                  subst hIdxEq
                  cases hElem : get? fields (Nat.sub (length fields) offset) with
                  | none => rw [hElem] at hRead; nomatch hRead
                  | some oldElemVal =>
                    rw [hElem] at hRead hWrite
                    dsimp only at hWrite ⊢
                    cases hSubT :
                        Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
                          locals oldElemVal rest newVal with
                    | ub => rw [hSubT] at hWrite; nomatch hWrite
                    | unsupported => rw [hSubT] at hWrite; nomatch hWrite
                    | ok updatedElemVal =>
                      rw [hSubT] at hWrite
                      have hSubA : evalValueProjWrite locals oldElemVal rest newVal = .ok updatedElemVal :=
                        (ih locals oldElemVal oldLeaf newVal updatedElemVal hRead).mpr hSubT
                      rw [hSubA]
                      exact hWrite
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | subslice fromIdx toIdx fromEnd =>
      cases val with
      | aggregate variantIdx fields =>
        cases variantIdx with
        | zero =>
          dsimp only [evalValueProjRead] at hRead
          dsimp only [evalValueProjWrite]
          rw [writeProjectedValue_subslice_zero] at hWrite
          cases hExt : extractSubslice fields fromIdx toIdx fromEnd with
          | none => rw [hExt] at hRead; nomatch hRead
          | some subElems =>
            rw [hExt] at hRead hWrite
            dsimp only at hWrite ⊢
            cases hSubT :
                Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
                  locals (.aggregate .zero subElems) rest newVal with
            | ub => rw [hSubT] at hWrite; nomatch hWrite
            | unsupported => rw [hSubT] at hWrite; nomatch hWrite
            | ok updatedSubVal =>
              rw [hSubT] at hWrite
              have hSubA :
                  evalValueProjWrite locals (.aggregate .zero subElems) rest newVal =
                    .ok updatedSubVal :=
                (ih locals (.aggregate .zero subElems) oldLeaf newVal updatedSubVal hRead).mpr hSubT
              rw [hSubA]
              cases updatedSubVal with
              | aggregate subVar updatedSubElems =>
                cases subVar <;> exact hWrite
              | _ => exact hWrite
        | succ _ => nomatch hRead
      | _ => nomatch hRead
    | deref => cases val <;> nomatch hRead
    | opaqueCast _ => cases val <;> nomatch hRead
    | unwrapUnsafeBinder _ => cases val <;> nomatch hRead


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

/-- Any `ScalarInt` returned by `evalCharToIntByKind` implies that the input
codepoint `bits` is a valid Unicode scalar value (both in `isValidUnicodeScalar`
and in `Trusted.Rustc.V2026_06_01.MirSemantics.isValidCharCode`). -/
theorem evalCharToIntByKind_some_implies_valid
    {bits : Nat}
    {targetKind : RigidTy}
    {outSc : ScalarInt}
    (hEval : evalCharToIntByKind bits targetKind = .some outSc) :
    isValidUnicodeScalar bits = true ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.isValidCharCode bits = true := by
  unfold evalCharToIntByKind at hEval
  cases hVal : isValidUnicodeScalar bits with
  | false => rw [hVal] at hEval; nomatch hEval
  | true =>
    exact ⟨rfl, (isValidUnicodeScalar_eq_isValidCharCode bits).symm.trans hVal⟩

/-- **Step Correspondence (`evalCharToInt_trusted_evalRvalue_correspondence`)**:
In `Runtime(PostCleanup)` MIR, `rustc` lowers `char as Int` to
`Rvalue.cast .intToInt op targetTy` on an unsigned 4-byte `RigidTy.char` operand.
Whenever `op` has type `.char` (`operandTy localDecls layouts op = .some { kind := .char, .. }`)
and evaluates to a 4-byte scalar `.scalar ⟨bits, 4⟩` (without requiring
`isValidUnicodeScalar bits = true` as an external hypothesis):
1. If `evalCharToIntByKind bits targetTy.kind = .some outSc`, then `bits` is a
   valid Unicode scalar value and
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
        .some { kind := .char, layoutIdx := charLayoutIdx }) :
    (∀ outSc : ScalarInt,
      evalCharToIntByKind bits targetTy.kind = .some outSc →
      isValidUnicodeScalar bits = true ∧
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
    have hValid := (evalCharToIntByKind_some_implies_valid hCharCast).1
    refine ⟨hValid, ?_⟩
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
      rw [hNone]
      cases isValidUnicodeScalar bits <;> rfl
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

/-! ### Canonical tuple byte layouts (`Ty::has_canonical_byte_layout` in `crates/anneal-mir/src/ir.rs`)

Episode 1's `resolve_offset_of` only answers `OffsetOf` on containers with a
*canonical byte layout*: `rustc`'s `repr(Rust)` layout is then the padding-free
concatenation of the fields in declaration order, so the byte offset of field `i`
is the unpadded prefix sum of the sizes of fields `0..i`. Without this gate the
prefix sum is wrong whenever `rustc` inserts padding or reorders fields: e.g.
`rustc 1.98` lays out `(u8, u32)` with the `u32` at byte `4`
(`offset_of!((u8, u32), 1) = 4`), while the unpadded prefix sum is `1`. -/

/-- Fuel-bounded trailing-zero count of `n` (`usize::trailing_zeros` for `n > 0`;
`0` when `n = 0` or the fuel is exhausted). -/
def natTrailingZerosAux : Nat → Nat → Nat
  | .zero, _ => 0
  | .succ fuel, n =>
    match Nat.beq n 0, Nat.beq (Nat.mod n 2) 0 with
    | false, true => Nat.succ (natTrailingZerosAux fuel (Nat.div n 2))
    | _, _ => 0

/-- `rustc`'s field-ordering alignment-group key `log2(max(align, size))`
(`Ty::alignment_group_key`: `align.max(size).trailing_zeros()`). -/
def alignmentGroupKey (size align : Nat) : Nat :=
  let m :=
    match Nat.ble align size with
    | true => size
    | false => align
  natTrailingZerosAux m m

mutual
/-- Whether a type contains a niche-bearing scalar (`bool`, `char`, `&T`) whose
in-tuple placement `rustc` may optimize (`Ty::contains_niche`). Kinds that
`anneal-mir`'s `Ty` cannot express conservatively report a niche. -/
def rigidTyContainsNiche : RigidTy → Bool
  | .int _ => false
  | .uint _ => false
  | .rawPtr _ _ => false
  | .never => false
  | .array elem n =>
    Bool.and (Bool.not (Nat.beq n 0)) (rigidTyContainsNiche elem)
  | .tuple ks => rigidTyListContainsNiche ks
  | _ => true

/-- `rigidTyContainsNiche` over a list of tuple field kinds (`any`). -/
def rigidTyListContainsNiche : List RigidTy → Bool
  | .nil => false
  | k :: ks => Bool.or (rigidTyContainsNiche k) (rigidTyListContainsNiche ks)
end

/-- Field-ordering keys `(align, alignmentGroupKey size align)` of the tuple fields
`ks` in declaration order, or `.none` if any field size or alignment is unresolved
or any alignment is `0`. -/
def tupleFieldOrderKeys?
    (fieldByteSize fieldAlign : RigidTy → Option Nat) :
    List RigidTy → Option (List (Nat × Nat))
  | .nil => .some .nil
  | k :: ks =>
    match fieldByteSize k, fieldAlign k, tupleFieldOrderKeys? fieldByteSize fieldAlign ks with
    | .some sz, .some al, .some rest =>
      match Nat.beq al 0 with
      | true => .none
      | false => .some ((al, alignmentGroupKey sz al) :: rest)
    | _, _, _ => .none

/-- Both the ABI alignments and the alignment-group keys are non-increasing in
declaration order. -/
def orderKeysNonIncreasing : List (Nat × Nat) → Bool
  | a :: b :: rest =>
    Bool.and (Nat.ble b.1 a.1)
      (Bool.and (Nat.ble b.2 a.2) (orderKeysNonIncreasing (b :: rest)))
  | _ => true

/-- Lay out the fields `ks` in declaration order starting at byte `off` without
inserting padding, requiring every field alignment to be positive (`al > 0`) and
every field offset to be a multiple of the field's alignment; returns the unpadded
end offset. -/
def tupleDeclOrderAlignedEnd?
    (fieldByteSize fieldAlign : RigidTy → Option Nat) :
    Nat → List RigidTy → Option Nat
  | off, .nil => .some off
  | off, k :: ks =>
    match fieldByteSize k, fieldAlign k with
    | .some sz, .some al =>
      match Bool.and (Bool.not (Nat.beq al 0)) (Nat.beq (Nat.mod off al) 0) with
      | true => tupleDeclOrderAlignedEnd? fieldByteSize fieldAlign (Nat.add off sz) ks
      | false => .none
    | _, _ => .none

/-- All tuple field kinds are structurally equal (`rigidTyEq`) to their successor. -/
def rigidTyListAllEq : List RigidTy → Bool
  | a :: b :: rest => Bool.and (rigidTyEq a b) (rigidTyListAllEq (b :: rest))
  | _ => true

/-- Tuple-level conditions of `Ty::has_canonical_byte_layout`: the tuple has at
most one field, or all fields have the same type, or no field contains a niche,
both the field alignments and alignment-group keys are non-increasing in
declaration order, every declaration-order field offset is aligned (with positive
field alignments), and the unpadded size is a multiple of the positive tuple
alignment (`tupleFieldsAlign`). -/
def tupleDeclOrderIsCanonical
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (ks : List RigidTy) : Bool :=
  match Nat.ble (length ks) 1, rigidTyListAllEq ks with
  | true, _ => true
  | false, true => true
  | false, false =>
    match
      rigidTyListContainsNiche ks,
      tupleFieldOrderKeys? fieldByteSize fieldAlign ks,
      tupleDeclOrderAlignedEnd? fieldByteSize fieldAlign 0 ks,
      tupleFieldsAlign fieldAlign ks
    with
    | false, .some keys, .some endOff, .some tupleAlign =>
      Bool.and (orderKeysNonIncreasing keys)
        (Bool.and (Bool.not (Nat.beq tupleAlign 0)) (Nat.beq (Nat.mod endOff tupleAlign) 0))
    | _, _, _, _ => false

mutual
/-- `Ty::has_canonical_byte_layout`: scalars, thin/wide pointers, and `!` are
canonical; arrays are canonical when their element is; tuples are canonical when
every field is canonical and `tupleDeclOrderIsCanonical` holds. Every kind that
`anneal-mir`'s `Ty` cannot express (ADTs, floats, slices, closures, ...) fails
closed (`false`). -/
def rigidTyHasCanonicalByteLayout
    (fieldByteSize fieldAlign : RigidTy → Option Nat) : RigidTy → Bool
  | .bool => true
  | .char => true
  | .int _ => true
  | .uint _ => true
  | .rawPtr _ _ => true
  | .ref _ _ => true
  | .never => true
  | .array elem _ => rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign elem
  | .tuple ks =>
    Bool.and
      (rigidTyListHasCanonicalByteLayout fieldByteSize fieldAlign ks)
      (tupleDeclOrderIsCanonical fieldByteSize fieldAlign ks)
  | _ => false

/-- `rigidTyHasCanonicalByteLayout` over a list of tuple field kinds (`all`). -/
def rigidTyListHasCanonicalByteLayout
    (fieldByteSize fieldAlign : RigidTy → Option Nat) : List RigidTy → Bool
  | .nil => true
  | k :: ks =>
    Bool.and
      (rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign k)
      (rigidTyListHasCanonicalByteLayout fieldByteSize fieldAlign ks)
end

/-- Resolve the byte offset of a `(variantIdx, fieldIdx)` projection chain inside
a canonical tuple type (`resolve_offset_of` in `crates/anneal-mir/src/lower/rvalue.rs`).
Fails closed (`.none`) if any container is not a tuple, if `variantIdx != 0`, if
`fieldIdx` is out of bounds, or if a container lacks a canonical byte layout
(`rigidTyHasCanonicalByteLayout`, Episode 1's `UnsupportedOffsetOfLayout`). -/
def resolveTupleOffsetOf
    (fieldByteSize fieldAlign : RigidTy → Option Nat) :
    RigidTy → List (VariantIdx × FieldIdx) → Option Nat
  | _, .nil => .some 0
  | .tuple tupleFields, (variantIdx, fieldIdx) :: rest =>
    match
      Bool.and (Nat.beq variantIdx 0)
        (rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields)),
      get? tupleFields fieldIdx,
      sumPrefixFieldSizes fieldByteSize tupleFields fieldIdx
    with
    | true, .some childKind, .some stepOff =>
      match resolveTupleOffsetOf fieldByteSize fieldAlign childKind rest with
      | .some tailOff => .some (Nat.add stepOff tailOff)
      | .none => .none
    | _, _, _ => .none
  | _, _ :: _ => .none

/-- Empty `OffsetOf` path resolves to byte offset `0`. -/
@[simp]
theorem resolveTupleOffsetOf_nil
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (kind : RigidTy) :
    resolveTupleOffsetOf fieldByteSize fieldAlign kind .nil = .some 0 := by
  cases kind <;> rfl

/-- Any `OffsetOf` step on a tuple with a non-zero `variantIdx` fails closed (`.none`). -/
theorem resolveTupleOffsetOf_nonzero_variant_eq_none
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (variantIdx : VariantIdx)
    (fieldIdx : FieldIdx)
    (rest : List (VariantIdx × FieldIdx))
    (hNonZero : variantIdx ≠ 0) :
    resolveTupleOffsetOf fieldByteSize fieldAlign (.tuple tupleFields)
        ((variantIdx, fieldIdx) :: rest) =
      .none := by
  have hBeq : Nat.beq variantIdx 0 = false := by
    cases h : Nat.beq variantIdx 0 with
    | false => rfl
    | true => exact False.elim (hNonZero (Nat.eq_of_beq_eq_true h))
  unfold resolveTupleOffsetOf
  rw [hBeq]
  rfl

/-- Any `OffsetOf` step with an out-of-bounds `fieldIdx` (`get? tupleFields fieldIdx = .none`)
fails closed (`.none`). -/
theorem resolveTupleOffsetOf_oob_field_eq_none
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (variantIdx : VariantIdx)
    (fieldIdx : FieldIdx)
    (rest : List (VariantIdx × FieldIdx))
    (hOob : get? tupleFields fieldIdx = .none) :
    resolveTupleOffsetOf fieldByteSize fieldAlign (.tuple tupleFields)
        ((variantIdx, fieldIdx) :: rest) =
      .none := by
  unfold resolveTupleOffsetOf
  rw [hOob]
  cases Bool.and (Nat.beq variantIdx 0)
    (rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields)) <;> rfl

/-- **Canonical-Layout Gate (`resolveTupleOffsetOf_noncanonical_eq_none`)**:
Any `OffsetOf` step on a tuple without a canonical byte layout (padding,
alignment-increasing or niche-dependent field order, or a field kind outside
`anneal-mir`'s `Ty`) fails closed (`.none`), matching Episode 1's
`UnsupportedOffsetOfLayout`. -/
theorem resolveTupleOffsetOf_noncanonical_eq_none
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (variantIdx : VariantIdx)
    (fieldIdx : FieldIdx)
    (rest : List (VariantIdx × FieldIdx))
    (hNonCanonical :
      rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields) = false) :
    resolveTupleOffsetOf fieldByteSize fieldAlign (.tuple tupleFields)
        ((variantIdx, fieldIdx) :: rest) =
      .none := by
  unfold resolveTupleOffsetOf
  rw [hNonCanonical, Bool.and_false]

/-- Any non-empty `OffsetOf` path on a non-tuple type fails closed (`.none`). -/
theorem resolveTupleOffsetOf_non_tuple_eq_none
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (kind : RigidTy)
    (step : VariantIdx × FieldIdx)
    (rest : List (VariantIdx × FieldIdx))
    (hNotTuple : ∀ fs, kind ≠ .tuple fs) :
    resolveTupleOffsetOf fieldByteSize fieldAlign kind (step :: rest) = .none := by
  cases kind with
  | tuple fs => exact False.elim (hNotTuple fs rfl)
  | _ => rfl

/-- Regression (`rustc 1.98`: `offset_of!((u8, u32), 1) = 4`): the padded tuple
`(u8, u32)` has no canonical byte layout, so `OffsetOf` fails closed instead of
returning the unpadded prefix sum `1`. -/
example :
    resolveTupleOffsetOf (intrinsicRigidTyByteSize .nil emptyLayoutTable)
      (intrinsicRigidTyAlign .nil emptyLayoutTable)
      (.tuple [.uint .u8, .uint .u32]) [(0, 1)] = .none := by
  rfl

/-- Regression (`rustc 1.98`: `offset_of!((u32, u16, u16), 2) = 6`): the
padding-free, alignment-sorted tuple `(u32, u16, u16)` is canonical. -/
example :
    resolveTupleOffsetOf (intrinsicRigidTyByteSize .nil emptyLayoutTable)
      (intrinsicRigidTyAlign .nil emptyLayoutTable)
      (.tuple [.uint .u32, .uint .u16, .uint .u16]) [(0, 2)] = .some 6 := by
  rfl

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
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (fieldIdx : FieldIdx)
    (fieldKind : RigidTy)
    (off fieldSz totalUnpadded align : Nat)
    (hResolve :
      resolveTupleOffsetOf fieldByteSize fieldAlign (.tuple tupleFields) [(0, fieldIdx)] =
        .some off)
    (hGet : get? tupleFields fieldIdx = .some fieldKind)
    (hFieldSz : fieldByteSize fieldKind = .some fieldSz)
    (hTotal : tupleFieldsByteSum fieldByteSize tupleFields = .some totalUnpadded) :
    off + fieldSz ≤ totalUnpadded ∧
    off + fieldSz ≤ alignUp totalUnpadded align := by
  unfold resolveTupleOffsetOf at hResolve
  rw [hGet] at hResolve
  cases hCan : rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields) with
  | false =>
    rw [hCan] at hResolve
    nomatch hResolve
  | true =>
  rw [hCan] at hResolve
  have h00 : (Nat.beq 0 0 && true) = true := rfl
  rw [h00] at hResolve
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

/-- In a padding-free declaration-order layout starting at byte `off`
(`tupleDeclOrderAlignedEnd?` succeeds), every field has a positive alignment
`0 < a` and the offset `off + p` of every field (`p` = its unpadded prefix sum)
is a multiple of that field's alignment. -/
theorem tupleDeclOrderAlignedEnd?_prefix_aligned
    (fieldByteSize fieldAlign : RigidTy → Option Nat) :
    ∀ (fs : List RigidTy) (off i : Nat) (k : RigidTy) (a p e : Nat),
      tupleDeclOrderAlignedEnd? fieldByteSize fieldAlign off fs = .some e →
      get? fs i = .some k →
      fieldAlign k = .some a →
      sumPrefixFieldSizes fieldByteSize fs i = .some p →
      0 < a ∧ (off + p) % a = 0 := by
  intro fs
  induction fs with
  | nil =>
    intro off i k a p e _ hGet
    nomatch hGet
  | cons k0 rest ih =>
    intro off i k a p e hEnd hGet hAl hPref
    unfold tupleDeclOrderAlignedEnd? at hEnd
    cases hSz0 : fieldByteSize k0 with
    | none => rw [hSz0] at hEnd; nomatch hEnd
    | some s0 =>
      cases hAl0 : fieldAlign k0 with
      | none => rw [hSz0, hAl0] at hEnd; nomatch hEnd
      | some a0 =>
        rw [hSz0, hAl0] at hEnd
        dsimp only at hEnd
        cases hMod : Bool.and (Bool.not (Nat.beq a0 0)) (Nat.beq (Nat.mod off a0) 0) with
        | false => rw [hMod] at hEnd; nomatch hEnd
        | true =>
          rw [hMod] at hEnd
          have ⟨hNotZ0, hMod0⟩ := Bool.and_eq_true_iff.mp hMod
          cases i with
          | zero =>
            simp only [get?_eq_getElem?, List.getElem?_cons_zero] at hGet
            injection hGet with hK
            subst hK
            rw [hAl0] at hAl
            injection hAl with hA
            subst hA
            unfold sumPrefixFieldSizes at hPref
            injection hPref with hP
            subst hP
            have hPos0 : 0 < a0 := by
              cases a0 with
              | zero => nomatch hNotZ0
              | succ n => omega
            have hOff : off % a0 = 0 := Nat.eq_of_beq_eq_true hMod0
            exact ⟨hPos0, by simpa using hOff⟩
          | succ i' =>
            simp only [get?_eq_getElem?, List.getElem?_cons_succ] at hGet
            unfold sumPrefixFieldSizes at hPref
            rw [hSz0] at hPref
            cases hRest : sumPrefixFieldSizes fieldByteSize rest i' with
            | none => rw [hRest] at hPref; nomatch hPref
            | some p' =>
              rw [hRest] at hPref
              injection hPref with hP
              change s0 + p' = p at hP
              have ⟨hPos, hIH⟩ := ih (Nat.add off s0) i' k a p' e hEnd hGet hAl hRest
              change (off + s0 + p') % a = 0 at hIH
              rw [← hP, ← Nat.add_assoc]
              exact ⟨hPos, hIH⟩

/-- If consecutive tuple fields are `rigidTyEq` (`rigidTyListAllEq`) and byte
sizes respect `rigidTyEq`, every field has the byte size of the first field. -/
theorem rigidTyListAllEq_size_eq_head
    (fieldByteSize : RigidTy → Option Nat)
    (hSizeCongr : ∀ k₁ k₂, rigidTyEq k₁ k₂ = true → fieldByteSize k₁ = fieldByteSize k₂) :
    ∀ (tl : List RigidTy) (hd : RigidTy) (j : Nat) (k : RigidTy),
      rigidTyListAllEq (hd :: tl) = true →
      get? (hd :: tl) j = .some k →
      fieldByteSize k = fieldByteSize hd := by
  intro tl
  induction tl with
  | nil =>
    intro hd j k _ hGet
    cases j with
    | zero =>
      simp only [get?_eq_getElem?, List.getElem?_cons_zero] at hGet
      injection hGet with hK
      subst hK
      rfl
    | succ j' =>
      simp only [get?_eq_getElem?, List.getElem?_cons_succ] at hGet
      nomatch hGet
  | cons b rest ih =>
    intro hd j k hAll hGet
    have hAll' : rigidTyEq hd b = true ∧ rigidTyListAllEq (b :: rest) = true := by
      unfold rigidTyListAllEq at hAll
      exact Bool.and_eq_true_iff.mp hAll
    cases j with
    | zero =>
      simp only [get?_eq_getElem?, List.getElem?_cons_zero] at hGet
      injection hGet with hK
      subst hK
      rfl
    | succ j' =>
      simp only [get?_eq_getElem?, List.getElem?_cons_succ] at hGet
      rw [ih b j' k hAll'.2 hGet]
      exact (hSizeCongr hd b hAll'.1).symm

/-- Unpadded prefix sums over uniformly sized fields (`fieldByteSize k = .some s`
for every field) are `i * s`. -/
theorem sumPrefixFieldSizes_uniform
    (fieldByteSize : RigidTy → Option Nat)
    (s : Nat) :
    ∀ (fs : List RigidTy) (i p : Nat),
      (∀ j k, get? fs j = .some k → fieldByteSize k = .some s) →
      sumPrefixFieldSizes fieldByteSize fs i = .some p →
      p = i * s := by
  intro fs
  induction fs with
  | nil =>
    intro i p _ hPref
    nomatch hPref
  | cons k0 rest ih =>
    intro i p hUni hPref
    cases i with
    | zero =>
      unfold sumPrefixFieldSizes at hPref
      injection hPref with hP
      omega
    | succ i' =>
      unfold sumPrefixFieldSizes at hPref
      have hK0 : fieldByteSize k0 = .some s := hUni 0 k0 rfl
      rw [hK0] at hPref
      cases hRest : sumPrefixFieldSizes fieldByteSize rest i' with
      | none => rw [hRest] at hPref; nomatch hPref
      | some p' =>
        rw [hRest] at hPref
        injection hPref with hP
        change s + p' = p at hP
        have hUni' : ∀ j k, get? rest j = .some k → fieldByteSize k = .some s :=
          fun j k h => hUni (j + 1) k h
        have hP' := ih i' p' hUni' hRest
        subst hP'
        rw [Nat.succ_mul]
        omega

/-- Core single-step alignment lemma: on any canonical tuple `.tuple tupleFields`,
the unpadded prefix sum `stepOff` of field `fieldIdx` (of kind `fieldKind` and
alignment `fieldAlignBytes`) is a multiple of `fieldAlignBytes`. -/
theorem canonicalTuple_stepOff_aligned
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (fieldIdx : FieldIdx)
    (fieldKind : RigidTy)
    (stepOff fieldAlignBytes : Nat)
    (hSizeMulAlign :
      ∀ k s a, fieldByteSize k = .some s → fieldAlign k = .some a → s % a = 0)
    (hSizeCongr : ∀ k₁ k₂, rigidTyEq k₁ k₂ = true → fieldByteSize k₁ = fieldByteSize k₂)
    (hCan : rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields) = true)
    (hGet : get? tupleFields fieldIdx = .some fieldKind)
    (hPref : sumPrefixFieldSizes fieldByteSize tupleFields fieldIdx = .some stepOff)
    (hAlign : fieldAlign fieldKind = .some fieldAlignBytes) :
    stepOff % fieldAlignBytes = 0 := by
  have hTupCan : tupleDeclOrderIsCanonical fieldByteSize fieldAlign tupleFields = true := by
    unfold rigidTyHasCanonicalByteLayout at hCan
    exact (Bool.and_eq_true_iff.mp hCan).2
  cases hIdx : fieldIdx with
  | zero =>
    subst hIdx
    cases tupleFields with
    | nil => nomatch hGet
    | cons _ _ =>
      unfold sumPrefixFieldSizes at hPref
      injection hPref with hP
      subst hP
      exact Nat.zero_mod _
  | succ i' =>
    subst hIdx
    unfold tupleDeclOrderIsCanonical at hTupCan
    cases hLen : Nat.ble (length tupleFields) 1 with
    | true =>
      have hLe : tupleFields.length ≤ 1 := Nat.le_of_ble_eq_true hLen
      have hLt : i' + 1 < tupleFields.length := by
        simp only [get?_eq_getElem?] at hGet
        exact (List.getElem?_eq_some_iff.mp hGet).1
      omega
    | false =>
      rw [hLen] at hTupCan
      cases hAll : rigidTyListAllEq tupleFields with
      | true =>
        cases tupleFields with
        | nil => nomatch hGet
        | cons hd tl =>
          unfold sumPrefixFieldSizes at hPref
          cases hHd : fieldByteSize hd with
          | none => rw [hHd] at hPref; nomatch hPref
          | some s =>
            have hUni : ∀ j k, get? (hd :: tl) j = .some k → fieldByteSize k = .some s := by
              intro j k hGetJ
              rw [rigidTyListAllEq_size_eq_head fieldByteSize hSizeCongr tl hd j k hAll hGetJ, hHd]
            have hKindSz : fieldByteSize fieldKind = .some s := hUni (i' + 1) fieldKind hGet
            have hSMod : s % fieldAlignBytes = 0 :=
              hSizeMulAlign fieldKind s fieldAlignBytes hKindSz hAlign
            have hPrefFull : sumPrefixFieldSizes fieldByteSize (hd :: tl) (i' + 1) = .some stepOff := by
              unfold sumPrefixFieldSizes
              exact hPref
            have hOffMul : stepOff = (i' + 1) * s :=
              sumPrefixFieldSizes_uniform fieldByteSize s (hd :: tl) (i' + 1) stepOff hUni hPrefFull
            rw [hOffMul, Nat.mul_mod, hSMod, Nat.mul_zero, Nat.zero_mod]
      | false =>
        rw [hAll] at hTupCan
        dsimp only at hTupCan
        cases hNiche : rigidTyListContainsNiche tupleFields with
        | true => rw [hNiche] at hTupCan; nomatch hTupCan
        | false =>
          rw [hNiche] at hTupCan
          cases hKeys : tupleFieldOrderKeys? fieldByteSize fieldAlign tupleFields with
          | none => rw [hKeys] at hTupCan; nomatch hTupCan
          | some keys =>
            rw [hKeys] at hTupCan
            cases hEnd : tupleDeclOrderAlignedEnd? fieldByteSize fieldAlign 0 tupleFields with
            | none => rw [hEnd] at hTupCan; nomatch hTupCan
            | some endOff =>
              have ⟨_, hAligned⟩ :=
                tupleDeclOrderAlignedEnd?_prefix_aligned fieldByteSize fieldAlign tupleFields 0 (i' + 1)
                  fieldKind fieldAlignBytes stepOff endOff hEnd hGet hAlign hPref
              simpa using hAligned

/-- **Tuple `OffsetOf` Alignment Invariant (`resolveTupleOffsetOf_single_step_aligned`)**:
Whenever a 1-step `OffsetOf` query `[(0, fieldIdx)]` on `.tuple tupleFields`
resolves to `off` and the selected field has alignment `fieldAlignBytes`, the
offset is a multiple of the field alignment (`fieldAlignBytes ∣ off`), provided
the layout functions are well formed: every resolved size is a multiple of the
resolved alignment (`hSizeMulAlign`) and sizes respect structural type equality
(`hSizeCongr`). -/
theorem resolveTupleOffsetOf_single_step_aligned
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (tupleFields : List RigidTy)
    (fieldIdx : FieldIdx)
    (fieldKind : RigidTy)
    (off fieldAlignBytes : Nat)
    (hSizeMulAlign :
      ∀ k s a, fieldByteSize k = .some s → fieldAlign k = .some a → s % a = 0)
    (hSizeCongr : ∀ k₁ k₂, rigidTyEq k₁ k₂ = true → fieldByteSize k₁ = fieldByteSize k₂)
    (hResolve :
      resolveTupleOffsetOf fieldByteSize fieldAlign (.tuple tupleFields) [(0, fieldIdx)] =
        .some off)
    (hGet : get? tupleFields fieldIdx = .some fieldKind)
    (hAlign : fieldAlign fieldKind = .some fieldAlignBytes) :
    off % fieldAlignBytes = 0 := by
  unfold resolveTupleOffsetOf at hResolve
  rw [hGet] at hResolve
  cases hCan : rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields) with
  | false =>
    rw [hCan] at hResolve
    nomatch hResolve
  | true =>
    rw [hCan] at hResolve
    have h00 : (Nat.beq 0 0 && true) = true := rfl
    rw [h00] at hResolve
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
      exact canonicalTuple_stepOff_aligned
        fieldByteSize fieldAlign tupleFields fieldIdx fieldKind off fieldAlignBytes
        hSizeMulAlign hSizeCongr hCan hGet hPref hAlign

/-- Resolve the leaf `RigidTy` reached by a multi-step `(variantIdx, fieldIdx)`
tuple projection chain. -/
def resolveTupleLeafKind : RigidTy → List (VariantIdx × FieldIdx) → Option RigidTy
  | kind, .nil => .some kind
  | .tuple tupleFields, (variantIdx, fieldIdx) :: rest =>
    match Nat.beq variantIdx 0, get? tupleFields fieldIdx with
    | true, .some childKind => resolveTupleLeafKind childKind rest
    | _, _ => .none
  | _, _ :: _ => .none

/-- If `tupleFieldsByteSum fieldByteSize fs = .some totalSz`, every in-bounds
field `get? fs idx = .some childKind` has a defined byte size. -/
theorem tupleFieldsByteSum_get?_some
    (fieldByteSize : RigidTy → Option Nat) :
    ∀ (fs : List RigidTy) (idx : Nat) (childKind : RigidTy) (totalSz : Nat),
      tupleFieldsByteSum fieldByteSize fs = .some totalSz →
      get? fs idx = .some childKind →
      ∃ childSz, fieldByteSize childKind = .some childSz := by
  intro fs
  induction fs with
  | nil =>
    intro idx _ _ _ hGet
    nomatch hGet
  | cons k rest ih =>
    intro idx childKind totalSz hSum hGet
    unfold tupleFieldsByteSum at hSum
    cases hK : fieldByteSize k with
    | none => rw [hK] at hSum; nomatch hSum
    | some szK =>
      cases hRest : tupleFieldsByteSum fieldByteSize rest with
      | none => rw [hK, hRest] at hSum; nomatch hSum
      | some restSz =>
        cases idx with
        | zero =>
          simp only [get?_eq_getElem?, List.getElem?_cons_zero] at hGet
          injection hGet with hEq
          subst hEq
          exact ⟨szK, hK⟩
        | succ idx' =>
          simp only [get?_eq_getElem?, List.getElem?_cons_succ] at hGet
          exact ih idx' childKind restSz hRest hGet

/-- **Multi-Step Tuple `OffsetOf` Upper-Bound Theorem (`resolveTupleOffsetOf_multi_step_bound`)**:
For any multi-step `OffsetOf` path `path : List (VariantIdx × FieldIdx)` from
`rootKind` reaching `leafKind`, whenever every canonical tuple's byte size is at
least the unpadded sum of its field byte sizes (`hTupleSumLe`), the cumulative
byte offset `off` plus the leaf field size `leafSz` never exceeds the root
container size `rootSz`: `off + leafSz ≤ rootSz`. -/
theorem resolveTupleOffsetOf_multi_step_bound
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (hTupleSumLe :
      ∀ fs tSz,
        rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple fs) = true →
        fieldByteSize (.tuple fs) = .some tSz →
        ∃ totalUnpadded,
          tupleFieldsByteSum fieldByteSize fs = .some totalUnpadded ∧
          totalUnpadded ≤ tSz) :
    ∀ (path : List (VariantIdx × FieldIdx)) (rootKind leafKind : RigidTy)
      (off rootSz leafSz : Nat),
      resolveTupleOffsetOf fieldByteSize fieldAlign rootKind path = .some off →
      resolveTupleLeafKind rootKind path = .some leafKind →
      fieldByteSize rootKind = .some rootSz →
      fieldByteSize leafKind = .some leafSz →
      off + leafSz ≤ rootSz := by
  intro path
  induction path with
  | nil =>
    intro rootKind leafKind off rootSz leafSz hRes hLeaf hRootSz hLeafSz
    rw [resolveTupleOffsetOf_nil] at hRes
    injection hRes with hOffZero
    subst hOffZero
    unfold resolveTupleLeafKind at hLeaf
    injection hLeaf with hKindEq
    subst hKindEq
    rw [hRootSz] at hLeafSz
    injection hLeafSz with hSzEq
    omega
  | cons step rest ih =>
    rcases step with ⟨variantIdx, fieldIdx⟩
    intro rootKind leafKind off rootSz leafSz hRes hLeaf hRootSz hLeafSz
    cases rootKind with
    | tuple tupleFields =>
      unfold resolveTupleOffsetOf at hRes
      unfold resolveTupleLeafKind at hLeaf
      cases hVar : Nat.beq variantIdx 0 with
      | false => rw [hVar] at hRes; nomatch hRes
      | true =>
        cases hCan : rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields) with
        | false => rw [hVar, hCan] at hRes; nomatch hRes
        | true =>
          rw [hVar, hCan, Bool.and_self] at hRes
          rw [hVar] at hLeaf
          cases hGet : get? tupleFields fieldIdx with
          | none => rw [hGet] at hRes; nomatch hRes
          | some childKind =>
            rw [hGet] at hRes hLeaf
            cases hPref : sumPrefixFieldSizes fieldByteSize tupleFields fieldIdx with
            | none => rw [hPref] at hRes; nomatch hRes
            | some stepOff =>
              rw [hPref] at hRes
              dsimp only at hRes
              cases hSub : resolveTupleOffsetOf fieldByteSize fieldAlign childKind rest with
              | none => rw [hSub] at hRes; nomatch hRes
              | some tailOff =>
                rw [hSub] at hRes
                injection hRes with hOffEq
                change stepOff + tailOff = off at hOffEq
                obtain ⟨totalUnpadded, hSum, hUnpadLe⟩ :=
                  hTupleSumLe tupleFields rootSz hCan hRootSz
                obtain ⟨childSz, hChildSz⟩ :=
                  tupleFieldsByteSum_get?_some fieldByteSize tupleFields fieldIdx childKind
                    totalUnpadded hSum hGet
                have hStepBound :=
                  sumPrefixFieldSizes_add_field_le_tupleFieldsByteSum
                    fieldByteSize tupleFields fieldIdx childKind stepOff childSz totalUnpadded
                    hGet hChildSz hPref hSum
                have hTailBound :=
                  ih childKind leafKind tailOff childSz leafSz hSub hLeaf hChildSz hLeafSz
                omega
    | _ => nomatch hRes

private theorem nat_mod_trans {x b a : Nat} (hxb : x % b = 0) (hba : b % a = 0) :
    x % a = 0 :=
  Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hba) (Nat.dvd_of_mod_eq_zero hxb))

/-- Along any resolved tuple path `path` from `rootKind` to `leafKind`, if every
tuple's alignment is a multiple of each of its fields' alignments
(`hTupleAlignDiv`), then the root container's alignment is a multiple of the
leaf field's alignment (`rootAl % leafAl = 0`). -/
theorem resolveTupleLeafKind_align_dvd
    (fieldAlign : RigidTy → Option Nat)
    (hTupleAlignDiv :
      ∀ fs idx ck,
        get? fs idx = .some ck →
        ∃ aC, fieldAlign ck = .some aC ∧
          ∀ aT, fieldAlign (.tuple fs) = .some aT → aT % aC = 0) :
    ∀ (path : List (VariantIdx × FieldIdx)) (rootKind leafKind : RigidTy)
      (rootAl leafAl : Nat),
      resolveTupleLeafKind rootKind path = .some leafKind →
      fieldAlign rootKind = .some rootAl →
      fieldAlign leafKind = .some leafAl →
      rootAl % leafAl = 0 := by
  intro path
  induction path with
  | nil =>
    intro rootKind leafKind rootAl leafAl hLeaf hRootAl hLeafAl
    unfold resolveTupleLeafKind at hLeaf
    injection hLeaf with hEq
    subst hEq
    rw [hRootAl] at hLeafAl
    injection hLeafAl with hAlEq
    subst hAlEq
    exact Nat.mod_self _
  | cons step rest ih =>
    rcases step with ⟨variantIdx, fieldIdx⟩
    intro rootKind leafKind rootAl leafAl hLeaf hRootAl hLeafAl
    cases rootKind with
    | tuple tupleFields =>
      unfold resolveTupleLeafKind at hLeaf
      cases hVar : Nat.beq variantIdx 0 with
      | false => rw [hVar] at hLeaf; nomatch hLeaf
      | true =>
        cases hGet : get? tupleFields fieldIdx with
        | none => rw [hVar, hGet] at hLeaf; nomatch hLeaf
        | some childKind =>
          rw [hVar, hGet] at hLeaf
          dsimp only at hLeaf
          obtain ⟨childAl, hChildAl, hDivRoot⟩ := hTupleAlignDiv tupleFields fieldIdx childKind hGet
          have hRootChild : rootAl % childAl = 0 := hDivRoot rootAl hRootAl
          have hChildLeaf : childAl % leafAl = 0 :=
            ih childKind leafKind childAl leafAl hLeaf hChildAl hLeafAl
          exact nat_mod_trans hRootChild hChildLeaf
    | _ => nomatch hLeaf

/-- **Multi-Step Tuple `OffsetOf` Alignment Theorem (`resolveTupleOffsetOf_multi_step_aligned`)**:
For any multi-step `OffsetOf` path `path : List (VariantIdx × FieldIdx)` from
`rootKind` reaching `leafKind` with byte offset `off` and leaf alignment
`leafAlignBytes`, the cumulative offset `off` is a multiple of `leafAlignBytes`
(`off % leafAlignBytes = 0`). -/
theorem resolveTupleOffsetOf_multi_step_aligned
    (fieldByteSize fieldAlign : RigidTy → Option Nat)
    (hSizeMulAlign :
      ∀ k s a, fieldByteSize k = .some s → fieldAlign k = .some a → s % a = 0)
    (hSizeCongr : ∀ k₁ k₂, rigidTyEq k₁ k₂ = true → fieldByteSize k₁ = fieldByteSize k₂)
    (hTupleAlignDiv :
      ∀ fs idx ck,
        get? fs idx = .some ck →
        ∃ aC, fieldAlign ck = .some aC ∧
          ∀ aT, fieldAlign (.tuple fs) = .some aT → aT % aC = 0) :
    ∀ (path : List (VariantIdx × FieldIdx)) (rootKind leafKind : RigidTy)
      (off leafAlignBytes : Nat),
      resolveTupleOffsetOf fieldByteSize fieldAlign rootKind path = .some off →
      resolveTupleLeafKind rootKind path = .some leafKind →
      fieldAlign leafKind = .some leafAlignBytes →
      off % leafAlignBytes = 0 := by
  intro path
  induction path with
  | nil =>
    intro rootKind leafKind off leafAlignBytes hRes _ _
    rw [resolveTupleOffsetOf_nil] at hRes
    injection hRes with hOffZero
    subst hOffZero
    exact Nat.zero_mod _
  | cons step rest ih =>
    rcases step with ⟨variantIdx, fieldIdx⟩
    intro rootKind leafKind off leafAlignBytes hRes hLeaf hLeafAl
    cases rootKind with
    | tuple tupleFields =>
      unfold resolveTupleOffsetOf at hRes
      unfold resolveTupleLeafKind at hLeaf
      cases hVar : Nat.beq variantIdx 0 with
      | false => rw [hVar] at hRes; nomatch hRes
      | true =>
        cases hCan : rigidTyHasCanonicalByteLayout fieldByteSize fieldAlign (.tuple tupleFields) with
        | false => rw [hVar, hCan] at hRes; nomatch hRes
        | true =>
          rw [hVar, hCan, Bool.and_self] at hRes
          rw [hVar] at hLeaf
          cases hGet : get? tupleFields fieldIdx with
          | none => rw [hGet] at hRes; nomatch hRes
          | some childKind =>
            rw [hGet] at hRes hLeaf
            cases hPref : sumPrefixFieldSizes fieldByteSize tupleFields fieldIdx with
            | none => rw [hPref] at hRes; nomatch hRes
            | some stepOff =>
              rw [hPref] at hRes
              dsimp only at hRes
              cases hSub : resolveTupleOffsetOf fieldByteSize fieldAlign childKind rest with
              | none => rw [hSub] at hRes; nomatch hRes
              | some tailOff =>
                rw [hSub] at hRes
                injection hRes with hOffEq
                change stepOff + tailOff = off at hOffEq
                obtain ⟨childAl, hChildAl, _⟩ := hTupleAlignDiv tupleFields fieldIdx childKind hGet
                have hStepChild : stepOff % childAl = 0 :=
                  canonicalTuple_stepOff_aligned
                    fieldByteSize fieldAlign tupleFields fieldIdx childKind stepOff childAl
                    hSizeMulAlign hSizeCongr hCan hGet hPref hChildAl
                have hChildLeaf : childAl % leafAlignBytes = 0 :=
                  resolveTupleLeafKind_align_dvd fieldAlign hTupleAlignDiv
                    rest childKind leafKind childAl leafAlignBytes hLeaf hChildAl hLeafAl
                have hStepLeaf : stepOff % leafAlignBytes = 0 :=
                  nat_mod_trans hStepChild hChildLeaf
                have hTailLeaf : tailOff % leafAlignBytes = 0 :=
                  ih childKind leafKind tailOff leafAlignBytes hSub hLeaf hLeafAl
                rw [← hOffEq, Nat.add_mod, hStepLeaf, hTailLeaf, Nat.zero_mod]
    | _ => nomatch hRes

/-- Multi-step regression (`rustc 1.98`: `offset_of!(((u32, u16, u16), (u16, u16)), 1.1) = 10`):
nested canonical tuple offset resolves to outer prefix `8` + inner prefix `2` = `10`,
while a nested padded inner tuple `((u32, u32), (u8, u32))` fails closed (`.none`). -/
example :
    resolveTupleOffsetOf (intrinsicRigidTyByteSize .nil emptyLayoutTable)
      (intrinsicRigidTyAlign .nil emptyLayoutTable)
      (.tuple [.tuple [.uint .u32, .uint .u16, .uint .u16], .tuple [.uint .u16, .uint .u16]])
      [(0, 1), (0, 1)] = .some 10 ∧
    resolveTupleOffsetOf (intrinsicRigidTyByteSize .nil emptyLayoutTable)
      (intrinsicRigidTyAlign .nil emptyLayoutTable)
      (.tuple [.tuple [.uint .u32, .uint .u32], .tuple [.uint .u8, .uint .u32]])
      [(0, 1), (0, 1)] = .none := by
  exact ⟨rfl, rfl⟩

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
      match
        resolveTupleOffsetOf (intrinsicRigidTyByteSize localDecls layouts)
          (intrinsicRigidTyAlign localDecls layouts) argTy.kind fields
      with
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
never introduces `.ub` on any input. Because Trusted's `evalRvalue` is
`.unsupported` on every `Rvalue.nullaryOp`, the refinement half holds for every
possible result and constrains nothing by itself; the value Anneal returns is
pinned to Trusted's own layout semantics by
`evalNullaryOp_sizeOf_matches_size_of_val_intrinsic`,
`evalNullaryOp_alignOf_matches_align_of_val_intrinsic`, and
`evalNullaryOp_ubChecks_matches_intrinsic`, and `.offsetOf` by the
canonical-layout gate (`resolveTupleOffsetOf_noncanonical_eq_none`,
`resolveTupleOffsetOf_single_step_aligned`). -/
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
      cases resolveTupleOffsetOf (intrinsicRigidTyByteSize localDecls layouts)
          (intrinsicRigidTyAlign localDecls layouts) kind fields with
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

/-- **`SizeOf` Agreement With `size_of_val` (`evalNullaryOp_sizeOf_matches_size_of_val_intrinsic`)**:
`Trusted.Rustc.V2026_06_01.MirSemantics.evalRvalue` leaves `Rvalue.nullaryOp`
unsupported, so `RvalueResultRefines` alone cannot constrain the value Anneal
returns. This theorem pins it to the value Trusted itself computes for the
equivalent intrinsic call: whenever `NullOp.sizeOf` on `argTy` returns
`.ok (.scalar sc) ..` under a 64-bit layout table, the `size_of_val::<T>(ptr)`
intrinsic (`evalNonSelectIntrinsicCall .sizeOfVal`, `Terminators.lean`) on a
thin 8-byte pointer whose sized, non-extern pointee type is `argTy.kind` writes
exactly the same `.scalar sc` to its destination (both read
`intrinsicRigidTyByteSize`, and Anneal's `sz ≤ isize::MAX` bound coincides with
the intrinsic's `sz < 2^63` check). -/
theorem evalNullaryOp_sizeOf_matches_size_of_val_intrinsic
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (argTy : Ty)
    (ptr : ProvenancePtr)
    (sc : ScalarInt)
    (hPtrBytes : layoutPointerBytes bodyLayouts = 8)
    (hPointee :
      resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = .some argTy.kind)
    (hNotSlice : ∀ elemTy, argTy.kind ≠ .slice elemTy)
    (hNotStr : argTy.kind ≠ .str)
    (hNotDyn : ∀ traitPath, argTy.kind ≠ .dynamic traitPath)
    (hNotExtern : intrinsicTailIsExtern 8 argTy.kind = false)
    (hEval :
      evalNullaryOp locals' .sizeOf argTy s.memory bodyLocalDecls bodyLayouts =
        .ok (.scalar sc) locals' s.memory) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalNonSelectIntrinsicCall
        .sizeOfVal s target bodyLocalDecls bodyLayouts argOps [.ptr ptr 8]
        locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar sc) := by
  have hInv : ∃ sz, intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts argTy.kind = .some sz ∧
      Nat.ble (signedHalfModulus 8) sz = false ∧ sc = ⟨sz, 8⟩ := by
    unfold evalNullaryOp at hEval
    dsimp only at hEval
    cases hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts argTy.kind with
    | none => rw [hSz] at hEval; nomatch hEval
    | some sz =>
      rw [hSz] at hEval
      dsimp only at hEval
      cases hLe : Nat.ble sz
          (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes bodyLayouts)) 2) 1) with
      | false => rw [hLe] at hEval; nomatch hEval
      | true =>
        rw [hLe] at hEval
        injection hEval with hVal _ _
        injection hVal with hSc
        refine ⟨sz, rfl, ?_, ?_⟩
        · have hLeSz := Nat.le_of_ble_eq_true hLe
          rw [hPtrBytes] at hLeSz
          have h8 : scalarModulus 8 = 18446744073709551616 := rfl
          have hHalf : signedHalfModulus 8 = 9223372036854775808 := rfl
          rw [hHalf]
          cases hB : Nat.ble 9223372036854775808 sz with
          | false => rfl
          | true =>
            have hGe := Nat.le_of_ble_eq_true hB
            simp only [nat_sub_eq, nat_div_eq, h8] at hLeSz
            omega
        · rw [← hSc, hPtrBytes]
  obtain ⟨sz, hSz, hBle, rfl⟩ := hInv
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalNonSelectIntrinsicCall
  dsimp only
  rw [hPointee]
  split
  · rename_i heq
    exact absurd (Option.some.inj heq) (hNotSlice _)
  · rename_i heq
    exact absurd (Option.some.inj heq) hNotStr
  · rename_i heq
    exact absurd (Option.some.inj heq) (hNotDyn _)
  · rename_i heq
    have hKind := Option.some.inj heq
    rw [← hKind, hNotExtern]
    dsimp only
    rw [hSz]
    dsimp only
    rw [hBle]
  · rename_i heq
    nomatch heq

/-- **`AlignOf` Agreement With `align_of_val` (`evalNullaryOp_alignOf_matches_align_of_val_intrinsic`)**:
Whenever `NullOp.alignOf` on `argTy` returns `.ok (.scalar sc) ..` under a 64-bit
layout table, the `align_of_val::<T>(ptr)` intrinsic
(`evalNonSelectIntrinsicCall .alignOfVal`, `Terminators.lean`) on a thin 8-byte
pointer whose sized, non-extern pointee type is `argTy.kind` writes exactly the
same `.scalar sc` (both read `intrinsicRigidTyAlign`). -/
theorem evalNullaryOp_alignOf_matches_align_of_val_intrinsic
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetBb : BasicBlockIdx)
    (argTy : Ty)
    (ptr : ProvenancePtr)
    (sc : ScalarInt)
    (hPtrBytes : layoutPointerBytes bodyLayouts = 8)
    (hPointee :
      resolveIntrinsicPointeeTy? target bodyLocalDecls bodyLayouts argOps = .some argTy.kind)
    (hNotSlice : ∀ elemTy, argTy.kind ≠ .slice elemTy)
    (hNotStr : argTy.kind ≠ .str)
    (hNotDyn : ∀ traitPath, argTy.kind ≠ .dynamic traitPath)
    (hNotExtern : intrinsicTailIsExtern 8 argTy.kind = false)
    (hEval :
      evalNullaryOp locals' .alignOf argTy s.memory bodyLocalDecls bodyLayouts =
        .ok (.scalar sc) locals' s.memory) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalNonSelectIntrinsicCall
        .alignOfVal s target bodyLocalDecls bodyLayouts argOps [.ptr ptr 8]
        locals' destination targetBb =
      writeIntrinsicReturn s locals' destination targetBb (.scalar sc) := by
  have hInv : ∃ align, intrinsicRigidTyAlign bodyLocalDecls bodyLayouts argTy.kind = .some align ∧
      sc = ⟨align, 8⟩ := by
    unfold evalNullaryOp at hEval
    dsimp only at hEval
    cases hSz : intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts argTy.kind with
    | none => rw [hSz] at hEval; nomatch hEval
    | some sz =>
      cases hAl : intrinsicRigidTyAlign bodyLocalDecls bodyLayouts argTy.kind with
      | none => rw [hSz, hAl] at hEval; nomatch hEval
      | some align =>
        rw [hSz, hAl] at hEval
        dsimp only at hEval
        cases hOk : Bool.and
            (Nat.ble sz (Nat.sub (Nat.div (scalarModulus (layoutPointerBytes bodyLayouts)) 2) 1))
            (Bool.not (Nat.beq align 0)) with
        | false => rw [hOk] at hEval; nomatch hEval
        | true =>
          rw [hOk] at hEval
          injection hEval with hVal _ _
          injection hVal with hSc
          exact ⟨align, rfl, by rw [← hSc, hPtrBytes]⟩
  obtain ⟨align, hAl, rfl⟩ := hInv
  unfold Trusted.Rustc.V2026_06_01.MirSemantics.evalNonSelectIntrinsicCall
  dsimp only
  rw [hPointee]
  split
  · rename_i heq
    exact absurd (Option.some.inj heq) (hNotSlice _)
  · rename_i heq
    exact absurd (Option.some.inj heq) hNotStr
  · rename_i heq
    exact absurd (Option.some.inj heq) (hNotDyn _)
  · rename_i heq
    have hKind := Option.some.inj heq
    rw [← hKind, hNotExtern]
    dsimp only
    rw [hAl]
  · rename_i heq
    nomatch heq


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

/-- Exact bidirectional characterization of `tryFieldsIntoValues?`:
`tryFieldsIntoValues? slots = .some vals` if and only if `slots = vals.map FieldSlot.init`. -/
theorem tryFieldsIntoValues?_eq_some_iff :
    ∀ (slots : List FieldSlot) (vals : List Value),
      tryFieldsIntoValues? slots = .some vals ↔ slots = vals.map FieldSlot.init := by
  intro slots
  induction slots with
  | nil =>
    intro vals
    constructor
    · intro h
      unfold tryFieldsIntoValues? at h
      injection h with hEq
      subst hEq
      rfl
    · intro h
      cases vals with
      | nil => rfl
      | cons _ _ => nomatch h
  | cons hd tl ih =>
    intro vals
    constructor
    · intro h
      cases hd with
      | uninit => nomatch h
      | nested _ _ _ _ => nomatch h
      | init v =>
        unfold tryFieldsIntoValues? at h
        cases hSub : tryFieldsIntoValues? tl with
        | none => rw [hSub] at h; nomatch h
        | some vs =>
          rw [hSub] at h
          injection h with hVals
          subst hVals
          have hTl := (ih vs).mp hSub
          simp [hTl]
    · intro h
      cases vals with
      | nil => nomatch h
      | cons v vs =>
        simp only [List.map_cons, List.cons.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact tryFieldsIntoValues?_map_init (v :: vs)

/-- **Order-Independent `n`-Field Promotion Equivalence (`tryIntoValue?_eq_some_iff`)**:
For any `PartialAggregate` shell of arbitrary arity `n`, `shell.tryIntoValue? = .some outVal`
if and only if either `shell.isAdt = false` or `shell.discriminantSet = true`, and
there exists `vals : List Value` such that `shell.fields = vals.map FieldSlot.init`
and `outVal = .aggregate (if shell.isAdt then shell.variantIdx else 0) vals`. -/
theorem tryIntoValue?_eq_some_iff (shell : PartialAggregate) (outVal : Value) :
    shell.tryIntoValue? = .some outVal ↔
      (shell.isAdt = false ∨ shell.discriminantSet = true) ∧
      ∃ vals : List Value,
        shell.fields = vals.map FieldSlot.init ∧
        outVal = .aggregate (match shell.isAdt with | true => shell.variantIdx | false => 0) vals := by
  constructor
  · intro hProm
    unfold PartialAggregate.tryIntoValue? at hProm
    cases hBlock : Bool.and shell.isAdt (Bool.not shell.discriminantSet) with
    | true => rw [hBlock] at hProm; nomatch hProm
    | false =>
      rw [hBlock] at hProm
      dsimp only at hProm
      cases hTry : tryFieldsIntoValues? shell.fields with
      | none => rw [hTry] at hProm; nomatch hProm
      | some vals =>
        rw [hTry] at hProm
        injection hProm with hOutEq
        have hTagOk : shell.isAdt = false ∨ shell.discriminantSet = true := by
          cases hA : shell.isAdt with
          | false => exact Or.inl rfl
          | true =>
            cases hD : shell.discriminantSet with
            | true => exact Or.inr rfl
            | false => rw [hA, hD] at hBlock; nomatch hBlock
        exact ⟨hTagOk, vals, (tryFieldsIntoValues?_eq_some_iff shell.fields vals).mp hTry, hOutEq.symm⟩
  · rintro ⟨hTagOk, vals, hFields, rfl⟩
    exact tryIntoValue?_of_all_init shell vals hFields hTagOk

/-- Convert a `PartialAggregate` shell to a `FieldSlot.nested` slot. -/
@[reducible]
def PartialAggregate.toFieldSlot (shell : PartialAggregate) : FieldSlot :=
  .nested shell.variantIdx shell.isAdt shell.discriminantSet shell.fields

/-- Read a projected value from a `PartialAggregate` shell (`read_from_partial_shell`
and `project_from_partial_shell` in `crates/anneal-mir/src/lower/rvalue.rs`),
recursing into `.nested` child shells along `proj`. -/
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
        | .some (.nested cVar cAdt cDisc cFields) =>
          readFromPartialShell locals ⟨cVar, cAdt, cDisc, cFields⟩ tail
        | .some .uninit => .ub
        | .none => .ub
      | _ => .ub
    | false => .ub
  | .field idx _ :: rest =>
    let actual := match shell.isAdt with | true => shell.variantIdx | false => 0
    match Nat.beq actual 0 with
    | true =>
      match get? shell.fields idx with
      | .some (.init fieldVal) => evalValueProjRead locals fieldVal rest
      | .some (.nested cVar cAdt cDisc cFields) =>
        readFromPartialShell locals ⟨cVar, cAdt, cDisc, cFields⟩ rest
      | .some .uninit => .ub
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

/-- **Nested Partial-Shell Read Soundness (`readFromPartialShell_nested_soundness`)**:
When field `outerIdx` of an outer `PartialAggregate` shell holds a nested
`PartialAggregate` child shell `childShell` (`FieldSlot.nested`), reading an
initialized leaf `initChildIdx` inside `childShell` succeeds with `.ok outVal`,
while reading an uninitialized sibling `uninitChildIdx` inside `childShell` or
reading the incomplete `childShell` as a whole (`proj = [.field outerIdx tyO]`)
faults with `.ub`. -/
theorem readFromPartialShell_nested_soundness
    (locals : List LocalSlot)
    (outerShell childShell : PartialAggregate)
    (outerIdx uninitChildIdx initChildIdx : FieldIdx)
    (tyO tyU tyI : Ty)
    (rest : List ProjectionElem)
    (v outVal : Value)
    (hOuterVar0 : (match outerShell.isAdt with | true => outerShell.variantIdx | false => 0) = 0)
    (hChildVar0 : (match childShell.isAdt with | true => childShell.variantIdx | false => 0) = 0)
    (hNestedSlot : get? outerShell.fields outerIdx = .some childShell.toFieldSlot)
    (hChildUninit : get? childShell.fields uninitChildIdx = .some .uninit)
    (hChildInit : get? childShell.fields initChildIdx = .some (.init v))
    (hSubRead : evalValueProjRead locals v rest = .ok outVal) :
    readFromPartialShell locals outerShell [.field outerIdx tyO] = .ub ∧
    readFromPartialShell locals outerShell
      (.field outerIdx tyO :: .field uninitChildIdx tyU :: rest) = .ub ∧
    readFromPartialShell locals outerShell
      (.field outerIdx tyO :: .field initChildIdx tyI :: rest) = .ok outVal := by
  have hChildSub :=
    readFromPartialShell_uninit_sibling_soundness
      locals childShell uninitChildIdx initChildIdx tyU tyI rest v outVal
      hChildVar0 hChildUninit hChildInit hSubRead
  refine ⟨?_, ?_, ?_⟩
  · unfold readFromPartialShell
    rw [hOuterVar0]
    dsimp only
    rw [hNestedSlot]
    exact hChildSub.1
  · unfold readFromPartialShell
    rw [hOuterVar0]
    dsimp only
    rw [hNestedSlot]
    exact hChildSub.2.1
  · unfold readFromPartialShell
    rw [hOuterVar0]
    dsimp only
    rw [hNestedSlot]
    exact hChildSub.2.2

/-- Outcome of a stateful partial-slot or frame mutation (`write_to_partial_slot`,
`set_discriminant_in_slot`, `eval_lowered_statement`). -/
inductive SlotWriteResult (α : Type) : Type where
  | ok : α → SlotWriteResult α
  | ub : SlotWriteResult α
  | unsupported : SlotWriteResult α

/-- Promote a `PartialAggregate` shell to `FieldSlot.init` if all fields (and
enum discriminant tag, if `isAdt = true`) are initialized, or keep it as
`FieldSlot.nested` otherwise. -/
def promoteShellToFieldSlot (shell : PartialAggregate) : FieldSlot :=
  match shell.tryIntoValue? with
  | .some fullVal => .init fullVal
  | .none => shell.toFieldSlot

/-- Convert a `FieldSlot` back to `LocalSlotState`, promoting any completed
`FieldSlot.nested` shell to `LocalSlotState.init`. -/
def fieldSlotToLocalSlotState : FieldSlot → LocalSlotState
  | .uninit => .uninit
  | .init v => .init v
  | .nested vIdx isAdt discSet fields =>
    let shell : PartialAggregate := ⟨vIdx, isAdt, discSet, fields⟩
    match shell.tryIntoValue? with
    | .some fullVal => .init fullVal
    | .none => .partialShell shell

/-- Recursive `D13b` partial-slot writer (`write_to_partial_slot` in
`crates/anneal-mir/src/lower/rvalue.rs:5177-5371`):
- On `proj = .nil`: overwrites `slot` with `.init newVal`.
- On `slot = .init existingVal`: delegates to `evalValueProjWrite locals existingVal proj newVal`.
- On `slot = .uninit` + `.field idx fieldTy :: rest`: materializes
  `PartialAggregate.newUninit fieldCount 0 false` (for `arityOf containerTy 0 false = .some fieldCount`),
  recurses on child `idx`, and promotes bottom-up via `promoteShellToFieldSlot`.
- On `slot = .uninit` + `.downcast _ variantIdx :: .field idx fieldTy :: tail`:
  materializes `PartialAggregate.newUninit fieldCount variantIdx true` (`discriminantSet = false`),
  recurses on child `idx`, and promotes bottom-up.
- On `slot = .nested ...` + `.field` or `.downcast :: .field`: checks that the
  active variant matches, recurses into child slot `idx`, updates `fields[idx]`,
  and promotes bottom-up via `promoteShellToFieldSlot`.
- On `slot = .uninit` or `.nested` + `.index` / `.constantIndex` / `.subslice`:
  faults with `.ub` (`c6d2ad74`, never materializing an array shell). -/
def writeToFieldSlot
    (locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat)
    (slot : FieldSlot)
    (containerTy : Ty) :
    List ProjectionElem → Value → SlotWriteResult FieldSlot
  | .nil, newVal => .ok (.init newVal)
  | p :: rest, newVal =>
    match slot with
    | .init existingVal =>
      match evalValueProjWrite locals existingVal (p :: rest) newVal with
      | .ok updatedVal => .ok (.init updatedVal)
      | .ub => .ub
      | .unsupported => .unsupported
    | .uninit =>
      match p with
      | .field idx fieldTy =>
        match arityOf containerTy 0 false with
        | .some fieldCount =>
          match Nat.blt idx fieldCount with
          | true =>
            match writeToFieldSlot locals arityOf .uninit fieldTy rest newVal with
            | .ok childSlot =>
              let initShell := PartialAggregate.newUninit fieldCount 0 false
              match set? initShell.fields idx childSlot with
              | .some fields' =>
                .ok (promoteShellToFieldSlot { initShell with fields := fields' })
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | false => .ub
        | .none => .ub
      | .downcast _ variantIdx =>
        match rest with
        | .field idx fieldTy :: tail =>
          match arityOf containerTy variantIdx true with
          | .some fieldCount =>
            match Nat.blt idx fieldCount with
            | true =>
              match writeToFieldSlot locals arityOf .uninit fieldTy tail newVal with
              | .ok childSlot =>
                let initShell := PartialAggregate.newUninit fieldCount variantIdx true
                match set? initShell.fields idx childSlot with
                | .some fields' =>
                  .ok (promoteShellToFieldSlot { initShell with fields := fields' })
                | .none => .ub
              | .ub => .ub
              | .unsupported => .unsupported
            | false => .ub
          | .none => .ub
        | .deref :: _ => .unsupported
        | .opaqueCast _ :: _ => .unsupported
        | .unwrapUnsafeBinder _ :: _ => .unsupported
        | _ => .ub
      | .index _ => .ub
      | .constantIndex _ _ _ => .ub
      | .subslice _ _ _ => .ub
      | .deref => .unsupported
      | .opaqueCast _ => .unsupported
      | .unwrapUnsafeBinder _ => .unsupported
    | .nested sVar sAdt sDisc sFields =>
      let actual := match sAdt with | true => sVar | false => 0
      match p with
      | .field idx fieldTy =>
        match Nat.beq actual 0, get? sFields idx with
        | true, .some oldChildSlot =>
          match writeToFieldSlot locals arityOf oldChildSlot fieldTy rest newVal with
          | .ok newChildSlot =>
            match set? sFields idx newChildSlot with
            | .some fields' =>
              .ok (promoteShellToFieldSlot ⟨sVar, sAdt, sDisc, fields'⟩)
            | .none => .ub
          | .ub => .ub
          | .unsupported => .unsupported
        | _, _ => .ub
      | .downcast _ variantIdx =>
        match rest with
        | .field idx fieldTy :: tail =>
          match Nat.beq actual variantIdx, get? sFields idx with
          | true, .some oldChildSlot =>
            match writeToFieldSlot locals arityOf oldChildSlot fieldTy tail newVal with
            | .ok newChildSlot =>
              match set? sFields idx newChildSlot with
              | .some fields' =>
                .ok (promoteShellToFieldSlot ⟨sVar, sAdt, sDisc, fields'⟩)
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _, _ => .ub
        | .deref :: _ => .unsupported
        | .opaqueCast _ :: _ => .unsupported
        | .unwrapUnsafeBinder _ :: _ => .unsupported
        | _ => .ub
      | .index _ => .ub
      | .constantIndex _ _ _ => .ub
      | .subslice _ _ _ => .ub
      | .deref => .unsupported
      | .opaqueCast _ => .unsupported
      | .unwrapUnsafeBinder _ => .unsupported

/-- Canonical tuple arity function extracting `fieldTys.length` from
`ty.kind = .tuple fieldTys` for non-ADT variant `0`. -/
def tupleArityOf (ty : Ty) (variantIdx : VariantIdx) (isAdt : Bool) : Option Nat :=
  match isAdt, Nat.beq variantIdx 0, ty.kind with
  | false, true, .tuple fieldTys => .some fieldTys.length
  | _, _, _ => .none

/-- **`c6d2ad74` Array Write Rejection on Uninit / Partial Shells (`writeToFieldSlot_array_proj_ub`)**:
Writing along `.index`, `.constantIndex`, or `.subslice` into an `.uninit` or
`.nested` partial-shell slot always faults with `.ub`. -/
theorem writeToFieldSlot_array_proj_ub
    (locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat)
    (slot : FieldSlot)
    (containerTy : Ty)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (newVal : Value)
    (hNotInit : ∀ v, slot ≠ .init v)
    (hArrProj :
      (∃ idxLocal, proj = .index idxLocal) ∨
      (∃ offset minLen fromEnd, proj = .constantIndex offset minLen fromEnd) ∨
      (∃ fromIdx toIdx fromEnd, proj = .subslice fromIdx toIdx fromEnd)) :
    writeToFieldSlot locals arityOf slot containerTy (proj :: rest) newVal = .ub := by
  cases slot with
  | init v => exact False.elim (hNotInit v rfl)
  | uninit =>
    rcases hArrProj with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl
  | nested _ _ _ _ =>
    rcases hArrProj with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;> rfl

/-- On an initialized slot `.init existingVal`, `writeToFieldSlot` delegates
directly to `evalValueProjWrite` (and therefore refines Trusted's
`writeProjectedValue`). -/
theorem writeToFieldSlot_init_correspondence
    (locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat)
    (existingVal newVal updatedVal : Value)
    (containerTy : Ty)
    (proj : List ProjectionElem) :
    (writeToFieldSlot locals arityOf (.init existingVal) containerTy proj newVal =
      .ok (.init updatedVal) ↔
      evalValueProjWrite locals existingVal proj newVal = .ok updatedVal) ∧
    (writeToFieldSlot locals arityOf (.init existingVal) containerTy proj newVal =
      .ok (.init updatedVal) →
      Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
        locals existingVal proj newVal = .ok updatedVal) := by
  have hIff :
      writeToFieldSlot locals arityOf (.init existingVal) containerTy proj newVal =
        .ok (.init updatedVal) ↔
        evalValueProjWrite locals existingVal proj newVal = .ok updatedVal := by
    cases proj with
    | nil =>
      constructor
      · intro h
        unfold writeToFieldSlot at h
        injection h with hInit
        injection hInit with hVal
        subst hVal
        rfl
      · intro h
        unfold evalValueProjWrite at h
        injection h with hVal
        subst hVal
        rfl
    | cons p rest =>
      unfold writeToFieldSlot
      dsimp only
      cases evalValueProjWrite locals existingVal (p :: rest) newVal with
      | ok v' =>
        constructor
        · intro h
          injection h with hInit
          injection hInit with hEq
          rw [hEq]
        · intro h
          injection h with hEq
          rw [hEq]
      | ub =>
        constructor <;> (intro h; nomatch h)
      | unsupported =>
        constructor <;> (intro h; nomatch h)
  exact ⟨hIff, fun h => evalValueProjWrite_refines_writeProjectedValue
    proj locals existingVal newVal updatedVal (hIff.mp h)⟩

/-- **General `n`-Field Final-Write Promotion Theorem (`writeToFieldSlot_promotes_last_field_n`)**:
Let `shell` be a `PartialAggregate` shell of arbitrary field count `n = vals.length`
where field `idx` is the last remaining `.uninit` field (`get? shell.fields idx = .some .uninit`)
and setting field `idx` to `.init v` completes `vals.map FieldSlot.init`
(`set? shell.fields idx (.init v) = .some (vals.map FieldSlot.init)`):
1. Before writing field `idx`, `shell.tryIntoValue? = .none` and reading field `idx`
   faults with `.ub`.
2. Writing `v` to `.field idx fieldTy` via `writeToFieldSlot` promotes the shell
   in a single step to `.ok (.init (.aggregate 0 vals))`! -/
theorem writeToFieldSlot_promotes_last_field_n
    (locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat)
    (shell : PartialAggregate)
    (containerTy fieldTy : Ty)
    (idx : FieldIdx)
    (v : Value)
    (vals : List Value)
    (hNotAdt : shell.isAdt = false)
    (hUninitIdx : get? shell.fields idx = .some .uninit)
    (hSetAllInit : set? shell.fields idx (.init v) = .some (vals.map FieldSlot.init)) :
    shell.tryIntoValue? = .none ∧
    readFromPartialShell locals shell [.field idx fieldTy] = .ub ∧
    writeToFieldSlot locals arityOf shell.toFieldSlot containerTy [.field idx fieldTy] v =
      .ok (.init (.aggregate 0 vals)) := by
  have hNone : shell.tryIntoValue? = .none :=
    tryIntoValue?_eq_none_of_uninit_field shell idx hUninitIdx
  refine ⟨hNone, ?_, ?_⟩
  · unfold readFromPartialShell
    rw [hNotAdt]
    dsimp only
    rw [hUninitIdx]
  · unfold PartialAggregate.toFieldSlot writeToFieldSlot
    dsimp only
    rw [hNotAdt]
    dsimp only
    rw [hUninitIdx]
    dsimp only
    unfold writeToFieldSlot
    dsimp only
    rw [hSetAllInit]
    dsimp only
    unfold promoteShellToFieldSlot PartialAggregate.tryIntoValue?
    dsimp only
    rw [tryFieldsIntoValues?_map_init]
    rfl

/-- In `Trusted.MirSemantics.setOrExtendFields`, writing index `idx` on an empty
field list `.nil` pads every lower unwritten index `j < idx` with `Value.unit`. -/
theorem get?_setOrExtendFields_nil_lt :
    ∀ (idx j : Nat) (v : Value),
      j < idx →
      get? (setOrExtendFields .nil idx v) j = .some .unit := by
  intro idx
  induction idx with
  | zero =>
    intro j _ hLt
    omega
  | succ k ih =>
    intro j v hLt
    cases j with
    | zero => rfl
    | succ j' =>
      simp only [setOrExtendFields, get?_eq_getElem?, List.getElem?_cons_succ]
      rw [← get?_eq_getElem?]
      exact ih j' v (by omega)

/-- In `Trusted.MirSemantics.setOrExtendFields`, writing index `idx` on `.nil`
stores `v` at index `idx`. -/
theorem get?_setOrExtendFields_nil_self :
    ∀ (idx : Nat) (v : Value),
      get? (setOrExtendFields .nil idx v) idx = .some v := by
  intro idx
  induction idx with
  | zero => intro v; rfl
  | succ k ih =>
    intro v
    simp only [setOrExtendFields, get?_eq_getElem?, List.getElem?_cons_succ]
    rw [← get?_eq_getElem?]
    exact ih v

/-- **General `n`-Field First-Write Divergence vs. Trusted `.unit` Padding (`writeToFieldSlot_first_field_n_vs_trusted_padding`)**:
When an uninitialized `n`-field tuple local (`fieldTys.length = n`, `0 < idx < n`)
has field `idx` initialized first (`_1.idx = v`):
1. **Anneal (`writeToFieldSlot`)**: materializes a `PartialAggregate` shell of
   length `n` whose `idx`-th slot is `.init v` and whose every other slot
   `j < n` (`j ≠ idx`) is `FieldSlot.uninit`, so reading `[_1.idx]` returns
   `.ok v` while reading ANY unwritten sibling field `[_1.j]` (`j < n`, `j ≠ idx`)
   or reading the whole local `_1` returns `.ub` (`UninitializedLocal`).
2. **Trusted (`writeProjectedValue` on `uninitFieldWriteShell? = .aggregate 0 []`)**:
   extends the empty field list via `setOrExtendFields [] idx v`, padding every
   lower unwritten field `j < idx` with `Value.unit` so `readProjectedValue` on
   `[.field j tyJ]` falsely returns `.ok .unit`! -/
theorem writeToFieldSlot_first_field_n_vs_trusted_padding
    (locals : List LocalSlot)
    (fieldTys : List RigidTy)
    (lIdx : LayoutIdx)
    (idx j : Nat)
    (fieldTy tyJ : Ty)
    (v : Value)
    (hIdxLt : idx < fieldTys.length)
    (hJLtIdx : j < idx) :
    let containerTy : Ty := { kind := .tuple fieldTys, layoutIdx := lIdx }
    let initFields := (replicateUninitFieldSlots fieldTys.length).set idx (.init v)
    let expectedShell : PartialAggregate :=
      { variantIdx := 0
        isAdt := false
        discriminantSet := false
        fields := initFields }
    writeToFieldSlot locals tupleArityOf .uninit containerTy [.field idx fieldTy] v =
      .ok expectedShell.toFieldSlot ∧
    readFromPartialShell locals expectedShell [.field idx fieldTy] = .ok v ∧
    readFromPartialShell locals expectedShell [.field j tyJ] = .ub ∧
    readFromPartialShell locals expectedShell .nil = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
      locals (.aggregate 0 .nil) [.field idx fieldTy] v =
      .ok (.aggregate 0 (setOrExtendFields .nil idx v)) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue
      locals (.aggregate 0 (setOrExtendFields .nil idx v)) [.field j tyJ] =
      .ok .unit := by
  intro containerTy initFields expectedShell
  have hRepLen : (replicateUninitFieldSlots fieldTys.length).length = fieldTys.length :=
    length_replicateUninitFieldSlots fieldTys.length
  have hIdxLtRep : idx < (replicateUninitFieldSlots fieldTys.length).length := by omega
  have hBlt : Nat.blt idx fieldTys.length = true := by simpa using hIdxLt
  have hSet :
      set? (replicateUninitFieldSlots fieldTys.length) idx (.init v) = .some initFields :=
    set?_eq_some_iff.mpr ⟨hIdxLtRep, rfl⟩
  have hJLtLen : j < fieldTys.length := by omega
  have hJNe : idx ≠ j := by omega
  have hGetIdx : get? initFields idx = .some (.init v) :=
    get?_of_set?_same hSet
  have hGetJ : get? initFields j = .some .uninit := by
    rw [get?_of_set?_ne hSet hJNe]
    exact get?_replicateUninitFieldSlots hJLtLen
  have hNoneProm : expectedShell.tryIntoValue? = .none :=
    tryIntoValue?_eq_none_of_uninit_field expectedShell j hGetJ
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩
  · unfold writeToFieldSlot tupleArityOf
    dsimp only [containerTy]
    rw [hBlt]
    dsimp only
    unfold writeToFieldSlot PartialAggregate.newUninit
    dsimp only
    rw [hSet]
    dsimp only
    unfold promoteShellToFieldSlot
    change SlotWriteResult.ok (match expectedShell.tryIntoValue? with
      | .some fullVal => FieldSlot.init fullVal
      | .none => expectedShell.toFieldSlot) = .ok expectedShell.toFieldSlot
    rw [hNoneProm]
  · unfold readFromPartialShell
    dsimp only [expectedShell]
    rw [hGetIdx]
    rfl
  · unfold readFromPartialShell
    dsimp only [expectedShell]
    rw [hGetJ]
  · unfold readFromPartialShell
    rw [hNoneProm]
  · dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.readProjectedValue]
    rw [get?_setOrExtendFields_nil_lt idx j v hJLtIdx]

/-- Field slots of a `PartialAggregate` shell after `SetDiscriminant(variantIdx)`
(`set_discriminant_in_slot` in `crates/anneal-mir/src/lower/rvalue.rs`):
- unchanged when the written tag equals `shell.variantIdx`;
- reset to `FieldSlot.uninit` (`shell.fields.fill(FieldSlot::Uninit)`) when the
  tag switches to a different variant, because payload fields written through
  `((_1 as A).i) = v` belong to variant `A` and never initialize variant `B`. -/
def setDiscriminantFields
    (shell : PartialAggregate)
    (variantIdx : VariantIdx) :
    List FieldSlot :=
  match Nat.beq shell.variantIdx variantIdx with
  | true => shell.fields
  | false => replicateUninitFieldSlots shell.fields.length

/-- Apply `StatementKind.setDiscriminant` at the root of a `PartialAggregate`
shell, setting `variantIdx := variantIdx`, `isAdt := true`, and
`discriminantSet := true`, resetting the field slots when the tag switches to a
different variant (`setDiscriminantFields`), and promoting to
`LocalSlotState.init` if all variant fields are already initialized. -/
def setDiscriminantOnShell
    (shell : PartialAggregate)
    (variantIdx : VariantIdx) :
    LocalSlotState :=
  let updated : PartialAggregate :=
    { variantIdx := variantIdx
      isAdt := true
      discriminantSet := true
      fields := setDiscriminantFields shell variantIdx }
  match updated.tryIntoValue? with
  | .some fullVal => .init fullVal
  | .none => .partialShell updated

/-- **`SetDiscriminant` Promotion Theorem (`setDiscriminantOnShell_promotes_initialized_variant`)**:
In `rustc` MIR, enum initialization writes each payload field via
`((_1 as V).i) = v_i` (leaving `discriminantSet = false`, so premature whole-enum
reads fail with `.ub`) and then executes `discriminant(_1) = V`.
Once all fields of variant `V = shell.variantIdx` are `.init`
(`shell.fields = vals.map FieldSlot.init`), `setDiscriminantOnShell shell V`
promotes the shell to `LocalSlotState.init (.aggregate V vals)` (including
0-field unit enum variants when `vals = []`). The tag must name the variant whose
fields were written (`hSameVariant`); see
`setDiscriminantOnShell_switch_variant_resets_fields` for the switching case. -/
theorem setDiscriminantOnShell_promotes_initialized_variant
    (shell : PartialAggregate)
    (variantIdx : VariantIdx)
    (vals : List Value)
    (hSameVariant : shell.variantIdx = variantIdx)
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
  · have hKeep : setDiscriminantFields shell variantIdx = shell.fields := by
      unfold setDiscriminantFields
      rw [hSameVariant, Nat.beq_refl]
    unfold setDiscriminantOnShell
    dsimp only
    rw [hKeep]
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

/-- **No Variant-Reinterpretation False Accept (`setDiscriminantOnShell_switch_variant_resets_fields`)**:
If payload fields were written for variant `shell.variantIdx` (e.g. `((_1 as A).0) = x`)
and `SetDiscriminant` then writes a *different* tag `variantIdx ≠ shell.variantIdx`
(`discriminant(_1) = B`), every field slot is reset to `FieldSlot.uninit`, so the
old payload is never reinterpreted as variant `B`'s payload: on a non-empty shell
the result is a tagged `.partialShell` whose fields are all uninitialized, it is
never promoted to `.init`, and a whole-local read faults with `.ub`
(`UninitializedLocal`). -/
theorem setDiscriminantOnShell_switch_variant_resets_fields
    (shell : PartialAggregate)
    (variantIdx : VariantIdx)
    (hSwitch : shell.variantIdx ≠ variantIdx)
    (hNonEmpty : shell.fields ≠ .nil) :
    let reset : PartialAggregate :=
      { variantIdx := variantIdx
        isAdt := true
        discriminantSet := true
        fields := replicateUninitFieldSlots shell.fields.length }
    setDiscriminantOnShell shell variantIdx = .partialShell reset ∧
    (∀ i, i < shell.fields.length → get? reset.fields i = .some .uninit) ∧
    (∀ v, setDiscriminantOnShell shell variantIdx ≠ .init v) ∧
    readFromPartialShell .nil reset .nil = .ub := by
  intro reset
  have hBeq : Nat.beq shell.variantIdx variantIdx = false := by
    cases h : Nat.beq shell.variantIdx variantIdx with
    | false => rfl
    | true => exact False.elim (hSwitch (Nat.eq_of_beq_eq_true h))
  have hReset : setDiscriminantFields shell variantIdx =
      replicateUninitFieldSlots shell.fields.length := by
    unfold setDiscriminantFields
    rw [hBeq]
  have hPos : 0 < shell.fields.length := by
    cases hF : shell.fields with
    | nil => exact False.elim (hNonEmpty hF)
    | cons _ _ => simp
  have hUninit0 : get? reset.fields 0 = .some .uninit :=
    get?_replicateUninitFieldSlots hPos
  have hNone : reset.tryIntoValue? = .none :=
    tryIntoValue?_eq_none_of_uninit_field reset 0 hUninit0
  have hEq : setDiscriminantOnShell shell variantIdx = .partialShell reset := by
    unfold setDiscriminantOnShell
    dsimp only
    rw [hReset]
    change (match reset.tryIntoValue? with
      | .some fullVal => LocalSlotState.init fullVal
      | .none => LocalSlotState.partialShell reset) = _
    rw [hNone]
  refine ⟨hEq, ?_, ?_, ?_⟩
  · intro i hLt
    exact get?_replicateUninitFieldSlots hLt
  · intro v hInit
    rw [hEq] at hInit
    nomatch hInit
  · unfold readFromPartialShell
    rw [hNone]

/-- **0-Field Unit Variant Tagging (`setDiscriminantOnShell_zero_field_variant`)**:
On a shell with no field slots (a 0-field unit enum variant), `SetDiscriminant(v)`
promotes to `.init (.aggregate v [])` for every tag `v`. -/
theorem setDiscriminantOnShell_zero_field_variant
    (shell : PartialAggregate)
    (variantIdx : VariantIdx)
    (hEmpty : shell.fields = .nil) :
    setDiscriminantOnShell shell variantIdx = .init (.aggregate variantIdx .nil) := by
  have hFields : setDiscriminantFields shell variantIdx = .nil := by
    unfold setDiscriminantFields
    cases Nat.beq shell.variantIdx variantIdx with
    | true => exact hEmpty
    | false => rw [hEmpty]; rfl
  unfold setDiscriminantOnShell
  dsimp only
  rw [hFields]
  rfl

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

/-- Pointwise lifting of a per-slot refinement relation `R` between Anneal
`LocalSlotState`s and Trusted `LocalSlot`s to whole frames (equal lengths). -/
def SlotsRefine (R : LocalSlotState → LocalSlot → Prop) :
    List LocalSlotState → List LocalSlot → Prop
  | .nil, .nil => True
  | a :: as, t :: ts => R a t ∧ SlotsRefine R as ts
  | _, _ => False

/-- Related frames have equal lengths. -/
theorem SlotsRefine.length_eq
    {R : LocalSlotState → LocalSlot → Prop} :
    ∀ {slots : List LocalSlotState} {locals : List LocalSlot},
      SlotsRefine R slots locals → slots.length = locals.length
  | .nil, .nil, _ => rfl
  | _ :: _, .nil, h => nomatch h
  | .nil, _ :: _, h => nomatch h
  | _ :: as, _ :: ts, h => by
    have := SlotsRefine.length_eq (slots := as) (locals := ts) h.2
    simp [this]

/-- Overwriting slot `i` on both sides with related slots preserves frame refinement. -/
theorem SlotsRefine.set
    {R : LocalSlotState → LocalSlot → Prop}
    {a : LocalSlotState} {t : LocalSlot}
    (hAT : R a t) :
    ∀ {slots : List LocalSlotState} {locals : List LocalSlot} (i : Nat),
      SlotsRefine R slots locals → SlotsRefine R (slots.set i a) (locals.set i t)
  | .nil, .nil, _, _ => trivial
  | _ :: _, .nil, _, h => nomatch h
  | .nil, _ :: _, _, h => nomatch h
  | _ :: _, _ :: _, 0, h => ⟨hAT, h.2⟩
  | _ :: as, _ :: ts, i + 1, h => ⟨h.1, SlotsRefine.set hAT (slots := as) (locals := ts) i h.2⟩

/-- Statement-level evaluator for `StatementKind.storageLive loc` over Anneal
slots (`eval_lowered_statement` in `crates/anneal-mir/src/lower/rvalue.rs`):
fails closed on an out-of-bounds local, and otherwise marks `loc` live and
`.uninit`, discarding any previous value or partial shell. -/
def evalStorageLive (slots : List LocalSlotState) (loc : Local) :
    Option (List LocalSlotState) :=
  match Nat.blt loc slots.length with
  | true => .some (slots.set loc .uninit)
  | false => .none

/-- Statement-level evaluator for `StatementKind.storageDead loc` over Anneal
slots: fails closed on an out-of-bounds local, and otherwise marks `loc` `.dead`. -/
def evalStorageDead (slots : List LocalSlotState) (loc : Local) :
    Option (List LocalSlotState) :=
  match Nat.blt loc slots.length with
  | true => .some (slots.set loc .dead)
  | false => .none

/-- Shared shape of the `StorageLive` / `StorageDead` correspondence: an in-bounds
local is overwritten with `newAnneal` / `newTrusted` on both sides, and an
out-of-bounds local faults on both sides. -/
private theorem storage_stmt_correspondence_aux
    (R : LocalSlotState → LocalSlot → Prop)
    (newAnneal : LocalSlotState)
    (newTrusted : LocalSlot)
    (hNew : R newAnneal newTrusted)
    (slots : List LocalSlotState)
    (locals : List LocalSlot)
    (loc : Local)
    (hRel : SlotsRefine R slots locals) :
    (loc < slots.length →
      get? locals loc ≠ .none ∧
      set? locals loc newTrusted = .some (locals.set loc newTrusted) ∧
      SlotsRefine R (slots.set loc newAnneal) (locals.set loc newTrusted)) ∧
    (¬ loc < slots.length → get? locals loc = .none) := by
  have hLen := SlotsRefine.length_eq hRel
  refine ⟨?_, ?_⟩
  · intro hLt
    have hLtT : loc < locals.length := hLen ▸ hLt
    refine ⟨?_, set?_eq_some_iff.mpr ⟨hLtT, rfl⟩, SlotsRefine.set hNew loc hRel⟩
    simp [hLtT]
  · intro hGe
    have hGeS : slots.length ≤ loc := Nat.le_of_not_lt hGe
    have hGeT : locals.length ≤ loc := hLen ▸ hGeS
    simp [hGeT]

/-- **`StorageLive` Correspondence (`evalStorageLive_trusted_correspondence`)**:
For every per-slot refinement relation `R` relating `.uninit` to `.uninit` and
every Anneal frame `slots` related to the Trusted frame `s.frame.locals`:
1. if `evalStorageLive slots loc = .some slots'`, then
   `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt` on `.storageLive loc` steps
   to `advanceStmt s locals'` (disabling the borrows minted from `loc`) for a
   Trusted frame `locals'` that is again related to `slots'`;
2. if `evalStorageLive` fails closed (out-of-bounds `loc`), Trusted faults with
   `.ub`.
`anneal-mir` does not model function-entry protectors (`Retag(FnEntry)`), so the
theorem assumes no active protector (`s.memory.activeProtectors = []`); with an
active protector Trusted may additionally fault on a protected borrow. -/
theorem evalStorageLive_trusted_correspondence
    (R : LocalSlotState → LocalSlot → Prop)
    (hUninit : R .uninit .uninit)
    (s : MachineState)
    (slots : List LocalSlotState)
    (loc : Local)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hRel : SlotsRefine R slots s.frame.locals)
    (hNoProt : s.memory.activeProtectors = .nil) :
    (∀ slots', evalStorageLive slots loc = .some slots' →
      ∃ locals',
        Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
            s ⟨.storageLive loc, span⟩ localDecls layouts =
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }) ∧
        SlotsRefine R slots' locals') ∧
    (evalStorageLive slots loc = .none →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
          s ⟨.storageLive loc, span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  have hAux := storage_stmt_correspondence_aux R .uninit .uninit hUninit
    slots s.frame.locals loc hRel
  refine ⟨?_, ?_⟩
  · intro slots' hEval
    unfold evalStorageLive at hEval
    cases hLt : Nat.blt loc slots.length with
    | false => rw [hLt] at hEval; nomatch hEval
    | true =>
      rw [hLt] at hEval
      injection hEval with hSlots
      subst hSlots
      have hLtN : loc < slots.length := by simpa using hLt
      obtain ⟨hGet, hSet, hRel'⟩ := hAux.1 hLtN
      refine ⟨s.frame.locals.set loc .uninit, ?_, hRel'⟩
      cases hSlot : get? s.frame.locals loc with
      | none => exact False.elim (hGet hSlot)
      | some slot =>
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
        rw [hSlot]
        dsimp only
        rw [hSet]
        dsimp only
        rw [hNoProt]
  · intro hEval
    unfold evalStorageLive at hEval
    cases hLt : Nat.blt loc slots.length with
    | true => rw [hLt] at hEval; nomatch hEval
    | false =>
      have hGe : ¬ loc < slots.length := by
        intro hLtN
        have hBlt : Nat.blt loc slots.length = true := by simpa using hLtN
        rw [hLt] at hBlt
        nomatch hBlt
      have hNone := hAux.2 hGe
      dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
      rw [hNone]

/-- **`StorageDead` Correspondence (`evalStorageDead_trusted_correspondence`)**:
For every per-slot refinement relation `R` relating `.dead` to `.dead` and every
Anneal frame `slots` related to `s.frame.locals`, a successful
`evalStorageDead slots loc = .some slots'` is matched by Trusted's `evalStmt` on
`.storageDead loc` stepping to a related frame (absent active protectors), and an
out-of-bounds `loc` faults on both sides. -/
theorem evalStorageDead_trusted_correspondence
    (R : LocalSlotState → LocalSlot → Prop)
    (hDead : R .dead .dead)
    (s : MachineState)
    (slots : List LocalSlotState)
    (loc : Local)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hRel : SlotsRefine R slots s.frame.locals)
    (hNoProt : s.memory.activeProtectors = .nil) :
    (∀ slots', evalStorageDead slots loc = .some slots' →
      ∃ locals',
        Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
            s ⟨.storageDead loc, span⟩ localDecls layouts =
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }) ∧
        SlotsRefine R slots' locals') ∧
    (evalStorageDead slots loc = .none →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
          s ⟨.storageDead loc, span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  have hAux := storage_stmt_correspondence_aux R .dead .dead hDead
    slots s.frame.locals loc hRel
  refine ⟨?_, ?_⟩
  · intro slots' hEval
    unfold evalStorageDead at hEval
    cases hLt : Nat.blt loc slots.length with
    | false => rw [hLt] at hEval; nomatch hEval
    | true =>
      rw [hLt] at hEval
      injection hEval with hSlots
      subst hSlots
      have hLtN : loc < slots.length := by simpa using hLt
      obtain ⟨hGet, hSet, hRel'⟩ := hAux.1 hLtN
      refine ⟨s.frame.locals.set loc .dead, ?_, hRel'⟩
      cases hSlot : get? s.frame.locals loc with
      | none => exact False.elim (hGet hSlot)
      | some slot =>
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
        rw [hSlot]
        dsimp only
        rw [hSet]
        dsimp only
        rw [hNoProt]
  · intro hEval
    unfold evalStorageDead at hEval
    cases hLt : Nat.blt loc slots.length with
    | true => rw [hLt] at hEval; nomatch hEval
    | false =>
      have hGe : ¬ loc < slots.length := by
        intro hLtN
        have hBlt : Nat.blt loc slots.length = true := by simpa using hLtN
        rw [hLt] at hBlt
        nomatch hBlt
      have hNone := hAux.2 hGe
      dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
      rw [hNone]

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

/-- **`D13b` Trusted Divergence on In-Place Enum Payload Writes (`evalStmt_assign_uninit_downcast_proj_ub`)**:
`Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt` materializes a default shell
for a projected write into a live but uninitialized local only when the first
projection is `.field` (`uninitFieldWriteShell?`), so `rustc`'s in-place enum
construction `((_1 as V).i) = rv` into an `.uninit` local faults with
`MirStepNode.fail .ub`, whereas Episode 1 (`write_to_partial_slot`) builds an
untagged ADT `PartialAggregate` shell (`isAdt = true`, `discriminantSet = false`)
that `SetDiscriminant` later promotes. Because Trusted reports `.ub` here rather
than `.unsupported`, the ADT partial-shell path lies outside the fragment on
which Anneal's statement semantics can refine Trusted's, and no refinement claim
may be made for it. -/
theorem evalStmt_assign_uninit_downcast_proj_ub
    (s : MachineState)
    (dstLoc : Local)
    (vName : Option String)
    (variantIdx : VariantIdx)
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
    (hUninit : get? locals₁ dstLoc = .some .uninit) :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
      s ⟨.assign ⟨dstLoc, .downcast vName variantIdx :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.fail .ub :=
  evalStmt_assign_uninit_non_aggregate_ub
    s dstLoc (.downcast vName variantIdx) rest rv span localDecls layouts val locals₁ mem₁
    (by intro h; nomatch h) hRv hUninit rfl

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

/-! ### Stateful `LocalSlotState` Evaluators (`PlaceMention`, `Assume`, `SetDiscriminant`, `writePlaceState`) & `SlotsRefine` Correspondence -/

/-- Pointwise lookup preservation for `SlotsRefine`: at any index `i`, either both
frames are out of bounds (`.none`) or both return related slots `R a t`. -/
theorem SlotsRefine.get?_rel
    {R : LocalSlotState → LocalSlot → Prop} :
    ∀ {slots : List LocalSlotState} {locals : List LocalSlot} (i : Nat),
      SlotsRefine R slots locals →
      (get? slots i = .none ∧ get? locals i = .none) ∨
      ∃ a t, get? slots i = .some a ∧ get? locals i = .some t ∧ R a t
  | .nil, .nil, _, _ => Or.inl ⟨rfl, rfl⟩
  | _ :: _, .nil, _, h => nomatch h
  | .nil, _ :: _, _, h => nomatch h
  | a :: _, t :: _, 0, h => Or.inr ⟨a, t, rfl, rfl, h.1⟩
  | _ :: as, _ :: ts, i + 1, h => by
    simp only [get?_eq_getElem?, List.getElem?_cons_succ]
    simp only [← get?_eq_getElem?]
    exact SlotsRefine.get?_rel (slots := as) (locals := ts) i h.2

/-- Strict per-slot refinement relation on promoted states (where any completed
`PartialAggregate` shell has already been promoted to `LocalSlotState.init`):
- `.dead` refines `.dead`
- `.uninit` refines `.uninit`
- `.init v` refines `.init v`
- `.partialShell _` does not refine any completed `LocalSlot`. -/
def PromotedSlotRefines : LocalSlotState → LocalSlot → Prop
  | .dead, .dead => True
  | .uninit, .uninit => True
  | .init v, .init w => v = w
  | _, _ => False

/-- Convert a single `LocalSlotState` to a `LocalSlot` for index/value projection
helpers, mapping any incomplete `.partialShell` to `.uninit` so index reads
through an incomplete shell fault with `.ub` (`UninitializedLocal`). -/
def slotStateToTrustedLocal : LocalSlotState → LocalSlot
  | .dead => .dead
  | .uninit => .uninit
  | .init v => .init v
  | .partialShell shell =>
    match shell.tryIntoValue? with
    | .some v => .init v
    | .none => .uninit

/-- Map `slotStateToTrustedLocal` across a frame of `LocalSlotState`s. -/
def slotsToTrustedLocals : List LocalSlotState → List LocalSlot
  | .nil => .nil
  | s :: rest => slotStateToTrustedLocal s :: slotsToTrustedLocals rest

/-- When `SlotsRefine PromotedSlotRefines slots locals` holds, `slotsToTrustedLocals slots`
is definitionally equal to `locals`. -/
theorem slotsToTrustedLocals_eq_of_promoted :
    ∀ {slots : List LocalSlotState} {locals : List LocalSlot},
      SlotsRefine PromotedSlotRefines slots locals →
      slotsToTrustedLocals slots = locals
  | .nil, .nil, _ => rfl
  | _ :: _, .nil, h => nomatch h
  | .nil, _ :: _, h => nomatch h
  | a :: as, t :: ts, ⟨hAT, hRest⟩ => by
    have hTl := slotsToTrustedLocals_eq_of_promoted hRest
    cases a with
    | dead =>
      cases t with
      | dead => simp [slotsToTrustedLocals, slotStateToTrustedLocal, hTl]
      | uninit => nomatch hAT
      | init _ => nomatch hAT
    | uninit =>
      cases t with
      | dead => nomatch hAT
      | uninit => simp [slotsToTrustedLocals, slotStateToTrustedLocal, hTl]
      | init _ => nomatch hAT
    | partialShell _ => nomatch hAT
    | init v =>
      cases t with
      | dead => nomatch hAT
      | uninit => nomatch hAT
      | init w =>
        dsimp only [PromotedSlotRefines] at hAT
        subst hAT
        simp [slotsToTrustedLocals, slotStateToTrustedLocal, hTl]

/-- Because `PartialAggregate.tryIntoValue?` only ever produces `.aggregate`
values, an index local in `slotsToTrustedLocals slots` holds `.init (.scalar sc)`
if and only if it holds `.init (.scalar sc)` in `slots` (never `.partialShell`). -/
theorem get?_slotsToTrustedLocals_scalar_iff :
    ∀ (slots : List LocalSlotState) (idxLocal : Local) (sc : ScalarInt),
      get? (slotsToTrustedLocals slots) idxLocal = .some (.init (.scalar sc)) ↔
        get? slots idxLocal = .some (.init (.scalar sc)) := by
  intro slots
  induction slots with
  | nil =>
    intro idxLocal sc
    constructor <;> (intro h; nomatch h)
  | cons hd tl ih =>
    intro idxLocal sc
    cases idxLocal with
    | zero =>
      simp only [slotsToTrustedLocals, get?_eq_getElem?, List.getElem?_cons_zero]
      cases hd with
      | dead => constructor <;> (intro h; nomatch h)
      | uninit => constructor <;> (intro h; nomatch h)
      | init v =>
        dsimp only [slotStateToTrustedLocal]
        constructor
        · intro h
          injection h with hSlot
          injection hSlot with hVal
          rw [hVal]
        · intro h
          injection h with hSlot
          injection hSlot with hVal
          rw [hVal]
      | partialShell shell =>
        dsimp only [slotStateToTrustedLocal]
        unfold PartialAggregate.tryIntoValue?
        cases Bool.and shell.isAdt (Bool.not shell.discriminantSet) with
        | true => constructor <;> (intro h; nomatch h)
        | false =>
          dsimp only
          cases tryFieldsIntoValues? shell.fields <;>
            (constructor <;> (intro h; nomatch h))
    | succ i' =>
      simp only [slotsToTrustedLocals, get?_eq_getElem?, List.getElem?_cons_succ]
      simp only [← get?_eq_getElem?]
      exact ih i' sc

/-- Read an array index local from `slots : List LocalSlotState`
(`StatementEvalState::read_index_local` in `crates/anneal-mir/src/lower/rvalue.rs:4630-4659`):
succeeds only when `idxLocal` holds an initialized `usize` scalar (`.init (.scalar sc)`
with `sc.sizeBytes == ptrBytes`), rejecting `.dead`, `.uninit`, `.partialShell`,
and non-`usize` values. -/
def readIndexLocalState
    (slots : List LocalSlotState)
    (ptrBytes : Nat)
    (idxLocal : Local) :
    Option ScalarInt :=
  match get? slots idxLocal with
  | .some (.init (.scalar sc)) =>
    match Nat.beq sc.sizeBytes ptrBytes with
    | true => .some sc
    | false => .none
  | _ => .none

/-- Validate that every `.index idxLocal` projection element in `proj` references
an initialized `usize` scalar in `slots : List LocalSlotState`. -/
def placeIndexLocalsInitState
    (slots : List LocalSlotState)
    (ptrBytes : Nat) :
    List ProjectionElem → Bool
  | .nil => true
  | .index idxLocal :: rest =>
    match readIndexLocalState slots ptrBytes idxLocal with
    | .some _ => placeIndexLocalsInitState slots ptrBytes rest
    | .none => false
  | _ :: rest => placeIndexLocalsInitState slots ptrBytes rest

/-- If `placeIndexLocalsInitState slots ptrBytes proj = true` and `R` maps
`LocalSlotState.init v` to `LocalSlot.init v`, then Trusted's
`placeIndexLocalsInit locals proj = true` holds on any `R`-related `locals`. -/
theorem placeIndexLocalsInitState_implies_trusted
    (R : LocalSlotState → LocalSlot → Prop)
    (hInit : ∀ v t, R (.init v) t → t = .init v)
    (slots : List LocalSlotState)
    (locals : List LocalSlot)
    (ptrBytes : Nat)
    (hRel : SlotsRefine R slots locals) :
    ∀ (proj : List ProjectionElem),
      placeIndexLocalsInitState slots ptrBytes proj = true →
      placeIndexLocalsInit locals proj = true := by
  intro proj
  induction proj with
  | nil => intro _; rfl
  | cons p rest ih =>
    intro hState
    cases p with
    | index idxLocal =>
      unfold placeIndexLocalsInitState at hState
      cases hIdx : readIndexLocalState slots ptrBytes idxLocal with
      | none => rw [hIdx] at hState; nomatch hState
      | some sc =>
        rw [hIdx] at hState
        unfold readIndexLocalState at hIdx
        rcases SlotsRefine.get?_rel idxLocal hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS, hGetT, hAT⟩
        · rw [hNoneS] at hIdx; nomatch hIdx
        · rw [hGetS] at hIdx
          cases a with
          | dead => nomatch hIdx
          | uninit => nomatch hIdx
          | partialShell _ => nomatch hIdx
          | init v =>
            cases v with
            | scalar sc' =>
              have hTEq := hInit (.scalar sc') t hAT
              subst hTEq
              unfold placeIndexLocalsInit
              rw [hGetT]
              exact ih hState
            | _ => nomatch hIdx
    | _ =>
      unfold placeIndexLocalsInitState at hState
      unfold placeIndexLocalsInit
      exact ih hState

/-- Read a `Place` from `slots : List LocalSlotState` (`StatementEvalState::read_place`
in `crates/anneal-mir/src/lower/rvalue.rs:4686-4733`). -/
def readPlaceState (slots : List LocalSlotState) (place : Place) : ProjReadResult :=
  let locals := slotsToTrustedLocals slots
  match get? slots place.local_ with
  | .none => .ub
  | .some .dead => .ub
  | .some .uninit => .ub
  | .some (.init rootVal) => evalValueProjRead locals rootVal place.projection
  | .some (.partialShell shell) => readFromPartialShell locals shell place.projection

/-- Move a `Place` from `slots : List LocalSlotState` (`StatementEvalState::move_place`
in `crates/anneal-mir/src/lower/rvalue.rs:4807-4813`):
moving a bare local (`place.projection = .nil`) transitions `place.local_` to
`.uninit`, while moving a projected place leaves the root slot unchanged. -/
def movePlaceState
    (slots : List LocalSlotState)
    (place : Place) :
    ProjReadResult × List LocalSlotState :=
  match readPlaceState slots place with
  | .ok val =>
    match place.projection with
    | .nil => (.ok val, slots.set place.local_ .uninit)
    | _ :: _ => (.ok val, slots)
  | err => (err, slots)

/-- Evaluate an `Operand` in `slots : List LocalSlotState`
(`eval_op` in `crates/anneal-mir/src/lower/rvalue.rs:5993-5998`). -/
def evalOperandState
    (slots : List LocalSlotState)
    (op : Operand)
    (layouts : LayoutTable := emptyLayoutTable)
    (globals : List CapturedAllocation := .nil) :
    ProjReadResult × List LocalSlotState :=
  match op with
  | .copy place => (readPlaceState slots place, slots)
  | .move place => movePlaceState slots place
  | .constant constOp =>
    match constOp.val with
    | .indirect _ _ => (.unsupported, slots)
    | .unevaluated _ => (.unsupported, slots)
    | cv =>
      match evalConstValue cv constOp.ty globals layouts with
      | .some val => (.ok val, slots)
      | .none => (.unsupported, slots)

/-- Stateful evaluator for `StatementKind.placeMention` over `slots : List LocalSlotState`
(`eval_lowered_statement` on `LoweredStatement::PlaceMention` in
`crates/anneal-mir/src/lower/rvalue.rs:6439-6513`):
1. Requires `place.local_` to be in bounds and not `.dead`;
2. Validates every `.index idxLocal` operand via `placeIndexLocalsInitState slots ptrBytes`;
3. When `projectionHasDeref place.projection = true`, requires the root local to
   hold an initialized pointer value (`.init (.ptr _ _)`), rejecting `.uninit` and
   `.partialShell`. -/
def evalPlaceMentionState
    (slots : List LocalSlotState)
    (ptrBytes : Nat)
    (place : Place) :
    Option Unit :=
  match get? slots place.local_ with
  | .none => .none
  | .some .dead => .none
  | .some rootSlot =>
    match placeIndexLocalsInitState slots ptrBytes place.projection with
    | false => .none
    | true =>
      match projectionHasDeref place.projection, rootSlot with
      | false, _ => .some ()
      | true, .init (.ptr _ _) => .some ()
      | true, _ => .none

/-- **Stateful `D9` `PlaceMention` Correspondence (`evalPlaceMentionState_trusted_correspondence`)**:
Under `SlotsRefine PromotedSlotRefines slots s.frame.locals`:
1. Whenever `evalPlaceMentionState slots ptrBytes place = .some ()`,
   `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt s ⟨.placeMention place, span⟩ localDecls layouts`
   steps to `advanceStmt s s.frame.locals` (leaving all slots and memory unchanged).
2. On an out-of-bounds or `.dead` root local, or on a `.deref` projection when
   the root local is `.uninit` or `.partialShell`, `evalPlaceMentionState` returns
   `.none` and Trusted faults with `MirStepNode.fail .ub`. -/
theorem evalPlaceMentionState_trusted_correspondence
    (s : MachineState)
    (slots : List LocalSlotState)
    (ptrBytes : Nat)
    (place : Place)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hRel : SlotsRefine PromotedSlotRefines slots s.frame.locals) :
    (evalPlaceMentionState slots ptrBytes place = .some () →
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.placeMention place, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s s.frame.locals)) ∧
    ((get? slots place.local_ = .none ∨ get? slots place.local_ = .some .dead) →
      evalPlaceMentionState slots ptrBytes place = .none ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.placeMention place, span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  have hIdxImp :=
    placeIndexLocalsInitState_implies_trusted PromotedSlotRefines
      (by
        intro v t h
        cases t with
        | dead => nomatch h
        | uninit => nomatch h
        | init w =>
          dsimp only [PromotedSlotRefines] at h
          rw [h])
      slots s.frame.locals ptrBytes hRel
  refine ⟨?_, ?_⟩
  · intro hOk
    unfold evalPlaceMentionState at hOk
    rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS, hGetT, hAT⟩
    · rw [hNoneS] at hOk; nomatch hOk
    · rw [hGetS] at hOk
      cases a with
      | dead => nomatch hOk
      | partialShell _ => nomatch hAT
      | uninit =>
        cases t with
        | dead => nomatch hAT
        | init _ => nomatch hAT
        | uninit =>
          dsimp only at hOk
          cases hIdx : placeIndexLocalsInitState slots ptrBytes place.projection with
          | false => rw [hIdx] at hOk; nomatch hOk
          | true =>
            rw [hIdx] at hOk
            dsimp only at hOk
            cases hDeref : projectionHasDeref place.projection with
            | true => rw [hDeref] at hOk; nomatch hOk
            | false =>
              have hIdxT := hIdxImp place.projection hIdx
              dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
              rw [hGetT]
              dsimp only [placeMentionOperandsInit]
              rw [hDeref, hIdxT]
      | init v =>
        cases t with
        | dead => nomatch hAT
        | uninit => nomatch hAT
        | init w =>
          dsimp only [PromotedSlotRefines] at hAT
          subst hAT
          dsimp only at hOk
          cases hIdx : placeIndexLocalsInitState slots ptrBytes place.projection with
          | false => rw [hIdx] at hOk; nomatch hOk
          | true =>
            have hIdxT := hIdxImp place.projection hIdx
            dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
            rw [hGetT]
            dsimp only [placeMentionOperandsInit]
            cases projectionHasDeref place.projection <;> rw [hIdxT]
  · intro hBad
    rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hNoneS, hNoneT⟩ | ⟨a, t, hGetS, hGetT, hAT⟩
    · refine ⟨?_, ?_⟩
      · unfold evalPlaceMentionState; rw [hNoneS]
      · dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]; rw [hNoneT]
    · rcases hBad with hNoneS | hDeadS
      · rw [hGetS] at hNoneS; nomatch hNoneS
      · rw [hGetS] at hDeadS
        injection hDeadS with hAEq
        subst hAEq
        cases t with
        | uninit => nomatch hAT
        | init _ => nomatch hAT
        | dead =>
          refine ⟨?_, ?_⟩
          · unfold evalPlaceMentionState; rw [hGetS]
          · dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]; rw [hGetT]

/-- Non-dereferencing operand predicate: for `.copy p` or `.move p`, `p.projection`
does not start with `.deref` (`p.projection = .nil ∨ ∃ h t, p.projection = h :: t ∧ h ≠ .deref`). -/
def OperandNonDeref : Operand → Prop
  | .copy p => ∀ r, p.projection ≠ .deref :: r
  | .move p => ∀ r, p.projection ≠ .deref :: r
  | .constant _ => True

/-- **Stateful `evalOperandState` Correspondence (`evalOperandState_trusted_correspondence`)**:
Under `SlotsRefine PromotedSlotRefines slots locals` and `OperandNonDeref op`,
every successful operand evaluation `evalOperandState slots op layouts globals = (.ok val, slots')`
is matched by `Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand` stepping to
`.ok val locals'` with `SlotsRefine PromotedSlotRefines slots' locals'`. -/
theorem evalOperandState_trusted_correspondence
    (slots slots' : List LocalSlotState)
    (locals : List LocalSlot)
    (op : Operand)
    (val : Value)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (layouts : LayoutTable)
    (callerLocals : List LocalSlot)
    (hRel : SlotsRefine PromotedSlotRefines slots locals)
    (hNoDeref : OperandNonDeref op)
    (hEval : evalOperandState slots op layouts globals = (.ok val, slots')) :
    ∃ locals',
      Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand
        locals op borrows globals layouts callerLocals = .ok val locals' ∧
      SlotsRefine PromotedSlotRefines slots' locals' := by
  have hLocEq : slotsToTrustedLocals slots = locals :=
    slotsToTrustedLocals_eq_of_promoted hRel
  cases op with
  | constant constOp =>
    unfold evalOperandState at hEval
    dsimp only at hEval
    cases hVal : constOp.val with
    | indirect _ _ => rw [hVal] at hEval; nomatch hEval
    | unevaluated _ => rw [hVal] at hEval; nomatch hEval
    | zeroSized =>
      rw [hVal] at hEval
      dsimp only at hEval
      cases hC : evalConstValue .zeroSized constOp.ty globals layouts with
      | none => rw [hC] at hEval; nomatch hEval
      | some cVal =>
        rw [hC] at hEval
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
        rw [hVal]
        dsimp only
        rw [hC]
    | scalar sc =>
      rw [hVal] at hEval
      dsimp only at hEval
      cases hC : evalConstValue (.scalar sc) constOp.ty globals layouts with
      | none => rw [hC] at hEval; nomatch hEval
      | some cVal =>
        rw [hC] at hEval
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
        rw [hVal]
        dsimp only
        rw [hC]
    | slice aId len =>
      rw [hVal] at hEval
      dsimp only at hEval
      cases hC : evalConstValue (.slice aId len) constOp.ty globals layouts with
      | none => rw [hC] at hEval; nomatch hEval
      | some cVal =>
        rw [hC] at hEval
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
        rw [hVal]
        dsimp only
        rw [hC]
  | copy place =>
    rcases place with ⟨loc, proj⟩
    unfold evalOperandState readPlaceState at hEval
    dsimp only at hEval
    rw [hLocEq] at hEval
    rcases SlotsRefine.get?_rel loc hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS, hGetT, hAT⟩
    · rw [hNoneS] at hEval; nomatch hEval
    · rw [hGetS] at hEval
      cases a with
      | dead => nomatch hEval
      | uninit => nomatch hEval
      | partialShell _ => nomatch hAT
      | init rootVal =>
        cases t with
        | dead => nomatch hAT
        | uninit => nomatch hAT
        | init w =>
          dsimp only [PromotedSlotRefines] at hAT
          subst hAT
          dsimp only at hEval
          injection hEval with hRead hSlots
          subst hSlots
          have hTRead := evalValueProjRead_refines_readProjectedValue proj locals rootVal val hRead
          refine ⟨locals, ?_, hRel⟩
          cases proj with
          | nil =>
            unfold evalValueProjRead at hRead
            injection hRead with hV
            subst hV
            dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
            rw [hGetT]
            rfl
          | cons p rest =>
            cases p with
            | deref => exact False.elim (hNoDeref rest rfl)
            | _ =>
              dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
              rw [hGetT]
              dsimp only
              rw [hTRead]
  | move place =>
    rcases place with ⟨loc, proj⟩
    unfold evalOperandState movePlaceState readPlaceState at hEval
    dsimp only at hEval
    rw [hLocEq] at hEval
    rcases SlotsRefine.get?_rel loc hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS, hGetT, hAT⟩
    · rw [hNoneS] at hEval; nomatch hEval
    · rw [hGetS] at hEval
      cases a with
      | dead => nomatch hEval
      | uninit => nomatch hEval
      | partialShell _ => nomatch hAT
      | init rootVal =>
        cases t with
        | dead => nomatch hAT
        | uninit => nomatch hAT
        | init w =>
          dsimp only [PromotedSlotRefines] at hAT
          subst hAT
          dsimp only at hEval
          cases hRead : evalValueProjRead locals rootVal proj with
          | ub => rw [hRead] at hEval; nomatch hEval
          | unsupported => rw [hRead] at hEval; nomatch hEval
          | ok outVal =>
            rw [hRead] at hEval
            dsimp only at hEval
            have hTRead := evalValueProjRead_refines_readProjectedValue proj locals rootVal outVal hRead
            cases proj with
            | nil =>
              injection hEval with hRes hSlots
              injection hRes with hVal
              subst hVal hSlots
              unfold evalValueProjRead at hRead
              injection hRead with hRootEq
              subst hRootEq
              have hLtT : loc < locals.length := by
                simp only [get?_eq_getElem?] at hGetT
                exact (List.getElem?_eq_some_iff.mp hGetT).1
              have hSetT : set? locals loc .uninit = .some (locals.set loc .uninit) :=
                set?_eq_some_iff.mpr ⟨hLtT, rfl⟩
              refine ⟨locals.set loc .uninit, ?_,
                SlotsRefine.set (R := PromotedSlotRefines) (a := .uninit) (t := .uninit) trivial loc hRel⟩
              dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
              rw [hGetT]
              dsimp only
              rw [hSetT]
            | cons p rest =>
              injection hEval with hRes hSlots
              injection hRes with hVal
              subst hVal hSlots
              refine ⟨locals, ?_, hRel⟩
              cases p with
              | deref => exact False.elim (hNoDeref rest rfl)
              | _ =>
                dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalOperand]
                rw [hGetT]
                dsimp only
                rw [hTRead]

/-- Stateful evaluator for `StatementKind.intrinsic (.assume op)` over
`slots : List LocalSlotState` (`LoweredStatement::Assume` in
`crates/anneal-mir/src/lower/rvalue.rs:6515-6527`). -/
def evalAssumeState
    (slots : List LocalSlotState)
    (op : Operand)
    (layouts : LayoutTable := emptyLayoutTable)
    (globals : List CapturedAllocation := .nil) :
    SlotWriteResult (List LocalSlotState) :=
  let (res, slots') := evalOperandState slots op layouts globals
  match res with
  | .ok (.scalar sc) =>
    match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
    | true => .ok slots'
    | false => .ub
  | .ok _ => .ub
  | .ub => .ub
  | .unsupported => .unsupported

/-- **Stateful `Assume` Correspondence (`evalAssumeState_trusted_correspondence`)**:
Under `SlotsRefine PromotedSlotRefines slots s.frame.locals` and `OperandNonDeref op`:
1. Whenever `evalAssumeState slots op layouts s.memory.globals = .ok slots'`, there exists `locals'`
   such that `Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt s ⟨.intrinsic (.assume op), span⟩ localDecls layouts`
   steps to `advanceStmt s locals'` and `SlotsRefine PromotedSlotRefines slots' locals'`.
2. Whenever `evalOperandState slots op layouts s.memory.globals = (.ok (.scalar ⟨0, 1⟩), slots')`,
   `evalAssumeState slots op layouts s.memory.globals = .ub` and Trusted's `evalStmt` faults with
   `MirStepNode.fail .ub`. -/
theorem evalAssumeState_trusted_correspondence
    (s : MachineState)
    (slots slots' : List LocalSlotState)
    (op : Operand)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hRel : SlotsRefine PromotedSlotRefines slots s.frame.locals)
    (hNoDeref : OperandNonDeref op) :
    (evalAssumeState slots op layouts s.memory.globals = .ok slots' →
      ∃ locals',
        Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
          s ⟨.intrinsic (.assume op), span⟩ localDecls layouts =
          MirStepNode.step (advanceStmt s locals') ∧
        SlotsRefine PromotedSlotRefines slots' locals') ∧
    (evalOperandState slots op layouts s.memory.globals = (.ok (.scalar ⟨0, 1⟩), slots') →
      evalAssumeState slots op layouts s.memory.globals = .ub ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
        s ⟨.intrinsic (.assume op), span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  refine ⟨?_, ?_⟩
  · intro hAssume
    unfold evalAssumeState at hAssume
    cases hOp : evalOperandState slots op layouts s.memory.globals with
    | mk res nextSlots =>
      rw [hOp] at hAssume
      dsimp only at hAssume
      cases res with
      | ub => nomatch hAssume
      | unsupported => nomatch hAssume
      | ok val =>
        cases val with
        | scalar sc =>
          dsimp only at hAssume
          cases hTrue : Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
          | false => rw [hTrue] at hAssume; nomatch hAssume
          | true =>
            rw [hTrue] at hAssume
            injection hAssume with hSlotsEq
            subst hSlotsEq
            obtain ⟨locals', hTOp, hRel'⟩ :=
              evalOperandState_trusted_correspondence
                slots nextSlots s.frame.locals op (.scalar sc)
                s.memory.borrows s.memory.globals layouts s.memory.callerLocals
                hRel hNoDeref hOp
            refine ⟨locals', ?_, hRel'⟩
            dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
            rw [hTOp]
            dsimp only
            rw [hTrue]
        | _ => nomatch hAssume
  · intro hFalseOp
    obtain ⟨locals', hTOp, _⟩ :=
      evalOperandState_trusted_correspondence
        slots slots' s.frame.locals op (.scalar ⟨0, 1⟩)
        s.memory.borrows s.memory.globals layouts s.memory.callerLocals
        hRel hNoDeref hFalseOp
    refine ⟨?_, ?_⟩
    · unfold evalAssumeState
      rw [hFalseOp]
      rfl
    · dsimp only [Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt]
      rw [hTOp]
      rfl

/-- Projected discriminant update on an initialized `Value`
(`set_discriminant_projected_mir_value` in `crates/anneal-mir/src/lower/rvalue.rs:5478-5799`). -/
def setDiscriminantProjectedValue
    (locals : List LocalSlot)
    (val : Value)
    (proj : List ProjectionElem)
    (variantIdx : VariantIdx) :
    ProjWriteResult :=
  match proj with
  | .nil =>
    match val with
    | .aggregate _ fields => .ok (.aggregate variantIdx fields)
    | .unit => .ok (.aggregate variantIdx .nil)
    | _ => .ub
  | p :: rest =>
    match evalValueProjRead locals val (p :: rest) with
    | .ok (.aggregate _ fields) =>
      evalValueProjWrite locals val (p :: rest) (.aggregate variantIdx fields)
    | .ok .unit =>
      evalValueProjWrite locals val (p :: rest) (.aggregate variantIdx .nil)
    | .ok _ => .ub
    | .ub => .ub
    | .unsupported => .unsupported

/-- Recursive `SetDiscriminant` over a `FieldSlot` (`set_discriminant_in_slot` in
`crates/anneal-mir/src/lower/rvalue.rs:5803-5980`):
- On `.init existingVal`: updates the target aggregate via `setDiscriminantProjectedValue`.
- On `.uninit`: faults with `.ub` (`UninitializedLocal`, or `.unsupported` on `.deref`).
- On `.nested`: at `proj = .nil`, applies `setDiscriminantOnShell` (resetting fields
  on variant switch and promoting via `tryIntoValue?`); at `.field` or `.downcast :: .field`,
  recurses into the child slot and promotes bottom-up via `promoteShellToFieldSlot`. -/
def setDiscriminantInFieldSlot
    (locals : List LocalSlot)
    (slot : FieldSlot) :
    List ProjectionElem → VariantIdx → SlotWriteResult FieldSlot
  | proj, variantIdx =>
    match slot with
    | .init existingVal =>
      match setDiscriminantProjectedValue locals existingVal proj variantIdx with
      | .ok updatedVal => .ok (.init updatedVal)
      | .ub => .ub
      | .unsupported => .unsupported
    | .uninit =>
      match proj with
      | .deref :: _ => .unsupported
      | .opaqueCast _ :: _ => .unsupported
      | .unwrapUnsafeBinder _ :: _ => .unsupported
      | _ => .ub
    | .nested sVar sAdt sDisc sFields =>
      match proj with
      | .nil =>
        match setDiscriminantOnShell ⟨sVar, sAdt, sDisc, sFields⟩ variantIdx with
        | .init fullVal => .ok (.init fullVal)
        | .partialShell updated => .ok updated.toFieldSlot
        | _ => .ub
      | .field idx _ :: rest =>
        let actual := match sAdt with | true => sVar | false => 0
        match Nat.beq actual 0, get? sFields idx with
        | true, .some childSlot =>
          match setDiscriminantInFieldSlot locals childSlot rest variantIdx with
          | .ok childSlot' =>
            match set? sFields idx childSlot' with
            | .some fields' =>
              .ok (promoteShellToFieldSlot ⟨sVar, sAdt, sDisc, fields'⟩)
            | .none => .ub
          | .ub => .ub
          | .unsupported => .unsupported
        | _, _ => .ub
      | .downcast _ expectedVar :: rest =>
        let actual := match sAdt with | true => sVar | false => 0
        match rest with
        | .field idx _ :: tail =>
          match Nat.beq actual expectedVar, get? sFields idx with
          | true, .some childSlot =>
            match setDiscriminantInFieldSlot locals childSlot tail variantIdx with
            | .ok childSlot' =>
              match set? sFields idx childSlot' with
              | .some fields' =>
                .ok (promoteShellToFieldSlot ⟨sVar, sAdt, sDisc, fields'⟩)
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _, _ => .ub
        | .deref :: _ => .unsupported
        | .opaqueCast _ :: _ => .unsupported
        | .unwrapUnsafeBinder _ :: _ => .unsupported
        | _ => .ub
      | .index _ :: _ => .ub
      | .constantIndex _ _ _ :: _ => .ub
      | .subslice _ _ _ :: _ => .ub
      | .deref :: _ => .unsupported
      | .opaqueCast _ :: _ => .unsupported
      | .unwrapUnsafeBinder _ :: _ => .unsupported

/-- **Nested Enum-in-Tuple `SetDiscriminant` Bottom-Up Promotion (`setDiscriminantInFieldSlot_nested_promotes`)**:
Suppose an outer tuple/struct shell `outerShell` (`outerShell.isAdt = false`)
holds a nested untagged enum shell `childShell` at field `idx` whose variant
`variantIdx = childShell.variantIdx` has all payload fields initialized
(`childShell.fields = childVals.map FieldSlot.init`), and setting field `idx`
of `outerShell` to `.init (.aggregate variantIdx childVals)` completes all
fields of `outerShell` (`set? outerShell.fields idx ... = .some (outerVals.map FieldSlot.init)`).
Then executing `setDiscriminantInFieldSlot` at `[.field idx fieldTy]` with
`variantIdx` promotes **both** the nested enum shell and the outer tuple shell
bottom-up in a single step to `.ok (.init (.aggregate 0 outerVals))`! -/
theorem setDiscriminantInFieldSlot_nested_promotes
    (locals : List LocalSlot)
    (outerShell childShell : PartialAggregate)
    (idx : FieldIdx)
    (fieldTy : Ty)
    (variantIdx : VariantIdx)
    (childVals outerVals : List Value)
    (hOuterTuple : outerShell.isAdt = false)
    (hGetChild : get? outerShell.fields idx = .some childShell.toFieldSlot)
    (hSameVar : childShell.variantIdx = variantIdx)
    (hChildFields : childShell.fields = childVals.map FieldSlot.init)
    (hOuterComplete :
      set? outerShell.fields idx (.init (.aggregate variantIdx childVals)) =
        .some (outerVals.map FieldSlot.init)) :
    setDiscriminantInFieldSlot locals outerShell.toFieldSlot [.field idx fieldTy] variantIdx =
      .ok (.init (.aggregate 0 outerVals)) := by
  have hChildProm :=
    (setDiscriminantOnShell_promotes_initialized_variant
      childShell variantIdx childVals hSameVar hChildFields).2
  unfold PartialAggregate.toFieldSlot setDiscriminantInFieldSlot
  dsimp only
  rw [hOuterTuple]
  dsimp only
  rw [hGetChild]
  dsimp only
  unfold setDiscriminantInFieldSlot
  dsimp only
  change (match
      match setDiscriminantOnShell childShell variantIdx with
      | .init fullVal => SlotWriteResult.ok (FieldSlot.init fullVal)
      | .partialShell updated => SlotWriteResult.ok updated.toFieldSlot
      | _ => SlotWriteResult.ub with
    | .ok childSlot' =>
      match set? outerShell.fields idx childSlot' with
      | .some fields' =>
        SlotWriteResult.ok
          (promoteShellToFieldSlot
            ⟨outerShell.variantIdx, false, outerShell.discriminantSet, fields'⟩)
      | .none => SlotWriteResult.ub
    | .ub => SlotWriteResult.ub
    | .unsupported => SlotWriteResult.unsupported) = _
  rw [hChildProm]
  dsimp only
  rw [hOuterComplete]
  dsimp only
  unfold promoteShellToFieldSlot PartialAggregate.tryIntoValue?
  dsimp only
  rw [tryFieldsIntoValues?_map_init]
  rfl

/-- Stateful evaluator for `StatementKind.setDiscriminant` over `slots : List LocalSlotState`
(`eval_lowered_statement` on `LoweredStatement::SetDiscriminant` in
`crates/anneal-mir/src/lower/rvalue.rs:6529-6585`). -/
def evalSetDiscriminantState
    (slots : List LocalSlotState)
    (place : Place)
    (variantIdx : VariantIdx) :
    SlotWriteResult (List LocalSlotState) :=
  let locals := slotsToTrustedLocals slots
  match get? slots place.local_ with
  | .none => .ub
  | .some .dead => .ub
  | .some .uninit =>
    match place.projection with
    | .deref :: _ => .unsupported
    | .opaqueCast _ :: _ => .unsupported
    | .unwrapUnsafeBinder _ :: _ => .unsupported
    | _ => .ub
  | .some (.init existingVal) =>
    match setDiscriminantInFieldSlot locals (.init existingVal) place.projection variantIdx with
    | .ok nextSlot => .ok (slots.set place.local_ (fieldSlotToLocalSlotState nextSlot))
    | .ub => .ub
    | .unsupported => .unsupported
  | .some (.partialShell shell) =>
    match setDiscriminantInFieldSlot locals shell.toFieldSlot place.projection variantIdx with
    | .ok nextSlot => .ok (slots.set place.local_ (fieldSlotToLocalSlotState nextSlot))
    | .ub => .ub
    | .unsupported => .unsupported

/-- **Stateful `SetDiscriminant` Correspondence (`evalSetDiscriminantState_trusted_correspondence`)**:
Under `SlotsRefine PromotedSlotRefines slots s.frame.locals`:
1. On a bare local `⟨loc, .nil⟩` holding `.init (.aggregate oldVar fields)` in `slots`,
   `evalSetDiscriminantState` returns `.ok (slots.set loc (.init (.aggregate variantIdx fields)))`,
   Trusted's `evalStmt` steps to `advanceStmt s (s.frame.locals.set loc (.init (.aggregate variantIdx fields)))`,
   and the updated frames satisfy `SlotsRefine PromotedSlotRefines`.
2. On a projected place `⟨loc, proj :: rest⟩` (`proj ≠ .deref`) where reading `proj :: rest`
   from `rootVal` yields `.aggregate oldVar fields` and writing `.aggregate variantIdx fields`
   back yields `rootVal'`, `evalSetDiscriminantState` returns `.ok (slots.set loc (.init rootVal'))`
   and Trusted's `evalStmt` steps to a `PromotedSlotRefines`-related frame. -/
theorem evalSetDiscriminantState_trusted_correspondence
    (s : MachineState)
    (slots : List LocalSlotState)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (variantIdx oldVar : VariantIdx)
    (fields : List Value)
    (rootVal rootVal' : Value)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hRel : SlotsRefine PromotedSlotRefines slots s.frame.locals) :
    (get? slots loc = .some (.init (.aggregate oldVar fields)) →
      evalSetDiscriminantState slots ⟨loc, .nil⟩ variantIdx =
        .ok (slots.set loc (.init (.aggregate variantIdx fields))) ∧
      ∃ locals',
        Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
          s ⟨.setDiscriminant ⟨loc, .nil⟩ variantIdx, span⟩ localDecls layouts =
          MirStepNode.step (advanceStmt s locals') ∧
        SlotsRefine PromotedSlotRefines
          (slots.set loc (.init (.aggregate variantIdx fields))) locals') ∧
    (proj ≠ .deref →
      get? slots loc = .some (.init rootVal) →
      evalValueProjRead s.frame.locals rootVal (proj :: rest) =
        .ok (.aggregate oldVar fields) →
      evalValueProjWrite s.frame.locals rootVal (proj :: rest)
        (.aggregate variantIdx fields) = .ok rootVal' →
      evalSetDiscriminantState slots ⟨loc, proj :: rest⟩ variantIdx =
        .ok (slots.set loc (.init rootVal')) ∧
      ∃ locals',
        Trusted.Rustc.V2026_06_01.MirSemantics.evalStmt
          s ⟨.setDiscriminant ⟨loc, proj :: rest⟩ variantIdx, span⟩ localDecls layouts =
          MirStepNode.step (advanceStmt s locals') ∧
        SlotsRefine PromotedSlotRefines
          (slots.set loc (.init rootVal')) locals') := by
  have hLocEq : slotsToTrustedLocals slots = s.frame.locals :=
    slotsToTrustedLocals_eq_of_promoted hRel
  refine ⟨?_, ?_⟩
  · intro hGetS
    rcases SlotsRefine.get?_rel loc hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS', hGetT, hAT⟩
    · rw [hNoneS] at hGetS; nomatch hGetS
    · rw [hGetS] at hGetS'
      injection hGetS' with hAEq
      subst hAEq
      cases t with
      | dead => nomatch hAT
      | uninit => nomatch hAT
      | init w =>
        dsimp only [PromotedSlotRefines] at hAT
        subst hAT
        have hLtT : loc < s.frame.locals.length := by
          simp only [get?_eq_getElem?] at hGetT
          exact (List.getElem?_eq_some_iff.mp hGetT).1
        have hSetT :
            set? s.frame.locals loc (.init (.aggregate variantIdx fields)) =
              .some (s.frame.locals.set loc (.init (.aggregate variantIdx fields))) :=
          set?_eq_some_iff.mpr ⟨hLtT, rfl⟩
        refine ⟨?_, s.frame.locals.set loc (.init (.aggregate variantIdx fields)), ?_,
          SlotsRefine.set (R := PromotedSlotRefines)
            (a := .init (.aggregate variantIdx fields))
            (t := .init (.aggregate variantIdx fields)) rfl loc hRel⟩
        · unfold evalSetDiscriminantState
          dsimp only
          rw [hGetS]
          rfl
        · exact (evalStmt_setDiscriminant_correspondence
            s loc proj rest variantIdx oldVar fields rootVal rootVal'
            (s.frame.locals.set loc (.init (.aggregate variantIdx fields)))
            span localDecls layouts).1 hGetT hSetT
  · intro hNotDeref hGetS hRead hWrite
    rcases SlotsRefine.get?_rel loc hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS', hGetT, hAT⟩
    · rw [hNoneS] at hGetS; nomatch hGetS
    · rw [hGetS] at hGetS'
      injection hGetS' with hAEq
      subst hAEq
      cases t with
      | dead => nomatch hAT
      | uninit => nomatch hAT
      | init w =>
        dsimp only [PromotedSlotRefines] at hAT
        subst hAT
        have hLtT : loc < s.frame.locals.length := by
          simp only [get?_eq_getElem?] at hGetT
          exact (List.getElem?_eq_some_iff.mp hGetT).1
        have hSetT :
            set? s.frame.locals loc (.init rootVal') =
              .some (s.frame.locals.set loc (.init rootVal')) :=
          set?_eq_some_iff.mpr ⟨hLtT, rfl⟩
        refine ⟨?_, s.frame.locals.set loc (.init rootVal'), ?_,
          SlotsRefine.set (R := PromotedSlotRefines)
            (a := .init rootVal') (t := .init rootVal') rfl loc hRel⟩
        · unfold evalSetDiscriminantState
          dsimp only
          rw [hLocEq, hGetS]
          dsimp only [setDiscriminantInFieldSlot, setDiscriminantProjectedValue]
          rw [hRead]
          dsimp only
          rw [hWrite]
          rfl
        · exact (evalStmt_setDiscriminant_correspondence
            s loc proj rest variantIdx oldVar fields rootVal rootVal'
            (s.frame.locals.set loc (.init rootVal'))
            span localDecls layouts).2 hNotDeref hGetT hRead hWrite hSetT

/-- Stateful place writer over `slots : List LocalSlotState`
(`StatementEvalState::write_place` in `crates/anneal-mir/src/lower/rvalue.rs:4850-4949`). -/
def writePlaceState
    (arityOf : Ty → VariantIdx → Bool → Option Nat)
    (slots : List LocalSlotState)
    (place : Place)
    (rootTy : Ty)
    (newVal : Value) :
    SlotWriteResult (List LocalSlotState) :=
  let locals := slotsToTrustedLocals slots
  match get? slots place.local_ with
  | .none => .ub
  | .some .dead => .ub
  | .some .uninit =>
    match writeToFieldSlot locals arityOf .uninit rootTy place.projection newVal with
    | .ok nextSlot => .ok (slots.set place.local_ (fieldSlotToLocalSlotState nextSlot))
    | .ub => .ub
    | .unsupported => .unsupported
  | .some (.init existingVal) =>
    match writeToFieldSlot locals arityOf (.init existingVal) rootTy place.projection newVal with
    | .ok nextSlot => .ok (slots.set place.local_ (fieldSlotToLocalSlotState nextSlot))
    | .ub => .ub
    | .unsupported => .unsupported
  | .some (.partialShell shell) =>
    match writeToFieldSlot locals arityOf shell.toFieldSlot rootTy place.projection newVal with
    | .ok nextSlot => .ok (slots.set place.local_ (fieldSlotToLocalSlotState nextSlot))
    | .ub => .ub
    | .unsupported => .unsupported

/-- **Stateful `writePlaceState` Correspondence on Initialized / Bare Places (`writePlaceState_trusted_correspondence`)**:
Under `SlotsRefine PromotedSlotRefines slots locals`:
1. Writing `newVal` to a bare live local `⟨loc, .nil⟩` (`get? slots loc = .some slot`,
   `slot ≠ .dead`) updates `slots` to `slots.set loc (.init newVal)` and Trusted's
   `writePlaceValue` (with `projection = .nil`) updates `locals` to
   `locals.set loc (.init newVal)`, preserving `SlotsRefine PromotedSlotRefines`.
2. Writing `newVal` to a projected non-`Deref` place `⟨loc, proj :: rest⟩` on an
   initialized root local (`get? slots loc = .some (.init rootVal)`) where
   `evalValueProjWrite locals rootVal (proj :: rest) newVal = .ok rootVal'`
   updates `slots` to `slots.set loc (.init rootVal')` and Trusted's
   `writeProjectedValue` returns `.ok rootVal'`, preserving `SlotsRefine PromotedSlotRefines`. -/
theorem writePlaceState_trusted_correspondence
    (arityOf : Ty → VariantIdx → Bool → Option Nat)
    (slots : List LocalSlotState)
    (locals : List LocalSlot)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (rootTy : Ty)
    (rootVal newVal rootVal' : Value)
    (hRel : SlotsRefine PromotedSlotRefines slots locals) :
    (∀ slot : LocalSlotState,
      get? slots loc = .some slot →
      slot ≠ .dead →
      writePlaceState arityOf slots ⟨loc, .nil⟩ rootTy newVal =
        .ok (slots.set loc (.init newVal)) ∧
      set? locals loc (.init newVal) = .some (locals.set loc (.init newVal)) ∧
      SlotsRefine PromotedSlotRefines
        (slots.set loc (.init newVal)) (locals.set loc (.init newVal))) ∧
    (get? slots loc = .some (.init rootVal) →
      evalValueProjWrite locals rootVal (proj :: rest) newVal = .ok rootVal' →
      writePlaceState arityOf slots ⟨loc, proj :: rest⟩ rootTy newVal =
        .ok (slots.set loc (.init rootVal')) ∧
      Trusted.Rustc.V2026_06_01.MirSemantics.writeProjectedValue
        locals rootVal (proj :: rest) newVal = .ok rootVal' ∧
      SlotsRefine PromotedSlotRefines
        (slots.set loc (.init rootVal')) (locals.set loc (.init rootVal'))) := by
  have hLocEq : slotsToTrustedLocals slots = locals :=
    slotsToTrustedLocals_eq_of_promoted hRel
  refine ⟨?_, ?_⟩
  · intro slot hGetS hNotDead
    rcases SlotsRefine.get?_rel loc hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS', hGetT, hAT⟩
    · rw [hNoneS] at hGetS; nomatch hGetS
    · rw [hGetS] at hGetS'
      injection hGetS' with hAEq
      subst hAEq
      have hLtT : loc < locals.length := by
        simp only [get?_eq_getElem?] at hGetT
        exact (List.getElem?_eq_some_iff.mp hGetT).1
      refine ⟨?_, set?_eq_some_iff.mpr ⟨hLtT, rfl⟩,
        SlotsRefine.set (R := PromotedSlotRefines)
          (a := .init newVal) (t := .init newVal) rfl loc hRel⟩
      unfold writePlaceState
      dsimp only
      rw [hGetS]
      cases slot with
      | dead => exact False.elim (hNotDead rfl)
      | uninit => rfl
      | init _ => rfl
      | partialShell _ => rfl
  · intro hGetS hWrite
    rcases SlotsRefine.get?_rel loc hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS', hGetT, hAT⟩
    · rw [hNoneS] at hGetS; nomatch hGetS
    · rw [hGetS] at hGetS'
      injection hGetS' with hAEq
      subst hAEq
      refine ⟨?_,
        evalValueProjWrite_refines_writeProjectedValue (proj :: rest) locals rootVal newVal rootVal' hWrite,
        SlotsRefine.set (R := PromotedSlotRefines)
          (a := .init rootVal') (t := .init rootVal') rfl loc hRel⟩
      unfold writePlaceState
      dsimp only
      rw [hLocEq, hGetS]
      dsimp only [writeToFieldSlot]
      rw [hWrite]
      rfl

end Anneal.Mir.PlaceAndRvalue
