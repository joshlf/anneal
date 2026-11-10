/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Anneal.Mir.PlaceAndRvalue
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Machine

open Trusted.Sequence
open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.Mir.PlaceAndRvalue

namespace Anneal.Mir.AdtAndControl

/-!
# ADT Layouts, Projected `Deinit`/`Retag`/`CopyNonOverlapping`, and Multi-Block CFG Execution

This module formalizes the Episode 1 semantic surface of `crates/anneal-mir`
(`ws-mir-lower-adt-deinit-retag-terminators`) and relates it to
`Trusted.Rustc.V2026_06_01.MirSemantics`:

1. **Section 1 — `ScalarValidRange` niches, ADT layouts, `OffsetOf`, and `Discriminant`**
   (`crates/anneal-mir/src/ir.rs`, `rvalue.rs`):
   - `ScalarValidRange` (`ir.rs`), its width-bounded wrapping/non-wrapping membership test,
     `full`/`nonZero` constructors, emptiness/fullness/niche characterizations, the
     wrapping complement partition, and exact agreement with Trusted's
     `wrappingRangeContains` (`rustc_abi::WrappingRange::contains`).
   - `AdtLayoutSpec`: `#[repr(C)]`/`#[repr(Rust)]`/`#[repr(transparent)]` structs, unions,
     explicit-tag `#[repr(Int)]`/`#[repr(C, Int)]` enums, `rustc`'s univariant tagless enums
     (absent variants are 1-ZSTs, `A1`/`B2`), zero-variant enums (`E0084`), and unspecified
     tagless layouts; `adtLayout?` and `resolveAdtOffsetOf` (`AdtDef::field_offset`), with
     `resolveAdtOffsetOf_bounds_and_align` (every resolved field fits in the container and is
     aligned), `#[repr(C)]` offset monotonicity, union zero offsets, and
     `#[repr(transparent)]` zero-offset delegation.
   - `evalAdtDiscriminant` (`Rvalue::Discriminant` on typed ADTs): absent/uninhabited variant
     rejection (`B2`), the niche-capable incomplete-shell rule (`PartialAggregate::tag_is_readable`,
     `A3`), and agreement with Trusted's `evalPlaceDiscriminant`.

2. **Section 2 — Projected `Deinit`, `Retag`, `CopyNonOverlapping`, `ShallowInitBox`,
   `WrapUnsafeBinder`, and `PointerCoercion`** (`rvalue.rs`):
   - `deinitFieldSlot` / `evalDeinitPlace` (`deinit_in_slot` / `deinit_place`) over the
     `FieldSlot` / `LocalSlotState` model of `Anneal.Mir.PlaceAndRvalue`, with the lens laws
     `evalDeinitPlace_read_same_ub` (Get-Deinit: every prefix and extension of the place,
     including the whole local, faults), `evalDeinitPlace_read_disjoint_eq` (Disjoint-Sibling
     and distinct-local frames), `evalDeinitPlace_write_reinit` (Put-After-Deinit re-promotion)
     and its niche counterpart `deinitFieldSlot_niche_write_needs_setDiscriminant` (`A3`).
   - A byte-level reference model (`deinitBytes` over `List (Option UInt8)`) and the simulation
     theorems `structBytes_deinit` / `evalDeinitPlace_bytes_simulation` /
     `evalDeinitPlace_reprC_bytes_simulation`: field-level `Deinit` on a struct with disjoint
     field layouts (in particular `#[repr(C)]`, via `resolveAdtOffsetOf`) is MiniRust's
     byte-range `Uninit` write (closing the projected-`Deinit` gap noted at
     `MiniRustSpec/Correspondence/Translate.lean:3742`).
   - Step refinement against Trusted's `evalStmt` on `.deinit` under the `SlotBelow` frame
     relation (Anneal knows less than Trusted; every Anneal read is a Trusted read:
     `readPlaceState_below_refines`), and the documented divergence on projected `Deinit`
     below an uninitialized local (`evalStmt_deinit_projected_uninit_root_divergence`).
   - `evalRetagPlace` (`retag_place`: raw retags and recursive reference checks with the `A3`
     dangling rule), `copyNonOverlappingChecks` (agreeing with Trusted's `rangesDisjoint`),
     `evalShallowInitBox`, `evalWrapUnsafeBinder`, and `evalPointerCoercion` with their
     soundness/preservation theorems.

3. **Section 3 — Multi-block terminator CFG execution** (`cfg.rs`):
   - `LTerminator` (`LoweredTerminator`), the single step `evalLoweredTerminator`
     (`eval_lowered_terminator`), and the fuel-bounded driver `runLoweredCfgSteps`
     (`eval_cfg_in_state`), with fuel metatheory (`runLoweredCfgSteps_zero_fuel`,
     `runLoweredCfgSteps_add_fuel`, `runLoweredCfgSteps_mono`),
     `evalSwitchTargets_eq_lookupSwitchTarget`, and the refinement theorems
     `evalLoweredTerminator_refines_trusted` / `runLoweredCfgSteps_refines_trusted` against
     Trusted's `evalTerminator` / `stepMirFn` / `stepMirState` under `BodyCorr` / `StateCorr`
     (Trusted never faults where Anneal succeeds), plus the projected-`Drop` refinement and
     the documented bare-`Drop` divergence.
-/

/-! ## Section 1: `ScalarValidRange` Niches -/

/-- Valid range of a scalar's bit pattern (`ScalarValidRange` in `crates/anneal-mir/src/ir.rs`,
`rustc`'s `WrappingRange`): `start..=end_`, wrapping around the scalar's modulus when
`start > end_`. -/
structure ScalarValidRange : Type where
  /-- First valid bit pattern. -/
  start : Nat
  /-- Last valid bit pattern (inclusive; below `start` for a wrapping range). -/
  end_ : Nat
  deriving DecidableEq, Repr

namespace ScalarValidRange

/-- `ScalarValidRange::contains(bits, bit_width)`: `bits` must fit in `bitWidth` bits
(`bits <= width_mask(bit_width)`, i.e. `bits < 2 ^ bitWidth`), and then lie in
`start..=end_` (non-wrapping, `start <= end_`) or in `start..` / `..=end_` (wrapping,
`start > end_`). -/
def contains (r : ScalarValidRange) (bits bitWidth : Nat) : Bool :=
  if bits < 2 ^ bitWidth then
    if r.start ≤ r.end_ then decide (r.start ≤ bits ∧ bits ≤ r.end_)
    else decide (r.start ≤ bits ∨ bits ≤ r.end_)
  else false

/-- `ScalarValidRange::full(bit_width)`: `0..=width_mask(bit_width)` (no niche). -/
def full (bitWidth : Nat) : ScalarValidRange := ⟨0, 2 ^ bitWidth - 1⟩

/-- `ScalarValidRange::non_zero(bit_width)`: `1..=width_mask(bit_width)` (the
`NonZero<T>` / `NonNull<T>` niche). -/
def nonZero (bitWidth : Nat) : ScalarValidRange := ⟨1, 2 ^ bitWidth - 1⟩

/-- `ScalarValidRange::is_wrapping`: `start > end_`. -/
def isWrapping (r : ScalarValidRange) : Bool := decide (r.end_ < r.start)

/-- `ScalarValidRange::is_empty(bit_width)`: only a non-wrapping range whose `start`
exceeds the width (`start > width_mask`, i.e. `2 ^ bitWidth ≤ start`) is empty. -/
def isEmpty (r : ScalarValidRange) (bitWidth : Nat) : Bool :=
  decide (r.start ≤ r.end_ ∧ 2 ^ bitWidth ≤ r.start)

/-- `ScalarValidRange::is_full(bit_width)`: every `bitWidth`-bit pattern is contained. -/
def isFull (r : ScalarValidRange) (bitWidth : Nat) : Bool :=
  if r.start ≤ r.end_ then decide (r.start = 0 ∧ 2 ^ bitWidth - 1 ≤ r.end_)
  else decide (2 ^ bitWidth - 1 ≤ r.end_ ∨ r.start = r.end_ + 1)

/-- A range exposes a niche (`contains_niche` for a scalar-valid-range ADT) iff it is not
full. -/
def containsNiche (r : ScalarValidRange) (bitWidth : Nat) : Bool := !r.isFull bitWidth

/-- The Trusted `WrappingRange` with the same bounds. -/
def toWrappingRange (r : ScalarValidRange) : WrappingRange := ⟨r.start, r.end_⟩

/-- The complement of a non-wrapping range `start..=end_` (`0 < start`) inside the
`bitWidth`-bit patterns: the wrapping range `(end_ + 1)..=(start - 1)`. -/
def complement (r : ScalarValidRange) : ScalarValidRange := ⟨r.end_ + 1, r.start - 1⟩

/-- Characterization of `contains` as a proposition. -/
theorem contains_eq_true_iff (r : ScalarValidRange) (bits bitWidth : Nat) :
    r.contains bits bitWidth = true ↔
      bits < 2 ^ bitWidth ∧
        ((r.start ≤ r.end_ ∧ r.start ≤ bits ∧ bits ≤ r.end_) ∨
          (r.end_ < r.start ∧ (r.start ≤ bits ∨ bits ≤ r.end_))) := by
  unfold contains
  by_cases hLt : bits < 2 ^ bitWidth
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hLt)]
    by_cases hLe : r.start ≤ r.end_
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hLe), decide_eq_true_iff]
      constructor
      · intro h; exact ⟨hLt, Or.inl ⟨hLe, h⟩⟩
      · rintro ⟨_, (⟨_, h⟩ | ⟨h, _⟩)⟩
        · exact h
        · exact absurd hLe (Nat.not_le.mpr h)
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hLe), decide_eq_true_iff]
      constructor
      · intro h; exact ⟨hLt, Or.inr ⟨Nat.lt_of_not_le hLe, h⟩⟩
      · rintro ⟨_, (⟨h, _⟩ | ⟨_, h⟩)⟩
        · exact absurd h hLe
        · exact h
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hLt)]
    constructor
    · intro h; exact absurd h Bool.false_ne_true
    · rintro ⟨h, _⟩; exact absurd h hLt

/-- **Width-bound soundness**: a contained bit pattern fits in `bitWidth` bits. -/
theorem contains_lt_pow {r : ScalarValidRange} {bits bitWidth : Nat}
    (h : r.contains bits bitWidth = true) : bits < 2 ^ bitWidth :=
  ((contains_eq_true_iff r bits bitWidth).mp h).1

/-- **Exact agreement with Trusted**: `contains` is the width bound conjoined with Trusted's
`wrappingRangeContains` (`rustc_abi::WrappingRange::contains`), which `ScalarLayout.initialized`
validity checks in `Trusted.Rustc.V2026_06_01.MirSemantics.Bytes` use. -/
theorem contains_eq_wrappingRangeContains (r : ScalarValidRange) (bits bitWidth : Nat) :
    r.contains bits bitWidth =
      (decide (bits < 2 ^ bitWidth) && wrappingRangeContains r.toWrappingRange bits) := by
  apply Bool.eq_iff_iff.mpr
  rw [contains_eq_true_iff, Bool.and_eq_true, decide_eq_true_iff]
  unfold wrappingRangeContains toWrappingRange
  dsimp only
  by_cases hLe : r.start ≤ r.end_
  · have hB : Nat.ble r.start r.end_ = true := Nat.ble_eq.mpr hLe
    rw [hB]
    simp only [Bool.and_eq_true, Nat.ble_eq]
    constructor
    · rintro ⟨hLt, (⟨_, h1, h2⟩ | ⟨h3, _⟩)⟩
      · exact ⟨hLt, h1, h2⟩
      · exact absurd hLe (Nat.not_le.mpr h3)
    · rintro ⟨hLt, h1, h2⟩
      exact ⟨hLt, Or.inl ⟨hLe, h1, h2⟩⟩
  · have hB : Nat.ble r.start r.end_ = false := by
      cases h : Nat.ble r.start r.end_ with
      | false => rfl
      | true => exact absurd (Nat.ble_eq.mp h) hLe
    rw [hB]
    simp only [Bool.or_eq_true, Nat.ble_eq]
    constructor
    · rintro ⟨hLt, (⟨h1, _, _⟩ | ⟨_, h3⟩)⟩
      · exact absurd h1 hLe
      · exact ⟨hLt, h3⟩
    · rintro ⟨hLt, h⟩
      exact ⟨hLt, Or.inr ⟨Nat.lt_of_not_le hLe, h⟩⟩

/-- **`full` completeness**: every `bitWidth`-bit pattern is in `full bitWidth`. -/
theorem full_contains {bits bitWidth : Nat} (h : bits < 2 ^ bitWidth) :
    (full bitWidth).contains bits bitWidth = true := by
  rw [contains_eq_true_iff]
  refine ⟨h, Or.inl ⟨Nat.zero_le _, Nat.zero_le _, ?_⟩⟩
  show bits ≤ 2 ^ bitWidth - 1
  omega

/-- `full bitWidth` contains exactly the `bitWidth`-bit patterns. -/
theorem full_contains_iff (bits bitWidth : Nat) :
    (full bitWidth).contains bits bitWidth = true ↔ bits < 2 ^ bitWidth :=
  ⟨contains_lt_pow, full_contains⟩

/-- **`nonZero` characterization**: for a positive width, `nonZero w` contains exactly the
non-zero `w`-bit patterns (the `NonZero<T>` niche excludes only `0`). -/
theorem nonZero_contains_iff {bits bitWidth : Nat} (hW : 0 < bitWidth) :
    (nonZero bitWidth).contains bits bitWidth = true ↔ 0 < bits ∧ bits < 2 ^ bitWidth := by
  have hPow : 2 ≤ 2 ^ bitWidth := by
    have h := Nat.pow_le_pow_right (show 0 < 2 by decide) hW
    rw [Nat.pow_one] at h
    exact h
  rw [contains_eq_true_iff]
  show (bits < 2 ^ bitWidth ∧
      ((1 ≤ 2 ^ bitWidth - 1 ∧ 1 ≤ bits ∧ bits ≤ 2 ^ bitWidth - 1) ∨
        (2 ^ bitWidth - 1 < 1 ∧ (1 ≤ bits ∨ bits ≤ 2 ^ bitWidth - 1)))) ↔ _
  constructor
  · rintro ⟨hLt, (⟨_, h1, _⟩ | ⟨hBad, _⟩)⟩
    · exact ⟨h1, hLt⟩
    · omega
  · rintro ⟨hPos, hLt⟩
    exact ⟨hLt, Or.inl ⟨by omega, hPos, by omega⟩⟩

/-- For a positive width, `nonZero w` never contains `0`. (At width `0`, `nonZero 0 =
1..=0` is a wrapping range containing the only `0`-bit pattern, as in `crates/anneal-mir`.) -/
theorem nonZero_not_contains_zero {bitWidth : Nat} (hW : 0 < bitWidth) :
    (nonZero bitWidth).contains 0 bitWidth = false := by
  cases h : (nonZero bitWidth).contains 0 bitWidth with
  | false => rfl
  | true =>
    have h' := ((nonZero_contains_iff hW).mp h).1
    exact absurd h' (Nat.lt_irrefl 0)

/-- **Emptiness characterization**: `isEmpty` holds iff no bit pattern is contained. -/
theorem isEmpty_iff_forall_not_contains (r : ScalarValidRange) (bitWidth : Nat) :
    r.isEmpty bitWidth = true ↔ ∀ bits, r.contains bits bitWidth = false := by
  unfold isEmpty
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨hLe, hBig⟩ bits
    cases h : r.contains bits bitWidth with
    | false => rfl
    | true =>
      rw [contains_eq_true_iff] at h
      omega
  · intro hAll
    have hPos : 0 < 2 ^ bitWidth := Nat.two_pow_pos bitWidth
    by_cases hLe : r.start ≤ r.end_
    · refine ⟨hLe, ?_⟩
      apply Classical.byContradiction
      intro hSmall
      have hTrue : r.contains r.start bitWidth = true := by
        rw [contains_eq_true_iff]
        exact ⟨by omega, Or.inl ⟨hLe, Nat.le_refl _, hLe⟩⟩
      rw [hAll r.start] at hTrue
      nomatch hTrue
    · have hTrue : r.contains 0 bitWidth = true := by
        rw [contains_eq_true_iff]
        exact ⟨hPos, Or.inr ⟨by omega, Or.inr (Nat.zero_le _)⟩⟩
      rw [hAll 0] at hTrue
      nomatch hTrue

/-- A wrapping range always contains the zero bit pattern. -/
theorem isWrapping_contains_zero {r : ScalarValidRange} (bitWidth : Nat)
    (h : r.isWrapping = true) : r.contains 0 bitWidth = true := by
  unfold isWrapping at h
  have hGt : r.end_ < r.start := of_decide_eq_true h
  rw [contains_eq_true_iff]
  exact ⟨Nat.two_pow_pos bitWidth, Or.inr ⟨hGt, Or.inr (Nat.zero_le _)⟩⟩

/-- **Fullness characterization**: `isFull` holds iff every `bitWidth`-bit pattern is
contained. -/
theorem isFull_iff_forall_contains (r : ScalarValidRange) (bitWidth : Nat) :
    r.isFull bitWidth = true ↔ ∀ bits, bits < 2 ^ bitWidth → r.contains bits bitWidth = true := by
  have hPos : 0 < 2 ^ bitWidth := Nat.two_pow_pos bitWidth
  unfold isFull
  by_cases hLe : r.start ≤ r.end_
  · simp only [hLe, ↓reduceIte, decide_eq_true_iff]
    constructor
    · rintro ⟨h0, hEnd⟩ bits hLt
      rw [contains_eq_true_iff]
      exact ⟨hLt, Or.inl ⟨hLe, by omega, by omega⟩⟩
    · intro hAll
      have h0 := (contains_eq_true_iff r 0 bitWidth).mp (hAll 0 hPos)
      have hMax := (contains_eq_true_iff r (2 ^ bitWidth - 1) bitWidth).mp
        (hAll (2 ^ bitWidth - 1) (by omega))
      omega
  · simp only [hLe, ↓reduceIte, decide_eq_true_iff]
    constructor
    · rintro hCase bits hLt
      rw [contains_eq_true_iff]
      omega
    · intro hAll
      by_cases hEnd : 2 ^ bitWidth - 1 ≤ r.end_
      · exact Or.inl hEnd
      · right
        apply Classical.byContradiction
        intro hAdj
        -- `end_ + 1` lies strictly between `end_` and `start` and inside the width.
        have h := (contains_eq_true_iff r (r.end_ + 1) bitWidth).mp
          (hAll (r.end_ + 1) (by omega))
        omega

/-- **Niche characterization**: a range exposes a niche iff some `bitWidth`-bit pattern is
excluded. -/
theorem containsNiche_iff_exists_excluded (r : ScalarValidRange) (bitWidth : Nat) :
    r.containsNiche bitWidth = true ↔
      ∃ bits, bits < 2 ^ bitWidth ∧ r.contains bits bitWidth = false := by
  unfold containsNiche
  constructor
  · intro h
    have hNotFull : r.isFull bitWidth = false := by
      cases hF : r.isFull bitWidth with
      | false => rfl
      | true => rw [hF] at h; nomatch h
    apply Classical.byContradiction
    intro hNo
    have hAll : ∀ bits, bits < 2 ^ bitWidth → r.contains bits bitWidth = true := by
      intro bits hLt
      cases hC : r.contains bits bitWidth with
      | true => rfl
      | false => exact absurd ⟨bits, hLt, hC⟩ hNo
    rw [(isFull_iff_forall_contains r bitWidth).mpr hAll] at hNotFull
    nomatch hNotFull
  · rintro ⟨bits, hLt, hC⟩
    cases hF : r.isFull bitWidth with
    | false => rfl
    | true =>
      have h := (isFull_iff_forall_contains r bitWidth).mp hF bits hLt
      rw [hC] at h
      nomatch h

/-- `NonZero<T>`-style ranges expose a niche (the `0` pattern). -/
theorem nonZero_containsNiche {bitWidth : Nat} (hW : 0 < bitWidth) :
    (nonZero bitWidth).containsNiche bitWidth = true :=
  (containsNiche_iff_exists_excluded _ _).mpr
    ⟨0, Nat.two_pow_pos bitWidth, nonZero_not_contains_zero hW⟩

/-- **Wrapping/non-wrapping partition**: for a non-wrapping range `start..=end_` with
`0 < start`, the wrapping range `complement r = (end_ + 1)..=(start - 1)` contains exactly
the `bitWidth`-bit patterns that `r` excludes. -/
theorem complement_contains {r : ScalarValidRange} {bitWidth : Nat}
    (hLe : r.start ≤ r.end_) (hStart : 0 < r.start)
    (bits : Nat) (hLt : bits < 2 ^ bitWidth) :
    r.complement.contains bits bitWidth = !r.contains bits bitWidth := by
  apply Bool.eq_iff_iff.mpr
  rw [Bool.not_eq_true', contains_eq_true_iff]
  constructor
  · intro hC
    cases hR : r.contains bits bitWidth with
    | false => rfl
    | true =>
      rw [contains_eq_true_iff] at hR
      simp only [complement] at hC
      omega
  · intro hNot
    have hNot' : ¬ (r.start ≤ bits ∧ bits ≤ r.end_) := by
      intro ⟨h1, h2⟩
      apply Bool.false_ne_true
      rw [← hNot, contains_eq_true_iff]
      exact ⟨hLt, Or.inl ⟨hLe, h1, h2⟩⟩
    simp only [complement]
    omega

end ScalarValidRange

/-! ## Section 1b: ADT Layout Specifications, `resolveAdtOffsetOf`, and Offset Bounds -/

/-- Exact size and ABI alignment of a field type (`TyLayout` in `crates/anneal-mir/src/ir.rs`). -/
structure FieldLayout : Type where
  /-- Size in bytes. -/
  size : Nat
  /-- ABI alignment in bytes. -/
  align : Nat
  deriving DecidableEq, Repr

/-- A 1-ZST (size `0`, alignment `1`), which `#[repr(transparent)]` ignores. -/
def FieldLayout.isOneZst (f : FieldLayout) : Bool := f.size == 0 && f.align == 1

/-- Primary `#[repr(...)]` of an ADT (`AdtReprKind` in `ir.rs`). -/
inductive AdtReprKind : Type where
  | rust
  | c
  | transparent
  deriving DecidableEq, Repr

/-- Layout-relevant shape of an ADT (the decision `AdtDef::layout_info` takes in `ir.rs`):
- `struct fields` / `union fields`;
- `taggedEnum tagSize variants`: an explicit integer tag (`#[repr(Int)]` when the `repr` is
  `rust`, `#[repr(C, Int)]` when it is `c`);
- `univariantEnum present variants`: a tagless, non-`#[repr(C)]` enum whose only present
  variant is `present` (every other variant is *absent*: an uninhabited 1-ZST variant,
  `AdtDef::univariant_index`), laid out like a struct of `present`'s fields without a tag;
- `noPresentEnum variants`: an enum without variants or with only absent ones (laid out like
  `!`; `E0084` rejects zero-variant enums with a non-`Rust` repr or `repr(align)`);
- `unspecifiedEnum variants`: a tagless `#[repr(C)]` enum (C `int` tag of target-dependent size)
  or a tagless enum with several present variants (`rustc` niche/tag optimizations), whose
  layout the model leaves unspecified (`LayoutError::Unspecified`). -/
inductive AdtShape : Type where
  | struct (fields : List FieldLayout)
  | union (fields : List FieldLayout)
  | taggedEnum (tagSize : Nat) (variants : List (List FieldLayout))
  | univariantEnum (present : Nat) (variants : List (List FieldLayout))
  | noPresentEnum (variants : List (List FieldLayout))
  | unspecifiedEnum (variants : List (List FieldLayout))

/-- An ADT layout specification (`AdtDef` with its fields' layouts resolved). -/
structure AdtLayoutSpec : Type where
  /-- Layout-relevant shape. -/
  shape : AdtShape
  /-- Primary representation. -/
  repr : AdtReprKind
  /-- `#[repr(align(N))]`, if any. -/
  reprAlign : Option Nat
  /-- For `#[repr(Rust)]` field lists: whether declaration order is the order `rustc`
  keeps (the sortedness and niche-freedom conditions of `Ty::has_canonical_byte_layout`,
  which depend on field types); the padding-freedom condition is checked by
  `paddingFree`. -/
  rustOrderCanonical : Bool

/-- Maximum of `base` and the fields' alignments. -/
def maxAlign (base : Nat) : List FieldLayout → Nat
  | [] => base
  | f :: fs => maxAlign (max base f.align) fs

/-- Sum of the fields' sizes. -/
def sumSizes : List FieldLayout → Nat
  | [] => 0
  | f :: fs => f.size + sumSizes fs

/-- Maximum field size (`0` for no fields). -/
def maxSize : List FieldLayout → Nat
  | [] => 0
  | f :: fs => max f.size (maxSize fs)

/-- Maximum of a list of naturals (`0` for the empty list). -/
def maxList : List Nat → Nat
  | [] => 0
  | x :: xs => max x (maxList xs)

/-- End offset of a `#[repr(C)]` field sequence starting at `start`: each field is placed at
the next multiple of its alignment. -/
def cEnd (start : Nat) : List FieldLayout → Nat
  | [] => start
  | f :: fs => cEnd (PlaceAndRvalue.alignUp start f.align + f.size) fs

/-- Offset of field `i` of a `#[repr(C)]` field sequence starting at `start`
(`struct_like_field_offset` with `AdtReprKind::C`). -/
def cOffset? (start : Nat) : List FieldLayout → Nat → Option Nat
  | [], _ => none
  | f :: _, 0 => some (PlaceAndRvalue.alignUp start f.align)
  | f :: fs, i + 1 => cOffset? (PlaceAndRvalue.alignUp start f.align + f.size) fs i

/-- Declaration order starting at `start` has no padding: every field's prefix-sum offset is a
multiple of its alignment (`Ty::has_canonical_byte_layout`'s padding condition). -/
def paddingFree (start : Nat) : List FieldLayout → Bool
  | [] => true
  | f :: fs => (start % f.align == 0) && paddingFree (start + f.size) fs

/-- Declaration-order prefix-sum offset of field `i` starting at `start` (`rust_field_offset`). -/
def rustOffset? (start : Nat) : List FieldLayout → Nat → Option Nat
  | [], _ => none
  | _ :: _, 0 => some start
  | f :: fs, i + 1 => rustOffset? (start + f.size) fs i

/-- The fields that are not 1-ZSTs. -/
def nonOneZstFields (fs : List FieldLayout) : List FieldLayout :=
  fs.filter (fun f => !f.isOneZst)

/-- Maximum of `base` and every field alignment of every variant. -/
def variantsAlign (base : Nat) : List (List FieldLayout) → Nat
  | [] => base
  | v :: vs => variantsAlign (maxAlign base v) vs

/-- Layout `(size, align)` of a struct-like field list (`struct_like_layout`): `#[repr(C)]`
and `#[repr(Rust)]` round the (padded resp. minimal) field extent up to the alignment;
`#[repr(transparent)]` has the layout of its unique non-1-ZST field (`E0690` for several,
`E0692` with `repr(align)`). -/
def structLayout? (repr : AdtReprKind) (reprAlign : Option Nat) (fs : List FieldLayout) :
    Option (Nat × Nat) :=
  match repr with
  | .c =>
    let a := maxAlign (reprAlign.getD 1) fs
    some (PlaceAndRvalue.alignUp (cEnd 0 fs) a, a)
  | .rust =>
    let a := maxAlign (reprAlign.getD 1) fs
    some (PlaceAndRvalue.alignUp (sumSizes fs) a, a)
  | .transparent =>
    match reprAlign, nonOneZstFields fs with
    | some _, _ => none
    | none, [] => some (0, 1)
    | none, [f] => some (f.size, f.align)
    | none, _ :: _ :: _ => none

/-- Offset of field `i` of a struct-like field list (`struct_like_field_offset`):
`#[repr(C)]` declaration-order padded offsets; `#[repr(Rust)]` prefix sums when declaration
order is canonical and padding-free; `#[repr(transparent)]` places its non-1-ZST field (and,
when every field is zero-sized, all fields) at `0` and other 1-ZSTs like `#[repr(Rust)]`. -/
def structFieldOffset? (repr : AdtReprKind) (rustCanon : Bool) (fs : List FieldLayout) (i : Nat) :
    Option Nat :=
  match repr with
  | .c => cOffset? 0 fs i
  | .rust => if rustCanon && paddingFree 0 fs then rustOffset? 0 fs i else none
  | .transparent =>
    match fs[i]? with
    | none => none
    | some f =>
      if !f.isOneZst then some 0
      else if fs.all (fun g => g.size == 0) then some 0
      else if rustCanon && paddingFree 0 fs then rustOffset? 0 fs i
      else none

/-- Layout of a union: at least one field (`E0784`), all at offset `0`; alignment the `max` of
the field and `repr(align)` alignments, size the largest field rounded up to it. -/
def unionLayout? (repr : AdtReprKind) (reprAlign : Option Nat) (fs : List FieldLayout) :
    Option (Nat × Nat) :=
  match fs with
  | [] => none
  | _ :: _ =>
    if repr = .transparent ∧ (reprAlign.isSome ∨ 1 < (nonOneZstFields fs).length) then none
    else
      let a := maxAlign (reprAlign.getD 1) fs
      some (PlaceAndRvalue.alignUp (maxSize fs) a, a)

/-- Alignment of the `#[repr(C, Int)]` payload union (the `max` variant struct alignment). -/
def payloadAlign (vs : List (List FieldLayout)) : Nat := variantsAlign 1 vs

/-- Offset of the `#[repr(C, Int)]` payload union after a tag of `tagSize` bytes. -/
def payloadOffset (tagSize : Nat) (vs : List (List FieldLayout)) : Nat :=
  PlaceAndRvalue.alignUp tagSize (payloadAlign vs)

/-- Layout of an explicit-tag enum (`tagged_layout`): `#[repr(Int)]` is a `#[repr(C)]` union of
one `#[repr(C)]` struct `(tag, fields...)` per variant; `#[repr(C, Int)]` is a `#[repr(C)]`
struct `(tag, payload)` whose payload is a `#[repr(C)]` union of the variants' field structs. -/
def taggedLayout? (repr : AdtReprKind) (reprAlign : Option Nat) (tagSize : Nat)
    (vs : List (List FieldLayout)) : Option (Nat × Nat) :=
  match repr with
  | .transparent => none
  | .rust =>
    let a := variantsAlign (max (reprAlign.getD 1) tagSize) vs
    let size := maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd tagSize v) (maxAlign tagSize v)))
    some (PlaceAndRvalue.alignUp size a, a)
  | .c =>
    let pa := payloadAlign vs
    let ps := maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v)))
    let a := max (max (reprAlign.getD 1) tagSize) pa
    some (PlaceAndRvalue.alignUp (payloadOffset tagSize vs + PlaceAndRvalue.alignUp ps pa) a, a)

/-- Field offset inside an explicit-tag enum (`AdtDef::field_offset`). -/
def taggedFieldOffset? (repr : AdtReprKind) (tagSize : Nat) (vs : List (List FieldLayout))
    (v i : Nat) : Option Nat :=
  match vs[v]? with
  | none => none
  | some fs =>
    match repr with
    | .transparent => none
    | .rust => cOffset? tagSize fs i
    | .c => (cOffset? 0 fs i).map (fun inner => payloadOffset tagSize vs + inner)

/-- Offset `0` of field `i` of an absent variant's (1-ZST) field list. -/
def absentFieldOffset? (fs : List FieldLayout) (i : Nat) : Option Nat :=
  if i < fs.length then some 0 else none

/-- Layout `(size, align)` of an ADT (`AdtDef::layout_info` restricted to exact layouts). -/
def adtLayout? (spec : AdtLayoutSpec) : Option (Nat × Nat) :=
  match spec.shape with
  | .struct fs => structLayout? spec.repr spec.reprAlign fs
  | .union fs => unionLayout? spec.repr spec.reprAlign fs
  | .taggedEnum tagSize vs => taggedLayout? spec.repr spec.reprAlign tagSize vs
  | .univariantEnum present vs =>
    match vs[present]? with
    | none => none
    | some fs => if spec.repr = .c then none else structLayout? spec.repr spec.reprAlign fs
  | .noPresentEnum vs =>
    match spec.repr with
    | .c => none
    | .transparent => if vs.length = 1 ∧ spec.reprAlign = none then some (0, 1) else none
    | .rust => if vs = [] ∧ spec.reprAlign.isSome then none else some (0, 1)
  | .unspecifiedEnum _ => none

/-- Field types (layouts) of variant `v` (`AdtDef::variant_fields`). -/
def variantFields (spec : AdtLayoutSpec) (v : Nat) : Option (List FieldLayout) :=
  match spec.shape with
  | .struct fs | .union fs => if v = 0 then some fs else none
  | .taggedEnum _ vs | .univariantEnum _ vs | .noPresentEnum vs | .unspecifiedEnum vs => vs[v]?

/-- `AdtDef::field_offset(variant_idx, field_idx)`: the byte offset of field `i` of variant `v`,
or `none` when the layout is ill-formed or unspecified (`resolve_offset_of`'s ADT step). -/
def resolveAdtOffsetOf (spec : AdtLayoutSpec) (v i : Nat) : Option Nat :=
  match adtLayout? spec with
  | none => none
  | some _ =>
    match spec.shape with
    | .struct fs => if v = 0 then structFieldOffset? spec.repr spec.rustOrderCanonical fs i else none
    | .union fs => if v = 0 ∧ i < fs.length then some 0 else none
    | .taggedEnum tagSize vs => taggedFieldOffset? spec.repr tagSize vs v i
    | .univariantEnum present vs =>
      match vs[v]? with
      | none => none
      | some fs =>
        if v = present then structFieldOffset? spec.repr spec.rustOrderCanonical fs i
        else absentFieldOffset? fs i
    | .noPresentEnum vs =>
      match vs[v]? with
      | none => none
      | some fs => absentFieldOffset? fs i
    | .unspecifiedEnum _ => none

/-- `n` is a power of two (every alignment in `rustc`'s layout model). -/
def IsPow2 (n : Nat) : Prop := ∃ k, n = 2 ^ k

/-- Every field of every variant of a shape. -/
def AdtShape.allFields : AdtShape → List FieldLayout
  | .struct fs | .union fs => fs
  | .taggedEnum _ vs | .univariantEnum _ vs | .noPresentEnum vs | .unspecifiedEnum vs => vs.flatten

/-- Well-formedness of a layout specification: power-of-two alignments and tag size, and
zero-sized (1-ZST) fields in absent variants (as `AdtDef::is_absent_variant` requires). -/
structure AdtLayoutSpec.WF (spec : AdtLayoutSpec) : Prop where
  fieldAlignPow2 : ∀ f ∈ spec.shape.allFields, IsPow2 f.align
  reprAlignPow2 : ∀ a, spec.reprAlign = some a → IsPow2 a
  tagPow2 : ∀ t vs, spec.shape = .taggedEnum t vs → IsPow2 t
  absentZeroSized : ∀ p vs, spec.shape = .univariantEnum p vs →
    ∀ v fs, vs[v]? = some fs → v ≠ p → ∀ f ∈ fs, f.size = 0
  noPresentZeroSized : ∀ vs, spec.shape = .noPresentEnum vs → ∀ fs ∈ vs, ∀ f ∈ fs, f.size = 0

/-! ### Arithmetic lemmas -/

theorem IsPow2.pos {n : Nat} (h : IsPow2 n) : 0 < n := by
  rcases h with ⟨k, rfl⟩
  exact Nat.two_pow_pos k

theorem IsPow2.dvd_of_le {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) (hLe : a ≤ b) : a ∣ b := by
  rcases ha with ⟨i, rfl⟩
  rcases hb with ⟨j, rfl⟩
  exact Nat.pow_dvd_pow 2 ((Nat.pow_le_pow_iff_right (by decide)).mp hLe)

theorem IsPow2.max {a b : Nat} (ha : IsPow2 a) (hb : IsPow2 b) : IsPow2 (max a b) := by
  rcases Nat.le_total a b with h | h
  · rw [Nat.max_eq_right h]; exact hb
  · rw [Nat.max_eq_left h]; exact ha

theorem isPow2_one : IsPow2 1 := ⟨0, rfl⟩

theorem alignUp_dvd (x a : Nat) (hPos : 0 < a) : a ∣ PlaceAndRvalue.alignUp x a :=
  Nat.dvd_of_mod_eq_zero (PlaceAndRvalue.alignUp_mod_eq_zero x a hPos)

theorem le_maxAlign_base : ∀ (base : Nat) (fs : List FieldLayout), base ≤ maxAlign base fs
  | _, [] => Nat.le_refl _
  | base, f :: fs => Nat.le_trans (Nat.le_max_left base f.align) (le_maxAlign_base _ fs)

theorem le_maxAlign_of_mem :
    ∀ (base : Nat) (fs : List FieldLayout) (f : FieldLayout), f ∈ fs → f.align ≤ maxAlign base fs
  | _, [], _, h => nomatch h
  | base, g :: gs, f, h => by
    rcases List.mem_cons.mp h with rfl | hMem
    · exact Nat.le_trans (Nat.le_max_right base f.align) (le_maxAlign_base _ gs)
    · exact le_maxAlign_of_mem _ gs f hMem

theorem maxAlign_pow2 :
    ∀ (base : Nat) (fs : List FieldLayout), IsPow2 base → (∀ f ∈ fs, IsPow2 f.align) →
      IsPow2 (maxAlign base fs)
  | _, [], hb, _ => hb
  | _, f :: fs, hb, hfs =>
    maxAlign_pow2 _ fs (hb.max (hfs f (List.mem_cons_self ..)))
      (fun g hg => hfs g (List.mem_cons_of_mem _ hg))

theorem le_maxSize_of_mem : ∀ (fs : List FieldLayout) (f : FieldLayout), f ∈ fs → f.size ≤ maxSize fs
  | [], _, h => nomatch h
  | g :: gs, f, h => by
    rcases List.mem_cons.mp h with rfl | hMem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxSize_of_mem gs f hMem) (Nat.le_max_right _ _)

theorem le_maxList_of_mem : ∀ (xs : List Nat) (x : Nat), x ∈ xs → x ≤ maxList xs
  | [], _, h => nomatch h
  | y :: ys, x, h => by
    rcases List.mem_cons.mp h with rfl | hMem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (le_maxList_of_mem ys x hMem) (Nat.le_max_right _ _)

theorem le_variantsAlign_base :
    ∀ (base : Nat) (vs : List (List FieldLayout)), base ≤ variantsAlign base vs
  | _, [] => Nat.le_refl _
  | base, v :: vs => Nat.le_trans (le_maxAlign_base base v) (le_variantsAlign_base _ vs)

theorem le_variantsAlign_of_mem :
    ∀ (base : Nat) (vs : List (List FieldLayout)) (fs : List FieldLayout) (f : FieldLayout),
      fs ∈ vs → f ∈ fs → f.align ≤ variantsAlign base vs
  | _, [], _, _, h, _ => nomatch h
  | base, v :: vs, fs, f, hV, hF => by
    rcases List.mem_cons.mp hV with rfl | hMem
    · exact Nat.le_trans (le_maxAlign_of_mem base fs f hF) (le_variantsAlign_base _ vs)
    · exact le_variantsAlign_of_mem _ vs fs f hMem hF

theorem variantsAlign_pow2 :
    ∀ (base : Nat) (vs : List (List FieldLayout)), IsPow2 base →
      (∀ fs ∈ vs, ∀ f ∈ fs, IsPow2 f.align) → IsPow2 (variantsAlign base vs)
  | _, [], hb, _ => hb
  | base, v :: vs, hb, hvs =>
    variantsAlign_pow2 _ vs (maxAlign_pow2 base v hb (hvs v (List.mem_cons_self ..)))
      (fun fs hfs => hvs fs (List.mem_cons_of_mem _ hfs))

theorem le_cEnd : ∀ (start : Nat) (fs : List FieldLayout), start ≤ cEnd start fs
  | _, [] => Nat.le_refl _
  | start, f :: fs =>
    Nat.le_trans (Nat.le_trans (PlaceAndRvalue.alignUp_ge start f.align) (Nat.le_add_right _ _)) (le_cEnd _ fs)

/-- **`#[repr(C)]` offsets are aligned and in bounds**: field `i` exists, its offset is a
multiple of its (positive) alignment, and the field ends before the sequence's end. -/
theorem cOffset?_spec :
    ∀ (start : Nat) (fs : List FieldLayout) (i off : Nat), cOffset? start fs i = some off →
      ∃ f, fs[i]? = some f ∧ off + f.size ≤ cEnd start fs ∧ (0 < f.align → f.align ∣ off)
  | _, [], _, _, h => by simp [cOffset?] at h
  | start, f :: fs, 0, off, h => by
    simp only [cOffset?, Option.some.injEq] at h
    subst h
    exact ⟨f, rfl, le_cEnd _ fs, fun hPos => alignUp_dvd start f.align hPos⟩
  | start, f :: fs, i + 1, off, h => by
    simp only [cOffset?] at h
    rcases cOffset?_spec _ fs i off h with ⟨g, hG, hEnd, hDvd⟩
    exact ⟨g, by simpa using hG, by simpa [cEnd] using hEnd, hDvd⟩

/-- **`#[repr(C)]` offset monotonicity**: an earlier field ends at or before a later field's
offset. -/
theorem cOffset?_monotone :
    ∀ (start : Nat) (fs : List FieldLayout) (i j oi oj : Nat), i < j →
      cOffset? start fs i = some oi → cOffset? start fs j = some oj →
      ∃ fi, fs[i]? = some fi ∧ oi + fi.size ≤ oj
  | _, [], _, _, _, _, _, h, _ => by simp [cOffset?] at h
  | start, f :: fs, 0, j + 1, oi, oj, _, hi, hj => by
    simp only [cOffset?, Option.some.injEq] at hi hj
    subst hi
    refine ⟨f, rfl, ?_⟩
    -- every later offset is at least the next start `PlaceAndRvalue.alignUp start f.align + f.size`
    have hGe : ∀ (st : Nat) (gs : List FieldLayout) (k o : Nat), cOffset? st gs k = some o → st ≤ o := by
      intro st gs
      induction gs generalizing st with
      | nil => intro k o h; simp [cOffset?] at h
      | cons g gs ih =>
        intro k o h
        cases k with
        | zero =>
          simp only [cOffset?, Option.some.injEq] at h
          subst h
          exact PlaceAndRvalue.alignUp_ge st g.align
        | succ k =>
          simp only [cOffset?] at h
          exact Nat.le_trans (Nat.le_trans (PlaceAndRvalue.alignUp_ge st g.align) (Nat.le_add_right _ _)) (ih _ k o h)
    exact hGe _ fs j oj hj
  | _, _ :: _, _ + 1, 0, _, _, hLt, _, _ => absurd hLt (Nat.not_lt_zero _)
  | start, f :: fs, i + 1, j + 1, oi, oj, hLt, hi, hj => by
    simp only [cOffset?] at hi hj
    rcases cOffset?_monotone _ fs i j oi oj (by omega) hi hj with ⟨fi, hFi, hLe⟩
    exact ⟨fi, by simpa using hFi, hLe⟩

/-- **Padding-free prefix offsets are aligned and in bounds** (`#[repr(Rust)]` canonical
layouts). -/
theorem rustOffset?_spec :
    ∀ (start : Nat) (fs : List FieldLayout) (i off : Nat), rustOffset? start fs i = some off →
      paddingFree start fs = true →
      ∃ f, fs[i]? = some f ∧ off + f.size ≤ start + sumSizes fs ∧ off % f.align = 0
  | _, [], _, _, h, _ => by simp [rustOffset?] at h
  | start, f :: fs, 0, off, h, hPad => by
    simp only [rustOffset?, Option.some.injEq] at h
    subst h
    simp only [paddingFree, Bool.and_eq_true, beq_iff_eq] at hPad
    refine ⟨f, rfl, ?_, hPad.1⟩
    simp only [sumSizes]
    omega
  | start, f :: fs, i + 1, off, h, hPad => by
    simp only [rustOffset?] at h
    simp only [paddingFree, Bool.and_eq_true, beq_iff_eq] at hPad
    rcases rustOffset?_spec _ fs i off h hPad.2 with ⟨g, hG, hEnd, hMod⟩
    refine ⟨g, by simpa using hG, ?_, hMod⟩
    simp only [sumSizes]
    omega

theorem sumSizes_nonOneZstFields : ∀ (fs : List FieldLayout), sumSizes (nonOneZstFields fs) = sumSizes fs
  | [] => rfl
  | f :: fs => by
    have ih := sumSizes_nonOneZstFields fs
    unfold nonOneZstFields at ih ⊢
    rw [List.filter_cons]
    cases hZ : f.isOneZst with
    | false => simp only [Bool.not_false, ↓reduceIte, sumSizes, ih]
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, ih, sumSizes]
      simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZ
      rw [hZ.1, Nat.zero_add]

theorem getElem?_mem {α : Type} {xs : List α} {i : Nat} {x : α} (h : xs[i]? = some x) : x ∈ xs :=
  List.mem_of_getElem? h

/-- **Struct-like offset bounds**: a resolved struct-like field offset lies inside the
struct-like layout and is aligned. -/
theorem structFieldOffset?_bounds (repr : AdtReprKind) (rustCanon : Bool) (reprAlign : Option Nat)
    (fs : List FieldLayout) (hPow : ∀ f ∈ fs, IsPow2 f.align)
    {i off size align : Nat}
    (hLay : structLayout? repr reprAlign fs = some (size, align))
    (hOff : structFieldOffset? repr rustCanon fs i = some off) :
    ∃ f, fs[i]? = some f ∧ off + f.size ≤ size ∧ f.align ∣ off := by
  cases repr with
  | c =>
    simp only [structLayout?, Option.some.injEq, Prod.mk.injEq] at hLay
    rcases hLay with ⟨rfl, rfl⟩
    simp only [structFieldOffset?] at hOff
    rcases cOffset?_spec 0 fs i off hOff with ⟨f, hF, hEnd, hDvd⟩
    exact ⟨f, hF, Nat.le_trans hEnd (PlaceAndRvalue.alignUp_ge _ _), hDvd (hPow f (getElem?_mem hF)).pos⟩
  | rust =>
    simp only [structLayout?, Option.some.injEq, Prod.mk.injEq] at hLay
    rcases hLay with ⟨rfl, rfl⟩
    simp only [structFieldOffset?] at hOff
    split at hOff
    · rename_i hCan
      simp only [Bool.and_eq_true] at hCan
      rcases rustOffset?_spec 0 fs i off hOff hCan.2 with ⟨f, hF, hEnd, hMod⟩
      refine ⟨f, hF, ?_, Nat.dvd_of_mod_eq_zero hMod⟩
      have := PlaceAndRvalue.alignUp_ge (sumSizes fs) (maxAlign (reprAlign.getD 1) fs)
      omega
    · nomatch hOff
  | transparent =>
    simp only [structFieldOffset?] at hOff
    cases hFi : fs[i]? with
    | none => rw [hFi] at hOff; nomatch hOff
    | some f =>
      rw [hFi] at hOff
      simp only at hOff
      refine ⟨f, rfl, ?_⟩
      have hMem : f ∈ fs := getElem?_mem hFi
      -- The struct layout is that of the unique non-1-ZST field (or `(0, 1)`).
      unfold structLayout? at hLay
      cases hRAo : reprAlign with
      | some a => rw [hRAo] at hLay; nomatch hLay
      | none =>
        cases hNZ : nonOneZstFields fs with
        | nil =>
          simp only [hRAo, hNZ, Option.some.injEq, Prod.mk.injEq] at hLay
          rcases hLay with ⟨rfl, rfl⟩
          -- every field is a 1-ZST
          have hZ : f.isOneZst = true := by
            cases hZf : f.isOneZst with
            | true => rfl
            | false =>
              have : f ∈ nonOneZstFields fs := by
                unfold nonOneZstFields; rw [List.mem_filter]; exact ⟨hMem, by simp [hZf]⟩
              rw [hNZ] at this; nomatch this
          simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZ
          have hAll : fs.all (fun g => g.size == 0) = true := by
            rw [List.all_eq_true]
            intro g hg
            cases hZg : g.isOneZst with
            | true =>
              simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZg
              simp [hZg.1]
            | false =>
              have : g ∈ nonOneZstFields fs := by
                unfold nonOneZstFields; rw [List.mem_filter]; exact ⟨hg, by simp [hZg]⟩
              rw [hNZ] at this; nomatch this
          have hNot : (!f.isOneZst) = false := by simp [FieldLayout.isOneZst, hZ.1, hZ.2]
          rw [hNot, hAll] at hOff
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hOff
          subst hOff
          exact ⟨by omega, Nat.dvd_zero _⟩
        | cons g gs =>
          cases gs with
          | cons _ _ => simp only [hRAo, hNZ, reduceCtorEq] at hLay
          | nil =>
            simp only [hRAo, hNZ, Option.some.injEq, Prod.mk.injEq] at hLay
            rcases hLay with ⟨rfl, rfl⟩
            cases hZf : f.isOneZst with
            | false =>
              -- `f` is the unique non-1-ZST field `g`, at offset `0`.
              have hfg : f ∈ nonOneZstFields fs := by
                unfold nonOneZstFields; rw [List.mem_filter]; exact ⟨hMem, by simp [hZf]⟩
              rw [hNZ, List.mem_singleton] at hfg
              subst hfg
              rw [hZf] at hOff
              simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hOff
              subst hOff
              exact ⟨by omega, Nat.dvd_zero _⟩
            | true =>
              simp only [FieldLayout.isOneZst, Bool.and_eq_true, beq_iff_eq] at hZf
              have hNot : (!f.isOneZst) = false := by simp [FieldLayout.isOneZst, hZf.1, hZf.2]
              rw [hNot] at hOff
              simp only [Bool.false_eq_true, ↓reduceIte] at hOff
              split at hOff
              · simp only [Option.some.injEq] at hOff
                subst hOff
                exact ⟨by omega, Nat.dvd_zero _⟩
              · split at hOff
                · rename_i _ hCan
                  simp only [Bool.and_eq_true] at hCan
                  rcases rustOffset?_spec 0 fs i off hOff hCan.2 with ⟨f', hF', hEnd, _⟩
                  rw [hFi, Option.some.injEq] at hF'
                  subst hF'
                  have hSum := sumSizes_nonOneZstFields fs
                  rw [hNZ] at hSum
                  simp only [sumSizes] at hSum
                  refine ⟨by omega, ?_⟩
                  rw [hZf.2]
                  exact Nat.one_dvd _
                · nomatch hOff

theorem mem_allFields_of_variant {vs : List (List FieldLayout)} {v : Nat} {fs : List FieldLayout}
    {f : FieldLayout} (hV : vs[v]? = some fs) (hF : f ∈ fs) : f ∈ vs.flatten :=
  List.mem_flatten.mpr ⟨fs, getElem?_mem hV, hF⟩

/-- **`resolveAdtOffsetOf_bounds_and_align`** (`AdtDef::field_offset`'s contract in `ir.rs`):
whenever `resolveAdtOffsetOf spec v i = some off` for a well-formed specification, variant `v`
and its field `i` exist with layout `f`, the ADT has a layout `(size, align)`, the field lies
inside the container (`off + f.size ≤ size`), and its offset is aligned (`f.align ∣ off`). -/
theorem resolveAdtOffsetOf_bounds_and_align (spec : AdtLayoutSpec) (hWF : spec.WF)
    {v i off : Nat} (h : resolveAdtOffsetOf spec v i = some off) :
    ∃ fs f size align, variantFields spec v = some fs ∧ fs[i]? = some f ∧
      adtLayout? spec = some (size, align) ∧ off + f.size ≤ size ∧ f.align ∣ off := by
  have hAll := hWF.fieldAlignPow2
  cases hL : adtLayout? spec with
  | none => simp [resolveAdtOffsetOf, hL] at h
  | some lay =>
    obtain ⟨size, align⟩ := lay
    cases hShape : spec.shape with
    | struct fs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      rw [hShape] at hAll
      split at h
      · rename_i hV
        subst hV
        rcases structFieldOffset?_bounds spec.repr spec.rustOrderCanonical spec.reprAlign fs
            hAll hL' h with ⟨f, hF, hEnd, hDvd⟩
        exact ⟨fs, f, size, align, by simp [variantFields, hShape], hF, rfl, hEnd, hDvd⟩
      · nomatch h
    | union fs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      split at h
      · rename_i hCond
        rcases hCond with ⟨rfl, hLt⟩
        simp only [Option.some.injEq] at h
        subst h
        have hF : fs[i]? = some fs[i] := List.getElem?_eq_getElem hLt
        refine ⟨fs, fs[i], size, align, by simp [variantFields, hShape], hF, rfl, ?_,
          Nat.dvd_zero _⟩
        unfold unionLayout? at hL'
        cases fs with
        | nil => nomatch hL'
        | cons g gs =>
          simp only at hL'
          split at hL'
          · nomatch hL'
          · simp only [Option.some.injEq, Prod.mk.injEq] at hL'
            rcases hL' with ⟨rfl, rfl⟩
            have := le_maxSize_of_mem (g :: gs) _ (getElem?_mem hF)
            have := PlaceAndRvalue.alignUp_ge (maxSize (g :: gs))
              (maxAlign (spec.reprAlign.getD 1) (g :: gs))
            omega
      · nomatch h
    | taggedEnum tagSize vs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      rw [hShape] at hAll
      have hTag : IsPow2 tagSize := hWF.tagPow2 tagSize vs hShape
      have hVsPow : ∀ fs ∈ vs, ∀ f ∈ fs, IsPow2 f.align := fun fs hfs f hf =>
        hAll f (List.mem_flatten.mpr ⟨fs, hfs, hf⟩)
      unfold taggedFieldOffset? at h
      cases hV : vs[v]? with
      | none => rw [hV] at h; nomatch h
      | some fs =>
        rw [hV] at h
        simp only at h
        have hFsMem : fs ∈ vs := getElem?_mem hV
        have hVF : variantFields spec v = some fs := by simp [variantFields, hShape, hV]
        cases hRepr : spec.repr with
        | transparent => rw [hRepr] at h; nomatch h
        | rust =>
          rw [hRepr] at h hL'
          simp only [taggedLayout?, Option.some.injEq, Prod.mk.injEq] at hL'
          rcases hL' with ⟨rfl, rfl⟩
          rcases cOffset?_spec tagSize fs i off h with ⟨f, hF, hEnd, hDvd⟩
          refine ⟨fs, f, _, _, hVF, hF, rfl, ?_,
            hDvd (hVsPow fs hFsMem f (getElem?_mem hF)).pos⟩
          have h1 := PlaceAndRvalue.alignUp_ge (cEnd tagSize fs) (maxAlign tagSize fs)
          have h2 := le_maxList_of_mem
            (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd tagSize v) (maxAlign tagSize v)))
            (PlaceAndRvalue.alignUp (cEnd tagSize fs) (maxAlign tagSize fs))
            (List.mem_map.mpr ⟨fs, hFsMem, rfl⟩)
          have h3 := PlaceAndRvalue.alignUp_ge
            (maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd tagSize v) (maxAlign tagSize v))))
            (variantsAlign (max (spec.reprAlign.getD 1) tagSize) vs)
          omega
        | c =>
          rw [hRepr] at h hL'
          simp only [taggedLayout?, Option.some.injEq, Prod.mk.injEq] at hL'
          rcases hL' with ⟨rfl, rfl⟩
          cases hIn : cOffset? 0 fs i with
          | none => rw [hIn] at h; nomatch h
          | some inner =>
            rw [hIn] at h
            simp only [Option.map_some, Option.some.injEq] at h
            subst h
            rcases cOffset?_spec 0 fs i inner hIn with ⟨f, hF, hEnd, hDvd⟩
            have hFMem : f ∈ fs := getElem?_mem hF
            have hFPow := hVsPow fs hFsMem f hFMem
            have hPA : IsPow2 (payloadAlign vs) := variantsAlign_pow2 1 vs isPow2_one hVsPow
            refine ⟨fs, f, _, _, hVF, hF, rfl, ?_, ?_⟩
            · have h1 := PlaceAndRvalue.alignUp_ge (cEnd 0 fs) (maxAlign 1 fs)
              have h2 := le_maxList_of_mem
                (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v)))
                (PlaceAndRvalue.alignUp (cEnd 0 fs) (maxAlign 1 fs))
                (List.mem_map.mpr ⟨fs, hFsMem, rfl⟩)
              have h3 := PlaceAndRvalue.alignUp_ge
                (maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v))))
                (payloadAlign vs)
              have h4 := PlaceAndRvalue.alignUp_ge
                (payloadOffset tagSize vs + PlaceAndRvalue.alignUp
                  (maxList (vs.map (fun v => PlaceAndRvalue.alignUp (cEnd 0 v) (maxAlign 1 v))))
                  (payloadAlign vs))
                (max (max (spec.reprAlign.getD 1) tagSize) (payloadAlign vs))
              omega
            · apply Nat.dvd_add
              · -- `f.align ∣ payloadAlign vs ∣ payloadOffset tagSize vs`
                have hLe : f.align ≤ payloadAlign vs :=
                  le_variantsAlign_of_mem 1 vs fs f hFsMem hFMem
                exact Nat.dvd_trans (hFPow.dvd_of_le hPA hLe)
                  (alignUp_dvd tagSize (payloadAlign vs) hPA.pos)
              · exact hDvd hFPow.pos
    | univariantEnum present vs =>
      have hL' := hL
      simp only [adtLayout?, hShape] at hL'
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      rw [hShape] at hAll
      cases hV : vs[v]? with
      | none => rw [hV] at h; nomatch h
      | some fs =>
        rw [hV] at h
        simp only at h
        have hVF : variantFields spec v = some fs := by simp [variantFields, hShape, hV]
        split at h
        · rename_i hEq
          subst hEq
          rw [hV] at hL'
          simp only at hL'
          split at hL'
          · nomatch hL'
          · have hPow : ∀ f ∈ fs, IsPow2 f.align := fun f hf =>
              hAll f (mem_allFields_of_variant hV hf)
            rcases structFieldOffset?_bounds spec.repr spec.rustOrderCanonical spec.reprAlign
                fs hPow hL' h with ⟨f, hF, hEnd, hDvd⟩
            exact ⟨fs, f, size, align, hVF, hF, rfl, hEnd, hDvd⟩
        · rename_i hNe
          unfold absentFieldOffset? at h
          split at h
          · rename_i hLt
            simp only [Option.some.injEq] at h
            subst h
            have hF : fs[i]? = some fs[i] := List.getElem?_eq_getElem hLt
            have hZero := hWF.absentZeroSized present vs hShape v fs hV hNe fs[i]
              (getElem?_mem hF)
            exact ⟨fs, fs[i], size, align, hVF, hF, rfl, by omega, Nat.dvd_zero _⟩
          · nomatch h
    | noPresentEnum vs =>
      simp only [resolveAdtOffsetOf, hL, hShape] at h
      cases hV : vs[v]? with
      | none => rw [hV] at h; nomatch h
      | some fs =>
        rw [hV] at h
        simp only at h
        unfold absentFieldOffset? at h
        split at h
        · rename_i hLt
          simp only [Option.some.injEq] at h
          subst h
          have hF : fs[i]? = some fs[i] := List.getElem?_eq_getElem hLt
          have hZero := hWF.noPresentZeroSized vs hShape fs (getElem?_mem hV) fs[i]
            (getElem?_mem hF)
          exact ⟨fs, fs[i], size, align, by simp [variantFields, hShape, hV], hF, rfl,
            by omega, Nat.dvd_zero _⟩
        · nomatch h
    | unspecifiedEnum vs =>
      simp [resolveAdtOffsetOf, hL, hShape] at h

/-- **Union fields all sit at offset `0`.** -/
theorem resolveAdtOffsetOf_union_eq_zero {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .union fs) {v i off : Nat}
    (h : resolveAdtOffsetOf spec v i = some off) : off = 0 := by
  unfold resolveAdtOffsetOf at h
  cases hLay : adtLayout? spec with
  | none => rw [hLay] at h; nomatch h
  | some _ =>
    rw [hLay, hShape] at h
    simp only at h
    split at h
    · simp only [Option.some.injEq] at h
      exact h.symm
    · nomatch h

/-- **`#[repr(transparent)]` delegation**: the unique non-1-ZST field of a well-formed
transparent struct sits at offset `0`. -/
theorem resolveAdtOffsetOf_transparent_nonZst {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .transparent)
    {i : Nat} {f : FieldLayout} (hF : fs[i]? = some f) (hNZ : f.isOneZst = false)
    (hLay : (adtLayout? spec).isSome = true) :
    resolveAdtOffsetOf spec 0 i = some 0 := by
  unfold resolveAdtOffsetOf
  cases hL : adtLayout? spec with
  | none => rw [hL] at hLay; nomatch hLay
  | some _ =>
    simp only [hShape, ↓reduceIte, structFieldOffset?, hRepr, hF, hNZ, Bool.not_false]

/-- **`#[repr(C)]` struct offsets are strictly ordered**: an earlier field of a `#[repr(C)]`
struct ends at or before a later field's offset. -/
theorem resolveAdtOffsetOf_reprC_monotone {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c)
    {i j oi oj : Nat} (hLt : i < j)
    (hi : resolveAdtOffsetOf spec 0 i = some oi) (hj : resolveAdtOffsetOf spec 0 j = some oj) :
    ∃ fi, fs[i]? = some fi ∧ oi + fi.size ≤ oj := by
  unfold resolveAdtOffsetOf at hi hj
  cases hL : adtLayout? spec with
  | none => rw [hL] at hi; nomatch hi
  | some _ =>
    rw [hL, hShape] at hi hj
    simp only [↓reduceIte, structFieldOffset?, hRepr] at hi hj
    exact cOffset?_monotone 0 fs i j oi oj hLt hi hj

/-! ## Section 1c: Typed ADT `Discriminant` -/

/-- Discriminant-relevant facts of a typed ADT (`AdtDef` in `ir.rs`): whether it is an enum,
its per-variant discriminant bit patterns (`AdtDef::discriminants`) and inhabitedness, whether
a value stores a tag (`AdtDef::requires_tag_write`), whether that tag is stored apart from the
variant fields (`AdtDef::tag_survives_field_deinit`; false for niche-capable tagless enums),
and the constant variant of a tagless layout (`AdtDef::univariant_index`, `0` otherwise). -/
structure AdtDiscrSpec : Type where
  isEnum : Bool
  discriminants : List Nat
  variantInhabited : List Bool
  requiresTagWrite : Bool
  tagSurvivesFieldDeinit : Bool
  taglessVariant : Nat

/-- `PartialAggregate::tag_is_readable` (`A3`) for a typed shell of an ADT described by `spec`:
an ADT without a stored tag always has a readable variant, and otherwise the tag must have been
written by `SetDiscriminant` and be stored apart from the (possibly uninitialized) fields. -/
def tagIsReadable (spec : AdtDiscrSpec) (shell : PartialAggregate) : Bool :=
  !spec.requiresTagWrite || (shell.discriminantSet && spec.tagSurvivesFieldDeinit)

/-- `discriminant_value`: the discriminant bits of variant `v` of an enum (`none` for an
uninhabited/absent or out-of-range variant, `UninhabitedEnumVariant`), and `0` for variant `0`
of a struct or union (`rustc`'s `discriminant_ty` is `u8`). -/
def discriminantValue? (spec : AdtDiscrSpec) (v : Nat) : Option Nat :=
  if spec.isEnum then
    match spec.variantInhabited[v]?, spec.discriminants[v]? with
    | some true, some d => some d
    | _, _ => none
  else if v = 0 then some 0 else none

/-- The variant a shell is narrowed to (`0` for a tuple shell), exactly as `readFromPartialShell`
and `writeToFieldSlot` compute it. -/
def shellVariant (shell : PartialAggregate) : Nat :=
  match shell.isAdt with
  | true => shell.variantIdx
  | false => 0

/-- `Rvalue::Discriminant` on a typed ADT place holding `slot` (`eval_lowered_rvalue_in_state`
with `StatementEvalState::typed_enum_variant`), where `wf` is `check_value_well_formed`:
- a dead local faults (`DeadLocal`);
- an uninitialized place has a defined discriminant only when no tag is stored;
- an initialized value reports its variant's discriminant, except that a niche-capable enum
  (`B4`, whose tag may live in a field's niche) requires the whole value to be well formed;
- a partial shell reports its variant only when its tag is readable (`A3`). -/
def evalAdtDiscriminant (spec : AdtDiscrSpec) (wf : Value → Bool) :
    LocalSlotState → Option Nat
  | .dead => none
  | .uninit => if spec.requiresTagWrite then none else discriminantValue? spec spec.taglessVariant
  | .init (.aggregate v fields) =>
    if !spec.tagSurvivesFieldDeinit && !wf (.aggregate v fields) then none
    else discriminantValue? spec v
  | .init _ => none
  | .partialShell shell =>
    if tagIsReadable spec shell then discriminantValue? spec (shellVariant shell) else none

/-- **Absent/uninhabited variants have no discriminant (`B2`)**: reading the discriminant of an
enum value or shell narrowed to an uninhabited variant faults. -/
theorem evalAdtDiscriminant_uninhabited_variant_none (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hEnum : spec.isEnum = true) {v : Nat} (hUninh : spec.variantInhabited[v]? = some false) :
    (∀ fields, evalAdtDiscriminant spec wf (.init (.aggregate v fields)) = none) ∧
    (∀ shell, shellVariant shell = v → evalAdtDiscriminant spec wf (.partialShell shell) = none) := by
  have hVal : discriminantValue? spec v = none := by
    simp [discriminantValue?, hEnum, hUninh]
  refine ⟨fun fields => ?_, fun shell hV => ?_⟩
  · simp only [evalAdtDiscriminant]
    split <;> simp_all
  · simp only [evalAdtDiscriminant, hV]
    split <;> simp_all

/-- **Niche-capable shells have no readable tag (`A3`)**: for an enum whose tag may be
niche-encoded in a variant field (`requires_tag_write` but not `tag_survives_field_deinit`),
`Discriminant` on any incomplete shell faults, even after `SetDiscriminant`. -/
theorem evalAdtDiscriminant_niche_shell_none (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hTag : spec.requiresTagWrite = true) (hNiche : spec.tagSurvivesFieldDeinit = false)
    (shell : PartialAggregate) :
    evalAdtDiscriminant spec wf (.partialShell shell) = none := by
  simp [evalAdtDiscriminant, tagIsReadable, hTag, hNiche]

/-- **Tags stored apart are readable on shells**: after `SetDiscriminant` has written a tag
stored apart from the fields, `Discriminant` on the incomplete shell is the variant's
discriminant. -/
theorem evalAdtDiscriminant_tag_apart_shell (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hApart : spec.tagSurvivesFieldDeinit = true) (shell : PartialAggregate)
    (hSet : shell.discriminantSet = true) :
    evalAdtDiscriminant spec wf (.partialShell shell) = discriminantValue? spec (shellVariant shell) := by
  simp [evalAdtDiscriminant, tagIsReadable, hApart, hSet]

/-- **Niche-capable values must be well formed (`B4`)**: an initialized niche-capable enum value
that is not well formed (e.g. `Some(NonZeroU32(0))`, whose bytes MiniRust decodes as `None`)
has no discriminant. -/
theorem evalAdtDiscriminant_niche_init_ill_formed_none (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hNiche : spec.tagSurvivesFieldDeinit = false) {v : Nat} {fields : List Value}
    (hBad : wf (.aggregate v fields) = false) :
    evalAdtDiscriminant spec wf (.init (.aggregate v fields)) = none := by
  simp [evalAdtDiscriminant, hNiche, hBad]

/-- An uninitialized enum that stores a tag has no discriminant (`UninitializedLocal`), while a
tagless one reports its constant discriminant without reading memory. -/
theorem evalAdtDiscriminant_uninit (spec : AdtDiscrSpec) (wf : Value → Bool) :
    evalAdtDiscriminant spec wf .uninit =
      if spec.requiresTagWrite then none else discriminantValue? spec spec.taglessVariant := rfl

/-- **Agreement with Trusted's `evalPlaceDiscriminant`**: whenever `evalAdtDiscriminant`
succeeds on an initialized aggregate, Trusted's `Rvalue.discriminant` evaluation of the same
value (with no layout information for the place) succeeds with the variant index as an 8-byte
scalar, and Anneal's result is that variant's declared discriminant (equal to the variant index
for the default sequential discriminants `0, 1, 2, …`). -/
theorem evalAdtDiscriminant_init_agrees_trusted (spec : AdtDiscrSpec) (wf : Value → Bool)
    (hEnum : spec.isEnum = true) {v : Nat} {fields : List Value} {d : Nat}
    (h : evalAdtDiscriminant spec wf (.init (.aggregate v fields)) = some d)
    (locals' : List LocalSlot) (mem : Memory) (place : Place) (localDecls : List LocalDecl)
    (layouts : LayoutTable) (hTy : placeTy localDecls layouts place = none) :
    evalPlaceDiscriminant (.aggregate v fields) locals' mem place localDecls layouts =
        .ok (.scalar ⟨v, 8⟩) locals' mem ∧
      spec.discriminants[v]? = some d ∧
      (spec.discriminants = List.range spec.discriminants.length → d = v) := by
  have hD : spec.discriminants[v]? = some d := by
    simp only [evalAdtDiscriminant] at h
    split at h
    · nomatch h
    · simp only [discriminantValue?, hEnum, ↓reduceIte] at h
      split at h
      · rename_i d' _ hD
        simp only [Option.some.injEq] at h
        subst h
        exact hD
      · nomatch h
  refine ⟨by simp [evalPlaceDiscriminant, hTy], hD, fun hSeq => ?_⟩
  have hLt : v < spec.discriminants.length := (List.getElem?_eq_some_iff.mp hD).1
  rw [hSeq, List.getElem?_range (by simpa using hLt)] at hD
  simpa using hD.symm

/-! ## Section 2: Projected `Deinit`, `Retag`, `CopyNonOverlapping`, and Pointer-Like Rvalues -/

/-! ### Section 2a: The projected `Deinit` evaluator -/

/-- Every field slot of a shell is uninitialized. -/
def allFieldsUninit : List FieldSlot → Bool
  | [] => true
  | .uninit :: rest => allFieldsUninit rest
  | .init _ :: _ => false
  | .nested _ _ _ _ :: _ => false

/-- `normalize_slot` on a shell: a complete shell is promoted to `.init` (`try_into_mir_value`);
an empty shell — no initialized field and no tag that matters (`PartialAggregate::is_empty`,
where for the untyped shells of this model only an enum shell's written tag matters) —
collapses to `.uninit`; any other shell is kept. -/
def normalizeShell (shell : PartialAggregate) : FieldSlot :=
  match shell.tryIntoValue? with
  | some v => .init v
  | none =>
    match (!shell.isAdt || !shell.discriminantSet) && allFieldsUninit shell.fields with
    | true => .uninit
    | false => shell.toFieldSlot

/-- `explode_init_slot` on an initialized aggregate: the equivalent complete shell (every field
initialized and the tag counted as written), which `normalizeShell` turns back into the value. -/
def explodeAggregate (variantIdx : Nat) (vals : List Value) : PartialAggregate :=
  ⟨variantIdx, true, true, vals.map .init⟩

/-- `validate_projection_tail` for a `Deinit` below an uninitialized part (where it changes
nothing), over this untyped model: no `Deref` (`UnsupportedPlaceProjection`), every `Downcast`
immediately followed by a `Field`, no `OpaqueCast`/`UnwrapUnsafeBinder`, and every `Index`
operand an initialized scalar local (the statement's pre-read index cache). -/
def deinitTailOk (locals : List LocalSlot) : List ProjectionElem → Bool
  | [] => true
  | .field _ _ :: rest => deinitTailOk locals rest
  | .downcast _ _ :: .field _ _ :: rest => deinitTailOk locals rest
  | .index i :: rest =>
    match get? locals i with
    | some (.init (.scalar _)) => deinitTailOk locals rest
    | _ => false
  | .constantIndex _ _ _ :: rest => deinitTailOk locals rest
  | .subslice _ _ _ :: rest => deinitTailOk locals rest
  | _ :: _ => false

/-- One `Field` step of `deinit_in_slot` on the (possibly just exploded) shell `shell`, where
`downcast` is the pending `Downcast` variant: the shell must be narrowed to the expected variant
(`InactiveVariantProjection`), the field must exist (`FieldOutOfBounds`), the child is
deinitialized by `child`, and below a `Downcast` a tag that does not survive field
deinitialization (`AdtDef::tag_survives_field_deinit`, `A3`) is forgotten
(`discriminant_set = false`). The result is normalized (`normalize_slot`). -/
def deinitShellStep (tagSurvives : Bool) (shell : PartialAggregate) (downcast : Option Nat)
    (idx : Nat) (child : FieldSlot → Option FieldSlot) : Option FieldSlot :=
  if shellVariant shell = downcast.getD 0 then
    match shell.fields[idx]? with
    | none => none
    | some c =>
      match child c with
      | none => none
      | some c' =>
        some (normalizeShell
          { shell with
            discriminantSet := shell.discriminantSet && (downcast.isNone || tagSurvives)
            fields := shell.fields.set idx c' })
  else none

/-- `deinit_in_slot`: writes "uninitialized" over the part `proj` of `slot`.
- `proj = []` makes the slot `.uninit`;
- below an uninitialized part nothing changes, but the place must be well formed
  (`deinitTailOk`);
- an initialized aggregate is exploded into a complete shell (`explode_init_slot`) and a
  `Field` (variant `0`) or `Downcast(v)` + `Field` step recurses into the field;
- a shell recurses the same way (`InactiveVariantProjection` on a variant mismatch);
- `Deref`, array projections on values or shells, a `Field` of a non-aggregate, and a
  `Downcast` not followed by a `Field` fail (`none`).
`tagSurvives` is `AdtDef::tag_survives_field_deinit` of the enum the place's `Downcast`s
narrow. -/
def deinitFieldSlot (tagSurvives : Bool) (locals : List LocalSlot) :
    FieldSlot → List ProjectionElem → Option FieldSlot
  | _, [] => some .uninit
  | .uninit, p :: rest => if deinitTailOk locals (p :: rest) then some .uninit else none
  | .init (.aggregate var vals), .field idx _ :: rest =>
    deinitShellStep tagSurvives (explodeAggregate var vals) none idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | .init (.aggregate var vals), .downcast _ v :: .field idx _ :: rest =>
    deinitShellStep tagSurvives (explodeAggregate var vals) (some v) idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | .nested var adt disc fs, .field idx _ :: rest =>
    deinitShellStep tagSurvives ⟨var, adt, disc, fs⟩ none idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    deinitShellStep tagSurvives ⟨var, adt, disc, fs⟩ (some v) idx
      (fun c => deinitFieldSlot tagSurvives locals c rest)
  | _, _ :: _ => none

/-- The `FieldSlot` view of a live local (`take_root_slot`). -/
def slotStateToFieldSlot : LocalSlotState → FieldSlot
  | .dead => .uninit
  | .uninit => .uninit
  | .partialShell shell => shell.toFieldSlot
  | .init v => .init v

/-- `StatementEvalState::deinit_place`: a dead (or missing) local faults (`DeadLocal`); the
bare local becomes `.uninit`; a projected place is deinitialized in the root slot by
`deinitFieldSlot` and the normalized slot is written back (`root_slot_state`). -/
def evalDeinitPlace (tagSurvives : Bool) (slots : List LocalSlotState) (place : Place) :
    Option (List LocalSlotState) :=
  match slots[place.local_]? with
  | none => none
  | some .dead => none
  | some st =>
    match place.projection with
    | [] => some (slots.set place.local_ .uninit)
    | p :: rest =>
      match deinitFieldSlot tagSurvives (slotsToTrustedLocals slots)
          (slotStateToFieldSlot st) (p :: rest) with
      | none => none
      | some slot' => some (slots.set place.local_ (fieldSlotToLocalSlotState slot'))

/-- Reading the part `q` of a field slot (`read_place` below the root): an uninitialized part
faults, an initialized one is read by `evalValueProjRead`, and a shell by
`readFromPartialShell`. -/
def readFieldSlot (locals : List LocalSlot) : FieldSlot → List ProjectionElem → ProjReadResult
  | .uninit, _ => .ub
  | .init v, q => evalValueProjRead locals v q
  | .nested var adt disc fs, q => readFromPartialShell locals ⟨var, adt, disc, fs⟩ q

/-- Case analysis on a `Nat.beq` test, as a decidable `if`. -/
theorem beq_cases (a b : Nat) : (Nat.beq a b = true ∧ a = b) ∨ (Nat.beq a b = false ∧ a ≠ b) := by
  cases hB : Nat.beq a b with
  | true => exact Or.inl ⟨rfl, Nat.eq_of_beq_eq_true hB⟩
  | false => exact Or.inr ⟨rfl, Nat.ne_of_beq_eq_false hB⟩

/-- `readFromPartialShell` on a `Field` step dispatches to the field's slot. -/
theorem readFromPartialShell_field (locals : List LocalSlot) (shell : PartialAggregate)
    (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readFromPartialShell locals shell (.field idx ty :: rest) =
      if shellVariant shell = 0 then
        match shell.fields[idx]? with
        | some c => readFieldSlot locals c rest
        | none => .ub
      else .ub := by
  obtain ⟨var, adt, disc, fs⟩ := shell
  have hFs : (match get? fs idx with
      | some (.init fieldVal) => evalValueProjRead locals fieldVal rest
      | some (.nested cVar cAdt cDisc cFields) =>
        readFromPartialShell locals ⟨cVar, cAdt, cDisc, cFields⟩ rest
      | some .uninit => ProjReadResult.ub
      | none => ProjReadResult.ub) =
      (match fs[idx]? with
      | some c => readFieldSlot locals c rest
      | none => .ub) := by
    rw [get?_eq_getElem?]
    cases fs[idx]? with
    | none => rfl
    | some c => cases c <;> rfl
  cases adt with
  | true =>
    rcases beq_cases var 0 with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · subst hE
      simp only [readFromPartialShell, shellVariant, show Nat.beq 0 0 = true from rfl, ↓reduceIte]
      exact hFs
    · simp only [readFromPartialShell, shellVariant, hB, hE, ↓reduceIte]
  | false =>
    simp only [readFromPartialShell, shellVariant, show Nat.beq 0 0 = true from rfl, ↓reduceIte]
    exact hFs

/-- `readFromPartialShell` on a `Downcast(v)` + `Field` step dispatches to the field's slot of
a shell narrowed to `v`. -/
theorem readFromPartialShell_downcast_field (locals : List LocalSlot) (shell : PartialAggregate)
    (n : Option String) (v idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    readFromPartialShell locals shell (.downcast n v :: .field idx ty :: rest) =
      if shellVariant shell = v then
        match shell.fields[idx]? with
        | some c => readFieldSlot locals c rest
        | none => .ub
      else .ub := by
  obtain ⟨var, adt, disc, fs⟩ := shell
  have hFs : (match get? fs idx with
      | some (.init fieldVal) => evalValueProjRead locals fieldVal rest
      | some (.nested cVar cAdt cDisc cFields) =>
        readFromPartialShell locals ⟨cVar, cAdt, cDisc, cFields⟩ rest
      | some .uninit => ProjReadResult.ub
      | none => ProjReadResult.ub) =
      (match fs[idx]? with
      | some c => readFieldSlot locals c rest
      | none => .ub) := by
    rw [get?_eq_getElem?]
    cases fs[idx]? with
    | none => rfl
    | some c => cases c <;> rfl
  cases adt with
  | true =>
    rcases beq_cases var v with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · subst hE
      simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, Nat.beq_refl,
        ↓reduceIte]
      exact hFs
    · simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, hB, hE,
        ↓reduceIte]
  | false =>
    rcases beq_cases 0 v with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · subst hE
      simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, Nat.beq_refl,
        ↓reduceIte]
      exact hFs
    · simp only [readFromPartialShell, shellVariant, isFieldHead, Bool.true_and, hB, hE,
        ↓reduceIte]

/-- `evalValueProjRead` on a `Field` step of an aggregate reads the field. -/
theorem evalValueProjRead_aggregate_field (locals : List LocalSlot) (var : Nat)
    (vals : List Value) (idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    evalValueProjRead locals (.aggregate var vals) (.field idx ty :: rest) =
      match vals[idx]? with
      | some fv => evalValueProjRead locals fv rest
      | none => .ub := by
  simp only [evalValueProjRead, ← get?_eq_getElem?]
  cases get? vals idx <;> rfl

/-- `evalValueProjRead` on a `Downcast(v)` + `Field` step of an aggregate of variant `var`
reads the field when `var = v`. -/
theorem evalValueProjRead_aggregate_downcast_field (locals : List LocalSlot) (var : Nat)
    (vals : List Value) (n : Option String) (v idx : Nat) (ty : Ty) (rest : List ProjectionElem) :
    evalValueProjRead locals (.aggregate var vals) (.downcast n v :: .field idx ty :: rest) =
      if var = v then
        match vals[idx]? with
        | some fv => evalValueProjRead locals fv rest
        | none => .ub
      else .ub := by
  rcases beq_cases var v with ⟨hB, hE⟩ | ⟨hB, hE⟩
  · simp only [evalValueProjRead, isFieldHead, Bool.true_and]
    rw [hB]
    simp only [hE, ↓reduceIte, ← get?_eq_getElem?]
    cases get? vals idx <;> rfl
  · simp only [evalValueProjRead, isFieldHead, Bool.true_and]
    rw [hB]
    simp only [hE, ↓reduceIte]

/-- `q` is a prefix or an extension of `p`: the paths a `Deinit` at `p` makes unreadable. -/
def PathComparable (p q : List ProjectionElem) : Prop :=
  (∃ s, q = p ++ s) ∨ (∃ s, p = q ++ s)

/-- Comparable non-empty paths agree on their first element. -/
theorem PathComparable.cons {a b : ProjectionElem} {p q : List ProjectionElem}
    (h : PathComparable (a :: p) (b :: q)) : b = a ∧ PathComparable p q := by
  rcases h with ⟨s, hs⟩ | ⟨s, hs⟩
  · simp only [List.cons_append, List.cons.injEq] at hs
    exact ⟨hs.1, Or.inl ⟨s, hs.2⟩⟩
  · simp only [List.cons_append, List.cons.injEq] at hs
    exact ⟨hs.1.symm, Or.inr ⟨s, hs.2⟩⟩

/-- The shape a `Deinit` at `proj` leaves behind: the slot is uninitialized along `proj`, i.e.
every node on the path is a shell narrowed to the path's variant, down to an uninitialized
part (which may also be an uninitialized ancestor). -/
def UninitAt : FieldSlot → List ProjectionElem → Prop
  | .uninit, _ => True
  | .nested var adt disc fs, .field idx _ :: rest =>
    shellVariant ⟨var, adt, disc, fs⟩ = 0 ∧ ∃ c, fs[idx]? = some c ∧ UninitAt c rest
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    shellVariant ⟨var, adt, disc, fs⟩ = v ∧ ∃ c, fs[idx]? = some c ∧ UninitAt c rest
  | _, _ => False

/-- An initialized slot is not uninitialized anywhere. -/
theorem UninitAt.not_init {v : Value} {p : List ProjectionElem} : ¬ UninitAt (.init v) p := by
  intro h
  cases p <;> simp only [UninitAt] at h

/-- A shell with a non-initialized field does not promote. -/
theorem tryIntoValue?_eq_none_of_getElem? {shell : PartialAggregate} {idx : Nat} {c : FieldSlot}
    (hc : shell.fields[idx]? = some c) (hNI : ∀ v, c ≠ .init v) : shell.tryIntoValue? = none := by
  cases h : shell.tryIntoValue? with
  | none => rfl
  | some out =>
    obtain ⟨_, vals, hF, _⟩ := (tryIntoValue?_eq_some_iff shell out).mp h
    rw [hF, List.getElem?_map] at hc
    cases hv : vals[idx]? with
    | none => rw [hv] at hc; nomatch hc
    | some w =>
      rw [hv] at hc
      simp only [Option.map_some, Option.some.injEq] at hc
      exact absurd hc.symm (hNI w)

/-- A shell that does not promote normalizes to `.uninit` (when empty) or stays a shell. -/
theorem normalizeShell_of_tryIntoValue?_none {shell : PartialAggregate}
    (h : shell.tryIntoValue? = none) :
    (normalizeShell shell = .uninit ∧
        ((!shell.isAdt || !shell.discriminantSet) && allFieldsUninit shell.fields) = true) ∨
      normalizeShell shell = shell.toFieldSlot := by
  unfold normalizeShell
  rw [h]
  cases hc : ((!shell.isAdt || !shell.discriminantSet) && allFieldsUninit shell.fields) with
  | true => exact Or.inl ⟨rfl, rfl⟩
  | false => exact Or.inr rfl

/-- Every field of an all-uninitialized field list is uninitialized. -/
theorem allFieldsUninit_getElem? : ∀ {fs : List FieldSlot} {i : Nat} {c : FieldSlot},
    allFieldsUninit fs = true → fs[i]? = some c → c = .uninit
  | [], _, _, _, h => by simp at h
  | .uninit :: _, 0, _, _, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    exact h.symm
  | .uninit :: rest, i + 1, _, hA, h =>
    allFieldsUninit_getElem? (fs := rest) hA (by simpa using h)
  | .init _ :: _, _, _, hA, _ => by simp [allFieldsUninit] at hA
  | .nested _ _ _ _ :: _, _, _, hA, _ => by simp [allFieldsUninit] at hA

/-- Inversion of a successful `deinitShellStep`. -/
theorem deinitShellStep_eq_some {ts : Bool} {shell : PartialAggregate} {dc : Option Nat}
    {idx : Nat} {child : FieldSlot → Option FieldSlot} {r : FieldSlot}
    (h : deinitShellStep ts shell dc idx child = some r) :
    shellVariant shell = dc.getD 0 ∧ ∃ c c', shell.fields[idx]? = some c ∧ child c = some c' ∧
      r = normalizeShell { shell with
        discriminantSet := shell.discriminantSet && (dc.isNone || ts)
        fields := shell.fields.set idx c' } := by
  unfold deinitShellStep at h
  split at h
  · rename_i hV
    split at h
    · nomatch h
    · rename_i c hc
      split at h
      · nomatch h
      · rename_i c' hcc
        exact ⟨hV, c, c', hc, hcc, (Option.some.inj h).symm⟩
  · nomatch h

/-- After a shell step whose child is uninitialized along `rest`, the normalized shell is
`.uninit` or the updated shell holding that child. -/
theorem normalizeShell_step_cases {shell : PartialAggregate} {idx : Nat} {c c' : FieldSlot}
    {disc' : Bool} {rest : List ProjectionElem} (hc : shell.fields[idx]? = some c)
    (hU : UninitAt c' rest) :
    normalizeShell { shell with discriminantSet := disc', fields := shell.fields.set idx c' } =
        .uninit ∨
      (normalizeShell { shell with discriminantSet := disc', fields := shell.fields.set idx c' } =
          .nested shell.variantIdx shell.isAdt disc' (shell.fields.set idx c') ∧
        (shell.fields.set idx c')[idx]? = some c') := by
  have hLt : idx < shell.fields.length := (List.getElem?_eq_some_iff.mp hc).1
  have hGet : (shell.fields.set idx c')[idx]? = some c' := by
    simp [List.getElem?_set_self hLt]
  have hNone : ({ shell with discriminantSet := disc', fields := shell.fields.set idx c' } :
      PartialAggregate).tryIntoValue? = none :=
    tryIntoValue?_eq_none_of_getElem? hGet (fun v hv => UninitAt.not_init (hv ▸ hU))
  rcases normalizeShell_of_tryIntoValue?_none hNone with ⟨h1, _⟩ | h2
  · exact Or.inl h1
  · exact Or.inr ⟨h2, hGet⟩

/-- **`Deinit` leaves its place uninitialized**: a successful `deinitFieldSlot` at `proj`
produces a slot that is uninitialized along `proj` (`UninitAt`). -/
theorem deinitFieldSlot_uninitAt (ts : Bool) (locals : List LocalSlot) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts locals slot p = some slot') : UninitAt slot' p := by
  fun_induction deinitFieldSlot ts locals slot p generalizing slot' with
  | case1 => cases h; trivial
  | case2 => cases h; trivial
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case5 var vals n v idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case6 var adt disc fs idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case7 var adt disc fs n v idx ty rest ih =>
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hU := ih c c' hcc
    rcases normalizeShell_step_cases hc hU with h1 | ⟨h2, hGet⟩
    · rw [h1]; trivial
    · rw [h2]; simp only [UninitAt]; exact ⟨hV, c', hGet, hU⟩
  | case8 => nomatch h

/-- A shell that is uninitialized along a path does not promote to a value. -/
theorem UninitAt.nested_tryIntoValue?_none {var : Nat} {adt disc : Bool} {fs : List FieldSlot}
    {p : List ProjectionElem} (h : UninitAt (.nested var adt disc fs) p) :
    (⟨var, adt, disc, fs⟩ : PartialAggregate).tryIntoValue? = none := by
  rcases p with _ | ⟨a, rest⟩
  · simp only [UninitAt] at h
  · cases a
    case field idx ty =>
      simp only [UninitAt] at h
      obtain ⟨_, c, hc, hU⟩ := h
      exact tryIntoValue?_eq_none_of_getElem? (shell := ⟨var, adt, disc, fs⟩) hc
        (fun v hv => UninitAt.not_init (hv ▸ hU))
    case downcast n v =>
      rcases rest with _ | ⟨b, rest⟩
      · simp only [UninitAt] at h
      · cases b
        case field idx ty =>
          simp only [UninitAt] at h
          obtain ⟨_, c, hc, hU⟩ := h
          exact tryIntoValue?_eq_none_of_getElem? (shell := ⟨var, adt, disc, fs⟩) hc
            (fun v hv => UninitAt.not_init (hv ▸ hU))
        all_goals simp only [UninitAt] at h
    all_goals simp only [UninitAt] at h

/-- Fuel form of `readFieldSlot_eq_ub_of_uninitAt` (induction on the path length). -/
theorem readFieldSlot_eq_ub_of_uninitAt_aux (locals : List LocalSlot) :
    ∀ (n : Nat) (p : List ProjectionElem), p.length ≤ n → ∀ (slot : FieldSlot)
      (q : List ProjectionElem), UninitAt slot p → PathComparable p q →
      readFieldSlot locals slot q = .ub := by
  intro n
  induction n with
  | zero =>
    intro p hLen slot q hU _
    have hp : p = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
    subst hp
    cases slot with
    | uninit => rfl
    | init v => exact absurd hU UninitAt.not_init
    | nested var adt disc fs => simp only [UninitAt] at hU
  | succ n ih =>
    intro p hLen slot q hU hq
    cases slot with
    | uninit => rfl
    | init v => exact absurd hU UninitAt.not_init
    | nested var adt disc fs =>
      have hNone := UninitAt.nested_tryIntoValue?_none hU
      rcases p with _ | ⟨a, rest⟩
      · simp only [UninitAt] at hU
      · simp only [List.length_cons] at hLen
        cases a
        case field idx ty =>
          simp only [UninitAt] at hU
          obtain ⟨hV, c, hc, hUc⟩ := hU
          rcases q with _ | ⟨b, q'⟩
          · simp only [readFieldSlot, readFromPartialShell, hNone]
          · obtain ⟨rfl, hq'⟩ := hq.cons
            simp only [readFieldSlot, readFromPartialShell_field, hV, ↓reduceIte, hc]
            exact ih rest (by omega) c q' hUc hq'
        case downcast nm v =>
          rcases rest with _ | ⟨b, rest⟩
          · simp only [UninitAt] at hU
          · simp only [List.length_cons] at hLen
            cases b
            case field idx ty =>
              simp only [UninitAt] at hU
              obtain ⟨hV, c, hc, hUc⟩ := hU
              rcases q with _ | ⟨b1, q'⟩
              · simp only [readFieldSlot, readFromPartialShell, hNone]
              · obtain ⟨rfl, hq1⟩ := hq.cons
                rcases q' with _ | ⟨b2, q''⟩
                · simp only [readFieldSlot, readFromPartialShell, isFieldHead, Bool.false_and]
                · obtain ⟨rfl, hq2⟩ := hq1.cons
                  simp only [readFieldSlot, readFromPartialShell_downcast_field, hV, ↓reduceIte,
                    hc]
                  exact ih rest (by omega) c q'' hUc hq2
            all_goals simp only [UninitAt] at hU
        all_goals simp only [UninitAt] at hU

/-- **Reads along a deinitialized path fault**: if `slot` is uninitialized along `p`, reading
any prefix or extension of `p` faults with `.ub`. -/
theorem readFieldSlot_eq_ub_of_uninitAt (locals : List LocalSlot) (p : List ProjectionElem)
    (slot : FieldSlot) (q : List ProjectionElem) (hU : UninitAt slot p)
    (hq : PathComparable p q) : readFieldSlot locals slot q = .ub :=
  readFieldSlot_eq_ub_of_uninitAt_aux locals p.length p (Nat.le_refl _) slot q hU hq

/-- A slot left by `Deinit` round-trips through the root-slot conversions. -/
theorem UninitAt.roundtrip {slot : FieldSlot} {p : List ProjectionElem} (h : UninitAt slot p) :
    slotStateToFieldSlot (fieldSlotToLocalSlotState slot) = slot ∧
      fieldSlotToLocalSlotState slot ≠ .dead := by
  cases slot with
  | uninit => exact ⟨rfl, by intro h; cases h⟩
  | init v => exact absurd h UninitAt.not_init
  | nested var adt disc fs =>
    have hN := UninitAt.nested_tryIntoValue?_none h
    simp only [fieldSlotToLocalSlotState, hN]
    exact ⟨rfl, by intro h; cases h⟩

/-- `readPlaceState` of a live local is `readFieldSlot` of its root slot (for a place without
`Deref`). -/
theorem readPlaceState_eq_readFieldSlot {slots : List LocalSlotState} {loc : Local}
    {st : LocalSlotState} (hSt : slots[loc]? = some st) (hLive : st ≠ .dead)
    (q : List ProjectionElem) (hNoDeref : projectionHasDeref q = false) :
    readPlaceState slots ⟨loc, q⟩ =
      readFieldSlot (slotsToTrustedLocals slots) (slotStateToFieldSlot st) q := by
  unfold readPlaceState
  simp only [hNoDeref, get?_eq_getElem?, hSt]
  cases st with
  | dead => exact absurd rfl hLive
  | uninit => rfl
  | init v => rfl
  | partialShell shell => rfl

/-- `deinitFieldSlot` at the empty path always yields `.uninit`. -/
theorem deinitFieldSlot_nil (ts : Bool) (locals : List LocalSlot) (slot : FieldSlot) :
    deinitFieldSlot ts locals slot [] = some .uninit := by
  cases slot <;> rfl

/-- Inversion of a successful `evalDeinitPlace`: the local is live and its root slot is
replaced by the result of `deinitFieldSlot` (the bare-local case is the empty path). -/
theorem evalDeinitPlace_eq_some {ts : Bool} {slots slots' : List LocalSlotState} {place : Place}
    (h : evalDeinitPlace ts slots place = some slots') :
    ∃ st, slots[place.local_]? = some st ∧ st ≠ .dead ∧
      ∃ slot', deinitFieldSlot ts (slotsToTrustedLocals slots) (slotStateToFieldSlot st)
          place.projection = some slot' ∧
        slots' = slots.set place.local_ (fieldSlotToLocalSlotState slot') := by
  unfold evalDeinitPlace at h
  split at h
  · nomatch h
  · nomatch h
  · rename_i st hNotDead hSt
    refine ⟨st, hSt, fun hD => hNotDead hD, ?_⟩
    split at h
    · rename_i hP
      refine ⟨.uninit, by rw [hP]; exact deinitFieldSlot_nil _ _ _, ?_⟩
      exact (Option.some.inj h).symm
    · rename_i p rest hP
      split at h
      · nomatch h
      · rename_i slot' hD
        refine ⟨slot', by rw [hP]; exact hD, (Option.some.inj h).symm⟩

/-- **Get-Deinit (`evalDeinitPlace_read_same_ub`)**: after a successful `Deinit` of `place`,
reading any prefix of `place` (including the whole root local `[]`) or any extension
`place.projection ++ suffix` (without `Deref`) faults with `.ub`. -/
theorem evalDeinitPlace_read_same_ub {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') {q : List ProjectionElem}
    (hq : PathComparable place.projection q) (hNoDeref : projectionHasDeref q = false) :
    readPlaceState slots' ⟨place.local_, q⟩ = .ub := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  obtain ⟨hRound, hNotDead⟩ := UninitAt.roundtrip hU
  have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
  have hGet : (slots.set place.local_ (fieldSlotToLocalSlotState slot'))[place.local_]? =
      some (fieldSlotToLocalSlotState slot') := by
    simp [List.getElem?_set_self hLt]
  rw [readPlaceState_eq_readFieldSlot hGet hNotDead q hNoDeref, hRound]
  exact readFieldSlot_eq_ub_of_uninitAt _ _ _ _ hU hq

/-- Get-Deinit, whole root local: after deinitializing any part of a local, the local as a
whole is unreadable (`tryIntoValue? = none` for its shell). -/
theorem evalDeinitPlace_read_root_ub {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') :
    readPlaceState slots' ⟨place.local_, []⟩ = .ub :=
  evalDeinitPlace_read_same_ub h (Or.inr ⟨place.projection, rfl⟩) rfl

/-- Get-Deinit, extensions: after `Deinit` of `place`, every `Deref`-free extension
`place.projection ++ suffix` is unreadable. -/
theorem evalDeinitPlace_read_extension_ub {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots')
    (suffix : List ProjectionElem)
    (hNoDeref : projectionHasDeref (place.projection ++ suffix) = false) :
    readPlaceState slots' ⟨place.local_, place.projection ++ suffix⟩ = .ub :=
  evalDeinitPlace_read_same_ub h (Or.inl ⟨suffix, rfl⟩) hNoDeref

/-! ### Section 2b: Disjoint-sibling and distinct-local frames of `Deinit` -/

/-- Reading field `g` of variant `k` of a shell: the common core of `readFromPartialShell` on
`Field` (`k = 0`) and `Downcast(k)` + `Field` steps. -/
def shellFieldRead (locals : List LocalSlot) (sh : PartialAggregate) (k g : Nat)
    (q : List ProjectionElem) : ProjReadResult :=
  if shellVariant sh = k then
    match sh.fields[g]? with
    | some c => readFieldSlot locals c q
    | none => .ub
  else .ub

/-- Every field read of an all-uninitialized shell faults. -/
theorem shellFieldRead_of_allFieldsUninit {locals : List LocalSlot} {sh : PartialAggregate}
    {k g : Nat} {q : List ProjectionElem} (h : allFieldsUninit sh.fields = true) :
    shellFieldRead locals sh k g q = .ub := by
  unfold shellFieldRead
  split
  · cases hg : sh.fields[g]? with
    | none => rfl
    | some c =>
      obtain rfl := allFieldsUninit_getElem? h hg
      rfl
  · rfl

/-- Field reads of a nested shell slot. -/
theorem readFieldSlot_nested_field (locals : List LocalSlot) (var : Nat) (adt disc : Bool)
    (fs : List FieldSlot) (g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (.nested var adt disc fs) (.field g t :: q) =
      shellFieldRead locals ⟨var, adt, disc, fs⟩ 0 g q := by
  simp only [readFieldSlot, readFromPartialShell_field, shellFieldRead]

/-- `Downcast(v)` + `Field` reads of a nested shell slot. -/
theorem readFieldSlot_nested_downcast_field (locals : List LocalSlot) (var : Nat)
    (adt disc : Bool) (fs : List FieldSlot) (n : Option String) (v g : Nat) (t : Ty)
    (q : List ProjectionElem) :
    readFieldSlot locals (.nested var adt disc fs) (.downcast n v :: .field g t :: q) =
      shellFieldRead locals ⟨var, adt, disc, fs⟩ v g q := by
  simp only [readFieldSlot, readFromPartialShell_downcast_field, shellFieldRead]

/-- Field reads of an initialized variant-`0` aggregate are field reads of its exploded shell. -/
theorem readFieldSlot_init_field (locals : List LocalSlot) {var : Nat} (vals : List Value)
    (hV : var = 0) (g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (.init (.aggregate var vals)) (.field g t :: q) =
      shellFieldRead locals (explodeAggregate var vals) 0 g q := by
  subst hV
  simp only [readFieldSlot, evalValueProjRead_aggregate_field, shellFieldRead, explodeAggregate,
    shellVariant, ↓reduceIte, List.getElem?_map]
  cases vals[g]? <;> rfl

/-- `Downcast(v)` + `Field` reads of an initialized aggregate are reads of its exploded shell. -/
theorem readFieldSlot_init_downcast_field (locals : List LocalSlot) (var : Nat)
    (vals : List Value) (n : Option String) (v g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (.init (.aggregate var vals)) (.downcast n v :: .field g t :: q) =
      shellFieldRead locals (explodeAggregate var vals) v g q := by
  simp only [readFieldSlot, evalValueProjRead_aggregate_downcast_field, shellFieldRead,
    explodeAggregate, shellVariant, List.getElem?_map]
  by_cases hv : var = v
  · simp only [hv, ↓reduceIte]
    cases vals[g]? <;> rfl
  · simp only [hv, ↓reduceIte]

/-- Field reads of a normalized, non-promoting shell are field reads of the shell (an empty
shell collapses to `.uninit`, whose reads fault like the all-uninitialized shell's). -/
theorem readFieldSlot_normalizeShell_field {locals : List LocalSlot} {sh : PartialAggregate}
    (hN : sh.tryIntoValue? = none) (g : Nat) (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (normalizeShell sh) (.field g t :: q) = shellFieldRead locals sh 0 g q := by
  rcases normalizeShell_of_tryIntoValue?_none hN with ⟨h1, hE⟩ | h2
  · rw [h1, shellFieldRead_of_allFieldsUninit ((Bool.and_eq_true _ _).mp hE).2]
    rfl
  · rw [h2]
    exact readFieldSlot_nested_field locals sh.variantIdx sh.isAdt sh.discriminantSet sh.fields g t q

/-- `Downcast(v)` + `Field` reads of a normalized, non-promoting shell. -/
theorem readFieldSlot_normalizeShell_downcast_field {locals : List LocalSlot}
    {sh : PartialAggregate} (hN : sh.tryIntoValue? = none) (n : Option String) (v g : Nat)
    (t : Ty) (q : List ProjectionElem) :
    readFieldSlot locals (normalizeShell sh) (.downcast n v :: .field g t :: q) =
      shellFieldRead locals sh v g q := by
  rcases normalizeShell_of_tryIntoValue?_none hN with ⟨h1, hE⟩ | h2
  · rw [h1, shellFieldRead_of_allFieldsUninit ((Bool.and_eq_true _ _).mp hE).2]
    rfl
  · rw [h2]
    exact readFieldSlot_nested_downcast_field locals sh.variantIdx sh.isAdt sh.discriminantSet
      sh.fields n v g t q

/-- Sibling frame of one shell step: field `g ≠ f` reads are unchanged by updating field `f`. -/
theorem shellFieldRead_set_ne {locals : List LocalSlot} {sh : PartialAggregate} {disc' : Bool}
    {f g k : Nat} {c' : FieldSlot} {q : List ProjectionElem} (hNe : f ≠ g) :
    shellFieldRead locals { sh with discriminantSet := disc', fields := sh.fields.set f c' } k g q =
      shellFieldRead locals sh k g q := by
  unfold shellFieldRead
  dsimp only
  rw [List.getElem?_set_ne hNe]
  rfl

/-- Reading through the updated field `f` of one shell step reads the new child. -/
theorem shellFieldRead_set_self {locals : List LocalSlot} {sh : PartialAggregate} {disc' : Bool}
    {f k : Nat} {c c' : FieldSlot} {q : List ProjectionElem} (hc : sh.fields[f]? = some c) :
    shellFieldRead locals { sh with discriminantSet := disc', fields := sh.fields.set f c' } k f q =
      if shellVariant sh = k then readFieldSlot locals c' q else .ub := by
  have hLt := (List.getElem?_eq_some_iff.mp hc).1
  unfold shellFieldRead
  dsimp only
  rw [List.getElem?_set_self hLt]
  rfl

/-- Reading field `f` of a shell whose field `f` is `c`. -/
theorem shellFieldRead_of_getElem? {locals : List LocalSlot} {sh : PartialAggregate} {f k : Nat}
    {c : FieldSlot} {q : List ProjectionElem} (hc : sh.fields[f]? = some c) :
    shellFieldRead locals sh k f q = if shellVariant sh = k then readFieldSlot locals c q else .ub := by
  simp only [shellFieldRead, hc]

/-- A projection `q` diverging from the deinitialized path `p` at some field step: both paths
agree on a common prefix of `Field` / `Downcast(v)` + `Field` steps and then select distinct
fields `f ≠ g` of the same struct, tuple, or (active) enum variant. -/
inductive Diverges : List ProjectionElem → List ProjectionElem → Prop where
  | field {f g : Nat} {t t' : Ty} {p q : List ProjectionElem} (hNe : f ≠ g) :
      Diverges (.field f t :: p) (.field g t' :: q)
  | downcastField {n n' : Option String} {v f g : Nat} {t t' : Ty} {p q : List ProjectionElem}
      (hNe : f ≠ g) : Diverges (.downcast n v :: .field f t :: p) (.downcast n' v :: .field g t' :: q)
  | fieldCons {f : Nat} {t t' : Ty} {p q : List ProjectionElem} (h : Diverges p q) :
      Diverges (.field f t :: p) (.field f t' :: q)
  | downcastFieldCons {n n' : Option String} {v f : Nat} {t t' : Ty} {p q : List ProjectionElem}
      (h : Diverges p q) :
      Diverges (.downcast n v :: .field f t :: p) (.downcast n' v :: .field f t' :: q)

/-- A diverging path is non-empty. -/
theorem Diverges.cons_left {p q : List ProjectionElem} (h : Diverges p q) :
    ∃ a rest, p = a :: rest := by
  cases h <;> exact ⟨_, _, rfl⟩

/-- The stepped shell of a successful shell step whose child is uninitialized along `rest` does
not promote. -/
theorem stepped_tryIntoValue?_none {sh : PartialAggregate} {disc' : Bool} {f : Nat}
    {c c' : FieldSlot} {rest : List ProjectionElem} (hc : sh.fields[f]? = some c)
    (hU : UninitAt c' rest) :
    ({ sh with discriminantSet := disc', fields := sh.fields.set f c' } :
      PartialAggregate).tryIntoValue? = none := by
  have hLt := (List.getElem?_eq_some_iff.mp hc).1
  exact tryIntoValue?_eq_none_of_getElem? (idx := f) (c := c')
    (show (sh.fields.set f c')[f]? = some c' from List.getElem?_set_self hLt)
    (fun v hv => UninitAt.not_init (hv ▸ hU))

/-- **Disjoint-sibling frame of `deinitFieldSlot`**: deinitializing `p` does not change the
result of reading any projection `q` that diverges from `p` at a field step. -/
theorem deinitFieldSlot_read_diverges_eq (ts : Bool) (dlocals locals : List LocalSlot)
    {p q : List ProjectionElem} (hDiv : Diverges p q) :
    ∀ (slot slot' : FieldSlot), deinitFieldSlot ts dlocals slot p = some slot' →
      readFieldSlot locals slot' q = readFieldSlot locals slot q := by
  induction hDiv with
  | @field f g t t' rp rq hNe =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init v =>
      cases v with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_field locals vals (var := var) hV, shellFieldRead_set_ne hNe]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_field, shellFieldRead_set_ne hNe]
  | @downcastField n n' v f g t t' rp rq hNe =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init val =>
      cases val with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_downcast_field, shellFieldRead_set_ne hNe]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_downcast_field, shellFieldRead_set_ne hNe]
  | @fieldCons f t t' rp rq _ ih =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init v =>
      cases v with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_field locals vals (var := var) hV, shellFieldRead_set_self hc,
          shellFieldRead_of_getElem? hc, ih c c' hcc]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_field, shellFieldRead_set_self hc, shellFieldRead_of_getElem? hc,
        ih c c' hcc]
  | @downcastFieldCons n n' v f t t' rp rq _ ih =>
    intro slot slot' h
    cases slot with
    | uninit =>
      simp only [deinitFieldSlot] at h
      split at h
      · cases h; rfl
      · nomatch h
    | init val =>
      cases val with
      | aggregate var vals =>
        simp only [deinitFieldSlot] at h
        obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
        have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
        rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
          readFieldSlot_init_downcast_field, shellFieldRead_set_self hc,
          shellFieldRead_of_getElem? hc, ih c c' hcc]
      | _ => nomatch h
    | nested var adt disc fs =>
      simp only [deinitFieldSlot] at h
      obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
      rw [readFieldSlot_normalizeShell_downcast_field (stepped_tryIntoValue?_none hc hU),
        readFieldSlot_nested_downcast_field, shellFieldRead_set_self hc,
        shellFieldRead_of_getElem? hc, ih c c' hcc]

/-- `readFieldSlot` depends on the frame only through initialized scalar index locals. -/
theorem readFieldSlot_congr {locals₁ locals₂ : List LocalSlot}
    (hSame : SameScalarLocals locals₁ locals₂) (slot : FieldSlot) (q : List ProjectionElem) :
    readFieldSlot locals₁ slot q = readFieldSlot locals₂ slot q := by
  cases slot with
  | uninit => rfl
  | init v => exact evalValueProjRead_congr_scalar_locals hSame q v
  | nested var adt disc fs => exact readFromPartialShell_congr_scalar_locals hSame q _

/-- `SameScalarLocals` is symmetric. -/
theorem SameScalarLocals.symm {locals₁ locals₂ : List LocalSlot}
    (h : SameScalarLocals locals₁ locals₂) : SameScalarLocals locals₂ locals₁ :=
  fun i sc => (h i sc).symm

/-- `slotsToTrustedLocals` is a pointwise map. -/
theorem slotsToTrustedLocals_eq_map : ∀ (slots : List LocalSlotState),
    slotsToTrustedLocals slots = slots.map slotStateToTrustedLocal
  | [] => rfl
  | s :: rest => by
    simp only [slotsToTrustedLocals, List.map_cons, slotsToTrustedLocals_eq_map rest]

/-- Replacing a slot that is not an initialized scalar by another such slot preserves every
initialized scalar index local. -/
theorem sameScalarLocals_set {slots : List LocalSlotState} {i : Nat} {old new : LocalSlotState}
    (hOld : slots[i]? = some old)
    (hO : ∀ sc, slotStateToTrustedLocal old ≠ .init (.scalar sc))
    (hN : ∀ sc, slotStateToTrustedLocal new ≠ .init (.scalar sc)) :
    SameScalarLocals (slotsToTrustedLocals slots) (slotsToTrustedLocals (slots.set i new)) := by
  intro j sc
  simp only [slotsToTrustedLocals_eq_map, get?_eq_getElem?, List.getElem?_map]
  by_cases hij : i = j
  · subst hij
    have hLt := (List.getElem?_eq_some_iff.mp hOld).1
    rw [List.getElem?_set_self hLt, hOld]
    simp only [Option.map_some, Option.some.injEq]
    exact ⟨fun h => absurd h (hO sc), fun h => absurd h (hN sc)⟩
  · rw [List.getElem?_set_ne hij]

/-- A promoted shell is an aggregate. -/
theorem tryIntoValue?_aggregate {shell : PartialAggregate} {v : Value}
    (h : shell.tryIntoValue? = some v) : ∃ var vals, v = .aggregate var vals := by
  obtain ⟨_, vals, _, rfl⟩ := (tryIntoValue?_eq_some_iff shell v).mp h
  exact ⟨_, vals, rfl⟩

/-- The root of a successful projected `Deinit` is not an initialized scalar. -/
theorem deinit_root_not_scalar {ts : Bool} {locals : List LocalSlot} {st : LocalSlotState}
    {a : ProjectionElem} {rest : List ProjectionElem} {slot' : FieldSlot}
    (h : deinitFieldSlot ts locals (slotStateToFieldSlot st) (a :: rest) = some slot') :
    ∀ sc, slotStateToTrustedLocal st ≠ .init (.scalar sc) := by
  intro sc hEq
  cases st with
  | dead => simp [slotStateToTrustedLocal] at hEq
  | uninit => simp [slotStateToTrustedLocal] at hEq
  | init v =>
    simp only [slotStateToTrustedLocal, LocalSlot.init.injEq] at hEq
    subst hEq
    nomatch h
  | partialShell shell =>
    simp only [slotStateToTrustedLocal] at hEq
    split at hEq
    · rename_i v hv
      obtain ⟨_, _, rfl⟩ := tryIntoValue?_aggregate hv
      simp at hEq
    · simp at hEq

/-- The slot a `Deinit` leaves behind is not an initialized scalar. -/
theorem UninitAt.not_scalar {slot : FieldSlot} {p : List ProjectionElem} (h : UninitAt slot p) :
    ∀ sc, slotStateToTrustedLocal (fieldSlotToLocalSlotState slot) ≠ .init (.scalar sc) := by
  intro sc hEq
  cases slot with
  | uninit => simp [fieldSlotToLocalSlotState, slotStateToTrustedLocal] at hEq
  | init v => exact UninitAt.not_init h
  | nested var adt disc fs =>
    have hN := UninitAt.nested_tryIntoValue?_none h
    simp [fieldSlotToLocalSlotState, slotStateToTrustedLocal, hN] at hEq

/-- Reading a place of a local whose slot is unchanged, in frames agreeing on scalar index
locals, gives the same result. -/
theorem readPlaceState_congr_unchanged {slots slots' : List LocalSlotState} {loc : Local}
    (hGet : slots'[loc]? = slots[loc]?)
    (hSame : SameScalarLocals (slotsToTrustedLocals slots) (slotsToTrustedLocals slots'))
    (q : List ProjectionElem) :
    readPlaceState slots' ⟨loc, q⟩ = readPlaceState slots ⟨loc, q⟩ := by
  unfold readPlaceState
  cases projectionHasDeref q with
  | true => rfl
  | false =>
    simp only [get?_eq_getElem?, hGet]
    cases slots[loc]? with
    | none => rfl
    | some st =>
      cases st with
      | dead => rfl
      | uninit => rfl
      | init v => exact (evalValueProjRead_congr_scalar_locals hSame q v).symm
      | partialShell sh => exact (readFromPartialShell_congr_scalar_locals hSame q sh).symm

/-- Two places are disjoint for a `Deinit` frame: the same local with diverging projections,
or distinct locals (the deinitialized place being projected, so that no initialized scalar
index local changes). -/
def DeinitDisjoint (place place' : Place) : Prop :=
  (place'.local_ = place.local_ ∧ Diverges place.projection place'.projection) ∨
    (place'.local_ ≠ place.local_ ∧ place.projection ≠ [])

/-- **Disjoint-Sibling Frame (`evalDeinitPlace_read_disjoint_eq`)**: after a successful
`Deinit` of `place`, reading any disjoint place `place'` — a different field `g ≠ f` of the same
struct/tuple/active enum variant (below any common prefix), or a different local — yields
exactly the same result as before. -/
theorem evalDeinitPlace_read_disjoint_eq {ts : Bool} {slots slots' : List LocalSlotState}
    {place place' : Place} (h : evalDeinitPlace ts slots place = some slots')
    (hDisj : DeinitDisjoint place place') :
    readPlaceState slots' place' = readPlaceState slots place' := by
  obtain ⟨st, hSt, hLive, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  have hProj : ∃ a rest, place.projection = a :: rest := by
    rcases hDisj with ⟨_, hDiv⟩ | ⟨_, hNe⟩
    · exact hDiv.cons_left
    · cases hp : place.projection with
      | nil => exact absurd hp hNe
      | cons a rest => exact ⟨a, rest, rfl⟩
  obtain ⟨a, rest, hP⟩ := hProj
  have hSame := sameScalarLocals_set hSt
    (deinit_root_not_scalar (show deinitFieldSlot ts _ _ (a :: rest) = some slot' by
      rw [← hP]; exact hD)) hU.not_scalar
  obtain ⟨loc', q⟩ := place'
  rcases hDisj with ⟨hLoc, hDiv⟩ | ⟨hNe, _⟩
  · simp only at hLoc hDiv
    subst hLoc
    obtain ⟨hRound, hNotDead⟩ := UninitAt.roundtrip hU
    have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hSt).1
    have hGet : (slots.set place.local_ (fieldSlotToLocalSlotState slot'))[place.local_]? =
        some (fieldSlotToLocalSlotState slot') := List.getElem?_set_self hLt
    cases hDeref : projectionHasDeref q with
    | true => simp only [readPlaceState, hDeref]
    | false =>
      rw [readPlaceState_eq_readFieldSlot hGet hNotDead q hDeref, hRound,
        readPlaceState_eq_readFieldSlot hSt hLive q hDeref, ← readFieldSlot_congr hSame]
      exact deinitFieldSlot_read_diverges_eq ts _ _ hDiv _ _ hD
  · exact readPlaceState_congr_unchanged (List.getElem?_set_ne (Ne.symm hNe)) hSame q

/-- Distinct-local frame of a bare-local `Deinit`: other locals read the same, provided the
deinitialized local did not hold an initialized scalar (which other places may use as an
`Index` operand). -/
theorem evalDeinitPlace_root_read_other_local_eq {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} (h : evalDeinitPlace ts slots place = some slots') {st : LocalSlotState}
    (hSt : slots[place.local_]? = some st)
    (hNotScalar : ∀ sc, slotStateToTrustedLocal st ≠ .init (.scalar sc))
    {loc' : Local} (hNe : loc' ≠ place.local_) (q : List ProjectionElem) :
    readPlaceState slots' ⟨loc', q⟩ = readPlaceState slots ⟨loc', q⟩ := by
  obtain ⟨st', hSt', _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  rw [hSt] at hSt'
  cases hSt'
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  exact readPlaceState_congr_unchanged (List.getElem?_set_ne (Ne.symm hNe))
    (sameScalarLocals_set hSt hNotScalar hU.not_scalar) q

/-! ### Section 2c: Put-after-`Deinit` re-promotion -/

/-- A path without `Downcast` steps (deinitializing along it never touches an enum tag). -/
def noDowncast : List ProjectionElem → Bool
  | [] => true
  | .downcast _ _ :: _ => false
  | _ :: rest => noDowncast rest

/-- A non-promoting enum/ADT shell whose tag is written normalizes to itself (it never
collapses). -/
theorem normalizeShell_eq_of_tagged {sh : PartialAggregate} (hN : sh.tryIntoValue? = none)
    (hAdt : sh.isAdt = true) (hDisc : sh.discriminantSet = true) :
    normalizeShell sh = sh.toFieldSlot := by
  unfold normalizeShell
  rw [hN]
  simp [hAdt, hDisc]

/-- A field of `vals.map .init` is an initialized field of `vals`. -/
theorem getElem?_map_init {vals : List Value} {idx : Nat} {c : FieldSlot}
    (h : (vals.map FieldSlot.init)[idx]? = some c) : ∃ cv, vals[idx]? = some cv ∧ c = .init cv := by
  rw [List.getElem?_map] at h
  cases hv : vals[idx]? with
  | none => rw [hv] at h; nomatch h
  | some cv =>
    rw [hv] at h
    simp only [Option.map_some, Option.some.injEq] at h
    exact ⟨cv, rfl, h.symm⟩

/-- Writing a field of an exploded aggregate after updating that field reassembles the
aggregate. -/
theorem map_init_set_set (vals : List Value) (idx : Nat) (c' : FieldSlot) (cv' : Value) :
    ((vals.map FieldSlot.init).set idx c').set idx (.init cv') =
      (vals.set idx cv').map FieldSlot.init := by
  rw [List.set_set, List.map_set]

/-- **Put-after-`Deinit` (`deinitFieldSlot_write_reinit`)**: deinitializing the part `p` of an
initialized value `v` and then writing `w` back to `p` restores an initialized slot, holding
exactly `v` updated at `p` with `w` (`evalValueProjWrite`), as long as the deinitialization did
not forget an enum tag (no `Downcast` on the path, or a tag stored apart from the fields). -/
theorem deinitFieldSlot_write_reinit (ts : Bool) (dlocals locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat) (w : Value) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts dlocals slot p = some slot') :
    ∀ (v : Value), slot = .init v → (ts = true ∨ noDowncast p = true) → ∀ (ty : Ty),
      ∃ v', evalValueProjWrite locals v p w = .ok v' ∧
        writeToFieldSlot locals arityOf slot' ty p w = .ok (.init v') := by
  fun_induction deinitFieldSlot ts dlocals slot p generalizing slot' with
  | case1 slot =>
    intro v _ _ ty
    cases h
    exact ⟨w, by cases v <;> rfl, rfl⟩
  | case2 => intro v hv; cases hv
  | case3 => intro v hv; cases hv
  | case4 var vals idx fty rest ih =>
    intro v hv hTag ty
    cases hv
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hV' : var = 0 := hV
    subst hV'
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
    obtain ⟨cv', hW, hWS⟩ := ih (.init cv) c' hcc cv rfl hTag fty
    have hLt : idx < vals.length := (List.getElem?_eq_some_iff.mp hcv).1
    have hN := stepped_tryIntoValue?_none (sh := explodeAggregate 0 vals)
      (disc' := (explodeAggregate 0 vals).discriminantSet && ((none : Option Nat).isNone || ts))
      hc hU
    rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate])]
    refine ⟨.aggregate 0 (vals.set idx cv'), ?_, ?_⟩
    · simp only [evalValueProjWrite, get?_eq_getElem?, hcv, hW,
        set?_eq_some_iff.mpr ⟨hLt, rfl⟩]
    · have hLt' : idx < ((vals.map FieldSlot.init).set idx c').length := by simp [hLt]
      simp only [PartialAggregate.toFieldSlot, explodeAggregate, writeToFieldSlot,
        get?_eq_getElem?,
        List.getElem?_set_self (l := vals.map FieldSlot.init) (a := c') (by simpa using hLt),
        Nat.beq_refl, hWS,
        set?_eq_some_iff.mpr ⟨hLt', rfl⟩, map_init_set_set, promoteShellToFieldSlot]
      rw [tryIntoValue?_of_all_init _ (vals.set idx cv') rfl (Or.inr rfl)]
  | case5 var vals n v idx fty rest ih =>
    intro val hv hTag ty
    cases hv
    have hTs : ts = true := by
      rcases hTag with hT | hT
      · exact hT
      · simp [noDowncast] at hT
    obtain ⟨hV, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    have hV' : var = v := hV
    subst hV'
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hcc
    obtain ⟨cv', hW, hWS⟩ := ih (.init cv) c' hcc cv rfl (Or.inl hTs) fty
    have hLt : idx < vals.length := (List.getElem?_eq_some_iff.mp hcv).1
    have hN := stepped_tryIntoValue?_none (sh := explodeAggregate var vals)
      (disc' := (explodeAggregate var vals).discriminantSet && ((some var).isNone || ts))
      hc hU
    rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate, hTs])]
    refine ⟨.aggregate var (vals.set idx cv'), ?_, ?_⟩
    · simp only [evalValueProjWrite, isFieldHead, Nat.beq_refl, Bool.and_self, get?_eq_getElem?,
        hcv, hW, set?_eq_some_iff.mpr ⟨hLt, rfl⟩]
    · have hLt' : idx < ((vals.map FieldSlot.init).set idx c').length := by simp [hLt]
      simp only [PartialAggregate.toFieldSlot, explodeAggregate, writeToFieldSlot,
        get?_eq_getElem?,
        List.getElem?_set_self (l := vals.map FieldSlot.init) (a := c') (by simpa using hLt),
        Nat.beq_refl, hWS,
        set?_eq_some_iff.mpr ⟨hLt', rfl⟩, map_init_set_set, promoteShellToFieldSlot, hTs,
        Bool.and_true, Bool.or_true]
      rw [tryIntoValue?_of_all_init _ (vals.set idx cv') rfl (Or.inr rfl)]
  | case6 => intro v hv; cases hv
  | case7 => intro v hv; cases hv
  | case8 => nomatch h

/-- `deinitTailOk` paths contain no `Deref`. -/
theorem deinitTailOk_noDeref (locals : List LocalSlot) (p : List ProjectionElem)
    (h : deinitTailOk locals p = true) : projectionHasDeref p = false := by
  fun_induction deinitTailOk locals p <;> simp_all [projectionHasDeref]

/-- A successfully deinitialized place has no `Deref`. -/
theorem deinitFieldSlot_noDeref {ts : Bool} {locals : List LocalSlot} {slot : FieldSlot}
    {p : List ProjectionElem} {slot' : FieldSlot}
    (h : deinitFieldSlot ts locals slot p = some slot') : projectionHasDeref p = false := by
  fun_induction deinitFieldSlot ts locals slot p generalizing slot' with
  | case1 => rfl
  | case2 p rest hT => exact deinitTailOk_noDeref _ _ hT
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case5 var vals n v idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case6 var adt disc fs idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case7 var adt disc fs n v idx ty rest ih =>
    obtain ⟨_, c, c', _, hcc, _⟩ := deinitShellStep_eq_some h
    simpa [projectionHasDeref] using ih c hcc
  | case8 => nomatch h

/-- `writePlaceState` on a live local writes through its root slot with `writeToFieldSlot`. -/
theorem writePlaceState_eq {arityOf : Ty → VariantIdx → Bool → Option Nat}
    {slots : List LocalSlotState} {place : Place} {rootTy : Ty} {w : Value} {st : LocalSlotState}
    (hSt : slots[place.local_]? = some st) (hLive : st ≠ .dead)
    (hNoDeref : projectionHasDeref place.projection = false) :
    writePlaceState arityOf slots place rootTy w =
      match writeToFieldSlot (slotsToTrustedLocals slots) arityOf (slotStateToFieldSlot st) rootTy
          place.projection w with
      | .ok next => .ok (slots.set place.local_ (fieldSlotToLocalSlotState next))
      | .ub => .ub
      | .unsupported => .unsupported := by
  unfold writePlaceState
  simp only [hNoDeref, get?_eq_getElem?, hSt]
  cases st with
  | dead => exact absurd rfl hLive
  | uninit => rfl
  | init v => rfl
  | partialShell sh => rfl

/-- **Put-After-Deinit Re-promotion (`evalDeinitPlace_write_reinit`)**: deinitializing a part
`place` of an initialized local and then writing `w` back to `place` (`writePlaceState`)
restores `.init` with the original root value updated at `place` — unless an enum tag was
forgotten on the way (see `deinitFieldSlot_niche_write_needs_setDiscriminant`). -/
theorem evalDeinitPlace_write_reinit {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {rootVal : Value} (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : evalDeinitPlace ts slots place = some slots')
    (hTag : ts = true ∨ noDowncast place.projection = true)
    (arityOf : Ty → VariantIdx → Bool → Option Nat) (rootTy : Ty) (w : Value) :
    ∃ rootVal', evalValueProjWrite (slotsToTrustedLocals slots') rootVal place.projection w =
        .ok rootVal' ∧
      writePlaceState arityOf slots' place rootTy w = .ok (slots.set place.local_ (.init rootVal')) := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  rw [hRoot] at hSt
  cases hSt
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  obtain ⟨hRound, hNotDead⟩ := UninitAt.roundtrip hU
  have hLt := (List.getElem?_eq_some_iff.mp hRoot).1
  have hGet : (slots.set place.local_ (fieldSlotToLocalSlotState slot'))[place.local_]? =
      some (fieldSlotToLocalSlotState slot') := List.getElem?_set_self hLt
  obtain ⟨v', hW, hWS⟩ := deinitFieldSlot_write_reinit ts _
    (slotsToTrustedLocals (slots.set place.local_ (fieldSlotToLocalSlotState slot'))) arityOf w
    _ _ _ hD rootVal rfl hTag rootTy
  refine ⟨v', hW, ?_⟩
  rw [writePlaceState_eq hGet hNotDead (deinitFieldSlot_noDeref hD), hRound, hWS]
  simp only [fieldSlotToLocalSlotState, List.set_set]

/-- **A niche-encoded tag is lost (`A3`)**: for an enum whose tag may live in a field's niche
(`tag_survives_field_deinit = false`), deinitializing a variant field and writing it back does
not restore an initialized value: the result is a shell of that variant with an unwritten tag
(the value needs `SetDiscriminant` again), and the whole value stays unreadable. -/
theorem deinitFieldSlot_niche_write_needs_setDiscriminant (dlocals locals : List LocalSlot)
    (arityOf : Ty → VariantIdx → Bool → Option Nat) (v f : Nat) (vals : List Value)
    (n : Option String) (t ty : Ty) (w : Value) (slot' : FieldSlot)
    (h : deinitFieldSlot false dlocals (.init (.aggregate v vals)) [.downcast n v, .field f t] =
      some slot')
    (r : FieldSlot)
    (hW : writeToFieldSlot locals arityOf slot' ty [.downcast n v, .field f t] w = .ok r) :
    ∃ fs, r = .nested v true false fs ∧ readFieldSlot locals r [] = .ub := by
  simp only [deinitFieldSlot] at h
  obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
  cases hcc
  have hLt : f < vals.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    simpa [explodeAggregate] using this
  have hN := stepped_tryIntoValue?_none (sh := explodeAggregate v vals)
    (disc' := (explodeAggregate v vals).discriminantSet && ((some v).isNone || false))
    (c' := FieldSlot.uninit) (rest := []) hc trivial
  have hRead : ∀ fs, readFieldSlot locals (.nested v true false fs) [] = .ub := by
    intro fs
    simp [readFieldSlot, readFromPartialShell, PartialAggregate.tryIntoValue?]
  rcases normalizeShell_of_tryIntoValue?_none hN with ⟨h1, _⟩ | h2
  · rw [h1] at hW
    simp only [writeToFieldSlot] at hW
    split at hW
    · rename_i cnt _
      split at hW
      · split at hW
        · rename_i fs' _
          cases hW
          refine ⟨fs', ?_, hRead fs'⟩
          simp [promoteShellToFieldSlot, PartialAggregate.tryIntoValue?, PartialAggregate.newUninit]
        · nomatch hW
      · nomatch hW
    · nomatch hW
  · rw [h2] at hW
    simp only [explodeAggregate, writeToFieldSlot, get?_eq_getElem?,
      List.getElem?_set_self (l := vals.map FieldSlot.init) (a := FieldSlot.uninit)
        (by simpa using hLt), Nat.beq_refl] at hW
    split at hW
    · rename_i fs' _
      cases hW
      refine ⟨fs', ?_, hRead fs'⟩
      simp [promoteShellToFieldSlot, PartialAggregate.tryIntoValue?]
    · nomatch hW

/-! ### Section 2d: `Deinit` refines Trusted's `evalStmt` -/

mutual
  /-- Anneal's view `slot` of a part is *below* Trusted's value `t`: Anneal knows less (an
  uninitialized part may correspond to any Trusted value), and everything Anneal knows agrees
  with Trusted (initialized parts are equal, shells have Trusted's variant and arity). -/
  def FieldSlotBelow : FieldSlot → Value → Prop
    | .uninit, _ => True
    | .init v, t => v = t
    | .nested var adt disc fs, .aggregate tv tfs =>
      shellVariant ⟨var, adt, disc, fs⟩ = tv ∧ FieldListBelow fs tfs
    | .nested _ _ _ _, _ => False

  /-- Pointwise `FieldSlotBelow` of equally long field lists. -/
  def FieldListBelow : List FieldSlot → List Value → Prop
    | [], [] => True
    | f :: fs, t :: ts => FieldSlotBelow f t ∧ FieldListBelow fs ts
    | _, _ => False
end

/-- Anneal's local state is below Trusted's local slot: dead locals agree, an uninitialized
Anneal local is uninitialized in Trusted or an aggregate there (e.g. after a projected `Deinit`
of all its fields, which Trusted does not track), and initialized/partial locals are below
Trusted's value. -/
def SlotBelow : LocalSlotState → LocalSlot → Prop
  | .dead, .dead => True
  | .uninit, .uninit => True
  | .uninit, .init (.aggregate _ _) => True
  | .init v, .init w => v = w
  | .partialShell shell, .init t => FieldSlotBelow shell.toFieldSlot t
  | _, _ => False

/-- Pointwise lookup in `FieldListBelow`. -/
theorem FieldListBelow.getElem? : ∀ {fs : List FieldSlot} {tfs : List Value} {g : Nat}
    {c : FieldSlot}, FieldListBelow fs tfs → fs[g]? = some c →
      ∃ tc, tfs[g]? = some tc ∧ FieldSlotBelow c tc
  | [], [], _, _, _, h => by simp at h
  | f :: fs, t :: ts, 0, c, hB, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨t, rfl, hB.1⟩
  | f :: fs, t :: ts, g + 1, c, hB, h => by
    simp only [List.getElem?_cons_succ] at h ⊢
    exact FieldListBelow.getElem? hB.2 h
  | [], _ :: _, _, _, hB, _ => by simp [FieldListBelow] at hB
  | _ :: _, [], _, _, hB, _ => by simp [FieldListBelow] at hB

/-- Updating position `g` of below-related lists with below-related elements. -/
theorem FieldListBelow.set : ∀ {fs : List FieldSlot} {tfs : List Value} (g : Nat)
    {c : FieldSlot} {tc : Value}, FieldListBelow fs tfs → tfs[g]? = some tc →
      FieldSlotBelow c tc → FieldListBelow (fs.set g c) tfs
  | [], [], _, _, _, _, h, _ => by simp at h
  | f :: fs, t :: ts, 0, c, tc, hB, h, hC => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    exact ⟨hC, hB.2⟩
  | f :: fs, t :: ts, g + 1, c, tc, hB, h, hC => by
    simp only [List.getElem?_cons_succ] at h
    exact ⟨hB.1, FieldListBelow.set g hB.2 h hC⟩
  | [], _ :: _, _, _, _, hB, _, _ => by simp [FieldListBelow] at hB
  | _ :: _, [], _, _, _, hB, _, _ => by simp [FieldListBelow] at hB

/-- `vals.map .init` is below `vals`. -/
theorem fieldListBelow_map_init : ∀ (vals : List Value), FieldListBelow (vals.map .init) vals
  | [] => trivial
  | _ :: vs => ⟨rfl, fieldListBelow_map_init vs⟩

/-- An all-initialized field list below `tfs` is `tfs`. -/
theorem FieldListBelow.eq_of_map_init : ∀ {vals tfs : List Value},
    FieldListBelow (vals.map .init) tfs → vals = tfs
  | [], [], _ => rfl
  | v :: vs, t :: ts, h => by
    have h1 : v = t := h.1
    rw [h1, FieldListBelow.eq_of_map_init h.2]
  | [], _ :: _, h => by simp [FieldListBelow] at h
  | _ :: _, [], h => by simp [FieldListBelow] at h

/-- A normalized shell below `t` stays below `t` (a promoted shell is exactly `t`). -/
theorem normalizeShell_below {sh : PartialAggregate} {tv : Nat} {tfs : List Value}
    (hV : shellVariant sh = tv) (hB : FieldListBelow sh.fields tfs) :
    FieldSlotBelow (normalizeShell sh) (.aggregate tv tfs) := by
  unfold normalizeShell
  cases hT : sh.tryIntoValue? with
  | some v =>
    obtain ⟨_, vals, hF, rfl⟩ := (tryIntoValue?_eq_some_iff sh v).mp hT
    rw [hF] at hB
    have := FieldListBelow.eq_of_map_init hB
    subst this
    show Value.aggregate _ vals = .aggregate tv vals
    rw [← hV]
    rfl
  | none =>
    cases (!sh.isAdt || !sh.discriminantSet) && allFieldsUninit sh.fields with
    | true => trivial
    | false => exact ⟨hV, hB⟩

/-- **`Deinit` stays below Trusted**: deinitializing a part of a slot that is below `t` yields a
slot that is still below `t` (Trusted's value is unchanged by a projected `Deinit`). -/
theorem deinitFieldSlot_below (ts : Bool) (locals : List LocalSlot) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts locals slot p = some slot') :
    ∀ (t : Value), FieldSlotBelow slot t → FieldSlotBelow slot' t := by
  fun_induction deinitFieldSlot ts locals slot p generalizing slot' with
  | case1 => intro t _; cases h; trivial
  | case2 => intro t _; cases h; trivial
  | case3 => nomatch h
  | case4 var vals idx ty rest ih =>
    intro t hB
    have ht : t = .aggregate var vals := hB.symm
    subst ht
    obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    exact normalizeShell_below rfl
      (FieldListBelow.set idx (fieldListBelow_map_init vals) hcv (ih (.init cv) c' hcc cv rfl))
  | case5 var vals n v idx ty rest ih =>
    intro t hB
    have ht : t = .aggregate var vals := hB.symm
    subst ht
    obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    exact normalizeShell_below rfl
      (FieldListBelow.set idx (fieldListBelow_map_init vals) hcv (ih (.init cv) c' hcc cv rfl))
  | case6 var adt disc fs idx ty rest ih =>
    intro t hB
    cases t with
    | aggregate tv tfs =>
      obtain ⟨hV, hBs⟩ := hB
      obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
      exact normalizeShell_below hV (FieldListBelow.set idx hBs htc (ih c c' hcc tc hCB))
    | _ => exact absurd hB id
  | case7 var adt disc fs n v idx ty rest ih =>
    intro t hB
    cases t with
    | aggregate tv tfs =>
      obtain ⟨hV, hBs⟩ := hB
      obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some h
      obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
      exact normalizeShell_below hV (FieldListBelow.set idx hBs htc (ih c c' hcc tc hCB))
    | _ => exact absurd hB id
  | case8 => nomatch h

/-- Reading the whole of a slot below `t` returns exactly `t`. -/
theorem readFieldSlot_below_nil {locals : List LocalSlot} {slot : FieldSlot} {t r : Value}
    (hB : FieldSlotBelow slot t) (hR : readFieldSlot locals slot [] = .ok r) : r = t := by
  cases slot with
  | uninit => nomatch hR
  | init v =>
    have hv : v = t := hB
    simp only [readFieldSlot, evalValueProjRead] at hR
    cases hR
    exact hv
  | nested var adt disc fs =>
    cases t with
    | aggregate tv tfs =>
      obtain ⟨hV, hBs⟩ := hB
      simp only [readFieldSlot, readFromPartialShell] at hR
      split at hR
      · rename_i v hT
        cases hR
        obtain ⟨_, vals, hF, rfl⟩ := (tryIntoValue?_eq_some_iff _ _).mp hT
        simp only at hF
        subst hF
        have := FieldListBelow.eq_of_map_init hBs
        subst this
        rw [← hV]
        rfl
      · nomatch hR
    | _ => exact absurd hB id

/-- Fuel form of `readFieldSlot_below_refines`. -/
theorem readFieldSlot_below_refines_aux (locals : List LocalSlot) :
    ∀ (n : Nat) (q : List ProjectionElem), q.length ≤ n → ∀ (slot : FieldSlot) (t r : Value),
      FieldSlotBelow slot t → readFieldSlot locals slot q = .ok r →
      evalValueProjRead locals t q = .ok r := by
  intro n
  induction n with
  | zero =>
    intro q hLen slot t r hB hR
    have hq : q = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hLen)
    subst hq
    rw [readFieldSlot_below_nil hB hR]
    rfl
  | succ n ih =>
    intro q hLen slot t r hB hR
    rcases q with _ | ⟨a, q'⟩
    · rw [readFieldSlot_below_nil hB hR]
      rfl
    · simp only [List.length_cons] at hLen
      cases slot with
      | uninit => nomatch hR
      | init v =>
        have hv : v = t := hB
        subst hv
        exact hR
      | nested var adt disc fs =>
        cases t with
        | aggregate tv tfs =>
          obtain ⟨hV, hBs⟩ := hB
          cases a
          case field g ty =>
            rw [readFieldSlot_nested_field] at hR
            simp only [shellFieldRead] at hR
            split at hR
            · rename_i hV0
              cases hc : fs[g]? with
              | none => rw [hc] at hR; nomatch hR
              | some c =>
                rw [hc] at hR
                obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
                rw [evalValueProjRead_aggregate_field, htc]
                exact ih q' (by omega) c tc r hCB hR
            · nomatch hR
          case downcast nm v =>
            rcases q' with _ | ⟨b, q''⟩
            · simp [readFieldSlot, readFromPartialShell] at hR
            · cases b
              case field g ty =>
                simp only [List.length_cons] at hLen
                rw [readFieldSlot_nested_downcast_field] at hR
                simp only [shellFieldRead] at hR
                split at hR
                · rename_i hVv
                  cases hc : fs[g]? with
                  | none => rw [hc] at hR; nomatch hR
                  | some c =>
                    rw [hc] at hR
                    obtain ⟨tc, htc, hCB⟩ := FieldListBelow.getElem? hBs hc
                    rw [evalValueProjRead_aggregate_downcast_field, ← hV, hVv]
                    simp only [↓reduceIte, htc]
                    exact ih q'' (by omega) c tc r hCB hR
                · nomatch hR
              all_goals simp [readFieldSlot, readFromPartialShell, isFieldHead] at hR
          all_goals simp [readFieldSlot, readFromPartialShell] at hR
        | _ => exact absurd hB id

/-- **Reads below Trusted are Trusted reads**: every successful read of a slot below `t`
returns what Trusted's value-tree read of `t` returns. -/
theorem readFieldSlot_below_refines {locals : List LocalSlot} {slot : FieldSlot} {t r : Value}
    {q : List ProjectionElem} (hB : FieldSlotBelow slot t)
    (hR : readFieldSlot locals slot q = .ok r) : evalValueProjRead locals t q = .ok r :=
  readFieldSlot_below_refines_aux locals q.length q (Nat.le_refl _) slot t r hB hR

/-- Below-related frames agree on initialized scalar index locals. -/
theorem sameScalarLocals_of_slotBelow {slots : List LocalSlotState} {locals : List LocalSlot}
    (hRel : SlotsRefine SlotBelow slots locals) :
    SameScalarLocals (slotsToTrustedLocals slots) locals := by
  intro i sc
  rw [slotsToTrustedLocals_eq_map, get?_eq_getElem?, get?_eq_getElem?, List.getElem?_map]
  rcases SlotsRefine.get?_rel i hRel with ⟨hA, hT⟩ | ⟨a, t, hA, hT, hAT⟩
  · simp only [get?_eq_getElem?] at hA hT
    simp [hA, hT]
  · simp only [get?_eq_getElem?] at hA hT
    rw [hA, hT]
    simp only [Option.map_some, Option.some.injEq]
    cases a with
    | dead => cases t <;> simp_all [SlotBelow, slotStateToTrustedLocal]
    | uninit =>
      cases t with
      | dead => simp_all [SlotBelow]
      | uninit => simp [slotStateToTrustedLocal]
      | init w => cases w <;> simp_all [SlotBelow, slotStateToTrustedLocal]
    | init v =>
      cases t with
      | init w =>
        have hvw : v = w := hAT
        subst hvw
        simp [slotStateToTrustedLocal]
      | _ => simp_all [SlotBelow]
    | partialShell sh =>
      cases t with
      | init w =>
        have hw : ∃ tv tfs, w = .aggregate tv tfs := by
          cases w with
          | aggregate tv tfs => exact ⟨tv, tfs, rfl⟩
          | _ => exact absurd hAT id
        obtain ⟨tv, tfs, rfl⟩ := hw
        simp only [slotStateToTrustedLocal]
        split
        · rename_i v hv
          obtain ⟨_, _, rfl⟩ := tryIntoValue?_aggregate hv
          simp
        · simp
      | _ => simp_all [SlotBelow]

/-- **`readPlaceState` refines Trusted's `readProjectedValue` on below-related frames**: every
successful Anneal read (in particular every read after a projected `Deinit`) is defined in
Trusted with the same value. -/
theorem readPlaceState_below_refines {slots : List LocalSlotState} {locals : List LocalSlot}
    {place : Place} {val : Value} (hRel : SlotsRefine SlotBelow slots locals)
    (hRead : readPlaceState slots place = .ok val) :
    ∃ rootVal, get? locals place.local_ = some (.init rootVal) ∧
      readProjectedValue locals rootVal place.projection = .ok val := by
  have hSame := sameScalarLocals_of_slotBelow hRel
  cases hDeref : projectionHasDeref place.projection with
  | true => simp only [readPlaceState, hDeref] at hRead; nomatch hRead
  | false =>
    rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hNoneS, _⟩ | ⟨a, t, hGetS, hGetT, hAT⟩
    · simp only [readPlaceState, hDeref, hNoneS] at hRead; nomatch hRead
    · have hLive : a ≠ .dead := by
        intro hD
        subst hD
        simp only [readPlaceState, hDeref, hGetS] at hRead
        nomatch hRead
      simp only [get?_eq_getElem?] at hGetS
      rw [readPlaceState_eq_readFieldSlot hGetS hLive _ hDeref, readFieldSlot_congr hSame] at hRead
      have hBelow : ∃ rootVal, t = .init rootVal ∧ FieldSlotBelow (slotStateToFieldSlot a) rootVal := by
        cases a with
        | dead => exact absurd rfl hLive
        | uninit =>
          cases t with
          | init w => exact ⟨w, rfl, trivial⟩
          | _ => simp [readFieldSlot, slotStateToFieldSlot] at hRead
        | init v =>
          cases t with
          | init w => exact ⟨w, rfl, hAT⟩
          | _ => exact absurd hAT id
        | partialShell sh =>
          cases t with
          | init w => exact ⟨w, rfl, hAT⟩
          | _ => exact absurd hAT id
      obtain ⟨rootVal, rfl, hB⟩ := hBelow
      exact ⟨rootVal, hGetT, evalValueProjRead_refines_readProjectedValue _ _ _ _
        (readFieldSlot_below_refines hB hRead)⟩

/-- A projected `Deinit` of an initialized value succeeds only on an aggregate. -/
theorem deinitFieldSlot_init_aggregate {ts : Bool} {locals : List LocalSlot} {v : Value}
    {a : ProjectionElem} {rest : List ProjectionElem} {slot' : FieldSlot}
    (h : deinitFieldSlot ts locals (.init v) (a :: rest) = some slot') :
    ∃ var vals, v = .aggregate var vals := by
  cases v with
  | aggregate var vals => exact ⟨var, vals, rfl⟩
  | _ => nomatch h

/-- The path of a successful `Deinit` of an initialized value is readable in that value (in any
frame: such a path has no `Index` step). -/
theorem deinitFieldSlot_init_read_ok (ts : Bool) (dlocals : List LocalSlot) (slot : FieldSlot)
    (p : List ProjectionElem) (slot' : FieldSlot)
    (h : deinitFieldSlot ts dlocals slot p = some slot') :
    ∀ (v : Value), slot = .init v → ∀ (locals : List LocalSlot),
      ∃ r, evalValueProjRead locals v p = .ok r := by
  fun_induction deinitFieldSlot ts dlocals slot p generalizing slot' with
  | case1 => intro v _ locals; exact ⟨v, by cases v <;> rfl⟩
  | case2 => intro v hv; cases hv
  | case3 => intro v hv; cases hv
  | case4 var vals idx ty rest ih =>
    intro v hv locals
    cases hv
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    obtain ⟨r, hr⟩ := ih (.init cv) c' hcc cv rfl locals
    exact ⟨r, by rw [evalValueProjRead_aggregate_field, hcv]; exact hr⟩
  | case5 var vals n v idx ty rest ih =>
    intro val hv locals
    cases hv
    obtain ⟨hV, c, c', hc, hcc, _⟩ := deinitShellStep_eq_some h
    have hV' : var = v := hV
    obtain ⟨cv, hcv, rfl⟩ := getElem?_map_init (vals := vals) hc
    obtain ⟨r, hr⟩ := ih (.init cv) c' hcc cv rfl locals
    exact ⟨r, by rw [evalValueProjRead_aggregate_downcast_field]; simp only [hV', ↓reduceIte, hcv]; exact hr⟩
  | case6 => intro v hv; cases hv
  | case7 => intro v hv; cases hv
  | case8 => nomatch h

/-- **Bare-local `Deinit` step refinement**: on below-related frames, Anneal's `Deinit` of a bare
local agrees with Trusted's `evalStmt`, which steps (never faults) to the frame with the local
uninitialized, and the frames stay related. -/
theorem evalStmt_deinit_root_refines {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {s : MachineState} {span : String} {localDecls : List LocalDecl}
    {layouts : LayoutTable} (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hRoot : place.projection = []) (h : evalDeinitPlace ts slots place = some slots') :
    evalStmt s ⟨.deinit place, span⟩ localDecls layouts =
        .step (advanceStmt s (s.frame.locals.set place.local_ .uninit)) ∧
      SlotsRefine SlotBelow slots' (s.frame.locals.set place.local_ .uninit) := by
  obtain ⟨st, hSt, hLive, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  rw [hRoot, deinitFieldSlot_nil] at hD
  cases hD
  rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hA, _⟩ | ⟨a, t, hA, hT, hAT⟩
  · simp only [get?_eq_getElem?] at hA
    rw [hA] at hSt
    nomatch hSt
  · simp only [get?_eq_getElem?] at hA hT
    rw [hA] at hSt
    cases hSt
    have hLtT : place.local_ < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hT).1
    have hTnd : t ≠ .dead := by
      intro hTd
      subst hTd
      cases st <;> simp_all [SlotBelow]
    refine ⟨?_, SlotsRefine.set (show SlotBelow .uninit .uninit from trivial) _ hRel⟩
    simp only [evalStmt, hRoot, get?_eq_getElem?, hT]
    cases t with
    | dead => exact absurd rfl hTnd
    | uninit => simp only [set?_eq_some_iff.mpr ⟨hLtT, rfl⟩]
    | init w => simp only [set?_eq_some_iff.mpr ⟨hLtT, rfl⟩]

/-- **Projected `Deinit` step refinement**: on below-related frames, whenever Anneal's projected
`Deinit` succeeds and Trusted's root holds a value in which the place is readable, Trusted's
`evalStmt` steps (never faults) with its frame unchanged, and Anneal's frame — now with the place
uninitialized — is still below it (so every later Anneal read is a Trusted read, by
`readPlaceState_below_refines`). -/
theorem evalStmt_deinit_projected_refines {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {s : MachineState} {span : String} {localDecls : List LocalDecl}
    {layouts : LayoutTable} (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hProj : place.projection ≠ []) (h : evalDeinitPlace ts slots place = some slots')
    {rootVal : Value} (hTRoot : s.frame.locals[place.local_]? = some (.init rootVal))
    {tv : Value} (hTRead : readProjectedValue s.frame.locals rootVal place.projection = .ok tv) :
    evalStmt s ⟨.deinit place, span⟩ localDecls layouts = .step (advanceStmt s s.frame.locals) ∧
      SlotsRefine SlotBelow slots' s.frame.locals := by
  obtain ⟨a, rest, hP⟩ : ∃ a rest, place.projection = a :: rest := by
    cases hp : place.projection with
    | nil => exact absurd hp hProj
    | cons a rest => exact ⟨a, rest, rfl⟩
  obtain ⟨st, hSt, hLive, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  have hU := deinitFieldSlot_uninitAt _ _ _ _ _ hD
  refine ⟨?_, ?_⟩
  · rw [hP] at hTRead
    simp only [evalStmt, hP, get?_eq_getElem?, hTRoot, hTRead]
  · rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hA, _⟩ | ⟨a', t, hA, hT, hAT⟩
    · simp only [get?_eq_getElem?] at hA
      rw [hA] at hSt
      nomatch hSt
    · simp only [get?_eq_getElem?] at hA hT
      rw [hA] at hSt
      cases hSt
      rw [hTRoot] at hT
      cases hT
      have hAgg : ∃ var vals, rootVal = .aggregate var vals := by
        cases st with
        | dead => exact absurd rfl hLive
        | uninit =>
          cases rootVal with
          | aggregate var vals => exact ⟨var, vals, rfl⟩
          | _ => exact absurd hAT id
        | init v =>
          have hv : v = rootVal := hAT
          subst hv
          exact deinitFieldSlot_init_aggregate (show deinitFieldSlot ts _ (.init v) (a :: rest) =
            some slot' by rw [← hP]; exact hD)
        | partialShell sh =>
          cases rootVal with
          | aggregate var vals => exact ⟨var, vals, rfl⟩
          | _ => exact absurd hAT id
      have hB0 : FieldSlotBelow (slotStateToFieldSlot st) rootVal := by
        cases st with
        | dead => exact absurd rfl hLive
        | uninit => trivial
        | init v => exact hAT
        | partialShell sh => exact hAT
      have hB := deinitFieldSlot_below _ _ _ _ _ hD rootVal hB0
      have hSB : SlotBelow (fieldSlotToLocalSlotState slot') (.init rootVal) := by
        cases slot' with
        | uninit =>
          obtain ⟨var, vals, rfl⟩ := hAgg
          trivial
        | init v => exact absurd hU UninitAt.not_init
        | nested var adt disc fs =>
          have hN := UninitAt.nested_tryIntoValue?_none hU
          simp only [fieldSlotToLocalSlotState, hN]
          exact hB
      have hLtT : place.local_ < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hTRoot).1
      have hSelf : s.frame.locals.set place.local_ (.init rootVal) = s.frame.locals := by
        have hEq : s.frame.locals[place.local_] = .init rootVal :=
          (List.getElem?_eq_some_iff.mp hTRoot).2
        rw [← hEq]
        exact List.set_getElem_self hLtT
      have := SlotsRefine.set hSB place.local_ hRel
      rwa [hSelf] at this

/-- **Projected `Deinit` of an initialized local refines Trusted unconditionally**: when the
Anneal root is initialized, Anneal's success alone implies Trusted's `evalStmt` steps with its
frame unchanged, and the frames stay related. -/
theorem evalStmt_deinit_projected_init_refines {ts : Bool} {slots slots' : List LocalSlotState}
    {place : Place} {s : MachineState} {span : String} {localDecls : List LocalDecl}
    {layouts : LayoutTable} (hRel : SlotsRefine SlotBelow slots s.frame.locals)
    (hProj : place.projection ≠ []) {rootVal : Value}
    (hRoot : slots[place.local_]? = some (.init rootVal))
    (h : evalDeinitPlace ts slots place = some slots') :
    evalStmt s ⟨.deinit place, span⟩ localDecls layouts = .step (advanceStmt s s.frame.locals) ∧
      SlotsRefine SlotBelow slots' s.frame.locals := by
  obtain ⟨st, hSt, _, slot', hD, _⟩ := evalDeinitPlace_eq_some h
  rw [hRoot] at hSt
  cases hSt
  rcases SlotsRefine.get?_rel place.local_ hRel with ⟨hA, _⟩ | ⟨a', t, hA, hT, hAT⟩
  · simp only [get?_eq_getElem?] at hA
    rw [hA] at hRoot
    nomatch hRoot
  · simp only [get?_eq_getElem?] at hA hT
    rw [hA] at hRoot
    cases hRoot
    cases t with
    | init w =>
      have hw : rootVal = w := hAT
      subst hw
      obtain ⟨r, hr⟩ := deinitFieldSlot_init_read_ok _ _ _ _ _ hD rootVal rfl s.frame.locals
      exact evalStmt_deinit_projected_refines hRel hProj h hT
        (evalValueProjRead_refines_readProjectedValue _ _ _ _ hr)
    | _ => exact absurd hAT id

/-- **Documented divergence**: Trusted's projected `Deinit` requires an initialized root and
faults on an uninitialized one, whereas Anneal (like MiniRust, which writes `Uninit` bytes over
already uninitialized bytes) treats a well-formed `Deinit` below an uninitialized local as a
no-op. Anneal is therefore more permissive than Trusted here; every other `Deinit` refines
Trusted (`evalStmt_deinit_root_refines`, `evalStmt_deinit_projected_refines`). -/
theorem evalStmt_deinit_projected_uninit_root_divergence {ts : Bool}
    {slots : List LocalSlotState} {place : Place} {s : MachineState} {span : String}
    {localDecls : List LocalDecl} {layouts : LayoutTable} (hProj : place.projection ≠ [])
    (hA : slots[place.local_]? = some .uninit)
    (hTail : deinitTailOk (slotsToTrustedLocals slots) place.projection = true)
    (hT : s.frame.locals[place.local_]? = some .uninit) :
    evalDeinitPlace ts slots place = some slots ∧
      evalStmt s ⟨.deinit place, span⟩ localDecls layouts = .fail .ub := by
  obtain ⟨a, rest, hP⟩ : ∃ a rest, place.projection = a :: rest := by
    cases hp : place.projection with
    | nil => exact absurd hp hProj
    | cons a rest => exact ⟨a, rest, rfl⟩
  have hLt : place.local_ < slots.length := (List.getElem?_eq_some_iff.mp hA).1
  refine ⟨?_, ?_⟩
  · rw [hP] at hTail
    simp only [evalDeinitPlace, hA, hP, slotStateToFieldSlot, deinitFieldSlot, hTail, ↓reduceIte,
      fieldSlotToLocalSlotState]
    have hEq : slots[place.local_] = .uninit := (List.getElem?_eq_some_iff.mp hA).2
    rw [← hEq, List.set_getElem_self hLt]
  · simp only [evalStmt, hP, get?_eq_getElem?, hT]

/-! ### Section 2e: Byte-level `Uninit` refinement (closing `Translate.lean:3742`) -/

/-- A reference byte image of a local in MiniRust's memory model: `none` is an `Uninit` byte. -/
abbrev ByteImage : Type := List (Option UInt8)

/-- MiniRust's `Deinit` of a place at byte offset `off` of size `len`: writes `Uninit` to
`[off, off + len)` and leaves every other byte unchanged. -/
def deinitBytes (img : ByteImage) (off len : Nat) : ByteImage :=
  img.mapIdx fun i b => if off ≤ i ∧ i < off + len then none else b

/-- `deinitBytes` preserves the image size. -/
theorem length_deinitBytes (img : ByteImage) (off len : Nat) :
    (deinitBytes img off len).length = img.length := by
  simp [deinitBytes]

/-- Bytes inside the deinitialized range become `Uninit`. -/
theorem deinitBytes_getElem?_inside {img : ByteImage} {off len i : Nat}
    (hIn : off ≤ i ∧ i < off + len) (hLt : i < img.length) :
    (deinitBytes img off len)[i]? = some none := by
  simp [deinitBytes, List.getElem?_mapIdx, hIn, List.getElem?_eq_getElem hLt]

/-- Bytes outside the deinitialized range are unchanged. -/
theorem deinitBytes_getElem?_outside {img : ByteImage} {off len i : Nat}
    (hOut : ¬ (off ≤ i ∧ i < off + len)) : (deinitBytes img off len)[i]? = img[i]? := by
  simp only [deinitBytes, List.getElem?_mapIdx]
  cases img[i]? with
  | none => rfl
  | some b => simp only [Option.map_some, hOut, ↓reduceIte]

/-- The bytes `[off, off + size)` of `img` represent a field slot: an uninitialized field is all
`Uninit` bytes, an initialized field is its encoding (`enc`, MiniRust's `encode`), and a nested
partially initialized shell constrains nothing at this level. -/
def FieldBytes (enc : Value → List UInt8) (img : ByteImage) (off size : Nat) : FieldSlot → Prop
  | .uninit => ∀ k, k < size → img[off + k]? = some none
  | .init v => (enc v).length = size ∧ ∀ k, k < size → img[off + k]? = ((enc v)[k]?).map some
  | .nested _ _ _ _ => True

/-- Every field of `fields`, laid out by `lay` (`offset, size`), lies inside `img` and is
represented by its bytes. -/
def StructBytes (enc : Value → List UInt8) (lay : Nat → Option (Nat × Nat)) (img : ByteImage)
    (fields : List FieldSlot) : Prop :=
  ∀ i c off size, fields[i]? = some c → lay i = some (off, size) →
    off + size ≤ img.length ∧ FieldBytes enc img off size c

/-- A field layout whose fields occupy pairwise disjoint byte ranges (structs; not unions). -/
def LayoutDisjoint (lay : Nat → Option (Nat × Nat)) : Prop :=
  ∀ i j oi si oj sj, i ≠ j → lay i = some (oi, si) → lay j = some (oj, sj) →
    oi + si ≤ oj ∨ oj + sj ≤ oi

/-- A field's byte representation only depends on its own bytes. -/
theorem fieldBytes_frame {enc : Value → List UInt8} {img img' : ByteImage} {off size : Nat}
    {c : FieldSlot} (hFrame : ∀ k, k < size → img'[off + k]? = img[off + k]?) :
    FieldBytes enc img off size c → FieldBytes enc img' off size c := by
  cases c with
  | uninit => intro h k hk; rw [hFrame k hk]; exact h k hk
  | init v =>
    intro h
    exact ⟨h.1, fun k hk => by rw [hFrame k hk]; exact h.2 k hk⟩
  | nested => intro _; trivial

/-- **Byte-level simulation of a field `Deinit`**: on a layout with pairwise disjoint fields,
uninitializing field `f` in the field-slot model corresponds exactly to MiniRust writing
`Uninit` over the field's byte range: the new image represents the updated fields. -/
theorem structBytes_deinit {enc : Value → List UInt8} {lay : Nat → Option (Nat × Nat)}
    {img : ByteImage} {fields : List FieldSlot} {f : Nat} {c : FieldSlot} {off size : Nat}
    (hS : StructBytes enc lay img fields) (hD : LayoutDisjoint lay)
    (hc : fields[f]? = some c) (hf : lay f = some (off, size)) :
    StructBytes enc lay (deinitBytes img off size) (fields.set f .uninit) := by
  intro j cj oj sj hcj hj
  have hLtF := (hS f c off size hc hf).1
  by_cases hjf : j = f
  · subst hjf
    rw [hf] at hj
    cases hj
    have hLtf : j < fields.length := (List.getElem?_eq_some_iff.mp hc).1
    rw [List.getElem?_set_self hLtf] at hcj
    cases hcj
    refine ⟨by rw [length_deinitBytes]; exact hLtF, ?_⟩
    intro k hk
    exact deinitBytes_getElem?_inside ⟨by omega, by omega⟩ (by omega)
  · rw [List.getElem?_set_ne (Ne.symm hjf)] at hcj
    obtain ⟨hLtJ, hFB⟩ := hS j cj oj sj hcj hj
    refine ⟨by rw [length_deinitBytes]; exact hLtJ, fieldBytes_frame (fun k hk => ?_) hFB⟩
    apply deinitBytes_getElem?_outside
    rcases hD j f oj sj off size hjf hj hf with h1 | h1 <;> omega

/-- A non-promoting shell converts to a partial-shell local. -/
theorem fieldSlotToLocalSlotState_toFieldSlot {sh : PartialAggregate}
    (h : sh.tryIntoValue? = none) : fieldSlotToLocalSlotState sh.toFieldSlot = .partialShell sh := by
  obtain ⟨a, b, c, d⟩ := sh
  simp only [fieldSlotToLocalSlotState, h]

/-- `Deinit` of field `f` of an initialized struct/tuple local leaves the exploded shell with
exactly field `f` uninitialized (the tag-carrying shell never collapses). -/
theorem evalDeinitPlace_field_shell {ts : Bool} {slots slots' : List LocalSlotState} {loc : Local}
    {vals : List Value} {f : Nat} {ty : Ty}
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals)))
    (h : evalDeinitPlace ts slots ⟨loc, [.field f ty]⟩ = some slots') :
    f < vals.length ∧
      slots' = slots.set loc (.partialShell ⟨0, true, true, (vals.map .init).set f .uninit⟩) := by
  obtain ⟨st, hSt, _, slot', hD, rfl⟩ := evalDeinitPlace_eq_some h
  simp only at hSt hD
  rw [hRoot] at hSt
  cases hSt
  simp only [slotStateToFieldSlot, deinitFieldSlot] at hD
  obtain ⟨_, c, c', hc, hcc, rfl⟩ := deinitShellStep_eq_some hD
  cases hcc
  have hLt : f < vals.length := by
    have := (List.getElem?_eq_some_iff.mp hc).1
    simpa [explodeAggregate] using this
  have hN := stepped_tryIntoValue?_none (sh := explodeAggregate 0 vals)
    (disc' := (explodeAggregate 0 vals).discriminantSet && ((none : Option Nat).isNone || ts))
    (c' := FieldSlot.uninit) (rest := []) hc trivial
  refine ⟨hLt, ?_⟩
  rw [normalizeShell_eq_of_tagged hN rfl (by simp [explodeAggregate]),
    fieldSlotToLocalSlotState_toFieldSlot hN]
  rfl

/-- **`Deinit` of a struct field is MiniRust's byte-range `Uninit` write**: if the bytes of an
initialized struct local represent its fields under a layout `lay` with disjoint fields, then
after Anneal's `Deinit` of field `f` the new shell is represented by the image in which exactly
`f`'s bytes `[off, off + size)` are `Uninit` (and every other byte is unchanged). -/
theorem evalDeinitPlace_bytes_simulation {ts : Bool} {slots slots' : List LocalSlotState}
    {loc : Local} {vals : List Value} {f : Nat} {ty : Ty} (enc : Value → List UInt8)
    (lay : Nat → Option (Nat × Nat)) (img : ByteImage)
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals)))
    (h : evalDeinitPlace ts slots ⟨loc, [.field f ty]⟩ = some slots')
    (hD : LayoutDisjoint lay) (hS : StructBytes enc lay img (vals.map .init))
    {off size : Nat} (hf : lay f = some (off, size)) :
    ∃ shell, slots'[loc]? = some (.partialShell shell) ∧
      StructBytes enc lay (deinitBytes img off size) shell.fields ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + size) → (deinitBytes img off size)[i]? = img[i]? := by
  obtain ⟨hLt, rfl⟩ := evalDeinitPlace_field_shell hRoot h
  have hLoc : loc < slots.length := (List.getElem?_eq_some_iff.mp hRoot).1
  have hc : (vals.map FieldSlot.init)[f]? = some (.init vals[f]) := by
    simp [List.getElem?_map, List.getElem?_eq_getElem hLt]
  exact ⟨_, List.getElem?_set_self hLoc, structBytes_deinit hS hD hc hf,
    fun i hi => deinitBytes_getElem?_outside hi⟩

/-- The field layout `(offset, size)` an `AdtLayoutSpec` assigns to the fields `fs` of variant
`0` (`resolveAdtOffsetOf`). -/
def specFieldLayout (spec : AdtLayoutSpec) (fs : List FieldLayout) : Nat → Option (Nat × Nat) :=
  fun i =>
    match resolveAdtOffsetOf spec 0 i, fs[i]? with
    | some o, some fl => some (o, fl.size)
    | _, _ => none

/-- Inversion of `specFieldLayout`. -/
theorem specFieldLayout_eq_some {spec : AdtLayoutSpec} {fs : List FieldLayout} {i o s : Nat}
    (h : specFieldLayout spec fs i = some (o, s)) :
    resolveAdtOffsetOf spec 0 i = some o ∧ ∃ fl, fs[i]? = some fl ∧ fl.size = s := by
  unfold specFieldLayout at h
  split at h
  · rename_i o' fl hO hF
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hO, fl, hF, rfl⟩
  · nomatch h

/-- `#[repr(C)]` struct fields occupy pairwise disjoint byte ranges. -/
theorem reprC_layoutDisjoint {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c) :
    LayoutDisjoint (specFieldLayout spec fs) := by
  intro i j oi si oj sj hNe hi hj
  obtain ⟨hoi, fli, hfli, rfl⟩ := specFieldLayout_eq_some hi
  obtain ⟨hoj, flj, hflj, rfl⟩ := specFieldLayout_eq_some hj
  rcases Nat.lt_or_gt_of_ne hNe with hlt | hgt
  · obtain ⟨fi, hfi, hle⟩ := resolveAdtOffsetOf_reprC_monotone hShape hRepr hlt hoi hoj
    rw [hfli] at hfi
    cases hfi
    exact Or.inl hle
  · obtain ⟨fj, hfj, hle⟩ := resolveAdtOffsetOf_reprC_monotone hShape hRepr hgt hoj hoi
    rw [hflj] at hfj
    cases hfj
    exact Or.inr hle

/-- **`#[repr(C)]` instance of the byte simulation** (the projected-`Deinit` bridge to
MiniRust): for a `#[repr(C)]` struct, Anneal's `Deinit` of field `f` is MiniRust's `Uninit`
write over `[resolveAdtOffsetOf f, resolveAdtOffsetOf f + size f)`, which lies inside the
struct and is aligned for the field (`resolveAdtOffsetOf_bounds_and_align`). -/
theorem evalDeinitPlace_reprC_bytes_simulation {ts : Bool} {slots slots' : List LocalSlotState}
    {loc : Local} {vals : List Value} {f : Nat} {ty : Ty} (enc : Value → List UInt8)
    (img : ByteImage) {spec : AdtLayoutSpec} {fs : List FieldLayout}
    (hShape : spec.shape = .struct fs) (hRepr : spec.repr = .c) (hWF : spec.WF)
    (hRoot : slots[loc]? = some (.init (.aggregate 0 vals)))
    (h : evalDeinitPlace ts slots ⟨loc, [.field f ty]⟩ = some slots')
    (hS : StructBytes enc (specFieldLayout spec fs) img (vals.map .init))
    {off : Nat} (hOff : resolveAdtOffsetOf spec 0 f = some off) {fl : FieldLayout}
    (hfl : fs[f]? = some fl) :
    (∃ size align, adtLayout? spec = some (size, align) ∧ off + fl.size ≤ size ∧ fl.align ∣ off) ∧
    ∃ shell, slots'[loc]? = some (.partialShell shell) ∧
      StructBytes enc (specFieldLayout spec fs) (deinitBytes img off fl.size) shell.fields ∧
      ∀ i, ¬ (off ≤ i ∧ i < off + fl.size) → (deinitBytes img off fl.size)[i]? = img[i]? := by
  have hLay : specFieldLayout spec fs f = some (off, fl.size) := by
    simp [specFieldLayout, hOff, hfl]
  refine ⟨?_, evalDeinitPlace_bytes_simulation enc _ img hRoot h
    (reprC_layoutDisjoint hShape hRepr) hS hLay⟩
  obtain ⟨fs', fl', size, align, hVF, hFl', hL, hBound, hAlign⟩ :=
    resolveAdtOffsetOf_bounds_and_align spec hWF hOff
  have hVF' : variantFields spec 0 = some fs := by simp [variantFields, hShape]
  rw [hVF'] at hVF
  cases hVF
  rw [hfl] at hFl'
  cases hFl'
  exact ⟨size, align, hL, hBound, hAlign⟩

/-! ### Section 2f: `Retag` -/

/-- What `check_retagged_reference` needs to know about a reference's pointee type: its
alignment (`none` when the layout model leaves it unspecified: `UnsupportedLayout`), whether its
size is exactly `0`, and whether it is inhabited. -/
structure RetagPointee : Type where
  align : Option Nat
  zeroSized : Bool
  inhabited : Bool

/-- The reference structure of a retagged place's type (the part `Ty::contains_ref` and
`retag_value` inspect): types without references reachable by value (scalars, raw pointers,
unions, ...), references `&T`/`&mut T`, by-value tuples/structs, and enums (each variant
described by a `.tuple` of its fields) that store a tag (`requires_tag_write`) which may or may
not survive field deinitialization (`tag_survives_field_deinit`). -/
inductive RetagTy : Type where
  | noRef : RetagTy
  | ref (pointee : RetagPointee) : RetagTy
  | tuple (fields : List RetagTy) : RetagTy
  | enum (variants : List RetagTy) (requiresTag tagSurvives : Bool) : RetagTy

mutual
  /-- `Ty::contains_ref`. -/
  def RetagTy.containsRef : RetagTy → Bool
    | .noRef => false
    | .ref _ => true
    | .tuple fs => RetagTy.listContainsRef fs
    | .enum vs _ _ => RetagTy.listContainsRef vs

  /-- Some type of the list contains a reference. -/
  def RetagTy.listContainsRef : List RetagTy → Bool
    | [] => false
    | t :: ts => t.containsRef || RetagTy.listContainsRef ts
end

/-- The context of a `Retag` (`RetagCtx`): the target pointer width, Anneal's synthetic address
of a pointer and the local whose synthetic allocation it points into (`resolve_synthetic_local`),
and the storage state of every local. -/
structure RetagCtx : Type where
  ptrBits : Nat
  addrOf : ProvenancePtr → Nat
  localOf : ProvenancePtr → Option Nat
  slots : List LocalSlotState

/-- The alignment check of `check_retagged_reference` (an unspecified alignment is
`UnsupportedLayout`). -/
def retagAlignOk (pt : RetagPointee) (addr : Nat) : Bool :=
  match pt.align with
  | some al => addr % al == 0
  | none => false

/-- The dangling check of `check_retagged_reference` (`A3`): a reference into the synthetic
allocation of a storage-dead local dangles unless its pointee is zero-sized. -/
def retagTargetLive (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) : Bool :=
  match ctx.localOf p with
  | some l =>
    match ctx.slots[l]? with
    | some .dead => pt.zeroSized
    | _ => true
  | none => true

/-- `check_retagged_reference`: the address is a valid `&T` bit pattern (non-null and within the
pointer width), aligned to the pointee's (specified) alignment, the pointee is inhabited, and the
reference does not dangle into a dead local (`retagTargetLive`). -/
def retagRefOk (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) : Bool :=
  (ctx.addrOf p != 0) && decide (ctx.addrOf p < 2 ^ ctx.ptrBits) &&
    retagAlignOk pt (ctx.addrOf p) && pt.inhabited && retagTargetLive ctx pt p

mutual
  /-- `retag_value`: validates every reference reachable by value in an initialized value. -/
  def retagValueOk (ctx : RetagCtx) : RetagTy → Value → Bool
    | .noRef, _ => true
    | .ref pt, .ptr p _ => retagRefOk ctx pt p
    | .ref _, _ => false
    | .tuple fs, .aggregate _ vals => !RetagTy.listContainsRef fs || retagValuesOk ctx fs vals
    | .tuple fs, _ => !RetagTy.listContainsRef fs
    | .enum vs _ _, .aggregate v vals => !RetagTy.listContainsRef vs || retagVariantOk ctx vs v vals
    | .enum vs _ _, _ => !RetagTy.listContainsRef vs

  /-- `retag_value` over the fields of a tuple/struct/variant (lengths must match). -/
  def retagValuesOk (ctx : RetagCtx) : List RetagTy → List Value → Bool
    | [], [] => true
    | t :: ts, v :: vs => retagValueOk ctx t v && retagValuesOk ctx ts vs
    | _, _ => false

  /-- `retag_value` on the fields of variant `v` of an enum. -/
  def retagVariantOk (ctx : RetagCtx) : List RetagTy → Nat → List Value → Bool
    | [], _, _ => false
    | .tuple fs :: _, 0, vals => retagValuesOk ctx fs vals
    | _ :: _, 0, _ => false
    | _ :: vs, v + 1, vals => retagVariantOk ctx vs v vals
end

mutual
  /-- `retag_shell` / `retag_value` on a field slot: an uninitialized part holding references is
  `UninitializedLocal`; an enum shell needs a readable tag (`tag_is_readable`, `A3`). -/
  def retagSlotOk (ctx : RetagCtx) : RetagTy → FieldSlot → Bool
    | t, .uninit => !t.containsRef
    | t, .init v => retagValueOk ctx t v
    | .tuple fs, .nested _ _ _ cfs => !RetagTy.listContainsRef fs || retagSlotsOk ctx fs cfs
    | .enum vs rt ts, .nested var _ disc cfs =>
      !RetagTy.listContainsRef vs || ((!rt || (disc && ts)) && retagVariantSlotsOk ctx vs var cfs)
    | _, .nested _ _ _ _ => false

  /-- `retag_shell` over the field slots of a shell. -/
  def retagSlotsOk (ctx : RetagCtx) : List RetagTy → List FieldSlot → Bool
    | [], [] => true
    | t :: ts, c :: cs => retagSlotOk ctx t c && retagSlotsOk ctx ts cs
    | _, _ => false

  /-- `retag_shell` on the field slots of the variant `v` of an enum shell. -/
  def retagVariantSlotsOk (ctx : RetagCtx) : List RetagTy → Nat → List FieldSlot → Bool
    | [], _, _ => false
    | .tuple fs :: _, 0, cs => retagSlotsOk ctx fs cs
    | _ :: _, 0, _ => false
    | _ :: vs, v + 1, cs => retagVariantSlotsOk ctx vs v cs
end

/-- `project_mir_value` / `project_from_partial_shell` into a field slot: the part of `slot` at
`q` (`none` when the path is unreadable). -/
def projectFieldSlot (locals : List LocalSlot) : FieldSlot → List ProjectionElem → Option FieldSlot
  | slot, [] => some slot
  | .init v, q =>
    match evalValueProjRead locals v q with
    | .ok w => some (.init w)
    | _ => none
  | .nested var adt disc fs, .field idx _ :: rest =>
    if shellVariant ⟨var, adt, disc, fs⟩ = 0 then
      match fs[idx]? with
      | some c => projectFieldSlot locals c rest
      | none => none
    else none
  | .nested var adt disc fs, .downcast _ v :: .field idx _ :: rest =>
    if shellVariant ⟨var, adt, disc, fs⟩ = v then
      match fs[idx]? with
      | some c => projectFieldSlot locals c rest
      | none => none
    else none
  | _, _ => none

/-- `StatementEvalState::retag_place`: a dead local faults (`DeadLocal`); `Retag(Raw)` requires a
raw-pointer place holding an initialized pointer whose address fits the pointer width (it may be
null, unaligned, or dangling); every other kind requires nothing of a place without references
but its liveness, and otherwise validates every reference reachable in the place's part. -/
def evalRetagPlace (ctx : RetagCtx) (kind : RetagKind) (place : Place) (ty : RetagTy)
    (rawPtrPlace : Bool) : Bool :=
  match ctx.slots[place.local_]? with
  | none => false
  | some .dead => false
  | some st =>
    match kind with
    | .raw =>
      rawPtrPlace &&
        (match readPlaceState ctx.slots place with
         | .ok (.ptr p _) => decide (ctx.addrOf p < 2 ^ ctx.ptrBits)
         | _ => false)
    | _ =>
      !ty.containsRef ||
        (match projectFieldSlot (slotsToTrustedLocals ctx.slots) (slotStateToFieldSlot st)
            place.projection with
         | some target => retagSlotOk ctx ty target
         | none => false)

/-- `retagAlignOk` spelled out. -/
theorem retagAlignOk_iff (pt : RetagPointee) (addr : Nat) :
    retagAlignOk pt addr = true ↔ ∃ al, pt.align = some al ∧ addr % al = 0 := by
  unfold retagAlignOk
  cases pt.align <;> simp

/-- `retagTargetLive` spelled out. -/
theorem retagTargetLive_iff (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) :
    retagTargetLive ctx pt p = true ↔
      ∀ l, ctx.localOf p = some l → ctx.slots[l]? = some .dead → pt.zeroSized = true := by
  unfold retagTargetLive
  cases hl : ctx.localOf p with
  | none => simp
  | some l =>
    cases hs : ctx.slots[l]? with
    | none => simp [hs]
    | some st => cases st <;> simp [hs]

/-- `retagRefOk` spelled out: non-null, within the pointer width, aligned, inhabited pointee,
and not dangling into a dead local unless zero-sized. -/
theorem retagRefOk_iff (ctx : RetagCtx) (pt : RetagPointee) (p : ProvenancePtr) :
    retagRefOk ctx pt p = true ↔
      ctx.addrOf p ≠ 0 ∧ ctx.addrOf p < 2 ^ ctx.ptrBits ∧
      (∃ al, pt.align = some al ∧ ctx.addrOf p % al = 0) ∧ pt.inhabited = true ∧
      (∀ l, ctx.localOf p = some l → ctx.slots[l]? = some .dead → pt.zeroSized = true) := by
  simp only [retagRefOk, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    retagAlignOk_iff, retagTargetLive_iff, and_assoc]

/-- A retag of a dead (or missing) local fails (`DeadLocal`), for every kind. -/
theorem evalRetagPlace_dead (ctx : RetagCtx) (kind : RetagKind) (place : Place) (ty : RetagTy)
    (b : Bool) (h : ctx.slots[place.local_]? = some .dead) :
    evalRetagPlace ctx kind place ty b = false := by
  simp [evalRetagPlace, h]

/-- **`Retag(Raw)` soundness**: a successful raw retag read an initialized pointer of the place
whose address fits the pointer width. -/
theorem evalRetagPlace_raw_sound {ctx : RetagCtx} {place : Place} {ty : RetagTy} {b : Bool}
    (h : evalRetagPlace ctx .raw place ty b = true) :
    b = true ∧ ∃ p sz, readPlaceState ctx.slots place = .ok (.ptr p sz) ∧
      ctx.addrOf p < 2 ^ ctx.ptrBits := by
  unfold evalRetagPlace at h
  split at h
  · nomatch h
  · nomatch h
  · simp only [Bool.and_eq_true] at h
    obtain ⟨hb, hR⟩ := h
    refine ⟨hb, ?_⟩
    split at hR
    · rename_i p sz hRead
      exact ⟨p, sz, hRead, by simpa using hR⟩
    · nomatch hR

/-- Retagging a reference-holding place whose local is uninitialized fails
(`UninitializedLocal`), for every non-raw kind. -/
theorem evalRetagPlace_uninit_ref {ctx : RetagCtx} {kind : RetagKind} {place : Place}
    {ty : RetagTy} {b : Bool} (hKind : kind ≠ .raw) (hRef : ty.containsRef = true)
    (h : ctx.slots[place.local_]? = some .uninit) :
    evalRetagPlace ctx kind place ty b = false := by
  unfold evalRetagPlace
  rw [h]
  cases kind with
  | raw => exact absurd rfl hKind
  | _ =>
    simp only [hRef, Bool.not_true, Bool.false_or, slotStateToFieldSlot]
    cases hp : place.projection with
    | nil => simp [projectFieldSlot, retagSlotOk, hRef]
    | cons a rest => simp [projectFieldSlot]

/-- **Reference retag soundness**: a successful non-raw retag of a place of reference type
validated an initialized pointer that is non-null, within the pointer width, aligned to its
pointee, points to an inhabited type, and does not dangle into a dead local (`A3`). -/
theorem evalRetagPlace_ref_sound {ctx : RetagCtx} {kind : RetagKind} {place : Place}
    {pt : RetagPointee} {b : Bool} (hKind : kind ≠ .raw)
    (h : evalRetagPlace ctx kind place (.ref pt) b = true) :
    ∃ st p sz, ctx.slots[place.local_]? = some st ∧ st ≠ .dead ∧
      projectFieldSlot (slotsToTrustedLocals ctx.slots) (slotStateToFieldSlot st)
        place.projection = some (.init (.ptr p sz)) ∧
      ctx.addrOf p ≠ 0 ∧ ctx.addrOf p < 2 ^ ctx.ptrBits ∧
      (∃ al, pt.align = some al ∧ ctx.addrOf p % al = 0) ∧ pt.inhabited = true ∧
      (∀ l, ctx.localOf p = some l → ctx.slots[l]? = some .dead → pt.zeroSized = true) := by
  unfold evalRetagPlace at h
  split at h
  · nomatch h
  · nomatch h
  · rename_i st hNotDead hSt
    cases kind with
    | raw => exact absurd rfl hKind
    | _ =>
      simp only [RetagTy.containsRef, Bool.not_true, Bool.false_or] at h
      split at h
      · rename_i target hT
        cases target with
        | uninit => simp [retagSlotOk, RetagTy.containsRef] at h
        | nested _ _ _ _ => simp [retagSlotOk] at h
        | init v =>
          cases v with
          | ptr p sz =>
            simp only [retagSlotOk, retagValueOk] at h
            exact ⟨st, p, sz, hSt, fun hD => hNotDead hD, hT, (retagRefOk_iff ctx pt p).mp h⟩
          | _ => simp [retagSlotOk, retagValueOk] at h
      · nomatch h

/-- The operand Trusted's `evalStmt` evaluates for `.retag` (`evalOperand (.copy place)`) agrees
with Anneal's read of the place on below-related frames: every value Anneal reads (and checks) is
the value Trusted retags. -/
theorem readPlaceState_below_evalOperand_copy {slots : List LocalSlotState}
    {locals : List LocalSlot} {place : Place} {val : Value}
    (hRel : SlotsRefine SlotBelow slots locals) (hRead : readPlaceState slots place = .ok val)
    (borrows : List BorrowEntry) (globals : List CapturedAllocation) (layouts : LayoutTable)
    (callerLocals : List LocalSlot) :
    evalOperand locals (.copy place) borrows globals layouts callerLocals = .ok val locals := by
  have hNoDeref : projectionHasDeref place.projection = false := by
    cases hD : projectionHasDeref place.projection with
    | false => rfl
    | true => simp only [readPlaceState, hD] at hRead; nomatch hRead
  obtain ⟨rootVal, hRoot, hProj⟩ := readPlaceState_below_refines hRel hRead
  simp only [evalOperand]
  split
  · rename_i restProj hp
    rw [hp] at hNoDeref
    simp [projectionHasDeref] at hNoDeref
  · simp only [hRoot, hProj]

/-- Trusted's `evalStmt` on `.retag` faults when the retagged place's local is uninitialized or
dead (its `evalOperand (.copy place)` read faults), exactly where Anneal's retag of a
reference-holding place fails too. -/
theorem evalStmt_retag_uninit_or_dead_ub (s : MachineState) (kind : RetagKind) (place : Place)
    (span : String) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (hNoDeref : projectionHasDeref place.projection = false)
    (hT : s.frame.locals[place.local_]? = some .uninit ∨
      s.frame.locals[place.local_]? = some .dead) :
    evalStmt s ⟨.retag kind place, span⟩ localDecls layouts = .fail .ub := by
  have hOp : evalOperand s.frame.locals (.copy place) s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals = .ub := by
    simp only [evalOperand]
    split
    · rename_i restProj hp
      rw [hp] at hNoDeref
      simp [projectionHasDeref] at hNoDeref
    · rcases hT with hT | hT <;> simp [hT]
  simp only [evalStmt, hOp]

/-! ### Section 2g: `CopyNonOverlapping` -/

/-- A pointer operand of `copy_nonoverlapping`: its address and the allocation id of its
provenance (`none` without provenance). -/
structure CopyPtr : Type where
  addr : Nat
  allocId : Option Nat

/-- The checks `eval_copy_nonoverlapping` performs before any memory access, for a target with
`ptrBits`-bit pointers (`max_usize = 2^ptrBits - 1`, `max_object_size = isize::MAX`):
1. the count and both addresses are valid `usize` / pointer bit patterns (never truncated);
2. even when the byte length is `0` (`count = 0` or a ZST), both pointers are non-null and
   aligned to the element type;
3. `count * elemSize ≤ isize::MAX` (`CopyLengthOverflow`) and neither range wraps the address
   space (`PointerRangeOverflow`);
4. a non-empty copy between pointers of the same allocation does not overlap
   (`CopyNonOverlappingOverlap`), i.e. Trusted's `rangesDisjoint` holds. -/
def copyNonOverlappingChecks (ptrBits : Nat) (src dst : CopyPtr) (count elemSize elemAlign : Nat) :
    Bool :=
  let maxUsize := 2 ^ ptrBits - 1
  let byteLen := count * elemSize
  decide (count ≤ maxUsize) && decide (src.addr ≤ maxUsize) && decide (dst.addr ≤ maxUsize) &&
    (src.addr != 0) && (dst.addr != 0) &&
    isAlignedOffset src.addr elemAlign && isAlignedOffset dst.addr elemAlign &&
    decide (byteLen ≤ 2 ^ (ptrBits - 1) - 1) &&
    decide (src.addr + byteLen ≤ maxUsize) && decide (dst.addr + byteLen ≤ maxUsize) &&
    (count == 0 || byteLen == 0 || src.allocId != dst.allocId ||
      rangesDisjoint src.addr byteLen dst.addr byteLen)

/-- Trusted's `rangesDisjoint` spelled out. -/
theorem rangesDisjoint_iff (s₁ l₁ s₂ l₂ : Nat) :
    rangesDisjoint s₁ l₁ s₂ l₂ = true ↔ s₁ + l₁ ≤ s₂ ∨ s₂ + l₂ ≤ s₁ := by
  simp [rangesDisjoint, Nat.ble_eq]

/-- **Overlap is exactly the failure of Trusted's `rangesDisjoint`**: `eval_copy_nonoverlapping`'s
overlap test `src < dst + len ∧ dst < src + len` holds iff `rangesDisjoint src len dst len` is
false. -/
theorem copyOverlap_iff_not_rangesDisjoint (src dst len : Nat) :
    (src < dst + len ∧ dst < src + len) ↔ rangesDisjoint src len dst len = false := by
  have h := rangesDisjoint_iff src len dst len
  constructor
  · rintro ⟨h1, h2⟩
    cases hR : rangesDisjoint src len dst len with
    | false => rfl
    | true => rcases h.mp hR with h3 | h3 <;> omega
  · intro hR
    have : ¬ (src + len ≤ dst ∨ dst + len ≤ src) := fun h' => by rw [h.mpr h'] at hR; nomatch hR
    omega

/-- Inversion of `copyNonOverlappingChecks`. -/
theorem copyNonOverlappingChecks_eq_true {ptrBits : Nat} {src dst : CopyPtr}
    {count elemSize elemAlign : Nat}
    (h : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign = true) :
    count ≤ 2 ^ ptrBits - 1 ∧ src.addr ≤ 2 ^ ptrBits - 1 ∧ dst.addr ≤ 2 ^ ptrBits - 1 ∧
      src.addr ≠ 0 ∧ dst.addr ≠ 0 ∧
      isAlignedOffset src.addr elemAlign = true ∧ isAlignedOffset dst.addr elemAlign = true ∧
      count * elemSize ≤ 2 ^ (ptrBits - 1) - 1 ∧
      src.addr + count * elemSize ≤ 2 ^ ptrBits - 1 ∧
      dst.addr + count * elemSize ≤ 2 ^ ptrBits - 1 ∧
      (count = 0 ∨ count * elemSize = 0 ∨ src.allocId ≠ dst.allocId ∨
        rangesDisjoint src.addr (count * elemSize) dst.addr (count * elemSize) = true) := by
  simp only [copyNonOverlappingChecks, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
  rcases h11 with ((h | h) | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (by simp only [rangesDisjoint, Bool.or_eq_true]; exact h)))

/-- **Zero-length copies are still checked**: even with `count = 0` (or a zero-sized element),
`copy_nonoverlapping` requires non-null, aligned, in-width pointers. -/
theorem copyNonOverlappingChecks_zero_len_sound {ptrBits : Nat} {src dst : CopyPtr}
    {count elemSize elemAlign : Nat}
    (h : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign = true) :
    src.addr ≠ 0 ∧ dst.addr ≠ 0 ∧ isAlignedOffset src.addr elemAlign = true ∧
      isAlignedOffset dst.addr elemAlign = true ∧ src.addr ≤ 2 ^ ptrBits - 1 ∧
      dst.addr ≤ 2 ^ ptrBits - 1 := by
  obtain ⟨_, h2, h3, h4, h5, h6, h7, _⟩ := copyNonOverlappingChecks_eq_true h
  exact ⟨h4, h5, h6, h7, h2, h3⟩

/-- A null pointer is rejected even for a zero-length copy (`NullPointerAccess`). -/
theorem copyNonOverlappingChecks_null_src (ptrBits : Nat) (dst : CopyPtr) (allocId : Option Nat)
    (count elemSize elemAlign : Nat) :
    copyNonOverlappingChecks ptrBits ⟨0, allocId⟩ dst count elemSize elemAlign = false := by
  simp [copyNonOverlappingChecks]

/-- **Agreement with Trusted's `rangesDisjoint`**: a successful non-empty copy within one
allocation copies between byte ranges that Trusted's `rangesDisjoint` accepts. -/
theorem copyNonOverlappingChecks_disjoint {ptrBits : Nat} {src dst : CopyPtr}
    {count elemSize elemAlign : Nat}
    (h : copyNonOverlappingChecks ptrBits src dst count elemSize elemAlign = true)
    (hLen : 0 < count * elemSize) (hSame : src.allocId = dst.allocId) :
    rangesDisjoint src.addr (count * elemSize) dst.addr (count * elemSize) = true := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, h11⟩ := copyNonOverlappingChecks_eq_true h
  rcases h11 with h | h | h | h
  · subst h; simp at hLen
  · omega
  · exact absurd hSame h
  · exact h

/-- **Agreement with Trusted's zero-count `copyNonOverlapping`**: once its operands are
evaluated, Trusted's copy of `0` elements is a no-op step (it never faults); Anneal's zero-count
copy is likewise a no-op after `copyNonOverlappingChecks`, so every successful Anneal zero-count
copy is matched by a Trusted step (Anneal is stricter: it also checks null/alignment/width). -/
theorem evalCopyNonOverlappingWithCount_zero (s : MachineState) (src dst : Operand)
    (localDecls : List LocalDecl) (layouts : LayoutTable) (srcVal dstVal : Value)
    (locals₃ : List LocalSlot) :
    evalCopyNonOverlappingWithCount s src dst localDecls layouts srcVal dstVal 0 locals₃ =
      .step (advanceStmt s locals₃) := rfl

/-! ### Section 2h: `ShallowInitBox`, `WrapUnsafeBinder`, and `PointerCoercion` -/

/-- Anneal's pointer value (`PointerValue`): an address and the allocation id of its
provenance. -/
structure APtr : Type where
  addr : Nat
  provenance : Option Nat
  deriving DecidableEq

/-- A raw pointer type `*m T` over abstract pointee types `τ`. -/
structure RawPtrTy (τ : Type) : Type where
  pointee : τ
  mutable : Bool

/-- `PointerCoercionKind`. -/
inductive PtrCoercion : Type where
  | mutToConst : PtrCoercion
  | arrayToPointer : PtrCoercion

/-- `is_valid_pointer_coercion`: `*mut T → *const T`, or `*m [T; N] → *m T` (same mutability);
`arrayElem` gives the element type of an array pointee. -/
def validPointerCoercion {τ : Type} [DecidableEq τ] (arrayElem : τ → Option τ) :
    PtrCoercion → RawPtrTy τ → RawPtrTy τ → Bool
  | .mutToConst, src, tgt => src.mutable && !tgt.mutable && decide (src.pointee = tgt.pointee)
  | .arrayToPointer, src, tgt =>
    decide (src.mutable = tgt.mutable) && decide (arrayElem src.pointee = some tgt.pointee)

/-- `PointerCoercion` (`eval_cast_in_state`): a valid coercion keeps the address (masked to the
pointer width) and the provenance and retypes the pointer. -/
def evalPointerCoercion {τ : Type} [DecidableEq τ] (arrayElem : τ → Option τ) (ptrBits : Nat)
    (c : PtrCoercion) (src tgt : RawPtrTy τ) (p : APtr) : Option (APtr × RawPtrTy τ) :=
  if validPointerCoercion arrayElem c src tgt then
    some (⟨p.addr % 2 ^ ptrBits, p.provenance⟩, tgt)
  else none

/-- **`PointerCoercion` never gains mutability**: a valid coercion to a mutable pointer starts
from a mutable pointer. -/
theorem validPointerCoercion_no_mut_gain {τ : Type} [DecidableEq τ] (arrayElem : τ → Option τ)
    (c : PtrCoercion) (src tgt : RawPtrTy τ) (h : validPointerCoercion arrayElem c src tgt = true)
    (hTgt : tgt.mutable = true) : src.mutable = true := by
  cases c with
  | mutToConst =>
    simp only [validPointerCoercion, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact h.1.1
  | arrayToPointer =>
    simp only [validPointerCoercion, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [h.1]
    exact hTgt

/-- **`PointerCoercion` preserves the pointer**: the provenance is unchanged and an in-width
address is unchanged; `MutToConstPointer` keeps the pointee and drops mutability. -/
theorem evalPointerCoercion_preserves {τ : Type} [DecidableEq τ] {arrayElem : τ → Option τ}
    {ptrBits : Nat} {c : PtrCoercion} {src tgt : RawPtrTy τ} {p q : APtr} {ty : RawPtrTy τ}
    (h : evalPointerCoercion arrayElem ptrBits c src tgt p = some (q, ty))
    (hW : p.addr < 2 ^ ptrBits) :
    q = p ∧ ty = tgt ∧ (c = .mutToConst → ty.pointee = src.pointee ∧ ty.mutable = false) := by
  unfold evalPointerCoercion at h
  split at h
  · rename_i hV
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [Nat.mod_eq_of_lt hW], rfl, ?_⟩
    rintro rfl
    simp only [validPointerCoercion, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hV
    exact ⟨hV.2.symm, hV.1.2⟩
  · nomatch h

/-- `ShallowInitBox(op, T)` (`eval_shallow_init_box`): a raw-pointer operand becomes a `*mut T`
with the same address (masked to the pointer width) and provenance; any other operand is a
`TypeMismatch`. -/
def evalShallowInitBox {τ : Type} (ptrBits : Nat) (operandTy : Option (RawPtrTy τ)) (inner : τ)
    (p : APtr) : Option (APtr × RawPtrTy τ) :=
  match operandTy with
  | some _ => some (⟨p.addr % 2 ^ ptrBits, p.provenance⟩, ⟨inner, true⟩)
  | none => none

/-- **`ShallowInitBox` preservation**: the result is a mutable raw pointer to the boxed type
with the operand's provenance and (in-width) address. -/
theorem evalShallowInitBox_preserves {τ : Type} {ptrBits : Nat} {operandTy : Option (RawPtrTy τ)}
    {inner : τ} {p q : APtr} {ty : RawPtrTy τ}
    (h : evalShallowInitBox ptrBits operandTy inner p = some (q, ty)) :
    operandTy.isSome = true ∧ ty = ⟨inner, true⟩ ∧ q.provenance = p.provenance ∧
      q.addr < 2 ^ ptrBits ∧ (p.addr < 2 ^ ptrBits → q = p) := by
  unfold evalShallowInitBox at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, Nat.mod_lt _ (Nat.two_pow_pos _), fun hW => by
      simp [Nat.mod_eq_of_lt hW]⟩
  · nomatch h

/-- `WrapUnsafeBinder(op, ty)` (`eval_wrap_unsafe_binder`): the operand must be well formed
(`check_value_well_formed`); it is returned unchanged when `ty` is the operand type, and
otherwise wrapped as the single field of the struct `ty`, whose `scalar_valid_range` (if any,
with the field's bit width) it must satisfy. -/
def evalWrapUnsafeBinder (wf : Value → Bool) (wraps : Bool)
    (range? : Option (ScalarValidRange × Nat)) (v : Value) : Option Value :=
  if !wf v then none
  else if !wraps then some v
  else
    match range?, v with
    | none, _ => some (.aggregate 0 [v])
    | some (r, w), .scalar sc => if r.contains sc.bits w then some (.aggregate 0 [v]) else none
    | some _, _ => none

/-- **`WrapUnsafeBinder` preservation**: the result is the operand itself or the single-field
wrapper whose field `0` reads back exactly the operand; the operand is well formed. -/
theorem evalWrapUnsafeBinder_preserves {wf : Value → Bool} {wraps : Bool}
    {range? : Option (ScalarValidRange × Nat)} {v out : Value}
    (h : evalWrapUnsafeBinder wf wraps range? v = some out) (locals : List LocalSlot) (ty : Ty) :
    wf v = true ∧
      ((wraps = false ∧ out = v) ∨
        (wraps = true ∧ out = .aggregate 0 [v] ∧
          evalValueProjRead locals out [.field 0 ty] = .ok v)) := by
  unfold evalWrapUnsafeBinder at h
  cases hW : wf v with
  | false => simp [hW] at h
  | true =>
    refine ⟨rfl, ?_⟩
    cases wraps with
    | false =>
      simp only [hW, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Option.some.injEq] at h
      exact Or.inl ⟨rfl, h.symm⟩
    | true =>
      simp only [hW, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      have hOut : out = .aggregate 0 [v] := by
        split at h
        · exact (Option.some.inj h).symm
        · split at h
          · exact (Option.some.inj h).symm
          · nomatch h
        · nomatch h
      subst hOut
      exact Or.inr ⟨rfl, rfl, rfl⟩

/-- **`WrapUnsafeBinder` enforces the wrapper's niche**: a scalar outside the wrapper struct's
`scalar_valid_range` (e.g. `0` for a `NonZero`-like wrapper) is rejected. -/
theorem evalWrapUnsafeBinder_rejects_niche {wf : Value → Bool} {r : ScalarValidRange} {w : Nat}
    {sc : ScalarInt} (hOut : r.contains sc.bits w = false) :
    evalWrapUnsafeBinder wf true (some (r, w)) (.scalar sc) = none := by
  unfold evalWrapUnsafeBinder
  cases wf (.scalar sc) <;> simp [hOut]

/-- **Operand evaluation refines Trusted on below-related frames**: every successful Anneal
operand evaluation (`copy`, `move`, or a constant) is matched by Trusted's `evalOperand` with the
same value, and the frames stay related. -/
theorem evalOperandState_below_refines (slots slots' : List LocalSlotState)
    (locals : List LocalSlot) (op : Operand) (val : Value) (borrows : List BorrowEntry)
    (globals : List CapturedAllocation) (layouts : LayoutTable) (callerLocals : List LocalSlot)
    (hRel : SlotsRefine SlotBelow slots locals) (hNoDeref : OperandNonDeref op)
    (hEval : evalOperandState slots op layouts globals = (.ok val, slots')) :
    ∃ locals', evalOperand locals op borrows globals layouts callerLocals = .ok val locals' ∧
      SlotsRefine SlotBelow slots' locals' := by
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
        dsimp only [evalOperand]
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
        dsimp only [evalOperand]
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
        dsimp only [evalOperand]
        rw [hVal]
        dsimp only
        rw [hC]
  | copy place =>
    unfold evalOperandState at hEval
    dsimp only at hEval
    injection hEval with hRead hSlots
    subst hSlots
    exact ⟨locals, readPlaceState_below_evalOperand_copy hRel hRead borrows globals layouts
      callerLocals, hRel⟩
  | move place =>
    rcases place with ⟨loc, proj⟩
    unfold evalOperandState movePlaceState at hEval
    dsimp only at hEval
    cases hRead : readPlaceState slots ⟨loc, proj⟩ with
    | ub => rw [hRead] at hEval; nomatch hEval
    | unsupported => rw [hRead] at hEval; nomatch hEval
    | ok outVal =>
      rw [hRead] at hEval
      dsimp only at hEval
      obtain ⟨rootVal, hGetT, hTRead⟩ := readPlaceState_below_refines hRel hRead
      cases proj with
      | nil =>
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        unfold readProjectedValue at hTRead
        injection hTRead with hRootEq
        subst hRootEq
        have hLtT : loc < locals.length := by
          simp only [get?_eq_getElem?] at hGetT
          exact (List.getElem?_eq_some_iff.mp hGetT).1
        have hSetT : set? locals loc .uninit = .some (locals.set loc .uninit) :=
          set?_eq_some_iff.mpr ⟨hLtT, rfl⟩
        refine ⟨locals.set loc .uninit, ?_,
          SlotsRefine.set (R := SlotBelow) (a := .uninit) (t := .uninit) trivial loc hRel⟩
        dsimp only [evalOperand]
        rw [hGetT]
        dsimp only
        rw [hSetT]
      | cons p rest =>
        injection hEval with hRes hSlots
        injection hRes with hV
        subst hV hSlots
        refine ⟨locals, ?_, hRel⟩
        cases p with
        | deref => exact False.elim (hNoDeref rest rfl)
        | _ =>
          dsimp only [evalOperand]
          rw [hGetT]
          dsimp only
          rw [hTRead]

/-! ## Section 3: Multi-block terminator CFG execution -/

/-- `SwitchTargets` of a lowered `SwitchInt` (`ir.rs`): parallel value/target lists and the
`otherwise` target. -/
structure LSwitchTargets : Type where
  values : List Nat
  targets : List Nat
  otherwise : Nat

/-- `SwitchTargets::target_for_value`: the target of the first matching value, else
`otherwise` (`zip` stops at the shorter list). -/
def targetForValue : List Nat → List Nat → Nat → Nat → Nat
  | x :: xs, t :: ts, otherwise, v => if v = x then t else targetForValue xs ts otherwise v
  | _, _, otherwise, _ => otherwise

/-- **`evalSwitchTargets_eq_lookupSwitchTarget`**: Anneal's switch target selection agrees
exactly with Trusted's `lookupSwitchTarget` on the zipped branch list. -/
theorem evalSwitchTargets_eq_lookupSwitchTarget :
    ∀ (values targets : List Nat) (otherwise v : Nat),
      targetForValue values targets otherwise v =
        lookupSwitchTarget v (values.zip targets) otherwise
  | [], _, _, _ => by cases ‹List Nat› <;> rfl
  | _ :: _, [], _, _ => rfl
  | x :: xs, t :: ts, otherwise, v => by
    simp only [targetForValue, List.zip_cons_cons, lookupSwitchTarget]
    rcases beq_cases v x with ⟨hB, hE⟩ | ⟨hB, hE⟩
    · rw [hB]
      simp [hE]
    · rw [hB]
      simp only [hE, ↓reduceIte]
      exact evalSwitchTargets_eq_lookupSwitchTarget xs ts otherwise v

/-- A lowered terminator (`LoweredTerminator` in `cfg.rs`). `SwitchInt` carries the byte width
of its discriminant type; `Assert` carries the places its panic message reads; `Call` carries the
type of its destination. -/
inductive LTerminator : Type where
  | goto (target : Nat) : LTerminator
  | switchInt (discr : Operand) (discrBytes : Nat) (targets : LSwitchTargets) : LTerminator
  | return_ : LTerminator
  | unreachable : LTerminator
  | drop (place : Place) (target : Nat) (unwind : UnwindAction) : LTerminator
  | assert (cond : Operand) (expected : Bool) (msg : List Place) (target : Nat)
      (unwind : UnwindAction) : LTerminator
  | call (func : Operand) (args : List Operand) (destination : Place) (destTy : Ty)
      (target : Option Nat) (unwind : UnwindAction) : LTerminator
  | unwindResume : LTerminator
  | unwindTerminate : LTerminator

/-- A lowered basic block (`LoweredBasicBlock`): its statements, terminator, and whether it is a
cleanup block. -/
structure LBlock : Type where
  statements : List Statement
  terminator : LTerminator
  isCleanup : Bool

/-- A lowered body's basic blocks (`LoweredBody`). -/
structure LBody : Type where
  blocks : List LBlock

/-- Outcome of a callee reported by the call handler (`CallOutcome`). -/
inductive CallOutcome : Type where
  | ret (v : Value) : CallOutcome
  | panic : CallOutcome

/-- The environment of CFG evaluation: layouts and globals for constants, the boundary
well-formedness check `check_value_well_formed` (with the inhabitedness of the return type
folded into `retOk`), the place-access check of `Drop`/`Call` destinations
(`check_place_access`), the arity function of shell writes, the statement evaluator
(`eval_lowered_statement` over a block's statements), and the call handler (`none`:
`UnsupportedCall`). -/
structure CfgEnv : Type where
  layouts : LayoutTable
  globals : List CapturedAllocation
  wf : Value → Bool
  retOk : Value → Bool
  placeAccessOk : List LocalSlotState → Place → Bool
  arityOf : Ty → VariantIdx → Bool → Option Nat
  evalStmts : List Statement → List LocalSlotState → Option (List LocalSlotState)
  handler : Option (Nat → Value → List Value → Option CallOutcome)

/-- The next control-flow step after a terminator (`CfgStep`): continue at a block with the new
frame and unwinding state (`some bb` while unwinding a panic raised in `bb`), or finish. -/
inductive CfgStep : Type where
  | goto (bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) : CfgStep
  | returned (v : Value) : CfgStep
  | panicked (bb : Nat) : CfgStep
  | terminated (bb : Nat) : CfgStep

/-- `check_unwind_action`: `Unreachable`/`Terminate` are always allowed; `Continue` and
`Cleanup` only outside cleanup blocks, and a `Cleanup` target must be an existing cleanup
block. -/
def unwindActionOk (body : LBody) (inCleanup : Bool) : UnwindAction → Bool
  | .unreachable => true
  | .terminate => true
  | .continue_ => !inCleanup
  | .cleanup t =>
    !inCleanup &&
      (match body.blocks[t]? with
       | some b => b.isCleanup
       | none => false)

/-- The edge check of every `Goto` step: the target exists and is a cleanup block iff the
evaluation is (now) unwinding (`InvalidBlock` / `InvalidEdge`). -/
def cfgGoto (body : LBody) (next : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) :
    Option CfgStep :=
  match body.blocks[next]? with
  | some nb => if nb.isCleanup = unwinding.isSome then some (.goto next slots unwinding) else none
  | none => none

/-- `start_panic` for a panic raised in block `bb` under the unwind action `unwind`:
`Unreachable` is undefined behavior; `Terminate` aborts; `Continue` unwinds out of the body;
`Cleanup(t)` starts unwinding at `t`; unwinding again while unwinding is `InvalidUnwind`. -/
def startPanic (body : LBody) (bb : Nat) (unwind : UnwindAction) (slots : List LocalSlotState)
    (unwinding : Option Nat) : Option CfgStep :=
  match unwind with
  | .unreachable => none
  | .terminate => some (.terminated bb)
  | .continue_ => if unwinding.isSome then none else some (.panicked bb)
  | .cleanup t => if unwinding.isSome then none else cfgGoto body t slots (some bb)

/-- Evaluates a list of operands left to right (`eval_operand` for call arguments). -/
def evalOperandsState (layouts : LayoutTable) (globals : List CapturedAllocation) :
    List LocalSlotState → List Operand → Option (List Value × List LocalSlotState)
  | slots, [] => some ([], slots)
  | slots, op :: ops =>
    match evalOperandState slots op layouts globals with
    | (.ok v, slots') =>
      match evalOperandsState layouts globals slots' ops with
      | some (vs, slots'') => some (v :: vs, slots'')
      | none => none
    | _ => none

/-- `eval_lowered_terminator`: evaluates the terminator of block `bb` (whose statements have
run) in `slots` and unwinding mode `unwinding`. The block must exist and be a cleanup block iff
the evaluation is unwinding. `none` is an error (undefined behavior, an ill-formed body, or an
unsupported call). -/
def evalLoweredTerminator (env : CfgEnv) (body : LBody) (bb : Nat)
    (slots : List LocalSlotState) (unwinding : Option Nat) : Option CfgStep :=
  match body.blocks[bb]? with
  | none => none
  | some block =>
    if block.isCleanup ≠ unwinding.isSome then none else
    match block.terminator with
    | .goto t => cfgGoto body t slots unwinding
    | .switchInt discr bytes targets =>
      if targets.values.length = targets.targets.length ∧ targets.values.Nodup ∧
          ∀ x ∈ targets.values, x < 2 ^ (8 * bytes) then
        match evalOperandState slots discr env.layouts env.globals with
        | (.ok (.scalar sc), slots') =>
          if sc.sizeBytes = bytes ∧ sc.bits < 2 ^ (8 * bytes) then
            cfgGoto body (targetForValue targets.values targets.targets targets.otherwise sc.bits)
              slots' unwinding
          else none
        | _ => none
      else none
    | .return_ =>
      if block.isCleanup then none else
      match readPlaceState slots ⟨0, []⟩ with
      | .ok v => if env.retOk v then some (.returned v) else none
      | _ => none
    | .unreachable => none
    | .drop place target unwind =>
      if env.placeAccessOk slots place ∧ unwindActionOk body block.isCleanup unwind then
        cfgGoto body target slots unwinding
      else none
    | .assert cond expected msg target unwind =>
      match evalOperandState slots cond env.layouts env.globals with
      | (.ok (.scalar sc), slots') =>
        if sc.sizeBytes = 1 ∧ sc.bits ≤ 1 then
          if ((sc.bits == 1) == expected) = true then
            if unwindActionOk body block.isCleanup unwind then cfgGoto body target slots' unwinding
            else none
          else
            if msg.all (fun p => match readPlaceState slots' p with
                | .ok v => env.wf v
                | _ => false) then
              startPanic body bb unwind slots' unwinding
            else none
        else none
      | _ => none
    | .call func args destination destTy target unwind =>
      match evalOperandState slots func env.layouts env.globals with
      | (.ok fv, slots1) =>
        if !env.wf fv then none else
        match evalOperandsState env.layouts env.globals slots1 args with
        | some (avs, slots2) =>
          if !(avs.all env.wf && env.placeAccessOk slots2 destination) then none else
          match env.handler with
          | none => none
          | some h =>
            match h bb fv avs with
            | some (.ret rv) =>
              if !unwindActionOk body block.isCleanup unwind then none else
              match target with
              | none => none
              | some t =>
                if !env.wf rv then none else
                match writePlaceState env.arityOf slots2 destination destTy rv with
                | .ok slots3 => cfgGoto body t slots3 unwinding
                | _ => none
            | some .panic => startPanic body bb unwind slots2 unwinding
            | none => none
        | none => none
      | _ => none
    | .unwindResume =>
      match unwinding with
      | some pbb => some (.panicked pbb)
      | none => none
    | .unwindTerminate =>
      match unwinding with
      | some pbb => some (.terminated pbb)
      | none => none

/-- Outcome of a fuel-bounded CFG evaluation (`CfgEvalOutcome`). -/
inductive CfgOutcome : Type where
  | returned (v : Value) : CfgOutcome
  | panicked (bb : Nat) : CfgOutcome
  | terminated (bb : Nat) : CfgOutcome
  | outOfFuel (bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) : CfgOutcome

/-- `eval_cfg_in_state`'s loop: each unit of fuel runs one block's statements and then its
terminator; fuel `0` stops at the block that would run next. -/
def runLoweredCfgSteps (env : CfgEnv) (body : LBody) :
    Nat → Nat → List LocalSlotState → Option Nat → Option CfgOutcome
  | 0, bb, slots, unwinding => some (.outOfFuel bb slots unwinding)
  | fuel + 1, bb, slots, unwinding =>
    match body.blocks[bb]? with
    | none => none
    | some block =>
      match env.evalStmts block.statements slots with
      | none => none
      | some slots1 =>
        match evalLoweredTerminator env body bb slots1 unwinding with
        | none => none
        | some (.goto next slots' unwinding') =>
          runLoweredCfgSteps env body fuel next slots' unwinding'
        | some (.returned v) => some (.returned v)
        | some (.panicked b) => some (.panicked b)
        | some (.terminated b) => some (.terminated b)

/-- **Zero fuel**: no block runs; the evaluation stops where it is. -/
theorem runLoweredCfgSteps_zero_fuel (env : CfgEnv) (body : LBody) (bb : Nat)
    (slots : List LocalSlotState) (unwinding : Option Nat) :
    runLoweredCfgSteps env body 0 bb slots unwinding = some (.outOfFuel bb slots unwinding) := rfl

/-- **Fuel composition**: running with `n + k` fuel is running with `n` fuel and, if that ran out
of fuel, continuing with `k` more from where it stopped. -/
theorem runLoweredCfgSteps_add_fuel (env : CfgEnv) (body : LBody) :
    ∀ (n k bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat),
      runLoweredCfgSteps env body (n + k) bb slots unwinding =
        match runLoweredCfgSteps env body n bb slots unwinding with
        | some (.outOfFuel bb' slots' unwinding') =>
          runLoweredCfgSteps env body k bb' slots' unwinding'
        | r => r := by
  intro n
  induction n with
  | zero => intro k bb slots unwinding; simp [runLoweredCfgSteps]
  | succ n ih =>
    intro k bb slots unwinding
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [runLoweredCfgSteps]
    cases body.blocks[bb]? with
    | none => rfl
    | some block =>
      simp only
      cases env.evalStmts block.statements slots with
      | none => rfl
      | some slots1 =>
        simp only
        cases evalLoweredTerminator env body bb slots1 unwinding with
        | none => rfl
        | some step =>
          cases step with
          | goto next slots' unwinding' => exact ih k next slots' unwinding'
          | returned v => rfl
          | panicked b => rfl
          | terminated b => rfl

/-- **Fuel monotonicity**: once an evaluation finishes (returns, panics, or terminates), more
fuel gives the same outcome. -/
theorem runLoweredCfgSteps_mono (env : CfgEnv) (body : LBody) {n k bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {o : CfgOutcome}
    (h : runLoweredCfgSteps env body n bb slots unwinding = some o)
    (hDone : ∀ bb' slots' unwinding', o ≠ .outOfFuel bb' slots' unwinding') :
    runLoweredCfgSteps env body (n + k) bb slots unwinding = some o := by
  rw [runLoweredCfgSteps_add_fuel, h]
  cases o with
  | outOfFuel bb' slots' unwinding' => exact absurd rfl (hDone bb' slots' unwinding')
  | _ => rfl

/-! ### Section 3b: Refinement of Trusted's `evalTerminator` / `stepMirFn` -/

/-- The Trusted terminator a lowered terminator corresponds to (`Assert`'s panic message and
`Call`'s destination type are not part of Trusted's syntax). -/
def LTerminator.toTrusted : LTerminator → TerminatorKind
  | .goto t => .goto t
  | .switchInt discr _ targets =>
    .switchInt discr ⟨targets.values.zip targets.targets, targets.otherwise⟩
  | .return_ => .return_
  | .unreachable => .unreachable
  | .drop place t u => .drop place t u
  | .assert cond expected _ t u => .assert cond expected t u
  | .call func args dest _ t u => .call func args dest t u
  | .unwindResume => .unwindResume
  | .unwindTerminate => .unwindTerminate

/-- The terminators covered by the step refinement: all but `Call` (Anneal abstracts callees by a
handler while Trusted links captured callee bodies) and `Drop` (whose divergence is
`evalLoweredTerminator_drop_bare_divergence`); operands must not start with a `Deref`. -/
def LTerminator.Refinable : LTerminator → Prop
  | .goto _ => True
  | .switchInt discr _ _ => OperandNonDeref discr
  | .return_ => True
  | .unreachable => True
  | .drop _ _ _ => False
  | .assert cond _ _ _ _ => OperandNonDeref cond
  | .call .. => False
  | .unwindResume => True
  | .unwindTerminate => True

/-- A lowered body corresponds to a captured Trusted body: a runtime phase, the same layouts,
the same blocks (statement-free on both sides, so a block is its terminator), the same
terminators and cleanup flags, and refinable terminators. -/
structure BodyCorr (env : CfgEnv) (body : LBody) (cm : CapturedMir) : Prop where
  phase : ∀ tag, cm.phase ≠ .other tag
  layouts : cm.layouts = env.layouts
  block : ∀ (i : Nat) (b : LBlock), body.blocks[i]? = some b →
    b.statements = [] ∧ b.terminator.Refinable ∧
      ∃ span, cm.basicBlocks[i]? = some ⟨[], ⟨b.terminator.toTrusted, span⟩, b.isCleanup⟩

/-- **`StateCorr`**: the lowered state at block `bb` with frame `slots` corresponds to the Trusted
machine state `s`: `s` is at the start of `bb` (its terminator, since blocks are statement-free),
Anneal's frame is below Trusted's (`SlotBelow`: every Anneal read is a Trusted read), and `s`
runs the root body (no active callee, empty call stack) with Anneal's globals. -/
structure StateCorr (env : CfgEnv) (bb : Nat) (slots : List LocalSlotState) (s : MachineState) :
    Prop where
  block : s.frame.blockIdx = bb
  stmt : s.frame.stmtIdx = 0
  slots : SlotsRefine SlotBelow slots s.frame.locals
  callee : s.memory.activeCallee = none
  stack : s.memory.callStack = []
  globals : s.memory.globals = env.globals

/-- A Trusted transition that continues at `s'` (silently, or emitting a branch event). -/
def TrustedStep (node : MirStepNode) (s' : MachineState) : Prop :=
  node = .step s' ∨ ∃ tag, node = .emitStep (.event tag) s'

/-- Under `BodyCorr`/`StateCorr`, Trusted's `stepMirFn` at `s` evaluates the corresponding
terminator. -/
theorem stepMirFn_eq_evalTerminator {env : CfgEnv} {body : LBody} {cm : CapturedMir} {bb : Nat}
    {slots : List LocalSlotState} {s : MachineState} {b : LBlock} (hBody : BodyCorr env body cm)
    (hCorr : StateCorr env bb slots s) (hb : body.blocks[bb]? = some b) :
    ∃ span, stepMirFn cm s = evalTerminator s ⟨b.terminator.toTrusted, span⟩ (some cm) := by
  obtain ⟨_, _, span, hcm⟩ := hBody.block bb b hb
  refine ⟨span, ?_⟩
  unfold stepMirFn
  simp only [hCorr.callee, Option.getD_none]
  split
  · rename_i tag hP
    exact absurd hP (hBody.phase tag)
  · simp only [get?_eq_getElem?, hCorr.block, hcm, hCorr.stmt, List.getElem?_nil,
      length_eq_list_length, List.length_nil, BEq.rfl, ↓reduceIte]

/-- Inversion of `cfgGoto`. -/
theorem cfgGoto_eq_some {body : LBody} {t : Nat} {slots : List LocalSlotState}
    {unwinding : Option Nat} {step : CfgStep} (h : cfgGoto body t slots unwinding = some step) :
    step = .goto t slots unwinding := by
  unfold cfgGoto at h
  split at h
  · split at h
    · exact (Option.some.inj h).symm
    · nomatch h
  · nomatch h

/-- The Trusted successor of a jump to `t` with frame `locals'` stays in correspondence. -/
theorem StateCorr.jump {env : CfgEnv} {bb : Nat} {slots slots' : List LocalSlotState}
    {s : MachineState} (hCorr : StateCorr env bb slots s) (t : Nat) (locals' : List LocalSlot)
    (hRel : SlotsRefine SlotBelow slots' locals') :
    StateCorr env t slots' { s with frame := { blockIdx := t, stmtIdx := 0, locals := locals' } } :=
  ⟨rfl, rfl, hRel, hCorr.callee, hCorr.stack, hCorr.globals⟩

/-- **`evalLoweredTerminator_refines_trusted`**: under `BodyCorr` and `StateCorr`, every
successful lowered terminator step is matched by Trusted's `stepMirFn`: a jump is a Trusted
`.step`/`.emitStep` to a corresponding state (preserving `StateCorr` on `Goto`, `SwitchInt`,
`Assert`-pass, and `Assert` cleanup jumps), `Return` is Trusted's `.retNormal` of the same value,
and a panic that unwinds out of the body (or aborts) is Trusted's `.panic` (or `.abort`) outcome.
In particular Trusted never faults with `.ub` where Anneal succeeds. -/
theorem evalLoweredTerminator_refines_trusted {env : CfgEnv} {body : LBody} {cm : CapturedMir}
    {bb : Nat} {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState}
    {step : CfgStep} (hBody : BodyCorr env body cm) (hCorr : StateCorr env bb slots s)
    (h : evalLoweredTerminator env body bb slots unwinding = some step) :
    match step with
    | .goto next slots' _ => ∃ s', TrustedStep (stepMirFn cm s) s' ∧ StateCorr env next slots' s'
    | .returned v => stepMirFn cm s = .retNormal v s.memory
    | .panicked _ => stepMirFn cm s = .retOutcome .panic
    | .terminated _ => stepMirFn cm s = .retOutcome .abort := by
  unfold evalLoweredTerminator at h
  cases hb : body.blocks[bb]? with
  | none => rw [hb] at h; nomatch h
  | some b =>
    rw [hb] at h
    simp only at h
    obtain ⟨_, hRef, _⟩ := hBody.block bb b hb
    obtain ⟨span, hStep⟩ := stepMirFn_eq_evalTerminator hBody hCorr hb
    rw [hStep]
    split at h
    · nomatch h
    · rename_i hClean
      cases hT : b.terminator with
      | goto t =>
        rw [hT] at h
        simp only at h
        obtain rfl := cfgGoto_eq_some h
        refine ⟨_, Or.inl ?_, hCorr.jump t s.frame.locals hCorr.slots⟩
        simp only [LTerminator.toTrusted, evalTerminator]
      | switchInt discr bytes targets =>
        rw [hT] at hRef
        rw [hT] at h
        simp only at h
        split at h
        · split at h
          · rename_i sc slots' hOp
            split at h
            · obtain rfl := cfgGoto_eq_some h
              obtain ⟨locals', hTOp, hRel⟩ := evalOperandState_below_refines slots slots'
                s.frame.locals discr (.scalar sc) s.memory.borrows env.globals env.layouts
                s.memory.callerLocals hCorr.slots hRef hOp
              refine ⟨_, Or.inr ⟨sc.bits, ?_⟩, hCorr.jump _ locals' hRel⟩
              simp only [LTerminator.toTrusted, evalTerminator, hBody.layouts, hCorr.globals,
                hTOp, evalSwitchTargets_eq_lookupSwitchTarget]
            · nomatch h
          · nomatch h
        · nomatch h
      | return_ =>
        rw [hT] at h
        simp only at h
        split at h
        · nomatch h
        · split at h
          · rename_i v hRead
            split at h
            · cases h
              obtain ⟨rootVal, hRoot, hProj⟩ := readPlaceState_below_refines hCorr.slots hRead
              simp only [readProjectedValue, ProjReadResult.ok.injEq] at hProj
              subst hProj
              simp only [LTerminator.toTrusted, evalTerminator, hRoot, hCorr.stack]
            · nomatch h
          · nomatch h
      | unreachable => rw [hT] at h; nomatch h
      | drop place t u => rw [hT] at hRef; exact absurd hRef id
      | assert cond expected msg t u =>
        rw [hT] at hRef
        rw [hT] at h
        simp only at h
        split at h
        · rename_i sc slots' hOp
          obtain ⟨locals', hTOp, hRel⟩ := evalOperandState_below_refines slots slots'
            s.frame.locals cond (.scalar sc) s.memory.borrows env.globals env.layouts
            s.memory.callerLocals hCorr.slots hRef hOp
          simp only [LTerminator.toTrusted, evalTerminator, hBody.layouts, hCorr.globals, hTOp]
          split at h
          · rename_i hBool
            obtain ⟨bits, sz⟩ := sc
            obtain ⟨_, hLe⟩ := hBool
            have hB01 : bits = 0 ∨ bits = 1 := by simp only at hLe; omega
            rcases hB01 with rfl | rfl <;> cases expected
            · -- `false` asserted to be `false`: the assertion passes
              rw [show (((0 : Nat) == 1) == false) = true from rfl] at h
              simp only [↓reduceIte] at h
              dsimp only
              split at h
              · obtain rfl := cfgGoto_eq_some h
                exact ⟨_, Or.inl rfl, hCorr.jump t locals' hRel⟩
              · nomatch h
            · -- `false` asserted to be `true`: the assertion fails
              rw [show (((0 : Nat) == 1) == true) = false from rfl] at h
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              dsimp only
              split at h
              · cases u with
                | unreachable => simp [startPanic] at h
                | terminate =>
                  simp only [startPanic, Option.some.injEq] at h
                  subst h
                  simp [applyUnwindAction]
                | continue_ =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · cases h
                    simp [applyUnwindAction, hCorr.stack]
                | cleanup c =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · obtain rfl := cfgGoto_eq_some h
                    exact ⟨{ s with frame := { blockIdx := c, stmtIdx := 0, locals := locals' } },
                      Or.inl rfl, hCorr.jump c locals' hRel⟩
              · nomatch h
            · -- `true` asserted to be `false`: the assertion fails
              rw [show (((1 : Nat) == 1) == false) = false from rfl] at h
              simp only [Bool.false_eq_true, ↓reduceIte] at h
              dsimp only
              split at h
              · cases u with
                | unreachable => simp [startPanic] at h
                | terminate =>
                  simp only [startPanic, Option.some.injEq] at h
                  subst h
                  simp [applyUnwindAction]
                | continue_ =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · cases h
                    simp [applyUnwindAction, hCorr.stack]
                | cleanup c =>
                  simp only [startPanic] at h
                  split at h
                  · nomatch h
                  · obtain rfl := cfgGoto_eq_some h
                    exact ⟨{ s with frame := { blockIdx := c, stmtIdx := 0, locals := locals' } },
                      Or.inl rfl, hCorr.jump c locals' hRel⟩
              · nomatch h
            · -- `true` asserted to be `true`: the assertion passes
              rw [show (((1 : Nat) == 1) == true) = true from rfl] at h
              simp only [↓reduceIte] at h
              dsimp only
              split at h
              · obtain rfl := cfgGoto_eq_some h
                exact ⟨_, Or.inl rfl, hCorr.jump t locals' hRel⟩
              · nomatch h
          · nomatch h
        · nomatch h
      | call func args dest destTy t u => rw [hT] at hRef; exact absurd hRef id
      | unwindResume =>
        rw [hT] at h
        simp only at h
        split at h
        · cases h
          simp [LTerminator.toTrusted, evalTerminator, hCorr.stack]
        · nomatch h
      | unwindTerminate =>
        rw [hT] at h
        simp only at h
        split at h
        · cases h
          simp [LTerminator.toTrusted, evalTerminator]
        · nomatch h

/-- Trusted's reflexive-transitive closure of continuing steps (`.step` / `.emitStep`) of
`stepMirFn`: a Trusted execution prefix that never faults. -/
inductive TrustedRun (cm : CapturedMir) : MachineState → MachineState → Prop where
  | refl (s : MachineState) : TrustedRun cm s s
  | step {s s' s'' : MachineState} :
      TrustedStep (stepMirFn cm s) s' → TrustedRun cm s' s'' → TrustedRun cm s s''

/-- **`runLoweredCfgSteps_refines_trusted`**: under `BodyCorr` (with the empty statement list
evaluating to the identity) and `StateCorr`, every successful fuel-bounded lowered CFG run is
matched by a fault-free Trusted execution of `stepMirFn` (equivalently `stepMirState` on
`.running` states) that reaches a corresponding state when fuel runs out, Trusted's
`.retNormal` of the same value on `Return`, and Trusted's `.panic` / `.abort` outcome when a
panic unwinds out of the body or aborts. Trusted never faults with `.ub` along the way. -/
theorem runLoweredCfgSteps_refines_trusted {env : CfgEnv} {body : LBody} {cm : CapturedMir}
    (hBody : BodyCorr env body cm) (hStmts : ∀ slots, env.evalStmts [] slots = some slots) :
    ∀ (fuel bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) (s : MachineState)
      (o : CfgOutcome), StateCorr env bb slots s →
      runLoweredCfgSteps env body fuel bb slots unwinding = some o →
      match o with
      | .outOfFuel bb' slots' _ => ∃ s', TrustedRun cm s s' ∧ StateCorr env bb' slots' s'
      | .returned v => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retNormal v s'.memory
      | .panicked _ => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retOutcome .panic
      | .terminated _ => ∃ s', TrustedRun cm s s' ∧ stepMirFn cm s' = .retOutcome .abort := by
  intro fuel
  induction fuel with
  | zero =>
    intro bb slots unwinding s o hCorr h
    simp only [runLoweredCfgSteps, Option.some.injEq] at h
    subst h
    exact ⟨s, .refl s, hCorr⟩
  | succ fuel ih =>
    intro bb slots unwinding s o hCorr h
    simp only [runLoweredCfgSteps] at h
    cases hb : body.blocks[bb]? with
    | none => rw [hb] at h; nomatch h
    | some block =>
      rw [hb] at h
      simp only at h
      obtain ⟨hNil, _, _⟩ := hBody.block bb block hb
      rw [hNil, hStmts] at h
      simp only at h
      cases hT : evalLoweredTerminator env body bb slots unwinding with
      | none => rw [hT] at h; nomatch h
      | some step =>
        rw [hT] at h
        have hRef := evalLoweredTerminator_refines_trusted hBody hCorr hT
        cases step with
        | goto next slots' unwinding' =>
          simp only at h hRef
          obtain ⟨s', hStep, hCorr'⟩ := hRef
          have hRest := ih next slots' unwinding' s' o hCorr' h
          cases o with
          | outOfFuel bb' slots'' _ =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
          | returned v =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
          | panicked b =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
          | terminated b =>
            obtain ⟨s'', hRun, hC⟩ := hRest
            exact ⟨s'', .step hStep hRun, hC⟩
        | returned v =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨s, .refl s, hRef⟩
        | panicked b =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨s, .refl s, hRef⟩
        | terminated b =>
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨s, .refl s, hRef⟩

/-- Trusted's `stepMirState` on a running state is `stepMirFn`, so `TrustedRun` is also a
fault-free `stepMirState` execution. -/
theorem stepMirState_running (cm : CapturedMir) (s : MachineState) :
    stepMirState cm (.running s) = stepMirFn cm s := rfl

/-- `Unreachable` is undefined behavior in both semantics: Anneal's step fails and Trusted's
`evalTerminator` faults with `.ub`. -/
theorem evalLoweredTerminator_unreachable_ub {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock}
    (hb : body.blocks[bb]? = some b) (hT : b.terminator = .unreachable) (s : MachineState)
    (span : String) (cmOpt : Option CapturedMir) :
    evalLoweredTerminator env body bb slots unwinding = none ∧
      evalTerminator s ⟨.unreachable, span⟩ cmOpt = .fail .ub := by
  refine ⟨?_, rfl⟩
  unfold evalLoweredTerminator
  rw [hb]
  simp only [hT]
  split <;> rfl

/-- An assertion that fails under `UnwindAction::Unreachable` is undefined behavior in both
semantics (Anneal's `UnwindIntoUnreachable`; Trusted's `applyUnwindAction` faults). -/
theorem assert_unreachable_unwind_ub (s : MachineState) (locals' : List LocalSlot) (body : LBody)
    (bb : Nat) (slots : List LocalSlotState) (unwinding : Option Nat) :
    startPanic body bb .unreachable slots unwinding = none ∧
      applyUnwindAction s locals' s.memory .unreachable = .faulted .ub := ⟨rfl, rfl⟩

/-- **Documented divergence of `Drop`**: Anneal's `Drop` (no drop glue) keeps the dropped bare
local's value, while Trusted's `evalTerminator` marks it uninitialized; a later read of the local
is defined in Anneal (and in Miri, for types without drop glue) but not in Trusted. Hence
`Drop` is excluded from `LTerminator.Refinable`. -/
theorem evalLoweredTerminator_drop_bare_divergence {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {b : LBlock} {loc : Local}
    {target : Nat} {u : UnwindAction} (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop ⟨loc, []⟩ target u) {step : CfgStep}
    (h : evalLoweredTerminator env body bb slots unwinding = some step)
    (s : MachineState) (span : String) (cmOpt : Option CapturedMir) {slot : LocalSlot}
    (hSlot : s.frame.locals[loc]? = some slot) (hLive : slot ≠ .dead) :
    step = .goto target slots unwinding ∧
      evalTerminator s ⟨.drop ⟨loc, []⟩ target u, span⟩ cmOpt =
        .step { s with frame := ⟨target, 0, s.frame.locals.set loc LocalSlot.uninit⟩ } := by
  refine ⟨?_, ?_⟩
  · unfold evalLoweredTerminator at h
    rw [hb] at h
    simp only [hT] at h
    split at h
    · nomatch h
    · split at h
      · exact cfgGoto_eq_some h
      · nomatch h
  · have hLt : loc < s.frame.locals.length := (List.getElem?_eq_some_iff.mp hSlot).1
    simp only [evalTerminator, get?_eq_getElem?, hSlot]
    cases slot with
    | dead => exact absurd rfl hLive
    | _ => simp only [set?_eq_some_iff.mpr ⟨hLt, rfl⟩]

/-- **Trivial (projected) `Drop` refines Trusted**: dropping a projected place that Anneal can
read jumps to the drop target in both semantics with the frame unchanged, preserving
`StateCorr`. -/
theorem evalLoweredTerminator_drop_projected_refines {env : CfgEnv} {body : LBody} {bb : Nat}
    {slots : List LocalSlotState} {unwinding : Option Nat} {s : MachineState} {b : LBlock}
    {place : Place} {target : Nat} {u : UnwindAction} {step : CfgStep}
    (hCorr : StateCorr env bb slots s) (hb : body.blocks[bb]? = some b)
    (hT : b.terminator = .drop place target u) (hProj : place.projection ≠ []) {v : Value}
    (hRead : readPlaceState slots place = .ok v)
    (h : evalLoweredTerminator env body bb slots unwinding = some step) (span : String)
    (cmOpt : Option CapturedMir) :
    step = .goto target slots unwinding ∧
      evalTerminator s ⟨.drop place target u, span⟩ cmOpt =
        .step { s with frame := ⟨target, 0, s.frame.locals⟩ } ∧
      StateCorr env target slots { s with frame := ⟨target, 0, s.frame.locals⟩ } := by
  refine ⟨?_, ?_, hCorr.jump target s.frame.locals hCorr.slots⟩
  · unfold evalLoweredTerminator at h
    rw [hb] at h
    simp only [hT] at h
    split at h
    · nomatch h
    · split at h
      · exact cfgGoto_eq_some h
      · nomatch h
  · obtain ⟨rootVal, hRoot, hTRead⟩ := readPlaceState_below_refines hCorr.slots hRead
    obtain ⟨a, rest, hP⟩ : ∃ a rest, place.projection = a :: rest := by
      cases hp : place.projection with
      | nil => exact absurd hp hProj
      | cons a rest => exact ⟨a, rest, rfl⟩
    simp only [get?_eq_getElem?] at hRoot
    simp only [evalTerminator, get?_eq_getElem?, hRoot, hP]
    rw [hP] at hTRead
    simp only [hTRead]

end Anneal.Mir.AdtAndControl
