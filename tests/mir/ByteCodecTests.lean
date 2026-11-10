import Anneal.ByteCodec

namespace Anneal.ByteCodecTests

open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.BitValidity
open Anneal.ByteCodec

/-!
# Kernel-Checked Regression & Negative Test Suite for `Anneal.ByteCodec`

Covers:
1. Positive round-trip, exact-width, and prefix-free slice laws (`decode_encode`,
   `decode_take_append`, `decode_slice_at_append`, `decode_sliceAbstractBytes_append`)
   across `unit`, `u8`, `boolByte`, `uintBitsLE`, `scalarLE`, `prod`, nested
   `(u32, (u16, u16))`, `padLeft`/`padRight`, `listFixed`/`array` (`Vector`),
   `refineNiche`, `scalarValidRange`, and `enumRepr`.
2. Negative rejection & non-membership theorems:
   - Out-of-range niche value (`0` for `NonZeroU32` `[1 ..= u32::MAX]`) and
     out-of-range discriminant (`3` for a 3-variant `#[repr(u8)]` enum) decode to
     `none` via `refineNiche_decode_rejects_false` / `enumRepr_decode_rejects_invalid_tag`.
   - Invalid `bool` bit patterns (`0x02`, `0xff`) and `.uninit` decode to `none`,
     and `¬ boolByte.IsSurjectiveInitDecoder`.
   - Padded codecs (`padRight c 2`, `padLeft 1 c`) emit `.uninit` padding bytes
     (`allBytesInitialized = false`) and violate `IsInitCodec` (`¬ IsInitCodec`),
     while remaining `IsSurjectiveInitDecoder` and `HasZeroValid`.
3. `MirValueCodec` + `Anneal.BitValidity` marker-trait bridges (`IsIntoBytes`,
   `IsFromBytes`, `IsFromZeros`, `IsTryFromBytes`, `¬ IsFromBytes`, `¬ IsIntoBytes`,
   `ByteSeqValid`, and `transmute_sound` / `transmute_typed`).
4. Fuel-free structural recursion (`termination_by` via `sizeOf_lt_*`) over
   `RigidTy` and `Value`, including a depth-20 nested `Value.aggregate` where
   `encodeUntypedValueToBytes defaultCodecFuel` exhausts fuel (`= none`) while
   `encodeUntypedValueFuelFree` succeeds.
5. Kernel `rfl` reduction examples and `_eq_true_iff` / disjointness /
   `rigidTyKindByteSize` (`8` vs `16`, `0`, `1`, `4`) checks for `isBoolRigidTy`,
   `isCharRigidTy`, `isUnitTupleRigidTy`, `isWidePointeeRigidTy`,
   `isWidePtrRigidTy`, and `isThinPtrRigidTy`.
-/

/-! ## 1. Positive Combinator Round-Trip & Prefix-Free Slice Regressions -/

def u16Codec : FixedByteCodec { bits : Nat // bits < 2 ^ (8 * 2) } 2 :=
  FixedByteCodec.uintBitsLE 2 (by decide)

def u32Codec : FixedByteCodec { bits : Nat // bits < 2 ^ (8 * 4) } 4 :=
  FixedByteCodec.uintBitsLE 4 (by decide)

def scalarU32Codec :
    FixedByteCodec { sv : ScalarInt // sv.sizeBytes = 4 ∧ sv.bits < 2 ^ (8 * 4) } 4 :=
  FixedByteCodec.scalarLE 4 (by decide)

/-- Nested tuple codec `(u32, (u16, u16))` of total width `4 + (2 + 2) = 8` bytes. -/
def nestedTupleCodec :
    FixedByteCodec
      ({ bits : Nat // bits < 2 ^ (8 * 4) } ×
        ({ bits : Nat // bits < 2 ^ (8 * 2) } × { bits : Nat // bits < 2 ^ (8 * 2) }))
      (4 + (2 + 2)) :=
  FixedByteCodec.prod u32Codec (FixedByteCodec.prod u16Codec u16Codec)

theorem unit_roundtrip_and_slice (pre post : List AbstractByte) :
    FixedByteCodec.unit.decode (FixedByteCodec.unit.encode ()) = some () ∧
    (sliceAbstractBytes (pre ++ FixedByteCodec.unit.encode () ++ post) pre.length 0).bind
      FixedByteCodec.unit.decode = some () :=
  ⟨FixedByteCodec.unit.decode_encode (),
   FixedByteCodec.unit.decode_sliceAbstractBytes_append pre post ()⟩

theorem unit_rejects_trailing_byte (b : AbstractByte) :
    FixedByteCodec.unit.decode [b] = none := rfl

theorem u8_roundtrip_and_slice (x : UInt8) (pre post : List AbstractByte) :
    FixedByteCodec.u8.decode ((FixedByteCodec.u8.encode x ++ post).take 1) = some x ∧
    (sliceAbstractBytes (pre ++ FixedByteCodec.u8.encode x ++ post) pre.length 1).bind
      FixedByteCodec.u8.decode = some x :=
  ⟨FixedByteCodec.u8.decode_take_append x post,
   FixedByteCodec.u8.decode_sliceAbstractBytes_append pre post x⟩

theorem boolByte_roundtrip_and_slice (b : Bool) (pre post : List AbstractByte) :
    FixedByteCodec.boolByte.decode (FixedByteCodec.boolByte.encode b) = some b ∧
    (sliceAbstractBytes (pre ++ FixedByteCodec.boolByte.encode b ++ post) pre.length 1).bind
      FixedByteCodec.boolByte.decode = some b :=
  ⟨FixedByteCodec.boolByte.decode_encode b,
   FixedByteCodec.boolByte.decode_sliceAbstractBytes_append pre post b⟩

theorem scalarU32_roundtrip_and_bridge
    (x : { sv : ScalarInt // sv.sizeBytes = 4 ∧ sv.bits < 2 ^ (8 * 4) })
    (pre post : List AbstractByte) :
    scalarU32Codec.decode (scalarU32Codec.encode x) = some x ∧
    encodeScalarBytes x.val none = some (scalarU32Codec.encode x) ∧
    (sliceAbstractBytes (pre ++ scalarU32Codec.encode x ++ post) pre.length 4).bind
      scalarU32Codec.decode = some x :=
  ⟨scalarU32Codec.decode_encode x,
   FixedByteCodec.encodeScalarBytes_eq_scalarLE_encode 4 (by decide) x,
   scalarU32Codec.decode_sliceAbstractBytes_append pre post x⟩

theorem nestedTuple_roundtrip_and_prefix_free_slice
    (a : { bits : Nat // bits < 2 ^ (8 * 4) })
    (b c : { bits : Nat // bits < 2 ^ (8 * 2) })
    (pre post : List AbstractByte) :
    nestedTupleCodec.decode (nestedTupleCodec.encode (a, (b, c))) = some (a, (b, c)) ∧
    nestedTupleCodec.decode ((nestedTupleCodec.encode (a, (b, c)) ++ post).take 8) =
      some (a, (b, c)) ∧
    (sliceAbstractBytes (pre ++ nestedTupleCodec.encode (a, (b, c)) ++ post) pre.length 8).bind
      nestedTupleCodec.decode = some (a, (b, c)) :=
  ⟨nestedTupleCodec.decode_encode (a, (b, c)),
   nestedTupleCodec.decode_take_append (a, (b, c)) post,
   nestedTupleCodec.decode_sliceAbstractBytes_append pre post (a, (b, c))⟩

theorem nestedTuple_traits :
    nestedTupleCodec.IsExactWidth ∧
    nestedTupleCodec.IsInitCodec ∧
    nestedTupleCodec.IsSurjectiveInitDecoder ∧
    nestedTupleCodec.HasZeroValid :=
  ⟨FixedByteCodec.prod_isExactWidth u32Codec (FixedByteCodec.prod u16Codec u16Codec),
   FixedByteCodec.prod_isInitCodec
     (FixedByteCodec.uintBitsLE_isInitCodec 4 (by decide))
     (FixedByteCodec.prod_isInitCodec
       (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide))
       (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide))),
   FixedByteCodec.prod_isSurjectiveInitDecoder
     (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide))
     (FixedByteCodec.prod_isSurjectiveInitDecoder
       (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide))
       (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide))),
   FixedByteCodec.prod_hasZeroValid
     (FixedByteCodec.uintBitsLE_hasZeroValid 4 (by decide))
     (FixedByteCodec.prod_hasZeroValid
       (FixedByteCodec.uintBitsLE_hasZeroValid 2 (by decide))
       (FixedByteCodec.uintBitsLE_hasZeroValid 2 (by decide)))⟩

theorem padLeft_padRight_roundtrip_and_slice
    (x : { bits : Nat // bits < 2 ^ (8 * 2) })
    (pre post : List AbstractByte) :
    let cRight := FixedByteCodec.padRight u16Codec 2
    let cLeft := FixedByteCodec.padLeft 2 u16Codec
    cRight.decode (cRight.encode x) = some x ∧
    cLeft.decode (cLeft.encode x) = some x ∧
    (sliceAbstractBytes (pre ++ cRight.encode x ++ post) pre.length 4).bind cRight.decode = some x ∧
    (sliceAbstractBytes (pre ++ cLeft.encode x ++ post) pre.length 4).bind cLeft.decode = some x :=
  ⟨(FixedByteCodec.padRight u16Codec 2).decode_encode x,
   (FixedByteCodec.padLeft 2 u16Codec).decode_encode x,
   (FixedByteCodec.padRight u16Codec 2).decode_sliceAbstractBytes_append pre post x,
   (FixedByteCodec.padLeft 2 u16Codec).decode_sliceAbstractBytes_append pre post x⟩

theorem listFixed_and_vector_array_roundtrip
    (xs : { l : List UInt8 // l.length = 4 })
    (vec : Vector UInt8 4)
    (pre post : List AbstractByte) :
    let listC := FixedByteCodec.listFixed 4 FixedByteCodec.u8
    let vecC := FixedByteCodec.array 4 FixedByteCodec.u8
    listC.decode (listC.encode xs) = some xs ∧
    vecC.decode (vecC.encode vec) = some vec ∧
    (sliceAbstractBytes (pre ++ vecC.encode vec ++ post) pre.length 4).bind vecC.decode =
      some vec :=
  ⟨(FixedByteCodec.listFixed 4 FixedByteCodec.u8).decode_encode xs,
   (FixedByteCodec.array 4 FixedByteCodec.u8).decode_encode vec,
   (FixedByteCodec.array 4 FixedByteCodec.u8).decode_sliceAbstractBytes_append pre post vec⟩

/-- Zero-sized element arrays (`[(); 3]`, width `3 * 0 = 0`) round-trip on `[]` and reject non-empty bytes. -/
theorem zst_array_roundtrip_and_exact_width (b : AbstractByte) :
    let zstArr := FixedByteCodec.listFixed 3 FixedByteCodec.unit
    zstArr.decode (zstArr.encode ⟨[(), (), ()], rfl⟩) = some ⟨[(), (), ()], rfl⟩ ∧
    zstArr.decode [b] = none :=
  ⟨(FixedByteCodec.listFixed 3 FixedByteCodec.unit).decode_encode ⟨[(), (), ()], rfl⟩,
   (FixedByteCodec.listFixed_isExactWidth 3 FixedByteCodec.unit).decode_eq_none_of_length_ne
     (by simp)⟩

/-- 3-variant fieldless `#[repr(u8)]` enum for testing `FixedByteCodec.enumRepr`. -/
inductive Ordering3 : Type where
  | less
  | equal
  | greater
  deriving DecidableEq

def ordering3ToTag : Ordering3 → Nat
  | .less => 0
  | .equal => 1
  | .greater => 2

def ordering3OfTag : Nat → Option Ordering3
  | 0 => some .less
  | 1 => some .equal
  | 2 => some .greater
  | _ => none

theorem ordering3_round (e : Ordering3) : ordering3OfTag (ordering3ToTag e) = some e := by
  cases e <;> rfl

theorem ordering3_bounds (e : Ordering3) : ordering3ToTag e < 2 ^ (8 * 1) := by
  cases e <;> decide

def ordering3Codec : FixedByteCodec Ordering3 1 :=
  FixedByteCodec.enumRepr 1 (by decide) ordering3ToTag ordering3OfTag
    ordering3_round ordering3_bounds

theorem ordering3_roundtrip_and_slice (e : Ordering3) (pre post : List AbstractByte) :
    ordering3Codec.decode (ordering3Codec.encode e) = some e ∧
    (sliceAbstractBytes (pre ++ ordering3Codec.encode e ++ post) pre.length 1).bind
      ordering3Codec.decode = some e :=
  ⟨ordering3Codec.decode_encode e,
   ordering3Codec.decode_sliceAbstractBytes_append pre post e⟩

theorem ordering3_decode_eq_some_iff_canonical (bs : List AbstractByte) (e : Ordering3) :
    ordering3Codec.decode bs = some e ↔
      (FixedByteCodec.uintBitsLE 1 (by decide)).decode bs =
        some ⟨ordering3ToTag e, ordering3_bounds e⟩ :=
  FixedByteCodec.enumRepr_decode_eq_some_iff
    1 (by decide) ordering3ToTag ordering3OfTag ordering3_round ordering3_bounds bs e

/-! ## 2. Negative Tests: Niche Rejection, `bool` Bit Patterns, Combinator Propagation, and Padding `¬ IsInitCodec` -/

def nonZeroU32Range : WrappingRange :=
  { start := 1, end_ := 2 ^ 32 - 1 }

def nonZeroU32RefineCodec :
    FixedByteCodec
      { x : { bits : Nat // bits < 2 ^ (8 * 4) } //
        wrappingRangeContains nonZeroU32Range x.val = true }
      4 :=
  u32Codec.refineNiche (fun x => wrappingRangeContains nonZeroU32Range x.val)

def nonZeroU32RangeCodec :
    FixedByteCodec
      { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true }
      4 :=
  FixedByteCodec.scalarValidRange 4 (by decide) nonZeroU32Range

theorem nonZeroU32Refine_positive_one :
    let one : { x : { bits : Nat // bits < 2 ^ (8 * 4) } //
                wrappingRangeContains nonZeroU32Range x.val = true } :=
      ⟨⟨1, by decide⟩, by decide⟩
    nonZeroU32RefineCodec.decode (nonZeroU32RefineCodec.encode one) = some one :=
  nonZeroU32RefineCodec.decode_encode _

def nonZeroU32Min :
    { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true } :=
  ⟨1, by decide, by decide⟩

def nonZeroU32Max :
    { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true } :=
  ⟨2 ^ 32 - 1, by decide, by decide⟩

/-- Positive round-trip, `decode_take_append`, and `decode_sliceAbstractBytes_append`
tests for `scalarValidRange` on both `1` and `u32::MAX` (`0xffff_ffff`). -/
theorem nonZeroU32ScalarValidRange_positive_bounds (pre post : List AbstractByte) :
    nonZeroU32RangeCodec.decode (nonZeroU32RangeCodec.encode nonZeroU32Min) = some nonZeroU32Min ∧
    nonZeroU32RangeCodec.decode ((nonZeroU32RangeCodec.encode nonZeroU32Max ++ post).take 4) =
      some nonZeroU32Max ∧
    (sliceAbstractBytes (pre ++ nonZeroU32RangeCodec.encode nonZeroU32Min ++ post) pre.length 4).bind
      nonZeroU32RangeCodec.decode = some nonZeroU32Min ∧
    (sliceAbstractBytes (pre ++ nonZeroU32RangeCodec.encode nonZeroU32Max ++ post) pre.length 4).bind
      nonZeroU32RangeCodec.decode = some nonZeroU32Max :=
  ⟨nonZeroU32RangeCodec.decode_encode nonZeroU32Min,
   nonZeroU32RangeCodec.decode_take_append nonZeroU32Max post,
   nonZeroU32RangeCodec.decode_sliceAbstractBytes_append pre post nonZeroU32Min,
   nonZeroU32RangeCodec.decode_sliceAbstractBytes_append pre post nonZeroU32Max⟩

/-- Non-pointer `.float 32` layout bridge via `decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map`. -/
theorem float32_scalarLayout_bridge (range : WrappingRange) (bs : List AbstractByte) :
    decodeScalarLayoutBytes (.initialized (.float 32) range) bs =
      ((FixedByteCodec.scalarValidRange 4 (by decide) range).decode bs).map
        (fun x => Value.scalar ⟨x.val, 4⟩) :=
  FixedByteCodec.decodeScalarLayoutBytes_initialized_nonPtr_eq_scalarValidRange_map
    (.float 32) range 4 (by decide) rfl rfl bs

/-- Negative test: `0` is rejected by `NonZeroU32` via `refineNiche_decode_rejects_false`. -/
theorem nonZeroU32Refine_rejects_zero :
    let zeroVal : { bits : Nat // bits < 2 ^ (8 * 4) } := ⟨0, by decide⟩
    nonZeroU32RefineCodec.decode (u32Codec.encode zeroVal) = none :=
  FixedByteCodec.refineNiche_decode_rejects_false u32Codec
    (fun x => wrappingRangeContains nonZeroU32Range x.val)
    (u32Codec.decode_encode ⟨0, by decide⟩)
    rfl

/-- Negative test: `0` is rejected by `scalarValidRange` on `NonZeroU32`. -/
theorem nonZeroU32ScalarValidRange_rejects_zero :
    nonZeroU32RangeCodec.decode (encodeLittleEndianBytes 0 4 none) = none :=
  FixedByteCodec.scalarValidRange_decode_rejects_out_of_range
    4 (by decide) nonZeroU32Range (by decide) rfl

/-- Negative test: `NonZeroU32` refined codec is NOT `IsSurjectiveInitDecoder`. -/
theorem nonZeroU32Refine_not_surjective_init :
    ¬ nonZeroU32RefineCodec.IsSurjectiveInitDecoder :=
  FixedByteCodec.refineNiche_not_isSurjectiveInitDecoder
    (c := u32Codec)
    (fun x : { bits : Nat // bits < 2 ^ (8 * 4) } =>
      wrappingRangeContains nonZeroU32Range x.val)
    (FixedByteCodec.uintBitsLE_isInitCodec 4 (by decide))
    (bad := ⟨0, by decide⟩)
    rfl

/-- Negative test: out-of-range discriminant `3` is rejected by 3-variant `ordering3Codec`. -/
theorem ordering3Codec_rejects_discriminant_3 :
    ordering3Codec.decode (encodeLittleEndianBytes 3 1 none) = none :=
  FixedByteCodec.enumRepr_decode_rejects_invalid_tag
    1 (by decide) ordering3ToTag ordering3OfTag ordering3_round ordering3_bounds
    (bits := 3) (by decide) rfl

/-- `enumRepr` marker-trait consequences (`B2-2`): `ordering3Codec` is `IsInitCodec` and
`HasZeroValid` (via `.less ↦ 0`), and NOT `IsSurjectiveInitDecoder` (via missing tag `3`). -/
theorem ordering3Codec_marker_traits :
    ordering3Codec.IsInitCodec ∧
    ordering3Codec.HasZeroValid ∧
    ¬ ordering3Codec.IsSurjectiveInitDecoder :=
  ⟨FixedByteCodec.enumRepr_isInitCodec
     1 (by decide) ordering3ToTag ordering3OfTag ordering3_round ordering3_bounds,
   FixedByteCodec.enumRepr_hasZeroValid_of
     1 (by decide) ordering3ToTag ordering3OfTag ordering3_round ordering3_bounds
     .less rfl,
   FixedByteCodec.enumRepr_not_isSurjectiveInitDecoder
     1 (by decide) ordering3ToTag ordering3OfTag ordering3_round ordering3_bounds
     (bits := 3) (by decide) (fun e => by cases e <;> decide)⟩

/-- Fieldless enum with non-zero discriminants `{1, 2}` fails `HasZeroValid` (`¬ FromZeros`)
via `enumRepr_hasZeroValid_iff`. -/
inductive NonZeroTagEnum : Type where
  | one
  | two
  deriving DecidableEq

def nonZeroTagToTag : NonZeroTagEnum → Nat
  | .one => 1
  | .two => 2

def nonZeroTagOfTag : Nat → Option NonZeroTagEnum
  | 1 => some .one
  | 2 => some .two
  | _ => none

theorem nonZeroTag_round (e : NonZeroTagEnum) : nonZeroTagOfTag (nonZeroTagToTag e) = some e := by
  cases e <;> rfl

theorem nonZeroTag_bounds (e : NonZeroTagEnum) : nonZeroTagToTag e < 2 ^ (8 * 1) := by
  cases e <;> decide

def nonZeroTagEnumCodec : FixedByteCodec NonZeroTagEnum 1 :=
  FixedByteCodec.enumRepr 1 (by decide) nonZeroTagToTag nonZeroTagOfTag
    nonZeroTag_round nonZeroTag_bounds

theorem nonZeroTagEnumCodec_not_hasZeroValid :
    ¬ nonZeroTagEnumCodec.HasZeroValid := by
  unfold nonZeroTagEnumCodec
  rw [FixedByteCodec.enumRepr_hasZeroValid_iff
        1 (by decide) nonZeroTagToTag nonZeroTagOfTag nonZeroTag_round nonZeroTag_bounds]
  rintro ⟨e₀, h0⟩
  cases e₀ <;> nomatch h0

/-- Lenient `ofTag` regression (`B1-1`): `lenientBoolOfTag` maps every tag `≥ 2` to
`some false`, yet `enumRepr` still rejects tag `2` with `none` because `toTag false = 0 ≠ 2`! -/
def lenientBoolToTag : Bool → Nat
  | false => 0
  | true => 1

def lenientBoolOfTag : Nat → Option Bool
  | 0 => some false
  | 1 => some true
  | _ => some false

theorem lenientBool_round (b : Bool) : lenientBoolOfTag (lenientBoolToTag b) = some b := by
  cases b <;> rfl

theorem lenientBool_bounds (b : Bool) : lenientBoolToTag b < 2 ^ (8 * 1) := by
  cases b <;> decide

def lenientBoolEnumCodec : FixedByteCodec Bool 1 :=
  FixedByteCodec.enumRepr 1 (by decide) lenientBoolToTag lenientBoolOfTag
    lenientBool_round lenientBool_bounds

theorem lenientBoolEnumCodec_rejects_tag_2 :
    lenientBoolOfTag 2 = some false ∧
    lenientBoolEnumCodec.decode (encodeLittleEndianBytes 2 1 none) = none :=
  ⟨rfl,
   FixedByteCodec.enumRepr_decode_rejects_non_canonical_tag
     1 (by decide) lenientBoolToTag lenientBoolOfTag lenientBool_round lenientBool_bounds
     (bits := 2) (by decide) (fun b => by cases b <;> decide)⟩

/-- Negative test: invalid `bool` bit patterns (`0x02`, `0xff`) and `.uninit` return `none`. -/
theorem boolByte_rejects_two :
    FixedByteCodec.boolByte.decode [.init (UInt8.ofNat 2) none] = none :=
  FixedByteCodec.boolByte_decode_invalid_of_ge_two (UInt8.ofNat 2) none (by decide)

theorem boolByte_rejects_0xff :
    FixedByteCodec.boolByte.decode [.init (UInt8.ofNat 0xff) none] = none :=
  FixedByteCodec.boolByte_decode_invalid_of_ge_two (UInt8.ofNat 0xff) none (by decide)

theorem boolByte_rejects_uninit :
    FixedByteCodec.boolByte.decode [.uninit] = none := rfl

theorem boolByte_not_surjective_init :
    ¬ FixedByteCodec.boolByte.IsSurjectiveInitDecoder :=
  FixedByteCodec.boolByte_not_isSurjectiveInitDecoder

/-- Negative propagation tests (`B1-6`): `prod`, `listFixed`, and `array` reject
whenever any component/element byte slice fails its element decoder. -/
theorem prod_propagates_component_rejections :
    let pairC := FixedByteCodec.prod FixedByteCodec.u8 FixedByteCodec.boolByte
    pairC.decode [.init (UInt8.ofNat 0x2a) none, .init (UInt8.ofNat 2) none] = none ∧
    pairC.decode [.uninit, .init (UInt8.ofNat 1) none] = none :=
  ⟨FixedByteCodec.prod_decode_eq_none_of_snd_none FixedByteCodec.u8 FixedByteCodec.boolByte
     boolByte_rejects_two,
   FixedByteCodec.prod_decode_eq_none_of_fst_none FixedByteCodec.u8 FixedByteCodec.boolByte rfl⟩

theorem listFixed_and_array_propagate_element_rejection :
    let badBytes : List AbstractByte :=
      [.init (UInt8.ofNat 1) none, .init (UInt8.ofNat 2) none, .init (UInt8.ofNat 0) none]
    (FixedByteCodec.listFixed 3 FixedByteCodec.boolByte).decode badBytes = none ∧
    (FixedByteCodec.array 3 FixedByteCodec.boolByte).decode badBytes = none := by
  have hMid :
      (FixedByteCodec.listFixed 2 FixedByteCodec.boolByte).decode
        [.init (UInt8.ofNat 2) none, .init (UInt8.ofNat 0) none] = none :=
    FixedByteCodec.listFixed_decode_eq_none_of_head_none 1 FixedByteCodec.boolByte
      boolByte_rejects_two
  have hList :
      (FixedByteCodec.listFixed 3 FixedByteCodec.boolByte).decode
        [.init (UInt8.ofNat 1) none, .init (UInt8.ofNat 2) none, .init (UInt8.ofNat 0) none] =
        none :=
    FixedByteCodec.listFixed_decode_eq_none_of_tail_none 2 FixedByteCodec.boolByte hMid
  exact ⟨hList, FixedByteCodec.array_decode_eq_none_of_listFixed_none 3 FixedByteCodec.boolByte hList⟩

/-- Negative test: padded codecs (`padRight` / `padLeft` with `padBytes = 2 > 0`) emit
`.uninit` bytes (`allBytesInitialized = false`) and violate `IsInitCodec`. -/
theorem padded_u16_not_isInitCodec :
    let cRight := FixedByteCodec.padRight u16Codec 2
    let cLeft := FixedByteCodec.padLeft 2 u16Codec
    let sample : { bits : Nat // bits < 2 ^ (8 * 2) } := ⟨0x1234, by decide⟩
    allBytesInitialized (cRight.encode sample) = false ∧
    allBytesInitialized (cLeft.encode sample) = false ∧
    ¬ cRight.IsInitCodec ∧
    ¬ cLeft.IsInitCodec ∧
    cRight.IsSurjectiveInitDecoder ∧
    cRight.HasZeroValid :=
  ⟨FixedByteCodec.allBytesInitialized_padRight_encode_eq_false u16Codec (by decide) ⟨0x1234, by decide⟩,
   FixedByteCodec.allBytesInitialized_padLeft_encode_eq_false (by decide) u16Codec ⟨0x1234, by decide⟩,
   FixedByteCodec.padRight_not_isInitCodec u16Codec (by decide) ⟨0, by decide⟩,
   FixedByteCodec.padLeft_not_isInitCodec (by decide) u16Codec ⟨0, by decide⟩,
   FixedByteCodec.padRight_isSurjectiveInitDecoder 2
     (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide)),
   FixedByteCodec.padRight_hasZeroValid 2
     (FixedByteCodec.uintBitsLE_hasZeroValid 2 (by decide))⟩

/-- Exact `padLeft`/`padRight` `IsInitCodec` characterization (`B2-1`): zero padding
preserves `IsInitCodec`, whereas positive padding violates it. -/
theorem pad_zero_vs_pos_isInitCodec_iff (p : Nat) :
    ((FixedByteCodec.padLeft p u16Codec).IsInitCodec ↔ p = 0 ∧ u16Codec.IsInitCodec) ∧
    ((FixedByteCodec.padRight u16Codec p).IsInitCodec ↔ p = 0 ∧ u16Codec.IsInitCodec) ∧
    (FixedByteCodec.padLeft 0 u16Codec).IsInitCodec ∧
    (FixedByteCodec.padRight u16Codec 0).IsInitCodec :=
  ⟨FixedByteCodec.padLeft_isInitCodec_iff u16Codec ⟨0, by decide⟩,
   FixedByteCodec.padRight_isInitCodec_iff u16Codec ⟨0, by decide⟩,
   FixedByteCodec.padLeft_isInitCodec_of_eq_zero rfl
     (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide)),
   FixedByteCodec.padRight_isInitCodec_of_eq_zero rfl
     (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide))⟩

/-! ## 3. `MirValueCodec` + `Anneal.BitValidity` Marker-Trait & `transmute_sound` Bridges -/

def nonZeroU32Layout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) nonZeroU32Range)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

def paddedU16TupleLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
}

/-- Real `rustc` layout for `(u8, u32)`: `u8` at offset `0`, 3 bytes of interior
alignment padding (`pad₁ = 3`), `u32` at offset `4`, total size `8` bytes (`pad₂ = 0`). -/
def paddedU8U32TupleLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
  variants := .single 0
  isUninhabited := false
}

/-- Real `rustc` layout for unpadded `(u16, u16)`: `u16` at offset `0` (`pad₁ = 0`),
`u16` at offset `2` (`pad₂ = 0`), total size `4` bytes. -/
def laidOutU16PairLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 2 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }, { bytes := 2 }] [0, 1]
  variants := .single 0
  isUninhabited := false
}

def testLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [nonZeroU32Layout, paddedU16TupleLayout, paddedU8U32TupleLayout, laidOutU16PairLayout]
}

def mirUnit : MirValueCodec testLayouts { kind := .tuple [], layoutIdx := 0 } Unit 0 :=
  MirValueCodec.unit testLayouts 0

def mirBool : MirValueCodec testLayouts { kind := .bool, layoutIdx := 0 } Bool 1 :=
  MirValueCodec.bool testLayouts 0

def mirU8 :
    MirValueCodec testLayouts { kind := .uint .u8, layoutIdx := 0 }
      { bits : Nat // bits < 2 ^ (8 * 1) } 1 :=
  MirValueCodec.uint testLayouts .u8 0

def mirU32 :
    MirValueCodec testLayouts { kind := .uint .u32, layoutIdx := 0 }
      { bits : Nat // bits < 2 ^ (8 * 4) } 4 :=
  MirValueCodec.uint testLayouts .u32 0

def mirNonZeroU32 :
    MirValueCodec testLayouts { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 }
      { bits : Nat // bits < 2 ^ (8 * 4) ∧ wrappingRangeContains nonZeroU32Range bits = true }
      4 :=
  MirValueCodec.primitiveNicheAdt
    testLayouts "core::num::NonZeroU32" [] 0 nonZeroU32Layout 4 32 false 0 nonZeroU32Range
    (by decide) rfl rfl rfl rfl rfl rfl rfl

def mirU8x4 :
    MirValueCodec testLayouts { kind := .array (.uint .u8) 4, layoutIdx := 0 }
      { xs : List { bits : Nat // bits < 2 ^ (8 * 1) } // xs.length = 4 }
      4 :=
  MirValueCodec.uintArray testLayouts .u8 4 (by decide) 0

def mirU16Pair :
    MirValueCodec testLayouts { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 4 }
      ({ bits : Nat // bits < 2 ^ (8 * 2) } × { bits : Nat // bits < 2 ^ (8 * 2) })
      4 :=
  MirValueCodec.uintPairTuple testLayouts .u16 .u16 4 rfl

def mirPaddedU16Tuple :
    MirValueCodec testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 }
      { bits : Nat // bits < 2 ^ (8 * 2) }
      4 :=
  MirValueCodec.paddedSingleElemTuple testLayouts .u16 2 1 paddedU16TupleLayout rfl rfl rfl

def mirPaddedU8U32Tuple :
    MirValueCodec testLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 2 }
      ({ bits : Nat // bits < 2 ^ (8 * 1) } × { bits : Nat // bits < 2 ^ (8 * 4) })
      8 :=
  MirValueCodec.uintPairArbitraryTuple
    testLayouts .u8 .u32 3 0 2 paddedU8U32TupleLayout [0, 1] rfl rfl rfl

def mirLaidOutU16Pair :
    MirValueCodec testLayouts { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 3 }
      ({ bits : Nat // bits < 2 ^ (8 * 2) } × { bits : Nat // bits < 2 ^ (8 * 2) })
      4 :=
  MirValueCodec.uintPairArbitraryTuple
    testLayouts .u16 .u16 0 0 3 laidOutU16PairLayout [0, 1] rfl rfl rfl

/-- `u32` satisfies all four zerocopy marker traits with a non-vacuous `IsTryFromBytes` range bound. -/
theorem mirU32_all_marker_traits :
    IsIntoBytes testLayouts { kind := .uint .u32, layoutIdx := 0 } ∧
    IsFromBytes testLayouts { kind := .uint .u32, layoutIdx := 0 } ∧
    IsFromZeros testLayouts { kind := .uint .u32, layoutIdx := 0 } ∧
    IsTryFromBytes testLayouts { kind := .uint .u32, layoutIdx := 0 }
      (fun v => ∃ bits, bits < 2 ^ 32 ∧ v = .scalar ⟨bits, 4⟩) :=
  ⟨mirU32.isIntoBytes (FixedByteCodec.uintBitsLE_isInitCodec 4 (by decide)),
   mirU32.isFromBytes (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide)),
   mirU32.isFromZeros (FixedByteCodec.uintBitsLE_hasZeroValid 4 (by decide)),
   mirU32.isTryFromBytes_of (fun ⟨bits, hLt⟩ => ⟨bits, hLt, rfl⟩)⟩

/-- `bool` is `IntoBytes`, `FromZeros`, and `IsTryFromBytes` with `{0, 1}` bit-pattern
invariant, but NOT `FromBytes`. -/
theorem mirBool_marker_traits_and_not_fromBytes :
    IsIntoBytes testLayouts { kind := .bool, layoutIdx := 0 } ∧
    IsFromZeros testLayouts { kind := .bool, layoutIdx := 0 } ∧
    IsTryFromBytes testLayouts { kind := .bool, layoutIdx := 0 }
      (fun v => v = .scalar ⟨0, 1⟩ ∨ v = .scalar ⟨1, 1⟩) ∧
    ¬ IsFromBytes testLayouts { kind := .bool, layoutIdx := 0 } :=
  ⟨mirBool.isIntoBytes FixedByteCodec.boolByte_isInitCodec,
   mirBool.isFromZeros FixedByteCodec.boolByte_hasZeroValid,
   mirBool.isTryFromBytes_of (fun b => by
     cases b with
     | false => exact Or.inl rfl
     | true => exact Or.inr rfl),
   mirBool.not_isFromBytes_of_rejected_init
     (bs := [.init (UInt8.ofNat 2) none]) rfl rfl boolByte_rejects_two⟩

/-- `NonZeroU32` is `IntoBytes` and `IsTryFromBytes` with non-zero guarantee
(`v ≠ .scalar ⟨0, 4⟩` and `1 ≤ bits ≤ 2^32 - 1`), but NOT `FromBytes` (`0` is rejected). -/
theorem mirNonZeroU32_into_and_not_fromBytes :
    IsIntoBytes testLayouts { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 } ∧
    IsTryFromBytes testLayouts { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 }
      (fun v => v ≠ .scalar ⟨0, 4⟩ ∧ ∃ bits, 1 ≤ bits ∧ bits < 2 ^ 32 ∧ v = .scalar ⟨bits, 4⟩) ∧
    ¬ IsFromBytes testLayouts { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 } := by
  refine ⟨mirNonZeroU32.isIntoBytes
            (FixedByteCodec.scalarValidRange_isInitCodec 4 (by decide) nonZeroU32Range),
          mirNonZeroU32.isTryFromBytes_of ?_,
          mirNonZeroU32.not_isFromBytes_of_rejected_init
            (bs := encodeLittleEndianBytes 0 4 none)
            (length_encodeLittleEndianBytes none 4 0)
            (allBytesInitialized_encodeLittleEndianBytes none 4 0)
            nonZeroU32ScalarValidRange_rejects_zero⟩
  rintro ⟨bits, hLt, hRange⟩
  have hGe1 : 1 ≤ bits := by
    unfold wrappingRangeContains nonZeroU32Range at hRange
    dsimp only at hRange
    have hBle : Nat.ble 1 (2 ^ 32 - 1) = true := by decide
    rw [hBle] at hRange
    dsimp only at hRange
    simp only [Bool.and_eq_true] at hRange
    exact Nat.le_of_ble_eq_true hRange.1
  refine ⟨?_, bits, hGe1, hLt, rfl⟩
  intro hEqZero
  change Value.scalar ⟨bits, 4⟩ = Value.scalar ⟨0, 4⟩ at hEqZero
  injection hEqZero with hSc
  have hBits0 : bits = 0 := congrArg ScalarInt.bits hSc
  omega

/-- Padded `(u16,)` (2-byte field + 2-byte trailing padding) is `FromBytes`, `FromZeros`,
and non-vacuous `IsTryFromBytes`, but NOT `IntoBytes`! -/
theorem mirPaddedU16Tuple_fromBytes_and_not_intoBytes :
    IsFromBytes testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 } ∧
    IsFromZeros testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 } ∧
    IsTryFromBytes testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 }
      (fun v => ∃ bits, bits < 2 ^ 16 ∧ v = .aggregate 0 [.scalar ⟨bits, 2⟩]) ∧
    ¬ IsIntoBytes testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 } :=
  ⟨mirPaddedU16Tuple.isFromBytes
     (FixedByteCodec.padRight_isSurjectiveInitDecoder 2
       (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide))),
   mirPaddedU16Tuple.isFromZeros
     (FixedByteCodec.padRight_hasZeroValid 2
       (FixedByteCodec.uintBitsLE_hasZeroValid 2 (by decide))),
   mirPaddedU16Tuple.isTryFromBytes_of (fun ⟨bits, hLt⟩ => ⟨bits, hLt, rfl⟩),
   mirPaddedU16Tuple.not_isIntoBytes_of_uninit_encode
     ⟨0x0042, by decide⟩
     (FixedByteCodec.allBytesInitialized_padRight_encode_eq_false
       (FixedByteCodec.uintBitsLE 2 (by decide)) (by decide) ⟨0x0042, by decide⟩)⟩

/-- Real laid-out `(u8, u32)` with 3 bytes of interior padding (`B1-2`) is
`FromBytes`, `FromZeros`, and non-vacuous `IsTryFromBytes`, while failing `IntoBytes`! -/
theorem mirPaddedU8U32Tuple_fromBytes_and_not_intoBytes :
    IsFromBytes testLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 2 } ∧
    IsFromZeros testLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 2 } ∧
    IsTryFromBytes testLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 2 }
      (fun v =>
        ∃ b0 b1,
          b0 < 2 ^ 8 ∧ b1 < 2 ^ 32 ∧
          v = .aggregate 0 [.scalar ⟨b0, 1⟩, .scalar ⟨b1, 4⟩]) ∧
    ¬ IsIntoBytes testLayouts { kind := .tuple [.uint .u8, .uint .u32], layoutIdx := 2 } := by
  refine
    ⟨mirPaddedU8U32Tuple.isFromBytes
       (FixedByteCodec.prod_isSurjectiveInitDecoder
         (FixedByteCodec.padRight_isSurjectiveInitDecoder 3
           (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 1 (by decide)))
         (FixedByteCodec.padRight_isSurjectiveInitDecoder 0
           (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide)))),
     mirPaddedU8U32Tuple.isFromZeros
       (FixedByteCodec.prod_hasZeroValid
         (FixedByteCodec.padRight_hasZeroValid 3
           (FixedByteCodec.uintBitsLE_hasZeroValid 1 (by decide)))
         (FixedByteCodec.padRight_hasZeroValid 0
           (FixedByteCodec.uintBitsLE_hasZeroValid 4 (by decide)))),
     mirPaddedU8U32Tuple.isTryFromBytes_of
       (fun ⟨⟨b0, hb0⟩, ⟨b1, hb1⟩⟩ => ⟨b0, b1, hb0, hb1, rfl⟩),
     mirPaddedU8U32Tuple.not_isIntoBytes_of_uninit_encode
       (⟨0x07, by decide⟩, ⟨0xdead_beef, by decide⟩)
       (by rfl)⟩

/-- Safe `transmute_sound` instance: `NonZeroU32 -> u32`. -/
theorem transmute_nonZeroU32_to_u32_sound
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel testLayouts
      { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel testLayouts
      { kind := .uint .u32, layoutIdx := 0 } bs = some v' :=
  MirValueCodec.transmute_sound mirNonZeroU32 mirU32
    (FixedByteCodec.scalarValidRange_isInitCodec 4 (by decide) nonZeroU32Range)
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide))
    v bs hEnc

/-- Safe `transmute_sound` instance: `(u16, u16) -> u32` and `[u8; 4] -> u32` and `bool -> u8`. -/
theorem transmute_u16Pair_to_u32_typed
    (p : { bits : Nat // bits < 2 ^ (8 * 2) } × { bits : Nat // bits < 2 ^ (8 * 2) }) :
    ∃ y : { bits : Nat // bits < 2 ^ (8 * 4) },
      mirU32.codec.decode (mirU16Pair.codec.encode p) = some y ∧
      decodeValueFromBytes defaultCodecFuel testLayouts
        { kind := .uint .u32, layoutIdx := 0 } (mirU16Pair.codec.encode p) =
        some (mirU32.toValue y) :=
  MirValueCodec.transmute_typed mirU16Pair mirU32
    (FixedByteCodec.prod_isInitCodec
      (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide))
      (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide)))
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide))
    p

theorem transmute_u8x4_to_u32_sound
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel testLayouts
      { kind := .array (.uint .u8) 4, layoutIdx := 0 } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel testLayouts
      { kind := .uint .u32, layoutIdx := 0 } bs = some v' :=
  MirValueCodec.transmute_sound mirU8x4 mirU32
    (FixedByteCodec.listFixed_isInitCodec 4 (FixedByteCodec.uintBitsLE_isInitCodec 1 (by decide)))
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide))
    v bs hEnc

theorem transmute_bool_to_u8_sound
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel testLayouts
      { kind := .bool, layoutIdx := 0 } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel testLayouts
      { kind := .uint .u8, layoutIdx := 0 } bs = some v' :=
  MirValueCodec.transmute_sound mirBool mirU8
    FixedByteCodec.boolByte_isInitCodec
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 1 (by decide))
    v bs hEnc

/-- Real laid-out unpadded `(u16, u16)` (`B2-1`, offsets `[0, 2]`, size `4`) satisfies
`IsIntoBytes`, `IsFromBytes`, `IsFromZeros`, and non-vacuous `IsTryFromBytes` purely
via `padRight_zero_isInitCodec` and combinator lemmas. -/
theorem mirLaidOutU16Pair_all_marker_traits :
    IsIntoBytes testLayouts { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 3 } ∧
    IsFromBytes testLayouts { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 3 } ∧
    IsFromZeros testLayouts { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 3 } ∧
    IsTryFromBytes testLayouts { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 3 }
      (fun v =>
        ∃ a b, a < 2 ^ 16 ∧ b < 2 ^ 16 ∧
          v = .aggregate 0 [.scalar ⟨a, 2⟩, .scalar ⟨b, 2⟩]) :=
  ⟨mirLaidOutU16Pair.isIntoBytes
     (FixedByteCodec.prod_isInitCodec
       (FixedByteCodec.padRight_zero_isInitCodec
         (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide)))
       (FixedByteCodec.padRight_zero_isInitCodec
         (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide)))),
   mirLaidOutU16Pair.isFromBytes
     (FixedByteCodec.prod_isSurjectiveInitDecoder
       (FixedByteCodec.padRight_isSurjectiveInitDecoder 0
         (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide)))
       (FixedByteCodec.padRight_isSurjectiveInitDecoder 0
         (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide)))),
   mirLaidOutU16Pair.isFromZeros
     (FixedByteCodec.prod_hasZeroValid
       (FixedByteCodec.padRight_hasZeroValid 0
         (FixedByteCodec.uintBitsLE_hasZeroValid 2 (by decide)))
       (FixedByteCodec.padRight_hasZeroValid 0
         (FixedByteCodec.uintBitsLE_hasZeroValid 2 (by decide)))),
   mirLaidOutU16Pair.isTryFromBytes_of
     (fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ => ⟨a, b, ha, hb, rfl⟩)⟩

/-- Bidirectional `transmute_sound` for real laid-out `(u16, u16)` (`B2-1`):
`(u16, u16) → u32` and `[u8; 4] → (u16, u16)`. -/
theorem transmute_laidOutU16Pair_to_u32_sound
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel testLayouts
      { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 3 } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel testLayouts
      { kind := .uint .u32, layoutIdx := 0 } bs = some v' :=
  MirValueCodec.transmute_sound mirLaidOutU16Pair mirU32
    (FixedByteCodec.prod_isInitCodec
      (FixedByteCodec.padRight_zero_isInitCodec
        (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide)))
      (FixedByteCodec.padRight_zero_isInitCodec
        (FixedByteCodec.uintBitsLE_isInitCodec 2 (by decide))))
    (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide))
    v bs hEnc

theorem transmute_u8x4_to_laidOutU16Pair_sound
    (v : Value) (bs : List AbstractByte)
    (hEnc : encodeValueToBytes defaultCodecFuel testLayouts
      { kind := .array (.uint .u8) 4, layoutIdx := 0 } v = some bs) :
    ∃ v', decodeValueFromBytes defaultCodecFuel testLayouts
      { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 3 } bs = some v' :=
  MirValueCodec.transmute_sound mirU8x4 mirLaidOutU16Pair
    (FixedByteCodec.listFixed_isInitCodec 4 (FixedByteCodec.uintBitsLE_isInitCodec 1 (by decide)))
    (FixedByteCodec.prod_isSurjectiveInitDecoder
      (FixedByteCodec.padRight_isSurjectiveInitDecoder 0
        (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide)))
      (FixedByteCodec.padRight_isSurjectiveInitDecoder 0
        (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide))))
    v bs hEnc

/-! ## 4. Fuel-Free Structural Recursion (`termination_by`) via `sizeOf_lt_*` -/

/-- Custom fuel-free scalar-leaf collector over `RigidTy` exercising `sizeOf_lt_*` directly. -/
def countPrimitiveLeaves : RigidTy → Nat
  | .bool | .char | .int _ | .uint _ | .float _ => 1
  | .array elem _ => countPrimitiveLeaves elem
  | .slice elem => countPrimitiveLeaves elem
  | .ref _ pointee => countPrimitiveLeaves pointee
  | .rawPtr _ pointee => countPrimitiveLeaves pointee
  | .tuple fields =>
    fields.attach.foldl (fun acc ⟨f, _⟩ => acc + countPrimitiveLeaves f) 0
  | .adt _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc + countPrimitiveLeaves a) 0
  | .alias _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc + countPrimitiveLeaves a) 0
  | .fnDef _ args =>
    args.attach.foldl (fun acc ⟨a, _⟩ => acc + countPrimitiveLeaves a) 0
  | .fnPtr inputs output _ _ =>
    countPrimitiveLeaves output +
      inputs.attach.foldl (fun acc ⟨inp, _⟩ => acc + countPrimitiveLeaves inp) 0
  | .closure _ upvars =>
    upvars.attach.foldl (fun acc ⟨u, _⟩ => acc + countPrimitiveLeaves u) 0
  | _ => 0
termination_by r => sizeOf r
decreasing_by
  · exact sizeOf_lt_elem_of_array _ _
  · exact sizeOf_lt_elem_of_slice _
  · exact sizeOf_lt_pointee_of_ref _ _
  · exact sizeOf_lt_pointee_of_rawPtr _ _
  · exact sizeOf_lt_of_mem_tuple_fields ‹_›
  · exact sizeOf_lt_of_mem_adt_args _ ‹_›
  · exact sizeOf_lt_of_mem_alias_args _ ‹_›
  · exact sizeOf_lt_of_mem_fnDef_args _ ‹_›
  · exact sizeOf_lt_output_of_fnPtr _ _ _ _
  · exact sizeOf_lt_of_mem_fnPtr_inputs _ _ _ ‹_›
  · exact sizeOf_lt_of_mem_closure_upvars _ ‹_›

theorem countPrimitiveLeaves_sample :
    countPrimitiveLeaves (.tuple [.bool, .array (.uint .u32) 4, .ref .not .char]) = 3 := by
  simp [countPrimitiveLeaves]

theorem rigidTyNodeCount_sample :
    rigidTyNodeCount (.tuple [.bool, .ref .not (.slice (.uint .u8))]) = 5 := by
  simp [rigidTyNodeCount]

/-- Build a unary nested `Value.aggregate` chain of depth `d` wrapping a 1-byte `0x2a` scalar. -/
def nestedAggregateDepth : Nat → Value
  | 0 => .scalar ⟨0x2a, 1⟩
  | d + 1 => .aggregate 0 [nestedAggregateDepth d]

theorem valueAggregateDepth_nestedAggregateDepth :
    ∀ d : Nat, valueAggregateDepth (nestedAggregateDepth d) = d
  | 0 => by rw [nestedAggregateDepth, valueAggregateDepth]
  | d + 1 => by
    rw [nestedAggregateDepth, valueAggregateDepth,
        foldr_attach_cons (nestedAggregateDepth d) []
          (fun g acc => Nat.max (valueAggregateDepth g) acc) 0]
    have hNil : ([].attach.foldr (fun ⟨g, _⟩ acc => Nat.max (valueAggregateDepth g) acc) 0) = 0 := rfl
    rw [hNil, valueAggregateDepth_nestedAggregateDepth d]
    simp only [Nat.max_def]
    split <;> omega

/-- At depth `20 > defaultCodecFuel` (`16`), `Trusted`'s `encodeUntypedValueToBytes`
exhausts `defaultCodecFuel` (`= none`), stabilizes at `fuel = 21` (`= some [0x2a]`),
and `encodeUntypedValueFuelFree` is proved equal to `Trusted`'s encoder via
`encodeUntypedValueToBytes_eq_some_imp_fuelFree` and `encodeUntypedValueToBytes_eq_fuelFree_of_depth_lt` (`B2-3`). -/
theorem fuelFree_succeeds_beyond_defaultCodecFuel :
    encodeUntypedValueToBytes defaultCodecFuel (nestedAggregateDepth 20) = none ∧
    encodeUntypedValueToBytes 21 (nestedAggregateDepth 20) =
      some [.init (UInt8.ofNat 0x2a) none] ∧
    encodeUntypedValueFuelFree (nestedAggregateDepth 20) =
      some [.init (UInt8.ofNat 0x2a) none] ∧
    (∀ fuel : Nat, 20 < fuel →
      encodeUntypedValueToBytes fuel (nestedAggregateDepth 20) =
        encodeUntypedValueFuelFree (nestedAggregateDepth 20)) ∧
    valueNodeCount (nestedAggregateDepth 20) = 21 := by
  have hFuel21 :
      encodeUntypedValueToBytes 21 (nestedAggregateDepth 20) =
        some [.init (UInt8.ofNat 0x2a) none] := rfl
  refine ⟨rfl,
          hFuel21,
          encodeUntypedValueToBytes_eq_some_imp_fuelFree 21
            (nestedAggregateDepth 20) [.init (UInt8.ofNat 0x2a) none] hFuel21,
          fun fuel hGt =>
            encodeUntypedValueToBytes_eq_fuelFree_of_depth_lt fuel (nestedAggregateDepth 20)
              (by rw [valueAggregateDepth_nestedAggregateDepth 20]; exact hGt),
          ?_⟩
  simp [nestedAggregateDepth, valueNodeCount]

/-! ## 5. Kernel `rfl` Reductions & Characterizations of `RigidTy` Predicates -/

example : isBoolRigidTy .bool = true := rfl
example : isBoolRigidTy .char = false := rfl
example : isCharRigidTy .char = true := rfl
example : isCharRigidTy (.uint .u32) = false := rfl
example : isUnitTupleRigidTy (.tuple []) = true := rfl
example : isUnitTupleRigidTy (.tuple [.bool]) = false := rfl
example : isWidePointeeRigidTy (.slice (.uint .u8)) = true := rfl
example : isWidePointeeRigidTy .str = true := rfl
example : isWidePointeeRigidTy (.dynamic "core::fmt::Debug") = true := rfl
example : isWidePointeeRigidTy (.uint .u64) = false := rfl
example : isWidePtrRigidTy (.ref .not .str) = true := rfl
example : isWidePtrRigidTy (.rawPtr .mut (.slice .bool)) = true := rfl
example : isWidePtrRigidTy (.ref .not (.uint .u32)) = false := rfl
example : isThinPtrRigidTy (.ref .not (.uint .u32)) = true := rfl
example : isThinPtrRigidTy (.rawPtr .mut .bool) = true := rfl
example : isThinPtrRigidTy (.fnPtr [.bool] (.tuple []) .safe .rust) = true := rfl
example : isThinPtrRigidTy (.ref .not .str) = false := rfl

theorem rigidTy_predicate_characterizations_and_sizes (r : RigidTy) :
    (isBoolRigidTy r = true ↔ r = .bool) ∧
    (isCharRigidTy r = true ↔ r = .char) ∧
    (isUnitTupleRigidTy r = true ↔ r = .tuple []) ∧
    (isThinPtrRigidTy r = true → isWidePtrRigidTy r = false ∧ rigidTyKindByteSize r = some 8) ∧
    (isWidePtrRigidTy r = true → isThinPtrRigidTy r = false ∧ rigidTyKindByteSize r = some 16) := by
  refine ⟨isBoolRigidTy_eq_true_iff r,
          isCharRigidTy_eq_true_iff r,
          isUnitTupleRigidTy_eq_true_iff r,
          fun hThin => ⟨isWidePtrRigidTy_eq_false_of_isThinPtrRigidTy hThin,
                        rigidTyKindByteSize_eq_eight_of_isThinPtrRigidTy hThin⟩,
          fun hWide => ⟨isThinPtrRigidTy_eq_false_of_isWidePtrRigidTy hWide,
                        rigidTyKindByteSize_eq_sixteen_of_isWidePtrRigidTy hWide⟩⟩

end Anneal.ByteCodecTests
