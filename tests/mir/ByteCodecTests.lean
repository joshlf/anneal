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

/-! ## 2. Negative Tests: Niche Rejection, `bool` Bit Patterns, and Padding `¬ IsInitCodec` -/

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

def testLayouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [nonZeroU32Layout, paddedU16TupleLayout]
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
    MirValueCodec testLayouts { kind := .tuple [.uint .u16, .uint .u16], layoutIdx := 2 }
      ({ bits : Nat // bits < 2 ^ (8 * 2) } × { bits : Nat // bits < 2 ^ (8 * 2) })
      4 :=
  MirValueCodec.uintPairTuple testLayouts .u16 .u16 2 rfl

def mirPaddedU16Tuple :
    MirValueCodec testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 }
      { bits : Nat // bits < 2 ^ (8 * 2) }
      4 :=
  MirValueCodec.paddedSingleElemTuple testLayouts .u16 2 1 paddedU16TupleLayout rfl rfl rfl

/-- `u32` satisfies all four zerocopy marker traits (`IntoBytes`, `FromBytes`, `FromZeros`, `TryFromBytes`). -/
theorem mirU32_all_marker_traits :
    IsIntoBytes testLayouts { kind := .uint .u32, layoutIdx := 0 } ∧
    IsFromBytes testLayouts { kind := .uint .u32, layoutIdx := 0 } ∧
    IsFromZeros testLayouts { kind := .uint .u32, layoutIdx := 0 } ∧
    IsTryFromBytes testLayouts { kind := .uint .u32, layoutIdx := 0 } :=
  ⟨mirU32.isIntoBytes (FixedByteCodec.uintBitsLE_isInitCodec 4 (by decide)),
   mirU32.isFromBytes (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 4 (by decide)),
   mirU32.isFromZeros (FixedByteCodec.uintBitsLE_hasZeroValid 4 (by decide)),
   mirU32.isTryFromBytes_trivial⟩

/-- `bool` is `IntoBytes`, `FromZeros`, and `TryFromBytes`, but NOT `FromBytes`. -/
theorem mirBool_marker_traits_and_not_fromBytes :
    IsIntoBytes testLayouts { kind := .bool, layoutIdx := 0 } ∧
    IsFromZeros testLayouts { kind := .bool, layoutIdx := 0 } ∧
    IsTryFromBytes testLayouts { kind := .bool, layoutIdx := 0 } ∧
    ¬ IsFromBytes testLayouts { kind := .bool, layoutIdx := 0 } :=
  ⟨mirBool.isIntoBytes FixedByteCodec.boolByte_isInitCodec,
   mirBool.isFromZeros FixedByteCodec.boolByte_hasZeroValid,
   mirBool.isTryFromBytes_trivial,
   mirBool.not_isFromBytes_of_rejected_init
     (bs := [.init (UInt8.ofNat 2) none]) rfl rfl boolByte_rejects_two⟩

/-- `NonZeroU32` is `IntoBytes` and `TryFromBytes`, but NOT `FromBytes` (`0` is rejected). -/
theorem mirNonZeroU32_into_and_not_fromBytes :
    IsIntoBytes testLayouts { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 } ∧
    IsTryFromBytes testLayouts { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 } ∧
    ¬ IsFromBytes testLayouts { kind := .adt "core::num::NonZeroU32" [], layoutIdx := 0 } :=
  ⟨mirNonZeroU32.isIntoBytes
     (FixedByteCodec.scalarValidRange_isInitCodec 4 (by decide) nonZeroU32Range),
   mirNonZeroU32.isTryFromBytes_trivial,
   mirNonZeroU32.not_isFromBytes_of_rejected_init
     (bs := encodeLittleEndianBytes 0 4 none)
     (length_encodeLittleEndianBytes none 4 0)
     (allBytesInitialized_encodeLittleEndianBytes none 4 0)
     nonZeroU32ScalarValidRange_rejects_zero⟩

/-- Padded `(u16,)` (2-byte field + 2-byte trailing padding) is `FromBytes`, `FromZeros`,
and `TryFromBytes`, but NOT `IntoBytes`! -/
theorem mirPaddedU16Tuple_fromBytes_and_not_intoBytes :
    IsFromBytes testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 } ∧
    IsFromZeros testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 } ∧
    IsTryFromBytes testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 } ∧
    ¬ IsIntoBytes testLayouts { kind := .tuple [.uint .u16], layoutIdx := 1 } :=
  ⟨mirPaddedU16Tuple.isFromBytes
     (FixedByteCodec.padRight_isSurjectiveInitDecoder 2
       (FixedByteCodec.uintBitsLE_isSurjectiveInitDecoder 2 (by decide))),
   mirPaddedU16Tuple.isFromZeros
     (FixedByteCodec.padRight_hasZeroValid 2
       (FixedByteCodec.uintBitsLE_hasZeroValid 2 (by decide))),
   mirPaddedU16Tuple.isTryFromBytes_trivial,
   mirPaddedU16Tuple.not_isIntoBytes_of_uninit_encode
     ⟨0x0042, by decide⟩
     (FixedByteCodec.allBytesInitialized_padRight_encode_eq_false
       (FixedByteCodec.uintBitsLE 2 (by decide)) (by decide) ⟨0x0042, by decide⟩)⟩

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

/-- At depth `20 > defaultCodecFuel` (`16`), the fuel-bounded `encodeUntypedValueToBytes`
exhausts fuel and returns `none`, whereas fuel-free `encodeUntypedValueFuelFree`
succeeds! -/
theorem fuelFree_succeeds_beyond_defaultCodecFuel :
    encodeUntypedValueToBytes defaultCodecFuel (nestedAggregateDepth 20) = none ∧
    encodeUntypedValueFuelFree (nestedAggregateDepth 20) =
      some [.init (UInt8.ofNat 0x2a) none] ∧
    valueNodeCount (nestedAggregateDepth 20) = 21 := by
  refine ⟨rfl, ?_, ?_⟩
  · simp [nestedAggregateDepth, encodeUntypedValueFuelFree, encodeScalarBytes, encodeLittleEndianBytes]
  · simp [nestedAggregateDepth, valueNodeCount]

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
