import Anneal.BitValidity

namespace Anneal.BitValidityStage1Tests

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Anneal.BitValidity

/-!
# Concrete Regression Tests for `Anneal.BitValidity` Section 7

Section 7 states its Stage-1 bridges over arbitrary layout tables, with many
layout hypotheses. Each test below instantiates one of them on the concrete
table `stage1Layouts` and discharges every hypothesis by `rfl`, so the
hypotheses are jointly satisfiable and the theorem is not vacuous. The tests
also run the executed decoder `decodeTypedValueFromBytes` directly on concrete
byte images.
-/

/-- `NonZero<u32>` newtype: the niche is on the backend scalar, with no field layouts. -/
def newtypeNonZeroU32Layout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := []
}

/-- A two-byte pair whose second half is a `NonMax<u8>`-style scalar (`0..=254`). -/
def nonMaxPairLayout : TypeLayout := {
  size := { bytes := 2 }
  align := { bytes := 1 }
  backendRepr :=
    .scalarPair (.initialized (.int 8 false) ⟨0, 255⟩)
      (.initialized (.int 8 false) ⟨0, 254⟩)
  fields := .arbitrary [{ bytes := 0 }, { bytes := 1 }] [0, 1]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := []
}

/-- `.primitive` `u32` field layout that records the `NonZero` niche. -/
def nonZeroU32PrimLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/-- A `u32` wrapper with a full-range backend whose field layout (index 2) is `NonZero`. -/
def wrapperWithNicheFieldLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨0, scalarModulus 4 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [2]
}

/-- Unpadded `(u16, u16)` struct decoded through its `.scalarPair` backend. -/
def u16PairLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 2 }
  backendRepr :=
    .scalarPair (.initialized (.int 16 false) ⟨0, 65535⟩)
      (.initialized (.int 16 false) ⟨0, 65535⟩)
  fields := .arbitrary [{ bytes := 0 }, { bytes := 2 }] [0, 1]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := []
}

/-- Fieldless `#[repr(u8)]` enum with three variants (`0..=2`). -/
def ordering3EnumLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 2⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 8 false) ⟨0, 2⟩) 0
    [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []]
  isUninhabited := false
}

/-- `#[repr(C)] struct Packet { header: [u8; 4], tag: u32 }` with field layouts 7 and 9. -/
def packetLayout : TypeLayout := {
  size := { bytes := 8 }
  align := { bytes := 4 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [7, 9]
}

/-- `[u8; 4]` array field layout with element field layout 8. -/
def u8x4ArrayLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .array { bytes := 1 } 4
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [8]
}

/-- Full-range `.primitive` `u8` field layout. -/
def u8PrimLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/-- Full-range `.primitive` `u32` field layout. -/
def u32PrimLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨0, scalarModulus 4 - 1⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/-- Single-field wrapper whose field layout (index 11) is itself a struct. -/
def outerWrapperLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 2 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [11]
}

/-- `(u16, u16)` struct whose field layouts are both index 12. -/
def innerU16PairLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 2 }
  backendRepr := .memory
  fields := .arbitrary [{ bytes := 0 }, { bytes := 2 }] [0, 1]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [12, 12]
}

/-- Full-range `.primitive` `u16` field layout. -/
def u16PrimLayout : TypeLayout := {
  size := { bytes := 2 }
  align := { bytes := 2 }
  backendRepr := .scalar (.initialized (.int 16 false) ⟨0, 65535⟩)
  fields := .primitive
  variants := .single 0
  isUninhabited := false
}

/-- Wrapper with a `NonZero` outer backend whose `fieldLayouts := [9]` points to
full-range `u32`. -/
def outerNicheWrapperLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := [9]
}

/-- Full-range 256-variant fieldless `#[repr(u8)]` enum (`0..=255`). -/
def byteTag256EnumLayout : TypeLayout := {
  size := { bytes := 1 }
  align := { bytes := 1 }
  backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .multiple (.initialized (.int 8 false) ⟨0, 255⟩) 0
    (List.replicate 256 (.arbitrary [] []))
  isUninhabited := false
}

def stage1Layouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [
    newtypeNonZeroU32Layout,
    nonMaxPairLayout,
    nonZeroU32PrimLayout,
    wrapperWithNicheFieldLayout,
    u16PairLayout,
    ordering3EnumLayout,
    packetLayout,
    u8x4ArrayLayout,
    u8PrimLayout,
    u32PrimLayout,
    outerWrapperLayout,
    innerU16PairLayout,
    u16PrimLayout,
    outerNicheWrapperLayout,
    byteTag256EnumLayout
  ]
}

def nonZeroU32Ty : Ty := { kind := .adt "core::num::NonZero" [.uint .u32], layoutIdx := 0 }

/-! ## Scalar niches for every list of type arguments -/

/-- The legacy decoder accepts all-zero bytes at `NonZero<u32>`; Stage-1 rejects them. -/
theorem nonZeroU32_stage1_niche_enforced :
    decodeTypedValueFromBytes defaultCodecFuel stage1Layouts nonZeroU32Ty (zeroInitBytes 4) =
      none ∧
    ¬ IsFromZerosTyped stage1Layouts nonZeroU32Ty ∧
    IsFromZeros stage1Layouts nonZeroU32Ty ∧
    checkFromBytesNicheAware stage1Layouts nonZeroU32Ty = false :=
  adt_generic_nonZero_typeArg_stage1_niche_enforced stage1Layouts _ 0 newtypeNonZeroU32Layout 0
    [0] rfl rfl rfl rfl rfl rfl rfl

theorem nonZeroU32_stage1_accepts_five :
    decodeTypedValueFromBytes defaultCodecFuel stage1Layouts nonZeroU32Ty
        (encodeLittleEndianBytes 5 4 none) =
      some (.aggregate 0 [.scalar ⟨5, 4⟩]) := by
  rfl

theorem nonZeroU32_stage1_rejects_provenance :
    decodeTypedValueFromBytes defaultCodecFuel stage1Layouts nonZeroU32Ty
        (encodeLittleEndianBytes 5 4 (some (3, 0))) = none := by
  rfl

/-! ## `checkBackendReprFullRange` on `.scalarPair` -/

theorem nonMaxPair_rejected :
    checkBackendReprFullRange nonMaxPairLayout = false ∧
    decodeTypedValueFromBytes defaultCodecFuel stage1Layouts
        { kind := .adt "NonMaxPair" [], layoutIdx := 1 }
        [.init (UInt8.ofNat 0) none, .init (UInt8.ofNat 255) none] = none ∧
    ¬ IsFromBytesTyped stage1Layouts { kind := .adt "NonMaxPair" [], layoutIdx := 1 } :=
  checkBackendReprFullRange_scalarPair_nonMax stage1Layouts _ [] 1 nonMaxPairLayout 0 [0, 1]
    rfl rfl rfl rfl rfl rfl rfl

/-! ## Stage-1 soundness of `checkFromBytesNicheAware` -/

def u16PairTy : Ty := { kind := .adt "Pair" [.uint .u16, .uint .u16], layoutIdx := 4 }

theorem u16Pair_stage1_fromBytes :
    IsFromBytesTyped stage1Layouts u16PairTy ∧ IsFromZerosTyped stage1Layouts u16PairTy :=
  checkFromBytesNicheAware_stage1_sound stage1Layouts _ rfl rfl

/-- The wrapper passes `checkFromBytesNicheAware` but is not Stage-1 `FromBytes`. -/
example :=
  checkFromBytesNicheAware_ignores_fieldLayouts stage1Layouts "Wrapper" 3 2
    wrapperWithNicheFieldLayout nonZeroU32PrimLayout 0 0 [0]
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `Packet` (with populated field layouts) is Stage-1 `FromBytes` and `FromZeros`. -/
example :=
  checkFromBytesNicheAware_composite_fieldLayouts_stage1_sound stage1Layouts "Packet" 6 7 8 9
    packetLayout u8x4ArrayLayout u8PrimLayout u32PrimLayout
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rfl rfl

/-! ## `char` surrogates and enum tags -/

theorem char_surrogate_rejected :
    decodeScalarLayoutBytesNoForge (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩)
        (encodeLittleEndianBytes 0xD800 4 none) = none ∧
    decodeScalarLayoutBytes (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩)
        (encodeLittleEndianBytes 0xD800 4 none) = some (.scalar ⟨0xD800, 4⟩) :=
  (decodeScalarLayoutBytesNoForge_charLayout_iff false 0xD800 (by decide)).2 (by decide)
    (by decide)

theorem ordering3_stage1_accepts_tag_provenance :
    decodeTypedValueFromBytes defaultCodecFuel stage1Layouts
        { kind := .adt "Ordering3" [], layoutIdx := 5 }
        [.init (UInt8.ofNat 1) (some (7, 0))] =
      some (.aggregate 1 []) := by
  rfl

/-- Every in-range tag of `Ordering3` indexes a fieldless variant. -/
theorem ordering3_fieldless :
    ∀ tag < scalarModulus 1, wrappingRangeContains ⟨0, 2⟩ tag = true →
      ∃ varMemOrder,
        get? [FieldsShape.arbitrary [] [], .arbitrary [] [], .arbitrary [] []] tag =
          some (.arbitrary [] varMemOrder) := by
  intro tag _ hIn
  have hLe : tag ≤ 2 := (wrappingRangeContains_zero_max_iff 2 tag).mp hIn
  match tag, hLe with
  | 0, _ => exact ⟨[], rfl⟩
  | 1, _ => exact ⟨[], rfl⟩
  | 2, _ => exact ⟨[], rfl⟩

/-- `Ordering3` decodes exactly its three tags and is Stage-1 `FromZeros`. -/
example :=
  adt_multiple_fieldless_enum_stage1 stage1Layouts "Ordering3" [] 5 ordering3EnumLayout 8 false
    ⟨0, 2⟩ [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []] [0]
    rfl rfl rfl rfl rfl rfl ordering3_fieldless

/-- A wrapper around a nested `(u16, u16)` struct is Stage-1 `FromBytes`. -/
example :=
  adt_nested_struct_fieldLayouts_isFromBytesTyped stage1Layouts "Outer" [] 10 11 12
    outerWrapperLayout innerU16PairLayout u16PrimLayout
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- `[u8; 4]` at its resolved array layout index (`7`) satisfies Stage-1 `FromBytes`. -/
theorem u8x4_resolvedLayout_isFromBytesTyped :
    IsFromBytesTyped stage1Layouts { kind := .array (.uint .u8) 4, layoutIdx := 7 } :=
  checkBaseFromBytesKind_isFromBytesTyped stage1Layouts (.array (.uint .u8) 4) 7 rfl rfl

/-- Inner `.primitive` field layout niche enforcement (`adt_fieldLayout_inner_primitive_stage1`). -/
example :=
  adt_fieldLayout_inner_primitive_stage1 stage1Layouts "Wrapper" [.uint .u32] 3 2
    wrapperWithNicheFieldLayout nonZeroU32PrimLayout 0 0 32 [0] false ⟨1, scalarModulus 4 - 1⟩
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

/-- Outer niche ignored when `fieldLayouts` points to a full-range inner `.primitive` layout. -/
theorem outerNicheWrapper_unenforced_stage1 :
    wrappingRangeContains ⟨1, scalarModulus 4 - 1⟩ 0 = false ∧
    decodeTypedValueFromBytes defaultCodecFuel stage1Layouts
        { kind := .adt "OuterNiche" [.uint .u32], layoutIdx := 13 } (zeroInitBytes 4) =
      some (.aggregate 0 [.scalar ⟨0, 4⟩]) ∧
    IsFromZerosTyped stage1Layouts { kind := .adt "OuterNiche" [.uint .u32], layoutIdx := 13 } :=
  adt_fieldLayout_path_outer_niche_unenforced_stage1 stage1Layouts "OuterNiche" [.uint .u32] 13 9
    outerNicheWrapperLayout u32PrimLayout 0 0 [0]
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

theorem byteTag256_fieldless :
    ∀ tag < scalarModulus 1,
      ∃ varMemOrder,
        get? (List.replicate 256 (FieldsShape.arbitrary [] [])) tag =
          some (.arbitrary [] varMemOrder) := by
  intro tag hLt
  have hLt256 : tag < 256 := by
    rw [Anneal.Scalars.scalarModulus_eq_two_pow] at hLt
    omega
  refine ⟨[], ?_⟩
  show (List.replicate 256 (FieldsShape.arbitrary [] []))[tag]? = some (.arbitrary [] [])
  rw [List.getElem?_replicate]
  simp [hLt256]

/-- Full-range 256-variant fieldless `#[repr(u8)]` enum is Stage-1 `FromBytes`. -/
theorem byteTag256_isFromBytesTyped :
    IsFromBytesTyped stage1Layouts { kind := .adt "ByteTag256" [], layoutIdx := 14 } :=
  adt_multiple_fieldless_enum_fullRange_isFromBytesTyped stage1Layouts "ByteTag256" [] 14
    byteTag256EnumLayout 8 false ⟨0, 255⟩ (List.replicate 256 (.arbitrary [] [])) [0]
    rfl rfl rfl rfl rfl rfl rfl (by decide) byteTag256_fieldless

end Anneal.BitValidityStage1Tests
