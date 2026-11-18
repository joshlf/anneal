import Anneal.Mir.Cast

namespace Anneal.CastStage1Tests

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult
open Trusted.Rustc.V2026_06_01.MirSemantics (decodeTypedValueFromBytes decodePtrBytesNoForge
  decodeScalarLayoutBytesNoForge abstractBytesUniformProv layoutPointerBytes
  FloatIntTarget IeeeFormat TreeBorrowPerm)
open Anneal.BitValidity
open Anneal.Mir
open Anneal.Mir.Cast

/-!
# Concrete Non-Vacuity Tests for `Anneal.Mir.Cast` Sections 8.5–8.7 and 10

Instantiates the Stage-1 provenance no-forge pointer characterizations (§8.5),
function-pointer bridges (§8.6), `ByteCodec.scalarNicheNewtype` step-level
`evalByteCast` / `evalRvalue` bridges (§8.7), and the IEEE-754 `f32` / `f64`
numeric-cast step theorems (§10) on a concrete 64-bit `LayoutTable`,
`LocalDecl` list, `LocalSlot` environment, and `emptyMemory`.
-/

/-- Placeholder ZST layout at index `0` (`unresolvedLayoutIdx`), so ADT targets sit at `idx ≥ 1`. -/
def unitPlaceholderLayout : TypeLayout := {
  size := { bytes := 0 }
  align := { bytes := 1 }
  backendRepr := .memory
  fields := .arbitrary [] []
  variants := .single 0
  isUninhabited := false
}

/-- `NonZero<u32>` newtype layout at resolved `layoutIdx = 1 ≠ 0`. -/
def nonZeroU32CastLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨1, scalarModulus 4 - 1⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := []
}

/-- Transparent `char`-range (`0..=0x10FFFF`) 4-byte newtype layout at resolved `layoutIdx = 2`. -/
def charRangeNewtypeLayout : TypeLayout := {
  size := { bytes := 4 }
  align := { bytes := 4 }
  backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩)
  fields := .arbitrary [{ bytes := 0 }] [0]
  variants := .single 0
  isUninhabited := false
  fieldLayouts := []
}

def castStage1Layouts : LayoutTable := {
  pointerBits := 64
  isLittleEndian := true
  entries := [unitPlaceholderLayout, nonZeroU32CastLayout, charRangeNewtypeLayout]
}

def samplePtr : ProvenancePtr := { allocId := 7, offsetBytes := 16 }

def castLocalDecls : List LocalDecl := [
  { mutability := .not, ty := { kind := .uint .u64, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 },
    debugName := none },
  { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := none }
]

def castLocals : List LocalSlot := [
  .init (.scalar ⟨42, 8⟩),
  .init (.ptr samplePtr 8),
  .init (.scalar ⟨5, 4⟩),
  .init (.scalar ⟨0, 4⟩)
]

def sampleFnPtrTy : Ty :=
  { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 0 }

def sampleRawPtrTy : Ty :=
  { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }

def nonZeroU32DstTy : Ty :=
  { kind := .adt "core::num::NonZero" [.uint .u32], layoutIdx := 1 }

/-! ## Section 8.5: Exact Pointer & `ScalarLayout` No-Forge Characterizations -/

theorem ptrBytesNoForge_ref_intact_and_provFree :
    decodePtrBytesNoForge true (.uint .u8) 8
        (encodeLittleEndianBytes 16 8 (some (7, 7))) = some (.ptr samplePtr 8) ∧
    (decodePtrBytesNoForge true (.uint .u8) 8 (encodeLittleEndianBytes 16 8 none) = none ↔
      Trusted.Sequence.length (encodeLittleEndianBytes 16 8 none) ≠ 8 ∨
      decodeScalarBytes (encodeLittleEndianBytes 16 8 none) false = none ∨
      abstractBytesUniformProv (encodeLittleEndianBytes 16 8 none) = false) :=
  ⟨by rfl, trusted_decodePtrBytesNoForge_thin_ref_eq_none_iff (.uint .u8) 8 _ rfl⟩

theorem scalarLayoutNoForge_nonNullPtr_range_enforced :
    decodeScalarLayoutBytesNoForge
        (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
        (encodeLittleEndianBytes 16 8 (some (7, 7))) = some (.ptr samplePtr 8) ∧
    decodeScalarLayoutBytesNoForge
        (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
        (encodeLittleEndianBytes 42 8 none) = some (.scalar ⟨42, 8⟩) ∧
    decodeScalarLayoutBytesNoForge
        (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
        (encodeLittleEndianBytes 0 8 none) = none ∧
    decodeScalarLayoutBytesNoForge
        (.union (.pointer 0))
        (encodeLittleEndianBytes 0 8 none) = some (.scalar ⟨0, 8⟩) := by
  have h1 : decodeScalarLayoutBytesNoForge
      (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
      (encodeLittleEndianBytes 16 8 (some (7, 7))) = some (.ptr samplePtr 8) :=
    (trusted_decodeScalarLayoutBytesNoForge_initialized_pointer_eq_ptr_iff 0 _ _ samplePtr).mpr
      ⟨rfl, rfl, ⟨16, 8⟩, 7, 7, rfl, rfl⟩
  have h2 : decodeScalarLayoutBytesNoForge
      (.initialized (.pointer 0) ⟨1, scalarModulus 8 - 1⟩)
      (encodeLittleEndianBytes 42 8 none) = some (.scalar ⟨42, 8⟩) :=
    (trusted_decodeScalarLayoutBytesNoForge_initialized_pointer_not_uniform_eq_scalar_iff
      0 ⟨1, scalarModulus 8 - 1⟩ (encodeLittleEndianBytes 42 8 none) ⟨42, 8⟩ none
      rfl rfl rfl).mpr (by decide)
  have h4 : decodeScalarLayoutBytesNoForge (.union (.pointer 0))
      (encodeLittleEndianBytes 0 8 none) = some (.scalar ⟨0, 8⟩) :=
    trusted_decodeScalarLayoutBytesNoForge_union_pointer_not_uniform_eq 0
      (encodeLittleEndianBytes 0 8 none) ⟨0, 8⟩ none rfl rfl rfl
  exact ⟨h1, h2, rfl, h4⟩

/-! ## Section 8.6: Function Pointers (`RigidTy.fnPtr`) vs Raw Pointers -/

/-- Intact / provenance-free `fnPtr` decoding through the Stage-1 bridges, and the byte-overwrite
no-forge agreement on a concrete pointer (decided by kernel evaluation: the general
`trusted_vs_anneal_overwrite_provenance_no_forge_agreement_fnPtr` depends on
`Classical.choice`, which this file excludes). -/
theorem fnPtr_intact_vs_provFree_and_overwrite :
    decodeTypedValueFromBytes defaultCodecFuel castStage1Layouts sampleFnPtrTy
        (encodeLittleEndianBytes 16 8 (some (7, 7))) = some (.ptr samplePtr 8) ∧
    decodeTypedValueFromBytes defaultCodecFuel castStage1Layouts sampleFnPtrTy
        (encodeLittleEndianBytes 42 8 none) = none ∧
    (let bytes := (encodeCastBytes 16 8 (some 7)).set 3 { data := 0xAA, prov := none }
     decodeCastVal .bits64 .rawPtr bytes =
       some (.ptr { allocId := 0, offsetBytes := decodeCastIntBytes bytes } none) ∧
     decodeTypedValueFromBytes defaultCodecFuel castStage1Layouts sampleFnPtrTy
       (bytes.map CastByte.toTrustedAbstractByte) = none) :=
  ⟨trusted_decodeTypedValueFromBytes_fnPtr_intact 15 castStage1Layouts [.uint .u32] (.uint .u32)
      .safe .rust 0 samplePtr rfl (by decide),
   trusted_decodeTypedValueFromBytes_fnPtr_provFree 15 castStage1Layouts [.uint .u32] (.uint .u32)
      .safe .rust 0 42 rfl (by decide),
   ⟨rfl, rfl⟩⟩

theorem step_u64_to_fnPtr_ub_vs_rawPtr_strips_and_ptr_to_fnPtr_preserves :
    (evalByteCast castLocals (.copy ⟨0, []⟩) sampleFnPtrTy emptyMemory castLocalDecls
        castStage1Layouts = ub ∧
     evalRvalue castLocals (.cast .transmute (.copy ⟨0, []⟩) sampleFnPtrTy) emptyMemory
        castLocalDecls castStage1Layouts = ub) ∧
    (evalByteCast castLocals (.copy ⟨0, []⟩) sampleRawPtrTy emptyMemory castLocalDecls
        castStage1Layouts = ok (.scalar ⟨42, 8⟩) castLocals emptyMemory ∧
     evalRvalue castLocals (.cast .transmute (.copy ⟨0, []⟩) sampleRawPtrTy) emptyMemory
        castLocalDecls castStage1Layouts = ok (.scalar ⟨42, 8⟩) castLocals emptyMemory ∧
     evalTransmuteSameSize .bits64 .rejectPtrToInt .u64 .rawPtr (.scalar 42) [] =
       .ok (.ptr { allocId := 0, offsetBytes := 42 } none) []) ∧
    (evalByteCast castLocals (.copy ⟨1, []⟩) sampleFnPtrTy emptyMemory castLocalDecls
        castStage1Layouts = ok (.ptr samplePtr 8) castLocals emptyMemory ∧
     evalRvalue castLocals (.cast .transmute (.copy ⟨1, []⟩) sampleFnPtrTy) emptyMemory
        castLocalDecls castStage1Layouts = ok (.ptr samplePtr 8) castLocals emptyMemory) :=
  ⟨trusted_evalByteCast_u64_to_fnPtr_ub castLocals castLocals (.copy ⟨0, []⟩) emptyMemory
      castLocalDecls castStage1Layouts [.uint .u32] (.uint .u32) .safe .rust 0 0 42 rfl
      (by decide) rfl rfl,
   trusted_evalByteCast_u64_to_thin_rawPtr_strips_provenance .rejectPtrToInt [] castLocals
      castLocals (.copy ⟨0, []⟩) emptyMemory castLocalDecls castStage1Layouts .not (.uint .u8)
      0 0 42 rfl rfl (by decide) rfl rfl,
   trusted_evalByteCast_thin_rawPtr_to_fnPtr_preserves_provenance castLocals castLocals
      (.copy ⟨1, []⟩) emptyMemory castLocalDecls castStage1Layouts .not (.uint .u8) [.uint .u32]
      (.uint .u32) .safe .rust 0 0 samplePtr rfl rfl (by decide) rfl rfl⟩

/-! ## Section 8.7: `ByteCodec.scalarNicheNewtype` ↔ Stage-1 `evalByteCast` / `evalRvalue` -/

/-- Step-level `NonZero<u32>` (`args = [.uint .u32]`, `dstLIdx = 1 ≠ 0`) accepts `5` and rejects
`0`. -/
theorem step_scalarNicheNewtype_nonZeroU32_accepts_five_and_rejects_zero :
    evalRvalue castLocals (.cast .transmute (.copy ⟨2, []⟩) nonZeroU32DstTy) emptyMemory
        castLocalDecls castStage1Layouts =
      ok (.aggregate 0 [.scalar ⟨5, 4⟩]) castLocals emptyMemory ∧
    evalRvalue castLocals (.cast .transmute (.copy ⟨3, []⟩) nonZeroU32DstTy) emptyMemory
        castLocalDecls castStage1Layouts = ub := by
  have h5 := trusted_evalByteCast_scalarNicheNewtype_iff castLocals castLocals (.copy ⟨2, []⟩)
    emptyMemory castLocalDecls castStage1Layouts .not .bool .u32 0 "core::num::NonZero"
    [.uint .u32] 1 nonZeroU32CastLayout 4 32 false 0 [0] ⟨1, scalarModulus 4 - 1⟩ 5
    (by decide) rfl rfl ⟨by decide, trivial⟩ (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) rfl rfl
  have h0 := trusted_evalByteCast_scalarNicheNewtype_iff castLocals castLocals (.copy ⟨3, []⟩)
    emptyMemory castLocalDecls castStage1Layouts .not .bool .u32 0 "core::num::NonZero"
    [.uint .u32] 1 nonZeroU32CastLayout 4 32 false 0 [0] ⟨1, scalarModulus 4 - 1⟩ 0
    (by decide) rfl rfl ⟨by decide, trivial⟩ (by decide) rfl rfl rfl rfl rfl rfl rfl rfl
    (by decide) rfl rfl
  exact ⟨h5.2.2.2.1.mpr (by decide), h0.2.2.2.2.mpr (by decide)⟩

/-- Concrete instantiation of the `char`-range (`0..=0x10FFFF`) surrogate divergence (`0xD800`). -/
theorem scalarNicheNewtype_charRange_surrogate_divergence :
    let c := ByteCodec.MirValueCodec.scalarNicheNewtype castStage1Layouts "CharWrapper" 2
      charRangeNewtypeLayout 4 32 false 0 [0] ⟨0, 0x10FFFF⟩ (by decide) rfl rfl rfl rfl rfl rfl
      rfl rfl
    (∃ x, c.codec.decode (encodeLittleEndianBytes 0xD800 4 none) = some x ∧ x.val = 0xD800) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.decodeValueFromBytes defaultCodecFuel castStage1Layouts
        { kind := .adt "CharWrapper" [], layoutIdx := 2 }
        (encodeLittleEndianBytes 0xD800 4 none) = some (.aggregate 0 [.scalar ⟨0xD800, 4⟩]) ∧
    decodeTypedValueFromBytes defaultCodecFuel castStage1Layouts
        { kind := .adt "CharWrapper" [.char], layoutIdx := 2 }
        (encodeLittleEndianBytes 0xD800 4 none) = none :=
  trusted_decodeTypedValueFromBytes_scalarNicheNewtype_charRange_surrogate_divergence
    castStage1Layouts "CharWrapper" [.char] 2 charRangeNewtypeLayout 32 false 0 [0]
    rfl rfl rfl rfl rfl rfl rfl rfl

/-! ## Section 10: IEEE-754 `f32` / `f64` Numeric Casts (`CastKind.{floatToInt, intToFloat, floatToFloat}`) -/

/-- Float-cast locals: `_0 : f64 = π`, `_1 : f32 = -0.0`, `_2 : i64 = -123`, `_3 : u64 = 2^53 + 3`,
`_4 : f64 = -1e39`, `_5 : isize = -1`. -/
def floatLocalDecls : List LocalDecl := [
  { mutability := .not, ty := { kind := .float .f64, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f32, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .int .i64, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .uint .u64, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .float .f64, layoutIdx := 0 }, debugName := none },
  { mutability := .not, ty := { kind := .int .isize, layoutIdx := 0 }, debugName := none }
]

def floatLocals : List LocalSlot := [
  .init (.scalar ⟨0x400921FB54442D18, 8⟩),
  .init (.scalar ⟨0x80000000, 4⟩),
  .init (.scalar ⟨scalarModulus 8 - 123, 8⟩),
  .init (.scalar ⟨9007199254740995, 8⟩),
  .init (.scalar ⟨0xC8078287F49C4A1D, 8⟩),
  .init (.scalar ⟨scalarModulus 8 - 1, 8⟩)
]

def floatI8Ty : Ty := { kind := .int .i8, layoutIdx := 0 }
def floatU8Ty : Ty := { kind := .uint .u8, layoutIdx := 0 }
def floatF32Ty : Ty := { kind := .float .f32, layoutIdx := 0 }
def floatF64Ty : Ty := { kind := .float .f64, layoutIdx := 0 }
def floatF128Ty : Ty := { kind := .float .f128, layoutIdx := 0 }

/-- Non-vacuity of the step-level soundness theorems: every hypothesis is discharged by `rfl` on a
concrete `evalRvalue` environment (64-bit `castStage1Layouts`), audited as named theorems under
`#print axioms` (`0` `Classical.choice`). -/
theorem evalRvalue_cast_floatToInt_sound_inst :
    ∃ out : ScalarInt,
      evalRvalue floatLocals (.cast .floatToInt (.copy ⟨0, []⟩) floatI8Ty) emptyMemory
          floatLocalDecls castStage1Layouts =
        .ok (.scalar out) floatLocals emptyMemory ∧
      out.sizeBytes * 8 =
        (FloatIntTarget.signed .i8).bitWidth (floatPtrWidthOfLayouts castStage1Layouts) ∧
      intValueOfBits (FloatIntTarget.signed .i8).isSigned
          ((FloatIntTarget.signed .i8).bitWidth (floatPtrWidthOfLayouts castStage1Layouts))
          out.bits =
        floatToIntValue (decodeBits .binary64 0x400921FB54442D18)
          ((FloatIntTarget.signed .i8).minValue (floatPtrWidthOfLayouts castStage1Layouts))
          ((FloatIntTarget.signed .i8).maxValue (floatPtrWidthOfLayouts castStage1Layouts)) ∧
      (IeeeFloatCast.isNaNBits .binary64 0x400921FB54442D18 = true → out.bits = 0) :=
  evalRvalue_cast_floatToInt_sound (locals := floatLocals) (op := .copy ⟨0, []⟩) (dstTy := floatI8Ty)
    (mem := emptyMemory) (localDecls := floatLocalDecls) (layouts := castStage1Layouts)
    (fmt := .binary64) (tgt := .signed .i8) rfl rfl rfl rfl rfl

theorem evalRvalue_cast_floatToFloat_sound_inst :
    ∃ out : ScalarInt,
      evalRvalue floatLocals (.cast .floatToFloat (.copy ⟨0, []⟩) floatF32Ty) emptyMemory
          floatLocalDecls castStage1Layouts =
        .ok (.scalar out) floatLocals emptyMemory ∧
      out.sizeBytes = IeeeFormat.binary32.byteWidth ∧
      (∀ (neg : Bool) (n d : Nat), decodeBits .binary64 0x400921FB54442D18 = .finite neg n d →
        out.bits = roundRatioTiesToEven .binary32 neg n d) ∧
      (IeeeFloatCast.isNaNBits .binary64 0x400921FB54442D18 = true →
        IeeeFloatCast.isNaNBits .binary32 out.bits = true ∧
          IeeeFloatCast.isQuietNaNBits .binary32 out.bits = true) :=
  evalRvalue_cast_floatToFloat_sound (locals := floatLocals) (op := .copy ⟨0, []⟩)
    (dstTy := floatF32Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
    (layouts := castStage1Layouts) (src := .binary64) (dst := .binary32) rfl rfl rfl rfl rfl

theorem evalRvalue_cast_intToFloat_exact_inst :
    ∃ out : ScalarInt,
      evalRvalue floatLocals (.cast .intToFloat (.copy ⟨2, []⟩) floatF64Ty) emptyMemory
          floatLocalDecls castStage1Layouts =
        .ok (.scalar out) floatLocals emptyMemory ∧
      out.sizeBytes = IeeeFormat.binary64.byteWidth ∧
      IeeeFloatCast.floatKindDenotesInt (decodeBits .binary64 out.bits)
        (intValueOfBits (FloatIntTarget.signed .i64).isSigned
          ((FloatIntTarget.signed .i64).bitWidth (floatPtrWidthOfLayouts castStage1Layouts))
          (scalarModulus 8 - 123)) :=
  evalRvalue_cast_intToFloat_exact (locals := floatLocals) (op := .copy ⟨2, []⟩)
    (dstTy := floatF64Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
    (layouts := castStage1Layouts) (fmt := .binary64) (src := .signed .i64) rfl rfl rfl rfl rfl
    (by decide +kernel)

theorem evalRvalue_cast_float_unsupported_of_no_format_inst :
    (evalRvalue floatLocals (.cast .floatToInt (.copy ⟨2, []⟩) floatI8Ty) emptyMemory
        floatLocalDecls castStage1Layouts = unsupported ∧
     evalRvalue floatLocals (.cast .floatToFloat (.copy ⟨2, []⟩) floatF32Ty) emptyMemory
        floatLocalDecls castStage1Layouts = unsupported) ∧
    (evalRvalue floatLocals (.cast .intToFloat (.copy ⟨2, []⟩) floatF128Ty) emptyMemory
        floatLocalDecls castStage1Layouts = unsupported ∧
     evalRvalue floatLocals (.cast .floatToFloat (.copy ⟨0, []⟩) floatF128Ty) emptyMemory
        floatLocalDecls castStage1Layouts = unsupported) :=
  ⟨(evalRvalue_cast_float_unsupported_of_no_format (locals := floatLocals) (op := .copy ⟨2, []⟩)
      (dstTy := floatI8Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
      (layouts := castStage1Layouts) rfl rfl).1 rfl |>.imp id (fun _ =>
      ((evalRvalue_cast_float_unsupported_of_no_format (locals := floatLocals) (op := .copy ⟨2, []⟩)
        (dstTy := floatF32Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
        (layouts := castStage1Layouts) rfl rfl).1 rfl).2),
   ⟨((evalRvalue_cast_float_unsupported_of_no_format (locals := floatLocals) (op := .copy ⟨2, []⟩)
      (dstTy := floatF128Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
      (layouts := castStage1Layouts) rfl rfl).2 rfl).1,
    ((evalRvalue_cast_float_unsupported_of_no_format (locals := floatLocals) (op := .copy ⟨0, []⟩)
      (dstTy := floatF128Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
      (layouts := castStage1Layouts) rfl rfl).2 rfl).2⟩⟩

/-- Concrete `evalRvalue` float casts on `castStage1Layouts`: `π as i8 = 3`, `π as f32`
(round to nearest), `-0.0f32 as u8 = 0`, `-0.0f32 as f64 = -0.0`, `-123i64 as f64`,
`(2^53 + 3) as f64 = 2^53 + 4` (tie to even), `-1e39f64 as i8 = i8::MIN` and `as f32 = -∞`
(saturation / overflow), and `-1isize as f32 = -1.0` (64-bit `isize`). -/
theorem step_float_casts_concrete :
    evalRvalue floatLocals (.cast .floatToInt (.copy ⟨0, []⟩) floatI8Ty) emptyMemory
        floatLocalDecls castStage1Layouts = ok (.scalar ⟨3, 1⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .floatToFloat (.copy ⟨0, []⟩) floatF32Ty) emptyMemory
        floatLocalDecls castStage1Layouts = ok (.scalar ⟨0x40490FDB, 4⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .floatToInt (.copy ⟨1, []⟩) floatU8Ty) emptyMemory
        floatLocalDecls castStage1Layouts = ok (.scalar ⟨0, 1⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .floatToFloat (.copy ⟨1, []⟩) floatF64Ty) emptyMemory
        floatLocalDecls castStage1Layouts =
      ok (.scalar ⟨0x8000000000000000, 8⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .intToFloat (.copy ⟨2, []⟩) floatF64Ty) emptyMemory
        floatLocalDecls castStage1Layouts =
      ok (.scalar ⟨0xC05EC00000000000, 8⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .intToFloat (.copy ⟨3, []⟩) floatF64Ty) emptyMemory
        floatLocalDecls castStage1Layouts =
      ok (.scalar ⟨0x4340000000000002, 8⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .floatToInt (.copy ⟨4, []⟩) floatI8Ty) emptyMemory
        floatLocalDecls castStage1Layouts = ok (.scalar ⟨0x80, 1⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .floatToFloat (.copy ⟨4, []⟩) floatF32Ty) emptyMemory
        floatLocalDecls castStage1Layouts = ok (.scalar ⟨0xFF800000, 4⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .intToFloat (.copy ⟨5, []⟩) floatF32Ty) emptyMemory
        floatLocalDecls castStage1Layouts = ok (.scalar ⟨0xBF800000, 4⟩) floatLocals emptyMemory ∧
    evalRvalue floatLocals (.cast .floatToFloat (.copy ⟨0, []⟩) floatF128Ty) emptyMemory
        floatLocalDecls castStage1Layouts = unsupported :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `evalFloatCast` at `castStage1Layouts` on a single scalar operand of byte width `sz`. -/
def fcast (ck : CastKind) (src dst : RigidTy) (bits sz : Nat) : Option Value :=
  evalFloatCast ck (some { kind := src, layoutIdx := 0 }) { kind := dst, layoutIdx := 0 }
    castStage1Layouts (.scalar ⟨bits, sz⟩)

/-- IEEE-754 `roundTiesToEven` subnormal and overflow boundaries for `f64 as f32`
(cross-checked against host binary32 rounding): exact ties at `1.5·2⁻¹⁴⁹` / `2.5·2⁻¹⁴⁹` round to
the even subnormal `2·2⁻¹⁴⁹` (sign-symmetric), `0.75·2⁻¹⁴⁹` rounds up to the least subnormal, the
largest subnormal rounds up into the least normal, `f32::MAX + ½ulp` (a tie with an odd
significand) overflows to `+∞`, and the value just below that tie stays at `f32::MAX`. -/
theorem fcast_f64_to_f32_ties_subnormal_and_overflow :
    fcast .floatToFloat (.float .f64) (.float .f32) 0x36A8000000000000 8 = some (.scalar ⟨0x2, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0x36B4000000000000 8 = some (.scalar ⟨0x2, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0xB6A8000000000000 8 =
      some (.scalar ⟨0x80000002, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0x3698000000000000 8 = some (.scalar ⟨0x1, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0x380FFFFFE0000000 8 =
      some (.scalar ⟨0x800000, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0x47EFFFFFF0000000 8 =
      some (.scalar ⟨0x7F800000, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0x47EFFFFFEFFFFFFF 8 =
      some (.scalar ⟨0x7F7FFFFF, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0x3FF0000010000000 8 =
      some (.scalar ⟨0x3F800000, 4⟩) ∧
    fcast .floatToFloat (.float .f64) (.float .f32) 0x3FF0000010000004 8 =
      some (.scalar ⟨0x3F800001, 4⟩) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- NaN quieting (one admissible deterministic choice under Rust's non-deterministic NaN
semantics, matching IEEE-754 / x86 `cvtsd2ss` / `cvtss2sd`): signaling NaNs are quieted, the
`f32 → f64` payload is preserved (shifted into the high significand bits) together with the sign,
and the `f64 → f32` payload is truncated to its top bits. Exact widening keeps the least `f32`
subnormal exact. -/
theorem fcast_nan_quieting_and_exact_widening :
    fcast .floatToFloat (.float .f64) (.float .f32) 0x7FF0000000000001 8 =
      some (.scalar ⟨0x7FC00000, 4⟩) ∧
    fcast .floatToFloat (.float .f32) (.float .f64) 0x7F800001 4 =
      some (.scalar ⟨0x7FF8000020000000, 8⟩) ∧
    fcast .floatToFloat (.float .f32) (.float .f64) 0xFFC00000 4 =
      some (.scalar ⟨0xFFF8000000000000, 8⟩) ∧
    fcast .floatToFloat (.float .f32) (.float .f64) 0x00000001 4 =
      some (.scalar ⟨0x36A0000000000000, 8⟩) := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- Saturating `as` casts at the integer extremes: `NaN → 0`, `2³¹f32 as i32 = i32::MAX`,
`2147483520f32 as i32` exact, `-2⁶³f64 as i64 = i64::MIN`, `+∞ as u8 = 255`,
`1e39f64 as u128 = u128::MAX`, and `-0.5 as isize = 0` (truncation toward zero). -/
theorem fcast_float_to_int_saturation_extremes :
    fcast .floatToInt (.float .f32) (.int .i32) 0x7FC00000 4 = some (.scalar ⟨0, 4⟩) ∧
    fcast .floatToInt (.float .f32) (.int .i32) 0x4F000000 4 = some (.scalar ⟨0x7FFFFFFF, 4⟩) ∧
    fcast .floatToInt (.float .f32) (.int .i32) 0x4EFFFFFF 4 = some (.scalar ⟨0x7FFFFF80, 4⟩) ∧
    fcast .floatToInt (.float .f64) (.int .i64) 0xC3E0000000000000 8 =
      some (.scalar ⟨0x8000000000000000, 8⟩) ∧
    fcast .floatToInt (.float .f64) (.uint .u8) 0x7FF0000000000000 8 = some (.scalar ⟨0xFF, 1⟩) ∧
    fcast .floatToInt (.float .f64) (.uint .u128) 0x48078287F49C4A1D 8 =
      some (.scalar ⟨2 ^ 128 - 1, 16⟩) ∧
    fcast .floatToInt (.float .f64) (.int .isize) 0xBFE0000000000000 8 = some (.scalar ⟨0, 8⟩) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `roundTiesToEven` integer-to-float at the format limits: `u128::MAX as f32 = +∞` (it exceeds
`f32::MAX + ½ulp`), `u128::MAX as f64 = 2¹²⁸`, `i128::MIN as f32 = -2¹²⁷` exactly,
`u64::MAX as f32 = 2⁶⁴`, `i64::MAX as f32 = 2⁶³`, and the `2²⁴ + 1` / `2²⁴ + 3` (`f32`) and
`2⁵³ + 1` (`f64`) ties rounding to the even neighbour. -/
theorem fcast_int_to_float_limits_and_ties :
    fcast .intToFloat (.uint .u128) (.float .f32) (2 ^ 128 - 1) 16 = some (.scalar ⟨0x7F800000, 4⟩) ∧
    fcast .intToFloat (.uint .u128) (.float .f64) (2 ^ 128 - 1) 16 =
      some (.scalar ⟨0x47F0000000000000, 8⟩) ∧
    fcast .intToFloat (.int .i128) (.float .f32) (2 ^ 127) 16 = some (.scalar ⟨0xFF000000, 4⟩) ∧
    fcast .intToFloat (.uint .u64) (.float .f32) 0xFFFFFFFFFFFFFFFF 8 =
      some (.scalar ⟨0x5F800000, 4⟩) ∧
    fcast .intToFloat (.int .i64) (.float .f32) 0x7FFFFFFFFFFFFFFF 8 =
      some (.scalar ⟨0x5F000000, 4⟩) ∧
    fcast .intToFloat (.int .i32) (.float .f32) 16777217 4 = some (.scalar ⟨0x4B800000, 4⟩) ∧
    fcast .intToFloat (.int .i32) (.float .f32) 16777219 4 = some (.scalar ⟨0x4B800002, 4⟩) ∧
    fcast .intToFloat (.uint .u64) (.float .f64) (2 ^ 53 + 1) 8 =
      some (.scalar ⟨0x4340000000000000, 8⟩) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! ## Section 10.1: End-to-end multi-statement `stepMirFn` float-cast runs

Each body below runs **from program entry** (`initMachineState body []`: `_0` uninitialized,
every other local dead) through `StorageLive`, float casts (`.constant` / `.copy` / `.move`),
`StorageDead`, and its root `return` under Anneal's trusted small-step function `stepMirFn`
(64-bit `castStage1Layouts`), kernel-evaluated by `rfl`. -/

section FloatStepRuns

open Trusted.Rustc.V2026_06_01.MirSemantics (MirStepNode MachineState stepMirFn initMachineState)

/-- Run `stepMirFn` for at most `fuel` silent steps, stopping at the first non-step node. -/
def runFloatSteps (body : CapturedMir) : Nat → MachineState → MirStepNode
  | 0, s => MirStepNode.step s
  | n + 1, s =>
    match stepMirFn body s with
    | .tau (.running s') => runFloatSteps body n s'
    | r => r

/-- Frame locals of a silent-step node. -/
def stepLocals? : MirStepNode → Option (List LocalSlot)
  | .tau (.running s) => some s.frame.locals
  | _ => none

/-- Scalar returned by a normal root-return node. -/
def retScalar? : MirStepNode → Option ScalarInt
  | .ret (.normal (.scalar sc, _)) => some sc
  | _ => none

/-- `as`-cast test statement. -/
def fStmt (k : StatementKind) : Statement := { kind := k, span := "cast-stage1-float" }
/-- Unprojected local place. -/
def fPlace (i : Nat) : Place := { local_ := i, projection := [] }
/-- Type of kind `k`. -/
def fTy (k : RigidTy) : Ty := { kind := k, layoutIdx := 0 }
/-- Scalar constant `⟨bits, sz⟩ : k`. -/
def fConst (k : RigidTy) (bits sz : Nat) : Operand :=
  .constant { ty := fTy k, val := .scalar (.int ⟨bits, sz⟩) }
/-- `_dst = op as k` with cast kind `ck`. -/
def fCast (dst : Nat) (ck : CastKind) (op : Operand) (k : RigidTy) : StatementKind :=
  .assign (fPlace dst) (.cast ck op (fTy k))

/-- Single-block `Runtime(PostCleanup)` body `bb0: stmts; return` over `castStage1Layouts`. -/
def floatBody (name : String) (decls : List RigidTy) (stmts : List StatementKind) :
    CapturedMir where
  defPath := name
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := decls.map fun k => { mutability := .mut, ty := fTy k, debugName := none }
  basicBlocks := [
    { statements := stmts.map fStmt
      terminator := { kind := .return_, span := "cast-stage1-float" }
      isCleanup := false }]
  fnAbi :=
    { args := []
      ret := { layout := unitPlaceholderLayout, mode := .direct }
      conv := .rust
      canUnwind := false }
  layouts := castStage1Layouts
  allocations := []

/-- (W1/W3/W4) `StorageLive(_1.._5)`; `_1 = const 1.5·2⁻¹⁴⁹_f64 as f32` (tie ↦ `0x2`);
`_2 = copy _1 as f64` (exact `2⁻¹⁴⁸`); `_3 = const +∞_f32 as i8`; `_4 = const +∞_f32 as u128`;
`_5 = move _4 as f32` (`u128::MAX ↦ +∞`); `_0 = move _2 as f32` (exact round trip);
`StorageDead(_5.._1)`; `return`. -/
def floatPipelineBody : CapturedMir :=
  floatBody "cast_stage1::float_pipeline"
    [.float .f32, .float .f32, .float .f64, .int .i8, .uint .u128, .float .f32]
    [.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     fCast 1 .floatToFloat (fConst (.float .f64) 0x36A8000000000000 8) (.float .f32),
     fCast 2 .floatToFloat (.copy (fPlace 1)) (.float .f64),
     fCast 3 .floatToInt (fConst (.float .f32) 0x7F800000 4) (.int .i8),
     fCast 4 .floatToInt (fConst (.float .f32) 0x7F800000 4) (.uint .u128),
     fCast 5 .intToFloat (.move (fPlace 4)) (.float .f32),
     fCast 0 .floatToFloat (.move (fPlace 2)) (.float .f32),
     .storageDead 5, .storageDead 4, .storageDead 3, .storageDead 2, .storageDead 1]

set_option maxRecDepth 200000 in
/-- End-to-end `stepMirFn` run of `floatPipelineBody` from program entry: after the prologue
and the six casts every local holds the IEEE-754 result (moved-from `_2`, `_4` are
`.uninit`), after the epilogue only `_0` is live, and the function returns `0x0000_0002_f32`. -/
theorem stepMirFn_float_pipeline_run :
    let s₀ := initMachineState floatPipelineBody []
    s₀.frame.locals = [.uninit, .dead, .dead, .dead, .dead, .dead] ∧
    stepLocals? (runFloatSteps floatPipelineBody 11 s₀) =
      some [.init (.scalar ⟨0x2, 4⟩), .init (.scalar ⟨0x2, 4⟩), .uninit,
        .init (.scalar ⟨0x7F, 1⟩), .uninit, .init (.scalar ⟨0x7F800000, 4⟩)] ∧
    stepLocals? (runFloatSteps floatPipelineBody 16 s₀) =
      some [.init (.scalar ⟨0x2, 4⟩), .dead, .dead, .dead, .dead, .dead] ∧
    retScalar? (runFloatSteps floatPipelineBody 17 s₀) = some ⟨0x2, 4⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- (W3) `StorageLive(_1.._13)`, then the twelve saturating float-to-int casts of
`LeanMiriSpec.WitFloatCastLM.wfcW3Body` into `_0 : i8 .. _11 : usize` (sources `_12 : f32`,
`_13 : f64`), then `return`. -/
def floatToIntAllTargetsBody : CapturedMir :=
  floatBody "cast_stage1::float_to_int_all_targets"
    [.int .i8, .int .i16, .int .i32, .int .i64, .int .i128, .int .isize, .uint .u8, .uint .u16,
     .uint .u32, .uint .u64, .uint .u128, .uint .usize, .float .f32, .float .f64]
    ((List.range 13).map (fun i => .storageLive (i + 1)) ++
    [fCast 13 .floatToFloat (fConst (.float .f32) 0xBFC00000 4) (.float .f64),
     fCast 12 .floatToFloat (fConst (.float .f64) 0x44B52D02C7E14AF6 8) (.float .f32),
     fCast 0 .floatToInt (fConst (.float .f32) 0x7F800000 4) (.int .i8),
     fCast 1 .floatToInt (fConst (.float .f64) 0xFFF0000000000000 8) (.int .i16),
     fCast 2 .floatToInt (fConst (.float .f64) 0x41E65A0BC0000000 8) (.int .i32),
     fCast 3 .floatToInt (fConst (.float .f64) 0xC007333333333333 8) (.int .i64),
     fCast 4 .floatToInt (fConst (.float .f64) 0x7FF8000000000000 8) (.int .i128),
     fCast 5 .floatToInt (fConst (.float .f32) 0x80000000 4) (.int .isize),
     fCast 6 .floatToInt (.copy (fPlace 13)) (.uint .u8),
     fCast 7 .floatToInt (fConst (.float .f32) 0x477FFF80 4) (.uint .u16),
     fCast 8 .floatToInt (fConst (.float .f64) 0x41F0000000000000 8) (.uint .u32),
     fCast 9 .floatToInt (fConst (.float .f32) 0x5F800000 4) (.uint .u64),
     fCast 10 .floatToInt (fConst (.float .f32) 0x7F7FFFFF 4) (.uint .u128),
     fCast 11 .floatToInt (.move (fPlace 12)) (.uint .usize)])

set_option maxRecDepth 200000 in
/-- End-to-end `stepMirFn` run hitting all twelve integer targets: `+∞ as i8 = 127`,
`-∞ as i16 = i16::MIN`, `3e9 as i32 = i32::MAX`, `-2.9 as i64 = -2`, `NaN as i128 = 0`,
`-0.0 as isize = 0`, `-1.5 as u8 = 0`, `65535.5 as u16 = u16::MAX`, `2³² as u32 = u32::MAX`,
`2⁶⁴ as u64 = u64::MAX`, `f32::MAX as u128` exact, `1e23 as usize = usize::MAX`. -/
theorem stepMirFn_float_to_int_all_targets_run :
    let s₀ := initMachineState floatToIntAllTargetsBody []
    stepLocals? (runFloatSteps floatToIntAllTargetsBody 27 s₀) =
      some [.init (.scalar ⟨0x7F, 1⟩), .init (.scalar ⟨0x8000, 2⟩),
        .init (.scalar ⟨0x7FFFFFFF, 4⟩), .init (.scalar ⟨0xFFFFFFFFFFFFFFFE, 8⟩),
        .init (.scalar ⟨0, 16⟩), .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨0, 1⟩),
        .init (.scalar ⟨0xFFFF, 2⟩), .init (.scalar ⟨0xFFFFFFFF, 4⟩),
        .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩),
        .init (.scalar ⟨0xFFFFFF00000000000000000000000000, 16⟩),
        .init (.scalar ⟨0xFFFFFFFFFFFFFFFF, 8⟩), .uninit,
        .init (.scalar ⟨0xBFF8000000000000, 8⟩)] ∧
    retScalar? (runFloatSteps floatToIntAllTargetsBody 28 s₀) = some ⟨0x7F, 1⟩ :=
  ⟨rfl, rfl⟩

/-- (W4) `StorageLive(_1.._8)`, then the integer-to-float casts of
`LeanMiriSpec.WitFloatCastLM.wfcW4Body`, then `return`. -/
def intToFloatTiesBody : CapturedMir :=
  floatBody "cast_stage1::int_to_float_ties"
    [.float .f32, .float .f32, .float .f64, .float .f32, .float .f32, .float .f32, .float .f64,
     .float .f64, .uint .u128]
    ((List.range 8).map (fun i => .storageLive (i + 1)) ++
    [fCast 8 .floatToInt (fConst (.float .f32) 0x7F800000 4) (.uint .u128),
     fCast 1 .intToFloat (.copy (fPlace 8)) (.float .f32),
     fCast 2 .intToFloat (.move (fPlace 8)) (.float .f64),
     fCast 3 .intToFloat (fConst (.int .i128) (2 ^ 127) 16) (.float .f32),
     fCast 4 .intToFloat (fConst (.int .i32) (2 ^ 24 + 1) 4) (.float .f32),
     fCast 5 .intToFloat (fConst (.int .i32) (2 ^ 24 + 3) 4) (.float .f32),
     fCast 6 .intToFloat (fConst (.uint .u64) (2 ^ 53 + 1) 8) (.float .f64),
     fCast 7 .intToFloat (fConst (.uint .u64) (2 ^ 53 + 3) 8) (.float .f64),
     fCast 0 .intToFloat (fConst (.int .i8) 0x80 1) (.float .f32)])

set_option maxRecDepth 200000 in
/-- End-to-end `stepMirFn` run of the integer-to-float limits: `u128::MAX as f32 = +∞`,
`u128::MAX as f64 = 2¹²⁸`, `i128::MIN as f32 = -2¹²⁷`, ties `2²⁴ + 1 ↦ 2²⁴`,
`2²⁴ + 3 ↦ 2²⁴ + 4`, `2⁵³ + 1 ↦ 2⁵³`, `2⁵³ + 3 ↦ 2⁵³ + 4`, and `i8::MIN as f32 = -128.0`. -/
theorem stepMirFn_int_to_float_ties_run :
    let s₀ := initMachineState intToFloatTiesBody []
    stepLocals? (runFloatSteps intToFloatTiesBody 17 s₀) =
      some [.init (.scalar ⟨0xC3000000, 4⟩), .init (.scalar ⟨0x7F800000, 4⟩),
        .init (.scalar ⟨0x47F0000000000000, 8⟩), .init (.scalar ⟨0xFF000000, 4⟩),
        .init (.scalar ⟨0x4B800000, 4⟩), .init (.scalar ⟨0x4B800002, 4⟩),
        .init (.scalar ⟨0x4340000000000000, 8⟩), .init (.scalar ⟨0x4340000000000002, 8⟩),
        .uninit] ∧
    retScalar? (runFloatSteps intToFloatTiesBody 18 s₀) = some ⟨0xC3000000, 4⟩ :=
  ⟨rfl, rfl⟩

/-- (W2) `StorageLive(_1.._4)`; `_1 = const 0x7F80_0001_f32 as f64`;
`_2 = const 0x7FF0_0000_0000_0001_f64 as f32`; `_3 = const 0x7FF0_0000_2000_0001_f64 as f32`;
`_4 = copy _1 as f32`; `_0 = move _4 as f64`; `return`. -/
def floatNaNBody : CapturedMir :=
  floatBody "cast_stage1::float_nan"
    [.float .f64, .float .f64, .float .f32, .float .f32, .float .f32]
    [.storageLive 1, .storageLive 2, .storageLive 3, .storageLive 4,
     fCast 1 .floatToFloat (fConst (.float .f32) 0x7F800001 4) (.float .f64),
     fCast 2 .floatToFloat (fConst (.float .f64) 0x7FF0000000000001 8) (.float .f32),
     fCast 3 .floatToFloat (fConst (.float .f64) 0x7FF0000020000001 8) (.float .f32),
     fCast 4 .floatToFloat (.copy (fPlace 1)) (.float .f32),
     fCast 0 .floatToFloat (.move (fPlace 4)) (.float .f64)]

set_option maxRecDepth 200000 in
/-- End-to-end `stepMirFn` NaN run: signaling NaNs are quieted with their payload kept
(`0x7F80_0001 ↦ 0x7FF8_0000_2000_0000`, `0x7FF0_0000_2000_0001 ↦ 0x7FC0_0001`) or truncated
(`0x7FF0_0000_0000_0001 ↦ 0x7FC0_0000`), and the payload NaN round-trips `f64 → f32 → f64`. -/
theorem stepMirFn_float_nan_run :
    let s₀ := initMachineState floatNaNBody []
    stepLocals? (runFloatSteps floatNaNBody 9 s₀) =
      some [.init (.scalar ⟨0x7FF8000020000000, 8⟩), .init (.scalar ⟨0x7FF8000020000000, 8⟩),
        .init (.scalar ⟨0x7FC00000, 4⟩), .init (.scalar ⟨0x7FC00001, 4⟩), .uninit] ∧
    retScalar? (runFloatSteps floatNaNBody 10 s₀) = some ⟨0x7FF8000020000000, 8⟩ :=
  ⟨rfl, rfl⟩

/-- (W5) Dead (`StorageDead`), never-live, uninitialized, and moved-from float-cast sources are
UB, and `f16` sources / `bool` sources fail closed, all from program entry. -/
def floatDeadBody : CapturedMir :=
  floatBody "cast_stage1::float_dead" [.float .f32, .float .f64]
    [.storageLive 1, fCast 1 .intToFloat (fConst (.int .i32) 3 4) (.float .f64), .storageDead 1,
     fCast 0 .floatToFloat (.copy (fPlace 1)) (.float .f32)]

def floatNeverLiveBody : CapturedMir :=
  floatBody "cast_stage1::float_never_live" [.float .f32, .float .f64]
    [fCast 0 .floatToFloat (.move (fPlace 1)) (.float .f32)]

def floatUninitBody : CapturedMir :=
  floatBody "cast_stage1::float_uninit" [.uint .u32, .float .f64]
    [.storageLive 1, fCast 0 .floatToInt (.copy (fPlace 1)) (.uint .u32)]

def floatMovedBody : CapturedMir :=
  floatBody "cast_stage1::float_moved" [.int .i32, .float .f64, .float .f32]
    [.storageLive 1, .storageLive 2,
     fCast 2 .floatToFloat (fConst (.float .f64) 0x4004000000000000 8) (.float .f32),
     fCast 1 .floatToFloat (.move (fPlace 2)) (.float .f64),
     fCast 0 .floatToInt (.move (fPlace 2)) (.int .i32)]

def floatF16Body : CapturedMir :=
  floatBody "cast_stage1::float_f16" [.float .f32]
    [fCast 0 .floatToFloat (fConst (.float .f16) 0x3C00 2) (.float .f32)]

def floatF128SrcBody : CapturedMir :=
  floatBody "cast_stage1::float_f128_src" [.float .f64]
    [fCast 0 .floatToFloat (fConst (.float .f128) (0x3FFF * 2 ^ 112) 16) (.float .f64)]

def floatF16DstBody : CapturedMir :=
  floatBody "cast_stage1::float_f16_dst" [.float .f16]
    [fCast 0 .floatToFloat (fConst (.float .f32) 0x3F800000 4) (.float .f16)]

def floatF128DstBody : CapturedMir :=
  floatBody "cast_stage1::float_f128_dst" [.float .f128]
    [fCast 0 .floatToFloat (fConst (.float .f64) 0x3FF0000000000000 8) (.float .f128)]

def floatBoolBody : CapturedMir :=
  floatBody "cast_stage1::float_bool" [.float .f32]
    [fCast 0 .intToFloat (fConst .bool 1 1) (.float .f32)]

def floatCharBody : CapturedMir :=
  floatBody "cast_stage1::float_char" [.float .f64]
    [fCast 0 .intToFloat (fConst .char 0x41 4) (.float .f64)]

set_option maxRecDepth 200000 in
/-- End-to-end `stepMirFn` negative controls: reading a dead (`StorageDead`), never-live,
uninitialized, or moved-from source in a float cast faults with `.ub`; `f16`/`f128` sources and
targets and `bool`/`char` sources fail closed with `.unsupported`. -/
theorem stepMirFn_float_ub_and_fail_closed_runs :
    runFloatSteps floatDeadBody 4 (initMachineState floatDeadBody []) = MirStepNode.fail .ub ∧
    runFloatSteps floatNeverLiveBody 1 (initMachineState floatNeverLiveBody []) =
      MirStepNode.fail .ub ∧
    runFloatSteps floatUninitBody 2 (initMachineState floatUninitBody []) =
      MirStepNode.fail .ub ∧
    runFloatSteps floatMovedBody 5 (initMachineState floatMovedBody []) =
      MirStepNode.fail .ub ∧
    runFloatSteps floatF16Body 1 (initMachineState floatF16Body []) = MirStepNode.unsupported ∧
    runFloatSteps floatF128SrcBody 1 (initMachineState floatF128SrcBody []) =
      MirStepNode.unsupported ∧
    runFloatSteps floatF16DstBody 1 (initMachineState floatF16DstBody []) =
      MirStepNode.unsupported ∧
    runFloatSteps floatF128DstBody 1 (initMachineState floatF128DstBody []) =
      MirStepNode.unsupported ∧
    runFloatSteps floatBoolBody 1 (initMachineState floatBoolBody []) = MirStepNode.unsupported ∧
    runFloatSteps floatCharBody 1 (initMachineState floatCharBody []) = MirStepNode.unsupported :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- (W5) Address-taken (`&raw mut _1`) local + float-to-int write (invalidating the raw-pointer
borrow entry) + int-to-float reads (`copy` & `move` round-trip) + `StorageDead` + `return`. -/
def promotedRawFloatBody : CapturedMir :=
  floatBody "cast_stage1::promoted_raw_float"
    [.float .f64, .int .i64, .rawPtr .mut (.int .i64), .float .f32]
    [.storageLive 1, .storageLive 2, .storageLive 3,
     .assign (fPlace 2) (.rawPtr .mut (fPlace 1)),
     fCast 1 .floatToInt (fConst (.float .f64) 0xC045600000000000 8) (.int .i64),
     fCast 3 .intToFloat (.copy (fPlace 1)) (.float .f32),
     fCast 1 .floatToInt (.move (fPlace 3)) (.int .i64),
     fCast 0 .intToFloat (.copy (fPlace 1)) (.float .f64),
     .storageDead 3, .storageDead 2, .storageDead 1]

/-- Borrow permissions of a silent-step node's memory. -/
def stepBorrowPerms? : MirStepNode → Option (List (Nat × TreeBorrowPerm))
  | .tau (.running s) => some (s.memory.borrows.map fun b => (b.tag, b.perm))
  | _ => none

set_option maxRecDepth 200000 in
/-- End-to-end `stepMirFn` run of `promotedRawFloatBody` from program entry: `_2 = &raw mut _1`
creates an `.active` borrow tag on `_1`; writing `-42.75_f64 as i64 = -42` into `_1` transitions
that borrow tag to `.disabled`; subsequent `intToFloat` / `floatToInt` casts read and overwrite
`_1`, `StorageDead` cleans up `_3.._1`, and the function returns `-42.0_f64`. -/
theorem stepMirFn_promoted_raw_float_cast_run :
    let s₀ := initMachineState promotedRawFloatBody []
    stepBorrowPerms? (runFloatSteps promotedRawFloatBody 4 s₀) = some [(1, .active)] ∧
    stepBorrowPerms? (runFloatSteps promotedRawFloatBody 5 s₀) = some [(1, .disabled)] ∧
    stepLocals? (runFloatSteps promotedRawFloatBody 8 s₀) =
      some [.init (.scalar ⟨0xC045000000000000, 8⟩), .init (.scalar ⟨0xFFFFFFFFFFFFFFD6, 8⟩),
        .init (.ptr { allocId := 1, offsetBytes := 0 } 8), .uninit] ∧
    retScalar? (runFloatSteps promotedRawFloatBody 12 s₀) = some ⟨0xC045000000000000, 8⟩ :=
  ⟨rfl, rfl, rfl, rfl⟩

end FloatStepRuns

/-! ## Axiom guards

Every theorem of this file depends on at most `propext` and `Quot.sound`: **no**
`Classical.choice`, `sorryAx`, or `Lean.ofReduceBool` (`#guard_msgs` fails the check otherwise). -/

section AxiomGuards

/--
info: 'Anneal.CastStage1Tests.ptrBytesNoForge_ref_intact_and_provFree' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms ptrBytesNoForge_ref_intact_and_provFree

/--
info: 'Anneal.CastStage1Tests.scalarLayoutNoForge_nonNullPtr_range_enforced' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms scalarLayoutNoForge_nonNullPtr_range_enforced

/--
info: 'Anneal.CastStage1Tests.fnPtr_intact_vs_provFree_and_overwrite' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms fnPtr_intact_vs_provFree_and_overwrite

/--
info: 'Anneal.CastStage1Tests.step_u64_to_fnPtr_ub_vs_rawPtr_strips_and_ptr_to_fnPtr_preserves' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_u64_to_fnPtr_ub_vs_rawPtr_strips_and_ptr_to_fnPtr_preserves

/--
info: 'Anneal.CastStage1Tests.step_scalarNicheNewtype_nonZeroU32_accepts_five_and_rejects_zero' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_scalarNicheNewtype_nonZeroU32_accepts_five_and_rejects_zero

/--
info: 'Anneal.CastStage1Tests.scalarNicheNewtype_charRange_surrogate_divergence' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms scalarNicheNewtype_charRange_surrogate_divergence

/--
info: 'Anneal.CastStage1Tests.evalRvalue_cast_floatToInt_sound_inst' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalRvalue_cast_floatToInt_sound_inst

/--
info: 'Anneal.CastStage1Tests.evalRvalue_cast_floatToFloat_sound_inst' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalRvalue_cast_floatToFloat_sound_inst

/--
info: 'Anneal.CastStage1Tests.evalRvalue_cast_intToFloat_exact_inst' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalRvalue_cast_intToFloat_exact_inst

/--
info: 'Anneal.CastStage1Tests.evalRvalue_cast_float_unsupported_of_no_format_inst' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms evalRvalue_cast_float_unsupported_of_no_format_inst

/--
info: 'Anneal.CastStage1Tests.step_float_casts_concrete' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms step_float_casts_concrete

/--
info: 'Anneal.CastStage1Tests.fcast_f64_to_f32_ties_subnormal_and_overflow' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms fcast_f64_to_f32_ties_subnormal_and_overflow

/--
info: 'Anneal.CastStage1Tests.fcast_nan_quieting_and_exact_widening' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms fcast_nan_quieting_and_exact_widening

/--
info: 'Anneal.CastStage1Tests.fcast_float_to_int_saturation_extremes' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms fcast_float_to_int_saturation_extremes

/--
info: 'Anneal.CastStage1Tests.fcast_int_to_float_limits_and_ties' depends on axioms:
  [propext]
-/
#guard_msgs (whitespace := lax) in
#print axioms fcast_int_to_float_limits_and_ties

/--
info: 'Anneal.CastStage1Tests.stepMirFn_float_pipeline_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_float_pipeline_run

/--
info: 'Anneal.CastStage1Tests.stepMirFn_float_to_int_all_targets_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_float_to_int_all_targets_run

/--
info: 'Anneal.CastStage1Tests.stepMirFn_int_to_float_ties_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_int_to_float_ties_run

/--
info: 'Anneal.CastStage1Tests.stepMirFn_float_nan_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_float_nan_run

/--
info: 'Anneal.CastStage1Tests.stepMirFn_float_ub_and_fail_closed_runs' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_float_ub_and_fail_closed_runs

/--
info: 'Anneal.CastStage1Tests.stepMirFn_promoted_raw_float_cast_run' depends on axioms:
  [propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms stepMirFn_promoted_raw_float_cast_run

end AxiomGuards

end Anneal.CastStage1Tests
