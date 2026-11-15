import Anneal.Mir.Cast

namespace Anneal.CastStage1Tests

open Trusted.MirAst
open Trusted.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics.RvalueEvalResult
open Trusted.Rustc.V2026_06_01.MirSemantics (decodeTypedValueFromBytes decodePtrBytesNoForge
  decodeScalarLayoutBytesNoForge abstractBytesUniformProv layoutPointerBytes)
open Anneal.BitValidity
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
   trusted_vs_anneal_overwrite_provenance_no_forge_agreement_fnPtr 15 castStage1Layouts [.uint .u32]
      (.uint .u32) .safe .rust 0 16 (some 7) 3 { data := 0xAA, prov := none } rfl (by decide)
      (Or.inl rfl)⟩

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
example :=
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
concrete `evalRvalue` environment (64-bit `castStage1Layouts`). -/
example :=
  evalRvalue_cast_floatToInt_sound (locals := floatLocals) (op := .copy ⟨0, []⟩) (dstTy := floatI8Ty)
    (mem := emptyMemory) (localDecls := floatLocalDecls) (layouts := castStage1Layouts)
    (fmt := .binary64) (tgt := .signed .i8) rfl rfl rfl rfl rfl

example :=
  evalRvalue_cast_floatToFloat_sound (locals := floatLocals) (op := .copy ⟨0, []⟩)
    (dstTy := floatF32Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
    (layouts := castStage1Layouts) (src := .binary64) (dst := .binary32) rfl rfl rfl rfl rfl

example :=
  evalRvalue_cast_intToFloat_exact (locals := floatLocals) (op := .copy ⟨2, []⟩)
    (dstTy := floatF64Ty) (mem := emptyMemory) (localDecls := floatLocalDecls)
    (layouts := castStage1Layouts) (fmt := .binary64) (src := .signed .i64) rfl rfl rfl rfl rfl
    (by decide +kernel)

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

end Anneal.CastStage1Tests
