import Lean
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators
import Trusted.Rustc.V2026_08_01.MirSemantics.Terminators
import Trusted.MirSemantics

/-!
# Comprehensive Kernel-Checked Tests for `UCG#558` / `rust#148259` Pointer-Byte Fragment Coherence, Companion Pointer Soundness (`W3`–`W5`), `Kani#5205` / `#5196` Read-Time Untyped-Byte Validity, and `V2026_06_01 == V2026_08_01` Lockstep Parity

Covers every positive control, negative adversarial manipulation, companion soundness fix,
read-time untyped-byte validity control, and lockstep dialect parity requirement across BOTH
`Trusted.Rustc.V2026_06_01.MirSemantics` and `Trusted.Rustc.V2026_08_01.MirSemantics`, followed
by a mechanical `Lean.Meta` axiom, reachability, and non-triviality audit.
-/

namespace Anneal.PtrByteCoherenceTests

namespace V06
export Trusted.Rustc.V2026_06_01.Layout (LayoutTable TypeLayout Size Align BackendRepr
  ScalarLayout PrimitiveKind WrappingRange FieldsShape VariantsShape)
export Trusted.Rustc.V2026_06_01.MirAst (Ty RigidTy Mutability UintTy IntTy ScalarInt
  ProvenancePtr ConstScalar ConstValue ConstOperand ProjectionElem Place Operand Rvalue
  Statement StatementKind NonDivergingIntrinsic LocalDecl CapturedAllocation CapturedMir
  Terminator TerminatorKind)
export Trusted.Rustc.V2026_06_01.MirSemantics (PtrByteFrag AbstractByte Value LocalSlot
  BorrowEntry TreeBorrowPerm Memory StackFrame MachineState SavedCallerFrame MirStepNode
  RvalueEvalResult PlaceReadResult Ptr2IntTransmutePolicy UnionPlaceInfo
  ResolvedCallTarget WriteBytesAction
  emptyMemory defaultCodecFuel
  normPtrByteOffset mkInitByte mkPtrFragByte
  abstractBytesCoherentPtrProv? abstractBytesUniformProv abstractBytesHaveProv
  mergeByteProvenance
  encodeLittleEndianBytes encodeScalarBytes decodeLittleEndianBytes decodeScalarBytes
  encodeValueToBytes decodeValueFromBytes
  encodeRawAbstractByteVal decodeRawAbstractByteVal? encodeRawAbstractByteVals
  decodeRawAbstractByteVals? overlayRawAbstractByteVals
  globalAllocSliceToAbstractBytes
  decodePtrBytesNoForge decodeScalarLayoutBytesNoForge decodeTypedValueFromBytes
  validateValueForTy? evalConstValue evalOperand evalByteCast evalRvalue
  evalStmt evalCopySingleDirect evalCopyUnionBytes evalForeignFrameCopySingleDirect
  writePlaceValue writeBytesAction)
end V06

namespace V08
export Trusted.Rustc.V2026_08_01.Layout (LayoutTable TypeLayout Size Align BackendRepr
  ScalarLayout PrimitiveKind WrappingRange FieldsShape VariantsShape)
export Trusted.Rustc.V2026_08_01.MirAst (Ty RigidTy Mutability UintTy IntTy ScalarInt
  ProvenancePtr ConstScalar ConstValue ConstOperand ProjectionElem Place Operand Rvalue
  Statement StatementKind NonDivergingIntrinsic LocalDecl CapturedAllocation CapturedMir
  Terminator TerminatorKind)
export Trusted.Rustc.V2026_08_01.MirSemantics (PtrByteFrag AbstractByte Value LocalSlot
  BorrowEntry TreeBorrowPerm Memory StackFrame MachineState SavedCallerFrame MirStepNode
  RvalueEvalResult PlaceReadResult Ptr2IntTransmutePolicy UnionPlaceInfo
  ResolvedCallTarget WriteBytesAction
  emptyMemory defaultCodecFuel
  normPtrByteOffset mkInitByte mkPtrFragByte
  abstractBytesCoherentPtrProv? abstractBytesUniformProv abstractBytesHaveProv
  mergeByteProvenance
  encodeLittleEndianBytes encodeScalarBytes decodeLittleEndianBytes decodeScalarBytes
  encodeValueToBytes decodeValueFromBytes
  encodeRawAbstractByteVal decodeRawAbstractByteVal? encodeRawAbstractByteVals
  decodeRawAbstractByteVals? overlayRawAbstractByteVals
  globalAllocSliceToAbstractBytes
  decodePtrBytesNoForge decodeScalarLayoutBytesNoForge decodeTypedValueFromBytes
  validateValueForTy? evalConstValue evalOperand evalByteCast evalRvalue
  evalStmt evalCopySingleDirect evalCopyUnionBytes evalForeignFrameCopySingleDirect
  writePlaceValue writeBytesAction)
end V08

/-! ## §0. Shared Dialect Fixtures (`V2026_06_01` and `V2026_08_01`) -/

section Fixtures06

open V06

def unitL06 : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

def u8L06 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def boolL06 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def charL06 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def u64L06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def rawPtrL06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def refPtrL06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- `Unaligned<bool>` (`#[repr(packed)] struct Unaligned<T>(T)`): align 1, field layout = `boolL06` (idx 2). -/
def unalignedBoolL06 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [2] }

/-- `MaybeUninit<bool>` (`union { uninit: (), value: bool }`): size 1, align 1, union with 2 fields. -/
def maybeUninitBoolL06 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }

/-- `MaybeUninit<Unaligned<bool>>`: size 1, align 1, union with 2 fields. -/
def maybeUninitUnalignedBoolL06 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [7, 0] }

/-- `MaybeUninit<*const u8>`: size 8, align 8, union with 2 fields (`rawPtrL06`, `unitL06`). -/
def maybeUninitPtrL06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [5, 0] }

/-- `MaybeUninit<char>`: size 4, align 4, union with 2 fields (`charL06`, `unitL06`). -/
def maybeUninitCharL06 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [3, 0] }

/-- Multi-variant enum (`enum E3 { A = 0, B = 1, C = 2 }`): `VariantsShape.multiple` at idx 12. -/
def enum3L06 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 2⟩),
    fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 2⟩) 0
      [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []],
    isUninhabited := false }

/-- `[u8; 4]` array layout at idx 13. -/
def arr4U8L06 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 4, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

/-- `[u8; 8]` array layout at idx 14. -/
def arr8U8L06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 8, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

/-- `union RawOrPtr { raw: u64, ptr: *const u8 }` at idx 15. -/
def rawOrPtrUnionL06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [4, 5] }

def layouts64_06 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [unitL06, u8L06, boolL06, charL06, u64L06, rawPtrL06, refPtrL06,
      unalignedBoolL06, maybeUninitBoolL06, maybeUninitUnalignedBoolL06,
      maybeUninitPtrL06, maybeUninitCharL06, enum3L06, arr4U8L06, arr8U8L06,
      rawOrPtrUnionL06] }

def layouts32_06 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true,
    entries := [unitL06, u8L06, boolL06, charL06] }

def tyU8_06 : Ty := { kind := .uint .u8, layoutIdx := 1 }
def tyBool_06 : Ty := { kind := .bool, layoutIdx := 2 }
def tyChar_06 : Ty := { kind := .char, layoutIdx := 3 }
def tyU64_06 : Ty := { kind := .uint .u64, layoutIdx := 4 }
def tyUsize_06 : Ty := { kind := .uint .usize, layoutIdx := 4 }
def tyRawPtrU8_06 : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 5 }
def tyMutPtrU8_06 : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 5 }
def tyRefU8_06 : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 6 }
def tyFnPtr_06 : Ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 6 }
def tyRawSliceU8_06 : Ty := { kind := .rawPtr .not (.slice (.uint .u8)), layoutIdx := 0 }
def tyRefSliceU8_06 : Ty := { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
def tyRefStr_06 : Ty := { kind := .ref .not .str, layoutIdx := 0 }
def tyRawDyn_06 : Ty := { kind := .rawPtr .not (.dynamic "T"), layoutIdx := 0 }
def tyRefDyn_06 : Ty := { kind := .ref .not (.dynamic "T"), layoutIdx := 0 }
def tyUnalignedBool_06 : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 7 }
def tyMaybeUninitBool_06 : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 8 }
def tyMaybeUninitUnalignedBool_06 : Ty :=
  { kind := .adt "core::mem::MaybeUninit" [.adt "Unaligned" [.bool]], layoutIdx := 9 }
def tyMaybeUninitPtr_06 : Ty :=
  { kind := .adt "core::mem::MaybeUninit" [.rawPtr .not (.uint .u8)], layoutIdx := 10 }
def tyMaybeUninitChar_06 : Ty := { kind := .adt "core::mem::MaybeUninit" [.char], layoutIdx := 11 }
def tyEnum3_06 : Ty := { kind := .adt "E3" [], layoutIdx := 12 }
def tyArr4U8_06 : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 13 }
def tyArr8U8_06 : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 14 }
def tyRawOrPtrUnion_06 : Ty := { kind := .adt "RawOrPtr" [], layoutIdx := 15 }

def ptr64_06 : ProvenancePtr := { allocId := 7, offsetBytes := 0x10 }
def ptr64Zero_06 : ProvenancePtr := { allocId := 7, offsetBytes := 0 }
def ptr64Plus4_06 : ProvenancePtr := { allocId := 7, offsetBytes := 0x14 }
def ptr64Plus256_06 : ProvenancePtr := { allocId := 7, offsetBytes := 256 }
def vtPtr64_06 : ProvenancePtr := { allocId := 42, offsetBytes := 0x80 }
def ptr32_06 : ProvenancePtr := { allocId := 9, offsetBytes := 0x10 }
def ptr32Zero_06 : ProvenancePtr := { allocId := 9, offsetBytes := 0 }
def ptr32Plus256_06 : ProvenancePtr := { allocId := 9, offsetBytes := 256 }
def vtPtr32_06 : ProvenancePtr := { allocId := 43, offsetBytes := 0x20 }

def ptr64Bytes_06 : List AbstractByte := encodeLittleEndianBytes 0x10 8 (some (7, 7))
def ptr64ZeroBytes_06 : List AbstractByte := encodeLittleEndianBytes 0 8 (some (7, 7))
def ptr64Plus4Bytes_06 : List AbstractByte := encodeLittleEndianBytes 0x14 8 (some (7, 7))
def ptr64Plus256Bytes_06 : List AbstractByte := encodeLittleEndianBytes 256 8 (some (7, 7))
def vtPtr64Bytes_06 : List AbstractByte := encodeLittleEndianBytes 0x80 8 (some (42, 42))

def ptr32Bytes_06 : List AbstractByte := encodeLittleEndianBytes 0x10 4 (some (9, 9))
def ptr32ZeroBytes_06 : List AbstractByte := encodeLittleEndianBytes 0 4 (some (9, 9))
def ptr32Plus256Bytes_06 : List AbstractByte := encodeLittleEndianBytes 256 4 (some (9, 9))
def vtPtr32Bytes_06 : List AbstractByte := encodeLittleEndianBytes 0x20 4 (some (43, 43))

def swap01_06 : List AbstractByte → List AbstractByte
  | a :: b :: rest => b :: a :: rest
  | xs => xs

def dupHead_06 (n : Nat) : List AbstractByte → List AbstractByte
  | a :: _ => List.replicate n a
  | [] => []

/-- Adjacent identical relocations `[p, p]` at offsets `0` and `8` (64-bit). -/
def adjRelocAlloc64_06 : CapturedAllocation :=
  { allocId := 50,
    bytes := [some 0x10, some 0, some 0, some 0, some 0, some 0, some 0, some 0,
              some 0x10, some 0, some 0, some 0, some 0, some 0, some 0, some 0],
    relocations := [(0, ptr64_06), (8, ptr64_06)],
    align := ⟨8⟩, mutability := .not }

/-- 32-bit global allocation with relocation at offset `0` and plain integer bytes at `4..7`. -/
def relocAlloc32_06 : CapturedAllocation :=
  { allocId := 51,
    bytes := [some 0x10, some 0, some 0, some 0, some 0xAA, some 0xBB, some 0xCC, some 0xDD],
    relocations := [(0, ptr32_06)],
    align := ⟨4⟩, mutability := .not }

/-- Plain integer global allocation holding `0x20000` (131072) with NO relocations. -/
def plainIntAlloc64_06 : CapturedAllocation :=
  { allocId := 52,
    bytes := [some 0x00, some 0x00, some 0x02, some 0x00, some 0x00, some 0x00, some 0x00, some 0x00],
    relocations := [],
    align := ⟨8⟩, mutability := .not }

def mkState06 (locals : List LocalSlot) (mem : Memory := emptyMemory) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals }, memory := mem }

def emptyBody06 (decls : List LocalDecl) (layouts : LayoutTable) : CapturedMir :=
  { defPath := "caller",
    phase := .runtimePostCleanup,
    role := .subject,
    argCount := 0,
    localDecls := decls,
    basicBlocks := [],
    fnAbi := { args := [], ret := { layout := u8L06, mode := .direct }, conv := .rust, canUnwind := false },
    layouts := layouts,
    allocations := [] }

end Fixtures06

section Fixtures08

open V08

def unitL08 : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

def u8L08 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 255⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def boolL08 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def charL08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def u64L08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def rawPtrL08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def refPtrL08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨1, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def unalignedBoolL08 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .arbitrary [⟨0⟩] [0], variants := .single 0, isUninhabited := false,
    fieldLayouts := [2] }

def maybeUninitBoolL08 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }

def maybeUninitUnalignedBoolL08 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [7, 0] }

def maybeUninitPtrL08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [5, 0] }

def maybeUninitCharL08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [3, 0] }

def enum3L08 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 2⟩),
    fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 2⟩) 0
      [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []],
    isUninhabited := false }

def arr4U8L08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 4, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

def arr8U8L08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 8, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

def rawOrPtrUnionL08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [4, 5] }

def layouts64_08 : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true,
    entries := [unitL08, u8L08, boolL08, charL08, u64L08, rawPtrL08, refPtrL08,
      unalignedBoolL08, maybeUninitBoolL08, maybeUninitUnalignedBoolL08,
      maybeUninitPtrL08, maybeUninitCharL08, enum3L08, arr4U8L08, arr8U8L08,
      rawOrPtrUnionL08] }

def layouts32_08 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true,
    entries := [unitL08, u8L08, boolL08, charL08] }

def tyU8_08 : Ty := { kind := .uint .u8, layoutIdx := 1 }
def tyBool_08 : Ty := { kind := .bool, layoutIdx := 2 }
def tyChar_08 : Ty := { kind := .char, layoutIdx := 3 }
def tyU64_08 : Ty := { kind := .uint .u64, layoutIdx := 4 }
def tyUsize_08 : Ty := { kind := .uint .usize, layoutIdx := 4 }
def tyRawPtrU8_08 : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 5 }
def tyMutPtrU8_08 : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 5 }
def tyRefU8_08 : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 6 }
def tyFnPtr_08 : Ty := { kind := .fnPtr [.uint .u32] (.uint .u32) .safe .rust, layoutIdx := 6 }
def tyRawSliceU8_08 : Ty := { kind := .rawPtr .not (.slice (.uint .u8)), layoutIdx := 0 }
def tyRefSliceU8_08 : Ty := { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
def tyRefStr_08 : Ty := { kind := .ref .not .str, layoutIdx := 0 }
def tyRawDyn_08 : Ty := { kind := .rawPtr .not (.dynamic "T"), layoutIdx := 0 }
def tyRefDyn_08 : Ty := { kind := .ref .not (.dynamic "T"), layoutIdx := 0 }
def tyUnalignedBool_08 : Ty := { kind := .adt "Unaligned" [.bool], layoutIdx := 7 }
def tyMaybeUninitBool_08 : Ty := { kind := .adt "core::mem::MaybeUninit" [.bool], layoutIdx := 8 }
def tyMaybeUninitUnalignedBool_08 : Ty :=
  { kind := .adt "core::mem::MaybeUninit" [.adt "Unaligned" [.bool]], layoutIdx := 9 }
def tyMaybeUninitPtr_08 : Ty :=
  { kind := .adt "core::mem::MaybeUninit" [.rawPtr .not (.uint .u8)], layoutIdx := 10 }
def tyMaybeUninitChar_08 : Ty := { kind := .adt "core::mem::MaybeUninit" [.char], layoutIdx := 11 }
def tyEnum3_08 : Ty := { kind := .adt "E3" [], layoutIdx := 12 }
def tyArr4U8_08 : Ty := { kind := .array (.uint .u8) 4, layoutIdx := 13 }
def tyArr8U8_08 : Ty := { kind := .array (.uint .u8) 8, layoutIdx := 14 }
def tyRawOrPtrUnion_08 : Ty := { kind := .adt "RawOrPtr" [], layoutIdx := 15 }

def ptr64_08 : ProvenancePtr := { allocId := 7, offsetBytes := 0x10 }
def ptr64Zero_08 : ProvenancePtr := { allocId := 7, offsetBytes := 0 }
def ptr64Plus4_08 : ProvenancePtr := { allocId := 7, offsetBytes := 0x14 }
def ptr64Plus256_08 : ProvenancePtr := { allocId := 7, offsetBytes := 256 }
def vtPtr64_08 : ProvenancePtr := { allocId := 42, offsetBytes := 0x80 }
def ptr32_08 : ProvenancePtr := { allocId := 9, offsetBytes := 0x10 }
def ptr32Zero_08 : ProvenancePtr := { allocId := 9, offsetBytes := 0 }
def ptr32Plus256_08 : ProvenancePtr := { allocId := 9, offsetBytes := 256 }
def vtPtr32_08 : ProvenancePtr := { allocId := 43, offsetBytes := 0x20 }

def ptr64Bytes_08 : List AbstractByte := encodeLittleEndianBytes 0x10 8 (some (7, 7))
def ptr64ZeroBytes_08 : List AbstractByte := encodeLittleEndianBytes 0 8 (some (7, 7))
def ptr64Plus4Bytes_08 : List AbstractByte := encodeLittleEndianBytes 0x14 8 (some (7, 7))
def ptr64Plus256Bytes_08 : List AbstractByte := encodeLittleEndianBytes 256 8 (some (7, 7))
def vtPtr64Bytes_08 : List AbstractByte := encodeLittleEndianBytes 0x80 8 (some (42, 42))

def ptr32Bytes_08 : List AbstractByte := encodeLittleEndianBytes 0x10 4 (some (9, 9))
def ptr32ZeroBytes_08 : List AbstractByte := encodeLittleEndianBytes 0 4 (some (9, 9))
def ptr32Plus256Bytes_08 : List AbstractByte := encodeLittleEndianBytes 256 4 (some (9, 9))
def vtPtr32Bytes_08 : List AbstractByte := encodeLittleEndianBytes 0x20 4 (some (43, 43))

def swap01_08 : List AbstractByte → List AbstractByte
  | a :: b :: rest => b :: a :: rest
  | xs => xs

def dupHead_08 (n : Nat) : List AbstractByte → List AbstractByte
  | a :: _ => List.replicate n a
  | [] => []

def adjRelocAlloc64_08 : CapturedAllocation :=
  { allocId := 50,
    bytes := [some 0x10, some 0, some 0, some 0, some 0, some 0, some 0, some 0,
              some 0x10, some 0, some 0, some 0, some 0, some 0, some 0, some 0],
    relocations := [(0, ptr64_08), (8, ptr64_08)],
    align := ⟨8⟩, mutability := .not }

def relocAlloc32_08 : CapturedAllocation :=
  { allocId := 51,
    bytes := [some 0x10, some 0, some 0, some 0, some 0xAA, some 0xBB, some 0xCC, some 0xDD],
    relocations := [(0, ptr32_08)],
    align := ⟨4⟩, mutability := .not }

def plainIntAlloc64_08 : CapturedAllocation :=
  { allocId := 52,
    bytes := [some 0x00, some 0x00, some 0x02, some 0x00, some 0x00, some 0x00, some 0x00, some 0x00],
    relocations := [],
    align := ⟨8⟩, mutability := .not }

def mkState08 (locals : List LocalSlot) (mem : Memory := emptyMemory) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals }, memory := mem }

def emptyBody08 (decls : List LocalDecl) (layouts : LayoutTable) : CapturedMir :=
  { defPath := "caller",
    phase := .runtimePostCleanup,
    role := .subject,
    argCount := 0,
    localDecls := decls,
    basicBlocks := [],
    fnAbi := { args := [], ret := { layout := u8L08, mode := .direct }, conv := .rust, canUnwind := false },
    layouts := layouts,
    allocations := [] }

end Fixtures08

/-! ## §1. Adversarial Pointer Byte Manipulations (Brief §3.1(a)–(h), Both Dialects + Parity) -/

/-- §3.1(a): 8-byte and 4-byte full reversal — including `offsetBytes = 0` all-zero bytes —
MUST strip provenance (yielding `.scalar` for raw pointers and `.none` for references/`fnPtr`)
in lockstep across `V2026_06_01` and `V2026_08_01`. -/
theorem neg_3_1a_reversal_8_and_4_including_zero_offset_v06 :
    V06.abstractBytesCoherentPtrProv? ptr64Bytes_06.reverse = none ∧
    V06.abstractBytesCoherentPtrProv? ptr64ZeroBytes_06.reverse = none ∧
    V06.abstractBytesCoherentPtrProv? ptr32Bytes_06.reverse = none ∧
    V06.abstractBytesCoherentPtrProv? ptr32ZeroBytes_06.reverse = none ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_06.reverse =
      some (.scalar ⟨0x1000000000000000, 8⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 8 ptr64Bytes_06.reverse = none ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 8 ptr64ZeroBytes_06.reverse =
      some (.scalar ⟨0, 8⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 8 ptr64ZeroBytes_06.reverse = none ∧
    V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyFnPtr_06
      ptr64ZeroBytes_06.reverse = none ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 4 ptr32Bytes_06.reverse =
      some (.scalar ⟨0x10000000, 4⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 4 ptr32Bytes_06.reverse = none ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 4 ptr32ZeroBytes_06.reverse =
      some (.scalar ⟨0, 4⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 4 ptr32ZeroBytes_06.reverse = none ∧
    V06.decodeValueFromBytes V06.defaultCodecFuel layouts64_06 tyRawPtrU8_06
      ptr64ZeroBytes_06.reverse = some (.scalar ⟨0, 8⟩) ∧
    V06.decodeValueFromBytes V06.defaultCodecFuel layouts64_06 tyRefU8_06
      ptr64ZeroBytes_06.reverse = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

theorem neg_3_1a_reversal_8_and_4_including_zero_offset_v08 :
    V08.abstractBytesCoherentPtrProv? ptr64Bytes_08.reverse = none ∧
    V08.abstractBytesCoherentPtrProv? ptr64ZeroBytes_08.reverse = none ∧
    V08.abstractBytesCoherentPtrProv? ptr32Bytes_08.reverse = none ∧
    V08.abstractBytesCoherentPtrProv? ptr32ZeroBytes_08.reverse = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_08.reverse =
      some (.scalar ⟨0x1000000000000000, 8⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 8 ptr64Bytes_08.reverse = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 8 ptr64ZeroBytes_08.reverse =
      some (.scalar ⟨0, 8⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 8 ptr64ZeroBytes_08.reverse = none ∧
    V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyFnPtr_08
      ptr64ZeroBytes_08.reverse = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 4 ptr32Bytes_08.reverse =
      some (.scalar ⟨0x10000000, 4⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 4 ptr32Bytes_08.reverse = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 4 ptr32ZeroBytes_08.reverse =
      some (.scalar ⟨0, 4⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 4 ptr32ZeroBytes_08.reverse = none ∧
    V08.decodeValueFromBytes V08.defaultCodecFuel layouts64_08 tyRawPtrU8_08
      ptr64ZeroBytes_08.reverse = some (.scalar ⟨0, 8⟩) ∧
    V08.decodeValueFromBytes V08.defaultCodecFuel layouts64_08 tyRefU8_08
      ptr64ZeroBytes_08.reverse = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.1(b): Swapping bytes 0 and 1 (8-byte and 4-byte, non-zero and zero offset) strips provenance. -/
theorem neg_3_1b_swap_bytes_0_1_v06_v08 :
    V06.decodePtrBytesNoForge false (.uint .u8) 8 (swap01_06 ptr64Bytes_06) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 8 (swap01_06 ptr64Bytes_06) = none ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 8 (swap01_06 ptr64ZeroBytes_06) =
      some (.scalar ⟨0, 8⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 8 (swap01_06 ptr64ZeroBytes_06) = none ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 4 (swap01_06 ptr32Bytes_06) =
      some (.scalar ⟨0x1000, 4⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 4 (swap01_06 ptr32Bytes_06) = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 8 (swap01_08 ptr64Bytes_08) =
      some (.scalar ⟨0x1000, 8⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 8 (swap01_08 ptr64Bytes_08) = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 8 (swap01_08 ptr64ZeroBytes_08) =
      some (.scalar ⟨0, 8⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 8 (swap01_08 ptr64ZeroBytes_08) = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 4 (swap01_08 ptr32Bytes_08) =
      some (.scalar ⟨0x1000, 4⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 4 (swap01_08 ptr32Bytes_08) = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.1(c): Duplicating byte 0 repeated `ptrBytes` times strips provenance (8-byte and 4-byte). -/
theorem neg_3_1c_duplicate_byte0_v06_v08 :
    V06.decodePtrBytesNoForge false (.uint .u8) 8 (dupHead_06 8 ptr64Bytes_06) =
      some (.scalar ⟨0x1010101010101010, 8⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 8 (dupHead_06 8 ptr64Bytes_06) = none ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 4 (dupHead_06 4 ptr32Bytes_06) =
      some (.scalar ⟨0x10101010, 4⟩) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 4 (dupHead_06 4 ptr32Bytes_06) = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 8 (dupHead_08 8 ptr64Bytes_08) =
      some (.scalar ⟨0x1010101010101010, 8⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 8 (dupHead_08 8 ptr64Bytes_08) = none ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 4 (dupHead_08 4 ptr32Bytes_08) =
      some (.scalar ⟨0x10101010, 4⟩) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 4 (dupHead_08 4 ptr32Bytes_08) = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.1(d): Same-`(allocId, tag)` offset splice (`p` byte 0 + `p+4` bytes `1..7`; AND `p` byte 0
+ `p+256` bytes `1..7` where byte 0 is identically `0x00` in both pointers!), cross-width splice,
and tag mismatch splice all strip provenance in both dialects. -/
theorem neg_3_1d_offset_splice_cross_width_and_tag_mismatch_v06_v08 :
    let spliceP4_06 := ptr64Bytes_06.take 1 ++ ptr64Plus4Bytes_06.drop 1
    let spliceP256_06 := ptr64ZeroBytes_06.take 1 ++ ptr64Plus256Bytes_06.drop 1
    let splice32P256_06 := ptr32ZeroBytes_06.take 1 ++ ptr32Plus256Bytes_06.drop 1
    let crossWidth_06 := ptr32Bytes_06.take 1 ++ ptr64Bytes_06.drop 1
    let tagMismatch_06 :=
      (V06.encodeLittleEndianBytes 0x10 8 (some (7, 7))).take 1 ++
      (V06.encodeLittleEndianBytes 0x10 8 (some (7, 8))).drop 1
    let spliceP4_08 := ptr64Bytes_08.take 1 ++ ptr64Plus4Bytes_08.drop 1
    let spliceP256_08 := ptr64ZeroBytes_08.take 1 ++ ptr64Plus256Bytes_08.drop 1
    let splice32P256_08 := ptr32ZeroBytes_08.take 1 ++ ptr32Plus256Bytes_08.drop 1
    let crossWidth_08 := ptr32Bytes_08.take 1 ++ ptr64Bytes_08.drop 1
    let tagMismatch_08 :=
      (V08.encodeLittleEndianBytes 0x10 8 (some (7, 7))).take 1 ++
      (V08.encodeLittleEndianBytes 0x10 8 (some (7, 8))).drop 1
    (V06.decodePtrBytesNoForge false (.uint .u8) 8 spliceP4_06 = some (.scalar ⟨0x10, 8⟩) ∧
     V06.decodePtrBytesNoForge true (.uint .u8) 8 spliceP4_06 = none ∧
     V06.decodePtrBytesNoForge false (.uint .u8) 8 spliceP256_06 = some (.scalar ⟨256, 8⟩) ∧
     V06.decodePtrBytesNoForge true (.uint .u8) 8 spliceP256_06 = none ∧
     V06.decodePtrBytesNoForge false (.uint .u8) 4 splice32P256_06 = some (.scalar ⟨256, 4⟩) ∧
     V06.decodePtrBytesNoForge true (.uint .u8) 4 splice32P256_06 = none ∧
     V06.decodePtrBytesNoForge false (.uint .u8) 8 crossWidth_06 = some (.scalar ⟨0x10, 8⟩) ∧
     V06.decodePtrBytesNoForge true (.uint .u8) 8 crossWidth_06 = none ∧
     V06.decodePtrBytesNoForge false (.uint .u8) 8 tagMismatch_06 = some (.scalar ⟨0x10, 8⟩) ∧
     V06.decodePtrBytesNoForge true (.uint .u8) 8 tagMismatch_06 = none) ∧
    (V08.decodePtrBytesNoForge false (.uint .u8) 8 spliceP4_08 = some (.scalar ⟨0x10, 8⟩) ∧
     V08.decodePtrBytesNoForge true (.uint .u8) 8 spliceP4_08 = none ∧
     V08.decodePtrBytesNoForge false (.uint .u8) 8 spliceP256_08 = some (.scalar ⟨256, 8⟩) ∧
     V08.decodePtrBytesNoForge true (.uint .u8) 8 spliceP256_08 = none ∧
     V08.decodePtrBytesNoForge false (.uint .u8) 4 splice32P256_08 = some (.scalar ⟨256, 4⟩) ∧
     V08.decodePtrBytesNoForge true (.uint .u8) 4 splice32P256_08 = none ∧
     V08.decodePtrBytesNoForge false (.uint .u8) 8 crossWidth_08 = some (.scalar ⟨0x10, 8⟩) ∧
     V08.decodePtrBytesNoForge true (.uint .u8) 8 crossWidth_08 = none ∧
     V08.decodePtrBytesNoForge false (.uint .u8) 8 tagMismatch_08 = some (.scalar ⟨0x10, 8⟩) ∧
     V08.decodePtrBytesNoForge true (.uint .u8) 8 tagMismatch_08 = none) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.1(e) + W3: Wide pointers (`&[u8]`, `*const [u8]`, `&str`, `&dyn Trait`, `*const dyn Trait`):
swapped halves, reversed data or vtable bytes, provenance on slice/`str` metadata, and
provenance-less or incoherent vtable bytes on `&dyn Trait` are rejected / stripped in both dialects. -/
theorem neg_3_1e_wide_ptrs_and_dyn_vtable_w3_v06 :
    let lenBytes := V06.encodeLittleEndianBytes 4 8 none
    let provLenBytes := V06.encodeLittleEndianBytes 4 8 (some (99, 99))
    let plainVtBytes := V06.encodeLittleEndianBytes 0x80 8 none
    -- Swapped data/meta halves on `&[u8]` and `*const [u8]`: metadata carries provenance -> rejected
    V06.decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lenBytes ++ ptr64Bytes_06) = none ∧
    V06.decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (lenBytes ++ ptr64Bytes_06) = none ∧
    -- Reversed data bytes on `&[u8]`, `*const [u8]`, `&str`
    V06.decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (ptr64Bytes_06.reverse ++ lenBytes) = none ∧
    V06.decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (ptr64Bytes_06.reverse ++ lenBytes) =
      some (.aggregate 0 [.scalar ⟨0x1000000000000000, 8⟩, .scalar ⟨4, 8⟩]) ∧
    V06.decodePtrBytesNoForge true .str 8 (ptr64Bytes_06.reverse ++ lenBytes) = none ∧
    -- Provenance on slice / str metadata rejected
    V06.decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (ptr64Bytes_06 ++ provLenBytes) = none ∧
    V06.decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (ptr64Bytes_06 ++ provLenBytes) = none ∧
    V06.decodePtrBytesNoForge true .str 8 (ptr64Bytes_06 ++ provLenBytes) = none ∧
    -- `&dyn Trait` (isRef = true): provenance-less or reversed vtable MUST return `none` (W3)
    V06.decodePtrBytesNoForge true (.dynamic "T") 8 (ptr64Bytes_06 ++ plainVtBytes) = none ∧
    V06.decodePtrBytesNoForge true (.dynamic "T") 8 (ptr64Bytes_06 ++ vtPtr64Bytes_06.reverse) = none ∧
    V06.decodePtrBytesNoForge true (.dynamic "T") 8 (ptr64Bytes_06.reverse ++ vtPtr64Bytes_06) = none ∧
    -- `*const dyn Trait` (isRef = false): reversed vtable strips vtable provenance to `.scalar`
    V06.decodePtrBytesNoForge false (.dynamic "T") 8 (ptr64Bytes_06 ++ vtPtr64Bytes_06.reverse) =
      some (.aggregate 0 [.ptr ptr64_06 8, .scalar ⟨0x8000000000000000, 8⟩]) ∧
    -- 32-bit `&dyn Trait`: reversed 4-byte vtable rejected
    V06.decodePtrBytesNoForge true (.dynamic "T") 4 (ptr32Bytes_06 ++ vtPtr32Bytes_06.reverse) = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

theorem neg_3_1e_wide_ptrs_and_dyn_vtable_w3_v08 :
    let lenBytes := V08.encodeLittleEndianBytes 4 8 none
    let provLenBytes := V08.encodeLittleEndianBytes 4 8 (some (99, 99))
    let plainVtBytes := V08.encodeLittleEndianBytes 0x80 8 none
    V08.decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (lenBytes ++ ptr64Bytes_08) = none ∧
    V08.decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (lenBytes ++ ptr64Bytes_08) = none ∧
    V08.decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (ptr64Bytes_08.reverse ++ lenBytes) = none ∧
    V08.decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (ptr64Bytes_08.reverse ++ lenBytes) =
      some (.aggregate 0 [.scalar ⟨0x1000000000000000, 8⟩, .scalar ⟨4, 8⟩]) ∧
    V08.decodePtrBytesNoForge true .str 8 (ptr64Bytes_08.reverse ++ lenBytes) = none ∧
    V08.decodePtrBytesNoForge true (.slice (.uint .u8)) 8 (ptr64Bytes_08 ++ provLenBytes) = none ∧
    V08.decodePtrBytesNoForge false (.slice (.uint .u8)) 8 (ptr64Bytes_08 ++ provLenBytes) = none ∧
    V08.decodePtrBytesNoForge true .str 8 (ptr64Bytes_08 ++ provLenBytes) = none ∧
    V08.decodePtrBytesNoForge true (.dynamic "T") 8 (ptr64Bytes_08 ++ plainVtBytes) = none ∧
    V08.decodePtrBytesNoForge true (.dynamic "T") 8 (ptr64Bytes_08 ++ vtPtr64Bytes_08.reverse) = none ∧
    V08.decodePtrBytesNoForge true (.dynamic "T") 8 (ptr64Bytes_08.reverse ++ vtPtr64Bytes_08) = none ∧
    V08.decodePtrBytesNoForge false (.dynamic "T") 8 (ptr64Bytes_08 ++ vtPtr64Bytes_08.reverse) =
      some (.aggregate 0 [.ptr ptr64_08 8, .scalar ⟨0x8000000000000000, 8⟩]) ∧
    V08.decodePtrBytesNoForge true (.dynamic "T") 4 (ptr32Bytes_08 ++ vtPtr32Bytes_08.reverse) = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.1(f) + W4: Global allocations — misaligned read at offset `1` or `4` across adjacent
identical relocations `[p, p]` strips provenance; 32-bit relocation at offset `0` does NOT
bleed provenance into bytes `4..7`. -/
theorem neg_3_1f_global_alloc_misaligned_and_32bit_no_bleed_v06_v08 :
    (match V06.globalAllocSliceToAbstractBytes adjRelocAlloc64_06 1 8 8,
           V06.globalAllocSliceToAbstractBytes adjRelocAlloc64_06 4 8 8,
           V06.globalAllocSliceToAbstractBytes relocAlloc32_06 4 4 4 with
     | some bsOff1, some bsOff4, some bs32Tail =>
       V06.abstractBytesCoherentPtrProv? bsOff1 = none ∧
       V06.decodePtrBytesNoForge false (.uint .u8) 8 bsOff1 =
         some (.scalar ⟨0x1000000000000000, 8⟩) ∧
       V06.decodePtrBytesNoForge true (.uint .u8) 8 bsOff1 = none ∧
       V06.abstractBytesCoherentPtrProv? bsOff4 = none ∧
       V06.decodePtrBytesNoForge false (.uint .u8) 8 bsOff4 =
         some (.scalar ⟨0x0000001000000000, 8⟩) ∧
       V06.decodePtrBytesNoForge true (.uint .u8) 8 bsOff4 = none ∧
       V06.abstractBytesHaveProv bs32Tail = false
     | _, _, _ => False) ∧
    (match V08.globalAllocSliceToAbstractBytes adjRelocAlloc64_08 1 8 8,
           V08.globalAllocSliceToAbstractBytes adjRelocAlloc64_08 4 8 8,
           V08.globalAllocSliceToAbstractBytes relocAlloc32_08 4 4 4 with
     | some bsOff1, some bsOff4, some bs32Tail =>
       V08.abstractBytesCoherentPtrProv? bsOff1 = none ∧
       V08.decodePtrBytesNoForge false (.uint .u8) 8 bsOff1 =
         some (.scalar ⟨0x1000000000000000, 8⟩) ∧
       V08.decodePtrBytesNoForge true (.uint .u8) 8 bsOff1 = none ∧
       V08.abstractBytesCoherentPtrProv? bsOff4 = none ∧
       V08.decodePtrBytesNoForge false (.uint .u8) 8 bsOff4 =
         some (.scalar ⟨0x0000001000000000, 8⟩) ∧
       V08.decodePtrBytesNoForge true (.uint .u8) 8 bsOff4 = none ∧
       V08.abstractBytesHaveProv bs32Tail = false
     | _, _, _ => False) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.1(g) + W5 (part 1): Integer-to-pointer forging (`0x20000`) is blocked in `evalConstValue`
(`.slice` and `.indirect`) and `evalByteCast` (`transmute`) across both dialects. -/
theorem neg_3_1g_const_and_bytecast_no_forge_v06_v08 :
    -- V2026_06_01
    V06.evalConstValue (.slice (.int ⟨0x20000, 8⟩) 4) tyRawSliceU8_06 [] layouts64_06 =
      some (.aggregate 0 [.scalar ⟨0x20000, 8⟩, .scalar ⟨4, 8⟩]) ∧
    V06.evalConstValue (.slice (.int ⟨0x20000, 8⟩) 4) tyRefSliceU8_06 [] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 52 0) tyRawPtrU8_06 [plainIntAlloc64_06] layouts64_06 =
      some (.scalar ⟨0x20000, 8⟩) ∧
    V06.evalConstValue (.indirect 52 0) tyRefU8_06 [plainIntAlloc64_06] layouts64_06 = none ∧
    (let decls06 : List V06.LocalDecl := [{ mutability := .not, ty := tyU64_06, debugName := none }]
     let locals06 : List V06.LocalSlot := [.init (.scalar ⟨0x20000, 8⟩)]
     V06.evalByteCast locals06 (.copy ⟨0, []⟩) tyRawPtrU8_06 V06.emptyMemory decls06 layouts64_06 =
       .ok (.scalar ⟨0x20000, 8⟩) locals06 V06.emptyMemory ∧
     V06.evalByteCast locals06 (.copy ⟨0, []⟩) tyRefU8_06 V06.emptyMemory decls06 layouts64_06 = .ub ∧
     V06.evalByteCast locals06 (.copy ⟨0, []⟩) tyFnPtr_06 V06.emptyMemory decls06 layouts64_06 = .ub) ∧
    -- V2026_08_01
    V08.evalConstValue (.slice (.int ⟨0x20000, 8⟩) 4) tyRawSliceU8_08 [] layouts64_08 =
      some (.aggregate 0 [.scalar ⟨0x20000, 8⟩, .scalar ⟨4, 8⟩]) ∧
    V08.evalConstValue (.slice (.int ⟨0x20000, 8⟩) 4) tyRefSliceU8_08 [] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 52 0) tyRawPtrU8_08 [plainIntAlloc64_08] layouts64_08 =
      some (.scalar ⟨0x20000, 8⟩) ∧
    V08.evalConstValue (.indirect 52 0) tyRefU8_08 [plainIntAlloc64_08] layouts64_08 = none ∧
    (let decls08 : List V08.LocalDecl := [{ mutability := .not, ty := tyU64_08, debugName := none }]
     let locals08 : List V08.LocalSlot := [.init (.scalar ⟨0x20000, 8⟩)]
     V08.evalByteCast locals08 (.copy ⟨0, []⟩) tyRawPtrU8_08 V08.emptyMemory decls08 layouts64_08 =
       .ok (.scalar ⟨0x20000, 8⟩) locals08 V08.emptyMemory ∧
     V08.evalByteCast locals08 (.copy ⟨0, []⟩) tyRefU8_08 V08.emptyMemory decls08 layouts64_08 = .ub ∧
     V08.evalByteCast locals08 (.copy ⟨0, []⟩) tyFnPtr_08 V08.emptyMemory decls08 layouts64_08 = .ub) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.1(g) + W5 (part 2): Integer-to-pointer forging (`0x20000`) is blocked end-to-end across
`evalCopySingleDirect`, `evalCopyUnionBytes`, and `evalForeignFrameCopySingleDirect` in both
`V2026_06_01` and `V2026_08_01`. -/
def StepHasLocal06 (idx : Nat) (expected : V06.LocalSlot) : V06.MirStepNode → Prop
  | .tau (.running s) => s.frame.locals[idx]? = some expected
  | _ => False

def StepHasCallerLocal06 (idx : Nat) (expected : V06.LocalSlot) : V06.MirStepNode → Prop
  | .tau (.running s) =>
    match s.memory.callStack with
    | cf :: _ => cf.frame.locals[idx]? = some expected
    | [] => False
  | _ => False

def IsUbStep06 : V06.MirStepNode → Prop
  | .vis (.inl (.fail .ub)) _ => True
  | _ => False

def StepHasLocal08 (idx : Nat) (expected : V08.LocalSlot) : V08.MirStepNode → Prop
  | .tau (.running s) => s.frame.locals[idx]? = some expected
  | _ => False

def StepHasCallerLocal08 (idx : Nat) (expected : V08.LocalSlot) : V08.MirStepNode → Prop
  | .tau (.running s) =>
    match s.memory.callStack with
    | cf :: _ => cf.frame.locals[idx]? = some expected
    | [] => False
  | _ => False

def IsUbStep08 : V08.MirStepNode → Prop
  | .vis (.inl (.fail .ub)) _ => True
  | _ => False

theorem neg_3_1g_copy_paths_no_forge_v06 :
    -- 1. evalCopySingleDirect: u64 (0x20000) -> *const u8 (no forge -> .scalar) vs -> &u8 (.ub)
    let srcPtr : V06.ProvenancePtr := { allocId := 10, offsetBytes := 0 }
    let dstRawPtr : V06.ProvenancePtr := { allocId := 11, offsetBytes := 0 }
    let dstRefPtr : V06.ProvenancePtr := { allocId := 12, offsetBytes := 0 }
    let srcEntry : V06.BorrowEntry :=
      { tag := 10, targetLocal := 0, targetProjection := [], perm := .frozen }
    let dstRawEntry : V06.BorrowEntry :=
      { tag := 11, targetLocal := 1, targetProjection := [], perm := .active }
    let dstRefEntry : V06.BorrowEntry :=
      { tag := 12, targetLocal := 2, targetProjection := [], perm := .active }
    let decls : List V06.LocalDecl := [
      { mutability := .not, ty := tyU64_06, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .mut, ty := tyRefU8_06, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.rawPtr .not (.uint .u8)), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.ref .not (.uint .u8)), layoutIdx := 5 }, debugName := none }
    ]
    let locals : List V06.LocalSlot := [
      .init (.scalar ⟨0x20000, 8⟩),
      .uninit,
      .uninit,
      .init (.ptr srcPtr 8),
      .init (.ptr dstRawPtr 8),
      .init (.ptr dstRefPtr 8)
    ]
    let mem : V06.Memory := { V06.emptyMemory with borrows := [srcEntry, dstRawEntry, dstRefEntry] }
    let st := mkState06 locals mem
    let resDirectRaw := V06.evalCopySingleDirect st (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      decls layouts64_06 srcPtr dstRawPtr srcEntry dstRawEntry locals
    let resDirectRef := V06.evalCopySingleDirect st (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)
      decls layouts64_06 srcPtr dstRefPtr srcEntry dstRefEntry locals
    -- 2. evalCopyUnionBytes: union holding raw 0x20000 -> *const u8 (no forge) vs -> &u8 (.ub)
    let uInfo : V06.UnionPlaceInfo :=
      { unionBytes := 8, fieldTarget := none, subBaseOffset := 0, placeByteBound := 8 }
    let uVal : V06.Value := .aggregate 0 [(.scalar ⟨0x20000, 8⟩ : V06.Value), .uninit]
    let declsU : List V06.LocalDecl := [
      { mutability := .not, ty := tyRawOrPtrUnion_06, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .mut, ty := tyRefU8_06, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.rawPtr .not (.uint .u8)), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.ref .not (.uint .u8)), layoutIdx := 5 }, debugName := none }
    ]
    let localsU : List V06.LocalSlot := [
      .init uVal, .uninit, .uninit,
      .init (.ptr srcPtr 8), .init (.ptr dstRawPtr 8), .init (.ptr dstRefPtr 8)
    ]
    let stU := mkState06 localsU mem
    let resUnionRaw := V06.evalCopyUnionBytes stU (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      declsU layouts64_06 srcPtr dstRawPtr srcEntry dstRawEntry (some uInfo) none 1 localsU
    let resUnionRef := V06.evalCopyUnionBytes stU (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)
      declsU layouts64_06 srcPtr dstRefPtr srcEntry dstRefEntry (some uInfo) none 1 localsU
    -- 3. evalForeignFrameCopySingleDirect: callee u64 (0x20000) -> caller *const u8 vs caller &u8
    let callerDecls : List V06.LocalDecl := [
      { mutability := .mut, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .mut, ty := tyRefU8_06, debugName := none }
    ]
    let savedCaller : V06.SavedCallerFrame :=
      { callerBody := emptyBody06 callerDecls layouts64_06,
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
        destination := ⟨0, []⟩ }
    let dstForeignRaw : V06.BorrowEntry :=
      { tag := 21, targetLocal := 0, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dstForeignRef : V06.BorrowEntry :=
      { tag := 22, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let srcCallee : V06.BorrowEntry :=
      { tag := 20, targetLocal := 0, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let memF : V06.Memory :=
      { V06.emptyMemory with
        borrows := [srcCallee, dstForeignRaw, dstForeignRef],
        callStack := [savedCaller] }
    let stF := mkState06 locals memF
    let resForeignRaw := V06.evalForeignFrameCopySingleDirect stF (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      decls layouts64_06 { allocId := 20, offsetBytes := 0 } { allocId := 21, offsetBytes := 0 }
      srcCallee dstForeignRaw 1 locals
    let resForeignRef := V06.evalForeignFrameCopySingleDirect stF (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)
      decls layouts64_06 { allocId := 20, offsetBytes := 0 } { allocId := 22, offsetBytes := 0 }
      srcCallee dstForeignRef 1 locals
    StepHasLocal06 1 (.init (.scalar ⟨0x20000, 8⟩)) resDirectRaw ∧
    IsUbStep06 resDirectRef ∧
    StepHasLocal06 1 (.init (.scalar ⟨0x20000, 8⟩)) resUnionRaw ∧
    IsUbStep06 resUnionRef ∧
    StepHasCallerLocal06 0 (.init (.scalar ⟨0x20000, 8⟩)) resForeignRaw ∧
    IsUbStep06 resForeignRef := by
  exact ⟨rfl, trivial, rfl, trivial, rfl, trivial⟩

theorem neg_3_1g_copy_paths_no_forge_v08 :
    let srcPtr : V08.ProvenancePtr := { allocId := 10, offsetBytes := 0 }
    let dstRawPtr : V08.ProvenancePtr := { allocId := 11, offsetBytes := 0 }
    let dstRefPtr : V08.ProvenancePtr := { allocId := 12, offsetBytes := 0 }
    let srcEntry : V08.BorrowEntry :=
      { tag := 10, targetLocal := 0, targetProjection := [], perm := .frozen }
    let dstRawEntry : V08.BorrowEntry :=
      { tag := 11, targetLocal := 1, targetProjection := [], perm := .active }
    let dstRefEntry : V08.BorrowEntry :=
      { tag := 12, targetLocal := 2, targetProjection := [], perm := .active }
    let decls : List V08.LocalDecl := [
      { mutability := .not, ty := tyU64_08, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .mut, ty := tyRefU8_08, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.rawPtr .not (.uint .u8)), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.ref .not (.uint .u8)), layoutIdx := 5 }, debugName := none }
    ]
    let locals : List V08.LocalSlot := [
      .init (.scalar ⟨0x20000, 8⟩),
      .uninit,
      .uninit,
      .init (.ptr srcPtr 8),
      .init (.ptr dstRawPtr 8),
      .init (.ptr dstRefPtr 8)
    ]
    let mem : V08.Memory := { V08.emptyMemory with borrows := [srcEntry, dstRawEntry, dstRefEntry] }
    let st := mkState08 locals mem
    let resDirectRaw := V08.evalCopySingleDirect st (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      decls layouts64_08 srcPtr dstRawPtr srcEntry dstRawEntry locals
    let resDirectRef := V08.evalCopySingleDirect st (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)
      decls layouts64_08 srcPtr dstRefPtr srcEntry dstRefEntry locals
    let uInfo : V08.UnionPlaceInfo :=
      { unionBytes := 8, fieldTarget := none, subBaseOffset := 0, placeByteBound := 8 }
    let uVal : V08.Value := .aggregate 0 [(.scalar ⟨0x20000, 8⟩ : V08.Value), .unit]
    let declsU : List V08.LocalDecl := [
      { mutability := .not, ty := tyRawOrPtrUnion_08, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .mut, ty := tyRefU8_08, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.rawPtr .not (.uint .u8)), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.ref .not (.uint .u8)), layoutIdx := 5 }, debugName := none }
    ]
    let localsU : List V08.LocalSlot := [
      .init uVal, .uninit, .uninit,
      .init (.ptr srcPtr 8), .init (.ptr dstRawPtr 8), .init (.ptr dstRefPtr 8)
    ]
    let stU := mkState08 localsU mem
    let resUnionRaw := V08.evalCopyUnionBytes stU (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      declsU layouts64_08 srcPtr dstRawPtr srcEntry dstRawEntry (some uInfo) none 1 localsU
    let resUnionRef := V08.evalCopyUnionBytes stU (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)
      declsU layouts64_08 srcPtr dstRefPtr srcEntry dstRefEntry (some uInfo) none 1 localsU
    let callerDecls : List V08.LocalDecl := [
      { mutability := .mut, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .mut, ty := tyRefU8_08, debugName := none }
    ]
    let savedCaller : V08.SavedCallerFrame :=
      { callerBody := emptyBody08 callerDecls layouts64_08,
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
        destination := ⟨0, []⟩ }
    let dstForeignRaw : V08.BorrowEntry :=
      { tag := 21, targetLocal := 0, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dstForeignRef : V08.BorrowEntry :=
      { tag := 22, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let srcCallee : V08.BorrowEntry :=
      { tag := 20, targetLocal := 0, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let memF : V08.Memory :=
      { V08.emptyMemory with
        borrows := [srcCallee, dstForeignRaw, dstForeignRef],
        callStack := [savedCaller] }
    let stF := mkState08 locals memF
    let resForeignRaw := V08.evalForeignFrameCopySingleDirect stF (.copy ⟨3, []⟩) (.copy ⟨4, []⟩)
      decls layouts64_08 { allocId := 20, offsetBytes := 0 } { allocId := 21, offsetBytes := 0 }
      srcCallee dstForeignRaw 1 locals
    let resForeignRef := V08.evalForeignFrameCopySingleDirect stF (.copy ⟨3, []⟩) (.copy ⟨5, []⟩)
      decls layouts64_08 { allocId := 20, offsetBytes := 0 } { allocId := 22, offsetBytes := 0 }
      srcCallee dstForeignRef 1 locals
    StepHasLocal08 1 (.init (.scalar ⟨0x20000, 8⟩)) resDirectRaw ∧
    IsUbStep08 resDirectRef ∧
    StepHasLocal08 1 (.init (.scalar ⟨0x20000, 8⟩)) resUnionRaw ∧
    IsUbStep08 resUnionRef ∧
    StepHasCallerLocal08 0 (.init (.scalar ⟨0x20000, 8⟩)) resForeignRaw ∧
    IsUbStep08 resForeignRef := by
  exact ⟨rfl, trivial, rfl, trivial, rfl, trivial⟩

/-- §3.1(h) + W5: Single mixed provenance byte + plain bytes stripped (`mergeByteProvenance`,
`decodeLittleEndianBytes`, `decodeValueFromBytes`); multi-variant enum (`VariantsShape.multiple`)
rejects provenance bytes under `.strictUcg630Ub`; same-pointee `ptr -> usize` copy does NOT
retain `.ptr` inside `usize` storage (both dialects). -/
theorem neg_3_1h_mixed_prov_enum_and_ptr_to_usize_v06 :
    -- mergeByteProvenance
    V06.mergeByteProvenance (some (7, 7)) none = none ∧
    V06.mergeByteProvenance none (some (7, 7)) = none ∧
    V06.mergeByteProvenance (some (7, 7)) (some (8, 8)) = none ∧
    V06.mergeByteProvenance (some (7, 7)) (some (7, 7)) = some (7, 7) ∧
    -- 1 provenance byte + 7 plain bytes
    (let mixedBytes := ptr64Bytes_06.take 1 ++ V06.encodeLittleEndianBytes 0 7 none
     V06.decodeLittleEndianBytes mixedBytes = some (0x10, none) ∧
     V06.decodeValueFromBytes V06.defaultCodecFuel layouts64_06 tyRawPtrU8_06 mixedBytes =
       some (.scalar ⟨0x10, 8⟩)) ∧
    -- VariantsShape.multiple rejects provenance byte under strictUcg630Ub, accepts plain byte
    V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyEnum3_06
      [V06.mkPtrFragByte 1 7 7 0 1 8] .strictUcg630Ub = none ∧
    V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyEnum3_06
      [V06.mkInitByte 1] .strictUcg630Ub = some (.aggregate 1 []) ∧
    -- Same-pointee `ptr -> usize` via `evalCopySingleDirect` rejects under `.strictUcg630Ub`
    (let srcPtr : V06.ProvenancePtr := { allocId := 30, offsetBytes := 0 }
     let dstPtr : V06.ProvenancePtr := { allocId := 31, offsetBytes := 0 }
     let srcEntry : V06.BorrowEntry :=
       { tag := 30, targetLocal := 0, targetProjection := [], perm := .frozen }
     let dstEntry : V06.BorrowEntry :=
       { tag := 31, targetLocal := 1, targetProjection := [], perm := .active }
     let decls : List V06.LocalDecl := [
       { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
       { mutability := .mut, ty := tyUsize_06, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 5 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 5 }, debugName := none }
     ]
     let locals : List V06.LocalSlot := [
       .init (.ptr ptr64_06 8), .uninit,
       .init (.ptr srcPtr 8), .init (.ptr dstPtr 8)
     ]
     let mem : V06.Memory := { V06.emptyMemory with borrows := [srcEntry, dstEntry] }
     let res := V06.evalCopySingleDirect (mkState06 locals mem) (.copy ⟨2, []⟩) (.copy ⟨3, []⟩)
       decls layouts64_06 srcPtr dstPtr srcEntry dstEntry locals
     IsUbStep06 res) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

theorem neg_3_1h_mixed_prov_enum_and_ptr_to_usize_v08 :
    V08.mergeByteProvenance (some (7, 7)) none = none ∧
    V08.mergeByteProvenance none (some (7, 7)) = none ∧
    V08.mergeByteProvenance (some (7, 7)) (some (8, 8)) = none ∧
    V08.mergeByteProvenance (some (7, 7)) (some (7, 7)) = some (7, 7) ∧
    (let mixedBytes := ptr64Bytes_08.take 1 ++ V08.encodeLittleEndianBytes 0 7 none
     V08.decodeLittleEndianBytes mixedBytes = some (0x10, none) ∧
     V08.decodeValueFromBytes V08.defaultCodecFuel layouts64_08 tyRawPtrU8_08 mixedBytes =
       some (.scalar ⟨0x10, 8⟩)) ∧
    V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyEnum3_08
      [V08.mkPtrFragByte 1 7 7 0 1 8] .strictUcg630Ub = none ∧
    V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyEnum3_08
      [V08.mkInitByte 1] .strictUcg630Ub = some (.aggregate 1 []) ∧
    (let srcPtr : V08.ProvenancePtr := { allocId := 30, offsetBytes := 0 }
     let dstPtr : V08.ProvenancePtr := { allocId := 31, offsetBytes := 0 }
     let srcEntry : V08.BorrowEntry :=
       { tag := 30, targetLocal := 0, targetProjection := [], perm := .frozen }
     let dstEntry : V08.BorrowEntry :=
       { tag := 31, targetLocal := 1, targetProjection := [], perm := .active }
     let decls : List V08.LocalDecl := [
       { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
       { mutability := .mut, ty := tyUsize_08, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 5 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 5 }, debugName := none }
     ]
     let locals : List V08.LocalSlot := [
       .init (.ptr ptr64_08 8), .uninit,
       .init (.ptr srcPtr 8), .init (.ptr dstPtr 8)
     ]
     let mem : V08.Memory := { V08.emptyMemory with borrows := [srcEntry, dstEntry] }
     let res := V08.evalCopySingleDirect (mkState08 locals mem) (.copy ⟨2, []⟩) (.copy ⟨3, []⟩)
       decls layouts64_08 srcPtr dstPtr srcEntry dstEntry locals
     IsUbStep08 res) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-! ## §2. Positive Controls (Brief §3.2(a)–(d), Both Dialects + Parity) -/

/-- §3.2(a): Intact 8-byte and 4-byte pointers copied byte-by-byte in order through `[u8; 8]` /
`[u8; 4]` AND via `copy_nonoverlapping::<u8>` retain exact provenance and dereference cleanly
to the pointee value in both dialects. -/
theorem pos_3_2a_intact_bytewise_copy_and_deref_v06 :
    -- Direct 8-byte and 4-byte coherent round-trip
    V06.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_06 = some (.ptr ptr64_06 8) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 8 ptr64Bytes_06 = some (.ptr ptr64_06 8) ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 8 ptr64ZeroBytes_06 = some (.ptr ptr64Zero_06 8) ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 4 ptr32Bytes_06 = some (.ptr ptr32_06 4) ∧
    V06.decodePtrBytesNoForge true (.uint .u8) 4 ptr32Bytes_06 = some (.ptr ptr32_06 4) ∧
    V06.decodePtrBytesNoForge false (.uint .u8) 4 ptr32ZeroBytes_06 = some (.ptr ptr32Zero_06 4) ∧
    -- End-to-end `copy_nonoverlapping::<u8>` of `*const u8` -> `[u8; 8]` -> `*const u8` -> deref!
    (let targetPtr : V06.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
     let srcPtrPtr : V06.ProvenancePtr := { allocId := 2, offsetBytes := 0 }
     let bufPtr : V06.ProvenancePtr := { allocId := 3, offsetBytes := 0 }
     let dstPtrPtr : V06.ProvenancePtr := { allocId := 4, offsetBytes := 0 }
     let bTarget : V06.BorrowEntry := { tag := 1, targetLocal := 0, targetProjection := [], perm := .frozen }
     let bSrc : V06.BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen }
     let bBuf : V06.BorrowEntry := { tag := 3, targetLocal := 2, targetProjection := [], perm := .active }
     let bDst : V06.BorrowEntry := { tag := 4, targetLocal := 3, targetProjection := [], perm := .active }
     let decls : List V06.LocalDecl := [
       { mutability := .not, ty := tyU8_06, debugName := none },        -- _0: u8 = 0x5A
       { mutability := .not, ty := tyRawPtrU8_06, debugName := none },  -- _1: *const u8 = &raw const _0
       { mutability := .mut, ty := tyArr8U8_06, debugName := none },    -- _2: [u8; 8]
       { mutability := .mut, ty := tyRawPtrU8_06, debugName := none },  -- _3: *const u8 (dst)
       { mutability := .not, ty := tyRawPtrU8_06, debugName := none },  -- _4: *const u8 = &_1 as *const u8
       { mutability := .not, ty := tyMutPtrU8_06, debugName := none },  -- _5: *mut u8 = &_2 as *mut u8
       { mutability := .not, ty := tyMutPtrU8_06, debugName := none }   -- _6: *mut u8 = &_3 as *mut u8
     ]
     let locals0 : List V06.LocalSlot := [
       .init (.scalar ⟨0x5A, 1⟩),
       .init (.ptr targetPtr 8),
       .init (.aggregate 0 (List.replicate 8 (.scalar ⟨0, 1⟩))),
       .uninit,
       .init (.ptr srcPtrPtr 8),
       .init (.ptr bufPtr 8),
       .init (.ptr dstPtrPtr 8)
     ]
     let mem0 : V06.Memory := { V06.emptyMemory with borrows := [bTarget, bSrc, bBuf, bDst] }
     let count8 : V06.Operand := .constant ⟨tyUsize_06, .scalar (.int ⟨8, 8⟩)⟩
     let stmt1 : V06.Statement :=
       ⟨.intrinsic (.copyNonOverlapping (.copy ⟨4, []⟩) (.copy ⟨5, []⟩) count8), ""⟩
     let stmt2 : V06.Statement :=
       ⟨.intrinsic (.copyNonOverlapping (.copy ⟨5, []⟩) (.copy ⟨6, []⟩) count8), ""⟩
     match V06.evalStmt (mkState06 locals0 mem0) stmt1 decls layouts64_06 with
     | .tau (.running s1) =>
       match V06.evalStmt s1 stmt2 decls layouts64_06 with
       | .tau (.running s2) =>
         -- Read `_3` as `*const u8` (materializes `.ptr targetPtr 8`) and dereference `*_3` -> `0x5A`!
         V06.evalOperand s2.frame.locals (.copy ⟨3, []⟩) s2.memory.borrows s2.memory.globals
           layouts64_06 s2.memory.callerLocals decls s2.memory.callStack =
           .ok (.ptr targetPtr 8) s2.frame.locals ∧
         V06.evalOperand s2.frame.locals (.copy ⟨3, [.deref]⟩) s2.memory.borrows s2.memory.globals
           layouts64_06 s2.memory.callerLocals decls s2.memory.callStack =
           .ok (.scalar ⟨0x5A, 1⟩) s2.frame.locals
       | _ => False
     | _ => False) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

theorem pos_3_2a_intact_bytewise_copy_and_deref_v08 :
    V08.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_08 = some (.ptr ptr64_08 8) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 8 ptr64Bytes_08 = some (.ptr ptr64_08 8) ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 8 ptr64ZeroBytes_08 = some (.ptr ptr64Zero_08 8) ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 4 ptr32Bytes_08 = some (.ptr ptr32_08 4) ∧
    V08.decodePtrBytesNoForge true (.uint .u8) 4 ptr32Bytes_08 = some (.ptr ptr32_08 4) ∧
    V08.decodePtrBytesNoForge false (.uint .u8) 4 ptr32ZeroBytes_08 = some (.ptr ptr32Zero_08 4) ∧
    (let targetPtr : V08.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
     let srcPtrPtr : V08.ProvenancePtr := { allocId := 2, offsetBytes := 0 }
     let bufPtr : V08.ProvenancePtr := { allocId := 3, offsetBytes := 0 }
     let dstPtrPtr : V08.ProvenancePtr := { allocId := 4, offsetBytes := 0 }
     let bTarget : V08.BorrowEntry := { tag := 1, targetLocal := 0, targetProjection := [], perm := .frozen }
     let bSrc : V08.BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .frozen }
     let bBuf : V08.BorrowEntry := { tag := 3, targetLocal := 2, targetProjection := [], perm := .active }
     let bDst : V08.BorrowEntry := { tag := 4, targetLocal := 3, targetProjection := [], perm := .active }
     let decls : List V08.LocalDecl := [
       { mutability := .not, ty := tyU8_08, debugName := none },
       { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
       { mutability := .mut, ty := tyArr8U8_08, debugName := none },
       { mutability := .mut, ty := tyRawPtrU8_08, debugName := none },
       { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
       { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
       { mutability := .not, ty := tyMutPtrU8_08, debugName := none }
     ]
     let locals0 : List V08.LocalSlot := [
       .init (.scalar ⟨0x5A, 1⟩),
       .init (.ptr targetPtr 8),
       .init (.aggregate 0 (List.replicate 8 (.scalar ⟨0, 1⟩))),
       .uninit,
       .init (.ptr srcPtrPtr 8),
       .init (.ptr bufPtr 8),
       .init (.ptr dstPtrPtr 8)
     ]
     let mem0 : V08.Memory := { V08.emptyMemory with borrows := [bTarget, bSrc, bBuf, bDst] }
     let count8 : V08.Operand := .constant ⟨tyUsize_08, .scalar (.int ⟨8, 8⟩)⟩
     let stmt1 : V08.Statement :=
       ⟨.intrinsic (.copyNonOverlapping (.copy ⟨4, []⟩) (.copy ⟨5, []⟩) count8), ""⟩
     let stmt2 : V08.Statement :=
       ⟨.intrinsic (.copyNonOverlapping (.copy ⟨5, []⟩) (.copy ⟨6, []⟩) count8), ""⟩
     match V08.evalStmt (mkState08 locals0 mem0) stmt1 decls layouts64_08 with
     | .tau (.running s1) =>
       match V08.evalStmt s1 stmt2 decls layouts64_08 with
       | .tau (.running s2) =>
         V08.evalOperand s2.frame.locals (.copy ⟨3, []⟩) s2.memory.borrows s2.memory.globals
           layouts64_08 s2.memory.callerLocals decls s2.memory.callStack =
           .ok (.ptr targetPtr 8) s2.frame.locals ∧
         V08.evalOperand s2.frame.locals (.copy ⟨3, [.deref]⟩) s2.memory.borrows s2.memory.globals
           layouts64_08 s2.memory.callerLocals decls s2.memory.callStack =
           .ok (.scalar ⟨0x5A, 1⟩) s2.frame.locals
       | _ => False
     | _ => False) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.2(b): Lossless union raw-byte carrier (`encodeRawAbstractByteVals` /
`decodeRawAbstractByteVals?` / `overlayRawAbstractByteVals`) preserves FULL `PtrByteFrag`
(including `tag ≠ allocId`!) AND `MaybeUninit<*const u8>` union round-trips cleanly back to `.ptr`
in both dialects. -/
theorem pos_3_2b_union_raw_byte_carrier_and_maybe_uninit_ptr_v06_v08 :
    -- Explicit `tag ≠ allocId` (`allocId := 7, tag := 99`) round-trip through raw-byte carrier
    (let bs06 := V06.encodeLittleEndianBytes 0x10 8 (some (7, 99))
     let vals06 := V06.encodeRawAbstractByteVals bs06
     let uninitBuf06 := List.replicate 8 (.uninit : V06.AbstractByte)
     let muVal06 : V06.Value := .aggregate 0 [.unit, .unit, .aggregate 0 vals06]
     let decls06 : List V06.LocalDecl := [{ mutability := .not, ty := tyMaybeUninitPtr_06, debugName := none }]
     V06.decodeRawAbstractByteVals? vals06 = some bs06 ∧
     V06.overlayRawAbstractByteVals vals06 uninitBuf06 = some bs06 ∧
     V06.abstractBytesCoherentPtrProv? bs06 =
       some { allocId := 7, tag := 99, byteIdx := 0, origOffset := 0x10, ptrBytes := 8 } ∧
     V06.evalOperand [.init muVal06] (.copy ⟨0, [.field 0 tyRawPtrU8_06]⟩) [] [] layouts64_06 [] decls06 =
       .ok (.ptr ptr64_06 8) [.init muVal06]) ∧
    (let bs08 := V08.encodeLittleEndianBytes 0x10 8 (some (7, 99))
     let vals08 := V08.encodeRawAbstractByteVals bs08
     let uninitBuf08 := List.replicate 8 (.uninit : V08.AbstractByte)
     let muVal08 : V08.Value := .aggregate 0 [.unit, .unit, .aggregate 0 vals08]
     let decls08 : List V08.LocalDecl := [{ mutability := .not, ty := tyMaybeUninitPtr_08, debugName := none }]
     V08.decodeRawAbstractByteVals? vals08 = some bs08 ∧
     V08.overlayRawAbstractByteVals vals08 uninitBuf08 = some bs08 ∧
     V08.abstractBytesCoherentPtrProv? bs08 =
       some { allocId := 7, tag := 99, byteIdx := 0, origOffset := 0x10, ptrBytes := 8 } ∧
     V08.evalOperand [.init muVal08] (.copy ⟨0, [.field 0 tyRawPtrU8_08]⟩) [] [] layouts64_08 [] decls08 =
       .ok (.ptr ptr64_08 8) [.init muVal08]) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.2(c) + W4: Aligned global allocation relocation reads (64-bit offsets `0` and `8`; 32-bit
offset `0`) retain exact coherent provenance in both dialects. -/
theorem pos_3_2c_aligned_global_reloc_reads_v06_v08 :
    (match V06.globalAllocSliceToAbstractBytes adjRelocAlloc64_06 0 8 8,
           V06.globalAllocSliceToAbstractBytes adjRelocAlloc64_06 8 8 8,
           V06.globalAllocSliceToAbstractBytes relocAlloc32_06 0 4 4 with
     | some bs0, some bs8, some bs32 =>
       V06.decodePtrBytesNoForge true (.uint .u8) 8 bs0 = some (.ptr ptr64_06 8) ∧
       V06.decodePtrBytesNoForge true (.uint .u8) 8 bs8 = some (.ptr ptr64_06 8) ∧
       V06.decodePtrBytesNoForge true (.uint .u8) 4 bs32 = some (.ptr ptr32_06 4)
     | _, _, _ => False) ∧
    (match V08.globalAllocSliceToAbstractBytes adjRelocAlloc64_08 0 8 8,
           V08.globalAllocSliceToAbstractBytes adjRelocAlloc64_08 8 8 8,
           V08.globalAllocSliceToAbstractBytes relocAlloc32_08 0 4 4 with
     | some bs0, some bs8, some bs32 =>
       V08.decodePtrBytesNoForge true (.uint .u8) 8 bs0 = some (.ptr ptr64_08 8) ∧
       V08.decodePtrBytesNoForge true (.uint .u8) 8 bs8 = some (.ptr ptr64_08 8) ∧
       V08.decodePtrBytesNoForge true (.uint .u8) 4 bs32 = some (.ptr ptr32_08 4)
     | _, _, _ => False) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.2(d) + W3: Intact `&dyn Trait` with `.ptr` vtable half round-trips cleanly through
`encodeValueToBytes` -> `decodeTypedValueFromBytes` / `decodePtrBytesNoForge` (both 64-bit
and 32-bit, across both dialects). -/
theorem pos_3_2d_intact_dyn_trait_roundtrip_v06_v08 :
    let dynVal64_06 : V06.Value := .aggregate 0 [.ptr ptr64_06 8, .ptr vtPtr64_06 8]
    let dynVal32_06 : V06.Value := .aggregate 0 [.ptr ptr32_06 4, .ptr vtPtr32_06 4]
    let dynVal64_08 : V08.Value := .aggregate 0 [.ptr ptr64_08 8, .ptr vtPtr64_08 8]
    let dynVal32_08 : V08.Value := .aggregate 0 [.ptr ptr32_08 4, .ptr vtPtr32_08 4]
    (match V06.encodeValueToBytes V06.defaultCodecFuel layouts64_06 tyRefDyn_06 dynVal64_06,
           V06.encodeValueToBytes V06.defaultCodecFuel layouts32_06 tyRefDyn_06 dynVal32_06 with
     | some bs64, some bs32 =>
       bs64.length = 16 ∧
       V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyRefDyn_06 bs64 =
         some dynVal64_06 ∧
       bs32.length = 8 ∧
       V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts32_06 tyRefDyn_06 bs32 =
         some dynVal32_06
     | _, _ => False) ∧
    (match V08.encodeValueToBytes V08.defaultCodecFuel layouts64_08 tyRefDyn_08 dynVal64_08,
           V08.encodeValueToBytes V08.defaultCodecFuel layouts32_08 tyRefDyn_08 dynVal32_08 with
     | some bs64, some bs32 =>
       bs64.length = 16 ∧
       V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyRefDyn_08 bs64 =
         some dynVal64_08 ∧
       bs32.length = 8 ∧
       V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts32_08 tyRefDyn_08 bs32 =
         some dynVal32_08
     | _, _ => False) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-! ## §3. `Kani#5205` / `#5196` Read-Time Untyped-Byte Validity Controls (Brief §3.3(a)–(d)) -/

/-- §3.3(a) & (b): Writing/copying `2u8` into `[u8; 1]`, `MaybeUninit<bool>`,
`MaybeUninit<Unaligned<bool>>`, `bool`, and `Unaligned<bool>` via `writeBytesAction` and untyped
copies (`evalCopySingleDirect`, `evalForeignFrameCopySingleDirect`) succeeds WITHOUT premature
write-time UB; subsequently reading that `2u8` as typed `bool` or `Unaligned<bool>` (`decodeTypedValueFromBytes`,
`Operand.copy`, `assume_init`/union field projection, or struct field projection `u.0`) faults
with `.ub` in `V2026_06_01`. -/
theorem kani5205_3_3ab_bool_and_unaligned_bool_v06 :
    -- 1. writeBytesAction writing `2u8` succeeds on bool, MaybeUninit<bool>, [u8; 1], Unaligned<bool>
    let bBool : V06.BorrowEntry := { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
    let bMuBool : V06.BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .active }
    let bArr1 : V06.BorrowEntry := { tag := 3, targetLocal := 2, targetProjection := [], perm := .active }
    let bUnal : V06.BorrowEntry := { tag := 4, targetLocal := 3, targetProjection := [], perm := .active }
    let bMuUnal : V06.BorrowEntry := { tag := 5, targetLocal := 4, targetProjection := [], perm := .active }
    let tyArr1 : V06.Ty := { kind := .array (.uint .u8) 1, layoutIdx := 0 }
    let decls : List V06.LocalDecl := [
      { mutability := .mut, ty := tyBool_06, debugName := none },
      { mutability := .mut, ty := tyMaybeUninitBool_06, debugName := none },
      { mutability := .mut, ty := tyArr1, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_06, debugName := none },
      { mutability := .mut, ty := tyMaybeUninitUnalignedBool_06, debugName := none }
    ]
    let bs := [bBool, bMuBool, bArr1, bUnal, bMuUnal]
    let wbTarget (tyArg : V06.RigidTy) : V06.ResolvedCallTarget :=
      { defPath := "core::ptr::write_bytes", typeArgs := [tyArg] }
    let wbCall (tag : Nat) (tyArg : V06.RigidTy) : V06.WriteBytesAction :=
      V06.writeBytesAction bs 0 (wbTarget tyArg) decls layouts64_06 []
        [.ptr { allocId := tag, offsetBytes := 0 } 8, .scalar ⟨2, 1⟩, .scalar ⟨1, 8⟩]
    let actBool := wbCall 1 .bool
    let actMuBool := wbCall 2 tyMaybeUninitBool_06.kind
    let actArr1 := wbCall 3 (.uint .u8)
    let actUnal := wbCall 4 tyUnalignedBool_06.kind
    let actMuUnal := wbCall 5 tyMaybeUninitUnalignedBool_06.kind
    -- 2. Foreign-frame untyped copy of `2u8` into caller's `bool` and `Unaligned<bool>` succeeds,
    --    and reading those caller locals at typed `bool` / `Unaligned<bool>` / `u.0` faults `.ub`!
    let callerDecls : List V06.LocalDecl := [
      { mutability := .mut, ty := tyBool_06, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_06, debugName := none }
    ]
    let savedCaller : V06.SavedCallerFrame :=
      { callerBody := emptyBody06 callerDecls layouts64_06,
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
        destination := ⟨0, []⟩ }
    let calleeDecls : List V06.LocalDecl := [
      { mutability := .not, ty := tyU8_06, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none }
    ]
    let srcE : V06.BorrowEntry :=
      { tag := 60, targetLocal := 0, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let dstBoolE : V06.BorrowEntry :=
      { tag := 61, targetLocal := 0, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dstUnalE : V06.BorrowEntry :=
      { tag := 62, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let calleeLocals : List V06.LocalSlot := [
      .init (.scalar ⟨2, 1⟩),
      .init (.ptr { allocId := 60, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 61, offsetBytes := 0 } 8)
    ]
    let memF : V06.Memory :=
      { V06.emptyMemory with borrows := [srcE, dstBoolE, dstUnalE], callStack := [savedCaller] }
    let resForeignBool := V06.evalForeignFrameCopySingleDirect (mkState06 calleeLocals memF)
      (.copy ⟨1, []⟩) (.copy ⟨2, []⟩) calleeDecls layouts64_06
      { allocId := 60, offsetBytes := 0 } { allocId := 61, offsetBytes := 0 }
      srcE dstBoolE 1 calleeLocals
    let resForeignUnal := V06.evalForeignFrameCopySingleDirect (mkState06 calleeLocals memF)
      (.copy ⟨1, []⟩) (.copy ⟨2, []⟩) calleeDecls layouts64_06
      { allocId := 60, offsetBytes := 0 } { allocId := 62, offsetBytes := 0 }
      srcE dstUnalE 1 calleeLocals
    -- Assertions:
    -- (a) All write_bytes actions succeed with `.store` (no premature write-time UB)
    (match actBool, actMuBool, actArr1, actUnal, actMuUnal with
     | .store ⟨0, []⟩ 0 1 (.scalar ⟨2, 1⟩),
       .store ⟨1, []⟩ 1 2 muBoolVal,
       .store ⟨2, []⟩ 2 3 (.aggregate 0 [.scalar ⟨2, 1⟩]),
       .store ⟨3, []⟩ 3 4 unalVal,
       .store ⟨4, []⟩ 4 5 muUnalVal =>
       -- Reading the union container itself succeeds (unions defer validity!)
       V06.validateValueForTy? layouts64_06 (some tyMaybeUninitBool_06) muBoolVal = true ∧
       V06.validateValueForTy? layouts64_06 (some tyMaybeUninitUnalignedBool_06) muUnalVal = true ∧
       -- (b) Typed reads of `2u8` as `bool` or `Unaligned<bool>` ALL fault `.ub` / `.none`!
       V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyBool_06
         [V06.mkInitByte 2] = none ∧
       V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyUnalignedBool_06
         [V06.mkInitByte 2] = none ∧
       V06.evalOperand [.init (.scalar ⟨2, 1⟩)] (.copy ⟨0, []⟩) [] [] layouts64_06 [] decls = .ub ∧
       V06.evalOperand [.uninit, .uninit, .uninit, .init unalVal] (.copy ⟨3, []⟩)
         [] [] layouts64_06 [] decls = .ub ∧
       V06.evalOperand [.uninit, .uninit, .uninit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]
         (.copy ⟨3, [.field 0 tyBool_06]⟩) [] [] layouts64_06 [] decls = .ub ∧
       V06.evalOperand [.uninit, .init muBoolVal] (.copy ⟨1, [.field 0 tyBool_06]⟩)
         [] [] layouts64_06 [] decls = .ub ∧
       V06.evalOperand [.uninit, .uninit, .uninit, .uninit, .init muUnalVal]
         (.copy ⟨4, [.field 0 tyUnalignedBool_06]⟩) [] [] layouts64_06 [] decls = .ub
     | _, _, _, _, _ => False) ∧
    -- Foreign untyped copy succeeds without write-time UB, then typed caller read faults `.ub`!
    (match resForeignBool, resForeignUnal with
     | .tau (.running sFB), .tau (.running sFU) =>
       match sFB.memory.callStack, sFU.memory.callStack with
       | cfB :: _, cfU :: _ =>
         V06.evalOperand cfB.frame.locals (.copy ⟨0, []⟩) [] [] layouts64_06 [] callerDecls = .ub ∧
         V06.evalOperand cfU.frame.locals (.copy ⟨1, []⟩) [] [] layouts64_06 [] callerDecls = .ub
       | _, _ => False
     | _, _ => False) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

theorem kani5205_3_3ab_bool_and_unaligned_bool_v08 :
    let bBool : V08.BorrowEntry := { tag := 1, targetLocal := 0, targetProjection := [], perm := .active }
    let bMuBool : V08.BorrowEntry := { tag := 2, targetLocal := 1, targetProjection := [], perm := .active }
    let bArr1 : V08.BorrowEntry := { tag := 3, targetLocal := 2, targetProjection := [], perm := .active }
    let bUnal : V08.BorrowEntry := { tag := 4, targetLocal := 3, targetProjection := [], perm := .active }
    let bMuUnal : V08.BorrowEntry := { tag := 5, targetLocal := 4, targetProjection := [], perm := .active }
    let tyArr1 : V08.Ty := { kind := .array (.uint .u8) 1, layoutIdx := 0 }
    let decls : List V08.LocalDecl := [
      { mutability := .mut, ty := tyBool_08, debugName := none },
      { mutability := .mut, ty := tyMaybeUninitBool_08, debugName := none },
      { mutability := .mut, ty := tyArr1, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_08, debugName := none },
      { mutability := .mut, ty := tyMaybeUninitUnalignedBool_08, debugName := none }
    ]
    let bs := [bBool, bMuBool, bArr1, bUnal, bMuUnal]
    let wbTarget (tyArg : V08.RigidTy) : V08.ResolvedCallTarget :=
      { defPath := "core::ptr::write_bytes", typeArgs := [tyArg] }
    let wbCall (tag : Nat) (tyArg : V08.RigidTy) : V08.WriteBytesAction :=
      V08.writeBytesAction bs 0 (wbTarget tyArg) decls layouts64_08 []
        [.ptr { allocId := tag, offsetBytes := 0 } 8, .scalar ⟨2, 1⟩, .scalar ⟨1, 8⟩]
    let actBool := wbCall 1 .bool
    let actMuBool := wbCall 2 tyMaybeUninitBool_08.kind
    let actArr1 := wbCall 3 (.uint .u8)
    let actUnal := wbCall 4 tyUnalignedBool_08.kind
    let actMuUnal := wbCall 5 tyMaybeUninitUnalignedBool_08.kind
    let callerDecls : List V08.LocalDecl := [
      { mutability := .mut, ty := tyBool_08, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_08, debugName := none }
    ]
    let savedCaller : V08.SavedCallerFrame :=
      { callerBody := emptyBody08 callerDecls layouts64_08,
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit] },
        destination := ⟨0, []⟩ }
    let calleeDecls : List V08.LocalDecl := [
      { mutability := .not, ty := tyU8_08, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none }
    ]
    let srcE : V08.BorrowEntry :=
      { tag := 60, targetLocal := 0, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let dstBoolE : V08.BorrowEntry :=
      { tag := 61, targetLocal := 0, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dstUnalE : V08.BorrowEntry :=
      { tag := 62, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let calleeLocals : List V08.LocalSlot := [
      .init (.scalar ⟨2, 1⟩),
      .init (.ptr { allocId := 60, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 61, offsetBytes := 0 } 8)
    ]
    let memF : V08.Memory :=
      { V08.emptyMemory with borrows := [srcE, dstBoolE, dstUnalE], callStack := [savedCaller] }
    let resForeignBool := V08.evalForeignFrameCopySingleDirect (mkState08 calleeLocals memF)
      (.copy ⟨1, []⟩) (.copy ⟨2, []⟩) calleeDecls layouts64_08
      { allocId := 60, offsetBytes := 0 } { allocId := 61, offsetBytes := 0 }
      srcE dstBoolE 1 calleeLocals
    let resForeignUnal := V08.evalForeignFrameCopySingleDirect (mkState08 calleeLocals memF)
      (.copy ⟨1, []⟩) (.copy ⟨2, []⟩) calleeDecls layouts64_08
      { allocId := 60, offsetBytes := 0 } { allocId := 62, offsetBytes := 0 }
      srcE dstUnalE 1 calleeLocals
    (match actBool, actMuBool, actArr1, actUnal, actMuUnal with
     | .store ⟨0, []⟩ 0 1 (.scalar ⟨2, 1⟩),
       .store ⟨1, []⟩ 1 2 muBoolVal,
       .store ⟨2, []⟩ 2 3 (.aggregate 0 [.scalar ⟨2, 1⟩]),
       .store ⟨3, []⟩ 3 4 unalVal,
       .store ⟨4, []⟩ 4 5 muUnalVal =>
       V08.validateValueForTy? layouts64_08 (some tyMaybeUninitBool_08) muBoolVal = true ∧
       V08.validateValueForTy? layouts64_08 (some tyMaybeUninitUnalignedBool_08) muUnalVal = true ∧
       V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyBool_08
         [V08.mkInitByte 2] = none ∧
       V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyUnalignedBool_08
         [V08.mkInitByte 2] = none ∧
       V08.evalOperand [.init (.scalar ⟨2, 1⟩)] (.copy ⟨0, []⟩) [] [] layouts64_08 [] decls = .ub ∧
       V08.evalOperand [.uninit, .uninit, .uninit, .init unalVal] (.copy ⟨3, []⟩)
         [] [] layouts64_08 [] decls = .ub ∧
       V08.evalOperand [.uninit, .uninit, .uninit, .init (.aggregate 0 [.scalar ⟨2, 1⟩])]
         (.copy ⟨3, [.field 0 tyBool_08]⟩) [] [] layouts64_08 [] decls = .ub ∧
       V08.evalOperand [.uninit, .init muBoolVal] (.copy ⟨1, [.field 0 tyBool_08]⟩)
         [] [] layouts64_08 [] decls = .ub ∧
       V08.evalOperand [.uninit, .uninit, .uninit, .uninit, .init muUnalVal]
         (.copy ⟨4, [.field 0 tyUnalignedBool_08]⟩) [] [] layouts64_08 [] decls = .ub
     | _, _, _, _, _ => False) ∧
    (match resForeignBool, resForeignUnal with
     | .tau (.running sFB), .tau (.running sFU) =>
       match sFB.memory.callStack, sFU.memory.callStack with
       | cfB :: _, cfU :: _ =>
         V08.evalOperand cfB.frame.locals (.copy ⟨0, []⟩) [] [] layouts64_08 [] callerDecls = .ub ∧
         V08.evalOperand cfU.frame.locals (.copy ⟨1, []⟩) [] [] layouts64_08 [] callerDecls = .ub
       | _, _ => False
     | _, _ => False) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.3(c): Valid `1u8` in `Unaligned<bool>` at unaligned byte offset `1` of `[u8; 4]` reads
cleanly (both via dereference at offset `1` and via `decodeTypedValueFromBytes`) in both dialects. -/
theorem kani5205_3_3c_valid_unaligned_bool_at_offset1_v06_v08 :
    (let decls06 : List V06.LocalDecl := [
       { mutability := .not, ty := tyArr4U8_06, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not tyUnalignedBool_06.kind, layoutIdx := 5 },
         debugName := none },
       { mutability := .not, ty := tyUnalignedBool_06, debugName := none }
     ]
     let arrVal06 : V06.Value :=
       .aggregate 0 [.scalar ⟨0xAA, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨0xBB, 1⟩, .scalar ⟨0xCC, 1⟩]
     let bArr06 : V06.BorrowEntry :=
       { tag := 70, targetLocal := 0, targetProjection := [], perm := .frozen }
     let locals06 : List V06.LocalSlot := [
       .init arrVal06,
       .init (.ptr { allocId := 70, offsetBytes := 1 } 8),
       .uninit
     ]
     V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyUnalignedBool_06
       [V06.mkInitByte 1] = some (.aggregate 0 [.scalar ⟨1, 1⟩]) ∧
     V06.evalOperand locals06 (.copy ⟨1, [.deref]⟩) [bArr06] [] layouts64_06 [] decls06 =
       .ok (.aggregate 0 [.scalar ⟨1, 1⟩]) locals06) ∧
    (let decls08 : List V08.LocalDecl := [
       { mutability := .not, ty := tyArr4U8_08, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not tyUnalignedBool_08.kind, layoutIdx := 5 },
         debugName := none },
       { mutability := .not, ty := tyUnalignedBool_08, debugName := none }
     ]
     let arrVal08 : V08.Value :=
       .aggregate 0 [.scalar ⟨0xAA, 1⟩, .scalar ⟨1, 1⟩, .scalar ⟨0xBB, 1⟩, .scalar ⟨0xCC, 1⟩]
     let bArr08 : V08.BorrowEntry :=
       { tag := 70, targetLocal := 0, targetProjection := [], perm := .frozen }
     let locals08 : List V08.LocalSlot := [
       .init arrVal08,
       .init (.ptr { allocId := 70, offsetBytes := 1 } 8),
       .uninit
     ]
     V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyUnalignedBool_08
       [V08.mkInitByte 1] = some (.aggregate 0 [.scalar ⟨1, 1⟩]) ∧
     V08.evalOperand locals08 (.copy ⟨1, [.deref]⟩) [bArr08] [] layouts64_08 [] decls08 =
       .ok (.aggregate 0 [.scalar ⟨1, 1⟩]) locals08) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- §3.3(d): Surrogate `char` `0xD800` succeeds in `[u8; 4]`, `u32`, `MaybeUninit<char>`, and
`write_bytes` (writing `0xD8` bytes), and faults with `.ub` / `.none` on typed `char` read in
both dialects. -/
theorem kani5205_3_3d_surrogate_char_v06_v08 :
    -- V2026_06_01
    (let surrBytes06 := V06.encodeLittleEndianBytes 0xD800 4 none
     let tyU32_06 : V06.Ty := { kind := .uint .u32, layoutIdx := 0 }
     let muCharVal06 : V06.Value :=
       .aggregate 0 [.unit, .unit, .aggregate 0 (V06.encodeRawAbstractByteVals surrBytes06)]
     let decls06 : List V06.LocalDecl := [
       { mutability := .mut, ty := tyChar_06, debugName := none },
       { mutability := .mut, ty := tyMaybeUninitChar_06, debugName := none }
     ]
     let bChar06 : V06.BorrowEntry := { tag := 80, targetLocal := 0, targetProjection := [], perm := .active }
     let bMuChar06 : V06.BorrowEntry := { tag := 81, targetLocal := 1, targetProjection := [], perm := .active }
     let wbChar06 := V06.writeBytesAction [bChar06, bMuChar06] 0
       { defPath := "core::ptr::write_bytes", typeArgs := [.char] } decls06 layouts64_06 []
       [.ptr { allocId := 80, offsetBytes := 0 } 8, .scalar ⟨0xD8, 1⟩, .scalar ⟨1, 8⟩]
     V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyArr4U8_06 surrBytes06 =
       some (.aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0xD8, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩]) ∧
     V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyU32_06 surrBytes06 =
       some (.scalar ⟨0xD800, 4⟩) ∧
     V06.validateValueForTy? layouts64_06 (some tyMaybeUninitChar_06) muCharVal06 = true ∧
     (match wbChar06 with | .store ⟨0, []⟩ 0 80 (.scalar ⟨0xD8D8D8D8, 4⟩) => True | _ => False) ∧
     V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyChar_06 surrBytes06 = none ∧
     V06.evalOperand [.init (.scalar ⟨0xD800, 4⟩)] (.copy ⟨0, []⟩) [] [] layouts64_06 [] decls06 = .ub ∧
     V06.evalOperand [.uninit, .init muCharVal06] (.copy ⟨1, [.field 0 tyChar_06]⟩)
       [] [] layouts64_06 [] decls06 = .ub) ∧
    -- V2026_08_01
    (let surrBytes08 := V08.encodeLittleEndianBytes 0xD800 4 none
     let tyU32_08 : V08.Ty := { kind := .uint .u32, layoutIdx := 0 }
     let muCharVal08 : V08.Value :=
       .aggregate 0 [.unit, .unit, .aggregate 0 (V08.encodeRawAbstractByteVals surrBytes08)]
     let decls08 : List V08.LocalDecl := [
       { mutability := .mut, ty := tyChar_08, debugName := none },
       { mutability := .mut, ty := tyMaybeUninitChar_08, debugName := none }
     ]
     let bChar08 : V08.BorrowEntry := { tag := 80, targetLocal := 0, targetProjection := [], perm := .active }
     let bMuChar08 : V08.BorrowEntry := { tag := 81, targetLocal := 1, targetProjection := [], perm := .active }
     let wbChar08 := V08.writeBytesAction [bChar08, bMuChar08] 0
       { defPath := "core::ptr::write_bytes", typeArgs := [.char] } decls08 layouts64_08 []
       [.ptr { allocId := 80, offsetBytes := 0 } 8, .scalar ⟨0xD8, 1⟩, .scalar ⟨1, 8⟩]
     V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyArr4U8_08 surrBytes08 =
       some (.aggregate 0 [.scalar ⟨0, 1⟩, .scalar ⟨0xD8, 1⟩, .scalar ⟨0, 1⟩, .scalar ⟨0, 1⟩]) ∧
     V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyU32_08 surrBytes08 =
       some (.scalar ⟨0xD800, 4⟩) ∧
     V08.validateValueForTy? layouts64_08 (some tyMaybeUninitChar_08) muCharVal08 = true ∧
     (match wbChar08 with | .store ⟨0, []⟩ 0 80 (.scalar ⟨0xD8D8D8D8, 4⟩) => True | _ => False) ∧
     V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyChar_08 surrBytes08 = none ∧
     V08.evalOperand [.init (.scalar ⟨0xD800, 4⟩)] (.copy ⟨0, []⟩) [] [] layouts64_08 [] decls08 = .ub ∧
     V08.evalOperand [.uninit, .init muCharVal08] (.copy ⟨1, [.field 0 tyChar_08]⟩)
       [] [] layouts64_08 [] decls08 = .ub) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-! ## §4. Explicit Lockstep Dialect Parity (`V2026_06_01 == V2026_08_01`) -/

inductive ValSummary : Type where
  | none : ValSummary
  | scalar (bits sizeBytes : Nat) : ValSummary
  | ptr (allocId offsetBytes sizeBytes : Nat) : ValSummary
  | agg (variantIdx : Nat) (fields : List ValSummary) : ValSummary
  | unit : ValSummary
  | uninit : ValSummary

mutual
def valSummaryVal06 : Trusted.Rustc.V2026_06_01.MirSemantics.Value → ValSummary
  | .scalar sc => .scalar sc.bits sc.sizeBytes
  | .ptr p sz => .ptr p.allocId p.offsetBytes sz
  | .aggregate v fs => .agg v (valSummaryList06 fs)
  | .unit => .unit
  | .uninit => .uninit

def valSummaryList06 : List Trusted.Rustc.V2026_06_01.MirSemantics.Value → List ValSummary
  | [] => []
  | x :: xs => valSummaryVal06 x :: valSummaryList06 xs
end

def valSummary06 : Option Trusted.Rustc.V2026_06_01.MirSemantics.Value → ValSummary
  | none => .none
  | some v => valSummaryVal06 v

mutual
def valSummaryVal08 : Trusted.Rustc.V2026_08_01.MirSemantics.Value → ValSummary
  | .scalar sc => .scalar sc.bits sc.sizeBytes
  | .ptr p sz => .ptr p.allocId p.offsetBytes sz
  | .aggregate v fs => .agg v (valSummaryList08 fs)
  | .unit => .unit

def valSummaryList08 : List Trusted.Rustc.V2026_08_01.MirSemantics.Value → List ValSummary
  | [] => []
  | x :: xs => valSummaryVal08 x :: valSummaryList08 xs
end

def valSummary08 : Option Trusted.Rustc.V2026_08_01.MirSemantics.Value → ValSummary
  | none => .none
  | some v => valSummaryVal08 v

/-- Lockstep parity vector comparing `V2026_06_01` and `V2026_08_01` across all core pointer-byte
coherence, wide-pointer, global-relocation, no-forge, and `Kani#5205` read-validity scenarios. -/
theorem lockstep_v06_v08_parity_matrix :
    let v06Results : List ValSummary := [
      valSummary06 (V06.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_06),
      valSummary06 (V06.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_06.reverse),
      valSummary06 (V06.decodePtrBytesNoForge true (.uint .u8) 8 ptr64ZeroBytes_06.reverse),
      valSummary06 (V06.decodePtrBytesNoForge false (.uint .u8) 8 (swap01_06 ptr64Bytes_06)),
      valSummary06 (V06.decodePtrBytesNoForge false (.uint .u8) 8 (dupHead_06 8 ptr64Bytes_06)),
      valSummary06 (V06.decodePtrBytesNoForge false (.uint .u8) 8
        (ptr64ZeroBytes_06.take 1 ++ ptr64Plus256Bytes_06.drop 1)),
      valSummary06 (V06.decodePtrBytesNoForge true (.dynamic "T") 8
        (ptr64Bytes_06 ++ V06.encodeLittleEndianBytes 0x80 8 none)),
      valSummary06 (V06.decodePtrBytesNoForge true (.dynamic "T") 8
        (ptr64Bytes_06 ++ vtPtr64Bytes_06)),
      valSummary06 (V06.decodePtrBytesNoForge false (.uint .u8) 4 ptr32Bytes_06),
      valSummary06 (V06.decodePtrBytesNoForge true (.uint .u8) 4 ptr32ZeroBytes_06.reverse),
      valSummary06 (V06.evalConstValue (.indirect 52 0) tyRawPtrU8_06 [plainIntAlloc64_06] layouts64_06),
      valSummary06 (V06.evalConstValue (.slice (.int ⟨0x20000, 8⟩) 4) tyRefSliceU8_06 [] layouts64_06),
      valSummary06 (V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyBool_06
        [V06.mkInitByte 2]),
      valSummary06 (V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyUnalignedBool_06
        [V06.mkInitByte 2]),
      valSummary06 (V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyUnalignedBool_06
        [V06.mkInitByte 1]),
      valSummary06 (V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyChar_06
        (V06.encodeLittleEndianBytes 0xD800 4 none)),
      valSummary06 (V06.decodeTypedValueFromBytes V06.defaultCodecFuel layouts64_06 tyEnum3_06
        [V06.mkPtrFragByte 1 7 7 0 1 8] .strictUcg630Ub)
    ]
    let v08Results : List ValSummary := [
      valSummary08 (V08.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_08),
      valSummary08 (V08.decodePtrBytesNoForge false (.uint .u8) 8 ptr64Bytes_08.reverse),
      valSummary08 (V08.decodePtrBytesNoForge true (.uint .u8) 8 ptr64ZeroBytes_08.reverse),
      valSummary08 (V08.decodePtrBytesNoForge false (.uint .u8) 8 (swap01_08 ptr64Bytes_08)),
      valSummary08 (V08.decodePtrBytesNoForge false (.uint .u8) 8 (dupHead_08 8 ptr64Bytes_08)),
      valSummary08 (V08.decodePtrBytesNoForge false (.uint .u8) 8
        (ptr64ZeroBytes_08.take 1 ++ ptr64Plus256Bytes_08.drop 1)),
      valSummary08 (V08.decodePtrBytesNoForge true (.dynamic "T") 8
        (ptr64Bytes_08 ++ V08.encodeLittleEndianBytes 0x80 8 none)),
      valSummary08 (V08.decodePtrBytesNoForge true (.dynamic "T") 8
        (ptr64Bytes_08 ++ vtPtr64Bytes_08)),
      valSummary08 (V08.decodePtrBytesNoForge false (.uint .u8) 4 ptr32Bytes_08),
      valSummary08 (V08.decodePtrBytesNoForge true (.uint .u8) 4 ptr32ZeroBytes_08.reverse),
      valSummary08 (V08.evalConstValue (.indirect 52 0) tyRawPtrU8_08 [plainIntAlloc64_08] layouts64_08),
      valSummary08 (V08.evalConstValue (.slice (.int ⟨0x20000, 8⟩) 4) tyRefSliceU8_08 [] layouts64_08),
      valSummary08 (V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyBool_08
        [V08.mkInitByte 2]),
      valSummary08 (V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyUnalignedBool_08
        [V08.mkInitByte 2]),
      valSummary08 (V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyUnalignedBool_08
        [V08.mkInitByte 1]),
      valSummary08 (V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyChar_08
        (V08.encodeLittleEndianBytes 0xD800 4 none)),
      valSummary08 (V08.decodeTypedValueFromBytes V08.defaultCodecFuel layouts64_08 tyEnum3_08
        [V08.mkPtrFragByte 1 7 7 0 1 8] .strictUcg630Ub)
    ]
    v06Results = v08Results ∧ v06Results.length = 17 := by
  exact ⟨rfl, rfl⟩

/-- Verify `Trusted.MirSemantics` re-exports `PtrByteFrag`, `abstractBytesCoherentPtrProv?`,
and lossless raw-byte carrier helpers cleanly. -/
theorem trusted_mir_semantics_reexports :
    Trusted.MirSemantics.normPtrByteOffset 4 0x1_0000_0010 = 0x10 ∧
    Trusted.MirSemantics.abstractBytesCoherentPtrProv?
      (Trusted.MirSemantics.encodeLittleEndianBytes 0x10 8 (some (7, 7))) =
      some { allocId := 7, tag := 7, byteIdx := 0, origOffset := 0x10, ptrBytes := 8 } := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-! ## §5. Mechanical Local Axiom, Reachability, & Non-Triviality Audit -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let rec isTrivialProp : Expr → Bool
    | .forallE _ _ body _ => isTrivialProp body
    | .letE _ _ _ body _ => isTrivialProp body
    | .mdata _ e => isTrivialProp e
    | e =>
      if e.isConstOf ``True then true
      else if e.isAppOfArity ``Eq 3 then e.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``HEq 4 then e.appFn!.appFn!.appArg! == e.appArg!
      else if e.isAppOfArity ``Iff 2 then
        e.appFn!.appArg! == e.appArg! || (isTrivialProp e.appFn!.appArg! && isTrivialProp e.appArg!)
      else if e.isAppOfArity ``And 2 then isTrivialProp e.appFn!.appArg! && isTrivialProp e.appArg!
      else if e.isAppOfArity ``Or 2 then isTrivialProp e.appFn!.appArg! || isTrivialProp e.appArg!
      else false
  -- Self-test `isTrivialProp`
  let natTy := mkConst ``Nat
  let trivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 1)
  let nonTrivEq := mkApp3 (mkConst ``Eq [1]) natTy (mkNatLit 1) (mkNatLit 2)
  let mkAnd (a b : Expr) : Expr := mkApp2 (mkConst ``And) a b
  let mkOr (a b : Expr) : Expr := mkApp2 (mkConst ``Or) a b
  unless isTrivialProp (mkConst ``True) && isTrivialProp trivEq && !isTrivialProp nonTrivEq
      && isTrivialProp (mkAnd (mkConst ``True) trivEq)
      && isTrivialProp (mkOr nonTrivEq trivEq)
      && !isTrivialProp (mkAnd trivEq nonTrivEq)
      && !isTrivialProp (mkOr nonTrivEq nonTrivEq) do
    throwError "PtrByteCoherenceTests audit self-test failed: isTrivialProp"
  let mut checked : Nat := 0
  let mut thmChecked : Nat := 0
  let mut reached : Std.HashSet Name := {}
  for (c, ci) in env.constants.map₂.toList do
    for d in ci.getUsedConstantsAsSet do
      reached := reached.insert d
    match ci with
    | .thmInfo v =>
      if !(privateToUserName c).isInternalDetail then
        if isTrivialProp v.type then
          throwError "PtrByteCoherenceTests audit failure: {c} has trivial type"
        thmChecked := thmChecked + 1
    | _ => pure ()
    let axs ← liftCoreM <| Lean.collectAxioms c
    for a in axs do
      if a == ``sorryAx then throwError "PtrByteCoherenceTests audit failure: {c} uses sorryAx"
      if a == ``Lean.ofReduceBool then
        throwError "PtrByteCoherenceTests audit failure: {c} uses Lean.ofReduceBool"
      unless a == ``propext || a == ``Quot.sound || a == ``Classical.choice do
        throwError "PtrByteCoherenceTests audit failure: {c} uses non-standard axiom {a}"
    checked := checked + 1
  let requiredConsts : List Name := [
    ``Trusted.Rustc.V2026_06_01.MirSemantics.PtrByteFrag,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.abstractBytesCoherentPtrProv?,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.decodePtrBytesNoForge,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.decodeTypedValueFromBytes,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.decodeValueFromBytes,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.encodeRawAbstractByteVals,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.decodeRawAbstractByteVals?,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.overlayRawAbstractByteVals,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.globalAllocSliceToAbstractBytes,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.mergeByteProvenance,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.validateValueForTy?,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyUnionBytes,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalCopySingleDirect,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalForeignFrameCopySingleDirect,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalConstValue,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalByteCast,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.writeBytesAction,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.PtrByteFrag,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.abstractBytesCoherentPtrProv?,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.decodePtrBytesNoForge,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.decodeTypedValueFromBytes,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.decodeValueFromBytes,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.encodeRawAbstractByteVals,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.decodeRawAbstractByteVals?,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.overlayRawAbstractByteVals,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.globalAllocSliceToAbstractBytes,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.mergeByteProvenance,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.validateValueForTy?,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalCopyUnionBytes,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalCopySingleDirect,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalForeignFrameCopySingleDirect,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalConstValue,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalByteCast,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.writeBytesAction
  ]
  for req in requiredConsts do
    unless reached.contains req do
      throwError "PtrByteCoherenceTests audit failure: test module does not reference {req}"
  if checked == 0 || thmChecked < 20 then
    throwError "PtrByteCoherenceTests audit failure: unexpected counts (checked={checked}, thmChecked={thmChecked})"
  logInfo m!"PtrByteCoherenceTests audit: verified {checked} declarations ({thmChecked} non-trivial theorems, all {requiredConsts.length} V06+V08 key Trusted constants exercised, standard axioms only, 0 sorryAx, 0 ofReduceBool)"

end Anneal.PtrByteCoherenceTests
