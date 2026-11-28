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
export Trusted.Rustc.V2026_06_01.MirAst (Ty RigidTy Mutability UintTy IntTy FloatTy ScalarInt
  ProvenancePtr ConstScalar ConstValue ConstOperand ProjectionElem Place Operand Rvalue
  Statement StatementKind NonDivergingIntrinsic LocalDecl CapturedAllocation CapturedMir
  Terminator TerminatorKind)
export Trusted.Rustc.V2026_06_01.MirSemantics (PtrByteFrag AbstractByte Value LocalSlot
  BorrowEntry TreeBorrowPerm Memory StackFrame MachineState SavedCallerFrame MirStepNode
  RvalueEvalResult PlaceReadResult Ptr2IntTransmutePolicy UnionPlaceInfo MemOpRes
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
  validateValueForTy? evalConstValue evalGlobalDerefRead evalSliceFatPtrDerefRead
  evalOperand evalByteCast evalRvalue
  evalStmt evalCopySingleDirect evalCopyUnionBytes evalForeignFrameCopySingleDirect
  evalCopyMemory writePlaceValue writeBytesAction)
end V06

namespace V08
export Trusted.Rustc.V2026_08_01.Layout (LayoutTable TypeLayout Size Align BackendRepr
  ScalarLayout PrimitiveKind WrappingRange FieldsShape VariantsShape)
export Trusted.Rustc.V2026_08_01.MirAst (Ty RigidTy Mutability UintTy IntTy FloatTy ScalarInt
  ProvenancePtr ConstScalar ConstValue ConstOperand ProjectionElem Place Operand Rvalue
  Statement StatementKind NonDivergingIntrinsic LocalDecl CapturedAllocation CapturedMir
  Terminator TerminatorKind)
export Trusted.Rustc.V2026_08_01.MirSemantics (PtrByteFrag AbstractByte Value LocalSlot
  BorrowEntry TreeBorrowPerm Memory StackFrame MachineState SavedCallerFrame MirStepNode
  RvalueEvalResult PlaceReadResult Ptr2IntTransmutePolicy UnionPlaceInfo MemOpRes
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
  validateValueForTy? evalConstValue evalGlobalDerefRead evalSliceFatPtrDerefRead
  evalOperand evalByteCast evalRvalue
  evalStmt evalCopySingleDirect evalCopyUnionBytes evalForeignFrameCopySingleDirect
  evalCopyMemory writePlaceValue writeBytesAction)
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

/-! ## §4b. `[adv ep1-B1]` Adversarial Regressions

Regression tests for the defects found and fixed in critic pass `ep1-B1`, plus end-to-end
falsification attempts that A0 only covered at the decoder level:

* 32-bit target width (`W3`/`W4`): `evalConstValue (.indirect ..)` and `evalGlobalDerefRead` used
  the 64-bit `intCastTargetBytes` / `rigidTyKindByteSize` defaults, so a 32-bit `usize` constant
  or `*const usize` global read returned an 8-byte value that spliced in the next 4 bytes of the
  allocation (`sc<0x2_0000_0001, 8>`), and 32-bit pointer constants / pointer global reads failed.
  `copyBytesSubplace` compared a 4-byte thin-pointer image against a 64-bit width, so an in-order
  `copy_nonoverlapping::<u8>` of a 32-bit pointer back into a `*const T` failed `.unsupported`.
* Split copies: assembling a pointer from two 4-byte `copy_nonoverlapping::<u8>` halves (in either
  step order) retains provenance; swapped or duplicated halves strip it.
* Same-value overwrites: storing a `u8`/`u32` that equals the existing pointer byte(s) through a
  `*mut u8` / `*mut u32` still drops those bytes' fragments (raw pointer -> `.scalar`, `&u8` -> UB).
* Partial union field writes: `u.a = 0u32` over `u.p = ptr` leaves bytes `4..7` as fragments, so
  `u.p` decodes to a provenance-less `.scalar`.
* Typed deref reads (`Kani#5205`): `*p` / `(*p).0` of an invalid `bool`, `char`, or
  `Unaligned<bool>` faults `.ub`, while the untyped `*mut u8` store itself succeeds. -/

section B1Fixtures06

open V06

def b1PtrL32_06 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def b1UsizeL32_06 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def b1U32L_06 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- 32-bit table: `0` unit, `1` u8, `2` thin pointer (4 bytes), `3` `[u8; 4]`, `4` usize (4 bytes). -/
def b1Layouts32_06 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true,
    entries := [unitL06, u8L06, b1PtrL32_06, arr4U8L06, b1UsizeL32_06] }

/-- `union U { a: u32, p: *const u8 }` (size 8) at idx 16 of an extension of `layouts64_06`. -/
def b1UnionAP_06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [17, 5] }

def b1Layouts64_06 : LayoutTable :=
  { layouts64_06 with entries := layouts64_06.entries ++ [b1UnionAP_06, b1U32L_06] }

def b1TyU32_06 : Ty := { kind := .uint .u32, layoutIdx := 17 }
def b1TyUnionAP_06 : Ty := { kind := .adt "U" [], layoutIdx := 16 }

/-- Two 32-bit `usize` values `1` and `2` back to back, no relocations. -/
def b1AllocUsize32_06 : CapturedAllocation :=
  { allocId := 70,
    bytes := [some 1, some 0, some 0, some 0, some 2, some 0, some 0, some 0],
    relocations := [], align := ⟨4⟩, mutability := .not }

/-- A 32-bit pointer relocation (`ptr32_06`) at offset `0` followed by the plain `u32` `2`. -/
def b1AllocPtr32_06 : CapturedAllocation :=
  { allocId := 71,
    bytes := [some 0x10, some 0, some 0, some 0, some 2, some 0, some 0, some 0],
    relocations := [(0, ptr32_06)], align := ⟨4⟩, mutability := .not }

def b1Usize32_06 : Ty := { kind := .uint .usize, layoutIdx := 4 }
def b1Isize32_06 : Ty := { kind := .int .isize, layoutIdx := 4 }
def b1RawPtr32_06 : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 2 }
def b1MutPtr32_06 : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 2 }
def b1RefPtr32_06 : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 2 }

def b1Count_06 (n w : Nat) (ty : Ty) : Operand := .constant ⟨ty, .scalar (.int ⟨n, w⟩)⟩

def b1Copy_06 (src dst : Nat) (count : Operand) : Statement :=
  ⟨.intrinsic (.copyNonOverlapping (.copy ⟨src, []⟩) (.copy ⟨dst, []⟩) count), ""⟩

def b1Assign_06 (p : Place) (op : Operand) : Statement := ⟨.assign p (.use op), ""⟩

def b1Active_06 (tag loc : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := [], perm := .active }

def b1Frozen_06 (tag loc : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := [], perm := .frozen }

/-- Run `stmts` in order from `st`, returning the final state (or `none` on any non-step node). -/
def b1Run_06 (decls : List LocalDecl) (layouts : LayoutTable) :
    MachineState → List Statement → Option MachineState
  | st, [] => some st
  | st, stmt :: rest =>
    match evalStmt st stmt decls layouts with
    | .tau (.running st') => b1Run_06 decls layouts st' rest
    | _ => none

/-- Read `p` (typed, with `decls`) in the final state of running `stmts`. -/
def b1ReadAfter_06 (decls : List LocalDecl) (layouts : LayoutTable) (st : MachineState)
    (stmts : List Statement) (p : Place) : Option PlaceReadResult :=
  match b1Run_06 decls layouts st stmts with
  | some s =>
    some (evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals decls s.memory.callStack |> fun r =>
        match r with
        | .ok v _ => .ok v []
        | .ub => .ub
        | .unsupported => .unsupported)
  | none => none

end B1Fixtures06

/-- B1 (`W3`/`W4` 32-bit): `evalConstValue (.indirect ..)` reads exactly the target-width bytes of
`usize`/`isize` constants (never splicing the following element), decodes 32-bit pointer
relocations to `.ptr` at width 4, strips a misaligned 32-bit relocation for a raw pointer and
rejects it for a reference; `evalGlobalDerefRead` (via `Operand.copy (*p)`) does the same for
`*const usize`, `*const *const u8`, and `*const &u8` reads of 32-bit globals. -/
theorem b1_w3_32bit_const_and_global_reads_v06 :
    V06.evalConstValue (.indirect 70 0) b1Usize32_06 [b1AllocUsize32_06] b1Layouts32_06 =
      some (.scalar ⟨1, 4⟩) ∧
    V06.evalConstValue (.indirect 70 4) b1Isize32_06 [b1AllocUsize32_06] b1Layouts32_06 =
      some (.scalar ⟨2, 4⟩) ∧
    V06.evalConstValue (.indirect 71 0) b1RawPtr32_06 [b1AllocPtr32_06] b1Layouts32_06 =
      some (.ptr ptr32_06 4) ∧
    V06.evalConstValue (.indirect 71 0) b1RefPtr32_06 [b1AllocPtr32_06] b1Layouts32_06 =
      some (.ptr ptr32_06 4) ∧
    V06.evalConstValue (.indirect 71 1) b1RawPtr32_06 [b1AllocPtr32_06] b1Layouts32_06 =
      some (.scalar ⟨0x02000000, 4⟩) ∧
    V06.evalConstValue (.indirect 71 1) b1RefPtr32_06 [b1AllocPtr32_06] b1Layouts32_06 = none ∧
    (let decls : List V06.LocalDecl := [
       { mutability := .not, ty := { kind := .rawPtr .not (.rawPtr .not (.uint .u8)), layoutIdx := 2 },
         debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not (.uint .usize), layoutIdx := 2 },
         debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not (.ref .not (.uint .u8)), layoutIdx := 2 },
         debugName := none }]
     let locals : List V06.LocalSlot := [
       .init (.ptr { allocId := 71, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 70, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 71, offsetBytes := 0 } 4)]
     let globals := [b1AllocPtr32_06, b1AllocUsize32_06]
     V06.evalOperand locals (.copy ⟨0, [.deref]⟩) [] globals b1Layouts32_06 [] decls =
       .ok (.ptr ptr32_06 4) locals ∧
     V06.evalOperand locals (.copy ⟨1, [.deref]⟩) [] globals b1Layouts32_06 [] decls =
       .ok (.scalar ⟨1, 4⟩) locals ∧
     V06.evalOperand locals (.copy ⟨2, [.deref]⟩) [] globals b1Layouts32_06 [] decls =
       .ok (.ptr ptr32_06 4) locals) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (§3.2(a) at 32 bits, end to end): `copy_nonoverlapping::<u8>(&p, &mut buf, 4)` followed by
`copy_nonoverlapping::<u8>(&buf, &mut q, 4)` on a 32-bit target leaves `q = p` with provenance
and `*q` dereferences; a direct 4-byte `u8` copy `p -> q` does the same. -/
theorem b1_32bit_bytewise_ptr_copy_roundtrip_v06 :
    let target : V06.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let decls : List V06.LocalDecl := [
      { mutability := .not, ty := tyU8_06, debugName := none },
      { mutability := .not, ty := b1RawPtr32_06, debugName := none },
      { mutability := .mut, ty := { kind := .array (.uint .u8) 4, layoutIdx := 3 }, debugName := none },
      { mutability := .mut, ty := b1RawPtr32_06, debugName := none },
      { mutability := .not, ty := b1RawPtr32_06, debugName := none },
      { mutability := .not, ty := b1MutPtr32_06, debugName := none },
      { mutability := .not, ty := b1MutPtr32_06, debugName := none }]
    let locals : List V06.LocalSlot := [
      .init (.scalar ⟨0x5A, 1⟩), .init (.ptr target 4),
      .init (.aggregate 0 (List.replicate 4 (.scalar ⟨0, 1⟩))), .uninit,
      .init (.ptr { allocId := 2, offsetBytes := 0 } 4),
      .init (.ptr { allocId := 3, offsetBytes := 0 } 4),
      .init (.ptr { allocId := 4, offsetBytes := 0 } 4)]
    let mem : V06.Memory :=
      { V06.emptyMemory with
        borrows := [b1Frozen_06 1 0, b1Frozen_06 2 1, b1Active_06 3 2, b1Active_06 4 3] }
    let st : V06.MachineState := mkState06 locals mem
    let c4 := b1Count_06 4 4 b1Usize32_06
    b1ReadAfter_06 decls b1Layouts32_06 st [b1Copy_06 4 5 c4, b1Copy_06 5 6 c4] ⟨3, []⟩ =
      some (.ok (.ptr target 4) []) ∧
    b1ReadAfter_06 decls b1Layouts32_06 st [b1Copy_06 4 5 c4, b1Copy_06 5 6 c4] ⟨3, [.deref]⟩ =
      some (.ok (.scalar ⟨0x5A, 1⟩) []) ∧
    b1ReadAfter_06 decls b1Layouts32_06 st [b1Copy_06 4 6 c4] ⟨3, []⟩ =
      some (.ok (.ptr target 4) []) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (split copies, 64-bit): assembling `q` from the two 4-byte halves of `p` with
`copy_nonoverlapping::<u8>` retains provenance in either step order and `*q` dereferences;
writing `p`'s halves swapped, or `p`'s low half twice, strips provenance (`q` reads as a
provenance-less `.scalar`) and `*q` faults `.ub`. -/
theorem b1_split_half_copies_v06 :
    let target : V06.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let decls : List V06.LocalDecl := [
      { mutability := .not, ty := tyU8_06, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none }]
    let locals : List V06.LocalSlot := [
      .init (.scalar ⟨0x5A, 1⟩), .init (.ptr target 8), .uninit,
      .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 2, offsetBytes := 4 } 8),
      .init (.ptr { allocId := 3, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 3, offsetBytes := 4 } 8)]
    let mem : V06.Memory :=
      { V06.emptyMemory with borrows := [b1Frozen_06 1 0, b1Frozen_06 2 1, b1Active_06 3 2] }
    let st : V06.MachineState := mkState06 locals mem
    let c4 := b1Count_06 4 8 tyUsize_06
    b1ReadAfter_06 decls layouts64_06 st [b1Copy_06 3 5 c4, b1Copy_06 4 6 c4] ⟨2, []⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_06 decls layouts64_06 st [b1Copy_06 3 5 c4, b1Copy_06 4 6 c4] ⟨2, [.deref]⟩ =
      some (.ok (.scalar ⟨0x5A, 1⟩) []) ∧
    b1ReadAfter_06 decls layouts64_06 st [b1Copy_06 4 6 c4, b1Copy_06 3 5 c4] ⟨2, []⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_06 decls layouts64_06 st [b1Copy_06 3 6 c4, b1Copy_06 4 5 c4] ⟨2, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_06 decls layouts64_06 st [b1Copy_06 3 6 c4, b1Copy_06 4 5 c4] ⟨2, [.deref]⟩ =
      some .ub ∧
    b1ReadAfter_06 decls layouts64_06 st [b1Copy_06 3 5 c4, b1Copy_06 3 6 c4] ⟨2, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_06 decls layouts64_06 st [b1Copy_06 3 5 c4, b1Copy_06 3 6 c4] ⟨2, [.deref]⟩ =
      some .ub := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (same-value overwrites and partial union writes): storing `0u8` / `0u32` over pointer
bytes that are already `0` (`p.offsetBytes = 0`) through `*mut u8` / `*mut u32` still drops those
bytes' fragments, so the raw pointer reads as `.scalar ⟨0, 8⟩`, `*p` faults, and the reference
read faults; in `union U { a: u32, p: *const u8 }`, `u.a = 0u32` after `u.p = ptr` leaves `u.p` a
provenance-less `.scalar ⟨0, 8⟩`, and `union RawOrPtr { raw: u64, ptr: *const u8 }` holding a
lossless raw-byte carrier image of `ptr` reads back `u.ptr = .scalar ⟨5, 8⟩` after `u.raw = 5`. -/
theorem b1_same_value_overwrite_and_partial_union_write_v06 :
    let target : V06.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let decls : List V06.LocalDecl := [
      { mutability := .mut, ty := tyU8_06, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .mut, ty := tyRefU8_06, debugName := none },
      { mutability := .mut, ty := b1TyUnionAP_06, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none },
      { mutability := .mut, ty := tyRawOrPtrUnion_06, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none }]
    let carrierU : V06.Value :=
      .aggregate 0 [.unit, .unit,
        .aggregate 0 (V06.encodeRawAbstractByteVals (V06.encodeLittleEndianBytes 0 8 (some (1, 1))))]
    let locals : List V06.LocalSlot := [
      .init (.scalar ⟨0x5A, 1⟩), .init (.ptr target 8), .init (.ptr target 8),
      .init (.aggregate 0 [.unit, .ptr target 8]),
      .init (.ptr { allocId := 10, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 11, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 10, offsetBytes := 1 } 8),
      .init carrierU,
      .init (.ptr { allocId := 12, offsetBytes := 0 } 8)]
    let mem : V06.Memory :=
      { V06.emptyMemory with
        borrows := [b1Frozen_06 1 0, b1Active_06 10 1, b1Active_06 11 1, b1Active_06 12 2] }
    let st : V06.MachineState := mkState06 locals mem
    let u8c (n : Nat) : V06.Operand := .constant ⟨tyU8_06, .scalar (.int ⟨n, 1⟩)⟩
    let u32c (n : Nat) : V06.Operand := .constant ⟨b1TyU32_06, .scalar (.int ⟨n, 4⟩)⟩
    let u64c (n : Nat) : V06.Operand := .constant ⟨tyU64_06, .scalar (.int ⟨n, 8⟩)⟩
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨4, [.deref]⟩ (u8c 0)] ⟨1, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨4, [.deref]⟩ (u8c 0)] ⟨1, [.deref]⟩ =
      some .ub ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨6, [.deref]⟩ (u8c 0)] ⟨1, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨5, [.deref]⟩ (u32c 0)] ⟨1, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨8, [.deref]⟩ (u8c 0)] ⟨2, []⟩ =
      some .ub ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨3, [.field 0 b1TyU32_06]⟩ (u32c 0)]
      ⟨3, [.field 1 tyRawPtrU8_06]⟩ = some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨3, [.field 0 b1TyU32_06]⟩ (u32c 0x10)]
      ⟨3, [.field 1 tyRawPtrU8_06]⟩ = some (.ok (.scalar ⟨0x10, 8⟩) []) ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [] ⟨3, [.field 1 tyRawPtrU8_06]⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [] ⟨7, [.field 1 tyRawPtrU8_06]⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨7, [.field 0 tyU64_06]⟩ (u64c 5)]
      ⟨7, [.field 1 tyRawPtrU8_06]⟩ = some (.ok (.scalar ⟨5, 8⟩) []) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (`Kani#5205` typed deref reads): storing `2u8` through a `*mut u8` into a `bool` or
`Unaligned<bool>` local, or `0xD800u32` through a `*mut u32` into a `char` local, succeeds;
reading the local afterwards faults `.ub`. Dereferencing `*const bool`, `&bool`, `*const char`,
and `*const Unaligned<bool>` (also `(*p).0`) at invalid storage faults `.ub`, and the same derefs
at valid storage succeed. -/
theorem b1_kani5205_typed_deref_reads_v06 :
    let decls : List V06.LocalDecl := [
      { mutability := .mut, ty := tyBool_06, debugName := none },
      { mutability := .mut, ty := tyChar_06, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_06, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not .bool, layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not .char, layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not tyUnalignedBool_06.kind, layoutIdx := 5 },
        debugName := none },
      { mutability := .not, ty := { kind := .ref .not .bool, layoutIdx := 6 }, debugName := none }]
    let ptrs : List V06.LocalSlot := [
      .init (.ptr { allocId := 10, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 11, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 12, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 13, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 14, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 15, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 16, offsetBytes := 0 } 8)]
    let good : List V06.LocalSlot :=
      [.init (.scalar ⟨1, 1⟩), .init (.scalar ⟨65, 4⟩), .init (.aggregate 0 [.scalar ⟨1, 1⟩])] ++ ptrs
    let bad : List V06.LocalSlot :=
      [.init (.scalar ⟨2, 1⟩), .init (.scalar ⟨0xD800, 4⟩), .init (.aggregate 0 [.scalar ⟨2, 1⟩])] ++ ptrs
    let borrows : List V06.BorrowEntry := [b1Active_06 10 0, b1Active_06 11 1, b1Active_06 12 2,
      b1Active_06 13 0, b1Active_06 14 1, b1Active_06 15 2, b1Active_06 16 0]
    let st : V06.MachineState := mkState06 good { V06.emptyMemory with borrows := borrows }
    let u8c (n : Nat) : V06.Operand := .constant ⟨tyU8_06, .scalar (.int ⟨n, 1⟩)⟩
    let u32c (n : Nat) : V06.Operand := .constant ⟨b1TyU32_06, .scalar (.int ⟨n, 4⟩)⟩
    let rd (ls : List V06.LocalSlot) (p : V06.Place) : V06.PlaceReadResult :=
      V06.evalOperand ls (.copy p) borrows [] layouts64_06 [] decls
    -- untyped stores of invalid bytes succeed; the typed read faults
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨3, [.deref]⟩ (u8c 2)] ⟨0, []⟩ = some .ub ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨4, [.deref]⟩ (u32c 0xD800)] ⟨1, []⟩ =
      some .ub ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨5, [.deref]⟩ (u8c 2)] ⟨2, []⟩ = some .ub ∧
    b1ReadAfter_06 decls b1Layouts64_06 st [b1Assign_06 ⟨5, [.deref]⟩ (u8c 2)]
      ⟨2, [.field 0 tyBool_06]⟩ = some .ub ∧
    -- typed derefs of invalid storage fault
    rd bad ⟨6, [.deref]⟩ = .ub ∧
    rd bad ⟨9, [.deref]⟩ = .ub ∧
    rd bad ⟨7, [.deref]⟩ = .ub ∧
    rd bad ⟨8, [.deref]⟩ = .ub ∧
    rd bad ⟨8, [.deref, .field 0 tyBool_06]⟩ = .ub ∧
    -- the same derefs of valid storage succeed
    rd good ⟨6, [.deref]⟩ = .ok (.scalar ⟨1, 1⟩) good ∧
    rd good ⟨9, [.deref]⟩ = .ok (.scalar ⟨1, 1⟩) good ∧
    rd good ⟨7, [.deref]⟩ = .ok (.scalar ⟨65, 4⟩) good ∧
    rd good ⟨8, [.deref]⟩ = .ok (.aggregate 0 [.scalar ⟨1, 1⟩]) good := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (direct `evalGlobalDerefRead` / `materializeReadPtrValue` controls): the 32-bit global
`usize` read covers exactly 4 bytes, and a raw-byte carrier image of a reversed pointer
materializes to a provenance-less `.scalar` at raw pointer type and to `none` at reference type,
while the in-order carrier image materializes back to `.ptr`. -/
theorem b1_direct_global_read_and_materialize_v06 :
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] b1AllocUsize32_06 0 4 []
      b1Layouts32_06 (some b1Usize32_06) = .ok (.scalar ⟨1, 4⟩) [] ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] b1AllocUsize32_06 4 4 []
      b1Layouts32_06 (some b1Usize32_06) = .ok (.scalar ⟨2, 4⟩) [] ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.materializeReadPtrValue layouts64_06 (some tyRawPtrU8_06)
      (.aggregate 0 (V06.encodeRawAbstractByteVals ptr64Bytes_06.reverse)) =
      some (.scalar ⟨0x1000000000000000, 8⟩) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.materializeReadPtrValue layouts64_06 (some tyRefU8_06)
      (.aggregate 0 (V06.encodeRawAbstractByteVals ptr64Bytes_06.reverse)) = none ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.materializeReadPtrValue layouts64_06 (some tyRefU8_06)
      (.aggregate 0 (V06.encodeRawAbstractByteVals ptr64Bytes_06)) = some (.ptr ptr64_06 8) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

section B1Fixtures08

open V08

def b1PtrL32_08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def b1UsizeL32_08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

def b1U32L_08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- 32-bit table: `0` unit, `1` u8, `2` thin pointer (4 bytes), `3` `[u8; 4]`, `4` usize (4 bytes). -/
def b1Layouts32_08 : LayoutTable :=
  { pointerBits := 32, isLittleEndian := true,
    entries := [unitL08, u8L08, b1PtrL32_08, arr4U8L08, b1UsizeL32_08] }

/-- `union U { a: u32, p: *const u8 }` (size 8) at idx 16 of an extension of `layouts64_08`. -/
def b1UnionAP_08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [17, 5] }

def b1Layouts64_08 : LayoutTable :=
  { layouts64_08 with entries := layouts64_08.entries ++ [b1UnionAP_08, b1U32L_08] }

def b1TyU32_08 : Ty := { kind := .uint .u32, layoutIdx := 17 }
def b1TyUnionAP_08 : Ty := { kind := .adt "U" [], layoutIdx := 16 }

/-- Two 32-bit `usize` values `1` and `2` back to back, no relocations. -/
def b1AllocUsize32_08 : CapturedAllocation :=
  { allocId := 70,
    bytes := [some 1, some 0, some 0, some 0, some 2, some 0, some 0, some 0],
    relocations := [], align := ⟨4⟩, mutability := .not }

/-- A 32-bit pointer relocation (`ptr32_08`) at offset `0` followed by the plain `u32` `2`. -/
def b1AllocPtr32_08 : CapturedAllocation :=
  { allocId := 71,
    bytes := [some 0x10, some 0, some 0, some 0, some 2, some 0, some 0, some 0],
    relocations := [(0, ptr32_08)], align := ⟨4⟩, mutability := .not }

def b1Usize32_08 : Ty := { kind := .uint .usize, layoutIdx := 4 }
def b1Isize32_08 : Ty := { kind := .int .isize, layoutIdx := 4 }
def b1RawPtr32_08 : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 2 }
def b1MutPtr32_08 : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 2 }
def b1RefPtr32_08 : Ty := { kind := .ref .not (.uint .u8), layoutIdx := 2 }

def b1Count_08 (n w : Nat) (ty : Ty) : Operand := .constant ⟨ty, .scalar (.int ⟨n, w⟩)⟩

def b1Copy_08 (src dst : Nat) (count : Operand) : Statement :=
  ⟨.intrinsic (.copyNonOverlapping (.copy ⟨src, []⟩) (.copy ⟨dst, []⟩) count), ""⟩

def b1Assign_08 (p : Place) (op : Operand) : Statement := ⟨.assign p (.use op), ""⟩

def b1Active_08 (tag loc : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := [], perm := .active }

def b1Frozen_08 (tag loc : Nat) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := [], perm := .frozen }

/-- Run `stmts` in order from `st`, returning the final state (or `none` on any non-step node). -/
def b1Run_08 (decls : List LocalDecl) (layouts : LayoutTable) :
    MachineState → List Statement → Option MachineState
  | st, [] => some st
  | st, stmt :: rest =>
    match evalStmt st stmt decls layouts with
    | .tau (.running st') => b1Run_08 decls layouts st' rest
    | _ => none

/-- Read `p` (typed, with `decls`) in the final state of running `stmts`. -/
def b1ReadAfter_08 (decls : List LocalDecl) (layouts : LayoutTable) (st : MachineState)
    (stmts : List Statement) (p : Place) : Option PlaceReadResult :=
  match b1Run_08 decls layouts st stmts with
  | some s =>
    some (evalOperand s.frame.locals (.copy p) s.memory.borrows s.memory.globals layouts
      s.memory.callerLocals decls s.memory.callStack |> fun r =>
        match r with
        | .ok v _ => .ok v []
        | .ub => .ub
        | .unsupported => .unsupported)
  | none => none

end B1Fixtures08

/-- B1 (`W3`/`W4` 32-bit): `evalConstValue (.indirect ..)` reads exactly the target-width bytes of
`usize`/`isize` constants (never splicing the following element), decodes 32-bit pointer
relocations to `.ptr` at width 4, strips a misaligned 32-bit relocation for a raw pointer and
rejects it for a reference; `evalGlobalDerefRead` (via `Operand.copy (*p)`) does the same for
`*const usize`, `*const *const u8`, and `*const &u8` reads of 32-bit globals. -/
theorem b1_w3_32bit_const_and_global_reads_v08 :
    V08.evalConstValue (.indirect 70 0) b1Usize32_08 [b1AllocUsize32_08] b1Layouts32_08 =
      some (.scalar ⟨1, 4⟩) ∧
    V08.evalConstValue (.indirect 70 4) b1Isize32_08 [b1AllocUsize32_08] b1Layouts32_08 =
      some (.scalar ⟨2, 4⟩) ∧
    V08.evalConstValue (.indirect 71 0) b1RawPtr32_08 [b1AllocPtr32_08] b1Layouts32_08 =
      some (.ptr ptr32_08 4) ∧
    V08.evalConstValue (.indirect 71 0) b1RefPtr32_08 [b1AllocPtr32_08] b1Layouts32_08 =
      some (.ptr ptr32_08 4) ∧
    V08.evalConstValue (.indirect 71 1) b1RawPtr32_08 [b1AllocPtr32_08] b1Layouts32_08 =
      some (.scalar ⟨0x02000000, 4⟩) ∧
    V08.evalConstValue (.indirect 71 1) b1RefPtr32_08 [b1AllocPtr32_08] b1Layouts32_08 = none ∧
    (let decls : List V08.LocalDecl := [
       { mutability := .not, ty := { kind := .rawPtr .not (.rawPtr .not (.uint .u8)), layoutIdx := 2 },
         debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not (.uint .usize), layoutIdx := 2 },
         debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not (.ref .not (.uint .u8)), layoutIdx := 2 },
         debugName := none }]
     let locals : List V08.LocalSlot := [
       .init (.ptr { allocId := 71, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 70, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 71, offsetBytes := 0 } 4)]
     let globals := [b1AllocPtr32_08, b1AllocUsize32_08]
     V08.evalOperand locals (.copy ⟨0, [.deref]⟩) [] globals b1Layouts32_08 [] decls =
       .ok (.ptr ptr32_08 4) locals ∧
     V08.evalOperand locals (.copy ⟨1, [.deref]⟩) [] globals b1Layouts32_08 [] decls =
       .ok (.scalar ⟨1, 4⟩) locals ∧
     V08.evalOperand locals (.copy ⟨2, [.deref]⟩) [] globals b1Layouts32_08 [] decls =
       .ok (.ptr ptr32_08 4) locals) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (§3.2(a) at 32 bits, end to end): `copy_nonoverlapping::<u8>(&p, &mut buf, 4)` followed by
`copy_nonoverlapping::<u8>(&buf, &mut q, 4)` on a 32-bit target leaves `q = p` with provenance
and `*q` dereferences; a direct 4-byte `u8` copy `p -> q` does the same. -/
theorem b1_32bit_bytewise_ptr_copy_roundtrip_v08 :
    let target : V08.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let decls : List V08.LocalDecl := [
      { mutability := .not, ty := tyU8_08, debugName := none },
      { mutability := .not, ty := b1RawPtr32_08, debugName := none },
      { mutability := .mut, ty := { kind := .array (.uint .u8) 4, layoutIdx := 3 }, debugName := none },
      { mutability := .mut, ty := b1RawPtr32_08, debugName := none },
      { mutability := .not, ty := b1RawPtr32_08, debugName := none },
      { mutability := .not, ty := b1MutPtr32_08, debugName := none },
      { mutability := .not, ty := b1MutPtr32_08, debugName := none }]
    let locals : List V08.LocalSlot := [
      .init (.scalar ⟨0x5A, 1⟩), .init (.ptr target 4),
      .init (.aggregate 0 (List.replicate 4 (.scalar ⟨0, 1⟩))), .uninit,
      .init (.ptr { allocId := 2, offsetBytes := 0 } 4),
      .init (.ptr { allocId := 3, offsetBytes := 0 } 4),
      .init (.ptr { allocId := 4, offsetBytes := 0 } 4)]
    let mem : V08.Memory :=
      { V08.emptyMemory with
        borrows := [b1Frozen_08 1 0, b1Frozen_08 2 1, b1Active_08 3 2, b1Active_08 4 3] }
    let st : V08.MachineState := mkState08 locals mem
    let c4 := b1Count_08 4 4 b1Usize32_08
    b1ReadAfter_08 decls b1Layouts32_08 st [b1Copy_08 4 5 c4, b1Copy_08 5 6 c4] ⟨3, []⟩ =
      some (.ok (.ptr target 4) []) ∧
    b1ReadAfter_08 decls b1Layouts32_08 st [b1Copy_08 4 5 c4, b1Copy_08 5 6 c4] ⟨3, [.deref]⟩ =
      some (.ok (.scalar ⟨0x5A, 1⟩) []) ∧
    b1ReadAfter_08 decls b1Layouts32_08 st [b1Copy_08 4 6 c4] ⟨3, []⟩ =
      some (.ok (.ptr target 4) []) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (split copies, 64-bit): assembling `q` from the two 4-byte halves of `p` with
`copy_nonoverlapping::<u8>` retains provenance in either step order and `*q` dereferences;
writing `p`'s halves swapped, or `p`'s low half twice, strips provenance (`q` reads as a
provenance-less `.scalar`) and `*q` faults `.ub`. -/
theorem b1_split_half_copies_v08 :
    let target : V08.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let decls : List V08.LocalDecl := [
      { mutability := .not, ty := tyU8_08, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none }]
    let locals : List V08.LocalSlot := [
      .init (.scalar ⟨0x5A, 1⟩), .init (.ptr target 8), .uninit,
      .init (.ptr { allocId := 2, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 2, offsetBytes := 4 } 8),
      .init (.ptr { allocId := 3, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 3, offsetBytes := 4 } 8)]
    let mem : V08.Memory :=
      { V08.emptyMemory with borrows := [b1Frozen_08 1 0, b1Frozen_08 2 1, b1Active_08 3 2] }
    let st : V08.MachineState := mkState08 locals mem
    let c4 := b1Count_08 4 8 tyUsize_08
    b1ReadAfter_08 decls layouts64_08 st [b1Copy_08 3 5 c4, b1Copy_08 4 6 c4] ⟨2, []⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_08 decls layouts64_08 st [b1Copy_08 3 5 c4, b1Copy_08 4 6 c4] ⟨2, [.deref]⟩ =
      some (.ok (.scalar ⟨0x5A, 1⟩) []) ∧
    b1ReadAfter_08 decls layouts64_08 st [b1Copy_08 4 6 c4, b1Copy_08 3 5 c4] ⟨2, []⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_08 decls layouts64_08 st [b1Copy_08 3 6 c4, b1Copy_08 4 5 c4] ⟨2, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_08 decls layouts64_08 st [b1Copy_08 3 6 c4, b1Copy_08 4 5 c4] ⟨2, [.deref]⟩ =
      some .ub ∧
    b1ReadAfter_08 decls layouts64_08 st [b1Copy_08 3 5 c4, b1Copy_08 3 6 c4] ⟨2, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_08 decls layouts64_08 st [b1Copy_08 3 5 c4, b1Copy_08 3 6 c4] ⟨2, [.deref]⟩ =
      some .ub := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (same-value overwrites and partial union writes): storing `0u8` / `0u32` over pointer
bytes that are already `0` (`p.offsetBytes = 0`) through `*mut u8` / `*mut u32` still drops those
bytes' fragments, so the raw pointer reads as `.scalar ⟨0, 8⟩`, `*p` faults, and the reference
read faults; in `union U { a: u32, p: *const u8 }`, `u.a = 0u32` after `u.p = ptr` leaves `u.p` a
provenance-less `.scalar ⟨0, 8⟩`, and `union RawOrPtr { raw: u64, ptr: *const u8 }` holding a
lossless raw-byte carrier image of `ptr` reads back `u.ptr = .scalar ⟨5, 8⟩` after `u.raw = 5`. -/
theorem b1_same_value_overwrite_and_partial_union_write_v08 :
    let target : V08.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    let decls : List V08.LocalDecl := [
      { mutability := .mut, ty := tyU8_08, debugName := none },
      { mutability := .mut, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .mut, ty := tyRefU8_08, debugName := none },
      { mutability := .mut, ty := b1TyUnionAP_08, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
      { mutability := .mut, ty := tyRawOrPtrUnion_08, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none }]
    let carrierU : V08.Value :=
      .aggregate 0 [.unit, .unit,
        .aggregate 0 (V08.encodeRawAbstractByteVals (V08.encodeLittleEndianBytes 0 8 (some (1, 1))))]
    let locals : List V08.LocalSlot := [
      .init (.scalar ⟨0x5A, 1⟩), .init (.ptr target 8), .init (.ptr target 8),
      .init (.aggregate 0 [.unit, .ptr target 8]),
      .init (.ptr { allocId := 10, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 11, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 10, offsetBytes := 1 } 8),
      .init carrierU,
      .init (.ptr { allocId := 12, offsetBytes := 0 } 8)]
    let mem : V08.Memory :=
      { V08.emptyMemory with
        borrows := [b1Frozen_08 1 0, b1Active_08 10 1, b1Active_08 11 1, b1Active_08 12 2] }
    let st : V08.MachineState := mkState08 locals mem
    let u8c (n : Nat) : V08.Operand := .constant ⟨tyU8_08, .scalar (.int ⟨n, 1⟩)⟩
    let u32c (n : Nat) : V08.Operand := .constant ⟨b1TyU32_08, .scalar (.int ⟨n, 4⟩)⟩
    let u64c (n : Nat) : V08.Operand := .constant ⟨tyU64_08, .scalar (.int ⟨n, 8⟩)⟩
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨4, [.deref]⟩ (u8c 0)] ⟨1, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨4, [.deref]⟩ (u8c 0)] ⟨1, [.deref]⟩ =
      some .ub ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨6, [.deref]⟩ (u8c 0)] ⟨1, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨5, [.deref]⟩ (u32c 0)] ⟨1, []⟩ =
      some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨8, [.deref]⟩ (u8c 0)] ⟨2, []⟩ =
      some .ub ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨3, [.field 0 b1TyU32_08]⟩ (u32c 0)]
      ⟨3, [.field 1 tyRawPtrU8_08]⟩ = some (.ok (.scalar ⟨0, 8⟩) []) ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨3, [.field 0 b1TyU32_08]⟩ (u32c 0x10)]
      ⟨3, [.field 1 tyRawPtrU8_08]⟩ = some (.ok (.scalar ⟨0x10, 8⟩) []) ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [] ⟨3, [.field 1 tyRawPtrU8_08]⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [] ⟨7, [.field 1 tyRawPtrU8_08]⟩ =
      some (.ok (.ptr target 8) []) ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨7, [.field 0 tyU64_08]⟩ (u64c 5)]
      ⟨7, [.field 1 tyRawPtrU8_08]⟩ = some (.ok (.scalar ⟨5, 8⟩) []) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (`Kani#5205` typed deref reads): storing `2u8` through a `*mut u8` into a `bool` or
`Unaligned<bool>` local, or `0xD800u32` through a `*mut u32` into a `char` local, succeeds;
reading the local afterwards faults `.ub`. Dereferencing `*const bool`, `&bool`, `*const char`,
and `*const Unaligned<bool>` (also `(*p).0`) at invalid storage faults `.ub`, and the same derefs
at valid storage succeed. -/
theorem b1_kani5205_typed_deref_reads_v08 :
    let decls : List V08.LocalDecl := [
      { mutability := .mut, ty := tyBool_08, debugName := none },
      { mutability := .mut, ty := tyChar_08, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_08, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not .bool, layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not .char, layoutIdx := 5 }, debugName := none },
      { mutability := .not, ty := { kind := .rawPtr .not tyUnalignedBool_08.kind, layoutIdx := 5 },
        debugName := none },
      { mutability := .not, ty := { kind := .ref .not .bool, layoutIdx := 6 }, debugName := none }]
    let ptrs : List V08.LocalSlot := [
      .init (.ptr { allocId := 10, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 11, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 12, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 13, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 14, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 15, offsetBytes := 0 } 8),
      .init (.ptr { allocId := 16, offsetBytes := 0 } 8)]
    let good : List V08.LocalSlot :=
      [.init (.scalar ⟨1, 1⟩), .init (.scalar ⟨65, 4⟩), .init (.aggregate 0 [.scalar ⟨1, 1⟩])] ++ ptrs
    let bad : List V08.LocalSlot :=
      [.init (.scalar ⟨2, 1⟩), .init (.scalar ⟨0xD800, 4⟩), .init (.aggregate 0 [.scalar ⟨2, 1⟩])] ++ ptrs
    let borrows : List V08.BorrowEntry := [b1Active_08 10 0, b1Active_08 11 1, b1Active_08 12 2,
      b1Active_08 13 0, b1Active_08 14 1, b1Active_08 15 2, b1Active_08 16 0]
    let st : V08.MachineState := mkState08 good { V08.emptyMemory with borrows := borrows }
    let u8c (n : Nat) : V08.Operand := .constant ⟨tyU8_08, .scalar (.int ⟨n, 1⟩)⟩
    let u32c (n : Nat) : V08.Operand := .constant ⟨b1TyU32_08, .scalar (.int ⟨n, 4⟩)⟩
    let rd (ls : List V08.LocalSlot) (p : V08.Place) : V08.PlaceReadResult :=
      V08.evalOperand ls (.copy p) borrows [] layouts64_08 [] decls
    -- untyped stores of invalid bytes succeed; the typed read faults
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨3, [.deref]⟩ (u8c 2)] ⟨0, []⟩ = some .ub ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨4, [.deref]⟩ (u32c 0xD800)] ⟨1, []⟩ =
      some .ub ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨5, [.deref]⟩ (u8c 2)] ⟨2, []⟩ = some .ub ∧
    b1ReadAfter_08 decls b1Layouts64_08 st [b1Assign_08 ⟨5, [.deref]⟩ (u8c 2)]
      ⟨2, [.field 0 tyBool_08]⟩ = some .ub ∧
    -- typed derefs of invalid storage fault
    rd bad ⟨6, [.deref]⟩ = .ub ∧
    rd bad ⟨9, [.deref]⟩ = .ub ∧
    rd bad ⟨7, [.deref]⟩ = .ub ∧
    rd bad ⟨8, [.deref]⟩ = .ub ∧
    rd bad ⟨8, [.deref, .field 0 tyBool_08]⟩ = .ub ∧
    -- the same derefs of valid storage succeed
    rd good ⟨6, [.deref]⟩ = .ok (.scalar ⟨1, 1⟩) good ∧
    rd good ⟨9, [.deref]⟩ = .ok (.scalar ⟨1, 1⟩) good ∧
    rd good ⟨7, [.deref]⟩ = .ok (.scalar ⟨65, 4⟩) good ∧
    rd good ⟨8, [.deref]⟩ = .ok (.aggregate 0 [.scalar ⟨1, 1⟩]) good := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 (direct `evalGlobalDerefRead` / `materializeReadPtrValue` controls): the 32-bit global
`usize` read covers exactly 4 bytes, and a raw-byte carrier image of a reversed pointer
materializes to a provenance-less `.scalar` at raw pointer type and to `none` at reference type,
while the in-order carrier image materializes back to `.ptr`. -/
theorem b1_direct_global_read_and_materialize_v08 :
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] b1AllocUsize32_08 0 4 []
      b1Layouts32_08 (some b1Usize32_08) = .ok (.scalar ⟨1, 4⟩) [] ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] b1AllocUsize32_08 4 4 []
      b1Layouts32_08 (some b1Usize32_08) = .ok (.scalar ⟨2, 4⟩) [] ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.materializeReadPtrValue layouts64_08 (some tyRawPtrU8_08)
      (.aggregate 0 (V08.encodeRawAbstractByteVals ptr64Bytes_08.reverse)) =
      some (.scalar ⟨0x1000000000000000, 8⟩) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.materializeReadPtrValue layouts64_08 (some tyRefU8_08)
      (.aggregate 0 (V08.encodeRawAbstractByteVals ptr64Bytes_08.reverse)) = none ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.materializeReadPtrValue layouts64_08 (some tyRefU8_08)
      (.aggregate 0 (V08.encodeRawAbstractByteVals ptr64Bytes_08)) = some (.ptr ptr64_08 8) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- B1 lockstep parity: the 32-bit constant / global-read regressions agree across
`V2026_06_01` and `V2026_08_01`. -/
theorem b1_lockstep_parity_32bit :
    let v06 : List ValSummary := [
      valSummary06 (V06.evalConstValue (.indirect 70 0) b1Usize32_06 [b1AllocUsize32_06] b1Layouts32_06),
      valSummary06 (V06.evalConstValue (.indirect 70 4) b1Isize32_06 [b1AllocUsize32_06] b1Layouts32_06),
      valSummary06 (V06.evalConstValue (.indirect 71 0) b1RawPtr32_06 [b1AllocPtr32_06] b1Layouts32_06),
      valSummary06 (V06.evalConstValue (.indirect 71 0) b1RefPtr32_06 [b1AllocPtr32_06] b1Layouts32_06),
      valSummary06 (V06.evalConstValue (.indirect 71 1) b1RawPtr32_06 [b1AllocPtr32_06] b1Layouts32_06),
      valSummary06 (V06.evalConstValue (.indirect 71 1) b1RefPtr32_06 [b1AllocPtr32_06] b1Layouts32_06)]
    let v08 : List ValSummary := [
      valSummary08 (V08.evalConstValue (.indirect 70 0) b1Usize32_08 [b1AllocUsize32_08] b1Layouts32_08),
      valSummary08 (V08.evalConstValue (.indirect 70 4) b1Isize32_08 [b1AllocUsize32_08] b1Layouts32_08),
      valSummary08 (V08.evalConstValue (.indirect 71 0) b1RawPtr32_08 [b1AllocPtr32_08] b1Layouts32_08),
      valSummary08 (V08.evalConstValue (.indirect 71 0) b1RefPtr32_08 [b1AllocPtr32_08] b1Layouts32_08),
      valSummary08 (V08.evalConstValue (.indirect 71 1) b1RawPtr32_08 [b1AllocPtr32_08] b1Layouts32_08),
      valSummary08 (V08.evalConstValue (.indirect 71 1) b1RefPtr32_08 [b1AllocPtr32_08] b1Layouts32_08)]
    v06 = v08 ∧ v06 = [.scalar 1 4, .scalar 2 4, .ptr 9 0x10 4, .ptr 9 0x10 4, .scalar 0x02000000 4, .none] := by
  exact ⟨rfl, rfl⟩

/-! ## §4.5. Pass A1 Adversarial Regressions & `lean-miri` Correspondence Gap Postmortem

### `lean-miri` Correspondence Gap Postmortem (`mir-correspondence-postmortem`)
Why `LeanMiriSpec` did not catch the three classes of defects uncovered in Pass A1:
1. **Global relocation provenance stripping (`evalGlobalDerefRead` / `evalConstValue (.indirect)`)**:
   `LeanMiriSpec` (`SimLM*` / `WitLM*`) bridges stack/heap allocations in `MachineState.memory` and
   scalar/ZST constants, and does not yet bridge `CapturedAllocation.relocations` in `body.globals`
   (`ConstValue.indirect` / `evalGlobalDerefRead`). Prior to A1, `readGlobalScalar` ignored
   `alloc.relocations` and `evalConstValue`/`evalGlobalDerefRead` called `decodeValueFromBytes`
   instead of `decodeTypedValueFromBytes`, allowing global pointer relocations to be read as plain
   integers/booleans/arrays/tuples/multi-variant enums and skipping `0..=0x10FFFF` surrogate niche
   checks.
2. **32-bit `evalCopyUnionBytes`, `convertCopySingleValue?`, and compound `[usize; N]` /
   `(*const T, usize)` widths**: Every `LeanMiriSpec` theorem carries the explicit 64-bit target
   hypothesis `(hptr8 : layoutPointerBytes body.layouts = 8)`, leaving `pointerBits = 32`
   (`layoutPointerBytes = 4`) outside the `LeanMiriSpec` hypothesis boundary. Prior to A1,
   `evalCopyUnionBytes` and `convertCopySingleValue?` consulted 64-bit `rigidTyByteSize` (`8` instead
   of `4`), faulting with spurious `.ub` on valid 32-bit union and single-element copies.
3. **Wide-pointer (`*const [T]`, `&[T]`, `&str`, `*const dyn Trait`, `&dyn Trait`) bytewise copy and
   partial sub-pointer overwrites in `copyBytesSubplace`**: `CopyLM4_2` covers thin pointers,
   integers, arrays, and unions (`isThinPtrCopyKind` / `isLayoutIndepByteKind`), leaving unsized
   wide-pointer destinations under bytewise `copy_nonoverlapping::<u8>` outside `CopyLM4_2`'s
   covered type fragment. Prior to A1, `copyBytesSubplace` restricted exact byte copy/partial
   overwrite to `isThinPtrCopyKind`. -/

section A1Fixtures06

open V06

/-- 4-byte global holding UTF-16 surrogate `0xD800` (invalid for `0..=0x10FFFF` niche ADTs). -/
def a1AllocSurrogate_06 : CapturedAllocation :=
  { allocId := 81,
    bytes := [some 0x00, some 0xD8, some 0x00, some 0x00],
    relocations := [], align := ⟨4⟩, mutability := .not }

/-- 4-byte global holding valid Unicode scalar `'A'` (`0x41`). -/
def a1AllocValidChar_06 : CapturedAllocation :=
  { allocId := 82,
    bytes := [some 0x41, some 0x00, some 0x00, some 0x00],
    relocations := [], align := ⟨4⟩, mutability := .not }

/-- `struct CharWrap(char)` with scalar `0..=0x10FFFF` layout (`charL06`). -/
def a1TyCharWrap_06 : Ty := { kind := .adt "CharWrap" [], layoutIdx := 3 }

/-- 32-bit `MaybeUninit<*const u8>`: size 4, align 4, union of (`b1PtrL32_06` at idx 2, `unitL06` at idx 0). -/
def a1MaybeUninitPtr32L_06 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }

/-- `[u8; 8]` at idx 6, `(*const u8, usize)` at idx 7, and `[u8; 16]` at idx 18. -/
def a1TupPtrUsize32L_06 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .scalarPair
      (.initialized (.pointer 0) ⟨0, 0xFFFFFFFF⟩)
      (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
    variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 4] }

def a1Arr16U8L_06 : TypeLayout :=
  { size := ⟨16⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 16, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

def a1Layouts32_06 : LayoutTable :=
  { b1Layouts32_06 with
    entries := b1Layouts32_06.entries ++ [a1MaybeUninitPtr32L_06, arr8U8L06, a1TupPtrUsize32L_06] }

def a1Layouts64_06 : LayoutTable :=
  { b1Layouts64_06 with entries := b1Layouts64_06.entries ++ [a1Arr16U8L_06] }

def a1TyMaybeUninitPtr32_06 : Ty := { kind := .adt "MaybeUninit" [], layoutIdx := 5 }

end A1Fixtures06

/-- A1 (Defect 1, `V2026_06_01`): `evalConstValue (.indirect ..)` and `evalGlobalDerefRead` enforce
`.strictUcg630Ub` relocation provenance rejection across integer scalars (`usize`, `u64`, `u8`),
`bool`, `char`, arrays, tuples, non-pointer `VariantsShape.multiple` enums (`W5`), and untyped
global reads, and reject UTF-16 surrogates (`0xD800`) on `0..=0x10FFFF` scalar-niche ADTs while
preserving coherent global pointer relocations and disjoint plain scalar bytes. -/
theorem a1_global_reloc_prov_and_surrogate_reject_v06 :
    let arrU64Ty : V06.Ty := { kind := .array (.uint .u64) 1, layoutIdx := 0 }
    let tupU64Ty : V06.Ty := { kind := .tuple [.uint .u64], layoutIdx := 0 }
    -- Positive controls: coherent pointer relocations and valid `CharWrap('A')`
    V06.evalConstValue (.indirect 50 0) tyRawPtrU8_06 [adjRelocAlloc64_06] layouts64_06 =
      some (.ptr ptr64_06 8) ∧
    V06.evalConstValue (.indirect 50 0) tyRefU8_06 [adjRelocAlloc64_06] layouts64_06 =
      some (.ptr ptr64_06 8) ∧
    V06.evalConstValue (.indirect 82 0) a1TyCharWrap_06 [a1AllocValidChar_06] layouts64_06 =
      some (.scalar ⟨0x41, 4⟩) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] a1AllocValidChar_06 0 4 []
      layouts64_06 (some a1TyCharWrap_06) = .ok (.scalar ⟨0x41, 4⟩) [] ∧
    -- Negative controls (`evalConstValue`): relocation provenance rejected on non-pointers + surrogate rejected
    V06.evalConstValue (.indirect 50 0) tyUsize_06 [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 50 0) tyU64_06 [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 50 0) tyU8_06 [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 50 0) tyBool_06 [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 50 0) tyChar_06 [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 50 0) arrU64Ty [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 50 0) tupU64Ty [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 50 0) tyEnum3_06 [adjRelocAlloc64_06] layouts64_06 = none ∧
    V06.evalConstValue (.indirect 81 0) a1TyCharWrap_06 [a1AllocSurrogate_06] layouts64_06 = none ∧
    -- Negative controls (`evalGlobalDerefRead`): relocation overlap & typed provenance/surrogate rejected with `.ub`
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_06 0 8 []
      layouts64_06 (some tyUsize_06) = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_06 0 1 []
      layouts64_06 (some tyU8_06) = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_06 0 1 []
      layouts64_06 (some tyBool_06) = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_06 0 8 []
      layouts64_06 (some arrU64Ty) = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_06 0 1 []
      layouts64_06 (some tyEnum3_06) = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_06 0 8 []
      layouts64_06 none = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] a1AllocSurrogate_06 0 4 []
      layouts64_06 (some a1TyCharWrap_06) = .ub ∧
    -- 32-bit relocation range check: offset 0 (`reloc`) faults `.ub`, offset 4 (`plain 2`) succeeds
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] b1AllocPtr32_06 0 4 []
      b1Layouts32_06 (some b1Usize32_06) = .ub ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] b1AllocPtr32_06 4 4 []
      b1Layouts32_06 (some b1Usize32_06) = .ok (.scalar ⟨2, 4⟩) [] ∧
    V06.evalConstValue (.indirect 71 0) b1Usize32_06 [b1AllocPtr32_06] b1Layouts32_06 = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- A1 (Defect 2, `V2026_06_01`): on a 32-bit target (`pointerBits = 32`), `[usize; 2]` and
`(*const u8, usize)` constants/globals decode at 4-byte element width, `evalCopyUnionBytes` copies
4-byte pointers into and out of `MaybeUninit<*const u8>` without spurious 64-bit bounds `.ub`,
`evalCopySingleDirect` (`convertCopySingleValue?`) copies `u32 -> *const u8` (without forging
provenance) and `*const u8 -> *const u32` (preserving provenance) while faulting `.ub` on
`*const u8 -> usize`, and 4-byte `copy_nonoverlapping::<u8>` of a 32-bit pointer into `usize`
faults `.ub`. -/
theorem a1_32bit_compound_union_and_single_copy_v06 :
    let arrUsize2 : V06.Ty := { kind := .array (.uint .usize) 2, layoutIdx := 0 }
    let tupUsize2 : V06.Ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 0 }
    let tupPtrUsize : V06.Ty := { kind := .tuple [.rawPtr .not (.uint .u8), .uint .usize], layoutIdx := 7 }
    let tyU32 : V06.Ty := { kind := .uint .u32, layoutIdx := 4 }
    let tyRawPtrU32 : V06.Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 2 }
    let target : V06.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    -- 1. 32-bit `[usize; 2]`, layout-free `(usize, usize)`, and captured-layout `(*const u8, usize)`
    V06.evalConstValue (.indirect 70 0) arrUsize2 [b1AllocUsize32_06] a1Layouts32_06 =
      some (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]) ∧
    V06.evalConstValue (.indirect 70 0) tupUsize2 [b1AllocUsize32_06] a1Layouts32_06 =
      some (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]) ∧
    Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead [] b1AllocUsize32_06 0 8 []
      a1Layouts32_06 (some arrUsize2) = .ok (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]) [] ∧
    V06.evalConstValue (.indirect 71 0) tupPtrUsize [b1AllocPtr32_06] a1Layouts32_06 =
      some (.aggregate 0 [.ptr ptr32_06 4, .scalar ⟨2, 4⟩]) ∧
    -- 2. 32-bit `evalCopyUnionBytes` (`*const u8` -> `MaybeUninit<*const u8>` -> `*const u8`)
    --    and `evalCopySingleDirect` (`u32 -> *const u8`, `*const u8 -> *const u32`, `*const u8 -> usize`)
    (let decls : List V06.LocalDecl := [
       { mutability := .not, ty := tyU8_06, debugName := none },                                        -- 0: backing u8
       { mutability := .not, ty := b1RawPtr32_06, debugName := none },                                   -- 1: src *const u8 (ptr)
       { mutability := .mut, ty := a1TyMaybeUninitPtr32_06, debugName := none },                         -- 2: union MaybeUninit<*const u8>
       { mutability := .mut, ty := b1RawPtr32_06, debugName := none },                                   -- 3: dst *const u8
       { mutability := .not, ty := tyU32, debugName := none },                                           -- 4: src u32 = 0x1234
       { mutability := .mut, ty := tyRawPtrU32, debugName := none },                                     -- 5: dst *const u32
       { mutability := .mut, ty := b1Usize32_06, debugName := none },                                    -- 6: dst usize
       { mutability := .not, ty := { kind := .rawPtr .not b1RawPtr32_06.kind, layoutIdx := 2 }, debugName := none }, -- 7: &1 (*const *const u8)
       { mutability := .not, ty := { kind := .rawPtr .mut b1RawPtr32_06.kind, layoutIdx := 2 }, debugName := none }, -- 8: &mut 2 as *mut *const u8
       { mutability := .not, ty := { kind := .rawPtr .not b1RawPtr32_06.kind, layoutIdx := 2 }, debugName := none }, -- 9: &2 as *const *const u8
       { mutability := .not, ty := { kind := .rawPtr .mut b1RawPtr32_06.kind, layoutIdx := 2 }, debugName := none }, -- 10: &mut 3 (*mut *const u8)
       { mutability := .not, ty := { kind := .rawPtr .not tyU32.kind, layoutIdx := 2 }, debugName := none },         -- 11: &4 (*const u32)
       { mutability := .not, ty := { kind := .rawPtr .mut tyRawPtrU32.kind, layoutIdx := 2 }, debugName := none },   -- 12: &mut 5 (*mut *const u32)
       { mutability := .not, ty := { kind := .rawPtr .mut b1Usize32_06.kind, layoutIdx := 2 }, debugName := none },  -- 13: &mut 6 (*mut usize)
       { mutability := .not, ty := b1RawPtr32_06, debugName := none },                                   -- 14: &1 as *const u8
       { mutability := .not, ty := b1MutPtr32_06, debugName := none }]                                   -- 15: &mut 6 as *mut u8
     let locals : List V06.LocalSlot := [
       .init (.scalar ⟨0x77, 1⟩),
       .init (.ptr target 4),
       .init (.aggregate 0 [.unit, .unit]),
       .uninit,
       .init (.scalar ⟨0x1234, 4⟩),
       .uninit,
       .uninit,
       .init (.ptr { allocId := 10, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 13, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 14, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 15, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 16, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 17, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 18, offsetBytes := 0 } 4)]
     let mem : V06.Memory :=
       { V06.emptyMemory with
         borrows := [
           b1Frozen_06 1 0, b1Frozen_06 10 1, b1Active_06 11 2, b1Frozen_06 12 2,
           b1Active_06 13 3, b1Frozen_06 14 4, b1Active_06 15 5, b1Active_06 16 6,
           b1Frozen_06 17 1, b1Active_06 18 6] }
     let st : V06.MachineState := mkState06 locals mem
     let c1 := b1Count_06 1 4 b1Usize32_06
     let c4 := b1Count_06 4 4 b1Usize32_06
     -- Union roundtrip (`evalCopyUnionBytes` at 32-bit): 1 -> 2 -> 3 preserves `target` provenance
     b1ReadAfter_06 decls a1Layouts32_06 st [b1Copy_06 7 8 c1, b1Copy_06 9 10 c1] ⟨3, []⟩ =
       some (.ok (.ptr target 4) []) ∧
     b1ReadAfter_06 decls a1Layouts32_06 st [b1Copy_06 7 8 c1, b1Copy_06 9 10 c1] ⟨3, [.deref]⟩ =
       some (.ok (.scalar ⟨0x77, 1⟩) []) ∧
     -- Single-element direct (`convertCopySingleValue?` at 32-bit): u32 -> *const u8 & *const u8 -> *const u32
     b1ReadAfter_06 decls a1Layouts32_06 st [b1Copy_06 11 10 c1] ⟨3, []⟩ =
       some (.ok (.scalar ⟨0x1234, 4⟩) []) ∧
     b1ReadAfter_06 decls a1Layouts32_06 st [b1Copy_06 7 12 c1] ⟨5, []⟩ =
       some (.ok (.ptr target 4) []) ∧
     -- Single-element direct `*const u8 -> usize` and 4-byte u8 copy `*const u8 -> usize` both fault `.ub`
     IsUbStep06 (V06.evalStmt st (b1Copy_06 7 13 c1) decls a1Layouts32_06) ∧
     IsUbStep06 (V06.evalStmt st (b1Copy_06 14 15 c4) decls a1Layouts32_06)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- A1 (Defect 3, `V2026_06_01`): `copyBytesSubplace` supports bytewise `copy_nonoverlapping::<u8>`
round-trips of wide pointers (`&[u8]` at both 64-bit 16B and 32-bit 8B, plus `&dyn T` with dual
data+vtable provenance), while partial 1-byte overwrites succeed at write time (`Kani#5205`) and
strip provenance on `*const [u8]` (`.scalar` data half) or fault `.ub` when `&[u8]` / `&dyn T` is
read. -/
theorem a1_wide_ptr_bytewise_copy_and_partial_overwrite_v06 :
    let target : V06.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    -- 1. 64-bit wide pointers (`&[u8]`, `*const [u8]`, `&dyn T`)
    (let decls64 : List V06.LocalDecl := [
       { mutability := .not, ty := tyU8_06, debugName := none },                                 -- 0: zero u8 = 0
       { mutability := .not, ty := tyRefSliceU8_06, debugName := none },                         -- 1: src &[u8]
       { mutability := .mut, ty := { kind := .array (.uint .u8) 16, layoutIdx := 18 }, debugName := none }, -- 2: [u8; 16]
       { mutability := .mut, ty := tyRefSliceU8_06, debugName := none },                         -- 3: dst &[u8]
       { mutability := .mut, ty := tyRawSliceU8_06, debugName := none },                         -- 4: mut *const [u8]
       { mutability := .not, ty := tyRefDyn_06, debugName := none },                             -- 5: src &dyn T
       { mutability := .mut, ty := tyRefDyn_06, debugName := none },                             -- 6: dst &dyn T
       { mutability := .not, ty := tyRawPtrU8_06, debugName := none },                           -- 7: &0 (*const u8)
       { mutability := .not, ty := tyRawPtrU8_06, debugName := none },                           -- 8: &1 as *const u8
       { mutability := .not, ty := tyMutPtrU8_06, debugName := none },                           -- 9: &mut 2 as *mut u8
       { mutability := .not, ty := tyMutPtrU8_06, debugName := none },                           -- 10: &mut 3 as *mut u8
       { mutability := .not, ty := tyMutPtrU8_06, debugName := none },                           -- 11: &mut 4 as *mut u8
       { mutability := .not, ty := tyRawPtrU8_06, debugName := none },                           -- 12: &5 as *const u8
       { mutability := .not, ty := tyMutPtrU8_06, debugName := none }]                           -- 13: &mut 6 as *mut u8
     let sliceVal : V06.Value := .aggregate 0 [.ptr target 8, .scalar ⟨3, 8⟩]
     let dynVal : V06.Value := .aggregate 0 [.ptr target 8, .ptr vtPtr64_06 8]
     let locals64 : List V06.LocalSlot := [
       .init (.scalar ⟨0, 1⟩),
       .init sliceVal,
       .init (.aggregate 0 (List.replicate 16 (.scalar ⟨0, 1⟩))),
       .init sliceVal,
       .init sliceVal,
       .init dynVal,
       .uninit,
       .init (.ptr { allocId := 10, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 12, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 13, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 14, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 15, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 16, offsetBytes := 0 } 8)]
     let mem64 : V06.Memory :=
       { V06.emptyMemory with
         borrows := [
           b1Frozen_06 1 0, b1Frozen_06 10 0, b1Frozen_06 11 1, b1Active_06 12 2,
           b1Active_06 13 3, b1Active_06 14 4, b1Frozen_06 15 5, b1Active_06 16 6] }
     let st64 : V06.MachineState := mkState06 locals64 mem64
     let c1 := b1Count_06 1 8 tyUsize_06
     let c16 := b1Count_06 16 8 tyUsize_06
     -- Full 16B bytewise roundtrip of `&[u8]` through `[u8; 16]` and direct 16B copy of `&dyn T`
     b1ReadAfter_06 decls64 a1Layouts64_06 st64 [b1Copy_06 8 9 c16, b1Copy_06 9 10 c16] ⟨3, []⟩ =
       some (.ok sliceVal []) ∧
     b1ReadAfter_06 decls64 a1Layouts64_06 st64 [b1Copy_06 12 13 c16] ⟨6, []⟩ =
       some (.ok dynVal []) ∧
     -- Partial 1-byte overwrite: `*const [u8]` strips data provenance; `&[u8]` and `&dyn T` defer UB to read!
     (b1Run_06 decls64 a1Layouts64_06 st64 [b1Copy_06 7 10 c1]).isSome = true ∧
     b1ReadAfter_06 decls64 a1Layouts64_06 st64 [b1Copy_06 7 10 c1] ⟨3, []⟩ = some .ub ∧
     b1ReadAfter_06 decls64 a1Layouts64_06 st64 [b1Copy_06 7 11 c1] ⟨4, []⟩ =
       some (.ok (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨3, 8⟩]) []) ∧
     (b1Run_06 decls64 a1Layouts64_06 st64 [b1Copy_06 12 13 c16, b1Copy_06 7 13 c1]).isSome = true ∧
     b1ReadAfter_06 decls64 a1Layouts64_06 st64 [b1Copy_06 12 13 c16, b1Copy_06 7 13 c1] ⟨6, []⟩ =
       some .ub) ∧
    -- 2. 32-bit 8B wide pointer `&[u8]` bytewise copy
    (let tyRefSlice32 : V06.Ty := { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
     let decls32 : List V06.LocalDecl := [
       { mutability := .not, ty := tyU8_06, debugName := none },
       { mutability := .not, ty := tyRefSlice32, debugName := none },
       { mutability := .mut, ty := tyRefSlice32, debugName := none },
       { mutability := .not, ty := b1RawPtr32_06, debugName := none },
       { mutability := .not, ty := b1MutPtr32_06, debugName := none }]
     let sliceVal32 : V06.Value := .aggregate 0 [.ptr target 4, .scalar ⟨3, 4⟩]
     let locals32 : List V06.LocalSlot := [
       .init (.scalar ⟨0xAA, 1⟩), .init sliceVal32, .uninit,
       .init (.ptr { allocId := 10, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 4)]
     let mem32 : V06.Memory :=
       { V06.emptyMemory with borrows := [b1Frozen_06 1 0, b1Frozen_06 10 1, b1Active_06 11 2] }
     let st32 : V06.MachineState := mkState06 locals32 mem32
     let c8 := b1Count_06 8 4 b1Usize32_06
     b1ReadAfter_06 decls32 a1Layouts32_06 st32 [b1Copy_06 3 4 c8] ⟨2, []⟩ =
       some (.ok sliceVal32 [])) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

section A1Fixtures08

open V08

def a1AllocSurrogate_08 : CapturedAllocation :=
  { allocId := 81,
    bytes := [some 0x00, some 0xD8, some 0x00, some 0x00],
    relocations := [], align := ⟨4⟩, mutability := .not }

def a1AllocValidChar_08 : CapturedAllocation :=
  { allocId := 82,
    bytes := [some 0x41, some 0x00, some 0x00, some 0x00],
    relocations := [], align := ⟨4⟩, mutability := .not }

def a1TyCharWrap_08 : Ty := { kind := .adt "CharWrap" [], layoutIdx := 3 }

def a1MaybeUninitPtr32L_08 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩, backendRepr := .memory,
    fields := .union 2, variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 0] }

def a1TupPtrUsize32L_08 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨4⟩,
    backendRepr := .scalarPair
      (.initialized (.pointer 0) ⟨0, 0xFFFFFFFF⟩)
      (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .arbitrary [⟨0⟩, ⟨4⟩] [0, 1],
    variants := .single 0, isUninhabited := false,
    fieldLayouts := [2, 4] }

def a1Arr16U8L_08 : TypeLayout :=
  { size := ⟨16⟩, align := ⟨1⟩, backendRepr := .memory,
    fields := .array ⟨1⟩ 16, variants := .single 0, isUninhabited := false,
    fieldLayouts := [1] }

def a1Layouts32_08 : LayoutTable :=
  { b1Layouts32_08 with
    entries := b1Layouts32_08.entries ++ [a1MaybeUninitPtr32L_08, arr8U8L08, a1TupPtrUsize32L_08] }

def a1Layouts64_08 : LayoutTable :=
  { b1Layouts64_08 with entries := b1Layouts64_08.entries ++ [a1Arr16U8L_08] }

def a1TyMaybeUninitPtr32_08 : Ty := { kind := .adt "MaybeUninit" [], layoutIdx := 5 }

end A1Fixtures08

/-- A1 (Defect 1, `V2026_08_01`): `V2026_08_01` counterpart of
`a1_global_reloc_prov_and_surrogate_reject_v06`. -/
theorem a1_global_reloc_prov_and_surrogate_reject_v08 :
    let arrU64Ty : V08.Ty := { kind := .array (.uint .u64) 1, layoutIdx := 0 }
    let tupU64Ty : V08.Ty := { kind := .tuple [.uint .u64], layoutIdx := 0 }
    V08.evalConstValue (.indirect 50 0) tyRawPtrU8_08 [adjRelocAlloc64_08] layouts64_08 =
      some (.ptr ptr64_08 8) ∧
    V08.evalConstValue (.indirect 50 0) tyRefU8_08 [adjRelocAlloc64_08] layouts64_08 =
      some (.ptr ptr64_08 8) ∧
    V08.evalConstValue (.indirect 82 0) a1TyCharWrap_08 [a1AllocValidChar_08] layouts64_08 =
      some (.scalar ⟨0x41, 4⟩) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] a1AllocValidChar_08 0 4 []
      layouts64_08 (some a1TyCharWrap_08) = .ok (.scalar ⟨0x41, 4⟩) [] ∧
    V08.evalConstValue (.indirect 50 0) tyUsize_08 [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 50 0) tyU64_08 [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 50 0) tyU8_08 [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 50 0) tyBool_08 [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 50 0) tyChar_08 [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 50 0) arrU64Ty [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 50 0) tupU64Ty [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 50 0) tyEnum3_08 [adjRelocAlloc64_08] layouts64_08 = none ∧
    V08.evalConstValue (.indirect 81 0) a1TyCharWrap_08 [a1AllocSurrogate_08] layouts64_08 = none ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_08 0 8 []
      layouts64_08 (some tyUsize_08) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_08 0 1 []
      layouts64_08 (some tyU8_08) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_08 0 1 []
      layouts64_08 (some tyBool_08) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_08 0 8 []
      layouts64_08 (some arrU64Ty) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_08 0 1 []
      layouts64_08 (some tyEnum3_08) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] adjRelocAlloc64_08 0 8 []
      layouts64_08 none = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] a1AllocSurrogate_08 0 4 []
      layouts64_08 (some a1TyCharWrap_08) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] b1AllocPtr32_08 0 4 []
      b1Layouts32_08 (some b1Usize32_08) = .ub ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] b1AllocPtr32_08 4 4 []
      b1Layouts32_08 (some b1Usize32_08) = .ok (.scalar ⟨2, 4⟩) [] ∧
    V08.evalConstValue (.indirect 71 0) b1Usize32_08 [b1AllocPtr32_08] b1Layouts32_08 = none := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- A1 (Defect 2, `V2026_08_01`): `V2026_08_01` counterpart of
`a1_32bit_compound_union_and_single_copy_v06`. -/
theorem a1_32bit_compound_union_and_single_copy_v08 :
    let arrUsize2 : V08.Ty := { kind := .array (.uint .usize) 2, layoutIdx := 0 }
    let tupUsize2 : V08.Ty := { kind := .tuple [.uint .usize, .uint .usize], layoutIdx := 0 }
    let tupPtrUsize : V08.Ty := { kind := .tuple [.rawPtr .not (.uint .u8), .uint .usize], layoutIdx := 7 }
    let tyU32 : V08.Ty := { kind := .uint .u32, layoutIdx := 4 }
    let tyRawPtrU32 : V08.Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 2 }
    let target : V08.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    V08.evalConstValue (.indirect 70 0) arrUsize2 [b1AllocUsize32_08] a1Layouts32_08 =
      some (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]) ∧
    V08.evalConstValue (.indirect 70 0) tupUsize2 [b1AllocUsize32_08] a1Layouts32_08 =
      some (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]) ∧
    Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead [] b1AllocUsize32_08 0 8 []
      a1Layouts32_08 (some arrUsize2) = .ok (.aggregate 0 [.scalar ⟨1, 4⟩, .scalar ⟨2, 4⟩]) [] ∧
    V08.evalConstValue (.indirect 71 0) tupPtrUsize [b1AllocPtr32_08] a1Layouts32_08 =
      some (.aggregate 0 [.ptr ptr32_08 4, .scalar ⟨2, 4⟩]) ∧
    (let decls : List V08.LocalDecl := [
       { mutability := .not, ty := tyU8_08, debugName := none },
       { mutability := .not, ty := b1RawPtr32_08, debugName := none },
       { mutability := .mut, ty := a1TyMaybeUninitPtr32_08, debugName := none },
       { mutability := .mut, ty := b1RawPtr32_08, debugName := none },
       { mutability := .not, ty := tyU32, debugName := none },
       { mutability := .mut, ty := tyRawPtrU32, debugName := none },
       { mutability := .mut, ty := b1Usize32_08, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not b1RawPtr32_08.kind, layoutIdx := 2 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .mut b1RawPtr32_08.kind, layoutIdx := 2 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not b1RawPtr32_08.kind, layoutIdx := 2 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .mut b1RawPtr32_08.kind, layoutIdx := 2 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .not tyU32.kind, layoutIdx := 2 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .mut tyRawPtrU32.kind, layoutIdx := 2 }, debugName := none },
       { mutability := .not, ty := { kind := .rawPtr .mut b1Usize32_08.kind, layoutIdx := 2 }, debugName := none },
       { mutability := .not, ty := b1RawPtr32_08, debugName := none },
       { mutability := .not, ty := b1MutPtr32_08, debugName := none }]
     let locals : List V08.LocalSlot := [
       .init (.scalar ⟨0x77, 1⟩),
       .init (.ptr target 4),
       .init (.aggregate 0 [.unit, .unit]),
       .uninit,
       .init (.scalar ⟨0x1234, 4⟩),
       .uninit,
       .uninit,
       .init (.ptr { allocId := 10, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 13, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 14, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 15, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 16, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 17, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 18, offsetBytes := 0 } 4)]
     let mem : V08.Memory :=
       { V08.emptyMemory with
         borrows := [
           b1Frozen_08 1 0, b1Frozen_08 10 1, b1Active_08 11 2, b1Frozen_08 12 2,
           b1Active_08 13 3, b1Frozen_08 14 4, b1Active_08 15 5, b1Active_08 16 6,
           b1Frozen_08 17 1, b1Active_08 18 6] }
     let st : V08.MachineState := mkState08 locals mem
     let c1 := b1Count_08 1 4 b1Usize32_08
     let c4 := b1Count_08 4 4 b1Usize32_08
     b1ReadAfter_08 decls a1Layouts32_08 st [b1Copy_08 7 8 c1, b1Copy_08 9 10 c1] ⟨3, []⟩ =
       some (.ok (.ptr target 4) []) ∧
     b1ReadAfter_08 decls a1Layouts32_08 st [b1Copy_08 7 8 c1, b1Copy_08 9 10 c1] ⟨3, [.deref]⟩ =
       some (.ok (.scalar ⟨0x77, 1⟩) []) ∧
     b1ReadAfter_08 decls a1Layouts32_08 st [b1Copy_08 11 10 c1] ⟨3, []⟩ =
       some (.ok (.scalar ⟨0x1234, 4⟩) []) ∧
     b1ReadAfter_08 decls a1Layouts32_08 st [b1Copy_08 7 12 c1] ⟨5, []⟩ =
       some (.ok (.ptr target 4) []) ∧
     IsUbStep08 (V08.evalStmt st (b1Copy_08 7 13 c1) decls a1Layouts32_08) ∧
     IsUbStep08 (V08.evalStmt st (b1Copy_08 14 15 c4) decls a1Layouts32_08)) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- A1 (Defect 3, `V2026_08_01`): `V2026_08_01` counterpart of
`a1_wide_ptr_bytewise_copy_and_partial_overwrite_v06`. -/
theorem a1_wide_ptr_bytewise_copy_and_partial_overwrite_v08 :
    let target : V08.ProvenancePtr := { allocId := 1, offsetBytes := 0 }
    (let decls64 : List V08.LocalDecl := [
       { mutability := .not, ty := tyU8_08, debugName := none },
       { mutability := .not, ty := tyRefSliceU8_08, debugName := none },
       { mutability := .mut, ty := { kind := .array (.uint .u8) 16, layoutIdx := 18 }, debugName := none },
       { mutability := .mut, ty := tyRefSliceU8_08, debugName := none },
       { mutability := .mut, ty := tyRawSliceU8_08, debugName := none },
       { mutability := .not, ty := tyRefDyn_08, debugName := none },
       { mutability := .mut, ty := tyRefDyn_08, debugName := none },
       { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
       { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
       { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
       { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
       { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
       { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
       { mutability := .not, ty := tyMutPtrU8_08, debugName := none }]
     let sliceVal : V08.Value := .aggregate 0 [.ptr target 8, .scalar ⟨3, 8⟩]
     let dynVal : V08.Value := .aggregate 0 [.ptr target 8, .ptr vtPtr64_08 8]
     let locals64 : List V08.LocalSlot := [
       .init (.scalar ⟨0, 1⟩),
       .init sliceVal,
       .init (.aggregate 0 (List.replicate 16 (.scalar ⟨0, 1⟩))),
       .init sliceVal,
       .init sliceVal,
       .init dynVal,
       .uninit,
       .init (.ptr { allocId := 10, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 12, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 13, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 14, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 15, offsetBytes := 0 } 8),
       .init (.ptr { allocId := 16, offsetBytes := 0 } 8)]
     let mem64 : V08.Memory :=
       { V08.emptyMemory with
         borrows := [
           b1Frozen_08 1 0, b1Frozen_08 10 0, b1Frozen_08 11 1, b1Active_08 12 2,
           b1Active_08 13 3, b1Active_08 14 4, b1Frozen_08 15 5, b1Active_08 16 6] }
     let st64 : V08.MachineState := mkState08 locals64 mem64
     let c1 := b1Count_08 1 8 tyUsize_08
     let c16 := b1Count_08 16 8 tyUsize_08
     b1ReadAfter_08 decls64 a1Layouts64_08 st64 [b1Copy_08 8 9 c16, b1Copy_08 9 10 c16] ⟨3, []⟩ =
       some (.ok sliceVal []) ∧
     b1ReadAfter_08 decls64 a1Layouts64_08 st64 [b1Copy_08 12 13 c16] ⟨6, []⟩ =
       some (.ok dynVal []) ∧
     (b1Run_08 decls64 a1Layouts64_08 st64 [b1Copy_08 7 10 c1]).isSome = true ∧
     b1ReadAfter_08 decls64 a1Layouts64_08 st64 [b1Copy_08 7 10 c1] ⟨3, []⟩ = some .ub ∧
     b1ReadAfter_08 decls64 a1Layouts64_08 st64 [b1Copy_08 7 11 c1] ⟨4, []⟩ =
       some (.ok (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨3, 8⟩]) []) ∧
     (b1Run_08 decls64 a1Layouts64_08 st64 [b1Copy_08 12 13 c16, b1Copy_08 7 13 c1]).isSome = true ∧
     b1ReadAfter_08 decls64 a1Layouts64_08 st64 [b1Copy_08 12 13 c16, b1Copy_08 7 13 c1] ⟨6, []⟩ =
       some .ub) ∧
    (let tyRefSlice32 : V08.Ty := { kind := .ref .not (.slice (.uint .u8)), layoutIdx := 0 }
     let decls32 : List V08.LocalDecl := [
       { mutability := .not, ty := tyU8_08, debugName := none },
       { mutability := .not, ty := tyRefSlice32, debugName := none },
       { mutability := .mut, ty := tyRefSlice32, debugName := none },
       { mutability := .not, ty := b1RawPtr32_08, debugName := none },
       { mutability := .not, ty := b1MutPtr32_08, debugName := none }]
     let sliceVal32 : V08.Value := .aggregate 0 [.ptr target 4, .scalar ⟨3, 4⟩]
     let locals32 : List V08.LocalSlot := [
       .init (.scalar ⟨0xAA, 1⟩), .init sliceVal32, .uninit,
       .init (.ptr { allocId := 10, offsetBytes := 0 } 4),
       .init (.ptr { allocId := 11, offsetBytes := 0 } 4)]
     let mem32 : V08.Memory :=
       { V08.emptyMemory with borrows := [b1Frozen_08 1 0, b1Frozen_08 10 1, b1Active_08 11 2] }
     let st32 : V08.MachineState := mkState08 locals32 mem32
     let c8 := b1Count_08 8 4 b1Usize32_08
     b1ReadAfter_08 decls32 a1Layouts32_08 st32 [b1Copy_08 3 4 c8] ⟨2, []⟩ =
       some (.ok sliceVal32 [])) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- A1 lockstep parity across `V2026_06_01` and `V2026_08_01` for `globalRelocsOverlapRange`,
`isPtrCopyKind`, global relocation rejection, surrogate rejection, and 32-bit compound decoding. -/
theorem a1_lockstep_parity :
    let b06 : List Bool := [
      Trusted.Rustc.V2026_06_01.MirSemantics.globalRelocsOverlapRange b1AllocPtr32_06.relocations 0 1 4,
      Trusted.Rustc.V2026_06_01.MirSemantics.globalRelocsOverlapRange b1AllocPtr32_06.relocations 3 1 4,
      Trusted.Rustc.V2026_06_01.MirSemantics.globalRelocsOverlapRange b1AllocPtr32_06.relocations 4 4 4,
      Trusted.Rustc.V2026_06_01.MirSemantics.isPtrCopyKind tyRefSliceU8_06.kind,
      Trusted.Rustc.V2026_06_01.MirSemantics.isPtrCopyKind tyRefDyn_06.kind,
      Trusted.Rustc.V2026_06_01.MirSemantics.isPtrCopyKind tyUsize_06.kind]
    let b08 : List Bool := [
      Trusted.Rustc.V2026_08_01.MirSemantics.globalRelocsOverlapRange b1AllocPtr32_08.relocations 0 1 4,
      Trusted.Rustc.V2026_08_01.MirSemantics.globalRelocsOverlapRange b1AllocPtr32_08.relocations 3 1 4,
      Trusted.Rustc.V2026_08_01.MirSemantics.globalRelocsOverlapRange b1AllocPtr32_08.relocations 4 4 4,
      Trusted.Rustc.V2026_08_01.MirSemantics.isPtrCopyKind tyRefSliceU8_08.kind,
      Trusted.Rustc.V2026_08_01.MirSemantics.isPtrCopyKind tyRefDyn_08.kind,
      Trusted.Rustc.V2026_08_01.MirSemantics.isPtrCopyKind tyUsize_08.kind]
    let v06 : List ValSummary := [
      valSummary06 (V06.evalConstValue (.indirect 50 0) tyUsize_06 [adjRelocAlloc64_06] layouts64_06),
      valSummary06 (V06.evalConstValue (.indirect 50 0) tyEnum3_06 [adjRelocAlloc64_06] layouts64_06),
      valSummary06 (V06.evalConstValue (.indirect 81 0) a1TyCharWrap_06 [a1AllocSurrogate_06] layouts64_06),
      valSummary06 (V06.evalConstValue (.indirect 70 0) { kind := .array (.uint .usize) 2, layoutIdx := 0 } [b1AllocUsize32_06] a1Layouts32_06),
      valSummary06 (V06.evalConstValue (.indirect 71 0) { kind := .tuple [.rawPtr .not (.uint .u8), .uint .usize], layoutIdx := 7 } [b1AllocPtr32_06] a1Layouts32_06)]
    let v08 : List ValSummary := [
      valSummary08 (V08.evalConstValue (.indirect 50 0) tyUsize_08 [adjRelocAlloc64_08] layouts64_08),
      valSummary08 (V08.evalConstValue (.indirect 50 0) tyEnum3_08 [adjRelocAlloc64_08] layouts64_08),
      valSummary08 (V08.evalConstValue (.indirect 81 0) a1TyCharWrap_08 [a1AllocSurrogate_08] layouts64_08),
      valSummary08 (V08.evalConstValue (.indirect 70 0) { kind := .array (.uint .usize) 2, layoutIdx := 0 } [b1AllocUsize32_08] a1Layouts32_08),
      valSummary08 (V08.evalConstValue (.indirect 71 0) { kind := .tuple [.rawPtr .not (.uint .u8), .uint .usize], layoutIdx := 7 } [b1AllocPtr32_08] a1Layouts32_08)]
    b06 = b08 ∧ b06 = [true, true, false, true, true, false] ∧
    v06 = v08 ∧
    v06 = [.none, .none, .none,
      .agg 0 [.scalar 1 4, .scalar 2 4],
      .agg 0 [.ptr 9 0x10 4, .scalar 2 4]] := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## §4c. `[adv ep1-B2]` Wide-Pointer Byte-Permutation Regressions

End-to-end `copy_nonoverlapping::<u8>` permutations of wide pointers (A1's new
`copyBytesSubplace` / `decodeUntypedStorageBytes` wide-pointer paths): swapping the data and
metadata halves of `&[u8]` / `*const [u8]`, swapping two data bytes, sourcing a `&dyn` vtable half
from plain slice-length bytes, assembling a `&[u8]` from its halves in either order (and from a
duplicated metadata half), and pinning the Brief §1.5 W5 / §3.1(h) policy that an untyped copy of
pointer bytes into `u64` storage faults under `.strictUcg630Ub`. -/

section B2Fixtures06

open V06

def b2Target_06 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
def b2SliceVal_06 : Value := .aggregate 0 [.ptr b2Target_06 8, .scalar ⟨3, 8⟩]
def b2DynVal_06 : Value := .aggregate 0 [.ptr b2Target_06 8, .ptr vtPtr64_06 8]

/-- Locals: `0` src `&[u8]`, `1` dst `&[u8]`, `2` dst `*const [u8]`, `3` src `&dyn T`,
`4` dst `&dyn T`, `5`/`6`/`7` = `&0` at byte `0`/`8`/`1`, `8`/`9`/`10` = `&mut 1` at `0`/`8`/`1`,
`11`/`12` = `&mut 2` at `0`/`8`, `13`/`14` = `&3` at `0`/`8`, `15`/`16` = `&mut 4` at `0`/`8`,
`17` dst `u64`, `18` = `&mut 17`, `19` uninit dst `&[u8]`, `20`/`21` = `&mut 19` at `0`/`8`. -/
def b2Decls_06 : List LocalDecl :=
  [{ mutability := .not, ty := tyRefSliceU8_06, debugName := none },
   { mutability := .mut, ty := tyRefSliceU8_06, debugName := none },
   { mutability := .mut, ty := tyRawSliceU8_06, debugName := none },
   { mutability := .not, ty := tyRefDyn_06, debugName := none },
   { mutability := .mut, ty := tyRefDyn_06, debugName := none }] ++
  List.replicate 3 { mutability := .not, ty := tyRawPtrU8_06, debugName := none } ++
  List.replicate 5 { mutability := .not, ty := tyMutPtrU8_06, debugName := none } ++
  List.replicate 2 { mutability := .not, ty := tyRawPtrU8_06, debugName := none } ++
  List.replicate 2 { mutability := .not, ty := tyMutPtrU8_06, debugName := none } ++
  [{ mutability := .mut, ty := tyU64_06, debugName := none },
   { mutability := .not, ty := tyMutPtrU8_06, debugName := none },
   { mutability := .mut, ty := tyRefSliceU8_06, debugName := none },
   { mutability := .not, ty := tyMutPtrU8_06, debugName := none },
   { mutability := .not, ty := tyMutPtrU8_06, debugName := none }]

def b2P_06 (a o : Nat) : LocalSlot := .init (.ptr { allocId := a, offsetBytes := o } 8)

def b2State_06 : MachineState :=
  mkState06
    ([.init b2SliceVal_06, .init b2SliceVal_06, .init b2SliceVal_06, .init b2DynVal_06,
      .init b2DynVal_06, b2P_06 10 0, b2P_06 10 8, b2P_06 10 1, b2P_06 11 0, b2P_06 11 8,
      b2P_06 11 1, b2P_06 12 0, b2P_06 12 8, b2P_06 13 0, b2P_06 13 8, b2P_06 14 0, b2P_06 14 8,
      .init (.scalar ⟨0, 8⟩), b2P_06 15 0, .uninit, b2P_06 16 0, b2P_06 16 8])
    { emptyMemory with
      borrows := [b1Frozen_06 10 0, b1Active_06 11 1, b1Active_06 12 2, b1Frozen_06 13 3,
        b1Active_06 14 4, b1Active_06 15 17, b1Active_06 16 19] }

def b2C_06 (n : Nat) : Operand := b1Count_06 n 8 tyUsize_06

def b2Read_06 (stmts : List Statement) (p : Place) : Option PlaceReadResult :=
  b1ReadAfter_06 b2Decls_06 a1Layouts64_06 b2State_06 stmts p

end B2Fixtures06

/-- B2 (§3.1(e) end to end through bytewise copies, `V2026_06_01`): swapping the data and length
halves of `&[u8]` or `*const [u8]` faults (the length half now carries pointer provenance); a
data-byte `0`/`1` swap faults for `&[u8]` and strips provenance for `*const [u8]`; a plain
length half copied into a `&dyn T` vtable half faults; a `&[u8]` assembled from its halves in
either order is the original value, while a lone data half or a duplicated length half faults;
an untyped copy of pointer bytes into `u64` storage faults under `.strictUcg630Ub` (W5). -/
theorem b2_wide_ptr_byte_permutations_v06 :
    b2Read_06 [b1Copy_06 5 8 (b2C_06 16)] ⟨1, []⟩ = some (.ok b2SliceVal_06 []) ∧
    b2Read_06 [b1Copy_06 5 9 (b2C_06 8), b1Copy_06 6 8 (b2C_06 8)] ⟨1, []⟩ = some .ub ∧
    b2Read_06 [b1Copy_06 5 12 (b2C_06 8), b1Copy_06 6 11 (b2C_06 8)] ⟨2, []⟩ = some .ub ∧
    b2Read_06 [b1Copy_06 5 8 (b2C_06 16), b1Copy_06 7 8 (b2C_06 1), b1Copy_06 5 10 (b2C_06 1)]
      ⟨1, []⟩ = some .ub ∧
    b2Read_06 [b1Copy_06 5 11 (b2C_06 16), b1Copy_06 7 11 (b2C_06 1)] ⟨2, []⟩ =
      some (.ok (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨3, 8⟩]) []) ∧
    b2Read_06 [b1Copy_06 6 16 (b2C_06 8)] ⟨4, []⟩ = some .ub ∧
    b2Read_06 [b1Copy_06 13 15 (b2C_06 8)] ⟨4, []⟩ = some (.ok b2DynVal_06 []) ∧
    b2Read_06 [b1Copy_06 5 20 (b2C_06 8)] ⟨19, []⟩ = some .ub ∧
    b2Read_06 [b1Copy_06 5 20 (b2C_06 8), b1Copy_06 6 21 (b2C_06 8)] ⟨19, []⟩ =
      some (.ok b2SliceVal_06 []) ∧
    b2Read_06 [b1Copy_06 6 21 (b2C_06 8), b1Copy_06 5 20 (b2C_06 8)] ⟨19, []⟩ =
      some (.ok b2SliceVal_06 []) ∧
    b2Read_06 [b1Copy_06 6 20 (b2C_06 8), b1Copy_06 6 21 (b2C_06 8)] ⟨19, []⟩ = some .ub ∧
    IsUbStep06 (V06.evalStmt b2State_06 (b1Copy_06 13 18 (b2C_06 8)) b2Decls_06 a1Layouts64_06) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

section B2Fixtures08

open V08

def b2Target_08 : ProvenancePtr := { allocId := 1, offsetBytes := 0 }
def b2SliceVal_08 : Value := .aggregate 0 [.ptr b2Target_08 8, .scalar ⟨3, 8⟩]
def b2DynVal_08 : Value := .aggregate 0 [.ptr b2Target_08 8, .ptr vtPtr64_08 8]

/-- Locals: `0` src `&[u8]`, `1` dst `&[u8]`, `2` dst `*const [u8]`, `3` src `&dyn T`,
`4` dst `&dyn T`, `5`/`6`/`7` = `&0` at byte `0`/`8`/`1`, `8`/`9`/`10` = `&mut 1` at `0`/`8`/`1`,
`11`/`12` = `&mut 2` at `0`/`8`, `13`/`14` = `&3` at `0`/`8`, `15`/`16` = `&mut 4` at `0`/`8`,
`17` dst `u64`, `18` = `&mut 17`, `19` uninit dst `&[u8]`, `20`/`21` = `&mut 19` at `0`/`8`. -/
def b2Decls_08 : List LocalDecl :=
  [{ mutability := .not, ty := tyRefSliceU8_08, debugName := none },
   { mutability := .mut, ty := tyRefSliceU8_08, debugName := none },
   { mutability := .mut, ty := tyRawSliceU8_08, debugName := none },
   { mutability := .not, ty := tyRefDyn_08, debugName := none },
   { mutability := .mut, ty := tyRefDyn_08, debugName := none }] ++
  List.replicate 3 { mutability := .not, ty := tyRawPtrU8_08, debugName := none } ++
  List.replicate 5 { mutability := .not, ty := tyMutPtrU8_08, debugName := none } ++
  List.replicate 2 { mutability := .not, ty := tyRawPtrU8_08, debugName := none } ++
  List.replicate 2 { mutability := .not, ty := tyMutPtrU8_08, debugName := none } ++
  [{ mutability := .mut, ty := tyU64_08, debugName := none },
   { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
   { mutability := .mut, ty := tyRefSliceU8_08, debugName := none },
   { mutability := .not, ty := tyMutPtrU8_08, debugName := none },
   { mutability := .not, ty := tyMutPtrU8_08, debugName := none }]

def b2P_08 (a o : Nat) : LocalSlot := .init (.ptr { allocId := a, offsetBytes := o } 8)

def b2State_08 : MachineState :=
  mkState08
    ([.init b2SliceVal_08, .init b2SliceVal_08, .init b2SliceVal_08, .init b2DynVal_08,
      .init b2DynVal_08, b2P_08 10 0, b2P_08 10 8, b2P_08 10 1, b2P_08 11 0, b2P_08 11 8,
      b2P_08 11 1, b2P_08 12 0, b2P_08 12 8, b2P_08 13 0, b2P_08 13 8, b2P_08 14 0, b2P_08 14 8,
      .init (.scalar ⟨0, 8⟩), b2P_08 15 0, .uninit, b2P_08 16 0, b2P_08 16 8])
    { emptyMemory with
      borrows := [b1Frozen_08 10 0, b1Active_08 11 1, b1Active_08 12 2, b1Frozen_08 13 3,
        b1Active_08 14 4, b1Active_08 15 17, b1Active_08 16 19] }

def b2C_08 (n : Nat) : Operand := b1Count_08 n 8 tyUsize_08

def b2Read_08 (stmts : List Statement) (p : Place) : Option PlaceReadResult :=
  b1ReadAfter_08 b2Decls_08 a1Layouts64_08 b2State_08 stmts p

end B2Fixtures08

/-- B2 (§3.1(e) end to end through bytewise copies, `V2026_08_01`): swapping the data and length
halves of `&[u8]` or `*const [u8]` faults (the length half now carries pointer provenance); a
data-byte `0`/`1` swap faults for `&[u8]` and strips provenance for `*const [u8]`; a plain
length half copied into a `&dyn T` vtable half faults; a `&[u8]` assembled from its halves in
either order is the original value, while a lone data half or a duplicated length half faults;
an untyped copy of pointer bytes into `u64` storage faults under `.strictUcg630Ub` (W5). -/
theorem b2_wide_ptr_byte_permutations_v08 :
    b2Read_08 [b1Copy_08 5 8 (b2C_08 16)] ⟨1, []⟩ = some (.ok b2SliceVal_08 []) ∧
    b2Read_08 [b1Copy_08 5 9 (b2C_08 8), b1Copy_08 6 8 (b2C_08 8)] ⟨1, []⟩ = some .ub ∧
    b2Read_08 [b1Copy_08 5 12 (b2C_08 8), b1Copy_08 6 11 (b2C_08 8)] ⟨2, []⟩ = some .ub ∧
    b2Read_08 [b1Copy_08 5 8 (b2C_08 16), b1Copy_08 7 8 (b2C_08 1), b1Copy_08 5 10 (b2C_08 1)]
      ⟨1, []⟩ = some .ub ∧
    b2Read_08 [b1Copy_08 5 11 (b2C_08 16), b1Copy_08 7 11 (b2C_08 1)] ⟨2, []⟩ =
      some (.ok (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨3, 8⟩]) []) ∧
    b2Read_08 [b1Copy_08 6 16 (b2C_08 8)] ⟨4, []⟩ = some .ub ∧
    b2Read_08 [b1Copy_08 13 15 (b2C_08 8)] ⟨4, []⟩ = some (.ok b2DynVal_08 []) ∧
    b2Read_08 [b1Copy_08 5 20 (b2C_08 8)] ⟨19, []⟩ = some .ub ∧
    b2Read_08 [b1Copy_08 5 20 (b2C_08 8), b1Copy_08 6 21 (b2C_08 8)] ⟨19, []⟩ =
      some (.ok b2SliceVal_08 []) ∧
    b2Read_08 [b1Copy_08 6 21 (b2C_08 8), b1Copy_08 5 20 (b2C_08 8)] ⟨19, []⟩ =
      some (.ok b2SliceVal_08 []) ∧
    b2Read_08 [b1Copy_08 6 20 (b2C_08 8), b1Copy_08 6 21 (b2C_08 8)] ⟨19, []⟩ = some .ub ∧
    IsUbStep08 (V08.evalStmt b2State_08 (b1Copy_08 13 18 (b2C_08 8)) b2Decls_08 a1Layouts64_08) := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-! ## §4d. `[adv ep1-A2]` Adversarial Regressions & `lean-miri` Correspondence Gap Postmortem

Covers the four soundness, parity, and `Kani#5205` gaps closed in `[adv ep1-A2]` across both
`V2026_06_01` and `V2026_08_01`:
1. **`W5` / `UCG#630` Multi-Variant Enum Provenance Leak (`decodeTypedValueFromBytes`)**:
   `enum PtrOrInt { Int(u64), Ptr(*const u8) }` with `BackendRepr.scalarPair (u8, .union (.pointer 0))`
   (`backendReprHasPointer = true`) previously bypassed `.strictUcg630Ub` and stripped pointer
   provenance into `PtrOrInt::Int(Value.scalar)` via `decodeFieldsBySpan`.
2. **`W5` & `Kani#5205` Cross-Frame `evalForeignFrameCopySingleDirect` Destination-Type Bypass**:
   `evalForeignFrameCopySingleDirect` previously passed `dstPlaceTyOpt = .none` and used callee
   `layouts`, permitting cross-frame `ptr -> usize` `Value.ptr` retention (`W5`), cross-frame
   `usize -> &u8` reference forgery (`W5`), and spurious `.ub` when projecting `u.0` on a valid
   `1u8` copied into a caller's `Unaligned<bool>`.
3. **`core::intrinsics::copy` (`evalCopyMemory`) `[u8; N]`, Pointer-Carrier, Raw-Ptr Scalar, and
   `Kani#5205` Parity**:
   `evalCopyMemory` now preserves `PtrByteFrag` and `.uninit` losslessly across `[u8; N]` and
   partial/incoherent pointer slots in BOTH dialects (closing the `V06` vs `V08` `.uninit` `[u8; N]`
   parity gap), decodes provenance-free raw-pointer bytes to `Value.scalar` (so `transmute` to
   `u64` succeeds), and defers `2u8` in `bool` / `0xD800` in `char` validity to typed reads.
4. **32-Bit & IEEE-754 Float Global Slice Dereference (`evalSliceFatPtrDerefRead`)**:
   `evalSliceFatPtrDerefRead` falls back to `decodeTypedValueFromBytes` on 32-bit `&[usize]` and
   `&[f32]` global slices while rejecting global pointer relocations at non-pointer element types.

### `lean-miri` Correspondence Gap Postmortem (`mir-correspondence-postmortem.md`)
Why `LeanMiriSpec` did not catch the four `A2` defects prior to `[adv ep1-A2]`:
1. `SimLM2_4` / `DropBinderAndSubtypeLM` enum transmute theorems cover fieldless `#[repr(Int)]`
   enums and `RichAdtSpec` enums rather than `TypeLayout`-only `VariantsShape.multiple` enums with
   `.union (.pointer 0)` `BackendRepr`.
2. `CopyLM4_2` proves single-frame `copy_nonoverlapping` (`targetFrameDepth = 0`, `callStack = []`),
   so `evalForeignFrameCopySingleDirect` (`copyEntriesTargetActiveFrame = false`) is outside its
   precondition.
3. `CoreMemPtrIntrinsicsTests` / `CoreMemPtrIntrinsicsMR` covered `evalCopyCall` on integer/struct
   buffers rather than `PtrByteFrag` pointer-byte round-trips or `2u8`/`0xD800` `Kani#5205` writes
   through `evalCopyMemory`.
4. `WideSliceDstLM` assumes 64-bit `layoutPointerBytes = 8` and integer element types, excluding
   32-bit `&[usize]` and `&[f32]` global slice dereferences. -/

section A2Fixtures06

open V06

/-- `enum PtrOrInt { Int(u64), Ptr(*const u8) }`: 16 bytes, tag `u8` at offset `0`, payload at `8`,
`backendRepr = .scalarPair (.initialized (.int 8 false) ⟨0, 1⟩) (.union (.pointer 0))`. -/
def a2PtrOrIntEnumL_06 : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩,
    backendRepr := .scalarPair
      (.initialized (.int 8 false) ⟨0, 1⟩)
      (.union (.pointer 0)),
    fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
      [.arbitrary [⟨0⟩, ⟨8⟩] [0, 1], .arbitrary [⟨0⟩, ⟨8⟩] [0, 1]],
    isUninhabited := false }

def a2Layouts64_06 : LayoutTable :=
  { a1Layouts64_06 with entries := a1Layouts64_06.entries ++ [a2PtrOrIntEnumL_06] }

def a2TyPtrOrInt_06 : Ty := { kind := .adt "PtrOrInt" [], layoutIdx := a1Layouts64_06.entries.length }

def a2EnumRelocGlobal_06 : CapturedAllocation :=
  { allocId := 80,
    bytes := List.replicate 8 (some 0) ++
      [some 0x10, some 0, some 0, some 0, some 0, some 0, some 0, some 0],
    relocations := [(8, ptr64_06)],
    align := ⟨8⟩, mutability := .not }

def a2Plain32Global_06 : CapturedAllocation :=
  { allocId := 81,
    bytes := [some 0x11, some 0x22, some 0, some 0, some 0x33, some 0x44, some 0, some 0],
    relocations := [],
    align := ⟨4⟩, mutability := .not }

def a2F32Global_06 : CapturedAllocation :=
  { allocId := 82,
    bytes := [some 0, some 0, some 0x80, some 0x3F],
    relocations := [],
    align := ⟨4⟩, mutability := .not }

def a2BorrowWin_06 (tag loc len : Nat) (perm : TreeBorrowPerm := .active) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := [], perm := perm,
    rangeOffset := 0, rangeLen := len }

end A2Fixtures06

section A2Fixtures08

open V08

def a2PtrOrIntEnumL_08 : TypeLayout :=
  { size := ⟨16⟩, align := ⟨8⟩,
    backendRepr := .scalarPair
      (.initialized (.int 8 false) ⟨0, 1⟩)
      (.union (.pointer 0)),
    fields := .arbitrary [⟨0⟩] [0],
    variants := .multiple (.initialized (.int 8 false) ⟨0, 1⟩) 0
      [.arbitrary [⟨0⟩, ⟨8⟩] [0, 1], .arbitrary [⟨0⟩, ⟨8⟩] [0, 1]],
    isUninhabited := false }

def a2Layouts64_08 : LayoutTable :=
  { a1Layouts64_08 with entries := a1Layouts64_08.entries ++ [a2PtrOrIntEnumL_08] }

def a2TyPtrOrInt_08 : Ty := { kind := .adt "PtrOrInt" [], layoutIdx := a1Layouts64_08.entries.length }

def a2EnumRelocGlobal_08 : CapturedAllocation :=
  { allocId := 80,
    bytes := List.replicate 8 (some 0) ++
      [some 0x10, some 0, some 0, some 0, some 0, some 0, some 0, some 0],
    relocations := [(8, ptr64_08)],
    align := ⟨8⟩, mutability := .not }

def a2Plain32Global_08 : CapturedAllocation :=
  { allocId := 81,
    bytes := [some 0x11, some 0x22, some 0, some 0, some 0x33, some 0x44, some 0, some 0],
    relocations := [],
    align := ⟨4⟩, mutability := .not }

def a2F32Global_08 : CapturedAllocation :=
  { allocId := 82,
    bytes := [some 0, some 0, some 0x80, some 0x3F],
    relocations := [],
    align := ⟨4⟩, mutability := .not }

def a2BorrowWin_08 (tag loc len : Nat) (perm : TreeBorrowPerm := .active) : BorrowEntry :=
  { tag := tag, targetLocal := loc, targetProjection := [], perm := perm,
    rangeOffset := 0, rangeLen := len }

end A2Fixtures08

/-- A2.1 (`W5` / `UCG#630` multi-variant enum with pointer `BackendRepr`, `V2026_06_01` & `V2026_08_01`):
`PtrOrInt` (`backendReprHasPointer = true`) rejects provenance-bearing bytes under `.strictUcg630Ub`
(both in `decodeTypedValueFromBytes` and `evalGlobalDerefRead`), strips provenance under
`.stripProvenance`, and decodes provenance-free bytes cleanly. -/
theorem a2_multiple_enum_ptr_backend_prov_reject_v06_v08 :
    let tag0_06 := V06.encodeLittleEndianBytes 0 8 none
    let plainPay_06 := V06.encodeLittleEndianBytes 0x42 8 none
    let tag0_08 := V08.encodeLittleEndianBytes 0 8 none
    let plainPay_08 := V08.encodeLittleEndianBytes 0x42 8 none
    V06.decodeTypedValueFromBytes V06.defaultCodecFuel a2Layouts64_06 a2TyPtrOrInt_06
      (tag0_06 ++ ptr64Bytes_06) .strictUcg630Ub = none ∧
    V06.decodeTypedValueFromBytes V06.defaultCodecFuel a2Layouts64_06 a2TyPtrOrInt_06
      (tag0_06 ++ ptr64Bytes_06) .stripProvenance =
        some (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨0x10, 8⟩]) ∧
    V06.decodeTypedValueFromBytes V06.defaultCodecFuel a2Layouts64_06 a2TyPtrOrInt_06
      (tag0_06 ++ plainPay_06) .strictUcg630Ub =
        some (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨0x42, 8⟩]) ∧
    V06.evalGlobalDerefRead [] a2EnumRelocGlobal_06 0 16 [] a2Layouts64_06 (some a2TyPtrOrInt_06) = .ub ∧
    V08.decodeTypedValueFromBytes V08.defaultCodecFuel a2Layouts64_08 a2TyPtrOrInt_08
      (tag0_08 ++ ptr64Bytes_08) .strictUcg630Ub = none ∧
    V08.decodeTypedValueFromBytes V08.defaultCodecFuel a2Layouts64_08 a2TyPtrOrInt_08
      (tag0_08 ++ ptr64Bytes_08) .stripProvenance =
        some (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨0x10, 8⟩]) ∧
    V08.decodeTypedValueFromBytes V08.defaultCodecFuel a2Layouts64_08 a2TyPtrOrInt_08
      (tag0_08 ++ plainPay_08) .strictUcg630Ub =
        some (.aggregate 0 [.scalar ⟨0, 8⟩, .scalar ⟨0x42, 8⟩]) ∧
    V08.evalGlobalDerefRead [] a2EnumRelocGlobal_08 0 16 [] a2Layouts64_08 (some a2TyPtrOrInt_08) = .ub := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

def a2ForeignCallerProj06 (callerDecls : List V06.LocalDecl) (st : V06.MirStepNode) :
    Option ValSummary :=
  match st with
  | .tau (.running s) =>
    match s.memory.callStack with
    | cf :: _ =>
      match V06.evalOperand cf.frame.locals (.copy ⟨2, [.field 0 tyBool_06]⟩)
          [] [] layouts64_06 [] callerDecls with
      | .ok v _ => some (valSummaryVal06 v)
      | .ub => some .none
      | .unsupported => none
    | [] => none
  | _ => none

def a2ForeignCallerProj08 (callerDecls : List V08.LocalDecl) (st : V08.MirStepNode) :
    Option ValSummary :=
  match st with
  | .tau (.running s) =>
    match s.memory.callStack with
    | cf :: _ =>
      match V08.evalOperand cf.frame.locals (.copy ⟨2, [.field 0 tyBool_08]⟩)
          [] [] layouts64_08 [] callerDecls with
      | .ok v _ => some (valSummaryVal08 v)
      | .ub => some .none
      | .unsupported => none
    | [] => none
  | _ => none

/-- A2.2 (`W5` & `Kani#5205` cross-frame `evalForeignFrameCopySingleDirect`, `V2026_06_01` & `V2026_08_01`):
resolving the foreign destination frame's `(dstDecls, dstLayouts)` blocks cross-frame `*const u8 -> usize`
provenance leaks (`W5`) and provenance-free `*const u8 -> &u8` reference forgery (`W5`), while decoding
cross-frame `*mut u8 -> Unaligned<bool>` into `.aggregate 0 [.scalar ...]` so `u.0` succeeds on `1u8`
and faults `.ub` on `2u8` even when callee `layouts` is `emptyLayoutTable`. -/
theorem a2_foreign_frame_copy_no_leak_no_forge_and_unal_proj_v06_v08 :
    let callerDecls06 : List V06.LocalDecl := [
      { mutability := .mut, ty := tyUsize_06, debugName := none },
      { mutability := .mut, ty := tyRefU8_06, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_06, debugName := none }
    ]
    let savedCaller06 : V06.SavedCallerFrame :=
      { callerBody := emptyBody06 callerDecls06 layouts64_06,
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨0, 8⟩), .uninit, .uninit] },
        destination := ⟨0, []⟩ }
    let tyPtrToRawPtr06 : V06.Ty := { kind := .rawPtr .not tyRawPtrU8_06.kind, layoutIdx := 0 }
    let tyMutPtrToRawPtr06 : V06.Ty := { kind := .rawPtr .mut tyRawPtrU8_06.kind, layoutIdx := 0 }
    let calleeDecls06 : List V06.LocalDecl := [
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyU8_06, debugName := none },
      { mutability := .not, ty := tyU8_06, debugName := none },
      { mutability := .not, ty := tyPtrToRawPtr06, debugName := none },
      { mutability := .not, ty := tyPtrToRawPtr06, debugName := none },
      { mutability := .not, ty := tyMutPtrToRawPtr06, debugName := none },
      { mutability := .not, ty := tyMutPtrToRawPtr06, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_06, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_06, debugName := none }
    ]
    let sPtrE06 : V06.BorrowEntry := { tag := 70, targetLocal := 0, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let sFakeE06 : V06.BorrowEntry := { tag := 71, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let sOneE06 : V06.BorrowEntry := { tag := 72, targetLocal := 2, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let sTwoE06 : V06.BorrowEntry := { tag := 73, targetLocal := 3, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let dUsizeE06 : V06.BorrowEntry := { tag := 74, targetLocal := 0, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dRefE06 : V06.BorrowEntry := { tag := 75, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dUnalE06 : V06.BorrowEntry := { tag := 76, targetLocal := 2, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let calleeLocs06 : List V06.LocalSlot := [
      .init (.ptr ptr64_06 8), .init (.scalar ⟨0x20000, 8⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨2, 1⟩),
      .init (.ptr ⟨70, 0⟩ 8), .init (.ptr ⟨71, 0⟩ 8), .init (.ptr ⟨74, 0⟩ 8), .init (.ptr ⟨75, 0⟩ 8),
      .init (.ptr ⟨72, 0⟩ 8), .init (.ptr ⟨73, 0⟩ 8), .init (.ptr ⟨76, 0⟩ 8)
    ]
    let mem06 : V06.Memory :=
      { V06.emptyMemory with
        borrows := [sPtrE06, sFakeE06, sOneE06, sTwoE06, dUsizeE06, dRefE06, dUnalE06],
        callStack := [savedCaller06] }
    let st06 := mkState06 calleeLocs06 mem06
    let emptyLay06 : V06.LayoutTable := { entries := [], pointerBits := 64, isLittleEndian := true }
    let leak06 := V06.evalForeignFrameCopySingleDirect st06 (.copy ⟨4, []⟩) (.copy ⟨6, []⟩)
      calleeDecls06 emptyLay06 ⟨70, 0⟩ ⟨74, 0⟩ sPtrE06 dUsizeE06 1 calleeLocs06
    let forge06 := V06.evalForeignFrameCopySingleDirect st06 (.copy ⟨5, []⟩) (.copy ⟨7, []⟩)
      calleeDecls06 emptyLay06 ⟨71, 0⟩ ⟨75, 0⟩ sFakeE06 dRefE06 1 calleeLocs06
    let okUnal06 := V06.evalForeignFrameCopySingleDirect st06 (.copy ⟨8, []⟩) (.copy ⟨10, []⟩)
      calleeDecls06 emptyLay06 ⟨72, 0⟩ ⟨76, 0⟩ sOneE06 dUnalE06 1 calleeLocs06
    let badUnal06 := V06.evalForeignFrameCopySingleDirect st06 (.copy ⟨9, []⟩) (.copy ⟨10, []⟩)
      calleeDecls06 emptyLay06 ⟨73, 0⟩ ⟨76, 0⟩ sTwoE06 dUnalE06 1 calleeLocs06
    -- V2026_08_01 mirror
    let callerDecls08 : List V08.LocalDecl := [
      { mutability := .mut, ty := tyUsize_08, debugName := none },
      { mutability := .mut, ty := tyRefU8_08, debugName := none },
      { mutability := .mut, ty := tyUnalignedBool_08, debugName := none }
    ]
    let savedCaller08 : V08.SavedCallerFrame :=
      { callerBody := emptyBody08 callerDecls08 layouts64_08,
        frame := { blockIdx := 0, stmtIdx := 0, locals := [.init (.scalar ⟨0, 8⟩), .uninit, .uninit] },
        destination := ⟨0, []⟩ }
    let tyPtrToRawPtr08 : V08.Ty := { kind := .rawPtr .not tyRawPtrU8_08.kind, layoutIdx := 0 }
    let tyMutPtrToRawPtr08 : V08.Ty := { kind := .rawPtr .mut tyRawPtrU8_08.kind, layoutIdx := 0 }
    let calleeDecls08 : List V08.LocalDecl := [
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyU8_08, debugName := none },
      { mutability := .not, ty := tyU8_08, debugName := none },
      { mutability := .not, ty := tyPtrToRawPtr08, debugName := none },
      { mutability := .not, ty := tyPtrToRawPtr08, debugName := none },
      { mutability := .not, ty := tyMutPtrToRawPtr08, debugName := none },
      { mutability := .not, ty := tyMutPtrToRawPtr08, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyRawPtrU8_08, debugName := none },
      { mutability := .not, ty := tyMutPtrU8_08, debugName := none }
    ]
    let sPtrE08 : V08.BorrowEntry := { tag := 70, targetLocal := 0, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let sFakeE08 : V08.BorrowEntry := { tag := 71, targetLocal := 1, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let sOneE08 : V08.BorrowEntry := { tag := 72, targetLocal := 2, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let sTwoE08 : V08.BorrowEntry := { tag := 73, targetLocal := 3, targetProjection := [], perm := .frozen, targetFrameDepth := 1 }
    let dUsizeE08 : V08.BorrowEntry := { tag := 74, targetLocal := 0, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dRefE08 : V08.BorrowEntry := { tag := 75, targetLocal := 1, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let dUnalE08 : V08.BorrowEntry := { tag := 76, targetLocal := 2, targetProjection := [], perm := .active, targetFrameDepth := 0 }
    let calleeLocs08 : List V08.LocalSlot := [
      .init (.ptr ptr64_08 8), .init (.scalar ⟨0x20000, 8⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨2, 1⟩),
      .init (.ptr ⟨70, 0⟩ 8), .init (.ptr ⟨71, 0⟩ 8), .init (.ptr ⟨74, 0⟩ 8), .init (.ptr ⟨75, 0⟩ 8),
      .init (.ptr ⟨72, 0⟩ 8), .init (.ptr ⟨73, 0⟩ 8), .init (.ptr ⟨76, 0⟩ 8)
    ]
    let mem08 : V08.Memory :=
      { V08.emptyMemory with
        borrows := [sPtrE08, sFakeE08, sOneE08, sTwoE08, dUsizeE08, dRefE08, dUnalE08],
        callStack := [savedCaller08] }
    let st08 := mkState08 calleeLocs08 mem08
    let emptyLay08 : V08.LayoutTable := { entries := [], pointerBits := 64, isLittleEndian := true }
    let leak08 := V08.evalForeignFrameCopySingleDirect st08 (.copy ⟨4, []⟩) (.copy ⟨6, []⟩)
      calleeDecls08 emptyLay08 ⟨70, 0⟩ ⟨74, 0⟩ sPtrE08 dUsizeE08 1 calleeLocs08
    let forge08 := V08.evalForeignFrameCopySingleDirect st08 (.copy ⟨5, []⟩) (.copy ⟨7, []⟩)
      calleeDecls08 emptyLay08 ⟨71, 0⟩ ⟨75, 0⟩ sFakeE08 dRefE08 1 calleeLocs08
    let okUnal08 := V08.evalForeignFrameCopySingleDirect st08 (.copy ⟨8, []⟩) (.copy ⟨10, []⟩)
      calleeDecls08 emptyLay08 ⟨72, 0⟩ ⟨76, 0⟩ sOneE08 dUnalE08 1 calleeLocs08
    let badUnal08 := V08.evalForeignFrameCopySingleDirect st08 (.copy ⟨9, []⟩) (.copy ⟨10, []⟩)
      calleeDecls08 emptyLay08 ⟨73, 0⟩ ⟨76, 0⟩ sTwoE08 dUnalE08 1 calleeLocs08
    IsUbStep06 leak06 ∧ IsUbStep06 forge06 ∧
    a2ForeignCallerProj06 callerDecls06 okUnal06 = some (.scalar 1 1) ∧
    a2ForeignCallerProj06 callerDecls06 badUnal06 = some .none ∧
    IsUbStep08 leak08 ∧ IsUbStep08 forge08 ∧
    a2ForeignCallerProj08 callerDecls08 okUnal08 = some (.scalar 1 1) ∧
    a2ForeignCallerProj08 callerDecls08 badUnal08 = some .none := by
  exact ⟨trivial, trivial, rfl, rfl, trivial, trivial, rfl, rfl⟩

def a2TwoPairMem_06 : V06.Memory :=
  { V06.emptyMemory with
    borrows := [a2BorrowWin_06 10 0 8 .frozen, a2BorrowWin_06 11 1 8 .active] }

def a2Step1_06 (srcTy dstTy : V06.Ty) (srcSlot dstSlot : V06.LocalSlot)
    (sOff dOff n : Nat) : Option (List V06.LocalSlot × V06.Memory) :=
  let decls : List V06.LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  let l := [srcSlot, dstSlot]
  match V06.evalCopyMemory (mkState06 l a2TwoPairMem_06) l decls layouts64_06
      ⟨10, sOff⟩ ⟨11, dOff⟩ n with
  | .ok res => some res
  | _ => none

def a2Copy1Slot_06 (srcTy dstTy : V06.Ty) (srcSlot dstSlot : V06.LocalSlot)
    (sOff dOff n : Nat) : Option V06.LocalSlot :=
  match a2Step1_06 srcTy dstTy srcSlot dstSlot sOff dOff n with
  | some (_ :: dst' :: _, _) => some dst'
  | _ => none

def a2Copy1Read_06 (srcTy dstTy : V06.Ty) (srcSlot dstSlot : V06.LocalSlot)
    (sOff dOff n : Nat) : Option ValSummary :=
  let decls : List V06.LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  match a2Step1_06 srcTy dstTy srcSlot dstSlot sOff dOff n with
  | some (l', _) =>
    match V06.evalOperand l' (.copy ⟨1, []⟩) [] [] layouts64_06 [] decls with
    | .ok v _ => some (valSummaryVal06 v)
    | .ub => some .none
    | .unsupported => none
  | none => none

def a2Copy1CastU64_06 (srcTy dstTy : V06.Ty) (srcSlot dstSlot : V06.LocalSlot)
    (sOff dOff n : Nat) : Option ValSummary :=
  let decls : List V06.LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  match a2Step1_06 srcTy dstTy srcSlot dstSlot sOff dOff n with
  | some (l', m') =>
    match V06.evalByteCast l' (.copy ⟨1, []⟩) tyU64_06 m' decls layouts64_06 with
    | .ok v _ _ => some (valSummaryVal06 v)
    | .ub => some .none
    | .unsupported => none
  | none => none

def a2TwoPairMem_08 : V08.Memory :=
  { V08.emptyMemory with
    borrows := [a2BorrowWin_08 10 0 8 .frozen, a2BorrowWin_08 11 1 8 .active] }

def a2Step1_08 (srcTy dstTy : V08.Ty) (srcSlot dstSlot : V08.LocalSlot)
    (sOff dOff n : Nat) : Option (List V08.LocalSlot × V08.Memory) :=
  let decls : List V08.LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  let l := [srcSlot, dstSlot]
  match V08.evalCopyMemory (mkState08 l a2TwoPairMem_08) l decls layouts64_08
      ⟨10, sOff⟩ ⟨11, dOff⟩ n with
  | .ok res => some res
  | _ => none

def a2Copy1Slot_08 (srcTy dstTy : V08.Ty) (srcSlot dstSlot : V08.LocalSlot)
    (sOff dOff n : Nat) : Option V08.LocalSlot :=
  match a2Step1_08 srcTy dstTy srcSlot dstSlot sOff dOff n with
  | some (_ :: dst' :: _, _) => some dst'
  | _ => none

def a2Copy1Read_08 (srcTy dstTy : V08.Ty) (srcSlot dstSlot : V08.LocalSlot)
    (sOff dOff n : Nat) : Option ValSummary :=
  let decls : List V08.LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  match a2Step1_08 srcTy dstTy srcSlot dstSlot sOff dOff n with
  | some (l', _) =>
    match V08.evalOperand l' (.copy ⟨1, []⟩) [] [] layouts64_08 [] decls with
    | .ok v _ => some (valSummaryVal08 v)
    | .ub => some .none
    | .unsupported => none
  | none => none

def a2Copy1CastU64_08 (srcTy dstTy : V08.Ty) (srcSlot dstSlot : V08.LocalSlot)
    (sOff dOff n : Nat) : Option ValSummary :=
  let decls : List V08.LocalDecl := [
    { mutability := .not, ty := srcTy, debugName := none },
    { mutability := .mut, ty := dstTy, debugName := none }
  ]
  match a2Step1_08 srcTy dstTy srcSlot dstSlot sOff dOff n with
  | some (l', m') =>
    match V08.evalByteCast l' (.copy ⟨1, []⟩) tyU64_08 m' decls layouts64_08 with
    | .ok v _ _ => some (valSummaryVal08 v)
    | .ub => some .none
    | .unsupported => none
  | none => none

def a2HalfBufSlot_06 : V06.LocalSlot :=
  .init (.aggregate 0
    (V06.encodeRawAbstractByteVals (ptr64Bytes_06.take 4) ++ List.replicate 4 .uninit))

def a2FullBufSlot_06 : V06.LocalSlot :=
  .init (.aggregate 0 (V06.encodeRawAbstractByteVals ptr64Bytes_06))

def a2HalfPtrSlot_06 : V06.LocalSlot :=
  .init (.aggregate 0
    (V06.encodeRawAbstractByteVals (ptr64Bytes_06.take 4 ++ List.replicate 4 .uninit)))

def a2HalfSwapSlot_06 : V06.LocalSlot :=
  .init (.aggregate 0
    (V06.encodeRawAbstractByteVals ((ptr64Bytes_06.drop 1).take 1 ++ ptr64Bytes_06.drop 1)))

def a2HalfBufSlot_08 : V08.LocalSlot :=
  .init (.aggregate 0
    (V08.encodeRawAbstractByteVals (ptr64Bytes_08.take 4) ++ List.replicate 4 (.scalar ⟨0, 0⟩)))

def a2FullBufSlot_08 : V08.LocalSlot :=
  .init (.aggregate 0 (V08.encodeRawAbstractByteVals ptr64Bytes_08))

def a2HalfPtrSlot_08 : V08.LocalSlot :=
  .init (.aggregate 0
    (V08.encodeRawAbstractByteVals (ptr64Bytes_08.take 4 ++ List.replicate 4 .uninit)))

def a2HalfSwapSlot_08 : V08.LocalSlot :=
  .init (.aggregate 0
    (V08.encodeRawAbstractByteVals ((ptr64Bytes_08.drop 1).take 1 ++ ptr64Bytes_08.drop 1)))

/-- A2.3a (`core::intrinsics::copy` / `evalCopyMemory` split `[u8; 8]` & pointer coherence,
`V2026_06_01` & `V2026_08_01`): split 4+4 byte `evalCopyMemory` into an initially `.uninit`
`[u8; 8]` buffer and from that `[u8; 8]` buffer into initially `.uninit` `*const u8` and `&u8`
preserves partial `PtrByteFrag` + `.uninit` carriers after the first 4-byte copy and reassembles
intact `Value.ptr` provenance after the second 4-byte copy across BOTH dialects. -/
theorem a2_evalCopyMemory_ptr_coherence_u8_buf_v06_v08 :
    a2Copy1Slot_06 tyRawPtrU8_06 tyArr8U8_06 (.init (.ptr ptr64_06 8)) .uninit 0 0 4 =
      some a2HalfBufSlot_06 ∧
    a2Copy1Slot_06 tyRawPtrU8_06 tyArr8U8_06 (.init (.ptr ptr64_06 8)) a2HalfBufSlot_06 4 4 4 =
      some a2FullBufSlot_06 ∧
    a2Copy1Slot_06 tyArr8U8_06 tyRawPtrU8_06 a2FullBufSlot_06 .uninit 0 0 4 =
      some a2HalfPtrSlot_06 ∧
    a2Copy1Read_06 tyArr8U8_06 tyRawPtrU8_06 a2FullBufSlot_06 a2HalfPtrSlot_06 4 4 4 =
      some (.ptr 7 0x10 8) ∧
    a2Copy1Slot_06 tyArr8U8_06 tyRefU8_06 a2FullBufSlot_06 .uninit 0 0 4 =
      some a2HalfPtrSlot_06 ∧
    a2Copy1Read_06 tyArr8U8_06 tyRefU8_06 a2FullBufSlot_06 a2HalfPtrSlot_06 4 4 4 =
      some (.ptr 7 0x10 8) ∧
    a2Copy1Slot_08 tyRawPtrU8_08 tyArr8U8_08 (.init (.ptr ptr64_08 8)) .uninit 0 0 4 =
      some a2HalfBufSlot_08 ∧
    a2Copy1Slot_08 tyRawPtrU8_08 tyArr8U8_08 (.init (.ptr ptr64_08 8)) a2HalfBufSlot_08 4 4 4 =
      some a2FullBufSlot_08 ∧
    a2Copy1Slot_08 tyArr8U8_08 tyRawPtrU8_08 a2FullBufSlot_08 .uninit 0 0 4 =
      some a2HalfPtrSlot_08 ∧
    a2Copy1Read_08 tyArr8U8_08 tyRawPtrU8_08 a2FullBufSlot_08 a2HalfPtrSlot_08 4 4 4 =
      some (.ptr 7 0x10 8) ∧
    a2Copy1Slot_08 tyArr8U8_08 tyRefU8_08 a2FullBufSlot_08 .uninit 0 0 4 =
      some a2HalfPtrSlot_08 ∧
    a2Copy1Read_08 tyArr8U8_08 tyRefU8_08 a2FullBufSlot_08 a2HalfPtrSlot_08 4 4 4 =
      some (.ptr 7 0x10 8) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A2.3b (`core::intrinsics::copy` / `evalCopyMemory` byte-swap, raw-ptr scalar, & `Kani#5205`,
`V2026_06_01` & `V2026_08_01`): swapping bytes `0` and `1` succeeds at untyped write time and
strips provenance on `*const u8` while faulting `.ub` on `&u8` at read time (`UCG#558`);
`0x1000u64` copied into `*const u8` commits `Value.scalar` so `evalByteCast` (`transmute`)
succeeds; and `2u8` into `bool` / `0xD800` into `char` succeed at write time and fault `.ub` on
typed read (`Kani#5205`). -/
theorem a2_evalCopyMemory_swap_cast_and_kani5205_v06_v08 :
    let tyU32_06 : V06.Ty := { kind := .uint .u32, layoutIdx := 0 }
    let tyU32_08 : V08.Ty := { kind := .uint .u32, layoutIdx := 0 }
    a2Copy1Slot_06 tyRawPtrU8_06 tyRawPtrU8_06 (.init (.ptr ptr64_06 8)) (.init (.ptr ptr64_06 8)) 1 0 1 =
      some a2HalfSwapSlot_06 ∧
    a2Copy1Read_06 tyRawPtrU8_06 tyRawPtrU8_06 (.init (.ptr ptr64_06 8)) a2HalfSwapSlot_06 0 1 1 =
      some (.scalar 0x1000 8) ∧
    a2Copy1Slot_06 tyRawPtrU8_06 tyRefU8_06 (.init (.ptr ptr64_06 8)) (.init (.ptr ptr64_06 8)) 1 0 1 =
      some a2HalfSwapSlot_06 ∧
    a2Copy1Read_06 tyRawPtrU8_06 tyRefU8_06 (.init (.ptr ptr64_06 8)) a2HalfSwapSlot_06 0 1 1 =
      some .none ∧
    a2Copy1CastU64_06 tyU64_06 tyRawPtrU8_06 (.init (.scalar ⟨0x1000, 8⟩)) .uninit 0 0 8 =
      some (.scalar 0x1000 8) ∧
    a2Copy1Read_06 tyU8_06 tyBool_06 (.init (.scalar ⟨2, 1⟩)) .uninit 0 0 1 = some .none ∧
    a2Copy1Read_06 tyU32_06 tyChar_06 (.init (.scalar ⟨0xD800, 4⟩)) .uninit 0 0 4 = some .none ∧
    a2Copy1Slot_08 tyRawPtrU8_08 tyRawPtrU8_08 (.init (.ptr ptr64_08 8)) (.init (.ptr ptr64_08 8)) 1 0 1 =
      some a2HalfSwapSlot_08 ∧
    a2Copy1Read_08 tyRawPtrU8_08 tyRawPtrU8_08 (.init (.ptr ptr64_08 8)) a2HalfSwapSlot_08 0 1 1 =
      some (.scalar 0x1000 8) ∧
    a2Copy1Slot_08 tyRawPtrU8_08 tyRefU8_08 (.init (.ptr ptr64_08 8)) (.init (.ptr ptr64_08 8)) 1 0 1 =
      some a2HalfSwapSlot_08 ∧
    a2Copy1Read_08 tyRawPtrU8_08 tyRefU8_08 (.init (.ptr ptr64_08 8)) a2HalfSwapSlot_08 0 1 1 =
      some .none ∧
    a2Copy1CastU64_08 tyU64_08 tyRawPtrU8_08 (.init (.scalar ⟨0x1000, 8⟩)) .uninit 0 0 8 =
      some (.scalar 0x1000 8) ∧
    a2Copy1Read_08 tyU8_08 tyBool_08 (.init (.scalar ⟨2, 1⟩)) .uninit 0 0 1 = some .none ∧
    a2Copy1Read_08 tyU32_08 tyChar_08 (.init (.scalar ⟨0xD800, 4⟩)) .uninit 0 0 4 = some .none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A2.4 (32-bit `&[usize]` and `&[f32]` global slice dereference + 32/64-bit relocation rejection,
`V2026_06_01` & `V2026_08_01`). -/
theorem a2_32bit_and_float_global_slice_deref_v06_v08 :
    let sliceUsize06 : Option V06.Ty := some { kind := .slice (.uint .usize), layoutIdx := 0 }
    let sliceF3206 : Option V06.Ty := some { kind := .slice (.float .f32), layoutIdx := 0 }
    let sliceU6406 : Option V06.Ty := some { kind := .slice (.uint .u64), layoutIdx := 0 }
    let sliceUsize08 : Option V08.Ty := some { kind := .slice (.uint .usize), layoutIdx := 0 }
    let sliceF3208 : Option V08.Ty := some { kind := .slice (.float .f32), layoutIdx := 0 }
    let sliceU6408 : Option V08.Ty := some { kind := .slice (.uint .u64), layoutIdx := 0 }
    V06.evalSliceFatPtrDerefRead [] ⟨81, 0⟩ 4 ⟨2, 4⟩ [] [] [a2Plain32Global_06]
      a1Layouts32_06 [] sliceUsize06 [] =
        .ok (.aggregate 0 [.scalar ⟨0x2211, 4⟩, .scalar ⟨0x4433, 4⟩]) [] ∧
    V06.evalSliceFatPtrDerefRead [] ⟨51, 0⟩ 4 ⟨2, 4⟩ [] [] [relocAlloc32_06]
      a1Layouts32_06 [] sliceUsize06 [] = .ub ∧
    V06.evalSliceFatPtrDerefRead [] ⟨82, 0⟩ 8 ⟨1, 8⟩ [] [] [a2F32Global_06]
      layouts64_06 [] sliceF3206 [] =
        .ok (.aggregate 0 [.scalar ⟨0x3F800000, 4⟩]) [] ∧
    V06.evalSliceFatPtrDerefRead [] ⟨51, 0⟩ 8 ⟨1, 8⟩ [] [] [relocAlloc32_06]
      layouts64_06 [] sliceF3206 [] = .ub ∧
    V06.evalSliceFatPtrDerefRead [] ⟨50, 0⟩ 8 ⟨2, 8⟩ [] [] [adjRelocAlloc64_06]
      layouts64_06 [] sliceU6406 [] = .ub ∧
    V08.evalSliceFatPtrDerefRead [] ⟨81, 0⟩ 4 ⟨2, 4⟩ [] [] [a2Plain32Global_08]
      a1Layouts32_08 [] sliceUsize08 [] =
        .ok (.aggregate 0 [.scalar ⟨0x2211, 4⟩, .scalar ⟨0x4433, 4⟩]) [] ∧
    V08.evalSliceFatPtrDerefRead [] ⟨51, 0⟩ 4 ⟨2, 4⟩ [] [] [relocAlloc32_08]
      a1Layouts32_08 [] sliceUsize08 [] = .ub ∧
    V08.evalSliceFatPtrDerefRead [] ⟨82, 0⟩ 8 ⟨1, 8⟩ [] [] [a2F32Global_08]
      layouts64_08 [] sliceF3208 [] =
        .ok (.aggregate 0 [.scalar ⟨0x3F800000, 4⟩]) [] ∧
    V08.evalSliceFatPtrDerefRead [] ⟨51, 0⟩ 8 ⟨1, 8⟩ [] [] [relocAlloc32_08]
      layouts64_08 [] sliceF3208 [] = .ub ∧
    V08.evalSliceFatPtrDerefRead [] ⟨50, 0⟩ 8 ⟨2, 8⟩ [] [] [adjRelocAlloc64_08]
      layouts64_08 [] sliceU6408 [] = .ub := by
  repeat first | refine ⟨?_, ?_⟩ | rfl | trivial

/-- A2.5 (`V2026_06_01 == V2026_08_01` lockstep parity across all Pass A2 regressions). -/
theorem a2_lockstep_parity :
    let rd06 : V06.PlaceReadResult → Option V06.Value
      | .ok v _ => some v
      | _ => none
    let rd08 : V08.PlaceReadResult → Option V08.Value
      | .ok v _ => some v
      | _ => none
    let v06 : List ValSummary := [
      valSummary06 (V06.decodeTypedValueFromBytes V06.defaultCodecFuel a2Layouts64_06 a2TyPtrOrInt_06
        (V06.encodeLittleEndianBytes 0 8 none ++ ptr64Bytes_06) .strictUcg630Ub),
      valSummary06 (V06.decodeTypedValueFromBytes V06.defaultCodecFuel a2Layouts64_06 a2TyPtrOrInt_06
        (V06.encodeLittleEndianBytes 0 8 none ++ V06.encodeLittleEndianBytes 0x42 8 none) .strictUcg630Ub),
      valSummary06 (rd06 (V06.evalSliceFatPtrDerefRead [] ⟨81, 0⟩ 4 ⟨2, 4⟩ [] [] [a2Plain32Global_06]
        a1Layouts32_06 [] (some { kind := .slice (.uint .usize), layoutIdx := 0 }) [])),
      valSummary06 (rd06 (V06.evalSliceFatPtrDerefRead [] ⟨51, 0⟩ 4 ⟨2, 4⟩ [] [] [relocAlloc32_06]
        a1Layouts32_06 [] (some { kind := .slice (.uint .usize), layoutIdx := 0 }) []))
    ]
    let v08 : List ValSummary := [
      valSummary08 (V08.decodeTypedValueFromBytes V08.defaultCodecFuel a2Layouts64_08 a2TyPtrOrInt_08
        (V08.encodeLittleEndianBytes 0 8 none ++ ptr64Bytes_08) .strictUcg630Ub),
      valSummary08 (V08.decodeTypedValueFromBytes V08.defaultCodecFuel a2Layouts64_08 a2TyPtrOrInt_08
        (V08.encodeLittleEndianBytes 0 8 none ++ V08.encodeLittleEndianBytes 0x42 8 none) .strictUcg630Ub),
      valSummary08 (rd08 (V08.evalSliceFatPtrDerefRead [] ⟨81, 0⟩ 4 ⟨2, 4⟩ [] [] [a2Plain32Global_08]
        a1Layouts32_08 [] (some { kind := .slice (.uint .usize), layoutIdx := 0 }) [])),
      valSummary08 (rd08 (V08.evalSliceFatPtrDerefRead [] ⟨51, 0⟩ 4 ⟨2, 4⟩ [] [] [relocAlloc32_08]
        a1Layouts32_08 [] (some { kind := .slice (.uint .usize), layoutIdx := 0 }) []))
    ]
    v06 = v08 ∧
    v06 = [.none, .agg 0 [.scalar 0 8, .scalar 0x42 8],
           .agg 0 [.scalar 0x2211 4, .scalar 0x4433 4], .none] := by
  exact ⟨rfl, rfl⟩

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
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalGlobalDerefRead,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalSliceFatPtrDerefRead,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.evalCopyMemory,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.globalRelocsOverlapRange,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.isPtrCopyKind,
    ``Trusted.Rustc.V2026_06_01.MirSemantics.materializeReadPtrValue,
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
    ``Trusted.Rustc.V2026_08_01.MirSemantics.writeBytesAction,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalGlobalDerefRead,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalSliceFatPtrDerefRead,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.evalCopyMemory,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.globalRelocsOverlapRange,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.isPtrCopyKind,
    ``Trusted.Rustc.V2026_08_01.MirSemantics.materializeReadPtrValue
  ]
  for req in requiredConsts do
    unless reached.contains req do
      throwError "PtrByteCoherenceTests audit failure: test module does not reference {req}"
  if checked == 0 || thmChecked < 20 then
    throwError "PtrByteCoherenceTests audit failure: unexpected counts (checked={checked}, thmChecked={thmChecked})"
  logInfo m!"PtrByteCoherenceTests audit: verified {checked} declarations ({thmChecked} non-trivial theorems, all {requiredConsts.length} V06+V08 key Trusted constants exercised, standard axioms only, 0 sorryAx, 0 ofReduceBool)"

end Anneal.PtrByteCoherenceTests
