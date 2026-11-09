/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Rustc.V2026_06_01.MirSemantics.Machine
import Miri

/-!
# Anneal `Trusted.Rustc.V2026_06_01` → `lean-miri` (`Miri.*`) Translation

Translates Anneal's `Trusted.Rustc.V2026_06_01` MIR AST, layout descriptors,
and scalar types into upstream `proofs-rs/lean-miri`'s `Miri.MIR`, `Miri.ABI`,
`Miri.Memory`, and `Miri.Interpreter` representations, and instantiates the
single-threaded Anneal machine hooks (`annealScalarOpsHooks`, `annealRvalueHooks`,
`annealControlHooks`, `annealTerminatorHooks`, `annealStepHooks`).
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Target Data Layout & Primitive Layout Translation -/

/-- Default 64-bit little-endian target data layout used by Anneal's MIR machine. -/
def annealTargetDataLayout : Miri.ABI.TargetDataLayout :=
  { endian := .little, pointerWidth := .w64 }

/-- Default 64-bit little-endian runtime target data layout. -/
def annealRuntimeDataLayout : Miri.ABI.RuntimeTargetDataLayout :=
  { Miri.ABI.RuntimeTargetDataLayout.default with base := annealTargetDataLayout }

/-- Translate an Anneal `IntTy` to `Miri.MIR.IntegerKind`. -/
def translateIntTy : IntTy → Miri.MIR.IntegerKind
  | .i8 => .i8
  | .i16 => .i16
  | .i32 => .i32
  | .i64 => .i64
  | .i128 => .i128
  | .isize => .isize

/-- Translate an Anneal `UintTy` to `Miri.MIR.IntegerKind`. -/
def translateUintTy : UintTy → Miri.MIR.IntegerKind
  | .u8 => .u8
  | .u16 => .u16
  | .u32 => .u32
  | .u64 => .u64
  | .u128 => .u128
  | .usize => .usize

/-- Byte width of a `Miri.MIR.IntegerKind` on a 64-bit target. -/
def integerKindByteWidth : Miri.MIR.IntegerKind → Nat
  | .i8 | .u8 => 1
  | .i16 | .u16 => 2
  | .i32 | .u32 => 4
  | .i64 | .u64 | .isize | .usize => 8
  | .i128 | .u128 => 16

/-- Translate an Anneal `IntTy` to `Miri.Interpreter.IntegerType` on a 64-bit target. -/
def translateIntIntegerType (it : IntTy) : Miri.Interpreter.IntegerType :=
  { size := Miri.ABI.Size.ofBytes (UInt64.ofNat (it.byteWidth 64))
    kind := translateIntTy it }

/-- Translate an Anneal `UintTy` to `Miri.Interpreter.IntegerType` on a 64-bit target. -/
def translateUintIntegerType (ut : UintTy) : Miri.Interpreter.IntegerType :=
  { size := Miri.ABI.Size.ofBytes (UInt64.ofNat (ut.byteWidth 64))
    kind := translateUintTy ut }

/-- Translate a byte count to `Miri.ABI.Size`. -/
def translateSizeBytes (bytes : Nat) : Miri.ABI.Size :=
  Miri.ABI.Size.ofBytes (UInt64.ofNat bytes)

/-- Translate an Anneal `Layout.Size` to `Miri.ABI.Size`. -/
def translateSize (s : Layout.Size) : Miri.ABI.Size :=
  translateSizeBytes s.bytes

/-- Translate a byte alignment to `Miri.ABI.Align` (defaulting to `Align.ONE` if invalid). -/
def translateAlignBytes (bytes : Nat) : Miri.ABI.Align :=
  match Miri.ABI.Align.fromBytes (UInt64.ofNat bytes) with
  | .ok a => a
  | .error _ => Miri.ABI.Align.ONE

/-- Translate an Anneal `Layout.Align` to `Miri.ABI.Align`. -/
def translateAlign (a : Layout.Align) : Miri.ABI.Align :=
  translateAlignBytes a.bytes

/-- Translate an Anneal `Layout.WrappingRange` to `Miri.ABI.WrappingRange`. -/
def translateWrappingRange (r : Layout.WrappingRange) : Miri.ABI.WrappingRange :=
  { start := BitVec.ofNat 128 r.start, «end» := BitVec.ofNat 128 r.end_ }

/-- Map a byte width (`1, 2, 4, 8, 16`) to `Miri.ABI.Integer`. -/
def translateAbiIntegerBytes (widthBytes : Nat) : Miri.ABI.Integer :=
  match widthBytes with
  | 1 => .I8
  | 2 => .I16
  | 4 => .I32
  | 8 => .I64
  | _ => .I128

/-- Map a bit width (`8, 16, 32, 64, 128`) to `Miri.ABI.Integer`. -/
def translateAbiIntegerBits (widthBits : Nat) : Miri.ABI.Integer :=
  match widthBits with
  | 8 => .I8
  | 16 => .I16
  | 32 => .I32
  | 64 => .I64
  | _ => .I128

/-- Map a float bit width (`16, 32, 64, 128`) to `Miri.ABI.Float`. -/
def translateAbiFloatBits (widthBits : Nat) : Miri.ABI.Float :=
  match widthBits with
  | 16 => .F16
  | 32 => .F32
  | 64 => .F64
  | _ => .F128

/-- Translate an Anneal `Layout.PrimitiveKind` to `Miri.ABI.Primitive`. -/
def translatePrimitiveKind : Layout.PrimitiveKind → Miri.ABI.Primitive
  | .int bits signed => .Int (translateAbiIntegerBits bits) signed
  | .float bits => .Float (translateAbiFloatBits bits)
  | .pointer addressSpace => .Pointer ⟨UInt32.ofNat addressSpace⟩

/-- Translate an Anneal `Layout.ScalarLayout` to `Miri.ABI.Scalar`. -/
def translateScalarLayout : Layout.ScalarLayout → Miri.ABI.Scalar
  | .initialized value validRange =>
      .Initialized
        (value := translatePrimitiveKind value)
        (validRange := translateWrappingRange validRange)
  | .union value =>
      .Union (value := translatePrimitiveKind value)

/-- Translate an Anneal `Layout.BackendRepr` to `Miri.ABI.BackendRepr`. -/
def translateBackendRepr : Layout.BackendRepr → Miri.ABI.BackendRepr
  | .scalar s => .Scalar (translateScalarLayout s)
  | .scalarPair a b =>
      let sa := translateScalarLayout a
      let sb := translateScalarLayout b
      let bOff := (sa.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO
      .ScalarPair (a := sa) (b := sb) (bOffset := bOff)
  | .memory => .Memory (sized := true)

/-- Translate an Anneal `Layout.FieldsShape` to `Miri.ABI.FieldsShape`. -/
def translateFieldsShape : Layout.FieldsShape → Miri.ABI.FieldsShape
  | .primitive => .Primitive
  | .union count => .Union count
  | .array stride count => .Array (translateSize stride) (UInt64.ofNat count)
  | .arbitrary offsets memoryIndex =>
      .Arbitrary (offsets.map translateSize).toArray memoryIndex.toArray

/-- Translate a per-variant `Layout.FieldsShape` to `Miri.ABI.VariantLayout`. -/
def translateVariantFieldsShape (fs : Layout.FieldsShape) : Miri.ABI.VariantLayout :=
  let (offsets, order) :=
    match fs with
    | .arbitrary offs ord => ((offs.map translateSize).toArray, ord.toArray)
    | _ => (#[], #[])
  { size := Miri.ABI.Size.ZERO
    backendRepr := .Memory (sized := true)
    fieldOffsets := offsets
    fieldsInMemoryOrder := order
    largestNiche := none
    uninhabited := false }

/-- Translate an Anneal `Layout.VariantsShape` to `Miri.ABI.Variants`. -/
def translateVariantsShape : Layout.VariantsShape → Miri.ABI.Variants
  | .empty => .Empty
  | .single index => .Single index
  | .multiple tag tagField variants =>
      .Multiple
        (translateScalarLayout tag)
        .Direct
        tagField
        (variants.map translateVariantFieldsShape).toArray

/-- Translate an Anneal `Layout.TypeLayout` to `Miri.ABI.LayoutData`. -/
def translateTypeLayout (tl : Layout.TypeLayout) : Miri.ABI.LayoutData :=
  let align := translateAlign tl.align
  { fields := translateFieldsShape tl.fields
    variants := translateVariantsShape tl.variants
    backendRepr := translateBackendRepr tl.backendRepr
    largestNiche := none
    uninhabited := tl.isUninhabited
    align := ⟨align⟩
    size := translateSize tl.size
    maxReprAlign := none
    unadjustedAbiAlign := align
    reprC := false
    randomizationSeed := 0 }

/-- Construct a `Miri.ABI.LayoutData` for a primitive scalar of `sizeBytes` bytes
with signedness `signed` and inclusive wrapping range `[rangeStart, rangeEnd]`. -/
def scalarLayoutData (sizeBytes : Nat) (signed : Bool)
    (rangeStart : Nat := 0)
    (rangeEnd : Nat := (2 ^ (8 * sizeBytes)) - 1) : Miri.ABI.LayoutData :=
  let sz := translateSizeBytes sizeBytes
  let al := translateAlignBytes sizeBytes
  let prim : Miri.ABI.Primitive := .Int (translateAbiIntegerBytes sizeBytes) signed
  let range : Miri.ABI.WrappingRange :=
    { start := BitVec.ofNat 128 rangeStart, «end» := BitVec.ofNat 128 rangeEnd }
  { fields := .Primitive
    variants := .Single 0
    backendRepr := .Scalar (.Initialized (value := prim) (validRange := range))
    largestNiche := none
    uninhabited := false
    align := ⟨al⟩
    size := sz
    maxReprAlign := none
    unadjustedAbiAlign := al
    reprC := false
    randomizationSeed := 0 }

/-- Construct a `Miri.ABI.LayoutData` for an IEEE-754 float of `sizeBytes` bytes
(`f16`, `f32`, `f64`, `f128`), whose backend scalar is a `Primitive.Float`
rather than an integer of the same width. -/
def floatLayoutData (sizeBytes : Nat) : Miri.ABI.LayoutData :=
  let sz := translateSizeBytes sizeBytes
  let al := translateAlignBytes sizeBytes
  let prim : Miri.ABI.Primitive := .Float (translateAbiFloatBits (8 * sizeBytes))
  let range : Miri.ABI.WrappingRange :=
    { start := 0, «end» := BitVec.ofNat 128 ((2 ^ (8 * sizeBytes)) - 1) }
  { fields := .Primitive
    variants := .Single 0
    backendRepr := .Scalar (.Initialized (value := prim) (validRange := range))
    largestNiche := none
    uninhabited := false
    align := ⟨al⟩
    size := sz
    maxReprAlign := none
    unadjustedAbiAlign := al
    reprC := false
    randomizationSeed := 0 }

/-- Construct a `Miri.ABI.LayoutData` for a pointer of 8 bytes. -/
def pointerLayoutData (nonNull : Bool := false) : Miri.ABI.LayoutData :=
  let sz := Miri.ABI.Size.ofBytes 8
  let al := Miri.ABI.Align.EIGHT
  let prim : Miri.ABI.Primitive := .Pointer Miri.ABI.AddressSpace.ZERO
  let range : Miri.ABI.WrappingRange :=
    { start := BitVec.ofNat 128 (if nonNull then 1 else 0)
      «end» := BitVec.ofNat 128 ((2 ^ 64) - 1) }
  { fields := .Primitive
    variants := .Single 0
    backendRepr := .Scalar (.Initialized (value := prim) (validRange := range))
    largestNiche := none
    uninhabited := false
    align := ⟨al⟩
    size := sz
    maxReprAlign := none
    unadjustedAbiAlign := al
    reprC := false
    randomizationSeed := 0 }

/-- Construct a `Miri.ABI.LayoutData` for a zero-sized unit/aggregate type. -/
def zstLayoutData : Miri.ABI.LayoutData :=
  { fields := .Arbitrary #[] #[]
    variants := .Single 0
    backendRepr := .Memory (sized := true)
    largestNiche := none
    uninhabited := false
    align := ⟨Miri.ABI.Align.ONE⟩
    size := Miri.ABI.Size.ZERO
    maxReprAlign := none
    unadjustedAbiAlign := Miri.ABI.Align.ONE
    reprC := false
    randomizationSeed := 0 }

/-- Whether a pointee `RigidTy` is syntactically known to be `Sized` without
consulting `LayoutTable`, so `*const T` / `*mut T` is guaranteed to be a thin
8-byte pointer rather than a 16-byte wide pointer carrying slice length or
trait-object vtable metadata. -/
def isThinRawPtrPointee : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ | .never
  | .tuple .nil | .fnDef _ _ | .rawPtr _ _ | .ref _ _ | .fnPtr _ _ _ _ => true
  | _ => false

/-- Encode the pointee `RigidTy` of a raw pointer (`*const T` / `*mut T`) into a
`Miri.MIR.TyId` strictly below `100` (disjoint from `100 + ty.layoutIdx`
aggregate IDs and `900 + ...` overflow-pair IDs): `60..82` for syntactically
known-sized pointees (`isThinRawPtrPointee`), and `40` for unsized or aggregate
pointees (which fail closed in `Deref`, `BinOp.Offset`, and `CastKind.PtrToPtr`). -/
def encodeRawPtrTyId : RigidTy → Miri.MIR.TyId
  | .tuple .nil | .fnDef _ _ => 60
  | .bool => 61
  | .char => 62
  | .int .i8 => 63
  | .int .i16 => 64
  | .int .i32 => 65
  | .int .i64 => 66
  | .int .i128 => 67
  | .int .isize => 68
  | .never => 69
  | .uint .u8 => 70
  | .uint .u16 => 71
  | .uint .u32 => 72
  | .uint .u64 => 73
  | .uint .u128 => 74
  | .uint .usize => 75
  | .float .f16 => 76
  | .float .f32 => 77
  | .float .f64 => 78
  | .float .f128 => 79
  | .rawPtr _ _ => 80
  | .ref _ _ => 81
  | .fnPtr _ _ _ _ => 82
  | _ => 40

/-- Recover the encoded pointee `Miri.MIR.TyId` from a `60..79` raw-pointer
`TyId` produced by `encodeRawPtrTyId`. Aggregate-pointee raw pointers (`40`)
and pointer-pointee raw pointers (`80..82`, whose inner pointer may be fat)
return `none`, so `BinOp.Offset` and dereferences fail closed rather than
guessing a stride or a width. -/
def rawPtrPointeeEncodedTyId? : Miri.MIR.TyId → Option Miri.MIR.TyId
  | 60 => some 51
  | 61 => some 1
  | 62 => some 2
  | 63 => some 10
  | 64 => some 11
  | 65 => some 12
  | 66 => some 13
  | 67 => some 14
  | 68 => some 15
  | 70 => some 20
  | 71 => some 21
  | 72 => some 22
  | 73 => some 23
  | 74 => some 24
  | 75 => some 25
  | 76 => some 30
  | 77 => some 31
  | 78 => some 32
  | 79 => some 33
  | _ => none

/-- Encode a scalar/pointer/unit `RigidTy` into a canonical `Miri.MIR.TyId` below `100`. -/
def encodeScalarRigidTy (k : RigidTy) : Option Miri.MIR.TyId :=
  match k with
  | .bool => some 1
  | .char => some 2
  | .int .i8 => some 10
  | .int .i16 => some 11
  | .int .i32 => some 12
  | .int .i64 => some 13
  | .int .i128 => some 14
  | .int .isize => some 15
  | .uint .u8 => some 20
  | .uint .u16 => some 21
  | .uint .u32 => some 22
  | .uint .u64 => some 23
  | .uint .u128 => some 24
  | .uint .usize => some 25
  | .float .f16 => some 30
  | .float .f32 => some 31
  | .float .f64 => some 32
  | .float .f128 => some 33
  | .rawPtr _ pointee => some (encodeRawPtrTyId pointee)
  | .ref _ _ => some 41
  | .fnPtr _ _ _ _ => some 42
  | .never => some 50
  | .tuple .nil | .fnDef _ _ => some 51
  | _ => none

/-- Canonical `Miri.ABI.LayoutData` for a scalar/pointer/unit `RigidTy`. -/
def scalarLayoutOfRigidTy (k : RigidTy) : Option Miri.ABI.LayoutData :=
  match k with
  | .bool => some (scalarLayoutData 1 false 0 1)
  | .char => some (scalarLayoutData 4 false 0 0x10FFFF)
  | .int it => some (scalarLayoutData (it.byteWidth 64) true)
  | .uint ut => some (scalarLayoutData (ut.byteWidth 64) false)
  | .float .f16 => some (floatLayoutData 2)
  | .float .f32 => some (floatLayoutData 4)
  | .float .f64 => some (floatLayoutData 8)
  | .float .f128 => some (floatLayoutData 16)
  | .rawPtr _ _ => some (pointerLayoutData false)
  | .ref _ _ => some (pointerLayoutData true)
  | .fnPtr _ _ _ _ => some (pointerLayoutData true)
  | .never => some { zstLayoutData with variants := .Empty, uninhabited := true }
  | .tuple .nil | .fnDef _ _ => some zstLayoutData
  | _ => none

/-- Encode an Anneal `Ty` into a canonical `Miri.MIR.TyId` that injectively
distinguishes all scalar primitive types (`bool`, `char`, `i8..isize`,
`u8..usize`, `f16..f128`, pointers/references), encodes homogeneous scalar arrays
with their element `TyId` in `(tyId - 1000) % 100`, and preserves `ty.layoutIdx` for
aggregates. -/
def encodeTyId (ty : Ty) : Miri.MIR.TyId :=
  match ty.kind with
  | .bool => 1
  | .char => 2
  | .int .i8 => 10
  | .int .i16 => 11
  | .int .i32 => 12
  | .int .i64 => 13
  | .int .i128 => 14
  | .int .isize => 15
  | .uint .u8 => 20
  | .uint .u16 => 21
  | .uint .u32 => 22
  | .uint .u64 => 23
  | .uint .u128 => 24
  | .uint .usize => 25
  | .float .f16 => 30
  | .float .f32 => 31
  | .float .f64 => 32
  | .float .f128 => 33
  | .rawPtr _ pointee => encodeRawPtrTyId pointee
  | .ref _ _ => 41
  | .fnPtr _ _ _ _ => 42
  | .never => 50
  | .tuple .nil | .fnDef _ _ => 51
  | .array elemKind _ =>
      match encodeScalarRigidTy elemKind with
      | some elemId => 1000 + 100 * ty.layoutIdx + elemId
      | none => 100 + ty.layoutIdx
  | _ => 100 + ty.layoutIdx

/-- Classify a `Miri.MIR.TyId` produced by `encodeTyId` into a
`Miri.Interpreter.ScalarTypeClass`. -/
def classifyEncodedTyId (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.ScalarTypeClass :=
  match tyId with
  | 1 => .ok .boolean
  | 2 => .ok .character
  | 10 => .ok (.integer .i8)
  | 11 => .ok (.integer .i16)
  | 12 => .ok (.integer .i32)
  | 13 => .ok (.integer .i64)
  | 14 => .ok (.integer .i128)
  | 15 => .ok (.integer .isize)
  | 20 => .ok (.integer .u8)
  | 21 => .ok (.integer .u16)
  | 22 => .ok (.integer .u32)
  | 23 => .ok (.integer .u64)
  | 24 => .ok (.integer .u128)
  | 25 => .ok (.integer .usize)
  | 30 | 31 | 32 | 33 => .ok .floating
  | 40 | 41 | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 | 68 | 69
  | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 | 81 | 82 | 90 => .ok .pointer
  | 42 => .ok .functionPointer
  | _ => .error (.invalidProgram s!"non-scalar TyId {tyId} in ScalarOps")

/-- Translate an Anneal `Ty` into a `Miri.Interpreter.LocalLayout`
(`Miri.ABI.TyAndLayout Miri.MIR.TyId`), using `layouts.lookup ty.layoutIdx` when
available for aggregate types or deriving the canonical scalar/pointer/ZST/array layout. -/
def translateTy (ty : Ty) (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.LocalLayout :=
  let layoutData : Miri.ABI.LayoutData :=
    match ty.kind with
    | .bool => scalarLayoutData 1 false 0 1
    | .char => scalarLayoutData 4 false 0 0x10FFFF
    | .int it => scalarLayoutData (it.byteWidth 64) true
    | .uint ut => scalarLayoutData (ut.byteWidth 64) false
    | .float .f16 => floatLayoutData 2
    | .float .f32 => floatLayoutData 4
    | .float .f64 => floatLayoutData 8
    | .float .f128 => floatLayoutData 16
    | .rawPtr _ _ => pointerLayoutData false
    | .ref _ _ => pointerLayoutData true
    | .fnPtr _ _ _ _ => pointerLayoutData true
    | .never => { zstLayoutData with variants := .Empty, uninhabited := true }
    | .tuple .nil | .fnDef _ _ => zstLayoutData
    | .array elemKind count =>
        match layouts.lookup ty.layoutIdx with
        | some tl => translateTypeLayout tl
        | none =>
            let elemLay := (scalarLayoutOfRigidTy elemKind).getD zstLayoutData
            let stride := elemLay.size
            let totalBytes := count * stride.bytes.toNat
            { fields := .Array stride (UInt64.ofNat count)
              variants := .Single 0
              backendRepr := .Memory (sized := true)
              largestNiche := none
              uninhabited := elemLay.uninhabited && decide (0 < count)
              align := elemLay.align
              size := Miri.ABI.Size.ofBytes (UInt64.ofNat totalBytes)
              maxReprAlign := none
              unadjustedAbiAlign := elemLay.unadjustedAbiAlign
              reprC := false
              randomizationSeed := 0 }
    | _ =>
        match layouts.lookup ty.layoutIdx with
        | some tl => translateTypeLayout tl
        | none => zstLayoutData
  { ty := encodeTyId ty, layout := layoutData }

/-- Reconstruct a `Miri.Interpreter.LocalLayout` from an encoded `Miri.MIR.TyId`
and a `LayoutTable`. -/
def layoutOfEncodedTyId (tyId : Miri.MIR.TyId) (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.LocalLayout :=
  match tyId with
  | 1 => translateTy { kind := .bool, layoutIdx := 0 }
  | 2 => translateTy { kind := .char, layoutIdx := 0 }
  | 10 => translateTy { kind := .int .i8, layoutIdx := 0 }
  | 11 => translateTy { kind := .int .i16, layoutIdx := 0 }
  | 12 => translateTy { kind := .int .i32, layoutIdx := 0 }
  | 13 => translateTy { kind := .int .i64, layoutIdx := 0 }
  | 14 => translateTy { kind := .int .i128, layoutIdx := 0 }
  | 15 => translateTy { kind := .int .isize, layoutIdx := 0 }
  | 20 => translateTy { kind := .uint .u8, layoutIdx := 0 }
  | 21 => translateTy { kind := .uint .u16, layoutIdx := 0 }
  | 22 => translateTy { kind := .uint .u32, layoutIdx := 0 }
  | 23 => translateTy { kind := .uint .u64, layoutIdx := 0 }
  | 24 => translateTy { kind := .uint .u128, layoutIdx := 0 }
  | 25 => translateTy { kind := .uint .usize, layoutIdx := 0 }
  | 30 => translateTy { kind := .float .f16, layoutIdx := 0 }
  | 31 => translateTy { kind := .float .f32, layoutIdx := 0 }
  | 32 => translateTy { kind := .float .f64, layoutIdx := 0 }
  | 33 => translateTy { kind := .float .f128, layoutIdx := 0 }
  | 40 | 60 | 61 | 62 | 63 | 64 | 65 | 66 | 67 | 68 | 69
  | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 | 81 | 82 =>
      { ty := tyId, layout := pointerLayoutData false }
  | 41 => translateTy { kind := .ref .not .bool, layoutIdx := 0 }
  | 42 => translateTy { kind := .fnPtr .nil .bool .safe .rust, layoutIdx := 0 }
  | 50 => translateTy { kind := .never, layoutIdx := 0 }
  | 51 => translateTy { kind := .tuple .nil, layoutIdx := 0 }
  | n =>
      let idx := n - 100
      match layouts.lookup idx with
      | some tl => { ty := tyId, layout := translateTypeLayout tl }
      | none => { ty := tyId, layout := zstLayoutData }

/-- Recover the element `LocalLayout` for a homogeneous array `baseLayout` with
element stride `stride`. When `baseLayout.ty ≥ 1000`, `(baseLayout.ty - 1000) % 100`
stores the scalar/pointer/ZST `encodeTyId` of the element type, so
`layoutOfEncodedTyId` reconstructs `translateTy { kind := elemKind, layoutIdx := 0 } layouts`
directly. -/
def arrayElemLayoutOf (layouts : LayoutTable)
    (baseLayout : Miri.Interpreter.LocalLayout) (stride : Miri.ABI.Size) :
    Miri.Interpreter.LocalLayout :=
  if baseLayout.ty ≥ 1000 then
    layoutOfEncodedTyId ((baseLayout.ty - 1000) % 100) layouts
  else
    { ty := 0
      layout :=
        { zstLayoutData with
          size := stride
          align := baseLayout.layout.align
          unadjustedAbiAlign := baseLayout.layout.unadjustedAbiAlign } }

/-! ## 2. Places, Constants, Operands, Rvalues, Statements, Terminators, Bodies -/

/-- Translate an Anneal `ProjectionElem` to `Miri.MIR.ProjectionElem`. -/
def translateProjectionElem : ProjectionElem → Miri.MIR.ProjectionElem
  | .deref => .Deref
  | .field fieldIdx ty => .Field fieldIdx (encodeTyId ty)
  | .index idxLocal => .Index idxLocal
  | .constantIndex offset minLength fromEnd => .ConstantIndex offset minLength fromEnd
  | .subslice fromIdx toIdx fromEnd => .Subslice fromIdx toIdx fromEnd
  | .downcast variantName variantIdx => .Downcast variantName variantIdx
  | .opaqueCast ty => .OpaqueCast (encodeTyId ty)
  | .unwrapUnsafeBinder ty => .UnwrapUnsafeBinder (encodeTyId ty)

/-- Translate an Anneal `Place` to `Miri.MIR.Place`. -/
def translatePlace (p : Place) : Miri.MIR.Place :=
  { localId := p.local_
    projection := (p.projection.map translateProjectionElem).toArray }

/-- Translate an Anneal `MirAst.ScalarInt` to `Miri.Memory.ScalarInt`. -/
def translateScalarInt (sc : MirAst.ScalarInt) :
    Except Miri.Memory.ScalarIntError Miri.Memory.ScalarInt := do
  let opt ← Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 sc.bits) (translateSizeBytes sc.sizeBytes)
  match opt with
  | some v => return v
  | none => throw (.integerConversionOverflow (Int.ofNat sc.bits))

/-- Translate an Anneal `ConstScalar` to `Miri.MIR.ScalarValue`. -/
def translateConstScalar : ConstScalar → Miri.MIR.ScalarValue
  | .int sc => .Int sc.bits sc.sizeBytes
  | .ptr p _ => .Ptr (.Allocation p.allocId p.offsetBytes false false)

/-- Translate an Anneal `ConstValue` to `Miri.MIR.ConstValue`. -/
def translateConstValue : ConstValue → Miri.MIR.ConstValue
  | .zeroSized => .ZeroSized
  | .scalar s => .Scalar (translateConstScalar s)
  | .slice (.ptr p _) meta_ => .Slice p.allocId meta_
  | .slice (.int sc) meta_ => .Slice sc.bits meta_
  | .indirect allocId offsetBytes => .Indirect allocId offsetBytes
  | .unevaluated _ => .ZeroSized

/-- Dummy `Miri.MIR.SpanRef` for translated MIR nodes. -/
def defaultSpanRef : Miri.MIR.SpanRef :=
  { id := 0 }

/-- Dummy `Miri.MIR.SourceInfo` for translated MIR statements and terminators. -/
def defaultSourceInfo : Miri.MIR.SourceInfo :=
  { span := defaultSpanRef, scope := 0 }

/-- Translate an Anneal `ConstOperand` to `Miri.MIR.ConstOperand`. -/
def translateConstOperand (c : ConstOperand) : Miri.MIR.ConstOperand :=
  let mirConst : Miri.MIR.MirConst :=
    match c.val with
    | .unevaluated _ =>
        .Unevaluated { definition := 0, arguments := #[], promoted := none } (encodeTyId c.ty)
    | cv => .Val (translateConstValue cv) (encodeTyId c.ty)
  { span := defaultSpanRef, userType := none, value := mirConst }

/-- Translate an Anneal `Operand` to `Miri.MIR.Operand`. -/
def translateOperand : Operand → Miri.MIR.Operand
  | .copy p => .Copy (translatePlace p)
  | .move p => .Move (translatePlace p)
  | .constant c => .Constant (translateConstOperand c)

/-- Translate an Anneal `BinOp` to `Miri.MIR.BinOp`. -/
def translateBinOp : BinOp → Miri.MIR.BinOp
  | .add => .Add
  | .addUnchecked => .AddUnchecked
  | .addWithOverflow => .AddWithOverflow
  | .sub => .Sub
  | .subUnchecked => .SubUnchecked
  | .subWithOverflow => .SubWithOverflow
  | .mul => .Mul
  | .mulUnchecked => .MulUnchecked
  | .mulWithOverflow => .MulWithOverflow
  | .div => .Div
  | .rem => .Rem
  | .bitXor => .BitXor
  | .bitAnd => .BitAnd
  | .bitOr => .BitOr
  | .shl => .Shl
  | .shlUnchecked => .ShlUnchecked
  | .shr => .Shr
  | .shrUnchecked => .ShrUnchecked
  | .eq => .Eq
  | .lt => .Lt
  | .le => .Le
  | .ne => .Ne
  | .ge => .Ge
  | .gt => .Gt
  | .cmp => .Cmp
  | .offset => .Offset

/-- Translate an Anneal `UnOp` to `Miri.MIR.UnOp`. -/
def translateUnOp : UnOp → Miri.MIR.UnOp
  | .not => .Not
  | .neg => .Neg
  | .ptrMetadata => .PtrMetadata

/-- Translate an Anneal `BorrowKind` to `Miri.MIR.BorrowKind`. -/
def translateBorrowKind : BorrowKind → Miri.MIR.BorrowKind
  | .shared => .Shared
  | .mut false => .Mut .Default
  | .mut true => .Mut .TwoPhaseBorrow

/-- Translate an Anneal `Mutability` to `Miri.MIR.RawPtrKind`. -/
def translateRawPtrKind : Mutability → Miri.MIR.RawPtrKind
  | .not => .Const
  | .mut => .Mut

/-- Translate Anneal's `Debug`-formatted `PointerCoercion` tag string
(`rustc_middle::ty::adjustment::PointerCoercion` emitted by `rustc-capture`) to
`Miri.MIR.PointerCoercion`. Unrecognized strings map to `.MutToConstPointer`,
which `Miri.Interpreter.Cast.cast` rejects in runtime MIR with
`StepError.invalidProgram`. -/
def translatePointerCoercion : String → Miri.MIR.PointerCoercion
  | "ReifyFnPointer(Safe)" | "ReifyFnPointer" => .ReifyFnPointer .Safe
  | "ReifyFnPointer(Unsafe)" => .ReifyFnPointer .Unsafe
  | "UnsafeFnPointer" => .UnsafeFnPointer
  | "ClosureFnPointer(Safe)" | "ClosureFnPointer(Normal)" => .ClosureFnPointer .Safe
  | "ClosureFnPointer(Unsafe)" => .ClosureFnPointer .Unsafe
  | "MutToConstPointer" => .MutToConstPointer
  | "ArrayToPointer" => .ArrayToPointer
  | "Unsize" => .Unsize
  | _ => .MutToConstPointer

/-- Translate an Anneal `CastKind` to `Miri.MIR.CastKind`. -/
def translateCastKind : CastKind → Miri.MIR.CastKind
  | .intToInt => .IntToInt
  | .floatToInt => .FloatToInt
  | .floatToFloat => .FloatToFloat
  | .intToFloat => .IntToFloat
  | .ptrToPtr => .PtrToPtr
  | .fnPtrToPtr => .FnPtrToPtr
  | .pointerExposeProvenance => .PointerExposeProvenance
  | .pointerWithExposedProvenance => .PointerWithExposedProvenance
  | .pointerCoercion ck => .PointerCoercion (translatePointerCoercion ck) .Implicit
  | .transmute => .Transmute
  | .subtype => .Subtype

/-- Translate an Anneal `AggregateKind` to `Miri.MIR.AggregateKind`. -/
def translateAggregateKind : AggregateKind → Miri.MIR.AggregateKind
  | .array elemTy => .Array (encodeTyId elemTy)
  | .tuple => .Tuple
  | .adt _ variantIdx activeField =>
      .Adt 0 variantIdx #[] none activeField
  | .closure _ => .Closure 0 #[]
  | .coroutine _ => .Coroutine 0 #[]
  | .rawPtr pointeeTy mutability =>
      .RawPtr (encodeTyId pointeeTy) (match mutability with | .not => .Not | .mut => .Mut)

/-- An unevaluated constant of type `ty`. `evalMirConstImmediate` reports
`StepError.unsupported` for it, never a value and never undefined behavior. -/
def untranslatableConstOperand (ty : Ty) : Miri.MIR.ConstOperand :=
  { span := defaultSpanRef
    userType := none
    value := .Unevaluated { definition := 0, arguments := #[], promoted := none } (encodeTyId ty) }

/-- Synthetic `Miri.MIR.TyId` that `annealProjectList` assigns to
`ProjectionElem.UnwrapUnsafeBinder arraySliceMetaTyId` when `translateRvalue`
lowers `Rvalue.len place`. It is disjoint from every `encodeTyId` output (`1, 2,
10..15, 20..25, 30..33, 40..42, 50, 51, 60..82`, and `≥ 100`), so no source-MIR
`ProjectionElem` (`translateProjectionElem`) can produce it.
`annealReadImmediate` extracts `(address, length)` metadata only for
`arraySliceMetaTyId` and rejects all other whole-array immediate reads (`ty ≠ 90`)
with `StepError.unsupported`, while `annealProjectionCx.subsliceLayout` rejects
all array subslices (both partial and whole-array) with `StepError.unsupported`. -/
def arraySliceMetaTyId : Miri.MIR.TyId := 90

/-- Translate an Anneal `Rvalue` to `Miri.MIR.Rvalue`.

The pinned rustc MIR (`Miri.MIR.Rvalue`) has no `Rvalue::Len`,
`Rvalue::ShallowInitBox`, or `NullOp::{SizeOf, AlignOf, OffsetOf}`.

* `len place` becomes `UnaryOp(PtrMetadata, Copy(place.UnwrapUnsafeBinder(arraySliceMetaTyId)))`,
  appending `ProjectionElem.UnwrapUnsafeBinder arraySliceMetaTyId` to
  `translatePlace place`. This is a modeling device, not rustc's lowering:
  rustc applies `PtrMetadata` to a pointer (for slices, a `&raw const (fake)`
  borrow of the place) and uses a constant for arrays. Because `encodeTyId`
  never returns `arraySliceMetaTyId` (`90`), no source-MIR projection can forge
  this tag (`translateProjectionElem`). `annealEvalOperand` first checks that an
  immediate local is initialized and every byte of a memory-backed array is
  initialized; `annealProjectList` then transmutes an array place's `LocalLayout`
  to `{ ty := arraySliceMetaTyId, layout := base.layout.layout }` (failing closed
  on non-arrays), `annealReadImmediate` reads `(address, length)` exclusively for
  `arraySliceMetaTyId` (while `subsliceLayout` rejects all array subslices and
  `annealReadImmediate` rejects all other whole-array reads with
  `StepError.unsupported`), and `PtrMetadata` extracts the length. This matches
  Anneal's `evalRvalue (.len place)`, except for an uninitialized memory-backed
  zero-length array, which has no bytes whose initialization could be checked.
* Rather than invent a meaning for `shallowInitBox` and the unsupported nullary
  operators, the translation maps them to an unevaluated constant, which
  `evalMirConstImmediate` rejects with `unsupported`. -/
def translateRvalue : Rvalue → Miri.MIR.Rvalue
  | .use op => .Use (translateOperand op) .No
  | .repeat op count =>
      .Repeat
        (translateOperand op)
        (.Value
          (encodeTyId { kind := .uint .usize, layoutIdx := 0 })
          { nodes := #[.Leaf count 8], root := 0 })
  | .ref bk place =>
      .Ref .Erased (translateBorrowKind bk) (translatePlace place)
  | .threadLocalRef _ => .ThreadLocalRef 0
  | .rawPtr mutability place => .RawPtr (translateRawPtrKind mutability) (translatePlace place)
  | .len place =>
      let mp := translatePlace place
      .UnaryOp .PtrMetadata
        (.Copy { mp with projection := mp.projection.push (.UnwrapUnsafeBinder arraySliceMetaTyId) })
  | .cast kind op targetTy =>
      .Cast (translateCastKind kind) (translateOperand op) (encodeTyId targetTy)
  | .binaryOp op lhs rhs =>
      .BinaryOp (translateBinOp op) (translateOperand lhs) (translateOperand rhs)
  | .nullaryOp .ubChecks _ => .Use (.RuntimeChecks .UbChecks) .No
  | .nullaryOp .contractChecks _ => .Use (.RuntimeChecks .ContractChecks) .No
  | .nullaryOp _ ty => .Use (.Constant (untranslatableConstOperand ty)) .No
  | .unaryOp op operand =>
      .UnaryOp (translateUnOp op) (translateOperand operand)
  | .discriminant place => .Discriminant (translatePlace place)
  | .aggregate kind ops =>
      .Aggregate (translateAggregateKind kind) (ops.map translateOperand).toArray
  | .shallowInitBox _ contentTy =>
      .Use (.Constant (untranslatableConstOperand contentTy)) .No
  | .copyForDeref place => .CopyForDeref (translatePlace place)
  | .wrapUnsafeBinder op targetTy =>
      .WrapUnsafeBinder (translateOperand op) (encodeTyId targetTy)

/-- Translate an Anneal `RetagKind` to `Miri.TreeBorrows.RetagPolicy.RetagMode`. -/
def translateRetagKind : RetagKind → Miri.TreeBorrows.RetagPolicy.RetagMode
  | .fnEntry => .FnEntry
  | .twoPhase => .TwoPhase
  | .raw => .Raw
  | .default => .Default

/-- Translate an Anneal `StatementKind` to `Miri.MIR.StatementKind`.

Pinned rustc (`Miri.MIR.StatementKind`) removed standalone `Deinit` and
`Retag` statements (folding retags into `Rvalue.Use _ .Yes`, `Rvalue.Ref`, and
call entry). Rather than silently mapping them to no-op `PlaceMention`
statements, `translateStmtKind` lowers them to an assignment of
`untranslatableConstOperand` so `Step.evalStatement` rejects them with
`StepError.unsupported` (or `StepError.stack` if the destination local is out
of bounds), never a silent success or undefined behavior. -/
def translateStmtKind : StatementKind → Miri.MIR.StatementKind
  | .assign place rv => .Assign (translatePlace place) (translateRvalue rv)
  | .setDiscriminant place variantIdx => .SetDiscriminant (translatePlace place) variantIdx
  | .deinit place =>
      .Assign (translatePlace place)
        (.Use (.Constant (untranslatableConstOperand { kind := .tuple .nil, layoutIdx := 0 })) .No)
  | .storageLive local_ => .StorageLive local_
  | .storageDead local_ => .StorageDead local_
  | .retag _ place =>
      .Assign (translatePlace place)
        (.Use (.Constant (untranslatableConstOperand { kind := .tuple .nil, layoutIdx := 0 })) .No)
  | .placeMention place => .PlaceMention (translatePlace place)
  | .intrinsic (.assume op) => .Intrinsic (.Assume (translateOperand op))
  | .intrinsic (.copyNonOverlapping src dst count) =>
      .Intrinsic (.CopyNonOverlapping
        { source := translateOperand src
          destination := translateOperand dst
          count := translateOperand count })
  | .coverage => .Coverage (.BlockMarker 0)
  | .constEvalCounter => .ConstEvalCounter
  | .backwardIncompatibleDropHint place =>
      .BackwardIncompatibleDropHint (translatePlace place) .Edition2024
  | .nop => .Nop

/-- Translate an Anneal `Statement` to `Miri.MIR.Statement`. -/
def translateStmt (stmt : Statement) : Miri.MIR.Statement :=
  { sourceInfo := defaultSourceInfo, kind := translateStmtKind stmt.kind }

/-- Translate an Anneal `SwitchTargets` to `Miri.MIR.SwitchTargets`. -/
def translateSwitchTargets (st : SwitchTargets) : Miri.MIR.SwitchTargets :=
  { cases := (st.branches.map fun (v, bb) => Miri.MIR.SwitchTarget.Case v bb).toArray
    otherwise := st.otherwise }

/-- Translate an Anneal `UnwindAction` to `Miri.MIR.UnwindAction`. -/
def translateUnwindAction : UnwindAction → Miri.MIR.UnwindAction
  | .continue_ => .Continue
  | .unreachable => .Unreachable
  | .terminate => .Terminate .Abi
  | .cleanup bb => .Cleanup bb

/-- Default `Miri.MIR.InlineAsmOptions` with all flags false. -/
def defaultInlineAsmOptions : Miri.MIR.InlineAsmOptions :=
  { pure := false
    nomem := false
    readonly := false
    preservesFlags := false
    noReturn := false
    noStack := false
    attSyntax := false
    raw := false
    mayUnwind := false }

/-- The `core::intrinsics` items whose calls Anneal's
`MirSemantics.evalTerminator` evaluates inline (`exact_div`, and every intrinsic
of `MirSemantics.evalInlineIntrinsicCall?`) and whose translated calls
`annealCallHooks` dispatches through `lean-miri`'s
`Miri.Interpreter.Intrinsics.eval` (`LM-4.2`). -/
inductive AnnealIntrinsic where
  | exactDiv
  | writeBytes
  | arithOffset
  | wrappingOffset
  | ctpop
  | ctlz
  | ctlzNonzero
  | cttz
  | cttzNonzero
  | bswap
  | bitreverse
  | rotateLeft
  | rotateRight
  | saturatingAdd
  | saturatingSub
  deriving DecidableEq, Repr

namespace AnnealIntrinsic

/-- Canonical `DefPath` that `rustc-capture` records for the intrinsic's
function item. -/
def defPath : AnnealIntrinsic → DefPath
  | .exactDiv => "core::intrinsics::exact_div"
  | .writeBytes => "core::intrinsics::write_bytes"
  | .arithOffset => "core::intrinsics::arith_offset"
  | .wrappingOffset => "core::intrinsics::wrapping_offset"
  | .ctpop => "core::intrinsics::ctpop"
  | .ctlz => "core::intrinsics::ctlz"
  | .ctlzNonzero => "core::intrinsics::ctlz_nonzero"
  | .cttz => "core::intrinsics::cttz"
  | .cttzNonzero => "core::intrinsics::cttz_nonzero"
  | .bswap => "core::intrinsics::bswap"
  | .bitreverse => "core::intrinsics::bitreverse"
  | .rotateLeft => "core::intrinsics::rotate_left"
  | .rotateRight => "core::intrinsics::rotate_right"
  | .saturatingAdd => "core::intrinsics::saturating_add"
  | .saturatingSub => "core::intrinsics::saturating_sub"

/-- The intrinsic's name (rustc's `sym::*` symbol), on which
`Miri.Interpreter.Intrinsics.eval` dispatches. Both `arith_offset` and its
`wrapping_offset` alias dispatch to `"arith_offset"`. -/
def name : AnnealIntrinsic → String
  | .exactDiv => "exact_div"
  | .writeBytes => "write_bytes"
  | .arithOffset | .wrappingOffset => "arith_offset"
  | .ctpop => "ctpop"
  | .ctlz => "ctlz"
  | .ctlzNonzero => "ctlz_nonzero"
  | .cttz => "cttz"
  | .cttzNonzero => "cttz_nonzero"
  | .bswap => "bswap"
  | .bitreverse => "bitreverse"
  | .rotateLeft => "rotate_left"
  | .rotateRight => "rotate_right"
  | .saturatingAdd => "saturating_add"
  | .saturatingSub => "saturating_sub"

/-- Number of value arguments of the intrinsic's signature. -/
def arity : AnnealIntrinsic → Nat
  | .writeBytes => 3
  | .ctpop | .ctlz | .ctlzNonzero | .cttz | .cttzNonzero | .bswap | .bitreverse => 1
  | .exactDiv | .arithOffset | .wrappingOffset | .rotateLeft | .rotateRight
  | .saturatingAdd | .saturatingSub => 2

/-- The correspondence-local `Miri.MIR.DefId` of the intrinsic. Every value is
below `64`, so `annealFnItemTyId` can pack it with a generic argument. -/
def defId : AnnealIntrinsic → Miri.MIR.DefId
  | .exactDiv => 1
  | .writeBytes => 2
  | .arithOffset => 3
  | .ctpop => 4
  | .ctlz => 5
  | .ctlzNonzero => 6
  | .cttz => 7
  | .cttzNonzero => 8
  | .bswap => 9
  | .bitreverse => 10
  | .rotateLeft => 11
  | .rotateRight => 12
  | .saturatingAdd => 13
  | .saturatingSub => 14
  | .wrappingOffset => 15

/-- Inverse of `defId`. -/
def ofDefId? : Miri.MIR.DefId → Option AnnealIntrinsic
  | 1 => some .exactDiv
  | 2 => some .writeBytes
  | 3 => some .arithOffset
  | 4 => some .ctpop
  | 5 => some .ctlz
  | 6 => some .ctlzNonzero
  | 7 => some .cttz
  | 8 => some .cttzNonzero
  | 9 => some .bswap
  | 10 => some .bitreverse
  | 11 => some .rotateLeft
  | 12 => some .rotateRight
  | 13 => some .saturatingAdd
  | 14 => some .saturatingSub
  | 15 => some .wrappingOffset
  | _ => none

/-- All intrinsics, in `defId` order. -/
def all : List AnnealIntrinsic :=
  [.exactDiv, .writeBytes, .arithOffset, .ctpop, .ctlz, .ctlzNonzero, .cttz, .cttzNonzero,
    .bswap, .bitreverse, .rotateLeft, .rotateRight, .saturatingAdd, .saturatingSub,
    .wrappingOffset]

/-- Recognize an intrinsic by the canonical `DefPath` of its function item (and
`std::intrinsics::arith_offset` / `wrapping_offset` aliases), with the same byte
comparison (`stringEq`) that `MirSemantics.evalTerminator` uses. -/
def ofDefPath? (p : DefPath) : Option AnnealIntrinsic :=
  match all.find? (fun k => stringEq p k.defPath) with
  | some k => some k
  | none =>
    if stringEq p "std::intrinsics::arith_offset" then some .arithOffset
    else if stringEq p "std::intrinsics::wrapping_offset" then some .wrappingOffset
    else none

end AnnealIntrinsic

/-- Smallest `Miri.MIR.TyId` that `annealFnItemTyId` assigns. Only callee
operands are decoded with `annealDecodeFnItemTyId`, and the callee operand of a
translated call is an `annealFnItemTyId` constant, another function item
(`TyId 51`), or a function pointer (`TyId 42`), so every TyId at or above this
base that reaches the decoder names an intrinsic. -/
def annealFnItemTyIdBase : Miri.MIR.TyId := 128

/-- `Miri.MIR.TyId` of the function item type `FnDef(k, [T])` of intrinsic `k`
instantiated at the type whose encoding is `argTy`.

`encodeTyId` maps every function item type to `51`, which drops the identity of
the called function. In rustc that identity lives in the callee operand's type
`FnDef(def_id, args)`, which `eval_callee_and_args` passes to `resolve`. The
callee operand of a translated intrinsic call therefore carries this TyId
instead, and `annealCallHooks.functionKind` decodes it with
`annealDecodeFnItemTyId`. The packing `base + defId + 64 * argTy` is injective
because every `defId` is below `64`. -/
def annealFnItemTyId (k : AnnealIntrinsic) (argTy : Miri.MIR.TyId) : Miri.MIR.TyId :=
  annealFnItemTyIdBase + k.defId + 64 * argTy

/-- Decode a TyId produced by `annealFnItemTyId`. -/
def annealDecodeFnItemTyId (tyId : Miri.MIR.TyId) : Option (AnnealIntrinsic × Miri.MIR.TyId) :=
  if annealFnItemTyIdBase ≤ tyId then
    match AnnealIntrinsic.ofDefId? ((tyId - annealFnItemTyIdBase) % 64) with
    | some k => some (k, (tyId - annealFnItemTyIdBase) / 64)
    | none => none
  else
    none

/-- Translate the callee operand of a `TerminatorKind.call`.

A constant function item of an `AnnealIntrinsic` with one generic type argument
`T` (`fnDef p [T]`) becomes the zero-sized constant of type
`annealFnItemTyId k (encodeTyId T)`, which records the intrinsic and its type
argument; every other callee is translated by `translateOperand`. -/
def translateCalleeOperand (func : Operand) : Miri.MIR.Operand :=
  match func with
  | .constant c =>
    match c.ty.kind with
    | .fnDef p (argKind :: .nil) =>
      match AnnealIntrinsic.ofDefPath? p with
      | some k =>
        .Constant
          { span := defaultSpanRef
            userType := none
            value := .Val .ZeroSized
              (annealFnItemTyId k (encodeTyId { kind := argKind, layoutIdx := 0 })) }
      | none => translateOperand func
    | _ => translateOperand func
  | _ => translateOperand func

/-- Translate an Anneal `TerminatorKind` to `Miri.MIR.TerminatorKind`. -/
def translateTerminatorKind : TerminatorKind → Miri.MIR.TerminatorKind
  | .goto target => .Goto target #[]
  | .switchInt discr targets =>
      .SwitchInt (translateOperand discr) (translateSwitchTargets targets)
  | .unwindResume => .UnwindResume
  | .unwindTerminate => .UnwindTerminate .Abi
  | .return_ => .Return
  | .unreachable => .Unreachable
  | .drop place target unwind =>
      .Drop (translatePlace place) target (translateUnwindAction unwind) false none
  | .call func args destination target unwind =>
      .Call (translateCalleeOperand func)
        (args.map fun a => ({ span := defaultSpanRef, operand := translateOperand a } : Miri.MIR.SpannedOperand)).toArray
        (translatePlace destination)
        target
        (translateUnwindAction unwind)
        .Normal
        defaultSpanRef
  | .tailCall func args =>
      .TailCall (translateOperand func)
        (args.map fun a => ({ span := defaultSpanRef, operand := translateOperand a } : Miri.MIR.SpannedOperand)).toArray
        defaultSpanRef
  | .assert cond expected target unwind =>
      let op := translateOperand cond
      .Assert op expected (.BoundsCheck op op) target (translateUnwindAction unwind)
  | .inlineAsm _ targets unwind =>
      .InlineAsm
        { asmMacro := .Asm
          template := #[]
          operands := #[]
          options := defaultInlineAsmOptions
          lineSpans := #[]
          targets := targets.toArray
          unwind := translateUnwindAction unwind }

/-- Translate an Anneal `Terminator` to `Miri.MIR.Terminator`. -/
def translateTerminator (term : Terminator) : Miri.MIR.Terminator :=
  { sourceInfo := defaultSourceInfo, kind := translateTerminatorKind term.kind }

/-- Translate an Anneal `BasicBlockData` to `Miri.MIR.BasicBlock`. -/
def translateBasicBlockData (bb : BasicBlockData) : Miri.MIR.BasicBlock :=
  { statements := (bb.statements.map translateStmt).toArray
    terminator := translateTerminator bb.terminator
    cleanup := bb.isCleanup }

/-- Translate an Anneal `MirPhaseTag` to `Miri.MIR.MirPhase`. -/
def translateMirPhase : MirPhaseTag → Miri.MIR.MirPhase
  | .runtimePostCleanup => .Runtime .PostCleanup
  | .runtimeOptimized => .Runtime .Optimized
  | .other "built" => .Built
  | .other "analysis-initial" => .Analysis .Initial
  | .other "analysis-post-cleanup" => .Analysis .PostCleanup
  | .other "runtime-initial" => .Runtime .Initial
  | .other _ => .Built

/-- Translate an Anneal `CapturedMir` body to `Miri.MIR.Body`. -/
def translateBody (cm : CapturedMir) : Miri.MIR.Body :=
  { phase := translateMirPhase cm.phase
    argumentCount := cm.argCount
    spreadArgument := none
    locals := (cm.localDecls.map fun d => encodeTyId d.ty).toArray
    basicBlocks := (cm.basicBlocks.map translateBasicBlockData).toArray }

/-! ## 3. Single-Threaded Anneal Step State & Interpreter Hooks -/

/-- Provenance type instantiated for Anneal's correspondence with `lean-miri`. -/
abbrev AnnealProv := Miri.Memory.Provenance

/-- Allocation memory state instantiated with `AnnealProv`, optional Tree Borrows
per-allocation trees (`LM-3.3`), and `MiriMemoryKind`. -/
abbrev AnnealMemory :=
  Miri.Memory.MemoryState
    AnnealProv
    (Option Miri.TreeBorrows.BorrowTree)
    Miri.Memory.MiriMemoryKind

/-- Single-threaded `lean-miri` machine state for Anneal correspondence, bundling:
* `memory`: `AnnealMemory` (`MemoryState` with optional `BorrowTree` extras),
* `addresses`: `Miri.Memory.AllocAddresses.GlobalAddressState` mapping live
  `AllocId`s to 64-bit virtual base addresses (`baseAddr`), and
* `borrowTracker`: optional `Miri.Interpreter.MachineHooks.BorrowState` (`LM-3.3`). -/
structure AnnealMachine : Type where
  memory : AnnealMemory := Miri.Memory.MemoryState.empty
  addresses : Miri.Memory.AllocAddresses.GlobalAddressState :=
    { provenanceMode := .default, addressMode := .managed, generation := none }
  borrowTracker : Option Miri.Interpreter.MachineHooks.BorrowState := none

namespace AnnealMachine

/-- Empty initial `AnnealMachine` with no allocations, cached base addresses, or borrow tracker. -/
def empty : AnnealMachine := {}

/-- Look up the cached 64-bit virtual base address for `allocId` in `mach.addresses`. -/
def lookupBaseAddr (mach : AnnealMachine) (allocId : Miri.Memory.AllocId) : Option UInt64 :=
  (mach.addresses.baseAddr.find? (fun entry => entry.allocId == allocId)).map (fun entry => entry.address)

end AnnealMachine

/-- Step state for `lean-miri` instantiated with `AnnealProv`, `LocalLayout`,
`Unit` frame extra, and `AnnealMachine`. -/
abbrev AnnealStepState :=
  Miri.Interpreter.StepState
    AnnealProv
    Miri.Interpreter.LocalLayout
    Unit
    AnnealMachine

/-- Look up the `Miri.Interpreter.LocalLayout` for a `Local` in `localDecls` and `layouts`. -/
def lookupLocalDeclLayout (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) : Option Miri.Interpreter.LocalLayout :=
  match get? localDecls localId with
  | some decl => some (translateTy decl.ty layouts)
  | none => none

/-- Construct a canonical `(T, bool)` scalar-pair layout for checked arithmetic
overflow operations when no matching tuple declaration is present in `localDecls`,
rounding `size` up to `elemLay.layout.align.abi` (`Size.alignTo`) so tuple size
is a valid ABI multiple of alignment. -/
def overflowPairLayout (elemLay : Miri.Interpreter.LocalLayout) : Miri.Interpreter.LocalLayout :=
  let boolPrim : Miri.ABI.Primitive := .Int .I8 false
  let boolRange : Miri.ABI.WrappingRange := { start := 0, «end» := 1 }
  let boolSc : Miri.ABI.Scalar := .Initialized (value := boolPrim) (validRange := boolRange)
  let elemSc : Miri.ABI.Scalar :=
    match elemLay.layout.backendRepr with
    | .Scalar s => s
    | _ =>
        .Initialized
          (value := .Int .I64 false)
          (validRange := { start := 0, «end» := BitVec.ofNat 128 ((2 ^ 64) - 1) })
  let bOff := elemLay.layout.size
  let unalignedSize := (bOff.add (Miri.ABI.Size.ofBytes 1)).toOption.getD bOff
  let totalSize := (unalignedSize.alignTo elemLay.layout.align.abi).toOption.getD unalignedSize
  { ty := 900 + elemLay.ty
    layout :=
      { elemLay.layout with
        fields := .Arbitrary #[Miri.ABI.Size.ZERO, bOff] #[0, 1]
        backendRepr := .ScalarPair (a := elemSc) (b := boolSc) (bOffset := bOff)
        size := totalSize } }

/-- Resolve the `LocalLayout` of a `(T, bool)` tuple declared in `localDecls`
whose element `T` encodes to `elemLay.ty`, falling back to `overflowPairLayout elemLay`
when no `(T, bool)` tuple declaration appears in `localDecls`. -/
def findOverflowTupleLayout (localDecls : List LocalDecl) (layouts : LayoutTable)
    (elemLay : Miri.Interpreter.LocalLayout) : Miri.Interpreter.LocalLayout :=
  match localDecls with
  | .nil => overflowPairLayout elemLay
  | decl :: rest =>
      match decl.ty.kind with
      | .tuple (.cons elemKind (.cons .bool .nil)) =>
          if encodeTyId { kind := elemKind, layoutIdx := 0 } == elemLay.ty then
            translateTy decl.ty layouts
          else
            findOverflowTupleLayout rest layouts elemLay
      | _ => findOverflowTupleLayout rest layouts elemLay

/-- 64-bit target pointer arithmetic context (`pointerSize = 8` bytes). -/
def annealPointerArithmetic : Miri.Memory.PointerArithmetic :=
  { pointerSize := Miri.ABI.Size.ofBytes 8 }

/-- Resolve a `Miri.Memory.Pointer (Option AnnealProv)` against the cached base
addresses in `mach.addresses` (`Miri.Memory.PointerResolver`).

* A pointer without provenance (`ptr.provenance = none`, such as a null or
  integer-cast pointer) fails with `.error ptr.offset.bytes`, which
  `Miri.Memory.checkAndDerefPtr` reports as
  `AccessError.danglingIntegerPointer`.
* A pointer with concrete provenance `some (.concrete allocId borTag)` resolves
  to allocation-relative offset `ptr.offset.bytes - baseAddr` when
  `mach.lookupBaseAddr allocId = some baseAddr` and
  `baseAddr ≤ ptr.offset.bytes`. -/
def annealResolvePtr (mach : AnnealMachine) :
    Miri.Memory.PointerResolver AnnealProv Miri.Memory.BorTag :=
  fun ptr _signedSize =>
    match ptr.provenance with
    | none => .error ptr.offset.bytes
    | some (.concrete allocId borTag) =>
      match mach.lookupBaseAddr allocId with
      | some baseAddr =>
        if baseAddr ≤ ptr.offset.bytes then
          .ok ⟨allocId, Miri.ABI.Size.ofBytes (ptr.offset.bytes - baseAddr), borTag⟩
        else
          .error ptr.offset.bytes
      | none => .error ptr.offset.bytes
    | some .wildcard => .error ptr.offset.bytes

/-- Wrapping allocation-relative pointer resolver (`ptr.offset.bytes - baseAddr`
modulo `2 ^ 64`) used by `annealReadMemoryPlace` and `annealWriteMemoryPlace`.
Whenever `baseAddr ≤ ptr.offset.bytes` (including all `annealStackBaseAddr`
stack allocations with `allocId < 2 ^ 32` and `offsetBytes < 2 ^ 32`), this
agrees identically with `annealResolvePtr`, while also resolving projected
element `MemPlace`s produced by `Pointer.wrappingSignedOffset` when `MemPlaceRel`
permits `baseAddr + relOffset + elemOff` to wrap `2 ^ 64` (out-of-bounds negative
wraps are still rejected by `Miri.Memory.checkedBounds` against `alloc.byteSize`). -/
def annealResolvePtrWrapping (mach : AnnealMachine) :
    Miri.Memory.PointerResolver AnnealProv Miri.Memory.BorTag :=
  fun ptr _signedSize =>
    match ptr.provenance with
    | none => .error ptr.offset.bytes
    | some (.concrete allocId borTag) =>
      match mach.lookupBaseAddr allocId with
      | some baseAddr =>
        .ok ⟨allocId, Miri.ABI.Size.ofBytes (ptr.offset.bytes - baseAddr), borTag⟩
      | none => .error ptr.offset.bytes
    | some .wildcard => .error ptr.offset.bytes

/-- Look up live allocation metadata for `allocId` in `mach.memory.live`
(`Miri.Memory.LiveAllocationLookup`).

If `allocId` has been deallocated (for example, by `StorageDead`), it is absent
from `mach.memory.live` and this lookup returns
`.error (.deadAllocation allocId)`, which `Miri.Memory.checkAndDerefPtr`
reports as `AccessError.allocationLookup (.deadAllocation allocId)`. -/
def annealLookupAlloc (mach : AnnealMachine) : Miri.Memory.LiveAllocationLookup :=
  fun allocId =>
    match mach.memory.live.find? (fun entry => entry.1 == allocId) with
    | some (_, localAlloc) =>
      .ok
        { size := localAlloc.allocation.byteSize
          align := localAlloc.allocation.align
          kind := .liveData
          mutability := localAlloc.allocation.mutability }
    | none => .error (.deadAllocation allocId)

/-- Compiler-only scalar leaves (`Miri.Interpreter.ExecutionScalar.Leaves`) for
Anneal's single-threaded machine, passed to
`Miri.Interpreter.ExecutionScalar.pointerBinary`. -/
def annealExecutionScalarLeaves (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.ExecutionScalar.Leaves AnnealStepState Unit where
  classify := fun _ tyId =>
    match classifyEncodedTyId tyId with
    | .ok cls => pure cls
    | .error err => throw err
  boolLayout := fun _ => pure (translateTy { kind := .bool, layoutIdx := 0 })
  orderingLayout := fun _ => pure (translateTy { kind := .int .i8, layoutIdx := 0 })
  overflowLayout := fun _ lay => pure (findOverflowTupleLayout localDecls layouts lay)
  metadataLayout := fun _ _ => pure (translateTy { kind := .uint .usize, layoutIdx := 0 })
  unitLayout := fun _ => pure (translateTy { kind := .tuple .nil, layoutIdx := 0 })

/-- Pointer binary operations (`Eq`/`Ne`/`Lt`/`Le`/`Gt`/`Ge` and `BinOp.Offset`)
for Anneal's single-threaded machine, matching
`Miri.Interpreter.ExecutionScalar` (`ExecutionScalar.lean`) and
`Miri.Interpreter.ptrOffsetInbounds`:
1. Relational pointer comparisons (`Eq`, `Ne`, `Lt`, `Le`, `Gt`, `Ge`) delegate
   directly to `Miri.Interpreter.ExecutionScalar.pointerBinary`, comparing
   64-bit addresses via `Scalar.toBits` on `AnnealProv` (`offsetIsAddr = true`).
2. `BinOp.Offset` extracts the pointer scalar (`toPointer`), resolves the
   pointee layout via `rawPtrPointeeEncodedTyId?` and `layoutOfEncodedTyId`,
   scales `right` by `pointeeLay.layout.size` via checked multiplication
   (`IntegerOps.binary .MulWithOverflow`, reporting `StepError.undefinedBehavior
   "PointerArithOverflow"` on overflow or unsigned delta `>= 2^63`), and runs
   `Miri.Interpreter.ptrOffsetInbounds` against `annealResolvePtr` and
   `annealLookupAlloc`.
3. Atomic-pointer arithmetic (`Add`, `Sub`, `BitOr`, `BitAnd`, `BitXor`) fails
   closed with `StepError.unsupported`. -/
@[irreducible]
def annealPointerBinary (layouts : LayoutTable) (op : Miri.MIR.BinOp)
    (left right : Miri.Interpreter.RvalueImmTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  fun st =>
    match op with
    | .Eq | .Ne | .Lt | .Le | .Gt | .Ge =>
      Miri.Interpreter.ExecutionScalar.pointerBinary
        annealTargetDataLayout
        (annealExecutionScalarLeaves .nil layouts)
        (fun _ tyId => pure (decide (60 ≤ tyId ∧ tyId ≤ 82)))
        (fun _ => pure (translateTy { kind := .uint .usize, layoutIdx := 0 }))
        () op left right st
    | _ =>
      if op != .Offset then
        .error (.unsupported "pointerBinary not supported in scalar/pointer fragment") st
      else
        match left.imm.toScalar with
        | .error err => .error (Miri.Interpreter.ScalarOps.immediateError err) st
        | .ok leftSc =>
          match leftSc.toPointer annealTargetDataLayout with
          | .error err => .error (Miri.Interpreter.ScalarOps.scalarError err) st
          | .ok pointer =>
            match rawPtrPointeeEncodedTyId? left.layout.ty with
            | none => .error (.unsupported "BinOp.Offset pointee layout not encoded") st
            | some pointeeTyId =>
              let pointeeLay := layoutOfEncodedTyId pointeeTyId layouts
              if !(pointeeLay.layout.isSized && pointeeLay.layout.size.bytes.toNat < 2 ^ 63) then
                .error (.invalidProgram "pointer Offset requires sized pointee fitting i64") st
              else
                match classifyEncodedTyId right.layout.ty with
                | .error err => .error err st
                | .ok (.integer rightKind) =>
                  match right.imm.toScalar with
                  | .error err => .error (Miri.Interpreter.ScalarOps.immediateError err) st
                  | .ok rightSc =>
                    match rightSc.toScalarInt with
                    | .error err => .error (Miri.Interpreter.ScalarOps.scalarError err) st
                    | .ok rightInt =>
                      match rightInt.toBits right.layout.layout.size with
                      | .error err => .error (Miri.Interpreter.ScalarOps.scalarIntError err) st
                      | .ok _ =>
                        match Miri.Memory.Scalar.fromInt (Prov := AnnealProv)
                            (Int.ofNat pointeeLay.layout.size.bytes.toNat)
                            right.layout.layout.size with
                        | .error err => .error (Miri.Interpreter.ScalarOps.scalarError err) st
                        | .ok strideSc =>
                          match strideSc.toScalarInt with
                          | .error err => .error (Miri.Interpreter.ScalarOps.scalarError err) st
                          | .ok strideInt =>
                            match Miri.Interpreter.IntegerOps.binary .MulWithOverflow
                                ⟨rightInt, ⟨right.layout.layout.size, rightKind⟩⟩
                                ⟨strideInt, ⟨right.layout.layout.size, rightKind⟩⟩ with
                            | .error err => .error (Miri.Interpreter.ScalarOps.integerError err) st
                            | .ok (.withOverflow scaledInt overflow) =>
                              if overflow then
                                .error (.undefinedBehavior "PointerArithOverflow") st
                              else
                                match (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv)
                                    scaledInt).toTargetIsize annealPointerArithmetic.pointerSize with
                                | .error err =>
                                  .error (Miri.Interpreter.ScalarOps.scalarError err) st
                                | .ok offset =>
                                  match right.layout.layout.backendRepr.isSigned with
                                  | .error _ =>
                                    .error (.invalidProgram "pointer Offset RHS signedness") st
                                  | .ok signed =>
                                    if !signed && offset.toInt < 0 then
                                      .error (.undefinedBehavior "PointerArithOverflow") st
                                    else
                                      match Miri.Interpreter.ptrOffsetInbounds
                                          annealPointerArithmetic pointer offset
                                          (annealResolvePtr st.machine)
                                          (annealLookupAlloc st.machine) with
                                      | .error (.access _) =>
                                        .error (.undefinedBehavior "pointer Offset out of bounds") st
                                      | .error (.pointer _) =>
                                        .error (.invalidProgram "pointer Offset arithmetic error") st
                                      | .ok nextPtr =>
                                        match Miri.Memory.Scalar.fromMaybePointer
                                            annealTargetDataLayout nextPtr with
                                        | .error err =>
                                          .error (Miri.Interpreter.ScalarOps.scalarError err) st
                                        | .ok result => .ok ⟨.scalar result, left.layout⟩ st
                            | .ok _ =>
                              .error (.invalidProgram
                                "MulWithOverflow returned non-overflow result") st
                | .ok _ => .error (.invalidProgram "pointer Offset RHS is not integral") st

/-- Validate thin-raw-pointer dereference well-formedness for
`ScalarOpsHooks.derefValidity` (invoked by `ScalarOps.unary .PtrMetadata`,
matching `Miri.Interpreter.PointerPlaceMachine.dereference` on `kind == .raw`
with a `Sized` pointee):
1. Accepts only thin `Sized` raw-pointer `TyId`s (`rawPtrPointeeEncodedTyId?`
   returning `some pointeeTyId` with `isSized = true`); non-thin raw pointers
   (`TyId = 40`) and safe references (`TyId = 41`, which require eager non-null,
   bounds, and alignment checks) fail closed with `StepError.unsupported`.
2. Extracts the thin pointer scalar (`toScalarAndMeta` with `.none` metadata,
   then `Scalar.toPointer`) without touching memory, so null and dangling thin
   raw pointers succeed as in Rust's `ptr::metadata`. -/
def annealDerefValidity (layouts : LayoutTable := emptyLayoutTable)
    (value : Miri.Interpreter.RvalueImmTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit :=
  match rawPtrPointeeEncodedTyId? value.layout.ty with
  | none =>
    throw (.unsupported
      s!"derefValidity not supported for non-thin or safe-reference TyId {value.layout.ty}")
  | some pointeeTyId =>
    let pointeeLay := layoutOfEncodedTyId pointeeTyId layouts
    if !pointeeLay.layout.isSized then
      throw (.unsupported "derefValidity unsized raw pointer")
    else
      match value.imm.toScalarAndMeta with
      | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
      | .ok (sc, .none) =>
        match sc.toPointer annealTargetDataLayout with
        | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
        | .ok _ => pure ()
      | .ok (_, .metadata _) =>
        throw (.invalidProgram "sized raw pointer immediate carries metadata")

/-- `ScalarOpsHooks` instantiated for Anneal's single-threaded machine. -/
def annealScalarOpsHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.ScalarOpsHooks AnnealProv AnnealStepState Unit where
  classify := fun _ tyId =>
    match classifyEncodedTyId tyId with
    | .ok cls => pure cls
    | .error err => throw err
  boolLayout := fun _ => pure (translateTy { kind := .bool, layoutIdx := 0 })
  orderingLayout := fun _ => pure (translateTy { kind := .int .i8, layoutIdx := 0 })
  overflowLayout := fun _ lay => pure (findOverflowTupleLayout localDecls layouts lay)
  metadataLayout := fun _ _ => pure (translateTy { kind := .uint .usize, layoutIdx := 0 })
  unitLayout := fun _ => pure (translateTy { kind := .tuple .nil, layoutIdx := 0 })
  floatBinary := fun _ op _ _ =>
    throw (.unsupported s!"floatBinary not supported: {repr op}")
  pointerBinary := fun _ op left right =>
    annealPointerBinary layouts op left right
  floatUnary := fun _ op _ =>
    throw (.unsupported s!"floatUnary not supported: {repr op}")
  derefValidity := fun _ value =>
    if value.layout.ty == arraySliceMetaTyId then pure ()
    else annealDerefValidity layouts value

/-- Read a `Miri.MIR.ConstOperand` directly into a `Miri.Interpreter.RvalueImmTy AnnealProv`. -/
def evalMirConstImmediate (layouts : LayoutTable) (c : Miri.MIR.ConstOperand) :
    Except Miri.Interpreter.StepError (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  match c.value with
  | .Val (.Scalar (.Int bits sizeBytes)) tyId =>
      let lay := layoutOfEncodedTyId tyId layouts
      match Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 bits) (translateSizeBytes sizeBytes) with
      | .ok (some sc) => .ok ⟨.scalar (.fromScalarInt sc), lay⟩
      | .ok none => .error (.invalidProgram "constant scalar integer overflow")
      | .error err => .error (.invalidProgram s!"invalid constant scalar: {repr err}")
  | .Val .ZeroSized tyId =>
      let lay := layoutOfEncodedTyId tyId layouts
      .ok ⟨.uninit, lay⟩
  | _ => .error (.unsupported "non-scalar constant in scalar rvalue evaluation")

/-- Resolve and memoize a local's `LocalLayout` in the top frame via
`Frame.getOrCacheLocalLayout`, writing the updated frame back to `AnnealStepState`
before any liveness check (matching `Miri.Interpreter.localToOp` and
`Place.placeLayoutOfLocal`). Out-of-bounds `localId`s propagate
`StepError.stack (.invalidLocal ...)` rather than fabricating a fallback layout
or misclassifying a stack indexing bug as undefined behavior. -/
def annealResolveAndCacheLocalLayout (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) (known : Option Miri.Interpreter.LocalLayout := none) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit ×
        Miri.Interpreter.LocalLayout) := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  let ls ←
    match frame.getLocal localId with
    | .ok ls => pure ls
    | .error e => throw (.stack e)
  let computed ←
    match ls.layout <|> lookupLocalDeclLayout localDecls layouts localId <|> known with
    | some l => pure l
    | none =>
        match frame.body.locals[localId]? with
        | some tyId => pure (layoutOfEncodedTyId tyId layouts)
        | none => throw (.stack (.missingLocalType localId))
  match frame.getOrCacheLocalLayout localId computed with
  | .error e => throw (.stack e)
  | .ok (frame', layout) =>
      let idx := st.stack.frames.size - 1
      if h : idx < st.stack.frames.size then
        set { st with stack := { frames := st.stack.frames.set idx frame' h } }
        return (frame', layout)
      else
        throw (.stack .emptyStack)

/-- Resolve the `LocalLayout` of field `fieldIdx` of `parent` using `hintFieldTy`
when supplied by a `ProjectionElem.Field`, or `TypeLayout.fieldLayouts` /
`BackendRepr` when called from `Miri.Interpreter.writeAggregate`. -/
def annealFieldLayout (layouts : LayoutTable) (hintFieldTy : Option Miri.MIR.TyId)
    (parent : Miri.Interpreter.LocalLayout) (fieldIdx : Nat) :
    Except Miri.Interpreter.ProjectionError Miri.Interpreter.LocalLayout :=
  match hintFieldTy with
  | some ft => .ok (layoutOfEncodedTyId ft layouts)
  | none =>
      let fromTable : Option Miri.Interpreter.LocalLayout :=
        if parent.ty ≥ 100 && parent.ty < 900 then
          match layouts.lookup (parent.ty - 100) with
          | some tl =>
              match get? tl.fieldLayouts fieldIdx with
              | some fLayoutIdx =>
                  match layouts.lookup fLayoutIdx with
                  | some fTl => some { ty := 100 + fLayoutIdx, layout := translateTypeLayout fTl }
                  | none => none
              | none => none
          | none => none
        else
          none
      match fromTable with
      | some fl => .ok fl
      | none =>
          match parent.layout.backendRepr with
          | .Scalar s =>
              if fieldIdx == 0 then
                let sz := (s.size annealRuntimeDataLayout).toOption.getD parent.layout.size
                let al := translateAlignBytes sz.bytes.toNat
                .ok { ty := 0
                      layout := { parent.layout with
                        fields := .Primitive
                        variants := .Single 0
                        size := sz
                        align := ⟨al⟩
                        unadjustedAbiAlign := al } }
              else
                .error (.invariant "scalar layout has only field 0")
          | .ScalarPair (a := a) (b := b) (bOffset := _) =>
              if fieldIdx == 0 then
                let sz := (a.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO
                let al := translateAlignBytes sz.bytes.toNat
                .ok { ty := 0
                      layout := { parent.layout with
                        fields := .Primitive
                        variants := .Single 0
                        backendRepr := .Scalar a
                        size := sz
                        align := ⟨al⟩
                        unadjustedAbiAlign := al } }
              else if fieldIdx == 1 then
                let sz := (b.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO
                let al := translateAlignBytes sz.bytes.toNat
                .ok { ty := 0
                      layout := { parent.layout with
                        fields := .Primitive
                        variants := .Single 0
                        backendRepr := .Scalar b
                        size := sz
                        align := ⟨al⟩
                        unadjustedAbiAlign := al } }
              else
                .error (.invariant "scalarPair layout has only fields 0 and 1")
          | _ => .error (.invariant "missing field layout in LayoutTable")

/-- `ProjectionCx` instantiated for struct and tuple field projections in
Anneal's single-threaded machine, wiring upstream
`Miri.Interpreter.projectionImmediateOffset` and thin-pointer offset arithmetic
for `Miri.Interpreter.project` / `Miri.Interpreter.projectField`. -/
def annealStructProjectionCx (layouts : LayoutTable)
    (hintFieldTy : Option Miri.MIR.TyId := none)
    (localIdx : Miri.MIR.LocalId → Except Miri.Interpreter.ProjectionError UInt64 := fun _ => .error (.invariant "localIndex not wired in LM-2.2")) :
    Miri.Interpreter.ProjectionCx AnnealProv where
  target := annealTargetDataLayout
  maxSizeOfVal := Miri.ABI.Size.ofBytes (UInt64.ofNat (2 ^ 63 - 1))
  isSliceOrStr := fun _ => .ok false
  field := fun parent fieldIdx => annealFieldLayout layouts hintFieldTy parent fieldIdx
  variant := fun parent vIdx =>
    if vIdx == 0 then .ok parent
    else .error (.invariant "multi-variant downcast not wired in LM-2.2")
  dynamicAlign := fun _ lay => .ok (some lay.layout.align.abi)
  packedAlign := fun _ => .ok none
  immediateOffset := fun value source offset target =>
    Miri.Interpreter.projectionImmediateOffset (fun _ _ => .ok ()) value source offset target false
  memoryOffset := fun place offset _ metadata => do
    if metadata.hasMeta then throw (.invariant "metadata on thin memory projection")
    let newOffset ← place.ptr.offset.add offset |>.mapError .size
    return { place with ptr := { place.ptr with offset := newOffset }, metadata := .none }
  subsliceLayout := fun _ _ => .error (.invariant "subsliceLayout not wired in LM-2.2")
  layoutOf := fun tyId => .ok (layoutOfEncodedTyId tyId layouts)
  deref := fun _ => .error (.invariant "deref not wired in LM-2.2")
  localIndex := localIdx

/-- Map a `Miri.Interpreter.ProjectionError` to a `Miri.Interpreter.StepError`.

The vendored interpreter has no such lifting for operand projections (its
`projectionLift` in `Place.lean` reports every non-machine error as a
callback), so this mapping follows rustc's interpreter instead. An out-of-bounds
index (`.bounds`) is undefined behavior (`BoundsCheckFailed`), as are an
out-of-bounds in-bounds offset and pointer arithmetic overflow. An unmet hook
obligation is unsupported. A violated projection invariant, such as a malformed
`ConstantIndex`, means ill-formed MIR, on which rustc reports a compiler bug
rather than UB, so it is an invalid program, like layout, size, alignment,
other offset, immediate, and scalar errors. -/
def annealLiftProjectionError :
    Miri.Interpreter.ProjectionError → Miri.Interpreter.StepError
  | .machineError err => err
  | .obligation op => .unsupported op
  | .invariant msg => .invalidProgram msg
  | .bounds len index => .undefinedBehavior s!"bounds check failed: index {index} >= len {len}"
  | .pointerArithOverflow => .undefinedBehavior "pointer arithmetic overflow in projection"
  | .layout err => .invalidProgram (reprStr err)
  | .size err => .invalidProgram (reprStr err)
  | .align err => .invalidProgram (reprStr err)
  | .offset (.inbounds _) => .undefinedBehavior "out-of-bounds projection offset"
  | .offset err => .invalidProgram (reprStr err)
  | .immediate err => .invalidProgram (reprStr err)
  | .scalar err => .invalidProgram (reprStr err)

/-- Read an array-index `LocalId` from `frame` (or `mach.memory` when the `usize`
local has been moved into stack memory) as a 64-bit `usize`, raising
`StepError.undefinedBehavior` if the index local is `.dead` or `.uninit`. -/
def annealLocalIndex
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (mach : AnnealMachine)
    (localId : Miri.MIR.LocalId) :
    Except Miri.Interpreter.ProjectionError UInt64 :=
  match frame.getLocalOperand localId with
  | .error (.localExpectedLive _) =>
      .error (.machineError (.undefinedBehavior "index local is dead"))
  | .error e =>
      .error (.machineError (.stack e))
  | .ok (.immediate .uninit) =>
      .error (.machineError (.undefinedBehavior "index local is uninitialized"))
  | .ok (.immediate (.scalar sc)) =>
      match sc.toBits (Miri.ABI.Size.ofBytes 8) with
      | .ok bits => .ok (UInt64.ofNat bits.toNat)
      | .error e => .error (.scalar e)
  | .ok (.indirect mp) =>
      match mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
          .error (.machineError (.unsupported "indirect index local without provenance"))
      | some allocId =>
          match mach.lookupBaseAddr allocId with
          | none =>
              .error (.machineError (.unsupported "indirect index local without baseAddr"))
          | some baseAddr =>
              match mach.memory.live.find? (fun (k, _) => k == allocId) with
              | none =>
                  .error (.machineError (.unsupported "indirect index local allocation not live"))
              | some (_, localAlloc) =>
                  let relOffset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr)
                  let rng := Miri.Memory.allocRange relOffset (Miri.ABI.Size.ofBytes 8)
                  match localAlloc.allocation.initializationMask.isRangeInitialized rng with
                  | Except.ok (Except.ok ()) =>
                      match localAlloc.allocation.readScalar annealTargetDataLayout rng false with
                      | .ok sc =>
                          match sc.toBits (Miri.ABI.Size.ofBytes 8) with
                          | .ok bits => .ok (UInt64.ofNat bits.toNat)
                          | .error e => .error (.scalar e)
                      | .error (.invalidUninitBytes _) =>
                          .error (.machineError (.undefinedBehavior "index local is uninitialized"))
                      | .error _ =>
                          .error (.machineError (.unsupported "indirect index scalar read failed"))
                  | _ =>
                      .error (.machineError (.undefinedBehavior "index local is uninitialized"))
  | .ok _ =>
      .error (.machineError (.unsupported "non-usize index local"))

/-- Resolve an `AnnealProv` pointer to `(AllocId, relativeOffset)` via
`mach.lookupBaseAddr`, instantiating `Miri.Memory.PointerResolver`. -/
def annealPointerResolver (mach : AnnealMachine) :
    Miri.Memory.PointerResolver AnnealProv Unit :=
  fun ptr _ =>
    match ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
    | some id =>
        match mach.lookupBaseAddr id with
        | some base =>
            if base ≤ ptr.offset.bytes then
              .ok ⟨id, Miri.ABI.Size.ofBytes (ptr.offset.bytes - base), ()⟩
            else
              .error ptr.offset.bytes
        | none => .error ptr.offset.bytes
    | none => .error ptr.offset.bytes

/-- Look up live `AllocationInfo` in `mach.memory.live`, instantiating
`Miri.Memory.LiveAllocationLookup`. -/
def annealLiveAllocationLookup (mach : AnnealMachine) :
    Miri.Memory.LiveAllocationLookup :=
  fun id =>
    match mach.memory.live.find? (fun (k, _) => k == id) with
    | some (_, la) =>
        .ok ⟨la.allocation.byteSize, la.allocation.align, .liveData, la.allocation.mutability⟩
    | none => .error (.unavailable id)

/-- `ProjectionCx` instantiated for Anneal's single-threaded machine, delegating
`memoryOffset` to `Miri.Interpreter.projectionMemoryOffset` so `OffsetMode.inbounds`
checks allocation bounds in `mach.memory.live` while `OffsetMode.wrapping` wraps
at target pointer width. -/
def annealProjectionCx
    (frame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable)
    (mach : AnnealMachine) :
    Miri.Interpreter.ProjectionCx AnnealProv where
  target := annealTargetDataLayout
  maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff
  isSliceOrStr := fun _ => .ok false
  field := fun baseLay _ =>
    match baseLay.layout.fields with
    | .Array stride _ => .ok (arrayElemLayoutOf layouts baseLay stride)
    | _ => .error (.obligation "non-array field projection in annealProjectionCx")
  variant := fun _ _ => .error (.obligation "variant projection in annealProjectionCx")
  dynamicAlign := fun _ _ => .ok none
  packedAlign := fun _ => .ok none
  immediateOffset :=
    Miri.Interpreter.projectionImmediateOffset (fun _ _ => .ok ()) (debugAssertions := false)
  memoryOffset :=
    Miri.Interpreter.projectionMemoryOffset
      annealPointerArithmetic
      (annealPointerResolver mach)
      (annealLiveAllocationLookup mach)
  subsliceLayout := fun baseLay _ =>
    match baseLay.layout.fields with
    | .Array _ _ => .error (.obligation "array subslice in annealProjectionCx")
    | _ => .error (.invariant "subslice on non-array")
  layoutOf := fun tyId => .ok (layoutOfEncodedTyId tyId layouts)
  deref := fun _ => .error (.obligation "deref in annealProjectionCx")
  localIndex := annealLocalIndex frame mach

/-- Sequentially apply a list of `Miri.MIR.ProjectionElem`s via `Miri.Interpreter.project`.
When `elem` is the synthetic `Rvalue.len` projection `.UnwrapUnsafeBinder arraySliceMetaTyId`,
`cxElem.layoutOf` preserves an `.Array` operand's `LayoutData` under `arraySliceMetaTyId`
and rejects non-array operands with `.obligation "len on non-array"`. -/
def annealProjectList
    (cx : Miri.Interpreter.ProjectionCx AnnealProv)
    (base : Miri.Interpreter.OpTy AnnealProv)
    (projs : List Miri.MIR.ProjectionElem) :
    Except Miri.Interpreter.ProjectionError (Miri.Interpreter.OpTy AnnealProv) :=
  match projs with
  | [] => .ok base
  | elem :: rest => do
      let cxElem :=
        match elem with
        | .UnwrapUnsafeBinder ty =>
            if ty == arraySliceMetaTyId then
              { cx with
                layoutOf := fun _ =>
                  match base.layout.layout.fields with
                  | .Array _ _ => .ok { ty := arraySliceMetaTyId, layout := base.layout.layout }
                  | _ => .error (.obligation "len on non-array") }
            else cx
        | _ => cx
      let next ← Miri.Interpreter.project cxElem base elem
      annealProjectList cx next rest

/-- Check that the byte slice `[relOffset, relOffset + size)` of an indirect
`MemPlace` is initialized in `mach.memory.live`, raising
`StepError.undefinedBehavior` if uninitialized.

`annealEvalOperand` and `annealEvalPlace` run this check on a whole
memory-backed local before projecting into it. That is stricter than Miri,
which checks only the bytes an access reads and none for a write. The check
mirrors Anneal's `MirSemantics`, where a projected read or write of a local
requires the local's whole value to be initialized, so both machines report UB
for an element access into an uninitialized array. -/
def annealCheckIndirectInitialized
    (mach : AnnealMachine)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (size : Miri.ABI.Size) :
    Except Miri.Interpreter.StepError Unit := do
  let some allocId := mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
    | throw (.unsupported "indirect place without provenance")
  let some baseAddr := mach.lookupBaseAddr allocId
    | throw (.unsupported "indirect place without baseAddr")
  let some (_, localAlloc) := mach.memory.live.find? (fun (k, _) => k == allocId)
    | throw (.unsupported "indirect place allocation not live")
  let relOffset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr)
  match localAlloc.allocation.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange relOffset size) with
  | Except.ok (Except.ok ()) => return ()
  | _ => throw (.undefinedBehavior "access to uninitialized indirect place")

/-- Whether `translateTy` gives a pointee of kind `k` its exact layout without
consulting a layout table: `bool`, `char`, the integer and float types, the
unit type `()`, and zero-sized function-item types (`RigidTy.fnDef`). Every
other pointee (an aggregate, whose layout lives at an index that a raw pointer
type does not record; `!`; an unsized slice, `str`, or trait object; or a
pointer, which may itself be fat) has no layout that a dereference can trust. -/
def derefPointeeKindHasExactLayout : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ | .tuple .nil | .fnDef _ _ => true
  | _ => false

/-- Resolve the pointee `LocalLayout` when dereferencing a raw-pointer local
`localId` (`*_p`), consulting `localDecls` when available and falling back to
`rawPtrPointeeEncodedTyId? ptrLayout.ty`. Safe references (`&T` / `&mut T`) and
pointees without an exact layout (`derefPointeeKindHasExactLayout`) resolve to
`none`, so the dereference never reads with a guessed width or bypasses
`PointerPlaceMachine.dereference`'s eager safe-reference checks: safe references
go through `annealDerefSafeRefToMemPlace`, which performs those checks, and
every other pointee fails closed. -/
def lookupDerefPointeeLayout (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) (ptrLayout : Miri.Interpreter.LocalLayout) :
    Option Miri.Interpreter.LocalLayout :=
  match get? localDecls localId with
  | some decl =>
      match decl.ty.kind with
      | .rawPtr _ pointeeKind =>
          if derefPointeeKindHasExactLayout pointeeKind then
            some (translateTy { kind := pointeeKind, layoutIdx := 0 } layouts)
          else
            none
      | _ => none
  | none =>
      (rawPtrPointeeEncodedTyId? ptrLayout.ty).map (layoutOfEncodedTyId · layouts)

/-- Resolve the pointee `LocalLayout` when dereferencing a safe-reference local
`localId` (`*_r` with `_r : &T` or `&mut T`) from its declaration, for the
pointees whose layout `translateTy` gives exactly
(`derefPointeeKindHasExactLayout`). The encoded `TyId` of a reference (`41`)
records neither its pointee nor its mutability, so undeclared locals resolve to
`none`, as do raw pointers and every other pointee. -/
def lookupRefDerefPointeeLayout (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) : Option Miri.Interpreter.LocalLayout :=
  match get? localDecls localId with
  | some decl =>
      match decl.ty.kind with
      | .ref _ pointeeKind =>
          if derefPointeeKindHasExactLayout pointeeKind then
            some (translateTy { kind := pointeeKind, layoutIdx := 0 } layouts)
          else
            none
      | _ => none
  | none => none

/-- Address-based misalignment check for `AnnealProv` (`offsetIsAddr = true`),
matching `Miri.Memory.Access.offsetMisalignment` (`Access.lean:183-188`). -/
def annealOffsetMisalignment (offset : Miri.ABI.Size) (required : Miri.ABI.Align) :
    Except Miri.Memory.AccessError (Option Miri.Memory.Misalignment) :=
  match offset.isAligned required with
  | .ok true => .ok none
  | .ok false => .ok (some ⟨Miri.ABI.Align.maxAlignedFactor offset, required⟩)
  | .error err => .error (.malformedAlignment err)

/-- Determine whether reading a scalar `BackendRepr` from memory reads pointer
provenance (`true` for `.Pointer _`, `false` for `.Int` / `.Float`, `none` for
non-scalar layouts), matching `MemoryOperand.lean:168-182`. -/
def annealScalarReadProvenance (repr : Miri.ABI.BackendRepr) : Option Bool :=
  match repr with
  | .Scalar (.Initialized (value := .Pointer _) ..) => some true
  | .Scalar (.Initialized (value := .Int _ _) ..)
  | .Scalar (.Initialized (value := .Float _) ..) => some false
  | _ => none

/-- Check scalar bit-pattern validity when reading or writing a memory-backed
place (`Validity.lean` / `Place.lean`):
* `bool` (`tyId = 1`): must be a 1-byte integer scalar equal to `0` or `1`;
* `char` (`tyId = 2`): must be a 4-byte integer scalar satisfying `isValidCharCode`;
* `&T` / `&mut T` (`tyId = 41`) and `fnPtr` (`tyId = 42`): must be non-null
  8-byte pointers (`WrappingRange 1..2^64-1` via `pointerLayoutData true`);
* `!` (`tyId = 50`): uninhabited (`false`);
* every other scalar/raw-pointer `tyId`: every canonical scalar or pointer
  immediate accepted by `readScalar` / `writeScalar` is valid. -/
def annealValidateScalarForTyId (tyId : Miri.MIR.TyId)
    (sc : Miri.Memory.Scalar AnnealProv) : Bool :=
  match tyId with
  | 1 =>
    match sc.toScalarInt with
    | .ok msc =>
      (msc.size == Miri.ABI.Size.ofBytes 1) && (msc.data.toNat == 0 || msc.data.toNat == 1)
    | .error _ => false
  | 2 =>
    match sc.toScalarInt with
    | .ok msc =>
      (msc.size == Miri.ABI.Size.ofBytes 4) && isValidCharCode msc.data.toNat
    | .error _ => false
  | 41 | 42 =>
    match sc.toPointer annealTargetDataLayout with
    | .ok p => p.offset.bytes != 0
    | .error _ => false
  | 50 => false
  | _ => true

/-- Read a scalar or zero-sized `Immediate` from a memory-backed `MemPlace`,
enforcing `Miri.Memory.checkAndDerefPtr` bounds/liveness/provenance first,
cached `mplace.misaligned` alignment second, `Allocation.readScalar`
initialization third, and `bool`/`char` bit-pattern validity fourth
(`MemoryOperand.lean:103-143, 278-315`, `Place.lean:188-191`). -/
@[irreducible]
def annealReadMemoryPlace (mplace : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  fun st =>
    let size := lay.layout.size
    match Miri.Memory.sizeAsI64 size with
    | .error _ => .error (.invalidProgram "memory read size overflow") st
    | .ok signedSize =>
      match Miri.Memory.checkAndDerefPtr annealPointerArithmetic mplace.ptr signedSize
          .memoryAccess (annealResolvePtrWrapping st.machine) (annealLookupAlloc st.machine) with
      | .error _ => .error (.undefinedBehavior "pointer dereference check failed") st
      | .ok checked =>
        match mplace.misaligned with
        | some _ => .error (.undefinedBehavior "misaligned pointer dereference") st
        | none =>
          match checked with
          | none => .ok ⟨.uninit, lay⟩ st
          | some access =>
            match annealScalarReadProvenance lay.layout.backendRepr with
            | none =>
              .error (.unsupported "non-scalar memory read in scalar/pointer fragment") st
            | some readProv =>
              match st.machine.memory.live.find?
                  (fun entry => entry.1 == access.pointer.allocId) with
              | none => .error (.undefinedBehavior "dereference of dead allocation") st
              | some (_, localAlloc) =>
                match localAlloc.allocation.readScalar annealTargetDataLayout
                    (Miri.Memory.allocRange access.pointer.offset size) readProv with
                | .ok sc =>
                  if annealValidateScalarForTyId lay.ty sc then
                    .ok ⟨.scalar sc, lay⟩ st
                  else
                    .error (.undefinedBehavior "reading invalid value") st
                | .error (.invalidUninitBytes _) =>
                  .error (.undefinedBehavior "read of uninitialized memory") st
                | .error (.readPointerAsInt _) | .error (.readPartialPointer _) =>
                  .error (.unsupported "pointer-bytes-as-int memory read in scalar/pointer fragment")
                    st
                | .error _ => .error (.invalidProgram "memory read error") st

/-- Read an `Immediate` from an `OpTy AnnealProv` in `AnnealStepState`, raising
`StepError.undefinedBehavior` on `.uninit` or invalid memory accesses just as
`MirSemantics.evalOperand` raises `.fail .ub`, extracting `(address, length)`
metadata exclusively for `arraySliceMetaTyId` (`Rvalue.len`), failing closed
(`StepError.unsupported`) on whole-array immediate reads, and routing scalar/ZST
indirect reads through `annealReadMemoryPlace`. -/
def annealReadImmediate (op : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) := do
  match op.op with
  | .immediate (.scalar s) => return ⟨.scalar s, op.layout⟩
  | .immediate (.scalarPair s1 s2) => return ⟨.scalarPair s1 s2, op.layout⟩
  | .immediate .uninit => throw (.undefinedBehavior "read of uninitialized local")
  | .indirect mp =>
      match op.layout.layout.fields with
      | .Array _ count =>
          let st ← get
          let some allocId := mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
            | throw (.unsupported "indirect operand without provenance")
          let some baseAddr := st.machine.lookupBaseAddr allocId
            | throw (.unsupported "indirect operand without baseAddr")
          let some (_, localAlloc) := st.machine.memory.live.find? (fun (k, _) => k == allocId)
            | throw (.unsupported "indirect operand allocation not live")
          let relOffset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr)
          if op.layout.ty == arraySliceMetaTyId then
            match localAlloc.allocation.initializationMask.isRangeInitialized
                (Miri.Memory.allocRange relOffset op.layout.layout.size) with
            | Except.ok (Except.ok ()) =>
                let some countSc :=
                  (Miri.Memory.ScalarInt.tryFromUInt
                    (BitVec.ofNat 128 count.toNat)
                    (Miri.ABI.Size.ofBytes 8)).toOption.join
                  | throw (.invalidProgram "array length overflow")
                let some prov := mp.ptr.provenance
                  | throw (.unsupported "indirect array operand without provenance")
                let ptrSc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨mp.ptr.offset, prov⟩
                return ⟨.scalarPair ptrSc (.fromScalarInt countSc),
                        { ty := arraySliceMetaTyId,
                          layout := (translateTy { kind := .ref .not (.slice .bool), layoutIdx := 0 }).layout }⟩
            | _ => throw (.undefinedBehavior "len of uninitialized array")
          else
            throw (.unsupported "whole-array immediate read not supported")
      | _ => annealReadMemoryPlace mp op.layout

/-- The eager checks that `Miri.Interpreter.PointerPlaceMachine.dereference`
performs on a safe reference (`Kind.reference`) when validity is enforced, as a
pure function of the machine, the reference immediate `ptrImm`, and the
pointee layout. After converting the immediate to a pointer, it checks, in this
order, that the pointer is non-null (`scalarMayBeNull`), dereferenceable for the
pointee's size (`checkPointerAccess`, here `Miri.Memory.checkAndDerefPtr`
against the cached base addresses with `annealResolvePtr`), and aligned to the
pointee's ABI alignment (`checkPointerAlign`). Each failure is undefined
behavior, so the resulting place never caches a misalignment. -/
def annealSafeRefDerefCheck (mach : AnnealMachine)
    (ptrImm : Miri.Interpreter.Immediate AnnealProv)
    (pointeeLay : Miri.Interpreter.LocalLayout) :
    Except Miri.Interpreter.StepError (Miri.Interpreter.MemPlace AnnealProv) :=
  match ptrImm.toScalar with
  | .error err => .error (Miri.Interpreter.ScalarOps.immediateError err)
  | .ok sc =>
    match sc.toPointer annealTargetDataLayout with
    | .error err => .error (Miri.Interpreter.ScalarOps.scalarError err)
    | .ok ptr =>
      if ptr.offset.bytes == 0 then
        .error (.undefinedBehavior "dereferencing a null reference")
      else
        match Miri.Memory.sizeAsI64 pointeeLay.layout.size with
        | .error _ => .error (.invalidProgram "reference pointee size overflow")
        | .ok signedSize =>
          match Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize
              (.dereferenceable "pointer") (annealResolvePtr mach)
              (annealLookupAlloc mach) with
          | .error _ => .error (.undefinedBehavior "dereferencing a dangling reference")
          | .ok _ =>
            match annealOffsetMisalignment ptr.offset pointeeLay.layout.align.abi with
            | .error err => .error (.invalidProgram (toString err))
            | .ok (some _) => .error (.undefinedBehavior "dereferencing an unaligned reference")
            | .ok none => .ok ⟨ptr, .none, none⟩

/-- Dereference a safe-reference local `localId` (`*_r` with `_r : &T` or
`&mut T`) as `Miri.Interpreter.PointerPlaceMachine.dereference` does for
`Kind.reference` when validity is enforced: read the reference, then run the
eager non-null, dereferenceability, and alignment checks of
`annealSafeRefDerefCheck` without changing the state. A raw pointer's
dereference (`annealDerefOperandToMemPlace`) instead performs none of these
checks (`PointerPlaceMachine.fromImmediate`) and leaves them to the access. -/
@[irreducible]
def annealDerefSafeRefToMemPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) (operand : Miri.Interpreter.Operand AnnealProv)
    (ptrLayout : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.MemPlace AnnealProv × Miri.Interpreter.LocalLayout) := do
  let some pointeeLay := lookupRefDerefPointeeLayout localDecls layouts localId
    | throw (.unsupported "dereference of local without pointee layout")
  let ptrImm ← annealReadImmediate ⟨operand, ptrLayout⟩
  let st ← get
  match annealSafeRefDerefCheck st.machine ptrImm.imm pointeeLay with
  | .ok mplace => return (mplace, pointeeLay)
  | .error err => throw err

/-- Construct a dereferenced `MemPlace` (`*_p`) from pointer local `localId`'s
current `Operand` and `LocalLayout`, caching numeric misalignment without
eagerly requiring the pointee allocation to be live (`PointerPlaceMachine.lean`).
Safe references, whose pointee layout `lookupDerefPointeeLayout` never resolves,
are dereferenced by `annealDerefSafeRefToMemPlace` with eager checks. -/
@[irreducible]
def annealDerefOperandToMemPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) (operand : Miri.Interpreter.Operand AnnealProv)
    (ptrLayout : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.MemPlace AnnealProv × Miri.Interpreter.LocalLayout) := do
  let some pointeeLay := lookupDerefPointeeLayout localDecls layouts localId ptrLayout
    | annealDerefSafeRefToMemPlace localDecls layouts localId operand ptrLayout
  let ptrImm ← annealReadImmediate ⟨operand, ptrLayout⟩
  let sc ←
    match ptrImm.imm.toScalar with
    | .ok s => pure s
    | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
  let ptr ←
    match sc.toPointer annealTargetDataLayout with
    | .ok p => pure p
    | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
  let mismatch ←
    match annealOffsetMisalignment ptr.offset pointeeLay.layout.align.abi with
    | .ok m => pure m
    | .error err => throw (.invalidProgram (toString err))
  return (⟨ptr, .none, mismatch⟩, pointeeLay)

/-- Project an `OpTy AnnealProv` along a sequence of `Miri.MIR.ProjectionElem`s
using upstream `Miri.Interpreter.project` (`Miri.Interpreter.projectField`). -/
def annealEvalProjection (layouts : LayoutTable)
    (base : Miri.Interpreter.OpTy AnnealProv) :
    List Miri.MIR.ProjectionElem →
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv)
  | [] => return base
  | elem :: rest => do
      let hintTy :=
        match elem with
        | .Field _ ft => some ft
        | _ => none
      let next ←
        match Miri.Interpreter.project (annealStructProjectionCx layouts hintTy) base elem with
        | .ok opTy => pure opTy
        | .error err => throw (annealLiftProjectionError err)
      annealEvalProjection layouts next rest

/-- Evaluate a local, a dereferenced pointer place (`*_p`), one field of a
scalar-pair local, an indexed array element, or a constant `Miri.MIR.Operand`
in the top frame of `AnnealStepState`.

1. Memoizes the resolved `LocalLayout` into `frame.locals[localId].layout` via
   `Frame.getOrCacheLocalLayout` before checking liveness, matching `lean-miri`'s
   `LocalAccess.localToOp`.
2. `Copy` and `Move` read the local exactly as `lean-miri`'s source operand
   evaluators (`Miri.Interpreter.OperandMachine.evalOperand` and
   `Miri.Interpreter.evalOperand`) do. `Move` then deinitializes an unprojected
   immediate moved-from local, implementing the runtime-MIR semantics that the
   pinned rustc documents for `Operand::Move` and that Anneal's
   `MirSemantics.evalOperand` implements: "in runtime MIR, this marks the place
   as deinitialized (i.e. writes `uninit` to all bytes of the place)"
   (`compiler/rustc_middle/src/mir/syntax.rs` at commit
   `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`).
3. Out-of-bounds `localId`s propagate `StepError.stack (.invalidLocal ...)`.
   Reading a `.dead` local (`StackError.localExpectedLive` from
   `Frame.getLocalOperand`) raises `StepError.undefinedBehavior`, matching rustc's
   `err_ub!(DeadLocal)` and Anneal's `MirStepNode.fail .ub` (whereas upstream
   `OperandMachine.stack` wraps `.localExpectedLive` as
   `StepError.stack (.localExpectedLive _)`, for which `RunLoop.reportsUB` is
   `false`).
4. A single `Deref` projection (`*_p`) constructs an `.indirect` memory operand
   with cached misalignment (`PointerPlaceMachine.lean`), deferring bounds,
   liveness, alignment, and initialization checks to `annealReadImmediate`. A
   safe reference (`*_r`) checks non-nullness, bounds, liveness, and alignment
   eagerly instead (`annealDerefSafeRefToMemPlace`).
5. A single `Field` projection reads one scalar of a local that holds a scalar
   pair, such as a component of a checked-arithmetic result.
6. On a memory-backed (`.indirect`) local whose whole allocation passes
   `annealCheckIndirectInitialized`, non-`Deref`/`Field` projections (`Index`,
   `ConstantIndex`, and synthetic `.UnwrapUnsafeBinder arraySliceMetaTyId` for
   `Rvalue.len`) delegate to `annealProjectList` and lift projection errors via
   `annealLiftProjectionError` (`StepError.undefinedBehavior` on out-of-bounds
   or dead/uninitialized index, `StepError.invalidProgram` on violated
   projection invariants such as a malformed `ConstantIndex`, and
   `StepError.unsupported` on unmet obligations such as array subslices). Even
   under `Move`, projected reads leave the parent local initialized, matching
   Anneal's `MirSemantics.evalOperand`. Projected reads on `.immediate .uninit`
   report `StepError.undefinedBehavior`, and all other immediate projections
   fail closed with `StepError.unsupported`.

Known infidelity: `Move` of a memory-backed (`.indirect`) local replaces the
local by `.live (.immediate .uninit)` instead of writing uninitialized bytes to
its allocation. The allocation then stays live but no longer belongs to the
local, so `Frame.deallocateLocal` never frees it, and pointers into it keep
reading the old bytes, even after `StorageDead`. rustc and Anneal deinitialize
the bytes in place. Before `annealReadImmediate` read `.indirect` operands this
path failed closed; no theorem covers it now, and `annealEvalOperand_move_live`
(an `LM-1.4` statement pin) fixes the current behavior for every operand. -/
def annealEvalOperand (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  match op with
  | .Copy place | .Move place =>
      let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts place.localId known
      let operand ← match frame'.getLocalOperand place.localId with
      | .ok op => pure op
      | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
      | .error e => throw (.stack e)
      match place.projection.toList with
      | [] =>
          match op with
          | .Move _ =>
            match frame'.replaceLocalValue place.localId (.live (.immediate .uninit)) with
            | .ok frame'' =>
              let st ← get
              let idx := st.stack.frames.size - 1
              if h : idx < st.stack.frames.size then
                set { st with stack := { frames := st.stack.frames.set idx frame'' h } }
                return ⟨operand, layout⟩
              else throw (.stack .emptyStack)
            | .error e => throw (.stack e)
          | _ => return ⟨operand, layout⟩
      | [Miri.MIR.ProjectionElem.Deref] =>
          let (mplace, pointeeLay) ←
            annealDerefOperandToMemPlace localDecls layouts place.localId operand layout
          return ⟨.indirect mplace, pointeeLay⟩
      | [Miri.MIR.ProjectionElem.Field idx fieldTy] =>
          match operand with
          | .immediate (.scalarPair s0 s1) =>
              if idx == 0 then
                return ⟨.immediate (.scalar s0), ⟨fieldTy, layout.layout⟩⟩
              else if idx == 1 then
                return ⟨.immediate (.scalar s1), ⟨fieldTy, layout.layout⟩⟩
              else
                annealEvalProjection layouts ⟨operand, layout⟩
                  [Miri.MIR.ProjectionElem.Field idx fieldTy]
          | _ =>
              annealEvalProjection layouts ⟨operand, layout⟩
                [Miri.MIR.ProjectionElem.Field idx fieldTy]
      | projs@(Miri.MIR.ProjectionElem.Field _ _ :: _)
      | projs@(Miri.MIR.ProjectionElem.Downcast _ _ :: _) =>
          annealEvalProjection layouts ⟨operand, layout⟩ projs
      | _ =>
          match operand with
          | .immediate .uninit =>
              throw (.undefinedBehavior "projected read of uninitialized local")
          | .indirect mp =>
              let st ← get
              match annealCheckIndirectInitialized st.machine mp layout.layout.size with
              | .error err => throw err
              | .ok () =>
                  match annealProjectList
                      (annealProjectionCx frame' layouts st.machine)
                      ⟨.indirect mp, layout⟩ place.projection.toList with
                  | .ok projected => return projected
                  | .error projErr => throw (annealLiftProjectionError projErr)
          | _ => throw (Miri.Interpreter.StepError.unsupported "projected operand in scalar rvalue")
  | .Constant c =>
      match evalMirConstImmediate layouts c with
      | .ok imm => return ⟨.immediate imm.imm, imm.layout⟩
      | .error e => throw e
  | .RuntimeChecks _ =>
      throw (.unsupported "RuntimeChecks operand")

/-- Project a `RuntimePlace AnnealProv` to field `fieldIdx` using upstream
`Miri.Interpreter.projectField` (`Place.projectRuntimePlace` carrier semantics). -/
def annealProjectFieldPlace (layouts : LayoutTable)
    (hintFieldTy : Option Miri.MIR.TyId)
    (place : Miri.Interpreter.RuntimePlace AnnealProv)
    (fieldIdx : Nat) :
    Except Miri.Interpreter.StepError (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let cx := annealStructProjectionCx layouts hintFieldTy
  match place.ref with
  | .memory mplace =>
      match Miri.Interpreter.projectField cx ⟨.indirect mplace, place.layout⟩ fieldIdx with
      | .ok ⟨.indirect mplace', layout'⟩ => return ⟨.memory mplace', layout'⟩
      | .ok ⟨.immediate _, _⟩ => throw (.invalidProgram "memory projection returned immediate")
      | .error err => throw (annealLiftProjectionError err)
  | .local frame localId offset identity =>
      let baseOffset := offset.getD Miri.ABI.Size.ZERO
      let carrier : Miri.Interpreter.MemPlace AnnealProv := ⟨⟨baseOffset, none⟩, .none, none⟩
      match Miri.Interpreter.projectField cx ⟨.indirect carrier, place.layout⟩ fieldIdx with
      | .ok ⟨.indirect result, layout'⟩ =>
          let bound ←
            match result.ptr.offset.add layout'.layout.size with
            | .ok b => pure b
            | .error _ => throw (.invalidProgram "projected local size overflow")
          let endOffset ←
            match baseOffset.add place.layout.layout.size with
            | .ok e => pure e
            | .error _ => throw (.invalidProgram "local size overflow")
          if result.ptr.offset.bytes < baseOffset.bytes || bound.bytes > endOffset.bytes then
            throw (.invalidProgram "projected local is out of bounds")
          else
            return ⟨.local frame localId (some result.ptr.offset) identity, layout'⟩
      | .ok ⟨.immediate _, _⟩ => throw (.invalidProgram "local projection returned immediate")
      | .error err => throw (annealLiftProjectionError err)

/-- Project a `RuntimePlace AnnealProv` along a list of `Miri.MIR.ProjectionElem`s. -/
def annealProjectPlaceList (layouts : LayoutTable)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) :
    List Miri.MIR.ProjectionElem →
    Except Miri.Interpreter.StepError (Miri.Interpreter.RuntimePlace AnnealProv)
  | [] => .ok place
  | .Field fieldIdx fieldTy :: rest => do
      let next ← annealProjectFieldPlace layouts (some fieldTy) place fieldIdx
      annealProjectPlaceList layouts next rest
  | .Downcast _ 0 :: rest =>
      annealProjectPlaceList layouts place rest
  | _ :: _ => .error (.unsupported "non-field place projection in LM-2.2")

/-- Resolve a projected `Miri.MIR.Place` to a `RuntimePlace AnnealProv` in the top frame. -/
def annealEvalProjectedPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let st ← get
  if st.stack.currentFrame?.isNone then
    throw (.stack .emptyStack)
  let frameIdx := st.stack.frames.size - 1
  let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts place.localId none
  let base : Miri.Interpreter.RuntimePlace AnnealProv :=
    ⟨.local frameIdx place.localId none frame'.localsIdentity, layout⟩
  match annealProjectPlaceList layouts base place.projection.toList with
  | .ok p => return p
  | .error err => throw err

/-- Resolve an unprojected local `Miri.MIR.Place`, a single-deref pointer place
(`*_p`), or an indexed array element projection (`Index` / `ConstantIndex`) on
an indirect array local to a `RuntimePlace AnnealProv` in the top frame,
memoizing the base local's `LocalLayout` via `Frame.getOrCacheLocalLayout` and
propagating `StepError.stack` on out-of-bounds `localId`s. -/
def annealEvalPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  if !place.projection.isEmpty then
    match place.projection.toList with
    | [Miri.MIR.ProjectionElem.Deref] =>
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        let (frame', layout) ←
          annealResolveAndCacheLocalLayout localDecls layouts place.localId none
        let operand ←
          match frame'.getLocalOperand place.localId with
          | .ok op => pure op
          | .error (.localExpectedLive _) => throw (.undefinedBehavior "read of dead local")
          | .error e => throw (.stack e)
        let (mplace, pointeeLay) ←
          annealDerefOperandToMemPlace localDecls layouts place.localId operand layout
        return ⟨.memory mplace, pointeeLay⟩
    | .Field _ _ :: _ | .Downcast _ _ :: _ =>
        annealEvalProjectedPlace localDecls layouts place
    | _ =>
        let st ← get
        if st.stack.currentFrame?.isNone then
          throw (.stack .emptyStack)
        let (frame', layout) ←
          annealResolveAndCacheLocalLayout localDecls layouts place.localId none
        match frame'.getLocalOperand place.localId with
        | .error (.localExpectedLive _) =>
            throw (.undefinedBehavior "projected write to dead local")
        | .error e =>
            throw (.stack e)
        | .ok (.immediate .uninit) =>
            throw (.undefinedBehavior "projected write to uninitialized local")
        | .ok (.immediate _) =>
            throw (.unsupported "projected destination place on immediate local")
        | .ok (.indirect mp) =>
            let st ← get
            match annealCheckIndirectInitialized st.machine mp layout.layout.size with
            | .error err => throw err
            | .ok () =>
                match annealProjectList
                    (annealProjectionCx frame' layouts st.machine)
                    ⟨.indirect mp, layout⟩ place.projection.toList with
                | .ok ⟨.indirect elemMp, elemLayout⟩ =>
                    return ⟨.memory elemMp, elemLayout⟩
                | .ok ⟨.immediate _, _⟩ =>
                    throw (.unsupported "projected place resolved to immediate")
                | .error projErr =>
                    throw (annealLiftProjectionError projErr)
  else
    let st ← get
    if st.stack.currentFrame?.isNone then
      throw (.stack .emptyStack)
    let frameIdx := st.stack.frames.size - 1
    let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts place.localId none
    return ⟨.local frameIdx place.localId none frame'.localsIdentity, layout⟩

/-- Write a scalar or zero-sized `Immediate` to a memory-backed `MemPlace`,
enforcing `Miri.Memory.checkAndDerefPtr` bounds/liveness/provenance first,
`Mutability.Mut` second, cached `mplace.misaligned` alignment third, and
committing the updated allocation via `MemoryState.setLiveAllocation`
(`MemoryOperand.lean:144-163, 237-273`). -/
@[irreducible]
def annealWriteMemoryPlace (val : Miri.Interpreter.Immediate AnnealProv)
    (mplace : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState Unit :=
  fun st =>
    let size := lay.layout.size
    match Miri.Memory.sizeAsI64 size with
    | .error _ => .error (.invalidProgram "memory write size overflow") st
    | .ok signedSize =>
      match Miri.Memory.checkAndDerefPtr annealPointerArithmetic mplace.ptr signedSize
          .memoryAccess (annealResolvePtrWrapping st.machine) (annealLookupAlloc st.machine) with
      | .error _ => .error (.undefinedBehavior "pointer dereference check failed") st
      | .ok checked =>
        match checked with
        | none =>
          match mplace.misaligned with
          | some _ => .error (.undefinedBehavior "misaligned pointer dereference") st
          | none =>
            match val with
            | .uninit => .ok () st
            | _ => .error (.invalidProgram "non-uninit immediate written to zero-sized place") st
        | some access =>
          if access.allocation.mutability != .Mut then
            .error (.undefinedBehavior "write to read-only allocation") st
          else
            match mplace.misaligned with
            | some _ => .error (.undefinedBehavior "misaligned pointer dereference") st
            | none =>
              match st.machine.memory.live.find?
                  (fun entry => entry.1 == access.pointer.allocId) with
              | none => .error (.undefinedBehavior "dereference of dead allocation") st
              | some (_, localAlloc) =>
                match val with
                | .uninit =>
                  match Miri.Memory.Allocation.writeUninit
                      (Miri.Memory.allocRange access.pointer.offset size)
                      (Miri.ABI.Size.ofBytes 8) localAlloc.allocation with
                  | .ok () alloc' =>
                    match st.machine.memory.setLiveAllocation access.pointer.allocId alloc' with
                    | .ok nextMem =>
                      .ok () { st with machine := { st.machine with memory := nextMem } }
                    | .error _ =>
                      .error (.undefinedBehavior "dereference of dead allocation") st
                  | .error _ _ => .error (.invalidProgram "memory writeUninit error") st
                | .scalar sc =>
                  if sc.size != size then
                    .error (.invalidProgram "scalar size mismatch in memory write") st
                  else if !annealValidateScalarForTyId lay.ty sc then
                    .error (.undefinedBehavior "writing invalid value") st
                  else
                    match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                        (Miri.Memory.allocRange access.pointer.offset size) sc
                        localAlloc.allocation with
                    | .ok () alloc' =>
                      match st.machine.memory.setLiveAllocation access.pointer.allocId alloc' with
                      | .ok nextMem =>
                        .ok () { st with machine := { st.machine with memory := nextMem } }
                      | .error _ =>
                        .error (.undefinedBehavior "dereference of dead allocation") st
                    | .error .readOnlyAllocation _ =>
                      .error (.undefinedBehavior "write to read-only allocation") st
                    | .error _ _ => .error (.invalidProgram "memory writeScalar error") st
                | .scalarPair _ _ =>
                  .error (.unsupported "scalarPair memory write in scalar/pointer fragment") st

/-- Write an `Immediate AnnealProv` into a `RuntimePlace AnnealProv` in the top frame.

* Out-of-bounds `localId`s propagate `StepError.stack (.invalidLocal ...)`.
* Writing to a `.dead` local (`StackError.localExpectedLive` from
  `Frame.getLocalOperand`) raises `StepError.undefinedBehavior` (matching rustc's
  `err_ub!(DeadLocal)` and `MirSemantics.evalStmt` on `.assign`).
* Writing to an `.indirect` memory-backed local or a `.memory` place (projected
  array element or dereferenced pointer) routes through `annealWriteMemoryPlace`
  (matching `Place.asMplaceOrMutableLocal` and `MemoryOperand`). -/
def annealWriteImmediate (val : Miri.Interpreter.Immediate AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match dest.ref with
  | .local frameIdx localId none _ =>
      if frameIdx != st.stack.frames.size - 1 then
        throw (.invalidProgram "place refers to another frame")
      match frame.getLocalOperand localId with
      | .error (.localExpectedLive _) =>
          throw (.undefinedBehavior "write to dead local")
      | .error e =>
          throw (.stack e)
      | .ok (.indirect mplace) =>
          annealWriteMemoryPlace val mplace dest.layout
      | .ok (.immediate _) =>
          let updatedFrame ←
            match frame.replaceLocalValue localId (.live (.immediate val)) with
            | .ok f => pure f
            | .error e => throw (.stack e)
          let idx := st.stack.frames.size - 1
          if h : idx < st.stack.frames.size then
            set { st with stack := { frames := st.stack.frames.set idx updatedFrame h } }
          else
            throw (.stack .emptyStack)
  | .memory mplace =>
      annealWriteMemoryPlace val mplace dest.layout
  | _ => throw (.unsupported "non-local immediate write in scalar fragment")

/-- Classify an encoded `Miri.MIR.TyId` into `Miri.Interpreter.CastTypeInfo` for
integer-like (`bool`, `char`, `i8..isize`, `u8..usize`) and thin raw-pointer
(`*const T` / `*mut T`) casts in `Miri.Interpreter.Cast.cast`. Floating-point,
provenance-exposure, unsizing, and aggregate casts fail closed with
`StepError.unsupported`. -/
def castTypeInfoOfEncodedTyId (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.CastTypeInfo :=
  match tyId with
  | 1 => .ok .boolean
  | 2 => .ok .character
  | 10 => .ok (.integer .i8)
  | 11 => .ok (.integer .i16)
  | 12 => .ok (.integer .i32)
  | 13 => .ok (.integer .i64)
  | 14 => .ok (.integer .i128)
  | 15 => .ok (.integer .isize)
  | 20 => .ok (.integer .u8)
  | 21 => .ok (.integer .u16)
  | 22 => .ok (.integer .u32)
  | 23 => .ok (.integer .u64)
  | 24 => .ok (.integer .u128)
  | 25 => .ok (.integer .usize)
  | 60 => .ok (.rawPointer 51)
  | 61 => .ok (.rawPointer 1)
  | 62 => .ok (.rawPointer 2)
  | 63 => .ok (.rawPointer 10)
  | 64 => .ok (.rawPointer 11)
  | 65 => .ok (.rawPointer 12)
  | 66 => .ok (.rawPointer 13)
  | 67 => .ok (.rawPointer 14)
  | 68 => .ok (.rawPointer 15)
  | 69 => .ok (.rawPointer 50)
  | 70 => .ok (.rawPointer 20)
  | 71 => .ok (.rawPointer 21)
  | 72 => .ok (.rawPointer 22)
  | 73 => .ok (.rawPointer 23)
  | 74 => .ok (.rawPointer 24)
  | 75 => .ok (.rawPointer 25)
  | 76 => .ok (.rawPointer 30)
  | 77 => .ok (.rawPointer 31)
  | 78 => .ok (.rawPointer 32)
  | 79 => .ok (.rawPointer 33)
  | 80 => .ok (.rawPointer 40)
  | 81 => .ok (.rawPointer 41)
  | 82 => .ok (.rawPointer 42)
  | _ => .error (.unsupported s!"cast typeInfo not wired in scalar fragment for TyId {tyId}")

/-- `CastHooks` instantiated for Anneal's single-threaded machine, supporting
integer-like `CastKind.IntToInt` and thin raw-pointer `CastKind.PtrToPtr` via
`Miri.Interpreter.Cast.cast`, while failing closed (`StepError.unsupported`) on
float, pointer-provenance exposure, unsizing, and transmute leaves. -/
def annealCastHooks (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.CastHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  typeInfo := fun _ tyId =>
    match castTypeInfoOfEncodedTyId tyId with
    | .ok info => pure info
    | .error err => throw err
  layoutOf := fun _ tyId => pure (layoutOfEncodedTyId tyId layouts)
  destLayout := fun p => p.layout
  readImmediate := fun _ op => annealReadImmediate op
  writeImmediate := fun _ val dest => annealWriteImmediate val dest
  writePointer := fun _ _ _ => throw (.unsupported "writePointer in cast")
  enforceValidity := fun _ _ => pure true
  enforceValidityRecursively := fun _ _ => pure true
  validatePlace := fun _ _ _ _ => throw (.unsupported "validatePlace in cast")
  derefPointer := fun _ _ => throw (.unsupported "derefPointer in cast")
  checkFunctionPointer := fun _ _ => throw (.unsupported "checkFunctionPointer in cast")
  exposeProvenance := fun _ _ => throw (.unsupported "exposeProvenance in cast")
  pointerFromExposedAddress := fun _ _ => throw (.unsupported "pointerFromExposedAddress in cast")
  usizeLayout := fun _ => pure (translateTy { kind := .uint .usize, layoutIdx := 0 })
  floatOps := {
    integerKindOf := fun _ _ => throw (.unsupported "floatOps.integerKindOf")
    formatOf := fun _ _ => throw (.unsupported "floatOps.formatOf")
    boolLayout := fun _ => pure (translateTy { kind := .bool, layoutIdx := 0 })
    floatNondeterministic := false
    chooseNaN := fun _ _ => throw (.unsupported "floatOps.chooseNaN") }
  ensureMonomorphic := fun _ _ => pure ()
  requireNoBoundVars := fun _ _ => pure ()
  resolveFunction := fun _ _ _ => throw (.unsupported "resolveFunction in cast")
  resolveClosureFnOnce := fun _ _ _ => throw (.unsupported "resolveClosureFnOnce in cast")
  functionPointer := fun _ _ => throw (.unsupported "functionPointer in cast")
  builtinDeref := fun _ _ _ => throw (.unsupported "builtinDeref in cast")
  boxLayout := fun _ _ => throw (.unsupported "boxLayout in cast")
  validateImmediateABI := fun _ _ => .error (.unsupported "validateImmediateABI in cast")
  copyAllowTransmute := fun _ _ _ => throw (.unsupported "copyAllowTransmute in cast")
  copyNoValidate := fun _ _ _ _ => throw (.unsupported "copyNoValidate in cast")
  projectRead := fun _ _ _ => throw (.unsupported "projectRead in cast")
  projectWrite := fun _ _ _ => throw (.unsupported "projectWrite in cast")
  fieldLayout := fun _ _ _ => throw (.unsupported "fieldLayout in cast")
  lockstepTails := fun _ _ _ => throw (.unsupported "lockstepTails in cast")
  vtableType := fun _ _ _ => throw (.unsupported "vtableType in cast")
  vtablePointer := fun _ _ _ => throw (.unsupported "vtablePointer in cast")
  principal := fun _ _ => throw (.unsupported "principal in cast")
  vtableEntries := fun _ _ _ => throw (.unsupported "vtableEntries in cast")
  supertraitSlot := fun _ _ _ => throw (.unsupported "supertraitSlot in cast")
  eraseSelfTraitRef := fun _ _ => throw (.unsupported "eraseSelfTraitRef in cast")
  normalizePrincipal := fun _ _ => throw (.unsupported "normalizePrincipal in cast")

/-- Zeroed host storage for a fresh `size`-byte allocation: the `zeroedStorage`
callback of `Miri.Memory.Allocation.tryNew`, which models rustc's
`AllocBytes::zeroed`. Anneal's machine never runs out of host memory, so the
callback always succeeds. -/
def annealZeroedStorage (size : Miri.ABI.Size) (_align : Miri.ABI.Align) :
    Option (Array UInt8) :=
  some (Array.replicate size.bytes.toNat 0)

/-- Base address that Anneal's machine assigns to the fresh stack allocation
`id`, namely `id * 2^32`.

Miri draws base addresses from an address generator with random slack. Nothing
in this fragment observes a numeric address, so a deterministic choice
suffices. Every multiple of `2^32` satisfies every alignment that
`Miri.ABI.Align.fromBytes` accepts (at most `2^29` bytes). While allocation ids
stay below `2^32`, the address is also non-null and allocations smaller than
4 GiB do not overlap. -/
def annealStackBaseAddr (id : Miri.Memory.AllocId) : UInt64 :=
  id.value <<< 32

/-- `PlaceHooks` instantiated for Anneal's single-threaded machine. They are the
memory leaves of `Miri.Interpreter.forceAllocation`, which moves an immediate
local into a fresh stack allocation.

* `allocateStack` follows rustc's `allocate_ptr`: it creates an uninitialized
  allocation with zeroed backing storage (`Allocation.tryNew`), reserves a
  fresh `AllocId`, records the allocation as live, caches the base address
  `annealStackBaseAddr id` in `mach.addresses` (the cache that
  `AnnealMachine.lookupBaseAddr` reads), and returns a pointer to that address
  with concrete provenance. Because `PointerProvenance.offsetIsAddr` holds for
  `Miri.Memory.Provenance`, a pointer's offset is its absolute address.
* `writeMemoryNoValidate` follows rustc's `ptr_get_alloc`: it subtracts the
  allocation's base address from the pointer address to obtain the
  allocation-relative offset that `Allocation.writeScalar` and
  `Allocation.writeUninit` expect.

Projections, dereferences, and writes of scalar pairs fail closed with
`StepError.unsupported`. -/
def annealPlaceHooks (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.PlaceHooks AnnealProv AnnealStepState Unit Unit where
  getFrame := do
    let state ← get
    match state.stack.currentFrame? with
    | some frame => pure frame
    | none => throw (.stack .emptyStack)
  setFrame := fun frame => do
    let state ← get
    let idx := state.stack.frames.size - 1
    if h : idx < state.stack.frames.size then
      set { state with stack := { frames := state.stack.frames.set idx frame h } }
    else
      throw (.stack .emptyStack)
  debugAssertions := false
  frameIndex := do
    let state ← get
    return state.stack.frames.size - 1
  resolveLayout := fun _ localId =>
    match lookupLocalDeclLayout localDecls layouts localId with
    | some l => pure l
    | none => throw (.stack (.missingLocalType localId))
  localToOp := fun _ _ => throw (.unsupported "localToOp")
  projection := fun _ => throw (.unsupported "projection")
  deref := fun _ _ _ => throw (.unsupported "deref")
  checkPlaceType := fun _ _ _ => throw (.unsupported "checkPlaceType")
  allocateStack := fun _ layout => do
    let allocation ←
      match Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
          annealZeroedStorage with
      | .ok allocation => pure allocation
      | .error _ => throw (.unsupported "stack allocation storage")
    let state ← get
    let (memory, reserved) := state.machine.memory.reserveAllocId
    let id ← match reserved with
      | .ok id => pure id
      | .error _ => throw (.unsupported "stack allocation ID")
    let base := annealStackBaseAddr id
    let memory := { memory with live := memory.live.push (id, ⟨.stack, allocation.withExtra none⟩) }
    let addresses := { state.machine.addresses with
      baseAddr := #[⟨id, base⟩] ++ state.machine.addresses.baseAddr }
    set { state with machine := { state.machine with memory := memory, addresses := addresses } }
    let pointer : Miri.Memory.Pointer (Option AnnealProv) :=
      ⟨Miri.ABI.Size.ofBytes base, some (.concrete id Miri.Memory.BorTag.one)⟩
    return ⟨⟨pointer, .none, none⟩, layout⟩
  writeMemoryNoValidate := fun _ value mplace => do
    let state ← get
    let memory := state.machine.memory
    let some id := mplace.mplace.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
      | throw (.unsupported "memory write through a pointer without an allocation")
    let some base := state.machine.lookupBaseAddr id
      | throw (.unsupported "memory write to an allocation without a base address")
    let offset := Miri.ABI.Size.ofBytes (mplace.mplace.ptr.offset.bytes - base)
    match memory.live.findIdx? (fun (k, _) => k == id) with
    | some idx =>
      match memory.live[idx]? with
      | some (k, ⟨kind, alloc⟩) =>
        let alloc' ← match value with
          | .uninit =>
              match Miri.Memory.Allocation.writeUninit
                  (Miri.Memory.allocRange offset mplace.layout.layout.size)
                  (Miri.ABI.Size.ofBytes 8) alloc with
              | EStateM.Result.ok _ a => pure a
              | EStateM.Result.error _ _ => throw (.unsupported "writeUninit failed")
          | .scalar s =>
              match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                  (Miri.Memory.allocRange offset s.size) s alloc with
              | EStateM.Result.ok _ a => pure a
              | EStateM.Result.error _ _ => throw (.unsupported "writeScalar failed")
          | .scalarPair _ _ =>
              throw (.unsupported "scalarPair in writeMemoryNoValidate")
        set { state with machine := { state.machine with
          memory := { memory with live := memory.live.set! idx (k, ⟨kind, alloc'⟩) } } }
      | none => throw (.unsupported "allocation not found")
    | none => throw (.unsupported "allocation not found")
  afterLocalMovedToMemory := fun _ _ _ => pure ()
  memoryOffset := fun _ _ _ _ _ => throw (.unsupported "memoryOffset")
  writeLocalImmediate := fun _ _ _ _ => throw (.unsupported "writeLocalImmediate")
  enforceValidity := fun _ _ => pure true
  validate := fun _ _ => pure ()

/-- Materialize an unprojected array destination `RuntimePlace` in memory,
mirroring `Miri.Interpreter.forceAllocation` (`Miri/Interpreter/Place.lean`):

* A `.memory` place, or a local that is already memory-backed (`.indirect`), is
  returned unchanged. As in `forceAllocation`, the existing allocation and its
  bytes and initialization mask are reused as they are.
* A `.dead` local raises `StepError.undefinedBehavior` (rustc's `DeadLocal`).
* An `.immediate` local moves into a fresh mutable stack allocation with the
  destination layout's size and alignment, which becomes the local's
  `MemPlace`.

The fresh allocation differs from `Miri.Interpreter.placeAllocateStack`, which
allocates with `.Uninit`: it is zero-filled and initialized
(`Allocation.fromBytes`), so its mask is the lazy `InitMask.new size true`. Its
callers in `annealAggregateHooks` complete normally only for zero-sized
aggregates and primitive scalar arrays, and for the latter `writeAggregate` and
`writeRepeat` overwrite every element of a padding-free layout. On normal
completion the bytes and per-byte initialization therefore agree with Miri's;
only the mask representation (lazy rather than materialized) differs. The old
immediate value is not copied because an initialized array local is never
immediate (`LocalRel.array_init_is_indirect`). -/
def annealEnsureAllocated (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.MemPlace AnnealProv) := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match dest.ref with
  | .memory mp => return mp
  | .local frameIdx localId none _ =>
      if frameIdx != st.stack.frames.size - 1 then
        throw (.invalidProgram "place refers to another frame")
      match frame.getLocalOperand localId with
      | .error (.localExpectedLive _) =>
          throw (.undefinedBehavior "write to dead local")
      | .error e =>
          throw (.stack e)
      | .ok (.indirect mp) => return mp
      | .ok (.immediate _) =>
          let sz := dest.layout.layout.size
          let al := dest.layout.layout.align.abi
          let allocation ←
            match Miri.Memory.Allocation.fromBytes (Array.replicate sz.bytes.toNat 0) al .Mut with
            | .ok a => pure a
            | .error _ => throw (.unsupported "stack allocation storage")
          let (memory, reserved) := st.machine.memory.reserveAllocId
          let id ← match reserved with
            | .ok id => pure id
            | .error _ => throw (.unsupported "stack allocation ID")
          let base := annealStackBaseAddr id
          let memory := { memory with live := memory.live.push (id, ⟨.stack, allocation.withExtra none⟩) }
          let addresses := { st.machine.addresses with
            baseAddr := #[⟨id, base⟩] ++ st.machine.addresses.baseAddr }
          let pointer : Miri.Memory.Pointer (Option AnnealProv) :=
            ⟨Miri.ABI.Size.ofBytes base, some (.concrete id Miri.Memory.BorTag.one)⟩
          let mp : Miri.Interpreter.MemPlace AnnealProv := ⟨pointer, .none, none⟩
          let updatedFrame ←
            match frame.replaceLocalValue localId (.live (.indirect mp)) with
            | .ok f => pure f
            | .error e => throw (.stack e)
          let idx := st.stack.frames.size - 1
          if h : idx < st.stack.frames.size then
            set { st with
                  stack := { frames := st.stack.frames.set idx updatedFrame h }
                  machine := { st.machine with memory := memory, addresses := addresses } }
            return mp
          else
            throw (.stack .emptyStack)
  | _ => throw (.unsupported "projected local in annealEnsureAllocated")

/-- Write scalar `sc` across `n` contiguous elements of size `elemSize` starting
at allocation-relative byte offset `off`. -/
def writeScalarRepeatedly
    (off : Miri.ABI.Size)
    (elemSize : Miri.ABI.Size)
    (n : Nat)
    (sc : Miri.Memory.Scalar AnnealProv)
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    Except Miri.Interpreter.StepError
      (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :=
  match n with
  | 0 => .ok alloc
  | k + 1 =>
      match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange off elemSize) sc alloc with
      | EStateM.Result.ok _ alloc' =>
          writeScalarRepeatedly
            (Miri.ABI.Size.ofBytes (off.bytes + elemSize.bytes))
            elemSize k sc alloc'
      | EStateM.Result.error _ _ =>
          .error (.unsupported "writeScalarRepeatedly failed")

/-- Write an aggregate element `Immediate` in-place into a projected `.memory`
slot `dest` inside `mach.memory.live` (`live.set!`, matching
`annealPlaceHooks.writeMemoryNoValidate` and `memCopyRepeatedly`). -/
def annealWriteAggregateElem (val : Miri.Interpreter.Immediate AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let st ← get
  let some _frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match dest.ref with
  | .memory mp =>
      let some id := mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
        | throw (.unsupported "memory write through a pointer without an allocation")
      let some base := st.machine.lookupBaseAddr id
        | throw (.unsupported "memory write to an allocation without a base address")
      let offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - base)
      match st.machine.memory.live.findIdx? (fun (k, _) => k == id) with
      | some idx =>
          match st.machine.memory.live[idx]? with
          | some (k, ⟨kind, alloc⟩) =>
              let alloc' ←
                match val with
                | .scalar s =>
                    match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                        (Miri.Memory.allocRange offset s.size) s alloc with
                    | EStateM.Result.ok _ a => pure a
                    | EStateM.Result.error _ _ => throw (.unsupported "writeScalar failed")
                | .uninit =>
                    match Miri.Memory.Allocation.writeUninit
                        (Miri.Memory.allocRange offset dest.layout.layout.size)
                        (Miri.ABI.Size.ofBytes 8) alloc with
                    | EStateM.Result.ok _ a => pure a
                    | EStateM.Result.error _ _ => throw (.unsupported "writeUninit failed")
                | .scalarPair _ _ =>
                    throw (.unsupported "scalarPair in annealWriteAggregateElem")
              set { st with machine := { st.machine with
                memory := { st.machine.memory with
                  live := st.machine.memory.live.set! idx (k, ⟨kind, alloc'⟩) } } }
          | none => throw (.unsupported "allocation not found")
      | none => throw (.unsupported "allocation not found")
  | _ => throw (.unsupported "non-memory aggregate element write")

/-- `AggregateHooks` instantiated for Anneal's single-threaded machine,
supporting homogeneous array construction (`AggregateKind.Array`) and
`Rvalue.Repeat` (`Miri.Interpreter.writeAggregate` and `Miri.Interpreter.writeRepeat`). -/
def annealAggregateHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  placeLayout := fun p => p.layout
  evalOperand := fun _ op known => do
    let opTy ← annealEvalOperand localDecls layouts op known
    let imm ← annealReadImmediate opTy
    return ⟨.immediate imm.imm, imm.layout⟩
  evalOperandAt := fun _ _ op known => do
    let opTy ← annealEvalOperand localDecls layouts op known
    let imm ← annealReadImmediate opTy
    return ⟨.immediate imm.imm, imm.layout⟩
  readPointer := fun _ _ => throw (.unsupported "readPointer in aggregate")
  readScalar := fun _ op => do
    let imm ← annealReadImmediate op
    match imm.imm.toScalar with
    | .ok sc => return sc
    | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
  projectDowncast := fun _ _ _ => throw (.unsupported "projectDowncast in aggregate")
  projectField := fun _ dest idx => do
    match dest.layout.layout.fields with
    | .Array stride _ =>
        let mp ← annealEnsureAllocated dest
        let elemLay := arrayElemLayoutOf layouts dest.layout stride
        let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (idx * stride.bytes.toNat))
        return ⟨.memory { mp with ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff.bytes) } },
                elemLay⟩
    | _ => throw (.unsupported "non-array projectField in aggregate")
  copyOp := fun _ src dest => do
    let imm ← annealReadImmediate src
    annealWriteAggregateElem imm.imm dest
  copyOpNoValidate := fun _ src dest _ => do
    let imm ← annealReadImmediate src
    annealWriteAggregateElem imm.imm dest
  writeDiscriminant := fun _ _ dest => do
    let _ ← annealEnsureAllocated dest
    pure ()
  enforceValidity := fun _ _ => pure true
  validate := fun _ _ => pure ()
  forceAllocation := fun _ dest => do
    let mp ← annealEnsureAllocated dest
    return ⟨.memory mp, dest.layout⟩
  length := fun _ dest =>
    match dest.layout.layout.fields with
    | .Array _ count => pure count
    | _ => throw (.invalidProgram "repeat destination is not an array")
  getPlaceAllocMut := fun _ _ => pure ()
  projectIndex := fun _ dest idx => do
    match dest.ref, dest.layout.layout.fields with
    | .memory mp, .Array stride _ =>
        let elemLay := arrayElemLayoutOf layouts dest.layout stride
        let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (idx.toNat * stride.bytes.toNat))
        return ⟨.memory { mp with ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff.bytes) } },
                elemLay⟩
    | _, _ => throw (.unsupported "projectIndex in aggregate")
  placePointer := fun dest =>
    match dest.ref with
    | .memory mp => .ok mp.ptr
    | _ => .error (.invalidProgram "placePointer requires mplace")
  wrappingOffset := Miri.Interpreter.aggregateWrappingOffset annealPointerArithmetic
  -- Scalar-element repetition uses `Allocation.writeScalar` (`writeScalarRepeatedly`)
  -- rather than `Allocation.copyRepeatedly` so fully initialized stack allocations
  -- retain the lazy `InitMask.new byteSize true` representation shared with
  -- `annealWriteAggregateElem` and `ArraySliceRel` (whereas `copyRepeatedly`
  -- materializes bit blocks via `applyCopy` and special-cases 1-byte zero-count copies).
  memCopyRepeatedly := fun _ firstPtr restPtr elemSize count _ => do
    if count == 0 then
      pure ()
    else
      let st ← get
      let some id := firstPtr.provenance.bind Miri.Memory.Provenance.getAllocId
        | throw (.unsupported "repeat pointer without allocation id")
      let some base := st.machine.lookupBaseAddr id
        | throw (.unsupported "repeat pointer without base address")
      let firstOff := Miri.ABI.Size.ofBytes (firstPtr.offset.bytes - base)
      let restOff := Miri.ABI.Size.ofBytes (restPtr.offset.bytes - base)
      match st.machine.memory.live.findIdx? (fun (k, _) => k == id) with
      | some allocIdx =>
          match st.machine.memory.live[allocIdx]? with
          | some (k, ⟨kind, alloc⟩) =>
              let sc ←
                match alloc.readScalar annealTargetDataLayout
                    (Miri.Memory.allocRange firstOff elemSize) false with
                | .ok s => pure s
                | .error _ => throw (.unsupported "repeat readScalar failed")
              let alloc' ←
                match writeScalarRepeatedly restOff elemSize count.toNat sc alloc with
                | .ok a => pure a
                | .error err => throw err
              set { st with machine := { st.machine with
                memory := { st.machine.memory with
                  live := st.machine.memory.live.set! allocIdx (k, ⟨kind, alloc'⟩) } } }
          | none => throw (.unsupported "repeat allocation not found")
      | none => throw (.unsupported "repeat allocation not found")

/-- Run `Miri.Interpreter.forceAllocation` under `annealPlaceHooks`, reporting a
dead local as undefined behavior.

`forceAllocation` reads the local through `Frame.getLocalOperand`, which fails
with `StackError.localExpectedLive` on a dead local; `lean-miri` wraps that as
`StepError.stack`, for which `RunLoop.reportsUB` is `false`. rustc instead
raises `err_ub!(DeadLocal)` from `LocalState::access_mut` when `force_allocation`
reaches a dead local (for example in `&raw const _1` after `StorageDead(_1)`),
and Anneal's `MirSemantics.evalRvalue` returns `.ub` for `Rvalue.rawPtr` and
`Rvalue.ref` of a dead local. This wrapper reclassifies exactly that error, as
`annealEvalOperand` does for reads of dead locals, and leaves every other
outcome and every resulting state unchanged. -/
def annealForceAllocation (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.MemPlace AnnealProv) :=
  fun st =>
    match Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) () place st with
    | .ok res st' => .ok res.mplace st'
    | .error (.stack (.localExpectedLive _)) st' =>
        .error (.undefinedBehavior "address of dead local") st'
    | .error e st' => .error e st'

/-- `RvalueHooks` instantiated for Anneal's single-threaded machine.

`writeAggregate` and `writeRepeat` delegate to `annealAggregateHooks`,
`forceAllocation` is `annealForceAllocation`, and `toRef` turns a memory place
into the pointer immediate that refers to it via `MemPlace.toRef` (rustc's
`MPlaceTy::to_ref`), reporting a malformed place as `StepError.invalidProgram`. -/
def annealRvalueHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  placeLayout := fun p => p.layout
  evalPlace := fun _ p _ => annealEvalPlace localDecls layouts p
  evalOperand := fun _ op known => annealEvalOperand localDecls layouts op known
  evalPlaceToOp := fun _ p known => annealEvalOperand localDecls layouts (.Copy p) known
  readImmediate := fun _ op => annealReadImmediate op
  writeImmediate := fun _ val dest => annealWriteImmediate val dest
  writePointer := fun _ _ _ => throw (.unsupported "writePointer")
  threadLocalPointer := fun _ _ => throw (.unsupported "threadLocalPointer")
  withRetagMode := fun _ _ action => action
  copyOp := fun _ src dest => do
    let imm ← annealReadImmediate src
    annealWriteImmediate imm.imm dest
  copyOpAllowTransmute := fun _ src dest => do
    let imm ← annealReadImmediate src
    annealWriteImmediate imm.imm dest
  binaryOp := fun c op l r => Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) c op l r
  unaryOp := fun c op v => Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks localDecls layouts) c op v
  writeAggregate := fun c k os d =>
    Miri.Interpreter.writeAggregate (annealAggregateHooks localDecls layouts) c k os d
  writeRepeat := fun c o d =>
    Miri.Interpreter.writeRepeat (annealAggregateHooks localDecls layouts) c o d
  forceAllocation := fun _ v => annealForceAllocation localDecls layouts v
  toRef := fun _ mp =>
    match mp.toRef annealTargetDataLayout with
    | .ok value => pure value
    | .error error => throw (.invalidProgram s!"place reference: {repr error}")
  enforceValidity := fun _ _ => pure true
  retagPtrValue := fun _ _ _ => pure none
  placeBaseRaw := fun _ _ => pure false
  normalize := fun _ tyId => pure tyId
  cast := fun c src kind ty dest =>
    Miri.Interpreter.Cast.cast (annealCastHooks layouts) c 16 src kind ty dest
  readDiscriminant := fun _ _ => throw (.unsupported "readDiscriminant")
  discriminantForVariant := fun _ _ _ => throw (.unsupported "discriminantForVariant")

/-! ## 4. Intrinsic Calls and Non-Diverging Intrinsic Statements (`LM-4.2`)

`annealIntrinsicHooks` instantiates `Miri.Interpreter.IntrinsicHooks` for
Anneal's single-threaded machine, so that the vendored
`Miri.Interpreter.Intrinsics.eval` and `Intrinsics.evalNondiverging` evaluate
intrinsic calls and `StatementKind::Intrinsic` statements. `annealCallHooks`
instantiates `Miri.Interpreter.CallHooks` so that the vendored call pipeline
`Miri.Interpreter.Call.evalCallTerminator` evaluates a `TerminatorKind::Call`
of an `AnnealIntrinsic` and dispatches it to `Intrinsics.eval`. The memory
leaves are the vendored operations: `MemoryLifecycle.memCopyRepeatedly` (through
`Intrinsics.memoryCopyAdapter`) for copies, `Allocation.writeRepeatedByte` for
`write_bytes`, `Memory.checkAndDerefPtr` for bounds and liveness, and
`Memory.checkPtrAlign` for alignment. Leaves that no `AnnealIntrinsic` reaches
fail closed with `StepError.unsupported`. -/

/-- Throw `StepError.unsupported` for a machine leaf that Anneal's intrinsic
fragment does not provide. -/
def annealUnsupportedLeaf {S A : Type} (leaf : String) : EStateM Miri.Interpreter.StepError S A :=
  throw (.unsupported s!"{leaf} is outside Anneal's intrinsic fragment")

/-- Float operation leaves; no `AnnealIntrinsic` reads a float. -/
def annealUnsupportedFloatOps :
    Miri.Interpreter.FloatOpsHooks AnnealProv AnnealStepState Unit where
  integerKindOf := fun _ _ => annealUnsupportedLeaf "floatOps.integerKindOf"
  formatOf := fun _ _ => annealUnsupportedLeaf "floatOps.formatOf"
  boolLayout := fun _ => pure (translateTy { kind := .bool, layoutIdx := 0 })
  floatNondeterministic := false
  chooseNaN := fun _ _ => annealUnsupportedLeaf "floatOps.chooseNaN"

/-- Allocation lookup for `Miri.Memory.checkPtrAlign`.

rustc's `is_ptr_misaligned` asks `get_alloc_info`, which also answers for a
deallocated allocation (`AllocKind::Dead`). Anneal's machine keeps no table of
freed allocations, so a lookup of an allocation that is no longer live reports
a dead allocation of alignment `1`. For `AnnealProv`
(`PointerProvenance.offsetIsAddr`) and the default machine alignment check,
`isPtrMisaligned` never consults the allocation's alignment or kind: it tests
the absolute address, so this fallback only keeps the lookup total. -/
def annealAlignLookup (mach : AnnealMachine) :
    Miri.Memory.AllocId → Except Miri.Memory.AllocationLookupError Miri.Memory.AllocationInfo :=
  fun allocId =>
    match annealLookupAlloc mach allocId with
    | .ok info => .ok info
    | .error _ =>
      .ok { size := Miri.ABI.Size.ZERO, align := Miri.ABI.Align.ONE, kind := .dead,
            mutability := .Not }

/-- rustc's `check_ptr_align` with alignment enforced (Miri's default
`-Zmiri-check-alignment`), through the vendored `Miri.Memory.checkPtrAlign`.
A misaligned pointer is undefined behavior. -/
def annealCheckPtrAlign (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (align : Miri.ABI.Align) : Miri.Interpreter.RvalueM AnnealStepState Unit :=
  fun st =>
    match Miri.Memory.checkPtrAlign ptr align true (annealResolvePtr st.machine)
        (annealAlignLookup st.machine) (fun _ _ _ _ _ => none) with
    | .ok () => .ok () st
    | .error (.alignmentCheckFailed _) =>
      .error (.undefinedBehavior "accessing memory with an unaligned pointer") st
    | .error err => .error (.invalidProgram s!"alignment check: {err}") st

/-- Pointer access leaf of `MemoryCopyHooks` (rustc's `get_ptr_access`): check
`size` bytes at `ptr` with `Miri.Memory.checkAndDerefPtr` against the memory
`memory` and the cached base addresses of `mach`. A zero-sized access needs no
allocation (`none`); a dangling, out-of-bounds, or provenance-free access of
non-zero size fails. -/
def annealCopyPointerAccess (memory : AnnealMemory) (mach : AnnealMachine)
    (ptr : Miri.Memory.Pointer (Option AnnealProv)) (size : Miri.ABI.Size) :
    Miri.Memory.MemoryStateHookResult AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind AnnealMachine
      (Option (Miri.Memory.AllocId × Miri.ABI.Size × Miri.Memory.BorTag)) :=
  let mach' : AnnealMachine := { mach with memory := memory }
  { memory := memory
    state := mach'
    outcome :=
      match Miri.Memory.sizeAsI64 size with
      | .error err => .error (toString err)
      | .ok signedSize =>
        match Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize .memoryAccess
            (annealResolvePtr mach') (annealLookupAlloc mach') with
        | .ok none => .ok none
        | .ok (some access) =>
          .ok (some (access.pointer.allocId, access.pointer.offset, access.pointer.extra))
        | .error err => .error (toString err) }

/-- `MemoryCopyHooks` of `MemoryLifecycle.memCopyRepeatedly` for Anneal's
machine, whose hook state is the machine itself.

* `pointerAccess` is `annealCopyPointerAccess`.
* `tryGetAllocId` resolves the pointer's allocation through the cached base
  addresses (rustc's `ptr_try_get_alloc_id`).
* `beforeAllocationAccess`, `beforeMemoryRead`, and `beforeMemoryWrite` succeed
  without effect. They are the machine's access hooks (data-race detection and
  the aliasing model); Anneal's single-threaded machine has no data races, and
  like every other memory access of this instantiation they track no borrow
  state, so Tree Borrows violations are not detected here (Anneal's own
  `TreeBorrowPerm` checks are stricter). -/
def annealMemoryCopyHooks :
    Miri.Memory.MemoryCopyHooks AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind AnnealMachine Miri.Memory.BorTag where
  synchronizeMemory := fun memory mach => { mach with memory := memory }
  pointerAccess := annealCopyPointerAccess
  tryGetAllocId := fun memory mach ptr size =>
    match annealResolvePtr { mach with memory := memory } ptr (Int.ofNat size.toNat) with
    | .ok resolved => some resolved.allocId
    | .error _ => none
  beforeAllocationAccess := fun memory mach _ =>
    { memory := memory, state := mach, outcome := .ok () }
  beforeMemoryRead := fun mach memory _ _ _ _ _ =>
    { memory := memory, hooks := mach, outcome := .ok () }
  beforeMemoryWrite := fun mach memory _ _ _ _ _ =>
    { memory := memory, hooks := mach, outcome := .ok () }

/-- Classify a failure of `MemoryLifecycle.memCopyRepeatedly`: a failed pointer
access (dangling, out-of-bounds, or provenance-free), overlapping
non-overlapping ranges (`copy_nonoverlapping`'s `copyRangesOverlap`), and a
write to read-only memory are undefined behavior, as in rustc's
`mem_copy_repeatedly`. -/
def annealClassifyMemCopyError : Miri.Memory.MemoryLifecycleError → Miri.Interpreter.StepError
  | .hookFailure hook message =>
    .undefinedBehavior s!"memory copy pointer check failed ({hook}): {message}"
  | .allocation .copyRangesOverlap =>
    .undefinedBehavior "copy_nonoverlapping called on overlapping ranges"
  | .allocation .readOnlyAllocation => .undefinedBehavior "write to read-only allocation"
  | .allocation (.outOfBounds _ _) => .undefinedBehavior "memory copy out of bounds"
  | .allocationNotLocal _ => .unsupported "memory copy of a non-local allocation"
  | err => .invalidProgram s!"memory copy: {err}"

/-- Copy `size` bytes from `source` to `dest` (rustc's `mem_copy`), lifting the
vendored `Intrinsics.memoryCopyAdapter` (`MemoryLifecycle.memCopyRepeatedly`
with one copy) from the memory/hook-state pair to `AnnealStepState`. Memory
mutations persist even when the copy fails. -/
def annealMemCopy (source dest : Miri.Memory.Pointer (Option AnnealProv))
    (size : Miri.ABI.Size) (nonoverlapping : Bool) :
    Miri.Interpreter.RvalueM AnnealStepState Unit :=
  fun st =>
    match Miri.Interpreter.Intrinsics.memoryCopyAdapter annealTargetDataLayout
        annealMemoryCopyHooks annealClassifyMemCopyError () source dest size nonoverlapping
        (st.machine.memory, st.machine) with
    | .ok () (memory, mach) => .ok () { st with machine := { mach with memory := memory } }
    | .error err (memory, mach) => .error err { st with machine := { mach with memory := memory } }

/-- Write `size` copies of `byte` at `ptr` (rustc's `write_bytes_ptr` with
`repeat_n`): a zero-sized write touches no allocation; otherwise the access is
checked with `Miri.Memory.checkAndDerefPtr` and performed by the vendored
`Allocation.writeRepeatedByte`, which initializes the bytes and clears their
provenance. Neither rustc's `write_bytes_intrinsic` nor this leaf checks
alignment. -/
def annealWriteRepeatedBytes (ptr : Miri.Memory.Pointer (Option AnnealProv)) (byte : UInt8)
    (size : Miri.ABI.Size) : Miri.Interpreter.RvalueM AnnealStepState Unit :=
  fun st =>
    match Miri.Memory.sizeAsI64 size with
    | .error _ => .error (.invalidProgram "write_bytes size does not fit i64") st
    | .ok signedSize =>
      match Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr signedSize .memoryAccess
          (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
      | .error _ => .error (.undefinedBehavior "write_bytes pointer check failed") st
      | .ok none => .ok () st
      | .ok (some access) =>
        match st.machine.memory.live.find? (fun entry => entry.1 == access.pointer.allocId) with
        | none => .error (.undefinedBehavior "write_bytes to a dead allocation") st
        | some (_, localAlloc) =>
          match Miri.Memory.Allocation.writeRepeatedByte access.pointer.offset byte size.bytes
              (Miri.ABI.Size.ofBytes 8) localAlloc.allocation with
          | .ok () alloc' =>
            match st.machine.memory.setLiveAllocation access.pointer.allocId alloc' with
            | .ok nextMem => .ok () { st with machine := { st.machine with memory := nextMem } }
            | .error _ => .error (.undefinedBehavior "write_bytes to a dead allocation") st
          | .error .readOnlyAllocation _ =>
            .error (.undefinedBehavior "write to read-only allocation") st
          | .error _ _ => .error (.invalidProgram "write_bytes allocation error") st

/-- Write a pointer immediate (`Scalar::from_maybe_pointer`) to `dest`. -/
def annealWritePointer (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit :=
  match Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout ptr with
  | .ok sc => annealWriteImmediate (.scalar sc) dest
  | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)

/-- Lift `Miri.Interpreter.ControlFlow.returnToBlock` (rustc's
`return_to_block`) to `RvalueM`. -/
def annealReturnToBlock (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.RvalueM AnnealStepState Unit :=
  fun st =>
    match Miri.Interpreter.ControlFlow.returnToBlock target st with
    | (st', .ok ()) => .ok () st'
    | (st', .error err) => .error err st'

/-- SIMD leaves; no `AnnealIntrinsic` is a SIMD intrinsic. -/
def annealIntrinsicSimdHooks (layouts : LayoutTable) :
    Miri.Interpreter.IntrinsicSimdHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  boolTy := 1
  u8Ty := 20
  isSimd := fun _ _ => pure false
  simdSizeAndType := fun _ _ => annealUnsupportedLeaf "simd.simdSizeAndType"
  forceAllocation := fun _ _ => annealUnsupportedLeaf "simd.forceAllocation"
  placeLayout := fun p => p.layout
  placePointer := fun _ => .error (.unsupported "simd.placePointer")
  fieldRead := fun _ _ _ => annealUnsupportedLeaf "simd.fieldRead"
  fieldWrite := fun _ _ _ => annealUnsupportedLeaf "simd.fieldWrite"
  fieldLayout := fun _ _ _ => annealUnsupportedLeaf "simd.fieldLayout"
  indexRead := fun _ _ _ => annealUnsupportedLeaf "simd.indexRead"
  indexWrite := fun _ _ _ => annealUnsupportedLeaf "simd.indexWrite"
  readImmediate := fun _ _ => annealUnsupportedLeaf "simd.readImmediate"
  writeImmediate := fun _ _ _ => annealUnsupportedLeaf "simd.writeImmediate"
  copyOp := fun _ _ _ => annealUnsupportedLeaf "simd.copyOp"
  derefImmediate := fun _ _ => annealUnsupportedLeaf "simd.derefImmediate"
  readPlaceImmediate := fun _ _ => annealUnsupportedLeaf "simd.readPlaceImmediate"
  unalignedPlace := fun _ _ _ => annealUnsupportedLeaf "simd.unalignedPlace"
  checkAlign := fun _ _ _ => annealUnsupportedLeaf "simd.checkAlign"
  readBytes := fun _ _ _ => annealUnsupportedLeaf "simd.readBytes"
  writeBytes := fun _ _ _ => annealUnsupportedLeaf "simd.writeBytes"
  shuffleConst := fun _ _ => annealUnsupportedLeaf "simd.shuffleConst"
  alignmentConst := fun _ _ => annealUnsupportedLeaf "simd.alignmentConst"
  scalarOps := annealScalarOpsHooks .nil layouts
  floatOps := annealUnsupportedFloatOps
  castHooks := annealCastHooks layouts
  chooseEqualFloatRight := fun _ _ _ => annealUnsupportedLeaf "simd.chooseEqualFloatRight"
  fuseMulAdd := fun _ => annealUnsupportedLeaf "simd.fuseMulAdd"
  mathLane := fun _ _ _ _ => annealUnsupportedLeaf "simd.mathLane"
  returnToBlock := fun _ target => annealReturnToBlock target

/-- Atomic leaves; no `AnnealIntrinsic` is an atomic intrinsic. -/
def annealIntrinsicAtomicHooks (layouts : LayoutTable) :
    Miri.Interpreter.IntrinsicAtomicHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  getGlobal := fun _ => none
  setGlobal := fun st _ => st
  threads := fun _ => Miri.Concurrency.ThreadManager.initial true
  getAtomic := fun _ _ => .error (.unsupported "atomic.getAtomic")
  setAtomic := fun _ _ => annealUnsupportedLeaf "atomic.setAtomic"
  placeLayout := fun p => p.layout
  placePointer := fun _ => .error (.unsupported "atomic.placePointer")
  physicalRead := fun _ _ => annealUnsupportedLeaf "atomic.physicalRead"
  physicalWrite := fun _ _ _ => annealUnsupportedLeaf "atomic.physicalWrite"
  ghostRead := fun _ _ => annealUnsupportedLeaf "atomic.ghostRead"
  checkPointerAlign := fun _ _ _ => annealUnsupportedLeaf "atomic.checkPointerAlign"
  resolveAllocation := fun _ _ => annealUnsupportedLeaf "atomic.resolveAllocation"
  mutability := fun _ _ => annealUnsupportedLeaf "atomic.mutability"
  scalarOps := annealScalarOpsHooks .nil layouts
  loadChoiceRank := fun _ _ => annealUnsupportedLeaf "atomic.loadChoiceRank"
  weakPolicy := .neverFail
  weakSuccessChoice := fun _ => annealUnsupportedLeaf "atomic.weakSuccessChoice"
  diagnostic := fun _ _ => annealUnsupportedLeaf "atomic.diagnostic"
  classifyDispatchError := fun _ => .unsupported "atomic dispatch"
  classifyGlobalError := fun _ => .unsupported "atomic global state"
  orderingConst := fun _ _ => annealUnsupportedLeaf "atomic.orderingConst"
  volatileConst := fun _ _ => annealUnsupportedLeaf "atomic.volatileConst"
  derefPointer := fun _ _ => annealUnsupportedLeaf "atomic.derefPointer"
  readImmediate := fun _ _ => annealUnsupportedLeaf "atomic.readImmediate"
  writeImmediate := fun _ _ _ => annealUnsupportedLeaf "atomic.writeImmediate"
  returnToBlock := fun _ target => annealReturnToBlock target

/-- `type_id` leaves; no `AnnealIntrinsic` queries type identity. -/
def annealIntrinsicTypeIdHooks :
    Miri.Interpreter.IntrinsicTypeIdHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  hasErasableRegions := fun _ _ => annealUnsupportedLeaf "typeId.hasErasableRegions"
  typeHash := fun _ _ => annealUnsupportedLeaf "typeId.typeHash"
  u128Layout := fun _ => annealUnsupportedLeaf "typeId.u128Layout"
  unitLayout := fun _ => annealUnsupportedLeaf "typeId.unitLayout"
  reserveTypeId := fun _ _ => annealUnsupportedLeaf "typeId.reserveTypeId"
  globalRootPointer := fun _ _ _ => annealUnsupportedLeaf "typeId.globalRootPointer"
  resolvePointer := fun _ _ => annealUnsupportedLeaf "typeId.resolvePointer"
  globalTypeId := fun _ _ => annealUnsupportedLeaf "typeId.globalTypeId"
  placeLayout := fun p => p.layout
  copyAllowTransmute := fun _ _ _ => annealUnsupportedLeaf "typeId.copyAllowTransmute"
  projectFieldRead := fun _ _ _ => annealUnsupportedLeaf "typeId.projectFieldRead"
  projectFieldWrite := fun _ _ _ => annealUnsupportedLeaf "typeId.projectFieldWrite"
  elementLayout := fun _ _ => annealUnsupportedLeaf "typeId.elementLayout"
  offsetRead := fun _ _ _ _ _ => annealUnsupportedLeaf "typeId.offsetRead"
  offsetWrite := fun _ _ _ _ _ => annealUnsupportedLeaf "typeId.offsetWrite"
  readImmediate := fun _ _ => annealUnsupportedLeaf "typeId.readImmediate"
  readPlaceScalar := fun _ _ => annealUnsupportedLeaf "typeId.readPlaceScalar"
  writeScalar := fun _ _ _ => annealUnsupportedLeaf "typeId.writeScalar"

/-- C variadic-argument leaves; no `AnnealIntrinsic` uses `va_list`. -/
def annealIntrinsicVarArgsHooks :
    Miri.Interpreter.IntrinsicVarArgsHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  getLists := fun _ => #[]
  setLists := fun st _ => st
  markDead := fun st _ _ _ => st
  reserveAllocId := fun _ => annealUnsupportedLeaf "varArgs.reserveAllocId"
  globalRootPointer := fun _ _ => annealUnsupportedLeaf "varArgs.globalRootPointer"
  resolvePointer := fun _ _ => annealUnsupportedLeaf "varArgs.resolvePointer"
  destLayout := fun p => p.layout
  layoutOf := fun _ _ => annealUnsupportedLeaf "varArgs.layoutOf"
  typeInfo := fun _ _ => annealUnsupportedLeaf "varArgs.typeInfo"
  identicalCTypes := fun _ _ _ => annealUnsupportedLeaf "varArgs.identicalCTypes"
  isCVoid := fun _ _ => annealUnsupportedLeaf "varArgs.isCVoid"
  vaListFields := fun _ _ => annealUnsupportedLeaf "varArgs.vaListFields"
  isRawPointer := fun _ _ => annealUnsupportedLeaf "varArgs.isRawPointer"
  projectField := fun _ _ _ => annealUnsupportedLeaf "varArgs.projectField"
  derefPointer := fun _ _ => annealUnsupportedLeaf "varArgs.derefPointer"
  placePointer := fun _ => .error (.unsupported "varArgs.placePointer")
  readPointer := fun _ _ => annealUnsupportedLeaf "varArgs.readPointer"
  readScalar := fun _ _ => annealUnsupportedLeaf "varArgs.readScalar"
  writePointer := fun _ _ _ => annealUnsupportedLeaf "varArgs.writePointer"
  forceAllocation := fun _ _ => annealUnsupportedLeaf "varArgs.forceAllocation"
  writeBytesPointer := fun _ _ _ _ => annealUnsupportedLeaf "varArgs.writeBytesPointer"
  copyAllowTransmute := fun _ _ _ => annealUnsupportedLeaf "varArgs.copyAllowTransmute"

/-- Integer kind of an integral `Miri.MIR.TyId` (`IntrinsicHooks.integerKind`);
an integer intrinsic applied to any other type is an invalid program. -/
def annealIntegerKindOf (tyId : Miri.MIR.TyId) :
    Miri.Interpreter.RvalueM AnnealStepState Miri.MIR.IntegerKind :=
  match classifyEncodedTyId tyId with
  | .ok (.integer kind) => pure kind
  | .ok _ => throw (.invalidProgram s!"integer intrinsic on non-integer TyId {tyId}")
  | .error err => throw err

/-- `IntrinsicHooks` instantiated for Anneal's single-threaded machine
(`LM-4.2`).

* Operands, places, and immediates use the same leaves as `annealRvalueHooks`
  (`annealEvalOperand`, `annealReadImmediate`, `annealWriteImmediate`), and
  integer arithmetic uses `annealScalarOpsHooks`.
* `layoutOf` and `pointeeType` decode the encoded TyIds of `encodeTyId`;
  `maxSizeOfVal` is `isize::MAX` (rustc's `max_size_of_val`).
* `checkAlign` is `annealCheckPtrAlign`, `memCopy` is `annealMemCopy`, and
  `writeBytes` is `annealWriteRepeatedBytes`.
* `returnToBlock` is `ControlFlow.returnToBlock`.
* Every other leaf fails closed with `StepError.unsupported`. -/
def annealIntrinsicHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.IntrinsicHooks AnnealProv AnnealStepState Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  simdHooks := annealIntrinsicSimdHooks layouts
  atomicHooks := annealIntrinsicAtomicHooks layouts
  typeIdHooks := annealIntrinsicTypeIdHooks
  varArgsHooks := annealIntrinsicVarArgsHooks
  varArgsFuel := 0
  target := annealTargetDataLayout
  pointerOffset := Miri.ABI.Size.ofBytes 8
  maxSizeOfVal := Miri.ABI.Size.ofBytes 0x7fff_ffff_ffff_ffff
  destLayout := fun p => p.layout
  layoutOf := fun _ tyId => pure (layoutOfEncodedTyId tyId layouts)
  pointeeType := fun _ tyId =>
    match rawPtrPointeeEncodedTyId? tyId with
    | some pointee => pure pointee
    | none => throw (.unsupported s!"pointee of TyId {tyId} is not encoded")
  integerKind := fun _ tyId => annealIntegerKindOf tyId
  usizeLayout := fun _ => pure (translateTy { kind := .uint .usize, layoutIdx := 0 })
  isizeLayout := fun _ => pure (translateTy { kind := .int .isize, layoutIdx := 0 })
  readImmediate := fun _ op => annealReadImmediate op
  evalOperand := fun _ op => annealEvalOperand localDecls layouts op none
  evalOperandAt := fun _ _ op => annealEvalOperand localDecls layouts op none
  writeImmediate := fun _ imm dest => annealWriteImmediate imm dest
  writePointer := fun _ ptr dest => annealWritePointer ptr dest
  copyOp := fun _ _ _ => annealUnsupportedLeaf "intrinsic.copyOp"
  placeToOp := fun _ _ => annealUnsupportedLeaf "intrinsic.placeToOp"
  placePointer := fun _ => .error (.unsupported "intrinsic.placePointer")
  derefPointer := fun _ _ => annealUnsupportedLeaf "intrinsic.derefPointer"
  immPointerToPlace := fun _ _ => annealUnsupportedLeaf "intrinsic.immPointerToPlace"
  dynamicSizeAlign := fun _ _ => annealUnsupportedLeaf "intrinsic.dynamicSizeAlign"
  scalarOps := annealScalarOpsHooks localDecls layouts
  floatOps := annealUnsupportedFloatOps
  applyFloatNondeterminism := fun _ _ => annealUnsupportedLeaf "intrinsic.applyFloatNondeterminism"
  chooseEqualFloatRight := fun _ _ _ => annealUnsupportedLeaf "intrinsic.chooseEqualFloatRight"
  fuseMulAdd := fun _ => annealUnsupportedLeaf "intrinsic.fuseMulAdd"
  floatFastError := fun _ _ _ => annealUnsupportedLeaf "intrinsic.floatFastError"
  checkAlign := fun _ ptr align => annealCheckPtrAlign ptr align
  memCopy := fun _ source dest size nonoverlapping => annealMemCopy source dest size nonoverlapping
  writeBytes := fun _ ptr byte size => annealWriteRepeatedBytes ptr byte size
  readBytesStripProvenance := fun _ _ _ => annealUnsupportedLeaf "intrinsic.readBytesStripProvenance"
  allocateStack := fun _ _ => annealUnsupportedLeaf "intrinsic.allocateStack"
  deallocateStack := fun _ _ => annealUnsupportedLeaf "intrinsic.deallocateStack"
  enforceValidity := fun _ _ => pure true
  enforceValidityRecursively := fun _ _ => pure true
  validatePlace := fun _ _ _ _ => annealUnsupportedLeaf "intrinsic.validatePlace"
  tryAllocId := fun _ _ => annealUnsupportedLeaf "intrinsic.tryAllocId"
  checkSignedAccess := fun _ _ _ => annealUnsupportedLeaf "intrinsic.checkSignedAccess"
  vtableSizeAlign := fun _ _ _ => annealUnsupportedLeaf "intrinsic.vtableSizeAlign"
  readDiscriminant := fun _ _ => annealUnsupportedLeaf "intrinsic.readDiscriminant"
  discriminantForVariant := fun _ _ _ => annealUnsupportedLeaf "intrinsic.discriminantForVariant"
  variantLayout := fun _ _ _ => annealUnsupportedLeaf "intrinsic.variantLayout"
  ensureMonomorphic := fun _ _ => pure ()
  typeNameConstant := fun _ _ _ => annealUnsupportedLeaf "intrinsic.typeNameConstant"
  needsDrop := fun _ _ => annealUnsupportedLeaf "intrinsic.needsDrop"
  variantCount := fun _ _ => annealUnsupportedLeaf "intrinsic.variantCount"
  callerLocationConstant := fun _ _ => annealUnsupportedLeaf "intrinsic.callerLocationConstant"
  chooseStaticKnown := fun _ => annealUnsupportedLeaf "intrinsic.chooseStaticKnown"
  catchUnwind := fun _ _ _ _ _ _ => annealUnsupportedLeaf "intrinsic.catchUnwind"
  returnToBlock := fun _ target => annealReturnToBlock target
  mathHooks := none

/-- Read a saved call destination or argument place as an operand (rustc's
`place_to_op`): a frame local is read like `Operand::Copy` of the local, and a
memory place is an indirect operand. -/
def annealStackPlaceToOp (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.Interpreter.RuntimeStackPlace AnnealProv) :
    Miri.Interpreter.CallM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) :=
  match place with
  | .frameLocal _ localId none _ _ =>
    annealEvalOperand localDecls layouts (.Copy ⟨localId, #[]⟩) none
  | .memory mp => pure ⟨.indirect mp.mplace, mp.layout⟩
  | .frameLocal _ _ (some _) _ _ => annealUnsupportedLeaf "call.placeToOp of a projected local"

/-- Dispatch an intrinsic call (rustc's `Machine::call_intrinsic`): evaluate it
with the vendored `Miri.Interpreter.Intrinsics.eval` under the intrinsic's name
and generic type arguments. When `Intrinsics.eval` does not handle the name it
returns `false`, and the call continues with the intrinsic's MIR fallback body
(`Instance { def: Item(def_id) }`), as rustc does for intrinsics with a
fallback body. -/
def annealCallIntrinsic (localDecls : List LocalDecl) (layouts : LayoutTable)
    (inst : Miri.Interpreter.CallInstance) (args : Array (Miri.Interpreter.OpTy AnnealProv))
    (dest : Miri.Interpreter.RuntimeStackPlace AnnealProv)
    (target : Option Miri.MIR.BasicBlockId) :
    Miri.Interpreter.CallM AnnealStepState (Option Miri.Interpreter.CallInstance) :=
  match AnnealIntrinsic.ofDefId? inst.defId with
  | none => annealUnsupportedLeaf "call of an intrinsic outside AnnealIntrinsic"
  | some k => do
    let types := inst.args.filterMap fun
      | .Type ty => some ty
      | _ => none
    let handled ← Miri.Interpreter.Intrinsics.eval (annealIntrinsicHooks localDecls layouts) ()
      k.name types args dest.toRuntimePlace target
    if handled then
      pure none
    else
      pure (some { kind := .Item inst.defId, args := inst.args })

/-- `CallHooks` instantiated for Anneal's single-threaded machine (`LM-4.2`),
for the vendored call pipeline `Miri.Interpreter.Call.evalCallTerminator`.

* `functionSignature`, `functionKind`, and `resolve` recognize the callee
  operand's function item type `annealFnItemTyId k T` (`translateCalleeOperand`)
  as `FnDef(k, [T])` and resolve it to `Instance { def: Intrinsic(k) }`.
  Intrinsics take no caller location, cannot unwind, and have the Rust ABI on
  both sides of the call (`FnABI`, `ArgABI`, and the extern ABI are `Unit`).
* `callIntrinsic` is `annealCallIntrinsic`. `findMirOrEvalFn`, the only way to
  reach an MIR body, fails closed: Anneal's correspondence relates a single
  frame and provides no callee bodies, including the MIR fallback bodies of
  intrinsics that `Intrinsics.eval` leaves unhandled.
* Every frame-construction and unwinding leaf fails closed with
  `StepError.unsupported`; no intrinsic call reaches them. -/
def annealCallHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.CallHooks AnnealProv AnnealStepState Unit Unit Unit Unit Unit Unit where
  debugAssertions := false
  getFrame := (annealPlaceHooks localDecls layouts).getFrame
  setFrame := (annealPlaceHooks localDecls layouts).setFrame
  frameIndex := (annealPlaceHooks localDecls layouts).frameIndex
  evalOperand := fun _ op => annealEvalOperand localDecls layouts op none
  evalOperandAt := fun _ _ op => annealEvalOperand localDecls layouts op none
  evalPlace := fun _ place _ => do
    let runtimePlace ← annealEvalPlace localDecls layouts place
    pure runtimePlace.stackView
  placeToOp := fun _ place => annealStackPlaceToOp localDecls layouts place
  forceAllocation := fun _ _ => annealUnsupportedLeaf "call.forceAllocation"
  functionSignature := fun _ layout =>
    match annealDecodeFnItemTyId layout.ty with
    | some (k, _) => pure (k.arity, ())
    | none => annealUnsupportedLeaf "call of a function other than an AnnealIntrinsic"
  functionKind := fun tyId =>
    match annealDecodeFnItemTyId tyId with
    | some (k, argTy) => pure (.FnDef k.defId #[.Type argTy])
    | none => annealUnsupportedLeaf "call of a function other than an AnnealIntrinsic"
  readPointer := fun _ _ => annealUnsupportedLeaf "call.readPointer"
  getPtrFn := fun _ _ => annealUnsupportedLeaf "call.getPtrFn"
  resolve := fun _ defId args =>
    match AnnealIntrinsic.ofDefId? defId with
    | some _ => pure { kind := .Intrinsic defId, args := args }
    | none => annealUnsupportedLeaf "call.resolve of a non-intrinsic item"
  fnAbiOfFnPtr := fun _ _ _ => annealUnsupportedLeaf "call.fnAbiOfFnPtr"
  fnAbiOfInstance := fun _ _ _ => pure ()
  requiresCallerLocation := fun _ => pure false
  callerLocation := annealUnsupportedLeaf "call.callerLocation"
  abiCanUnwind := fun _ => false
  abiVariadic := fun _ => false
  abiFixedCount := fun _ => 0
  abiArgs := fun _ => #[]
  abiReturn := fun _ => ()
  sameConvention := fun _ _ => true
  isRustCall := fun _ => false
  rustAbi := ()
  argLayout := fun _ => translateTy { kind := .tuple .nil, layoutIdx := 0 }
  argIsIgnore := fun _ => false
  isOneZst := fun _ => false
  checkArgumentCompat := fun _ _ _ => pure true
  checkTargetFeatures := fun _ _ => pure ()
  tupleFields := fun _ => annealUnsupportedLeaf "call.tupleFields"
  projectFnArg := fun _ _ _ => annealUnsupportedLeaf "call.projectFnArg"
  localLayout := fun _ _ => annealUnsupportedLeaf "call.localLayout"
  localSpan := fun _ _ => annealUnsupportedLeaf "call.localSpan"
  storageLiveDyn := fun _ _ _ => annealUnsupportedLeaf "call.storageLiveDyn"
  copyAllowTransmute := fun _ _ _ => annealUnsupportedLeaf "call.copyAllowTransmute"
  protectArgument := fun _ _ => annealUnsupportedLeaf "call.protectArgument"
  withRetagMode := fun _ _ action => action
  nonCapturingClosure := fun _ _ _ => pure false
  allocateStack := fun _ _ => annealUnsupportedLeaf "call.allocateStack"
  copyToMemory := fun _ _ _ => annealUnsupportedLeaf "call.copyToMemory"
  vaListPtr := fun _ _ => annealUnsupportedLeaf "call.vaListPtr"
  writeZeroBytes := fun _ _ _ => annealUnsupportedLeaf "call.writeZeroBytes"
  vaListKeyField := fun _ _ => annealUnsupportedLeaf "call.vaListKeyField"
  writePointerToMemory := fun _ _ _ => annealUnsupportedLeaf "call.writePointerToMemory"
  pushRaw := fun _ _ _ _ _ => annealUnsupportedLeaf "call.pushRaw"
  pushDone := fun _ => annealUnsupportedLeaf "call.pushDone"
  popRaw := fun _ => annealUnsupportedLeaf "call.popRaw"
  cleanup := fun _ _ _ => annealUnsupportedLeaf "call.cleanup"
  afterFrameInit := fun _ => annealUnsupportedLeaf "call.afterFrameInit"
  callExtra := fun _ _ _ _ _ _ _ => annealUnsupportedLeaf "call.callExtra"
  callIntrinsic := fun _ inst args dest target _ =>
    annealCallIntrinsic localDecls layouts inst args dest target
  callLlvmIntrinsic := fun _ _ _ _ _ => annealUnsupportedLeaf "call.callLlvmIntrinsic"
  findMirOrEvalFn := fun _ _ _ _ _ _ _ =>
    annealUnsupportedLeaf "call.findMirOrEvalFn (MIR bodies, including intrinsic fallback bodies)"
  resolveVirtual := fun _ _ _ _ _ _ => annealUnsupportedLeaf "call.resolveVirtual"
  isDynamic := fun _ => annealUnsupportedLeaf "call.isDynamic"
  unpackDynForDrop := fun _ _ => annealUnsupportedLeaf "call.unpackDynForDrop"
  resolveDropGlue := fun _ _ => annealUnsupportedLeaf "call.resolveDropGlue"
  mplaceToMutRef := fun _ _ => annealUnsupportedLeaf "call.mplaceToMutRef"
  fakeUnitReturn := fun _ => annealUnsupportedLeaf "call.fakeUnitReturn"

/-- Dispatch budget of `Call.evalCallTerminator` for Anneal's machine: one step
for the intrinsic itself and one for a MIR fallback, which `findMirOrEvalFn`
then rejects. -/
def annealCallBudget : Nat := 2

/-- `ControlHooks` instantiated for Anneal's single-threaded machine. -/
def annealControlHooks :
    Miri.Interpreter.ControlHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv) where
  bodySpan := fun _ => .ok defaultSpanRef
  returnOperand := fun _ state =>
    match state.stack.currentFrame? with
    | none => (state, .error (.stack .emptyStack))
    | some frame =>
        match frame.getLocal 0 with
        | .ok (.mk (.live (.immediate (.scalar s))) _) => (state, .ok (.immediate (.scalar s)))
        | .ok (.mk (.live (.immediate (.scalarPair s1 s2))) _) =>
            (state, .ok (.immediate (.scalarPair s1 s2)))
        | .ok (.mk (.live (.indirect mp)) _) => (state, .ok (.indirect mp))
        | .ok (.mk (.live (.immediate .uninit)) _) | .ok (.mk .dead _) =>
            (state, .error (.undefinedBehavior "return with uninitialized or dead _0"))
        | .error e => (state, .error (.stack e))
  popFrame := fun _ state =>
    match state.stack.popFrame with
    | .ok (stack', popped) => ({ state with stack := stack' }, .ok popped)
    | .error e => (state, .error (.stack e))
  copyReturn := fun _ retOp returnPlace state =>
    match returnPlace with
    | .frameLocal callerFrameIdx destLocal none _ _ =>
        match state.stack.currentFrame? with
        | none =>
            -- Root frame return (empty caller stack): return value has been extracted from `_0`.
            (state, .ok ())
        | some callerFrame =>
            if callerFrameIdx != state.stack.frames.size - 1 then
              (state, .error (.invalidProgram "caller frame index mismatch"))
            else
              match callerFrame.getLocal destLocal with
              | .error e => (state, .error (.stack e))
              | .ok callerDestState =>
                  match callerDestState.value with
                  | .dead => (state, .error (.undefinedBehavior "caller destination local is dead"))
                  | .live _ =>
                      match callerFrame.replaceLocalValue destLocal (.live retOp) with
                      | .error e => (state, .error (.stack e))
                      | .ok updatedCaller =>
                          let idx := state.stack.frames.size - 1
                          if h : idx < state.stack.frames.size then
                            ({ state with stack := { frames := state.stack.frames.set idx updatedCaller h } }, .ok ())
                          else
                            (state, .error (.stack .emptyStack))
    | _ => (state, .error (.unsupported "projected or memory returnPlace in scalar fragment"))
  cleanupFrame := fun _ _ _ state => (state, .ok .normal)
  unwindTerminate := fun _ _ state => (state, .error (.unsupported "unwindTerminate"))

/-- `TerminatorHooks` instantiated for Anneal's single-threaded machine. -/
def annealTerminatorHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.TerminatorHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv)
      (Miri.Interpreter.RvalueImmTy AnnealProv) where
  toControlHooks := annealControlHooks
  evalDiscriminant := fun _ op state =>
    Miri.Interpreter.runRvalue
      (do
        let opTy ← annealEvalOperand localDecls layouts op none
        annealReadImmediate opTy)
      state
  compareSwitchCase := fun choice value caseVal state =>
    Miri.Interpreter.runRvalue
      (do
        let caseScalar ←
          match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 caseVal) value.layout.layout.size with
          | .ok sc => pure sc
          | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
        let result ←
          Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks localDecls layouts)
            choice
            .Eq
            value
            ⟨.scalar caseScalar, value.layout⟩
        let resScalar ←
          match result.imm.toScalar with
          | .ok sc => pure sc
          | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
        match resScalar.toBool with
        | .ok b => return b
        | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err))
      state
  call := fun choice term state =>
    Miri.Interpreter.Call.run
      (Miri.Interpreter.Call.evalCallTerminator (annealCallHooks localDecls layouts) choice
        annealCallBudget term)
      state
  tailCall := fun _ _ state => (state, .error (.unsupported "tailCall terminator"))
  drop := fun _ _ _ _ state => (state, .error (.unsupported "drop terminator"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ op state =>
    Miri.Interpreter.runRvalue
      (do
        let opTy ← annealEvalOperand localDecls layouts op none
        let imm ← annealReadImmediate opTy
        let sc ←
          match imm.imm.toScalar with
          | .ok sc => pure sc
          | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
        match sc.toBool with
        | .ok b => return b
        | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err))
      state
  -- A failed `Assert` panics and unwinds in both rustc and Anneal (`applyUnwindAction`);
  -- it is never undefined behavior. Unwinding is outside the scalar fragment.
  assertPanic := fun _ _ _ state => (state, .error (.undefinedBehavior "assert panic"))

/-- Compiler and machine leaves of `lean-miri`'s source `storage_live_dyn` and
`storage_dead` (`Miri.Interpreter.Frame.storageLive` / `Frame.storageDead`) for
Anneal's single-threaded machine.

* `veryTriviallySized` answers `true`: `Runtime(PostCleanup)` MIR has no
  unsized locals, so `storage_live_dyn` never needs a layout or metadata.
* `afterLocalWrite` has nothing to do: data-race clocks exist only for
  multi-threaded machines.
* `allocateDyn` reports a `StackError` failure: `Runtime(PostCleanup)` MIR has
  no unsized locals.
* `deallocateStack` frees the allocation of a memory-backed local, which
  `forceAllocation` and `annealEnsureAllocated` create. Like rustc's
  `deallocate_ptr`, it requires the
  pointer's provenance to name a live allocation, and then removes that
  allocation from `memory.live`. rustc's remaining checks (allocation kind,
  protectors, and the offset of the pointer) cannot fail for these fresh stack
  allocations, so they are not modeled. Nor does the hook record the freed
  allocation in `memory.dead` or release its base address: allocation IDs are
  monotonically fresh (`nextAllocId + 1`), so absence from `memory.live`
  already suffices to detect dangling pointers to freed stack allocations. -/
def annealLocalStorageHooks (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.LocalStorageHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMemory where
  veryTriviallySized := fun _ => .ok true
  layout := fun st _ localId =>
    match lookupLocalDeclLayout localDecls layouts localId with
    | some l => ⟨st, .ok l⟩
    | none => ⟨st, .error (.missingLocalType localId)⟩
  isSized := fun l => l.layout.isSized
  afterLocalWrite := fun st _ _ => ⟨st, .ok ()⟩
  allocateDyn := fun st _ _ =>
    ⟨st, .error (.allocationFailure "unsized locals are outside the scalar fragment")⟩
  deallocateStack := fun st ptr =>
    match ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
    | some id =>
        if st.live.any (fun entry => entry.1 == id) then
          ⟨{ st with live := st.live.filter (fun entry => entry.1 != id) }, .ok ()⟩
        else
          ⟨st, .error (.deallocationFailure "stack allocation is not live")⟩
    | none => ⟨st, .error (.deallocationFailure "stack pointer has no allocation provenance")⟩

/-- Run a current-frame storage operation (`Frame.storageLive` or
`Frame.storageDead`), writing back the resulting frame and memory even when the
operation fails, as `lean-miri`'s machine-level `MachineHooks.storageLiveDyn` and
`MachineHooks.storageDead` do. -/
def annealRunFrameStorage
    (op : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit →
      AnnealMemory →
      Miri.Interpreter.LocalStorageResult AnnealProv Miri.Interpreter.LocalLayout Unit
        AnnealMemory)
    (state : AnnealStepState) : Miri.Interpreter.StepResult AnnealStepState Unit :=
  match state.stack.currentFrame? with
  | none => (state, .error (.stack .emptyStack))
  | some frame =>
      let result := op frame state.machine.memory
      let idx := state.stack.frames.size - 1
      if h : idx < state.stack.frames.size then
        let state' : AnnealStepState :=
          { stack := { frames := state.stack.frames.set idx result.frame h }
            machine := { state.machine with memory := result.state } }
        match result.outcome with
        | .ok () => (state', .ok ())
        | .error e => (state', .error (.stack e))
      else
        (state, .error (.stack .emptyStack))

/-- `StepHooks` instantiated for Anneal's single-threaded machine. -/
def annealStepHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  assign := fun choice place rvalue state =>
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks localDecls layouts) choice rvalue place)
      state
  evalPlace := fun _ place _ state =>
    Miri.Interpreter.runRvalue (annealEvalPlace localDecls layouts place) state
  writeDiscriminant := fun _ _ _ state =>
    (state, .error (.unsupported "writeDiscriminant"))
  storageLive := fun _ localId state =>
    annealRunFrameStorage
      (fun frame mem => frame.storageLive mem (annealLocalStorageHooks localDecls layouts) localId)
      state
  storageDead := fun _ localId state =>
    annealRunFrameStorage
      (fun frame mem => frame.storageDead mem (annealLocalStorageHooks localDecls layouts) localId)
      state
  intrinsic := fun choice intrinsic state =>
    Miri.Interpreter.runRvalue
      (Miri.Interpreter.Intrinsics.evalNondiverging (annealIntrinsicHooks localDecls layouts)
        choice intrinsic)
      state
  incrementConstEvalCounter := fun _ state => (state, .ok ())
  returnFromCurrentFrame := fun choice unwinding state =>
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame annealControlHooks choice unwinding state
  beforeTerminator := fun _ state => (state, .ok ())
  terminator := fun choice term state =>
    Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooks localDecls layouts) choice term state


/-! ## `LM-2.2` Aggregate / Struct / Tuple / Enum / Union Hook Suite -/

/-- Read an `Immediate` from a memory-backed `MemPlace AnnealProv` at `layout`,
diagnosing `StepError.undefinedBehavior` when the field's byte range in the
underlying `Allocation` is uninitialized (`InvalidUninitBytes`), extracting
`(address, length)` metadata exclusively for `arraySliceMetaTyId` (`Rvalue.len`),
and failing closed (`StepError.unsupported`) on whole-array immediate reads. -/
def annealReadIndirectImmediate (mp : Miri.Interpreter.MemPlace AnnealProv)
    (layout : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) := do
  let state ← get
  let memory := state.machine.memory
  let some id := mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
    | throw (.unsupported "memory read through a pointer without an allocation")
  let some base := state.machine.lookupBaseAddr id
    | throw (.unsupported "memory read from an allocation without a base address")
  let offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - base)
  match memory.live.find? (fun (k, _) => k == id) with
  | none => throw (.undefinedBehavior "dangling allocation in memory read")
  | some (_, ⟨_, alloc⟩) =>
      match layout.layout.fields with
      | .Array _ count =>
          if layout.ty == arraySliceMetaTyId then
            match alloc.initializationMask.isRangeInitialized (Miri.Memory.allocRange offset layout.layout.size) with
            | Except.ok (Except.ok ()) =>
                let some countSc := (Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 count.toNat) (Miri.ABI.Size.ofBytes 8)).toOption.join
                  | throw (.invalidProgram "array length overflow")
                let some prov := mp.ptr.provenance
                  | throw (.unsupported "indirect array operand without provenance")
                let ptrSc := Miri.Memory.Scalar.fromPointer annealTargetDataLayout ⟨mp.ptr.offset, prov⟩
                return ⟨.scalarPair ptrSc (.fromScalarInt countSc), translateTy { kind := .ref .not (.slice .bool), layoutIdx := 0 }⟩
            | _ => throw (.undefinedBehavior "len of uninitialized array")
          else
            throw (.unsupported "whole-array immediate read not supported")
      | _ =>
          if layout.layout.size == Miri.ABI.Size.ZERO then
            return ⟨.uninit, layout⟩
          else
            match layout.layout.backendRepr with
            | .Scalar _ =>
                match alloc.readScalar annealTargetDataLayout
                    (Miri.Memory.allocRange offset layout.layout.size) false with
                | .ok s => return ⟨.scalar s, layout⟩
                | .error (.invalidUninitBytes _) =>
                    throw (.undefinedBehavior "read of uninitialized memory field")
                | .error (.outOfBounds ..) =>
                    throw (.undefinedBehavior "out-of-bounds memory field read")
                | .error _ => throw (.unsupported "readScalar failed")
            | .ScalarPair (a := a) (b := b) (bOffset := bOff) =>
                let szA := (a.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO
                let szB := (b.size annealRuntimeDataLayout).toOption.getD Miri.ABI.Size.ZERO
                let offB := Miri.ABI.Size.ofBytes (offset.bytes + bOff.bytes)
                let s0 ←
                  match alloc.readScalar annealTargetDataLayout
                      (Miri.Memory.allocRange offset szA) false with
                  | .ok s => pure s
                  | .error (.invalidUninitBytes _) =>
                      throw (.undefinedBehavior "read of uninitialized scalarPair field 0")
                  | .error (.outOfBounds ..) =>
                      throw (.undefinedBehavior "out-of-bounds scalarPair field 0 read")
                  | .error _ => throw (.unsupported "readScalar field 0 failed")
                let s1 ←
                  match alloc.readScalar annealTargetDataLayout
                      (Miri.Memory.allocRange offB szB) false with
                  | .ok s => pure s
                  | .error (.invalidUninitBytes _) =>
                      throw (.undefinedBehavior "read of uninitialized scalarPair field 1")
                  | .error (.outOfBounds ..) =>
                      throw (.undefinedBehavior "out-of-bounds scalarPair field 1 read")
                  | .error _ => throw (.unsupported "readScalar field 1 failed")
                return ⟨.scalarPair s0 s1, layout⟩
            | _ => throw (.unsupported "indirect non-scalar readImmediate")

/-- Read an `Immediate` from an `OpTy AnnealProv` in `AnnealStepState`, raising
`StepError.undefinedBehavior` on `.uninit` just as `MirSemantics.evalOperand` raises
`.fail .ub`, and reading scalar/scalarPair fields from memory on `.indirect`. -/
def annealReadImmediateLM2_2 (op : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) := do
  match op.op with
  | .immediate (.scalar s) => return ⟨.scalar s, op.layout⟩
  | .immediate (.scalarPair s1 s2) => return ⟨.scalarPair s1 s2, op.layout⟩
  | .immediate .uninit => throw (.undefinedBehavior "read of uninitialized local")
  | .indirect mp => annealReadIndirectImmediate mp op.layout

/-- Write an `Immediate AnnealProv` into a memory-backed `MemPlace AnnealProv` at
relative byte offset `relOffset` and field layout `fieldLayout`. -/
def annealWriteIndirectImmediate (val : Miri.Interpreter.Immediate AnnealProv)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (relOffset : Miri.ABI.Size)
    (fieldLayout : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let state ← get
  let memory := state.machine.memory
  let some id := mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
    | throw (.unsupported "memory write through a pointer without an allocation")
  let some base := state.machine.lookupBaseAddr id
    | throw (.unsupported "memory write to an allocation without a base address")
  let offset := Miri.ABI.Size.ofBytes ((mp.ptr.offset.bytes - base) + relOffset.bytes)
  match memory.live.findIdx? (fun (k, _) => k == id) with
  | some idx =>
      match memory.live[idx]? with
      | some (k, ⟨kind, alloc⟩) =>
          let alloc' ←
            match val with
            | .uninit =>
                if fieldLayout.layout.size == Miri.ABI.Size.ZERO then
                  pure alloc
                else
                  match Miri.Memory.Allocation.writeUninit
                      (Miri.Memory.allocRange offset fieldLayout.layout.size)
                      (Miri.ABI.Size.ofBytes 8) alloc with
                  | EStateM.Result.ok _ a => pure a
                  | EStateM.Result.error _ _ => throw (.unsupported "writeUninit failed")
            | .scalar s =>
                match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                    (Miri.Memory.allocRange offset s.size) s alloc with
                | EStateM.Result.ok _ a => pure a
                | EStateM.Result.error _ _ => throw (.unsupported "writeScalar failed")
            | .scalarPair s0 s1 =>
                match fieldLayout.layout.backendRepr with
                | .ScalarPair (a := _) (b := _) (bOffset := bOff) =>
                    let alloc₁ ←
                      match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                          (Miri.Memory.allocRange offset s0.size) s0 alloc with
                      | EStateM.Result.ok _ a => pure a
                      | EStateM.Result.error _ _ => throw (.unsupported "writeScalar s0 failed")
                    let offB := Miri.ABI.Size.ofBytes (offset.bytes + bOff.bytes)
                    match Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                        (Miri.Memory.allocRange offB s1.size) s1 alloc₁ with
                    | EStateM.Result.ok _ a => pure a
                    | EStateM.Result.error _ _ => throw (.unsupported "writeScalar s1 failed")
                | _ => throw (.unsupported "scalarPair in writeMemoryNoValidate")
          set { state with machine := { state.machine with
            memory := { memory with live := memory.live.set! idx (k, ⟨kind, alloc'⟩) } } }
      | none => throw (.unsupported "allocation not found")
  | none => throw (.unsupported "allocation not found")

/-- Extended `PlaceHooks` for projected local writes and aggregate construction
(`Miri.Interpreter.asMplaceOrMutableLocal` / `Miri.Interpreter.writePlaceImmediateNoValidate`),
supporting thin-pointer `memoryOffset` and `.scalarPair` writes in
`writeMemoryNoValidate` via `annealWriteIndirectImmediate` while keeping
`annealPlaceHooks` unchanged for `LM-1.4`. -/
def annealMutablePlaceHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.PlaceHooks AnnealProv AnnealStepState Unit Unit :=
  { annealPlaceHooks localDecls layouts with
    writeMemoryNoValidate := fun _ value mplace =>
      annealWriteIndirectImmediate value mplace.mplace Miri.ABI.Size.ZERO mplace.layout
    memoryOffset := fun _ place offset _ metadata => do
      if metadata.hasMeta then
        throw (.invalidProgram "metadata on thin memory place offset")
      match place.ptr.offset.add offset with
      | .ok newOffset =>
          return { place with ptr := { place.ptr with offset := newOffset }, metadata := .none }
      | .error _ =>
          throw (.invalidProgram "place memory offset overflow") }

/-- Write an `Immediate AnnealProv` into a projected local place
`.local frameIdx localId (some relOffset) _` using upstream
`Miri.Interpreter.writePlaceImmediateNoValidate` (`asMplaceOrMutableLocal` →
`forceAllocation`), materializing `.Scalar`, `.ScalarPair`, and `.Memory`
immediate locals into stack `Allocation`s before writing the projected field and
mapping dead-local `StackError.localExpectedLive` to `StepError.undefinedBehavior`.

Upstream `forceAllocation` obtains the local's layout from
`Miri.Interpreter.placeLayoutOfLocal`, which returns the layout cached in the
frame and calls `PlaceHooks.resolveLayout` only when nothing is cached.
`annealWriteImmediateLM2_2` calls this function with the default empty `localDecls`
and `layouts`, so the write relies on the cache. That holds because
`annealEvalPlace` (`annealResolveAndCacheLocalLayout`) caches the root local's
layout before any projected write. For an uncached local, `resolveLayout` would
fail with `StackError.missingLocalType`. -/
def annealWriteProjectedLocalImmediate (val : Miri.Interpreter.Immediate AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := fun st =>
  match Miri.Interpreter.writePlaceImmediateNoValidate
      (annealMutablePlaceHooks localDecls layouts) () val dest st with
  | .ok () st' => .ok () st'
  | .error (.stack (.localExpectedLive _)) st' =>
      .error (.undefinedBehavior "write to dead local") st'
  | .error err st' => .error err st'

/-- Write an `Immediate AnnealProv` into a `RuntimePlace AnnealProv` in the top frame.

* Out-of-bounds `localId`s propagate `StepError.stack (.invalidLocal ...)`.
* Writing to a `.dead` local (`StackError.localExpectedLive` from
  `Frame.getLocalOperand`) raises `StepError.undefinedBehavior` (matching rustc's
  `err_ub!(DeadLocal)` and `MirSemantics.evalStmt` on `.assign`).
* Unprojected writes to an `.indirect` (memory-backed) local write through its
  `MemPlace` with `annealWriteIndirectImmediate`, exactly as upstream
  `Miri.Interpreter.writePlaceImmediateNoValidate` does: there
  `asMplaceOrMutableLocal` returns `.memory` for an `.indirect` local and the
  value goes to `writeMemoryNoValidate` (`annealMutablePlaceHooks`). Since
  aggregate construction and projected field writes move `.Scalar`/`.ScalarPair`
  struct locals into memory (`forceAllocation`), a later whole-value assignment
  `_1 = copy _2` must take this path.
* Projected field writes delegate to upstream
  `Miri.Interpreter.writePlaceImmediateNoValidate` via
  `annealWriteProjectedLocalImmediate`, and `.memory` places delegate to
  `annealWriteIndirectImmediate`. -/
def annealWriteImmediateLM2_2 (val : Miri.Interpreter.Immediate AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match dest.ref with
  | .local frameIdx localId none _ =>
      if frameIdx != st.stack.frames.size - 1 then
        throw (.invalidProgram "place refers to another frame")
      match frame.getLocalOperand localId with
      | .error (.localExpectedLive _) =>
          throw (.undefinedBehavior "write to dead local")
      | .error e =>
          throw (.stack e)
      | .ok (.indirect mp) =>
          annealWriteIndirectImmediate val mp Miri.ABI.Size.ZERO dest.layout
      | .ok (.immediate _) =>
          let updatedFrame ←
            match frame.replaceLocalValue localId (.live (.immediate val)) with
            | .ok f => pure f
            | .error e => throw (.stack e)
          let idx := st.stack.frames.size - 1
          if h : idx < st.stack.frames.size then
            set { st with stack := { frames := st.stack.frames.set idx updatedFrame h } }
          else
            throw (.stack .emptyStack)
  | .local _ _ (some _) _ =>
      annealWriteProjectedLocalImmediate val dest
  | .memory mp =>
      annealWriteIndirectImmediate val mp Miri.ABI.Size.ZERO dest.layout

/-- `CastHooks` instantiated for Anneal's single-threaded machine, supporting
integer-like `CastKind.IntToInt` via `Miri.Interpreter.Cast.cast` and failing
closed (`StepError.unsupported`) on float, pointer-provenance, unsizing, and
transmute leaves. -/
def annealCastHooksLM2_2 (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.CastHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  typeInfo := fun _ tyId =>
    match castTypeInfoOfEncodedTyId tyId with
    | .ok info => pure info
    | .error err => throw err
  layoutOf := fun _ tyId => pure (layoutOfEncodedTyId tyId layouts)
  destLayout := fun p => p.layout
  readImmediate := fun _ op => annealReadImmediateLM2_2 op
  writeImmediate := fun _ val dest => annealWriteImmediateLM2_2 val dest
  writePointer := fun _ _ _ => throw (.unsupported "writePointer in cast")
  enforceValidity := fun _ _ => pure true
  enforceValidityRecursively := fun _ _ => pure true
  validatePlace := fun _ _ _ _ => throw (.unsupported "validatePlace in cast")
  derefPointer := fun _ _ => throw (.unsupported "derefPointer in cast")
  checkFunctionPointer := fun _ _ => throw (.unsupported "checkFunctionPointer in cast")
  exposeProvenance := fun _ _ => throw (.unsupported "exposeProvenance in cast")
  pointerFromExposedAddress := fun _ _ => throw (.unsupported "pointerFromExposedAddress in cast")
  usizeLayout := fun _ => pure (translateTy { kind := .uint .usize, layoutIdx := 0 })
  floatOps := {
    integerKindOf := fun _ _ => throw (.unsupported "floatOps.integerKindOf")
    formatOf := fun _ _ => throw (.unsupported "floatOps.formatOf")
    boolLayout := fun _ => pure (translateTy { kind := .bool, layoutIdx := 0 })
    floatNondeterministic := false
    chooseNaN := fun _ _ => throw (.unsupported "floatOps.chooseNaN") }
  ensureMonomorphic := fun _ _ => pure ()
  requireNoBoundVars := fun _ _ => pure ()
  resolveFunction := fun _ _ _ => throw (.unsupported "resolveFunction in cast")
  resolveClosureFnOnce := fun _ _ _ => throw (.unsupported "resolveClosureFnOnce in cast")
  functionPointer := fun _ _ => throw (.unsupported "functionPointer in cast")
  builtinDeref := fun _ _ _ => throw (.unsupported "builtinDeref in cast")
  boxLayout := fun _ _ => throw (.unsupported "boxLayout in cast")
  validateImmediateABI := fun _ _ => .error (.unsupported "validateImmediateABI in cast")
  copyAllowTransmute := fun _ _ _ => throw (.unsupported "copyAllowTransmute in cast")
  copyNoValidate := fun _ _ _ _ => throw (.unsupported "copyNoValidate in cast")
  projectRead := fun _ _ _ => throw (.unsupported "projectRead in cast")
  projectWrite := fun _ _ _ => throw (.unsupported "projectWrite in cast")
  fieldLayout := fun _ _ _ => throw (.unsupported "fieldLayout in cast")
  lockstepTails := fun _ _ _ => throw (.unsupported "lockstepTails in cast")
  vtableType := fun _ _ _ => throw (.unsupported "vtableType in cast")
  vtablePointer := fun _ _ _ => throw (.unsupported "vtablePointer in cast")
  principal := fun _ _ => throw (.unsupported "principal in cast")
  vtableEntries := fun _ _ _ => throw (.unsupported "vtableEntries in cast")
  supertraitSlot := fun _ _ _ => throw (.unsupported "supertraitSlot in cast")
  eraseSelfTraitRef := fun _ _ => throw (.unsupported "eraseSelfTraitRef in cast")
  normalizePrincipal := fun _ _ => throw (.unsupported "normalizePrincipal in cast")

/-- Whether `copy_op` into `dest` takes rustc's memory-to-memory `mem_copy` path
for a non-zero-sized `AbiRepr.Memory (sized := true)` struct/tuple layout
(`FieldsShape.Arbitrary`). -/
def usesStructMemCopyDest (dest : Miri.Interpreter.RuntimePlace AnnealProv) : Bool :=
  match dest.layout.layout.backendRepr with
  | .Memory (sized := true) =>
      match dest.layout.layout.fields with
      | .Arbitrary _ _ => dest.layout.layout.size != Miri.ABI.Size.ZERO
      | _ => false
  | _ => false

/-- Map an `AllocError` of a whole-value struct copy to a `StepError`. -/
def annealStructMemCopyError : Miri.Memory.AllocError → Miri.Interpreter.StepError
  | .copyRangesOverlap => .undefinedBehavior "whole-value copy between overlapping ranges"
  | .outOfBounds _ _ => .undefinedBehavior "whole-value copy out of bounds"
  | .readOnlyAllocation => .undefinedBehavior "write to read-only allocation"
  | _ => .unsupported "whole-value copy failed"

/-- Whether a copy of `size` bytes from offset `srcOff` of `srcAlloc` to offset
`destOff` of `destAlloc` (in a different allocation) covers both allocations
entirely and targets a mutable destination allocation (`Mutability.Mut`). -/
def isWholeStructAllocationCopy
    (srcAlloc destAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (srcOff destOff size : Miri.ABI.Size) (sameAlloc : Bool) : Bool :=
  !sameAlloc && srcOff.bytes == 0 && destOff.bytes == 0 &&
    size == srcAlloc.byteSize && size == destAlloc.byteSize &&
    destAlloc.mutability == .Mut

/-- Build the mutable destination allocation produced by copying all bytes,
initialization bits, and pointer provenance of `srcAlloc` into a mutable
destination allocation carrying metadata `destExtra`. -/
def copyWholeStructAllocation
    (srcAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (destExtra : Option Miri.TreeBorrows.BorrowTree) :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (srcAlloc.withoutNativeBuffer.withMutability .Mut).setExtra destExtra

/-- rustc's `copy_op` memory path for a `.Memory (sized := true)` struct/tuple
(`usesStructMemCopyDest`): `dest.force_mplace` (`Miri.Interpreter.forceAllocation`)
followed by `mem_copy(src, dest, dest_size, nonoverlapping = true)`, copying the
raw bytes, initialization mask (preserving uninitialized padding bytes), and
provenance map from `src` to `dest`. -/
def annealStructMemCopyOp (localDecls : List LocalDecl) (layouts : LayoutTable)
    (src : Miri.Interpreter.OpTy AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState Unit := do
  match src.op with
  | .immediate .uninit =>
      throw (.undefinedBehavior "read of uninitialized local")
  | .immediate imm =>
      annealWriteImmediateLM2_2 imm dest
  | .indirect srcMp =>
      let forced ← fun st =>
        match Miri.Interpreter.forceAllocation (annealMutablePlaceHooks localDecls layouts) () dest st with
        | .ok res st' => .ok res st'
        | .error (.stack (.localExpectedLive _)) st' =>
            .error (.undefinedBehavior "write to dead local") st'
        | .error err st' => .error err st'
      let destMp := forced.mplace
      let st ← get
      let some srcId := srcMp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
        | throw (.unsupported "copy source without an allocation")
      let some srcBase := st.machine.lookupBaseAddr srcId
        | throw (.unsupported "copy source without a base address")
      let some (_, srcLocal) := st.machine.memory.live.find? (fun (k, _) => k == srcId)
        | throw (.undefinedBehavior "dangling allocation in memory copy")
      let some destId := destMp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId
        | throw (.unsupported "copy destination without an allocation")
      let some destBase := st.machine.lookupBaseAddr destId
        | throw (.unsupported "copy destination without a base address")
      let srcOff := Miri.ABI.Size.ofBytes (srcMp.ptr.offset.bytes - srcBase)
      let destOff := Miri.ABI.Size.ofBytes (destMp.ptr.offset.bytes - destBase)
      match st.machine.memory.live.findIdx? (fun (k, _) => k == destId) with
      | none => throw (.undefinedBehavior "dangling allocation in memory copy")
      | some destIdx =>
          match st.machine.memory.live[destIdx]? with
          | none => throw (.undefinedBehavior "dangling allocation in memory copy")
          | some (k, ⟨kind, destAlloc⟩) =>
              let size := dest.layout.layout.size
              if isWholeStructAllocationCopy srcLocal.allocation destAlloc srcOff destOff size
                  (srcId == destId) then
                let destAlloc' := copyWholeStructAllocation srcLocal.allocation destAlloc.extra
                set { st with machine := { st.machine with
                  memory := { st.machine.memory with
                    live := st.machine.memory.live.set! destIdx (k, ⟨kind, destAlloc'⟩) } } }
              else
                match Miri.Memory.Allocation.copy srcLocal.allocation
                    (Miri.Memory.allocRange srcOff size) destOff
                    (Miri.ABI.Size.ofBytes 8) (srcId == destId) true destAlloc with
                | EStateM.Result.ok () destAlloc' =>
                    set { st with machine := { st.machine with
                      memory := { st.machine.memory with
                        live := st.machine.memory.live.set! destIdx (k, ⟨kind, destAlloc'⟩) } } }
                | EStateM.Result.error err _ => throw (annealStructMemCopyError err)

/-- `AggregateHooks` instantiated for Anneal's single-threaded machine, wiring
upstream `Miri.Interpreter.writeAggregate` and `Miri.Interpreter.writeRepeat`
across homogeneous arrays (`annealEnsureAllocated`, `writeScalarRepeatedly`) and
`AbiRepr.Scalar`, `AbiRepr.ScalarPair`, and `AbiRepr.Memory` structs/tuples
(`annealProjectFieldPlace`, `annealStructMemCopyOp`, `annealWriteImmediateLM2_2`). -/
def annealAggregateHooksLM2_2 (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  placeLayout := fun p => p.layout
  evalOperand := fun _ op known => annealEvalOperand localDecls layouts op known
  evalOperandAt := fun _ _ op known => do
    let opTy ← annealEvalOperand localDecls layouts op known
    match opTy.op with
    | .immediate _ =>
        let imm ← annealReadImmediateLM2_2 opTy
        return ⟨.immediate imm.imm, imm.layout⟩
    | .indirect _ =>
        return opTy
  readPointer := fun _ op => do
    let imm ← annealReadImmediateLM2_2 op
    match imm.imm.toScalar with
    | .ok sc =>
        match sc.toPointer annealTargetDataLayout with
        | .ok p => return p
        | .error _ => throw (.invalidProgram "expected pointer scalar")
    | .error _ => throw (.invalidProgram "expected scalar immediate")
  readScalar := fun _ op => do
    let imm ← annealReadImmediateLM2_2 op
    match imm.imm.toScalar with
    | .ok sc => return sc
    | .error _ => throw (.invalidProgram "expected scalar immediate")
  projectDowncast := fun _ dest variant =>
    if variant == 0 then pure dest
    else throw (.unsupported "multi-variant aggregate downcast not wired in LM-2.2")
  projectField := fun _ dest fieldIdx =>
    match dest.layout.layout.fields with
    | .Array stride _ => do
        let mp ← annealEnsureAllocated dest
        let elemLay := arrayElemLayoutOf layouts dest.layout stride
        let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (fieldIdx * stride.bytes.toNat))
        return ⟨.memory { mp with ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff.bytes) } }, elemLay⟩
    | _ =>
        match annealProjectFieldPlace layouts none dest fieldIdx with
        | .ok p => pure p
        | .error err => throw err
  copyOp := fun _ src dest =>
    if usesStructMemCopyDest ⟨dest.ref, src.layout⟩ && usesStructMemCopyDest dest then
      annealStructMemCopyOp localDecls layouts src dest
    else do
      let imm ← annealReadImmediateLM2_2 src
      annealWriteImmediateLM2_2 imm.imm dest
  copyOpNoValidate := fun _ src dest _ =>
    if usesStructMemCopyDest ⟨dest.ref, src.layout⟩ && usesStructMemCopyDest dest then
      annealStructMemCopyOp localDecls layouts src dest
    else do
      let imm ← annealReadImmediateLM2_2 src
      annealWriteImmediateLM2_2 imm.imm dest
  writeDiscriminant := fun _ variant dest =>
    match dest.layout.layout.fields with
    | .Array _ _ | .Union _ => do
        let _ ← annealEnsureAllocated dest
        pure ()
    | _ =>
        if variant == 0 then pure ()
        else throw (.unsupported "multi-variant aggregate writeDiscriminant not wired in LM-2.2")
  enforceValidity := fun _ _ => pure true
  validate := fun _ _ => pure ()
  forceAllocation := fun _ dest => do
    let mp ← annealEnsureAllocated dest
    return ⟨.memory mp, dest.layout⟩
  length := fun _ dest =>
    match dest.layout.layout.fields with
    | .Array _ count => pure count
    | _ => throw (.invalidProgram "repeat destination is not an array")
  getPlaceAllocMut := fun _ _ => pure ()
  projectIndex := fun _ dest idx => do
    match dest.ref, dest.layout.layout.fields with
    | .memory mp, .Array stride _ =>
        let elemLay := arrayElemLayoutOf layouts dest.layout stride
        let elemOff := Miri.ABI.Size.ofBytes (UInt64.ofNat (idx.toNat * stride.bytes.toNat))
        return ⟨.memory { mp with ptr := { mp.ptr with offset := Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes + elemOff.bytes) } }, elemLay⟩
    | _, _ => throw (.unsupported "projectIndex in aggregate")
  placePointer := fun dest =>
    match dest.ref with
    | .memory mp => .ok mp.ptr
    | _ => .error (.invalidProgram "placePointer requires mplace")
  wrappingOffset := Miri.Interpreter.aggregateWrappingOffset annealPointerArithmetic
  memCopyRepeatedly := fun _ firstPtr restPtr elemSize count _ => do
    if count == 0 then
      pure ()
    else
      let st ← get
      let some id := firstPtr.provenance.bind Miri.Memory.Provenance.getAllocId
        | throw (.unsupported "repeat pointer without allocation id")
      let some base := st.machine.lookupBaseAddr id
        | throw (.unsupported "repeat pointer without base address")
      let firstOff := Miri.ABI.Size.ofBytes (firstPtr.offset.bytes - base)
      let restOff := Miri.ABI.Size.ofBytes (restPtr.offset.bytes - base)
      match st.machine.memory.live.findIdx? (fun (k, _) => k == id) with
      | some allocIdx =>
          match st.machine.memory.live[allocIdx]? with
          | some (k, ⟨kind, alloc⟩) =>
              let sc ←
                match alloc.readScalar annealTargetDataLayout
                    (Miri.Memory.allocRange firstOff elemSize) false with
                | .ok s => pure s
                | .error _ => throw (.unsupported "repeat readScalar failed")
              let alloc' ←
                match writeScalarRepeatedly restOff elemSize count.toNat sc alloc with
                | .ok a => pure a
                | .error err => throw err
              set { st with machine := { st.machine with
                memory := { st.machine.memory with
                  live := st.machine.memory.live.set! allocIdx (k, ⟨kind, alloc'⟩) } } }
          | none => throw (.unsupported "repeat allocation not found")
      | none => throw (.unsupported "repeat allocation not found")

/-- `RvalueHooks` instantiated for Anneal's single-threaded machine. -/
def annealRvalueHooksLM2_2 (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.RvalueHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  placeLayout := fun p => p.layout
  evalPlace := fun _ p _ => annealEvalPlace localDecls layouts p
  evalOperand := fun _ op known => annealEvalOperand localDecls layouts op known
  evalPlaceToOp := fun _ p known => annealEvalOperand localDecls layouts (.Copy p) known
  readImmediate := fun _ op => annealReadImmediateLM2_2 op
  writeImmediate := fun _ val dest => annealWriteImmediateLM2_2 val dest
  writePointer := fun _ _ _ => throw (.unsupported "writePointer")
  threadLocalPointer := fun _ _ => throw (.unsupported "threadLocalPointer")
  withRetagMode := fun _ _ action => action
  copyOp := fun _ src dest =>
    if usesStructMemCopyDest dest then
      annealStructMemCopyOp localDecls layouts src dest
    else do
      let imm ← annealReadImmediateLM2_2 src
      annealWriteImmediateLM2_2 imm.imm dest
  copyOpAllowTransmute := fun _ src dest =>
    if usesStructMemCopyDest dest then
      annealStructMemCopyOp localDecls layouts src dest
    else do
      let imm ← annealReadImmediateLM2_2 src
      annealWriteImmediateLM2_2 imm.imm dest
  binaryOp := fun c op l r => Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) c op l r
  unaryOp := fun c op v => Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks localDecls layouts) c op v
  writeAggregate := fun c k os d =>
    Miri.Interpreter.writeAggregate (annealAggregateHooksLM2_2 localDecls layouts) c k os d
  writeRepeat := fun c o d => Miri.Interpreter.writeRepeat (annealAggregateHooksLM2_2 localDecls layouts) c o d
  forceAllocation := fun c v => do
    let res ← Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) c v
    pure res.mplace
  toRef := fun _ _ => throw (.unsupported "toRef")
  enforceValidity := fun _ _ => pure true
  retagPtrValue := fun _ _ _ => pure none
  placeBaseRaw := fun _ _ => pure false
  normalize := fun _ tyId => pure tyId
  cast := fun c src kind ty dest =>
    Miri.Interpreter.Cast.cast (annealCastHooksLM2_2 layouts) c 16 src kind ty dest
  readDiscriminant := fun _ _ => throw (.unsupported "readDiscriminant")
  discriminantForVariant := fun _ _ _ => throw (.unsupported "discriminantForVariant")

theorem copyOp_eq_read_write_of_immediate
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (st : AnnealStepState) :
    (annealRvalueHooksLM2_2 localDecls layouts).copyOp () ⟨.immediate imm, lay⟩ dest st =
      (annealReadImmediateLM2_2 ⟨.immediate imm, lay⟩ >>= fun r => annealWriteImmediateLM2_2 r.imm dest) st := by
  unfold annealRvalueHooksLM2_2
  dsimp only
  cases usesStructMemCopyDest dest <;> cases imm <;> rfl

theorem bind_copyOp_eq_of_immediate
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {f : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv)}
    {dest : Miri.Interpreter.RuntimePlace AnnealProv}
    {m₀ : AnnealStepState}
    (h : ∀ src m₁, f m₀ = .ok src m₁ → ∃ imm, src.op = .immediate imm) :
    (f >>= fun src => (annealRvalueHooksLM2_2 localDecls layouts).copyOp () src dest) m₀ =
      ((f >>= annealReadImmediateLM2_2) >>= fun imm => annealWriteImmediateLM2_2 imm.imm dest) m₀ := by
  dsimp only [Bind.bind, EStateM.bind]
  cases hf : f m₀ with
  | error e s => rfl
  | ok src m₁ =>
    obtain ⟨imm, himm⟩ := h src m₁ hf
    rcases src with ⟨op, lay⟩
    dsimp only at himm
    subst himm
    exact copyOp_eq_read_write_of_immediate localDecls layouts imm lay dest m₁

theorem bind_copyOp_eq_of_not_usesStructMemCopyDest
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {f : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv)}
    {dest : Miri.Interpreter.RuntimePlace AnnealProv}
    (h : usesStructMemCopyDest dest = false)
    (m₀ : AnnealStepState) :
    (f >>= fun src => (annealRvalueHooksLM2_2 localDecls layouts).copyOp () src dest) m₀ =
      ((f >>= annealReadImmediateLM2_2) >>= fun imm => annealWriteImmediateLM2_2 imm.imm dest) m₀ := by
  unfold annealRvalueHooksLM2_2
  dsimp only
  rw [h]
  dsimp only [↓reduceIte, Bind.bind, EStateM.bind]
  cases f m₀ <;> rfl

/-- `TerminatorHooks` instantiated for the `LM-2.2` aggregate hook suite. -/
def annealTerminatorHooksLM2_2 (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.TerminatorHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.Operand AnnealProv)
      (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  { annealTerminatorHooks localDecls layouts with
    evalDiscriminant := fun _ op state =>
      Miri.Interpreter.runRvalue
        (do
          let opTy ← annealEvalOperand localDecls layouts op none
          annealReadImmediateLM2_2 opTy)
        state
    readAssertCondition := fun _ op state =>
      Miri.Interpreter.runRvalue
        (do
          let opTy ← annealEvalOperand localDecls layouts op none
          let imm ← annealReadImmediateLM2_2 opTy
          let sc ←
            match imm.imm.toScalar with
            | .ok sc => pure sc
            | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
          match sc.toBool with
          | .ok b => return b
          | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err))
        state }

/-- `StepHooks` instantiated for the `LM-2.2` aggregate hook suite (`LM-2.2`..`LM-2.4`). -/
def annealStepHooksLM2_2 (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.StepHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      AnnealMachine
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealStepHooks localDecls layouts with
    assign := fun choice place rvalue state =>
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooksLM2_2 localDecls layouts) choice rvalue place)
        state
    terminator := fun choice term state =>
      Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooksLM2_2 localDecls layouts) choice term state }

end LeanMiriSpec.Correspondence
