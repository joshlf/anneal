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

/-- Encode an Anneal `Ty` into a canonical `Miri.MIR.TyId` that injectively
distinguishes all scalar primitive types (`bool`, `char`, `i8..isize`,
`u8..usize`, `f16..f128`, pointers/references) and preserves `ty.layoutIdx` for
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
  | 70 | 71 | 72 | 73 | 74 | 75 | 76 | 77 | 78 | 79 | 80 | 81 | 82 => .ok .pointer
  | 42 => .ok .functionPointer
  | _ => .error (.invalidProgram s!"non-scalar TyId {tyId} in ScalarOps")

/-- Translate an Anneal `Ty` into a `Miri.Interpreter.LocalLayout`
(`Miri.ABI.TyAndLayout Miri.MIR.TyId`), using `layouts.lookup ty.layoutIdx` when
available for aggregate types or deriving the canonical scalar/pointer/ZST layout. -/
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

/-- Translate an Anneal `Rvalue` to `Miri.MIR.Rvalue`.

The pinned rustc MIR (`Miri.MIR.Rvalue`) has neither `Rvalue::Len`,
`Rvalue::ShallowInitBox`, nor `NullOp::{SizeOf, AlignOf, OffsetOf}`. Rather
than invent a meaning for them, the translation maps `len` to `CopyForDeref`
(which `evalRvalueIntoPlace` rejects in runtime MIR with `invalidProgram`) and
`shallowInitBox` and those nullary operators to an unevaluated constant (which
`evalMirConstImmediate` rejects with `unsupported`). Neither outcome is a value
or undefined behavior, so no simulation theorem can match them against Anneal
results. -/
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
  | .len place => .CopyForDeref (translatePlace place)
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
      .Call (translateOperand func)
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

/-- Pointer binary operations (`BinOp.Offset`) for Anneal's single-threaded
machine, matching `Miri.Interpreter.ExecutionScalar` (`ExecutionScalar.lean`)
and `Miri.Interpreter.ptrOffsetInbounds`:
1. Extracts the pointer scalar (`toPointer`) and resolves the pointee layout
   via `rawPtrPointeeEncodedTyId?` and `layoutOfEncodedTyId`.
2. Scales the count operand `right` by `pointeeLay.layout.size` using checked
   multiplication (`IntegerOps.binary .MulWithOverflow`), reporting
   `StepError.undefinedBehavior "PointerArithOverflow"` on multiplication
   overflow, `isize` conversion overflow, or an unsigned byte delta `>= 2^63`
   (`!signed && offset.toInt < 0`).
3. Runs `Miri.Interpreter.ptrOffsetInbounds` against `annealResolvePtr` and
   `annealLookupAlloc`, reporting `StepError.undefinedBehavior` on dangling or
   without-provenance pointers (when `offset != 0`), deallocated targets, or
   out-of-bounds offsets. -/
@[irreducible]
def annealPointerBinary (layouts : LayoutTable) (op : Miri.MIR.BinOp)
    (left right : Miri.Interpreter.RvalueImmTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) :=
  fun st =>
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
  derefValidity := fun _ _ => pure ()

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

/-- Whether `translateTy` gives a pointee of kind `k` its exact layout without
consulting a layout table: `bool`, `char`, the integer and float types, and the
unit type. Every other pointee (an aggregate, whose layout lives at an index
that a raw pointer type does not record; an unsized slice, `str`, or trait
object; or a pointer, which may itself be fat) has no layout that a dereference
can trust. -/
def derefPointeeKindHasExactLayout : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ | .tuple .nil => true
  | _ => false

/-- Resolve the pointee `LocalLayout` when dereferencing a raw-pointer local
`localId` (`*_p`), consulting `localDecls` when available and falling back to
`rawPtrPointeeEncodedTyId? ptrLayout.ty`. Safe references (`&T` / `&mut T`) and
pointees without an exact layout (`derefPointeeKindHasExactLayout`) resolve to
`none`, so the dereference fails closed instead of reading with a guessed width
or bypassing `PointerPlaceMachine.dereference`'s eager safe-reference checks. -/
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
          .memoryAccess (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
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
`MirSemantics.evalOperand` raises `.fail .ub`. -/
def annealReadImmediate (op : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) := do
  match op.op with
  | .immediate (.scalar s) => return ⟨.scalar s, op.layout⟩
  | .immediate (.scalarPair s1 s2) => return ⟨.scalarPair s1 s2, op.layout⟩
  | .immediate .uninit => throw (.undefinedBehavior "read of uninitialized local")
  | .indirect mplace => annealReadMemoryPlace mplace op.layout

/-- Construct a dereferenced `MemPlace` (`*_p`) from pointer local `localId`'s
current `Operand` and `LocalLayout`, caching numeric misalignment without
eagerly requiring the pointee allocation to be live (`PointerPlaceMachine.lean`). -/
@[irreducible]
def annealDerefOperandToMemPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) (operand : Miri.Interpreter.Operand AnnealProv)
    (ptrLayout : Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.MemPlace AnnealProv × Miri.Interpreter.LocalLayout) := do
  let some pointeeLay := lookupDerefPointeeLayout localDecls layouts localId ptrLayout
    | throw (.unsupported "dereference of local without pointee layout")
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

/-- Evaluate a local, a dereferenced pointer place (`*_p`), one field of a
scalar-pair local, or a constant `Miri.MIR.Operand` in the top frame of
`AnnealStepState`.

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
   `err_ub!(DeadLocal)` and Anneal's `MirStepNode.fail .ub`.
4. A single `Deref` projection (`*_p`) constructs an `.indirect` memory operand
   with cached misalignment (`PointerPlaceMachine.lean`), deferring bounds,
   liveness, alignment, and initialization checks to `annealReadImmediate`.
5. A single `Field` projection reads one scalar of a local that holds a scalar
   pair, such as a component of a checked-arithmetic result. Even under `Move`
   it leaves the local unchanged, because Anneal's `MirSemantics.evalOperand`
   keeps the parent aggregate initialized on projected reads. Every other
   projection fails closed with `StepError.unsupported`.

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
              let fieldImm := if idx == 0 then s0 else s1
              return ⟨.immediate (.scalar fieldImm), ⟨fieldTy, layout.layout⟩⟩
          | _ => throw (Miri.Interpreter.StepError.unsupported "projected operand not scalarPair")
      | _ => throw (Miri.Interpreter.StepError.unsupported "projected operand in scalar rvalue")
  | .Constant c =>
      match evalMirConstImmediate layouts c with
      | .ok imm => return ⟨.immediate imm.imm, imm.layout⟩
      | .error e => throw e
  | .RuntimeChecks _ =>
      throw (.unsupported "RuntimeChecks operand")

/-- Resolve an unprojected local `Miri.MIR.Place` or single-deref pointer place
(`*_p`) to a `RuntimePlace AnnealProv` in the top frame, memoizing the base
local's `LocalLayout` via `Frame.getOrCacheLocalLayout` and propagating
`StepError.stack` on out-of-bounds `localId`s. -/
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
    | _ =>
        throw (.unsupported "projected destination place in scalar assign")
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
          .memoryAccess (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
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
* Writing to an `.indirect` memory-backed local or a `.memory` dereferenced
  place routes through `annealWriteMemoryPlace` (matching
  `Place.asMplaceOrMutableLocal` and `MemoryOperand`). -/
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

`forceAllocation` is `annealForceAllocation`. `toRef` turns a memory place into
the pointer immediate that refers to it exactly as `lean-miri`'s own machine
bindings (`PlaceMachine` and `ExecutionMachine`) do: through `MemPlace.toRef`
(rustc's `MPlaceTy::to_ref`), reporting a malformed place as
`StepError.invalidProgram`. -/
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
  writeAggregate := fun _ _ _ _ => throw (.unsupported "writeAggregate")
  writeRepeat := fun _ _ _ => throw (.unsupported "writeRepeat")
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
  call := fun _ _ state => (state, .error (.unsupported "call terminator"))
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
* `deallocateStack` frees the allocation of a memory-backed local, which only
  `forceAllocation` creates. Like rustc's `deallocate_ptr`, it requires the
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
  intrinsic := fun _ _ state => (state, .error (.unsupported "intrinsic"))
  incrementConstEvalCounter := fun _ state => (state, .ok ())
  returnFromCurrentFrame := fun choice unwinding state =>
    Miri.Interpreter.ControlFlow.returnFromCurrentFrame annealControlHooks choice unwinding state
  beforeTerminator := fun _ state => (state, .ok ())
  terminator := fun choice term state =>
    Miri.Interpreter.ControlFlow.evalTerminator (annealTerminatorHooks localDecls layouts) choice term state

end LeanMiriSpec.Correspondence
