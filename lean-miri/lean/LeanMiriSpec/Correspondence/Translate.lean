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
  | .rawPtr _ _ => 40
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
  | 40 | 41 => .ok .pointer
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
  | 40 => translateTy { kind := .rawPtr .not .bool, layoutIdx := 0 }
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
  | .pointerCoercion _ => .PointerCoercion .Unsize .Implicit
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

The pinned rustc MIR (`Miri.MIR.Rvalue`) has neither `Rvalue::Len` nor
`NullOp::{SizeOf, AlignOf, OffsetOf}`. Rather than invent a meaning for them,
the translation maps `len` to `CopyForDeref` (which `evalRvalueIntoPlace`
rejects in runtime MIR with `invalidProgram`) and those nullary operators to an
unevaluated constant (which `evalMirConstImmediate` rejects with
`unsupported`). Neither outcome is a value or undefined behavior, so no
simulation theorem can match them against Anneal results. -/
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
  | .shallowInitBox op contentTy =>
      .Cast .Transmute (translateOperand op) (encodeTyId contentTy)
  | .copyForDeref place => .CopyForDeref (translatePlace place)
  | .wrapUnsafeBinder op targetTy =>
      .WrapUnsafeBinder (translateOperand op) (encodeTyId targetTy)

/-- Translate an Anneal `RetagKind` to `Miri.TreeBorrows.RetagPolicy.RetagMode`. -/
def translateRetagKind : RetagKind → Miri.TreeBorrows.RetagPolicy.RetagMode
  | .fnEntry => .FnEntry
  | .twoPhase => .TwoPhase
  | .raw => .Raw
  | .default => .Default

/-- Translate an Anneal `StatementKind` to `Miri.MIR.StatementKind`. -/
def translateStmtKind : StatementKind → Miri.MIR.StatementKind
  | .assign place rv => .Assign (translatePlace place) (translateRvalue rv)
  | .setDiscriminant place variantIdx => .SetDiscriminant (translatePlace place) variantIdx
  | .deinit place => .PlaceMention (translatePlace place)
  | .storageLive local_ => .StorageLive local_
  | .storageDead local_ => .StorageDead local_
  | .retag _ place => .PlaceMention (translatePlace place)
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

/-- Translate an Anneal `CapturedMir` body to `Miri.MIR.Body`. -/
def translateBody (cm : CapturedMir) : Miri.MIR.Body :=
  { phase := .Runtime .PostCleanup
    argumentCount := cm.argCount
    spreadArgument := none
    locals := (cm.localDecls.map fun d => encodeTyId d.ty).toArray
    basicBlocks := (cm.basicBlocks.map translateBasicBlockData).toArray }

/-! ## 3. Single-Threaded Anneal Step State & Interpreter Hooks -/

/-- Provenance type instantiated for Anneal's correspondence with `lean-miri`. -/
abbrev AnnealProv := Miri.Memory.Provenance

/-- Step state for `lean-miri` instantiated with `AnnealProv`, `LocalLayout`,
`Unit` frame extra, and `Miri.Memory.MemoryState AnnealProv Unit Unit`. -/
abbrev AnnealStepState :=
  Miri.Interpreter.StepState
    AnnealProv
    Miri.Interpreter.LocalLayout
    Unit
    (Miri.Memory.MemoryState AnnealProv Unit Unit)

/-- Look up the `Miri.Interpreter.LocalLayout` for a `Local` in `localDecls` and `layouts`. -/
def lookupLocalDeclLayout (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Miri.MIR.LocalId) : Option Miri.Interpreter.LocalLayout :=
  match get? localDecls localId with
  | some decl => some (translateTy decl.ty layouts)
  | none => none

/-- Construct a `(T, bool)` scalar-pair layout for checked arithmetic overflow operations. -/
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
  let totalSize := (bOff.add (Miri.ABI.Size.ofBytes 1)).toOption.getD bOff
  { ty := 900 + elemLay.ty
    layout :=
      { elemLay.layout with
        fields := .Arbitrary #[Miri.ABI.Size.ZERO, bOff] #[0, 1]
        backendRepr := .ScalarPair (a := elemSc) (b := boolSc) (bOffset := bOff)
        size := totalSize } }

/-- `ScalarOpsHooks` instantiated for Anneal's single-threaded machine. -/
def annealScalarOpsHooks :
    Miri.Interpreter.ScalarOpsHooks AnnealProv AnnealStepState Unit where
  classify := fun _ tyId =>
    match classifyEncodedTyId tyId with
    | .ok cls => pure cls
    | .error err => throw err
  boolLayout := fun _ => pure (translateTy { kind := .bool, layoutIdx := 0 })
  orderingLayout := fun _ => pure (translateTy { kind := .int .i8, layoutIdx := 0 })
  overflowLayout := fun _ lay => pure (overflowPairLayout lay)
  metadataLayout := fun _ _ => pure (translateTy { kind := .uint .usize, layoutIdx := 0 })
  unitLayout := fun _ => pure (translateTy { kind := .tuple .nil, layoutIdx := 0 })
  floatBinary := fun _ op _ _ =>
    throw (.unsupported s!"floatBinary not supported: {repr op}")
  pointerBinary := fun _ op _ _ =>
    throw (.unsupported s!"pointerBinary not supported in scalar fragment: {repr op}")
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

/-- Evaluate an unprojected local or constant `Miri.MIR.Operand` in the top frame of
`AnnealStepState`.

`Copy` and `Move` share one branch, exactly as in `lean-miri`'s source operand
evaluators (`Miri.Interpreter.OperandMachine.evalOperand` and
`Miri.Interpreter.evalOperand`): the pinned rustc leaves move invalidation
unimplemented, so reading `Move place` leaves the source local unchanged. This
differs from Anneal's `MirSemantics.evalOperand`, which deinitializes a root
local on `Operand.move`; that divergence is deliberately not papered over here.

Reading a dead local is undefined behavior, matching rustc's `DeadLocal`. -/
def annealEvalOperand (localDecls : List LocalDecl) (layouts : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv) := do
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  match op with
  | .Copy place | .Move place =>
      if !place.projection.isEmpty then
        throw (.unsupported "projected operand in scalar rvalue")
      let localState ←
        match frame.getLocal place.localId with
        | .ok ls => pure ls
        | .error _ => throw (.undefinedBehavior "out-of-bounds local read")
      let layout ←
        match localState.layout <|> lookupLocalDeclLayout localDecls layouts place.localId <|> known with
        | some l => pure l
        | none =>
            match frame.body.locals[place.localId]? with
            | some tyId => pure (layoutOfEncodedTyId tyId layouts)
            | none => throw (.stack (.missingLocalType place.localId))
      match localState.value with
      | .dead => throw (.undefinedBehavior "read of dead local")
      | .live operand => return ⟨operand, layout⟩
  | .Constant c =>
      match evalMirConstImmediate layouts c with
      | .ok imm => return ⟨.immediate imm.imm, imm.layout⟩
      | .error e => throw e
  | .RuntimeChecks _ =>
      throw (.unsupported "RuntimeChecks operand")

/-- Read an `Immediate` from an `OpTy AnnealProv` in `AnnealStepState`, raising
`StepError.undefinedBehavior` on `.uninit` just as `MirSemantics.evalOperand` raises
`.fail .ub`. -/
def annealReadImmediate (op : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) := do
  match op.op with
  | .immediate (.scalar s) => return ⟨.scalar s, op.layout⟩
  | .immediate (.scalarPair s1 s2) => return ⟨.scalarPair s1 s2, op.layout⟩
  | .immediate .uninit => throw (.undefinedBehavior "read of uninitialized local")
  | .indirect _ => throw (.unsupported "indirect operand in scalar rvalue")

/-- Resolve an unprojected `Miri.MIR.Place` to a `RuntimePlace AnnealProv` in the top frame. -/
def annealEvalPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  if !place.projection.isEmpty then
    throw (.unsupported "projected destination place in scalar assign")
  let st ← get
  let some frame := st.stack.currentFrame?
    | throw (.stack .emptyStack)
  let frameIdx := st.stack.frames.size - 1
  let cachedLayout : Option Miri.Interpreter.LocalLayout :=
    match frame.getLocal place.localId with
    | .ok ls => ls.layout
    | .error _ => none
  let layout : Miri.Interpreter.LocalLayout :=
    match cachedLayout <|> lookupLocalDeclLayout localDecls layouts place.localId with
    | some l => l
    | none =>
        match frame.body.locals[place.localId]? with
        | some tyId => layoutOfEncodedTyId tyId layouts
        | none => translateTy { kind := .tuple .nil, layoutIdx := 0 }
  return ⟨.local frameIdx place.localId none frame.localsIdentity, layout⟩

/-- Write an `Immediate AnnealProv` into a `RuntimePlace AnnealProv` in the top frame,
failing with `StepError.undefinedBehavior` if the destination local is `.dead` or
out of bounds (matching `MirSemantics.evalStmt` on `.assign`). -/
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
      match frame.getLocal localId with
      | .error _ => throw (.undefinedBehavior "write to out-of-bounds local")
      | .ok ls =>
          match ls.value with
          | .dead => throw (.undefinedBehavior "write to dead local")
          | .live _ =>
              let updatedFrame ←
                match frame.replaceLocalValue localId (.live (.immediate val)) with
                | .ok f => pure f
                | .error e => throw (.stack e)
              let idx := st.stack.frames.size - 1
              if h : idx < st.stack.frames.size then
                set { st with stack := { frames := st.stack.frames.set idx updatedFrame h } }
              else
                throw (.stack .emptyStack)
  | _ => throw (.unsupported "non-local immediate write in scalar fragment")

/-- `RvalueHooks` instantiated for Anneal's single-threaded machine. -/
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
  binaryOp := fun c op l r => Miri.Interpreter.ScalarOps.binary annealScalarOpsHooks c op l r
  unaryOp := fun c op v => Miri.Interpreter.ScalarOps.unary annealScalarOpsHooks c op v
  writeAggregate := fun _ _ _ _ => throw (.unsupported "writeAggregate")
  writeRepeat := fun _ _ _ => throw (.unsupported "writeRepeat")
  forceAllocation := fun _ _ => throw (.unsupported "forceAllocation")
  toRef := fun _ _ => throw (.unsupported "toRef")
  enforceValidity := fun _ _ => pure true
  retagPtrValue := fun _ _ _ => pure none
  placeBaseRaw := fun _ _ => pure false
  normalize := fun _ tyId => pure tyId
  cast := fun _ _ _ _ _ => throw (.unsupported "cast")
  readDiscriminant := fun _ _ => throw (.unsupported "readDiscriminant")
  discriminantForVariant := fun _ _ _ => throw (.unsupported "discriminantForVariant")

/-- `ControlHooks` instantiated for Anneal's single-threaded machine. -/
def annealControlHooks :
    Miri.Interpreter.ControlHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      (Miri.Memory.MemoryState AnnealProv Unit Unit)
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
        | _ => (state, .error (.undefinedBehavior "return with uninitialized or dead _0"))
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
              | .error _ => (state, .error (.undefinedBehavior "caller destination local out of bounds"))
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
      (Miri.Memory.MemoryState AnnealProv Unit Unit)
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
  compareSwitchCase := fun _ imm caseVal state =>
    match imm.imm.toScalarInt with
    | .ok sc => (state, .ok (sc.data.toNat == caseVal))
    | .error _ => (state, .error (.invalidProgram "non-scalar switchInt discriminant"))
  call := fun _ _ state => (state, .error (.unsupported "call terminator"))
  tailCall := fun _ _ state => (state, .error (.unsupported "tailCall terminator"))
  drop := fun _ _ _ _ state => (state, .error (.unsupported "drop terminator"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ op state =>
    Miri.Interpreter.runRvalue
      (do
        let opTy ← annealEvalOperand localDecls layouts op none
        let imm ← annealReadImmediate opTy
        match imm.imm.toScalarInt with
        | .ok sc =>
            match sc.tryToBool with
            | .ok b => return b
            | .error _ => throw (.undefinedBehavior "invalid bool assert condition")
        | .error _ => throw (.invalidProgram "non-scalar assert condition"))
      state
  -- A failed `Assert` panics and unwinds in both rustc and Anneal (`applyUnwindAction`);
  -- it is never undefined behavior. Unwinding is outside the scalar fragment.
  assertPanic := fun _ _ _ state => (state, .error (.unsupported "assert panic (unwinding)"))

/-- Compiler and machine leaves of `lean-miri`'s source `storage_live_dyn` and
`storage_dead` (`Miri.Interpreter.Frame.storageLive` / `Frame.storageDead`) for
Anneal's single-threaded machine.

* `veryTriviallySized` answers `true`: `Runtime(PostCleanup)` MIR has no
  unsized locals, so `storage_live_dyn` never needs a layout or metadata.
* `afterLocalWrite` has nothing to do: data-race clocks exist only for
  multi-threaded machines.
* `allocateDyn` (unsized locals) and `deallocateStack` (memory-backed locals)
  report `StackError` failures. Locals become memory-backed only through
  `forceAllocation`, which `annealRvalueHooks` does not support, so neither
  leaf is reachable from a state whose locals are all immediate. -/
def annealLocalStorageHooks (localDecls : List LocalDecl) (layouts : LayoutTable) :
    Miri.Interpreter.LocalStorageHooks
      AnnealProv
      Miri.Interpreter.LocalLayout
      Unit
      (Miri.Memory.MemoryState AnnealProv Unit Unit) where
  veryTriviallySized := fun _ => .ok true
  layout := fun st _ localId =>
    match lookupLocalDeclLayout localDecls layouts localId with
    | some l => ⟨st, .ok l⟩
    | none => ⟨st, .error (.missingLocalType localId)⟩
  isSized := fun l => l.layout.isSized
  afterLocalWrite := fun st _ _ => ⟨st, .ok ()⟩
  allocateDyn := fun st _ _ =>
    ⟨st, .error (.allocationFailure "unsized locals are outside the scalar fragment")⟩
  deallocateStack := fun st _ =>
    ⟨st, .error (.deallocationFailure "memory-backed locals are outside the scalar fragment")⟩

/-- Run a current-frame storage operation (`Frame.storageLive` or
`Frame.storageDead`), writing back the resulting frame and memory even when the
operation fails, as `lean-miri`'s machine-level `MachineHooks.storageLiveDyn` and
`MachineHooks.storageDead` do. -/
def annealRunFrameStorage
    (op : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit →
      Miri.Memory.MemoryState AnnealProv Unit Unit →
      Miri.Interpreter.LocalStorageResult AnnealProv Miri.Interpreter.LocalLayout Unit
        (Miri.Memory.MemoryState AnnealProv Unit Unit))
    (state : AnnealStepState) : Miri.Interpreter.StepResult AnnealStepState Unit :=
  match state.stack.currentFrame? with
  | none => (state, .error (.stack .emptyStack))
  | some frame =>
      let result := op frame state.machine
      let idx := state.stack.frames.size - 1
      if h : idx < state.stack.frames.size then
        let state' : AnnealStepState :=
          { stack := { frames := state.stack.frames.set idx result.frame h }
            machine := result.state }
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
      (Miri.Memory.MemoryState AnnealProv Unit Unit)
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
