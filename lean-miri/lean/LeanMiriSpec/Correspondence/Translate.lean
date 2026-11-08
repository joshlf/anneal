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

/-- `ProjectionCx` instantiated for Anneal's single-threaded machine, wiring
upstream `Miri.Interpreter.projectionImmediateOffset` and thin-pointer offset
arithmetic for `Miri.Interpreter.project` / `Miri.Interpreter.projectField`. -/
def annealProjectionCx (layouts : LayoutTable)
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

/-- Lift a `Miri.Interpreter.ProjectionError` to `Miri.Interpreter.StepError`,
mapping runtime bounds/overflow checks to `StepError.undefinedBehavior` and
compiler/layout invariant mismatches to `StepError.invalidProgram`. -/
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
  | .rawPtr _ _ => some 40
  | .ref _ _ => some 41
  | .fnPtr _ _ _ _ => some 42
  | .never => some 50
  | .tuple .nil | .fnDef _ _ => some 51
  | _ => none

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

def arraySliceMetaTyId : Miri.MIR.TyId := 60

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

def annealPointerArithmetic : Miri.Memory.PointerArithmetic :=
  { pointerSize := Miri.ABI.Size.ofBytes 8 }

def annealLiveAllocationLookup (mach : AnnealMachine) :
    Miri.Memory.LiveAllocationLookup :=
  fun id =>
    match mach.memory.live.find? (fun (k, _) => k == id) with
    | some (_, la) =>
        .ok ⟨la.allocation.byteSize, la.allocation.align, .liveData, la.allocation.mutability⟩
    | none => .error (.unavailable id)

def annealArrayProjectionCx
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

def annealLiftProjectionError : Miri.Interpreter.ProjectionError → Miri.Interpreter.StepError
  | .machineError err => err
  | .bounds .. | .pointerArithOverflow =>
      .undefinedBehavior "out-of-bounds projection"
  | err =>
      .invalidProgram s!"projection invariant violation: {repr err}"

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
        match Miri.Interpreter.project (annealProjectionCx layouts hintTy) base elem with
        | .ok opTy => pure opTy
        | .error err => throw (annealLiftProjectionError err)
      annealEvalProjection layouts next rest

/-- Evaluate a local, projected field(s) of a local, or a constant
`Miri.MIR.Operand` in the top frame of `AnnealStepState`.

1. Memoizes the resolved `LocalLayout` into `frame.locals[localId].layout` via
   `Frame.getOrCacheLocalLayout` before checking liveness, matching `lean-miri`'s
   `LocalAccess.localToOp`.
2. `Copy` and `Move` read the local exactly as `lean-miri`'s source operand
   evaluators (`Miri.Interpreter.OperandMachine.evalOperand` and
   `Miri.Interpreter.evalOperand`) do. `Move` then deinitializes an unprojected
   moved-from local, implementing the runtime-MIR semantics that the pinned
   rustc documents for `Operand::Move` and that Anneal's
   `MirSemantics.evalOperand` implements: "in runtime MIR, this marks the place
   as deinitialized (i.e. writes `uninit` to all bytes of the place)"
   (`compiler/rustc_middle/src/mir/syntax.rs` at commit
   `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`). The pinned Miri interpreter, and
   hence upstream `lean-miri`, leaves this invalidation unimplemented, so on
   moves these hooks are deliberately stricter than upstream: afterwards the
   moved-from local reads as uninitialized in both machines.
3. Out-of-bounds `localId`s propagate `StepError.stack (.invalidLocal ...)`.
   Reading a `.dead` local (`StackError.localExpectedLive` from
   `Frame.getLocalOperand`) raises `StepError.undefinedBehavior`, matching rustc's
   `err_ub!(DeadLocal)` and Anneal's `MirStepNode.fail .ub` (whereas upstream
   `OperandMachine.stack` wraps `.localExpectedLive` as
   `StepError.stack (.localExpectedLive _)`, for which `RunLoop.reportsUB` is
   `false`).
4. A single `.Field 0` or `.Field 1` projection on an immediate `.scalarPair`
   local returns that component directly, tagged with the field's `TyId` but
   the pair's `LayoutData` (`⟨fieldTy, layout.layout⟩`). This shortcut is taken
   for every immediate pair, not only as a fallback; it exists for unindexed
   `layoutIdx = 0` `(T, bool)` checked-arithmetic results, whose synthesized
   layout uses `FieldsShape.Primitive` and so cannot be projected by
   `Miri.Interpreter.projectField`. Every other projected `.Field` read
   delegates to `annealEvalProjection` (`Miri.Interpreter.project` /
   `projectionImmediateOffset`). Even under `Move` projected reads leave the
   parent aggregate initialized, matching Anneal's `MirSemantics.evalOperand`. -/
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
      | projs => annealEvalProjection layouts ⟨operand, layout⟩ projs
  | .Constant c =>
      match evalMirConstImmediate layouts c with
      | .ok imm => return ⟨.immediate imm.imm, imm.layout⟩
      | .error e => throw e
  | .RuntimeChecks _ =>
      throw (.unsupported "RuntimeChecks operand")

/-- Read an `Immediate` from a memory-backed `MemPlace AnnealProv` at `layout`,
diagnosing `StepError.undefinedBehavior` when the field's byte range in the
underlying `Allocation` is uninitialized (`InvalidUninitBytes`). -/
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
      if layout.layout.size == Miri.ABI.Size.ZERO then
        return ⟨.uninit, layout⟩
      else
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
def annealReadImmediate (op : Miri.Interpreter.OpTy AnnealProv) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) := do
  match op.op with
  | .immediate (.scalar s) => return ⟨.scalar s, op.layout⟩
  | .immediate (.scalarPair s1 s2) => return ⟨.scalarPair s1 s2, op.layout⟩
  | .immediate .uninit => throw (.undefinedBehavior "read of uninitialized local")
  | .indirect mp => annealReadIndirectImmediate mp op.layout

/-- Project a `RuntimePlace AnnealProv` to field `fieldIdx` using upstream
`Miri.Interpreter.projectField` (`Place.projectRuntimePlace` carrier semantics). -/
def annealProjectFieldPlace (layouts : LayoutTable)
    (hintFieldTy : Option Miri.MIR.TyId)
    (place : Miri.Interpreter.RuntimePlace AnnealProv)
    (fieldIdx : Nat) :
    Except Miri.Interpreter.StepError (Miri.Interpreter.RuntimePlace AnnealProv) := do
  let cx := annealProjectionCx layouts hintFieldTy
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

/-- Resolve a `Miri.MIR.Place` to a `RuntimePlace AnnealProv` in the top
frame, memoizing the local's `LocalLayout` via `Frame.getOrCacheLocalLayout` and
propagating `StepError.stack` on out-of-bounds `localId`s (matching
`Miri.Interpreter.Place.evalPlace` / `placeLayoutOfLocal`). -/
def annealEvalPlace (localDecls : List LocalDecl) (layouts : LayoutTable)
    (place : Miri.MIR.Place) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RuntimePlace AnnealProv) := do
  if !place.projection.isEmpty then
    annealEvalProjectedPlace localDecls layouts place
  else
    let st ← get
    if st.stack.currentFrame?.isNone then
      throw (.stack .emptyStack)
    let frameIdx := st.stack.frames.size - 1
    let (frame', layout) ← annealResolveAndCacheLocalLayout localDecls layouts place.localId none
    return ⟨.local frameIdx place.localId none frame'.localsIdentity, layout⟩

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
`annealWriteImmediate` calls this function with the default empty `localDecls`
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

/-- Classify an encoded `Miri.MIR.TyId` into `Miri.Interpreter.CastTypeInfo` for
integer-like (`bool`, `char`, `i8..isize`, `u8..usize`) casts in
`Miri.Interpreter.Cast.cast`. Floating-point, pointer, and aggregate casts
fail closed with `StepError.unsupported` until their downstream hooks
(`ValidityVisitor`, provenance exposure, vtables) are wired. -/
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
  | _ => .error (.unsupported s!"cast typeInfo not wired in scalar fragment for TyId {tyId}")

/-- `CastHooks` instantiated for Anneal's single-threaded machine, supporting
integer-like `CastKind.IntToInt` via `Miri.Interpreter.Cast.cast` and failing
closed (`StepError.unsupported`) on float, pointer-provenance, unsizing, and
transmute leaves. -/
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
      annealWriteImmediate imm dest
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
upstream `Miri.Interpreter.writeAggregate` to `annealProjectFieldPlace`,
`annealEvalOperand`, `annealStructMemCopyOp` (for `.Memory` sub-structs), and
`annealWriteImmediate` across `AbiRepr.Scalar`, `AbiRepr.ScalarPair`, and
`AbiRepr.Memory` structs/tuples. -/
def annealAggregateHooks (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.AggregateHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) where
  target := annealTargetDataLayout
  placeLayout := fun p => p.layout
  evalOperand := fun _ op known => annealEvalOperand localDecls layouts op known
  readPointer := fun _ op => do
    let imm ← annealReadImmediate op
    match imm.imm.toScalar with
    | .ok sc =>
        match sc.toPointer annealTargetDataLayout with
        | .ok p => return p
        | .error _ => throw (.invalidProgram "expected pointer scalar")
    | .error _ => throw (.invalidProgram "expected scalar immediate")
  readScalar := fun _ op => do
    let imm ← annealReadImmediate op
    match imm.imm.toScalar with
    | .ok sc => return sc
    | .error _ => throw (.invalidProgram "expected scalar immediate")
  projectDowncast := fun _ dest variant =>
    if variant == 0 then pure dest
    else throw (.unsupported "multi-variant aggregate downcast not wired in LM-2.2")
  projectField := fun _ dest fieldIdx =>
    match dest.layout.layout.fields with
    | .Array stride _ => do
        let res ← Miri.Interpreter.forceAllocation (annealMutablePlaceHooks localDecls layouts) () dest
        let mp := res.mplace
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
      let imm ← annealReadImmediate src
      annealWriteImmediate imm.imm dest
  copyOpNoValidate := fun _ src dest _ =>
    if usesStructMemCopyDest ⟨dest.ref, src.layout⟩ && usesStructMemCopyDest dest then
      annealStructMemCopyOp localDecls layouts src dest
    else do
      let imm ← annealReadImmediate src
      annealWriteImmediate imm.imm dest
  writeDiscriminant := fun _ variant _ =>
    if variant == 0 then pure ()
    else throw (.unsupported "multi-variant aggregate writeDiscriminant not wired in LM-2.2")
  enforceValidity := fun _ _ => pure true
  validate := fun _ _ => pure ()
  forceAllocation := fun c dest => do
    let res ← Miri.Interpreter.forceAllocation (annealMutablePlaceHooks localDecls layouts) c dest
    return ⟨.memory res.mplace, res.layout⟩
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
  copyOp := fun _ src dest =>
    if usesStructMemCopyDest dest then
      annealStructMemCopyOp localDecls layouts src dest
    else do
      let imm ← annealReadImmediate src
      annealWriteImmediate imm.imm dest
  copyOpAllowTransmute := fun _ src dest =>
    if usesStructMemCopyDest dest then
      annealStructMemCopyOp localDecls layouts src dest
    else do
      let imm ← annealReadImmediate src
      annealWriteImmediate imm.imm dest
  binaryOp := fun c op l r => Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks localDecls layouts) c op l r
  unaryOp := fun c op v => Miri.Interpreter.ScalarOps.unary (annealScalarOpsHooks localDecls layouts) c op v
  writeAggregate := fun c k os d =>
    Miri.Interpreter.writeAggregate (annealAggregateHooks localDecls layouts) c k os d
  writeRepeat := fun c o d => Miri.Interpreter.writeRepeat (annealAggregateHooks localDecls layouts) c o d
  forceAllocation := fun c v => do
    let res ← Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) c v
    pure res.mplace
  toRef := fun _ _ => throw (.unsupported "toRef")
  enforceValidity := fun _ _ => pure true
  retagPtrValue := fun _ _ _ => pure none
  placeBaseRaw := fun _ _ => pure false
  normalize := fun _ tyId => pure tyId
  cast := fun c src kind ty dest =>
    Miri.Interpreter.Cast.cast (annealCastHooks layouts) c 16 src kind ty dest
  readDiscriminant := fun _ _ => throw (.unsupported "readDiscriminant")
  discriminantForVariant := fun _ _ _ => throw (.unsupported "discriminantForVariant")

theorem copyOp_eq_read_write_of_immediate
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (imm : Miri.Interpreter.Immediate AnnealProv)
    (lay : Miri.Interpreter.LocalLayout)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv)
    (st : AnnealStepState) :
    (annealRvalueHooks localDecls layouts).copyOp () ⟨.immediate imm, lay⟩ dest st =
      (annealReadImmediate ⟨.immediate imm, lay⟩ >>= fun r => annealWriteImmediate r.imm dest) st := by
  unfold annealRvalueHooks
  dsimp only
  cases usesStructMemCopyDest dest <;> cases imm <;> rfl

theorem bind_copyOp_eq_of_immediate
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {f : Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv)}
    {dest : Miri.Interpreter.RuntimePlace AnnealProv}
    {m₀ : AnnealStepState}
    (h : ∀ src m₁, f m₀ = .ok src m₁ → ∃ imm, src.op = .immediate imm) :
    (f >>= fun src => (annealRvalueHooks localDecls layouts).copyOp () src dest) m₀ =
      ((f >>= annealReadImmediate) >>= fun imm => annealWriteImmediate imm.imm dest) m₀ := by
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
    (f >>= fun src => (annealRvalueHooks localDecls layouts).copyOp () src dest) m₀ =
      ((f >>= annealReadImmediate) >>= fun imm => annealWriteImmediate imm.imm dest) m₀ := by
  unfold annealRvalueHooks
  dsimp only
  rw [h]
  dsimp only [↓reduceIte, Bind.bind, EStateM.bind]
  cases f m₀ <;> rfl

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
  allocation in `memory.dead` or release its base address, as rustc does for
  later dangling-pointer diagnostics and address reuse: no pointer to a local
  escapes in this fragment, so nothing can observe either record. -/
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
