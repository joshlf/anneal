import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Statements
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Places

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

/-!
Small-step interaction-tree execution of MIR `Statement`s (`advanceStmt`,
`evalStmt`) for `Runtime(PostCleanup)` MIR at
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`#88`, `#100`, `#102`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L303-L420>

> "pub enum StatementKind<'tcx> {
>     Assign(Box<(Place<'tcx>, Rvalue<'tcx>)>),
>     FakeRead(Box<(FakeReadCause, Place<'tcx>)>),
>     SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },
>     Deinit(Box<Place<'tcx>>),
>     StorageLive(Local),
>     StorageDead(Local),
>     Retag(RetagKind, Box<Place<'tcx>>),
>     PlaceMention(Box<Place<'tcx>>),
>     AscribeUserType(Box<(Place<'tcx>, UserTypeProjection)>, Variance),
>     Coverage(CoverageKind),
>     Intrinsic(Box<NonDivergingIntrinsic<'tcx>>),
>     ConstEvalCounter,
>     Nop,
>     BackwardIncompatibleDropHint { place: Box<Place<'tcx>>, reason: BackwardIncompatibleDropReason },
> }"
-/

/--
Advance the program counter to the next statement in the current basic block.
-/
def advanceStmt
    (s : MachineState)
    (locals' : List LocalSlot)
    (mem' : Memory := s.memory) :
    MachineState :=
  { s with
    frame := {
      s.frame with
      stmtIdx := Nat.add s.frame.stmtIdx 1
      locals := locals'
    }
    memory := mem'
  }

/--
Concatenate two `List Value` sequences.
-/
@[reducible]
def appendValues : List Value → List Value → List Value
  | .nil, ys => ys
  | x :: xs, ys => x :: appendValues xs ys

/--
Replace `length srcSlice` elements in `dstElems` starting at index `dstStart`
with `srcSlice`.
-/
@[reducible]
def spliceValues
    (srcSlice : List Value)
    (dstStart : Nat)
    (dstElems : List Value) :
    List Value :=
  let n := length srcSlice
  appendValues
    (takeValues dstStart dstElems)
    (appendValues srcSlice (dropValues (Nat.add dstStart n) dstElems))

/--
Test whether two `RigidTy` constructors share the same runtime `Value` shape
so a single-element `copy_nonoverlapping` can transfer the `Value` directly
without re-encoding through `AbstractByte`s.
-/
@[reducible]
def sameRigidTyShape (k₁ k₂ : RigidTy) : Bool :=
  match k₁, k₂ with
  | .bool, .bool => true
  | .char, .char => true
  | .uint _, .uint _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .int _, .int _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .uint _, .int _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .int _, .uint _ =>
    match intCastTargetBytes k₁, intCastTargetBytes k₂ with
    | .some n₁, .some n₂ => Nat.beq n₁ n₂
    | _, _ => false
  | .array e₁ n₁, .array e₂ n₂ =>
    match Nat.beq n₁ n₂ with
    | false => false
    | true =>
      match rigidTyKindByteSize e₁, rigidTyKindByteSize e₂ with
      | .some s₁, .some s₂ => Nat.beq s₁ s₂
      | _, _ => false
  | .tuple ks₁, .tuple ks₂ => Nat.beq (length ks₁) (length ks₂)
  | .adt p₁ _, .adt p₂ _ => stringEq p₁ p₂
  | .ref _ _, .ref _ _ => true
  | .rawPtr _ _, .rawPtr _ _ => true
  | _, _ => false

/--
Resolve the pointee `Ty` of a pointer `Operand` using `operandTy` and
`pointeeTyOf`, preserving the pointee's `LayoutTable` index when `ptrTy` carries
a single pointee layout entry in `TypeLayout.fieldLayouts`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1705-L1725>

> "pub struct LayoutData<FieldIdx, VariantIdx> {
>     pub fields: FieldsShape<FieldIdx>,
>     pub variants: Variants<FieldIdx, VariantIdx>,
>     pub abi: BackendRepr,
>     ...
> }"
-/
@[reducible]
def operandPointeeTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Option Ty :=
  match operandTy localDecls layouts op with
  | .some ptrTy =>
    match pointeeTyOf ptrTy with
    | .some pt =>
      match LayoutTable.lookup layouts ptrTy.layoutIdx with
      | .some ptrLayout =>
        let isPtrRepr :=
          match ptrLayout.backendRepr with
          | .scalar (.initialized (.pointer _) _) => true
          | .scalar (.union (.pointer _)) => true
          | .scalarPair (.initialized (.pointer _) _) _ => true
          | .scalarPair (.union (.pointer _)) _ => true
          | _ => false
        match isPtrRepr, ptrLayout.fieldLayouts with
        | true, ptLayoutIdx :: .nil =>
          .some { kind := pt.kind, layoutIdx := ptLayoutIdx }
        | _, _ => .some pt
      | .none => .some pt
    | .none => .none
  | .none => .none

/--
Compute the ABI byte alignment of a `RigidTy` when determined structurally by
its primitive, pointer, or homogeneous array constructor on a 64-bit target.

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of a value specifies what addresses are valid to store the
> value at. A value of alignment n must only be stored at an address that is a
> multiple of n."
-/
@[reducible]
def rigidTyKindByteAlign : RigidTy → Option Nat
  | .bool => .some 1
  | .char => .some 4
  | .uint .u8 => .some 1
  | .uint .u16 => .some 2
  | .uint .u32 => .some 4
  | .uint .u64 => .some 8
  | .uint .u128 => .some 16
  | .uint .usize => .some 8
  | .int .i8 => .some 1
  | .int .i16 => .some 2
  | .int .i32 => .some 4
  | .int .i64 => .some 8
  | .int .i128 => .some 16
  | .int .isize => .some 8
  | .float .f16 => .some 2
  | .float .f32 => .some 4
  | .float .f64 => .some 8
  | .float .f128 => .some 16
  | .tuple .nil => .some 1
  | .fnDef _ _ => .some 1
  | .never => .some 1
  | .fnPtr _ _ _ _ => .some 8
  | .ref _ _ => .some 8
  | .rawPtr _ _ => .some 8
  | .array elemKind _ => rigidTyKindByteAlign elemKind
  | _ => .none

/--
Resolve the byte alignment of `ty` using `rigidTyKindByteAlign` for primitives,
pointers, and primitive arrays, or `LayoutTable.lookup layouts ty.layoutIdx` for
ADTs and layout-indexed aggregates (defaulting to `1` when unconstrained).
-/
@[reducible]
def rigidTyByteAlign (layouts : LayoutTable) (ty : Ty) : Nat :=
  match rigidTyKindByteAlign ty.kind with
  | .some align => align
  | .none =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | .some l =>
      match Nat.beq l.align.bytes 0 with
      | true => 1
      | false => l.align.bytes
    | .none => 1

/--
Resolve the pointee byte alignment of a pointer `Operand` (defaulting to `1`
when the operand carries no static pointee type).
-/
@[reducible]
def operandPointeeAlign
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (op : Operand) :
    Nat :=
  match operandPointeeTy localDecls layouts op with
  | .some pt => rigidTyByteAlign layouts pt
  | .none => 1

/--
Test whether byte offset `offset` is a multiple of non-zero alignment `align`
(`offset % align == 0`).

Reference (`core::intrinsics::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.copy_nonoverlapping.html>

> "`src` and `dst` must be properly aligned."
-/
@[reducible]
def isAlignedOffset (offset align : Nat) : Bool :=
  match Nat.beq align 0 with
  | true => true
  | false => Nat.beq (Nat.mod offset align) 0

/--
Test whether two half-open byte intervals `[start₁, start₁ + len₁)` and
`[start₂, start₂ + len₂)` within the same allocation are disjoint.

Reference (`core::intrinsics::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.copy_nonoverlapping.html>

> "The memory regions of size `count * size_of::<T>()` bytes referenced by `src`
> and `dst` must not overlap."
-/
@[reducible]
def rangesDisjoint (start₁ len₁ start₂ len₂ : Nat) : Bool :=
  Bool.or
    (Nat.ble (Nat.add start₁ len₁) start₂)
    (Nat.ble (Nat.add start₂ len₂) start₁)

/--
Look up the total byte size of `localIdx` when its `LocalDecl` layout in
`layouts` has `FieldsShape.union`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1649-L1650>

> "/// All fields start at no offset. The `usize` is the field count.
> Union(NonZeroUsize),"
-/
@[reducible]
def unionLocalByteSize?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (localIdx : LocalIdx) :
    Option Nat :=
  match localDecls with
  | .nil => .none
  | _ :: _ =>
    match get? localDecls localIdx with
    | .some decl =>
      match LayoutTable.lookup layouts decl.ty.layoutIdx with
      | .some l =>
        match l.fields with
        | .union _ => .some l.size.bytes
        | _ => .none
      | .none => .none
    | .none => .none

/--
Test whether `localIdx` in `localDecls` has a `FieldsShape.union` layout in
`layouts`.
-/
@[reducible]
def localDeclIsUnion
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (localIdx : LocalIdx) :
    Bool :=
  match unionLocalByteSize? localDecls layouts localIdx with
  | .some _ => true
  | .none => false

/--
Extract the union field `Ty` from a direct union field projection
`[.field _ fieldTy]` or an array-to-element thin-pointer projection
`[.field _ fieldTy, .subslice 0 _ false]` (after stripping transparent
`.opaqueCast` and `.unwrapUnsafeBinder` wrappers).
-/
@[reducible]
def extractUnionFieldProj? (proj : List ProjectionElem) : Option Ty :=
  match stripTransparentProjections proj with
  | .field _ fieldTy :: .nil => .some fieldTy
  | .field _ fieldTy :: .subslice .zero _ false :: .nil => .some fieldTy
  | _ => .none

/--
Determine the element byte stride and array length `(elemStride, arrLen)` of an
array type `arrTy` (`RigidTy.array elemKind arrLen`).
-/
@[reducible]
def arrayElemStrideAndLen?
    (layouts : LayoutTable)
    (arrTy : Ty) :
    Option (Nat × Nat) :=
  match arrTy.kind with
  | .array elemKind arrLen =>
    match rigidTyKindByteSize elemKind with
    | .some elemSz => .some (elemSz, arrLen)
    | .none =>
      match LayoutTable.lookup layouts arrTy.layoutIdx with
      | .some l =>
        match l.fields with
        | .array stride count => .some (stride.bytes, count)
        | _ =>
          match elemKind with
          | .tuple ks =>
            match tupleFieldsByteSize ks with
            | .some sz => .some (sz, arrLen)
            | .none => .none
          | _ =>
            match Nat.beq arrLen 0 with
            | true => .none
            | false =>
              match Nat.beq (Nat.mod l.size.bytes arrLen) 0 with
              | true => .some (Nat.div l.size.bytes arrLen, arrLen)
              | false => .none
      | .none =>
        match elemKind with
        | .tuple ks =>
          match tupleFieldsByteSize ks with
          | .some sz => .some (sz, arrLen)
          | .none => .none
        | _ => .none
  | _ => .none

/--
Resolved byte-window metadata for a pointer targeting a `FieldsShape.union`
local or one of its fields or array/subslice sub-places.
-/
structure UnionPlaceInfo : Type where
  /-- Total byte size of the root union local (`TypeLayout.size.bytes`). -/
  unionBytes : Nat
  /-- Target union field `(fieldIdx, fieldTy, fieldBytes)` when projected. -/
  fieldTarget : Option (Nat × Ty × Nat)
  /-- Byte offset from offset `0` of the union introduced by sub-projections. -/
  subBaseOffset : Nat
  /-- Addressable byte bound of the projected place starting at `subBaseOffset`. -/
  placeByteBound : Nat

/--
Resolve a trailing projection suffix `rest` within a union field `fieldTy` of
size `fieldBytes` (covering `[]`, `.subslice fromIdx toIdx false` produced by
`deriveStackElemThinPtr`, `.constantIndex idx minLen false`, and single-field
transparent wrappers `.field 0 innerTy` such as `ManuallyDrop<T>`).
-/
@[reducible]
def resolveUnionFieldSuffix?
    (layouts : LayoutTable)
    (unionBytes : Nat)
    (fieldIdx : Nat)
    (fieldTy : Ty)
    (fieldBytes : Nat)
    (innerTy : Ty)
    (rest : List ProjectionElem) :
    Option UnionPlaceInfo :=
  match rest with
  | .nil =>
    .some
      { unionBytes := unionBytes
        fieldTarget := .some (fieldIdx, fieldTy, fieldBytes)
        subBaseOffset := 0
        placeByteBound := fieldBytes }
  | .subslice fromIdx toIdx false :: .nil =>
    match arrayElemStrideAndLen? layouts innerTy with
    | .some (elemStride, arrLen) =>
      match Bool.and (Nat.ble fromIdx toIdx) (Nat.ble toIdx arrLen) with
      | false => .none
      | true =>
        let baseOff := Nat.mul fromIdx elemStride
        let subBound := Nat.mul (Nat.sub toIdx fromIdx) elemStride
        match Nat.ble (Nat.add baseOff subBound) fieldBytes with
        | false => .none
        | true =>
          .some
            { unionBytes := unionBytes
              fieldTarget := .some (fieldIdx, fieldTy, fieldBytes)
              subBaseOffset := baseOff
              placeByteBound := subBound }
    | .none =>
      match Nat.beq fromIdx 0 with
      | false => .none
      | true =>
        .some
          { unionBytes := unionBytes
            fieldTarget := .some (fieldIdx, fieldTy, fieldBytes)
            subBaseOffset := 0
            placeByteBound := fieldBytes }
  | .constantIndex idx minLen false :: .nil =>
    match arrayElemStrideAndLen? layouts innerTy with
    | .some (elemStride, arrLen) =>
      match
        Bool.and
          (Nat.ble minLen arrLen)
          (Nat.ble (Nat.add idx 1) arrLen)
      with
      | false => .none
      | true =>
        let baseOff := Nat.mul idx elemStride
        match Nat.ble (Nat.add baseOff elemStride) fieldBytes with
        | false => .none
        | true =>
          .some
            { unionBytes := unionBytes
              fieldTarget := .some (fieldIdx, fieldTy, fieldBytes)
              subBaseOffset := baseOff
              placeByteBound := elemStride }
    | .none => .none
  | _ => .none

/--
Resolve `proj` on a union local of size `unionBytes` into its `UnionPlaceInfo`
byte window when `proj` addresses the union root, a union field, an array
subslice/index of a union field, or a same-sized field-`0` transparent wrapper
inside a union field (such as `MaybeUninit<T>` wrapping `ManuallyDrop<T>`).
-/
@[reducible]
def extractUnionPlaceInfo?
    (layouts : LayoutTable)
    (unionBytes : Nat)
    (proj : List ProjectionElem) :
    Option UnionPlaceInfo :=
  match stripTransparentProjections proj with
  | .nil =>
    .some
      { unionBytes := unionBytes
        fieldTarget := .none
        subBaseOffset := 0
        placeByteBound := unionBytes }
  | .field fieldIdx fieldTy :: rest =>
    match rigidTyByteSize layouts fieldTy with
    | .none => .none
    | .some fieldBytes =>
      match Nat.ble fieldBytes unionBytes with
      | false => .none
      | true =>
        match rest with
        | .field .zero innerTy :: innerRest =>
          match rigidTyByteSize layouts innerTy with
          | .some innerBytes =>
            match Nat.beq fieldBytes innerBytes with
            | true =>
              resolveUnionFieldSuffix?
                layouts
                unionBytes
                fieldIdx
                fieldTy
                fieldBytes
                innerTy
                innerRest
            | false => .none
          | .none => .none
        | _ =>
          resolveUnionFieldSuffix?
            layouts
            unionBytes
            fieldIdx
            fieldTy
            fieldBytes
            fieldTy
            rest
  | _ => .none

/--
Resolve `entry` as a frame-local union endpoint when `entry.targetLocal` has a
`FieldsShape.union` layout in `localDecls` / `layouts`, exists in `locals`, and
projects a supported union byte window.
-/
@[reducible]
def resolveUnionEndpoint?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (entry : BorrowEntry) :
    Option UnionPlaceInfo :=
  match unionLocalByteSize? localDecls layouts entry.targetLocal with
  | .none => .none
  | .some unionBytes =>
    match get? locals entry.targetLocal with
    | .none => .none
    | .some _ =>
      extractUnionPlaceInfo? layouts unionBytes entry.targetProjection

/--
Pad or truncate `bs` to `targetBytes` bytes, filling any trailing positions
`[length bs .. targetBytes)` with `AbstractByte.uninit`.
-/
@[reducible]
def padUnionAbstractBytes
    (targetBytes : Nat)
    (bs : List AbstractByte) :
    List AbstractByte :=
  let len := length bs
  match Nat.ble targetBytes len with
  | true => takeAbstractBytes targetBytes bs
  | false =>
    appendAbstractBytes bs (replicateUninitBytes (Nat.sub targetBytes len))

/--
Encode the `unionBytes`-byte storage image of a union local from its populated
`fieldVals`, padding any uninitialized byte positions up to `unionBytes` with
`AbstractByte.uninit`.

Reference (The Rust Reference, "Unions"):
<https://doc.rust-lang.org/1.98.0/reference/items/unions.html>

> "The key property of unions is that all fields of a union share common
> storage. As a result, writes to one field of a union can overwrite its other
> fields, and size of a union is determined by the size of its largest field."
-/
@[reducible]
def encodeUnionStorageBytes
    (layouts : LayoutTable)
    (unionBytes : Nat)
    (fieldTarget : Option (Nat × Ty × Nat))
    (fieldVals : List Value) :
    List AbstractByte :=
  let baseBytes : List AbstractByte :=
    match fieldVals with
    | .nil => replicateUninitBytes unionBytes
    | _ :: _ =>
      match
        encodeUnionFieldsWith
          (encodeUntypedValueToBytes defaultCodecFuel)
          unionBytes
          fieldVals
      with
      | .some bs => padUnionAbstractBytes unionBytes bs
      | .none => replicateUninitBytes unionBytes
  match fieldTarget with
  | .none => baseBytes
  | .some (fIdx, fTy, fBytes) =>
    match Nat.beq fBytes 0 with
    | true => baseBytes
    | false =>
      match get? fieldVals fIdx with
      | .none => baseBytes
      | .some .unit => baseBytes
      | .some fv =>
        let typedOpt : Option (List AbstractByte) :=
          match encodeValueToBytes defaultCodecFuel layouts fTy fv with
          | .some bs => .some bs
          | .none =>
            match encodeUntypedValueToBytes defaultCodecFuel fv with
            | .some bs =>
              match Nat.beq (length bs) fBytes with
              | true => .some bs
              | false => .none
            | .none => .none
        match typedOpt with
        | .some fieldBs =>
          match writeAbstractBytesAt baseBytes 0 fieldBs with
          | .some merged => merged
          | .none => baseBytes
        | .none => baseBytes

/--
Reset a union aggregate's `fields` list when its storage contains uninitialized
or non-decodable bytes, preserving field `0` only when field `0` is a zero-sized
`()` value (such as `uninit: ()` in `Uninit<T>` or `MaybeUninit<T>`) and
clearing any stale non-ZST field values.
-/
@[reducible]
def resetUnionFields (fields : List Value) : List Value :=
  match fields with
  | .unit :: _ => .unit :: .nil
  | .aggregate .zero .nil :: _ => .aggregate .zero .nil :: .nil
  | _ => .nil

/--
Evaluate the single-element direct value copy branch (`count == 1` and
`srcStart == 0` and `dstStart == 0`) of `evalCopyNonOverlapping`.
-/
def evalCopySingleDirect
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  let overlaps :=
    match Nat.beq srcPtr.tag dstPtr.tag with
    | true => true
    | false =>
      match
        Nat.beq srcEntry.targetLocal dstEntry.targetLocal
      with
      | false => false
      | true =>
        projectionsOverlap
          srcEntry.targetProjection
          dstEntry.targetProjection
  match overlaps with
  | true => MirStepNode.fail .ub
  | false =>
    let srcRootSlot : Option LocalSlot :=
      match get? locals₃ srcEntry.targetLocal with
      | .some slot => .some slot
      | .none =>
        match get? s.memory.callerLocals srcEntry.targetLocal with
        | .some slot => .some slot
        | .none =>
          get?
            s.memory.callerLocals
            (Nat.sub srcEntry.targetLocal (length locals₃))
    match srcRootSlot with
    | .some (.init srcRootVal) =>
      match
        readProjectedValue
          locals₃
          srcRootVal
          srcEntry.targetProjection
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok copiedVal =>
        let dstPlace : Place := {
          local_ := dstEntry.targetLocal
          projection := dstEntry.targetProjection
        }
        let convertedOpt : Option Value :=
          match
            operandPointeeTy localDecls layouts src,
            operandPointeeTy localDecls layouts dst
          with
          | .some srcPt, .some dstPt =>
            match sameRigidTyShape srcPt.kind dstPt.kind with
            | true => .some copiedVal
            | false =>
              match
                rigidTyByteSize layouts srcPt,
                rigidTyByteSize layouts dstPt
              with
              | .some sSz, .some dSz =>
                match Nat.beq sSz dSz with
                | false => .none
                | true =>
                  match
                    encodeValueToBytes
                      defaultCodecFuel
                      layouts
                      srcPt
                      copiedVal
                  with
                  | .some bs =>
                    decodeValueFromBytes
                      defaultCodecFuel
                      layouts
                      dstPt
                      bs
                  | .none => .none
              | _, _ => .some copiedVal
          | _, _ => .some copiedVal
        match convertedOpt with
        | .none => MirStepNode.fail .ub
        | .some finalVal =>
          match
            writePlaceValue
              locals₃
              s.memory.borrows
              dstPlace
              finalVal
              localDecls
              layouts
          with
          | .ok locals₄ =>
            let borrows' :=
              invalidateConflictingBorrows
                s.memory.borrows
                dstEntry.targetLocal
                (.some dstPtr.tag)
                (length s.memory.callStack)
            MirStepNode.step
              (advanceStmt
                s
                locals₄
                { s.memory with borrows := borrows' })
          | .unsupported => MirStepNode.unsupported
          | .ub =>
            match get? locals₃ dstPlace.local_ with
            | .some _ => MirStepNode.fail .ub
            | .none =>
              let callerIdx :=
                match get? s.memory.callerLocals dstPlace.local_ with
                | .some _ => dstPlace.local_
                | .none => Nat.sub dstPlace.local_ (length locals₃)
              let coerceToCallerDst (oldVal : Value) : Value :=
                match oldVal, finalVal with
                | .aggregate 0 dstElems, .scalar sc =>
                  match
                    Bool.and
                      (Bool.not (Nat.beq sc.sizeBytes 1))
                      (Nat.ble sc.sizeBytes (length dstElems))
                  with
                  | false => finalVal
                  | true =>
                    match
                      encodeUntypedValueToBytes defaultCodecFuel finalVal
                    with
                    | .none => finalVal
                    | .some bs =>
                      match
                        decodeArrayChunksWith
                          (fun chunk =>
                            decodeValueFromBytes
                              defaultCodecFuel
                              layouts
                              { kind := .uint .u8, layoutIdx := 0 }
                              chunk)
                          1
                          (length bs)
                          bs
                      with
                      | .some copiedBytes =>
                        .aggregate 0 (spliceValues copiedBytes 0 dstElems)
                      | .none => finalVal
                | _, _ => finalVal
              let callerWriteRes : PlaceWriteResult :=
                match dstPlace.projection with
                | .nil =>
                  match get? s.memory.callerLocals callerIdx with
                  | .some .dead => .ub
                  | .some (.init oldVal) =>
                    let coercedVal := coerceToCallerDst oldVal
                    match
                      set? s.memory.callerLocals callerIdx (.init coercedVal)
                    with
                    | .some callerLocals' => .ok callerLocals'
                    | .none => .ub
                  | .some .uninit =>
                    match
                      set? s.memory.callerLocals callerIdx (.init finalVal)
                    with
                    | .some callerLocals' => .ok callerLocals'
                    | .none => .ub
                  | .none => .ub
                | .deref :: _ => .ub
                | proj :: rest =>
                  match get? s.memory.callerLocals callerIdx with
                  | .some (.init rootVal) =>
                    let coercedVal :=
                      match
                        readProjectedValue locals₃ rootVal (proj :: rest)
                      with
                      | .ok oldSubVal => coerceToCallerDst oldSubVal
                      | _ => finalVal
                    match
                      writeProjectedValue
                        locals₃
                        rootVal
                        (proj :: rest)
                        coercedVal
                    with
                    | .ok rootVal' =>
                      match
                        set? s.memory.callerLocals callerIdx (.init rootVal')
                      with
                      | .some callerLocals' => .ok callerLocals'
                      | .none => .ub
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | _ => .ub
              match callerWriteRes with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok callerLocals' =>
                let borrows' :=
                  invalidateConflictingBorrows
                    s.memory.borrows
                    dstEntry.targetLocal
                    (.some dstPtr.tag)
                    dstEntry.targetFrameDepth
                MirStepNode.step
                  (advanceStmt
                    s
                    locals₃
                    { s.memory with
                      borrows := borrows'
                      callerLocals := callerLocals' })
    | _ => MirStepNode.fail .ub

/--
Write `newVal` to `dstPlace` in `locals₃` (or `s.memory.callerLocals` when
`dstPlace.local_` indexes a caller local), invalidate conflicting Tree Borrows
tags on `dstTargetLocal` relative to `dstTag`, and advance `s` to the next
statement.
-/
def commitCopyDstPlaceWrite
    (s : MachineState)
    (dstPlace : Place)
    (dstTargetLocal : LocalIdx)
    (dstTag : Nat)
    (locals₃ : List LocalSlot)
    (newVal : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    writePlaceValue
      locals₃
      s.memory.borrows
      dstPlace
      newVal
      localDecls
      layouts
  with
  | .ok locals₄ =>
    let borrows' :=
      invalidateConflictingBorrows
        s.memory.borrows
        dstTargetLocal
        (.some dstTag)
        (length s.memory.callStack)
    MirStepNode.step
      (advanceStmt
        s
        locals₄
        { s.memory with borrows := borrows' })
  | .unsupported => MirStepNode.unsupported
  | .ub =>
    match get? locals₃ dstPlace.local_ with
    | .some _ => MirStepNode.fail .ub
    | .none =>
      let callerIdx :=
        match get? s.memory.callerLocals dstPlace.local_ with
        | .some _ => dstPlace.local_
        | .none => Nat.sub dstPlace.local_ (length locals₃)
      let callerWriteRes : PlaceWriteResult :=
        match dstPlace.projection with
        | .nil =>
          match get? s.memory.callerLocals callerIdx with
          | .some .dead => .ub
          | .some _ =>
            match set? s.memory.callerLocals callerIdx (.init newVal) with
            | .some callerLocals' => .ok callerLocals'
            | .none => .ub
          | .none => .ub
        | .deref :: _ => .ub
        | proj :: rest =>
          match get? s.memory.callerLocals callerIdx with
          | .some (.init rootVal) =>
            match
              writeProjectedValue
                locals₃
                rootVal
                (proj :: rest)
                newVal
            with
            | .ok rootVal' =>
              match set? s.memory.callerLocals callerIdx (.init rootVal') with
              | .some callerLocals' => .ok callerLocals'
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _ => .ub
      match callerWriteRes with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callerLocals' =>
        let borrows' :=
          invalidateConflictingBorrows
            s.memory.borrows
            dstTargetLocal
            (.some dstTag)
            0
        MirStepNode.step
          (advanceStmt
            s
            locals₃
            { s.memory with
              borrows := borrows'
              callerLocals := callerLocals' })

/--
Source byte-slice extraction result for `evalCopyUnionBytes`.
-/
inductive UnionSrcSliceResult : Type where
  /-- Source access violated bounds, alignment, liveness, or initialization. -/
  | ub : UnionSrcSliceResult
  /-- Source value uses an unmodeled representation. -/
  | unsupported : UnionSrcSliceResult
  /-- Extracted `copiedBytes`, whether `src` lives in `locals₃`, and effective
      byte offset from offset `0` of `srcEntry.targetLocal`. -/
  | ok
      (copiedBytes : List AbstractByte)
      (srcInFrame : Bool)
      (srcEffStart : Nat) :
      UnionSrcSliceResult

/--
Evaluate `copy_nonoverlapping` (`countBits > 0`) when `src`, `dst`, or both
address a `FieldsShape.union` local (`srcUnionOpt` / `dstUnionOpt`).

Enforces pointer alignment (`isAlignedOffset`), place and union byte bounds,
non-overlap (`rangesDisjoint`), and Rust typed-memory bit-validity:
- Uninitialized union bytes (`AbstractByte.uninit`) may be copied into a union
  destination (`dstUnionOpt = .some _`), updating `dst` to its decoded typed
  field/union value when all required bytes are valid or resetting `dst` to its
  uninitialized union representation via `resetUnionFields` when `.uninit` bytes
  remain.
- Copying uninitialized union bytes into a non-union destination
  (`dstUnionOpt = .none`) fails closed with `MirStepNode.fail .ub` unless every
  uninitialized byte falls strictly within aggregate padding of `dst`'s layout.

Reference (`core::intrinsics::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.copy_nonoverlapping.html>

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The following is a non-exhaustive list of invalid values:
> - A value of any type, other than a union or raw pointer, with uninitialized
>   bytes (except for padding bytes, which may be uninitialized)."
-/
def evalCopyUnionBytes
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (srcUnionOpt dstUnionOpt : Option UnionPlaceInfo)
    (n : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  let elemBytesOpt : Option Nat :=
    match operandPointeeTy localDecls layouts src with
    | .some pt => rigidTyByteSize layouts pt
    | .none =>
      match operandPointeeTy localDecls layouts dst with
      | .some pt => rigidTyByteSize layouts pt
      | .none => .some 1
  match elemBytesOpt with
  | .none => MirStepNode.fail .ub
  | .some elemSz =>
    let copyByteLen := Nat.mul n elemSz
    let srcAlign := operandPointeeAlign localDecls layouts src
    let dstAlign := operandPointeeAlign localDecls layouts dst
    let srcSliceRes : UnionSrcSliceResult :=
      match srcUnionOpt with
      | .some srcInfo =>
        match get? locals₃ srcEntry.targetLocal with
        | .none => .ub
        | .some .dead => .ub
        | .some srcSlot =>
          let srcFields : List Value :=
            match srcSlot with
            | .init (.aggregate _ fs) => fs
            | .init otherVal => otherVal :: .nil
            | _ => .nil
          let srcEffStart :=
            Nat.add srcInfo.subBaseOffset srcPtr.offsetBytes
          let srcBoundsOk :=
            Bool.and
              (isAlignedOffset srcEffStart srcAlign)
              (Bool.and
                (Nat.ble
                  (Nat.add srcPtr.offsetBytes copyByteLen)
                  srcInfo.placeByteBound)
                (Nat.ble
                  (Nat.add srcEffStart copyByteLen)
                  srcInfo.unionBytes))
          match srcBoundsOk with
          | false => .ub
          | true =>
            let srcStorageBytes :=
              encodeUnionStorageBytes
                layouts
                srcInfo.unionBytes
                srcInfo.fieldTarget
                srcFields
            match
              sliceAbstractBytes srcStorageBytes srcEffStart copyByteLen
            with
            | .some copied => .ok copied true srcEffStart
            | .none => .ub
      | .none =>
        let srcInFrame : Bool :=
          match get? locals₃ srcEntry.targetLocal with
          | .some _ => true
          | .none => false
        let srcRootSlot : Option LocalSlot :=
          match get? locals₃ srcEntry.targetLocal with
          | .some slot => .some slot
          | .none =>
            match get? s.memory.callerLocals srcEntry.targetLocal with
            | .some slot => .some slot
            | .none =>
              get?
                s.memory.callerLocals
                (Nat.sub srcEntry.targetLocal (length locals₃))
        match srcRootSlot with
        | .some (.init srcRootVal) =>
          match isAlignedOffset srcPtr.offsetBytes srcAlign with
          | false => .ub
          | true =>
            match
              readProjectedValue
                locals₃
                srcRootVal
                srcEntry.targetProjection
            with
            | .ub => .ub
            | .unsupported => .unsupported
            | .ok srcSubVal =>
              let srcPlace : Place := {
                local_ := srcEntry.targetLocal
                projection := srcEntry.targetProjection
              }
              let srcPlaceTyOpt : Option Ty :=
                match srcInFrame with
                | true => placeTy localDecls layouts srcPlace
                | false => .none
              let fullSrcBytesOpt : Option (List AbstractByte) :=
                match srcPlaceTyOpt with
                | .some sTy =>
                  match
                    encodeValueToBytes defaultCodecFuel layouts sTy srcSubVal
                  with
                  | .some bs => .some bs
                  | .none =>
                    encodeUntypedValueToBytes defaultCodecFuel srcSubVal
                | .none =>
                  encodeUntypedValueToBytes defaultCodecFuel srcSubVal
              match fullSrcBytesOpt with
              | .none => .unsupported
              | .some fullSrcBytes =>
                match
                  sliceAbstractBytes
                    fullSrcBytes
                    srcPtr.offsetBytes
                    copyByteLen
                with
                | .some copied => .ok copied srcInFrame srcPtr.offsetBytes
                | .none => .ub
        | _ => .ub
    match srcSliceRes with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok copiedBytes srcInFrame srcEffStart =>
      match dstUnionOpt with
      | .some dstInfo =>
        match get? locals₃ dstEntry.targetLocal with
        | .none => MirStepNode.fail .ub
        | .some .dead => MirStepNode.fail .ub
        | .some dstSlot =>
          let (dstVar, dstFields) : VariantIdx × List Value :=
            match dstSlot with
            | .init (.aggregate vIdx fs) => (vIdx, fs)
            | .init otherVal => (0, otherVal :: .nil)
            | _ => (0, .nil)
          let dstEffStart :=
            Nat.add dstInfo.subBaseOffset dstPtr.offsetBytes
          let dstBoundsOk :=
            Bool.and
              (isAlignedOffset dstEffStart dstAlign)
              (Bool.and
                (Nat.ble
                  (Nat.add dstPtr.offsetBytes copyByteLen)
                  dstInfo.placeByteBound)
                (Nat.ble
                  (Nat.add dstEffStart copyByteLen)
                  dstInfo.unionBytes))
          let disjointOk :=
            match
              Bool.and
                srcInFrame
                (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
            with
            | false => true
            | true =>
              rangesDisjoint
                srcEffStart
                copyByteLen
                dstEffStart
                copyByteLen
          match Bool.and dstBoundsOk disjointOk with
          | false => MirStepNode.fail .ub
          | true =>
            let dstStorageBytes :=
              encodeUnionStorageBytes
                layouts
                dstInfo.unionBytes
                dstInfo.fieldTarget
                dstFields
            match
              writeAbstractBytesAt dstStorageBytes dstEffStart copiedBytes
            with
            | .none => MirStepNode.fail .ub
            | .some updatedUnionBytes =>
              let newUnionVal : Value :=
                match dstInfo.fieldTarget with
                | .some (dstFieldIdx, dstFieldTy, dstFieldBytes) =>
                  match
                    sliceAbstractBytes updatedUnionBytes 0 dstFieldBytes
                  with
                  | .some updatedFieldBytes =>
                    match
                      decodeValueFromBytes
                        defaultCodecFuel
                        layouts
                        dstFieldTy
                        updatedFieldBytes
                    with
                    | .some decodedFieldVal =>
                      Value.aggregate
                        dstVar
                        (setOrExtendFields
                          (resetUnionFields dstFields)
                          dstFieldIdx
                          decodedFieldVal)
                    | .none =>
                      Value.aggregate dstVar (resetUnionFields dstFields)
                  | .none =>
                    Value.aggregate dstVar (resetUnionFields dstFields)
                | .none =>
                  let decodedRootOpt : Option Value :=
                    match get? localDecls dstEntry.targetLocal with
                    | .some decl =>
                      decodeValueFromBytes
                        defaultCodecFuel
                        layouts
                        decl.ty
                        updatedUnionBytes
                    | .none => .none
                  match decodedRootOpt with
                  | .some decodedUnionVal => decodedUnionVal
                  | .none =>
                    Value.aggregate dstVar (resetUnionFields dstFields)
              match
                set? locals₃ dstEntry.targetLocal (.init newUnionVal)
              with
              | .none => MirStepNode.fail .ub
              | .some locals₄ =>
                let borrows' :=
                  invalidateConflictingBorrows
                    s.memory.borrows
                    dstEntry.targetLocal
                    (.some dstPtr.tag)
                    (length s.memory.callStack)
                MirStepNode.step
                  (advanceStmt
                    s
                    locals₄
                    { s.memory with borrows := borrows' })
      | .none =>
        let dstStart := dstPtr.offsetBytes
        let overlaps :=
          match
            Bool.and
              (Nat.beq srcPtr.tag dstPtr.tag)
              (Bool.not (Nat.beq copyByteLen 0))
          with
          | true => true
          | false =>
            match
              Bool.and
                srcInFrame
                (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
            with
            | true => Bool.not (Nat.beq copyByteLen 0)
            | false => false
        match
          Bool.and
            (isAlignedOffset dstStart dstAlign)
            (Bool.not overlaps)
        with
        | false => MirStepNode.fail .ub
        | true =>
          let dstPlace : Place := {
            local_ := dstEntry.targetLocal
            projection := dstEntry.targetProjection
          }
          let dstInFrame : Bool :=
            match get? locals₃ dstPlace.local_ with
            | .some _ => true
            | .none => false
          let dstLocalPlaceTy : Option Ty :=
            match dstInFrame with
            | true => placeTy localDecls layouts dstPlace
            | false => .none
          let dstIsAdt : Bool :=
            match dstLocalPlaceTy with
            | .some { kind := .adt _ _, .. } => true
            | _ => false
          let dstTargetTyOpt : Option Ty :=
            match dstLocalPlaceTy with
            | .some t => .some t
            | .none => operandPointeeTy localDecls layouts dst
          let dstRootSlot : Option LocalSlot :=
            match get? locals₃ dstEntry.targetLocal with
            | .some slot => .some slot
            | .none =>
              match get? s.memory.callerLocals dstEntry.targetLocal with
              | .some slot => .some slot
              | .none =>
                get?
                  s.memory.callerLocals
                  (Nat.sub dstEntry.targetLocal (length locals₃))
          match dstRootSlot with
          | .none => MirStepNode.fail .ub
          | .some .dead => MirStepNode.fail .ub
          | .some .uninit =>
            match dstPlace.projection, Nat.beq dstStart 0, dstTargetTyOpt with
            | .nil, true, .some dstPt =>
              match rigidTyByteSize layouts dstPt with
              | .some dstBytes =>
                match Nat.beq copyByteLen dstBytes with
                | false => MirStepNode.fail .ub
                | true =>
                  match
                    decodeValueFromBytes
                      defaultCodecFuel
                      layouts
                      dstPt
                      copiedBytes
                  with
                  | .some decodedVal =>
                    commitCopyDstPlaceWrite
                      s
                      dstPlace
                      dstEntry.targetLocal
                      dstPtr.tag
                      locals₃
                      decodedVal
                      localDecls
                      layouts
                  | .none => MirStepNode.fail .ub
              | .none => MirStepNode.fail .ub
            | _, _, _ => MirStepNode.fail .ub
          | .some (.init dstRootVal) =>
            match
              readProjectedValue
                locals₃
                dstRootVal
                dstEntry.targetProjection
            with
            | .unsupported => MirStepNode.unsupported
            | .ub =>
              match Nat.beq dstStart 0, dstTargetTyOpt with
              | true, .some dstPt =>
                match rigidTyByteSize layouts dstPt with
                | .some dstBytes =>
                  match Nat.beq copyByteLen dstBytes with
                  | false => MirStepNode.fail .ub
                  | true =>
                    match
                      decodeValueFromBytes
                        defaultCodecFuel
                        layouts
                        dstPt
                        copiedBytes
                    with
                    | .some decodedVal =>
                      commitCopyDstPlaceWrite
                        s
                        dstPlace
                        dstEntry.targetLocal
                        dstPtr.tag
                        locals₃
                        decodedVal
                        localDecls
                        layouts
                    | .none => MirStepNode.fail .ub
                | .none => MirStepNode.fail .ub
              | _, _ => MirStepNode.fail .ub
            | .ok dstSubVal =>
              let spliceBytesToDstArray : Option Value :=
                match Bool.not dstIsAdt, dstSubVal with
                | true, .aggregate 0 dstElems =>
                  match
                    Nat.ble
                      (Nat.add dstStart copyByteLen)
                      (length dstElems)
                  with
                  | false => .none
                  | true =>
                    match
                      decodeArrayChunksWith
                        (fun chunk =>
                          decodeValueFromBytes
                            defaultCodecFuel
                            layouts
                            { kind := .uint .u8, layoutIdx := 0 }
                            chunk)
                        1
                        copyByteLen
                        copiedBytes
                    with
                    | .some decodedByteVals =>
                      .some
                        (.aggregate 0
                          (spliceValues decodedByteVals dstStart dstElems))
                    | .none => .none
                | _, _ => .none
              match dstTargetTyOpt with
              | .some dstPt =>
                match
                  encodeValueToBytes defaultCodecFuel layouts dstPt dstSubVal
                with
                | .some dstOldBytes =>
                  match
                    writeAbstractBytesAt dstOldBytes dstStart copiedBytes
                  with
                  | .none => MirStepNode.fail .ub
                  | .some updatedDstBytes =>
                    match
                      decodeValueFromBytes
                        defaultCodecFuel
                        layouts
                        dstPt
                        updatedDstBytes
                    with
                    | .some decodedVal =>
                      commitCopyDstPlaceWrite
                        s
                        dstPlace
                        dstEntry.targetLocal
                        dstPtr.tag
                        locals₃
                        decodedVal
                        localDecls
                        layouts
                    | .none => MirStepNode.fail .ub
                | .none =>
                  match spliceBytesToDstArray with
                  | .some splicedVal =>
                    commitCopyDstPlaceWrite
                      s
                      dstPlace
                      dstEntry.targetLocal
                      dstPtr.tag
                      locals₃
                      splicedVal
                      localDecls
                      layouts
                  | .none => MirStepNode.fail .ub
              | .none =>
                match spliceBytesToDstArray with
                | .some splicedVal =>
                  commitCopyDstPlaceWrite
                    s
                    dstPlace
                    dstEntry.targetLocal
                    dstPtr.tag
                    locals₃
                    splicedVal
                    localDecls
                    layouts
                | .none => MirStepNode.fail .ub

/--
`copy_nonoverlapping` source and destination borrow targets both lie in the
active frame. With an empty `callStack` (root frame active) this always holds
(every live tag then targets depth `0`). Inside an inline callee, when a source
or destination tag was minted in a suspended caller frame
(`BorrowEntry.targetFrameDepth < length callStack`), `evalCopyNonOverlappingWithCount`
routes single-element direct copies through `evalForeignFrameCopySingleDirect`
(`DIV-MR-CALL-TARGET-LOCAL`).
-/
def copyEntriesTargetActiveFrame
    (callStack : List SavedCallerFrame)
    (srcEntry dstEntry : BorrowEntry) :
    Bool :=
  match callStack with
  | .nil => true
  | _ :: _ =>
    Bool.and
      (Nat.beq srcEntry.targetFrameDepth (length callStack))
      (Nat.beq dstEntry.targetFrameDepth (length callStack))

/--
Tree Borrows read-then-write check and permission transition for a single-element
direct `copy_nonoverlapping` from `(srcPtr, srcEntry)` to `(dstPtr, dstEntry)`:
checks source read UB (`hasTreeReadUB`), applies the source read transition
(`freezeTreeBorrowsOnReadAtProj` / `updateBorrowPermOnReadAtProj`), checks
destination ancestor write UB (`treeBorrowAncestorsChildAccessUB .write`) and
active function-entry protectors (`hasProtectedTreeWriteConflict` /
`hasProtectedWriteConflict`), and applies the projection- and tree-aware write
transition (`invalidateTreeBorrowsAtProj` / `invalidateConflictingBorrowsAtProj`
/ `invalidateConflictingBorrows`). Returns `.none` on any Tree Borrows UB.
-/
def borrowsAfterCopySingleDirect
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry) :
    Option (List BorrowEntry) :=
  let readUB : Bool :=
    match borrows with
    | b₁ :: b₂ :: restBorrows =>
      let allBorrows := b₁ :: b₂ :: restBorrows
      hasTreeReadUB
        allBorrows
        allBorrows
        activeProtectors
        srcEntry.targetLocal
        (.some srcPtr.tag)
        srcEntry.targetProjection
        srcEntry.rangeOffset
        srcEntry.rangeLen
        srcEntry.targetFrameDepth
    | _ => false
  match readUB with
  | true => .none
  | false =>
    let borrowsAfterRead : List BorrowEntry :=
      match borrows with
      | .nil => .nil
      | single :: .nil =>
        updateBorrowPermOnReadAtProj
          (single :: .nil)
          single
          srcEntry.targetLocal
          (.some srcPtr.tag)
          srcEntry.targetProjection
          srcEntry.rangeOffset
          srcEntry.rangeLen
          activeProtectors
          srcEntry.targetFrameDepth :: .nil
      | b₁ :: b₂ :: restBorrows =>
        let allBorrows := b₁ :: b₂ :: restBorrows
        freezeTreeBorrowsOnReadAtProj
          allBorrows
          allBorrows
          srcEntry.targetLocal
          (.some srcPtr.tag)
          srcEntry.targetProjection
          srcEntry.rangeOffset
          srcEntry.rangeLen
          activeProtectors
          srcEntry.targetFrameDepth
    let dstWriteTreeUB : Bool :=
      match borrowsAfterRead with
      | .nil => false
      | single :: .nil =>
        match lookupBorrow (single :: .nil) dstPtr.tag with
        | .some dEntryAfter =>
          match dEntryAfter.perm with
          | .frozen | .disabled => true
          | _ => false
        | .none => true
      | b₁ :: b₂ :: restBorrows =>
        let allBorrows := b₁ :: b₂ :: restBorrows
        match lookupBorrow allBorrows dstPtr.tag with
        | .some dEntryAfter =>
          match dEntryAfter.perm with
          | .frozen | .disabled => true
          | _ => treeBorrowAncestorsChildAccessUB .write allBorrows dEntryAfter.parentTag
        | .none => true
    match dstWriteTreeUB with
    | true => .none
    | false =>
      let protConflict : Bool :=
        match activeProtectors with
        | .nil => false
        | _ :: _ =>
          match borrowsAfterRead with
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            hasProtectedTreeWriteConflict
              allBorrows
              allBorrows
              activeProtectors
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEntry.targetProjection
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
          | _ =>
            hasProtectedWriteConflict
              borrowsAfterRead
              activeProtectors
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEntry.targetProjection
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
      match protConflict with
      | true => .none
      | false =>
        let borrows' : List BorrowEntry :=
          match borrowsAfterRead with
          | .nil => .nil
          | single :: .nil =>
            let b := single :: .nil
            match dstEntry.targetProjection with
            | .nil =>
              match Nat.beq dstEntry.rangeLen 0 with
              | true =>
                invalidateConflictingBorrows
                  b
                  dstEntry.targetLocal
                  (.some dstPtr.tag)
                  dstEntry.targetFrameDepth
              | false =>
                invalidateConflictingBorrowsAtProj
                  b
                  dstEntry.targetLocal
                  (.some dstPtr.tag)
                  .nil
                  dstEntry.rangeOffset
                  dstEntry.rangeLen
                  dstEntry.targetFrameDepth
            | pHead :: pTail =>
              invalidateConflictingBorrowsAtProj
                b
                dstEntry.targetLocal
                (.some dstPtr.tag)
                (pHead :: pTail)
                dstEntry.rangeOffset
                dstEntry.rangeLen
                dstEntry.targetFrameDepth
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            invalidateTreeBorrowsAtProj
              allBorrows
              allBorrows
              dstEntry.targetLocal
              (.some dstPtr.tag)
              dstEntry.targetProjection
              dstEntry.rangeOffset
              dstEntry.rangeLen
              dstEntry.targetFrameDepth
        .some borrows'

/--
Whether every element of `elems` is the zero-sized `Value.unit` (vacuously
`true` on `.nil`).
-/
@[reducible]
def allUnitValues : List Value → Bool
  | .nil => true
  | .unit :: rest => allUnitValues rest
  | _ :: _ => false

/--
Whether `elems` is non-empty and every element is the zero-sized `Value.unit`:
the runtime witness of a zero-sized element type when no static pointee type is
in scope. Unlike `allUnitValues`, an empty list is not a witness.
-/
@[reducible]
def nonEmptyAllUnitValues : List Value → Bool
  | .nil => false
  | .unit :: rest => allUnitValues rest
  | _ :: _ => false

/--
Whether every element of `elems` occupies exactly `elemSz` bytes: for
`elemSz = 0` every element must be `Value.unit` (`allUnitValues`), otherwise
every element must have byte size `elemSz` (`elemsHaveUniformByteStride`).
-/
@[reducible]
def elemsMatchByteStride (elems : List Value) (elemSz : Nat) : Bool :=
  match Nat.beq elemSz 0 with
  | true => allUnitValues elems
  | false => elemsHaveUniformByteStride elems elemSz

/--
Whether every element of `elems` is a one-byte scalar.
-/
@[reducible]
def elemsAreByteScalars : List Value → Bool
  | .nil => true
  | .scalar sc :: rest =>
    match Nat.beq sc.sizeBytes 1 with
    | true => elemsAreByteScalars rest
    | false => false
  | _ :: _ => false

/--
One endpoint (`src` or `dst`) of a multi-element or sub-place
`copy_nonoverlapping`: the pointer value `ptr`, its live borrow `entry`, the
optional initialized root value `rootValOpt` of the local (or caller-owned
referent) that `entry` targets (`.some v` when the root slot is `.init v`,
`.none` when it is `.uninit`), and the operand's static pointee type
`pointeeOpt` when known.
-/
structure CopyEndpoint : Type where
  /-- Pointer value of the operand. -/
  ptr : ProvenancePtr
  /-- Borrow entry of `ptr.tag`. -/
  entry : BorrowEntry
  /-- Initialized root value of `entry.targetLocal`, or `.none` when `.uninit`. -/
  rootValOpt : Option Value
  /-- Static pointee type of the operand (`operandPointeeTy`), when known. -/
  pointeeOpt : Option Ty

/--
Outcome of resolving a multi-element or sub-place `copy_nonoverlapping`
(`resolveCopySubplaceMulti`) before it is committed to the machine state.
-/
inductive CopySliceOutcome : Type where
  /-- The copy is undefined behavior. -/
  | ub : CopySliceOutcome
  /-- The copy is not modeled (fail closed). -/
  | unsupported : CopySliceOutcome
  /-- The copy transfers zero bytes: no memory or borrow-state effect. -/
  | noop : CopySliceOutcome
  /-- Write `newVal` to `dstPlace`, after the Tree Borrows read of the source
      place `srcWindowProj` and write of the destination place `dstWindowProj`
      (projections relative to each borrow's target local). -/
  | write
      (dstPlace : Place)
      (newVal : Value)
      (srcWindowProj dstWindowProj : List ProjectionElem) :
      CopySliceOutcome

/--
Static byte size `size_of::<T>()` of the pointee `T` of a
`copy_nonoverlapping::<T>` whose operands have static pointee types
`srcPtOpt` / `dstPtOpt` (`tyByteSize`), when either is known.
-/
@[reducible]
def copyPointeeByteSize?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtOpt dstPtOpt : Option Ty) :
    Option Nat :=
  let srcSzOpt : Option Nat :=
    match srcPtOpt with
    | .some srcPt => tyByteSize localDecls layouts srcPt
    | .none => .none
  match srcSzOpt with
  | .some sz => .some sz
  | .none =>
    match dstPtOpt with
    | .some dstPt => tyByteSize localDecls layouts dstPt
    | .none => .none

/--
Whether the static pointee sizes of the two operands of a `copy_nonoverlapping`
are both known and differ (ill-typed for a single type parameter `T`).
-/
@[reducible]
def copyPointeeSizesConflict
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtOpt dstPtOpt : Option Ty) :
    Bool :=
  match srcPtOpt, dstPtOpt with
  | .some srcPt, .some dstPt =>
    match tyByteSize localDecls layouts srcPt, tyByteSize localDecls layouts dstPt with
    | .some a, .some b => Bool.not (Nat.beq a b)
    | _, _ => false
  | _, _ => false

/--
Whether the place `⟨loc, proj⟩` of an active-frame local is statically a struct,
enum, or tuple (`RigidTy.adt` / `RigidTy.tuple`), i.e. an aggregate whose
`Value.aggregate 0 fields` representation is not a sequence of equally sized
elements. `false` for caller-owned referents and untyped places.
-/
@[reducible]
def copyPlaceIsNonArrayAggregate
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (loc : Local)
    (proj : List ProjectionElem) :
    Bool :=
  match get? locals loc with
  | .none => false
  | .some _ =>
    match placeTy localDecls layouts { local_ := loc, projection := proj } with
    | .some { kind := .adt _ _, .. } => true
    | .some { kind := .tuple _, .. } => true
    | _ => false

/--
Static element kind of the array or slice place `⟨loc, parentProj⟩` of an
active-frame local (`RigidTy.array ek _` / `RigidTy.slice ek`), when known.
-/
@[reducible]
def copyContainerElemKind?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (loc : Local)
    (parentProj : List ProjectionElem) :
    Option RigidTy :=
  match get? locals loc with
  | .none => .none
  | .some _ =>
    match placeTy localDecls layouts { local_ := loc, projection := parentProj } with
    | .some { kind := .array ek _, .. } => .some ek
    | .some { kind := .slice ek, .. } => .some ek
    | _ => .none

/--
Resolve the array or slice that the endpoint `ep` of a multi-element
`copy_nonoverlapping` points into, as `(parentProj, baseIdx, elems)`: the
projection of the container within `ep.entry.targetLocal`, the element index of
the pointed-to place inside it, and its element values.

- When the borrow's projection ends with a forward
  `.constantIndex idx minLen false` (an element pointer such as
  `&raw const a[idx]`) and the enclosing place reads as `.aggregate 0 elems`,
  is not statically a struct or tuple, and contains index `idx`, the container
  is the enclosing array with `baseIdx = idx` (`splitLastConstantIndex?`). If
  the element is itself a sequence and only its own elements have the copied
  element size `elemSzOpt`, the element is the container instead.
- Otherwise, when the pointed-to place itself reads as `.aggregate 0 elems` and
  is not statically a struct or tuple, it is the container with `baseIdx = 0`.
- Otherwise the endpoint is not an array (`.none`), and the copy is evaluated
  on bytes.

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "src must be valid for reads of count * size_of::<T>() bytes or that number must be 0."
> "dst must be valid for writes of count * size_of::<T>() bytes or that number must be 0."

Reference (The Rust Reference 1.98.0, "Array layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#array-layout>

> "An array of [T; N] has a size of size_of::<T>() * N and the same alignment of T. Arrays are laid out so that the zero-based nth element of the array is offset from the start of the array by n * size_of::<T>() bytes."

Justification: an access of `count * size_of::<T>()` bytes starting at element
`idx` of an array of `T` covers exactly the elements `idx .. idx + count`,
because consecutive elements are `size_of::<T>()` bytes apart. Resolving the
enclosing array turns the byte access into an element window; the caller checks
that the elements really have the copied element size (`copyContainerStrideOk`)
before using that window.

Modeling assumptions and unsupported behavior: `fromEnd` constant indices and
dynamic indices whose index local is not an initialized scalar are not peeled;
a struct or tuple is never treated as a sequence when its static type is known.
-/
def resolveArraySliceEndpoint?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (ep : CopyEndpoint)
    (elemSzOpt : Option Nat) :
    Option (List ProjectionElem × Nat × List Value) :=
  match ep.rootValOpt with
  | .none => .none
  | .some rootVal =>
    let resolvedProj : List ProjectionElem :=
      match resolveBorrowProjectionElems locals ep.entry.targetProjection with
      | .some rp => normalizeSubsliceProjections rp
      | .none => ep.entry.targetProjection
    let direct : Option (List ProjectionElem × Nat × List Value) :=
      match
        copyPlaceIsNonArrayAggregate localDecls layouts locals ep.entry.targetLocal resolvedProj
      with
      | true => .none
      | false =>
        match readProjectedValue locals rootVal resolvedProj with
        | .ok (.aggregate 0 elems) => .some (resolvedProj, 0, elems)
        | _ => .none
    match splitLastConstantIndex? resolvedProj with
    | .none => direct
    | .some (initProj, idx, minLen) =>
      match
        copyPlaceIsNonArrayAggregate localDecls layouts locals ep.entry.targetLocal initProj
      with
      | true => direct
      | false =>
        match readProjectedValue locals rootVal initProj with
        | .ok (.aggregate 0 outerElems) =>
          match
            Bool.and
              (Nat.ble minLen (length outerElems))
              (Nat.blt idx (length outerElems))
          with
          | false => direct
          | true =>
            match direct, elemSzOpt with
            | .some (innerProj, innerIdx, innerElems), .some elemSz =>
              match
                elemsMatchByteStride outerElems elemSz,
                elemsMatchByteStride innerElems elemSz
              with
              | false, true => .some (innerProj, innerIdx, innerElems)
              | _, _ => .some (initProj, idx, outerElems)
            | _, _ => .some (initProj, idx, outerElems)
        | _ => direct

/--
Element-stride guard for one container of a multi-element `copy_nonoverlapping`
(`copySliceStrideOk`): whether an element of the container occupies exactly one
copied element.

- When the container's static element kind `elemKindOpt` and the operand's
  pointee type `pointeeOpt` are both known, the element kind must have the
  pointee's value shape (`sameRigidTyShape`) or be a primitive scalar of the
  copied element size.
- Otherwise (an untyped container, e.g. a caller-owned referent), every element
  value must have the copied element size `elemSzOpt` (`elemsMatchByteStride`).

Reference (The Rust Reference 1.98.0, "Array layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#array-layout>

> "An array of [T; N] has a size of size_of::<T>() * N and the same alignment of T. Arrays are laid out so that the zero-based nth element of the array is offset from the start of the array by n * size_of::<T>() bytes."

Justification: transferring `count` element values is the same as copying
`count * size_of::<T>()` bytes only if each element value occupies
`size_of::<T>()` bytes at the stride of the array. When this guard fails the
copy is type-punned across element boundaries and is not evaluated on element
values.

Modeling assumption: a primitive scalar of equal size is accepted because the
model represents every primitive scalar as `Value.scalar` of that byte size.
-/
@[reducible]
def copyContainerStrideOk
    (elemKindOpt : Option RigidTy)
    (pointeeOpt : Option Ty)
    (elems : List Value)
    (elemSzOpt : Option Nat) :
    Bool :=
  match elemKindOpt, pointeeOpt with
  | .some ek, .some pt =>
    match sameRigidTyShape ek pt.kind with
    | true => true
    | false =>
      match isPrimitiveScalarKind ek, rigidTyKindByteSize ek, elemSzOpt with
      | true, .some ekSz, .some elemSz => Nat.beq ekSz elemSz
      | _, _, _ => false
  | _, _ =>
    match elemSzOpt with
    | .some elemSz => elemsMatchByteStride elems elemSz
    | .none => false

/--
Element byte size used to convert pointer byte offsets to element indices: the
static pointee size `elemSzOpt` when known, otherwise the byte size of the first
element value of the source (else destination) container.
-/
@[reducible]
def copyEffElemSize?
    (elemSzOpt : Option Nat)
    (srcElems dstElems : List Value) :
    Option Nat :=
  match elemSzOpt with
  | .some sz => .some sz
  | .none =>
    match srcElems with
    | e :: _ => inferValueByteSizeAux 8 e
    | .nil =>
      match dstElems with
      | e :: _ => inferValueByteSizeAux 8 e
      | .nil => .none

/--
Projection of the element window `start .. start + n` of the container
`parentProj` whose length is `len`: `parentProj` itself when the window covers
the whole container, and `parentProj` followed by
`.subslice start (start + n) false` otherwise.
-/
@[reducible]
def copySliceWindowProj
    (parentProj : List ProjectionElem)
    (start n len : Nat) :
    List ProjectionElem :=
  match Bool.and (Nat.beq start 0) (Nat.beq n len) with
  | true => parentProj
  | false => appendProjections parentProj (.subslice start (Nat.add start n) false :: .nil)

/--
Tree Borrows read-then-write check and permission transition for a
multi-element or byte-level `copy_nonoverlapping` that reads the source place
`srcWindowProj` and writes the destination place `dstWindowProj` (both relative
to their borrow's target local): `borrowsAfterCopySingleDirect` on the borrow
entries re-targeted at the accessed windows, with no byte sub-range
(`rangeLen := 0`). Returns `.none` on any Tree Borrows undefined behavior.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Breaking the pointer aliasing rules. The exact aliasing rules are not determined yet, but here is an outline of the general principles:"
> "&T must point to memory that is not mutated while they are live (except for data inside an UnsafeCell<U>), and &mut T must point to memory that is not read or written by any pointer not derived from the reference and that no other reference points to while they are live."

Justification: the copy reads every byte of the source window through `srcPtr`
and writes every byte of the destination window through `dstPtr`, so the
aliasing state must be checked and updated for those whole windows, not only
for the single element the pointers were derived from.

Modeling assumption: the aliasing model is Tree Borrows as implemented by
`borrowsAfterCopySingleDirect`; the Reference states the aliasing rules only in
outline.
-/
def borrowsAfterCopySlice
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (srcWindowProj dstWindowProj : List ProjectionElem) :
    Option (List BorrowEntry) :=
  borrowsAfterCopySingleDirect
    borrows
    activeProtectors
    srcPtr
    dstPtr
    { srcEntry with targetProjection := srcWindowProj, rangeOffset := 0, rangeLen := 0 }
    { dstEntry with targetProjection := dstWindowProj, rangeOffset := 0, rangeLen := 0 }

/--
Whether an access of `accessBytes` bytes through the endpoint `ep`
(`ep.ptr.offsetBytes` bytes past the place `ep.entry` borrows) lies inside the
allocation of the local it targets: `.some true` when it certainly does,
`.some false` when it certainly does not, and `.none` when the allocation size
or the place offset is unknown.

The allocation size is `tyByteSize` of the declared type for a declared
active-frame local and `valueDefaultByteSize` of `ep.rootValOpt` otherwise (an
untyped or caller-owned initialized target); the offset of the borrowed place is
`borrowPlaceByteOffset?`, falling back to `projectionChainByteOffset?` on the
runtime value only for an undeclared initialized target (never for a declared
local whose layout lacks field offsets).

Reference (`core::ptr`, "Safety", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/index.html#safety>

> "For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that the pointer be dereferenceable. The provenance of the pointer is used to determine which allocation it is derived from; a pointer is dereferenceable if the memory range of the given size starting at the pointer is entirely contained within the bounds of that allocation. Note that in Rust, every (stack-allocated) variable is considered a separate allocation."

Justification: `.some false` states that the accessed memory range is not
"entirely contained within the bounds of that allocation", so the pointer is
not dereferenceable for the access, which is a necessary condition for validity;
the caller turns only this answer into undefined behavior. `.some true` is
necessary but "not always sufficient" for validity, so the caller never treats
it as permission by itself.

Modeling assumptions: the allocation of a pointer into a local is that whole
local ("every (stack-allocated) variable is considered a separate allocation");
for an untyped target the size and offsets are inferred from the runtime value.
-/
def copyAccessFitsAlloc?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (ep : CopyEndpoint)
    (accessBytes : Nat) :
    Option Bool :=
  let declTyOpt : Option Ty :=
    match get? locals ep.entry.targetLocal, get? localDecls ep.entry.targetLocal with
    | .some _, .some decl => .some decl.ty
    | _, _ => .none
  let rootBytesOpt : Option Nat :=
    match declTyOpt with
    | .some declTy => tyByteSize localDecls layouts declTy
    | .none =>
      match ep.rootValOpt with
      | .some rootVal => valueDefaultByteSize rootVal
      | .none => .none
  let resolvedEntry : BorrowEntry :=
    match resolveBorrowProjectionElems locals ep.entry.targetProjection with
    | .some rp => { ep.entry with targetProjection := rp }
    | .none => ep.entry
  let placeOffOpt : Option Nat :=
    match borrowPlaceByteOffset? locals callerLocals localDecls layouts resolvedEntry callStack with
    | .some off => .some off
    | .none =>
      match declTyOpt, ep.rootValOpt with
      | .none, .some rootVal =>
        projectionChainByteOffset?
          layouts
          .none
          (.some rootVal)
          .none
          0
          .nil
          (normalizeSubsliceProjections
            (stripTransparentProjections resolvedEntry.targetProjection))
      | _, _ => .none
  match rootBytesOpt, placeOffOpt with
  | .some rootBytes, .some placeOff =>
    .some
      (Nat.ble
        (Nat.add (Nat.add placeOff ep.ptr.offsetBytes) accessBytes)
        rootBytes)
  | _, _ => .none

/--
`true` exactly when `fitsOpt` (`copyAccessFitsAlloc?`) reports an access that is
certainly outside its allocation.
-/
@[reducible]
def copyAccessCertainlyOob : Option Bool → Bool
  | .some false => true
  | _ => false

/--
Element-window path of a multi-element `copy_nonoverlapping` whose endpoints
both point into arrays or slices (`resolveArraySliceEndpoint?`): the source
container is `srcElems` at `srcParentProj` with the pointer at element
`srcBaseIdx`, and likewise for the destination.

- A copy between containers of zero-sized `Value.unit` elements without a
  static pointee type is a no-op.
- Pointer byte offsets are converted to element indices
  (`byteOffsetToElemIdx?`); an offset that is not a whole number of elements is
  not modeled (`.unsupported`; alignment was already checked).
- When a window exceeds its container, the copy is undefined behavior if an
  access is certainly outside its allocation (`copyAccessFitsAlloc?`), or if
  that is unknown and the exceeded container is the root local itself with an
  exact, non-zero element stride; otherwise it stays inside the allocation or
  is type-punned and is not modeled (`.unsupported`).
- When both windows are in bounds, the element stride must be exact
  (`copyContainerStrideOk`, else `.unsupported`), the windows must not overlap
  (else `.ub`), and the source window is spliced into the destination container;
  the outcome names the two accessed windows for the Tree Borrows
  read-then-write transition (`borrowsAfterCopySlice`, applied by
  `evalCopySubplaceMulti`).

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "src must be valid for reads of count * size_of::<T>() bytes or that number must be 0."
> "dst must be valid for writes of count * size_of::<T>() bytes or that number must be 0."
> "The region of memory beginning at src with a size of count * size_of::<T>() bytes must not overlap with the region of memory beginning at dst with the same size."

Reference (`core::ptr`, "Safety", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/index.html#safety>

> "For memory accesses of size zero, every non-null pointer is valid for reads/writes."
> "For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that the pointer be dereferenceable. The provenance of the pointer is used to determine which allocation it is derived from; a pointer is dereferenceable if the memory range of the given size starting at the pointer is entirely contained within the bounds of that allocation. Note that in Rust, every (stack-allocated) variable is considered a separate allocation."

Justification: the copy accesses `count * size_of::<T>()` bytes at each pointer;
with an exact element stride those bytes are the element windows
`start .. start + count`. Undefined behavior is reported only for an access
that is certainly not contained in its allocation (a necessary condition for
validity fails), for overlapping windows, and for an aliasing violation. A
window that leaves its container but may stay inside the allocation (a nested
array, a type-punned element size) is never reported as undefined behavior.

Modeling assumptions and unsupported behavior: tags are compared as in the
single-element path (a copy between two pointers with the same tag is
undefined behavior); in-allocation overruns of a nested array and type-punned
element sizes fail closed with `.unsupported`.
-/
def copySliceElements
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (srcEp dstEp : CopyEndpoint)
    (elemSzOpt : Option Nat)
    (n : Nat)
    (srcParentProj : List ProjectionElem)
    (srcBaseIdx : Nat)
    (srcElems : List Value)
    (dstParentProj : List ProjectionElem)
    (dstBaseIdx : Nat)
    (dstElems : List Value) :
    CopySliceOutcome :=
  let effSzOpt := copyEffElemSize? elemSzOpt srcElems dstElems
  let strideOk : Bool :=
    Bool.and
      (copyContainerStrideOk
        (copyContainerElemKind? localDecls layouts locals srcEp.entry.targetLocal srcParentProj)
        srcEp.pointeeOpt
        srcElems
        effSzOpt)
      (copyContainerStrideOk
        (copyContainerElemKind? localDecls layouts locals dstEp.entry.targetLocal dstParentProj)
        dstEp.pointeeOpt
        dstElems
        effSzOpt)
  let zeroByteSlice : Bool :=
    match elemSzOpt with
    | .some _ => false
    | .none => Bool.and (nonEmptyAllUnitValues srcElems) (nonEmptyAllUnitValues dstElems)
  match zeroByteSlice with
  | true => .noop
  | false =>
    let offElemSz : Nat :=
      match effSzOpt with
      | .some sz => sz
      | .none => 0
    match
      byteOffsetToElemIdx? srcEp.ptr.offsetBytes offElemSz,
      byteOffsetToElemIdx? dstEp.ptr.offsetBytes offElemSz
    with
    | .some srcOff, .some dstOff =>
      let effSrcStart := Nat.add srcBaseIdx srcOff
      let effDstStart := Nat.add dstBaseIdx dstOff
      let srcIn := Nat.ble (Nat.add effSrcStart n) (length srcElems)
      let dstIn := Nat.ble (Nat.add effDstStart n) (length dstElems)
      match Bool.and srcIn dstIn with
      | false =>
        let boundsSzOpt : Option Nat :=
          match elemSzOpt with
          | .some sz => .some sz
          | .none =>
            match strideOk with
            | true => effSzOpt
            | false => .none
        let srcFits : Option Bool :=
          match boundsSzOpt with
          | .some sz =>
            copyAccessFitsAlloc?
              localDecls layouts locals callerLocals callStack srcEp (Nat.mul n sz)
          | .none => .none
        let dstFits : Option Bool :=
          match boundsSzOpt with
          | .some sz =>
            copyAccessFitsAlloc?
              localDecls layouts locals callerLocals callStack dstEp (Nat.mul n sz)
          | .none => .none
        match Bool.or (copyAccessCertainlyOob srcFits) (copyAccessCertainlyOob dstFits) with
        | true => .ub
        | false =>
          let srcRootOverrun : Bool :=
            match srcIn, srcParentProj, srcFits with
            | false, .nil, .none => true
            | _, _, _ => false
          let dstRootOverrun : Bool :=
            match dstIn, dstParentProj, dstFits with
            | false, .nil, .none => true
            | _, _, _ => false
          match
            Bool.and
              strideOk
              (Bool.and
                (Bool.not
                  (Bool.or (nonEmptyAllUnitValues srcElems) (nonEmptyAllUnitValues dstElems)))
                (Bool.or srcRootOverrun dstRootOverrun))
          with
          | true => .ub
          | false => .unsupported
      | true =>
        match strideOk with
        | false => .unsupported
        | true =>
          let srcWindowProj :=
            copySliceWindowProj srcParentProj effSrcStart n (length srcElems)
          let dstWindowProj :=
            copySliceWindowProj dstParentProj effDstStart n (length dstElems)
          let overlaps : Bool :=
            match Nat.beq srcEp.ptr.tag dstEp.ptr.tag with
            | true => true
            | false =>
              match Nat.beq srcEp.entry.targetLocal dstEp.entry.targetLocal with
              | false => false
              | true => projectionsOverlap srcWindowProj dstWindowProj
          match overlaps with
          | true => .ub
          | false =>
            .write
              { local_ := dstEp.entry.targetLocal, projection := dstParentProj }
              (.aggregate 0
                (spliceValues
                  (takeValues n (dropValues effSrcStart srcElems))
                  effDstStart
                  dstElems))
              srcWindowProj
              dstWindowProj
    | _, _ => .unsupported

/--
Byte-level path of a multi-element or sub-place `copy_nonoverlapping` when at
least one endpoint is not an array or slice (`copyViaBytes`): the source bytes
are the untyped encoding of the source value, and they are placed into the
destination only where the model can place them exactly.

- An access that is certainly outside its allocation is undefined behavior
  (`copyAccessFitsAlloc?` at `count * size_of::<T>()` bytes).
- Source: the source is sliced by element only when it is a genuine array or
  slice whose elements have the copied element size
  (`elemsMatchByteStride`); otherwise the whole pointed-to value is encoded,
  which requires the pointer to sit at the start of that value
  (`srcPtr.offsetBytes = 0`). The encoded length must equal
  `count * size_of::<T>()` when that is known.
- Destination: raw bytes are spliced only into a byte container (`[u8; N]`,
  `[i8; N]`, a byte slice, or an untyped sequence of one-byte scalars) at the
  byte index of the pointer; otherwise the bytes are decoded as one whole value
  of the pointed-to place (or of its enclosing array when the pointer is at
  element `0`), which requires `dstPtr.offsetBytes = 0` and an exact size match.
- The accessed source and destination places must not overlap; the outcome
  names exactly those places for the Tree Borrows read-then-write transition
  (`borrowsAfterCopySlice`, applied by `evalCopySubplaceMulti`).
- Every remaining case (a partial read or write of a value, a pointer into the
  middle of a value, a type-punned sequence) is inside the allocation as far as
  the model knows and fails closed with `.unsupported`.

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "src must be valid for reads of count * size_of::<T>() bytes or that number must be 0."
> "dst must be valid for writes of count * size_of::<T>() bytes or that number must be 0."
> "The region of memory beginning at src with a size of count * size_of::<T>() bytes must not overlap with the region of memory beginning at dst with the same size."
> "Like read, copy_nonoverlapping creates a bitwise copy of T, regardless of whether T is Copy."

Reference (`core::ptr`, "Safety", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/index.html#safety>

> "For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that the pointer be dereferenceable. The provenance of the pointer is used to determine which allocation it is derived from; a pointer is dereferenceable if the memory range of the given size starting at the pointer is entirely contained within the bounds of that allocation. Note that in Rust, every (stack-allocated) variable is considered a separate allocation."

Justification: a "bitwise copy" writes exactly the source bytes at the
destination pointer. Splicing bytes element-wise is exact only when each
destination element is one byte, and decoding a whole value is exact only when
the written range is exactly the range of that value; every other placement
would write a different set of bytes than the copy does, so it is not modeled.
Undefined behavior is reported only when a necessary validity condition fails
(the access is certainly outside the allocation), when the accessed places
overlap, when the aliasing model rejects the accesses, or when the copied bytes
do not form a value of the destination type.

Modeling assumptions and unsupported behavior: bytes that do not decode at the
destination type (for example uninitialized bytes) are reported as undefined
behavior, the policy of the single-element path; a copy between two pointers
with the same tag is undefined behavior as in the single-element path.
-/
def copyBytesSubplace
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (srcEp dstEp : CopyEndpoint)
    (elemSzOpt : Option Nat)
    (n : Nat)
    (srcWinOpt dstWinOpt : Option (List ProjectionElem × Nat × List Value)) :
    CopySliceOutcome :=
  let expBytesOpt : Option Nat :=
    match elemSzOpt with
    | .some sz => .some (Nat.mul n sz)
    | .none => .none
  let sliceElemSzOpt : Option Nat :=
    match elemSzOpt with
    | .some sz => .some sz
    | .none =>
      match srcWinOpt with
      | .some (_, _, e :: rest) =>
        match inferValueByteSizeAux 8 e with
        | .some sz =>
          match elemsMatchByteStride (e :: rest) sz with
          | true => .some sz
          | false => .none
        | .none => .none
      | _ => .none
  let fitsAt (ep : CopyEndpoint) (bytesOpt : Option Nat) : Option Bool :=
    match bytesOpt with
    | .some bytes =>
      copyAccessFitsAlloc? localDecls layouts locals callerLocals callStack ep bytes
    | .none => .none
  match
    Bool.or
      (copyAccessCertainlyOob (fitsAt srcEp expBytesOpt))
      (copyAccessCertainlyOob (fitsAt dstEp expBytesOpt))
  with
  | true => .ub
  | false =>
    let srcResolvedProj : List ProjectionElem :=
      match resolveBorrowProjectionElems locals srcEp.entry.targetProjection with
      | .some rp => normalizeSubsliceProjections rp
      | .none => srcEp.entry.targetProjection
    let dstResolvedProj : List ProjectionElem :=
      match resolveBorrowProjectionElems locals dstEp.entry.targetProjection with
      | .some rp => normalizeSubsliceProjections rp
      | .none => dstEp.entry.targetProjection
    let wholeSrc : Option (Value × List ProjectionElem) :=
      match Nat.beq srcEp.ptr.offsetBytes 0, srcEp.rootValOpt with
      | true, .some srcRootVal =>
        match readProjectedValue locals srcRootVal srcEp.entry.targetProjection with
        | .ok srcSubVal => .some (srcSubVal, srcResolvedProj)
        | _ => .none
      | _, _ => .none
    let srcSlice : Option (Value × List ProjectionElem) :=
      match srcWinOpt, sliceElemSzOpt with
      | .some (srcParentProj, srcBaseIdx, srcElems), .some elemSz =>
        match
          elemsMatchByteStride srcElems elemSz,
          byteOffsetToElemIdx? srcEp.ptr.offsetBytes elemSz
        with
        | true, .some srcOff =>
          let effSrcStart := Nat.add srcBaseIdx srcOff
          match Nat.ble (Nat.add effSrcStart n) (length srcElems) with
          | true =>
            .some
              (.aggregate 0 (takeValues n (dropValues effSrcStart srcElems)),
                copySliceWindowProj srcParentProj effSrcStart n (length srcElems))
          | false => .none
        | _, _ => wholeSrc
      | _, _ => wholeSrc
    match srcSlice with
    | .none =>
      match srcEp.rootValOpt with
      | .none => .ub
      | .some srcRootVal =>
        match readProjectedValue locals srcRootVal srcEp.entry.targetProjection with
        | .ub => .ub
        | _ => .unsupported
    | .some (sVal, srcEffProj) =>
      match encodeUntypedValueToBytes defaultCodecFuel sVal with
      | .none => .unsupported
      | .some bs =>
        let lenOk : Bool :=
          match expBytesOpt with
          | .some expBytes => Nat.beq (length bs) expBytes
          | .none => true
        match lenOk with
        | false => .unsupported
        | true =>
          match copyAccessCertainlyOob (fitsAt dstEp (.some (length bs))) with
          | true => .ub
          | false =>
            let commit
                (dstPlace : Place)
                (newVal : Value)
                (dstEffProj : List ProjectionElem) :
                CopySliceOutcome :=
              let overlaps : Bool :=
                match Nat.beq srcEp.ptr.tag dstEp.ptr.tag with
                | true => true
                | false =>
                  match Nat.beq srcEp.entry.targetLocal dstEp.entry.targetLocal with
                  | false => false
                  | true => projectionsOverlap srcEffProj dstEffProj
              match overlaps with
              | true => .ub
              | false => .write dstPlace newVal srcEffProj dstEffProj
            let dstLocal := dstEp.entry.targetLocal
            let dstByteWin : Option (List ProjectionElem × Nat × List Value) :=
              match dstWinOpt with
              | .some (dstParentProj, dstBaseIdx, dstElems) =>
                let isByteContainer : Bool :=
                  match
                    copyContainerElemKind? localDecls layouts locals dstLocal dstParentProj
                  with
                  | .some (.uint .u8) => true
                  | .some (.int .i8) => true
                  | .some _ => false
                  | .none =>
                    match dstElems with
                    | .nil => false
                    | _ :: _ => elemsAreByteScalars dstElems
                match isByteContainer with
                | true => .some (dstParentProj, dstBaseIdx, dstElems)
                | false => .none
              | .none => .none
            match dstByteWin with
            | .some (dstParentProj, dstBaseIdx, dstElems) =>
              let effDstStart := Nat.add dstBaseIdx dstEp.ptr.offsetBytes
              match Nat.ble (Nat.add effDstStart (length bs)) (length dstElems) with
              | false => .unsupported
              | true =>
                match
                  decodeArrayChunksWith
                    (fun chunk =>
                      decodeValueFromBytes
                        defaultCodecFuel
                        layouts
                        { kind := .uint .u8, layoutIdx := 0 }
                        chunk)
                    1
                    (length bs)
                    bs
                with
                | .some copiedBytes =>
                  commit
                    { local_ := dstLocal, projection := dstParentProj }
                    (.aggregate 0 (spliceValues copiedBytes effDstStart dstElems))
                    (copySliceWindowProj dstParentProj effDstStart (length bs) (length dstElems))
                | .none => .unsupported
            | .none =>
              match Nat.beq dstEp.ptr.offsetBytes 0 with
              | false => .unsupported
              | true =>
                let dstPlaceTyOpt : Option Ty :=
                  match get? locals dstLocal with
                  | .some _ =>
                    placeTy
                      localDecls
                      layouts
                      { local_ := dstLocal, projection := dstEp.entry.targetProjection }
                  | .none => .none
                let dstTargetTyOpt : Option Ty :=
                  match dstPlaceTyOpt with
                  | .some t => .some t
                  | .none =>
                    match dstEp.pointeeOpt, dstEp.rootValOpt with
                    | .some pt, .some dstRootVal =>
                      match
                        readProjectedValue locals dstRootVal dstEp.entry.targetProjection,
                        rigidTyByteSize layouts pt
                      with
                      | .ok dstSubVal, .some ptBytes =>
                        let shapeCompatible : Bool :=
                          match dstSubVal, pt.kind with
                          | .aggregate _ _, .uint _ => false
                          | .aggregate _ _, .int _ => false
                          | .aggregate _ _, .bool => false
                          | .aggregate _ _, .char => false
                          | .aggregate _ _, .float _ => false
                          | .scalar _, .array _ _ => false
                          | .scalar _, .adt _ _ => false
                          | .scalar _, .tuple _ => false
                          | _, _ => true
                        match shapeCompatible, valueDefaultByteSize dstSubVal with
                        | true, .some subBytes =>
                          match Nat.beq ptBytes subBytes with
                          | true => .some pt
                          | false => .none
                        | _, _ => .none
                      | _, _ => .none
                    | _, _ => .none
                let decodeAt
                    (tyOpt : Option Ty)
                    (dstProj dstEffProj : List ProjectionElem) :
                    Option CopySliceOutcome :=
                  let canWriteToSlot : Bool :=
                    match dstEp.rootValOpt, stripLeadingOpaqueCast dstProj with
                    | .none, _ :: _ => false
                    | _, _ => true
                  match canWriteToSlot, tyOpt with
                  | true, .some dstTy =>
                    match rigidTyByteSize layouts dstTy with
                    | .none => .none
                    | .some dstBytes =>
                      match Nat.beq (length bs) dstBytes with
                      | false => .none
                      | true =>
                        match decodeValueFromBytes defaultCodecFuel layouts dstTy bs with
                        | .some decodedVal =>
                          .some
                            (commit
                              { local_ := dstLocal, projection := dstProj }
                              decodedVal
                              dstEffProj)
                        | .none => .some .ub
                  | _, _ => .none
                match decodeAt dstTargetTyOpt dstEp.entry.targetProjection dstResolvedProj with
                | .some outcome => outcome
                | .none =>
                  match dstWinOpt with
                  | .some (dstParentProj, .zero, _) =>
                    let parentTyOpt : Option Ty :=
                      match get? locals dstLocal with
                      | .some _ =>
                        placeTy
                          localDecls
                          layouts
                          { local_ := dstLocal, projection := dstParentProj }
                      | .none => .none
                    match decodeAt parentTyOpt dstParentProj dstParentProj with
                    | .some outcome => outcome
                    | .none => .unsupported
                  | .none =>
                    match dstEp.rootValOpt, splitLastConstantIndex? dstResolvedProj with
                    | .none, .some (initProj, .zero, _) =>
                      match stripLeadingOpaqueCast initProj with
                      | .nil =>
                        let parentTyOpt : Option Ty :=
                          match get? locals dstLocal with
                          | .some _ =>
                            placeTy
                              localDecls
                              layouts
                              { local_ := dstLocal, projection := initProj }
                          | .none => .none
                        match decodeAt parentTyOpt initProj initProj with
                        | .some outcome => outcome
                        | .none => .unsupported
                      | _ :: _ => .unsupported
                    | _, _ => .unsupported
                  | _ => .unsupported

/--
Resolve a `copy_nonoverlapping` of `n ≥ 1` elements that is neither a union
copy nor the single-element direct copy (`n = 1` with both pointers at byte
offset `0`): a multi-element copy, or a copy through a pointer at a non-zero
byte offset (`RawPtrOffsetMutator:wrong_value:MirDiffTag.normalScalar`).

1. Both root slots must be live (neither `.none` nor `.dead`, else `.ub`).
2. Both pointers must be aligned for the pointee type (`checkDerefAlign`, else
   `.ub`).
3. A copy whose pointee type is statically zero-sized transfers zero bytes and
   is a no-op (even if either live root slot is `.uninit`).
4. Otherwise, the source root slot must be initialized (else `.ub`), while a
   live `.uninit` destination may be initialized as a whole value through
   `copyBytesSubplace` (failing closed with `.unsupported` for in-bounds partial
   writes and `.ub` when certainly out of bounds). When both endpoints point
   into initialized arrays or slices (`resolveArraySliceEndpoint?`), the copy is
   the element-window copy `copySliceElements`; otherwise it is the byte-level
   copy `copyBytesSubplace`.

The resolution depends on the machine state only through `callerLocals` and
`callStack` (to locate caller-owned referents and place offsets); the aliasing
transition and the destination commit are applied by `evalCopySubplaceMulti`.

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "Copies count * size_of::<T>() bytes from src to dst. The source and destination must not overlap."
> "src must be valid for reads of count * size_of::<T>() bytes or that number must be 0."
> "dst must be valid for writes of count * size_of::<T>() bytes or that number must be 0."
> "Both src and dst must be properly aligned."
> "Note that even if the effectively copied size (count * size_of::<T>()) is 0, the pointers must be properly aligned."

Reference (`core::ptr`, "Safety", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/index.html#safety>

> "For memory accesses of size zero, every non-null pointer is valid for reads/writes."

Justification: the copy transfers `count * size_of::<T>()` bytes, not one
element: a pointer to element `i` of an array with `count > 1` reads `count`
consecutive elements, and the pointer's byte offset is a byte offset, not an
element index. Alignment is required "even if the effectively copied size ...
is 0", so it is checked before the zero-size case; a zero-sized access is
otherwise valid through "every non-null pointer", and the model has no null
pointers with a borrow entry, so it is a no-op. A non-zero copy does not read
`dst` before overwriting it, so a live `.uninit` destination is valid for
writes.

Modeling assumptions and unsupported behavior: alignment is decided by
`checkDerefAlign` on the pointer's byte offset (the borrowed place itself is
assumed aligned for the pointee type); operand pointee types that disagree in
size fail closed with `.unsupported`; partial writes into an `.uninit`
destination fail closed with `.unsupported` unless certainly out of bounds.
-/
def resolveCopySubplaceMulti
    (callerLocals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (n : Nat)
    (locals₃ : List LocalSlot) :
    CopySliceOutcome :=
  let srcRootSlot : Option LocalSlot :=
    match get? locals₃ srcEntry.targetLocal with
    | .some slot => .some slot
    | .none =>
      match get? callerLocals srcEntry.targetLocal with
      | .some slot => .some slot
      | .none =>
        get?
          callerLocals
          (Nat.sub srcEntry.targetLocal (length locals₃))
  let dstRootSlot : Option LocalSlot :=
    match get? locals₃ dstEntry.targetLocal with
    | .some slot => .some slot
    | .none =>
      match get? callerLocals dstEntry.targetLocal with
      | .some slot => .some slot
      | .none =>
        get?
          callerLocals
          (Nat.sub dstEntry.targetLocal (length locals₃))
  match srcRootSlot, dstRootSlot with
  | .none, _ => .ub
  | _, .none => .ub
  | .some .dead, _ => .ub
  | _, .some .dead => .ub
  | .some srcSlot, .some dstSlot =>
    let srcPtOpt := operandPointeeTy localDecls layouts src
    let dstPtOpt := operandPointeeTy localDecls layouts dst
    match
      Bool.and
        (checkDerefAlign localDecls layouts srcPtOpt srcPtr.offsetBytes)
        (checkDerefAlign localDecls layouts dstPtOpt dstPtr.offsetBytes)
    with
    | false => .ub
    | true =>
      match copyPointeeSizesConflict localDecls layouts srcPtOpt dstPtOpt with
      | true => .unsupported
      | false =>
        let elemSzOpt := copyPointeeByteSize? localDecls layouts srcPtOpt dstPtOpt
        match elemSzOpt with
        | .some .zero => .noop
        | _ =>
          match srcSlot with
          | .init srcRootVal =>
            let srcEp : CopyEndpoint :=
              { ptr := srcPtr
                entry := srcEntry
                rootValOpt := .some srcRootVal
                pointeeOpt := srcPtOpt }
            let dstRootValOpt : Option Value :=
              match dstSlot with
              | .init v => .some v
              | _ => .none
            let dstEp : CopyEndpoint :=
              { ptr := dstPtr
                entry := dstEntry
                rootValOpt := dstRootValOpt
                pointeeOpt := dstPtOpt }
            let srcWinOpt := resolveArraySliceEndpoint? localDecls layouts locals₃ srcEp elemSzOpt
            let dstWinOpt := resolveArraySliceEndpoint? localDecls layouts locals₃ dstEp elemSzOpt
            match srcWinOpt, dstWinOpt with
            | .some (srcParentProj, srcBaseIdx, srcElems),
              .some (dstParentProj, dstBaseIdx, dstElems) =>
              copySliceElements
                localDecls
                layouts
                locals₃
                callerLocals
                callStack
                srcEp
                dstEp
                elemSzOpt
                n
                srcParentProj
                srcBaseIdx
                srcElems
                dstParentProj
                dstBaseIdx
                dstElems
            | _, _ =>
              copyBytesSubplace
                localDecls
                layouts
                locals₃
                callerLocals
                callStack
                srcEp
                dstEp
                elemSzOpt
                n
                srcWinOpt
                dstWinOpt
          | _ => .ub

/--
Write `newVal` to `dstPlace` in `locals₃` (or `s.memory.callerLocals` when
`dstPlace.local_` indexes a caller-owned referent), install the borrow table
`borrows'` computed by the caller, and advance `s` to the next statement: the
destination commit of `commitCopyDstPlaceWrite` for a copy whose Tree Borrows
transition (`borrowsAfterCopySlice`) was already applied.
-/
def commitCopyDstPlaceWriteWithBorrows
    (s : MachineState)
    (dstPlace : Place)
    (locals₃ : List LocalSlot)
    (newVal : Value)
    (borrows' : List BorrowEntry)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    writePlaceValue
      locals₃
      s.memory.borrows
      dstPlace
      newVal
      localDecls
      layouts
  with
  | .ok locals₄ =>
    MirStepNode.step
      (advanceStmt
        s
        locals₄
        { s.memory with borrows := borrows' })
  | .unsupported => MirStepNode.unsupported
  | .ub =>
    match get? locals₃ dstPlace.local_ with
    | .some _ => MirStepNode.fail .ub
    | .none =>
      let callerIdx :=
        match get? s.memory.callerLocals dstPlace.local_ with
        | .some _ => dstPlace.local_
        | .none => Nat.sub dstPlace.local_ (length locals₃)
      let callerWriteRes : PlaceWriteResult :=
        match dstPlace.projection with
        | .nil =>
          match get? s.memory.callerLocals callerIdx with
          | .some .dead => .ub
          | .some _ =>
            match set? s.memory.callerLocals callerIdx (.init newVal) with
            | .some callerLocals' => .ok callerLocals'
            | .none => .ub
          | .none => .ub
        | .deref :: _ => .ub
        | proj :: rest =>
          match get? s.memory.callerLocals callerIdx with
          | .some (.init rootVal) =>
            match
              writeProjectedValue
                locals₃
                rootVal
                (proj :: rest)
                newVal
            with
            | .ok rootVal' =>
              match set? s.memory.callerLocals callerIdx (.init rootVal') with
              | .some callerLocals' => .ok callerLocals'
              | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
          | _ => .ub
      match callerWriteRes with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok callerLocals' =>
        MirStepNode.step
          (advanceStmt
            s
            locals₃
            { s.memory with
              borrows := borrows'
              callerLocals := callerLocals' })

/--
Evaluate a `copy_nonoverlapping` of `countBits ≥ 1` elements that is neither a
union copy nor the single-element direct copy: resolve it
(`resolveCopySubplaceMulti`) and commit the outcome: `.ub`, `.unsupported`, a
no-op step, or a destination write. A write first runs the Tree Borrows
read-then-write check and transition on the accessed source and destination
places (`borrowsAfterCopySlice`, `.ub` on a violation) and then commits the
value with the updated borrow table (`commitCopyDstPlaceWriteWithBorrows`).

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "Copies count * size_of::<T>() bytes from src to dst. The source and destination must not overlap."

Justification and modeling assumptions: see `resolveCopySubplaceMulti`.
-/
def evalCopySubplaceMulti
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match
    resolveCopySubplaceMulti
      s.memory.callerLocals
      s.memory.callStack
      src
      dst
      localDecls
      layouts
      srcPtr
      dstPtr
      srcEntry
      dstEntry
      countBits
      locals₃
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .noop => MirStepNode.step (advanceStmt s locals₃)
  | .write dstPlace newVal srcWindowProj dstWindowProj =>
    match
      borrowsAfterCopySlice
        s.memory.borrows
        s.memory.activeProtectors
        srcPtr
        dstPtr
        srcEntry
        dstEntry
        srcWindowProj
        dstWindowProj
    with
    | .none => MirStepNode.fail .ub
    | .some borrows' =>
      commitCopyDstPlaceWriteWithBorrows
        s
        dstPlace
        locals₃
        newVal
        borrows'
        localDecls
        layouts

/--
Evaluate `copy_nonoverlapping` once `srcVal`, `dstVal`, and scalar `countBits`
have been evaluated into `locals₃`, supporting direct element copies,
byte-encoded copies into initialized or union destinations, untyped copies of
uninitialized union bytes (`FieldsShape.union`) into a union destination, and
multi-element and offset sub-place copies (`evalCopySubplaceMulti`).

The union copy (`evalCopyUnionBytes`) and the single-element direct copy
(`evalCopySingleDirect`, `countBits = 1` with both pointers at byte offset `0`)
are dispatched first and are unchanged; every other copy copies
`countBits * size_of::<T>()` bytes through `evalCopySubplaceMulti`
(`RawPtrOffsetMutator:wrong_value:MirDiffTag.normalScalar`).

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "Copies count * size_of::<T>() bytes from src to dst. The source and destination must not overlap."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The following is a non-exhaustive list of invalid values:
> - A value of any type, other than a union or raw pointer, with uninitialized
>   bytes (except for padding bytes, which may be uninitialized)."

Justification: the copied byte count is `count * size_of::<T>()`, so only the
case `count = 1` at the start of the pointed-to place is a copy of exactly one
value of that place; all other cases are resolved on element windows or bytes.
-/
def evalCopyNonOverlappingPermOk
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  let n := countBits
  let srcStart := srcPtr.offsetBytes
  let dstStart := dstPtr.offsetBytes
  let srcUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ srcEntry
  let dstUnionOpt :=
    resolveUnionEndpoint? localDecls layouts locals₃ dstEntry
  let hasUnionEndpoint :=
    match srcUnionOpt, dstUnionOpt with
    | .none, .none => false
    | _, _ => true
  match hasUnionEndpoint with
  | true =>
    evalCopyUnionBytes
      s
      src
      dst
      localDecls
      layouts
      srcPtr
      dstPtr
      srcEntry
      dstEntry
      srcUnionOpt
      dstUnionOpt
      n
      locals₃
  | false =>
    let isSingleDirect :=
      Bool.and
        (Nat.beq n 1)
        (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0))
    match isSingleDirect with
    | true =>
      evalCopySingleDirect
        s
        src
        dst
        localDecls
        layouts
        srcPtr
        dstPtr
        srcEntry
        dstEntry
        locals₃
    | false =>
      evalCopySubplaceMulti
        s
        src
        dst
        localDecls
        layouts
        srcPtr
        dstPtr
        srcEntry
        dstEntry
        n
        locals₃

/--
Frame-qualified single-element direct value copy (`count == 1`, `srcStart == 0`,
`dstStart == 0`) for `copy_nonoverlapping` when at least one of `srcEntry` or
`dstEntry` targets a suspended caller frame (`copyEntriesTargetActiveFrame = false`,
`DIV-MR-CALL-TARGET-LOCAL`). Reads the source value from `(srcEntry.targetFrameDepth,
srcEntry.targetLocal)` (`readFrameLocalSlot`), checks disjointness on the pair
`(targetFrameDepth, targetLocal)` and `targetProjection`, applies the Tree Borrows
read-then-write check and transition (`borrowsAfterCopySingleDirect`), and writes
the converted value to `(dstEntry.targetFrameDepth, dstEntry.targetLocal)`
(`writeFrameLocalSlot`). Non-unit counts or non-zero byte offsets across frames
fail closed with `MirStepNode.unsupported`.
-/
def evalForeignFrameCopySingleDirect
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (srcEntry dstEntry : BorrowEntry)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match
    Bool.and
      (Nat.beq countBits 1)
      (Bool.and
        (Nat.beq srcPtr.offsetBytes 0)
        (Nat.beq dstPtr.offsetBytes 0))
  with
  | false => MirStepNode.unsupported
  | true =>
    let overlaps :=
      match Nat.beq srcPtr.tag dstPtr.tag with
      | true => true
      | false =>
        match
          Bool.and
            (Nat.beq srcEntry.targetFrameDepth dstEntry.targetFrameDepth)
            (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
        with
        | false => false
        | true =>
          projectionsOverlap
            srcEntry.targetProjection
            dstEntry.targetProjection
    match overlaps with
    | true => MirStepNode.fail .ub
    | false =>
      match
        readFrameLocalSlot
          locals₃
          s.memory.callStack
          s.memory.callerLocals
          srcEntry.targetFrameDepth
          srcEntry.targetLocal
      with
      | .some (.init srcRootVal) =>
        match
          readProjectedValue
            locals₃
            srcRootVal
            srcEntry.targetProjection
        with
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
        | .ok copiedVal =>
          let convertedOpt : Option Value :=
            match
              operandPointeeTy localDecls layouts src,
              operandPointeeTy localDecls layouts dst
            with
            | .some srcPt, .some dstPt =>
              match sameRigidTyShape srcPt.kind dstPt.kind with
              | true => .some copiedVal
              | false =>
                match
                  rigidTyByteSize layouts srcPt,
                  rigidTyByteSize layouts dstPt
                with
                | .some sSz, .some dSz =>
                  match Nat.beq sSz dSz with
                  | false => .none
                  | true =>
                    match
                      encodeValueToBytes
                        defaultCodecFuel
                        layouts
                        srcPt
                        copiedVal
                    with
                    | .some bs =>
                      decodeValueFromBytes
                        defaultCodecFuel
                        layouts
                        dstPt
                        bs
                    | .none => .none
                | _, _ => .some copiedVal
            | _, _ => .some copiedVal
          match convertedOpt with
          | .none => MirStepNode.fail .ub
          | .some finalVal =>
            match
              borrowsAfterCopySingleDirect
                s.memory.borrows
                s.memory.activeProtectors
                srcPtr
                dstPtr
                srcEntry
                dstEntry
            with
            | .none => MirStepNode.fail .ub
            | .some borrows' =>
              let dstRootSlotOpt :=
                readFrameLocalSlot
                  locals₃
                  s.memory.callStack
                  s.memory.callerLocals
                  dstEntry.targetFrameDepth
                  dstEntry.targetLocal
              let newDstRootRes : PlaceReadResult :=
                match dstEntry.targetProjection with
                | .nil =>
                  match dstRootSlotOpt with
                  | .some .dead => .ub
                  | .some _ => .ok finalVal locals₃
                  | .none => .ub
                | pHead :: pTail =>
                  match dstRootSlotOpt with
                  | .some (.init dstRootVal) =>
                    match
                      writeProjectedValue
                        locals₃
                        dstRootVal
                        (pHead :: pTail)
                        finalVal
                    with
                    | .ok dstRootVal' => .ok dstRootVal' locals₃
                    | .ub => .ub
                    | .unsupported => .unsupported
                  | _ => .ub
              match newDstRootRes with
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
              | .ok newDstRootVal _ =>
                match
                  writeFrameLocalSlot
                    locals₃
                    s.memory.callStack
                    s.memory.callerLocals
                    dstEntry.targetFrameDepth
                    dstEntry.targetLocal
                    (.init newDstRootVal)
                with
                | .some (locals₄, callStack', callerLocals') =>
                  MirStepNode.step
                    (advanceStmt
                      s
                      locals₄
                      { s.memory with
                        borrows := borrows'
                        callStack := callStack'
                        callerLocals := callerLocals' })
                | .none => MirStepNode.fail .ub
      | _ => MirStepNode.fail .ub

/--
Execute a `NonDivergingIntrinsic.copyNonOverlapping src dst count` statement with
pre-resolved count bits.
-/
def evalCopyNonOverlappingWithCount
    (s : MachineState)
    (src dst : Operand)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (srcVal dstVal : Value)
    (countBits : Nat)
    (locals₃ : List LocalSlot) :
    MirStepNode :=
  match Nat.beq countBits 0 with
  | true => MirStepNode.step (advanceStmt s locals₃)
  | false =>
    match srcVal, dstVal with
    | .ptr srcPtr _, .ptr dstPtr _ =>
      match
        lookupBorrow s.memory.borrows srcPtr.tag,
        lookupBorrow s.memory.borrows dstPtr.tag
      with
      | .some srcEntry, .some dstEntry =>
        match srcEntry.perm, dstEntry.perm with
        | .disabled, _ => MirStepNode.fail .ub
        | _, .frozen => MirStepNode.fail .ub
        | _, .disabled => MirStepNode.fail .ub
        | _, _ =>
          match copyEntriesTargetActiveFrame s.memory.callStack srcEntry dstEntry with
          | false =>
            evalForeignFrameCopySingleDirect
              s
              src
              dst
              localDecls
              layouts
              srcPtr
              dstPtr
              srcEntry
              dstEntry
              countBits
              locals₃
          | true =>
            evalCopyNonOverlappingPermOk
              s
              src
              dst
              localDecls
              layouts
              srcPtr
              dstPtr
              srcEntry
              dstEntry
              countBits
              locals₃
      | _, _ => MirStepNode.fail .ub
    | _, _ => MirStepNode.fail .ub

/--
Execute a `NonDivergingIntrinsic.copyNonOverlapping src dst count` statement.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L449-L473>

> "pub enum NonDivergingIntrinsic<'tcx> {
>     Assume(Operand<'tcx>),
>     CopyNonOverlapping(CopyNonOverlapping<'tcx>),
> }"
-/
def evalCopyNonOverlapping
    (s : MachineState)
    (src dst count : Operand)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    evalOperand
      s.frame.locals
      src
      s.memory.borrows
      s.memory.globals
      layouts
      s.memory.callerLocals
      localDecls
      s.memory.callStack
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok srcVal locals₁ =>
    match
      evalOperand
        locals₁
        dst
        s.memory.borrows
        s.memory.globals
        layouts
        s.memory.callerLocals
        localDecls
        s.memory.callStack
    with
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
    | .ok dstVal locals₂ =>
      match
        evalOperand
          locals₂
          count
          s.memory.borrows
          s.memory.globals
          layouts
          s.memory.callerLocals
          localDecls
          s.memory.callStack
      with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok (.scalar countSc) locals₃ =>
        evalCopyNonOverlappingWithCount
          s
          src
          dst
          localDecls
          layouts
          srcVal
          dstVal
          countSc.bits
          locals₃
      | .ok _ _ => MirStepNode.fail .ub

/--
Whether a function-entry-protected tag with Tree Borrows permission `perm`
prevents deallocating its allocation (`DIV-MR-TB-UNSAFECELL-PROTECTED-IM`):
exactly the permissions for which a foreign write is undefined behavior while
protected. `.cell` never prevents deallocation (interior mutability tolerates
foreign writes) and a `.disabled` tag no longer protects anything; every other
state does. Every Anneal tag has performed its initial child access when it was
created (or is a fail-closed protected `.reservedIM`), so MiniRust's
`had_local_read` flag is `true` for `.reservedFrz` and `.frozen`.

Reference (MiniRust `spec/mem/tree_borrows/state_machine_protected.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/state_machine_protected.md#L126-L140>

> "/// Strongly protected nodes can block deallocation, based on their permission.
> /// Specifically, they block allocation iff they would cause UB on a foreign write,
> /// that is, if they have been locally accessed ("used"), with an exception for `Cell`.
> /// The check for whether the protector is actually strong happens elsewhere.
> fn prevents_deallocation(&self) -> bool {
>     match self {
>         PermissionProt::Unique => true,
>         PermissionProt::Reserved { had_local_read, .. } | PermissionProt::Frozen { had_local_read } => *had_local_read,
>
>         PermissionProt::Disabled => false,
>
>         // Cell never prevents deallocation
>         PermissionProt::Cell => false,
>     }"
-/
@[reducible]
def preventsDeallocation : TreeBorrowPerm → Bool
  | .cell => false
  | .reservedFrz _ => true
  | .reservedIM => true
  | .unique => true
  | .frozen => true
  | .disabled => false

/--
Test whether any `BorrowEntry` in `borrows` targeting stack local `loc` of the
frame at depth `targetFrameDepth` (default `0`) carries a function-entry lifetime
protector (`RetagKind.fnEntry`) that is still active in `activeProtectors`
(`isBorrowProtected`) and whose permission prevents deallocation
(`preventsDeallocation`: every state except `.cell` and `.disabled`).

Freeing `loc`'s storage (`StorageDead(loc)`, the implicit deallocation performed
by `StorageLive(loc)`, or the frame teardown of `TerminatorKind.return_`) acts as
a write to every byte of the local that disables every tag minted from it
(`disableLocalBorrows`), so the presence of such a protected tag makes the
deallocation immediate undefined behavior. This check subsumes the whole-local
foreign-write conflict check
`hasProtectedWriteConflict borrows activeProtectors loc .none .nil 0 0 targetFrameDepth`
(`hasProtectedLocalBorrow_of_hasProtectedWriteConflict`). A protected `.cell`
tag of interior-mutable data never blocks deallocation
(`DIV-MR-TB-UNSAFECELL-PROTECTED-IM`), and tags of another frame's local with
the same index are not affected (`BorrowEntry.targetFrameDepth`).

Reference (MiniRust `spec/mem/tree_borrows/tree.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L7-L8>

> "When a reborrow occurs at function entry (i.e. the original reference is
> passed as an argument), we add a *protector* to the reborrow. When a node is
> protected, it is UB for this node to become `Disabled`."

Reference (MiniRust `spec/mem/tree_borrows/memory.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/mem/tree_borrows/memory.md#L209-L215>

> "// Check that ptr has the permission to write the entire allocation.
> extra.root.access(Some(path), AccessKind::Write, Offset::ZERO, size)?;
>
> // Check that allocation is not strongly protected.
> if extra.root.contains_strong_protector_preventing_deallocation() {
>     throw_ub!("Tree Borrows: deallocating strongly protected allocation")
> }"

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L366-L373>

> "`StorageLive`/`StorageDead` act like the heap operations
> `allocate`/`deallocate`, but for stack-allocated local variables."
-/
def hasProtectedLocalBorrow
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (loc : Local)
    (targetFrameDepth : Nat := 0) :
    Bool :=
  match borrows with
  | .nil => false
  | entry :: rest =>
    match
      Bool.and
        (Bool.and
          (Nat.beq entry.targetFrameDepth targetFrameDepth)
          (Nat.beq entry.targetLocal loc))
        (Bool.and
          (isBorrowProtected activeProtectors entry)
          (preventsDeallocation entry.perm))
    with
    | true => true
    | false => hasProtectedLocalBorrow rest activeProtectors loc targetFrameDepth

/--
Disable every `BorrowEntry` in `borrows` targeting stack local `loc` of the frame
at depth `targetFrameDepth` (default `0`), setting its Tree Borrows permission to
`.disabled` and marking its backing allocation deallocated (`allocDead := true`),
and leave every other entry unchanged. `allocDead` keeps a later
`StorageLive(loc)` revival from giving stale tags the new allocation's bounds
for `BinOp.Offset` (`DIV-LM-D6-OFFSET-DISABLED-TAG`).

`StorageDead(loc)` frees `loc`'s storage and `StorageLive(loc)` allocates fresh
storage for it (implicitly freeing any previous allocation), so every
provenance tag minted from the previous allocation of `loc` (including reborrow
descendants, which inherit `targetLocal` from their parent entry) becomes
dangling. As in Tree Borrows, where deallocation is a write access to the whole
allocation that leaves every tag of the dead allocation unusable, the entries
stay in the borrow table but lose every permission: each place read, place
write, safe reborrow (`Rvalue.ref`), retag, `copy_nonoverlapping`, unsizing
coercion, or pointer offset that resolves a disabled tag faults with `.ub`.

The entries are disabled rather than removed because a provenance tag with no
stack borrow entry falls back to `lookupGlobalAlloc` on `ptrVal.allocId`, and
stack borrow tags (`Memory.nextTag`, starting at `1`) share their numbering with
captured global allocation identifiers (also numbered from `1`): a removed
stale tag would silently read or write an unrelated global allocation instead
of faulting. Because tags are minted from the monotonically increasing
`Memory.nextTag`, no reference or raw pointer created after `StorageLive(loc)`
can share a disabled tag, so stale pointers are never revived into the new
allocation.

`(BorrowEntry.targetFrameDepth, BorrowEntry.targetLocal)` identifies the
borrowed local across every inline call frame on `Memory.callStack`, so
deallocating a callee local never disables a caller-frame entry whose local
index happens to equal `loc` (`DIV-MR-CALLER-BORROW-ACROSS-SCALAR-CALL`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs>

> "If the local is already allocated, calling `StorageLive` again will
> implicitly free the local and then allocate fresh uninitialized memory. If a
> local is already deallocated, calling `StorageDead` again is a NOP."

Reference (MiniRust `spec/lang/step/statements.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/statements.md#L166-L169>

> "fn storage_live(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult {
>     // First remove the old storage, if any.
>     // This means the same address may be re-used for the new stoage.
>     self.storage_dead(mem, local)?;"
-/
def disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local)
    (targetFrameDepth : Nat := 0) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | entry :: rest =>
    match
      Bool.and
        (Nat.beq entry.targetFrameDepth targetFrameDepth)
        (Nat.beq entry.targetLocal loc)
    with
    | true =>
      { entry with perm := .disabled, allocDead := true } ::
        disableLocalBorrows rest loc targetFrameDepth
    | false => entry :: disableLocalBorrows rest loc targetFrameDepth

/--
Definitional simplification equation for `disableLocalBorrows` on the empty
borrow table.
-/
@[simp]
theorem disableLocalBorrows_nil (loc : Local) {targetFrameDepth : Nat} :
    disableLocalBorrows .nil loc targetFrameDepth = .nil := rfl

/--
No borrow entry is protected when no function-entry protector is active, so
`hasProtectedLocalBorrow borrows .nil loc` is always `false`.
-/
@[simp]
theorem hasProtectedLocalBorrow_nil_protectors
    (borrows : List BorrowEntry)
    (loc : Local)
    {targetFrameDepth : Nat} :
    hasProtectedLocalBorrow borrows .nil loc targetFrameDepth = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hProt : isBorrowProtected .nil entry = false := by
      unfold isBorrowProtected
      cases entry.protector <;> rfl
    simp only [hasProtectedLocalBorrow, hProt, Bool.false_and, Bool.and_false]
    exact ih

/--
A protected tag whose permission makes a foreign write undefined behavior
(`borrowEntryWriteConflicts entry .none`) also prevents deallocation.
-/
theorem preventsDeallocation_of_borrowEntryWriteConflicts
    (entry : BorrowEntry)
    (h : borrowEntryWriteConflicts entry .none = true) :
    preventsDeallocation entry.perm = true := by
  revert h
  unfold borrowEntryWriteConflicts
  cases entry.perm with
  | cell => intro h; exact h
  | reservedFrz c => intro _; rfl
  | reservedIM => intro _; rfl
  | unique => intro _; rfl
  | frozen => intro _; rfl
  | disabled => intro h; exact h

/--
`hasProtectedLocalBorrow` subsumes the whole-local foreign-write protector
check: whenever a direct write to the whole of `loc` would disable a protected
tag (`hasProtectedWriteConflict borrows activeProtectors loc .none .nil`), so
does deallocating `loc`.
-/
theorem hasProtectedLocalBorrow_of_hasProtectedWriteConflict
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (loc : Local)
    {targetFrameDepth : Nat}
    (h :
      hasProtectedWriteConflict borrows activeProtectors loc .none .nil 0 0 targetFrameDepth =
        true) :
    hasProtectedLocalBorrow borrows activeProtectors loc targetFrameDepth = true := by
  induction borrows with
  | nil => exact h
  | cons entry rest ih =>
    unfold hasProtectedWriteConflict at h
    unfold hasProtectedLocalBorrow
    cases hT :
        Bool.and
          (Nat.beq entry.targetFrameDepth targetFrameDepth)
          (Nat.beq entry.targetLocal loc) with
    | false =>
      simp only [hT, Bool.false_and] at h ⊢
      exact ih h
    | true =>
      cases hP : isBorrowProtected activeProtectors entry with
      | false =>
        simp only [hT, hP, Bool.false_and, Bool.and_false] at h ⊢
        exact ih h
      | true =>
        cases hW : borrowEntryWriteConflicts entry .none with
        | false =>
          simp only [hT, hP, hW, Bool.and_false] at h
          have hrest := ih h
          simp only [Bool.true_and]
          cases preventsDeallocation entry.perm <;> simp only [hrest]
        | true =>
          simp only [Bool.true_and, preventsDeallocation_of_borrowEntryWriteConflicts entry hW]

/--
`hasProtectedLocalBorrow borrows activeProtectors loc` is `false` when no entry
targets `loc`.
-/
theorem hasProtectedLocalBorrow_eq_false_of_forall_ne
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (loc : Local)
    (h : ∀ entry ∈ borrows, entry.targetLocal ≠ loc)
    {targetFrameDepth : Nat} :
    hasProtectedLocalBorrow borrows activeProtectors loc targetFrameDepth = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hNe : entry.targetLocal ≠ loc := h entry (List.Mem.head rest)
    have hBeq : Nat.beq entry.targetLocal loc = false := by
      cases hB : Nat.beq entry.targetLocal loc with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB))
    simp only [hasProtectedLocalBorrow, hBeq, Bool.and_false, Bool.false_and]
    exact ih (fun e he => h e (List.Mem.tail entry he))

/--
`disableLocalBorrows borrows loc` leaves `borrows` unchanged when no entry
targets `loc`.
-/
theorem disableLocalBorrows_eq_self_of_forall_ne
    (borrows : List BorrowEntry)
    (loc : Local)
    (h : ∀ entry ∈ borrows, entry.targetLocal ≠ loc)
    {targetFrameDepth : Nat} :
    disableLocalBorrows borrows loc targetFrameDepth = borrows := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hNe : entry.targetLocal ≠ loc := h entry (List.Mem.head rest)
    have hBeq : Nat.beq entry.targetLocal loc = false := by
      cases hB : Nat.beq entry.targetLocal loc with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB))
    simp only [disableLocalBorrows, hBeq, Bool.and_false]
    rw [ih (fun e he => h e (List.Mem.tail entry he))]

/--
Every entry of `disableLocalBorrows borrows loc` that targets `loc` is
`.disabled`: no provenance tag minted from a previous allocation of `loc`
retains any access permission.
-/
theorem perm_eq_disabled_of_mem_disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local)
    {targetFrameDepth : Nat} :
    ∀ entry ∈ disableLocalBorrows borrows loc targetFrameDepth,
      entry.targetFrameDepth = targetFrameDepth →
      entry.targetLocal = loc → entry.perm = .disabled ∧ entry.allocDead = true := by
  induction borrows with
  | nil => intro entry hMem; nomatch hMem
  | cons hd rest ih =>
    intro entry hMem hD hT
    cases hB :
        Bool.and
          (Nat.beq hd.targetFrameDepth targetFrameDepth)
          (Nat.beq hd.targetLocal loc) with
    | true =>
      simp only [disableLocalBorrows, hB] at hMem
      cases hMem with
      | head => exact ⟨rfl, rfl⟩
      | tail _ hMemRest => exact ih entry hMemRest hD hT
    | false =>
      simp only [disableLocalBorrows, hB] at hMem
      cases hMem with
      | head =>
        have h1 : Nat.beq hd.targetFrameDepth targetFrameDepth = true := by
          rw [hD]; exact Nat.beq_refl targetFrameDepth
        have h2 : Nat.beq hd.targetLocal loc = true := by
          rw [hT]; exact Nat.beq_refl loc
        rw [h1, h2] at hB
        exact Bool.noConfusion hB
      | tail _ hMemRest => exact ih entry hMemRest hD hT

/--
Resolving provenance tag `tag` in `disableLocalBorrows borrows loc` yields the
entry that `tag` resolves to in `borrows`, disabled exactly when it targets
`loc`; tags without a stack borrow entry remain unresolved.
-/
theorem lookupBorrow_disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local)
    (tag : Nat)
    {targetFrameDepth : Nat} :
    lookupBorrow (disableLocalBorrows borrows loc targetFrameDepth) tag =
      (match lookupBorrow borrows tag with
       | .some entry =>
         match
           Bool.and
             (Nat.beq entry.targetFrameDepth targetFrameDepth)
             (Nat.beq entry.targetLocal loc)
         with
         | true => .some { entry with perm := .disabled, allocDead := true }
         | false => .some entry
       | .none => .none) := by
  induction borrows with
  | nil => rfl
  | cons hd rest ih =>
    cases hB :
        Bool.and
          (Nat.beq hd.targetFrameDepth targetFrameDepth)
          (Nat.beq hd.targetLocal loc) <;>
      cases hT : Nat.beq hd.tag tag <;>
        simp only [disableLocalBorrows, lookupBorrow, hB, hT, ih]

/--
A provenance tag that resolved to a borrow entry targeting `loc` resolves to
that entry disabled after `disableLocalBorrows borrows loc`.
-/
theorem lookupBorrow_disableLocalBorrows_of_targetLocal_eq
    (borrows : List BorrowEntry)
    (loc : Local)
    (tag : Nat)
    (entry : BorrowEntry)
    (hLookup : lookupBorrow borrows tag = .some entry)
    (hTarget : entry.targetLocal = loc)
    {targetFrameDepth : Nat}
    (hDepth : entry.targetFrameDepth = targetFrameDepth) :
    lookupBorrow (disableLocalBorrows borrows loc targetFrameDepth) tag =
      .some { entry with perm := .disabled, allocDead := true } := by
  rw [lookupBorrow_disableLocalBorrows, hLookup]
  have hB : Nat.beq entry.targetLocal loc = true := by
    rw [hTarget]
    exact Nat.beq_refl loc
  have hD : Nat.beq entry.targetFrameDepth targetFrameDepth = true := by
    rw [hDepth]
    exact Nat.beq_refl targetFrameDepth
  simp only [hB, hD, Bool.and_self]

/--
A provenance tag that resolved to a borrow entry targeting a local other than
`loc` resolves to the same entry after `disableLocalBorrows borrows loc`.
-/
theorem lookupBorrow_disableLocalBorrows_of_targetLocal_ne
    (borrows : List BorrowEntry)
    (loc : Local)
    (tag : Nat)
    (entry : BorrowEntry)
    (hLookup : lookupBorrow borrows tag = .some entry)
    (hTarget : entry.targetLocal ≠ loc)
    {targetFrameDepth : Nat} :
    lookupBorrow (disableLocalBorrows borrows loc targetFrameDepth) tag = .some entry := by
  rw [lookupBorrow_disableLocalBorrows, hLookup]
  have hB : Nat.beq entry.targetLocal loc = false := by
    cases hB' : Nat.beq entry.targetLocal loc with
    | false => rfl
    | true => exact False.elim (hTarget (Nat.eq_of_beq_eq_true hB'))
  simp only [hB, Bool.and_false]

/--
A provenance tag without a stack borrow entry in `borrows` (e.g. a pointer to a
captured global allocation) remains unresolved after
`disableLocalBorrows borrows loc`.
-/
theorem lookupBorrow_disableLocalBorrows_of_eq_none
    (borrows : List BorrowEntry)
    (loc : Local)
    (tag : Nat)
    (hLookup : lookupBorrow borrows tag = .none)
    {targetFrameDepth : Nat} :
    lookupBorrow (disableLocalBorrows borrows loc targetFrameDepth) tag = .none := by
  rw [lookupBorrow_disableLocalBorrows, hLookup]

/--
Test whether projection path `proj` contains a `.deref` projection, i.e.
whether computing the place loads a pointer value out of (a sub-place of) its
root local. In `Runtime(PostCleanup)` MIR a `Deref` may only appear as the
first projection of a place, so this coincides with `proj` starting with
`.deref` on well-formed bodies.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L114-L115>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1166-L1171>

> "Furthermore, `Deref` projections must be the first projection within any
> place (if they appear at all)"
>
> "A `Deref` projection begins by loading a value from the parent place, as if
> by [`Operand::Copy`]. It then dereferences the resulting pointer, creating a
> place of the pointee's type. The resulting address is the address that was
> stored in the pointer."
-/
def projectionHasDeref : List ProjectionElem → Bool
  | .nil => false
  | .deref :: _ => true
  | _ :: rest => projectionHasDeref rest

/--
Test whether every `.index idxLocal` projection in `proj` names a local of
`locals` holding an initialized scalar (`.init (.scalar _)`), i.e. whether
every index operand read while computing the place is initialized.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1192-L1279>

> "/// Index into a slice/array.
> ...
> Index(V),"
-/
def placeIndexLocalsInit (locals : List LocalSlot) : List ProjectionElem → Bool
  | .nil => true
  | .index idxLocal :: rest =>
    match get? locals idxLocal with
    | .some (.init (.scalar _)) => placeIndexLocalsInit locals rest
    | _ => false
  | _ :: rest => placeIndexLocalsInit locals rest

/--
Test whether every operand that `StatementKind.placeMention` reads while
computing a place with live root slot `rootSlot` and projection path `proj` in
`locals` is initialized:

1. when `proj` dereferences its root (`projectionHasDeref proj`), the root local
   must hold an initialized value (`.init _`) from which the pointer is loaded;
2. every `.index idxLocal` projection must name an initialized scalar local
   (`placeIndexLocalsInit locals proj`).

A bare mention of a live but uninitialized local (`proj = []`, `rootSlot =
.uninit`) reads nothing and remains defined. The place itself is never loaded,
so the pointee of a dereferenced raw pointer may be dangling. MiniRust
additionally requires the pointee of a dereferenced safe pointer (`&T`,
`&mut T`, `Box<T>`) to be dereferenceable when the place is computed; that
check is not modeled here, so `PlaceMention(*r)` through a dangling reference
`r` steps where MiniRust faults.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs>

> "This statement exists to preserve a trace of a scrutinee matched against a
> wildcard binding. This is especially useful for `let _ = PLACE;` bindings that
> desugar to a single `PlaceMention(PLACE)`.
>
> When executed at runtime, this computes the given place, but then discards
> it without doing a load. `let _ = *ptr;` is fine even if the pointer is
> dangling."

Reference (MiniRust `spec/lang/step/expressions.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/expressions.md#L250-L256>

> "// We know the pointer is valid for its type, but make sure safe pointers are also dereferenceable.
> // (We don't do a full retag here, this is not considered creating a new pointer.)
> if let Some(pointee) = ptr_type.safe_pointee() {
> ...
>     self.mem.dereferenceable(ptr.thin_pointer, self.compute_size(pointee.layout, ptr.metadata))?;
> }"
-/
def placeMentionOperandsInit
    (locals : List LocalSlot)
    (rootSlot : LocalSlot)
    (proj : List ProjectionElem) :
    Bool :=
  match projectionHasDeref proj, rootSlot with
  | true, .init _ => placeIndexLocalsInit locals proj
  | true, _ => false
  | false, _ => placeIndexLocalsInit locals proj

/--
Definitional simplification equation for `projectionHasDeref` on the empty
projection.
-/
@[simp]
theorem projectionHasDeref_nil : projectionHasDeref .nil = false := rfl

/--
Definitional simplification equation for `placeIndexLocalsInit` on the empty
projection.
-/
@[simp]
theorem placeIndexLocalsInit_nil (locals : List LocalSlot) :
    placeIndexLocalsInit locals .nil = true := rfl

/--
A bare `PlaceMention` of a local (empty projection) reads no operand, so
`placeMentionOperandsInit` holds for every root slot.
-/
@[simp]
theorem placeMentionOperandsInit_nil (locals : List LocalSlot) (rootSlot : LocalSlot) :
    placeMentionOperandsInit locals rootSlot .nil = true := by
  cases rootSlot <;> rfl

/--
Materialize inner aggregate shells along a chain of intermediate aggregate
`.field` projections inside `val` whenever the current slot at `fieldIdx` is
absent (on a union shell `.aggregate 0 .nil`), `.unit` (inactive union slot), or
`Value.uninit` (uninitialized non-union aggregate field).

1. When `fieldTy.kind` is a struct/union (`.adt _ _`) or tuple (`.tuple _`) and
   the remaining projection path continues with `.field nextIdx _`,
   `uninitContainerFieldShell?` materializes an arity-padded `Value.uninit`
   shell (`.aggregate 0 (replicateValue arity .uninit)`) for non-union tuples
   and single-variant structs, or `.aggregate 0 .nil` for unions, failing closed
   with `.none` when a non-union `.adt` has unknown arity or `nextIdx` is out of
   bounds.
2. Fixed-length array fields (`.array _ _`) are never materialized, so an
   element write through a never-written array field (`_u.arr[i] = val`) faults
   with `.ub`.

`evalStmt` and `writeReturnDestination` apply this both to the initial root
shell of an uninitialized destination (`uninitFieldWriteShell?`) and to the
current value of an initialized destination before a projected write.
Transparent metadata projections (`.opaqueCast` and `.unwrapUnsafeBinder`) are
traversed without altering the value, and `stripTransparentProjections` is used
when checking whether the remaining projection chain continues with a `.field`
projection. Every slot it visits that is already present and neither `.unit` nor
`.uninit` is kept as is, so on a root whose intermediate field slots along the
chain are all populated (`fieldShellChainPopulated`) the result is `.some val`
and the write coincides with `writeProjectedValue` on the original root.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1135-L1165>

> "- [`Field`](ProjectionElem::Field): `Field` projections take their parent
>   place and create a place referring to one of the fields of the type."
-/
def ensureNestedFieldShells
    (val : Value)
    (projs : List ProjectionElem)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (curTyOpt : Option Ty := .none) :
    Option Value :=
  match projs with
  | .opaqueCast castTy :: nextProj :: rest =>
    let nextTyOpt :=
      match curTyOpt with
      | .some _ => .some (resolveTyWithLocalDecls localDecls layouts castTy)
      | .none => .none
    ensureNestedFieldShells val (nextProj :: rest) localDecls layouts nextTyOpt
  | .unwrapUnsafeBinder innerTy :: nextProj :: rest =>
    let nextTyOpt :=
      match curTyOpt with
      | .some _ => .some (resolveTyWithLocalDecls localDecls layouts innerTy)
      | .none => .none
    ensureNestedFieldShells val (nextProj :: rest) localDecls layouts nextTyOpt
  | .field fieldIdx fieldTy :: nextProj :: rest =>
    match val with
    | .aggregate variantIdx fields =>
      let isInnerAggField :=
        match stripTransparentProjections (nextProj :: rest), fieldTy.kind with
        | .field _ _ :: _, .adt _ _ => true
        | .field _ _ :: _, .tuple _ => true
        | _, _ => false
      match isInnerAggField with
      | true =>
        let resolvedFieldTy : Ty :=
          match curTyOpt with
          | .some curTy =>
            resolveFieldStepTy
              localDecls
              layouts
              (resolveTyWithLocalDecls localDecls layouts curTy)
              fieldIdx
              fieldTy
          | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
        let nextFirstIdxOpt : Option FieldIdx :=
          match stripTransparentProjections (nextProj :: rest) with
          | .field nextIdx _ :: _ => .some nextIdx
          | _ => .none
        let materializeChild : Option Value :=
          match nextFirstIdxOpt with
          | .none => .none
          | .some nextIdx =>
            match uninitContainerFieldShell? localDecls layouts resolvedFieldTy nextIdx with
            | .none => .none
            | .some emptyChild =>
              ensureNestedFieldShells
                emptyChild
                (nextProj :: rest)
                localDecls
                layouts
                (.some resolvedFieldTy)
        match get? fields fieldIdx with
        | .none =>
          let allowExtend :=
            match curTyOpt with
            | .some curTy =>
              isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts curTy)
            | .none => false
          match allowExtend, materializeChild with
          | true, .some childShell =>
            .some (.aggregate variantIdx (setOrExtendFields fields fieldIdx childShell))
          | _, _ => .none
        | .some .unit =>
          match materializeChild with
          | .some childShell =>
            match set? fields fieldIdx childShell with
            | .some fields' => .some (.aggregate variantIdx fields')
            | .none => .none
          | .none => .none
        | .some .uninit =>
          match materializeChild with
          | .some childShell =>
            match set? fields fieldIdx childShell with
            | .some fields' => .some (.aggregate variantIdx fields')
            | .none => .none
          | .none => .none
        | .some childVal =>
          match
            ensureNestedFieldShells
              childVal
              (nextProj :: rest)
              localDecls
              layouts
              (.some resolvedFieldTy)
          with
          | .some childVal' =>
            match set? fields fieldIdx childVal' with
            | .some fields' => .some (.aggregate variantIdx fields')
            | .none => .some (.aggregate variantIdx fields)
          | .none => .none
      | false => .some (.aggregate variantIdx fields)
    | _ => .some val
  | _ => .some val

/--
Whether every intermediate struct, union, or tuple field slot that
`ensureNestedFieldShells val projs` inspects along `projs` is already present
and neither `.unit` union placeholder nor `Value.uninit`.

When `fieldShellChainPopulated val projs = true`,
`ensureNestedFieldShells val projs localDecls layouts curTyOpt` returns
`.some val` unchanged (`ensureNestedFieldShells_eq_self_of_populated`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1135-L1165>

> "- [`Field`](ProjectionElem::Field): `Field` projections take their parent
>   place and create a place referring to one of the fields of the type."
-/
def fieldShellChainPopulated : Value → List ProjectionElem → Bool
  | val, .opaqueCast _ :: nextProj :: rest =>
    fieldShellChainPopulated val (nextProj :: rest)
  | val, .unwrapUnsafeBinder _ :: nextProj :: rest =>
    fieldShellChainPopulated val (nextProj :: rest)
  | .aggregate _ fields, .field fieldIdx fieldTy :: nextProj :: rest =>
    let isInnerAggField :=
      match stripTransparentProjections (nextProj :: rest), fieldTy.kind with
      | .field _ _ :: _, .adt _ _ => true
      | .field _ _ :: _, .tuple _ => true
      | _, _ => false
    match isInnerAggField with
    | true =>
      match get? fields fieldIdx with
      | .none => false
      | .some .unit => false
      | .some .uninit => false
      | .some childVal => fieldShellChainPopulated childVal (nextProj :: rest)
    | false => true
  | _, _ => true

/--
Default root value for a projected assignment `dst = rv` into a live but
uninitialized destination local `loc` (`.uninit`) whose first projection `proj`
is an in-bounds field projection (`.field fieldIdx fieldTy`) and whose declared
type (`placeTy localDecls layouts { local_ := loc, projection := .nil }`) is a
tuple, a single-variant struct with known layout arity, or a union:
- For non-union tuples and single-variant structs (`uninitContainerFieldShell?`),
  the root shell is `.aggregate 0 (replicateValue arity .uninit)` with every
  slot `0 .. arity - 1` set to `Value.uninit`, and `ensureNestedFieldShells`
  recursively pads any nested intermediate struct/tuple shells along `rest` to
  their declared arities so whole-aggregate reads and reads of unwritten lower
  or higher sibling fields fault with `.ub`.
- For unions (`isUnionLayout = true`), the shell starts as `.aggregate 0 .nil`
  so `writeProjectedForLocal` applies raw-byte union overlay semantics.
- When `proj` is a leading `ProjectionElem.opaqueCast`
  (`DIV-TR-OPAQUECAST-ROOT-DISPATCH`), the leading cast chain is stripped
  (`stripLeadingOpaqueCast`) and the shell is the one of the field projection
  below it, keyed on the effective cast type: local `loc` is re-declared at
  that type (`eraseLeadingOpaqueCastDecls`), because `(_loc as T).f = v` writes
  field `f` of `_loc` at type `T`, not at the local's declared opaque type.
- When `proj` is neither `.field` nor a cast chain followed by `.field`,
  `fieldIdx` is out of bounds, or a non-union container along the path has
  unknown arity, returns `.none` (fail-closed).

Reference (MiniRust `spec/lang/step/statements.md` at commit
`d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed`):
<https://github.com/minirust/minirust/blob/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/spec/lang/step/statements.md#L32-L38>

> "fn eval_statement(&mut self, Statement::Assign { destination, source }: Statement) -> NdResult {
>     let (place, ty) = self.eval_place(destination)?;
>     let (val, _) = self.eval_value(source)?;
>     self.place_store(place, val, ty)?;"

Reference (The Rust Reference, "Union types"):
<https://doc.rust-lang.org/1.98.0/reference/items/unions.html#reading-and-writing-union-fields>

> "Unions have no notion of an \"active field\". Instead, every union access
> just interprets the storage as the type of the field used for the access."

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1148-L1150>

> "///  - [`OpaqueCast`](ProjectionElem::OpaqueCast): This projection changes the place's type to the
> ///    given one, and makes no other changes. A `OpaqueCast` projection on any type other than an
> ///    opaque type from the current crate is not well-formed."

Justification for the cast arm: the cast "changes the place's type to the given
one, and makes no other changes", so the container whose field shell is
allocated is the local at the cast type.
-/
def uninitFieldWriteShell?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem := .nil) :
    Option Value :=
  match proj with
  | .field fieldIdx fieldTy =>
    match placeTy localDecls layouts { local_ := loc, projection := .nil } with
    | .some rootTy =>
      match uninitContainerFieldShell? localDecls layouts rootTy fieldIdx with
      | .some rootShell =>
        ensureNestedFieldShells
          rootShell
          (.field fieldIdx fieldTy :: rest)
          localDecls
          layouts
          (.some rootTy)
      | .none => .none
    | .none => .none
  | .opaqueCast castTy =>
    match stripLeadingOpaqueCast rest with
    | .field fieldIdx fieldTy :: fieldRest =>
      let castDecls :=
        eraseLeadingOpaqueCastDecls localDecls layouts loc (.opaqueCast castTy :: rest)
      match placeTy castDecls layouts { local_ := loc, projection := .nil } with
      | .some rootTy =>
        match uninitContainerFieldShell? castDecls layouts rootTy fieldIdx with
        | .some rootShell =>
          ensureNestedFieldShells
            rootShell
            (.field fieldIdx fieldTy :: fieldRest)
            castDecls
            layouts
            (.some rootTy)
        | .none => .none
      | .none => .none
    | _ => .none
  | _ => .none

/--
Execute a function-entry retag (`RetagKind::FnEntry`) of the reference stored
in `place`, whose current value is `.ptr ptrVal sz` with live borrow entry
`parentEntry`, after `evalOperand` produced `locals'`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L276-L287>

> "pub enum RetagKind {
>     /// The initial retag of arguments when entering a function.
>     FnEntry,"

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/mod.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/mod.rs#L211-L216>

> "protector: is_protected.then_some(if ref_mutability.is_some() {
>     // Strong protector for references
>     ProtectorKind::StrongProtector"
-/
def evalFnEntryRetag
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (place : Place)
    (ptrVal : ProvenancePtr)
    (sz : Nat)
    (parentEntry : BorrowEntry)
    (locals' : List LocalSlot) :
    MirStepNode :=
  let protId := s.memory.nextProtector
  let attachOnly :=
    MirStepNode.step
      (advanceStmt
        s
        locals'
        { s.memory with
          borrows := attachBorrowProtector s.memory.borrows ptrVal.tag protId
          activeProtectors := protId :: s.memory.activeProtectors
          nextProtector := Nat.add protId 1 })
  match placeTy localDecls layouts place with
  | .none => attachOnly
  | .some ty =>
    match ty.kind with
    | .ref mutability pointee =>
      match rigidTyIsUninhabited 16 pointee with
      | true => MirStepNode.fail .ub
      | false =>
        let childPerm := fnEntryRetagPerm mutability pointee
        let skipInitRead :=
          match childPerm with
          | .cell => true
          | _ => rigidTyIsZeroSized 16 pointee
        let tag := s.memory.nextTag
        let readUB :=
          match skipInitRead with
          | true => false
          | false =>
            hasTreeReadUB
              s.memory.borrows
              s.memory.borrows
              s.memory.activeProtectors
              parentEntry.targetLocal
              (.some ptrVal.tag)
              parentEntry.targetProjection
              parentEntry.rangeOffset
              parentEntry.rangeLen
              parentEntry.targetFrameDepth
        match readUB with
        | true => MirStepNode.fail .ub
        | false =>
          let borrowsAfterRead :=
            match skipInitRead with
            | true => s.memory.borrows
            | false =>
              freezeTreeBorrowsOnReadAtProj
                s.memory.borrows
                s.memory.borrows
                parentEntry.targetLocal
                (.some ptrVal.tag)
                parentEntry.targetProjection
                parentEntry.rangeOffset
                parentEntry.rangeLen
                s.memory.activeProtectors
                parentEntry.targetFrameDepth
          let child : BorrowEntry := {
            tag := tag
            targetLocal := parentEntry.targetLocal
            targetFrameDepth := parentEntry.targetFrameDepth
            allocDead := parentEntry.allocDead
            targetProjection := parentEntry.targetProjection
            perm := childPerm
            rangeOffset := parentEntry.rangeOffset
            rangeLen := parentEntry.rangeLen
            protector := .some protId
            parentTag := .some ptrVal.tag
          }
          match place.projection with
          | .nil =>
            match
              set?
                locals'
                place.local_
                (.init
                  (.ptr
                    { allocId := tag, offsetBytes := ptrVal.offsetBytes }
                    sz))
            with
            | .some locals'' =>
              MirStepNode.step
                (advanceStmt
                  s
                  locals''
                  { s.memory with
                    borrows := child :: borrowsAfterRead
                    nextTag := Nat.add tag 1
                    activeProtectors := protId :: s.memory.activeProtectors
                    nextProtector := Nat.add protId 1 })
            | .none => MirStepNode.fail .ub
          | _ :: _ => MirStepNode.unsupported
    | _ => attachOnly

/--
Execute a non-function-entry MIR retag (`RetagKind.default`, `.twoPhase`, or
`.raw`) on `place`, whose value in `s.frame.locals` is `(.ptr ptrVal sz)` with
existing non-disabled `parentEntry`.

When `place` resolves in `localDecls` / `layouts` to a reference `&T` or
`&mut T`, an uninhabited `pointee` (`rigidTyIsUninhabited 16 pointee = true`)
faults immediately with `MirStepNode.fail .ub`; otherwise Miri's
`tb_retag_ptr_value` / `tb_reborrow` allocates a fresh
unprotected child tag under `ptrVal.tag` with `retagPerm retagKind mutability
pointee`, performs an initial child read through `ptrVal.tag` unless the new
permission is `.cell` (`Permission::associated_access`) or the pointee is
zero-sized (`rigidTyIsZeroSized 16 pointee`), and writes the new provenance
back into `place`. When `place`'s type is unknown or non-reference, falls back
to advancing without creating a child tag.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/mod.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/mod.rs#L198-L212>

> "let associated_access = perm.associated_access();"
-/
def evalNonFnEntryRetag
    (retagKind : RetagKind)
    (s : MachineState)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (place : Place)
    (ptrVal : ProvenancePtr)
    (sz : Nat)
    (parentEntry : BorrowEntry)
    (locals' : List LocalSlot) :
    MirStepNode :=
  match placeTy localDecls layouts place with
  | .none => MirStepNode.step (advanceStmt s locals')
  | .some ty =>
    match ty.kind with
    | .ref mutability pointee =>
      match rigidTyIsUninhabited 16 pointee with
      | true => MirStepNode.fail .ub
      | false =>
        let childPerm := retagPerm retagKind mutability pointee
        let skipInitRead :=
          match childPerm with
          | .cell => true
          | _ => rigidTyIsZeroSized 16 pointee
        let tag := s.memory.nextTag
        let readUB :=
          match skipInitRead with
          | true => false
          | false =>
            hasTreeReadUB
              s.memory.borrows
              s.memory.borrows
              s.memory.activeProtectors
              parentEntry.targetLocal
              (.some ptrVal.tag)
              parentEntry.targetProjection
              parentEntry.rangeOffset
              parentEntry.rangeLen
              parentEntry.targetFrameDepth
        match readUB with
        | true => MirStepNode.fail .ub
        | false =>
          let borrowsAfterRead :=
            match skipInitRead with
            | true => s.memory.borrows
            | false =>
              freezeTreeBorrowsOnReadAtProj
                s.memory.borrows
                s.memory.borrows
                parentEntry.targetLocal
                (.some ptrVal.tag)
                parentEntry.targetProjection
                parentEntry.rangeOffset
                parentEntry.rangeLen
                s.memory.activeProtectors
                parentEntry.targetFrameDepth
          let child : BorrowEntry := {
            tag := tag
            targetLocal := parentEntry.targetLocal
            targetFrameDepth := parentEntry.targetFrameDepth
            allocDead := parentEntry.allocDead
            targetProjection := parentEntry.targetProjection
            perm := childPerm
            rangeOffset := parentEntry.rangeOffset
            rangeLen := parentEntry.rangeLen
            protector := .none
            parentTag := .some ptrVal.tag
          }
          match place.projection with
          | .nil =>
            match
              set?
                locals'
                place.local_
                (.init
                  (.ptr
                    { allocId := tag, offsetBytes := ptrVal.offsetBytes }
                    sz))
            with
            | .some locals'' =>
              MirStepNode.step
                (advanceStmt
                  s
                  locals''
                  { s.memory with
                    borrows := child :: borrowsAfterRead
                    nextTag := Nat.add tag 1 })
            | .none => MirStepNode.fail .ub
          | _ :: _ => MirStepNode.unsupported
    | _ => MirStepNode.step (advanceStmt s locals')

/--
Truncate a resolved local projection path at the first `.field` projection whose
container type resolves to a `FieldsShape.union` layout (`isUnionLayout`).

Because all fields of a Rust `union` alias at byte offset `0` (`FieldsShape::Union`),
a projected write into `_u.f` (or `(s.u).f` inside an outer struct/tuple `s`) is
conservatively treated as overlapping the entire union sub-place (`[]` for
`_u.f`, `[.field idxU unionTy]` for `(s.u).f`), invalidating or
protector-conflicting with borrows of any sibling union field while preserving
borrows of disjoint outer struct/tuple/array fields.

This is exact for borrows of whole sibling fields of nonzero size (every union
field starts at offset `0`, so any nonzero-sized write and any nonzero-sized
sibling field share byte `0`). Zero-sized writes (`placeIsZeroSized`) skip
union-level projection truncation in `resolveBorrowWriteLocalProj` and
`resolveDerefBorrowWriteFullProj`, retaining Anneal's untruncated projection
overlap: sibling union-field borrows are preserved, though (unlike Miri's
zero-byte access) foreign borrows of the ZST sub-place itself or enclosing
whole-union `[]` borrows are still invalidated. It also over-approximates
Miri's byte-range Tree Borrows access when a nonzero-sized written or borrowed
sub-place covers bytes disjoint from the other (for example a write to `_u.f.g`
versus a borrow of `_u.f.h`, or a 1-byte write to `_u.a` versus a borrow of
byte `1` of a wider sibling field), or when a sibling borrow targets a
zero-sized union field: Anneal then disables, or reports a protector conflict
on, a borrow that Miri's access leaves untouched.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1649-L1650>

> "/// All fields start at no offset. The `usize` is the field count.
> Union(NonZeroUsize),"
-/
@[reducible]
def truncateTyProjAtUnion
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (baseTy : Ty) :
    List ProjectionElem → List ProjectionElem
  | .nil => .nil
  | .deref :: rest => .deref :: rest
  | .field fieldIdx fieldTy :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    match isUnionLayout layouts rBase with
    | true => .nil
    | false =>
      let nextTy : Ty :=
        match isUnresolvedLayoutIdx layouts fieldTy.layoutIdx with
        | false => fieldTy
        | true =>
          match LayoutTable.lookup layouts rBase.layoutIdx with
          | .some l =>
            match l.variants with
            | .single _ =>
              match get? l.fieldLayouts fieldIdx with
              | .some flIdx => { fieldTy with layoutIdx := flIdx }
              | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
            | _ => resolveTyWithLocalDecls localDecls layouts fieldTy
          | .none => resolveTyWithLocalDecls localDecls layouts fieldTy
      .field fieldIdx fieldTy ::
        truncateTyProjAtUnion localDecls layouts nextTy rest
  | .opaqueCast castTy :: rest =>
    .opaqueCast castTy ::
      truncateTyProjAtUnion
        localDecls
        layouts
        (resolveTyWithLocalDecls localDecls layouts castTy)
        rest
  | .unwrapUnsafeBinder innerTy :: rest =>
    .unwrapUnsafeBinder innerTy ::
      truncateTyProjAtUnion
        localDecls
        layouts
        (resolveTyWithLocalDecls localDecls layouts innerTy)
        rest
  | .index idxLocal :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    match elemTyOf rBase with
    | .some { kind := ek, .. } =>
      let elemTy : Ty :=
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          resolveTyWithLocalDecls
            localDecls
            layouts
            { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      .index idxLocal ::
        truncateTyProjAtUnion localDecls layouts elemTy rest
    | .none => .index idxLocal :: rest
  | .constantIndex off minLen fromEnd :: rest =>
    let rBase := resolveTyWithLocalDecls localDecls layouts baseTy
    match elemTyOf rBase with
    | .some { kind := ek, .. } =>
      let elemTy : Ty :=
        match LayoutTable.lookup layouts rBase.layoutIdx with
        | .some { fields := .array _ _, fieldLayouts := flIdx :: _, .. } =>
          { kind := ek, layoutIdx := flIdx }
        | _ =>
          resolveTyWithLocalDecls
            localDecls
            layouts
            { kind := ek, layoutIdx := synthKindLayoutIdx layouts ek }
      .constantIndex off minLen fromEnd ::
        truncateTyProjAtUnion localDecls layouts elemTy rest
    | .none => .constantIndex off minLen fromEnd :: rest
  | .subslice fromIdx toIdx fromEnd :: rest =>
    .subslice fromIdx toIdx fromEnd ::
      truncateTyProjAtUnion localDecls layouts baseTy rest
  | .downcast variantName variantIdx :: rest =>
    .downcast variantName variantIdx ::
      truncateTyProjAtUnion localDecls layouts baseTy rest

/--
Resolve the effective borrow-invalidation and protector-conflict projection path
for a non-dereference projected local write `dst = ⟨dstLoc, projs⟩`.

When `placeTouchesUnion localDecls layouts ⟨dstLoc, projs⟩` is `false` (all
non-union struct/tuple/enum/array writes, or when `localDecls` / `layouts` is
empty) or `placeIsZeroSized localDecls layouts ⟨dstLoc, projs⟩` is `true` (a
zero-byte write, which touches no storage bytes), returns the
dynamic-index-resolved projection path unchanged. Otherwise truncates at the
enclosing union container via `truncateTyProjAtUnion` so nonzero-sized writes to
one union field overlap borrows of all sibling union fields.

Frame-local dereferencing writes (`(*p).f = v`, or `*p = v` where `p` borrows a
union field) apply the same truncation via `resolveDerefBorrowWriteFullProj`,
`derefWriteUnionProtectorUB`, and `invalidateDerefWriteBorrowsWithLayouts`
(whereas writes to `callerLocals` carry no caller `LocalDecl` table in `Memory`
and remain untyped).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def resolveBorrowWriteLocalProj
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (dstLoc : Local)
    (projs : List ProjectionElem) :
    List ProjectionElem :=
  let resolvedLocalProj :=
    match resolveBorrowProjectionElems locals projs with
    | .some rp => rp
    | .none => projs
  match
    Bool.and
      (placeTouchesUnion
        localDecls
        layouts
        { local_ := dstLoc, projection := projs })
      (Bool.not
        (placeIsZeroSized
          localDecls
          layouts
          { local_ := dstLoc, projection := projs }))
  with
  | false => resolvedLocalProj
  | true =>
    match get? localDecls dstLoc with
    | .some decl =>
      truncateTyProjAtUnion localDecls layouts decl.ty resolvedLocalProj
    | .none => resolvedLocalProj

/--
Non-union identity for `resolveBorrowWriteLocalProj`: whenever
`placeTouchesUnion localDecls layouts ⟨dstLoc, projs⟩ = false`,
`resolveBorrowWriteLocalProj` reduces to `resolveBorrowProjectionElems` with
fallback `projs`.
-/
theorem resolveBorrowWriteLocalProj_of_not_union
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (dstLoc : Local)
    (projs : List ProjectionElem)
    (hNoUnion :
      placeTouchesUnion localDecls layouts { local_ := dstLoc, projection := projs } = false) :
    resolveBorrowWriteLocalProj localDecls layouts locals dstLoc projs =
      (match resolveBorrowProjectionElems locals projs with
       | .some rp => rp
       | .none => projs) := by
  unfold resolveBorrowWriteLocalProj
  rw [hNoUnion]
  rfl

/--
Zero-sized write identity for `resolveBorrowWriteLocalProj`: whenever
`placeIsZeroSized localDecls layouts ⟨dstLoc, projs⟩ = true`, a zero-byte write
does not truncate at an enclosing union container.
-/
theorem resolveBorrowWriteLocalProj_of_zst
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (dstLoc : Local)
    (projs : List ProjectionElem)
    (hZst :
      placeIsZeroSized localDecls layouts { local_ := dstLoc, projection := projs } = true) :
    resolveBorrowWriteLocalProj localDecls layouts locals dstLoc projs =
      (match resolveBorrowProjectionElems locals projs with
       | .some rp => rp
       | .none => projs) := by
  unfold resolveBorrowWriteLocalProj
  rw [hZst]
  cases placeTouchesUnion localDecls layouts { local_ := dstLoc, projection := projs } <;> rfl

/--
Resolve the effective borrow-invalidation and protector-conflict projection path
for a frame-local dereferencing write whose resolved target sub-place on
`targetLocal` is `fullProj` (`resolveDerefWriteFullProj`).

Short-circuits definitionally to `.nil` when `fullProj = .nil`. When `fullProj`
is non-empty, truncates at the first enclosing `FieldsShape.union` container via
`truncateTyProjAtUnion` whenever `placeTouchesUnion` is `true` and
`placeIsZeroSized` is `false`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def resolveDerefBorrowWriteFullProj
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (targetLocal : Local)
    (fullProj : List ProjectionElem) :
    List ProjectionElem :=
  match fullProj with
  | .nil => .nil
  | pHead :: pTail =>
    match
      Bool.and
        (placeTouchesUnion
          localDecls
          layouts
          { local_ := targetLocal, projection := pHead :: pTail })
        (Bool.not
          (placeIsZeroSized
            localDecls
            layouts
            { local_ := targetLocal, projection := pHead :: pTail }))
    with
    | false => pHead :: pTail
    | true =>
      match get? localDecls targetLocal with
      | .some decl =>
        truncateTyProjAtUnion localDecls layouts decl.ty (pHead :: pTail)
      | .none => pHead :: pTail

/--
Test whether a frame-local dereferencing write to `dst` (`dst = ⟨ptrLoc, .deref :: restProj⟩`)
conflicts with an active function-entry protector after union-container
truncation (`resolveDerefBorrowWriteFullProj`), catching sibling union-field
protector conflicts on `(*p).f = val` and `*p = val` (`p = &mut _u.f`).
Short-circuits definitionally to `false` when `activeProtectors = .nil` or when
`fullProj = .nil` (already checked by `evalPlaceWrite`).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def derefWriteUnionProtectorUB
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals₁ : List LocalSlot)
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (dst : Place)
    (restProj : List ProjectionElem)
    (callStack : List SavedCallerFrame := .nil) :
    Bool :=
  match activeProtectors with
  | .nil => false
  | pH :: pT =>
    let prots := pH :: pT
    match get? locals₁ dst.local_ with
    | .some (.init ptrOrFatVal) =>
      match extractDerefPtrVal? ptrOrFatVal with
      | .some ptrVal =>
        match lookupBorrow borrows ptrVal.tag with
        | .some entry =>
          let fullProj :=
            resolveDerefWriteFullProj locals₁ locals₁ ptrOrFatVal entry restProj .nil callStack
          match fullProj with
          | .nil => false
          | fHead :: fTail =>
            let effProj :=
              resolveDerefBorrowWriteFullProj
                localDecls layouts entry.targetLocal (fHead :: fTail)
            match borrows with
            | b₁ :: b₂ :: restBorrows =>
              let allBorrows := b₁ :: b₂ :: restBorrows
              hasProtectedTreeWriteConflict
                allBorrows
                allBorrows
                prots
                entry.targetLocal
                (.some ptrVal.tag)
                effProj
                entry.rangeOffset
                entry.rangeLen
                entry.targetFrameDepth
            | _ =>
              hasProtectedWriteConflict
                borrows
                prots
                entry.targetLocal
                (.some ptrVal.tag)
                effProj
                entry.rangeOffset
                entry.rangeLen
                entry.targetFrameDepth
        | .none => false
      | .none => false
    | _ => false

/--
Layout-aware counterpart of `invalidateDerefWriteBorrows` for frame-local
dereferencing writes in `evalStmt`: resolves `fullProj` via
`resolveDerefWriteFullProj`, truncates nonzero-sized union field paths via
`resolveDerefBorrowWriteFullProj` (`R1`), and updates Tree Borrows permissions
across `borrows`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
@[reducible]
def invalidateDerefWriteBorrowsWithLayouts
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals₁ : List LocalSlot)
    (borrows : List BorrowEntry)
    (dst : Place)
    (restProj : List ProjectionElem)
    (callStack : List SavedCallerFrame := .nil) :
    List BorrowEntry :=
  match borrows with
  | .nil => .nil
  | single :: .nil =>
    let b := single :: .nil
    match get? locals₁ dst.local_ with
    | .some (.init ptrOrFatVal) =>
      match extractDerefPtrVal? ptrOrFatVal with
      | .some ptrVal =>
        match lookupBorrow b ptrVal.tag with
        | .some entry =>
          let fullProj :=
            resolveDerefWriteFullProj
              locals₁
              locals₁
              ptrOrFatVal
              entry
              restProj
              .nil
              callStack
          let effProj :=
            resolveDerefBorrowWriteFullProj
              localDecls
              layouts
              entry.targetLocal
              fullProj
          match effProj with
          | .nil =>
            match Nat.beq entry.rangeLen 0 with
            | true =>
              invalidateConflictingBorrows
                b
                entry.targetLocal
                (.some ptrVal.tag)
                entry.targetFrameDepth
            | false =>
              invalidateConflictingBorrowsAtProj
                b
                entry.targetLocal
                (.some ptrVal.tag)
                .nil
                entry.rangeOffset
                entry.rangeLen
                entry.targetFrameDepth
          | pHead :: pTail =>
            invalidateConflictingBorrowsAtProj
              b
              entry.targetLocal
              (.some ptrVal.tag)
              (pHead :: pTail)
              entry.rangeOffset
              entry.rangeLen
              entry.targetFrameDepth
        | .none => b
      | .none => b
    | _ => b
  | b₁ :: b₂ :: restBorrows =>
    let allBorrows := b₁ :: b₂ :: restBorrows
    match get? locals₁ dst.local_ with
    | .some (.init ptrOrFatVal) =>
      match extractDerefPtrVal? ptrOrFatVal with
      | .some ptrVal =>
        match lookupBorrow allBorrows ptrVal.tag with
        | .some entry =>
          let fullProj :=
            resolveDerefWriteFullProj
              locals₁
              locals₁
              ptrOrFatVal
              entry
              restProj
              .nil
              callStack
          let effProj :=
            resolveDerefBorrowWriteFullProj
              localDecls
              layouts
              entry.targetLocal
              fullProj
          invalidateTreeBorrowsAtProj
            allBorrows
            allBorrows
            entry.targetLocal
            (.some ptrVal.tag)
            effProj
            entry.rangeOffset
            entry.rangeLen
            entry.targetFrameDepth
        | .none => allBorrows
      | .none => allBorrows
    | _ => allBorrows

/--
`SetDiscriminant` may initialize an `.uninit` local only when the local is
declared at an ADT type (or has no declaration, as in declaration-free test
bodies); any other declared type fails closed (`DIV-LM-ENUM-SET-DISCR-UNINIT`).

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L357-L363>

> "/// Write the discriminant for a variant to the enum Place.
> ///
> /// This is permitted for both coroutines and ADTs. This does not necessarily
> /// write to the entire place; instead, it writes to the minimum set of bytes
> /// as required by the layout for the type.
> SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },"
-/
def setDiscriminantUninitDeclOk
    (localDecls : List LocalDecl)
    (loc : Local) :
    Bool :=
  match get? localDecls loc with
  | .some decl =>
    match decl.ty.kind with
    | .adt _ _ => true
    | _ => false
  | .none => true

/--
Construct the `Value.uninit`-padded payload field list for `SetDiscriminant(loc, variantIdx)`
on an `.uninit` local `loc` using `enumVariantPayloadArity?`, returning `.none`
(fail-closed) when `loc`'s declaration or captured variant layout is absent or
`variantIdx` is out of bounds.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L357-L363>

> "/// Write the discriminant for a variant to the enum Place.
> ///
> /// This is permitted for both coroutines and ADTs. This does not necessarily
> /// write to the entire place; instead, it writes to the minimum set of bytes
> /// as required by the layout for the type.
> SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },"
-/
@[reducible]
def setDiscriminantUninitPayload?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (variantIdx : VariantIdx) :
    Option (List Value) :=
  match get? localDecls loc with
  | .some decl =>
    match enumVariantPayloadArity? localDecls layouts decl.ty variantIdx with
    | .some arity => .some (replicateValue arity .uninit)
    | .none => .none
  | .none => .none

/--
Validate and pad the payload field list `fields` of an already-initialized
aggregate at `p` when `SetDiscriminant(p, variantIdx)` sets its variant to
`variantIdx`:
- When `p` resolves to an ADT with a captured layout entry in `layouts` and
  `variantIdx` is an inhabited in-range variant with payload arity `arity`
  (`enumVariantPayloadArity?`), pads trailing slots up to `arity` with
  `Value.uninit` (`padFieldsToArity`), so switching from a narrower variant
  (such as `None`) to a wider variant (`Some(T)`) marks the unwritten payload
  fields uninitialized.
- Otherwise (no resolved place type, a non-ADT place such as a coroutine, no
  captured layout entry, or an out-of-range or uninhabited `variantIdx`),
  returns `.none`, so `evalStmt` fails closed with `.ub`: without the target
  variant's arity the model cannot tell which payload fields the new variant
  leaves uninitialized, and keeping a shorter `fields` list would let a later
  whole-value read of `p` succeed although trailing payload fields were never
  written. This matches `setDiscriminantUninitPayload?`, which fails closed on
  the same missing layout data for an `.uninit` local.

Modeling note (`agent_docs/trusted-rust.md`): the quoted documentation says
`SetDiscriminant` writes only the bytes the layout requires for the tag, so the
model keeps the payload values already present in `fields` under the new
variant. Those values describe the underlying bytes at the new variant's field
types only when each retained field of the target variant has the same offset,
size, and type as the corresponding field of the source variant (as in the
shared-prefix witnesses `wit_lm2_3_prefix_setDiscriminant_read` and
`wit_lm2_3_upcast_setDiscriminant_read_and_trailing_ub`). Re-reading a retained
`Value` at a target-variant field whose offset, size, or type differs is not
justified by the quoted documentation and remains an unsupported modeling
assumption of this definition.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L357-L363>

> "/// Write the discriminant for a variant to the enum Place.
> ///
> /// This is permitted for both coroutines and ADTs. This does not necessarily
> /// write to the entire place; instead, it writes to the minimum set of bytes
> /// as required by the layout for the type.
> SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },"
-/
@[reducible]
def padSetDiscriminantInitFields?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (p : Place)
    (variantIdx : VariantIdx)
    (fields : List Value) :
    Option (List Value) :=
  match placeTyResolved localDecls layouts p with
  | .some pTy =>
    match pTy.kind with
    | .adt _ _ =>
      let rTy := resolveTyWithLocalDecls localDecls layouts pTy
      match LayoutTable.lookup layouts rTy.layoutIdx with
      | .some _ =>
        match enumVariantPayloadArity? localDecls layouts rTy variantIdx with
        | .some arity => .some (padFieldsToArity fields arity)
        | .none => .none
      | .none => .none
    | _ => .none
  | .none => .none

/--
`SetDiscriminant(loc, variantIdx)` on a whole local of the active frame whose
payload fields are `fields` (`replicateValue arity .uninit` when the local was
`.uninit`, so every payload field stays uninitialized; `DIV-LM-ENUM-SET-DISCR-UNINIT`):
writing the tag is a write to `loc`, so it faults with `.ub` on a protected-write
conflict (`hasProtectedWriteConflict`) and otherwise applies the foreign-write
transition to every borrow of `loc` (`invalidateConflictingBorrows`), both scoped
to the active frame's depth `length s.memory.callStack`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L357-L363>

> "/// Write the discriminant for a variant to the enum Place."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "- Breaking the pointer aliasing rules."
-/
def evalSetDiscriminantLocal
    (s : MachineState)
    (loc : Local)
    (variantIdx : Nat)
    (fields : List Value) :
    MirStepNode :=
  let depth := length s.memory.callStack
  match set? s.frame.locals loc (.init (.aggregate variantIdx fields)) with
  | .some locals' =>
    match s.memory.activeProtectors with
    | .nil =>
      MirStepNode.step
        (advanceStmt s locals'
          { s.memory with
            borrows := invalidateConflictingBorrows s.memory.borrows loc .none depth })
    | protHead :: protTail =>
      match
        hasProtectedWriteConflict
          s.memory.borrows
          (protHead :: protTail)
          loc
          .none
          .nil
          0
          0
          depth
      with
      | true => MirStepNode.fail .ub
      | false =>
        MirStepNode.step
          (advanceStmt s locals'
            { s.memory with
              borrows := invalidateConflictingBorrows s.memory.borrows loc .none depth })
  | .none => MirStepNode.fail .ub

/--
The pointer stored in `dst.local_` (for `dst = ⟨_, .deref :: _⟩`) is a tracked
stack borrow whose target local lives in a suspended caller frame rather than
the active frame (`DIV-MR-CALL-TARGET-LOCAL`). Always `false` when
`callStack` is empty.
-/
def derefTargetsSuspendedFrame
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (callStack : List SavedCallerFrame)
    (dst : Place) :
    Bool :=
  match callStack with
  | .nil => false
  | _ :: _ =>
    match get? locals dst.local_ with
    | .some (.init ptrOrFatVal) =>
      match extractDerefPtrVal? ptrOrFatVal with
      | .some ptrVal =>
        match lookupBorrow borrows ptrVal.tag with
        | .some entry =>
          match activeFrameSlot? locals callStack entry.targetFrameDepth entry.targetLocal with
          | .some _ => false
          | .none => true
        | .none => false
      | .none => false
    | _ => false

/--
Result of a frame-qualified place write that may update the active frame's
locals and any part of `Memory` (borrow table, suspended caller frames, or the
root frame's caller-owned referent slots).
-/
inductive FrameWriteResult : Type where
  /-- The write succeeded with active-frame locals `locals` and memory `mem`. -/
  | ok (locals : List LocalSlot) (mem : Memory) : FrameWriteResult
  /-- The write is undefined behavior. -/
  | ub : FrameWriteResult
  /-- The write uses an unmodeled construct. -/
  | unsupported : FrameWriteResult

/--
Dereferencing write `dst = val` (`dst = ⟨ptrLoc, .deref :: restProj⟩`) whose
pointer targets a local outside the active frame: a local of a suspended caller
frame or a caller-owned referent of the root frame (`DIV-MR-CALL-TARGET-LOCAL`).
The write goes to the owning frame's slot list (`foreignFrameTarget?`) through
`evalCallerPlaceWrite` (protector-checked at the target's frame depth), the
Tree Borrows ancestor check `derefWriteTreeUB` applies, the borrows of
`(entry.targetFrameDepth, entry.targetLocal)` receive the write transition
(`invalidateDerefWriteBorrows`), and the updated slot list is committed back
into `Memory.callStack` or `Memory.callerLocals` (`commitForeignFrameLocals`).
A target in the active frame is `.ub` (the active-frame write `evalPlaceWrite`
already rejected it), and so is a target whose frame already returned.

Reference (The Rust Reference, "Pointer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html>

> "Mutable references point to memory which is owned by some other value."
-/
def foreignFrameDerefWrite
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (dst : Place)
    (restProj : List ProjectionElem)
    (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    FrameWriteResult :=
  match get? locals₁ dst.local_ with
  | .some (.init ptrOrFatVal) =>
    match extractDerefPtrVal? ptrOrFatVal with
    | .some ptrVal =>
      match lookupBorrow mem₁.borrows ptrVal.tag with
      | .some entry =>
        match activeFrameSlot? locals₁ mem₁.callStack entry.targetFrameDepth entry.targetLocal with
        | .some _ => .ub
        | .none =>
          match
            foreignFrameTarget?
              mem₁.callStack
              mem₁.callerLocals
              entry.targetFrameDepth
              entry.targetLocal
          with
          | .none => .ub
          | .some target =>
            let (writeDecls, writeLayouts) :=
              match target with
              | .savedFrame _ _ => (localDecls, layouts)
              | .callerReferent _ => (.nil, emptyLayoutTable)
            match
              evalCallerPlaceWrite
                locals₁
                target.locals
                mem₁.borrows
                dst
                val
                mem₁.activeProtectors
                writeDecls
                writeLayouts
                mem₁.callStack
            with
            | .ok targetLocals' =>
              let (targetDecls, targetLayouts) :=
                foreignFrameDeclsAndLayouts
                  mem₁.callStack
                  layouts
                  entry.targetFrameDepth
                  entry.targetLocal
              match
                Bool.or
                  (derefWriteTreeUB locals₁ mem₁.borrows dst)
                  (derefWriteUnionProtectorUB
                    targetDecls
                    targetLayouts
                    locals₁
                    mem₁.borrows
                    mem₁.activeProtectors
                    dst
                    restProj
                    mem₁.callStack)
              with
              | true => .ub
              | false =>
                let borrows' :=
                  match targetDecls with
                  | .nil =>
                    invalidateDerefWriteBorrows
                      locals₁
                      mem₁.borrows
                      dst
                      restProj
                      mem₁.callerLocals
                      mem₁.callStack
                  | _ :: _ =>
                    invalidateDerefWriteBorrowsWithLayouts
                      targetDecls
                      targetLayouts
                      locals₁
                      mem₁.borrows
                      dst
                      restProj
                      mem₁.callStack
                match commitForeignFrameLocals mem₁ target targetLocals' with
                | .some mem₂ => .ok locals₁ { mem₂ with borrows := borrows' }
                | .none => .ub
            | .ub => .ub
            | .unsupported => .unsupported
      | .none => .ub
    | .none => .ub
  | _ => .ub

/--
`StatementKind.assign` / `StatementKind.setDiscriminant` step for a
dereferencing write whose pointer targets a local outside the active frame
(`foreignFrameDerefWrite`), advancing to the next statement.
-/
def evalForeignFrameDerefWrite
    (s : MachineState)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (dst : Place)
    (restProj : List ProjectionElem)
    (val : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match foreignFrameDerefWrite locals₁ mem₁ dst restProj val localDecls layouts with
  | .ok locals₂ mem₂ => MirStepNode.step (advanceStmt s locals₂ mem₂)
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported

/--
Dereferencing `SetDiscriminant` write of `newVal` to `p = ⟨ptrLoc, .deref :: rest⟩`:
tries the active-frame write `evalPlaceWrite` (with Tree Borrows and union
protector checks) and falls back on `.ub` to `evalForeignFrameDerefWrite` so
both suspended caller-frame locals (`Memory.callStack`) and root-frame
caller-owned referents (`Memory.callerLocals`) are updated consistently with
`StatementKind.assign` (`DIV-MR-CALL-TARGET-LOCAL`).
-/
def evalSetDiscriminantDerefWrite
    (s : MachineState)
    (locals₁ : List LocalSlot)
    (p : Place)
    (rest : List ProjectionElem)
    (newVal : Value)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match
    evalPlaceWrite
      locals₁
      s.memory.borrows
      p
      newVal
      s.memory.activeProtectors
      localDecls
      layouts
      s.memory.callStack
  with
  | .ok locals₂ =>
    match
      Bool.or
        (derefWriteTreeUB locals₁ s.memory.borrows p)
        (derefWriteUnionProtectorUB
          localDecls
          layouts
          locals₁
          s.memory.borrows
          s.memory.activeProtectors
          p
          rest
          s.memory.callStack)
    with
    | true => MirStepNode.fail .ub
    | false =>
      MirStepNode.step
        (advanceStmt s locals₂
          { s.memory with
            borrows :=
              invalidateDerefWriteBorrowsWithLayouts
                localDecls
                layouts
                locals₁
                s.memory.borrows
                p
                rest
                s.memory.callStack })
  | .ub =>
    evalForeignFrameDerefWrite s locals₁ s.memory p rest newVal localDecls layouts
  | .unsupported => MirStepNode.unsupported

/--
Execute a single MIR `Statement` from state `s` using `localDecls` and `layouts`
for type- and layout-aware rvalue and intrinsic evaluation.

`StorageDead(loc)` and `StorageLive(loc)` (which implicitly frees any previous
allocation of `loc`) fault with `MirStepNode.fail .ub` when a tag minted from
`loc` is still protected by an active function-entry protector
(`hasProtectedLocalBorrow`, only consulted when some protector is active), and
otherwise disable every tag minted from `loc` (`disableLocalBorrows`) before
marking `loc` `.dead` or `.uninit`. Together these ensure that deallocating a
local bearing an active protector is immediate UB, and that references and raw
pointers created before `StorageDead(loc)` or a second `StorageLive(loc)` fault
with `.ub` on every later access or reborrow instead of reaching the storage
allocated by `StorageLive(loc)` (or a global allocation sharing their tag).
`PlaceMention(place)` requires every operand read while computing `place` (the
root pointer of a dereference and every `Index` local) to be initialized
(`placeMentionOperandsInit`). A projected assignment into a live but
uninitialized local writes into the arity-padded shell from
`uninitFieldWriteShell?` when the projection starts with an in-bounds field of a
tuple, single-variant struct with known layout arity, or union, and otherwise
faults with `.ub`. A projected assignment into an initialized local first
materializes missing, `.unit`-padded, or `Value.uninit` intermediate struct,
union, and tuple field shells along the written field chain
(`ensureNestedFieldShells`), which leaves roots whose intermediate field slots
are all populated unchanged.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L357-L420>

> "/// Write the discriminant for a variant to the enum Place.
> ///
> /// This is permitted for both coroutines and ADTs. This does not necessarily
> /// write to the entire place; instead, it writes to the minimum set of bytes
> /// as required by the layout for the type.
> SetDiscriminant { place: Box<Place<'tcx>>, variant_index: VariantIdx },
> ...
> /// Retag references in the given place, ensuring they got fresh tags. ...
> Retag(RetagKind, Box<Place<'tcx>>),
>
> /// This statement exists to preserve a trace of a scrutinee matched against a
> /// wildcard binding. ...
> PlaceMention(Box<Place<'tcx>>),"

Opaque-cast root dispatch (`DIV-TR-OPAQUECAST-ROOT-DISPATCH`): in
`StatementKind.deinit`, `StatementKind.setDiscriminant`, and
`StatementKind.assign`, a place whose projection is a pure
`ProjectionElem.opaqueCast` chain (`stripLeadingOpaqueCast p.projection = .nil`
with a leading `.opaqueCast`) names the whole local and takes the whole-local
arm (`Deinit` marks the local `.uninit`, `Assign` may initialize a live
`.uninit` local, and `SetDiscriminant` resolves the enum at the cast type via
`eraseLeadingOpaqueCastDecls`). A cast chain followed by further projections
takes the projected arm unchanged, whose typed helpers follow `.opaqueCast`
steps and whose field shell for an uninitialized local is keyed on the cast
type (`uninitFieldWriteShell?`). Places without a leading `.opaqueCast` evaluate
exactly as before.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1148-L1150>

> "///  - [`OpaqueCast`](ProjectionElem::OpaqueCast): This projection changes the place's type to the
> ///    given one, and makes no other changes. A `OpaqueCast` projection on any type other than an
> ///    opaque type from the current crate is not well-formed."

Justification: the cast "changes the place's type to the given one, and makes no
other changes", so whether a statement addresses a whole local or a strict
sub-place is decided by the projections below the leading casts, and any
type-directed step uses the cast type.

Modeling assumption: well-formedness of each cast is a compiler fact about the
captured MIR and is not re-checked.
-/
def evalStmt
    (s : MachineState)
    (stmt : Statement)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match stmt.kind with
  | .nop => MirStepNode.step (advanceStmt s s.frame.locals)
  | .coverage => MirStepNode.step (advanceStmt s s.frame.locals)
  | .constEvalCounter => MirStepNode.step (advanceStmt s s.frame.locals)
  | .backwardIncompatibleDropHint _ => MirStepNode.step (advanceStmt s s.frame.locals)
  | .placeMention place =>
    match get? s.frame.locals place.local_ with
    | .none => MirStepNode.fail .ub
    | .some .dead => MirStepNode.fail .ub
    | .some rootSlot =>
      match placeMentionOperandsInit s.frame.locals rootSlot place.projection with
      | true => MirStepNode.step (advanceStmt s s.frame.locals)
      | false => MirStepNode.fail .ub
  | .retag retagKind place =>
    match
      evalOperand
        s.frame.locals
        (.copy place)
        s.memory.borrows
        s.memory.globals
        layouts
        s.memory.callerLocals
        localDecls
        s.memory.callStack
    with
    | .ok val locals' =>
      let placeTyOpt := placeTy localDecls layouts place
      let isMutRefPlace :=
        match placeTyOpt with
        | .some { kind := .ref .mut _, .. } => true
        | _ => false
      let checkGlobalRetag (ptrOrFatVal : Value) (ptrVal : ProvenancePtr) : MirStepNode :=
        match lookupGlobalAlloc s.memory.globals ptrVal.allocId with
        | .some alloc =>
          let mutOk :=
            match isMutRefPlace, alloc.mutability with
            | true, .not => false
            | _, _ => true
          let boundsOk :=
            match ptrOrFatVal with
            | .aggregate 0 (.ptr p 8 :: .scalar lenSc :: .nil) =>
              let elemSz :=
                match placeTyOpt with
                | .some { kind := .ref _ (.slice ek), .. } =>
                  match rigidTyByteSize layouts { kind := ek, layoutIdx := 0 } with
                  | .some n => n
                  | .none => 1
                | .some { kind := .rawPtr _ (.slice ek), .. } =>
                  match rigidTyByteSize layouts { kind := ek, layoutIdx := 0 } with
                  | .some n => n
                  | .none => 1
                | _ => 1
              Nat.ble
                (Nat.add p.offsetBytes (Nat.mul lenSc.bits elemSz))
                (length alloc.bytes)
            | _ =>
              let pointeeBytes :=
                match placeTyOpt with
                | .some pTy =>
                  match pointeeTyOf pTy with
                  | .some innerTy =>
                    match rigidTyByteSize layouts innerTy with
                    | .some n => n
                    | .none => 0
                  | .none => 0
                | .none => 0
              Nat.ble (Nat.add ptrVal.offsetBytes pointeeBytes) (length alloc.bytes)
          match Bool.and mutOk boundsOk with
          | true => MirStepNode.step (advanceStmt s locals')
          | false => MirStepNode.fail .ub
        | .none =>
          let isNonNullEmptySlice :=
            match ptrOrFatVal with
            | .aggregate 0 (.ptr p 8 :: .scalar ⟨0, 8⟩ :: .nil) =>
              Bool.and
                (Bool.not isMutRefPlace)
                (Bool.not
                  (Bool.and
                    (Nat.beq p.allocId 0)
                    (Nat.beq p.offsetBytes 0)))
            | _ => false
          match isNonNullEmptySlice with
          | true => MirStepNode.step (advanceStmt s locals')
          | false => MirStepNode.fail .ub
      let retagPtrVal
          (ptrVal : ProvenancePtr)
          (sz : Nat)
          (allowGlobal : Bool) :
          MirStepNode :=
        match lookupBorrow s.memory.borrows ptrVal.tag with
        | .some entry =>
          match entry.perm with
          | .disabled => MirStepNode.fail .ub
          | _ =>
            match retagKind with
            | .fnEntry =>
              evalFnEntryRetag
                s localDecls layouts place ptrVal sz entry locals'
            | .default | .twoPhase | .raw =>
              evalNonFnEntryRetag
                retagKind s localDecls layouts place ptrVal sz entry locals'
        | .none =>
          match allowGlobal with
          | true => checkGlobalRetag val ptrVal
          | false => MirStepNode.fail .ub
      match placeTyOpt with
      | .some { kind := .rawPtr _ _, .. } =>
        match retagKind with
        | .raw => MirStepNode.step (advanceStmt s locals')
        | .default | .twoPhase | .fnEntry => MirStepNode.fail .ub
      | .some { kind := .ref _ pointee, .. } =>
        match rigidTyIsUninhabited 16 pointee with
        | true => MirStepNode.fail .ub
        | false =>
          match val with
          | .ptr ptrVal sz => retagPtrVal ptrVal sz true
          | .scalar sc =>
            match
              Bool.and
                (rigidTyIsZeroSized 16 pointee)
                (Bool.not (Nat.beq sc.bits 0))
            with
            | true => MirStepNode.step (advanceStmt s locals')
            | false => MirStepNode.fail .ub
          | .aggregate 0 (.ptr ptrVal 8 :: .scalar _ :: .nil) =>
            match lookupBorrow s.memory.borrows ptrVal.tag with
            | .some entry =>
              match entry.perm, isMutRefPlace with
              | .disabled, _ => MirStepNode.fail .ub
              | .frozen, true => MirStepNode.fail .ub
              | _, _ =>
                match retagKind with
                | .fnEntry =>
                  let protId := s.memory.nextProtector
                  let borrows' :=
                    attachBorrowProtector s.memory.borrows ptrVal.tag protId
                  let mem' : Memory := {
                    s.memory with
                    borrows := borrows'
                    activeProtectors := protId :: s.memory.activeProtectors
                    nextProtector := Nat.add protId 1
                  }
                  MirStepNode.step (advanceStmt s locals' mem')
                | _ => MirStepNode.step (advanceStmt s locals')
            | .none => checkGlobalRetag val ptrVal
          | _ => MirStepNode.fail .ub
      | .none =>
        match val with
        | .ptr ptrVal sz => retagPtrVal ptrVal sz false
        | .aggregate 0 (.ptr ptrVal 8 :: .scalar _ :: .nil) =>
          match lookupBorrow s.memory.borrows ptrVal.tag with
          | .some entry =>
            match entry.perm with
            | .disabled => MirStepNode.fail .ub
            | _ =>
              match retagKind with
              | .fnEntry =>
                let protId := s.memory.nextProtector
                let borrows' :=
                  attachBorrowProtector s.memory.borrows ptrVal.tag protId
                let mem' : Memory := {
                  s.memory with
                  borrows := borrows'
                  activeProtectors := protId :: s.memory.activeProtectors
                  nextProtector := Nat.add protId 1
                }
                MirStepNode.step (advanceStmt s locals' mem')
              | _ => MirStepNode.step (advanceStmt s locals')
          | .none => checkGlobalRetag val ptrVal
        | _ => MirStepNode.fail .ub
      | .some _ =>
        match val with
        | .ptr ptrVal sz => retagPtrVal ptrVal sz true
        | _ => MirStepNode.step (advanceStmt s locals')
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .storageLive loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .uninit with
      | .some locals' =>
        match s.memory.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with
                borrows :=
                  disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
              (length s.memory.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with
                  borrows :=
                    disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .storageDead loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .dead with
      | .some locals' =>
        match s.memory.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals'
              { s.memory with
                borrows :=
                  disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
              (length s.memory.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with
                  borrows :=
                    disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deinit p =>
    let depth := length s.memory.callStack
    match p.projection, stripLeadingOpaqueCast p.projection with
    | .nil, _ =>
      match get? s.frame.locals p.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals p.local_ .uninit with
        | .some locals' =>
          match s.memory.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrows s.memory.borrows p.local_ .none depth
            MirStepNode.step
              (advanceStmt s locals' { s.memory with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                s.memory.borrows
                (protHead :: protTail)
                p.local_
                .none
                .nil
                0
                0
                depth
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrows s.memory.borrows p.local_ .none depth
              MirStepNode.step
                (advanceStmt s locals' { s.memory with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | .opaqueCast _ :: _, .nil =>
      match get? s.frame.locals p.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals p.local_ .uninit with
        | .some locals' =>
          match s.memory.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrows s.memory.borrows p.local_ .none depth
            MirStepNode.step
              (advanceStmt s locals' { s.memory with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                s.memory.borrows
                (protHead :: protTail)
                p.local_
                .none
                .nil
                0
                0
                depth
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrows s.memory.borrows p.local_ .none depth
              MirStepNode.step
                (advanceStmt s locals' { s.memory with borrows := borrows' })
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | proj :: rest, _ =>
      let resolvedLocalProj :=
        resolveBorrowWriteLocalProj
          localDecls
          layouts
          s.frame.locals
          p.local_
          (proj :: rest)
      match get? s.frame.locals p.local_ with
      | .some (.init rootVal) =>
        match
          deinitProjectedForLocal
            s.frame.locals
            localDecls
            layouts
            p.local_
            rootVal
            (proj :: rest)
        with
        | .ok rootVal' =>
          match set? s.frame.locals p.local_ (.init rootVal') with
          | .some locals' =>
            match s.memory.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  s.memory.borrows
                  p.local_
                  .none
                  resolvedLocalProj
                  0
                  0
                  depth
              MirStepNode.step
                (advanceStmt s locals' { s.memory with borrows := borrows' })
            | protHead :: protTail =>
              match
                hasProtectedWriteConflict
                  s.memory.borrows
                  (protHead :: protTail)
                  p.local_
                  .none
                  resolvedLocalProj
                  0
                  0
                  depth
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    s.memory.borrows
                    p.local_
                    .none
                    resolvedLocalProj
                    0
                    0
                    depth
                MirStepNode.step
                  (advanceStmt s locals' { s.memory with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | .some .uninit =>
        match
          deinitTailOk
            s.frame.locals
            localDecls
            layouts
            (placeTy localDecls layouts { local_ := p.local_, projection := .nil })
            (proj :: rest)
        with
        | true =>
          match s.memory.activeProtectors with
          | .nil =>
            let borrows' :=
              invalidateConflictingBorrowsAtProj
                s.memory.borrows
                p.local_
                .none
                resolvedLocalProj
                0
                0
                depth
            MirStepNode.step
              (advanceStmt s s.frame.locals { s.memory with borrows := borrows' })
          | protHead :: protTail =>
            match
              hasProtectedWriteConflict
                s.memory.borrows
                (protHead :: protTail)
                p.local_
                .none
                resolvedLocalProj
                0
                0
                depth
            with
            | true => MirStepNode.fail .ub
            | false =>
              let borrows' :=
                invalidateConflictingBorrowsAtProj
                  s.memory.borrows
                  p.local_
                  .none
                  resolvedLocalProj
                  0
                  0
                  depth
              MirStepNode.step
                (advanceStmt s s.frame.locals { s.memory with borrows := borrows' })
        | false =>
          match projectionHasDeref (proj :: rest) with
          | true => MirStepNode.unsupported
          | false => MirStepNode.fail .ub
      | _ => MirStepNode.fail .ub
  | .intrinsic (.assume op) =>
    match
      evalOperand
        s.frame.locals
        op
        s.memory.borrows
        s.memory.globals
        layouts
        s.memory.callerLocals
        localDecls
        s.memory.callStack
    with
    | .ok (.scalar sc) locals' =>
      match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.beq sc.bits 1) with
      | true => MirStepNode.step (advanceStmt s locals')
      | false => MirStepNode.fail .ub
    | .ok _ _ => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported
  | .intrinsic (.copyNonOverlapping src dst count) =>
    evalCopyNonOverlapping s src dst count localDecls layouts
  | .setDiscriminant p variantIdx =>
    match p.projection, stripLeadingOpaqueCast p.projection with
    | .nil, _ =>
      match get? s.frame.locals p.local_ with
      | .some (.init (.aggregate _ fields)) =>
        match padSetDiscriminantInitFields? localDecls layouts p variantIdx fields with
        | .some fields' => evalSetDiscriminantLocal s p.local_ variantIdx fields'
        | .none => MirStepNode.fail .ub
      | .some (.init _) => MirStepNode.fail .ub
      | .some .uninit =>
        match setDiscriminantUninitDeclOk localDecls p.local_ with
        | false => MirStepNode.unsupported
        | true =>
          match setDiscriminantUninitPayload? localDecls layouts p.local_ variantIdx with
          | .some uninitFields => evalSetDiscriminantLocal s p.local_ variantIdx uninitFields
          | .none => MirStepNode.fail .ub
      | .some .dead => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | .opaqueCast castTy :: restCast, .nil =>
      let castDecls :=
        eraseLeadingOpaqueCastDecls
          localDecls
          layouts
          p.local_
          (.opaqueCast castTy :: restCast)
      let rootPlace : Place := { local_ := p.local_, projection := .nil }
      match get? s.frame.locals p.local_ with
      | .some (.init (.aggregate _ fields)) =>
        match padSetDiscriminantInitFields? castDecls layouts rootPlace variantIdx fields with
        | .some fields' => evalSetDiscriminantLocal s p.local_ variantIdx fields'
        | .none => MirStepNode.fail .ub
      | .some (.init _) => MirStepNode.fail .ub
      | .some .uninit =>
        match setDiscriminantUninitDeclOk castDecls p.local_ with
        | false => MirStepNode.unsupported
        | true =>
          match setDiscriminantUninitPayload? castDecls layouts p.local_ variantIdx with
          | .some uninitFields => evalSetDiscriminantLocal s p.local_ variantIdx uninitFields
          | .none => MirStepNode.fail .ub
      | .some .dead => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | proj :: rest, _ =>
      match
        evalOperand
          s.frame.locals
          (.copy p)
          s.memory.borrows
          s.memory.globals
          layouts
          s.memory.callerLocals
          localDecls
          s.memory.callStack
      with
      | .ok (.aggregate _ fields) locals₁ =>
        match padSetDiscriminantInitFields? localDecls layouts p variantIdx fields with
        | .none => MirStepNode.fail .ub
        | .some fields' =>
          let newVal : Value := .aggregate variantIdx fields'
          match proj with
          | .deref =>
            evalSetDiscriminantDerefWrite s locals₁ p rest newVal localDecls layouts
          | _ =>
            let depth := length s.memory.callStack
            let resolvedLocalProj :=
              resolveBorrowWriteLocalProj localDecls layouts locals₁ p.local_ (proj :: rest)
            match
              hasProtectedWriteConflict
                s.memory.borrows
                s.memory.activeProtectors
                p.local_
                .none
                resolvedLocalProj
                0
                0
                depth
            with
            | true => MirStepNode.fail .ub
            | false =>
              match
                writePlaceValue
                  locals₁
                  s.memory.borrows
                  p
                  newVal
                  localDecls
                  layouts
                  s.memory.callStack
              with
              | .ok locals₂ =>
                MirStepNode.step
                  (advanceStmt s locals₂
                    { s.memory with
                      borrows :=
                        invalidateConflictingBorrowsAtProj
                          s.memory.borrows
                          p.local_
                          .none
                          resolvedLocalProj
                          0
                          0
                          depth })
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
      | .ok _ _ => MirStepNode.fail .ub
      | .ub =>
        match proj, rest with
        | .deref, .nil =>
          match get? s.frame.locals p.local_ with
          | .some (.init (.ptr ptrVal _)) =>
            match lookupBorrow s.memory.borrows ptrVal.tag with
            | .some entry =>
              match entry.perm, entry.targetProjection, Nat.beq ptrVal.offsetBytes 0 with
              | .frozen, _, _ => MirStepNode.fail .ub
              | .disabled, _, _ => MirStepNode.fail .ub
              | _, _ :: _, _ => MirStepNode.fail .ub
              | _, _, false => MirStepNode.fail .ub
              | _, .nil, true =>
                let pointeeAdtOk : Bool :=
                  match placeTyResolved localDecls layouts p with
                  | .some { kind := .adt _ _, .. } => true
                  | .some _ => false
                  | .none => true
                match
                  activeFrameSlot?
                    s.frame.locals
                    s.memory.callStack
                    entry.targetFrameDepth
                    entry.targetLocal
                with
                | .some .uninit =>
                  match
                    Bool.and
                      pointeeAdtOk
                      (setDiscriminantUninitDeclOk localDecls entry.targetLocal)
                  with
                  | false => MirStepNode.unsupported
                  | true =>
                    match setDiscriminantUninitPayload? localDecls layouts entry.targetLocal variantIdx with
                    | .some uninitFields =>
                      evalSetDiscriminantDerefWrite
                        s s.frame.locals p .nil (.aggregate variantIdx uninitFields) localDecls layouts
                    | .none => MirStepNode.fail .ub
                | .some _ => MirStepNode.fail .ub
                | .none =>
                  match
                    foreignFrameSlot?
                      s.memory.callStack
                      s.memory.callerLocals
                      entry.targetFrameDepth
                      entry.targetLocal
                  with
                  | .some .uninit =>
                    let (targetDecls, targetLayouts) :=
                      foreignFrameDeclsAndLayouts
                        s.memory.callStack
                        layouts
                        entry.targetFrameDepth
                        entry.targetLocal
                    match
                      Bool.and
                        pointeeAdtOk
                        (setDiscriminantUninitDeclOk targetDecls entry.targetLocal)
                    with
                    | false => MirStepNode.unsupported
                    | true =>
                      match setDiscriminantUninitPayload? targetDecls targetLayouts entry.targetLocal variantIdx with
                      | .some uninitFields =>
                        evalSetDiscriminantDerefWrite
                          s s.frame.locals p .nil (.aggregate variantIdx uninitFields) localDecls layouts
                      | .none => MirStepNode.fail .ub
                  | _ => MirStepNode.fail .ub
            | .none => MirStepNode.fail .ub
          | _ => MirStepNode.fail .ub
        | _, _ => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
  | .assign dst rv =>
    match evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | .ok val locals₁ mem₁ =>
      match dst.projection, stripLeadingOpaqueCast dst.projection with
      | .nil, _ =>
        match get? locals₁ dst.local_ with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? locals₁ dst.local_ (.init val) with
          | .some locals₂ =>
            match mem₁.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrows
                  mem₁.borrows dst.local_ .none (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | protHead :: protTail =>
              match
                hasProtectedWriteConflict
                  mem₁.borrows
                  (protHead :: protTail)
                  dst.local_
                  .none
                  .nil
                  0
                  0
                  (length mem₁.callStack)
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrows
                    mem₁.borrows dst.local_ .none (length mem₁.callStack)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub
      | .deref :: restProj, _ =>
        match
          evalPlaceWrite
            locals₁
            mem₁.borrows
            dst
            val
            mem₁.activeProtectors
            localDecls
            layouts
            mem₁.callStack
        with
        | .ok locals₂ =>
          match
            Bool.or
              (derefWriteTreeUB locals₁ mem₁.borrows dst)
              (derefWriteUnionProtectorUB
                localDecls
                layouts
                locals₁
                mem₁.borrows
                mem₁.activeProtectors
                dst
                restProj
                mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            let borrows' :=
              invalidateDerefWriteBorrowsWithLayouts
                localDecls
                layouts
                locals₁
                mem₁.borrows
                dst
                restProj
                mem₁.callStack
            MirStepNode.step
              (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .ub =>
          match mem₁.callStack with
          | .nil =>
            match mem₁.callerLocals with
            | .nil => MirStepNode.fail .ub
            | _ :: _ =>
              match
                evalCallerPlaceWrite
                  locals₁
                  mem₁.callerLocals
                  mem₁.borrows
                  dst
                  val
                  mem₁.activeProtectors
              with
              | .ok callerLocals' =>
                match derefWriteTreeUB locals₁ mem₁.borrows dst with
                | true => MirStepNode.fail .ub
                | false =>
                  let borrows' :=
                    invalidateDerefWriteBorrows
                      locals₁
                      mem₁.borrows
                      dst
                      restProj
                      mem₁.callerLocals
                  MirStepNode.step
                    (advanceStmt
                      s
                      locals₁
                      { mem₁ with
                        borrows := borrows'
                        callerLocals := callerLocals' })
              | .ub => MirStepNode.fail .ub
              | .unsupported => MirStepNode.unsupported
          | _ :: _ =>
            evalForeignFrameDerefWrite s locals₁ mem₁ dst restProj val localDecls layouts
        | .unsupported => MirStepNode.unsupported
      | .opaqueCast _ :: _, .nil =>
        match get? locals₁ dst.local_ with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? locals₁ dst.local_ (.init val) with
          | .some locals₂ =>
            match mem₁.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrows
                  mem₁.borrows dst.local_ .none (length mem₁.callStack)
              MirStepNode.step
                (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | protHead :: protTail =>
              match
                hasProtectedWriteConflict
                  mem₁.borrows
                  (protHead :: protTail)
                  dst.local_
                  .none
                  .nil
                  0
                  0
                  (length mem₁.callStack)
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrows
                    mem₁.borrows dst.local_ .none (length mem₁.callStack)
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub
      | proj :: rest, _ =>
        match get? locals₁ dst.local_ with
        | .some (.init rootVal) =>
          match
            ensureNestedFieldShells
              rootVal
              (proj :: rest)
              localDecls
              layouts
              (placeTy localDecls layouts { local_ := dst.local_, projection := .nil })
          with
          | .none => MirStepNode.fail .ub
          | .some shelledRoot =>
            match
              writeProjectedForLocal
                locals₁
                localDecls
                layouts
                dst.local_
                shelledRoot
                (proj :: rest)
                val
            with
            | .ok rootVal' =>
              match set? locals₁ dst.local_ (.init rootVal') with
              | .some locals₂ =>
                let resolvedLocalProj :=
                  resolveBorrowWriteLocalProj
                    localDecls
                    layouts
                    locals₁
                    dst.local_
                    (proj :: rest)
                match mem₁.activeProtectors with
                | .nil =>
                  let borrows' :=
                    invalidateConflictingBorrowsAtProj
                      mem₁.borrows
                      dst.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      (length mem₁.callStack)
                  MirStepNode.step
                    (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
                | protHead :: protTail =>
                  match
                    hasProtectedWriteConflict
                      mem₁.borrows
                      (protHead :: protTail)
                      dst.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      (length mem₁.callStack)
                  with
                  | true => MirStepNode.fail .ub
                  | false =>
                    let borrows' :=
                      invalidateConflictingBorrowsAtProj
                        mem₁.borrows
                        dst.local_
                        .none
                        resolvedLocalProj
                        0
                        0
                        (length mem₁.callStack)
                    MirStepNode.step
                      (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
              | .none => MirStepNode.fail .ub
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
        | .some .uninit =>
          match uninitFieldWriteShell? localDecls layouts dst.local_ proj rest with
          | .some rootVal =>
            match
              writeProjectedForLocal
                locals₁
                localDecls
                layouts
                dst.local_
                rootVal
                (proj :: rest)
                val
            with
            | .ok rootVal' =>
              match set? locals₁ dst.local_ (.init rootVal') with
              | .some locals₂ =>
                let resolvedLocalProj :=
                  resolveBorrowWriteLocalProj
                    localDecls
                    layouts
                    locals₁
                    dst.local_
                    (proj :: rest)
                match mem₁.activeProtectors with
                | .nil =>
                  let borrows' :=
                    invalidateConflictingBorrowsAtProj
                      mem₁.borrows
                      dst.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      (length mem₁.callStack)
                  MirStepNode.step
                    (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
                | protHead :: protTail =>
                  match
                    hasProtectedWriteConflict
                      mem₁.borrows
                      (protHead :: protTail)
                      dst.local_
                      .none
                      resolvedLocalProj
                      0
                      0
                      (length mem₁.callStack)
                  with
                  | true => MirStepNode.fail .ub
                  | false =>
                    let borrows' :=
                      invalidateConflictingBorrowsAtProj
                        mem₁.borrows
                        dst.local_
                        .none
                        resolvedLocalProj
                        0
                        0
                        (length mem₁.callStack)
                    MirStepNode.step
                      (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
              | .none => MirStepNode.fail .ub
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
          | .none => MirStepNode.fail .ub
        | .some .dead => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub
    | .ub => MirStepNode.fail .ub
    | .unsupported => MirStepNode.unsupported

/--
Universal characterization of `StatementKind.storageDead loc` in `evalStmt`
(`D2` / `D14a-storage`):
1. When `loc` is in bounds (`get? s.frame.locals loc = .some slot`,
   `set? s.frame.locals loc .dead = .some localsDead`) and no borrow entry
   targeting `loc` is protected by `s.memory.activeProtectors`
   at the active frame's depth
   (`hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc (length s.memory.callStack) = false`),
   `evalStmt` steps to `advanceStmt s localsDead { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) }`,
   in which every borrow entry targeting `loc` of the active frame is `.disabled` with a deallocated allocation.
2. When `loc` is in bounds and a borrow entry targeting `loc` is protected by
   `s.memory.activeProtectors` (`hasProtectedLocalBorrow = true`), `evalStmt`
   faults with `MirStepNode.fail .ub`.
3. When `loc` is out of bounds (`get? s.frame.locals loc = .none`), `evalStmt`
   faults with `MirStepNode.fail .ub`.
-/
theorem evalStmt_storageDead_purges_borrows
    (s : MachineState)
    (loc : Local)
    (slot : LocalSlot)
    (localsDead : List LocalSlot)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .dead = .some localsDead →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc
        (length s.memory.callStack) = false →
      evalStmt s ⟨.storageDead loc, span⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s localsDead
            { s.memory with
              borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) }) ∧
      ∀ entry ∈ disableLocalBorrows s.memory.borrows loc (length s.memory.callStack),
        entry.targetFrameDepth = length s.memory.callStack →
        entry.targetLocal = loc → entry.perm = .disabled ∧ entry.allocDead = true) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .dead = .some localsDead →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc
        (length s.memory.callStack) = true →
      evalStmt s ⟨.storageDead loc, span⟩ localDecls layouts = MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .none →
      evalStmt s ⟨.storageDead loc, span⟩ localDecls layouts = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hGet hSet hProt
    refine ⟨?_, perm_eq_disabled_of_mem_disableLocalBorrows s.memory.borrows loc⟩
    cases hAP : s.memory.activeProtectors with
    | nil => simp [evalStmt, hGet, hSet, hAP]
    | cons p ps =>
      rw [hAP] at hProt
      simp [evalStmt, hGet, hSet, hAP, hProt]
  · intro hGet hSet hProt
    cases hAP : s.memory.activeProtectors with
    | nil =>
      rw [hAP, hasProtectedLocalBorrow_nil_protectors] at hProt
      nomatch hProt
    | cons p ps =>
      rw [hAP] at hProt
      simp [evalStmt, hGet, hSet, hAP, hProt]
  · intro hNone
    simp [evalStmt, hNone]

/--
Universal characterization of `StatementKind.storageLive loc` in `evalStmt`
(`D2` / `D14a-storage`):
1. When `loc` is in bounds (`get? s.frame.locals loc = .some slot`,
   `set? s.frame.locals loc .uninit = .some localsUninit`) and no borrow entry
   targeting `loc` is protected by `s.memory.activeProtectors`
   at the active frame's depth
   (`hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc (length s.memory.callStack) = false`),
   `evalStmt` steps to `advanceStmt s localsUninit { s.memory with borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) }`,
   in which every borrow entry targeting `loc` of the active frame is `.disabled` with a deallocated allocation.
2. When `loc` is in bounds and a borrow entry targeting `loc` is protected by
   `s.memory.activeProtectors` (`hasProtectedLocalBorrow = true`), the implicit
   deallocation of `loc`'s previous storage makes `evalStmt` fault with
   `MirStepNode.fail .ub`.
3. When `loc` is out of bounds (`get? s.frame.locals loc = .none`), `evalStmt`
   faults with `MirStepNode.fail .ub`.
-/
theorem evalStmt_storageLive_purges_borrows
    (s : MachineState)
    (loc : Local)
    (slot : LocalSlot)
    (localsUninit : List LocalSlot)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .uninit = .some localsUninit →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc
        (length s.memory.callStack) = false →
      evalStmt s ⟨.storageLive loc, span⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s localsUninit
            { s.memory with
              borrows := disableLocalBorrows s.memory.borrows loc (length s.memory.callStack) }) ∧
      ∀ entry ∈ disableLocalBorrows s.memory.borrows loc (length s.memory.callStack),
        entry.targetFrameDepth = length s.memory.callStack →
        entry.targetLocal = loc → entry.perm = .disabled ∧ entry.allocDead = true) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .uninit = .some localsUninit →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc
        (length s.memory.callStack) = true →
      evalStmt s ⟨.storageLive loc, span⟩ localDecls layouts = MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .none →
      evalStmt s ⟨.storageLive loc, span⟩ localDecls layouts = MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hGet hSet hProt
    refine ⟨?_, perm_eq_disabled_of_mem_disableLocalBorrows s.memory.borrows loc⟩
    cases hAP : s.memory.activeProtectors with
    | nil => simp [evalStmt, hGet, hSet, hAP]
    | cons p ps =>
      rw [hAP] at hProt
      simp [evalStmt, hGet, hSet, hAP, hProt]
  · intro hGet hSet hProt
    cases hAP : s.memory.activeProtectors with
    | nil =>
      rw [hAP, hasProtectedLocalBorrow_nil_protectors] at hProt
      nomatch hProt
    | cons p ps =>
      rw [hAP] at hProt
      simp [evalStmt, hGet, hSet, hAP, hProt]
  · intro hNone
    simp [evalStmt, hNone]

/--
Universal proof (`D2` / `D14a-storage`) that once `StorageDead(loc)` or
`StorageLive(loc)` has disabled `loc`'s borrows (`disableLocalBorrows borrows loc`),
a pointer `ptrVal` whose provenance tag resolved to a borrow entry targeting
`loc` (`lookupBorrow borrows ptrVal.tag = .some entry`,
`entry.targetLocal = loc`) resolves to that entry disabled, and faults with
`.ub` on every dereferencing read (`evalPlaceRead`, `evalOperand` copy/move),
every dereferencing write (`writePlaceValue`, `evalPlaceWrite`,
`StatementKind.setDiscriminant`), every safe reborrow (`Rvalue.ref`), every
reference retag (`StatementKind.retag`), and every non-zero-length
`copy_nonoverlapping` (`evalCopyNonOverlappingWithCount`) through it. This holds
for arbitrary frame locals `localsAfter` (in particular after `loc` has been
revived by `StorageLive(loc)` and re-initialized) and arbitrary captured global
allocations `globals`: the disabled stack borrow entry keeps shadowing any
global allocation that shares the pointer's allocation identifier.

The theorem holds for the borrows of `loc` at any frame depth `d`
(`entry.targetFrameDepth = d`), and the disabled entry also records the
deallocation (`allocDead := true`). Pointer arithmetic (`evalPtrOffsetBinOp`) is
deliberately not characterized here: it checks allocation bounds only, so a
non-zero offset through such a tag faults because `allocDead` gives the dead
allocation the byte bound `0`, while a zero-byte offset stays defined
(`DIV-LM-D6-OFFSET-DISABLED-TAG`). Raw address-of (`Rvalue.rawPtr`) is not
characterized either.
-/
theorem evalStmt_storageRevive_old_ptr_deref_ub
    (s : MachineState)
    (borrows : List BorrowEntry)
    (globals : List CapturedAllocation)
    (callerLocals : List LocalSlot)
    (activeProtectors : List Nat)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (mem : Memory)
    (loc ptrLoc : Local)
    (ptrVal : ProvenancePtr)
    (sz : Nat)
    (restProj : List ProjectionElem)
    (localsAfter : List LocalSlot)
    (writeVal : Value)
    (borrowKind : BorrowKind)
    (retagKind : RetagKind)
    (span : String)
    (srcOp dstOp : Operand)
    (otherVal : Value)
    (n : Nat)
    (entry : BorrowEntry)
    (d : Nat)
    (hLookup : lookupBorrow borrows ptrVal.tag = .some entry)
    (hTarget : entry.targetLocal = loc)
    (hDepth : entry.targetFrameDepth = d)
    (hPtrSlot : get? localsAfter ptrLoc = .some (.init (.ptr ptrVal sz))) :
    let borrowsAfter := disableLocalBorrows borrows loc d
    let derefPlace : Place := { local_ := ptrLoc, projection := .deref :: restProj }
    let sAfter : MachineState :=
      { s with
        frame := { s.frame with locals := localsAfter }
        memory := { s.memory with borrows := borrowsAfter } }
    lookupBorrow borrowsAfter ptrVal.tag =
      .some { entry with perm := .disabled, allocDead := true } ∧
    evalPlaceRead localsAfter derefPlace borrowsAfter globals layouts callerLocals localDecls = .ub ∧
    evalOperand localsAfter (.copy derefPlace) borrowsAfter globals layouts callerLocals localDecls = .ub ∧
    evalOperand localsAfter (.move derefPlace) borrowsAfter globals layouts callerLocals localDecls = .ub ∧
    writePlaceValue localsAfter borrowsAfter derefPlace writeVal localDecls layouts = .ub ∧
    evalPlaceWrite localsAfter borrowsAfter derefPlace writeVal activeProtectors localDecls layouts = .ub ∧
    evalRvalue localsAfter (.ref borrowKind derefPlace)
      { mem with borrows := borrowsAfter } localDecls layouts = .ub ∧
    (match placeTy localDecls layouts ⟨ptrLoc, .nil⟩, retagKind with
     | .some { kind := .rawPtr _ _, .. }, .raw =>
       evalStmt sAfter ⟨.retag retagKind ⟨ptrLoc, .nil⟩, span⟩ localDecls layouts =
         MirStepNode.step (advanceStmt sAfter localsAfter)
     | _, _ =>
       evalStmt sAfter ⟨.retag retagKind ⟨ptrLoc, .nil⟩, span⟩ localDecls layouts =
         MirStepNode.fail .ub) ∧
    evalStmt sAfter ⟨.setDiscriminant derefPlace n, span⟩ localDecls layouts =
      MirStepNode.fail .ub ∧
    evalCopyNonOverlappingWithCount sAfter srcOp dstOp localDecls layouts
      (.ptr ptrVal sz) otherVal (n + 1) localsAfter = MirStepNode.fail .ub ∧
    evalCopyNonOverlappingWithCount sAfter srcOp dstOp localDecls layouts
      otherVal (.ptr ptrVal sz) (n + 1) localsAfter = MirStepNode.fail .ub := by
  dsimp only
  have hDis : lookupBorrow (disableLocalBorrows borrows loc d) ptrVal.tag =
      .some { entry with perm := .disabled, allocDead := true } :=
    lookupBorrow_disableLocalBorrows_of_targetLocal_eq borrows loc ptrVal.tag entry hLookup hTarget
      hDepth
  have hWrite :
      writePlaceValue localsAfter (disableLocalBorrows borrows loc d)
        { local_ := ptrLoc, projection := .deref :: restProj } writeVal localDecls layouts = .ub := by
    simp [writePlaceValue, hPtrSlot, hDis]
  have hOpCopy :
      evalOperand localsAfter (.copy { local_ := ptrLoc, projection := .deref :: restProj })
        (disableLocalBorrows borrows loc d) globals layouts callerLocals localDecls = .ub := by
    cases localDecls <;> simp [evalOperand, hPtrSlot, hDis]
  have hOpMove :
      evalOperand localsAfter (.move { local_ := ptrLoc, projection := .deref :: restProj })
        (disableLocalBorrows borrows loc d) globals layouts callerLocals localDecls = .ub := by
    cases localDecls <;> simp [evalOperand, hPtrSlot, hDis]
  refine ⟨hDis, ?_, hOpCopy, hOpMove, hWrite, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · cases localDecls <;> simp [evalPlaceRead, hPtrSlot, hDis]
  · unfold evalPlaceWrite
    cases activeProtectors with
    | nil => exact hWrite
    | cons p ps =>
      dsimp only
      split
      · rfl
      · exact hWrite
  · unfold evalRvalue evalRvalueRefDeref
    dsimp only
    rw [hPtrSlot]
    dsimp only
    split
    · rfl
    · rw [hDis]
  · unfold evalStmt evalOperand readProjectedValue
    dsimp only
    rw [hPtrSlot]
    dsimp only
    cases hPlaceTy : placeTy localDecls layouts ⟨ptrLoc, .nil⟩ with
    | none =>
      dsimp only
      rw [hDis]
    | some ty =>
      rcases ty with ⟨kind, layIdx⟩
      cases kind with
      | rawPtr m p =>
        cases retagKind <;> rfl
      | ref m p =>
        dsimp only
        cases rigidTyIsUninhabited 16 p
        · dsimp only; rw [hDis]
        · rfl
      | _ =>
        dsimp only
        rw [hDis]
  · cases localDecls <;> cases restProj <;> simp [evalStmt, evalOperand, hPtrSlot, hDis]
  · unfold evalCopyNonOverlappingWithCount
    simp only [Nat.beq]
    cases otherVal with
    | ptr dstPtr dstSz =>
      dsimp only
      rw [hDis]
      cases hDst : lookupBorrow (disableLocalBorrows borrows loc d) dstPtr.tag <;> rfl
    | _ => rfl
  · unfold evalCopyNonOverlappingWithCount
    simp only [Nat.beq]
    cases otherVal with
    | ptr srcPtr srcSz =>
      dsimp only
      rw [hDis]
      cases hSrc : lookupBorrow (disableLocalBorrows borrows loc d) srcPtr.tag with
      | none => rfl
      | some srcEntry =>
        dsimp only
        cases hPerm : srcEntry.perm <;> rfl
    | _ => rfl

/--
Universal proof that a bare `StatementKind.placeMention` (`place.projection = []`)
on a live local (`get? s.frame.locals loc = .some .uninit` or `.some (.init v)`)
steps cleanly to `advanceStmt s s.frame.locals` without loading or mutating the
local.
-/
theorem evalStmt_placeMention_local_uninit_ok
    (s : MachineState)
    (loc : Local)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    (get? s.frame.locals loc = .some .uninit →
      evalStmt s ⟨.placeMention ⟨loc, .nil⟩, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s s.frame.locals)) ∧
    (∀ v : Value,
      get? s.frame.locals loc = .some (.init v) →
      evalStmt s ⟨.placeMention ⟨loc, .nil⟩, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s s.frame.locals)) := by
  refine ⟨?_, ?_⟩
  · intro hUninit
    simp [evalStmt, hUninit]
  · intro v hInit
    simp [evalStmt, hInit]

/--
Universal proof that a dereferencing `StatementKind.placeMention`
(`place.projection = .deref :: restProj`) steps cleanly to
`advanceStmt s s.frame.locals` whenever the root pointer local is initialized
(`get? s.frame.locals loc = .some (.init v)`) and every `.index idxLocal` along
`restProj` is an initialized scalar
(`placeIndexLocalsInit s.frame.locals restProj = true`), even if the pointee
is dangling (`let _ = *ptr;`). For safe pointers this is more permissive than
MiniRust, which also requires the pointee to be dereferenceable (see
`placeMentionOperandsInit`).
-/
theorem evalStmt_placeMention_deref_init_ok
    (s : MachineState)
    (loc : Local)
    (v : Value)
    (restProj : List ProjectionElem)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hInit : get? s.frame.locals loc = .some (.init v))
    (hIdxOk : placeIndexLocalsInit s.frame.locals restProj = true) :
    evalStmt s ⟨.placeMention ⟨loc, .deref :: restProj⟩, span⟩ localDecls layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) := by
  simp [evalStmt, placeMentionOperandsInit, projectionHasDeref,
    placeIndexLocalsInit, hInit, hIdxOk]

/--
Universal proof that a dereferencing `StatementKind.placeMention`
(`place.projection = .deref :: restProj`) faults with `MirStepNode.fail .ub`
whenever the root local is uninitialized (`.some .uninit`), dead (`.some .dead`),
or out of bounds (`.none`), or whenever any `.index idxLocal` along `restProj`
is not an initialized scalar (`placeIndexLocalsInit s.frame.locals restProj = false`).
-/
theorem evalStmt_placeMention_deref_uninit_ub
    (s : MachineState)
    (loc : Local)
    (restProj : List ProjectionElem)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    (get? s.frame.locals loc = .some .uninit →
      evalStmt s ⟨.placeMention ⟨loc, .deref :: restProj⟩, span⟩ localDecls layouts =
        MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .some .dead →
      evalStmt s ⟨.placeMention ⟨loc, .deref :: restProj⟩, span⟩ localDecls layouts =
        MirStepNode.fail .ub) ∧
    (get? s.frame.locals loc = .none →
      evalStmt s ⟨.placeMention ⟨loc, .deref :: restProj⟩, span⟩ localDecls layouts =
        MirStepNode.fail .ub) ∧
    (∀ slot : LocalSlot,
      get? s.frame.locals loc = .some slot →
      placeIndexLocalsInit s.frame.locals restProj = false →
      evalStmt s ⟨.placeMention ⟨loc, .deref :: restProj⟩, span⟩ localDecls layouts =
        MirStepNode.fail .ub) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hUninit
    simp [evalStmt, placeMentionOperandsInit, projectionHasDeref, hUninit]
  · intro hDead
    simp [evalStmt, hDead]
  · intro hNone
    simp [evalStmt, hNone]
  · intro slot hSlot hIdxFalse
    cases slot <;>
      simp [evalStmt, placeMentionOperandsInit, projectionHasDeref, placeIndexLocalsInit, hSlot, hIdxFalse]

/--
Biconditional (`↔`) characterization of `StatementKind.placeMention` along a
non-dereferencing projection path (`projectionHasDeref proj = false`) on a live
local (`get? s.frame.locals loc = .some slot`, `slot ≠ .dead`):
1. `evalStmt` steps cleanly to `advanceStmt s s.frame.locals` if and only if
   every `.index idxLocal` along `proj` is an initialized scalar
   (`placeIndexLocalsInit s.frame.locals proj = true`).
2. `evalStmt` faults with `MirStepNode.fail .ub` if and only if some
   `.index idxLocal` along `proj` is not an initialized scalar
   (`placeIndexLocalsInit s.frame.locals proj = false`).
-/
theorem evalStmt_placeMention_nonDeref_index_iff
    (s : MachineState)
    (loc : Local)
    (slot : LocalSlot)
    (proj : List ProjectionElem)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (hNoDeref : projectionHasDeref proj = false)
    (hSlot : get? s.frame.locals loc = .some slot)
    (hLive : slot ≠ .dead) :
    (evalStmt s ⟨.placeMention ⟨loc, proj⟩, span⟩ localDecls layouts =
        MirStepNode.step (advanceStmt s s.frame.locals) ↔
      placeIndexLocalsInit s.frame.locals proj = true) ∧
    (evalStmt s ⟨.placeMention ⟨loc, proj⟩, span⟩ localDecls layouts =
        MirStepNode.fail .ub ↔
      placeIndexLocalsInit s.frame.locals proj = false) := by
  cases slot with
  | dead => exact False.elim (hLive rfl)
  | uninit =>
    cases hIdx : placeIndexLocalsInit s.frame.locals proj <;>
      simp [evalStmt, placeMentionOperandsInit, hNoDeref, hSlot, hIdx] <;>
        intro h <;> nomatch h
  | init v =>
    cases hIdx : placeIndexLocalsInit s.frame.locals proj <;>
      simp [evalStmt, placeMentionOperandsInit, hNoDeref, hSlot, hIdx] <;>
        intro h <;> nomatch h

/--
`ensureNestedFieldShells` on a single-element projection list `[proj]` returns
`.some val` unchanged.
-/
@[simp]
theorem ensureNestedFieldShells_singleton
    (val : Value)
    (proj : ProjectionElem)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (curTyOpt : Option Ty := .none) :
    ensureNestedFieldShells val [proj] localDecls layouts curTyOpt = .some val := by
  cases proj <;> rfl

private theorem length_eq_list_length :
    ∀ {α : Type} (xs : List α), length xs = xs.length
  | _, .nil => rfl
  | _, _ :: _ => by simp [length]

private theorem length_replicateValue :
    ∀ (n : Nat) (v : Value), (replicateValue n v).length = n
  | .zero, _ => rfl
  | .succ k, v => by simp [replicateValue, length_replicateValue k v]

private theorem get?_replicateValue_of_lt :
    ∀ (n idx : Nat) (v : Value),
      idx < n → get? (replicateValue n v) idx = .some v
  | .zero, _, _, h => nomatch h
  | .succ _, .zero, _, _ => rfl
  | .succ k, .succ j, v, h =>
    get?_replicateValue_of_lt k j v (Nat.lt_of_succ_lt_succ h)

private theorem set?_replicateValue_of_lt
    (n idx : Nat)
    (v w : Value)
    (hLt : idx < n) :
    set? (replicateValue n v) idx w = .some ((replicateValue n v).set idx w) := by
  change (if idx < (replicateValue n v).length then
      some ((replicateValue n v).set idx w) else none) =
    .some ((replicateValue n v).set idx w)
  simp [length_replicateValue n v, hLt]

private theorem resolveTyWithLocalDecls_idem
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    resolveTyWithLocalDecls localDecls layouts
      (resolveTyWithLocalDecls localDecls layouts ty) =
    resolveTyWithLocalDecls localDecls layouts ty := by
  rcases ty with ⟨k, idx⟩
  unfold resolveTyWithLocalDecls
  dsimp only
  cases hU : isUnresolvedLayoutIdx layouts idx with
  | false =>
    dsimp only
    rw [hU]
  | true =>
    dsimp only
    cases hF : findDeclOrContainerElemTyWithKind? localDecls layouts k with
    | some declTy =>
      dsimp only
      cases isUnresolvedLayoutIdx layouts declTy.layoutIdx with
      | false => rfl
      | true => simp only [hF]
    | none =>
      dsimp only
      cases hZ : Nat.beq idx 0 <;> cases localDecls <;> dsimp only
      · rw [hU]; dsimp only; rw [hZ]
      · rw [hU]; dsimp only; rw [hF]; dsimp only; rw [hZ]
      · rw [hU]; dsimp only; rw [hZ]
      · cases hP : isPrimitiveScalarKind k with
        | true =>
          dsimp only
          rw [hU]; dsimp only; rw [hF]; dsimp only; rw [hZ]; dsimp only; rw [hP]
        | false =>
          dsimp only
          cases isUnresolvedLayoutIdx layouts (unresolvedLayoutIdx layouts) with
          | false => rfl
          | true =>
            dsimp only
            rw [hF]
            dsimp only
            cases Nat.beq (unresolvedLayoutIdx layouts) 0 with
            | false => rfl
            | true => simp only [hP]

private theorem resolveTyWithLocalDecls_tuple_kind
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fields : List RigidTy)
    (layoutIdx : Nat) :
    (resolveTyWithLocalDecls localDecls layouts
      { kind := .tuple fields, layoutIdx := layoutIdx }).kind = .tuple fields := by
  unfold resolveTyWithLocalDecls
  cases isUnresolvedLayoutIdx layouts layoutIdx with
  | false => rfl
  | true =>
    cases findDeclOrContainerElemTyWithKind? localDecls layouts (.tuple fields) with
    | some _ => rfl
    | none =>
      cases Nat.beq layoutIdx 0 <;> cases localDecls <;> rfl

private theorem uninitContainerFieldShell?_tuple
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fields : List RigidTy)
    (layoutIdx : Nat)
    (fieldIdx : FieldIdx)
    (hLt : fieldIdx < length fields) :
    uninitContainerFieldShell? localDecls layouts
      { kind := .tuple fields, layoutIdx := layoutIdx } fieldIdx =
    .some (.aggregate 0 (replicateValue (length fields) .uninit)) := by
  have hIdem :=
    resolveTyWithLocalDecls_idem localDecls layouts
      { kind := .tuple fields, layoutIdx := layoutIdx }
  rcases hR :
      resolveTyWithLocalDecls localDecls layouts
        { kind := .tuple fields, layoutIdx := layoutIdx } with ⟨rk, rl⟩
  have hRk : rk = .tuple fields := by
    have hRes := resolveTyWithLocalDecls_tuple_kind localDecls layouts fields layoutIdx
    rw [hR] at hRes
    exact hRes
  subst hRk
  rw [hR] at hIdem
  have hBlt : Nat.blt fieldIdx (length fields) = true := Nat.blt_eq.mpr hLt
  unfold uninitContainerFieldShell? isUnionLayout nonUnionAggregateArity?
  rw [hR]
  dsimp only
  rw [hIdem]
  dsimp only
  rw [hBlt]

/--
`uninitFieldWriteShell?` returns the arity-padded `Value.uninit` aggregate shell
(`.aggregate 0 (replicateValue (length fields) .uninit)`) for an in-bounds
single-level field projection (`fieldIdx < length fields`) on a tuple-typed
local, and `.none` when `fieldIdx` is out of bounds.
-/
theorem uninitFieldWriteShell?_field_tuple
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (fields : List RigidTy)
    (layoutIdx : Nat)
    (hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } =
      .some { kind := .tuple fields, layoutIdx := layoutIdx })
    (hLt : fieldIdx < length fields) :
    uninitFieldWriteShell? localDecls layouts loc (.field fieldIdx fieldTy) =
      .some (.aggregate 0 (replicateValue (length fields) .uninit)) := by
  unfold uninitFieldWriteShell?
  rw [hTy]
  dsimp only
  rw [uninitContainerFieldShell?_tuple localDecls layouts fields layoutIdx fieldIdx hLt]
  rfl

/--
`uninitFieldWriteShell?` returns `.some (.aggregate 0 .nil)` for an in-bounds
single-level field projection (`fieldIdx < count`) on a union local whose
resolved `TypeLayout` has `fields = .union count`.
-/
theorem uninitFieldWriteShell?_field_union
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rootTy : Ty)
    (defPath : DefPath)
    (args : List RigidTy)
    (l : TypeLayout)
    (count : Nat)
    (hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } = .some rootTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts rootTy).kind = .adt defPath args)
    (hLook :
      LayoutTable.lookup layouts
        (resolveTyWithLocalDecls localDecls layouts rootTy).layoutIdx = .some l)
    (hFields : l.fields = .union count)
    (hLt : fieldIdx < count) :
    uninitFieldWriteShell? localDecls layouts loc (.field fieldIdx fieldTy) =
      .some (.aggregate 0 .nil) := by
  have hBlt : Nat.blt fieldIdx count = true := Nat.blt_eq.mpr hLt
  unfold uninitFieldWriteShell?
  rw [hTy]
  dsimp only
  unfold uninitContainerFieldShell? isUnionLayout
  rcases hR : resolveTyWithLocalDecls localDecls layouts rootTy with ⟨rk, rl⟩
  rw [hR] at hKind hLook
  dsimp only at hKind hLook ⊢
  subst hKind
  rcases l with ⟨sz, al, br, fs, vs, uninh, fls, vds⟩
  dsimp only at hFields
  subst hFields
  rw [hLook]
  dsimp only
  rw [hBlt]
  rfl

/--
`uninitFieldWriteShell?` returns the arity-padded `Value.uninit` shell
(`.aggregate 0 (replicateValue (length offsets) .uninit)`) for an in-bounds
single-level field projection (`fieldIdx < length offsets`) on a non-union
inhabited single-variant struct local (`variants = .single 0`,
`fields = .arbitrary offsets _`).
-/
theorem uninitFieldWriteShell?_field_struct
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rootTy : Ty)
    (defPath : DefPath)
    (args : List RigidTy)
    (l : TypeLayout)
    (offsets : List Size)
    (memOrder : List Nat)
    (hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } = .some rootTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts rootTy).kind = .adt defPath args)
    (hLook :
      LayoutTable.lookup layouts
        (resolveTyWithLocalDecls localDecls layouts rootTy).layoutIdx = .some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single 0)
    (hFields : l.fields = .arbitrary offsets memOrder)
    (hLt : fieldIdx < length offsets) :
    uninitFieldWriteShell? localDecls layouts loc (.field fieldIdx fieldTy) =
      .some (.aggregate 0 (replicateValue (length offsets) .uninit)) := by
  have hBlt : Nat.blt fieldIdx (length offsets) = true := Nat.blt_eq.mpr hLt
  have hIdem := resolveTyWithLocalDecls_idem localDecls layouts rootTy
  unfold uninitFieldWriteShell?
  rw [hTy]
  dsimp only
  unfold uninitContainerFieldShell? isUnionLayout nonUnionAggregateArity?
  rcases hR : resolveTyWithLocalDecls localDecls layouts rootTy with ⟨rk, rl⟩
  rw [hR] at hKind hLook hIdem
  dsimp only at hKind hLook ⊢
  subst hKind
  rcases l with ⟨sz, al, br, fs, vs, uninh, fls, vds⟩
  dsimp only at hInhab hVar hFields
  subst hInhab hVar hFields
  rw [hLook]
  simp only [hIdem, hLook, hBlt, ensureNestedFieldShells]

/--
`uninitFieldWriteShell?` yields `.none` for every projection head other than a
field projection or a leading `.opaqueCast` (whose shell is the one of the
field projection below the cast chain, `DIV-TR-OPAQUECAST-ROOT-DISPATCH`),
regardless of any trailing projections `rest`.
-/
theorem uninitFieldWriteShell?_eq_none_of_not_field
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem := .nil)
    (hNotField : ∀ (fieldIdx : FieldIdx) (fieldTy : Ty), proj ≠ .field fieldIdx fieldTy)
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none := by
  cases proj with
  | field fieldIdx fieldTy => exact False.elim (hNotField fieldIdx fieldTy rfl)
  | opaqueCast castTy => exact False.elim (hNotCast castTy rfl)
  | _ => rfl

/--
`uninitFieldWriteShell?` yields `.none` whenever the destination local's
declared root type is neither a struct/union (`.adt _ _`), a closure
(`.closure _ _`), nor a tuple (`.tuple _`).
-/
theorem uninitFieldWriteShell?_eq_none_of_non_aggregate_ty
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem := .nil)
    (hNotAdt : ∀ (defPath : DefPath) (args : List RigidTy) (layoutIdx : Nat),
      placeTy localDecls layouts { local_ := loc, projection := .nil } ≠
        .some { kind := .adt defPath args, layoutIdx := layoutIdx })
    (hNotTuple : ∀ (fields : List RigidTy) (layoutIdx : Nat),
      placeTy localDecls layouts { local_ := loc, projection := .nil } ≠
        .some { kind := .tuple fields, layoutIdx := layoutIdx })
    (hNotClosure : ∀ (defPath : DefPath) (captures : List RigidTy) (layoutIdx : Nat),
      placeTy localDecls layouts { local_ := loc, projection := .nil } ≠
        .some { kind := .closure defPath captures, layoutIdx := layoutIdx } := by
      intro _ _ _ h; nomatch h)
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none := by
  cases proj with
  | opaqueCast castTy => exact False.elim (hNotCast castTy rfl)
  | field fieldIdx fieldTy =>
    unfold uninitFieldWriteShell?
    cases hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } with
    | none => rfl
    | some ty =>
      have hResKind :
          (resolveTyWithLocalDecls localDecls layouts ty).kind = ty.kind := by
        unfold resolveTyWithLocalDecls
        cases isUnresolvedLayoutIdx layouts ty.layoutIdx with
        | false => rfl
        | true =>
          cases findDeclOrContainerElemTyWithKind? localDecls layouts ty.kind with
          | some _ => rfl
          | none =>
            cases Nat.beq ty.layoutIdx 0 <;> cases localDecls <;>
              (try rfl) <;> cases isPrimitiveScalarKind ty.kind <;> rfl
      rcases ty with ⟨kind, layoutIdx⟩
      have hIdem :=
        resolveTyWithLocalDecls_idem localDecls layouts
          { kind := kind, layoutIdx := layoutIdx }
      rcases hR :
          resolveTyWithLocalDecls localDecls layouts
            { kind := kind, layoutIdx := layoutIdx } with ⟨rk, rl⟩
      rw [hR] at hResKind hIdem
      dsimp only at hResKind
      subst hResKind
      dsimp only
      unfold uninitContainerFieldShell? isUnionLayout nonUnionAggregateArity?
      rw [hR]
      dsimp only
      rw [hIdem]
      dsimp only
      cases rk with
      | adt defPath args => exact False.elim (hNotAdt defPath args layoutIdx hTy)
      | tuple fields => exact False.elim (hNotTuple fields layoutIdx hTy)
      | closure defPath captures => exact False.elim (hNotClosure defPath captures layoutIdx hTy)
      | _ => rfl
  | _ => rfl

/--
Whenever `uninitFieldWriteShell?` returns `.none` at `.nil` (i.e. the root type
or head projection admits no field shell), it returns `.none` for every trailing
projection path `rest`.
-/
theorem uninitFieldWriteShell?_eq_none_of_nil
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (hNil : uninitFieldWriteShell? localDecls layouts loc proj .nil = .none)
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none := by
  cases proj with
  | opaqueCast castTy => exact False.elim (hNotCast castTy rfl)
  | field fieldIdx fieldTy =>
    unfold uninitFieldWriteShell? at hNil ⊢
    cases hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } with
    | none => rfl
    | some rootTy =>
      rw [hTy] at hNil
      dsimp only at hNil ⊢
      cases hSh : uninitContainerFieldShell? localDecls layouts rootTy fieldIdx with
      | none => rfl
      | some rootShell =>
        rw [hSh] at hNil
        dsimp only [ensureNestedFieldShells] at hNil
        nomatch hNil
  | _ => rfl

/--
Universal characterization (`D13b`) of a projected assignment
`dst = rv` with `dst.projection = .field fieldIdx fieldTy :: rest` into a live
but uninitialized local `dstLoc` with a struct, union, or tuple shell
(`uninitFieldWriteShell? localDecls layouts dstLoc (.field fieldIdx fieldTy) rest =
.some shell`):
1. When the projected write into the shell succeeds
   (`writeProjectedForLocal locals₁ localDecls layouts dstLoc shell
   (.field fieldIdx fieldTy :: rest) val = .ok rootVal'`) and no active protector
   conflicts with the write, `evalStmt` initializes `dstLoc` to `rootVal'`,
   invalidates the borrows conflicting with the written projection, and steps.
2. When an active function-entry protector conflicts with the write
   (`hasProtectedWriteConflict = true`), `evalStmt` faults with
   `MirStepNode.fail .ub`.
-/
theorem evalStmt_assign_uninit_aggregate_field_step
    (s : MachineState)
    (dstLoc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (shell rootVal' : Value)
    (locals₂ : List LocalSlot)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hShell : uninitFieldWriteShell? localDecls layouts dstLoc (.field fieldIdx fieldTy) rest =
      .some shell)
    (hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc shell
        (.field fieldIdx fieldTy :: rest) val = .ok rootVal')
    (hSet : set? locals₁ dstLoc (.init rootVal') = .some locals₂)
    (hNoConflict : ∀ (protHead : Nat) (protTail : List Nat),
      mem₁.activeProtectors = protHead :: protTail →
      hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
        (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
          (.field fieldIdx fieldTy :: rest)) 0 0 (length mem₁.callStack) = false) :
    evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.step
        (advanceStmt s locals₂
          { mem₁ with
            borrows :=
              invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                  (.field fieldIdx fieldTy :: rest)) 0 0 (length mem₁.callStack) }) := by
  have hEval :
      evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: rest⟩ rv, span⟩ localDecls layouts =
        match mem₁.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals₂
              { mem₁ with
                borrows :=
                  invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                    (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                      (.field fieldIdx fieldTy :: rest)) 0 0 (length mem₁.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
              (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                (.field fieldIdx fieldTy :: rest)) 0 0 (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals₂
                { mem₁ with
                  borrows :=
                    invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                      (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                        (.field fieldIdx fieldTy :: rest)) 0 0 (length mem₁.callStack) }) := by
    unfold evalStmt
    dsimp only
    rw [hRv]
    dsimp only
    rw [hUninit, hShell]
    dsimp only
    rw [hWrite]
    dsimp only
    rw [hSet]
  rw [hEval]
  cases hAP : mem₁.activeProtectors with
  | nil => rfl
  | cons protHead protTail =>
    dsimp only
    have hC := hNoConflict protHead protTail hAP
    rw [hC]

/--
`D13b` protected-write conflict boundary: when an uninitialized aggregate field
write would disable a borrow protected by an active function-entry protector
(`hasProtectedWriteConflict = true`), `evalStmt` faults with
`MirStepNode.fail .ub`.
-/
theorem evalStmt_assign_uninit_aggregate_field_protected_conflict_ub
    (s : MachineState)
    (dstLoc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (shell rootVal' : Value)
    (locals₂ : List LocalSlot)
    (protHead : Nat)
    (protTail : List Nat)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hShell : uninitFieldWriteShell? localDecls layouts dstLoc (.field fieldIdx fieldTy) rest =
      .some shell)
    (hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc shell
        (.field fieldIdx fieldTy :: rest) val = .ok rootVal')
    (hSet : set? locals₁ dstLoc (.init rootVal') = .some locals₂)
    (hAP : mem₁.activeProtectors = protHead :: protTail)
    (hConflict :
      hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
        (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
          (.field fieldIdx fieldTy :: rest)) 0 0 (length mem₁.callStack) = true) :
    evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.fail .ub := by
  unfold evalStmt
  dsimp only
  rw [hRv]
  dsimp only
  rw [hUninit, hShell]
  dsimp only
  rw [hWrite]
  dsimp only
  rw [hSet, hAP]
  dsimp only
  rw [hConflict]

/--
`D13b` single-variant struct field initialization (`evalStmt_assign_uninit_struct_field_ok`):
writing `val` into in-bounds field `fieldIdx < length offsets` of a live but
uninitialized local `dstLoc` whose declared type is an inhabited single-variant
struct (`variants = .single 0`, `fields = .arbitrary offsets memOrder`), with no
active protector, initializes `dstLoc` to the arity-padded aggregate
`.aggregate 0 ((replicateValue (length offsets) .uninit).set fieldIdx val)`
(leaving every unwritten field `j ≠ fieldIdx` as `Value.uninit`) and steps.
-/
theorem evalStmt_assign_uninit_struct_field_ok
    (s : MachineState)
    (dstLoc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (rootTy : Ty)
    (defPath : DefPath)
    (args : List RigidTy)
    (l : TypeLayout)
    (offsets : List Size)
    (memOrder : List Nat)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (locals₂ : List LocalSlot)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hTy : placeTy localDecls layouts { local_ := dstLoc, projection := .nil } = .some rootTy)
    (hKind : (resolveTyWithLocalDecls localDecls layouts rootTy).kind = .adt defPath args)
    (hLook :
      LayoutTable.lookup layouts
        (resolveTyWithLocalDecls localDecls layouts rootTy).layoutIdx = .some l)
    (hInhab : l.isUninhabited = false)
    (hVar : l.variants = .single 0)
    (hFields : l.fields = .arbitrary offsets memOrder)
    (hLt : fieldIdx < length offsets)
    (hSet :
      set? locals₁ dstLoc
        (.init (.aggregate 0 ((replicateValue (length offsets) .uninit).set fieldIdx val))) =
        .some locals₂)
    (hProt : mem₁.activeProtectors = .nil)
    (hNoUnion :
      placeTouchesUnion localDecls layouts
        { local_ := dstLoc, projection := .field fieldIdx fieldTy :: .nil } = false := by rfl) :
    evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: .nil⟩ rv, span⟩ localDecls layouts =
      MirStepNode.step
        (advanceStmt s locals₂
          { mem₁ with
            borrows :=
              invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                (match resolveBorrowProjectionElems locals₁ (.field fieldIdx fieldTy :: .nil) with
                 | .some rp => rp
                 | .none => .field fieldIdx fieldTy :: .nil) 0 0 (length mem₁.callStack) }) := by
  have hShell :=
    uninitFieldWriteShell?_field_struct localDecls layouts dstLoc fieldIdx fieldTy
      rootTy defPath args l offsets memOrder hTy hKind hLook hInhab hVar hFields hLt
  have hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc
        (.aggregate 0 (replicateValue (length offsets) .uninit))
        (.field fieldIdx fieldTy :: .nil) val =
        .ok (.aggregate 0 ((replicateValue (length offsets) .uninit).set fieldIdx val)) := by
    unfold writeProjectedForLocal
    rw [hNoUnion]
    dsimp only [writeProjectedValue]
    rw [get?_replicateValue_of_lt (length offsets) fieldIdx .uninit hLt]
    dsimp only [writeProjectedValue]
    rw [set?_replicateValue_of_lt (length offsets) fieldIdx .uninit val hLt]
  have hStep :=
    evalStmt_assign_uninit_aggregate_field_step s dstLoc fieldIdx fieldTy .nil rv span
      localDecls layouts val locals₁ mem₁
      (.aggregate 0 (replicateValue (length offsets) .uninit))
      (.aggregate 0 ((replicateValue (length offsets) .uninit).set fieldIdx val))
      locals₂ hRv hUninit hShell hWrite hSet
      (fun protHead protTail hAP => by rw [hProt] at hAP; nomatch hAP)
  rw [resolveBorrowWriteLocalProj_of_not_union localDecls layouts locals₁ dstLoc
    (.field fieldIdx fieldTy :: .nil) hNoUnion] at hStep
  exact hStep

/--
`D13b` tuple field initialization (`evalStmt_assign_uninit_tuple_field_ok`):
writing `val` into in-bounds field `fieldIdx < length fields` of a live but
uninitialized local `dstLoc` whose declared type is a tuple (`.tuple fields`),
with no active protector, initializes `dstLoc` to the arity-padded aggregate
`.aggregate 0 ((replicateValue (length fields) .uninit).set fieldIdx val)`
(leaving every unwritten sibling field `j ≠ fieldIdx` as `Value.uninit`) and
steps.
-/
theorem evalStmt_assign_uninit_tuple_field_ok
    (s : MachineState)
    (dstLoc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fields : List RigidTy)
    (layoutIdx : Nat)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (locals₂ : List LocalSlot)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hTy : placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
      .some { kind := .tuple fields, layoutIdx := layoutIdx })
    (hLt : fieldIdx < length fields)
    (hSet :
      set? locals₁ dstLoc
        (.init (.aggregate 0 ((replicateValue (length fields) .uninit).set fieldIdx val))) =
        .some locals₂)
    (hProt : mem₁.activeProtectors = .nil) :
    evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: .nil⟩ rv, span⟩ localDecls layouts =
      MirStepNode.step
        (advanceStmt s locals₂
          { mem₁ with
            borrows :=
              invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                (match resolveBorrowProjectionElems locals₁ (.field fieldIdx fieldTy :: .nil) with
                 | .some rp => rp
                 | .none => .field fieldIdx fieldTy :: .nil) 0 0 (length mem₁.callStack) }) := by
  have hShell :=
    uninitFieldWriteShell?_field_tuple localDecls layouts dstLoc fieldIdx fieldTy
      fields layoutIdx hTy hLt
  have hNoUnion :
      placeTouchesUnion localDecls layouts
        { local_ := dstLoc, projection := .field fieldIdx fieldTy :: .nil } = false := by
    unfold placeTy at hTy
    cases hDecl : get? localDecls dstLoc with
    | none => rw [hDecl] at hTy; nomatch hTy
    | some decl =>
      rw [hDecl] at hTy
      dsimp only [resolveProjectedTy] at hTy
      injection hTy with hDeclTy
      cases localDecls with
      | nil => nomatch hDecl
      | cons d ds =>
        rcases layouts with ⟨pB, lE, entries⟩
        cases entries with
        | nil => rfl
        | cons e es =>
          unfold placeTouchesUnion
          dsimp only
          rw [hDecl]
          dsimp only
          rw [hDeclTy]
          unfold tyProjTouchesUnion isUnionLayout
          have hResKind :=
            resolveTyWithLocalDecls_tuple_kind (d :: ds)
              { pointerBits := pB, isLittleEndian := lE, entries := e :: es } fields layoutIdx
          dsimp only
          rw [hResKind]
  have hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc
        (.aggregate 0 (replicateValue (length fields) .uninit))
        (.field fieldIdx fieldTy :: .nil) val =
        .ok (.aggregate 0 ((replicateValue (length fields) .uninit).set fieldIdx val)) := by
    unfold writeProjectedForLocal
    rw [hNoUnion]
    dsimp only [writeProjectedValue]
    rw [get?_replicateValue_of_lt (length fields) fieldIdx .uninit hLt]
    dsimp only [writeProjectedValue]
    rw [set?_replicateValue_of_lt (length fields) fieldIdx .uninit val hLt]
  have hStep :=
    evalStmt_assign_uninit_aggregate_field_step s dstLoc fieldIdx fieldTy .nil rv span
      localDecls layouts val locals₁ mem₁
      (.aggregate 0 (replicateValue (length fields) .uninit))
      (.aggregate 0 ((replicateValue (length fields) .uninit).set fieldIdx val))
      locals₂ hRv hUninit hShell hWrite hSet
      (fun protHead protTail hAP => by rw [hProt] at hAP; nomatch hAP)
  rw [resolveBorrowWriteLocalProj_of_not_union localDecls layouts locals₁ dstLoc
    (.field fieldIdx fieldTy :: .nil) hNoUnion] at hStep
  exact hStep

/--
`D13b` nested tuple field initialization (`evalStmt_assign_uninit_nested_field_ok`):
writing `val` into a 2-level nested field path
`[.field outerIdx outerTy, .field innerIdx innerTy]` on a live but uninitialized
tuple local `dstLoc` (`outerIdx < length tupleFields`) whose outer field `outerTy`
is itself a tuple `.tuple innerFields` (`innerIdx < length innerFields`), with no
active protector, materializes arity-padded `Value.uninit` shells at both the
outer and inner levels, stores `val` at `innerIdx` inside `outerIdx`, and steps.
-/
theorem evalStmt_assign_uninit_nested_field_ok
    (s : MachineState)
    (dstLoc : Local)
    (outerIdx innerIdx : FieldIdx)
    (outerTy innerTy : Ty)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (tupleFields innerFields : List RigidTy)
    (layoutIdx : Nat)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (locals₂ : List LocalSlot)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hTy : placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
      .some { kind := .tuple tupleFields, layoutIdx := layoutIdx })
    (hOuterKind : outerTy.kind = .tuple innerFields)
    (hOuterLt : outerIdx < length tupleFields)
    (hInnerLt : innerIdx < length innerFields)
    (hSet :
      set? locals₁ dstLoc
        (.init
          (.aggregate 0
            ((replicateValue (length tupleFields) .uninit).set outerIdx
              (.aggregate 0 ((replicateValue (length innerFields) .uninit).set innerIdx val))))) =
        .some locals₂)
    (hProt : mem₁.activeProtectors = .nil)
    (hNoUnion :
      placeTouchesUnion localDecls layouts
        { local_ := dstLoc, projection := [.field outerIdx outerTy, .field innerIdx innerTy] } =
        false := by rfl) :
    let projs : List ProjectionElem := [.field outerIdx outerTy, .field innerIdx innerTy]
    evalStmt s ⟨.assign ⟨dstLoc, projs⟩ rv, span⟩ localDecls layouts =
      MirStepNode.step
        (advanceStmt s locals₂
          { mem₁ with
            borrows :=
              invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                (match resolveBorrowProjectionElems locals₁ projs with
                 | .some rp => rp
                 | .none => projs) 0 0 (length mem₁.callStack) }) := by
  dsimp only
  let innerShell : Value := .aggregate 0 (replicateValue (length innerFields) .uninit)
  let shell : Value :=
    .aggregate 0 ((replicateValue (length tupleFields) .uninit).set outerIdx innerShell)
  let rootVal' : Value :=
    .aggregate 0
      ((replicateValue (length tupleFields) .uninit).set outerIdx
        (.aggregate 0 ((replicateValue (length innerFields) .uninit).set innerIdx val)))
  have hStepOuterKind :
      (resolveFieldStepTy localDecls layouts
        (resolveTyWithLocalDecls localDecls layouts
          { kind := .tuple tupleFields, layoutIdx := layoutIdx })
        outerIdx outerTy).kind = .tuple innerFields := by
    rcases outerTy with ⟨ok, ol⟩
    dsimp only at hOuterKind
    subst hOuterKind
    unfold resolveFieldStepTy
    cases isUnresolvedLayoutIdx layouts ol with
    | false => rfl
    | true =>
      dsimp only
      cases LayoutTable.lookup layouts
          (resolveTyWithLocalDecls localDecls layouts
            { kind := .tuple tupleFields, layoutIdx := layoutIdx }).layoutIdx with
      | none => exact resolveTyWithLocalDecls_tuple_kind localDecls layouts innerFields ol
      | some l =>
        dsimp only
        cases l.variants with
        | single _ =>
          dsimp only
          cases get? l.fieldLayouts outerIdx with
          | some _ => rfl
          | none => exact resolveTyWithLocalDecls_tuple_kind localDecls layouts innerFields ol
        | _ => exact resolveTyWithLocalDecls_tuple_kind localDecls layouts innerFields ol
  have hShell :
      uninitFieldWriteShell? localDecls layouts dstLoc (.field outerIdx outerTy)
        [.field innerIdx innerTy] = .some shell := by
    rcases outerTy with ⟨outerKind, outerLayoutIdx⟩
    dsimp only at hOuterKind
    subst hOuterKind
    unfold uninitFieldWriteShell?
    rw [hTy]
    dsimp only
    rw [uninitContainerFieldShell?_tuple localDecls layouts tupleFields layoutIdx outerIdx hOuterLt]
    dsimp only [ensureNestedFieldShells, stripTransparentProjections]
    rw [get?_replicateValue_of_lt (length tupleFields) outerIdx .uninit hOuterLt]
    dsimp only
    have hInnerSh :
        uninitContainerFieldShell? localDecls layouts
          (resolveFieldStepTy localDecls layouts
            (resolveTyWithLocalDecls localDecls layouts
              { kind := .tuple tupleFields, layoutIdx := layoutIdx })
            outerIdx { kind := .tuple innerFields, layoutIdx := outerLayoutIdx })
          innerIdx = .some innerShell := by
      generalize
        resolveFieldStepTy localDecls layouts
          (resolveTyWithLocalDecls localDecls layouts
            { kind := .tuple tupleFields, layoutIdx := layoutIdx })
          outerIdx { kind := .tuple innerFields, layoutIdx := outerLayoutIdx } = stTy at hStepOuterKind ⊢
      rcases stTy with ⟨sk, sl⟩
      dsimp only at hStepOuterKind
      subst hStepOuterKind
      exact uninitContainerFieldShell?_tuple localDecls layouts innerFields sl innerIdx hInnerLt
    rw [hInnerSh]
    dsimp only [ensureNestedFieldShells]
    rw [set?_replicateValue_of_lt (length tupleFields) outerIdx .uninit innerShell hOuterLt]
  have hGetSetSelf : ∀ (xs : List Value) (k : Nat) (v : Value),
      k < xs.length → get? (xs.set k v) k = .some v := by
    intro xs k v hk
    change (xs.set k v)[k]? = .some v
    simp [hk]
  have hSetSetSelf : ∀ (xs : List Value) (k : Nat) (v w : Value),
      k < xs.length → set? (xs.set k v) k w = .some (xs.set k w) := by
    intro xs k v w hk
    change (if k < (xs.set k v).length then some ((xs.set k v).set k w) else none) =
      .some (xs.set k w)
    simp [hk]
  have hOuterRepLt : outerIdx < (replicateValue (length tupleFields) .uninit).length := by
    rw [length_replicateValue]; exact hOuterLt
  have hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc shell
        [.field outerIdx outerTy, .field innerIdx innerTy] val = .ok rootVal' := by
    unfold writeProjectedForLocal
    rw [hNoUnion]
    dsimp only [shell, innerShell, rootVal', writeProjectedValue]
    rw [hGetSetSelf _ outerIdx innerShell hOuterRepLt]
    dsimp only [innerShell, writeProjectedValue]
    rw [get?_replicateValue_of_lt (length innerFields) innerIdx .uninit hInnerLt]
    dsimp only [writeProjectedValue]
    rw [set?_replicateValue_of_lt (length innerFields) innerIdx .uninit val hInnerLt]
    dsimp only
    rw [hSetSetSelf _ outerIdx _ _ hOuterRepLt]
  have hStep :=
    evalStmt_assign_uninit_aggregate_field_step s dstLoc outerIdx outerTy
      [.field innerIdx innerTy] rv span localDecls layouts val locals₁ mem₁ shell rootVal'
      locals₂ hRv hUninit hShell hWrite hSet
      (fun protHead protTail hAP => by rw [hProt] at hAP; nomatch hAP)
  rw [resolveBorrowWriteLocalProj_of_not_union localDecls layouts locals₁ dstLoc
    [.field outerIdx outerTy, .field innerIdx innerTy] hNoUnion] at hStep
  exact hStep

/--
`D13b` boundary (`evalStmt_assign_uninit_non_aggregate_ub`): a projected
assignment into a live but uninitialized local faults with `MirStepNode.fail .ub`
whenever no shell applies (`uninitFieldWriteShell? localDecls layouts dstLoc proj = .none`).
-/
theorem evalStmt_assign_uninit_non_aggregate_ub
    (s : MachineState)
    (dstLoc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (hNotDeref : proj ≠ .deref)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hNoShell : uninitFieldWriteShell? localDecls layouts dstLoc proj = .none)
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.fail .ub := by
  have hNoShellRest :
      uninitFieldWriteShell? localDecls layouts dstLoc proj rest = .none :=
    uninitFieldWriteShell?_eq_none_of_nil localDecls layouts dstLoc proj rest hNoShell hNotCast
  cases proj with
  | deref => exact False.elim (hNotDeref rfl)
  | opaqueCast castTy => exact False.elim (hNotCast castTy rfl)
  | _ => simp [evalStmt, hRv, hUninit, hNoShellRest]

/--
Writing back the element already stored at `i` in `xs` leaves `xs` unchanged.
-/
private theorem set?_self_of_get?
    {α : Type}
    (xs : List α)
    (i : Nat)
    (x : α)
    (h : get? xs i = .some x) :
    set? xs i x = .some xs := by
  change xs[i]? = .some x at h
  change (if i < xs.length then some (xs.set i x) else none) = .some xs
  have hlt : i < xs.length := (List.getElem?_eq_some_iff.mp h).1
  have hx : xs[i] = x := (List.getElem?_eq_some_iff.mp h).2
  simp [hlt, ← hx]

/--
Non-regression for initialized roots (`D13b`): `ensureNestedFieldShells` returns
`.some val` unchanged on every value whose field chain along `projs` is populated
(`fieldShellChainPopulated val projs = true`), for any `localDecls`, `layouts`,
and `curTyOpt`.
-/
theorem ensureNestedFieldShells_eq_self_of_populated :
    ∀ (projs : List ProjectionElem) (val : Value)
      (localDecls : List LocalDecl := .nil)
      (layouts : LayoutTable := emptyLayoutTable)
      (curTyOpt : Option Ty := .none),
      fieldShellChainPopulated val projs = true →
      ensureNestedFieldShells val projs localDecls layouts curTyOpt = .some val := by
  intro projs
  induction projs with
  | nil => intro val _ _ _ _; cases val <;> rfl
  | cons p tl ih =>
    intro val localDecls layouts curTyOpt hPop
    cases tl with
    | nil => cases p <;> cases val <;> rfl
    | cons nextProj rest =>
      cases p with
      | opaqueCast ty =>
        cases val <;> exact ih _ localDecls layouts _ hPop
      | unwrapUnsafeBinder ty =>
        cases val <;> exact ih _ localDecls layouts _ hPop
      | field fieldIdx fieldTy =>
        cases val with
        | aggregate variantIdx fields =>
          unfold fieldShellChainPopulated at hPop
          unfold ensureNestedFieldShells
          have key : ∀ (childVal : Value) (resTy : Ty),
              get? fields fieldIdx = .some childVal →
              fieldShellChainPopulated childVal (nextProj :: rest) = true →
              (match ensureNestedFieldShells childVal (nextProj :: rest) localDecls layouts (.some resTy) with
                | .some childVal' =>
                  match set? fields fieldIdx childVal' with
                  | .some fields' => Option.some (Value.aggregate variantIdx fields')
                  | .none => Option.some (Value.aggregate variantIdx fields)
                | .none => Option.none) = .some (.aggregate variantIdx fields) := by
            intro childVal resTy hGet hPop'
            rw [ih childVal localDecls layouts (.some resTy) hPop']
            dsimp only
            rw [set?_self_of_get? fields fieldIdx _ hGet]
          have hInner :
              (match stripTransparentProjections (nextProj :: rest), fieldTy.kind with
               | .field _ _ :: _, .adt _ _ => true
               | .field _ _ :: _, .tuple _ => true
               | _, _ => false) = true ∨
              (match stripTransparentProjections (nextProj :: rest), fieldTy.kind with
               | .field _ _ :: _, .adt _ _ => true
               | .field _ _ :: _, .tuple _ => true
               | _, _ => false) = false := by
            cases (match stripTransparentProjections (nextProj :: rest), fieldTy.kind with
                   | .field _ _ :: _, .adt _ _ => true
                   | .field _ _ :: _, .tuple _ => true
                   | _, _ => false) <;> simp
          rcases hInner with hTrue | hFalse
          · rw [hTrue] at hPop ⊢
            dsimp only at hPop ⊢
            cases hGet : get? fields fieldIdx with
            | none => rw [hGet] at hPop; nomatch hPop
            | some childVal =>
              rw [hGet] at hPop
              cases childVal with
              | unit => nomatch hPop
              | uninit => nomatch hPop
              | scalar sc => exact key _ _ hGet hPop
              | ptr pv sz => exact key _ _ hGet hPop
              | aggregate v fs => exact key _ _ hGet hPop
          · rw [hFalse]
        | _ => rfl
      | _ => cases val <;> rfl

/--
`evalStmt`-level non-regression for initialized roots (`D13b`): when `dstLoc`
holds `.init rootVal` whose intermediate field slots along `proj :: rest` are
populated (`fieldShellChainPopulated rootVal (proj :: rest) = true`), a
non-dereference projected assignment `dst = rv` whose projection does not start
with `.opaqueCast` (`hNotCast`; a pure cast chain is a whole-local write,
`DIV-TR-OPAQUECAST-ROOT-DISPATCH`) evaluates
`writeProjectedForLocal locals₁ localDecls layouts dstLoc rootVal (proj :: rest) val`
on the original `rootVal` and steps identically to pre-`D13b` semantics.
-/
theorem evalStmt_assign_init_projected_step
    (s : MachineState)
    (dstLoc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val rootVal rootVal' : Value)
    (locals₁ locals₂ : List LocalSlot)
    (mem₁ : Memory)
    (hNotDeref : proj ≠ .deref)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hInit : get? locals₁ dstLoc = .some (.init rootVal))
    (hPop : fieldShellChainPopulated rootVal (proj :: rest) = true)
    (hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc rootVal (proj :: rest) val =
        .ok rootVal')
    (hSet : set? locals₁ dstLoc (.init rootVal') = .some locals₂)
    (hNoConflict : ∀ (protHead : Nat) (protTail : List Nat),
      mem₁.activeProtectors = protHead :: protTail →
      hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
        (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
          (proj :: rest)) 0 0 (length mem₁.callStack) = false)
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.step
        (advanceStmt s locals₂
          { mem₁ with
            borrows :=
              invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                  (proj :: rest)) 0 0 (length mem₁.callStack) }) := by
  have hEns :=
    ensureNestedFieldShells_eq_self_of_populated (proj :: rest) rootVal localDecls layouts
      (placeTy localDecls layouts { local_ := dstLoc, projection := .nil }) hPop
  have hEval :
      evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
        match mem₁.activeProtectors with
        | .nil =>
          MirStepNode.step
            (advanceStmt s locals₂
              { mem₁ with
                borrows :=
                  invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                    (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                      (proj :: rest)) 0 0 (length mem₁.callStack) })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
              (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                (proj :: rest)) 0 0 (length mem₁.callStack)
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals₂
                { mem₁ with
                  borrows :=
                    invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                      (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                        (proj :: rest)) 0 0 (length mem₁.callStack) }) := by
    cases proj with
    | deref => exact False.elim (hNotDeref rfl)
    | opaqueCast castTy => exact False.elim (hNotCast castTy rfl)
    | _ =>
      unfold evalStmt
      dsimp only
      rw [hRv]
      dsimp only
      rw [hInit]
      dsimp only
      rw [hEns]
      dsimp only
      rw [hWrite]
      dsimp only
      rw [hSet]
  rw [hEval]
  cases hAP : mem₁.activeProtectors with
  | nil => rfl
  | cons protHead protTail =>
    dsimp only
    have hC := hNoConflict protHead protTail hAP
    rw [hC]

private theorem writeProjectedValue_uninit_non_field_subproj_ub
    (locals₁ : List LocalSlot)
    (fields : List Value)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (nextProj : ProjectionElem)
    (rest : List ProjectionElem)
    (val : Value)
    (hSlot : get? fields fieldIdx = .none ∨ get? fields fieldIdx = .some .uninit)
    (hSub :
      (∃ idxLocal, nextProj = .index idxLocal) ∨
      (∃ offset minLen fromEnd, nextProj = .constantIndex offset minLen fromEnd) ∨
      (∃ fromIdx toIdx fromEnd, nextProj = .subslice fromIdx toIdx fromEnd) ∨
      (∃ variantName variantIdx, nextProj = .downcast variantName variantIdx)) :
    writeProjectedValue locals₁ (.aggregate 0 fields)
      (.field fieldIdx fieldTy :: nextProj :: rest) val = .ub := by
  dsimp only [writeProjectedValue]
  rcases hSlot with hNone | hUn
  · rw [hNone]
    rcases hSub with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
  · rw [hUn]
    rcases hSub with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

private theorem get?_replicateValue_none_or_uninit :
    ∀ (n idx : Nat),
      get? (replicateValue n .uninit) idx = .none ∨
        get? (replicateValue n .uninit) idx = .some .uninit
  | .zero, .zero => Or.inl rfl
  | .zero, .succ _ => Or.inl rfl
  | .succ _, .zero => Or.inr rfl
  | .succ k, .succ j => get?_replicateValue_none_or_uninit k j

/--
`D13b` sub-projection boundary (`evalStmt_assign_uninit_field_non_field_subproj_ub`):
writing through a never-written field of a live but uninitialized local `dstLoc`
followed immediately by an array index (`.index`), constant index
(`.constantIndex`), subslice (`.subslice`), or enum variant downcast
(`.downcast`) faults with `MirStepNode.fail .ub` for every `fieldTy` and every
declared root type.
-/
theorem evalStmt_assign_uninit_field_non_field_subproj_ub
    (s : MachineState)
    (dstLoc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (nextProj : ProjectionElem)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hSub :
      (∃ idxLocal, nextProj = .index idxLocal) ∨
      (∃ offset minLen fromEnd, nextProj = .constantIndex offset minLen fromEnd) ∨
      (∃ fromIdx toIdx fromEnd, nextProj = .subslice fromIdx toIdx fromEnd) ∨
      (∃ variantName variantIdx, nextProj = .downcast variantName variantIdx)) :
    evalStmt s
        ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: nextProj :: rest⟩ rv, span⟩
        localDecls layouts =
      MirStepNode.fail .ub := by
  have hEnsId : ∀ (fs : List Value) (rt : Ty),
      ensureNestedFieldShells (.aggregate 0 fs)
        (.field fieldIdx fieldTy :: nextProj :: rest)
        localDecls layouts (.some rt) = .some (.aggregate 0 fs) := by
    intro fs rt
    rcases fieldTy with ⟨kind, lIdx⟩
    rcases hSub with ⟨idxLocal, rfl⟩ | ⟨offset, minLen, fromEnd, rfl⟩ |
        ⟨fromIdx, toIdx, fromEnd, rfl⟩ | ⟨variantName, variantIdx, rfl⟩ <;>
      (cases kind <;> rfl)
  unfold evalStmt
  dsimp only
  rw [hRv]
  dsimp only
  rw [hUninit]
  cases hSh : uninitFieldWriteShell? localDecls layouts dstLoc
      (.field fieldIdx fieldTy) (nextProj :: rest) with
  | none => rfl
  | some shell =>
    have hShape :
        shell = .aggregate 0 .nil ∨
        ∃ arity,
          shell = .aggregate 0 (replicateValue arity .uninit) ∧
          (∀ decl,
            get? localDecls dstLoc = .some decl →
            isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts decl.ty) = false) := by
      unfold uninitFieldWriteShell? at hSh
      cases hTy : placeTy localDecls layouts { local_ := dstLoc, projection := .nil } with
      | none => rw [hTy] at hSh; nomatch hSh
      | some rootTy =>
        rw [hTy] at hSh
        dsimp only at hSh
        unfold uninitContainerFieldShell? at hSh
        rcases hR : resolveTyWithLocalDecls localDecls layouts rootTy with ⟨rk, rl⟩
        rw [hR] at hSh
        dsimp only at hSh
        cases hUL : isUnionLayout layouts { kind := rk, layoutIdx := rl } with
        | true =>
          rw [hUL] at hSh
          dsimp only at hSh
          cases hLk : LayoutTable.lookup layouts rl with
          | none => rw [hLk] at hSh; nomatch hSh
          | some l =>
            rw [hLk] at hSh
            rcases l with ⟨sz, al, br, fs, vs, uninh, fls, vds⟩
            cases fs with
            | union count =>
              dsimp only at hSh
              cases hBlt : Nat.blt fieldIdx count with
              | false => rw [hBlt] at hSh; nomatch hSh
              | true =>
                rw [hBlt] at hSh
                dsimp only at hSh
                rw [hEnsId .nil rootTy] at hSh
                injection hSh with hEq
                exact Or.inl hEq.symm
            | _ => nomatch hSh
        | false =>
          rw [hUL] at hSh
          dsimp only at hSh
          cases hAr : nonUnionAggregateArity? localDecls layouts { kind := rk, layoutIdx := rl } with
          | none => rw [hAr] at hSh; nomatch hSh
          | some arity =>
            rw [hAr] at hSh
            dsimp only at hSh
            cases hBlt : Nat.blt fieldIdx arity with
            | false => rw [hBlt] at hSh; nomatch hSh
            | true =>
              rw [hBlt] at hSh
              dsimp only at hSh
              rw [hEnsId (replicateValue arity .uninit) rootTy] at hSh
              injection hSh with hEq
              refine Or.inr ⟨arity, hEq.symm, fun decl hDecl => ?_⟩
              unfold placeTy at hTy
              rw [hDecl] at hTy
              injection hTy with hDeclTy
              rw [hDeclTy, hR]
              exact hUL
    have hWriteUb :
        writeProjectedForLocal locals₁ localDecls layouts dstLoc shell
          (.field fieldIdx fieldTy :: nextProj :: rest) val = .ub := by
      unfold writeProjectedForLocal
      cases hTU : placeTouchesUnion localDecls layouts
          { local_ := dstLoc, projection := .field fieldIdx fieldTy :: nextProj :: rest } with
      | false =>
        rcases hShape with rfl | ⟨arity, rfl, _⟩
        · exact writeProjectedValue_uninit_non_field_subproj_ub
            locals₁ .nil fieldIdx fieldTy nextProj rest val
            (Or.inl (by cases fieldIdx <;> rfl)) hSub
        · exact writeProjectedValue_uninit_non_field_subproj_ub
            locals₁ (replicateValue arity .uninit) fieldIdx fieldTy nextProj rest val
            (get?_replicateValue_none_or_uninit arity fieldIdx) hSub
      | true =>
        cases hDecl : get? localDecls dstLoc with
        | none =>
          rcases hShape with rfl | ⟨arity, rfl, _⟩
          · exact writeProjectedValue_uninit_non_field_subproj_ub
              locals₁ .nil fieldIdx fieldTy nextProj rest val
              (Or.inl (by cases fieldIdx <;> rfl)) hSub
          · exact writeProjectedValue_uninit_non_field_subproj_ub
              locals₁ (replicateValue arity .uninit) fieldIdx fieldTy nextProj rest val
              (get?_replicateValue_none_or_uninit arity fieldIdx) hSub
        | some decl =>
          dsimp only
          unfold writeProjectedValueUnionAware
          rcases hShape with rfl | ⟨arity, rfl, hNotUnion⟩
          · dsimp only
            split
            · rename_i count _ _
              cases Nat.ble (.succ fieldIdx) count with
              | false => rfl
              | true =>
                rcases hSub with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
            · have hN : get? (.nil : List Value) fieldIdx = .none := by cases fieldIdx <;> rfl
              simp [hN]
          · have hNU := hNotUnion decl hDecl
            unfold isUnionLayout at hNU
            rcases hRD : resolveTyWithLocalDecls localDecls layouts decl.ty with ⟨dk, dl⟩
            rw [hRD] at hNU
            dsimp only at hNU ⊢
            rcases get?_replicateValue_none_or_uninit arity fieldIdx with hN | hU
            · cases dk <;> (try { dsimp only; rw [hN] })
              cases hLk : LayoutTable.lookup layouts dl with
              | none => dsimp only; rw [hN]
              | some l =>
                rw [hLk] at hNU
                rcases l with ⟨_, _, _, fs, _, _, _, _⟩
                cases fs with
                | union _ => nomatch hNU
                | _ => dsimp only; rw [hN]
            · rcases hSub with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
              · cases dk <;> (try { dsimp only; rw [hU]; rfl })
                cases hLk : LayoutTable.lookup layouts dl with
                | none => dsimp only; rw [hU]; rfl
                | some l =>
                  rw [hLk] at hNU
                  rcases l with ⟨_, _, _, fs, _, _, _, _⟩
                  cases fs with
                  | union _ => nomatch hNU
                  | _ => dsimp only; rw [hU]; rfl
    dsimp only
    rw [hWriteUb]

/--
`D13b` array-field boundary (`evalStmt_assign_uninit_array_field_elem_ub`):
writing an element of a never-written fixed-length array field
(`.field fieldIdx { kind := .array elemKind count, .. } :: .index idxLocal :: rest`)
of a live but uninitialized local faults with `MirStepNode.fail .ub`, whatever
the local's declared type (`ensureNestedFieldShells` materializes shells only
for struct, union, and tuple fields, never fixed-length arrays).
-/
theorem evalStmt_assign_uninit_array_field_elem_ub
    (s : MachineState)
    (dstLoc idxLocal : Local)
    (fieldIdx : FieldIdx)
    (elemKind : RigidTy)
    (count arrLayoutIdx : Nat)
    (rest : List ProjectionElem)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit) :
    evalStmt s
        ⟨.assign
          ⟨dstLoc,
            .field fieldIdx { kind := .array elemKind count, layoutIdx := arrLayoutIdx } ::
              .index idxLocal :: rest⟩ rv,
          span⟩
        localDecls layouts =
      MirStepNode.fail .ub :=
  evalStmt_assign_uninit_field_non_field_subproj_ub
    s dstLoc fieldIdx { kind := .array elemKind count, layoutIdx := arrLayoutIdx }
    (.index idxLocal) rest rv span localDecls layouts val locals₁ mem₁
    hRv hUninit (Or.inl ⟨idxLocal, rfl⟩)

/--
`F1` partial-shell regression (`evalStmt_assign_uninit_pair_partial_vs_full_copy`):
on a 2-tuple local `_1 : (u32, u32)` initially `.uninit`:
1. Writing `_1.0 = v` initializes `_1` to `.aggregate 0 [v, .uninit]`, so a
   whole-local read `copy _1` and a sibling read `copy _1.1` both fault with
   `.ub`, while `copy _1.0` returns `.ok v`.
2. Subsequently writing `_1.1 = w` updates `_1` to `.aggregate 0 [v, w]`, so
   `copy _1` succeeds with `.ok (.aggregate 0 [v, w])`.
-/
theorem evalStmt_assign_uninit_pair_partial_vs_full_copy
    (val1 val2 : ScalarInt) :
    let v : Value := .scalar val1
    let w : Value := .scalar val2
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let pairTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
    let decls : List LocalDecl :=
      [ { mutability := .mut, ty := u32Ty, debugName := .none }
      , { mutability := .mut, ty := pairTy, debugName := .none }
      , { mutability := .not, ty := u32Ty, debugName := .none }
      , { mutability := .not, ty := u32Ty, debugName := .none } ]
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit, .init v, .init w] }
        memory := emptyMemory }
    let localsAfter0 : List LocalSlot :=
      [.uninit, .init (.aggregate 0 [v, .uninit]), .init v, .init w]
    let s1 : MachineState := advanceStmt s0 localsAfter0 emptyMemory
    let localsAfter1 : List LocalSlot :=
      [.uninit, .init (.aggregate 0 [v, w]), .init v, .init w]
    let s2 : MachineState := advanceStmt s1 localsAfter1 emptyMemory
    evalStmt s0 ⟨.assign ⟨1, [.field 0 u32Ty]⟩ (.use (.copy ⟨2, .nil⟩)), "w0"⟩ decls emptyLayoutTable =
      MirStepNode.step s1 ∧
    evalOperand localsAfter0 (.copy ⟨1, .nil⟩) .nil .nil emptyLayoutTable .nil decls .nil = .ub ∧
    evalOperand localsAfter0 (.copy ⟨1, [.field 1 u32Ty]⟩) .nil .nil emptyLayoutTable .nil decls .nil = .ub ∧
    readProjectedValue localsAfter0 (.aggregate 0 [v, .uninit]) [.field 0 u32Ty] = .ok v ∧
    evalStmt s1 ⟨.assign ⟨1, [.field 1 u32Ty]⟩ (.use (.copy ⟨3, .nil⟩)), "w1"⟩ decls emptyLayoutTable =
      MirStepNode.step s2 ∧
    evalOperand localsAfter1 (.copy ⟨1, .nil⟩) .nil .nil emptyLayoutTable .nil decls .nil =
      .ok (.aggregate 0 [v, w]) localsAfter1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
`F1` nested partial-shell regression (`evalStmt_assign_uninit_nested_pair_partial_vs_full_copy`):
on a nested tuple local `_1 : ((u32, u32), u32)` initially `.uninit`:
1. Writing `_1.0.0 = v` initializes `_1` to
   `.aggregate 0 [.aggregate 0 [v, .uninit], .uninit]`, so both `copy _1.0` and
   `copy _1` fault with `.ub` while reading `_1.0.0` yields `.ok v`.
2. Writing `_1.0.1 = w` updates `_1` to
   `.aggregate 0 [.aggregate 0 [v, w], .uninit]`, so `copy _1.0` returns
   `.ok (.aggregate 0 [v, w])` while `copy _1` still faults with `.ub` until
   `_1.1` is also initialized.
-/
theorem evalStmt_assign_uninit_nested_pair_partial_vs_full_copy
    (val1 val2 : ScalarInt) :
    let v : Value := .scalar val1
    let w : Value := .scalar val2
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let innerPairTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
    let outerTy : Ty :=
      { kind := .tuple [.tuple [.uint .u32, .uint .u32], .uint .u32], layoutIdx := 0 }
    let decls : List LocalDecl :=
      [ { mutability := .mut, ty := u32Ty, debugName := .none }
      , { mutability := .mut, ty := outerTy, debugName := .none }
      , { mutability := .not, ty := u32Ty, debugName := .none }
      , { mutability := .not, ty := u32Ty, debugName := .none } ]
    let s0 : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .uninit, .init v, .init w] }
        memory := emptyMemory }
    let localsAfter0 : List LocalSlot :=
      [.uninit, .init (.aggregate 0 [.aggregate 0 [v, .uninit], .uninit]), .init v, .init w]
    let s1 : MachineState := advanceStmt s0 localsAfter0 emptyMemory
    let localsAfter1 : List LocalSlot :=
      [.uninit, .init (.aggregate 0 [.aggregate 0 [v, w], .uninit]), .init v, .init w]
    let s2 : MachineState := advanceStmt s1 localsAfter1 emptyMemory
    evalStmt s0
        ⟨.assign ⟨1, [.field 0 innerPairTy, .field 0 u32Ty]⟩ (.use (.copy ⟨2, .nil⟩)), "nw0"⟩
        decls emptyLayoutTable =
      MirStepNode.step s1 ∧
    evalOperand localsAfter0 (.copy ⟨1, [.field 0 innerPairTy]⟩) .nil .nil
        emptyLayoutTable .nil decls .nil = .ub ∧
    evalOperand localsAfter0 (.copy ⟨1, .nil⟩) .nil .nil
        emptyLayoutTable .nil decls .nil = .ub ∧
    readProjectedValue localsAfter0 (.aggregate 0 [.aggregate 0 [v, .uninit], .uninit])
        [.field 0 innerPairTy, .field 0 u32Ty] = .ok v ∧
    evalStmt s1
        ⟨.assign ⟨1, [.field 0 innerPairTy, .field 1 u32Ty]⟩ (.use (.copy ⟨3, .nil⟩)), "nw1"⟩
        decls emptyLayoutTable =
      MirStepNode.step s2 ∧
    evalOperand localsAfter1 (.copy ⟨1, [.field 0 innerPairTy]⟩) .nil .nil
        emptyLayoutTable .nil decls .nil =
      .ok (.aggregate 0 [v, w]) localsAfter1 ∧
    evalOperand localsAfter1 (.copy ⟨1, .nil⟩) .nil .nil
        emptyLayoutTable .nil decls .nil = .ub := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/--
`F2` `Deinit` Tree Borrows invalidation and active-protector UB
(`evalStmt_deinit_projected_borrow_invalidation_and_protector_ub`):
on a non-union tuple `_1 : (u32, u32)` initialized to `.aggregate 0 [v, w]`:
1. `Deinit(_1.0)` disables an `.active` borrow targeting `_1.0` while leaving an
   `.active` borrow targeting sibling `_1.1` untouched, updating `_1` to
   `.init (.aggregate 0 [.uninit, w])`.
2. When the borrow targeting `_1.0` carries an active protector `protId`,
   `Deinit(_1.0)` faults with `MirStepNode.fail .ub`.
-/
theorem evalStmt_deinit_projected_borrow_invalidation_and_protector_ub
    (v w : Value) :
    let u32Ty : Ty := { kind := .uint .u32, layoutIdx := 0 }
    let pairTy : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
    let decls : List LocalDecl :=
      [ { mutability := .mut, ty := u32Ty, debugName := .none }
      , { mutability := .mut, ty := pairTy, debugName := .none } ]
    let b0 : BorrowEntry :=
      { tag := 10, targetLocal := 1, targetProjection := [.field 0 u32Ty],
        perm := .active, targetFrameDepth := 0 }
    let b1 : BorrowEntry :=
      { tag := 11, targetLocal := 1, targetProjection := [.field 1 u32Ty],
        perm := .active, targetFrameDepth := 0 }
    let memUnprot : Memory := { emptyMemory with borrows := [b0, b1] }
    let sUnprot : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [v, w])] }
        memory := memUnprot }
    let localsAfter : List LocalSlot :=
      [.uninit, .init (.aggregate 0 [.uninit, w])]
    let b0Prot : BorrowEntry := { b0 with protector := .some 7 }
    let memProt : Memory :=
      { emptyMemory with borrows := [b0Prot, b1], activeProtectors := [7] }
    let sProt : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [v, w])] }
        memory := memProt }
    evalStmt sUnprot ⟨.deinit ⟨1, [.field 0 u32Ty]⟩, "d0"⟩ decls emptyLayoutTable =
      MirStepNode.step
        (advanceStmt sUnprot localsAfter
          { memUnprot with borrows := [{ b0 with perm := .disabled }, b1] }) ∧
    evalStmt sProt ⟨.deinit ⟨1, [.field 0 u32Ty]⟩, "d0p"⟩ decls emptyLayoutTable =
      MirStepNode.fail .ub := by
  exact ⟨rfl, rfl⟩

/--
`B2` fail-closed `SetDiscriminant` regression
(`evalStmt_setDiscriminant_init_without_layout_ub`): on an initialized
`_1 : Option<u32>` holding `None` (`.aggregate 0 []`), `SetDiscriminant(_1, 1)`
without a captured layout entry for `Option<u32>` cannot determine the payload
arity of `Some`, so `padSetDiscriminantInitFields?` returns `.none` and
`evalStmt` faults with `.ub` instead of storing the payload-less
`.aggregate 1 []`, which a later `copy _1` would read as a fully initialized
`Some` value.
-/
theorem evalStmt_setDiscriminant_init_without_layout_ub :
    let optTy : Ty := { kind := .adt "core::option::Option" [.uint .u32], layoutIdx := 0 }
    let decls : List LocalDecl :=
      [ { mutability := .mut, ty := { kind := .uint .u32, layoutIdx := 0 }, debugName := .none }
      , { mutability := .mut, ty := optTy, debugName := .none } ]
    let s : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .init (.aggregate 0 [])] }
        memory := emptyMemory }
    padSetDiscriminantInitFields? decls emptyLayoutTable ⟨1, .nil⟩ 1 [] = .none ∧
    evalStmt s ⟨.setDiscriminant ⟨1, .nil⟩ 1, "sd"⟩ decls emptyLayoutTable =
      MirStepNode.fail .ub := by
  exact ⟨rfl, rfl⟩

/--
`R1` union-field overlap truncation (`resolveBorrowWriteLocalProj_union_root`):
when `dstLoc`'s declared type resolves to a `FieldsShape.union` layout
(`isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts decl.ty) = true`)
and `layouts.entries` is non-empty, `resolveBorrowWriteLocalProj` truncates any
direct `.field fieldIdx fieldTy :: rest` write on `dstLoc` to `.nil`, so
`borrowEntryOverlapsWrite` treats the write as overlapping every sibling union
field borrow `&_u.other`.
-/
theorem resolveBorrowWriteLocalProj_union_root
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals : List LocalSlot)
    (dstLoc : Local)
    (decl : LocalDecl)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rest : List ProjectionElem)
    (hEntries : layouts.entries ≠ .nil)
    (hDecl : get? localDecls dstLoc = .some decl)
    (hUnion : isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts decl.ty) = true)
    (hNonZst :
      placeIsZeroSized
        localDecls
        layouts
        { local_ := dstLoc, projection := .field fieldIdx fieldTy :: rest } = false) :
    resolveBorrowWriteLocalProj localDecls layouts locals dstLoc
      (.field fieldIdx fieldTy :: rest) = .nil := by
  cases localDecls with
  | nil => cases hDecl
  | cons d ds =>
    rcases layouts with ⟨pB, lE, entries⟩
    cases entries with
    | nil => exact False.elim (hEntries rfl)
    | cons e es =>
      unfold resolveBorrowWriteLocalProj placeTouchesUnion
      rw [hNonZst]
      dsimp only
      rw [hDecl]
      dsimp only [tyProjTouchesUnion]
      rw [hUnion]
      dsimp only
      cases hRes : resolveBorrowProjectionElems locals rest with
      | none =>
        dsimp only [resolveBorrowProjectionElems]
        rw [hRes]
        dsimp only [truncateTyProjAtUnion]
        rw [hUnion]
        rfl
      | some rp =>
        dsimp only [resolveBorrowProjectionElems]
        rw [hRes]
        dsimp only [truncateTyProjAtUnion]
        rw [hUnion]
        rfl

/--
`R1` union sibling-field borrow invalidation and active-protector UB
(`evalStmt_assign_union_field_sibling_borrow_invalidation_and_protector_ub`):
when `dstLoc` is a `FieldsShape.union` local (`isUnionLayout = true`) and
`writeTy` is nonzero-sized (`tyIsZeroSized writeTy = false`), writing to
`.field writeIdx writeTy` overlaps a borrow targeting ANY sibling field
`.field borIdx borTy` (`borIdx ≠ writeIdx` included):
1. With no active protectors (`mem₁.activeProtectors = .nil`), an `.active` or
   `.frozen` borrow targeting `.field borIdx borTy` of `dstLoc` transitions to
   `.disabled`.
2. When that sibling borrow is protected by `mem₁.activeProtectors` (`protId`)
   and is `.active` or `.frozen`, `evalStmt` faults with `MirStepNode.fail .ub`.
-/
theorem evalStmt_assign_union_field_sibling_borrow_invalidation_and_protector_ub
    (s : MachineState)
    (dstLoc : Local)
    (decl : LocalDecl)
    (writeIdx borIdx : FieldIdx)
    (writeTy borTy : Ty)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val rootVal rootVal' : Value)
    (locals₁ locals₂ : List LocalSlot)
    (mem₁ : Memory)
    (tag protId : Nat)
    (perm : TreeBorrowPerm)
    (hEntries : layouts.entries ≠ .nil)
    (hDecl : get? localDecls dstLoc = .some decl)
    (hUnion : isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts decl.ty) = true)
    (hNonZst : tyIsZeroSized writeTy = false)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hInit : get? locals₁ dstLoc = .some (.init rootVal))
    (hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc
        rootVal
        (.field writeIdx writeTy :: .nil) val = .ok rootVal')
    (hSet : set? locals₁ dstLoc (.init rootVal') = .some locals₂)
    (hPerm : perm = .active ∨ perm = .frozen) :
    (let sibEntry : BorrowEntry :=
       { tag := tag, targetLocal := dstLoc,
         targetProjection := .field borIdx borTy :: .nil, perm := perm,
         targetFrameDepth := length mem₁.callStack }
     mem₁.borrows = sibEntry :: .nil →
     mem₁.activeProtectors = .nil →
     evalStmt s ⟨.assign ⟨dstLoc, .field writeIdx writeTy :: .nil⟩ rv, span⟩
         localDecls layouts =
       MirStepNode.step
         (advanceStmt s locals₂
           { mem₁ with borrows := { sibEntry with perm := .disabled } :: .nil })) ∧
    (let protEntry : BorrowEntry :=
       { tag := tag, targetLocal := dstLoc,
         targetProjection := .field borIdx borTy :: .nil, perm := perm,
         protector := .some protId, targetFrameDepth := length mem₁.callStack }
     mem₁.borrows = protEntry :: .nil →
     mem₁.activeProtectors = protId :: .nil →
     evalStmt s ⟨.assign ⟨dstLoc, .field writeIdx writeTy :: .nil⟩ rv, span⟩
         localDecls layouts =
       MirStepNode.fail .ub) := by
  have hPlaceNonZst :
      placeIsZeroSized
        localDecls
        layouts
        { local_ := dstLoc, projection := .field writeIdx writeTy :: .nil } = false := by
    unfold placeIsZeroSized placeTy
    rw [hDecl]
    exact hNonZst
  have hTrunc :=
    resolveBorrowWriteLocalProj_union_root
      localDecls layouts locals₁ dstLoc decl writeIdx writeTy .nil
      hEntries hDecl hUnion hPlaceNonZst
  refine ⟨?_, ?_⟩
  · intro sibEntry hBor hAP
    unfold evalStmt
    dsimp only [ensureNestedFieldShells]
    rw [hRv]
    dsimp only [ensureNestedFieldShells]
    rw [hInit]
    dsimp only [ensureNestedFieldShells]
    rw [hWrite]
    dsimp only
    rw [hSet, hAP, hBor, hTrunc]
    rcases hPerm with rfl | rfl <;>
      simp [invalidateConflictingBorrowsAtProj, updateBorrowPermAtProj,
        treeBorrowWriterRelatedness, borrowEntryOverlapsWrite,
        projectionsOverlap, stripTransparentProjections,
        normalizeSubsliceProjections, projectionsOverlapAux,
        treeBorrowNodeAccess, treeBorrowPermTransition, applyTreeBorrowTransition,
        sibEntry, Nat.beq_refl]
  · intro protEntry hBor hAP
    unfold evalStmt
    dsimp only [ensureNestedFieldShells]
    rw [hRv]
    dsimp only [ensureNestedFieldShells]
    rw [hInit]
    dsimp only [ensureNestedFieldShells]
    rw [hWrite]
    dsimp only
    rw [hSet, hAP, hBor, hTrunc]
    rcases hPerm with rfl | rfl <;>
      simp [hasProtectedWriteConflict,
        borrowEntryOverlapsWrite, projectionsOverlap, stripTransparentProjections,
        normalizeSubsliceProjections, projectionsOverlapAux,
        isBorrowProtected, natListContainsBool, borrowEntryWriteConflicts,
        protEntry, Nat.beq_refl]

private theorem lookupBorrow_mem_of_some
    {borrows : List BorrowEntry} {tag : Nat} {entry : BorrowEntry}
    (h : lookupBorrow borrows tag = .some entry) : entry ∈ borrows := by
  induction borrows with
  | nil => cases h
  | cons b bs ih =>
    unfold lookupBorrow at h
    cases hEq : Nat.beq b.tag tag with
    | true =>
      rw [hEq] at h
      injection h with hb
      subst hb
      exact .head _
    | false =>
      rw [hEq] at h
      exact .tail _ (ih h)

private theorem nat_beq_eq_false_of_ne {a b : Nat} (hne : a ≠ b) : Nat.beq a b = false := by
  cases h : Nat.beq a b with
  | false => rfl
  | true => exact False.elim (hne (Nat.eq_of_beq_eq_true h))

/--
Whole-local pointer dereference identity for `invalidateDerefWriteBorrowsWithLayouts`:
when `ptrLoc` holds a thin pointer `.ptr ptrVal sz`, `restProj = .nil`, and every
entry in `borrows` has `targetProjection = .nil`, `invalidateDerefWriteBorrowsWithLayouts`
reduces identically to `invalidateDerefWriteBorrows`.
-/
theorem invalidateDerefWriteBorrowsWithLayouts_eq_of_thinPtr_nil_target
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (locals₁ : List LocalSlot)
    (borrows : List BorrowEntry)
    (ptrLoc : Local)
    (ptrVal : ProvenancePtr)
    (sz : Nat)
    (hPtr : get? locals₁ ptrLoc = .some (.init (.ptr ptrVal sz)))
    (hNilTargets : ∀ b ∈ borrows, b.targetProjection = .nil) :
    invalidateDerefWriteBorrowsWithLayouts
      localDecls layouts locals₁ borrows ⟨ptrLoc, .deref :: .nil⟩ .nil =
    invalidateDerefWriteBorrows
      locals₁ borrows ⟨ptrLoc, .deref :: .nil⟩ .nil := by
  cases borrows with
  | nil => rfl
  | cons b₁ rest =>
    cases rest with
    | nil =>
      unfold invalidateDerefWriteBorrowsWithLayouts invalidateDerefWriteBorrows
      rw [hPtr]
      dsimp only [extractDerefPtrVal?]
      cases hLook : lookupBorrow (b₁ :: .nil) ptrVal.tag with
      | none => rfl
      | some entry =>
        have hTgt : entry.targetProjection = .nil :=
          hNilTargets entry (lookupBorrow_mem_of_some hLook)
        have hFull :
            resolveDerefWriteFullProj locals₁ locals₁ (.ptr ptrVal sz) entry .nil = .nil := by
          unfold resolveDerefWriteFullProj
          rw [hTgt]
          rfl
        dsimp only []
        rw [hFull]
        rfl
    | cons b₂ rest₂ =>
      unfold invalidateDerefWriteBorrowsWithLayouts invalidateDerefWriteBorrows
      rw [hPtr]
      dsimp only [extractDerefPtrVal?]
      cases hLook : lookupBorrow (b₁ :: b₂ :: rest₂) ptrVal.tag with
      | none => rfl
      | some entry =>
        have hTgt : entry.targetProjection = .nil :=
          hNilTargets entry (lookupBorrow_mem_of_some hLook)
        have hFull :
            resolveDerefWriteFullProj locals₁ locals₁ (.ptr ptrVal sz) entry .nil = .nil := by
          unfold resolveDerefWriteFullProj
          rw [hTgt]
          rfl
        dsimp only []
        rw [hFull]

/--
`R1` dereferencing union field write sibling-borrow invalidation and
active-protector UB
(`evalStmt_assign_deref_union_field_sibling_borrow_invalidation_and_protector_ub`):
when `ptrLoc` holds an `.active` root pointer/reference `writerEntry` targeting
union local `uLoc` (`isUnionLayout = true`), and `sibEntry` (`sibTag ≠ ptrVal.tag`)
is a foreign `.active` or `.frozen` borrow targeting ANY sibling union field
`.field borIdx borTy` (`borIdx ≠ writeIdx` included), a frame-local dereferencing
write `(*ptrLoc).writeIdx = rv` to nonzero-sized field `writeTy`
(`tyIsZeroSized writeTy = false`) overlaps `sibEntry`:
1. With `mem₁.activeProtectors = .nil`, `sibEntry` transitions to `.disabled`
   while `writerEntry` stays `.active`.
2. When `sibEntry` carries active protector `protId` (`mem₁.activeProtectors = protId :: .nil`)
   and `mem₁.callerLocals = .nil`, `evalStmt` faults with `MirStepNode.fail .ub`.
-/
theorem evalStmt_assign_deref_union_field_sibling_borrow_invalidation_and_protector_ub
    (s : MachineState)
    (ptrLoc uLoc : Local)
    (uDecl : LocalDecl)
    (ptrVal : ProvenancePtr)
    (ptrSz sibTag protId : Nat)
    (writeIdx borIdx : FieldIdx)
    (writeTy borTy : Ty)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ locals₂ : List LocalSlot)
    (mem₁ : Memory)
    (sibPerm : TreeBorrowPerm)
    (hEntries : layouts.entries ≠ .nil)
    (hDecl : get? localDecls uLoc = .some uDecl)
    (hUnion : isUnionLayout layouts (resolveTyWithLocalDecls localDecls layouts uDecl.ty) = true)
    (hNonZst : tyIsZeroSized writeTy = false)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hPtr : get? locals₁ ptrLoc = .some (.init (.ptr ptrVal ptrSz)))
    (hTagNe : ptrVal.tag ≠ sibTag)
    (hSibPerm : sibPerm = .active ∨ sibPerm = .frozen) :
    let writerEntry : BorrowEntry :=
      { tag := ptrVal.tag, targetLocal := uLoc, targetProjection := .nil, perm := .active }
    let dst : Place := ⟨ptrLoc, .deref :: .field writeIdx writeTy :: .nil⟩
    (let sibEntry : BorrowEntry :=
       { tag := sibTag, targetLocal := uLoc,
         targetProjection := .field borIdx borTy :: .nil, perm := sibPerm }
     mem₁.borrows = writerEntry :: sibEntry :: .nil →
     mem₁.activeProtectors = .nil →
     writePlaceValue locals₁ mem₁.borrows dst val localDecls layouts mem₁.callStack =
       .ok locals₂ →
     evalStmt s ⟨.assign dst rv, span⟩ localDecls layouts =
       MirStepNode.step
         (advanceStmt s locals₂
           { mem₁ with
             borrows := writerEntry :: { sibEntry with perm := .disabled } :: .nil })) ∧
    (let protEntry : BorrowEntry :=
       { tag := sibTag, targetLocal := uLoc,
         targetProjection := .field borIdx borTy :: .nil, perm := sibPerm,
         protector := .some protId }
     mem₁.borrows = writerEntry :: protEntry :: .nil →
     mem₁.activeProtectors = protId :: .nil →
     mem₁.callerLocals = .nil →
     mem₁.callStack = .nil →
     writePlaceValue locals₁ mem₁.borrows dst val localDecls layouts mem₁.callStack =
       .ok locals₂ →
     evalStmt s ⟨.assign dst rv, span⟩ localDecls layouts =
       MirStepNode.fail .ub) := by
  intro writerEntry dst
  have hEffNil :
      resolveDerefBorrowWriteFullProj
        localDecls layouts uLoc (.field writeIdx writeTy :: .nil) = .nil := by
    cases localDecls with
    | nil => cases hDecl
    | cons d ds =>
      rcases layouts with ⟨pB, lE, entries⟩
      cases entries with
      | nil => exact False.elim (hEntries rfl)
      | cons e es =>
        unfold resolveDerefBorrowWriteFullProj placeTouchesUnion placeIsZeroSized placeTy
        dsimp only []
        rw [hDecl]
        dsimp only [tyProjTouchesUnion, resolveProjectedTy]
        rw [hUnion, hNonZst]
        dsimp only [truncateTyProjAtUnion]
        rw [hUnion]
        rfl
  have hBeqNe : Nat.beq sibTag ptrVal.tag = false :=
    nat_beq_eq_false_of_ne hTagNe.symm
  have hBeqNeSym : Nat.beq ptrVal.tag sibTag = false :=
    nat_beq_eq_false_of_ne hTagNe
  refine ⟨?_, ?_⟩
  · intro sibEntry hBor hAP hWOk
    unfold evalStmt
    dsimp only [dst]
    rw [hRv]
    dsimp only [evalPlaceWrite]
    rw [hAP]
    dsimp only
    rw [hWOk]
    dsimp only [derefWriteTreeUB, derefWriteUnionProtectorUB,
      invalidateDerefWriteBorrowsWithLayouts]
    rw [hBor, hPtr]
    dsimp only [lookupBorrow, extractDerefPtrVal?, writerEntry]
    simp only [Nat.beq_refl]
    have hFull :
        resolveDerefWriteFullProj
          locals₁ locals₁ (.ptr ptrVal ptrSz)
          { tag := ptrVal.tag, targetLocal := uLoc, targetProjection := .nil, perm := .active }
          (.field writeIdx writeTy :: .nil) .nil mem₁.callStack =
          (.field writeIdx writeTy :: .nil) := rfl
    rw [hFull, hEffNil]
    dsimp only [treeBorrowAncestorsChildAccessUB, Bool.or]
    rcases hSibPerm with rfl | rfl <;>
    · dsimp only [invalidateTreeBorrowsAtProj, updateBorrowPermTreeAtProj,
        updateBorrowPermAtProj, resolveTreeBorrowWriterTag, lookupBorrow,
        isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux, length, sibEntry]
      simp [lookupBorrow, isBorrowDescendantOrSelfAux, hBeqNe, hBeqNeSym,
        borrowEntryOverlapsWrite, projectionsOverlap, stripTransparentProjections,
        normalizeSubsliceProjections, projectionsOverlapAux,
        treeBorrowWriterRelatedness, treeBorrowNodeAccess,
        treeBorrowPermTransition, applyTreeBorrowTransition]
  · intro protEntry hBor hAP hCaller hCS hWOk
    unfold evalStmt
    dsimp only [dst]
    rw [hRv]
    dsimp only
    cases hEPW :
        evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors localDecls layouts
          mem₁.callStack with
    | ub =>
      dsimp only
      rw [hCS]
      dsimp only
      rw [hCaller]
    | unsupported =>
      exfalso
      unfold evalPlaceWrite at hEPW
      rw [hAP] at hEPW
      dsimp only at hEPW
      split at hEPW
      · cases hEPW
      · rw [hWOk] at hEPW; cases hEPW
    | ok locs₂ =>
      dsimp only [derefWriteTreeUB, derefWriteUnionProtectorUB]
      rw [hAP, hBor, hPtr]
      dsimp only [lookupBorrow, extractDerefPtrVal?, writerEntry]
      simp only [Nat.beq_refl]
      have hFull :
          resolveDerefWriteFullProj
            locals₁ locals₁ (.ptr ptrVal ptrSz)
            { tag := ptrVal.tag, targetLocal := uLoc, targetProjection := .nil, perm := .active }
            (.field writeIdx writeTy :: .nil) .nil mem₁.callStack =
            (.field writeIdx writeTy :: .nil) := rfl
      rw [hFull]
      dsimp only []
      rw [hEffNil]
      dsimp only [treeBorrowAncestorsChildAccessUB]
      rcases hSibPerm with rfl | rfl <;>
      · dsimp only [hasProtectedTreeWriteConflict, resolveTreeBorrowWriterTag,
          lookupBorrow, isBorrowDescendantOrSelf, isBorrowDescendantOrSelfAux,
          length, protEntry]
        simp [lookupBorrow, isBorrowDescendantOrSelfAux, hBeqNe, hBeqNeSym,
          borrowEntryOverlapsWrite, projectionsOverlap,
          stripTransparentProjections, normalizeSubsliceProjections, projectionsOverlapAux,
          isBorrowProtected, natListContainsBool, borrowEntryWriteConflicts,
          treeBorrowWriterRelatedness, treeBorrowNodeAccess, treeBorrowPermTransition,
          treeBorrowTransitionIsUB]

end Trusted.Rustc.V2026_06_01.MirSemantics
