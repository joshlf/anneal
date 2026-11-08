import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_08_01.Layout
import Trusted.Rustc.V2026_08_01.MirAst.Types
import Trusted.Rustc.V2026_08_01.MirAst.Places
import Trusted.Rustc.V2026_08_01.MirAst.Rvalues
import Trusted.Rustc.V2026_08_01.MirAst.Statements
import Trusted.Rustc.V2026_08_01.MirAst.Body
import Trusted.Rustc.V2026_08_01.MirSemantics.State
import Trusted.Rustc.V2026_08_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_08_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_08_01.MirSemantics.Places

namespace Trusted.Rustc.V2026_08_01.MirSemantics

open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_08_01.Layout
open Trusted.Rustc.V2026_08_01.MirAst

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
          with
          | .ok locals₄ =>
            let borrows' :=
              invalidateConflictingBorrows
                s.memory.borrows
                dstEntry.targetLocal
                (.some dstPtr.tag)
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
    (newVal : Value) :
    MirStepNode :=
  match
    writePlaceValue
      locals₃
      s.memory.borrows
      dstPlace
      newVal
  with
  | .ok locals₄ =>
    let borrows' :=
      invalidateConflictingBorrows
        s.memory.borrows
        dstTargetLocal
        (.some dstTag)
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
                | .none => MirStepNode.fail .ub

/--
Evaluate `copy_nonoverlapping` once `srcVal`, `dstVal`, and scalar `countBits`
have been evaluated into `locals₃`, supporting direct element copies,
byte-encoded copies into initialized or union destinations, and untyped copies
of uninitialized union bytes (`FieldsShape.union`) into a union destination.

Reference (`core::intrinsics::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/intrinsics/fn.copy_nonoverlapping.html>

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The following is a non-exhaustive list of invalid values:
> - A value of any type, other than a union or raw pointer, with uninitialized
>   bytes (except for padding bytes, which may be uninitialized)."
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
              match srcRootSlot, dstRootSlot with
              | .some (.init srcRootVal), .some (.init dstRootVal) =>
                let dstPlace : Place := {
                  local_ := dstEntry.targetLocal
                  projection := dstEntry.targetProjection
                }
                let dstLocalPlaceTy : Option Ty :=
                  match get? locals₃ dstPlace.local_ with
                  | .some _ => placeTy localDecls layouts dstPlace
                  | .none => .none
                let dstIsAdt : Bool :=
                  match dstLocalPlaceTy with
                  | .some { kind := .adt _ _, .. } => true
                  | _ => false
                let writeDstVal (newVal : Value) : MirStepNode :=
                  commitCopyDstPlaceWrite
                    s
                    dstPlace
                    dstEntry.targetLocal
                    dstPtr.tag
                    locals₃
                    newVal
                let copyViaBytes
                    (srcSubVal dstSubVal : Value) :
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
                    let srcSliceVal : Option Value :=
                      match srcSubVal with
                      | .aggregate 0 srcElems =>
                        match
                          Nat.ble (Nat.add srcStart n) (length srcElems)
                        with
                        | true =>
                          .some
                            (.aggregate 0
                              (takeValues n (dropValues srcStart srcElems)))
                        | false =>
                          match Nat.beq srcStart 0 with
                          | true => .some srcSubVal
                          | false => .none
                      | _ => .some srcSubVal
                    let dstTargetTyOpt : Option Ty :=
                      match dstLocalPlaceTy with
                      | .some t => .some t
                      | .none => operandPointeeTy localDecls layouts dst
                    match srcSliceVal with
                    | .none => MirStepNode.fail .ub
                    | .some sVal =>
                      match encodeUntypedValueToBytes defaultCodecFuel sVal with
                      | .none => MirStepNode.unsupported
                      | .some bs =>
                        let spliceBytesToDstArray : Option Value :=
                          match Bool.not dstIsAdt, dstSubVal with
                          | true, .aggregate 0 dstElems =>
                            match
                              Nat.ble
                                (Nat.add dstStart (length bs))
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
                                  (length bs)
                                  bs
                              with
                              | .some copiedBytes =>
                                .some
                                  (.aggregate 0
                                    (spliceValues
                                      copiedBytes
                                      dstStart
                                      dstElems))
                              | .none => .none
                          | _, _ => .none
                        let preferSplicedArray : Bool :=
                          match dstLocalPlaceTy, dstSubVal with
                          | .none, .aggregate 0 _ => true
                          | _, _ => false
                        match preferSplicedArray, spliceBytesToDstArray with
                        | true, .some splicedVal => writeDstVal splicedVal
                        | _, _ =>
                          match dstTargetTyOpt with
                          | .some dstPt =>
                            match rigidTyByteSize layouts dstPt with
                            | .some dstBytes =>
                              match Nat.beq (length bs) dstBytes with
                              | true =>
                                match
                                  decodeValueFromBytes
                                    defaultCodecFuel
                                    layouts
                                    dstPt
                                    bs
                                with
                                | .some decodedVal => writeDstVal decodedVal
                                | .none =>
                                  match spliceBytesToDstArray with
                                  | .some splicedVal => writeDstVal splicedVal
                                  | .none => MirStepNode.fail .ub
                              | false =>
                                match spliceBytesToDstArray with
                                | .some splicedVal => writeDstVal splicedVal
                                | .none => MirStepNode.unsupported
                            | .none =>
                              match spliceBytesToDstArray with
                              | .some splicedVal => writeDstVal splicedVal
                              | .none => MirStepNode.unsupported
                          | .none =>
                            match spliceBytesToDstArray with
                            | .some splicedVal => writeDstVal splicedVal
                            | .none => MirStepNode.fail .ub
                match
                  readProjectedValue
                    locals₃
                    srcRootVal
                    srcEntry.targetProjection,
                  readProjectedValue
                    locals₃
                    dstRootVal
                    dstEntry.targetProjection
                with
                | .ok (.aggregate 0 srcElems),
                  .ok (.aggregate 0 dstElems) =>
                  let inBounds :=
                    Bool.and
                      (Bool.not dstIsAdt)
                      (Bool.and
                        (Nat.ble (Nat.add srcStart n) (length srcElems))
                        (Nat.ble (Nat.add dstStart n) (length dstElems)))
                  match inBounds with
                  | false =>
                    match
                      Bool.and
                        (Nat.beq dstStart 0)
                        (Nat.ble (Nat.add srcStart n) (length srcElems))
                    with
                    | true =>
                      copyViaBytes
                        (.aggregate 0 srcElems)
                        (.aggregate 0 dstElems)
                    | false => MirStepNode.fail .ub
                  | true =>
                    let sameContainer :=
                      Bool.and
                        (Nat.beq srcEntry.targetLocal dstEntry.targetLocal)
                        (projectionsOverlap
                          srcEntry.targetProjection
                          dstEntry.targetProjection)
                    let disjoint :=
                      match Nat.beq srcPtr.tag dstPtr.tag with
                      | true => false
                      | false =>
                        match sameContainer with
                        | false => true
                        | true =>
                          Bool.or
                            (Nat.ble (Nat.add srcStart n) dstStart)
                            (Nat.ble (Nat.add dstStart n) srcStart)
                    match disjoint with
                    | false => MirStepNode.fail .ub
                    | true =>
                      let copiedSlice :=
                        takeValues n (dropValues srcStart srcElems)
                      let dstElems' :=
                        spliceValues copiedSlice dstStart dstElems
                      writeDstVal (.aggregate 0 dstElems')
                | .ok srcSubVal, .ok dstSubVal =>
                  copyViaBytes srcSubVal dstSubVal
                | .ok srcSubVal, .ub =>
                  match Nat.beq dstStart 0 with
                  | true => copyViaBytes srcSubVal .unit
                  | false => MirStepNode.fail .ub
                | _, _ => MirStepNode.fail .ub
              | _, _ => MirStepNode.fail .ub
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
Test whether any `BorrowEntry` in `borrows` targeting stack local `loc` carries a
function-entry lifetime protector (`RetagKind.fnEntry`) that is still active in
`activeProtectors` (`isBorrowProtected`).

Freeing `loc`'s storage (`StorageDead(loc)`, or the implicit deallocation
performed by `StorageLive(loc)`) acts as a write to every byte of the local that
disables every tag minted from it (`disableLocalBorrows`), so the presence of
such a protected tag makes the deallocation immediate undefined behavior. This
check subsumes the whole-local foreign-write conflict check
`hasProtectedWriteConflict borrows activeProtectors loc .none .nil`: unlike a
foreign write, which tolerates `.reserved` (and already-`.disabled`) tags,
deallocation rejects every protected tag regardless of its current permission.
Function-entry protectors only cover memory owned by other frames (argument
pointees), so with frame-relative `BorrowEntry.targetLocal` indices a protected
entry can only match a local of the running frame through an index collision
with a caller-frame local inside an inline callee frame, where the check errs
on the side of `.ub`.

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
    (loc : Local) :
    Bool :=
  match borrows with
  | .nil => false
  | entry :: rest =>
    match
      Bool.and
        (Nat.beq entry.targetLocal loc)
        (isBorrowProtected activeProtectors entry)
    with
    | true => true
    | false => hasProtectedLocalBorrow rest activeProtectors loc

/--
Disable every `BorrowEntry` in `borrows` targeting stack local `loc` (setting its
Tree Borrows permission to `.disabled`), leaving every other entry unchanged.

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

`BorrowEntry.targetLocal` indexes the locals of the frame that minted the tag,
while the borrow table is shared by every inline call frame on
`Memory.callStack`, so inside an inline callee frame this also disables
caller-frame entries whose local index equals `loc`. The approximation is
conservative: it can only make a later access through such a caller tag fault
with `.ub` after the callee returns, never hide undefined behavior.

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
def disableLocalBorrows : List BorrowEntry → Local → List BorrowEntry
  | .nil, _ => .nil
  | entry :: rest, loc =>
    match Nat.beq entry.targetLocal loc with
    | true => { entry with perm := .disabled } :: disableLocalBorrows rest loc
    | false => entry :: disableLocalBorrows rest loc

/--
Definitional simplification equation for `disableLocalBorrows` on the empty
borrow table.
-/
@[simp]
theorem disableLocalBorrows_nil (loc : Local) :
    disableLocalBorrows .nil loc = .nil := rfl

/--
No borrow entry is protected when no function-entry protector is active, so
`hasProtectedLocalBorrow borrows .nil loc` is always `false`.
-/
@[simp]
theorem hasProtectedLocalBorrow_nil_protectors
    (borrows : List BorrowEntry)
    (loc : Local) :
    hasProtectedLocalBorrow borrows .nil loc = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hProt : isBorrowProtected .nil entry = false := by
      unfold isBorrowProtected
      cases entry.protector <;> rfl
    simp only [hasProtectedLocalBorrow, hProt, Bool.and_false]
    exact ih

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
    (h : hasProtectedWriteConflict borrows activeProtectors loc .none .nil = true) :
    hasProtectedLocalBorrow borrows activeProtectors loc = true := by
  induction borrows with
  | nil => exact h
  | cons entry rest ih =>
    unfold hasProtectedWriteConflict at h
    unfold hasProtectedLocalBorrow
    cases hT : Nat.beq entry.targetLocal loc with
    | false =>
      simp only [hT, Bool.false_and] at h ⊢
      exact ih h
    | true =>
      cases hP : isBorrowProtected activeProtectors entry with
      | false =>
        simp only [hT, hP, Bool.false_and, Bool.and_false] at h ⊢
        exact ih h
      | true => rfl

/--
`hasProtectedLocalBorrow borrows activeProtectors loc` is `false` when no entry
targets `loc`.
-/
theorem hasProtectedLocalBorrow_eq_false_of_forall_ne
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (loc : Local)
    (h : ∀ entry ∈ borrows, entry.targetLocal ≠ loc) :
    hasProtectedLocalBorrow borrows activeProtectors loc = false := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hNe : entry.targetLocal ≠ loc := h entry (List.Mem.head rest)
    have hBeq : Nat.beq entry.targetLocal loc = false := by
      cases hB : Nat.beq entry.targetLocal loc with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB))
    simp only [hasProtectedLocalBorrow, hBeq, Bool.false_and]
    exact ih (fun e he => h e (List.Mem.tail entry he))

/--
`disableLocalBorrows borrows loc` leaves `borrows` unchanged when no entry
targets `loc`.
-/
theorem disableLocalBorrows_eq_self_of_forall_ne
    (borrows : List BorrowEntry)
    (loc : Local)
    (h : ∀ entry ∈ borrows, entry.targetLocal ≠ loc) :
    disableLocalBorrows borrows loc = borrows := by
  induction borrows with
  | nil => rfl
  | cons entry rest ih =>
    have hNe : entry.targetLocal ≠ loc := h entry (List.Mem.head rest)
    have hBeq : Nat.beq entry.targetLocal loc = false := by
      cases hB : Nat.beq entry.targetLocal loc with
      | false => rfl
      | true => exact False.elim (hNe (Nat.eq_of_beq_eq_true hB))
    simp only [disableLocalBorrows, hBeq]
    rw [ih (fun e he => h e (List.Mem.tail entry he))]

/--
Every entry of `disableLocalBorrows borrows loc` that targets `loc` is
`.disabled`: no provenance tag minted from a previous allocation of `loc`
retains any access permission.
-/
theorem perm_eq_disabled_of_mem_disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local) :
    ∀ entry ∈ disableLocalBorrows borrows loc,
      entry.targetLocal = loc → entry.perm = .disabled := by
  induction borrows with
  | nil => intro entry hMem; nomatch hMem
  | cons hd rest ih =>
    intro entry hMem hT
    cases hB : Nat.beq hd.targetLocal loc with
    | true =>
      simp only [disableLocalBorrows, hB] at hMem
      cases hMem with
      | head => rfl
      | tail _ hMemRest => exact ih entry hMemRest hT
    | false =>
      simp only [disableLocalBorrows, hB] at hMem
      cases hMem with
      | head => exact absurd hT (Nat.ne_of_beq_eq_false hB)
      | tail _ hMemRest => exact ih entry hMemRest hT

/--
Resolving provenance tag `tag` in `disableLocalBorrows borrows loc` yields the
entry that `tag` resolves to in `borrows`, disabled exactly when it targets
`loc`; tags without a stack borrow entry remain unresolved.
-/
theorem lookupBorrow_disableLocalBorrows
    (borrows : List BorrowEntry)
    (loc : Local)
    (tag : Nat) :
    lookupBorrow (disableLocalBorrows borrows loc) tag =
      (match lookupBorrow borrows tag with
       | .some entry =>
         match Nat.beq entry.targetLocal loc with
         | true => .some { entry with perm := .disabled }
         | false => .some entry
       | .none => .none) := by
  induction borrows with
  | nil => rfl
  | cons hd rest ih =>
    cases hB : Nat.beq hd.targetLocal loc <;>
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
    (hTarget : entry.targetLocal = loc) :
    lookupBorrow (disableLocalBorrows borrows loc) tag =
      .some { entry with perm := .disabled } := by
  rw [lookupBorrow_disableLocalBorrows, hLookup]
  have hB : Nat.beq entry.targetLocal loc = true := by
    rw [hTarget]
    exact Nat.beq_refl loc
  simp only [hB]

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
    (hTarget : entry.targetLocal ≠ loc) :
    lookupBorrow (disableLocalBorrows borrows loc) tag = .some entry := by
  rw [lookupBorrow_disableLocalBorrows, hLookup]
  have hB : Nat.beq entry.targetLocal loc = false := by
    cases hB' : Nat.beq entry.targetLocal loc with
    | false => rfl
    | true => exact False.elim (hTarget (Nat.eq_of_beq_eq_true hB'))
  simp only [hB]

/--
A provenance tag without a stack borrow entry in `borrows` (e.g. a pointer to a
captured global allocation) remains unresolved after
`disableLocalBorrows borrows loc`.
-/
theorem lookupBorrow_disableLocalBorrows_of_eq_none
    (borrows : List BorrowEntry)
    (loc : Local)
    (tag : Nat)
    (hLookup : lookupBorrow borrows tag = .none) :
    lookupBorrow (disableLocalBorrows borrows loc) tag = .none := by
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
(`placeMentionOperandsInit`).

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
    with
    | .ok ptrOrFatVal locals' =>
      match extractDerefPtrVal? ptrOrFatVal with
      | .some ptrVal =>
        let placeTyOpt := placeTy localDecls layouts place
        let isMutRefPlace :=
          match placeTyOpt with
          | .some { kind := .ref .mut _, .. } => true
          | _ => false
        match lookupBorrow s.memory.borrows ptrVal.tag with
        | .some entry =>
          let permOk :=
            match entry.perm, isMutRefPlace with
            | .disabled, _ => false
            | .frozen, true => false
            | _, _ => true
          match permOk with
          | false => MirStepNode.fail .ub
          | true =>
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
        | .none =>
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
      | .none => MirStepNode.fail .ub
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
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })
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
              { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })
        | protHead :: protTail =>
          match
            hasProtectedLocalBorrow
              s.memory.borrows
              (protHead :: protTail)
              loc
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals'
                { s.memory with borrows := disableLocalBorrows s.memory.borrows loc })
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .deinit p =>
    match p.projection with
    | .nil =>
      match get? s.frame.locals p.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals p.local_ .uninit with
        | .some locals' => MirStepNode.step (advanceStmt s locals')
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | proj :: rest =>
      match get? s.frame.locals p.local_ with
      | .some (.init rootVal) =>
        match readProjectedValue s.frame.locals rootVal (proj :: rest) with
        | .ok _ => MirStepNode.step (advanceStmt s s.frame.locals)
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
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
    match p.projection with
    | .nil =>
      match get? s.frame.locals p.local_ with
      | .some (.init (.aggregate _ fields)) =>
        let newSlot := .init (.aggregate variantIdx fields)
        match set? s.frame.locals p.local_ newSlot with
        | .some locals' => MirStepNode.step (advanceStmt s locals')
        | .none => MirStepNode.fail .ub
      | .some (.init _) => MirStepNode.fail .ub
      | .some .uninit => MirStepNode.fail .ub
      | .some .dead => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | _ :: _ =>
      match
        evalOperand
          s.frame.locals
          (.copy p)
          s.memory.borrows
          s.memory.globals
          layouts
          s.memory.callerLocals
      with
      | .ok (.aggregate _ fields) locals₁ =>
        match
          writePlaceValue
            locals₁
            s.memory.borrows
            p
            (.aggregate variantIdx fields)
        with
        | .ok locals₂ => MirStepNode.step (advanceStmt s locals₂)
        | .ub => MirStepNode.fail .ub
        | .unsupported => MirStepNode.unsupported
      | .ok _ _ => MirStepNode.fail .ub
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
  | .assign dst rv =>
    match evalRvalue s.frame.locals rv s.memory localDecls layouts with
    | .ok val locals₁ mem₁ =>
      match dst.projection with
      | .nil =>
        match get? locals₁ dst.local_ with
        | .some .dead => MirStepNode.fail .ub
        | .some _ =>
          match set? locals₁ dst.local_ (.init val) with
          | .some locals₂ =>
            match mem₁.activeProtectors with
            | .nil =>
              let borrows' :=
                invalidateConflictingBorrows mem₁.borrows dst.local_ .none
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
              with
              | true => MirStepNode.fail .ub
              | false =>
                let borrows' :=
                  invalidateConflictingBorrows mem₁.borrows dst.local_ .none
                MirStepNode.step
                  (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
          | .none => MirStepNode.fail .ub
        | .none => MirStepNode.fail .ub
      | .deref :: restProj =>
        match
          evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors
        with
        | .ok locals₂ =>
          let borrows' :=
            invalidateDerefWriteBorrows locals₁ mem₁.borrows dst restProj
          MirStepNode.step
            (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
        | .ub =>
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
        | .unsupported => MirStepNode.unsupported
      | proj :: rest =>
        match get? locals₁ dst.local_ with
        | .some (.init rootVal) =>
          match writeProjectedValue locals₁ rootVal (proj :: rest) val with
          | .ok rootVal' =>
            match set? locals₁ dst.local_ (.init rootVal') with
            | .some locals₂ =>
              let resolvedLocalProj :=
                match resolveBorrowProjectionElems locals₁ (proj :: rest) with
                | .some rp => rp
                | .none => proj :: rest
              match mem₁.activeProtectors with
              | .nil =>
                let borrows' :=
                  invalidateConflictingBorrowsAtProj
                    mem₁.borrows
                    dst.local_
                    .none
                    resolvedLocalProj
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
                with
                | true => MirStepNode.fail .ub
                | false =>
                  let borrows' :=
                    invalidateConflictingBorrowsAtProj
                      mem₁.borrows
                      dst.local_
                      .none
                      resolvedLocalProj
                  MirStepNode.step
                    (advanceStmt s locals₂ { mem₁ with borrows := borrows' })
            | .none => MirStepNode.fail .ub
          | .ub => MirStepNode.fail .ub
          | .unsupported => MirStepNode.unsupported
        | .some .uninit => MirStepNode.fail .ub
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
   (`hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false`),
   `evalStmt` steps to `advanceStmt s localsDead { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }`,
   in which every borrow entry targeting `loc` is `.disabled`.
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
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false →
      evalStmt s ⟨.storageDead loc, span⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s localsDead
            { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }) ∧
      ∀ entry ∈ disableLocalBorrows s.memory.borrows loc,
        entry.targetLocal = loc → entry.perm = .disabled) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .dead = .some localsDead →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = true →
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
   (`hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false`),
   `evalStmt` steps to `advanceStmt s localsUninit { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }`,
   in which every borrow entry targeting `loc` is `.disabled`.
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
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = false →
      evalStmt s ⟨.storageLive loc, span⟩ localDecls layouts =
        MirStepNode.step
          (advanceStmt s localsUninit
            { s.memory with borrows := disableLocalBorrows s.memory.borrows loc }) ∧
      ∀ entry ∈ disableLocalBorrows s.memory.borrows loc,
        entry.targetLocal = loc → entry.perm = .disabled) ∧
    (get? s.frame.locals loc = .some slot →
      set? s.frame.locals loc .uninit = .some localsUninit →
      hasProtectedLocalBorrow s.memory.borrows s.memory.activeProtectors loc = true →
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

Pointer arithmetic (`evalPtrOffsetBinOp`) and raw address-of (`Rvalue.rawPtr`)
are deliberately not characterized: `Places.lean` currently faults on any
disabled tag before inspecting the offset or the access, which is stricter than
MiniRust and Miri for zero-byte offsets and raw address-of (both defined on
dangling pointers), and those rules belong to `ws-lm-div-places-ptr`.
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
    (hLookup : lookupBorrow borrows ptrVal.tag = .some entry)
    (hTarget : entry.targetLocal = loc)
    (hPtrSlot : get? localsAfter ptrLoc = .some (.init (.ptr ptrVal sz))) :
    let borrowsAfter := disableLocalBorrows borrows loc
    let derefPlace : Place := { local_ := ptrLoc, projection := .deref :: restProj }
    let sAfter : MachineState :=
      { s with
        frame := { s.frame with locals := localsAfter }
        memory := { s.memory with borrows := borrowsAfter } }
    lookupBorrow borrowsAfter ptrVal.tag = .some { entry with perm := .disabled } ∧
    evalPlaceRead localsAfter derefPlace borrowsAfter globals layouts callerLocals localDecls = .ub ∧
    evalOperand localsAfter (.copy derefPlace) borrowsAfter globals layouts callerLocals = .ub ∧
    evalOperand localsAfter (.move derefPlace) borrowsAfter globals layouts callerLocals = .ub ∧
    writePlaceValue localsAfter borrowsAfter derefPlace writeVal = .ub ∧
    evalPlaceWrite localsAfter borrowsAfter derefPlace writeVal activeProtectors = .ub ∧
    evalRvalue localsAfter (.ref borrowKind derefPlace)
      { mem with borrows := borrowsAfter } localDecls layouts = .ub ∧
    evalStmt sAfter ⟨.retag retagKind ⟨ptrLoc, .nil⟩, span⟩ localDecls layouts =
      MirStepNode.fail .ub ∧
    evalStmt sAfter ⟨.setDiscriminant derefPlace n, span⟩ localDecls layouts =
      MirStepNode.fail .ub ∧
    evalCopyNonOverlappingWithCount sAfter srcOp dstOp localDecls layouts
      (.ptr ptrVal sz) otherVal (n + 1) localsAfter = MirStepNode.fail .ub ∧
    evalCopyNonOverlappingWithCount sAfter srcOp dstOp localDecls layouts
      otherVal (.ptr ptrVal sz) (n + 1) localsAfter = MirStepNode.fail .ub := by
  dsimp only
  have hDis : lookupBorrow (disableLocalBorrows borrows loc) ptrVal.tag =
      .some { entry with perm := .disabled } :=
    lookupBorrow_disableLocalBorrows_of_targetLocal_eq borrows loc ptrVal.tag entry hLookup hTarget
  have hWrite :
      writePlaceValue localsAfter (disableLocalBorrows borrows loc)
        { local_ := ptrLoc, projection := .deref :: restProj } writeVal = .ub := by
    simp [writePlaceValue, hPtrSlot, hDis]
  refine ⟨hDis, ?_, ?_, ?_, hWrite, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [evalPlaceRead, hPtrSlot, hDis]
  · simp [evalOperand, hPtrSlot, hDis]
  · simp [evalOperand, hPtrSlot, hDis]
  · unfold evalPlaceWrite
    cases activeProtectors with
    | nil => exact hWrite
    | cons p ps =>
      dsimp only
      split
      · rfl
      · exact hWrite
  · cases borrowKind <;> simp [evalRvalue, hPtrSlot, hDis]
  · simp [evalStmt, evalOperand, readProjectedValue, hPtrSlot, hDis]
  · simp [evalStmt, evalOperand, hPtrSlot, hDis]
  · unfold evalCopyNonOverlappingWithCount
    simp only [Nat.beq]
    cases otherVal with
    | ptr dstPtr dstSz =>
      dsimp only
      rw [hDis]
      cases hDst : lookupBorrow (disableLocalBorrows borrows loc) dstPtr.tag <;> rfl
    | _ => rfl
  · unfold evalCopyNonOverlappingWithCount
    simp only [Nat.beq]
    cases otherVal with
    | ptr srcPtr srcSz =>
      dsimp only
      rw [hDis]
      cases hSrc : lookupBorrow (disableLocalBorrows borrows loc) srcPtr.tag with
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

end Trusted.Rustc.V2026_08_01.MirSemantics
