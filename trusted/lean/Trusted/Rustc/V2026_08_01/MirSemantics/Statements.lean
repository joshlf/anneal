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
Execute a single MIR `Statement` from state `s` using `localDecls` and `layouts`
for type- and layout-aware rvalue and intrinsic evaluation.

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
    | .some _ => MirStepNode.step (advanceStmt s s.frame.locals)
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
      | .some locals' => MirStepNode.step (advanceStmt s locals')
      | .none => MirStepNode.fail .ub
    | .none => MirStepNode.fail .ub
  | .storageDead loc =>
    match get? s.frame.locals loc with
    | .some _ =>
      match set? s.frame.locals loc .dead with
      | .some locals' => MirStepNode.step (advanceStmt s locals')
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

end Trusted.Rustc.V2026_08_01.MirSemantics
