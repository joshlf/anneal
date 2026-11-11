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
            localDecls
            layouts
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
Materialize default `.aggregate 0 .nil` shells along a chain of intermediate
aggregate `.field` projections inside `val` whenever the current slot at
`fieldIdx` is either absent (`fieldIdx ≥ length fields`) or `.unit` padding
produced by an earlier `setOrExtendFields` on a higher-index sibling field.

1. When `fieldTy.kind` is a struct/union (`.adt _ _`) or tuple (`.tuple _`) and
   the remaining projection path continues with `.field _ _`, materializing an
   inner `.aggregate 0 ...` shell prevents `writeProjectedValue` from collapsing
   `.field 0` onto `.unit` (losing the inner aggregate wrapper) or faulting with
   `.ub` on `.field (k + 1)` against `.unit`.
2. Fixed-length array fields (`.array _ _`) are never materialized, so an
   element write through a never-written array field (`_u.arr[i] = val`) still
   faults with `.ub`. An array shell would have to fill every unwritten element
   with a `.unit` placeholder, and a later read of such an element
   (`copy _u.arr[j]`) would return that placeholder instead of faulting on the
   uninitialized element as MiniRust and Miri do.

`evalStmt` applies this both to the default shell of an uninitialized
destination (`uninitFieldWriteShell?`) and to the current value of an
initialized destination before a projected write. Transparent metadata
projections (`.opaqueCast` and `.unwrapUnsafeBinder`) are traversed without
altering the value, and `stripTransparentProjections` is used when checking
whether the remaining projection chain continues with a `.field` projection.
Every slot it visits that is already present and not `.unit` is kept as is, so
on a root whose intermediate field slots along the chain are all populated
(`fieldShellChainPopulated`) the result is the root itself and the write
coincides with `writeProjectedValue` on the original root.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L1135-L1165>

> "- [`Field`](ProjectionElem::Field): `Field` projections take their parent
>   place and create a place referring to one of the fields of the type."
-/
def ensureNestedFieldShells (val : Value) (projs : List ProjectionElem) : Value :=
  match projs with
  | .opaqueCast _ :: nextProj :: rest =>
    ensureNestedFieldShells val (nextProj :: rest)
  | .unwrapUnsafeBinder _ :: nextProj :: rest =>
    ensureNestedFieldShells val (nextProj :: rest)
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
        match get? fields fieldIdx with
        | .none =>
          let childShell :=
            ensureNestedFieldShells (.aggregate 0 .nil) (nextProj :: rest)
          .aggregate variantIdx (setOrExtendFields fields fieldIdx childShell)
        | .some .unit =>
          let childShell :=
            ensureNestedFieldShells (.aggregate 0 .nil) (nextProj :: rest)
          .aggregate variantIdx (setOrExtendFields fields fieldIdx childShell)
        | .some childVal =>
          let childVal' :=
            ensureNestedFieldShells childVal (nextProj :: rest)
          match set? fields fieldIdx childVal' with
          | .some fields' => .aggregate variantIdx fields'
          | .none => .aggregate variantIdx fields
      | false => .aggregate variantIdx fields
    | _ => val
  | _ => val

/--
Whether every intermediate struct, union, or tuple field slot that
`ensureNestedFieldShells val projs` inspects along `projs` is already present
and not `.unit` padding.

When `fieldShellChainPopulated val projs = true`, `ensureNestedFieldShells val projs`
returns `val` unchanged (`ensureNestedFieldShells_eq_self_of_populated`).

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
      | .some childVal => fieldShellChainPopulated childVal (nextProj :: rest)
    | false => true
  | _, _ => true

/--
Default root value for a projected assignment `dst = rv` into a live but
uninitialized destination local `loc` (`.uninit`) whose first projection
`proj` is a field projection (`.field _ _`) and whose declared type
(`placeTy localDecls layouts { local_ := loc, projection := .nil }`) is a
struct, union, or tuple (`.adt _ _` or `.tuple _`).

The shell starts as `.aggregate 0 .nil` and uses `ensureNestedFieldShells` along
`.field fieldIdx fieldTy :: rest` so both single-level field writes (`_1.f = v`)
and nested aggregate field writes (`_1.a.b = v` or `_1.0.1 = v`) materialize
`.aggregate 0 ...` shells at every intermediate `.adt` or `.tuple` field.
A field with a higher index that was never written still faults with `.ub` when
read, while a lower-index field that was never written reads as the `.unit`
padding that `setOrExtendFields` also uses for union fields. Every other
projection head (`.index`, `.constantIndex`, `.subslice`, `.downcast`,
`.opaqueCast`, `.unwrapUnsafeBinder`; `.deref` writes never reach this helper)
and every non-aggregate declared type yields `.none`, preserving the fault on
projected writes into uninitialized locals.

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
    | .some { kind := .adt _ _, .. } =>
      .some
        (ensureNestedFieldShells
          (.aggregate 0 .nil)
          (.field fieldIdx fieldTy :: rest))
    | .some { kind := .tuple _, .. } =>
      .some
        (ensureNestedFieldShells
          (.aggregate 0 .nil)
          (.field fieldIdx fieldTy :: rest))
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
          let child : BorrowEntry := {
            tag := tag
            targetLocal := parentEntry.targetLocal
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
          let child : BorrowEntry := {
            tag := tag
            targetLocal := parentEntry.targetLocal
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
    (restProj : List ProjectionElem) :
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
            resolveDerefWriteFullProj locals₁ locals₁ ptrOrFatVal entry restProj
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
            | _ =>
              hasProtectedWriteConflict
                borrows
                prots
                entry.targetLocal
                (.some ptrVal.tag)
                effProj
                entry.rangeOffset
                entry.rangeLen
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
    (restProj : List ProjectionElem) :
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
            | false =>
              invalidateConflictingBorrowsAtProj
                b
                entry.targetLocal
                (.some ptrVal.tag)
                .nil
                entry.rangeOffset
                entry.rangeLen
          | pHead :: pTail =>
            invalidateConflictingBorrowsAtProj
              b
              entry.targetLocal
              (.some ptrVal.tag)
              (pHead :: pTail)
              entry.rangeOffset
              entry.rangeLen
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
        | .none => allBorrows
      | .none => allBorrows
    | _ => allBorrows

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
uninitialized local writes into the default shell from `uninitFieldWriteShell?`
when the projection starts with a field of a struct, union, or tuple local, and
otherwise faults with `.ub`. A projected assignment into an initialized local
first materializes missing or `.unit`-padded intermediate struct, union, and
tuple field shells along the written field chain (`ensureNestedFieldShells`),
which leaves roots whose intermediate field slots are all populated unchanged.

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
        localDecls
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
        localDecls
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
          localDecls
      with
      | .ok (.aggregate _ fields) locals₁ =>
        match
          writePlaceValue
            locals₁
            s.memory.borrows
            p
            (.aggregate variantIdx fields)
            localDecls
            layouts
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
          evalPlaceWrite
            locals₁
            mem₁.borrows
            dst
            val
            mem₁.activeProtectors
            localDecls
            layouts
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
                restProj)
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
        | .unsupported => MirStepNode.unsupported
      | proj :: rest =>
        match get? locals₁ dst.local_ with
        | .some (.init rootVal) =>
          match
            writeProjectedForLocal
              locals₁
              localDecls
              layouts
              dst.local_
              (ensureNestedFieldShells rootVal (proj :: rest))
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
  have hDis : lookupBorrow (disableLocalBorrows borrows loc) ptrVal.tag =
      .some { entry with perm := .disabled } :=
    lookupBorrow_disableLocalBorrows_of_targetLocal_eq borrows loc ptrVal.tag entry hLookup hTarget
  have hWrite :
      writePlaceValue localsAfter (disableLocalBorrows borrows loc)
        { local_ := ptrLoc, projection := .deref :: restProj } writeVal localDecls layouts = .ub := by
    simp [writePlaceValue, hPtrSlot, hDis]
  have hOpCopy :
      evalOperand localsAfter (.copy { local_ := ptrLoc, projection := .deref :: restProj })
        (disableLocalBorrows borrows loc) globals layouts callerLocals localDecls = .ub := by
    cases localDecls <;> simp [evalOperand, hPtrSlot, hDis]
  have hOpMove :
      evalOperand localsAfter (.move { local_ := ptrLoc, projection := .deref :: restProj })
        (disableLocalBorrows borrows loc) globals layouts callerLocals localDecls = .ub := by
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
  · cases localDecls <;> simp [evalStmt, evalOperand, hPtrSlot, hDis]
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

/--
`ensureNestedFieldShells` on a single-element projection list `[proj]` is the
identity on `val`.
-/
@[simp]
theorem ensureNestedFieldShells_singleton
    (val : Value)
    (proj : ProjectionElem) :
    ensureNestedFieldShells val [proj] = val := by
  cases proj <;> rfl

/--
`uninitFieldWriteShell?` returns the empty aggregate shell for a single-level
field projection on a local whose declared type is a struct or union.
-/
theorem uninitFieldWriteShell?_field_adt
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (defPath : DefPath)
    (args : List RigidTy)
    (layoutIdx : Nat)
    (hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } =
      .some { kind := .adt defPath args, layoutIdx := layoutIdx }) :
    uninitFieldWriteShell? localDecls layouts loc (.field fieldIdx fieldTy) =
      .some (.aggregate 0 .nil) := by
  simp [uninitFieldWriteShell?, hTy]

/--
`uninitFieldWriteShell?` returns the empty aggregate shell for a single-level
field projection on a tuple-typed local.
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
      .some { kind := .tuple fields, layoutIdx := layoutIdx }) :
    uninitFieldWriteShell? localDecls layouts loc (.field fieldIdx fieldTy) =
      .some (.aggregate 0 .nil) := by
  simp [uninitFieldWriteShell?, hTy]

/--
`uninitFieldWriteShell?` yields `.none` for every projection head other than a
field projection, regardless of any trailing projections `rest`.
-/
theorem uninitFieldWriteShell?_eq_none_of_not_field
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem := .nil)
    (hNotField : ∀ (fieldIdx : FieldIdx) (fieldTy : Ty), proj ≠ .field fieldIdx fieldTy) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none := by
  cases proj with
  | field fieldIdx fieldTy => exact False.elim (hNotField fieldIdx fieldTy rfl)
  | _ => rfl

/--
`uninitFieldWriteShell?` yields `.none` whenever the destination local's
declared root type is neither a struct/union (`.adt _ _`) nor a tuple
(`.tuple _`).
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
        .some { kind := .tuple fields, layoutIdx := layoutIdx }) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none := by
  cases proj with
  | field fieldIdx fieldTy =>
    unfold uninitFieldWriteShell?
    cases hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } with
    | none => rfl
    | some ty =>
      rcases ty with ⟨kind, layoutIdx⟩
      cases kind with
      | adt defPath args => exact False.elim (hNotAdt defPath args layoutIdx hTy)
      | tuple fields => exact False.elim (hNotTuple fields layoutIdx hTy)
      | _ => rfl
  | _ => rfl

/--
Whether `uninitFieldWriteShell?` returns `.none` depends only on the root local
and the head projection `proj`, not on the trailing projection path `rest`.
-/
@[simp]
theorem uninitFieldWriteShell?_eq_none_iff
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none ↔
      uninitFieldWriteShell? localDecls layouts loc proj .nil = .none := by
  cases proj with
  | field fieldIdx fieldTy =>
    unfold uninitFieldWriteShell?
    cases hTy : placeTy localDecls layouts { local_ := loc, projection := .nil } with
    | none => simp
    | some ty =>
      rcases ty with ⟨kind, layoutIdx⟩
      cases kind <;> simp
  | _ => simp [uninitFieldWriteShell?]

/--
Universal characterization (`D13b`) of a projected assignment
`dst = rv` with `dst.projection = .field fieldIdx fieldTy :: rest` into a live
but uninitialized local `dstLoc` with a struct, union, or tuple shell
(`uninitFieldWriteShell? localDecls layouts dstLoc (.field fieldIdx fieldTy) rest =
.some shell`):
1. When the projected write into the shell succeeds
   (`writeProjectedValue locals₁ shell (.field fieldIdx fieldTy :: rest) val =
   .ok rootVal'`) and no active protector conflicts with the write, `evalStmt`
   initializes `dstLoc` to `rootVal'`, invalidates the borrows conflicting with
   the written projection, and steps.
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
          (.field fieldIdx fieldTy :: rest)) = false) :
    evalStmt s ⟨.assign ⟨dstLoc, .field fieldIdx fieldTy :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.step
        (advanceStmt s locals₂
          { mem₁ with
            borrows :=
              invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                  (.field fieldIdx fieldTy :: rest)) }) := by
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
                      (.field fieldIdx fieldTy :: rest)) })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
              (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                (.field fieldIdx fieldTy :: rest))
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals₂
                { mem₁ with
                  borrows :=
                    invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                      (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                        (.field fieldIdx fieldTy :: rest)) }) := by
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
          (.field fieldIdx fieldTy :: rest)) = true) :
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
`D13b` union / struct field initialization (`evalStmt_assign_uninit_union_field_ok`):
writing `val` into field `fieldIdx` of a live but uninitialized local `dstLoc`
whose declared type is a struct or union (`.adt defPath args`) without a
`FieldsShape.union` layout override (`placeTouchesUnion = false`), with no active
protector, initializes `dstLoc` to the aggregate holding `val` at `fieldIdx`
(`.aggregate 0 (setOrExtendFields .nil fieldIdx val)`) and steps.
-/
theorem evalStmt_assign_uninit_union_field_ok
    (s : MachineState)
    (dstLoc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (defPath : DefPath)
    (args : List RigidTy)
    (layoutIdx : Nat)
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (locals₂ : List LocalSlot)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hTy : placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
      .some { kind := .adt defPath args, layoutIdx := layoutIdx })
    (hSet : set? locals₁ dstLoc (.init (.aggregate 0 (setOrExtendFields .nil fieldIdx val))) =
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
                 | .none => .field fieldIdx fieldTy :: .nil) }) := by
  have hShell :=
    uninitFieldWriteShell?_field_adt localDecls layouts dstLoc fieldIdx fieldTy
      defPath args layoutIdx hTy
  have hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc (.aggregate 0 .nil)
        (.field fieldIdx fieldTy :: .nil) val =
        .ok (.aggregate 0 (setOrExtendFields .nil fieldIdx val)) := by
    unfold writeProjectedForLocal
    rw [hNoUnion]
    cases fieldIdx <;> rfl
  have hStep :=
    evalStmt_assign_uninit_aggregate_field_step s dstLoc fieldIdx fieldTy .nil rv span
      localDecls layouts val locals₁ mem₁ (.aggregate 0 .nil)
      (.aggregate 0 (setOrExtendFields .nil fieldIdx val)) locals₂ hRv hUninit hShell hWrite hSet
      (fun protHead protTail hAP => by rw [hProt] at hAP; nomatch hAP)
  rw [resolveBorrowWriteLocalProj_of_not_union localDecls layouts locals₁ dstLoc
    (.field fieldIdx fieldTy :: .nil) hNoUnion] at hStep
  exact hStep

/--
`D13b` tuple field initialization (`evalStmt_assign_uninit_tuple_field_ok`):
writing `val` into field `fieldIdx` of a live but uninitialized local `dstLoc`
whose declared type is a tuple (`.tuple fields`), with no active protector,
initializes `dstLoc` to `.aggregate 0 (setOrExtendFields .nil fieldIdx val)`
and steps.
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
    (hSet : set? locals₁ dstLoc (.init (.aggregate 0 (setOrExtendFields .nil fieldIdx val))) =
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
                 | .none => .field fieldIdx fieldTy :: .nil) }) := by
  have hShell :=
    uninitFieldWriteShell?_field_tuple localDecls layouts dstLoc fieldIdx fieldTy
      fields layoutIdx hTy
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
          have hResKind :
              (resolveTyWithLocalDecls (d :: ds) { pointerBits := pB, isLittleEndian := lE, entries := e :: es }
                { kind := .tuple fields, layoutIdx := layoutIdx }).kind = .tuple fields := by
            unfold resolveTyWithLocalDecls
            repeat' (first | rfl | split)
          dsimp only
          rw [hResKind]
  have hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc (.aggregate 0 .nil)
        (.field fieldIdx fieldTy :: .nil) val =
        .ok (.aggregate 0 (setOrExtendFields .nil fieldIdx val)) := by
    unfold writeProjectedForLocal
    rw [hNoUnion]
    cases fieldIdx <;> rfl
  have hStep :=
    evalStmt_assign_uninit_aggregate_field_step s dstLoc fieldIdx fieldTy .nil rv span
      localDecls layouts val locals₁ mem₁ (.aggregate 0 .nil)
      (.aggregate 0 (setOrExtendFields .nil fieldIdx val)) locals₂ hRv hUninit hShell hWrite hSet
      (fun protHead protTail hAP => by rw [hProt] at hAP; nomatch hAP)
  rw [resolveBorrowWriteLocalProj_of_not_union localDecls layouts locals₁ dstLoc
    (.field fieldIdx fieldTy :: .nil) hNoUnion] at hStep
  exact hStep

/--
`D13b` nested aggregate field initialization (`evalStmt_assign_uninit_nested_field_ok`):
writing `val` into a 2-level nested field path
`[.field outerIdx outerTy, .field innerIdx innerTy]` on a live but uninitialized
struct, union, or tuple local `dstLoc` whose outer field `outerTy` is itself a
struct/union (`.adt _ _`) or tuple (`.tuple _`), with no active protector,
materializes both the outer and inner `.aggregate 0 ...` shells, stores `val`
at `innerIdx` inside `outerIdx`, and steps.
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
    (val : Value)
    (locals₁ : List LocalSlot)
    (mem₁ : Memory)
    (locals₂ : List LocalSlot)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hUninit : get? locals₁ dstLoc = .some .uninit)
    (hRootAgg :
      (∃ defPath args layoutIdx,
        placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
          .some { kind := .adt defPath args, layoutIdx := layoutIdx }) ∨
      (∃ tupleFields layoutIdx,
        placeTy localDecls layouts { local_ := dstLoc, projection := .nil } =
          .some { kind := .tuple tupleFields, layoutIdx := layoutIdx }))
    (hOuterAgg :
      (∃ innerDefPath innerArgs, outerTy.kind = .adt innerDefPath innerArgs) ∨
      (∃ innerFields, outerTy.kind = .tuple innerFields))
    (hSet :
      set? locals₁ dstLoc
        (.init
          (.aggregate 0
            (setOrExtendFields .nil outerIdx
              (.aggregate 0 (setOrExtendFields .nil innerIdx val))))) =
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
                 | .none => projs) }) := by
  dsimp only
  let shell : Value :=
    .aggregate 0 (setOrExtendFields .nil outerIdx (.aggregate 0 .nil))
  let rootVal' : Value :=
    .aggregate 0
      (setOrExtendFields .nil outerIdx
        (.aggregate 0 (setOrExtendFields .nil innerIdx val)))
  have hGetNil : ∀ k : Nat, get? (.nil : List Value) k = .none := by
    intro k; cases k <;> rfl
  have hGetExt : ∀ (k : Nat) (v : Value),
      get? (setOrExtendFields .nil k v) k = .some v := by
    intro k v
    induction k with
    | zero => rfl
    | succ n ih => exact ih
  have hLenExt : ∀ (k : Nat) (v : Value),
      (setOrExtendFields .nil k v).length = k + 1 := by
    intro k v
    induction k with
    | zero => rfl
    | succ n ih =>
      change (Value.unit :: setOrExtendFields .nil n v).length = n + 1 + 1
      simp [ih]
  have hListSetExt : ∀ (k : Nat) (v w : Value),
      (setOrExtendFields .nil k v).set k w = setOrExtendFields .nil k w := by
    intro k v w
    induction k with
    | zero => rfl
    | succ n ih =>
      change (Value.unit :: setOrExtendFields .nil n v).set (n + 1) w =
        Value.unit :: setOrExtendFields .nil n w
      simp [ih]
  have hSetExt : ∀ (k : Nat) (v w : Value),
      set? (setOrExtendFields .nil k v) k w = .some (setOrExtendFields .nil k w) := by
    intro k v w
    change (if k < (setOrExtendFields .nil k v).length then
        some ((setOrExtendFields .nil k v).set k w) else none) =
      .some (setOrExtendFields .nil k w)
    simp [hLenExt k v, hListSetExt k v w]
  have hShell :
      uninitFieldWriteShell? localDecls layouts dstLoc (.field outerIdx outerTy)
        [.field innerIdx innerTy] = .some shell := by
    rcases outerTy with ⟨outerKind, outerLayoutIdx⟩
    rcases hRootAgg with ⟨defPath, args, layoutIdx, hTy⟩ | ⟨tupleFields, layoutIdx, hTy⟩ <;>
      rcases hOuterAgg with ⟨innerDefPath, innerArgs, hKind⟩ | ⟨innerFields, hKind⟩ <;>
      dsimp only at hKind <;> subst hKind <;>
      simp [uninitFieldWriteShell?, ensureNestedFieldShells, stripTransparentProjections,
        hTy, hGetNil outerIdx, shell]
  have hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc shell
        [.field outerIdx outerTy, .field innerIdx innerTy] val = .ok rootVal' := by
    unfold writeProjectedForLocal
    rw [hNoUnion]
    dsimp only [shell, rootVal', writeProjectedValue]
    rw [hGetExt outerIdx (.aggregate 0 .nil)]
    dsimp only [writeProjectedValue]
    rw [hGetNil innerIdx]
    dsimp only [writeProjectedValue]
    rw [hSetExt outerIdx (.aggregate 0 .nil)
      (.aggregate 0 (setOrExtendFields .nil innerIdx val))]
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
assignment into a live but uninitialized local still faults with
`MirStepNode.fail .ub` whenever no default shell applies
(`uninitFieldWriteShell? localDecls layouts dstLoc proj = .none`), i.e. when the
projection does not start with a field projection (`.index`, `.constantIndex`,
`.subslice`, `.downcast`, ...) or the local's declared type is not a struct,
union, or tuple.
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
    (hNoShell : uninitFieldWriteShell? localDecls layouts dstLoc proj = .none) :
    evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.fail .ub := by
  have hNoShellRest :
      uninitFieldWriteShell? localDecls layouts dstLoc proj rest = .none :=
    (uninitFieldWriteShell?_eq_none_iff localDecls layouts dstLoc proj rest).mpr hNoShell
  cases proj with
  | deref => exact False.elim (hNotDeref rfl)
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
Non-regression for initialized roots (`D13b`): `ensureNestedFieldShells` is the
identity on every value whose field chain along `projs` is populated
(`fieldShellChainPopulated val projs = true`).
-/
theorem ensureNestedFieldShells_eq_self_of_populated :
    ∀ (projs : List ProjectionElem) (val : Value),
      fieldShellChainPopulated val projs = true →
      ensureNestedFieldShells val projs = val := by
  intro projs
  induction projs with
  | nil => intro val _; cases val <;> rfl
  | cons p tl ih =>
    intro val hPop
    cases tl with
    | nil => cases p <;> cases val <;> rfl
    | cons nextProj rest =>
      cases p with
      | opaqueCast ty =>
        cases val <;> exact ih _ hPop
      | unwrapUnsafeBinder ty =>
        cases val <;> exact ih _ hPop
      | field fieldIdx fieldTy =>
        cases val with
        | aggregate variantIdx fields =>
          unfold fieldShellChainPopulated at hPop
          unfold ensureNestedFieldShells
          have key : ∀ (childVal : Value),
              get? fields fieldIdx = .some childVal →
              fieldShellChainPopulated childVal (nextProj :: rest) = true →
              (match set? fields fieldIdx (ensureNestedFieldShells childVal (nextProj :: rest)) with
                | .some fields' => Value.aggregate variantIdx fields'
                | .none => Value.aggregate variantIdx fields) = .aggregate variantIdx fields := by
            intro childVal hGet hPop'
            rw [ih childVal hPop', set?_self_of_get? fields fieldIdx _ hGet]
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
              | scalar sc => exact key _ hGet hPop
              | ptr pv sz => exact key _ hGet hPop
              | aggregate v fs => exact key _ hGet hPop
          · rw [hFalse]
        | _ => rfl
      | _ => cases val <;> rfl

/--
Non-regression for initialized roots (`D13b`): on a root whose field chain along
the written projection is populated (`fieldShellChainPopulated rootVal projs = true`),
the projected write after `ensureNestedFieldShells` coincides with
`writeProjectedValue` on the original root.
-/
theorem writeProjectedValue_ensureNestedFieldShells_of_populated
    (locals : List LocalSlot)
    (rootVal : Value)
    (projs : List ProjectionElem)
    (val : Value)
    (hPop : fieldShellChainPopulated rootVal projs = true) :
    writeProjectedValue locals (ensureNestedFieldShells rootVal projs) projs val =
      writeProjectedValue locals rootVal projs val := by
  rw [ensureNestedFieldShells_eq_self_of_populated projs rootVal hPop]

theorem writeProjectedForLocal_ensureNestedFieldShells_of_populated
    (locals : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (rootVal : Value)
    (projs : List ProjectionElem)
    (val : Value)
    (hPop : fieldShellChainPopulated rootVal projs = true) :
    writeProjectedForLocal locals localDecls layouts loc
        (ensureNestedFieldShells rootVal projs) projs val =
      writeProjectedForLocal locals localDecls layouts loc rootVal projs val := by
  rw [ensureNestedFieldShells_eq_self_of_populated projs rootVal hPop]

/--
`evalStmt`-level non-regression for initialized roots (`D13b`): when `dstLoc`
holds `.init rootVal` whose intermediate field slots along `proj :: rest` are
populated (`fieldShellChainPopulated rootVal (proj :: rest) = true`), a
non-dereference projected assignment `dst = rv` evaluates
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
          (proj :: rest)) = false) :
    evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.step
        (advanceStmt s locals₂
          { mem₁ with
            borrows :=
              invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                  (proj :: rest)) }) := by
  have hWriteShell :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc
        (ensureNestedFieldShells rootVal (proj :: rest))
        (proj :: rest) val = .ok rootVal' := by
    rw [writeProjectedForLocal_ensureNestedFieldShells_of_populated
      locals₁ localDecls layouts dstLoc rootVal (proj :: rest) val hPop]
    exact hWrite
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
                      (proj :: rest)) })
        | protHead :: protTail =>
          match
            hasProtectedWriteConflict mem₁.borrows (protHead :: protTail) dstLoc .none
              (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                (proj :: rest))
          with
          | true => MirStepNode.fail .ub
          | false =>
            MirStepNode.step
              (advanceStmt s locals₂
                { mem₁ with
                  borrows :=
                    invalidateConflictingBorrowsAtProj mem₁.borrows dstLoc .none
                      (resolveBorrowWriteLocalProj localDecls layouts locals₁ dstLoc
                        (proj :: rest)) }) := by
    cases proj with
    | deref => exact False.elim (hNotDeref rfl)
    | _ =>
      unfold evalStmt
      dsimp only
      rw [hRv]
      dsimp only
      rw [hInit]
      dsimp only
      rw [hWriteShell]
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
`D13b` nested field write into an unpopulated slot of an already-initialized
aggregate (`evalStmt_assign_init_unpopulated_nested_field_ok`): when `dstLoc`
holds `.init (.aggregate variantIdx fields)` (for instance, after an earlier
field write initialized a sibling field of `dstLoc` or after `SetDiscriminant`
initialized an enum variant), `outerTy` is a struct/union (`.adt _ _`) or tuple
(`.tuple _`), and the slot at `outerIdx` is still unpopulated
(`get? fields outerIdx = .none ∨ get? fields outerIdx = .some .unit`), writing
`val` into `[.field outerIdx outerTy, .field innerIdx innerTy]` materializes the
inner `.aggregate 0 ...` shell at `outerIdx`, stores `val` at `innerIdx`, and
steps.
-/
theorem evalStmt_assign_init_unpopulated_nested_field_ok
    (s : MachineState)
    (dstLoc : Local)
    (variantIdx : VariantIdx)
    (fields : List Value)
    (outerIdx innerIdx : FieldIdx)
    (outerTy innerTy : Ty)
    (rv : Rvalue)
    (span : String)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (val : Value)
    (locals₁ locals₂ : List LocalSlot)
    (mem₁ : Memory)
    (hRv : evalRvalue s.frame.locals rv s.memory localDecls layouts = .ok val locals₁ mem₁)
    (hInit : get? locals₁ dstLoc = .some (.init (.aggregate variantIdx fields)))
    (hOuterAgg :
      (∃ innerDefPath innerArgs, outerTy.kind = .adt innerDefPath innerArgs) ∨
      (∃ innerFields, outerTy.kind = .tuple innerFields))
    (hSlot : get? fields outerIdx = .none ∨ get? fields outerIdx = .some .unit)
    (hSet :
      set? locals₁ dstLoc
        (.init
          (.aggregate variantIdx
            (setOrExtendFields fields outerIdx
              (.aggregate 0 (setOrExtendFields .nil innerIdx val))))) =
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
                 | .none => projs) }) := by
  dsimp only
  have hGetNil : ∀ k : Nat, get? (.nil : List Value) k = .none := by
    intro k; cases k <;> rfl
  have hGetExt : ∀ (fs : List Value) (k : Nat) (v : Value),
      get? (setOrExtendFields fs k v) k = .some v := by
    intro fs
    induction fs with
    | nil =>
      intro k v
      induction k with
      | zero => rfl
      | succ n ih => exact ih
    | cons hd tl ihFs =>
      intro k v
      cases k with
      | zero => rfl
      | succ n => exact ihFs n v
  have hLenLtExt : ∀ (fs : List Value) (k : Nat) (v : Value),
      k < (setOrExtendFields fs k v).length := by
    intro fs
    induction fs with
    | nil =>
      intro k v
      induction k with
      | zero => exact Nat.zero_lt_succ 0
      | succ n ih =>
        change n + 1 < (Value.unit :: setOrExtendFields .nil n v).length
        simp only [List.length_cons]
        exact Nat.succ_lt_succ ih
    | cons hd tl ihFs =>
      intro k v
      cases k with
      | zero => exact Nat.zero_lt_succ tl.length
      | succ n =>
        change n + 1 < (hd :: setOrExtendFields tl n v).length
        simp only [List.length_cons]
        exact Nat.succ_lt_succ (ihFs n v)
  have hListSetExt : ∀ (fs : List Value) (k : Nat) (v w : Value),
      (setOrExtendFields fs k v).set k w = setOrExtendFields fs k w := by
    intro fs
    induction fs with
    | nil =>
      intro k v w
      induction k with
      | zero => rfl
      | succ n ih =>
        change (Value.unit :: setOrExtendFields .nil n v).set (n + 1) w =
          Value.unit :: setOrExtendFields .nil n w
        simp [ih]
    | cons hd tl ihFs =>
      intro k v w
      cases k with
      | zero => rfl
      | succ n =>
        change (hd :: setOrExtendFields tl n v).set (n + 1) w =
          hd :: setOrExtendFields tl n w
        simp [ihFs n v w]
  have hSetExt : ∀ (fs : List Value) (k : Nat) (v w : Value),
      set? (setOrExtendFields fs k v) k w = .some (setOrExtendFields fs k w) := by
    intro fs k v w
    change (if k < (setOrExtendFields fs k v).length then
        some ((setOrExtendFields fs k v).set k w) else none) =
      .some (setOrExtendFields fs k w)
    simp [hLenLtExt fs k v, hListSetExt fs k v w]
  have hEns :
      ensureNestedFieldShells (.aggregate variantIdx fields)
        [.field outerIdx outerTy, .field innerIdx innerTy] =
        .aggregate variantIdx (setOrExtendFields fields outerIdx (.aggregate 0 .nil)) := by
    rcases outerTy with ⟨outerKind, outerLayoutIdx⟩
    rcases hOuterAgg with ⟨innerDefPath, innerArgs, hKind⟩ | ⟨innerFields, hKind⟩ <;>
      dsimp only at hKind <;> subst hKind <;>
      (rcases hSlot with hS | hS <;>
        simp [ensureNestedFieldShells, stripTransparentProjections, hS])
  have hWrite :
      writeProjectedForLocal locals₁ localDecls layouts dstLoc
        (.aggregate variantIdx (setOrExtendFields fields outerIdx (.aggregate 0 .nil)))
        [.field outerIdx outerTy, .field innerIdx innerTy] val =
        .ok (.aggregate variantIdx
          (setOrExtendFields fields outerIdx
            (.aggregate 0 (setOrExtendFields .nil innerIdx val)))) := by
    unfold writeProjectedForLocal
    rw [hNoUnion]
    dsimp only [writeProjectedValue]
    rw [hGetExt fields outerIdx (.aggregate 0 .nil)]
    dsimp only [writeProjectedValue]
    rw [hGetNil innerIdx]
    dsimp only [writeProjectedValue]
    rw [hSetExt fields outerIdx (.aggregate 0 .nil)
      (.aggregate 0 (setOrExtendFields .nil innerIdx val))]
  unfold evalStmt
  dsimp only
  rw [hRv]
  dsimp only
  rw [hInit]
  dsimp only
  rw [hEns, hWrite]
  dsimp only
  rw [hSet, hProt,
    resolveBorrowWriteLocalProj_of_not_union localDecls layouts locals₁ dstLoc
      [.field outerIdx outerTy, .field innerIdx innerTy] hNoUnion]

private theorem writeProjectedForLocal_uninit_non_field_subproj_ub
    (locals₁ : List LocalSlot)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (dstLoc : Local)
    (fieldIdx : FieldIdx)
    (fieldTy : Ty)
    (nextProj : ProjectionElem)
    (rest : List ProjectionElem)
    (val : Value)
    (hSub :
      (∃ idxLocal, nextProj = .index idxLocal) ∨
      (∃ offset minLen fromEnd, nextProj = .constantIndex offset minLen fromEnd) ∨
      (∃ fromIdx toIdx fromEnd, nextProj = .subslice fromIdx toIdx fromEnd) ∨
      (∃ variantName variantIdx, nextProj = .downcast variantName variantIdx)) :
    writeProjectedForLocal locals₁ localDecls layouts dstLoc (.aggregate 0 .nil)
      (.field fieldIdx fieldTy :: nextProj :: rest) val = .ub := by
  have hGetNil : get? (.nil : List Value) fieldIdx = .none := by
    cases fieldIdx <;> rfl
  have hWP :
      writeProjectedValue locals₁ (.aggregate 0 .nil)
        (.field fieldIdx fieldTy :: nextProj :: rest) val = .ub := by
    rcases hSub with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;>
      (cases fieldIdx <;> rfl)
  unfold writeProjectedForLocal
  cases placeTouchesUnion localDecls layouts
      { local_ := dstLoc, projection := .field fieldIdx fieldTy :: nextProj :: rest } with
  | false => exact hWP
  | true =>
    cases get? localDecls dstLoc with
    | none => exact hWP
    | some decl =>
      dsimp only
      unfold writeProjectedValueUnionAware
      dsimp only
      split
      · rename_i count l _
        cases Nat.ble (.succ fieldIdx) count with
        | false => rfl
        | true =>
          rcases hSub with ⟨_, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl
      · simp [hGetNil]

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
  have hEns :
      ensureNestedFieldShells (.aggregate 0 .nil)
        (.field fieldIdx fieldTy :: nextProj :: rest) = .aggregate 0 .nil := by
    rcases fieldTy with ⟨kind, lIdx⟩
    rcases hSub with ⟨idxLocal, rfl⟩ | ⟨offset, minLen, fromEnd, rfl⟩ |
        ⟨fromIdx, toIdx, fromEnd, rfl⟩ | ⟨variantName, variantIdx, rfl⟩ <;>
      (cases kind <;> rfl)
  have hW :=
    writeProjectedForLocal_uninit_non_field_subproj_ub
      locals₁ localDecls layouts dstLoc fieldIdx fieldTy nextProj rest val hSub
  unfold evalStmt
  dsimp only
  rw [hRv]
  dsimp only
  rw [hUninit]
  cases hSh : uninitFieldWriteShell? localDecls layouts dstLoc
      (.field fieldIdx fieldTy) (nextProj :: rest) with
  | none => rfl
  | some shell =>
    have hShell : shell = .aggregate 0 .nil := by
      unfold uninitFieldWriteShell? at hSh
      dsimp only at hSh
      rw [hEns] at hSh
      split at hSh <;> first | (injection hSh with h; exact h.symm) | nomatch hSh
    subst hShell
    dsimp only
    rw [hW]

/--
`D13b` array-field boundary (`evalStmt_assign_uninit_array_field_elem_ub`):
writing an element of a never-written fixed-length array field
(`.field fieldIdx { kind := .array elemKind count, .. } :: .index idxLocal :: rest`)
of a live but uninitialized local still faults with `MirStepNode.fail .ub`,
whatever the local's declared type. `ensureNestedFieldShells` materializes no
array shell, because filling the unwritten elements with `.unit` placeholders
would let later reads of those elements succeed where MiniRust and Miri report
a read of uninitialized memory.
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
        (ensureNestedFieldShells rootVal (.field writeIdx writeTy :: .nil))
        (.field writeIdx writeTy :: .nil) val = .ok rootVal')
    (hSet : set? locals₁ dstLoc (.init rootVal') = .some locals₂)
    (hPerm : perm = .active ∨ perm = .frozen) :
    (let sibEntry : BorrowEntry :=
       { tag := tag, targetLocal := dstLoc,
         targetProjection := .field borIdx borTy :: .nil, perm := perm }
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
         protector := .some protId }
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
    dsimp only
    rw [hRv]
    dsimp only
    rw [hInit]
    dsimp only
    rw [hWrite]
    dsimp only
    rw [hSet, hAP, hBor, hTrunc]
    rcases hPerm with rfl | rfl <;>
      simp [invalidateConflictingBorrowsAtProj, updateBorrowPermAtProj,
        treeBorrowWriterRelatedness, borrowEntryOverlapsWrite,
        projectionsOverlap, stripTransparentProjections,
        normalizeSubsliceProjections, projectionsOverlapAux,
        treeBorrowNodeAccess, treeBorrowPermTransition, applyTreeBorrowTransition,
        sibEntry]
  · intro protEntry hBor hAP
    unfold evalStmt
    dsimp only
    rw [hRv]
    dsimp only
    rw [hInit]
    dsimp only
    rw [hWrite]
    dsimp only
    rw [hSet, hAP, hBor, hTrunc]
    rcases hPerm with rfl | rfl <;>
      simp [hasProtectedWriteConflict,
        borrowEntryOverlapsWrite, projectionsOverlap, stripTransparentProjections,
        normalizeSubsliceProjections, projectionsOverlapAux,
        isBorrowProtected, natListContainsBool, borrowEntryWriteConflicts,
        protEntry]

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
     writePlaceValue locals₁ mem₁.borrows dst val localDecls layouts = .ok locals₂ →
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
     writePlaceValue locals₁ mem₁.borrows dst val localDecls layouts = .ok locals₂ →
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
          (.field writeIdx writeTy :: .nil) = (.field writeIdx writeTy :: .nil) := rfl
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
  · intro protEntry hBor hAP hCaller hWOk
    unfold evalStmt
    dsimp only [dst]
    rw [hRv]
    dsimp only
    cases hEPW : evalPlaceWrite locals₁ mem₁.borrows dst val mem₁.activeProtectors localDecls layouts with
    | ub =>
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
            (.field writeIdx writeTy :: .nil) = (.field writeIdx writeTy :: .nil) := rfl
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
