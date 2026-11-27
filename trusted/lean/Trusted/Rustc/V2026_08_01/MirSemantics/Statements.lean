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
Test whether `bytes` contains any `AbstractByte.uninit` byte.
-/
def hasUninitByte : List AbstractByte → Bool
  | .nil => false
  | .uninit :: _ => true
  | .init _ _ :: rest => hasUninitByte rest

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
Extract raw overlay bytes from the trailing element of a union aggregate's
`fieldVals` when it is a `unionBytes`-element lossless raw-byte carrier
`.aggregate 0 rawVals`.

Reference (The Rust Reference 1.98.0, "Unions"):
<https://doc.rust-lang.org/1.98.0/reference/items/unions.html>

> "The key property of unions is that all fields of a union share common
> storage. As a result, writes to one field of a union can overwrite its other
> fields, and size of a union is determined by the size of its largest field."

Modeling choice (`agent_docs/trusted-rust.md`): Reads the trailing lossless
raw-byte overlay slot appended by `overlayRawAbstractByteVals`.
-/
def trailingUnionOverlayBytes? (unionBytes : Nat) : List Value → Option (List AbstractByte)
  | .nil => .none
  | .aggregate 0 rawVals :: .nil =>
    match Nat.beq (length rawVals) unionBytes with
    | true => decodeRawAbstractByteVals? rawVals
    | false => .none
  | _ :: .nil => .none
  | _ :: rest => trailingUnionOverlayBytes? unionBytes rest

/--
Encode the `unionBytes`-byte storage image of a union local from its populated
`fieldVals`, preserving any lossless raw-byte overlay (including full
`PtrByteFrag` metadata and invalid scalar bit patterns) and padding any
uninitialized byte positions up to `unionBytes` with `AbstractByte.uninit`.

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
    (fieldVals : List Value)
    (unionLayoutIdxOpt : Option Nat := .none) :
    List AbstractByte :=
  let layoutEncodedOpt : Option (List AbstractByte) :=
    match unionLayoutIdxOpt with
    | .some uIdx =>
      match encodeByLayoutIdxAux 8 layouts uIdx (.aggregate 0 fieldVals) with
      | .some bs => .some (padUnionAbstractBytes unionBytes bs)
      | .none => .none
    | .none => .none
  match layoutEncodedOpt with
  | .some bs => bs
  | .none =>
    match trailingUnionOverlayBytes? unionBytes fieldVals with
    | .some rawBs => rawBs
    | .none =>
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
Whether `k` is a non-pointer primitive scalar (`bool`, `char`, integer, or float)
that must not receive a provenance-bearing `Value.ptr` directly without passing
through `Ptr2IntTransmutePolicy` byte conversion.
-/
@[reducible]
def isNonPtrPrimitiveKind : RigidTy → Bool
  | .bool | .char | .int _ | .uint _ | .float _ => true
  | _ => false

/--
Convert a copied single-element value `copiedVal` from `srcPt` to `dstEffTy`
without forging pointer provenance, without letting pointer provenance leak
into a non-pointer integer destination (even under matching pointee shapes),
and without triggering premature write-time UB on invalid scalar bit patterns
(`Kani#5205` / `#5196`).

Reference (`core::ptr::copy_nonoverlapping` documentation, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "The copy is \"untyped\" in the sense that data may be uninitialized or
> otherwise violate the requirements of `T`. The initialization state is
> preserved exactly."

Reference (`core::mem::transmute` documentation, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/mem/fn.transmute.html>

> "Transmuting pointers to integers in a const context is undefined behavior,
> unless the pointer was originally created from an integer."
-/
def convertCopySingleValue?
    (layouts : LayoutTable)
    (srcPtOpt dstPtOpt dstPlaceTyOpt : Option Ty)
    (copiedVal : Value) :
    Option Value :=
  let effDstTyOpt : Option Ty :=
    match dstPlaceTyOpt with
    | .some t => .some t
    | .none => dstPtOpt
  let encodeCopied (sTyOpt : Option Ty) : Option (List AbstractByte) :=
    match sTyOpt with
    | .some sTy =>
      match encodeTypedValueToBytes layouts sTy copiedVal with
      | .some bs => .some bs
      | .none => encodeUntypedValueToBytes defaultCodecFuel copiedVal
    | .none => encodeUntypedValueToBytes defaultCodecFuel copiedVal
  match srcPtOpt, effDstTyOpt with
  | .some srcPt, .some dstTy =>
    let directProvLeak : Bool :=
      Bool.and (valueHasProv copiedVal) (isNonPtrPrimitiveKind dstTy.kind)
    let needsByteConvert : Bool :=
      Bool.or directProvLeak (Bool.not (sameRigidTyShape srcPt.kind dstTy.kind))
    match needsByteConvert with
    | false =>
      match dstTy.kind, copiedVal with
      | .adt _ _, .scalar _ | .adt _ _, .ptr _ _ =>
        match encodeCopied (.some srcPt) with
        | .some bs => decodeUntypedStorageBytes defaultCodecFuel layouts dstTy bs .strictUcg630Ub
        | .none => .none
      | _, _ => .some copiedVal
    | true =>
      match encodeCopied (.some srcPt) with
      | .some bs =>
        match rigidTyByteSize layouts dstTy with
        | .some dSz =>
          match Nat.beq (length bs) dSz with
          | true => decodeUntypedStorageBytes defaultCodecFuel layouts dstTy bs .strictUcg630Ub
          | false => .none
        | .none =>
          match directProvLeak with
          | true => .none
          | false => .some copiedVal
      | .none =>
        match directProvLeak with
        | true => .none
        | false =>
          match rigidTyByteSize layouts srcPt, rigidTyByteSize layouts dstTy with
          | .some sSz, .some dSz =>
            match Nat.beq sSz dSz with
            | false => .none
            | true => .none
          | _, _ => .some copiedVal
  | .none, .some dstTy =>
    match Bool.and (valueHasProv copiedVal) (isNonPtrPrimitiveKind dstTy.kind) with
    | true => .none
    | false => .some copiedVal
  | _, .none => .some copiedVal

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
        let dstPlaceTyOpt : Option Ty :=
          match get? locals₃ dstPlace.local_ with
          | .some _ => placeTyResolved localDecls layouts dstPlace
          | .none => .none
        let srcPtOpt := operandPointeeTy localDecls layouts src
        let dstPtOpt := operandPointeeTy localDecls layouts dst
        let convertedOpt : Option Value :=
          convertCopySingleValue? layouts srcPtOpt dstPtOpt dstPlaceTyOpt copiedVal
        match convertedOpt with
        | .none => MirStepNode.fail .ub
        | .some finalVal =>
          match
            writePlaceValueUntyped
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
                      .aggregate 0 (spliceValues (encodeRawAbstractByteVals bs) 0 dstElems)
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
`dstPlace.local_` indexes a caller local) via `writePlaceValueUntyped`,
invalidate conflicting Tree Borrows tags on `dstTargetLocal` relative to
`dstTag`, and advance `s` to the next statement.
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
    writePlaceValueUntyped
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
non-overlap (`rangesDisjoint`), UCG #558 pointer-byte fragment coherence
without provenance forging, and read-time validity (`Kani#5205` / `#5196`):
- Uninitialized union bytes (`AbstractByte.uninit`), invalid scalar bit
  patterns, and intact or fragmented pointer bytes copied into a union
  destination (`dstUnionOpt = .some _`) are preserved losslessly via
  `decodeUnionBytesWithCountOpt`.
- Copying into a non-union destination (`dstUnionOpt = .none`) uses
  `decodeUntypedStorageBytes` (preserving `PtrByteFrag` in `[u8; N]`, never
  forging pointer provenance, rejecting provenance into non-pointer scalars
  under `.strictUcg630Ub`, and deferring `bool`/`char`/`Unaligned<bool>`
  bit-validity checks to typed reads).

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
          let srcUnionLayoutIdxOpt : Option Nat :=
            match get? localDecls srcEntry.targetLocal with
            | .some decl => .some (resolveTyWithLocalDecls localDecls layouts decl.ty).layoutIdx
            | .none => .none
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
                srcUnionLayoutIdxOpt
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
                | true => placeTyResolved localDecls layouts srcPlace
                | false => .none
              let fullSrcBytesOpt : Option (List AbstractByte) :=
                match srcPlaceTyOpt with
                | .some sTy =>
                  match encodeTypedValueToBytes layouts sTy srcSubVal with
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
          let dstUnionLayoutIdxOpt : Option Nat :=
            match get? localDecls dstEntry.targetLocal with
            | .some decl => .some (resolveTyWithLocalDecls localDecls layouts decl.ty).layoutIdx
            | .none => .none
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
                dstUnionLayoutIdxOpt
            match
              writeAbstractBytesAt dstStorageBytes dstEffStart copiedBytes
            with
            | .none => MirStepNode.fail .ub
            | .some updatedUnionBytes =>
              let losslessUnionOpt : Option Value :=
                match dstUnionLayoutIdxOpt with
                | .some uIdx =>
                  match LayoutTable.lookup layouts uIdx with
                  | .some { isUninhabited := false, variants := .single 0, fields := .union count, .. } =>
                    decodeUnionBytesWithCountOpt layouts uIdx count updatedUnionBytes
                  | _ => .none
                | .none => .none
              let newUnionVal : Value :=
                match losslessUnionOpt with
                | .some unionVal => unionVal
                | .none =>
                  match dstInfo.fieldTarget with
                  | .some (dstFieldIdx, dstFieldTy, dstFieldBytes) =>
                    match
                      sliceAbstractBytes updatedUnionBytes 0 dstFieldBytes
                    with
                    | .some updatedFieldBytes =>
                      match
                        decodeUntypedStorageBytes
                          defaultCodecFuel
                          layouts
                          dstFieldTy
                          updatedFieldBytes
                          .strictUcg630Ub
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
                        decodeUntypedStorageBytes
                          defaultCodecFuel
                          layouts
                          (resolveTyWithLocalDecls localDecls layouts decl.ty)
                          updatedUnionBytes
                          .strictUcg630Ub
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
            | true => placeTyResolved localDecls layouts dstPlace
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
                    decodeUntypedStorageBytes
                      defaultCodecFuel
                      layouts
                      dstPt
                      copiedBytes
                      .strictUcg630Ub
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
                      decodeUntypedStorageBytes
                        defaultCodecFuel
                        layouts
                        dstPt
                        copiedBytes
                        .strictUcg630Ub
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
                    match hasUninitByte copiedBytes with
                    | true => .none
                    | false =>
                      .some
                        (.aggregate 0
                          (spliceValues (encodeRawAbstractByteVals copiedBytes) dstStart dstElems))
                | _, _ => .none
              match dstTargetTyOpt with
              | .some dstPt =>
                let dstOldBytesOpt : Option (List AbstractByte) :=
                  match encodeTypedValueToBytes layouts dstPt dstSubVal with
                  | .some bs => .some bs
                  | .none => encodeUntypedValueToBytes defaultCodecFuel dstSubVal
                match dstOldBytesOpt with
                | .some dstOldBytes =>
                  match
                    writeAbstractBytesAt dstOldBytes dstStart copiedBytes
                  with
                  | .none => MirStepNode.fail .ub
                  | .some updatedDstBytes =>
                    let isPartialWrite : Bool := Nat.blt copyByteLen (length updatedDstBytes)
                    match
                      decodeUntypedStorageBytes
                        defaultCodecFuel
                        layouts
                        dstPt
                        updatedDstBytes
                        .strictUcg630Ub
                        isPartialWrite
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
  | v :: rest =>
    match isRawFragByteVal v with
    | true => elemsAreByteScalars rest
    | false => false

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
    match placeTyResolved localDecls layouts { local_ := loc, projection := proj } with
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
    match placeTyResolved localDecls layouts { local_ := loc, projection := parentProj } with
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
Whether `k` is an unsigned or signed primitive integer `RigidTy` (`.uint _` or
`.int _`), whose runtime representation is `Value.scalar` of its fixed byte
width and whose bit-validity invariant admits every initialized bit pattern.

Reference (The Rust Reference 1.98.0, "Numeric types — Integer types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#integer-types>

> "The unsigned integer types consist of:"
> "The signed two's complement integer types consist of:"

Justification: unlike `bool` or `char`, Rust's fixed-width integer types have no
invalid initialized bit patterns, so equal-width signed and unsigned integer
scalars can be transferred directly without bit-pattern re-validation.

Modeling assumptions and unsupported behavior: non-integer scalar kinds (`bool`,
`char`, `float`) return `false`.
-/
@[reducible]
def isUnrestrictedIntKind : RigidTy → Bool
  | .uint _ => true
  | .int _ => true
  | _ => false

/--
Whether every element value in `elems` has the exact runtime representation of
a scalar or thin-pointer pointee type `pt` of byte size `elemSz`, and (for
restricted scalars `.bool` / `.char`) satisfies `pt`'s validity invariant.
Used by `copyContainerStrideOk` for untyped containers (e.g. caller-owned
referents) so direct element-window splicing never confuses `.aggregate`,
`.scalar`, and `.ptr` element shapes.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The following is a non-exhaustive list of invalid values:
> - A `bool` that isn't 0 or 1.
> - A `char` that is a surrogate or above `char::MAX`."

Justification: when an untyped container's elements are spliced directly for a
pointee type `pt`, requiring each element to match `pt`'s runtime constructor,
width, and scalar range ensures no invalid `bool`/`char` or mismatched aggregate
enters a typed destination.

Modeling assumptions and unsupported behavior: aggregate and wide-pointer
pointee types return `false` on untyped containers so they fail closed with
`.unsupported`.
-/
def elemsAllMatchPointeeRep (pt : Ty) (elemSz : Nat) : List Value → Bool
  | .nil => true
  | v :: rest =>
    let ok : Bool :=
      match pt.kind, v with
      | .uint _, .scalar sc | .int _, .scalar sc | .float _, .scalar sc =>
        Nat.beq sc.sizeBytes elemSz
      | .bool, .scalar sc =>
        Bool.and (Nat.beq sc.sizeBytes 1) (Bool.or (Nat.beq sc.bits 0) (Nat.beq sc.bits 1))
      | .char, .scalar sc =>
        Bool.and (Nat.beq sc.sizeBytes 4) (isValidCharCode sc.bits)
      | .fnPtr _ _ _ _, .ptr _ ptrSz => Nat.beq ptrSz elemSz
      | .rawPtr _ pointee, .ptr _ ptrSz | .ref _ pointee, .ptr _ ptrSz =>
        let isThin : Bool :=
          match pointee with
          | .slice _ | .str | .dynamic _ => false
          | _ => true
        Bool.and isThin (Nat.beq ptrSz elemSz)
      | _, _ => false
    match ok with
    | true => elemsAllMatchPointeeRep pt elemSz rest
    | false => false

/--
Whether every value in `elems` is a `Value.scalar` of exact byte width `elemSz`.
-/
def elemsAllScalarsOfSize (elemSz : Nat) : List Value → Bool
  | .nil => true
  | .scalar sc :: rest =>
    match Nat.beq sc.sizeBytes elemSz with
    | true => elemsAllScalarsOfSize elemSz rest
    | false => false
  | _ :: _ => false

/--
Element-stride and representation guard for one container of a multi-element
`copy_nonoverlapping` (`copySliceElements`): whether transferring element
values directly is representation- and validity-exact for one copied element
of the pointee type.

- When both the container's static element kind `elemKindOpt` and the operand's
  pointee type `pointeeOpt` are known, they must be structurally identical
  (`rigidTyEq ek pt.kind`), or both must be unrestricted integer scalars
  (`.uint _` / `.int _`) of the copied element byte size `elemSzOpt` (so
  restricted scalars like `bool`/`char`, distinct tuple/ADT types, and
  aggregate-vs-scalar mismatches are never spliced directly as element values).
- When the container is untyped (`elemKindOpt = .none`, e.g. a caller-owned
  referent) and `pointeeOpt = .some pt`, every element value must match `pt`'s
  exact scalar or thin-pointer representation (`elemsAllMatchPointeeRep`).
- When `pointeeOpt = .none`, only uniform-width scalar elements matching
  `elemSzOpt` (and, if typed, an unrestricted integer container element kind)
  are accepted (`elemsAllScalarsOfSize`).

Reference (The Rust Reference 1.98.0, "Array layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#array-layout>

> "An array of [T; N] has a size of size_of::<T>() * N and the same alignment of T. Arrays are laid out so that the zero-based nth element of the array is offset from the start of the array by n * size_of::<T>() bytes."

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The following is a non-exhaustive list of invalid values:
> - A `bool` that isn't 0 or 1.
> - A `char` that is a surrogate or above `char::MAX`."

Justification: transferring `count` element values directly is equivalent to
copying `count * size_of::<T>()` bytes only when each element occupies
`size_of::<T>()` bytes at the array stride and shares the destination's value
representation without violating destination validity invariants. Mismatched
types (such as `u8` into `[bool; N]`, wrapper structs into `[u32; N]`, distinct
tuples, or untyped aggregate caller referents) fail closed with `.unsupported`
rather than corrupting runtime values or synthesizing false `.ub`.

Modeling assumption: signed and unsigned integer scalars of equal byte width
share the same `Value.scalar` representation and unrestricted validity range.
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
    match rigidTyEq ek pt.kind with
    | true => true
    | false =>
      match
        isUnrestrictedIntKind ek,
        isUnrestrictedIntKind pt.kind,
        rigidTyKindByteSize ek,
        elemSzOpt
      with
      | true, true, .some ekSz, .some elemSz => Nat.beq ekSz elemSz
      | _, _, _, _ => false
  | .none, .some pt =>
    match elemSzOpt with
    | .some elemSz => elemsAllMatchPointeeRep pt elemSz elems
    | .none => false
  | .some ek, .none =>
    match isUnrestrictedIntKind ek, rigidTyKindByteSize ek, elemSzOpt with
    | true, .some ekSz, .some elemSz =>
      Bool.and (Nat.beq ekSz elemSz) (elemsAllScalarsOfSize elemSz elems)
    | _, _, _ => false
  | .none, .none =>
    match elemSzOpt with
    | .some elemSz => elemsAllScalarsOfSize elemSz elems
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
Select the effective pointee `Ty` shared by the two endpoints of an array-window
`copy_nonoverlapping` (`copySliceElements`): prefers `srcPtOpt` when present and
falls back to `dstPtOpt` when `srcPtOpt` is `.none` (paired with
`copySlicePointeesCompatible`).
-/
@[reducible]
def copyEffectivePointee? (srcPtOpt dstPtOpt : Option Ty) : Option Ty :=
  match srcPtOpt, dstPtOpt with
  | .some sp, _ => .some sp
  | .none, .some dp => .some dp
  | .none, .none => .none

/--
Whether the source and destination pointee types of an array-window
`copy_nonoverlapping` (`copySliceElements`) agree in runtime element
representation when both are statically known: either structurally equal
(`rigidTyEq`), or both unrestricted integer scalars (`isUnrestrictedIntKind`;
byte-size equality was already checked by `copyPointeeSizesConflict`).

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "pub const unsafe fn copy_nonoverlapping<T>(src: *const T, dst: *mut T, count: usize)"

Justification: in `core::ptr::copy_nonoverlapping::<T>`, `src` and `dst` share a
common pointee `T`; rejecting mismatched pointee shapes on synthetic MIR (such
as `*const (u32, u32)` vs `*mut u64` or `*const u8` vs `*mut bool`) prevents
direct element-window splicing from placing incompatible runtime `Value`s into
the destination array.

Modeling assumptions and unsupported behavior: mismatched non-integer pointee
types fail closed with `.unsupported`; equal-width signed/unsigned integers
share the same `Value.scalar` representation.
-/
@[reducible]
def copySlicePointeesCompatible (srcPtOpt dstPtOpt : Option Ty) : Bool :=
  match srcPtOpt, dstPtOpt with
  | .some sp, .some dp =>
    match rigidTyEq sp.kind dp.kind with
    | true => true
    | false =>
      Bool.and (isUnrestrictedIntKind sp.kind) (isUnrestrictedIntKind dp.kind)
  | _, _ => true

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
- When both windows are in bounds, the element stride and cross-endpoint pointee
  representation must agree (`copySlicePointeesCompatible` and
  `copyContainerStrideOk` at `copyEffectivePointee?`, else `.unsupported`), the
  windows must not overlap (else `.ub`), and the source window is spliced into
  the destination container; the outcome names the two accessed windows for the
  Tree Borrows read-then-write transition (`borrowsAfterCopySlice`, applied by
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
  let effPtOpt := copyEffectivePointee? srcEp.pointeeOpt dstEp.pointeeOpt
  let strideOk : Bool :=
    Bool.and
      (copySlicePointeesCompatible srcEp.pointeeOpt dstEp.pointeeOpt)
      (Bool.and
        (copyContainerStrideOk
          (copyContainerElemKind? localDecls layouts locals srcEp.entry.targetLocal srcParentProj)
          effPtOpt
          srcElems
          effSzOpt)
        (copyContainerStrideOk
          (copyContainerElemKind? localDecls layouts locals dstEp.entry.targetLocal dstParentProj)
          effPtOpt
          dstElems
          effSzOpt))
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
Whether `k` is a primitive scalar `RigidTy` whose byte representation is
layout-table-independent and supported by `Bytes.lean` (`encodeValueToBytes` /
`decodeValueFromBytes`): integer scalars, `bool`, and `char`.
-/
@[reducible]
def isLayoutIndepScalarKind : RigidTy → Bool
  | .uint _ => true
  | .int _ => true
  | .bool => true
  | .char => true
  | _ => false

/--
Whether `k` has a layout-table-independent exact byte representation in
`Bytes.lean` (primitive scalars, zero-sized `()`/`fnDef`, and arrays of
layout-independent primitive scalars or length `0`).
-/
@[reducible]
def isLayoutIndepByteKind : RigidTy → Bool
  | .uint _ => true
  | .int _ => true
  | .bool => true
  | .char => true
  | .tuple .nil => true
  | .fnDef _ _ => true
  | .array ek n => Bool.or (Nat.beq n 0) (isLayoutIndepScalarKind ek)
  | _ => false

/--
Whether every `RigidTy` in `ks` satisfies `isLayoutIndepScalarKind`.
-/
def listAllLayoutIndepScalar : List RigidTy → Bool
  | .nil => true
  | k :: rest =>
    match isLayoutIndepScalarKind k with
    | true => listAllLayoutIndepScalar rest
    | false => false

/--
Whether every `Value` in `vs` is a non-pointer flat value (`Value.scalar` or
`Value.unit`). Rejects `Value.ptr` so untyped byte encoding never serializes an
abstract pointer's relative `offsetBytes` (`0` at allocation base) as concrete
zero address bytes.
-/
def allNonPtrScalarOrUnitValues : List Value → Bool
  | .nil => true
  | .scalar _ :: rest => allNonPtrScalarOrUnitValues rest
  | .unit :: rest => allNonPtrScalarOrUnitValues rest
  | _ :: _ => false

/--
Whether a `ScalarLayout` has a `PrimitiveKind.int` representation (as opposed to
`.pointer` or `.float`), so `decodeScalarLayoutBytes` produces `Value.scalar`
without fabricating pointer provenance from raw integer bytes.
-/
@[reducible]
def scalarLayoutIsNonPtr : ScalarLayout → Bool
  | .initialized (.int _ _) _ => true
  | .union (.int _ _) => true
  | _ => false

/--
Whether every layout index in `flIdxs` resolves in `layouts` to a non-zero-sized
live single-variant non-pointer primitive scalar layout (`FieldsShape.primitive`),
excluding 0-sized generic parameter placeholders (`sigIsParamPlaceholder`), so
`decodeValueFromBytes`'s `fieldLayouts` path decodes each field cleanly.
-/
def fieldLayoutsAllPrimitive (layouts : LayoutTable) : List Nat → Bool
  | .nil => true
  | flIdx :: rest =>
    match LayoutTable.lookup layouts flIdx with
    | .some {
        size := sz,
        isUninhabited := false,
        variants := .single _,
        fields := .primitive,
        backendRepr := .scalar sl, .. } =>
      match Bool.and (Nat.ble 1 sz.bytes) (scalarLayoutIsNonPtr sl) with
      | true => fieldLayoutsAllPrimitive layouts rest
      | false => false
    | _ => false

/--
Whether `k` is a thin pointer type (`.rawPtr`, `.ref`, or `.fnPtr` with sized
pointee, i.e., not `.slice`, `.str`, or `.dynamic`).
-/
@[reducible]
def isThinPtrCopyKind : RigidTy → Bool
  | .fnPtr _ _ _ _ => true
  | .rawPtr _ pointee | .ref _ pointee =>
    match pointee with
    | .slice _ | .str | .dynamic _ => false
    | _ => true
  | _ => false

/--
Whether `encodeValueToBytes defaultCodecFuel layouts ty v` produces the exact
in-memory byte representation of `v : ty` without falling back to untyped
declaration-order field concatenation (which ignores `repr(Rust)` field
reordering, padding, and enum tags/niches) or serializing abstract `Value.ptr`
offsets (`0` at the start of a non-null stack allocation) as concrete zero
address bytes.

Reference (The Rust Reference 1.98.0, "Type layout — The Rust representation"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#the-rust-representation>

> "There are no guarantees of data layout made by this representation."

Reference (The Rust Reference 1.98.0, "Pointer types — References (`&` and `&mut`)"):
<https://doc.rust-lang.org/1.98.0/reference/types/pointer.html#shared-references->

> "Shared references point to memory which is owned by some other value."

Justification: `encodeValueToBytes` captures exact Rust memory bytes only when
either the type's byte layout is fixed independently of `LayoutTable`
(`isLayoutIndepByteKind`), or a captured `TypeLayout` entry provides explicit
`FieldsShape.arbitrary` field offsets (or non-zero non-pointer `.primitive`, or
zero-sized unit `.arbitrary .nil`) for a non-generic single-variant struct/tuple
whose runtime field values contain no abstract pointers
(`allNonPtrScalarOrUnitValues`). Non-zero-sized 0-field niche/tag ADTs, enums,
pointer-carrying structs, generic ADTs, and layout-free tuples/structs fail
closed.

Modeling assumptions and unsupported behavior: encoding of enums, generic ADTs,
pointer-containing aggregates, and non-zero-sized 0-field ADTs is not modeled
here and returns `false` so `copyBytesSubplace` fails closed with `.unsupported`.
-/
@[reducible]
def srcValHasExactByteEncoding
    (layouts : LayoutTable)
    (ty : Ty)
    (v : Value) :
    Bool :=
  match isLayoutIndepByteKind ty.kind with
  | true => true
  | false =>
    match isThinPtrCopyKind ty.kind with
    | true => true
    | false =>
      match ty.kind with
      | .tuple (kHead :: kTail) =>
        match LayoutTable.lookup layouts ty.layoutIdx with
        | .some l =>
          match l.isUninhabited, l.fields with
          | false, .arbitrary offsets _ =>
            Bool.and
              (Nat.beq (length offsets) (length (kHead :: kTail)))
              (listAllLayoutIndepScalar (kHead :: kTail))
          | _, _ => false
        | .none => false
      | .adt _ _ =>
        match LayoutTable.lookup layouts ty.layoutIdx with
        | .some l =>
          match l.isUninhabited, l.variants, l.fields with
          | false, .single _, .primitive =>
            match l.backendRepr, v with
            | .scalar sl, .scalar _ =>
              Bool.and (Nat.ble 1 l.size.bytes) (scalarLayoutIsNonPtr sl)
            | _, _ => false
          | false, .single _, .arbitrary .nil _ => Nat.beq l.size.bytes 0
          | false, .single _, .arbitrary offsets _ =>
            match v with
            | .aggregate _ fieldVals =>
              Bool.and
                (Nat.beq (length offsets) (length fieldVals))
                (allNonPtrScalarOrUnitValues fieldVals)
            | _ => false
          | _, _, _ => false
        | .none => false
      | _ => false

/--
Whether `decodeValueFromBytes defaultCodecFuel layouts ty bs` decodes `bs` into
an exact value of `ty` without falling back to declaration-order tuple decoding,
synthetic `layoutIdx := 0` element lookups, unchecked non-zero-sized 0-field
tag/niche acceptance, or guessed span decoding.

Reference (The Rust Reference 1.98.0, "Type layout — The Rust representation"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#the-rust-representation>

> "There are no guarantees of data layout made by this representation."

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution are “valid”, and producing an invalid value is hence immediate UB."

Justification: decoding raw bytes into a tuple or struct without explicit
captured field offsets and per-field scalar layouts would fabricate a
declaration-order layout that Rust does not guarantee, and accepting non-zero
0-field ADTs without tag validation would ignore niche/discriminant invariants.
Restricting decoding to `isLayoutIndepByteKind` types, zero-sized 0-field unit
structs, and explicitly laid-out non-pointer single-variant structs or tuples
ensures every committed value matches the captured Rust layout.

Modeling assumptions and unsupported behavior: decoding into enums, generic
ADTs, pointer-containing structs, non-zero-sized 0-field ADTs, and layout-free
heterogeneous tuples returns `false` so `copyBytesSubplace` fails closed with
`.unsupported`.
-/
@[reducible]
def dstTyHasExactByteDecode
    (layouts : LayoutTable)
    (ty : Ty) :
    Bool :=
  match isLayoutIndepByteKind ty.kind with
  | true => true
  | false =>
    match isThinPtrCopyKind ty.kind with
    | true => true
    | false =>
      match ty.kind with
      | .tuple (kHead :: kTail) =>
        match LayoutTable.lookup layouts ty.layoutIdx with
        | .some l =>
          match l.isUninhabited, l.fields with
          | false, .arbitrary offsets _ =>
            Bool.and
              (Nat.beq (length offsets) (length (kHead :: kTail)))
              (listAllLayoutIndepScalar (kHead :: kTail))
          | _, _ => false
        | .none => false
      | .adt _ _ =>
        match LayoutTable.lookup layouts ty.layoutIdx with
        | .some l =>
          match l.isUninhabited, l.variants, l.fields with
          | false, .single _, .primitive =>
            match l.backendRepr with
            | .scalar sl =>
              Bool.and (Nat.ble 1 l.size.bytes) (scalarLayoutIsNonPtr sl)
            | _ => false
          | false, .single _, .arbitrary .nil _ => Nat.beq l.size.bytes 0
          | false, .single _, .arbitrary offsets _ =>
            match
              Bool.and
                (Nat.beq (length l.fieldLayouts) (length offsets))
                (fieldLayoutsAllPrimitive layouts l.fieldLayouts)
            with
            | true => true
            | false =>
              match offsets, l.backendRepr with
              | _ :: .nil, .scalar s0 => scalarLayoutIsNonPtr s0
              | _ :: _ :: .nil, .scalarPair s0 s1 =>
                Bool.and (scalarLayoutIsNonPtr s0) (scalarLayoutIsNonPtr s1)
              | _, _ => false
          | _, _, _ => false
        | .none => false
      | _ => false

/--
Byte-level path of a multi-element or sub-place `copy_nonoverlapping` when at
least one endpoint is not an array or slice (`copyViaBytes`): the source bytes
are obtained by layout-faithful encoding of the source value
(`encodeValueToBytes` guarded by `srcValHasExactByteEncoding` for declared
active locals, or scalar-only untyped encoding for untyped scalar slices and
scalars), and they are placed into the destination only where the model can
place them with an exact captured layout (`dstTyHasExactByteDecode`).

- An access that is certainly outside its allocation is undefined behavior
  (`copyAccessFitsAlloc?` at `count * size_of::<T>()` bytes).
- Source: the source is sliced by element only when it is a genuine array or
  slice whose elements have the copied element size (`elemsMatchByteStride`)
  and are layout-independent primitive scalars (or untyped flat scalars);
  otherwise the whole pointed-to value is encoded at `srcPtr.offsetBytes = 0`
  only when its exact byte layout is known (`srcValHasExactByteEncoding` for
  declared locals, or `.scalar`/`.unit` for untyped targets). The encoded
  length must equal `count * size_of::<T>()` when that is known.
- Destination: raw bytes are spliced only into a byte container (`[u8; N]`,
  `[i8; N]`, a byte slice, or an untyped sequence of one-byte scalars) at the
  byte index of the pointer; otherwise the bytes are decoded as one whole value
  of the layout-resolved pointed-to place (`placeTyResolved`, or its enclosing
  array when the pointer is at element `0`) guarded by
  `dstTyHasExactByteDecode`, requiring `dstPtr.offsetBytes = 0` and an exact
  size match.
- The accessed source and destination places must not overlap; the outcome
  names exactly those places for the Tree Borrows read-then-write transition
  (`borrowsAfterCopySlice`, applied by `evalCopySubplaceMulti`).
- Every remaining case (a partial read or write of a value, a pointer into the
  middle of a value, an enum or layout-free `repr(Rust)` aggregate, or a
  type-punned sequence) is inside the allocation as far as the model knows and
  fails closed with `.unsupported`.

Reference (`core::ptr::copy_nonoverlapping`, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "src must be valid for reads of count * size_of::<T>() bytes or that number must be 0."
> "dst must be valid for writes of count * size_of::<T>() bytes or that number must be 0."
> "The region of memory beginning at src with a size of count * size_of::<T>() bytes must not overlap with the region of memory beginning at dst with the same size."
> "Like read, copy_nonoverlapping creates a bitwise copy of T, regardless of whether T is Copy."

Reference (`core::ptr`, "Safety", Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/index.html#safety>

> "For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that the pointer be dereferenceable. The provenance of the pointer is used to determine which allocation it is derived from; a pointer is dereferenceable if the memory range of the given size starting at the pointer is entirely contained within the bounds of that allocation. Note that in Rust, every (stack-allocated) variable is considered a separate allocation."

Justification: a "bitwise copy" reads and writes exact in-memory bytes.
Splicing bytes element-wise is exact only when each destination element is one
byte, and layout-faithful encoding/decoding via `placeTyResolved` and
`srcValHasExactByteEncoding` / `dstTyHasExactByteDecode` prevents silent
declaration-order fabrication for `repr(Rust)` structs/tuples, enums, and
synthetic `layoutIdx := 0` collisions. Undefined behavior is reported only when
a necessary validity condition fails (the access is certainly outside the
allocation), when the accessed places overlap, or when the aliasing model
rejects the accesses.

Modeling assumptions and unsupported behavior: bytes that `decodeValueFromBytes`
does not decode at the destination type, sources or destinations without an
exact captured byte layout (such as enums, layout-free tuples/structs, or
untyped caller-owned aggregates), and raw-byte pointer reinterpretation fail
closed with `.unsupported`; a copy between two pointers with the same tag is
undefined behavior as in the single-element path.

Target pointer width: a thin-pointer destination (`isThinPtrCopyKind`) has the
target pointer width `layoutPointerBytes layouts` (4 bytes on a 32-bit target),
both for the partial-pointer-fragment window check and for the whole-value
decode, so an in-order `copy_nonoverlapping::<u8>` of all 4 bytes of a 32-bit
pointer into a `*const T` place decodes the coherent `PtrByteFrag` image back
to the pointer instead of failing the size comparison against a 64-bit width.

Reference (The Rust Reference 1.98.0, "Type Layout — Primitive data layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#primitive-data-layout>

> "usize and isize have a size big enough to contain every address on the
> target platform. For example, on a 32 bit target, this is 4 bytes, and on a
> 64 bit target, this is 8 bytes."

Reference (The Rust Reference 1.98.0, "Type Layout — Pointers and references layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#pointers-and-references-layout>

> "Pointers to sized types have the same size and alignment as usize."

Modeling choice (`agent_docs/trusted-rust.md`): on 64-bit targets the thin
pointer width `layoutPointerBytes layouts = 8` equals `rigidTyByteSize`, so the
64-bit cases are unchanged.
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
      (Bool.or
        (copyAccessCertainlyOob (fitsAt srcEp expBytesOpt))
        (copyAccessCertainlyOob (fitsAt dstEp expBytesOpt)))
      (Nat.beq srcEp.ptr.tag dstEp.ptr.tag)
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
    let srcSubPlaceTyOpt : Option Ty :=
      match get? locals srcEp.entry.targetLocal with
      | .some _ =>
        placeTyResolved
          localDecls
          layouts
          { local_ := srcEp.entry.targetLocal
            projection := srcEp.entry.targetProjection }
      | .none => .none
    let srcSubSliceOk : Bool :=
      match expBytesOpt, srcSubPlaceTyOpt with
      | .some expB, .some srcTy =>
        match isThinPtrCopyKind srcTy.kind, tyByteSize localDecls layouts srcTy with
        | true, .some sB =>
          Bool.and
            (Nat.ble (Nat.add srcEp.ptr.offsetBytes expB) sB)
            (Bool.or (Nat.blt 0 srcEp.ptr.offsetBytes) (Nat.blt expB sB))
        | _, _ => false
      | _, _ => false
    let wholeSrc : Option (Value × List ProjectionElem × Option (List ProjectionElem × List Value)) :=
      match Bool.or (Nat.beq srcEp.ptr.offsetBytes 0) srcSubSliceOk, srcEp.rootValOpt with
      | true, .some srcRootVal =>
        match readProjectedValue locals srcRootVal srcEp.entry.targetProjection with
        | .ok srcSubVal => .some (srcSubVal, srcResolvedProj, .none)
        | _ => .none
      | _, _ => .none
    let srcSlice : Option (Value × List ProjectionElem × Option (List ProjectionElem × List Value)) :=
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
            let slicedElems := takeValues n (dropValues effSrcStart srcElems)
            .some
              (.aggregate 0 slicedElems,
                copySliceWindowProj srcParentProj effSrcStart n (length srcElems),
                .some (srcParentProj, slicedElems))
          | false => .none
        | _, _ => wholeSrc
      | _, _ => wholeSrc
    match srcSlice with
    | .none =>
      match srcEp.rootValOpt with
      | .none => .ub
      | .some _ => .unsupported
    | .some (sVal, srcEffProj, sliceInfoOpt) =>
      let bsOpt : Option (List AbstractByte) :=
        match sliceInfoOpt with
        | .some (srcParentProj, slicedElems) =>
          match
            copyContainerElemKind?
              localDecls
              layouts
              locals
              srcEp.entry.targetLocal
              srcParentProj
          with
          | .some ek =>
            let ekExact : Bool :=
              match isLayoutIndepScalarKind ek with
              | true => true
              | false =>
                match ek with
                | .tuple .nil | .fnDef _ _ => true
                | _ => false
            match ekExact with
            | true =>
              match
                encodeValueToBytes
                  defaultCodecFuel
                  layouts
                  { kind := .array ek (length slicedElems), layoutIdx := unresolvedLayoutIdx layouts }
                  sVal
              with
              | .some bs => .some bs
              | .none =>
                match ek with
                | .uint .u8 | .int .i8 => decodeRawAbstractByteVals? slicedElems
                | _ => .none
            | false => .none
          | .none =>
            match allNonPtrScalarOrUnitValues slicedElems with
            | true => encodeUntypedValueToBytes defaultCodecFuel sVal
            | false => .none
        | .none =>
          let rawFullBsOpt : Option (List AbstractByte) :=
            match srcSubPlaceTyOpt with
            | .some srcTy =>
              match srcValHasExactByteEncoding layouts srcTy sVal with
              | true =>
                match encodeTypedValueToBytes layouts srcTy sVal with
                | .some bs => .some bs
                | .none =>
                  match isThinPtrCopyKind srcTy.kind, sVal with
                  | true, .aggregate 0 rawVals => decodeRawAbstractByteVals? rawVals
                  | _, _ =>
                    match srcTy.kind, sVal with
                    | .array (.uint .u8) n, .aggregate 0 rawVals =>
                      match Nat.beq (length rawVals) n with
                      | true => decodeRawAbstractByteVals? rawVals
                      | false => .none
                    | .array (.int .i8) n, .aggregate 0 rawVals =>
                      match Nat.beq (length rawVals) n with
                      | true => decodeRawAbstractByteVals? rawVals
                      | false => .none
                    | _, _ => .none
              | false => .none
            | .none =>
              match sVal with
              | .scalar _ => encodeUntypedValueToBytes defaultCodecFuel sVal
              | .unit => encodeUntypedValueToBytes defaultCodecFuel sVal
              | _ => .none
          match rawFullBsOpt with
          | .none => .none
          | .some fullBs =>
            match srcSubSliceOk, expBytesOpt with
            | true, .some expB => sliceAbstractBytes fullBs srcEp.ptr.offsetBytes expB
            | _, _ => .some fullBs
      match bsOpt with
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
                match hasUninitByte bs with
                | true => .unsupported
                | false =>
                  commit
                    { local_ := dstLocal, projection := dstParentProj }
                    (.aggregate 0 (spliceValues (encodeRawAbstractByteVals bs) effDstStart dstElems))
                    (copySliceWindowProj dstParentProj effDstStart (length bs) (length dstElems))
            | .none =>
              let dstPlaceTyOpt : Option Ty :=
                match get? locals dstLocal with
                | .some _ =>
                  placeTyResolved
                    localDecls
                    layouts
                    { local_ := dstLocal, projection := dstEp.entry.targetProjection }
                | .none => .none
              let partialPtrDstOutcomeOpt : Option CopySliceOutcome :=
                match dstPlaceTyOpt with
                | .some dstTy =>
                  match isThinPtrCopyKind dstTy.kind, rigidTyByteSize layouts dstTy with
                  | true, .some _ =>
                    let dstBytes := layoutPointerBytes layouts
                    match
                      Bool.and
                        (Nat.ble (Nat.add dstEp.ptr.offsetBytes (length bs)) dstBytes)
                        (Bool.or (Nat.blt 0 dstEp.ptr.offsetBytes) (Nat.blt (length bs) dstBytes))
                    with
                    | false => .none
                    | true =>
                      let oldDstBytesOpt : Option (List AbstractByte) :=
                        match dstEp.rootValOpt with
                        | .none =>
                          match stripLeadingOpaqueCast dstEp.entry.targetProjection with
                          | .nil => .some (replicateUninitBytes dstBytes)
                          | _ :: _ => .none
                        | .some dstRootVal =>
                          match readProjectedValue locals dstRootVal dstEp.entry.targetProjection with
                          | .ok (.aggregate 0 rawVals) => decodeRawAbstractByteVals? rawVals
                          | .ok dstSubVal => encodeTypedValueToBytes layouts dstTy dstSubVal
                          | _ => .none
                      match oldDstBytesOpt with
                      | .none => .none
                      | .some oldDstBytes =>
                        match writeAbstractBytesAt oldDstBytes dstEp.ptr.offsetBytes bs with
                        | .none => .none
                        | .some mergedBytes =>
                          match
                            decodeUntypedStorageBytes
                              defaultCodecFuel
                              layouts
                              dstTy
                              mergedBytes
                              .strictUcg630Ub
                              true
                          with
                          | .some decodedVal =>
                            .some
                              (commit
                                { local_ := dstLocal, projection := dstEp.entry.targetProjection }
                                decodedVal
                                dstResolvedProj)
                          | .none => .none
                  | _, _ => .none
                | .none => .none
              match partialPtrDstOutcomeOpt with
              | .some outcome => outcome
              | .none =>
                match Nat.beq dstEp.ptr.offsetBytes 0 with
                | false => .unsupported
                | true =>
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
                          let repExact : Bool :=
                            match dstSubVal with
                            | .scalar sc =>
                              Bool.and
                                (isLayoutIndepScalarKind pt.kind)
                                (Nat.beq ptBytes sc.sizeBytes)
                            | _ => false
                          match repExact with
                          | true => .some pt
                          | false => .none
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
                      match dstTyHasExactByteDecode layouts dstTy with
                      | false => .none
                      | true =>
                        match rigidTyByteSize layouts dstTy with
                        | .none => .none
                        | .some dstBytes =>
                          match Nat.beq (length bs) dstBytes with
                          | false =>
                            match
                              Bool.and
                                (isThinPtrCopyKind dstTy.kind)
                                (Nat.beq (length bs) (layoutPointerBytes layouts))
                            with
                            | false => .none
                            | true =>
                              match
                                decodeUntypedStorageBytes
                                  defaultCodecFuel
                                  layouts
                                  dstTy
                                  bs
                                  .strictUcg630Ub
                              with
                              | .some decodedVal =>
                                .some
                                  (commit
                                    { local_ := dstLocal, projection := dstProj }
                                    decodedVal
                                    dstEffProj)
                              | .none => .none
                          | true =>
                            match
                              decodeUntypedStorageBytes
                                defaultCodecFuel
                                layouts
                                dstTy
                                bs
                                .strictUcg630Ub
                            with
                            | .some decodedVal =>
                              .some
                                (commit
                                  { local_ := dstLocal, projection := dstProj }
                                  decodedVal
                                  dstEffProj)
                            | .none =>
                              match
                                Bool.and
                                  (isNonPtrPrimitiveKind dstTy.kind)
                                  (policyRejectsProv .strictUcg630Ub bs)
                              with
                              | true => .some .ub
                              | false => .none
                    | _, _ => .none
                  match decodeAt dstTargetTyOpt dstEp.entry.targetProjection dstResolvedProj with
                  | .some outcome => outcome
                  | .none =>
                    match dstWinOpt with
                    | .some (dstParentProj, .zero, _) =>
                      let parentTyOpt : Option Ty :=
                        match get? locals dstLocal with
                        | .some _ =>
                          placeTyResolved
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
                        match
                          stripLeadingOpaqueCast initProj,
                          copyPlaceIsNonArrayAggregate localDecls layouts locals dstLocal initProj
                        with
                        | .nil, false =>
                          let parentTyOpt : Option Ty :=
                            match get? locals dstLocal with
                            | .some _ =>
                              placeTyResolved
                                localDecls
                                layouts
                                { local_ := dstLocal, projection := initProj }
                            | .none => .none
                          match decodeAt parentTyOpt initProj initProj with
                          | .some outcome => outcome
                          | .none => .unsupported
                        | _, _ => .unsupported
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
    writePlaceValueUntyped
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
    let elemSzOpt : Option Nat :=
      copyPointeeByteSize?
        localDecls
        layouts
        (operandPointeeTy localDecls layouts src)
        (operandPointeeTy localDecls layouts dst)
    let srcPlaceSizeMismatch : Bool :=
      match elemSzOpt, get? locals₃ srcEntry.targetLocal with
      | .some eSz, .some _ =>
        match
          placeTyResolved
            localDecls
            layouts
            { local_ := srcEntry.targetLocal, projection := srcEntry.targetProjection }
        with
        | .some sPlaceTy =>
          match tyByteSize localDecls layouts sPlaceTy with
          | .some pSz => Bool.not (Nat.beq pSz eSz)
          | .none => false
        | .none => false
      | _, _ => false
    let dstPlaceSizeMismatch : Bool :=
      match elemSzOpt, get? locals₃ dstEntry.targetLocal with
      | .some eSz, .some _ =>
        match
          placeTyResolved
            localDecls
            layouts
            { local_ := dstEntry.targetLocal, projection := dstEntry.targetProjection }
        with
        | .some dPlaceTy =>
          match tyByteSize localDecls layouts dPlaceTy with
          | .some pSz => Bool.not (Nat.beq pSz eSz)
          | .none => false
        | .none => false
      | _, _ => false
    let isSingleDirect :=
      Bool.and
        (Nat.beq n 1)
        (Bool.and
          (Bool.and (Nat.beq srcStart 0) (Nat.beq dstStart 0))
          (Bool.and (Bool.not srcPlaceSizeMismatch) (Bool.not dstPlaceSizeMismatch)))
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
            convertCopySingleValue?
              layouts
              (operandPointeeTy localDecls layouts src)
              (operandPointeeTy localDecls layouts dst)
              .none
              copiedVal
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
padding that `setOrExtendFields` also uses for union fields. A leading
`ProjectionElem.opaqueCast` (`DIV-TR-OPAQUECAST-ROOT-DISPATCH`) is stripped
together with the rest of the leading cast chain (`stripLeadingOpaqueCast`), and
the shell is the one of the field projection below it, keyed on the effective
cast type: local `loc` is re-declared at that type
(`eraseLeadingOpaqueCastDecls`), because `(_loc as T).f = v` writes field `f` of
`_loc` at type `T`, not at the local's declared opaque type. Every other
projection head (`.index`, `.constantIndex`, `.subslice`, `.downcast`,
`.unwrapUnsafeBinder`, or a cast chain not followed by `.field`; `.deref` writes
never reach this helper) and every non-aggregate declared or cast type yields
`.none`, preserving the fault on projected writes into uninitialized locals.

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
  | .opaqueCast castTy =>
    match stripLeadingOpaqueCast rest with
    | .field fieldIdx fieldTy :: fieldRest =>
      match
        placeTy
          (eraseLeadingOpaqueCastDecls localDecls layouts loc (.opaqueCast castTy :: rest))
          layouts
          { local_ := loc, projection := .nil }
      with
      | .some { kind := .adt _ _, .. } =>
        .some
          (ensureNestedFieldShells
            (.aggregate 0 .nil)
            (.field fieldIdx fieldTy :: fieldRest))
      | .some { kind := .tuple _, .. } =>
        .some
          (ensureNestedFieldShells
            (.aggregate 0 .nil)
            (.field fieldIdx fieldTy :: fieldRest))
      | _ => .none
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
`SetDiscriminant(loc, variantIdx)` on a whole local of the active frame whose
payload fields are `fields` (`.nil` when the local was `.uninit`, so every
payload field stays uninitialized; `DIV-LM-ENUM-SET-DISCR-UNINIT`): writing the
tag is a write to `loc`, so it faults with `.ub` on a protected-write conflict
(`hasProtectedWriteConflict`) and otherwise applies the foreign-write transition
to every borrow of `loc` (`invalidateConflictingBorrows`), both scoped to the
active frame's depth `length s.memory.callStack`.

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
          let ptrBytes := layoutPointerBytes layouts
          let isNonNullEmptySlice :=
            match ptrOrFatVal with
            | .aggregate 0 (.ptr p pSz :: .scalar ⟨0, lSz⟩ :: .nil) =>
              Bool.and
                (Bool.and (Nat.beq pSz ptrBytes) (Nat.beq lSz ptrBytes))
                (Bool.and
                  (Bool.not isMutRefPlace)
                  (Bool.not
                    (Bool.and
                      (Nat.beq p.allocId 0)
                      (Nat.beq p.offsetBytes 0))))
            | .aggregate 0 (.scalar s :: .scalar ⟨0, lSz⟩ :: .nil) =>
              Bool.and
                (Bool.and (Nat.beq s.sizeBytes ptrBytes) (Nat.beq lSz ptrBytes))
                (Bool.and
                  (Bool.not isMutRefPlace)
                  (Bool.not (Nat.beq s.bits 0)))
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
    match p.projection, stripLeadingOpaqueCast p.projection with
    | .nil, _ =>
      match get? s.frame.locals p.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals p.local_ .uninit with
        | .some locals' => MirStepNode.step (advanceStmt s locals')
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | .opaqueCast _ :: _, .nil =>
      match get? s.frame.locals p.local_ with
      | .some .dead => MirStepNode.fail .ub
      | .some _ =>
        match set? s.frame.locals p.local_ .uninit with
        | .some locals' => MirStepNode.step (advanceStmt s locals')
        | .none => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | proj :: rest, _ =>
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
        evalSetDiscriminantLocal s p.local_ variantIdx fields
      | .some (.init _) => MirStepNode.fail .ub
      | .some .uninit =>
        match setDiscriminantUninitDeclOk localDecls p.local_ with
        | true => evalSetDiscriminantLocal s p.local_ variantIdx .nil
        | false => MirStepNode.unsupported
      | .some .dead => MirStepNode.fail .ub
      | .none => MirStepNode.fail .ub
    | .opaqueCast castTy :: restCast, .nil =>
      match get? s.frame.locals p.local_ with
      | .some (.init (.aggregate _ fields)) =>
        evalSetDiscriminantLocal s p.local_ variantIdx fields
      | .some (.init _) => MirStepNode.fail .ub
      | .some .uninit =>
        match
          setDiscriminantUninitDeclOk
            (eraseLeadingOpaqueCastDecls
              localDecls
              layouts
              p.local_
              (.opaqueCast castTy :: restCast))
            p.local_
        with
        | true => evalSetDiscriminantLocal s p.local_ variantIdx .nil
        | false => MirStepNode.unsupported
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
        let newVal : Value := .aggregate variantIdx fields
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
                  | true =>
                    evalSetDiscriminantDerefWrite
                      s s.frame.locals p .nil (.aggregate variantIdx .nil) localDecls layouts
                  | false => MirStepNode.unsupported
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
                    let (targetDecls, _) :=
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
                    | true =>
                      evalSetDiscriminantDerefWrite
                        s s.frame.locals p .nil (.aggregate variantIdx .nil) localDecls layouts
                    | false => MirStepNode.unsupported
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
        let decls' :=
          eraseLeadingOpaqueCastDecls localDecls layouts dst.local_ (proj :: rest)
        match get? locals₁ dst.local_ with
        | .some (.init rootVal) =>
          match
            writeProjectedForLocal
              locals₁
              decls'
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
                  decls'
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
                decls'
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
                    decls'
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
    cases localDecls with
    | nil =>
      dsimp only [placeTy, get?]
      rw [List.getElem?_nil, hDis]
    | cons decl0 declRest =>
      dsimp only [placeTy, placeTyResolved]
      cases hDecl : get? (decl0 :: declRest) ptrLoc with
      | none =>
        dsimp only [materializeReadPtrValue, validateValueForTy?]
        rw [hDis]
      | some decl =>
        rcases decl with ⟨_, ⟨kind, layIdx⟩, _⟩
        dsimp only [resolveProjectedTy, resolveProjectedTyResolved, materializeReadPtrValue]
        cases hVal : validateValueForTy? layouts (.some ⟨kind, layIdx⟩) (.ptr ptrVal sz) with
        | false =>
          cases kind with
          | rawPtr _ _ => cases hVal
          | _ => rfl
        | true =>
          dsimp only
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
        .some { kind := .tuple fields, layoutIdx := layoutIdx })
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none := by
  cases proj with
  | opaqueCast castTy => exact False.elim (hNotCast castTy rfl)
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
and the head projection `proj`, not on the trailing projection path `rest`,
for a head projection other than `.opaqueCast` (`hNotCast`; the shell below a
leading cast chain depends on the projections that follow it,
`DIV-TR-OPAQUECAST-ROOT-DISPATCH`).
-/
@[simp]
theorem uninitFieldWriteShell?_eq_none_iff
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (loc : Local)
    (proj : ProjectionElem)
    (rest : List ProjectionElem)
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    uninitFieldWriteShell? localDecls layouts loc proj rest = .none ↔
      uninitFieldWriteShell? localDecls layouts loc proj .nil = .none := by
  cases proj with
  | opaqueCast castTy => exact False.elim (hNotCast castTy rfl)
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
                 | .none => .field fieldIdx fieldTy :: .nil) 0 0 (length mem₁.callStack) }) := by
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
                 | .none => .field fieldIdx fieldTy :: .nil) 0 0 (length mem₁.callStack) }) := by
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
                 | .none => projs) 0 0 (length mem₁.callStack) }) := by
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
    (hNoShell : uninitFieldWriteShell? localDecls layouts dstLoc proj = .none)
    (hNotCast : ∀ (castTy : Ty), proj ≠ .opaqueCast castTy := by intro _ h; nomatch h) :
    evalStmt s ⟨.assign ⟨dstLoc, proj :: rest⟩ rv, span⟩ localDecls layouts =
      MirStepNode.fail .ub := by
  have hNoShellRest :
      uninitFieldWriteShell? localDecls layouts dstLoc proj rest = .none :=
    (uninitFieldWriteShell?_eq_none_iff localDecls layouts dstLoc proj rest hNotCast).mpr hNoShell
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
                 | .none => projs) 0 0 (length mem₁.callStack) }) := by
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
        sibEntry, Nat.beq_refl]
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


/--
Validate a resolved `TypeLayout` for an ADT/closure at `layoutIdx`: accepts any
entry passing `layoutValidForAdt`, plus non-zero-index inhabited single-variant
`.primitive` entries (such as `NonNull<T>` or transparent newtypes).
-/
@[reducible]
def layoutValidForResolvedAdt (layoutIdx : Nat) (l : TypeLayout) : Bool :=
  match layoutValidForAdt l with
  | true => true
  | false =>
    match Nat.beq layoutIdx 0, l.isUninhabited, l.fields, l.variants with
    | false, false, .primitive, .single _ => true
    | _, _, _, _ => false

/--
Check whether any element of `ks` satisfies `pred`.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Most types have a fixed size that is known at compile time and implement the
> trait `Sized`."
-/
@[reducible]
def anyUnsizedRigidTy (pred : RigidTy → Bool) : List RigidTy → Bool
  | .nil => false
  | k :: rest =>
    match pred k with
    | true => true
    | false => anyUnsizedRigidTy pred rest

/--
Fuel-bounded check for whether `ty` is unsized (`.slice`, `.str`, `.dynamic`,
`.foreign`) or is a compound array/tuple containing an unsized type.

Reference (The Rust Reference, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Most types have a fixed size that is known at compile time and implement the
> trait `Sized`. A type with a size that is known only at run-time is called a
> dynamically sized type (DST) or, informally, an unsized type."
-/
@[reducible]
def isUnsizedRigidTy : Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ fuel', ty =>
    match ty with
    | .slice _ => true
    | .str => true
    | .dynamic _ => true
    | .foreign _ => true
    | .array elemTy _ => isUnsizedRigidTy fuel' elemTy
    | .tuple ks => anyUnsizedRigidTy (isUnsizedRigidTy fuel') ks
    | _ => false

/--
Look up a `TypeLayout` for a sized `ty : RigidTy` by scanning `localDecls` for a
declaration with `rigidTyEq decl.ty.kind ty`, returning `.none` when `ty` is
unsized (`isUnsizedRigidTy 8 ty = true`) or when no local of type `ty` carries a
layout. Rejecting unsized types here is essential because `rustc-capture` lowers
`tcx.layout_of` for unsized locals (recording the static prefix layout or a ZST
fallback layout), which must never be treated as the complete static layout of
an unsized type. There is also deliberately no positional fallback: an unrelated
entry such as `layouts.entries[0]` (often the return place's layout) would
silently report the wrong size and alignment.

Reference (`compiler/rustc_middle/src/ty/layout.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/layout.rs#L706-L712>

> "fn layout_of(&self, ty: Ty<'tcx>) -> Self::LayoutOfResult"
-/
@[reducible]
def findDeclLayoutForRigidTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Option TypeLayout :=
  match localDecls with
  | .nil => .none
  | decl :: rest =>
    match Bool.and (Bool.not (isUnsizedRigidTy 8 ty)) (rigidTyEq decl.ty.kind ty) with
    | true =>
      match LayoutTable.lookup layouts decl.ty.layoutIdx with
      | .some l => .some l
      | .none => findDeclLayoutForRigidTy rest layouts ty
    | false => findDeclLayoutForRigidTy rest layouts ty

/--
Compute the ABI byte alignment of a `RigidTy` when determined directly by its
primitive, pointer, or homogeneous array constructor on a 64-bit target.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of a value specifies what addresses are valid to store the
> value at. A value of alignment `n` must only be stored at an address that is a
> multiple of `n`."
-/
@[reducible]
def intrinsicRigidTyKindAlign : RigidTy → Option Nat
  | .bool => .some 1
  | .char => .some 4
  | .never => .some 1
  | .uint w => intCastTargetBytes (.uint w)
  | .int w => intCastTargetBytes (.int w)
  | .float .f16 => .some 2
  | .float .f32 => .some 4
  | .float .f64 => .some 8
  | .float .f128 => .some 16
  | .tuple .nil => .some 1
  | .fnDef _ _ => .some 1
  | .fnPtr _ _ _ _ => .some 8
  | .ref _ _ => .some 8
  | .rawPtr _ _ => .some 8
  | .array elemKind _ => intrinsicRigidTyKindAlign elemKind
  | _ => .none

/--
Compute the maximum `fieldAlign k` over the fields `ks` of a tuple, or `1` for
the unit tuple `()`, faulting with `.none` if any field alignment is unknown.

Reference (The Rust Reference, "The Rust Representation"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.repr.rust.layout>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.tuple.def>

> "The only data layout guarantees made by this representation are those
> required for soundness. These are:
>
> - The offset of a field is divisible by that field's alignment.
>
> - The alignment of the type is at least the maximum alignment of its fields."
> "Tuples are laid out according to the Rust representation."

Modeling choice: the Reference guarantees only that a tuple's alignment is AT
LEAST the maximum field alignment; this helper returns exactly that maximum
(what `rustc` computes today). Callers use it as the root-allocation alignment,
where a lower bound is sound for "aligned" verdicts and for the symbolic
`ptr_mask` criterion.
-/
@[reducible]
def tupleFieldsAlign (fieldAlign : RigidTy → Option Nat) : List RigidTy → Option Nat
  | .nil => .some 1
  | k :: rest =>
    match fieldAlign k, tupleFieldsAlign fieldAlign rest with
    | .some a, .some restA =>
      match Nat.ble a restA with
      | true => .some restA
      | false => .some a
    | _, _ => .none

/--
Fuel-bounded recursive helper for `intrinsicRigidTyAlign`, resolving nested
arrays of tuples/ADTs and nested tuples on a 64-bit target. `fuel` bounds the
type nesting depth only: `tupleFieldsAlign` folds over tuple fields without
consuming fuel, so tuples of any arity resolve.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2863-L2874>

> "pub const unsafe fn align_of_val<T: ?Sized>(ptr: *const T) -> usize;"
-/
@[reducible]
def intrinsicRigidTyAlignAux :
    Nat → List LocalDecl → LayoutTable → RigidTy → Option Nat
  | .zero, _, _, _ => .none
  | .succ fuel', localDecls, layouts, ty =>
    match intrinsicRigidTyKindAlign ty with
    | .some a => .some a
    | .none =>
      match ty with
      | .array elemKind _ =>
        match findDeclLayoutForRigidTy localDecls layouts elemKind with
        | .some l =>
          match Align.isPowerOfTwoBytes l.align with
          | true => .some l.align.bytes
          | false => .none
        | .none =>
          match findDeclLayoutForRigidTy localDecls layouts ty with
          | .some l =>
            match Align.isPowerOfTwoBytes l.align with
            | true => .some l.align.bytes
            | false => .none
          | .none => intrinsicRigidTyAlignAux fuel' localDecls layouts elemKind
      | .tuple ks =>
        match findDeclLayoutForRigidTy localDecls layouts ty with
        | .some l =>
          match Align.isPowerOfTwoBytes l.align with
          | true => .some l.align.bytes
          | false => .none
        | .none => tupleFieldsAlign (intrinsicRigidTyAlignAux fuel' localDecls layouts) ks
      | _ =>
        match findDeclLayoutForRigidTy localDecls layouts ty with
        | .some l =>
          match Align.isPowerOfTwoBytes l.align with
          | true => .some l.align.bytes
          | false => .none
        | .none => .none

/--
Determine the ABI byte alignment of a sized `RigidTy` on a 64-bit target for
`align_of_val`, validating that any `LayoutTable` entry alignment is a positive
power of two.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2863-L2874>

> "pub const unsafe fn align_of_val<T: ?Sized>(ptr: *const T) -> usize;"
-/
@[reducible]
def intrinsicRigidTyAlign
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Option Nat :=
  intrinsicRigidTyAlignAux 8 localDecls layouts ty

/--
Sum `fieldSize k` over the fields `ks` of a tuple, before the total is padded to
the tuple's alignment, faulting with `.none` if any field size is unknown.

Reference (The Rust Reference, "The Rust Representation"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.repr.rust.layout.struct>

> "For structs, it is further guaranteed that the fields do not overlap. That
> is, the fields can be ordered such that the offset plus the size of any field
> is less than or equal to the offset of the next field in the ordering."
-/
@[reducible]
def tupleFieldsByteSum (fieldSize : RigidTy → Option Nat) : List RigidTy → Option Nat
  | .nil => .some 0
  | k :: rest =>
    match fieldSize k, tupleFieldsByteSum fieldSize rest with
    | .some sz, .some restSz => .some (Nat.add sz restSz)
    | _, _ => .none

/--
Round `bytes` up to the nearest multiple of `alignBytes`.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is always a multiple of its alignment."
-/
@[reducible]
def roundUpToAlign (bytes alignBytes : Nat) : Nat :=
  match Nat.beq (Nat.mod bytes alignBytes) 0 with
  | true => bytes
  | false => Nat.add bytes (Nat.sub alignBytes (Nat.mod bytes alignBytes))

/--
Fuel-bounded recursive helper for `intrinsicRigidTyByteSize`, resolving nested
arrays and tuples of floats, `!`, and nested aggregates on a 64-bit target.

Without a `LayoutTable` entry, a tuple's size is the sum of its field sizes
rounded up to its alignment (`intrinsicRigidTyAlignAux`): the smallest size the
`Rust` representation permits, which `rustc` attains by ordering fields by
decreasing alignment. Summing without padding would give `(u32, u8)` size `5`,
violating the size/alignment invariant below. `fuel` bounds the type nesting
depth only: `tupleFieldsByteSum` folds over tuple fields without consuming fuel.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is always a multiple of its alignment."
-/
@[reducible]
def intrinsicRigidTyByteSizeAux :
    Nat → List LocalDecl → LayoutTable → RigidTy → Option Nat
  | .zero, _, _, _ => .none
  | .succ fuel', localDecls, layouts, ty =>
    match rigidTyKindByteSize ty with
    | .some sz => .some sz
    | .none =>
      match ty with
      | .never => .some 0
      | .float .f16 => .some 2
      | .float .f32 => .some 4
      | .float .f64 => .some 8
      | .float .f128 => .some 16
      | .array elemKind n =>
        match findDeclLayoutForRigidTy localDecls layouts elemKind with
        | .some l => .some (Nat.mul l.size.bytes n)
        | .none =>
          match findDeclLayoutForRigidTy localDecls layouts ty with
          | .some l => .some l.size.bytes
          | .none =>
            match intrinsicRigidTyByteSizeAux fuel' localDecls layouts elemKind with
            | .some elemSz => .some (Nat.mul elemSz n)
            | .none => .none
      | .tuple ks =>
        match findDeclLayoutForRigidTy localDecls layouts ty with
        | .some l => .some l.size.bytes
        | .none =>
          match
            tupleFieldsByteSum (intrinsicRigidTyByteSizeAux fuel' localDecls layouts) ks,
            intrinsicRigidTyAlignAux (.succ fuel') localDecls layouts ty
          with
          | .some rawBytes, .some alignBytes => .some (roundUpToAlign rawBytes alignBytes)
          | _, _ => .none
      | _ =>
        match findDeclLayoutForRigidTy localDecls layouts ty with
        | .some l => .some l.size.bytes
        | .none => .none

/--
Determine the static byte size of a sized `RigidTy` on a 64-bit target for
`arith_offset` and `size_of_val`, returning `.none` for unsized types (`.slice`,
`.str`, `.dynamic`, `.foreign`) or unresolvable ADTs.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."
-/
@[reducible]
def intrinsicRigidTyByteSize
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Option Nat :=
  intrinsicRigidTyByteSizeAux 8 localDecls layouts ty

/-!
## Shared Memory, Layout-Consistency, Tree Borrows, Exact Byte Codec, and Typed-Validity Helpers

Supporting ground operational semantics promoted into the TCB for the 8 core
memory & pointer intrinsics (`core::intrinsics::{copy, compare_bytes, raw_eq,
typed_swap_nonoverlapping, ptr_offset_from, ptr_offset_from_unsigned, ptr_mask,
black_box}`), matching `rustc 1.98.0-nightly (14210df0e 2026-05-31)` and the
Rust Reference 1.98.0.

All fuel-recursive helpers are top-level structurally recursive definitions over
`Init.Core` primitives (no `let rec` / `WellFounded.fix`, no `partial`, no
`unsafe`), ensuring kernel reducibility and `TrustedBoundary` containment.
-/

/--
Three-way outcome for memory, alignment, layout, and pointer-resolution checks
that distinguish defined results (`.ok`), immediate undefined behavior (`.ub`),
and fail-closed unmodeled boundaries (`.unsupported`).

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Rust code is incorrect if it exhibits any of the behaviors in the following
> list. This includes code within unsafe blocks and unsafe functions."
-/
inductive MemOpRes (α : Type) : Type where
  /-- Operation succeeded with value `val`. -/
  | ok (val : α) : MemOpRes α
  /-- Operation triggered immediate undefined behavior. -/
  | ub : MemOpRes α
  /-- Operation reached an unmodeled semantic boundary (fail closed). -/
  | unsupported : MemOpRes α

/--
Three-way typed validity outcome for byte slices (`typed_swap_nonoverlapping`)
and runtime values (`black_box`): `.valid` when all modeled validity invariants
hold, `.ub` when a documented validity invariant is violated, and `.unsupported`
when the model lacks enough layout/target/provenance information to decide
soundly without risking missed or false UB.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution are “valid”, and producing an invalid value is hence immediate UB."
-/
inductive TypedValidity : Type where
  /-- All modeled validity invariants hold. -/
  | valid : TypedValidity
  /-- A documented Rust validity invariant is violated (immediate UB). -/
  | ub : TypedValidity
  /-- Validity depends on unmodeled layout, enum, or provenance facts (fail closed). -/
  | unsupported : TypedValidity

/--
Minimum of two natural numbers in `Init.Core`.
-/
@[reducible]
def minNat (a b : Nat) : Nat :=
  match Nat.ble a b with
  | true => a
  | false => b

/--
Allocation container identity unifying frame-qualified stack locals and global
`CapturedAllocation` entries for disjointness and atomic-buffer checks.

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L21-L25>

> "//! * For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that
> //!   the pointer be *dereferenceable*. The [provenance] of the pointer is used to determine which
> //!   [allocation] it is derived from; a pointer is dereferenceable if the memory range of the given
> //!   size starting at the pointer is entirely contained within the bounds of that allocation. Note
> //!   that in Rust, every (stack-allocated) variable is considered a separate allocation."
-/
inductive AllocKey : Type where
  /-- Stack local `local_` belonging to the frame at depth `frameDepth`. -/
  | stack (frameDepth : Nat) (local_ : Local) : AllocKey
  /-- Global/static `CapturedAllocation` identified by `allocId`. -/
  | global (allocId : AllocId) : AllocKey

/--
Structural equality on `AllocKey`.
-/
@[reducible]
def AllocKey.beq : AllocKey → AllocKey → Bool
  | .stack d1 l1, .stack d2 l2 => Bool.and (Nat.beq d1 d2) (Nat.beq l1 l2)
  | .global a1, .global a2 => Nat.beq a1 a2
  | _, _ => false

/--
Target-aware byte width of an integer `RigidTy`, resolving `usize` and `isize`
from `layoutPointerBytes layouts` rather than hardcoding 8 bytes.

Reference (The Rust Reference 1.98.0, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The usize type is an unsigned integer type with the same number of bits as the platform’s pointer type. It can represent every memory address in the process."
> "The isize type is a signed two’s complement integer type with the same number of bits as the platform’s pointer type."
-/
@[reducible]
def intTyTargetBytes (layouts : LayoutTable) : RigidTy → Option Nat
  | .uint .u8 => .some 1
  | .uint .u16 => .some 2
  | .uint .u32 => .some 4
  | .uint .u64 => .some 8
  | .uint .u128 => .some 16
  | .uint .usize => .some (layoutPointerBytes layouts)
  | .int .i8 => .some 1
  | .int .i16 => .some 2
  | .int .i32 => .some 4
  | .int .i64 => .some 8
  | .int .i128 => .some 16
  | .int .isize => .some (layoutPointerBytes layouts)
  | _ => .none

/--
Byte width of an IEEE-754 floating-point `FloatTy`.

Reference (The Rust Reference 1.98.0, "Floating-Point Types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html#floating-point-types>

> "The IEEE 754-2008 “binary32” and “binary64” floating-point types are f32 and f64, respectively."
-/
@[reducible]
def floatTyByteWidth : FloatTy → Nat
  | .f16 => 2
  | .f32 => 4
  | .f64 => 8
  | .f128 => 16

/--
Target-aware byte width of a `ScalarLayout` (`rustc_abi::Scalar`), using
`layoutPointerBytes layouts` for `PrimitiveKind.pointer _` instead of assuming
a 64-bit pointer width.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1379-L1393>

> "pub enum Primitive {
>     ...
>     Int(Integer, bool),
>     Float(Float),
>     Pointer(AddressSpace),
> }"
-/
@[reducible]
def scalarLayoutTargetByteWidth (layouts : LayoutTable) (sl : ScalarLayout) : Option Nat :=
  let pk :=
    match sl with
    | .initialized p _ => p
    | .union p => p
  match pk with
  | .pointer _ => .some (layoutPointerBytes layouts)
  | _ => primitiveKindByteWidth pk

/--
Test whether `VariantsShape` is `.single _`.
-/
@[reducible]
def isSingleVariantShape : VariantsShape → Bool
  | .single _ => true
  | _ => false

/--
Return the last element of a tuple field list `ks` when every preceding element
is sized (`isUnsized k = false`), or `.none` when `ks` is empty or has an
unsized non-last element.

Reference (The Rust Reference 1.98.0, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Structs may contain a DST as the last field; this makes the struct itself a
> DST."
-/
@[reducible]
def tupleLastRigidTy? (isUnsized : RigidTy → Bool) : List RigidTy → Option RigidTy
  | .nil => .none
  | k :: .nil => .some k
  | k :: rest =>
    match isUnsized k with
    | true => .none
    | false => tupleLastRigidTy? isUnsized rest

/--
Fuel-bounded resolution of a known dynamically-sized wide-pointer tail
(`[T]`, `str`, `dyn Trait`) through nested tuples (`(Hdr, [T])`, etc.).

Reference (The Rust Reference 1.98.0, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html#r-dynamic-sized.pointer-types>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types, since they also store metadata:"
> "Pointers to slices store the number of elements; pointers to `str` store the
> length in bytes."
> "Pointers to trait objects store a pointer to a vtable."
> "Pointers to a struct or tuple with an unsized tail store the same metadata as
> a pointer to that tail."
-/
def knownWidePointeeTailAux? : Nat → RigidTy → Option RigidTy
  | .zero, _ => .none
  | .succ fuel', ty =>
    match ty with
    | .slice elem => .some (.slice elem)
    | .str => .some .str
    | .dynamic tr => .some (.dynamic tr)
    | .tuple ks =>
      match tupleLastRigidTy? (isUnsizedRigidTy fuel') ks with
      | .some lastK => knownWidePointeeTailAux? fuel' lastK
      | .none => .none
    | _ => .none

/--
Fuel-bounded check for whether a pointer to `ty` may be a wide pointer (a slice,
`str`, `dyn Trait`, an ADT whose fields are not in `RigidTy.adt`, a generic
`.param`/`.alias`, `.other`, or a tuple whose last element may be unsized).
`extern` `.foreign` types use thin pointers and answer `false`. Exhausting
`fuel` answers `true` (fail closed).

Reference (The Rust Reference 1.98.0, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html>

> "Structs may contain a DST as the last field; this makes the struct itself a
> DST."
-/
def ptrPointeeMayBeUnsizedAux : Nat → RigidTy → Bool
  | .zero, _ => true
  | .succ fuel', ty =>
    match ty with
    | .slice _ => true
    | .str => true
    | .dynamic _ => true
    | .adt _ _ => true
    | .param _ _ => true
    | .alias _ _ => true
    | .other _ => true
    | .tuple ks =>
      match tupleLastRigidTy? (isUnsizedRigidTy fuel') ks with
      | .some lastK => ptrPointeeMayBeUnsizedAux fuel' lastK
      | .none => false
    | _ => false

/--
Test whether `l : TypeLayout` has the size, alignment, and structural shape of a
1-word thin pointer (`.primitive` of `ptrBytes`) or a 2-word wide pointer
(`.arbitrary [o0, o1] _` of `2 * ptrBytes`) on `layouts`.

Reference (The Rust Reference 1.98.0, "Dynamically Sized Types"):
<https://doc.rust-lang.org/1.98.0/reference/dynamically-sized-types.html#r-dynamic-sized.pointer-types>

> "Pointer types to DSTs are sized but have twice the size of pointers to sized
> types"
-/
def isConsistentPtrLayout (layouts : LayoutTable) (l : TypeLayout) : Bool :=
  let ptrBytes := layoutPointerBytes layouts
  match
    Bool.and
      (TypeLayout.isWellFormed l)
      (Bool.and
        (Bool.not l.isUninhabited)
        (Bool.and
          (isSingleVariantShape l.variants)
          (Nat.ble l.align.bytes ptrBytes)))
  with
  | false => false
  | true =>
    match l.fields with
    | .primitive =>
      match Nat.beq l.size.bytes ptrBytes with
      | false => false
      | true =>
        match l.backendRepr with
        | .scalar sl =>
          match scalarLayoutTargetByteWidth layouts sl with
          | .some w => Nat.beq w ptrBytes
          | .none => false
        | .memory => true
        | .scalarPair _ _ => false
    | .arbitrary (o0 :: o1 :: .nil) _ =>
      let twoWords := Nat.mul 2 ptrBytes
      let offsetsOk :=
        Bool.or
          (Bool.and (Nat.beq o0.bytes 0) (Nat.beq o1.bytes ptrBytes))
          (Bool.and (Nat.beq o0.bytes ptrBytes) (Nat.beq o1.bytes 0))
      let reprOk :=
        match l.backendRepr with
        | .scalarPair s0 s1 =>
          match
            scalarLayoutTargetByteWidth layouts s0,
            scalarLayoutTargetByteWidth layouts s1
          with
          | .some w0, .some w1 => Bool.and (Nat.beq w0 ptrBytes) (Nat.beq w1 ptrBytes)
          | _, _ => false
        | .memory => true
        | .scalar _ => false
      Bool.and (Nat.beq l.size.bytes twoWords) (Bool.and offsetsOk reprOk)
    | _ => false

/--
Look up the confirmed byte size of a pointer (`&T` / `*const T` / `*mut T`) to
`pointee` from `localDecls` / `layouts`, strictly skipping unresolved
`layoutIdx = 0` entries (`isUnresolvedLayoutIdx`) and validating
`isConsistentPtrLayout` so an unrelated `entries[0]` never misclassifies a wide
custom-DST pointer as thin or vice versa.

Reference (`compiler/rustc_middle/src/ty/layout.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/ty/layout.rs#L706-L712>

> "fn layout_of(&self, ty: Ty<'tcx>) -> Self::LayoutOfResult"
-/
def declPtrToPointeeByteSize?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (pointee : RigidTy) :
    Option Nat :=
  match localDecls with
  | .nil => .none
  | decl :: rest =>
    let matchesPt : Bool :=
      match decl.ty.kind with
      | .ref _ pt => rigidTyEq pt pointee
      | .rawPtr _ pt => rigidTyEq pt pointee
      | _ => false
    match
      Bool.and matchesPt (Bool.not (isUnresolvedLayoutIdx layouts decl.ty.layoutIdx))
    with
    | true =>
      match LayoutTable.lookup layouts decl.ty.layoutIdx with
      | .some l =>
        match isConsistentPtrLayout layouts l with
        | true => .some l.size.bytes
        | false => declPtrToPointeeByteSize? rest layouts pointee
      | .none => declPtrToPointeeByteSize? rest layouts pointee
    | false => declPtrToPointeeByteSize? rest layouts pointee

/--
Helper checking that every `RigidTy` in `ks` satisfies `pred`.
-/
@[reducible]
def allRigidTysSatisfy (pred : RigidTy → Bool) : List RigidTy → Bool
  | .nil => true
  | k :: rest =>
    match pred k with
    | true => allRigidTysSatisfy pred rest
    | false => false

/--
Fuel-bounded gate testing whether Anneal's structural 64-bit layout helpers
(`Bytes.rigidTyKindByteSize`, `Places.intrinsicRigidTyKindAlign`) can be trusted
for `ty` on `layouts`:
- Pointer-width types (`usize`, `isize`, `fn()`, thin/wide pointers) require a
  64-bit table (`pointerBits == 64`).
- When `withAlign = true`, 8- and 16-byte primitives (`i64`/`u64`/`f64`/`i128`/
  `u128`/`f128`) require `pointerBits == 64` (on 32-bit platforms such as
  `i686`, `u64`/`f64` may be 4-aligned), and 2- and 4-byte primitives require
  `pointerBits ≥ 32`.
- Pointers to possibly-unsized pointees (`ptrPointeeMayBeUnsizedAux`, e.g.,
  custom DST `&Packet` or `&(u8, T)`) require a non-unresolved `LocalDecl`
  confirming an 8-byte pointer layout (`declPtrToPointeeByteSize? = .some 8`)
  unless the pointee is a directly handled top-level `[T]` / `str` / `dyn Trait`.

Reference (The Rust Reference 1.98.0, "Type Layout — Primitive Types"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.primitive.platform-specific-alignment>

> "The alignment of primitives is platform-specific. In most cases, their
> alignment is equal to their size, but it may be less. In particular, `i128`
> and `u128` are often aligned to 4 or 8 bytes even though their size is 16, and
> on many 32-bit platforms, `i64`, `u64`, and `f64` are only aligned to 4 bytes,
> not 8."
-/
def rigidTyLayoutDeterminedAux
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (withAlign : Bool) :
    Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ fuel', ty =>
    let ptrBits :=
      match layouts.pointerBits with
      | 0 => 64
      | n + 1 => n + 1
    let is64 := Nat.beq ptrBits 64
    let isAtLeast32 := Nat.ble 32 ptrBits
    match ty with
    | .bool => true
    | .never => true
    | .fnDef _ _ => true
    | .tuple .nil => true
    | .int .i8 => true
    | .uint .u8 => true
    | .int .i16 => match withAlign with | true => isAtLeast32 | false => true
    | .uint .u16 => match withAlign with | true => isAtLeast32 | false => true
    | .float .f16 => match withAlign with | true => isAtLeast32 | false => true
    | .int .i32 => match withAlign with | true => isAtLeast32 | false => true
    | .uint .u32 => match withAlign with | true => isAtLeast32 | false => true
    | .float .f32 => match withAlign with | true => isAtLeast32 | false => true
    | .char => match withAlign with | true => isAtLeast32 | false => true
    | .int .i64 => match withAlign with | true => is64 | false => true
    | .uint .u64 => match withAlign with | true => is64 | false => true
    | .float .f64 => match withAlign with | true => is64 | false => true
    | .int .i128 => match withAlign with | true => is64 | false => true
    | .uint .u128 => match withAlign with | true => is64 | false => true
    | .float .f128 => match withAlign with | true => is64 | false => true
    | .int .isize => is64
    | .uint .usize => is64
    | .fnPtr _ _ _ _ => is64
    | .ref _ pt =>
      match is64 with
      | false => false
      | true =>
        match pt with
        | .slice _ => true
        | .str => true
        | .dynamic _ => true
        | _ =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | false => true
          | true =>
            match declPtrToPointeeByteSize? localDecls layouts pt with
            | .some sz => Nat.beq sz 8
            | .none => false
    | .rawPtr _ pt =>
      match is64 with
      | false => false
      | true =>
        match pt with
        | .slice _ => true
        | .str => true
        | .dynamic _ => true
        | _ =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | false => true
          | true =>
            match declPtrToPointeeByteSize? localDecls layouts pt with
            | .some sz => Nat.beq sz 8
            | .none => false
    | .array elem n =>
      match Nat.beq n 0, withAlign with
      | true, false => true
      | _, _ => rigidTyLayoutDeterminedAux localDecls layouts withAlign fuel' elem
    | .tuple ks =>
      allRigidTysSatisfy
        (rigidTyLayoutDeterminedAux localDecls layouts withAlign fuel')
        ks
    | .adt _ _ => true
    | .closure _ _ => true
    | _ => false

/--
Test whether an explicit `TypeLayout` entry `l` is both size-consistent and
shape-consistent with the `Ty` it annotates on `layouts`, preventing mislabeled
layout indices (such as a primitive `u64` entry annotating `[u8; 8]` or `u8`)
from inflating alignment or widening Tree Borrows tag windows.

Reference (The Rust Reference 1.98.0, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an array with that item type including alignment padding. The size of a value is always a multiple of its alignment."
-/
def explicitLayoutConsistent (layouts : LayoutTable) (ty : Ty) (l : TypeLayout) : Bool :=
  let ptrBytes := layoutPointerBytes layouts
  match TypeLayout.isWellFormed l with
  | false => false
  | true =>
    match ty.kind with
    | .bool =>
      Bool.and (Bool.not l.isUninhabited)
        (Bool.and (Nat.beq l.size.bytes 1)
          (Bool.and (Nat.beq l.align.bytes 1)
            (Bool.and (isSingleVariantShape l.variants)
              (match l.fields with | .primitive => true | _ => false))))
    | .char =>
      Bool.and (Bool.not l.isUninhabited)
        (Bool.and (Nat.beq l.size.bytes 4)
          (Bool.and (Nat.ble l.align.bytes 4)
            (Bool.and (isSingleVariantShape l.variants)
              (match l.fields with | .primitive => true | _ => false))))
    | .int _ =>
      match intTyTargetBytes layouts ty.kind with
      | .some sz =>
        Bool.and (Bool.not l.isUninhabited)
          (Bool.and (Nat.beq l.size.bytes sz)
            (Bool.and (Nat.ble l.align.bytes sz)
              (Bool.and (isSingleVariantShape l.variants)
                (match l.fields with | .primitive => true | _ => false))))
      | .none => false
    | .uint _ =>
      match intTyTargetBytes layouts ty.kind with
      | .some sz =>
        Bool.and (Bool.not l.isUninhabited)
          (Bool.and (Nat.beq l.size.bytes sz)
            (Bool.and (Nat.ble l.align.bytes sz)
              (Bool.and (isSingleVariantShape l.variants)
                (match l.fields with | .primitive => true | _ => false))))
      | .none => false
    | .float w =>
      let sz := floatTyByteWidth w
      Bool.and (Bool.not l.isUninhabited)
        (Bool.and (Nat.beq l.size.bytes sz)
          (Bool.and (Nat.ble l.align.bytes sz)
            (Bool.and (isSingleVariantShape l.variants)
              (match l.fields with | .primitive => true | _ => false))))
    | .never =>
      Bool.and l.isUninhabited
        (Bool.and (Nat.beq l.size.bytes 0)
          (Bool.and (Nat.beq l.align.bytes 1)
            (match l.fields with | .primitive => true | _ => false)))
    | .fnDef _ _ =>
      Bool.and (Bool.not l.isUninhabited)
        (Bool.and (Nat.beq l.size.bytes 0)
          (Bool.and (Nat.beq l.align.bytes 1) (isSingleVariantShape l.variants)))
    | .fnPtr _ _ _ _ =>
      Bool.and (isConsistentPtrLayout layouts l) (Nat.beq l.size.bytes ptrBytes)
    | .ref _ pt =>
      match isConsistentPtrLayout layouts l with
      | false => false
      | true =>
        match knownWidePointeeTailAux? 8 pt with
        | .some _ => Nat.beq l.size.bytes (Nat.mul 2 ptrBytes)
        | .none =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | true =>
            Bool.or (Nat.beq l.size.bytes ptrBytes) (Nat.beq l.size.bytes (Nat.mul 2 ptrBytes))
          | false => Nat.beq l.size.bytes ptrBytes
    | .rawPtr _ pt =>
      match isConsistentPtrLayout layouts l with
      | false => false
      | true =>
        match knownWidePointeeTailAux? 8 pt with
        | .some _ => Nat.beq l.size.bytes (Nat.mul 2 ptrBytes)
        | .none =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | true =>
            Bool.or (Nat.beq l.size.bytes ptrBytes) (Nat.beq l.size.bytes (Nat.mul 2 ptrBytes))
          | false => Nat.beq l.size.bytes ptrBytes
    | .array elem n =>
      match isUnsizedRigidTy 8 elem with
      | true => false
      | false =>
        match l.fields, l.variants with
        | .array stride count, .single _ =>
          let elemSzCheck : Bool :=
            match intTyTargetBytes layouts elem with
            | .some esz => Nat.beq stride.bytes esz
            | .none =>
              match elem with
              | .bool => Nat.beq stride.bytes 1
              | .char => Nat.beq stride.bytes 4
              | .float fw => Nat.beq stride.bytes (floatTyByteWidth fw)
              | .never => Nat.beq stride.bytes 0
              | .fnDef _ _ => Nat.beq stride.bytes 0
              | .tuple .nil => Nat.beq stride.bytes 0
              | .fnPtr _ _ _ _ => Nat.beq stride.bytes ptrBytes
              | _ => true
          Bool.and (Nat.beq count n)
            (Bool.and (Nat.beq l.size.bytes (Nat.mul stride.bytes n)) elemSzCheck)
        | _, _ => false
    | .tuple .nil =>
      Bool.and (Bool.not l.isUninhabited)
        (Bool.and (Nat.beq l.size.bytes 0)
          (Bool.and (Nat.beq l.align.bytes 1) (isSingleVariantShape l.variants)))
    | .tuple ks =>
      match isUnsizedRigidTy 8 (.tuple ks) with
      | true => false
      | false =>
        match l.fields, l.variants with
        | .arbitrary offsets _, .single _ => Nat.beq (length offsets) (length ks)
        | _, _ => false
    | .adt _ _ => layoutValidForResolvedAdt ty.layoutIdx l
    | .closure _ _ => layoutValidForResolvedAdt ty.layoutIdx l
    | .str => false
    | .slice _ => false
    | .dynamic _ => false
    | .foreign _ => false
    | .param _ _ => false
    | .alias _ _ => false
    | .other _ => false

/--
Look up a `LocalDecl` matching `kind` whose explicit `TypeLayout` in `layouts`
satisfies `explicitLayoutConsistent`, returning `(decl.ty.layoutIdx, l)`.
-/
def findConsistentDeclLayout?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (kind : RigidTy) :
    Option (LayoutIdx × TypeLayout) :=
  match isUnsizedRigidTy 8 kind with
  | true => .none
  | false =>
    match localDecls with
    | .nil => .none
    | decl :: rest =>
      match rigidTyEq decl.ty.kind kind with
      | false => findConsistentDeclLayout? rest layouts kind
      | true =>
        match LayoutTable.lookup layouts decl.ty.layoutIdx with
        | .some l =>
          match explicitLayoutConsistent layouts decl.ty l with
          | true => .some (decl.ty.layoutIdx, l)
          | false => findConsistentDeclLayout? rest layouts kind
        | .none => findConsistentDeclLayout? rest layouts kind

/--
Look up the explicit `TypeLayout` annotated on `ty` when `ty.layoutIdx` is in
bounds and satisfies `explicitLayoutConsistent`, never adopting an inconsistent
layout entry.
-/
def consistentExplicitLayout?
    (layouts : LayoutTable)
    (ty : Ty) :
    Option (LayoutIdx × TypeLayout) :=
  match LayoutTable.lookup layouts ty.layoutIdx with
  | .some l =>
    match explicitLayoutConsistent layouts ty l with
    | true => .some (ty.layoutIdx, l)
    | false => .none
  | .none => .none

/--
Resolve a `Ty` to a consistent `(LayoutIdx × TypeLayout)` pair, checking
`ty.layoutIdx` first and falling back to `findConsistentDeclLayout?`.
-/
def resolveConsistentLayout?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Option (LayoutIdx × TypeLayout) :=
  match consistentExplicitLayout? layouts ty with
  | .some pair => .some pair
  | .none => findConsistentDeclLayout? localDecls layouts ty.kind

/--
Target-width- and layout-consistency-aware exact root ABI alignment of `ty : Ty`:
1. Rejects structurally unsized types (`isUnsizedRigidTy 8 ty.kind = true`).
2. Trusts `ty.layoutIdx` ONLY when `explicitLayoutConsistent layouts ty l = true`
   (and `findConsistentDeclLayout?` otherwise).
3. Computes recursive primitive, pointer, array, and tuple alignments directly
   without ever calling `findDeclLayoutForRigidTy` (which does not check
   `explicitLayoutConsistent` or `isUnresolvedLayoutIdx`), failing closed on
   unlaid-out ADTs/closures and non-64-bit platform-dependent alignments unless
   confirmed by a consistent explicit `TypeLayout`.
4. `i128`, `u128`, and `f128` without a consistent `TypeLayout` (explicit or from
   a local of the same type) fail closed (`.none`). The same value serves both
   as the REQUIRED alignment (`copy`, `raw_eq`, `typed_swap_nonoverlapping`) and
   as the GUARANTEED root-allocation alignment (`checkPtrArgAligned`,
   `ptr_mask`), so any fixed guess is unsound in one of the two roles on some
   target: the Reference states these types are often aligned to 4 or 8 bytes.

Reference (The Rust Reference 1.98.0, "Type Layout — Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of a value specifies what addresses are valid to store the value at. A value of alignment n must only be stored at an address that is a multiple of n."

Reference (The Rust Reference 1.98.0, "Type Layout — Primitive data layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.primitive.platform-specific-alignment>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.primitive.size-align>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.pointer.thin>

> "The alignment of primitives is platform-specific. In most cases, their
> alignment is equal to their size, but it may be less. In particular, `i128`
> and `u128` are often aligned to 4 or 8 bytes even though their size is 16, and
> on many 32-bit platforms, `i64`, `u64`, and `f64` are only aligned to 4 bytes,
> not 8."
> "`usize` and `isize` have the same size and alignment."
> "Pointers to sized types have the same size and alignment as `usize`."

Reference (The Rust Reference 1.98.0, "Boolean type" and "Character type"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html#r-type.bool.layout>
<https://doc.rust-lang.org/1.98.0/reference/types/char.html#r-type.char.layout>

> "An object with the boolean type has a size and alignment of 1 each."
> "`char` is guaranteed to have the same size and alignment as `u32` on all platforms."

Reference (The Rust Reference 1.98.0, "Type Layout — Tuple Layout" and "The Rust representation"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.tuple.def>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.tuple.unit>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.repr.rust.layout>

> "Tuples are laid out according to the Rust representation."
> "The exception to this is the unit tuple (()), which is guaranteed as a zero-sized type to have a size of 0 and an alignment of 1."
> "The alignment of the type is at least the maximum alignment of its fields."

Modeling choice (supplied target facts, not documented Rust guarantees): without
a layout entry, 2-byte and 4-byte primitives are taken as size-aligned on targets with
`pointerBits >= 32`, 8-byte primitives, `usize`/`isize`, and thin pointers as
8-aligned only on 64-bit targets, and 1-tuples `(T,)` inherit `T`'s alignment
(matching `rustc`); `>= 2`-field tuples without a consistent explicit or
declaration `TypeLayout` fail closed `.none`, as does every other width.
-/
def exactRootAllocAlignAux?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → Option Nat
  | .zero, _ => .none
  | .succ fuel', ty =>
    match isUnsizedRigidTy 8 ty.kind with
    | true => .none
    | false =>
      match consistentExplicitLayout? layouts ty with
      | .some (_, l) => .some l.align.bytes
      | .none =>
        match findConsistentDeclLayout? localDecls layouts ty.kind with
        | .some (_, l) => .some l.align.bytes
        | .none =>
          let ptrBits :=
            match layouts.pointerBits with
            | 0 => 64
            | n + 1 => n + 1
          let is64 := Nat.beq ptrBits 64
          let isAtLeast32 := Nat.ble 32 ptrBits
          match ty.kind with
          | .bool | .never | .fnDef _ _ | .tuple .nil | .int .i8 | .uint .u8 => .some 1
          | .int .i16 | .uint .u16 | .float .f16 =>
            match isAtLeast32 with | true => .some 2 | false => .none
          | .int .i32 | .uint .u32 | .float .f32 | .char =>
            match isAtLeast32 with | true => .some 4 | false => .none
          | .int .i64 | .uint .u64 | .float .f64 =>
            match is64 with | true => .some 8 | false => .none
          | .int .i128 | .uint .u128 | .float .f128 => .none
          | .int .isize | .uint .usize | .fnPtr _ _ _ _ =>
            match is64 with | true => .some 8 | false => .none
          | .ref _ pt | .rawPtr _ pt =>
            match is64 with
            | false => .none
            | true =>
              match knownWidePointeeTailAux? 8 pt with
              | .some _ => .some 8
              | .none =>
                match ptrPointeeMayBeUnsizedAux 8 pt with
                | false => .some 8
                | true =>
                  match declPtrToPointeeByteSize? localDecls layouts pt with
                  | .some sz =>
                    match Nat.beq sz 8 with | true => .some 8 | false => .none
                  | .none => .none
          | .array elem _ =>
            exactRootAllocAlignAux? localDecls layouts fuel'
              { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
          | .tuple (k :: .nil) =>
            exactRootAllocAlignAux? localDecls layouts fuel'
              { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
          | .tuple _ => .none
          | _ => .none

/--
Target-width- and layout-consistency-aware exact root ABI alignment of `ty : Ty`.
-/
@[reducible]
def exactRootAllocAlign?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Option Nat :=
  exactRootAllocAlignAux? localDecls layouts 8 ty

/--
Target-aware exact ABI byte alignment of `kind : RigidTy`.
-/
@[reducible]
def exactRigidTyAlign?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (kind : RigidTy) :
    Option Nat :=
  exactRootAllocAlign? localDecls layouts { kind := kind, layoutIdx := unresolvedLayoutIdx layouts }

/--
Target-width- and layout-consistency-aware exact byte size of `ty`:
1. Rejects structurally unsized types (`isUnsizedRigidTy 8 ty.kind = true`).
2. Trusts `ty.layoutIdx` only when `explicitLayoutConsistent layouts ty l = true`.
3. Resolves primitive, pointer-width (`layoutPointerBytes`), and confirmed
   custom-DST pointer types directly without 64-bit assumptions.
4. For `>= 2`-field tuples (which use the unspecified Rust representation,
   including field reordering under `-Z randomize-layout`), requires a
   consistent explicit or declaration `TypeLayout` and fails closed `.none`
   otherwise (modeling choice: 1-tuples `(T,)` without a layout entry inherit
   `T`'s byte size, matching `rustc`).

Reference (The Rust Reference 1.98.0, "Type Layout — Size and Alignment",
"Tuple Layout", and "The Rust representation"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.tuple.def>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.tuple.unit>
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#r-layout.repr.rust.layout>

> "The size of a value is the offset in bytes between successive elements in an array with that item type including alignment padding. The size of a value is always a multiple of its alignment."
> "Tuples are laid out according to the Rust representation."
> "The exception to this is the unit tuple (()), which is guaranteed as a zero-sized type to have a size of 0 and an alignment of 1."
> "The only data layout guarantees made by this representation are those required for soundness."
-/
def exactTyByteSizeAux?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → Option Nat
  | .zero, _ => .none
  | .succ fuel', ty =>
    match isUnsizedRigidTy 8 ty.kind with
    | true => .none
    | false =>
      match consistentExplicitLayout? layouts ty with
      | .some (_, l) => .some l.size.bytes
      | .none =>
        let ptrBytes := layoutPointerBytes layouts
        match ty.kind with
        | .bool => .some 1
        | .char => .some 4
        | .never => .some 0
        | .fnDef _ _ => .some 0
        | .tuple .nil => .some 0
        | .int _ => intTyTargetBytes layouts ty.kind
        | .uint _ => intTyTargetBytes layouts ty.kind
        | .float w => .some (floatTyByteWidth w)
        | .fnPtr _ _ _ _ => .some ptrBytes
        | .ref _ pt =>
          match knownWidePointeeTailAux? 8 pt with
          | .some _ => .some (Nat.mul 2 ptrBytes)
          | .none =>
            match ptrPointeeMayBeUnsizedAux 8 pt with
            | false => .some ptrBytes
            | true => declPtrToPointeeByteSize? localDecls layouts pt
        | .rawPtr _ pt =>
          match knownWidePointeeTailAux? 8 pt with
          | .some _ => .some (Nat.mul 2 ptrBytes)
          | .none =>
            match ptrPointeeMayBeUnsizedAux 8 pt with
            | false => .some ptrBytes
            | true => declPtrToPointeeByteSize? localDecls layouts pt
        | .array elem n =>
          match findConsistentDeclLayout? localDecls layouts ty.kind with
          | .some (_, l) => .some l.size.bytes
          | .none =>
            match exactTyByteSizeAux? localDecls layouts fuel'
                { kind := elem, layoutIdx := unresolvedLayoutIdx layouts } with
            | .some esz => .some (Nat.mul esz n)
            | .none => .none
        | .tuple (k :: .nil) =>
          match findConsistentDeclLayout? localDecls layouts ty.kind with
          | .some (_, l) => .some l.size.bytes
          | .none =>
            exactTyByteSizeAux? localDecls layouts fuel'
              { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
        | .tuple ks =>
          match findConsistentDeclLayout? localDecls layouts (.tuple ks) with
          | .some (_, l) => .some l.size.bytes
          | .none => .none
        | .adt _ _ =>
          match findConsistentDeclLayout? localDecls layouts ty.kind with
          | .some (_, l) => .some l.size.bytes
          | .none => .none
        | .closure _ _ =>
          match findConsistentDeclLayout? localDecls layouts ty.kind with
          | .some (_, l) => .some l.size.bytes
          | .none => .none
        | _ => .none

/--
Target-aware exact byte size of `ty : Ty`.
-/
@[reducible]
def exactTyByteSize?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty) :
    Option Nat :=
  exactTyByteSizeAux? localDecls layouts 8 ty

/--
Target-aware exact byte size of `kind : RigidTy` (using `unresolvedLayoutIdx`
so no unrelated `entries[0]` is adopted).
-/
@[reducible]
def exactRigidTyByteSize?
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (kind : RigidTy) :
    Option Nat :=
  exactTyByteSize? localDecls layouts { kind := kind, layoutIdx := unresolvedLayoutIdx layouts }

/--
Test whether `p : ProvenancePtr` is backed by a live or recorded entry in
`mem.borrows`, `mem.globals`, or `mem.fnPtrs`.
-/
@[reducible]
def isBackedPtr (mem : Memory) (p : ProvenancePtr) : Bool :=
  match lookupBorrow mem.borrows p.tag with
  | .some _ => true
  | .none =>
    match lookupGlobalAlloc mem.globals p.allocId with
    | .some _ => true
    | .none =>
      match lookupFnPtr mem.fnPtrs p.allocId with
      | .some _ => true
      | .none => false

/--
Validate that `v` is a well-formed `ptrBytes`-wide thin pointer value (rejecting
over-wide `.scalar` bits and over-wide unbacked `allocId = 0` offsets `≥ 2^(8*ptrBytes)`)
and test whether it is the null pointer (`0`, in either `.scalar ⟨0, ptrBytes⟩`
or unbacked `.ptr ⟨0, 0⟩ ptrBytes` encoding). Returns `.none` if `v` is
malformed.

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "//! * A [null] pointer is *never* valid for reads/writes."
-/
@[reducible]
def isNullThinPtr (mem : Memory) (ptrBytes : Nat) : Value → Option Bool
  | .scalar sv =>
    match Bool.and (Nat.beq sv.sizeBytes ptrBytes) (Nat.blt sv.bits (scalarModulus ptrBytes)) with
    | true => .some (Nat.beq sv.bits 0)
    | false => .none
  | .ptr p sz =>
    match Nat.beq sz ptrBytes with
    | false => .none
    | true =>
      match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
      | true =>
        match Nat.blt p.offsetBytes (scalarModulus ptrBytes) with
        | true => .some (Nat.beq p.offsetBytes 0)
        | false => .none
      | false => .some false
  | _ => .none

/--
Decode a `usize`-typed operand value (`count`, `bytes`, `mask`) on a target with
pointer width `ptrBytes`:
- `.scalar sc` with `sc.sizeBytes == ptrBytes` and `sc.bits < 2^(8*ptrBytes)` =>
  `.ok sc.bits`.
- Provenance-free unbacked `.ptr p ptrBytes` (`p.allocId == 0` and unbacked,
  `p.offsetBytes < 2^(8*ptrBytes)`) => `.ok p.offsetBytes`.
- Provenance-carrying `.ptr p ptrBytes` => `.unsupported` (symbolic allocation
  base address is unknown).
- Wrong width, over-wide bits/offset, or non-scalar/non-pointer `Value` => `.ub`.

Reference (The Rust Reference 1.98.0, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The usize type is an unsigned integer type with the same number of bits as the platform’s pointer type. It can represent every memory address in the process."
-/
@[reducible]
def decodeUsizeArg? (mem : Memory) (ptrBytes : Nat) : Value → MemOpRes Nat
  | .scalar sc =>
    match Bool.and (Nat.beq sc.sizeBytes ptrBytes) (Nat.blt sc.bits (scalarModulus ptrBytes)) with
    | true => .ok sc.bits
    | false => .ub
  | .ptr p sz =>
    match Nat.beq sz ptrBytes with
    | false => .ub
    | true =>
      match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
      | true =>
        match Nat.blt p.offsetBytes (scalarModulus ptrBytes) with
        | true => .ok p.offsetBytes
        | false => .ub
      | false => .unsupported
  | _ => .ub

/--
Check whether `metaVal` is a well-formed wide-pointer metadata component for
pointer width `ptrBytes` (an in-range `ptrBytes`-wide scalar slice length or
well-formed `ptrBytes`-wide vtable pointer).
-/
@[reducible]
def isValidWidePtrMetaValForWidth (mem : Memory) (ptrBytes : Nat) (v : Value) : Bool :=
  match isNullThinPtr mem ptrBytes v with
  | .some _ => true
  | .none => false

/--
Normalize a borrow entry's projection path for a non-zero-sized Tree Borrows
access by truncating at the first enclosing `FieldsShape.union` container
(`truncateTyProjAtUnion`), ensuring accesses through sibling union-field borrows
(e.g., `u.a` vs `u.b`) properly conflict.

Reference (The Rust Reference 1.98.0, "Unions"):
<https://doc.rust-lang.org/1.98.0/reference/items/unions.html>

> "The key property of unions is that all fields of a union share common
> storage. As a result, writes to one field of a union can overwrite its other
> fields, and size of a union is determined by the size of its largest field."
-/
def normalizeAccessBorrowProj
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (targetLocal : Local)
    (proj : List ProjectionElem) :
    List ProjectionElem :=
  match proj with
  | .nil => .nil
  | pHead :: pTail =>
    match placeTouchesUnion targetDecls targetLayouts
        { local_ := targetLocal, projection := pHead :: pTail } with
    | false => pHead :: pTail
    | true =>
      match get? targetDecls targetLocal with
      | .some decl =>
        truncateTyProjAtUnion targetDecls targetLayouts decl.ty (pHead :: pTail)
      | .none => pHead :: pTail

/--
Exact-range, union-truncated Tree Borrows read check and permission transition
for a non-zero read of `[accessOff, accessOff + accessLen)` through `(tag, entry)`.
Uses the exact access interval `(accessOff, accessLen)` rather than widening a
ranged borrow to `(entry.rangeOffset, entry.rangeLen)`.

Reference (MiniRust `spec/mem/tree_borrows/tree.md` at commit
`5f78e227bbe30ae9fb5e1286a772d91a92e3622a`):
<https://github.com/minirust/minirust/blob/5f78e227bbe30ae9fb5e1286a772d91a92e3622a/spec/mem/tree_borrows/tree.md#L89-L125>

> "/// Recusively do state transition on `self` node and all its descendants.
> /// `path` is the path from `self` to the accessed node.
> /// `path` is None when the accessed node is not a descendant of `self`."

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#r-undefined.alias>

> "Breaking the pointer aliasing rules. The exact aliasing rules are not
> determined yet, but here is an outline of the general principles:"

Modeling choice: because the Reference leaves the exact aliasing rules
undetermined, the Tree Borrows transitions applied here (following Miri and
MiniRust, cited above) are a modeling choice of this semantics, not a
documented Rust guarantee.
-/
def borrowsAfterReadAccess
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (tag : Nat)
    (entry : BorrowEntry)
    (accessOff accessLen : Nat) :
    Option (List BorrowEntry) :=
  match entry.perm with
  | .disabled => .none
  | _ =>
    let effProj :=
      normalizeAccessBorrowProj targetDecls targetLayouts entry.targetLocal entry.targetProjection
    match
      hasTreeReadUB
        borrows
        borrows
        activeProtectors
        entry.targetLocal
        (.some tag)
        effProj
        accessOff
        accessLen
        entry.targetFrameDepth
    with
    | true => .none
    | false =>
      .some
        (freezeTreeBorrowsOnReadAtProj
          borrows
          borrows
          entry.targetLocal
          (.some tag)
          effProj
          accessOff
          accessLen
          activeProtectors
          entry.targetFrameDepth)

/--
Exact-range, union-truncated Tree Borrows write check and permission transition
for a non-zero write of `[accessOff, accessOff + accessLen)` through `(tag, entry)`.
Uses the exact access interval `(accessOff, accessLen)` rather than widening a
ranged borrow to `(entry.rangeOffset, entry.rangeLen)`.

Reference (Miri Tree Borrows implementation,
`src/borrow_tracker/tree_borrows/perms.rs` and `tree.rs` at Miri commit
`7fa591d7d4dd9af8154becbc8332f8096f8323b1`):
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/perms.rs#L179-L198>
<https://github.com/rust-lang/miri/blob/7fa591d7d4dd9af8154becbc8332f8096f8323b1/src/borrow_tracker/tree_borrows/tree.rs#L157-L159>

> "ReservedFrz { conflicted: true } if protected => return None,
> ReservedFrz { .. } | ReservedIM | Unique => Unique,
> Frozen | Disabled => return None,"

> "if protected && self.accessed && transition.produces_disabled() {
>     return Err(TransitionError::ProtectedDisabled(old_perm));
> }"

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#r-undefined.alias>

> "Breaking the pointer aliasing rules. The exact aliasing rules are not
> determined yet, but here is an outline of the general principles:"

Modeling choice: the Miri Tree Borrows transitions quoted above are a modeling
choice of this semantics, not a documented Rust guarantee (the Reference leaves
the exact aliasing rules undetermined).
-/
def borrowsAfterWriteAccess
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (targetDecls : List LocalDecl)
    (targetLayouts : LayoutTable)
    (tag : Nat)
    (entry : BorrowEntry)
    (accessOff accessLen : Nat) :
    Option (List BorrowEntry) :=
  let childWriteUB : Bool :=
    match entry.perm with
    | .frozen | .disabled => true
    | .reservedFrz true => isBorrowProtected activeProtectors entry
    | _ => false
  match childWriteUB with
  | true => .none
  | false =>
    let ancWriteUB : Bool :=
      match borrows with
      | _ :: _ :: _ => treeBorrowAncestorsChildAccessUB .write borrows entry.parentTag
      | _ => false
    match ancWriteUB with
    | true => .none
    | false =>
      let effProj :=
        normalizeAccessBorrowProj
          targetDecls targetLayouts entry.targetLocal entry.targetProjection
      let protConflict : Bool :=
        match activeProtectors with
        | .nil => false
        | _ :: _ =>
          match borrows with
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            hasProtectedTreeWriteConflict
              allBorrows
              allBorrows
              activeProtectors
              entry.targetLocal
              (.some tag)
              effProj
              accessOff
              accessLen
              entry.targetFrameDepth
          | _ =>
            hasProtectedWriteConflict
              borrows
              activeProtectors
              entry.targetLocal
              (.some tag)
              effProj
              accessOff
              accessLen
              entry.targetFrameDepth
      match protConflict with
      | true => .none
      | false =>
        let borrows' : List BorrowEntry :=
          match borrows with
          | .nil => .nil
          | single :: .nil =>
            invalidateConflictingBorrowsAtProj
              (single :: .nil)
              entry.targetLocal
              (.some tag)
              effProj
              accessOff
              accessLen
              entry.targetFrameDepth
          | b₁ :: b₂ :: restBorrows =>
            let allBorrows := b₁ :: b₂ :: restBorrows
            invalidateTreeBorrowsAtProj
              allBorrows
              allBorrows
              entry.targetLocal
              (.some tag)
              effProj
              accessOff
              accessLen
              entry.targetFrameDepth
        .some borrows'

/--
Test whether an untyped `Value` (such as a caller-owned referent without a
`LocalDecl`) is leaf- or homogeneous-flat-array-shaped so its byte size and raw
byte image are uniquely determined without hidden struct/tuple padding.
-/
def untypedValueHasExactByteImage : Nat → Value → Bool
  | .zero, _ => false
  | .succ _, .unit => true
  | .succ _, .scalar sv => Nat.blt 0 sv.sizeBytes
  | .succ _, .ptr _ sz => Nat.blt 0 sz
  | .succ _, .aggregate varIdx fields =>
    match Nat.beq varIdx 0 with
    | false => false
    | true =>
      match fields with
      | .nil => true
      | _ :: _ => isHomogeneousUntypedFields fields

/--
Resolved live memory allocation endpoint for a dereferenceable pointer argument
in `copy`, `compare_bytes`, `raw_eq`, and `typed_swap_nonoverlapping`.

Carries `tagWindow : Option (Nat × Nat)`, the exact half-open byte interval
`[winStart, winEnd)` covered by the borrow tag (intersecting explicit range
bounds `[entry.rangeOffset, min (rangeOffset + rangeLen) allocSize)` with the
projected sub-place `[placeOff, placeOff + placeSize)` when both are present).
-/
structure ResolvedMemEndpoint : Type where
  /-- Owning stack local or global allocation identity. -/
  allocKey : AllocKey
  /-- Total size of the owning root allocation in bytes. -/
  allocSize : Nat
  /-- Effective byte offset of the pointer from the start of the root allocation. -/
  effOff : Nat
  /-- Byte window `[winStart, winEnd)` tracked by the borrow tag, or `.none` if undetermined. -/
  tagWindow : Option (Nat × Nat)
  /-- Stack borrow `(tag, entry)` if stack-backed; `.none` for globals. -/
  borrow? : Option (Nat × BorrowEntry)
  /-- Backing global allocation if global-backed; `.none` for stack locals. -/
  globalAlloc? : Option CapturedAllocation
  /-- `LocalDecl` table of the owning frame. -/
  targetDecls : List LocalDecl
  /-- `LayoutTable` of the owning frame. -/
  targetLayouts : LayoutTable
  /-- Declared root type of the stack local, if available. -/
  rootTy? : Option Ty
  /-- Current root `LocalSlot` of the stack local, if stack-backed. -/
  rootSlot? : Option LocalSlot
  /-- Known guaranteed ABI alignment of the root allocation, if determined. -/
  rootAlign? : Option Nat

/--
Resolve a pointer `p : ProvenancePtr` to a live stack or global
`ResolvedMemEndpoint`:
- Deallocated stack borrows (`entry.allocDead = true`, set by `StorageDead` and
  frame teardown) fault immediately with `.ub` BEFORE inspecting
  `(entry.targetFrameDepth, entry.targetLocal)`, preventing a dangling pointer
  from aliasing a later callee's live local at the same depth/index and masking
  dangling-pointer `.ub` as `.unsupported`.
- Dead or out-of-frame stack locals and unbacked/non-existent allocations fault
  with `.ub`.
- Stack locals whose projection offset or root allocation size cannot be
  determined cleanly (including padded untyped caller referents) fail closed
  with `.unsupported`.
- Computes `tagWindow` by intersecting any explicit `[rangeOffset, rangeEnd)`
  borrow range with the projected sub-place `[placeOff, placeOff + placeSize)`
  computed via `exactTyByteSize?`.

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L21-L25>

> "//! * For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that
> //!   the pointer be *dereferenceable*. The [provenance] of the pointer is used to determine which
> //!   [allocation] it is derived from; a pointer is dereferenceable if the memory range of the given
> //!   size starting at the pointer is entirely contained within the bounds of that allocation. Note
> //!   that in Rust, every (stack-allocated) variable is considered a separate allocation."
-/
def resolveLiveMemEndpoint
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (p : ProvenancePtr) :
    MemOpRes ResolvedMemEndpoint :=
  match lookupBorrow s.memory.borrows p.tag with
  | .some entry =>
    match entry.allocDead with
    | true => .ub
    | false =>
      match
        readFrameLocalSlot
          locals
          s.memory.callStack
          s.memory.callerLocals
          entry.targetFrameDepth
          entry.targetLocal
      with
      | .none => .ub
      | .some .dead => .ub
      | .some slot =>
        let (targetDecls, targetLayouts) : List LocalDecl × LayoutTable :=
          match activeFrameSlot? locals s.memory.callStack entry.targetFrameDepth entry.targetLocal with
          | .some _ => (bodyLocalDecls, bodyLayouts)
          | .none =>
            foreignFrameDeclsAndLayouts
              s.memory.callStack
              bodyLayouts
              entry.targetFrameDepth
              entry.targetLocal
        let rootTy? : Option Ty :=
          match get? targetDecls entry.targetLocal with
          | .some decl => .some decl.ty
          | .none => .none
        match
          borrowPlaceByteOffset?
            locals
            s.memory.callerLocals
            bodyLocalDecls
            bodyLayouts
            entry
            s.memory.callStack
        with
        | .none => .unsupported
        | .some placeOff =>
          let rootSizeOpt : Option Nat :=
            match rootTy? with
            | .some rTy => exactTyByteSize? targetDecls targetLayouts rTy
            | .none =>
              match slot with
              | .init rootVal =>
                match untypedValueHasExactByteImage defaultCodecFuel rootVal with
                | true => valueDefaultByteSize rootVal
                | false => .none
              | _ => .none
          match rootSizeOpt with
          | .none => .unsupported
          | .some allocSize =>
            let normProj :=
              normalizeSubsliceProjections (stripTransparentProjections entry.targetProjection)
            let projWinOpt : Option (Nat × Nat) :=
              match normProj with
              | .nil => .some (0, allocSize)
              | _ :: _ =>
                match
                  placeTyResolved targetDecls targetLayouts
                    { local_ := entry.targetLocal, projection := entry.targetProjection }
                with
                | .none => .none
                | .some placeTy =>
                  match exactTyByteSize? targetDecls targetLayouts placeTy with
                  | .none => .none
                  | .some pSz =>
                    match Nat.ble (Nat.add placeOff pSz) allocSize with
                    | true => .some (placeOff, Nat.add placeOff pSz)
                    | false => .none
            let tagWindow : Option (Nat × Nat) :=
              match Nat.blt 0 entry.rangeLen with
              | false => projWinOpt
              | true =>
                let rStart := entry.rangeOffset
                let rEnd := minNat (Nat.add entry.rangeOffset entry.rangeLen) allocSize
                match projWinOpt with
                | .none => .none
                | .some (pStart, pEnd) =>
                  let iStart := maxNat rStart pStart
                  let iEnd := minNat rEnd pEnd
                  match Nat.ble iStart iEnd with
                  | true => .some (iStart, iEnd)
                  | false => .some (iStart, iStart)
            let rootAlign? : Option Nat :=
              match rootTy? with
              | .some rTy => exactRootAllocAlign? targetDecls targetLayouts rTy
              | .none => .none
            .ok {
              allocKey := .stack entry.targetFrameDepth entry.targetLocal
              allocSize := allocSize
              effOff := Nat.add placeOff p.offsetBytes
              tagWindow := tagWindow
              borrow? := .some (p.tag, entry)
              globalAlloc? := .none
              targetDecls := targetDecls
              targetLayouts := targetLayouts
              rootTy? := rootTy?
              rootSlot? := .some slot
              rootAlign? := rootAlign?
            }
  | .none =>
    match lookupGlobalAlloc s.memory.globals p.allocId with
    | .some gAlloc =>
      let allocSize := length gAlloc.bytes
      let gAlign? :=
        match Align.isPowerOfTwoBytes gAlloc.align with
        | true => .some gAlloc.align.bytes
        | false => .none
      .ok {
        allocKey := .global gAlloc.allocId
        allocSize := allocSize
        effOff := p.offsetBytes
        tagWindow := .some (0, allocSize)
        borrow? := .none
        globalAlloc? := .some gAlloc
        targetDecls := bodyLocalDecls
        targetLayouts := bodyLayouts
        rootTy? := .none
        rootSlot? := .none
        rootAlign? := gAlign?
      }
    | .none => .ub

/--
Three-way allocation-bounds and Tree Borrows tag-window check for an access of
`accessLen` bytes at `ep.effOff`:
- Outside `[0, ep.allocSize]` => `.ub` (not dereferenceable).
- Inside `[0, ep.allocSize]` with `accessLen = 0` => `.ok ()`.
- Inside `[0, ep.allocSize]` with `accessLen > 0` and inside `ep.tagWindow` =>
  `.ok ()`.
- Inside `[0, ep.allocSize]` with `accessLen > 0` but outside `ep.tagWindow` (or
  undetermined `tagWindow`) => `.unsupported` (Tree Borrows permits in-alloc
  out-of-subplace accesses, but per-tag permissions cannot track sibling conflicts).

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L21-L25>

> "//! * For a pointer to be valid for reads/writes, it is necessary, but not always sufficient, that
> //!   the pointer be *dereferenceable*. The [provenance] of the pointer is used to determine which
> //!   [allocation] it is derived from; a pointer is dereferenceable if the memory range of the given
> //!   size starting at the pointer is entirely contained within the bounds of that allocation."
-/
@[reducible]
def endpointAccessCheck (ep : ResolvedMemEndpoint) (accessLen : Nat) : MemOpRes Unit :=
  match Nat.ble (Nat.add ep.effOff accessLen) ep.allocSize with
  | false => .ub
  | true =>
    match Nat.beq accessLen 0 with
    | true => .ok ()
    | false =>
      match ep.tagWindow with
      | .none => .unsupported
      | .some (winStart, winEnd) =>
        match
          Bool.and
            (Nat.ble winStart ep.effOff)
            (Nat.ble (Nat.add ep.effOff accessLen) winEnd)
        with
        | true => .ok ()
        | false => .unsupported

/--
Three-way symbolic alignment check for a thin pointer argument `ptrVal` against
required alignment `reqAlign` (a positive power of two):
- Alignment `≤ 1` always holds for any valid `ptrBytes`-wide thin pointer.
- For stack borrows, uses the exact symbolic criterion on the root allocation's
  guaranteed alignment `rootAlign` (`exactRootAllocAlign?`) and total offset
  `effOff = placeOff + p.offsetBytes`: `reqAlign ≤ rootAlign ∧ effOff % reqAlign == 0`
  => `.ok ()`; definite misalignment (`effOff % reqAlign ≠ 0` or known
  `rootAlign < reqAlign`) => `.ub`; unknown `rootAlign` with `effOff % reqAlign == 0`
  => `.unsupported`.
- For globals, applies the same exact criterion to `gAlloc.align.bytes` and
  `p.offsetBytes`.
- For provenance-free integer pointers (`.scalar` or unbacked `allocId == 0`),
  checks `addr % reqAlign == 0` directly (so aligned null passes for 0-byte
  `copy`, while misaligned addresses fault `.ub`).
- For unknown unbacked `allocId ≠ 0`, faults `.ub` when `nonZeroAccess = true`
  or `p.offsetBytes % reqAlign ≠ 0`, and fails closed `.unsupported` otherwise.
- For a stack borrow whose allocation is deallocated (`entry.allocDead = true`),
  faults `.ub` when `nonZeroAccess = true` (a dangling pointer is not
  dereferenceable) and fails closed `.unsupported` otherwise: after a frame pop
  the same `(targetFrameDepth, targetLocal)` may name an unrelated local of a
  later callee, so neither the root alignment nor the place offset of the dead
  allocation can be recovered from the current declarations (modeling choice).

Reference (The Rust Reference 1.98.0, "Type Layout — Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The alignment of a value specifies what addresses are valid to store the value at. A value of alignment n must only be stored at an address that is a multiple of n."
-/
def checkPtrArgAligned
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrVal : Value)
    (reqAlign : Nat)
    (nonZeroAccess : Bool) :
    MemOpRes Unit :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  let modW := scalarModulus ptrBytes
  match ptrVal with
  | .scalar sv =>
    match Bool.and (Nat.beq sv.sizeBytes ptrBytes) (Nat.blt sv.bits modW) with
    | false => .ub
    | true =>
      match Nat.ble reqAlign 1 with
      | true => .ok ()
      | false =>
        match Nat.beq (Nat.mod sv.bits reqAlign) 0 with
        | true => .ok ()
        | false => .ub
  | .ptr p sz =>
    match Nat.beq sz ptrBytes with
    | false => .ub
    | true =>
      let isUnbackedInt :=
        Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr s.memory p))
      match Bool.and isUnbackedInt (Bool.not (Nat.blt p.offsetBytes modW)) with
      | true => .ub
      | false =>
        match Nat.ble reqAlign 1 with
        | true => .ok ()
        | false =>
          match lookupBorrow s.memory.borrows p.tag with
          | .some entry =>
            match entry.allocDead with
            | true =>
              match nonZeroAccess with
              | true => .ub
              | false => .unsupported
            | false =>
              let deadSlotUb : Bool :=
                match nonZeroAccess with
                | false => false
                | true =>
                  match
                    readFrameLocalSlot
                      locals s.memory.callStack s.memory.callerLocals
                      entry.targetFrameDepth entry.targetLocal
                  with
                  | .none => true
                  | .some .dead => true
                  | .some _ => false
              match deadSlotUb with
              | true => .ub
              | false =>
                match
                  borrowPlaceByteOffset?
                    locals
                    s.memory.callerLocals
                    bodyLocalDecls
                    bodyLayouts
                    entry
                    s.memory.callStack
                with
                | .none => .unsupported
                | .some placeOff =>
                  let effOff := Nat.add placeOff p.offsetBytes
                  let (targetDecls, targetLayouts) : List LocalDecl × LayoutTable :=
                    match
                      frameLocalDeclsAndLayoutsAtDepth
                        s.memory.callStack
                        bodyLocalDecls
                        bodyLayouts
                        entry.targetFrameDepth
                    with
                    | .some pair => pair
                    | .none =>
                      foreignFrameDeclsAndLayouts
                        s.memory.callStack
                        bodyLayouts
                        entry.targetFrameDepth
                        entry.targetLocal
                  let rootAlign? : Option Nat :=
                    match get? targetDecls entry.targetLocal with
                    | .some rootDecl => exactRootAllocAlign? targetDecls targetLayouts rootDecl.ty
                    | .none => .none
                  match rootAlign? with
                  | .some rootAlign =>
                    match Bool.and (Nat.ble reqAlign rootAlign) (Nat.beq (Nat.mod effOff reqAlign) 0) with
                    | true => .ok ()
                    | false => .ub
                  | .none =>
                    match Nat.beq (Nat.mod effOff reqAlign) 0 with
                    | false => .ub
                    | true => .unsupported
          | .none =>
            match lookupGlobalAlloc s.memory.globals p.allocId with
            | .some gAlloc =>
              match Align.isPowerOfTwoBytes gAlloc.align with
              | true =>
                match
                  Bool.and
                    (Nat.ble reqAlign gAlloc.align.bytes)
                    (Nat.beq (Nat.mod p.offsetBytes reqAlign) 0)
                with
                | true => .ok ()
                | false => .ub
              | false =>
                match Nat.beq (Nat.mod p.offsetBytes reqAlign) 0 with
                | false => .ub
                | true => .unsupported
            | .none =>
              match isUnbackedInt with
              | true =>
                match Nat.beq (Nat.mod p.offsetBytes reqAlign) 0 with
                | true => .ok ()
                | false => .ub
              | false =>
                match nonZeroAccess with
                | true => .ub
                | false =>
                  match Nat.beq (Nat.mod p.offsetBytes reqAlign) 0 with
                  | false => .ub
                  | true => .unsupported
  | _ => .ub

/-! ### Exact Abstract-Byte Storage Codec, Layout Data Mask, Padding Reset & Round-Trip Commit -/

/--
Structural equality on optional `PtrByteFrag` byte provenance.
-/
@[reducible]
def optProvEq : Option PtrByteFrag → Option PtrByteFrag → Bool
  | .none, .none => true
  | .some f1, .some f2 => PtrByteFrag.beq f1 f2
  | _, _ => false

/--
Elementwise exact equality on `List AbstractByte`.
-/
def abstractBytesEq : List AbstractByte → List AbstractByte → Bool
  | .nil, .nil => true
  | a :: as, b :: bs =>
    match abstractByteEq a b with
    | true => abstractBytesEq as bs
    | false => false
  | _, _ => false

/--
Byte-level refinement `stored ⊑ written`: `stored` either equals `written`
(same byte and provenance) or is `.uninit` (demoting an initialized byte to
uninitialized can only add UB on subsequent raw reads, never lose UB).
-/
@[reducible]
def abstractByteRefines : AbstractByte → AbstractByte → Bool
  | .uninit, _ => true
  | .init b1 p1, .init b2 p2 =>
    Bool.and (Nat.beq b1.toBitVec.toNat b2.toBitVec.toNat) (optProvEq p1 p2)
  | .init _ _, .uninit => false

/--
Elementwise refinement `stored ⊑ written` on equal-length `List AbstractByte`s.
-/
def abstractBytesRefine : List AbstractByte → List AbstractByte → Bool
  | .nil, .nil => true
  | a :: as, b :: bs =>
    match abstractByteRefines a b with
    | true => abstractBytesRefine as bs
    | false => false
  | _, _ => false

/--
Test whether every byte in `bytes` is `AbstractByte.uninit`.
-/
def allBytesUninit : List AbstractByte → Bool
  | .nil => true
  | .uninit :: rest => allBytesUninit rest
  | .init _ _ :: _ => false

/--
Helper verifying all remaining bytes are `.init _ expectedProv`.
-/
def allBytesMatchProv (expectedProv : Option PtrByteFrag) : List AbstractByte → Bool
  | .nil => true
  | .uninit :: _ => false
  | .init _ p :: rest =>
    match optProvEq expectedProv p with
    | true => allBytesMatchProv expectedProv rest
    | false => false

/--
Helper verifying every byte in `bytes` is initialized with `.none` provenance.
-/
def allBytesMatchNone : List AbstractByte → Bool
  | .nil => true
  | .init _ .none :: rest => allBytesMatchNone rest
  | _ :: _ => false

/--
Check that every byte in non-empty `bytes` is either initialized with `.none`
provenance (`allBytesMatchNone`) or forms a strictly coherent UCG #558 pointer
byte image (`abstractBytesCoherentPtrProv?`), returning `.none` on any `.uninit`
byte or fragmented/reversed/spliced provenance.
-/
def allBytesSameProv : List AbstractByte → Option (Option (Nat × Nat))
  | .nil => .none
  | b :: rest =>
    let bytes := b :: rest
    match allBytesMatchNone bytes with
    | true => .some .none
    | false =>
      match abstractBytesCoherentPtrProv? bytes with
      | .some frag => .some (.some (frag.allocId, frag.tag))
      | .none => .none

/--
Test whether any byte in `bytes` carries real allocation provenance (excluding
unbacked `allocId = 0` bytes with no backing borrow/global/fnPtr).
-/
def bytesHaveRealProvenance (mem : Memory) : List AbstractByte → Bool
  | .nil => false
  | .uninit :: rest => bytesHaveRealProvenance mem rest
  | .init _ .none :: rest => bytesHaveRealProvenance mem rest
  | .init _ (.some frag) :: rest =>
    match Bool.and (Nat.beq frag.allocId 0) (Bool.not (isBackedPtr mem { allocId := 0, offsetBytes := 0 })) with
    | true => bytesHaveRealProvenance mem rest
    | false => true

/--
Extract concrete `UInt8` bytes from an initialized, provenance-free byte slice.
-/
def extractRawU8Bytes : List AbstractByte → Option (List UInt8)
  | .nil => .some .nil
  | .uninit :: _ => .none
  | .init b _ :: rest =>
    match extractRawU8Bytes rest with
    | .some bs => .some (b :: bs)
    | .none => .none

/--
Strip provenance from `bytes` for `compare_bytes` and `raw_eq`, checking
initialization across the ENTIRE slice FIRST (so any `.uninit` byte faults `.ub`
even if an earlier byte carries provenance), then failing closed `.unsupported`
if any byte carries real allocation provenance.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2307-L2313>

> "/// It's UB to call this if any of the *bytes* in `*a` or `*b` are uninitialized.
> /// Note that this is a stricter criterion than just the *values* being
> /// fully-initialized: if `T` has padding, it's UB to call this intrinsic.
> ///
> /// At compile-time, it is furthermore UB to call this if any of the bytes
> /// in `*a` or `*b` have provenance."
-/
def stripProvenanceBytes (mem : Memory) (bytes : List AbstractByte) : MemOpRes (List UInt8) :=
  match hasUninitByte bytes with
  | true => .ub
  | false =>
    match bytesHaveRealProvenance mem bytes with
    | true => .unsupported
    | false =>
      match extractRawU8Bytes bytes with
      | .some raw => .ok raw
      | .none => .ub

/--
Encode a `ProvenancePtr` of byte width `sz` in little-endian order, attaching
`.none` provenance for unbacked `allocId = 0` integer addresses and
`.some (p.allocId, p.tag)` for provenance-carrying pointers.
-/
@[reducible]
def encodePtrRawBytes (mem : Memory) (p : ProvenancePtr) (sz : Nat) : Option (List AbstractByte) :=
  let prov : Option (Nat × Nat) :=
    match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
    | true => .none
    | false => .some (p.allocId, p.tag)
  encodeScalarBytes ⟨p.offsetBytes, sz⟩ prov

/--
Check that a 2-field `.scalarPair s0 s1` layout without `fieldLayouts` genuinely
places its two scalars in memory order (`[0, 1]` or `[1, 0]`) at offsets
`(firstOff, secondOff)` satisfying `firstOff = 0 ∧ 0 < sz0 ∧ 0 < sz1 ∧
sz0 ≤ secondOff < sz0 + sz1 ∧ secondOff + sz1 ≤ totalSize`, separating true
scalar-pair fields from trailing ZST fields after a nested pair.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1793-L1808>

> "pub enum BackendRepr {
>     Scalar(Scalar),
>     ScalarPair(Scalar, Scalar),"
-/
def scalarPairOffsetsValid
    (layouts : LayoutTable)
    (offsets : List Size)
    (memIdx : List Nat)
    (s0 s1 : ScalarLayout)
    (totalSize : Nat) :
    Option (Nat × Nat × Nat × Nat × Bool) :=
  match offsets, scalarLayoutTargetByteWidth layouts s0, scalarLayoutTargetByteWidth layouts s1 with
  | off0 :: off1 :: .nil, .some sz0, .some sz1 =>
    let pair? : Option (Nat × Nat × Bool) :=
      match memIdx with
      | 0 :: 1 :: .nil => .some (off0.bytes, off1.bytes, false)
      | 1 :: 0 :: .nil => .some (off1.bytes, off0.bytes, true)
      | _ => .none
    match pair? with
    | .none => .none
    | .some (firstOff, secondOff, swapped) =>
      match
        Bool.and (Nat.beq firstOff 0)
          (Bool.and (Nat.blt 0 sz0)
            (Bool.and (Nat.blt 0 sz1)
              (Bool.and (Nat.ble sz0 secondOff)
                (Bool.and (Nat.blt secondOff (Nat.add sz0 sz1))
                  (Nat.ble (Nat.add secondOff sz1) totalSize)))))
      with
      | true => .some (firstOff, sz0, secondOff, sz1, swapped)
      | false => .none
  | _, _, _ => .none

/--
Write each field value into `buf` at `offsets[i]` using `encodeField` and
strictly verifying that each field's encoded byte length equals `expectedLen`.
-/
def encodeFieldsAtOffsetsExactWith
    (encodeField : Nat → Value → Option (List AbstractByte))
    (expectedLen : Nat → Option Nat) :
    List Size → List Nat → List Value → List AbstractByte → Option (List AbstractByte)
  | .nil, .nil, .nil, buf => .some buf
  | off :: restOffs, fIdx :: restIdxs, fv :: restVals, buf =>
    match encodeField fIdx fv, expectedLen fIdx with
    | .some fBytes, .some expSz =>
      match Nat.beq (length fBytes) expSz with
      | false => .none
      | true =>
        match writeAbstractBytesAt buf off.bytes fBytes with
        | .none => .none
        | .some buf' =>
          encodeFieldsAtOffsetsExactWith
            encodeField expectedLen restOffs restIdxs restVals buf'
    | _, _ => .none
  | _, _, _, _ => .none

/--
Encode elements of a homogeneous flat untyped array of known element byte size.
-/
def encodeUntypedFlatElemsExact
    (mem : Memory)
    (elemSz : Nat) :
    List Value → Option (List AbstractByte)
  | .nil => .some .nil
  | v :: rest =>
    let elemBs? : Option (List AbstractByte) :=
      match v with
      | .unit =>
        match Nat.beq elemSz 0 with
        | true => .some .nil
        | false => .none
      | .scalar sv =>
        match Nat.beq sv.sizeBytes elemSz with
        | true => encodeScalarBytes sv .none
        | false => .none
      | .ptr p sz =>
        match Nat.beq sz elemSz with
        | true => encodePtrRawBytes mem p sz
        | false => .none
      | .aggregate _ _ => .none
    match elemBs?, encodeUntypedFlatElemsExact mem elemSz rest with
    | .some eb, .some rb => .some (appendAbstractBytes eb rb)
    | _, _ => .none

/--
Encode an untyped value only when it is a leaf (`.unit`, `.scalar`, `.ptr`) or a
homogeneous flat array of equal-size leaves (no hidden struct/tuple padding).
-/
def encodeUntypedLeafOrArrayExact (mem : Memory) (v : Value) : Option (List AbstractByte) :=
  match v with
  | .unit => .some .nil
  | .scalar sv => encodeScalarBytes sv .none
  | .ptr p sz => encodePtrRawBytes mem p sz
  | .aggregate varIdx fields =>
    match Nat.beq varIdx 0 with
    | false => .none
    | true =>
      match fields with
      | .nil => .some .nil
      | v0 :: _ =>
        match isHomogeneousUntypedFields fields, flatValueByteSize? v0 with
        | true, .some elemSz => encodeUntypedFlatElemsExact mem elemSz fields
        | _, _ => .none

/--
Encode an array's elements at `elemLIdx` with stride `stride` into `buf` starting
at `curOff`.
-/
def encodeArrayElemsAtLayoutIdx
    (encodeElem : Value → Option (List AbstractByte))
    (elemSize stride curOff : Nat) :
    List Value → List AbstractByte → Option (List AbstractByte)
  | .nil, buf => .some buf
  | ev :: rest, buf =>
    match encodeElem ev with
    | .none => .none
    | .some eb =>
      match Nat.beq (length eb) elemSize with
      | false => .none
      | true =>
        match writeAbstractBytesAt buf curOff eb with
        | .none => .none
        | .some buf' =>
          encodeArrayElemsAtLayoutIdx encodeElem elemSize stride (Nat.add curOff stride) rest buf'

/--
Concatenate two `List Bool`s.
-/
@[reducible]
def appendBoolList : List Bool → List Bool → List Bool
  | .nil, ys => ys
  | x :: xs, ys => x :: appendBoolList xs ys

/--
Repeat a `List Bool` `count` times.
-/
def repeatBoolList (chunk : List Bool) : Nat → List Bool
  | .zero => .nil
  | .succ n => appendBoolList chunk (repeatBoolList chunk n)

/--
Bitwise-OR `patch` onto `base` starting at byte offset `off`, returning `.none`
if `off + length patch > length base`.
-/
def orBoolListAt : List Bool → Nat → List Bool → Option (List Bool)
  | base, _, .nil => .some base
  | .nil, _, _ :: _ => .none
  | b :: rest, .zero, p :: pRest =>
    match orBoolListAt rest .zero pRest with
    | .some tail' => .some (Bool.or b p :: tail')
    | .none => .none
  | b :: rest, .succ off, patch =>
    match orBoolListAt rest off patch with
    | .some tail' => .some (b :: tail')
    | .none => .none

/--
Fold `orBoolListAt` over `FieldsShape.arbitrary` fields.
-/
def arbitraryFieldsDataMask
    (fieldMask : Nat → Option (List Bool)) :
    List Size → List Nat → List Bool → Option (List Bool)
  | .nil, .nil, acc => .some acc
  | off :: restOffs, fIdx :: restIdxs, acc =>
    match fieldMask fIdx with
    | .none => .none
    | .some fm =>
      match orBoolListAt acc off.bytes fm with
      | .none => .none
      | .some acc' => arbitraryFieldsDataMask fieldMask restOffs restIdxs acc'
  | _, _, _ => .none

/--
Fold `orBoolListAt` at offset `0` over `FieldsShape.union` field layouts
(computing the union of all fields' data byte positions, so bytes that are
padding in every field remain `false` and get reset to `.uninit`).
-/
def unionFieldsDataMask
    (fieldMask : Nat → Option (List Bool)) :
    List Nat → List Bool → Option (List Bool)
  | .nil, acc => .some acc
  | fIdx :: restIdxs, acc =>
    match fieldMask fIdx with
    | .none => .none
    | .some fm =>
      match orBoolListAt acc 0 fm with
      | .none => .none
      | .some acc' => unionFieldsDataMask fieldMask restIdxs acc'

/--
Compute the exact data-vs-padding mask (`true` = data byte kept by a typed copy,
`false` = padding byte reset to `.uninit`) for `layouts.entries[lIdx]`, aligned
with `lean-miri`'s `unionRanges` (`ValidityVisitor.lean`) and `rustc`'s
`union_data_range_uncached`:
- Uninhabited union fields contribute an all-`false` mask so inhabited unions
  containing an uninhabited field (`union U { a: u32, b: ! }`) remain exact.
- Unions without `fieldLayouts` fail closed (`.none`) unless they have a
  full-width `.scalar (.initialized _ _)` ABI (never accepting `.scalar (.union _)`
  without `fieldLayouts`).
- The scalar-array fast path fires ONLY when `elemFl.isUninhabited == false`,
  `elemFl.variants = .single _`, `elemFl.backendRepr = .scalar (.initialized pk r)`,
  and `scalarLayoutTargetByteWidth = elemFl.size.bytes = stride.bytes` (zero
  internal or stride padding).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2545-L2563>

> "/// Non-overlapping *typed* swap of a single value.
> ...
> /// * The memory pointed by `x` and `y` must both contain values of type `T`."
-/
def layoutDataMask (layouts : LayoutTable) : Nat → LayoutIdx → Option (List Bool)
  | .zero, _ => .none
  | .succ fuel', lIdx =>
    match LayoutTable.lookup layouts lIdx with
    | .none => .none
    | .some l =>
      match TypeLayout.isWellFormed l with
      | false => .none
      | true =>
        match l.isUninhabited with
        | true => .some (replicateBool l.size.bytes false)
        | false =>
          match l.variants with
          | .empty => .some (replicateBool l.size.bytes false)
          | .multiple _ _ _ => .none
          | .single _ =>
            match l.fields with
            | .primitive =>
              match Nat.beq l.size.bytes 0 with
              | true => .some .nil
              | false =>
                match l.backendRepr with
                | .scalar (.initialized pk r) =>
                  match scalarLayoutTargetByteWidth layouts (.initialized pk r) with
                  | .some w =>
                    match Nat.beq w l.size.bytes with
                    | true => .some (replicateBool l.size.bytes true)
                    | false => .none
                  | .none => .none
                | _ => .none
            | .arbitrary .nil _ => .some (replicateBool l.size.bytes false)
            | .arbitrary offsets memIdx =>
              match Nat.beq (length l.fieldLayouts) (length offsets) with
              | true =>
                arbitraryFieldsDataMask
                  (fun fIdx => layoutDataMask layouts fuel' fIdx)
                  offsets
                  l.fieldLayouts
                  (replicateBool l.size.bytes false)
              | false =>
                match offsets, l.backendRepr with
                | off0 :: .nil, .scalar (.initialized pk0 r0) =>
                  match scalarLayoutTargetByteWidth layouts (.initialized pk0 r0) with
                  | .some sz0 =>
                    orBoolListAt
                      (replicateBool l.size.bytes false)
                      off0.bytes
                      (replicateBool sz0 true)
                  | .none => .none
                | off0 :: off1 :: .nil, .scalarPair (.initialized pk0 r0) (.initialized pk1 r1) =>
                  match
                    scalarPairOffsetsValid
                      layouts (off0 :: off1 :: .nil) memIdx
                      (.initialized pk0 r0) (.initialized pk1 r1) l.size.bytes
                  with
                  | .some (firstOff, sz0, secondOff, sz1, _) =>
                    match
                      orBoolListAt
                        (replicateBool l.size.bytes false)
                        firstOff
                        (replicateBool sz0 true)
                    with
                    | .some m1 => orBoolListAt m1 secondOff (replicateBool sz1 true)
                    | .none => .none
                  | .none => .none
                | _, _ => .none
            | .array stride count =>
              match Nat.beq count 0 with
              | true =>
                match Nat.beq l.size.bytes 0 with
                | true => .some .nil
                | false => .none
              | false =>
                match Nat.beq l.size.bytes (Nat.mul stride.bytes count) with
                | false => .none
                | true =>
                  match l.fieldLayouts with
                  | .nil => .none
                  | elemLIdx :: _ =>
                    match LayoutTable.lookup layouts elemLIdx with
                    | .none => .none
                    | .some elemFl =>
                      let fastPath : Bool :=
                        match elemFl.isUninhabited, elemFl.variants, elemFl.backendRepr with
                        | false, .single _, .scalar (.initialized pk r) =>
                          match scalarLayoutTargetByteWidth layouts (.initialized pk r) with
                          | .some w =>
                            Bool.and
                              (Nat.beq elemFl.size.bytes stride.bytes)
                              (Nat.beq w elemFl.size.bytes)
                          | .none => false
                        | _, _, _ => false
                      match fastPath with
                      | true => .some (replicateBool l.size.bytes true)
                      | false =>
                        match layoutDataMask layouts fuel' elemLIdx with
                        | .none => .none
                        | .some elemMask =>
                          match Nat.ble (length elemMask) stride.bytes with
                          | false => .none
                          | true =>
                            let paddedElem :=
                              appendBoolList
                                elemMask
                                (replicateBool (Nat.sub stride.bytes (length elemMask)) false)
                            .some (repeatBoolList paddedElem count)
            | .union _ =>
              match l.fieldLayouts with
              | fHead :: fTail =>
                unionFieldsDataMask
                  (fun fIdx => layoutDataMask layouts fuel' fIdx)
                  (fHead :: fTail)
                  (replicateBool l.size.bytes false)
              | .nil =>
                match l.backendRepr with
                | .scalar (.initialized pk r) =>
                  match scalarLayoutTargetByteWidth layouts (.initialized pk r) with
                  | .some w =>
                    match Nat.beq w l.size.bytes with
                    | true => .some (replicateBool l.size.bytes true)
                    | false => .none
                  | .none => .none
                | _ => .none

/--
Test whether every typed slot in a layout-less union's slot list is empty
(`.unit`, or non-enum `.aggregate 0 .nil`).
-/
def allUntypedUnionSlotsEmpty (hasNonZstFieldlessEnum0 : Bool) : List Value → Bool
  | .nil => true
  | .unit :: rest => allUntypedUnionSlotsEmpty hasNonZstFieldlessEnum0 rest
  | .aggregate 0 .nil :: rest =>
    match hasNonZstFieldlessEnum0 with
    | true => false
    | false => allUntypedUnionSlotsEmpty hasNonZstFieldlessEnum0 rest
  | _ :: _ => false

/--
Merge ALL non-empty typed union slots into `(buf, bufMask)` using exact
`fieldLayouts` and `layoutDataMask`, preserving every byte initialized by any
field (including larger fields after smaller ones or byte-array fields covering
another field's padding) and failing closed (`.none`) if two slots disagree on a
non-padding byte.
-/
def mergeExactUnionTypedSlots
    (layouts : LayoutTable)
    (encodeAt : Nat → Value → Option (List AbstractByte))
    (maskFuel totalSize : Nat) :
    List Nat → List Value → List AbstractByte → List Bool → Option (List AbstractByte)
  | .nil, .nil, buf, _ => .some buf
  | fIdx :: restIdxs, fv :: restVals, buf, bufMask =>
    match LayoutTable.lookup layouts fIdx with
    | .none => .none
    | .some fl =>
      match Nat.beq fl.size.bytes 0 with
      | true =>
        mergeExactUnionTypedSlots layouts encodeAt maskFuel totalSize restIdxs restVals buf bufMask
      | false =>
        match fv with
        | .unit =>
          mergeExactUnionTypedSlots layouts encodeAt maskFuel totalSize restIdxs restVals buf bufMask
        | _ =>
          match encodeAt fIdx fv, layoutDataMask layouts (.succ maskFuel) fIdx with
          | .some fBs, .some fMask =>
            match
              Bool.and (Nat.beq (length fBs) fl.size.bytes)
                (Bool.and (Nat.beq (length fMask) fl.size.bytes) (Nat.ble fl.size.bytes totalSize))
            with
            | false => .none
            | true =>
              match mergeMaskedAbstractBytes buf bufMask fBs fMask with
              | .none => .none
              | .some (buf', bufMask') =>
                mergeExactUnionTypedSlots
                  layouts encodeAt maskFuel totalSize restIdxs restVals buf' bufMask'
          | _, _ => .none
  | _, _, _, _ => .none

/--
Encode a single leaf value (`.scalar` or `.ptr`) into `expectedSz` raw
little-endian bytes for a layout slot without `fieldLayouts`.
-/
def encodeLeafForScalarLayout
    (mem : Memory)
    (expectedSz : Nat) :
    Value → Option (List AbstractByte)
  | .scalar sv =>
    match Nat.beq sv.sizeBytes expectedSz with
    | true => encodeScalarBytes sv .none
    | false => .none
  | .ptr p sz =>
    match Nat.beq sz expectedSz with
    | true => encodePtrRawBytes mem p sz
    | false => .none
  | _ => .none

/--
Exact, layout-directed raw abstract-byte encoder for `v` at `layouts.entries[lIdx]`:
- Fails closed (`.none`) on big-endian `LayoutTable`s (`isLittleEndian = false`).
- Preserves raw scalar bytes (including invalid `bool`/`char` bit patterns) so
  `typed_swap_nonoverlapping` observes UB rather than misclassifying as
  `.unsupported`.
- Encodes `.arbitrary` structs/tuples strictly from `TypeLayout.fields` +
  `fieldLayouts` (or validated `.scalar`/memory-ordered `.scalarPair` when
  `fieldLayouts = .nil`), NEVER guessing field types from generic `args` or
  packing nested padded structs back-to-back.

Reference (The Rust Reference 1.98.0, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an array with that item type including alignment padding."
-/
def encodeValueAtLayoutIdx
    (mem : Memory)
    (layouts : LayoutTable) :
    Nat → LayoutIdx → Value → Option (List AbstractByte)
  | .zero, _, _ => .none
  | .succ fuel', lIdx, v =>
    match layouts.isLittleEndian with
    | false => .none
    | true =>
      match LayoutTable.lookup layouts lIdx with
      | .none => .none
      | .some l =>
        match Bool.and (TypeLayout.isWellFormed l) (Bool.not l.isUninhabited) with
        | false => .none
        | true =>
          match l.variants with
          | .empty => .none
          | .multiple _ _ _ => .none
          | .single expectedVar =>
            match l.fields with
            | .primitive =>
              match Nat.beq l.size.bytes 0 with
              | true =>
                match v with
                | .unit => .some .nil
                | .aggregate varIdx .nil =>
                  match Nat.beq varIdx expectedVar with
                  | true => .some .nil
                  | false => .none
                | _ => .none
              | false =>
                match l.backendRepr with
                | .scalar sl =>
                  match scalarLayoutTargetByteWidth layouts sl with
                  | .some w =>
                    match Nat.beq w l.size.bytes with
                    | true => encodeLeafForScalarLayout mem l.size.bytes v
                    | false => .none
                  | .none => .none
                | _ => encodeLeafForScalarLayout mem l.size.bytes v
            | .arbitrary .nil _ =>
              match v with
              | .unit => .some (replicateUninitBytes l.size.bytes)
              | .aggregate varIdx .nil =>
                match Nat.beq varIdx expectedVar with
                | true => .some (replicateUninitBytes l.size.bytes)
                | false => .none
              | _ => .none
            | .arbitrary offsets memIdx =>
              match v with
              | .aggregate varIdx fieldVals =>
                match
                  Bool.and
                    (Nat.beq varIdx expectedVar)
                    (Nat.beq (length fieldVals) (length offsets))
                with
                | false => .none
                | true =>
                  match Nat.beq (length l.fieldLayouts) (length offsets) with
                  | true =>
                    encodeFieldsAtOffsetsExactWith
                      (fun fIdx fv => encodeValueAtLayoutIdx mem layouts fuel' fIdx fv)
                      (fun fIdx =>
                        match LayoutTable.lookup layouts fIdx with
                        | .some fl => .some fl.size.bytes
                        | .none => .none)
                      offsets
                      l.fieldLayouts
                      fieldVals
                      (replicateUninitBytes l.size.bytes)
                  | false =>
                    match offsets, fieldVals, l.backendRepr with
                    | off0 :: .nil, v0 :: .nil, .scalar s0 =>
                      match scalarLayoutTargetByteWidth layouts s0 with
                      | .some sz0 =>
                        match encodeLeafForScalarLayout mem sz0 v0 with
                        | .some b0 =>
                          writeAbstractBytesAt (replicateUninitBytes l.size.bytes) off0.bytes b0
                        | .none => .none
                      | .none => .none
                    | off0 :: off1 :: .nil, v0 :: v1 :: .nil, .scalarPair s0 s1 =>
                      match
                        scalarPairOffsetsValid layouts (off0 :: off1 :: .nil) memIdx s0 s1 l.size.bytes
                      with
                      | .some (firstOff, sz0, secondOff, sz1, swapped) =>
                        let (firstVal, secondVal) :=
                          match swapped with
                          | false => (v0, v1)
                          | true => (v1, v0)
                        match
                          encodeLeafForScalarLayout mem sz0 firstVal,
                          encodeLeafForScalarLayout mem sz1 secondVal
                        with
                        | .some b0, .some b1 =>
                          match writeAbstractBytesAt (replicateUninitBytes l.size.bytes) firstOff b0 with
                          | .some buf1 => writeAbstractBytesAt buf1 secondOff b1
                          | .none => .none
                        | _, _ => .none
                      | .none => .none
                    | _, _, _ => .none
              | _ => .none
            | .array stride count =>
              match Nat.beq count 0 with
              | true =>
                match Nat.beq l.size.bytes 0 with
                | false => .none
                | true =>
                  match v with
                  | .unit => .some .nil
                  | .aggregate varIdx .nil =>
                    match Nat.beq varIdx expectedVar with
                    | true => .some .nil
                    | false => .none
                  | _ => .none
              | false =>
                match Nat.beq l.size.bytes (Nat.mul stride.bytes count) with
                | false => .none
                | true =>
                  match v with
                  | .aggregate varIdx elems =>
                    match
                      Bool.and (Nat.beq varIdx expectedVar) (Nat.beq (length elems) count)
                    with
                    | false => .none
                    | true =>
                      match l.fieldLayouts with
                      | elemLIdx :: _ =>
                        match LayoutTable.lookup layouts elemLIdx with
                        | .some elemFl =>
                          match Nat.ble elemFl.size.bytes stride.bytes with
                          | false => .none
                          | true =>
                            encodeArrayElemsAtLayoutIdx
                              (fun ev => encodeValueAtLayoutIdx mem layouts fuel' elemLIdx ev)
                              elemFl.size.bytes
                              stride.bytes
                              0
                              elems
                              (replicateUninitBytes l.size.bytes)
                        | .none => .none
                      | .nil => .none
                  | _ => .none
            | .union count =>
              match v with
              | .unit =>
                match Nat.beq l.size.bytes 0 with
                | true => .some .nil
                | false => .none
              | .scalar sv =>
                match Nat.ble sv.sizeBytes l.size.bytes with
                | false => .none
                | true =>
                  match encodeScalarBytes sv .none with
                  | .some bs => writeAbstractBytesAt (replicateUninitBytes l.size.bytes) 0 bs
                  | .none => .none
              | .ptr p sz =>
                match Nat.ble sz l.size.bytes with
                | false => .none
                | true =>
                  match encodePtrRawBytes mem p sz with
                  | .some bs => writeAbstractBytesAt (replicateUninitBytes l.size.bytes) 0 bs
                  | .none => .none
              | .aggregate varIdx fieldVals =>
                match Nat.beq varIdx 0 with
                | false => .none
                | true =>
                  match splitUnionTypedAndOverlay count fieldVals with
                  | .none => .none
                  | .some (typedVals, overlayOpt) =>
                    match overlayOpt with
                    | .some rawVals =>
                      match
                        Bool.and
                          (Nat.beq (length rawVals) l.size.bytes)
                          (Nat.ble
                            (unionNonUnitNonZstTypedSlotCount layouts count l.fieldLayouts typedVals)
                            1)
                      with
                      | false => .none
                      | true =>
                        match overlayRawAbstractByteVals rawVals (replicateUninitBytes l.size.bytes) with
                        | .none => .none
                        | .some rawImg =>
                          match Nat.beq (length l.fieldLayouts) (length typedVals) with
                          | true =>
                            mergeExactUnionTypedSlots
                              layouts
                              (fun fIdx fv => encodeValueAtLayoutIdx mem layouts fuel' fIdx fv)
                              fuel'
                              l.size.bytes
                              l.fieldLayouts
                              typedVals
                              rawImg
                              (replicateBool l.size.bytes true)
                          | false =>
                            match
                              allUntypedUnionSlotsEmpty
                                (layoutEntriesHaveNonZstFieldlessEnum0 layouts.entries)
                                typedVals
                            with
                            | true => .some rawImg
                            | false => .none
                    | .none =>
                      match Nat.beq (length l.fieldLayouts) (length typedVals) with
                      | true =>
                        mergeExactUnionTypedSlots
                          layouts
                          (fun fIdx fv => encodeValueAtLayoutIdx mem layouts fuel' fIdx fv)
                          fuel'
                          l.size.bytes
                          l.fieldLayouts
                          typedVals
                          (replicateUninitBytes l.size.bytes)
                          (replicateBool l.size.bytes false)
                      | false =>
                        let hasEnum0 := layoutEntriesHaveNonZstFieldlessEnum0 layouts.entries
                        match allUntypedUnionSlotsEmpty hasEnum0 typedVals with
                        | true => .some (replicateUninitBytes l.size.bytes)
                        | false =>
                          -- Untyped union payload (e.g., `MaybeUninit<[u8; N]>` without fieldLayouts):
                          -- accept only leaf or homogeneous flat-array payloads.
                          let payloadOpt : Option Value :=
                            match typedVals with
                            | fv :: .nil => .some fv
                            | .unit :: fv :: .nil => .some fv
                            | .aggregate 0 .nil :: fv :: .nil =>
                              match hasEnum0 with
                              | true => .none
                              | false => .some fv
                            | _ => .none
                          match payloadOpt with
                          | .none => .none
                          | .some pv =>
                            match encodeUntypedLeafOrArrayExact mem pv with
                            | .some bs =>
                              match Nat.ble (length bs) l.size.bytes with
                              | true => writeAbstractBytesAt (replicateUninitBytes l.size.bytes) 0 bs
                              | false => .none
                            | .none => .none

/--
Encode array elements for a known element `RigidTy` when no `TypeLayout` entry
with `fieldLayouts` is present.
-/
def encodeRawArrayElems
    (encodeElem : Value → Option (List AbstractByte))
    (elemSz : Nat) :
    List Value → Option (List AbstractByte)
  | .nil => .some .nil
  | ev :: rest =>
    match encodeElem ev, encodeRawArrayElems encodeElem elemSz rest with
    | .some eb, .some rb =>
      match Nat.beq (length eb) elemSz with
      | true => .some (appendAbstractBytes eb rb)
      | false => .none
    | _, _ => .none

/--
Exact raw byte encoder for `v : Value` at optional `tyOpt : Option Ty`,
preserving invalid scalar bit patterns and `.uninit` sub-values, enforcing
little-endianness, and never guessing sequential layouts for `>= 2`-field tuples
or unlaid-out ADTs.
-/
def encodeRawValueBytes
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Option Ty → Value → Option (List AbstractByte)
  | .zero, _, _ => .none
  | .succ fuel', tyOpt, v =>
    match layouts.isLittleEndian with
    | false => .none
    | true =>
      match tyOpt with
      | .none => encodeUntypedLeafOrArrayExact mem v
      | .some ty =>
        let ptrBytes := layoutPointerBytes layouts
        match consistentExplicitLayout? layouts ty with
        | .some (lIdx, _) => encodeValueAtLayoutIdx mem layouts (.succ fuel') lIdx v
        | .none =>
          match ty.kind with
          | .bool => encodeLeafForScalarLayout mem 1 v
          | .char => encodeLeafForScalarLayout mem 4 v
          | .int _ =>
            match intTyTargetBytes layouts ty.kind with
            | .some sz => encodeLeafForScalarLayout mem sz v
            | .none => .none
          | .uint _ =>
            match intTyTargetBytes layouts ty.kind with
            | .some sz => encodeLeafForScalarLayout mem sz v
            | .none => .none
          | .float w => encodeLeafForScalarLayout mem (floatTyByteWidth w) v
          | .never =>
            match v with
            | .unit | .aggregate 0 .nil => .some .nil
            | _ => .none
          | .fnDef _ _ =>
            match v with
            | .unit | .aggregate 0 .nil => .some .nil
            | _ => .none
          | .tuple .nil =>
            match v with
            | .unit | .aggregate 0 .nil => .some .nil
            | _ => .none
          | .fnPtr _ _ _ _ => encodeLeafForScalarLayout mem ptrBytes v
          | .ref _ pt =>
            match knownWidePointeeTailAux? 8 pt with
            | .some _ =>
              match v with
              | .aggregate 0 (dVal :: mVal :: .nil) =>
                match
                  encodeLeafForScalarLayout mem ptrBytes dVal,
                  encodeLeafForScalarLayout mem ptrBytes mVal
                with
                | .some db, .some mb => .some (appendAbstractBytes db mb)
                | _, _ => .none
              | _ => .none
            | .none =>
              match ptrPointeeMayBeUnsizedAux 8 pt with
              | false => encodeLeafForScalarLayout mem ptrBytes v
              | true =>
                match declPtrToPointeeByteSize? localDecls layouts pt with
                | .some sz =>
                  match Nat.beq sz ptrBytes with
                  | true => encodeLeafForScalarLayout mem ptrBytes v
                  | false =>
                    match Nat.beq sz (Nat.mul 2 ptrBytes), v with
                    | true, .aggregate 0 (dVal :: mVal :: .nil) =>
                      match
                        encodeLeafForScalarLayout mem ptrBytes dVal,
                        encodeLeafForScalarLayout mem ptrBytes mVal
                      with
                      | .some db, .some mb => .some (appendAbstractBytes db mb)
                      | _, _ => .none
                    | _, _ => .none
                | .none => .none
          | .rawPtr _ pt =>
            match knownWidePointeeTailAux? 8 pt with
            | .some _ =>
              match v with
              | .aggregate 0 (dVal :: mVal :: .nil) =>
                match
                  encodeLeafForScalarLayout mem ptrBytes dVal,
                  encodeLeafForScalarLayout mem ptrBytes mVal
                with
                | .some db, .some mb => .some (appendAbstractBytes db mb)
                | _, _ => .none
              | _ => .none
            | .none =>
              match ptrPointeeMayBeUnsizedAux 8 pt with
              | false => encodeLeafForScalarLayout mem ptrBytes v
              | true =>
                match declPtrToPointeeByteSize? localDecls layouts pt with
                | .some sz =>
                  match Nat.beq sz ptrBytes with
                  | true => encodeLeafForScalarLayout mem ptrBytes v
                  | false =>
                    match Nat.beq sz (Nat.mul 2 ptrBytes), v with
                    | true, .aggregate 0 (dVal :: mVal :: .nil) =>
                      match
                        encodeLeafForScalarLayout mem ptrBytes dVal,
                        encodeLeafForScalarLayout mem ptrBytes mVal
                      with
                      | .some db, .some mb => .some (appendAbstractBytes db mb)
                      | _, _ => .none
                    | _, _ => .none
                | .none => .none
          | .array elem n =>
            match Nat.beq n 0 with
            | true =>
              match v with
              | .unit | .aggregate 0 .nil => .some .nil
              | _ => .none
            | false =>
              let elemTy : Ty := { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
              match exactTyByteSize? localDecls layouts elemTy with
              | .none => .none
              | .some elemSz =>
                match v with
                | .aggregate 0 elems =>
                  match Nat.beq (length elems) n with
                  | true =>
                    encodeRawArrayElems
                      (fun ev => encodeRawValueBytes mem localDecls layouts fuel' (.some elemTy) ev)
                      elemSz
                      elems
                  | false => .none
                | _ => .none
          | .tuple (k :: .nil) =>
            let innerTy : Ty := { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
            match v with
            | .aggregate 0 (v0 :: .nil) =>
              encodeRawValueBytes mem localDecls layouts fuel' (.some innerTy) v0
            | _ => .none
          | .tuple ks =>
            match findConsistentDeclLayout? localDecls layouts (.tuple ks) with
            | .some (lIdx, _) => encodeValueAtLayoutIdx mem layouts (.succ fuel') lIdx v
            | .none => .none
          | .adt _ _ =>
            match findConsistentDeclLayout? localDecls layouts ty.kind with
            | .some (lIdx, _) => encodeValueAtLayoutIdx mem layouts (.succ fuel') lIdx v
            | .none => .none
          | .closure _ _ =>
            match findConsistentDeclLayout? localDecls layouts ty.kind with
            | .some (lIdx, _) => encodeValueAtLayoutIdx mem layouts (.succ fuel') lIdx v
            | .none => .none
          | _ => .none

/--
Read the full root `List AbstractByte` image of `ep : ResolvedMemEndpoint`.
-/
def readRootAbstractBytes
    (mem : Memory)
    (ep : ResolvedMemEndpoint) :
    Option (List AbstractByte) :=
  match ep.globalAlloc? with
  | .some gAlloc =>
    globalAllocSliceToAbstractBytes gAlloc 0 ep.allocSize (layoutPointerBytes ep.targetLayouts)
  | .none =>
    match ep.rootSlot? with
    | .some .uninit => .some (replicateUninitBytes ep.allocSize)
    | .some (.init rootVal) =>
      match encodeRawValueBytes mem ep.targetDecls ep.targetLayouts defaultCodecFuel ep.rootTy? rootVal with
      | .some bs =>
        match Nat.beq (length bs) ep.allocSize with
        | true => .some bs
        | false => .none
      | .none => .none
    | _ => .none

/--
Apply a data mask `mask` to `bytes`: keep bytes where `mask[i] = true` and reset
padding bytes where `mask[i] = false` to `AbstractByte.uninit`.
-/
def applyDataMask : List Bool → List AbstractByte → Option (List AbstractByte)
  | .nil, .nil => .some .nil
  | true :: mRest, b :: bRest =>
    match applyDataMask mRest bRest with
    | .some tail' => .some (b :: tail')
    | .none => .none
  | false :: mRest, _ :: bRest =>
    match applyDataMask mRest bRest with
    | .some tail' => .some (.uninit :: tail')
    | .none => .none
  | _, _ => .none

/--
Compute the data-vs-padding mask for `ty : Ty`, consulting a consistent explicit
layout first and falling back to structural masks for primitives, pointers,
arrays, and 1-tuples.
-/
def tyDataMask
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → Option (List Bool)
  | .zero, _ => .none
  | .succ fuel', ty =>
    match resolveConsistentLayout? localDecls layouts ty with
    | .some (lIdx, _) => layoutDataMask layouts (.succ fuel') lIdx
    | .none =>
      let ptrBytes := layoutPointerBytes layouts
      match ty.kind with
      | .bool => .some (replicateBool 1 true)
      | .char => .some (replicateBool 4 true)
      | .int _ =>
        match intTyTargetBytes layouts ty.kind with
        | .some sz => .some (replicateBool sz true)
        | .none => .none
      | .uint _ =>
        match intTyTargetBytes layouts ty.kind with
        | .some sz => .some (replicateBool sz true)
        | .none => .none
      | .float w => .some (replicateBool (floatTyByteWidth w) true)
      | .tuple .nil | .fnDef _ _ => .some .nil
      | .never => .some .nil
      | .fnPtr _ _ _ _ => .some (replicateBool ptrBytes true)
      | .ref _ pt =>
        match knownWidePointeeTailAux? 8 pt with
        | .some _ => .some (replicateBool (Nat.mul 2 ptrBytes) true)
        | .none =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | false => .some (replicateBool ptrBytes true)
          | true =>
            match declPtrToPointeeByteSize? localDecls layouts pt with
            | .some sz => .some (replicateBool sz true)
            | .none => .none
      | .rawPtr _ pt =>
        match knownWidePointeeTailAux? 8 pt with
        | .some _ => .some (replicateBool (Nat.mul 2 ptrBytes) true)
        | .none =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | false => .some (replicateBool ptrBytes true)
          | true =>
            match declPtrToPointeeByteSize? localDecls layouts pt with
            | .some sz => .some (replicateBool sz true)
            | .none => .none
      | .array elem n =>
        match Nat.beq n 0 with
        | true => .some .nil
        | false =>
          match tyDataMask localDecls layouts fuel'
              { kind := elem, layoutIdx := unresolvedLayoutIdx layouts } with
          | .some em => .some (repeatBoolList em n)
          | .none => .none
      | .tuple (k :: .nil) =>
        tyDataMask localDecls layouts fuel'
          { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
      | _ => .none

/--
Reset every padding byte of a typed `T` value's byte image `bytes` to
`AbstractByte.uninit`, preserving all data bytes (including union data ranges
and pointer provenance). Applied uniformly to both stack locals and global
allocations in `typed_swap_nonoverlapping`.
-/
def resetTypedPaddingBytes
    (fuel : Nat)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : Ty)
    (bytes : List AbstractByte) :
    Option (List AbstractByte) :=
  match tyDataMask localDecls layouts fuel ty with
  | .none => .none
  | .some mask => applyDataMask mask bytes

/--
Test whether `WrappingRange` `r` excludes at least one bit pattern in
`[0, 2^(8 * widthBytes))`.
-/
@[reducible]
def validRangeExcludesAny (widthBytes : Nat) (r : WrappingRange) : Bool :=
  let maxVal := Nat.sub (scalarModulus widthBytes) 1
  match Nat.ble r.start r.end_ with
  | true => Bool.not (Bool.and (Nat.beq r.start 0) (Nat.ble maxVal r.end_))
  | false => Bool.not (Nat.ble r.start (Nat.add r.end_ 1))

/--
Test whether `WrappingRange` `r` covers every non-null bit pattern
`1..=(2^(8 * ptrBytes) - 1)` (i.e. `0..=MAX` or `1..=MAX`).
-/
@[reducible]
def validRangeCoversAllNonNull (ptrBytes : Nat) (r : WrappingRange) : Bool :=
  let maxVal := Nat.sub (scalarModulus ptrBytes) 1
  match Nat.ble r.start r.end_ with
  | true => Bool.and (Nat.ble r.start 1) (Nat.ble maxVal r.end_)
  | false => Nat.ble r.start (Nat.add r.end_ 1)

/--
Helper testing whether any element in `xs` satisfies `pred`.
-/
@[reducible]
def anyListTrue {α : Type} (pred : α → Bool) : List α → Bool
  | .nil => false
  | x :: rest =>
    match pred x with
    | true => true
    | false => anyListTrue pred rest

/--
Fuel-bounded check for **layout uninhabitedness** of `ty : RigidTy`:
- `!` is uninhabited; `[T; n]` is uninhabited iff `n > 0` and `T` is uninhabited;
  a tuple is uninhabited iff any field is uninhabited; an ADT/closure is
  uninhabited iff its consistent `TypeLayout` marks `isUninhabited = true` or
  `variants = .empty`.
- Pointer and reference types (`&T`, `&mut T`, `*const T`, `*mut T`, `fn()`) are
  NEVER layout-uninhabited (`rustc_ty_utils::layout` assigns every `&T` an
  inhabited non-null pointer scalar; uninhabited-pointee `&!` is checked on
  reference values via `referenceToUninhabited`, not on `raw_eq::<&!>`).

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1937-L1943>

> "pub enum Variants<FieldIdx: Idx, VariantIdx: Idx> {
>     /// A type with no valid variants. Must be uninhabited.
>     Empty,"
-/
def isUninhabitedRigidTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ fuel', ty =>
    match ty with
    | .never => true
    | .array elem n =>
      match Nat.beq n 0 with
      | true => false
      | false => isUninhabitedRigidTy localDecls layouts fuel' elem
    | .tuple ks => anyListTrue (isUninhabitedRigidTy localDecls layouts fuel') ks
    | .adt _ _ =>
      match findConsistentDeclLayout? localDecls layouts ty with
      | .some (_, l) =>
        Bool.or l.isUninhabited (match l.variants with | .empty => true | _ => false)
      | .none => false
    | .closure _ _ =>
      match findConsistentDeclLayout? localDecls layouts ty with
      | .some (_, l) =>
        Bool.or l.isUninhabited (match l.variants with | .empty => true | _ => false)
      | .none => false
    | _ => false

/--
Test whether `ty : Ty` is layout-uninhabited, consulting its consistent explicit
`TypeLayout` first and then `isUninhabitedRigidTy`.
-/
def isUninhabitedTy
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (fuel : Nat)
    (ty : Ty) :
    Bool :=
  match consistentExplicitLayout? layouts ty with
  | .some (_, l) =>
    Bool.or l.isUninhabited (match l.variants with | .empty => true | _ => false)
  | .none => isUninhabitedRigidTy localDecls layouts fuel ty.kind

/--
Test whether a thin reference `&T` / `&mut T` points to a sized,
layout-uninhabited pointee `T` (e.g. `&!`, `&(u8, !)`; returns `false` for
unsized `&[!]` and for `&&!` whose pointee `&!` is layout-inhabited).

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#r-undefined.validity.reference-box>

> "A reference or `Box<T>` must be aligned and non-null, it cannot be dangling,
> and it must point to a valid value (in case of dynamically sized types, using
> the actual dynamic type of the pointee as determined by the metadata). Note
> that the last point (about pointing to a valid value) remains a subject of
> some debate."
-/
def referenceToUninhabited
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (pointee : RigidTy) :
    Bool :=
  match isUnsizedRigidTy 8 pointee with
  | true => false
  | false => isUninhabitedRigidTy localDecls layouts 8 pointee

/--
Test whether `(pk, r, bits)` is a Unicode surrogate code point (`0xD800..=0xDFFF`)
inside a `char`-shaped `ScalarLayout` (`Int(32, false)` with `validRange =
0..=0x10FFFF`). Because `TypeLayout` cannot distinguish `char` from a pattern
type `u32 is 0..=0x10FFFF`, layout-driven validators fail closed `.unsupported`
on such surrogates while direct `RigidTy.char` remains exact `.ub`.

Reference (The Rust Reference 1.98.0, "Character type"):
<https://doc.rust-lang.org/1.98.0/reference/types/char.html#r-type.char.intro>
<https://doc.rust-lang.org/1.98.0/reference/types/char.html#r-type.char.value>

> "The `char` type represents a single Unicode scalar value (i.e., a code point
> that is not a surrogate)."
> "A value of type `char` is represented as a 32-bit unsigned word in the 0x0000
> to 0xD7FF or 0xE000 to 0x10FFFF range. It is immediate undefined behavior to
> create a `char` that falls outside this range."
-/
@[reducible]
def charShapedSurrogate (pk : PrimitiveKind) (r : WrappingRange) (bits : Nat) : Bool :=
  match pk with
  | .int 32 false =>
    Bool.and (Nat.beq r.start 0)
      (Bool.and (Nat.beq r.end_ 1114111)
        (Bool.and (Nat.ble 55296 bits) (Nat.ble bits 57343)))
  | _ => false

/--
Combine two `TypedValidity` outcomes without letting `.unsupported` in an
earlier field or element mask a definite `.ub` in a later field or element
(`.ub` absorbs both `.valid` and `.unsupported`).
-/
@[reducible]
def TypedValidity.combine (a : TypedValidity) (b : Unit → TypedValidity) : TypedValidity :=
  match a with
  | .ub => .ub
  | .valid => b ()
  | .unsupported =>
    match b () with
    | .ub => .ub
    | _ => .unsupported

/--
Validate `bytes` as a non-null `ptrBytes`-wide thin pointer (used for `&T`,
`fn()`, and `dyn Trait` vtables):
- Any `.uninit` byte or wrong byte length => `.ub`.
- Fragmented or mixed provenance across the bytes => `.unsupported` (partial
  pointers strip provenance and may be null).
- Provenance-free `0` or unbacked `allocId = 0, offset = 0` => `.ub`.
-/
def validateNonNullPtrBytes
    (mem : Memory)
    (ptrBytes : Nat)
    (bytes : List AbstractByte) :
    TypedValidity :=
  match Nat.beq (length bytes) ptrBytes with
  | false => .ub
  | true =>
    match hasUninitByte bytes with
    | true => .ub
    | false =>
      match allBytesSameProv bytes with
      | .none => .unsupported
      | .some .none =>
        match decodeScalarBytes bytes false with
        | .some (sv, _) =>
          match Nat.beq sv.bits 0 with
          | true => .ub
          | false => .valid
        | .none => .ub
      | .some (.some (a, _)) =>
        match decodeScalarBytes bytes false with
        | .some (sv, _) =>
          match
            Bool.and (Nat.beq a 0)
              (Bool.not (isBackedPtr mem { allocId := 0, offsetBytes := sv.bits }))
          with
          | true =>
            match Nat.beq sv.bits 0 with
            | true => .ub
            | false => .valid
          | false => .valid
        | .none => .ub

/--
Validate `bytes` against a compiler `ScalarLayout` `sl` on `layouts` (enforcing
little-endianness, target pointer width, initialization, non-pointer provenance
rejection, fragmented-provenance guard on niche/non-null pointers, `validRange`,
`validRangeCoversAllNonNull`, and `charShapedSurrogate`).
-/
def validateScalarLayoutBytes
    (mem : Memory)
    (layouts : LayoutTable)
    (sl : ScalarLayout)
    (bytes : List AbstractByte) :
    TypedValidity :=
  match layouts.isLittleEndian with
  | false => .unsupported
  | true =>
    match scalarLayoutTargetByteWidth layouts sl with
    | .none => .unsupported
    | .some sz =>
      match Nat.beq (length bytes) sz with
      | false => .unsupported
      | true =>
        match sl with
        | .union _ => .valid
        | .initialized pk validRange =>
          match hasUninitByte bytes with
          | true => .ub
          | false =>
            match pk with
            | .pointer _ =>
              match allBytesSameProv bytes with
              | .none =>
                match validRangeExcludesAny sz validRange with
                | true => .unsupported
                | false => .valid
              | .some .none =>
                match decodeScalarBytes bytes false with
                | .some (sv, _) =>
                  match wrappingRangeContains validRange sv.bits with
                  | true => .valid
                  | false => .ub
                | .none => .ub
              | .some (.some (a, _)) =>
                match decodeScalarBytes bytes false with
                | .some (sv, _) =>
                  match
                    Bool.and (Nat.beq a 0)
                      (Bool.not (isBackedPtr mem { allocId := 0, offsetBytes := sv.bits }))
                  with
                  | true =>
                    match wrappingRangeContains validRange sv.bits with
                    | true => .valid
                    | false => .ub
                  | false =>
                    match validRangeCoversAllNonNull sz validRange with
                    | true => .valid
                    | false => .unsupported
                | .none => .ub
            | .int _ _ | .float _ =>
              match bytesHaveRealProvenance mem bytes with
              | true => .unsupported
              | false =>
                match decodeScalarBytes bytes false with
                | .some (sv, _) =>
                  match wrappingRangeContains validRange sv.bits with
                  | false => .ub
                  | true =>
                    match charShapedSurrogate pk validRange sv.bits with
                    | true => .unsupported
                    | false => .valid
                | .none => .ub

/--
Validate wide-pointer metadata bytes (`metaBytes`) for a known DST tail
(`[T]`, `str`, or `dyn Trait`):
- `dyn Trait` (both `&dyn Trait` and `*const dyn Trait`): vtable pointer must be
  initialized and non-null (`validateNonNullPtrBytes`).
- `[T]` / `str`: must be initialized and provenance-free; for references (`isRef
  = true`), `len * elemSize ≤ isize::MAX` (with `hasHeaderPrefix = true` failing
  closed `.unsupported` when not already oversized).
-/
def validateWideMetaBytes
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (isRef : Bool)
    (hasHeaderPrefix : Bool)
    (tailTy : RigidTy)
    (metaBytes : List AbstractByte) :
    TypedValidity :=
  match layouts.isLittleEndian with
  | false => .unsupported
  | true =>
    let ptrBytes := layoutPointerBytes layouts
    match Nat.beq (length metaBytes) ptrBytes with
    | false => .ub
    | true =>
      match tailTy with
      | .dynamic _ => validateNonNullPtrBytes mem ptrBytes metaBytes
      | .str =>
        match hasUninitByte metaBytes with
        | true => .ub
        | false =>
          match bytesHaveRealProvenance mem metaBytes with
          | true => .unsupported
          | false =>
            match isRef with
            | false => .valid
            | true =>
              match decodeScalarBytes metaBytes false with
              | .none => .ub
              | .some (lenSc, _) =>
                let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
                match Nat.ble lenSc.bits isizeMax with
                | false => .ub
                | true =>
                  match hasHeaderPrefix with
                  | true => .unsupported
                  | false => .valid
      | .slice elemTy =>
        match hasUninitByte metaBytes with
        | true => .ub
        | false =>
          match bytesHaveRealProvenance mem metaBytes with
          | true => .unsupported
          | false =>
            match isRef with
            | false => .valid
            | true =>
              match decodeScalarBytes metaBytes false with
              | .none => .ub
              | .some (lenSc, _) =>
                match exactRigidTyByteSize? localDecls layouts elemTy with
                | .none => .unsupported
                | .some elemSz =>
                  let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
                  match Nat.ble (Nat.mul lenSc.bits elemSz) isizeMax with
                  | false => .ub
                  | true =>
                    match hasHeaderPrefix with
                    | true => .unsupported
                    | false => .valid
      | _ => .unsupported

/--
Decode a single scalar or pointer `Value` from `bytes` according to target-aware
`ScalarLayout` `sl`. In `V2026_08_01` (which has no `Value.uninit` constructor),
any `.uninit` byte fails closed (`.none`). Rejects fragmented/mixed provenance
when `sl` excludes any bit pattern and enforces `validRange`,
`validRangeCoversAllNonNull`, and `charShapedSurrogate`.
-/
def decodeScalarLayoutBytesTarget
    (mem : Memory)
    (layouts : LayoutTable)
    (sl : ScalarLayout)
    (_allowUninit : Bool)
    (bytes : List AbstractByte) :
    Option Value :=
  match layouts.isLittleEndian with
  | false => .none
  | true =>
    match scalarLayoutTargetByteWidth layouts sl with
    | .none => .none
    | .some expectedSz =>
      match Nat.beq (length bytes) expectedSz with
      | false => .none
      | true =>
        match allBytesUninit bytes with
        | true => .none
        | false =>
          match hasUninitByte bytes with
          | true => .none
          | false =>
            match sl with
            | .union pk =>
              match allBytesSameProv bytes, decodeScalarBytes bytes false with
              | .some (.some (a, _)), .some (sv, _) =>
                match pk with
                | .pointer _ =>
                  .some (.ptr { allocId := a, offsetBytes := sv.bits } expectedSz)
                | _ => .none
              | .some .none, .some (sv, _) =>
                .some (.scalar sv)
              | _, _ => .none
            | .initialized pk validRange =>
              match pk with
              | .pointer _ =>
                match allBytesSameProv bytes, decodeScalarBytes bytes false with
                | .some (.some (a, _)), .some (sv, _) =>
                  match
                    Bool.and (Nat.beq a 0) (Bool.not (isBackedPtr mem { allocId := 0, offsetBytes := sv.bits }))
                  with
                  | true =>
                    match wrappingRangeContains validRange sv.bits with
                    | true => .some (.ptr { allocId := 0, offsetBytes := sv.bits } expectedSz)
                    | false => .none
                  | false =>
                    match validRangeCoversAllNonNull expectedSz validRange with
                    | true => .some (.ptr { allocId := a, offsetBytes := sv.bits } expectedSz)
                    | false => .none
                | .some .none, .some (sv, _) =>
                  match wrappingRangeContains validRange sv.bits with
                  | true => .some (.ptr { allocId := 0, offsetBytes := sv.bits } expectedSz)
                  | false => .none
                | _, _ => .none
              | _ =>
                match bytesHaveRealProvenance mem bytes with
                | true => .none
                | false =>
                  match decodeScalarBytes bytes false with
                  | .some (sv, _) =>
                    match wrappingRangeContains validRange sv.bits with
                    | false => .none
                    | true =>
                      match charShapedSurrogate pk validRange sv.bits with
                      | true => .none
                      | false => .some (.scalar sv)
                  | .none => .none

/--
Decode `FieldsShape.arbitrary` fields strictly by `fieldLayouts` at `offsets`.
-/
def decodeFieldsAtLayoutIdxs
    (decodeAt : LayoutIdx → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List Nat → Option (List Value)
  | .nil, .nil => .some .nil
  | off :: restOffs, fIdx :: restIdxs =>
    match LayoutTable.lookup layouts fIdx with
    | .none => .none
    | .some fl =>
      match sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | .none => .none
      | .some slice =>
        match decodeAt fIdx slice, decodeFieldsAtLayoutIdxs decodeAt layouts bytes restOffs restIdxs with
        | .some fv, .some fvs => .some (fv :: fvs)
        | _, _ => .none
  | _, _ => .none

/--
Decode `count` array chunks at `stride` starting from `curOff`.
-/
def decodeArrayElemsAtLayoutIdx
    (decodeElem : List AbstractByte → Option Value)
    (bytes : List AbstractByte)
    (elemSize stride curOff : Nat) :
    Nat → Option (List Value)
  | .zero => .some .nil
  | .succ rem =>
    match sliceAbstractBytes bytes curOff elemSize with
    | .none => .none
    | .some slice =>
      match
        decodeElem slice,
        decodeArrayElemsAtLayoutIdx decodeElem bytes elemSize stride (Nat.add curOff stride) rem
      with
      | .some ev, .some evs => .some (ev :: evs)
      | _, _ => .none

/--
Decode every field of a union from offset `0` using `fieldLayouts`, demoting any
field whose bytes cannot decode as a valid value (or ZST fields) to `.unit`
(matching `V2026_08_01.MirSemantics.Bytes.decodeUnionFieldsByLayoutIdxs`, since
`V2026_08_01` has no `Value.uninit` constructor).
-/
def decodeUnionFieldsAtLayoutIdxs
    (decodeAt : LayoutIdx → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Nat → List Value
  | .nil => .nil
  | fIdx :: rest =>
    let fv : Value :=
      match LayoutTable.lookup layouts fIdx with
      | .none => .unit
      | .some fl =>
        match Nat.beq fl.size.bytes 0 with
        | true => .unit
        | false =>
          match sliceAbstractBytes bytes 0 fl.size.bytes with
          | .some slice =>
            match decodeAt fIdx slice with
            | .some v => v
            | .none => .unit
          | .none => .unit
    fv :: decodeUnionFieldsAtLayoutIdxs decodeAt layouts bytes rest

/--
Exact layout-directed decoder (`decodeValueAtLayoutIdx`), mirroring
`encodeValueAtLayoutIdx`:
- Fails closed (`.none`) on big-endian `LayoutTable`s.
- Decodes ADTs/structs/tuples/arrays strictly from `TypeLayout.fields`,
  `fieldLayouts`, and `backendRepr` (in memory order for `.scalarPair`).
- In `V2026_08_01` (which has no `Value.uninit` constructor), wholly-`.uninit`
  sub-values fail closed (`.none`) while whole-local uninit commits as
  `LocalSlot.uninit` in `commitRootAbstractBytes`.
-/
def decodeValueAtLayoutIdx
    (mem : Memory)
    (layouts : LayoutTable)
    (allowPartialUninit : Bool) :
    Nat → LayoutIdx → List AbstractByte → Option Value
  | .zero, _, _ => .none
  | .succ fuel', lIdx, bytes =>
    match layouts.isLittleEndian with
    | false => .none
    | true =>
      match LayoutTable.lookup layouts lIdx with
      | .none => .none
      | .some l =>
        match
          Bool.and (TypeLayout.isWellFormed l)
            (Bool.and (Bool.not l.isUninhabited) (Nat.beq (length bytes) l.size.bytes))
        with
        | false => .none
        | true =>
          match l.variants with
          | .empty => .none
          | .multiple _ _ _ => .none
          | .single varIdx =>
            match l.fields with
            | .primitive =>
              match Nat.beq l.size.bytes 0 with
              | true => .some .unit
              | false =>
                match l.backendRepr with
                | .scalar s0 =>
                  decodeScalarLayoutBytesTarget mem layouts s0 allowPartialUninit bytes
                | _ =>
                  match allBytesUninit bytes with
                  | true => .none
                  | false =>
                    match bytesHaveRealProvenance mem bytes with
                    | true => .none
                    | false =>
                      match decodeScalarBytes bytes false with
                      | .some (sv, _) => .some (.scalar sv)
                      | .none => .none
            | .arbitrary .nil _ => .some (.aggregate varIdx .nil)
            | .arbitrary offsets memIdx =>
              match allBytesUninit bytes with
              | true => .none
              | false =>
                match Nat.beq (length l.fieldLayouts) (length offsets) with
                | true =>
                  match
                    decodeFieldsAtLayoutIdxs
                      (fun fIdx bs =>
                        decodeValueAtLayoutIdx mem layouts allowPartialUninit fuel' fIdx bs)
                      layouts
                      bytes
                      offsets
                      l.fieldLayouts
                  with
                  | .some vals => .some (.aggregate varIdx vals)
                  | .none => .none
                | false =>
                  match offsets, l.backendRepr with
                  | off0 :: .nil, .scalar s0 =>
                    match scalarLayoutTargetByteWidth layouts s0 with
                    | .some sz0 =>
                      match sliceAbstractBytes bytes off0.bytes sz0 with
                      | .some sl0 =>
                        match decodeScalarLayoutBytesTarget mem layouts s0 allowPartialUninit sl0 with
                        | .some v0 => .some (.aggregate varIdx (v0 :: .nil))
                        | .none => .none
                      | .none => .none
                    | .none => .none
                  | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
                    match
                      scalarPairOffsetsValid layouts (off0 :: off1 :: .nil) memIdx s0 s1 l.size.bytes
                    with
                    | .some (firstOff, sz0, secondOff, sz1, swapped) =>
                      match
                        sliceAbstractBytes bytes firstOff sz0,
                        sliceAbstractBytes bytes secondOff sz1
                      with
                      | .some sl0, .some sl1 =>
                        match
                          decodeScalarLayoutBytesTarget mem layouts s0 allowPartialUninit sl0,
                          decodeScalarLayoutBytesTarget mem layouts s1 allowPartialUninit sl1
                        with
                        | .some vFirst, .some vSecond =>
                          match swapped with
                          | false => .some (.aggregate varIdx (vFirst :: vSecond :: .nil))
                          | true => .some (.aggregate varIdx (vSecond :: vFirst :: .nil))
                        | _, _ => .none
                      | _, _ => .none
                    | .none => .none
                  | _, _ => .none
            | .array stride count =>
              match Nat.beq count 0 with
              | true => .some (.aggregate varIdx .nil)
              | false =>
                match Nat.beq l.size.bytes (Nat.mul stride.bytes count) with
                | false => .none
                | true =>
                  match l.fieldLayouts with
                  | elemLIdx :: _ =>
                    match LayoutTable.lookup layouts elemLIdx with
                    | .some elemFl =>
                      match Nat.ble elemFl.size.bytes stride.bytes with
                      | false => .none
                      | true =>
                        match
                          decodeArrayElemsAtLayoutIdx
                            (fun bs =>
                              decodeValueAtLayoutIdx mem layouts allowPartialUninit fuel' elemLIdx bs)
                            bytes
                            elemFl.size.bytes
                            stride.bytes
                            0
                            count
                        with
                        | .some vals => .some (.aggregate varIdx vals)
                        | .none => .none
                    | .none => .none
                  | .nil => .none
            | .union count =>
              match allBytesUninit bytes with
              | true =>
                match Nat.beq varIdx 0 with
                | true => .some (.aggregate 0 (replicateValue count .unit))
                | false => .none
              | false =>
                let rawOverlayFallback : Unit → Option Value := fun _ =>
                  match Bool.and (Nat.beq varIdx 0) (Nat.blt 0 count) with
                  | false => .none
                  | true =>
                    match forceValueListOpt (encodeRawAbstractByteVals bytes) with
                    | .some rawVals =>
                      .some
                        (.aggregate 0
                          (appendValueList
                            (replicateValue count .unit)
                            (.aggregate 0 rawVals :: .nil)))
                    | .none => .none
                match l.fieldLayouts with
                | fHead :: fTail =>
                  match Nat.beq (length (fHead :: fTail)) count with
                  | true =>
                    let vals :=
                      decodeUnionFieldsAtLayoutIdxs
                        (fun fIdx bs =>
                          decodeValueAtLayoutIdx mem layouts true fuel' fIdx bs)
                        layouts
                        bytes
                        (fHead :: fTail)
                    match
                      encodeValueAtLayoutIdx mem layouts (.succ fuel') lIdx (.aggregate varIdx vals)
                    with
                    | .some reBs =>
                      match abstractBytesEq reBs bytes with
                      | true => .some (.aggregate varIdx vals)
                      | false => rawOverlayFallback ()
                    | .none => rawOverlayFallback ()
                  | false => rawOverlayFallback ()
                | .nil =>
                  match l.backendRepr with
                  | .scalar s0 =>
                    match decodeScalarLayoutBytesTarget mem layouts s0 true bytes with
                    | .some v => .some v
                    | .none => rawOverlayFallback ()
                  | _ => rawOverlayFallback ()

/--
Decode tuple fields at `offsets` pairing each element's `RigidTy` with its
optional `TypeLayout` index from `fieldLayouts` so type-level invariants (`&!`,
`&[T]`/`&str` lengths, `dyn` vtables, `char`) are preserved when committing into
stack tuple locals.
-/
def decodeTupleFieldsAtOffsetsWith
    (decodeField : RigidTy → Option LayoutIdx → List AbstractByte → Option Value)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List RigidTy → List Nat → Option (List Value)
  | .nil, .nil, _ => .some .nil
  | off :: restOffs, k :: restKs, fIdxs =>
    let (fIdxOpt, restIdxs) : Option LayoutIdx × List Nat :=
      match fIdxs with
      | fIdx :: tail => (.some fIdx, tail)
      | .nil => (.none, .nil)
    let fTy : Ty :=
      match fIdxOpt with
      | .some fIdx => { kind := k, layoutIdx := fIdx }
      | .none => { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
    match exactTyByteSize? localDecls layouts fTy with
    | .none => .none
    | .some fSz =>
      match sliceAbstractBytes bytes off.bytes fSz with
      | .none => .none
      | .some slice =>
        match
          decodeField k fIdxOpt slice,
          decodeTupleFieldsAtOffsetsWith
            decodeField localDecls layouts bytes restOffs restKs restIdxs
        with
        | .some fv, .some fvs => .some (fv :: fvs)
        | _, _ => .none
  | _, _, _ => .none

/--
Decode array chunks using `decodeElem`, returning `.none` if any chunk fails.
-/
def decodePartialUninitArrayChunks
    (decodeElem : List AbstractByte → Option Value)
    (elemSz : Nat) :
    Nat → List AbstractByte → Option (List Value)
  | .zero, .nil => .some .nil
  | .succ rem, bs =>
    let chunk := takeAbstractBytes elemSz bs
    let rest := dropAbstractBytes elemSz bs
    match Nat.beq (length chunk) elemSz with
    | false => .none
    | true =>
      match decodeElem chunk, decodePartialUninitArrayChunks decodeElem elemSz rem rest with
      | .some ev, .some evs => .some (ev :: evs)
      | _, _ => .none
  | _, _ => .none

/--
Decode a single thin pointer byte slice of width `ptrBytes` (for raw ptr, ref,
or fnPtr).
-/
def decodeThinPtrBytes
    (mem : Memory)
    (ptrBytes : Nat)
    (requireNonNull : Bool)
    (_allowUninit : Bool)
    (bytes : List AbstractByte) :
    Option Value :=
  match Nat.beq (length bytes) ptrBytes with
  | false => .none
  | true =>
    match allBytesUninit bytes with
    | true => .none
    | false =>
      match allBytesSameProv bytes, decodeScalarBytes bytes false with
      | .some (.some (a, _)), .some (sv, _) =>
        match
          Bool.and requireNonNull
            (Bool.and (Nat.beq a 0)
              (Bool.and (Nat.beq sv.bits 0)
                (Bool.not (isBackedPtr mem { allocId := 0, offsetBytes := 0 }))))
        with
        | true => .none
        | false => .some (.ptr { allocId := a, offsetBytes := sv.bits } ptrBytes)
      | .some .none, .some (sv, _) =>
        match Bool.and requireNonNull (Nat.beq sv.bits 0) with
        | true => .none
        | false => .some (.ptr { allocId := 0, offsetBytes := sv.bits } ptrBytes)
      | _, _ => .none

/--
Decode a `List AbstractByte` into a `Value` for committing into a stack
`LocalSlot`, enforcing type-level invariants (`bool`, `char`, `&!`, `&[T]`/`&str`
lengths, `dyn` vtables, tuple fields) and using raw-byte union overlays for
partially initialized unions (in `V2026_08_01`, which has no `Value.uninit`
constructor, partially initialized non-union leaves fail closed `.none`, while
wholly-uninit locals commit as `LocalSlot.uninit` in `commitRootAbstractBytes`;
all commits are guarded downstream by `abstractBytesRefine`).
-/
def decodePartialUninitValue
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (allowUninitLeaf : Bool) :
    Nat → Option Ty → List AbstractByte → Option Value
  | .zero, _, _ => .none
  | .succ fuel', tyOpt, bytes =>
    match layouts.isLittleEndian with
    | false => .none
    | true =>
      match tyOpt with
      | .none =>
        match bytes with
        | .nil => .some .unit
        | _ :: _ =>
          match bytesHaveRealProvenance mem bytes with
          | true =>
            let ptrBytes := layoutPointerBytes layouts
            match Nat.beq (length bytes) ptrBytes with
            | true => decodeThinPtrBytes mem ptrBytes false allowUninitLeaf bytes
            | false => .none
          | false =>
            match hasUninitByte bytes with
            | true => .none
            | false =>
              match decodeScalarBytes bytes false with
              | .some (sv, _) => .some (.scalar sv)
              | .none => .none
      | .some ty =>
        let ptrBytes := layoutPointerBytes layouts
        match ty.kind with
        | .bool =>
          match bytes with
          | .uninit :: .nil => .none
          | .init b .none :: .nil =>
            let n := b.toBitVec.toNat
            match Nat.ble n 1 with
            | true => .some (.scalar ⟨n, 1⟩)
            | false => .none
          | _ => .none
        | .char =>
          match Nat.beq (length bytes) 4 with
          | false => .none
          | true =>
            match allBytesUninit bytes with
            | true => .none
            | false =>
              match bytesHaveRealProvenance mem bytes with
              | true => .none
              | false =>
                match decodeScalarBytes bytes false with
                | .some (sv, _) =>
                  match isValidCharCode sv.bits with
                  | true => .some (.scalar sv)
                  | false => .none
                | .none => .none
        | .int _ | .uint _ =>
          match intTyTargetBytes layouts ty.kind with
          | .none => .none
          | .some sz =>
            match Nat.beq (length bytes) sz with
            | false => .none
            | true =>
              match allBytesUninit bytes with
              | true => .none
              | false =>
                match bytesHaveRealProvenance mem bytes with
                | true => .none
                | false =>
                  match decodeScalarBytes bytes false with
                  | .some (sv, _) => .some (.scalar sv)
                  | .none => .none
        | .float w =>
          let sz := floatTyByteWidth w
          match Nat.beq (length bytes) sz with
          | false => .none
          | true =>
            match allBytesUninit bytes with
            | true => .none
            | false =>
              match bytesHaveRealProvenance mem bytes with
              | true => .none
              | false =>
                match decodeScalarBytes bytes false with
                | .some (sv, _) => .some (.scalar sv)
                | .none => .none
        | .tuple .nil | .fnDef _ _ =>
          match bytes with
          | .nil => .some .unit
          | _ :: _ => .none
        | .never => .none
        | .fnPtr _ _ _ _ => decodeThinPtrBytes mem ptrBytes true allowUninitLeaf bytes
        | .ref _ pt =>
          match knownWidePointeeTailAux? 8 pt with
          | .some tailTy =>
            let hasHeader := match pt with | .tuple _ => true | _ => false
            match Nat.beq (length bytes) (Nat.mul 2 ptrBytes) with
            | false => .none
            | true =>
              match allBytesUninit bytes with
              | true => .none
              | false =>
                let dBs := takeAbstractBytes ptrBytes bytes
                let mBs := dropAbstractBytes ptrBytes bytes
                match validateWideMetaBytes mem localDecls layouts true hasHeader tailTy mBs with
                | .valid =>
                  match
                    decodeThinPtrBytes mem ptrBytes true false dBs,
                    match tailTy with
                    | .dynamic _ => decodeThinPtrBytes mem ptrBytes true false mBs
                    | _ =>
                      match bytesHaveRealProvenance mem mBs with
                      | true => .none
                      | false =>
                        match decodeScalarBytes mBs false with
                        | .some (msv, _) => .some (.scalar msv)
                        | .none => .none
                  with
                  | .some dv, .some mv => .some (.aggregate 0 (dv :: mv :: .nil))
                  | _, _ => .none
                | _ => .none
          | .none =>
            match ptrPointeeMayBeUnsizedAux 8 pt with
            | false =>
              match referenceToUninhabited localDecls layouts pt with
              | true => .none
              | false => decodeThinPtrBytes mem ptrBytes true allowUninitLeaf bytes
            | true =>
              match declPtrToPointeeByteSize? localDecls layouts pt with
              | .some sz =>
                match Nat.beq sz ptrBytes with
                | true =>
                  match referenceToUninhabited localDecls layouts pt with
                  | true => .none
                  | false => decodeThinPtrBytes mem ptrBytes true allowUninitLeaf bytes
                | false => .none
              | .none => .none
        | .rawPtr _ pt =>
          match knownWidePointeeTailAux? 8 pt with
          | .some tailTy =>
            let hasHeader := match pt with | .tuple _ => true | _ => false
            match Nat.beq (length bytes) (Nat.mul 2 ptrBytes) with
            | false => .none
            | true =>
              match allBytesUninit bytes with
              | true => .none
              | false =>
                let dBs := takeAbstractBytes ptrBytes bytes
                let mBs := dropAbstractBytes ptrBytes bytes
                match validateWideMetaBytes mem localDecls layouts false hasHeader tailTy mBs with
                | .valid =>
                  match
                    decodeThinPtrBytes mem ptrBytes false false dBs,
                    match tailTy with
                    | .dynamic _ => decodeThinPtrBytes mem ptrBytes true false mBs
                    | _ =>
                      match bytesHaveRealProvenance mem mBs with
                      | true => .none
                      | false =>
                        match decodeScalarBytes mBs false with
                        | .some (msv, _) => .some (.scalar msv)
                        | .none => .none
                  with
                  | .some dv, .some mv => .some (.aggregate 0 (dv :: mv :: .nil))
                  | _, _ => .none
                | _ => .none
          | .none =>
            match ptrPointeeMayBeUnsizedAux 8 pt with
            | false => decodeThinPtrBytes mem ptrBytes false allowUninitLeaf bytes
            | true =>
              match declPtrToPointeeByteSize? localDecls layouts pt with
              | .some sz =>
                match Nat.beq sz ptrBytes with
                | true => decodeThinPtrBytes mem ptrBytes false allowUninitLeaf bytes
                | false => .none
              | .none => .none
        | .array (.uint .u8) n =>
          match Nat.beq (length bytes) n with
          | false => .none
          | true =>
            match
              decodePartialUninitArrayChunks
                (fun chunk =>
                  match chunk with
                  | .uninit :: .nil => .none
                  | .init b .none :: .nil => .some (.scalar ⟨b.toBitVec.toNat, 1⟩)
                  | _ => .none)
                1
                n
                bytes
            with
            | .some elems => .some (.aggregate 0 elems)
            | .none => .none
        | .array elem n =>
          match Nat.beq n 0 with
          | true =>
            match bytes with
            | .nil => .some (.aggregate 0 .nil)
            | _ :: _ => .none
          | false =>
            let elemTy : Ty :=
              match resolveConsistentLayout? localDecls layouts ty with
              | .some (_, { fields := .array _ _, fieldLayouts := elemLIdx :: _, .. }) =>
                { kind := elem, layoutIdx := elemLIdx }
              | _ => { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
            match exactTyByteSize? localDecls layouts elemTy with
            | .none => .none
            | .some elemSz =>
              match Nat.beq (length bytes) (Nat.mul elemSz n) with
              | false => .none
              | true =>
                match
                  decodePartialUninitArrayChunks
                    (fun chunk =>
                      decodePartialUninitValue
                        mem localDecls layouts true fuel' (.some elemTy) chunk)
                    elemSz
                    n
                    bytes
                with
                | .some elems => .some (.aggregate 0 elems)
                | .none => .none
        | .tuple (k :: .nil) =>
          let innerTy : Ty :=
            match resolveConsistentLayout? localDecls layouts ty with
            | .some (_, { fields := .arbitrary _ _, fieldLayouts := fIdx :: .nil, .. }) =>
              { kind := k, layoutIdx := fIdx }
            | _ => { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
          match
            decodePartialUninitValue mem localDecls layouts allowUninitLeaf fuel' (.some innerTy) bytes
          with
          | .some v0 => .some (.aggregate 0 (v0 :: .nil))
          | .none => .none
        | .tuple ks =>
          match resolveConsistentLayout? localDecls layouts ty with
          | .some (_, l) =>
            match l.fields, l.variants with
            | .arbitrary offsets _, .single expectedVar =>
              match
                Bool.and (Nat.beq (length offsets) (length ks)) (Nat.beq (length bytes) l.size.bytes)
              with
              | false => .none
              | true =>
                match allBytesUninit bytes with
                | true => .none
                | false =>
                  let fIdxs : List Nat :=
                    match Nat.beq (length l.fieldLayouts) (length ks) with
                    | true => l.fieldLayouts
                    | false => .nil
                  match
                    decodeTupleFieldsAtOffsetsWith
                      (fun fk fIdxOpt slice =>
                        let fTy : Ty :=
                          match fIdxOpt with
                          | .some fIdx => { kind := fk, layoutIdx := fIdx }
                          | .none => { kind := fk, layoutIdx := unresolvedLayoutIdx layouts }
                        decodePartialUninitValue mem localDecls layouts true fuel' (.some fTy) slice)
                      localDecls
                      layouts
                      bytes
                      offsets
                      ks
                      fIdxs
                  with
                  | .some vals => .some (.aggregate expectedVar vals)
                  | .none => .none
            | _, _ => .none
          | .none => .none
        | .adt _ _ | .closure _ _ =>
          match resolveConsistentLayout? localDecls layouts ty with
          | .some (lIdx, _) => decodeValueAtLayoutIdx mem layouts true (.succ fuel') lIdx bytes
          | .none => .none
        | _ => .none

/--
Convert a `List AbstractByte` into `List (Option UInt8)` for a global
`CapturedAllocation`.
-/
def abstractBytesToGlobalOptBytes : List AbstractByte → List (Option UInt8)
  | .nil => .nil
  | .uninit :: rest => .none :: abstractBytesToGlobalOptBytes rest
  | .init b _ :: rest => .some b :: abstractBytesToGlobalOptBytes rest

/--
Build global relocation records `(byteOffset, ProvenancePtr)` from `bytes` using
pointer word size `ptrBytes`. Downstream `commitRootAbstractBytes` re-reads
`globalAllocSliceToAbstractBytes` and enforces `abstractBytesEq`, so any partial
pointer or 32-bit relocation width mismatch fails closed `.unsupported`.
-/
def buildGlobalRelocsAux (ptrBytes : Nat) : Nat → Nat → List AbstractByte → List (Nat × ProvenancePtr)
  | _, _, .nil => .nil
  | off, .succ skip, _ :: rest => buildGlobalRelocsAux ptrBytes (Nat.add off 1) skip rest
  | off, .zero, b :: rest =>
    match b with
    | .init _ (.some frag) =>
      let window := takeAbstractBytes ptrBytes (b :: rest)
      match Nat.beq (length window) ptrBytes, abstractBytesCoherentPtrProv? window with
      | true, .some wFrag =>
        match Bool.and (Nat.beq frag.allocId wFrag.allocId) (Nat.beq wFrag.ptrBytes ptrBytes), ptrBytes with
        | true, .succ ptrBytes' =>
          (off, { allocId := wFrag.allocId, offsetBytes := wFrag.origOffset }) ::
            buildGlobalRelocsAux ptrBytes (Nat.add off 1) ptrBytes' rest
        | _, _ => buildGlobalRelocsAux ptrBytes (Nat.add off 1) 0 rest
      | _, _ => buildGlobalRelocsAux ptrBytes (Nat.add off 1) 0 rest
    | _ => buildGlobalRelocsAux ptrBytes (Nat.add off 1) 0 rest

/--
Replace the `CapturedAllocation` with `allocId` in `globals`.
-/
def updateGlobalAllocById
    (allocId : AllocId)
    (updated : CapturedAllocation) :
    List CapturedAllocation → Option (List CapturedAllocation)
  | .nil => .none
  | g :: rest =>
    match Nat.beq g.allocId allocId with
    | true => .some (updated :: rest)
    | false =>
      match updateGlobalAllocById allocId updated rest with
      | .some rest' => .some (g :: rest')
      | .none => .none

/--
Commit a full root allocation byte image `newRootBytes` back into `ep` with
mandatory round-trip verification:
- On **global allocations**: requires `gAlloc.mutability == .mut` (else `.ub`),
  updates bytes & relocations, re-reads `globalAllocSliceToAbstractBytes`, and
  enforces exact `abstractBytesEq` (failing closed `.unsupported` on partial
  pointers or relocation width bleed).
- On **stack locals**: if all bytes are `.uninit`, commits `LocalSlot.uninit`;
  otherwise decodes via `decodePartialUninitValue`, re-encodes via
  `encodeRawValueBytes`, and enforces `abstractBytesRefine reencoded newRootBytes`
  (failing closed `.unsupported` if any byte or provenance would be altered or
  uninit padding would be promoted back to initialized).
-/
def commitRootAbstractBytes
    (mem : Memory)
    (locals : List LocalSlot)
    (ep : ResolvedMemEndpoint)
    (newRootBytes : List AbstractByte) :
    MemOpRes (List LocalSlot × Memory) :=
  match Nat.beq (length newRootBytes) ep.allocSize with
  | false => .unsupported
  | true =>
    match ep.globalAlloc? with
    | .some gAlloc =>
      match gAlloc.mutability with
      | .not => .ub
      | .mut =>
        let ptrBytes := layoutPointerBytes ep.targetLayouts
        let updatedAlloc : CapturedAllocation := {
          gAlloc with
          bytes := abstractBytesToGlobalOptBytes newRootBytes
          relocations := buildGlobalRelocsAux ptrBytes 0 0 newRootBytes
        }
        match globalAllocSliceToAbstractBytes updatedAlloc 0 ep.allocSize ptrBytes with
        | .none => .unsupported
        | .some rereadBytes =>
          match abstractBytesEq rereadBytes newRootBytes with
          | false => .unsupported
          | true =>
            match updateGlobalAllocById gAlloc.allocId updatedAlloc mem.globals with
            | .some globals' => .ok (locals, { mem with globals := globals' })
            | .none => .ub
    | .none =>
      match ep.allocKey with
      | .global _ => .unsupported
      | .stack frameDepth targetLocal =>
        match allBytesUninit newRootBytes with
        | true =>
          match
            writeFrameLocalSlot locals mem.callStack mem.callerLocals frameDepth targetLocal .uninit
          with
          | .some (locals', callStack', callerLocals') =>
            .ok (locals', { mem with callStack := callStack', callerLocals := callerLocals' })
          | .none => .ub
        | false =>
          match
            decodePartialUninitValue
              mem ep.targetDecls ep.targetLayouts false defaultCodecFuel ep.rootTy? newRootBytes
          with
          | .none => .unsupported
          | .some decodedVal =>
            match
              encodeRawValueBytes
                mem ep.targetDecls ep.targetLayouts defaultCodecFuel ep.rootTy? decodedVal
            with
            | .none => .unsupported
            | .some reencoded =>
              match abstractBytesRefine reencoded newRootBytes with
              | false => .unsupported
              | true =>
                match
                  writeFrameLocalSlot
                    locals mem.callStack mem.callerLocals frameDepth targetLocal (.init decodedVal)
                with
                | .some (locals', callStack', callerLocals') =>
                  .ok (locals', { mem with callStack := callStack', callerLocals := callerLocals' })
                | .none => .ub

/--
Overlapping `memmove` byte-copy core (`core::intrinsics::copy`) for a positive
`byteCount > 0`:
- **Phase A (read-snapshot)**: resolves `srcPtr` to a live endpoint, checks
  bounds and tag window (`endpointAccessCheck`), snapshots `byteCount` raw
  `AbstractByte`s preserving provenance and `.uninit`, and applies exact-range
  Tree Borrows read transitions yielding `borrows₁`.
- **Phase B (write on post-read `borrows₁`)**: resolves `dstPtr` against
  `borrows₁` (catching sibling `.unique` -> `.frozen` read-then-write UB),
  checks bounds, tag window, and global mutability, applies exact-range Tree
  Borrows write transitions yielding `borrows₂`, patches the snapshot into `dst`,
  and commits via `commitRootAbstractBytes`.

Reference (`core::ptr::copy` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L554-L589>

> "/// Copies `count * size_of::<T>()` bytes from `src` to `dst`. The source
> /// and destination may overlap.
> ...
> /// Copying takes place as if the bytes were copied from `src`
> /// to a temporary array and then copied from the array to `dst`.
> ///
> /// The copy is \"untyped\" in the sense that data may be uninitialized or otherwise violate the
> /// requirements of `T`. The initialization state is preserved exactly.
> ...
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes or that number must be 0,
> ///   and `dst` must remain valid even when `src` is read for `count * size_of::<T>()` bytes. (This
> ///   means if the memory ranges overlap, the `dst` pointer must not be invalidated by `src` reads.)"
-/
def evalCopyMemory
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (srcPtr dstPtr : ProvenancePtr)
    (byteCount : Nat) :
    MemOpRes (List LocalSlot × Memory) :=
  match resolveLiveMemEndpoint s locals bodyLocalDecls bodyLayouts srcPtr with
  | .ub => .ub
  | .unsupported => .unsupported
  | .ok srcEp =>
    match Nat.ble (Nat.add srcEp.effOff byteCount) srcEp.allocSize with
    | false => .ub
    | true =>
      match resolveLiveMemEndpoint s locals bodyLocalDecls bodyLayouts dstPtr with
      | .ub => .ub
      | .unsupported => .unsupported
      | .ok dstEp0 =>
        match Nat.ble (Nat.add dstEp0.effOff byteCount) dstEp0.allocSize with
        | false => .ub
        | true =>
          let dstWritable : Bool :=
            match dstEp0.globalAlloc? with
            | .some g => match g.mutability with | .mut => true | .not => false
            | .none => true
          match dstWritable with
          | false => .ub
          | true =>
            match endpointAccessCheck srcEp byteCount with
            | .ub => .ub
            | .unsupported => .unsupported
            | .ok () =>
              let borrows₁Opt : Option (List BorrowEntry) :=
                match srcEp.borrow? with
                | .none => .some s.memory.borrows
                | .some (srcTag, srcEntry) =>
                  borrowsAfterReadAccess
                    s.memory.borrows
                    s.memory.activeProtectors
                    srcEp.targetDecls
                    srcEp.targetLayouts
                    srcTag
                    srcEntry
                    srcEp.effOff
                    byteCount
              match borrows₁Opt with
              | .none => .ub
              | .some borrows₁ =>
                let s₁ : MachineState := { s with memory := { s.memory with borrows := borrows₁ } }
                match resolveLiveMemEndpoint s₁ locals bodyLocalDecls bodyLayouts dstPtr with
                | .ub => .ub
                | .unsupported => .unsupported
                | .ok dstEp =>
                  match endpointAccessCheck dstEp byteCount with
                  | .ub => .ub
                  | .unsupported => .unsupported
                  | .ok () =>
                    let borrows₂Opt : Option (List BorrowEntry) :=
                      match dstEp.borrow? with
                      | .none => .some borrows₁
                      | .some (dstTag, dstEntry) =>
                        borrowsAfterWriteAccess
                          borrows₁
                          s.memory.activeProtectors
                          dstEp.targetDecls
                          dstEp.targetLayouts
                          dstTag
                          dstEntry
                          dstEp.effOff
                          byteCount
                    match borrows₂Opt with
                    | .none => .ub
                    | .some borrows₂ =>
                      let mem₂ : Memory := { s.memory with borrows := borrows₂ }
                      match readRootAbstractBytes s.memory srcEp with
                      | .none => .unsupported
                      | .some srcRootBytes =>
                        match sliceAbstractBytes srcRootBytes srcEp.effOff byteCount with
                        | .none => .ub
                        | .some snapshot =>
                          match readRootAbstractBytes mem₂ dstEp with
                          | .none => .unsupported
                          | .some dstRootBytes =>
                            match writeAbstractBytesAt dstRootBytes dstEp.effOff snapshot with
                            | .none => .ub
                            | .some patchedRootBytes =>
                              commitRootAbstractBytes mem₂ locals dstEp patchedRootBytes

/-! ### 3-Way Layout- and Target-Width-Aware Typed Byte & Value Validation -/

/--
Validate all fields of a tuple at `offsets`, pairing each element's `RigidTy`
with its optional `TypeLayout` index from `fieldLayouts` so type-level validity
invariants (`&!`, `&[T]`/`&str` lengths, `dyn` vtables, `char`) are enforced.
-/
def validateTupleFieldsBytesWith
    (validateField : RigidTy → Option LayoutIdx → List AbstractByte → TypedValidity)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List RigidTy → List Nat → TypedValidity
  | .nil, .nil, _ => .valid
  | off :: restOffs, k :: restKs, fIdxs =>
    let (fIdxOpt, restIdxs) : Option LayoutIdx × List Nat :=
      match fIdxs with
      | fIdx :: tail => (.some fIdx, tail)
      | .nil => (.none, .nil)
    let fTy : Ty :=
      match fIdxOpt with
      | .some fIdx => { kind := k, layoutIdx := fIdx }
      | .none => { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
    let headRes : TypedValidity :=
      match exactTyByteSize? localDecls layouts fTy with
      | .none => .unsupported
      | .some fSz =>
        match sliceAbstractBytes bytes off.bytes fSz with
        | .none => .unsupported
        | .some slice => validateField k fIdxOpt slice
    TypedValidity.combine headRes fun _ =>
      validateTupleFieldsBytesWith
        validateField localDecls layouts bytes restOffs restKs restIdxs
  | _, _, _ => .unsupported

/--
Validate all fields of a layout's `.arbitrary` shape at `offsets` using
`fieldLayouts` (combining with `TypedValidity.combine` so an unresolved or
unsupported earlier field never masks a definite `.ub` in a later field).
-/
def validateLayoutFieldsWith
    (validateAt : LayoutIdx → List AbstractByte → TypedValidity)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List Nat → TypedValidity
  | .nil, .nil => .valid
  | off :: restOffs, fIdx :: restIdxs =>
    let headRes : TypedValidity :=
      match LayoutTable.lookup layouts fIdx with
      | .none => .unsupported
      | .some fl =>
        match sliceAbstractBytes bytes off.bytes fl.size.bytes with
        | .none => .unsupported
        | .some slice => validateAt fIdx slice
    TypedValidity.combine headRes fun _ =>
      validateLayoutFieldsWith validateAt layouts bytes restOffs restIdxs
  | _, _ => .unsupported

/--
Validate `count` array chunks at stride `stride` starting at `curOff`.
-/
def validateArrayChunksWith
    (validateElem : List AbstractByte → TypedValidity)
    (bytes : List AbstractByte)
    (elemSize stride curOff : Nat) :
    Nat → TypedValidity
  | .zero => .valid
  | .succ rem =>
    match sliceAbstractBytes bytes curOff elemSize with
    | .none => .unsupported
    | .some slice =>
      TypedValidity.combine (validateElem slice) fun _ =>
        validateArrayChunksWith validateElem bytes elemSize stride (Nat.add curOff stride) rem

/--
3-way layout-directed byte-slice validity checker for `layouts.entries[lIdx]`
(used for ADTs, closures, and laid-out tuples/arrays in `typed_swap_nonoverlapping`).

Modeling choice: `TypeLayout` carries `fieldLayouts : List LayoutIdx` and
`ScalarLayout` valid ranges without per-field `RigidTy`s. Direct `&!`, arrays
`[&!; n]`, and tuples `(..., &!)` reject uninhabited pointees via
`referenceToUninhabited` in `validateTypedBytes`, while a `&!` stored inside an
ADT/closure field relies on `rustc`'s captured `TypeLayout` (`isUninhabited` /
`variants = .empty` on the field or enclosing layout) because `TypeLayout` does
not record pointee `RigidTy`s for pointer fields.
-/
def validateTypedBytesForLayoutIdx
    (mem : Memory)
    (layouts : LayoutTable) :
    Nat → LayoutIdx → List AbstractByte → TypedValidity
  | .zero, _, _ => .unsupported
  | .succ fuel', lIdx, bytes =>
    match layouts.isLittleEndian with
    | false => .unsupported
    | true =>
      match LayoutTable.lookup layouts lIdx with
      | .none => .unsupported
      | .some l =>
        match TypeLayout.isWellFormed l with
        | false => .unsupported
        | true =>
          match l.isUninhabited with
          | true => .ub
          | false =>
            match Nat.beq (length bytes) l.size.bytes with
            | false => .unsupported
            | true =>
              match l.variants with
              | .empty => .ub
              | .multiple _ _ _ => .unsupported
              | .single _ =>
                match l.fields with
                | .union _ => .valid
                | .primitive =>
                  match Nat.beq l.size.bytes 0 with
                  | true => .valid
                  | false =>
                    match l.backendRepr with
                    | .scalar s0 => validateScalarLayoutBytes mem layouts s0 bytes
                    | _ => .unsupported
                | .arbitrary .nil _ => .valid
                | .arbitrary offsets memIdx =>
                  match Nat.beq (length l.fieldLayouts) (length offsets) with
                  | true =>
                    validateLayoutFieldsWith
                      (fun fIdx bs => validateTypedBytesForLayoutIdx mem layouts fuel' fIdx bs)
                      layouts
                      bytes
                      offsets
                      l.fieldLayouts
                  | false =>
                    match offsets, l.backendRepr with
                    | off0 :: .nil, .scalar s0 =>
                      match scalarLayoutTargetByteWidth layouts s0 with
                      | .some sz0 =>
                        match sliceAbstractBytes bytes off0.bytes sz0 with
                        | .some sl0 => validateScalarLayoutBytes mem layouts s0 sl0
                        | .none => .unsupported
                      | .none => .unsupported
                    | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
                      match
                        scalarPairOffsetsValid
                          layouts (off0 :: off1 :: .nil) memIdx s0 s1 l.size.bytes
                      with
                      | .some (firstOff, sz0, secondOff, sz1, _) =>
                        match
                          sliceAbstractBytes bytes firstOff sz0,
                          sliceAbstractBytes bytes secondOff sz1
                        with
                        | .some sl0, .some sl1 =>
                          TypedValidity.combine (validateScalarLayoutBytes mem layouts s0 sl0) fun _ =>
                            validateScalarLayoutBytes mem layouts s1 sl1
                        | _, _ => .unsupported
                      | .none => .unsupported
                    | _, _ => .unsupported
                | .array stride count =>
                  match Nat.beq count 0 with
                  | true => .valid
                  | false =>
                    match Nat.beq l.size.bytes (Nat.mul stride.bytes count) with
                    | false => .unsupported
                    | true =>
                      match l.fieldLayouts with
                      | .nil => .unsupported
                      | elemLIdx :: _ =>
                        match LayoutTable.lookup layouts elemLIdx with
                        | .none => .unsupported
                        | .some elemFl =>
                          match Nat.ble elemFl.size.bytes stride.bytes with
                          | false => .unsupported
                          | true =>
                            validateArrayChunksWith
                              (fun bs =>
                                validateTypedBytesForLayoutIdx mem layouts fuel' elemLIdx bs)
                              bytes
                              elemFl.size.bytes
                              stride.bytes
                              0
                              count

/--
3-way byte-slice validity checker for a typed value of `ty : Ty`
(`typed_swap_nonoverlapping`, `kani#5205`):
- Enforces `bool` (`0`/`1`), `char` (non-surrogate `≤ 0x10FFFF`), integer/float
  initialization and non-provenance, non-null `fn()` and `&T`, uninhabited-pointee
  `&!` rejection, wide-pointer metadata (slice length `≤ isize::MAX` and non-null
  `dyn` vtables even on raw `*const dyn Trait`), custom-DST pointer sizing, and
  layout-driven ADT/tuple/array validation (never substituting generic `args` as
  field types).

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution are “valid”, and producing an invalid value is hence immediate UB."
-/
def validateTypedBytes
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → List AbstractByte → TypedValidity
  | .zero, _, _ => .unsupported
  | .succ fuel', ty, bytes =>
    match layouts.isLittleEndian with
    | false => .unsupported
    | true =>
      let ptrBytes := layoutPointerBytes layouts
      match ty.kind with
      | .never => .ub
      | .bool =>
        match Nat.beq (length bytes) 1 with
        | false => .unsupported
        | true =>
          match hasUninitByte bytes with
          | true => .ub
          | false =>
            match bytesHaveRealProvenance mem bytes with
            | true => .unsupported
            | false =>
              match decodeScalarBytes bytes false with
              | .some (sv, _) =>
                match Nat.ble sv.bits 1 with
                | true => .valid
                | false => .ub
              | .none => .ub
      | .char =>
        match Nat.beq (length bytes) 4 with
        | false => .unsupported
        | true =>
          match hasUninitByte bytes with
          | true => .ub
          | false =>
            match bytesHaveRealProvenance mem bytes with
            | true => .unsupported
            | false =>
              match decodeScalarBytes bytes false with
              | .some (sv, _) =>
                match isValidCharCode sv.bits with
                | true => .valid
                | false => .ub
              | .none => .ub
      | .int _ | .uint _ =>
        match intTyTargetBytes layouts ty.kind with
        | .none => .unsupported
        | .some sz =>
          match Nat.beq (length bytes) sz with
          | false => .unsupported
          | true =>
            match hasUninitByte bytes with
            | true => .ub
            | false =>
              match bytesHaveRealProvenance mem bytes with
              | true => .unsupported
              | false => .valid
      | .float w =>
        match Nat.beq (length bytes) (floatTyByteWidth w) with
        | false => .unsupported
        | true =>
          match hasUninitByte bytes with
          | true => .ub
          | false =>
            match bytesHaveRealProvenance mem bytes with
            | true => .unsupported
            | false => .valid
      | .tuple .nil | .fnDef _ _ =>
        match bytes with
        | .nil => .valid
        | _ :: _ => .unsupported
      | .fnPtr _ _ _ _ => validateNonNullPtrBytes mem ptrBytes bytes
      | .ref _ pt =>
        match knownWidePointeeTailAux? 8 pt with
        | .some tailTy =>
          let hasHeader :=
            match pt with
            | .tuple _ => true
            | _ => false
          match Nat.beq (length bytes) (Nat.mul 2 ptrBytes) with
          | false =>
            match Nat.beq (length bytes) ptrBytes with
            | true => .ub
            | false => .unsupported
          | true =>
            let dBs := takeAbstractBytes ptrBytes bytes
            let mBs := dropAbstractBytes ptrBytes bytes
            TypedValidity.combine (validateNonNullPtrBytes mem ptrBytes dBs) fun _ =>
              validateWideMetaBytes mem localDecls layouts true hasHeader tailTy mBs
        | .none =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | false =>
            match referenceToUninhabited localDecls layouts pt with
            | true => .ub
            | false => validateNonNullPtrBytes mem ptrBytes bytes
          | true =>
            match declPtrToPointeeByteSize? localDecls layouts pt with
            | .some sz =>
              match Nat.beq sz ptrBytes with
              | true =>
                match referenceToUninhabited localDecls layouts pt with
                | true => .ub
                | false => validateNonNullPtrBytes mem ptrBytes bytes
              | false =>
                match Nat.beq sz (Nat.mul 2 ptrBytes) with
                | true =>
                  match Nat.beq (length bytes) sz with
                  | false =>
                    match Nat.beq (length bytes) ptrBytes with
                    | true => .ub
                    | false => .unsupported
                  | true =>
                    let dBs := takeAbstractBytes ptrBytes bytes
                    match validateNonNullPtrBytes mem ptrBytes dBs with
                    | .ub => .ub
                    | _ => .unsupported
                | false => .unsupported
            | .none =>
              match Nat.beq (length bytes) (Nat.mul 2 ptrBytes) with
              | true =>
                let dBs := takeAbstractBytes ptrBytes bytes
                match validateNonNullPtrBytes mem ptrBytes dBs with
                | .ub => .ub
                | _ => .unsupported
              | false => .unsupported
      | .rawPtr _ pt =>
        match knownWidePointeeTailAux? 8 pt with
        | .some tailTy =>
          let hasHeader :=
            match pt with
            | .tuple _ => true
            | _ => false
          match Nat.beq (length bytes) (Nat.mul 2 ptrBytes) with
          | false =>
            match Nat.beq (length bytes) ptrBytes with
            | true => .ub
            | false => .unsupported
          | true =>
            let dBs := takeAbstractBytes ptrBytes bytes
            let mBs := dropAbstractBytes ptrBytes bytes
            match hasUninitByte dBs with
            | true => .ub
            | false => validateWideMetaBytes mem localDecls layouts false hasHeader tailTy mBs
        | .none =>
          match ptrPointeeMayBeUnsizedAux 8 pt with
          | false =>
            match Nat.beq (length bytes) ptrBytes with
            | false => .unsupported
            | true =>
              match hasUninitByte bytes with
              | true => .ub
              | false => .valid
          | true =>
            match declPtrToPointeeByteSize? localDecls layouts pt with
            | .some sz =>
              match Nat.beq sz ptrBytes with
              | true =>
                match Nat.beq (length bytes) ptrBytes with
                | false => .unsupported
                | true =>
                  match hasUninitByte bytes with
                  | true => .ub
                  | false => .valid
              | false =>
                match Nat.beq sz (Nat.mul 2 ptrBytes) with
                | true =>
                  match Nat.beq (length bytes) sz with
                  | false =>
                    match Nat.beq (length bytes) ptrBytes with
                    | true => .ub
                    | false => .unsupported
                  | true =>
                    let dBs := takeAbstractBytes ptrBytes bytes
                    match hasUninitByte dBs with
                    | true => .ub
                    | false => .unsupported
                | false => .unsupported
            | .none => .unsupported
      | .array elem n =>
        match Nat.beq n 0 with
        | true =>
          match bytes with
          | .nil => .valid
          | _ :: _ => .unsupported
        | false =>
          let elemTy : Ty :=
            match resolveConsistentLayout? localDecls layouts ty with
            | .some (_, { fields := .array _ _, fieldLayouts := elemLIdx :: _, .. }) =>
              { kind := elem, layoutIdx := elemLIdx }
            | _ => { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
          match exactTyByteSize? localDecls layouts elemTy with
          | .none => .unsupported
          | .some elemSz =>
            match Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => .unsupported
            | true =>
              validateArrayChunksWith
                (fun bs => validateTypedBytes mem localDecls layouts fuel' elemTy bs)
                bytes
                elemSz
                elemSz
                0
                n
      | .tuple (k :: .nil) =>
        let innerTy : Ty :=
          match resolveConsistentLayout? localDecls layouts ty with
          | .some (_, { fields := .arbitrary _ _, fieldLayouts := fIdx :: .nil, .. }) =>
            { kind := k, layoutIdx := fIdx }
          | _ => { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
        validateTypedBytes mem localDecls layouts fuel' innerTy bytes
      | .tuple ks =>
        match resolveConsistentLayout? localDecls layouts ty with
        | .some (_, l) =>
          match l.fields, l.variants with
          | .arbitrary offsets _, .single _ =>
            match Nat.beq (length offsets) (length ks), Nat.beq (length bytes) l.size.bytes with
            | true, true =>
              let fIdxs : List Nat :=
                match Nat.beq (length l.fieldLayouts) (length ks) with
                | true => l.fieldLayouts
                | false => .nil
              validateTupleFieldsBytesWith
                (fun fk fIdxOpt slice =>
                  let fTy : Ty :=
                    match fIdxOpt with
                    | .some fIdx => { kind := fk, layoutIdx := fIdx }
                    | .none => { kind := fk, layoutIdx := unresolvedLayoutIdx layouts }
                  validateTypedBytes mem localDecls layouts fuel' fTy slice)
                localDecls
                layouts
                bytes
                offsets
                ks
                fIdxs
            | _, _ => .unsupported
          | _, _ => .unsupported
        | .none => .unsupported
      | .adt _ _ | .closure _ _ =>
        match resolveConsistentLayout? localDecls layouts ty with
        | .some (lIdx, _) => validateTypedBytesForLayoutIdx mem layouts (.succ fuel') lIdx bytes
        | .none => .unsupported
      | _ => .unsupported

/--
Fold `TypedValidity` over a list of `LayoutIdx`s to check whether every field
layout permits a wholly uninitialized value.
-/
def allFieldLayoutsPermitUninit
    (check : LayoutIdx → TypedValidity) :
    List Nat → TypedValidity
  | .nil => .valid
  | fIdx :: rest =>
    TypedValidity.combine (check fIdx) fun _ => allFieldLayoutsPermitUninit check rest

/--
Test whether `layouts.entries[lIdx]` permits a wholly uninitialized value
(`Value.uninit`): `.valid` for inhabited ZSTs, inhabited unions, and arrays /
single-variant structs whose fields all permit uninit; `.ub` for uninhabited
types, non-ZST primitives, and multi-variant enums; `.unsupported` when layout
information is missing.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "Note: Uninitialized memory is also implicitly invalid for any type that has a restricted set of valid values. In other words, the only cases in which reading uninitialized memory is permitted are inside `union`s and in “padding” (the gaps between the fields of a type)."
-/
def layoutPermitsUninit (layouts : LayoutTable) : Nat → LayoutIdx → TypedValidity
  | .zero, _ => .unsupported
  | .succ fuel', lIdx =>
    match LayoutTable.lookup layouts lIdx with
    | .none => .unsupported
    | .some l =>
      match TypeLayout.isWellFormed l with
      | false => .unsupported
      | true =>
        match l.isUninhabited with
        | true => .ub
        | false =>
          match l.variants with
          | .empty => .ub
          | .multiple _ _ _ => .ub
          | .single _ =>
            match l.fields with
            | .union _ => .valid
            | .primitive =>
              match Nat.beq l.size.bytes 0 with
              | true => .valid
              | false => .ub
            | .arbitrary .nil _ => .valid
            | .arbitrary offsets _ =>
              match Nat.beq (length l.fieldLayouts) (length offsets) with
              | true =>
                allFieldLayoutsPermitUninit (layoutPermitsUninit layouts fuel') l.fieldLayouts
              | false =>
                match Nat.beq l.size.bytes 0 with
                | true => .valid
                | false => .unsupported
            | .array _ count =>
              match Nat.beq count 0 with
              | true => .valid
              | false =>
                match l.fieldLayouts with
                | elemLIdx :: _ => layoutPermitsUninit layouts fuel' elemLIdx
                | .nil => .unsupported

/--
Fold `TypedValidity` over tuple element `RigidTy`s paired with optional
`fieldLayouts` for `tyPermitsUninit`.
-/
def allTupleFieldsPermitUninit
    (check : RigidTy → Option LayoutIdx → TypedValidity) :
    List RigidTy → List Nat → TypedValidity
  | .nil, _ => .valid
  | k :: restKs, fIdx :: restIdxs =>
    TypedValidity.combine (check k (.some fIdx)) fun _ =>
      allTupleFieldsPermitUninit check restKs restIdxs
  | k :: restKs, .nil =>
    TypedValidity.combine (check k .none) fun _ =>
      allTupleFieldsPermitUninit check restKs .nil

/--
Test whether `ty : Ty` permits a wholly uninitialized value (`Value.uninit`) for
`black_box`.
-/
def tyPermitsUninit
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → TypedValidity
  | .zero, _ => .unsupported
  | .succ fuel', ty =>
    match ty.kind with
    | .never => .ub
    | .bool | .char | .int _ | .uint _ | .float _ => .ub
    | .ref _ _ | .rawPtr _ _ | .fnPtr _ _ _ _ => .ub
    | .tuple .nil | .fnDef _ _ => .valid
    | .array elem n =>
      match Nat.beq n 0 with
      | true => .valid
      | false =>
        let elemTy : Ty :=
          match resolveConsistentLayout? localDecls layouts ty with
          | .some (_, { fields := .array _ _, fieldLayouts := elemLIdx :: _, .. }) =>
            { kind := elem, layoutIdx := elemLIdx }
          | _ => { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
        tyPermitsUninit localDecls layouts fuel' elemTy
    | .tuple ks =>
      let fIdxs : List Nat :=
        match resolveConsistentLayout? localDecls layouts ty with
        | .some (_, l) =>
          match Nat.beq (length l.fieldLayouts) (length ks) with
          | true => l.fieldLayouts
          | false => .nil
        | .none => .nil
      allTupleFieldsPermitUninit
        (fun k fIdxOpt =>
          let fTy : Ty :=
            match fIdxOpt with
            | .some fIdx => { kind := k, layoutIdx := fIdx }
            | .none => { kind := k, layoutIdx := unresolvedLayoutIdx layouts }
          tyPermitsUninit localDecls layouts fuel' fTy)
        ks
        fIdxs
    | .adt _ _ | .closure _ _ =>
      match resolveConsistentLayout? localDecls layouts ty with
      | .some (lIdx, _) => layoutPermitsUninit layouts (.succ fuel') lIdx
      | .none => .unsupported
    | _ => .unsupported

/--
Validate a runtime `Value` against a `ScalarLayout` `sl` for `black_box`.
-/
def validateScalarLayoutValue
    (mem : Memory)
    (layouts : LayoutTable)
    (sl : ScalarLayout)
    (v : Value) :
    TypedValidity :=
  match scalarLayoutTargetByteWidth layouts sl with
  | .none => .unsupported
  | .some expectedSz =>
    let modW := scalarModulus expectedSz
    match sl with
    | .union _ =>
      match v with
      | .scalar sc =>
        match Bool.and (Nat.beq sc.sizeBytes expectedSz) (Nat.blt sc.bits modW) with
        | true => .valid
        | false => .ub
      | .ptr _ sz =>
        match Nat.beq sz expectedSz with
        | true => .valid
        | false => .ub
      | .aggregate _ _ => .unsupported
      | .unit => .ub
    | .initialized pk validRange =>
      match v with
      | .unit => .ub
      | .aggregate _ _ => .unsupported
      | .scalar sc =>
        match Bool.and (Nat.beq sc.sizeBytes expectedSz) (Nat.blt sc.bits modW) with
        | false => .ub
        | true =>
          match wrappingRangeContains validRange sc.bits with
          | false => .ub
          | true =>
            match charShapedSurrogate pk validRange sc.bits with
            | true => .unsupported
            | false => .valid
      | .ptr p sz =>
        match Nat.beq sz expectedSz with
        | false => .ub
        | true =>
          match pk with
          | .pointer _ =>
            match
              Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p))
            with
            | true =>
              match Bool.and (Nat.blt p.offsetBytes modW) (wrappingRangeContains validRange p.offsetBytes) with
              | true => .valid
              | false => .ub
            | false =>
              match validRangeCoversAllNonNull expectedSz validRange with
              | true => .valid
              | false => .unsupported
          | .int _ _ | .float _ =>
            match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
            | false => .unsupported
            | true =>
              match Bool.and (Nat.blt p.offsetBytes modW) (wrappingRangeContains validRange p.offsetBytes) with
              | false => .ub
              | true =>
                match charShapedSurrogate pk validRange p.offsetBytes with
                | true => .unsupported
                | false => .valid

/--
Validate wide-pointer metadata `metaVal : Value` for `black_box`.
-/
def validateWideMetaValue
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (isRef : Bool)
    (hasHeaderPrefix : Bool)
    (tailTy : RigidTy)
    (metaVal : Value) :
    TypedValidity :=
  let ptrBytes := layoutPointerBytes layouts
  match tailTy with
  | .dynamic _ =>
    match isNullThinPtr mem ptrBytes metaVal with
    | .none => .ub
    | .some true => .ub
    | .some false => .valid
  | .str =>
    match decodeUsizeArg? mem ptrBytes metaVal with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok lenBits =>
      match isRef with
      | false => .valid
      | true =>
        let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
        match Nat.ble lenBits isizeMax with
        | false => .ub
        | true =>
          match hasHeaderPrefix with
          | true => .unsupported
          | false => .valid
  | .slice elemTy =>
    match decodeUsizeArg? mem ptrBytes metaVal with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok lenBits =>
      match isRef with
      | false => .valid
      | true =>
        match exactRigidTyByteSize? localDecls layouts elemTy with
        | .none => .unsupported
        | .some elemSz =>
          let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
          match Nat.ble (Nat.mul lenBits elemSz) isizeMax with
          | false => .ub
          | true =>
            match hasHeaderPrefix with
            | true => .unsupported
            | false => .valid
  | _ => .unsupported

/--
Validate field values against `fieldLayouts`.
-/
def validateLayoutFieldsValuesWith
    (validateAt : LayoutIdx → Value → TypedValidity) :
    List Nat → List Value → TypedValidity
  | .nil, .nil => .valid
  | fIdx :: restIdxs, fv :: restVals =>
    TypedValidity.combine (validateAt fIdx fv) fun _ =>
      validateLayoutFieldsValuesWith validateAt restIdxs restVals
  | _, _ => .ub

/--
Validate all elements in a value list with `validateElem`.
-/
def validateValueListWith
    (validateElem : Value → TypedValidity) :
    List Value → TypedValidity
  | .nil => .valid
  | v :: rest =>
    TypedValidity.combine (validateElem v) fun _ => validateValueListWith validateElem rest

/--
Validate tuple field values paired with their `RigidTy`s (and optional
`fieldLayouts`).
-/
def validateTupleValuesWith
    (validateField : RigidTy → Option LayoutIdx → Value → TypedValidity) :
    List RigidTy → List Nat → List Value → TypedValidity
  | .nil, _, .nil => .valid
  | k :: restKs, fIdx :: restIdxs, fv :: restVals =>
    TypedValidity.combine (validateField k (.some fIdx) fv) fun _ =>
      validateTupleValuesWith validateField restKs restIdxs restVals
  | k :: restKs, .nil, fv :: restVals =>
    TypedValidity.combine (validateField k .none fv) fun _ =>
      validateTupleValuesWith validateField restKs .nil restVals
  | _, _, _ => .ub

/--
3-way layout-directed runtime `Value` validator for `layouts.entries[lIdx]`
(used by `black_box` on ADTs, closures, and laid-out fields).

Modeling choice: `TypeLayout` carries `fieldLayouts : List LayoutIdx` and
`ScalarLayout` valid ranges without per-field `RigidTy`s. Direct `&!`, arrays
`[&!; n]`, and tuples `(..., &!)` reject uninhabited pointees via
`referenceToUninhabited` in `validateBlackBoxValue`, while a `&!` stored inside
an ADT/closure field relies on `rustc`'s captured `TypeLayout` (`isUninhabited`
/ `variants = .empty` on the field or enclosing layout) because `TypeLayout`
does not record pointee `RigidTy`s for pointer fields.
-/
def validateValueAtLayoutIdx
    (mem : Memory)
    (layouts : LayoutTable) :
    Nat → LayoutIdx → Value → TypedValidity
  | .zero, _, _ => .unsupported
  | .succ fuel', lIdx, v =>
    match LayoutTable.lookup layouts lIdx with
    | .none => .unsupported
    | .some l =>
      match TypeLayout.isWellFormed l with
      | false => .unsupported
      | true =>
        match l.isUninhabited with
        | true => .ub
        | false =>
          match l.variants with
          | .empty => .ub
          | .multiple _ _ _ => .unsupported
          | .single expectedVar =>
            match l.fields with
            | .union _ => .valid
            | .primitive =>
              match Nat.beq l.size.bytes 0 with
              | true =>
                match v with
                | .unit => .valid
                | .aggregate varIdx .nil =>
                  match Nat.beq varIdx expectedVar with | true => .valid | false => .ub
                | _ => .ub
              | false =>
                match l.backendRepr with
                | .scalar s0 => validateScalarLayoutValue mem layouts s0 v
                | _ => .unsupported
            | .arbitrary .nil _ =>
              match v with
              | .unit => .valid
              | .aggregate varIdx .nil =>
                match Nat.beq varIdx expectedVar with | true => .valid | false => .ub
              | _ => .ub
            | .arbitrary offsets memIdx =>
              match v with
              | .aggregate varIdx fVals =>
                match
                  Bool.and
                    (Nat.beq varIdx expectedVar)
                    (Nat.beq (length fVals) (length offsets))
                with
                | false => .ub
                | true =>
                  match Nat.beq (length l.fieldLayouts) (length offsets) with
                  | true =>
                    validateLayoutFieldsValuesWith
                      (fun fIdx fv => validateValueAtLayoutIdx mem layouts fuel' fIdx fv)
                      l.fieldLayouts
                      fVals
                  | false =>
                    match offsets, fVals, l.backendRepr with
                    | _ :: .nil, v0 :: .nil, .scalar s0 =>
                      validateScalarLayoutValue mem layouts s0 v0
                    | off0 :: off1 :: .nil, v0 :: v1 :: .nil, .scalarPair s0 s1 =>
                      match
                        scalarPairOffsetsValid
                          layouts (off0 :: off1 :: .nil) memIdx s0 s1 l.size.bytes
                      with
                      | .some (_, _, _, _, swapped) =>
                        let (vFirst, vSecond) :=
                          match swapped with
                          | false => (v0, v1)
                          | true => (v1, v0)
                        TypedValidity.combine (validateScalarLayoutValue mem layouts s0 vFirst) fun _ =>
                          validateScalarLayoutValue mem layouts s1 vSecond
                      | .none => .unsupported
                    | _, _, _ => .unsupported
              | _ => .ub
            | .array _ count =>
              match Nat.beq count 0 with
              | true =>
                match v with
                | .unit => .valid
                | .aggregate varIdx .nil =>
                  match Nat.beq varIdx expectedVar with | true => .valid | false => .ub
                | _ => .ub
              | false =>
                match v with
                | .aggregate varIdx elems =>
                  match
                    Bool.and (Nat.beq varIdx expectedVar) (Nat.beq (length elems) count)
                  with
                  | false => .ub
                  | true =>
                    match l.fieldLayouts with
                    | elemLIdx :: _ =>
                      validateValueListWith
                        (fun ev => validateValueAtLayoutIdx mem layouts fuel' elemLIdx ev)
                        elems
                    | .nil => .unsupported
                | _ => .ub

/--
3-way layout- and target-width-aware runtime `Value` validator for
`core::intrinsics::black_box<T>(dummy: T) -> T`:
- Rejects invalid `bool`, invalid/surrogate `char`, wrong-width or out-of-range
  scalars (using `layoutPointerBytes` for `usize`/`isize`), null `&T`/wide
  `&[T]`/`&str`/`&dyn`/`fn()`, uninhabited-pointee `&!`, null `dyn` vtables on
  both `&dyn` and `*const dyn`, and oversized slice reference lengths.
- Fails closed `.unsupported` on unknown/unsized `T`, provenance in non-pointer
  scalars, `charShapedSurrogate` in layout scalars, unvalidated multi-variant
  enums, and unconfirmed custom-DST pointer widths.
- Note: `V2026_08_01.MirSemantics.Value` has no `.uninit` constructor (whole-
  local uninitialization is tracked at `LocalSlot.uninit`).

Reference (`library/core/src/hint.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/hint.rs#L315-L321>

> "/// An identity function that *__hints__* to the compiler to be maximally pessimistic about what
> /// `black_box` could do.
> ///
> /// Unlike [`std::convert::identity`], a Rust compiler is encouraged to assume that `black_box` can
> /// use `dummy` in any possible valid way that Rust code is allowed to without introducing undefined
> /// behavior in the calling code."
-/
def validateBlackBoxValue
    (mem : Memory)
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → Ty → Value → TypedValidity
  | .zero, _, _ => .unsupported
  | .succ fuel', ty, v =>
    let ptrBytes := layoutPointerBytes layouts
    match ty.kind with
    | .never => .ub
    | .bool =>
      match v with
      | .scalar sc =>
        match Bool.and (Nat.beq sc.sizeBytes 1) (Nat.ble sc.bits 1) with
        | true => .valid
        | false => .ub
      | .ptr p sz =>
        match Nat.beq sz 1 with
        | false => .ub
        | true =>
          match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
          | false => .unsupported
          | true =>
            match Nat.ble p.offsetBytes 1 with
            | true => .valid
            | false => .ub
      | _ => .ub
    | .char =>
      match v with
      | .scalar sc =>
        match Bool.and (Nat.beq sc.sizeBytes 4) (isValidCharCode sc.bits) with
        | true => .valid
        | false => .ub
      | .ptr p sz =>
        match Nat.beq sz 4 with
        | false => .ub
        | true =>
          match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
          | false => .unsupported
          | true =>
            match isValidCharCode p.offsetBytes with
            | true => .valid
            | false => .ub
      | _ => .ub
    | .int _ | .uint _ =>
      match intTyTargetBytes layouts ty.kind with
      | .none => .unsupported
      | .some sz =>
        let modSz := scalarModulus sz
        match v with
        | .scalar sc =>
          match Bool.and (Nat.beq sc.sizeBytes sz) (Nat.blt sc.bits modSz) with
          | true => .valid
          | false => .ub
        | .ptr p pSz =>
          match Nat.beq pSz sz with
          | false => .ub
          | true =>
            match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
            | true =>
              match Nat.blt p.offsetBytes modSz with | true => .valid | false => .ub
            | false => .unsupported
        | _ => .ub
    | .float w =>
      let sz := floatTyByteWidth w
      let modSz := scalarModulus sz
      match v with
      | .scalar sc =>
        match Bool.and (Nat.beq sc.sizeBytes sz) (Nat.blt sc.bits modSz) with
        | true => .valid
        | false => .ub
      | .ptr p pSz =>
        match Nat.beq pSz sz with
        | false => .ub
        | true =>
          match Bool.and (Nat.beq p.allocId 0) (Bool.not (isBackedPtr mem p)) with
          | true =>
            match Nat.blt p.offsetBytes modSz with | true => .valid | false => .ub
          | false => .unsupported
      | _ => .ub
    | .tuple .nil | .fnDef _ _ =>
      match v with
      | .unit => .valid
      | .aggregate 0 .nil => .valid
      | _ => .ub
    | .fnPtr _ _ _ _ =>
      match isNullThinPtr mem ptrBytes v with
      | .none => .ub
      | .some true => .ub
      | .some false => .valid
    | .ref _ pt =>
      match knownWidePointeeTailAux? 8 pt with
      | .some tailTy =>
        let hasHeader := match pt with | .tuple _ => true | _ => false
        match v with
        | .aggregate 0 (dVal :: mVal :: .nil) =>
          match isNullThinPtr mem ptrBytes dVal with
          | .none => .ub
          | .some true => .ub
          | .some false =>
            validateWideMetaValue mem localDecls layouts true hasHeader tailTy mVal
        | _ => .ub
      | .none =>
        match ptrPointeeMayBeUnsizedAux 8 pt with
        | false =>
          match referenceToUninhabited localDecls layouts pt with
          | true => .ub
          | false =>
            match isNullThinPtr mem ptrBytes v with
            | .none => .ub
            | .some true => .ub
            | .some false => .valid
        | true =>
          match declPtrToPointeeByteSize? localDecls layouts pt with
          | .some sz =>
            match Nat.beq sz ptrBytes with
            | true =>
              match referenceToUninhabited localDecls layouts pt with
              | true => .ub
              | false =>
                match isNullThinPtr mem ptrBytes v with
                | .none => .ub
                | .some true => .ub
                | .some false => .valid
            | false =>
              match Nat.beq sz (Nat.mul 2 ptrBytes) with
              | true =>
                match v with
                | .aggregate 0 (dVal :: mVal :: .nil) =>
                  match isNullThinPtr mem ptrBytes dVal, isValidWidePtrMetaValForWidth mem ptrBytes mVal with
                  | .none, _ => .ub
                  | .some true, _ => .ub
                  | _, false => .ub
                  | .some false, true => .unsupported
                | _ => .ub
              | false => .unsupported
          | .none =>
            match v with
            | .aggregate 0 (dVal :: mVal :: .nil) =>
              match isNullThinPtr mem ptrBytes dVal, isValidWidePtrMetaValForWidth mem ptrBytes mVal with
              | .none, _ => .ub
              | .some true, _ => .ub
              | _, false => .ub
              | .some false, true => .unsupported
            | _ =>
              match isNullThinPtr mem ptrBytes v with
              | .none => .ub
              | .some true => .ub
              | .some false => .unsupported
    | .rawPtr _ pt =>
      match knownWidePointeeTailAux? 8 pt with
      | .some tailTy =>
        let hasHeader := match pt with | .tuple _ => true | _ => false
        match v with
        | .aggregate 0 (dVal :: mVal :: .nil) =>
          match isNullThinPtr mem ptrBytes dVal with
          | .none => .ub
          | .some _ =>
            validateWideMetaValue mem localDecls layouts false hasHeader tailTy mVal
        | _ => .ub
      | .none =>
        match ptrPointeeMayBeUnsizedAux 8 pt with
        | false =>
          match isNullThinPtr mem ptrBytes v with
          | .none => .ub
          | .some _ => .valid
        | true =>
          match declPtrToPointeeByteSize? localDecls layouts pt with
          | .some sz =>
            match Nat.beq sz ptrBytes with
            | true =>
              match isNullThinPtr mem ptrBytes v with
              | .none => .ub
              | .some _ => .valid
            | false =>
              match Nat.beq sz (Nat.mul 2 ptrBytes) with
              | true =>
                match v with
                | .aggregate 0 (dVal :: mVal :: .nil) =>
                  match isNullThinPtr mem ptrBytes dVal, isValidWidePtrMetaValForWidth mem ptrBytes mVal with
                  | .none, _ => .ub
                  | _, false => .ub
                  | .some _, true => .unsupported
                | _ => .ub
              | false => .unsupported
          | .none =>
            match v with
            | .aggregate 0 (dVal :: mVal :: .nil) =>
              match isNullThinPtr mem ptrBytes dVal, isValidWidePtrMetaValForWidth mem ptrBytes mVal with
              | .none, _ => .ub
              | _, false => .ub
              | .some _, true => .unsupported
            | _ =>
              match isNullThinPtr mem ptrBytes v with
              | .none => .ub
              | .some _ => .unsupported
    | .array elem n =>
      match Nat.beq n 0 with
      | true =>
        match v with
        | .unit => .valid
        | .aggregate 0 .nil => .valid
        | _ => .ub
      | false =>
        match v with
        | .aggregate 0 elems =>
          match Nat.beq (length elems) n with
          | false => .ub
          | true =>
            let elemTy : Ty :=
              match resolveConsistentLayout? localDecls layouts ty with
              | .some (_, { fields := .array _ _, fieldLayouts := elemLIdx :: _, .. }) =>
                { kind := elem, layoutIdx := elemLIdx }
              | _ => { kind := elem, layoutIdx := unresolvedLayoutIdx layouts }
            validateValueListWith
              (fun ev => validateBlackBoxValue mem localDecls layouts fuel' elemTy ev)
              elems
        | _ => .ub
    | .tuple ks =>
      match v with
      | .aggregate 0 fVals =>
        match Nat.beq (length fVals) (length ks) with
        | false => .ub
        | true =>
          let fIdxs : List Nat :=
            match resolveConsistentLayout? localDecls layouts ty with
            | .some (_, l) =>
              match Nat.beq (length l.fieldLayouts) (length ks) with
              | true => l.fieldLayouts
              | false => .nil
            | .none => .nil
          validateTupleValuesWith
            (fun fk fIdxOpt fv =>
              let fTy : Ty :=
                match fIdxOpt with
                | .some fIdx => { kind := fk, layoutIdx := fIdx }
                | .none => { kind := fk, layoutIdx := unresolvedLayoutIdx layouts }
              validateBlackBoxValue mem localDecls layouts fuel' fTy fv)
            ks
            fIdxs
            fVals
      | _ => .ub
    | .adt _ _ | .closure _ _ =>
      match resolveConsistentLayout? localDecls layouts ty with
      | .some (lIdx, _) => validateValueAtLayoutIdx mem layouts (.succ fuel') lIdx v
      | .none => .unsupported
    | _ => .unsupported

end Trusted.Rustc.V2026_08_01.MirSemantics
