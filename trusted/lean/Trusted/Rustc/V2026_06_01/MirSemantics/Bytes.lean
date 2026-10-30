import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars

namespace Trusted.Rustc.V2026_06_01.MirSemantics

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst

/-!
Byte-level value representation (`AbstractByte`) and little-endian layout-driven
encoding and decoding (`encodeScalarBytes`, `decodeScalarBytes`,
`encodeValueToBytes`, `decodeValueFromBytes`) for `Runtime(PostCleanup)` MIR at
`rustc 1.98.0-nightly (14210df0e 2026-05-31)` (`#88`, `#100`, `#101`, `#102`).

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html>

> "The layout of a type is its size, alignment, and the relative offsets of its
> fields. For enums, how the discriminant is laid out and interpreted is also
> part of type layout."

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Producing an invalid value. Producing a value happens any time a value is
> assigned to or read from a place, passed to a function/primitive operation or
> returned from a function/primitive operation."
-/

/--
Alias for `ScalarInt` used by byte-level scalar encoding and decoding helpers.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The unsigned integer types consist of: ... u8, u16, u32, u64, u128, usize"
-/
abbrev ScalarVal : Type := ScalarInt

/--
Single byte in the abstract machine memory representation of a Rust value,
modeling initialized bytes (with optional pointer provenance `(allocId, tag)`)
and uninitialized or padding bytes (`.uninit`).

Constructor `.uninit` represents an uninitialized or padding byte; reading an
`.uninit` byte at a scalar, boolean, character, or pointer type produces
undefined behavior (`.none` during decoding). Constructor `.init` carries the
8-bit value `byte : UInt8` together with optional `(allocId, tag)` provenance
for pointer round-tripping.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The following is a non-exhaustive list of invalid values:
> - A value of any type, other than a union or raw pointer, with uninitialized
>   bytes (except for padding bytes, which may be uninitialized). Note that
>   reading an integer of any type from uninitialized memory is undefined
>   behavior."

Reference (`compiler/rustc_middle/src/mir/interpret/allocation.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L53-L63>

> "pub struct Allocation<Prov = AllocId, Extra = (), Bytes = Box<[u8]>>"
-/
inductive AbstractByte : Type where
  /-- Uninitialized or padding byte. -/
  | uninit : AbstractByte
  /-- Initialized byte `byte` with optional `(allocId, tag)` provenance. -/
  | init (byte : UInt8) (prov : Option (Nat × Nat)) : AbstractByte

/--
Test whether an `AbstractByte` is initialized (`.init _ _`).
-/
@[reducible]
def AbstractByte.isInit : AbstractByte → Bool
  | .uninit => false
  | .init _ _ => true

/--
Combine provenance annotations from two adjacent initialized bytes, retaining
the first present `(allocId, tag)` pair.
-/
@[reducible]
def mergeByteProvenance
    (p₁ p₂ : Option (Nat × Nat)) :
    Option (Nat × Nat) :=
  match p₂ with
  | .none => p₁
  | .some _ =>
    match p₁ with
    | .some _ => p₁
    | .none => p₂

/--
Encode the low `numBytes` bytes of `bits` in little-endian order, attaching
provenance `prov` to each emitted `AbstractByte.init`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L259-L264>

> "pub enum Endian {
>     Little,
>     Big,
> }"
-/
@[reducible]
def encodeLittleEndianBytes
    (bits : Nat) :
    Nat → Option (Nat × Nat) → List AbstractByte
  | .zero, _ => .nil
  | .succ rem, prov =>
    .init (UInt8.ofNat bits) prov ::
      encodeLittleEndianBytes (Nat.div bits 256) rem prov

/--
Encode a non-zero-width `ScalarVal` into `sv.sizeBytes` little-endian
`AbstractByte`s carrying optional provenance `prov`.

Returns `.none` when `sv.sizeBytes == 0`.

Reference (The Rust Reference, "Numeric types"):
<https://doc.rust-lang.org/1.98.0/reference/types/numeric.html>

> "The unsigned integer types consist of:
>
> Type   Minimum   Maximum
> u8     0         2^8-1
> u16    0         2^16-1
> u32    0         2^32-1
> u64    0         2^64-1
> u128   0         2^128-1"
-/
@[reducible]
def encodeScalarBytes
    (sv : ScalarVal)
    (prov : Option (Nat × Nat) := .none) :
    Option (List AbstractByte) :=
  match Nat.beq sv.sizeBytes 0 with
  | true => .none
  | false => .some (encodeLittleEndianBytes sv.bits sv.sizeBytes prov)

/--
Decode a list of little-endian `AbstractByte`s into an unsigned bit pattern
`bits : Nat` and combined provenance `Option (Nat × Nat)`.

Returns `.none` if any byte in the list is `.uninit`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Note that reading an integer of any type from uninitialized memory is
> undefined behavior."
-/
@[reducible]
def decodeLittleEndianBytes :
    List AbstractByte → Option (Nat × Option (Nat × Nat))
  | .nil => .some (0, .none)
  | .uninit :: _ => .none
  | .init b prov :: rest =>
    match decodeLittleEndianBytes rest with
    | .some (highBits, restProv) =>
      .some
        (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits),
         mergeByteProvenance prov restProv)
    | .none => .none

/--
Decode a non-empty list of little-endian `AbstractByte`s into a `ScalarVal` of
width `length bytes` together with its combined provenance.

In Anneal's MIR semantics, both signed (`signed = true`) and unsigned
(`signed = false`) `ScalarVal` values store their canonical two's-complement
unsigned bit pattern in `[0, 2^(8 * sizeBytes))`. Returns `.none` if `bytes` is
empty or contains any `.uninit` byte.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Note that reading an integer of any type from uninitialized memory is
> undefined behavior."
-/
@[reducible]
def decodeScalarBytes
    (bytes : List AbstractByte)
    (_signed : Bool := false) :
    Option (ScalarVal × Option (Nat × Nat)) :=
  let sz := length bytes
  match Nat.beq sz 0 with
  | true => .none
  | false =>
    match decodeLittleEndianBytes bytes with
    | .some (bits, prov) => .some (⟨bits, sz⟩, prov)
    | .none => .none

/--
Construct a list of `n` `.uninit` bytes to initialize an aggregate byte buffer
prior to writing fields at their layout offsets.
-/
@[reducible]
def replicateUninitBytes : Nat → List AbstractByte
  | .zero => .nil
  | .succ k => .uninit :: replicateUninitBytes k

/--
Take the first `n` `AbstractByte`s from a byte list.
-/
@[reducible]
def takeAbstractBytes : Nat → List AbstractByte → List AbstractByte
  | .zero, _ => .nil
  | _, .nil => .nil
  | .succ k, b :: bs => b :: takeAbstractBytes k bs

/--
Drop the first `n` `AbstractByte`s from a byte list.
-/
@[reducible]
def dropAbstractBytes : Nat → List AbstractByte → List AbstractByte
  | .zero, bs => bs
  | _, .nil => .nil
  | .succ k, _ :: bs => dropAbstractBytes k bs

/--
Concatenate two `List AbstractByte` sequences.
-/
@[reducible]
def appendAbstractBytes :
    List AbstractByte → List AbstractByte → List AbstractByte
  | .nil, ys => ys
  | x :: xs, ys => x :: appendAbstractBytes xs ys

/--
Extract a contiguous slice of `len` `AbstractByte`s starting at byte offset
`offset` in `bytes`, returning `.none` if `offset + len > length bytes`.
-/
@[reducible]
def sliceAbstractBytes
    (bytes : List AbstractByte)
    (offset len : Nat) :
    Option (List AbstractByte) :=
  match Nat.ble (Nat.add offset len) (length bytes) with
  | false => .none
  | true => .some (takeAbstractBytes len (dropAbstractBytes offset bytes))

/--
Overwrite ` patch` into `buf` starting at byte offset `offset`.

Returns `.none` if `offset + length patch > length buf`.
-/
@[reducible]
def writeAbstractBytesAt :
    List AbstractByte → Nat → List AbstractByte → Option (List AbstractByte)
  | buf, _, .nil => .some buf
  | .nil, _, _ :: _ => .none
  | _ :: bufRest, .zero, w :: wRest =>
    match writeAbstractBytesAt bufRest .zero wRest with
    | .some tail' => .some (w :: tail')
    | .none => .none
  | b :: bufRest, .succ off, wList =>
    match writeAbstractBytesAt bufRest off wList with
    | .some tail' => .some (b :: tail')
    | .none => .none

/--
Look up whether byte offset `offset` falls within an 8-byte relocation entry
`(relocOffset, targetPtr)` in `relocs`.
-/
def lookupRelocAllocId :
    List (Nat × ProvenancePtr) → Nat → Option ProvenancePtr
  | .nil, _ => .none
  | (relocOff, targetPtr) :: rest, offset =>
    match
      Bool.and
        (Nat.ble relocOff offset)
        (Bool.not (Nat.ble (Nat.add relocOff 8) offset))
    with
    | true => .some targetPtr
    | false => lookupRelocAllocId rest offset

/--
Read `remLen` bytes starting at `offset` from a `CapturedAllocation`'s byte mask
and relocation table into a `List AbstractByte`.
-/
def globalAllocBytesAux
    (bytes : List (Option UInt8))
    (relocs : List (Nat × ProvenancePtr)) :
    Nat → Nat → Option (List AbstractByte)
  | _, .zero => .some .nil
  | offset, .succ rem =>
    match get? bytes offset with
    | .none => .none
    | .some optByte =>
      match globalAllocBytesAux bytes relocs (Nat.add offset 1) rem with
      | .none => .none
      | .some restBytes =>
        let absByte :=
          match optByte with
          | .none => AbstractByte.uninit
          | .some b =>
            let prov :=
              match lookupRelocAllocId relocs offset with
              | .some targetPtr => .some (targetPtr.allocId, targetPtr.tag)
              | .none => .none
            AbstractByte.init b prov
        .some (absByte :: restBytes)

/--
Extract `len` `AbstractByte`s starting at `offset` from a global
`CapturedAllocation`.

Reference (`compiler/rustc_middle/src/mir/interpret/allocation.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L53-L63>

> "pub struct Allocation<Prov = AllocId, Extra = (), Bytes = Box<[u8]>>"
-/
def globalAllocSliceToAbstractBytes
    (alloc : CapturedAllocation)
    (offset len : Nat) :
    Option (List AbstractByte) :=
  globalAllocBytesAux alloc.bytes alloc.relocations offset len

/--
Test whether `code` is a valid Unicode scalar value (`0x0000..=0xD7FF` or
`0xE000..=0x10FFFF`, i.e., `code < 55296 ∨ (57344 ≤ code ∧ code ≤ 1114111)`).

Reference (The Rust Reference, "Textual types"):
<https://doc.rust-lang.org/1.98.0/reference/types/textual.html>

> "A value of type `char` is a Unicode scalar value (i.e. a code point that is
> not a surrogate), represented as a 32-bit unsigned word in the 0x0000 to
> 0xD7FF or 0xE000 to 0x10FFFF range. It is immediate Undefined Behavior to
> create a `char` that falls outside this range."
-/
@[reducible]
def isValidCharCode (code : Nat) : Bool :=
  Bool.or
    (Bool.not (Nat.ble 55296 code))
    (Bool.and (Nat.ble 57344 code) (Nat.ble code 1114111))

/--
Test whether unsigned bit pattern `v` lies within `WrappingRange` `r`, modeling
`rustc_abi::WrappingRange::contains`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1439-L1448>

> "pub fn contains(&self, v: u128) -> bool {
>     if self.start <= self.end {
>         self.start <= v && v <= self.end
>     } else {
>         self.start <= v || v <= self.end
>     }
> }"
-/
@[reducible]
def wrappingRangeContains (r : WrappingRange) (v : Nat) : Bool :=
  match Nat.ble r.start r.end_ with
  | true => Bool.and (Nat.ble r.start v) (Nat.ble v r.end_)
  | false => Bool.or (Nat.ble r.start v) (Nat.ble v r.end_)

/--
Byte width of a `PrimitiveKind` on a 64-bit target.
-/
@[reducible]
def primitiveKindByteWidth : PrimitiveKind → Option Nat
  | .int bits _ =>
    match Nat.beq bits 0 with
    | true => .none
    | false => .some (Nat.div bits 8)
  | .float bits =>
    match Nat.beq bits 0 with
    | true => .none
    | false => .some (Nat.div bits 8)
  | .pointer _ => .some 8

/--
Byte width of a `ScalarLayout` on a 64-bit target.
-/
@[reducible]
def scalarLayoutByteWidth : ScalarLayout → Option Nat
  | .initialized pk _ => primitiveKindByteWidth pk
  | .union pk => primitiveKindByteWidth pk

/--
Decode `bytes` according to a compiler `ScalarLayout` descriptor `sl`, enforcing
`validRange` when `sl` is `.initialized pk validRange`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1539-L1559>

> "pub enum Scalar {
>     Initialized {
>         value: Primitive,
>         valid_range: WrappingRange,
>     },
>     Union {
>         value: Primitive,
>     },
> }"
-/
@[reducible]
def decodeScalarLayoutBytes
    (sl : ScalarLayout)
    (bytes : List AbstractByte) :
    Option Value :=
  match scalarLayoutByteWidth sl with
  | .none => .none
  | .some sz =>
    match Nat.beq (length bytes) sz with
    | false => .none
    | true =>
      match sl with
      | .initialized pk validRange =>
        match decodeScalarBytes bytes false with
        | .none => .none
        | .some (sv, prov) =>
          match wrappingRangeContains validRange sv.bits with
          | false => .none
          | true =>
            match pk with
            | .pointer _ =>
              match prov with
              | .some (allocId, _) =>
                .some (.ptr { allocId := allocId, offsetBytes := sv.bits } sz)
              | .none =>
                .some
                  (.ptr
                    { allocId := Nat.div sv.bits 65536
                      offsetBytes := Nat.mod sv.bits 65536 }
                    sz)
            | _ => .some (.scalar sv)
      | .union pk =>
        match decodeScalarBytes bytes false with
        | .some (sv, prov) =>
          match pk with
          | .pointer _ =>
            match prov with
            | .some (allocId, _) =>
              .some (.ptr { allocId := allocId, offsetBytes := sv.bits } sz)
            | .none =>
              .some
                (.ptr
                  { allocId := Nat.div sv.bits 65536
                    offsetBytes := Nat.mod sv.bits 65536 }
                  sz)
          | _ => .some (.scalar sv)
        | .none => .none

/--
Compute the target byte size of a `RigidTy` when determined directly by its
structural type constructor on a 64-bit target.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "The size of a value is the offset in bytes between successive elements in an
> array with that item type including alignment padding."
-/
@[reducible]
def rigidTyKindByteSize : RigidTy → Option Nat
  | .bool => .some 1
  | .char => .some 4
  | .uint w => intCastTargetBytes (.uint w)
  | .int w => intCastTargetBytes (.int w)
  | .tuple .nil => .some 0
  | .fnDef _ _ => .some 0
  | .fnPtr _ _ _ _ => .some 8
  | .ref _ pointee =>
    match pointee with
    | .slice _ => .some 16
    | .str => .some 16
    | .dynamic _ => .some 16
    | _ => .some 8
  | .rawPtr _ pointee =>
    match pointee with
    | .slice _ => .some 16
    | .str => .some 16
    | .dynamic _ => .some 16
    | _ => .some 8
  | .array elemKind n =>
    match rigidTyKindByteSize elemKind with
    | .some elemSz => .some (Nat.mul elemSz n)
    | .none => .none
  | _ => .none

/--
Sum the byte sizes of a list of `RigidTy` tuple elements when each element has a
known structural byte size.
-/
@[reducible]
def tupleFieldsByteSize : List RigidTy → Option Nat
  | .nil => .some 0
  | k :: rest =>
    match rigidTyKindByteSize k, tupleFieldsByteSize rest with
    | .some sz, .some restSz => .some (Nat.add sz restSz)
    | _, _ => .none

/--
Determine the byte size of `ty` using `rigidTyKindByteSize` for primitives,
pointers, and homogeneous primitive arrays, or `LayoutTable.lookup layouts
ty.layoutIdx` for ADTs and layout-indexed aggregates.
-/
@[reducible]
def rigidTyByteSize (layouts : LayoutTable) (ty : Ty) : Option Nat :=
  match rigidTyKindByteSize ty.kind with
  | .some sz => .some sz
  | .none =>
    match LayoutTable.lookup layouts ty.layoutIdx with
    | .some l => .some l.size.bytes
    | .none =>
      match ty.kind with
      | .tuple ks => tupleFieldsByteSize ks
      | _ => .none

/--
Encode a list of homogeneous element `Value`s using `encodeElem`, checking that
each encoded element has byte length `expectedElemSize` and concatenating the
resulting byte sequences.
-/
@[reducible]
def encodeListWith
    (encodeElem : Value → Option (List AbstractByte))
    (expectedElemSize : Nat) :
    List Value → Option (List AbstractByte)
  | .nil => .some .nil
  | v :: rest =>
    match encodeElem v with
    | .some bs =>
      match Nat.beq (length bs) expectedElemSize with
      | false => .none
      | true =>
        match encodeListWith encodeElem expectedElemSize rest with
        | .some restBs => .some (appendAbstractBytes bs restBs)
        | .none => .none
    | .none => .none

/--
Decode `count` homogeneous elements of byte size `elemSize` from `bytes` using
`decodeElem`.
-/
@[reducible]
def decodeArrayChunksWith
    (decodeElem : List AbstractByte → Option Value)
    (elemSize : Nat) :
    Nat → List AbstractByte → Option (List Value)
  | .zero, .nil => .some .nil
  | .zero, _ :: _ => .none
  | .succ k, bytes =>
    match Nat.ble elemSize (length bytes) with
    | false => .none
    | true =>
      let chunk := takeAbstractBytes elemSize bytes
      let rest := dropAbstractBytes elemSize bytes
      match decodeElem chunk with
      | .some v =>
        match decodeArrayChunksWith decodeElem elemSize k rest with
        | .some vs => .some (v :: vs)
        | .none => .none
      | .none => .none

/--
Encode a runtime `Value` without requiring a type descriptor by dispatching on
the value's runtime representation (`.unit`, `.scalar`, `.ptr`, or `.aggregate`).
-/
@[reducible]
def encodeUntypedValueToBytes :
    Nat → Value → Option (List AbstractByte)
  | .zero, _ => .none
  | .succ _, .unit => .some .nil
  | .succ _, .scalar sv => encodeScalarBytes sv .none
  | .succ _, .ptr p sz =>
    encodeScalarBytes ⟨p.offsetBytes, sz⟩ (.some (p.allocId, p.tag))
  | .succ fuel', .aggregate _ fields =>
    let rec encodeFields : List Value → Option (List AbstractByte)
      | .nil => .some .nil
      | f :: fs =>
        match encodeUntypedValueToBytes fuel' f, encodeFields fs with
        | .some b1, .some b2 => .some (appendAbstractBytes b1 b2)
        | _, _ => .none
    encodeFields fields

/--
Write a list of aggregate field `Value`s into `buf` at the byte offsets given by
`offsets : List Size`.

When `fieldKinds` provides a matching `RigidTy` for field `i`, `encodeTyped` is
tried first before falling back to `encodeFallback`. Any bytes in `buf` not
covered by a field remain `.uninit` (representing inter-field or trailing
padding).
-/
@[reducible]
def encodeFieldsAtOffsetsWith
    (encodeTyped : RigidTy → Value → Option (List AbstractByte))
    (encodeFallback : Value → Option (List AbstractByte)) :
    List Size → List RigidTy → List Value → List AbstractByte →
      Option (List AbstractByte)
  | .nil, _, .nil, buf => .some buf
  | .nil, _, _ :: _, _ => .none
  | _ :: _, _, .nil, _ => .none
  | off :: offRest, kinds, v :: vRest, buf =>
    let fBytesOpt : Option (List AbstractByte) :=
      match kinds with
      | k :: _ =>
        match encodeTyped k v with
        | .some bs => .some bs
        | .none =>
          match rigidTyKindByteSize k with
          | .some _ => .none
          | .none => encodeFallback v
      | .nil => encodeFallback v
    let nextKinds :=
      match kinds with
      | _ :: kRest => kRest
      | .nil => .nil
    match fBytesOpt with
    | .none => .none
    | .some fBytes =>
      match writeAbstractBytesAt buf off.bytes fBytes with
      | .none => .none
      | .some buf' =>
        encodeFieldsAtOffsetsWith encodeTyped encodeFallback offRest nextKinds
          vRest buf'

/--
Encode a list of tuple field `Value`s sequentially according to `fieldKinds`
when no explicit offset table is present.
-/
@[reducible]
def encodeSeqFieldsWith
    (encodeTyped : RigidTy → Value → Option (List AbstractByte)) :
    List RigidTy → List Value → Option (List AbstractByte)
  | .nil, .nil => .some .nil
  | .nil, _ :: _ => .none
  | _ :: _, .nil => .none
  | k :: kRest, v :: vRest =>
    match encodeTyped k v, encodeSeqFieldsWith encodeTyped kRest vRest with
    | .some b1, .some b2 => .some (appendAbstractBytes b1 b2)
    | _, _ => .none

/--
Decode a list of aggregate fields from `bytes` at the byte offsets given by
`offsets : List Size` using explicit field types `fieldKinds : List RigidTy`.

Bytes outside `[offsets[i].bytes .. offsets[i].bytes + sizeOfKind(fieldKinds[i]))`
are ignored during decoding, allowing structs with uninitialized padding bytes
between or after fields to decode when all field bytes are valid.
-/
@[reducible]
def decodeFieldsAtOffsetsWith
    (decodeTyped : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat)
    (bytes : List AbstractByte) :
    List Size → List RigidTy → Option (List Value)
  | .nil, .nil => .some .nil
  | .nil, _ :: _ => .none
  | _ :: _, .nil => .none
  | off :: offRest, k :: kRest =>
    match sizeOfKind k with
    | .none => .none
    | .some fSize =>
      match sliceAbstractBytes bytes off.bytes fSize with
      | .none => .none
      | .some fSlice =>
        match decodeTyped k fSlice with
        | .none => .none
        | .some v =>
          match
            decodeFieldsAtOffsetsWith decodeTyped sizeOfKind bytes offRest kRest
          with
          | .some vs => .some (v :: vs)
          | .none => .none

/--
Decode a list of aggregate fields from `bytes` at the byte offsets given by
`offsets : List Size` using compiler-computed per-field layout table indices
`fieldLayoutIdxs : List Nat` (`TypeLayout.fieldLayouts`).

For each field `(off, fIdx)`, looks up `fl` at `fIdx` in `layouts`, slices the
exact field byte span `[off.bytes .. off.bytes + fl.size.bytes)` (ignoring any
uninitialized inter-field or trailing padding bytes), and decodes the field at
layout `fIdx` (enforcing per-field `ScalarLayout` `validRange` niche, boolean,
and character bit-validity invariants).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The following is a non-exhaustive list of invalid values:
> - A `bool` that isn't 0 or 1.
> - A `char` that is a surrogate or above `char::MAX`.
> - A value of any type, other than a union or raw pointer, with uninitialized
>   bytes (except for padding bytes, which may be uninitialized)."
-/
@[reducible]
def decodeFieldsByLayoutIdxs
    (decodeByLayout : Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List Nat → Option (List Value)
  | .nil, .nil => .some .nil
  | .nil, _ :: _ => .none
  | _ :: _, .nil => .none
  | off :: offRest, fIdx :: fRest =>
    match LayoutTable.lookup layouts fIdx with
    | .none => .none
    | .some fl =>
      match sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | .none => .none
      | .some fSlice =>
        match decodeByLayout fIdx fSlice with
        | .none => .none
        | .some v =>
          match
            decodeFieldsByLayoutIdxs
              decodeByLayout
              layouts
              bytes
              offRest
              fRest
          with
          | .some vs => .some (v :: vs)
          | .none => .none

/--
Select and encode a union field from `fieldVals` into a buffer of `totalSize`
bytes at offset `0`, preferring the first field whose encoded byte length
matches `totalSize` (such as the initialized payload field `value:
ManuallyDrop<T>` in `MaybeUninit<T>`), and otherwise writing the first encodable
field at offset `0`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1649-L1650>

> "/// All fields start at no offset. The `usize` is the field count.
> Union(NonZeroUsize),"
-/
@[reducible]
def encodeUnionFieldsWith
    (encodeFallback : Value → Option (List AbstractByte))
    (totalSize : Nat)
    (fieldVals : List Value) :
    Option (List AbstractByte) :=
  let rec findFullSize : List Value → Option (List AbstractByte)
    | .nil => .none
    | fv :: rest =>
      match encodeFallback fv with
      | .some fBytes =>
        match Nat.beq (length fBytes) totalSize with
        | true =>
          writeAbstractBytesAt (replicateUninitBytes totalSize) 0 fBytes
        | false => findFullSize rest
      | .none => findFullSize rest
  match findFullSize fieldVals with
  | .some bs => .some bs
  | .none =>
    match fieldVals with
    | firstField :: _ =>
      match encodeFallback firstField with
      | .some fBytes =>
        writeAbstractBytesAt (replicateUninitBytes totalSize) 0 fBytes
      | .none => .none
    | .nil => .none

/--
Decode every union field in `fieldLayoutIdxs` (`TypeLayout.fieldLayouts`) from
byte offset `0` of `bytes`, where all union fields overlap
(`FieldsShape.union`).

Zero-sized union fields (such as `uninit: ()` at field `0` of `MaybeUninit<T>`)
decode to `Value.unit`, full-sized union fields (such as `value:
ManuallyDrop<T>` at field `1` of `MaybeUninit<T>`) decode via `payloadVal` or
`decodeByLayout`, and smaller non-zero union fields decode from the prefix slice
`[0 .. fl.size.bytes)`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1649-L1650>

> "/// All fields start at no offset. The `usize` is the field count.
> Union(NonZeroUsize),"
-/
@[reducible]
def decodeUnionFieldsByLayoutIdxs
    (decodeByLayout : Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (bytes : List AbstractByte)
    (totalSize : Nat)
    (payloadVal : Value) :
    List Nat → List Value
  | .nil => .nil
  | fIdx :: fRest =>
    let fieldVal : Value :=
      match LayoutTable.lookup layouts fIdx with
      | .none => payloadVal
      | .some fl =>
        match Nat.beq fl.size.bytes 0 with
        | true => .unit
        | false =>
          match Nat.beq fl.size.bytes totalSize with
          | true =>
            match payloadVal with
            | .unit =>
              match decodeByLayout fIdx bytes with
              | .some v => v
              | .none => .unit
            | v => v
          | false =>
            match sliceAbstractBytes bytes 0 fl.size.bytes with
            | .none => .unit
            | .some fSlice =>
              match decodeByLayout fIdx fSlice with
              | .some v => v
              | .none =>
                match decodeScalarBytes fSlice false with
                | .some (sv, _) => .scalar sv
                | .none => .unit
    fieldVal ::
      decodeUnionFieldsByLayoutIdxs
        decodeByLayout
        layouts
        bytes
        totalSize
        payloadVal
        fRest

/--
Decode a list of aggregate fields from `bytes` using the byte span between
consecutive offsets in `offsets` up to `totalSize`.
-/
@[reducible]
def decodeFieldsBySpan
    (bytes : List AbstractByte)
    (totalSize : Nat) :
    List Size → Option (List Value)
  | .nil => .some .nil
  | off :: offRest =>
    let nextOff :=
      match offRest with
      | next :: _ => next.bytes
      | .nil => totalSize
    match Nat.ble off.bytes nextOff with
    | false => .none
    | true =>
      let span := Nat.sub nextOff off.bytes
      match sliceAbstractBytes bytes off.bytes span with
      | .none => .none
      | .some fSlice =>
        let fieldValOpt : Option Value :=
          match Nat.beq span 0 with
          | true => .some Value.unit
          | false =>
            match decodeScalarBytes fSlice false with
            | .some (sv, _) => .some (.scalar sv)
            | .none => .none
        match fieldValOpt with
        | .none => .none
        | .some v =>
          match decodeFieldsBySpan bytes totalSize offRest with
          | .some vs => .some (v :: vs)
          | .none => .none

/--
Decode a list of tuple fields sequentially from `bytes` using `fieldKinds`.
-/
@[reducible]
def decodeSeqFieldsWith
    (decodeTyped : RigidTy → List AbstractByte → Option Value)
    (sizeOfKind : RigidTy → Option Nat) :
    List RigidTy → List AbstractByte → Option (List Value)
  | .nil, .nil => .some .nil
  | .nil, _ :: _ => .none
  | k :: kRest, bytes =>
    match sizeOfKind k with
    | .none => .none
    | .some fSize =>
      match Nat.ble fSize (length bytes) with
      | false => .none
      | true =>
        let chunk := takeAbstractBytes fSize bytes
        let rest := dropAbstractBytes fSize bytes
        match decodeTyped k chunk with
        | .none => .none
        | .some v =>
          match decodeSeqFieldsWith decodeTyped sizeOfKind kRest rest with
          | .some vs => .some (v :: vs)
          | .none => .none

/--
Default structural recursion budget for `encodeValueToBytes` and
`decodeValueFromBytes`.
-/
@[reducible]
def defaultCodecFuel : Nat := 16

/--
Fuel-bounded byte-level encoder converting a runtime `Value` of type `ty` under
`layouts` into its little-endian `List AbstractByte` representation.

- `.bool`: `0` encodes to `[.init 0x00 none]` and `1` encodes to
  `[.init 0x01 none]`; any other bit pattern fails with `.none`.
- `.char`: 4-byte Unicode scalar value (`isValidCharCode`) encodes to 4
  little-endian initialized bytes.
- `.uint _` and `.int _`: fixed-width (`1, 2, 4, 8, 16` byte) scalar encodes in
  little-endian order via `encodeScalarBytes`.
- `.tuple .nil` and `.fnDef _ _`: zero-sized value encodes to `[]`.
- `.rawPtr _ _` and `.ref _ _`: 8-byte thin pointer encodes its offset in
  little-endian order while attaching `.some (p.allocId, p.tag)` provenance to
  all 8 bytes; 16-byte wide pointer encodes its 8-byte data pointer followed by
  its 8-byte metadata scalar.
- `.array elemKind n`: encodes all `n` elements sequentially.
- `.tuple fieldKinds` and `.adt defPath args`: initializes a buffer of
  `layout.size.bytes` `.uninit` bytes and writes each field at its exact byte
  offset from `FieldsShape.arbitrary`, leaving any inter-field or trailing
  padding bytes as `.uninit`.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html>

> "The layout of a type is its size, alignment, and the relative offsets of its
> fields."

Reference (The Rust Reference, "Boolean type"):
<https://doc.rust-lang.org/1.98.0/reference/types/boolean.html>

> "The value false has the bit pattern 0x00 and the value true has the bit
> pattern 0x01. It is undefined behavior for an object with the boolean type to
> have any other bit pattern."
-/
@[reducible]
def encodeValueToBytes :
    Nat → LayoutTable → Ty → Value → Option (List AbstractByte)
  | .zero, _, _, _ => .none
  | .succ fuel', layouts, ty, v =>
    match ty.kind with
    | .bool =>
      match v with
      | .scalar sv =>
        match Nat.beq sv.sizeBytes 1 with
        | false => .none
        | true =>
          match Nat.beq sv.bits 0 with
          | true => .some (.init (UInt8.ofNat 0) .none :: .nil)
          | false =>
            match Nat.beq sv.bits 1 with
            | true => .some (.init (UInt8.ofNat 1) .none :: .nil)
            | false => .none
      | _ => .none
    | .char =>
      match v with
      | .scalar sv =>
        match Bool.and (Nat.beq sv.sizeBytes 4) (isValidCharCode sv.bits) with
        | true => encodeScalarBytes sv .none
        | false => .none
      | _ => .none
    | .uint w =>
      match intCastTargetBytes (.uint w), v with
      | .some expectedBytes, .scalar sv =>
        match Nat.beq sv.sizeBytes expectedBytes with
        | true => encodeScalarBytes sv .none
        | false => .none
      | _, _ => .none
    | .int w =>
      match intCastTargetBytes (.int w), v with
      | .some expectedBytes, .scalar sv =>
        match Nat.beq sv.sizeBytes expectedBytes with
        | true => encodeScalarBytes sv .none
        | false => .none
      | _, _ => .none
    | .tuple .nil =>
      match v with
      | .unit => .some .nil
      | .aggregate 0 .nil => .some .nil
      | _ => .none
    | .fnDef _ _ =>
      match v with
      | .unit => .some .nil
      | .aggregate 0 .nil => .some .nil
      | _ => .none
    | .fnPtr _ _ _ _ =>
      match v with
      | .ptr p 8 =>
        encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag))
      | .scalar sv =>
        match Nat.beq sv.sizeBytes 8 with
        | true => encodeScalarBytes sv .none
        | false => .none
      | _ => .none
    | .rawPtr _ pointee =>
      let isWide :=
        match pointee with
        | .slice _ => true
        | .str => true
        | .dynamic _ => true
        | _ => false
      match isWide, v with
      | false, .ptr p 8 =>
        encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag))
      | false, .scalar sv =>
        match Nat.beq sv.sizeBytes 8 with
        | true => encodeScalarBytes sv .none
        | false => .none
      | true, .aggregate 0 (.ptr p 8 :: .scalar metaSc :: .nil) =>
        match
          encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag)),
          encodeScalarBytes ⟨metaSc.bits, 8⟩ .none
        with
        | .some b1, .some b2 => .some (appendAbstractBytes b1 b2)
        | _, _ => .none
      | _, _ => .none
    | .ref _ pointee =>
      let isWide :=
        match pointee with
        | .slice _ => true
        | .str => true
        | .dynamic _ => true
        | _ => false
      match isWide, v with
      | false, .ptr p 8 =>
        encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag))
      | false, .scalar sv =>
        match Nat.beq sv.sizeBytes 8 with
        | true => encodeScalarBytes sv .none
        | false => .none
      | true, .aggregate 0 (.ptr p 8 :: .scalar metaSc :: .nil) =>
        match
          encodeScalarBytes ⟨p.offsetBytes, 8⟩ (.some (p.allocId, p.tag)),
          encodeScalarBytes ⟨metaSc.bits, 8⟩ .none
        with
        | .some b1, .some b2 => .some (appendAbstractBytes b1 b2)
        | _, _ => .none
      | _, _ => .none
    | .array elemKind n =>
      match Nat.beq n 0 with
      | true =>
        match v with
        | .unit => .some .nil
        | .aggregate 0 .nil => .some .nil
        | _ => .none
      | false =>
        match v with
        | .aggregate 0 elems =>
          match Nat.beq (length elems) n with
          | false => .none
          | true =>
            let elemSzOpt : Option Nat :=
              match rigidTyKindByteSize elemKind with
              | .some sz => .some sz
              | .none =>
                match LayoutTable.lookup layouts ty.layoutIdx with
                | .some l =>
                  match l.fields with
                  | .array stride _ => .some stride.bytes
                  | _ => .none
                | .none => .none
            match elemSzOpt with
            | .none => .none
            | .some elemSz =>
              encodeListWith
                (fun e =>
                  encodeValueToBytes fuel' layouts
                    { kind := elemKind, layoutIdx := 0 } e)
                elemSz
                elems
        | _ => .none
    | .tuple (kHead :: kTail) =>
      let fieldKinds := kHead :: kTail
      match v with
      | .aggregate 0 fieldVals =>
        match Nat.beq (length fieldVals) (length fieldKinds) with
        | false => .none
        | true =>
          let encodeTyped := fun (k : RigidTy) (fv : Value) =>
            encodeValueToBytes fuel' layouts { kind := k, layoutIdx := 0 } fv
          let encodeFallback := fun (fv : Value) =>
            encodeUntypedValueToBytes fuel' fv
          match LayoutTable.lookup layouts ty.layoutIdx with
          | .some l =>
            match l.fields with
            | .arbitrary offsets _ =>
              match Nat.beq (length offsets) (length fieldVals) with
              | true =>
                encodeFieldsAtOffsetsWith
                  encodeTyped
                  encodeFallback
                  offsets
                  fieldKinds
                  fieldVals
                  (replicateUninitBytes l.size.bytes)
              | false =>
                encodeSeqFieldsWith encodeTyped fieldKinds fieldVals
            | _ => encodeSeqFieldsWith encodeTyped fieldKinds fieldVals
          | .none => encodeSeqFieldsWith encodeTyped fieldKinds fieldVals
      | _ => .none
    | .adt _ args =>
      match LayoutTable.lookup layouts ty.layoutIdx with
      | .none =>
        match v with
        | .unit => .some .nil
        | .aggregate 0 .nil => .some .nil
        | _ => encodeUntypedValueToBytes fuel' v
      | .some l =>
        match l.isUninhabited with
        | true => .none
        | false =>
          let encodeTyped := fun (k : RigidTy) (fv : Value) =>
            encodeValueToBytes fuel' layouts { kind := k, layoutIdx := 0 } fv
          let encodeFallback := fun (fv : Value) =>
            encodeUntypedValueToBytes fuel' fv
          match l.variants with
          | .empty => .none
          | .single expectedVar =>
            match l.fields, v with
            | .arbitrary offsets _, .aggregate varIdx fieldVals =>
              match
                Bool.and
                  (Nat.beq varIdx expectedVar)
                  (Nat.beq (length offsets) (length fieldVals))
              with
              | false => .none
              | true =>
                let fieldKinds :=
                  match Nat.beq (length args) (length offsets) with
                  | true => args
                  | false => .nil
                encodeFieldsAtOffsetsWith
                  encodeTyped
                  encodeFallback
                  offsets
                  fieldKinds
                  fieldVals
                  (replicateUninitBytes l.size.bytes)
            | .arbitrary .nil _, .unit =>
              .some (replicateUninitBytes l.size.bytes)
            | .primitive, .scalar sv =>
              match Nat.beq sv.sizeBytes l.size.bytes with
              | true => encodeScalarBytes sv .none
              | false => .none
            | .union _, .aggregate _ fieldVals =>
              encodeUnionFieldsWith encodeFallback l.size.bytes fieldVals
            | _, _ => .none
          | .multiple tagLayout tagField variantShapes =>
            match v with
            | .aggregate varIdx fieldVals =>
              match
                l.fields,
                scalarLayoutByteWidth tagLayout,
                get? variantShapes varIdx
              with
              | .arbitrary outerOffsets _,
                .some tagSz,
                .some (.arbitrary varOffsets _) =>
                match get? outerOffsets tagField with
                | .none => .none
                | .some tagOff =>
                  match encodeScalarBytes ⟨varIdx, tagSz⟩ .none with
                  | .none => .none
                  | .some tagBytes =>
                    match
                      writeAbstractBytesAt
                        (replicateUninitBytes l.size.bytes)
                        tagOff.bytes
                        tagBytes
                    with
                    | .none => .none
                    | .some bufWithTag =>
                      encodeFieldsAtOffsetsWith
                        encodeTyped
                        encodeFallback
                        varOffsets
                        .nil
                        fieldVals
                        bufWithTag
              | _, _, _ => .none
            | _ => .none
    | _ => .none

/--
Fuel-bounded byte-level decoder converting a little-endian `List AbstractByte`
into a runtime `Value` of type `ty` under `layouts`.

Returns `.none` whenever the byte sequence has the wrong byte length or violates
the bit-validity invariant of `ty` (such as reading `.uninit` into a scalar,
boolean, character, or pointer, or reading a non-`0`/`1` byte into `.bool`, a
surrogate or out-of-range scalar into `.char`, a null address without provenance
into `.ref`, or an out-of-range niche value into `.initialized` `ScalarLayout`).
For `.adt` structs and tuples with `FieldsShape.arbitrary`, bytes at padding
offsets outside field spans are not read and may be `.uninit`.

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "The following is a non-exhaustive list of invalid values:
> - A `bool` that isn't 0 or 1.
> - A `char` that is a surrogate or above `char::MAX`.
> - A value of any type, other than a union or raw pointer, with uninitialized
>   bytes (except for padding bytes, which may be uninitialized)."
-/
@[reducible]
def decodeValueFromBytes :
    Nat → LayoutTable → Ty → List AbstractByte → Option Value
  | .zero, _, _, _ => .none
  | .succ fuel', layouts, ty, bytes =>
    match ty.kind with
    | .bool =>
      match bytes with
      | .init b _ :: .nil =>
        let n := b.toBitVec.toNat
        match Nat.beq n 0 with
        | true => .some (.scalar ⟨0, 1⟩)
        | false =>
          match Nat.beq n 1 with
          | true => .some (.scalar ⟨1, 1⟩)
          | false => .none
      | _ => .none
    | .char =>
      match Nat.beq (length bytes) 4 with
      | false => .none
      | true =>
        match decodeScalarBytes bytes false with
        | .some (sv, _) =>
          match isValidCharCode sv.bits with
          | true => .some (.scalar sv)
          | false => .none
        | .none => .none
    | .uint w =>
      match intCastTargetBytes (.uint w) with
      | .some expectedBytes =>
        match Nat.beq (length bytes) expectedBytes with
        | false => .none
        | true =>
          match decodeScalarBytes bytes false with
          | .some (sv, _) => .some (.scalar sv)
          | .none => .none
      | .none => .none
    | .int w =>
      match intCastTargetBytes (.int w) with
      | .some expectedBytes =>
        match Nat.beq (length bytes) expectedBytes with
        | false => .none
        | true =>
          match decodeScalarBytes bytes true with
          | .some (sv, _) => .some (.scalar sv)
          | .none => .none
      | .none => .none
    | .tuple .nil =>
      match bytes with
      | .nil => .some .unit
      | _ :: _ => .none
    | .fnDef _ _ =>
      match bytes with
      | .nil => .some .unit
      | _ :: _ => .none
    | .never => .none
    | .fnPtr _ _ _ _ =>
      match Nat.beq (length bytes) 8 with
      | false => .none
      | true =>
        match decodeScalarBytes bytes false with
        | .some (sv, prov) =>
          match prov with
          | .some (allocId, _) =>
            .some (.ptr { allocId := allocId, offsetBytes := sv.bits } 8)
          | .none =>
            match Nat.beq sv.bits 0 with
            | true => .none
            | false =>
              .some
                (.ptr
                  { allocId := Nat.div sv.bits 65536
                    offsetBytes := Nat.mod sv.bits 65536 }
                  8)
        | .none => .none
    | .rawPtr _ pointee =>
      let isWide :=
        match pointee with
        | .slice _ => true
        | .str => true
        | .dynamic _ => true
        | _ => false
      match isWide with
      | false =>
        match Nat.beq (length bytes) 8 with
        | false => .none
        | true =>
          match decodeScalarBytes bytes false with
          | .some (sv, prov) =>
            match prov with
            | .some (allocId, _) =>
              .some (.ptr { allocId := allocId, offsetBytes := sv.bits } 8)
            | .none =>
              .some
                (.ptr
                  { allocId := Nat.div sv.bits 65536
                    offsetBytes := Nat.mod sv.bits 65536 }
                  8)
          | .none => .none
      | true =>
        match Nat.beq (length bytes) 16 with
        | false => .none
        | true =>
          let dataBytes := takeAbstractBytes 8 bytes
          let metaBytes := dropAbstractBytes 8 bytes
          match
            decodeScalarBytes dataBytes false,
            decodeScalarBytes metaBytes false
          with
          | .some (dataSv, prov), .some (metaSv, _) =>
            let ptrVal : ProvenancePtr :=
              match prov with
              | .some (allocId, _) =>
                { allocId := allocId, offsetBytes := dataSv.bits }
              | .none =>
                { allocId := Nat.div dataSv.bits 65536
                  offsetBytes := Nat.mod dataSv.bits 65536 }
            .some (.aggregate 0 (.ptr ptrVal 8 :: .scalar metaSv :: .nil))
          | _, _ => .none
    | .ref _ pointee =>
      let isWide :=
        match pointee with
        | .slice _ => true
        | .str => true
        | .dynamic _ => true
        | _ => false
      match isWide with
      | false =>
        match Nat.beq (length bytes) 8 with
        | false => .none
        | true =>
          match decodeScalarBytes bytes false with
          | .some (sv, prov) =>
            match prov with
            | .some (allocId, _) =>
              .some (.ptr { allocId := allocId, offsetBytes := sv.bits } 8)
            | .none =>
              match Nat.beq sv.bits 0 with
              | true => .none
              | false =>
                .some
                  (.ptr
                    { allocId := Nat.div sv.bits 65536
                      offsetBytes := Nat.mod sv.bits 65536 }
                    8)
          | .none => .none
      | true =>
        match Nat.beq (length bytes) 16 with
        | false => .none
        | true =>
          let dataBytes := takeAbstractBytes 8 bytes
          let metaBytes := dropAbstractBytes 8 bytes
          match
            decodeScalarBytes dataBytes false,
            decodeScalarBytes metaBytes false
          with
          | .some (dataSv, prov), .some (metaSv, _) =>
            match prov with
            | .some (allocId, _) =>
              let ptrVal : ProvenancePtr :=
                { allocId := allocId, offsetBytes := dataSv.bits }
              .some (.aggregate 0 (.ptr ptrVal 8 :: .scalar metaSv :: .nil))
            | .none =>
              match Nat.beq dataSv.bits 0 with
              | true => .none
              | false =>
                let ptrVal : ProvenancePtr :=
                  { allocId := Nat.div dataSv.bits 65536
                    offsetBytes := Nat.mod dataSv.bits 65536 }
                .some (.aggregate 0 (.ptr ptrVal 8 :: .scalar metaSv :: .nil))
          | _, _ => .none
    | .array elemKind n =>
      match Nat.beq n 0 with
      | true =>
        match bytes with
        | .nil => .some (.aggregate 0 .nil)
        | _ :: _ => .none
      | false =>
        let elemSzOpt : Option Nat :=
          match rigidTyKindByteSize elemKind with
          | .some sz => .some sz
          | .none =>
            match LayoutTable.lookup layouts ty.layoutIdx with
            | .some l =>
              match l.fields with
              | .array stride _ => .some stride.bytes
              | _ => .none
            | .none => .none
        match elemSzOpt with
        | .none => .none
        | .some elemSz =>
          match Nat.beq (length bytes) (Nat.mul elemSz n) with
          | false => .none
          | true =>
            match
              decodeArrayChunksWith
                (fun chunk =>
                  decodeValueFromBytes fuel' layouts
                    { kind := elemKind, layoutIdx := 0 } chunk)
                elemSz
                n
                bytes
            with
            | .some elems => .some (.aggregate 0 elems)
            | .none => .none
    | .tuple (kHead :: kTail) =>
      let fieldKinds := kHead :: kTail
      let decodeTyped := fun (k : RigidTy) (bs : List AbstractByte) =>
        decodeValueFromBytes fuel' layouts { kind := k, layoutIdx := 0 } bs
      let sizeOfKind := fun (k : RigidTy) =>
        rigidTyByteSize layouts { kind := k, layoutIdx := 0 }
      match LayoutTable.lookup layouts ty.layoutIdx with
      | .some l =>
        match Nat.beq (length bytes) l.size.bytes with
        | false => .none
        | true =>
          match l.fields with
          | .arbitrary offsets _ =>
            match
              decodeFieldsAtOffsetsWith
                decodeTyped
                sizeOfKind
                bytes
                offsets
                fieldKinds
            with
            | .some vals => .some (.aggregate 0 vals)
            | .none => .none
          | _ =>
            match decodeSeqFieldsWith decodeTyped sizeOfKind fieldKinds bytes with
            | .some vals => .some (.aggregate 0 vals)
            | .none => .none
      | .none =>
        match decodeSeqFieldsWith decodeTyped sizeOfKind fieldKinds bytes with
        | .some vals => .some (.aggregate 0 vals)
        | .none => .none
    | .adt _ args =>
      match LayoutTable.lookup layouts ty.layoutIdx with
      | .none => .none
      | .some l =>
        match
          Bool.or
            l.isUninhabited
            (Bool.not (Nat.beq (length bytes) l.size.bytes))
        with
        | true => .none
        | false =>
          let decodeTyped := fun (k : RigidTy) (bs : List AbstractByte) =>
            decodeValueFromBytes fuel' layouts { kind := k, layoutIdx := 0 } bs
          let sizeOfKind := fun (k : RigidTy) =>
            rigidTyByteSize layouts { kind := k, layoutIdx := 0 }
          match l.variants with
          | .empty => .none
          | .single variantIdx =>
            match l.fields with
            | .arbitrary .nil _ => .some (.aggregate variantIdx .nil)
            | .arbitrary offsets _ =>
              let byArgs :=
                match Nat.beq (length args) (length offsets) with
                | true =>
                  decodeFieldsAtOffsetsWith
                    decodeTyped
                    sizeOfKind
                    bytes
                    offsets
                    args
                | false => .none
              match byArgs with
              | .some vals => .some (.aggregate variantIdx vals)
              | .none =>
                let hasFieldLayouts :=
                  Nat.beq (length l.fieldLayouts) (length offsets)
                match hasFieldLayouts with
                | true =>
                  let decodeByLayout := fun (fIdx : Nat) (bs : List AbstractByte) =>
                    decodeValueFromBytes
                      fuel'
                      layouts
                      { kind := .adt "" .nil, layoutIdx := fIdx }
                      bs
                  match
                    decodeFieldsByLayoutIdxs
                      decodeByLayout
                      layouts
                      bytes
                      offsets
                      l.fieldLayouts
                  with
                  | .some vals => .some (.aggregate variantIdx vals)
                  | .none => .none
                | false =>
                  match offsets, l.backendRepr with
                  | off0 :: .nil, .scalar s0 =>
                    match scalarLayoutByteWidth s0 with
                    | .none => .none
                    | .some sz0 =>
                      match sliceAbstractBytes bytes off0.bytes sz0 with
                      | .none => .none
                      | .some slice0 =>
                        match decodeScalarLayoutBytes s0 slice0 with
                        | .some v0 => .some (.aggregate variantIdx (v0 :: .nil))
                        | .none => .none
                  | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
                    match scalarLayoutByteWidth s0, scalarLayoutByteWidth s1 with
                    | .some sz0, .some sz1 =>
                      match
                        sliceAbstractBytes bytes off0.bytes sz0,
                        sliceAbstractBytes bytes off1.bytes sz1
                      with
                      | .some slice0, .some slice1 =>
                        match
                          decodeScalarLayoutBytes s0 slice0,
                          decodeScalarLayoutBytes s1 slice1
                        with
                        | .some v0, .some v1 =>
                          .some (.aggregate variantIdx (v0 :: v1 :: .nil))
                        | _, _ => .none
                      | _, _ => .none
                    | _, _ => .none
                  | _, _ =>
                    match decodeFieldsBySpan bytes l.size.bytes offsets with
                    | .some vals => .some (.aggregate variantIdx vals)
                    | .none => .none
            | .primitive =>
              match Nat.beq l.size.bytes 0 with
              | true => .some .unit
              | false =>
                match l.backendRepr with
                | .scalar s0 => decodeScalarLayoutBytes s0 bytes
                | _ =>
                  match decodeScalarBytes bytes false with
                  | .some (sv, _) => .some (.scalar sv)
                  | .none => .none
            | .union fieldCount =>
              let byArg : Option Value :=
                match args with
                | argKind :: .nil =>
                  decodeValueFromBytes
                    fuel'
                    layouts
                    { kind := argKind, layoutIdx := 0 }
                    bytes
                | _ => .none
              let payloadVal : Value :=
                match byArg with
                | .some v0 => v0
                | .none =>
                  match l.backendRepr with
                  | .scalar (.union pk) =>
                    match decodeScalarLayoutBytes (.union pk) bytes with
                    | .some v0 => v0
                    | .none => .unit
                  | .scalar s0 =>
                    match decodeScalarLayoutBytes s0 bytes with
                    | .some v0 => v0
                    | .none => .unit
                  | _ =>
                    match decodeScalarBytes bytes false with
                    | .some (sv, _) => .scalar sv
                    | .none => .unit
              match l.fieldLayouts with
              | fHead :: fTail =>
                let decodeByLayout :=
                  fun (fIdx : Nat) (bs : List AbstractByte) =>
                    decodeValueFromBytes
                      fuel'
                      layouts
                      { kind := .adt "" .nil, layoutIdx := fIdx }
                      bs
                let vals :=
                  decodeUnionFieldsByLayoutIdxs
                    decodeByLayout
                    layouts
                    bytes
                    l.size.bytes
                    payloadVal
                    (fHead :: fTail)
                .some (.aggregate variantIdx vals)
              | .nil =>
                let numFields :=
                  match Nat.beq fieldCount 0 with
                  | true => 1
                  | false => fieldCount
                .some
                  (.aggregate
                    variantIdx
                    (replicateValue numFields payloadVal))
            | .array stride count =>
              match
                decodeArrayChunksWith
                  (fun chunk =>
                    match decodeScalarBytes chunk false with
                    | .some (sv, _) => .some (.scalar sv)
                    | .none => .none)
                  stride.bytes
                  count
                  bytes
              with
              | .some vals => .some (.aggregate variantIdx vals)
              | .none => .none
          | .multiple tagLayout tagField variantShapes =>
            match l.fields, scalarLayoutByteWidth tagLayout with
            | .arbitrary outerOffsets _, .some tagSz =>
              match get? outerOffsets tagField with
              | .none => .none
              | .some tagOff =>
                match sliceAbstractBytes bytes tagOff.bytes tagSz with
                | .none => .none
                | .some tagSlice =>
                  match decodeScalarLayoutBytes tagLayout tagSlice with
                  | .some (.scalar tagSc) =>
                    let varIdx := tagSc.bits
                    match get? variantShapes varIdx with
                    | .some (.arbitrary varOffsets _) =>
                      match decodeFieldsBySpan bytes l.size.bytes varOffsets with
                      | .some vals => .some (.aggregate varIdx vals)
                      | .none => .none
                    | _ => .none
                  | _ => .none
            | _, _ => .none
    | _ => .none

end Trusted.Rustc.V2026_06_01.MirSemantics
