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
Target pointer width in bytes derived from `layouts.pointerBits`,
defaulting to `8` bytes (64-bit target) when `layouts.pointerBits == 0`.

Reference (The Rust Reference 1.98.0, "Type Layout — Pointers and references layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#pointers-and-references-layout>

> "Pointers to sized types have the same size and alignment as usize."

Modeling note (`agent_docs/trusted-rust.md`): `layouts.pointerBits = 0` denotes
an unspecified default 64-bit target (`8` bytes); non-zero `pointerBits` yields
`pointerBits / 8` (e.g., `32 -> 4`, `64 -> 8`).
-/
@[reducible]
def layoutPointerBytes (layouts : LayoutTable) : Nat :=
  match layouts.pointerBits with
  | 0 => 8
  | n + 1 => Nat.div (n + 1) 8

/--
Normalize a pointer byte offset modulo `256 ^ ptrBytes` (`scalarModulus ptrBytes`)
so `PtrByteFrag.origOffset` matches the fixed-width little-endian byte image of
the originating pointer for `0 < ptrBytes ≤ 8`.

Reference (The Rust Reference 1.98.0, "Type Layout — Primitive data layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#primitive-data-layout>

> "usize and isize have a size big enough to contain every address on the
> target platform. For example, on a 32 bit target, this is 4 bytes, and on a
> 64 bit target, this is 8 bytes."

Modeling choice (`agent_docs/trusted-rust.md`): Aligns `PtrByteFrag.origOffset`
with Miri's 8-byte zero-padded `PointerFrag.bytes` image (`UCG#558` /
`rust#148259`), ensuring offset splices between distinct offsets with matching
`(allocId, tag)` (such as `p` and `p + 256`) are rejected.
-/
@[reducible]
def normPtrByteOffset (ptrBytes offset : Nat) : Nat :=
  Nat.mod offset (scalarModulus ptrBytes)

/--
Per-byte pointer provenance fragment carried by an initialized `AbstractByte`,
recording the originating pointer's allocation ID, Tree Borrows tag, 0-based
little-endian byte index `0 .. ptrBytes - 1`, normalized originating offset
`origOffset` (`offset mod 256^ptrBytes`), and pointer width `ptrBytes > 0`.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Accessing (loading from or storing to) a place that is dangling or based on
> a misaligned pointer."

Reference (`compiler/rustc_middle/src/mir/interpret/allocation.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L53-L63>

> "pub struct Allocation<Prov = AllocId, Extra = (), Bytes = Box<[u8]>>"

Modeling choice (`agent_docs/trusted-rust.md`): The stable Rust Reference does
not prescribe an operational fragment format for sub-pointer byte copies;
`PtrByteFrag` follows `UCG#558`, `rust#148259`, and Miri's `PointerFrag`
fragment coherence rule so only intact, in-order byte copies of a single pointer
image retain provenance, while reversals, swaps, duplicates, cross-width splices,
and same-`(allocId, tag)` offset splices strip provenance.
-/
structure PtrByteFrag : Type where
  /-- Target global or stack allocation identifier. -/
  allocId : Nat
  /-- Borrow-table provenance tag carried by the originating pointer. -/
  tag : Nat
  /-- 0-based little-endian byte index (`0 .. ptrBytes - 1`) within the pointer image. -/
  byteIdx : Nat
  /-- Originating pointer byte offset normalized modulo `256 ^ ptrBytes` at encode time. -/
  origOffset : Nat
  /-- Originating pointer width in bytes (`4` or `8`; guarded `> 0` on decode). -/
  ptrBytes : Nat

/--
Structural equality on `PtrByteFrag`.
-/
@[reducible]
def PtrByteFrag.beq (f₁ f₂ : PtrByteFrag) : Bool :=
  Bool.and (Nat.beq f₁.allocId f₂.allocId)
    (Bool.and (Nat.beq f₁.tag f₂.tag)
      (Bool.and (Nat.beq f₁.byteIdx f₂.byteIdx)
        (Bool.and (Nat.beq f₁.origOffset f₂.origOffset)
          (Nat.beq f₁.ptrBytes f₂.ptrBytes))))

/--
Extract the legacy `(allocId, tag)` pair from a `PtrByteFrag`.
-/
@[reducible]
def PtrByteFrag.provPair (f : PtrByteFrag) : Nat × Nat :=
  (f.allocId, f.tag)

/--
Single byte in the abstract machine memory representation of a Rust value,
modeling initialized bytes (with optional pointer-byte provenance fragment
`PtrByteFrag`) and uninitialized or padding bytes (`.uninit`).

Constructor `.uninit` represents an uninitialized or padding byte; reading an
`.uninit` byte at a scalar, boolean, character, or pointer type produces
undefined behavior (`.none` during decoding). Constructor `.init` carries the
8-bit value `byte : UInt8` together with optional `PtrByteFrag` provenance
for coherent pointer round-tripping (`UCG#558` / `rust#148259`).

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
  /-- Initialized byte `byte` with optional `PtrByteFrag` provenance fragment. -/
  | init (byte : UInt8) (prov : Option PtrByteFrag) : AbstractByte

/--
Test whether an `AbstractByte` is initialized (`.init _ _`).
-/
@[reducible]
def AbstractByte.isInit : AbstractByte → Bool
  | .uninit => false
  | .init _ _ => true

/--
Extract the optional `(allocId, tag)` provenance pair carried by an
`AbstractByte`, returning `.none` for `.uninit` and provenance-free `.init` bytes.
-/
@[reducible]
def AbstractByte.provPair? : AbstractByte → Option (Nat × Nat)
  | .uninit => .none
  | .init _ .none => .none
  | .init _ (.some frag) => .some (frag.allocId, frag.tag)

/--
Construct a provenance-free initialized `AbstractByte`.
-/
@[reducible]
def mkInitByte (byte : UInt8) : AbstractByte :=
  .init byte .none

/--
Construct an initialized `AbstractByte` carrying a normalized `PtrByteFrag`.
-/
@[reducible]
def mkPtrFragByte
    (byte : UInt8)
    (allocId tag byteIdx origOffset ptrBytes : Nat) :
    AbstractByte :=
  .init byte
    (.some {
      allocId := allocId
      tag := tag
      byteIdx := byteIdx
      origOffset := normPtrByteOffset ptrBytes origOffset
      ptrBytes := ptrBytes
    })

/--
`true` when some byte of `bytes` is initialized with pointer provenance
(`AbstractByte.init _ (.some _)`).
-/
@[reducible]
def abstractBytesHaveProv : List AbstractByte → Bool
  | .nil => false
  | .init _ (.some _) :: _ => true
  | _ :: rest => abstractBytesHaveProv rest

/--
Recursive helper for `abstractBytesCoherentPtrProv?`: verifies that every
remaining byte at position `expectedIdx .. ptrBytes - 1` is `.init _ (.some frag)`
with matching `(allocId, tag, origOffset, ptrBytes)` and `frag.byteIdx == expectedIdx`,
terminating cleanly only when `expectedIdx == ptrBytes`.

Modeling choice (`agent_docs/trusted-rust.md`): Enforces `UCG#558` / `rust#148259`
/ Miri `PointerFrag` fragment coherence so any partial, reversed, swapped,
duplicated, cross-width, or offset-spliced byte sequence strips provenance.
-/
@[reducible]
def abstractBytesCoherentPtrProvAux
    (allocId tag origOffset ptrBytes : Nat) :
    Nat → List AbstractByte → Bool
  | expectedIdx, .nil => Nat.beq expectedIdx ptrBytes
  | expectedIdx, .init _ (.some frag) :: rest =>
    Bool.and
      (Bool.and (Nat.beq frag.allocId allocId)
        (Bool.and (Nat.beq frag.tag tag)
          (Bool.and (Nat.beq frag.byteIdx expectedIdx)
            (Bool.and (Nat.beq frag.origOffset origOffset)
              (Nat.beq frag.ptrBytes ptrBytes)))))
      (abstractBytesCoherentPtrProvAux allocId tag origOffset ptrBytes (Nat.add expectedIdx 1) rest)
  | _, _ :: _ => false

/--
Check strict `UCG#558` pointer-byte fragment coherence on `bytes`, returning
`.some headFrag` iff:
- `bytes` has exact non-zero length `ptrBytes = headFrag.ptrBytes > 0`, AND
- every byte `i ∈ [0, ptrBytes)` is `.init _ (.some frag)` with identical
  `(allocId, tag, origOffset, ptrBytes)` AND `frag.byteIdx == i`.

Returns `.none` for empty lists, `.uninit`, plain bytes, reversals, swaps,
duplicates, cross-width splices, and same-`(allocId, tag)` offset splices.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Accessing (loading from or storing to) a place that is dangling or based on
> a misaligned pointer."

Modeling choice (`agent_docs/trusted-rust.md`): Operational alignment with
`UCG#558`, `rust#148259`, and Miri's `ProvenanceMap::inspect_fragments`.
-/
@[reducible]
def abstractBytesCoherentPtrProv? : List AbstractByte → Option PtrByteFrag
  | .init _ (.some frag) :: rest =>
    match
      Bool.and
        (Nat.blt 0 frag.ptrBytes)
        (Bool.and
          (Nat.beq frag.byteIdx 0)
          (abstractBytesCoherentPtrProvAux
            frag.allocId frag.tag frag.origOffset frag.ptrBytes 1 rest))
    with
    | true => .some frag
    | false => .none
  | _ => .none

/--
Boolean predicate form of `abstractBytesCoherentPtrProv?`.
-/
@[reducible]
def abstractBytesCoherentPtrProv (bytes : List AbstractByte) : Bool :=
  match abstractBytesCoherentPtrProv? bytes with
  | .some _ => true
  | .none => false

/--
Combine provenance annotations from two adjacent initialized bytes strictly:
retains `.some (a, t)` ONLY when both bytes carry the exact same `(allocId, tag)`
pair, stripping provenance (`.none`) whenever either byte lacks provenance or the
two pairs disagree.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Accessing (loading from or storing to) a place that is dangling or based on
> a misaligned pointer."

Modeling choice (`agent_docs/trusted-rust.md`): Closes single-byte and mixed-byte
provenance leaks where combining one provenance-bearing byte with plain or
foreign-allocation bytes previously retained provenance.
-/
@[reducible]
def mergeByteProvenance
    (p₁ p₂ : Option (Nat × Nat)) :
    Option (Nat × Nat) :=
  match p₁, p₂ with
  | .some (a₁, t₁), .some (a₂, t₂) =>
    match Bool.and (Nat.beq a₁ a₂) (Nat.beq t₁ t₂) with
    | true => .some (a₁, t₁)
    | false => .none
  | _, _ => .none

/--
Encode a single `AbstractByte` into a lossless `Value` carrier (keeping
`inductive Value` unchanged):
- `.uninit` -> `.scalar ⟨0, 0⟩`
- `.init b .none` -> `.scalar ⟨b, 1⟩`
- `.init b (.some frag)` -> 5-element aggregate carrying `b` and all five
  `PtrByteFrag` fields (`allocId`, `tag`, `byteIdx`, `origOffset`, `ptrBytes`)
  with a 1-byte `.ptr` leaf so `valueHasProv = true`, `valueContainsUninit = false`,
  and `valueContainsUnit = false`.

Modeling choice (`agent_docs/trusted-rust.md`): Internal abstract-byte storage
carrier for union overlays and bytewise pointer copies through `[u8; N]`;
disjoint from valid Rust pointer `Value`s (Rust pointers have width `4` or `8`,
never `1`).
-/
@[reducible]
def encodeRawAbstractByteVal : AbstractByte → Value
  | .uninit => .scalar ⟨0, 0⟩
  | .init b .none => .scalar ⟨b.toBitVec.toNat, 1⟩
  | .init b (.some frag) =>
    .aggregate 0
      (.ptr { allocId := frag.allocId, offsetBytes := b.toBitVec.toNat } 1 ::
       .scalar ⟨frag.tag, 8⟩ ::
       .scalar ⟨frag.byteIdx, 8⟩ ::
       .scalar ⟨frag.origOffset, 8⟩ ::
       .scalar ⟨frag.ptrBytes, 8⟩ :: .nil)

/--
Decode a single lossless raw-byte carrier `Value` produced by
`encodeRawAbstractByteVal` back into its exact `AbstractByte`.

Reference (`core::ptr::copy_nonoverlapping` documentation, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "The copy is \"untyped\" in the sense that data may be uninitialized or
> otherwise violate the requirements of `T`. The initialization state is
> preserved exactly."

Modeling choice (`agent_docs/trusted-rust.md`): Exact partial inverse of
`encodeRawAbstractByteVal`.
-/
@[reducible]
def decodeRawAbstractByteVal? : Value → Option AbstractByte
  | .scalar ⟨0, 0⟩ => .some .uninit
  | .scalar ⟨bits, 1⟩ => .some (.init (UInt8.ofNat bits) .none)
  | .aggregate 0
      (.ptr p 1 ::
       .scalar ⟨tag, 8⟩ ::
       .scalar ⟨byteIdx, 8⟩ ::
       .scalar ⟨origOffset, 8⟩ ::
       .scalar ⟨ptrBytes, 8⟩ :: .nil) =>
    .some
      (.init (UInt8.ofNat p.offsetBytes)
        (.some {
          allocId := p.allocId
          tag := tag
          byteIdx := byteIdx
          origOffset := origOffset
          ptrBytes := ptrBytes
        }))
  | _ => .none

/--
Decode a list of lossless raw-byte carrier `Value`s into `List AbstractByte`.

Reference (`core::ptr::copy_nonoverlapping` documentation, Rust 1.98.0):
<https://doc.rust-lang.org/1.98.0/core/ptr/fn.copy_nonoverlapping.html>

> "The copy is \"untyped\" in the sense that data may be uninitialized or
> otherwise violate the requirements of `T`. The initialization state is
> preserved exactly."

Modeling choice (`agent_docs/trusted-rust.md`): Pointwise lift of
`decodeRawAbstractByteVal?` over `List Value`.
-/
def decodeRawAbstractByteVals? : List Value → Option (List AbstractByte)
  | .nil => .some .nil
  | v :: rest =>
    match decodeRawAbstractByteVal? v, decodeRawAbstractByteVals? rest with
    | .some b, .some bs => .some (b :: bs)
    | _, _ => .none

/--
`true` when `v` is the 5-element lossless raw-byte provenance-fragment carrier
produced by `encodeRawAbstractByteVal (.init _ (.some _))`.
-/
@[reducible]
def isRawFragByteVal : Value → Bool
  | .aggregate 0
      (.ptr _ 1 ::
       .scalar ⟨_, 8⟩ ::
       .scalar ⟨_, 8⟩ ::
       .scalar ⟨_, 8⟩ ::
       .scalar ⟨_, 8⟩ :: .nil) => true
  | _ => false

/--
Encode `numBytes` provenance-free little-endian bytes of `bits`.
-/
@[reducible]
def encodePlainLittleEndianBytes (bits : Nat) : Nat → List AbstractByte
  | .zero => .nil
  | .succ rem =>
    .init (UInt8.ofNat bits) .none ::
      encodePlainLittleEndianBytes (Nat.div bits 256) rem

/--
Recursive helper for `encodePtrBytes`, stamping each emitted byte with its
0-based `byteIdx`, normalized `origOffset`, and `ptrBytes`.
-/
@[reducible]
def encodePtrBytesAux
    (allocId tag origOffset ptrBytes : Nat) :
    Nat → Nat → Nat → List AbstractByte
  | _, _, .zero => .nil
  | bits, idx, .succ rem =>
    .init (UInt8.ofNat bits)
      (.some {
        allocId := allocId
        tag := tag
        byteIdx := idx
        origOffset := origOffset
        ptrBytes := ptrBytes
      }) ::
      encodePtrBytesAux allocId tag origOffset ptrBytes (Nat.div bits 256) (Nat.add idx 1) rem

/--
Encode a pointer's `bits` into `ptrBytes` little-endian `AbstractByte`s,
stamping byte `i ∈ [0, ptrBytes)` with coherent `PtrByteFrag` metadata
`(allocId, tag, byteIdx := i, origOffset := normPtrByteOffset ptrBytes bits, ptrBytes)`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L259-L264>

> "pub enum Endian {
>     Little,
>     Big,
> }"

Modeling choice (`agent_docs/trusted-rust.md`): Stamps Miri-compatible
`PtrByteFrag` metadata on every encoded pointer byte (`UCG#558` / `rust#148259`).
-/
@[reducible]
def encodePtrBytes
    (bits ptrBytes allocId tag : Nat) :
    List AbstractByte :=
  encodePtrBytesAux allocId tag (normPtrByteOffset ptrBytes bits) ptrBytes bits 0 ptrBytes

/--
Encode the low `numBytes` bytes of `bits` in little-endian order: emits plain
`.init _ .none` bytes when `prov = .none`, and coherent `PtrByteFrag`-stamped
pointer bytes (`encodePtrBytes`) when `prov = .some (allocId, tag)`.

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
    (bits : Nat)
    (numBytes : Nat)
    (prov : Option (Nat × Nat)) :
    List AbstractByte :=
  match prov with
  | .none => encodePlainLittleEndianBytes bits numBytes
  | .some (allocId, tag) => encodePtrBytes bits numBytes allocId tag

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
Decode a list of little-endian `AbstractByte`s into its unsigned bit pattern
`bits : Nat`, returning `.none` if any byte is `.uninit`.
-/
@[reducible]
def decodeLittleEndianBits : List AbstractByte → Option Nat
  | .nil => .some 0
  | .uninit :: _ => .none
  | .init b _ :: rest =>
    match decodeLittleEndianBits rest with
    | .some highBits => .some (Nat.add b.toBitVec.toNat (Nat.mul 256 highBits))
    | .none => .none

/--
Decode a list of little-endian `AbstractByte`s into an unsigned bit pattern
`bits : Nat` and strictly coherent pointer provenance `Option (Nat × Nat)`.

Returns `.none` if any byte in the list is `.uninit`. The returned provenance is
`.some (frag.allocId, frag.tag)` iff `abstractBytesCoherentPtrProv? bytes = .some frag`,
and `.none` otherwise (stripping provenance on partial, mixed, reversed, swapped,
duplicated, cross-width, or offset-spliced byte sequences).

Reference (The Rust Reference, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Note that reading an integer of any type from uninitialized memory is
> undefined behavior."
-/
@[reducible]
def decodeLittleEndianBytes
    (bytes : List AbstractByte) :
    Option (Nat × Option (Nat × Nat)) :=
  match decodeLittleEndianBits bytes with
  | .none => .none
  | .some bits =>
    let prov : Option (Nat × Nat) :=
      match abstractBytesCoherentPtrProv? bytes with
      | .some frag => .some (frag.allocId, frag.tag)
      | .none => .none
    .some (bits, prov)

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
Look up whether byte offset `offset` falls within a `ptrBytes`-wide relocation
entry `(relocOffset, targetPtr)` in `relocs`, returning both `relocOffset` and
`targetPtr` so callers can compute `byteIdx := offset - relocOffset`.

Reference (`compiler/rustc_middle/src/mir/interpret/allocation.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L53-L63>

> "pub struct Allocation<Prov = AllocId, Extra = (), Bytes = Box<[u8]>>"

Modeling choice (`agent_docs/trusted-rust.md`): Bounds each relocation strictly
to `[relocOff, relocOff + ptrBytes)` (e.g. `4` bytes on 32-bit targets, `8`
bytes on 64-bit targets) so 32-bit relocations never bleed provenance into
adjacent bytes `4..7`, and exposes `relocOff` to stamp `PtrByteFrag.byteIdx`.
-/
def lookupRelocEntry
    (relocs : List (Nat × ProvenancePtr))
    (offset : Nat)
    (ptrBytes : Nat := 8) :
    Option (Nat × ProvenancePtr) :=
  match relocs with
  | .nil => .none
  | (relocOff, targetPtr) :: rest =>
    match
      Bool.and
        (Nat.ble relocOff offset)
        (Bool.not (Nat.ble (Nat.add relocOff ptrBytes) offset))
    with
    | true => .some (relocOff, targetPtr)
    | false => lookupRelocEntry rest offset ptrBytes

/--
Look up whether byte offset `offset` falls within a `ptrBytes`-wide relocation
entry `(relocOffset, targetPtr)` in `relocs`.
-/
def lookupRelocAllocId
    (relocs : List (Nat × ProvenancePtr))
    (offset : Nat)
    (ptrBytes : Nat := 8) :
    Option ProvenancePtr :=
  match lookupRelocEntry relocs offset ptrBytes with
  | .some (_, targetPtr) => .some targetPtr
  | .none => .none

/--
Compute the normalized originating pointer offset for a global relocation
`(relocOff, targetPtr)` of width `ptrBytes` in `bytes`: reads the `ptrBytes`
little-endian concrete bytes stored at `[relocOff .. relocOff + ptrBytes)` when
all are initialized, falling back to `normPtrByteOffset ptrBytes targetPtr.offsetBytes`.

Modeling choice (`agent_docs/trusted-rust.md`): Matches `rustc`'s representation
where relocation target offsets are encoded in the allocation's concrete byte
buffer while `relocations` carries the target `AllocId` (and base offset).
-/
def readGlobalRelocOrigOffset
    (bytes : List (Option UInt8))
    (relocOff ptrBytes : Nat)
    (targetPtr : ProvenancePtr) :
    Nat :=
  let rec readLe : Nat → Nat → Option Nat
    | _, .zero => .some 0
    | off, .succ rem =>
      match get? bytes off with
      | .some (.some b) =>
        match readLe (Nat.add off 1) rem with
        | .some hi => .some (Nat.add b.toBitVec.toNat (Nat.mul 256 hi))
        | .none => .none
      | _ => .none
  match readLe relocOff ptrBytes with
  | .some bits => normPtrByteOffset ptrBytes bits
  | .none => normPtrByteOffset ptrBytes targetPtr.offsetBytes

/--
Read `remLen` bytes starting at `offset` from a `CapturedAllocation`'s byte mask
and relocation table into a `List AbstractByte`, stamping `PtrByteFrag` with
`byteIdx := offset - relocOff` and `ptrBytes` for bytes covered by a relocation.
-/
def globalAllocBytesAux
    (bytes : List (Option UInt8))
    (relocs : List (Nat × ProvenancePtr))
    (offset : Nat)
    (rem : Nat)
    (ptrBytes : Nat := 8) :
    Option (List AbstractByte) :=
  match rem with
  | .zero => .some .nil
  | .succ rem' =>
    match get? bytes offset with
    | .none => .none
    | .some optByte =>
      match globalAllocBytesAux bytes relocs (Nat.add offset 1) rem' ptrBytes with
      | .none => .none
      | .some restBytes =>
        let absByte :=
          match optByte with
          | .none => AbstractByte.uninit
          | .some b =>
            let prov : Option PtrByteFrag :=
              match Nat.blt 0 ptrBytes, lookupRelocEntry relocs offset ptrBytes with
              | true, .some (relocOff, targetPtr) =>
                .some {
                  allocId := targetPtr.allocId
                  tag := targetPtr.tag
                  byteIdx := Nat.sub offset relocOff
                  origOffset := readGlobalRelocOrigOffset bytes relocOff ptrBytes targetPtr
                  ptrBytes := ptrBytes
                }
              | _, _ => .none
            AbstractByte.init b prov
        .some (absByte :: restBytes)

/--
Extract `len` `AbstractByte`s starting at `offset` from a global
`CapturedAllocation` at target pointer width `ptrBytes` (default `8`).

Reference (`compiler/rustc_middle/src/mir/interpret/allocation.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/interpret/allocation.rs#L53-L63>

> "pub struct Allocation<Prov = AllocId, Extra = (), Bytes = Box<[u8]>>"
-/
def globalAllocSliceToAbstractBytes
    (alloc : CapturedAllocation)
    (offset len : Nat)
    (ptrBytes : Nat := 8) :
    Option (List AbstractByte) :=
  match Nat.ble offset (length alloc.bytes) with
  | false => .none
  | true => globalAllocBytesAux alloc.bytes alloc.relocations offset len ptrBytes

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
Byte width of a `PrimitiveKind` at target pointer width `ptrBytes` (default `8`).

Reference (The Rust Reference 1.98.0, "Type Layout — Primitive data layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#primitive-data-layout>

> "usize and isize have a size big enough to contain every address on the
> target platform. For example, on a 32 bit target, this is 4 bytes, and on a
> 64 bit target, this is 8 bytes."
-/
@[reducible]
def primitiveKindByteWidth (pk : PrimitiveKind) (ptrBytes : Nat := 8) : Option Nat :=
  match pk with
  | .int bits _ =>
    match Nat.beq bits 0 with
    | true => .none
    | false => .some (Nat.div bits 8)
  | .float bits =>
    match Nat.beq bits 0 with
    | true => .none
    | false => .some (Nat.div bits 8)
  | .pointer _ =>
    match Nat.beq ptrBytes 0 with
    | true => .none
    | false => .some ptrBytes

/--
Byte width of a `ScalarLayout` at target pointer width `ptrBytes` (default `8`).
-/
@[reducible]
def scalarLayoutByteWidth (sl : ScalarLayout) (ptrBytes : Nat := 8) : Option Nat :=
  match sl with
  | .initialized pk _ => primitiveKindByteWidth pk ptrBytes
  | .union pk => primitiveKindByteWidth pk ptrBytes

/--
Decode `bytes` according to a compiler `ScalarLayout` descriptor `sl` at target
pointer width `ptrBytes` (default `8`), enforcing `validRange` when `sl` is
`.initialized pk validRange` and strict `UCG#558` pointer-byte fragment coherence
without ever fabricating pointer provenance from integer bits.

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

Reference (The Rust Reference 1.98.0, "Behavior considered undefined"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html>

> "Accessing (loading from or storing to) a place that is dangling or based on
> a misaligned pointer."

Modeling choice (`agent_docs/trusted-rust.md`): Pointer scalar layouts retain
`Value.ptr` ONLY when `abstractBytesCoherentPtrProv? bytes` succeeds at width `sz`,
and otherwise decode to provenance-less `Value.scalar` (subject to `validRange`
for `.initialized`), never forging provenance from integer bits.
-/
@[reducible]
def decodeScalarLayoutBytes
    (sl : ScalarLayout)
    (bytes : List AbstractByte)
    (ptrBytes : Nat := 8) :
    Option Value :=
  match scalarLayoutByteWidth sl ptrBytes with
  | .none => .none
  | .some sz =>
    match Nat.beq (length bytes) sz with
    | false => .none
    | true =>
      match sl with
      | .initialized pk validRange =>
        match decodeScalarBytes bytes false with
        | .none => .none
        | .some (sv, _) =>
          match wrappingRangeContains validRange sv.bits with
          | false => .none
          | true =>
            match pk with
            | .pointer _ =>
              match abstractBytesCoherentPtrProv? bytes with
              | .some frag =>
                match Nat.beq frag.ptrBytes sz with
                | true =>
                  .some (.ptr { allocId := frag.allocId, offsetBytes := sv.bits } sz)
                | false => .some (.scalar sv)
              | .none => .some (.scalar sv)
            | _ => .some (.scalar sv)
      | .union pk =>
        match decodeScalarBytes bytes false with
        | .some (sv, _) =>
          match pk with
          | .pointer _ =>
            match abstractBytesCoherentPtrProv? bytes with
            | .some frag =>
              match Nat.beq frag.ptrBytes sz with
              | true =>
                .some (.ptr { allocId := frag.allocId, offsetBytes := sv.bits } sz)
              | false => .some (.scalar sv)
            | .none => .some (.scalar sv)
          | _ => .some (.scalar sv)
        | .none => .none

/--
Compute the target byte size of a `RigidTy` at target pointer width `ptrBytes`.

Reference (The Rust Reference 1.98.0, "Type Layout — Primitive data layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#primitive-data-layout>

> "usize and isize have a size big enough to contain every address on the
> target platform. For example, on a 32 bit target, this is 4 bytes, and on a
> 64 bit target, this is 8 bytes."
-/
@[reducible]
def rigidTyKindByteSizeFor (ptrBytes : Nat) : RigidTy → Option Nat
  | .bool => .some 1
  | .char => .some 4
  | .uint .usize => .some ptrBytes
  | .int .isize => .some ptrBytes
  | .uint w => intCastTargetBytes (.uint w)
  | .int w => intCastTargetBytes (.int w)
  | .tuple .nil => .some 0
  | .fnDef _ _ => .some 0
  | .fnPtr _ _ _ _ => .some ptrBytes
  | .ref _ pointee =>
    match pointee with
    | .slice _ => .some (Nat.add ptrBytes ptrBytes)
    | .str => .some (Nat.add ptrBytes ptrBytes)
    | .dynamic _ => .some (Nat.add ptrBytes ptrBytes)
    | _ => .some ptrBytes
  | .rawPtr _ pointee =>
    match pointee with
    | .slice _ => .some (Nat.add ptrBytes ptrBytes)
    | .str => .some (Nat.add ptrBytes ptrBytes)
    | .dynamic _ => .some (Nat.add ptrBytes ptrBytes)
    | _ => .some ptrBytes
  | .array elemKind n =>
    match rigidTyKindByteSizeFor ptrBytes elemKind with
    | .some elemSz => .some (Nat.mul elemSz n)
    | .none => .none
  | _ => .none

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
Sum the byte sizes of a list of `RigidTy` tuple elements at target pointer width
`ptrBytes` when each element has a known structural byte size.
-/
@[reducible]
def tupleFieldsByteSizeFor (ptrBytes : Nat) : List RigidTy → Option Nat
  | .nil => .some 0
  | k :: rest =>
    match rigidTyKindByteSizeFor ptrBytes k, tupleFieldsByteSizeFor ptrBytes rest with
    | .some sz, .some restSz => .some (Nat.add sz restSz)
    | _, _ => .none

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
the value's runtime representation (`.unit`, `.scalar`, `.ptr`, or `.aggregate`),
failing closed (`.none`) on `Value.uninit`.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "- An integer (`i*`/`u*`), floating point value (`f*`), or raw pointer must be initialized, i.e., must not be obtained from uninitialized memory."
>
> "Note: Uninitialized memory is also implicitly invalid for any type that has a restricted set of valid values. In other words, the only cases in which reading uninitialized memory is permitted are inside `union`s and in “padding” (the gaps between the fields of a type)."
-/
@[reducible]
def encodeUntypedValueToBytes :
    Nat → Value → Option (List AbstractByte)
  | .zero, _ => .none
  | .succ _, .unit => .some .nil
  | .succ _, .uninit => .none
  | .succ _, .scalar sv => encodeScalarBytes sv .none
  | .succ _, .ptr p sz =>
    encodeScalarBytes ⟨p.offsetBytes, sz⟩ (.some (p.allocId, p.tag))
  | .succ fuel', .aggregate varIdx fields =>
    match isRawFragByteVal (.aggregate varIdx fields) with
    | true =>
      match decodeRawAbstractByteVal? (.aggregate varIdx fields) with
      | .some b => .some (b :: .nil)
      | .none => .none
    | false =>
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
Encode union fields `fieldVals` into a shared storage buffer of `totalSize`
bytes at offset `0` (`FieldsShape.union`).

1-to-1 with overlapping union field storage in Rust (`FieldsShape::Union`):
- When `firstField` encodes to `firstBytes` of full union size
  (`length firstBytes == totalSize`), writes `firstBytes` at offset `0` over an
  uninitialized `totalSize`-byte buffer.
- When `firstField` encodes to `firstBytes` of zero size (`length firstBytes ==
  0`, such as `uninit: ()` at field `0` of `MaybeUninit<T>`), preserves any
  full-size backing field in `rest` (via `findFullSize rest`), or otherwise
  returns `replicateUninitBytes totalSize`.
- When `firstField` encodes to a smaller non-zero active variant
  (`0 < length firstBytes < totalSize`), overlays `firstBytes` at offset `0`
  onto `baseBuf` (taken from `findFullSize rest` if a full-size backing field
  is present, or `replicateUninitBytes totalSize` otherwise), preserving
  trailing bytes `[length firstBytes .. totalSize)` from the backing union
  storage.

Reference (The Rust Reference, "Unions"):
<https://doc.rust-lang.org/1.98.0/reference/items/unions.html>

> "The key property of unions is that all fields of a union share common
> storage. As a result, writes to one field of a union can overwrite its other
> fields, and size of a union is determined by the size of its largest field."
>
> "Unions have no notion of an “active field”. Instead, every union access just
> interprets the storage as the type of the field used for the access. Reading a
> union field reads the bits of the union at the field’s type."

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
  match fieldVals with
  | .nil => .none
  | firstField :: rest =>
    match encodeFallback firstField with
    | .some firstBytes =>
      match Nat.beq (length firstBytes) totalSize with
      | true =>
        match findFullSize (firstField :: rest) with
        | .some bs => .some bs
        | .none =>
          writeAbstractBytesAt (replicateUninitBytes totalSize) 0 firstBytes
      | false =>
        match Nat.beq (length firstBytes) 0 with
        | true =>
          match findFullSize rest with
          | .some bs => .some bs
          | .none =>
            writeAbstractBytesAt (replicateUninitBytes totalSize) 0 firstBytes
        | false =>
          let baseBuf :=
            match findFullSize rest with
            | .some bs => bs
            | .none => replicateUninitBytes totalSize
          writeAbstractBytesAt baseBuf 0 firstBytes
    | .none => findFullSize rest

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
            match decodeByLayout fIdx bytes with
            | .some v => v
            | .none => .unit
          | false =>
            match sliceAbstractBytes bytes 0 fl.size.bytes with
            | .none => .unit
            | .some fSlice =>
              match decodeByLayout fIdx fSlice with
              | .some v => v
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
Return `true` when decoding a value of `RigidTy` `k` consults `Ty.layoutIdx`
in the `LayoutTable` (namely `.adt`, `.tuple`, and `.array`), and `false` for
layout-independent primitive and pointer kinds.

Reference (The Rust Reference, "Type Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html>

> "The layout of a type is its size, alignment, and the relative offsets of its
> fields."
-/
@[reducible]
def tupleKindNeedsLayoutIdx : RigidTy → Bool
  | .adt _ _ => true
  | .tuple (_ :: _) => true
  | .array elemKind _ => tupleKindNeedsLayoutIdx elemKind
  | _ => false

/--
Return `true` when any field kind in `ks` consults `Ty.layoutIdx`
(`tupleKindNeedsLayoutIdx`).

Reference (The Rust Reference, "Tuple Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#tuple-layout>

> "Tuples do not have any guarantees about their layout."
-/
@[reducible]
def anyTupleKindNeedsLayoutIdx : List RigidTy → Bool
  | .nil => false
  | k :: rest => Bool.or (tupleKindNeedsLayoutIdx k) (anyTupleKindNeedsLayoutIdx rest)

/--
Decode a list of tuple fields from `bytes` at `offsets` pairing each field's
`RigidTy` in `fieldKinds` with its compiler-computed `TypeLayout.fieldLayouts`
index `fIdx` so compound tuple fields (such as `(Unaligned<bool>,)`) resolve
their exact field layout rather than falling back to `layoutIdx := 0`.

Reference (The Rust Reference, "Tuple Layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#tuple-layout>

> "Tuples do not have any guarantees about their layout."
-/
@[reducible]
def decodeTupleFieldsWithLayouts
    (decodeTypedWithLayout : RigidTy → Nat → List AbstractByte → Option Value)
    (layouts : LayoutTable)
    (bytes : List AbstractByte) :
    List Size → List RigidTy → List Nat → Option (List Value)
  | .nil, .nil, .nil => .some .nil
  | off :: offRest, k :: kRest, fIdx :: fRest =>
    match LayoutTable.lookup layouts fIdx with
    | .none => .none
    | .some fl =>
      match sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | .none => .none
      | .some fSlice =>
        match decodeTypedWithLayout k fIdx fSlice with
        | .none => .none
        | .some v =>
          match
            decodeTupleFieldsWithLayouts
              decodeTypedWithLayout
              layouts
              bytes
              offRest
              kRest
              fRest
          with
          | .some vs => .some (v :: vs)
          | .none => .none
  | _, _, _ => .none

/--
Default structural recursion budget for `encodeValueToBytes` and
`decodeValueFromBytes`.
-/
@[reducible]
def defaultCodecFuel : Nat := 16

/--
Search `discriminants` starting at 0-based variant index `curIdx` for the first
variant whose machine discriminant bit pattern equals `tagBits`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1950-L1954>

> "    /// Enum-likes with more than one variant: each variant comes with
>     /// a *discriminant* (usually the same as the variant index but the user can
>     /// assign explicit discriminant values). That discriminant gets encoded
>     /// as a *tag* on the machine."
-/
@[reducible]
def findDiscriminantVariantIdx? : Nat → List Nat → Nat → Option Nat
  | _, .nil, _ => .none
  | curIdx, d :: rest, tagBits =>
    match Nat.beq d tagBits with
    | true => .some curIdx
    | false => findDiscriminantVariantIdx? (.succ curIdx) rest tagBits

/--
Resolve a decoded multi-variant enum tag bit pattern `tagBits` to its 0-based
variant index: when `variantDiscriminants` (`TypeLayout.variantDiscriminants`) is
non-empty, matches `tagBits` against the explicit per-variant machine
discriminants (rejecting undeclared gap bit patterns with `.none`); when empty,
falls back to the default `0 .. n - 1` direct variant-index encoding.

Reference (The Rust Reference, "Primitive representation of field-less enums"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#primitive-representation-of-field-less-enums>

> "For field-less enums, primitive representations set the size and alignment to
> be the same as the primitive type of the same name. For example, a field-less
> enum with a `u8` representation can only have discriminants between 0 and 255
> inclusive."
-/
@[reducible]
def resolveEnumVariantIdxByTag
    (variantDiscriminants : List Nat)
    (tagBits : Nat) :
    Option Nat :=
  match variantDiscriminants with
  | .nil => .some tagBits
  | d :: rest => findDiscriminantVariantIdx? 0 (d :: rest) tagBits

/--
Resolve the machine discriminant bit pattern to write at `tagField` when
encoding variant `varIdx` of a `VariantsShape.multiple` enum: when
`variantDiscriminants` is empty, uses `varIdx` directly (`0 .. n - 1` default
discriminants); when populated, looks up `variantDiscriminants[varIdx]` and
validates that it fits in `tagSz` bytes (`< scalarModulus tagSz`) and satisfies
`tagLayout`'s `WrappingRange`.

Reference (`compiler/rustc_abi/src/lib.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_abi/src/lib.rs#L1950-L1954>

> "    /// Enum-likes with more than one variant: each variant comes with
>     /// a *discriminant* (usually the same as the variant index but the user can
>     /// assign explicit discriminant values). That discriminant gets encoded
>     /// as a *tag* on the machine."
-/
@[reducible]
def resolveEnumDiscriminantForVariant
    (tagLayout : ScalarLayout)
    (tagSz : Nat)
    (variantDiscriminants : List Nat)
    (varIdx : Nat) :
    Option Nat :=
  match variantDiscriminants with
  | .nil => .some varIdx
  | d :: rest =>
    match get? (d :: rest) varIdx with
    | .some discrBits =>
      let inWidth := Nat.blt discrBits (scalarModulus tagSz)
      let inRange :=
        match tagLayout with
        | .initialized _ vr => wrappingRangeContains vr discrBits
        | .union _ => true
      match Bool.and inWidth inRange with
      | true => .some discrBits
      | false => .none
    | .none => .none

/--
Fuel-bounded byte-level encoder converting a runtime `Value` of type `ty` under
`layouts` into its little-endian `List AbstractByte` representation.

- `.bool`: `0` encodes to `[.init 0x00 none]` and `1` encodes to
  `[.init 0x01 none]`; any other bit pattern fails with `.none`.
- `.char`: 4-byte Unicode scalar value (`isValidCharCode`) encodes to 4
  little-endian initialized bytes.
- `.uint _` and `.int _`: fixed-width (`1, 2, 4, 8, 16` byte; `layoutPointerBytes`
  for `usize`/`isize`) scalar encodes in little-endian order via `encodeScalarBytes`.
- `.tuple .nil` and `.fnDef _ _`: zero-sized value encodes to `[]`.
- `.rawPtr _ _`, `.ref _ _`, and `.fnPtr`: thin pointer of target width
  `ptrBytes := layoutPointerBytes layouts` encodes its offset in little-endian
  order while stamping coherent `PtrByteFrag` metadata onto all `ptrBytes` bytes;
  wide pointers encode their `ptrBytes`-byte data pointer followed by their
  `ptrBytes`-byte metadata (`.scalar` length or `.ptr` `dyn` vtable pointer,
  stamping `PtrByteFrag` onto both halves).
- `.array elemKind n`: encodes all `n` elements sequentially (using element
  `fieldLayouts` when present, and preserving lossless raw-byte provenance
  carriers in `[u8; n]`).
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

Reference (The Rust Reference 1.98.0, "Type Layout — Pointers and references layout"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#pointers-and-references-layout>

> "Pointers to sized types have the same size and alignment as usize."
> "Pointers to unsized types are sized. The size and alignment of a pointer to
> an unsized type are each guaranteed to be greater than or equal to those of a
> pointer to a sized type."
-/
@[reducible]
def encodeValueToBytes :
    Nat → LayoutTable → Ty → Value → Option (List AbstractByte)
  | .zero, _, _, _ => .none
  | .succ fuel', layouts, ty, v =>
    let ptrBytes := layoutPointerBytes layouts
    let encodePtrHalf (halfVal : Value) : Option (List AbstractByte) :=
      match Nat.blt 0 ptrBytes, halfVal with
      | true, .ptr p sz =>
        match Nat.beq sz ptrBytes with
        | true => encodeScalarBytes ⟨p.offsetBytes, ptrBytes⟩ (.some (p.allocId, p.tag))
        | false => .none
      | true, .scalar sv =>
        match Nat.beq sv.sizeBytes ptrBytes with
        | true => encodeScalarBytes sv .none
        | false => .none
      | true, .aggregate 0 rawVals =>
        match Nat.beq (length rawVals) ptrBytes with
        | true => decodeRawAbstractByteVals? rawVals
        | false => .none
      | _, _ => .none
    let encodeWideMetaHalf (metaVal : Value) : Option (List AbstractByte) :=
      match Nat.blt 0 ptrBytes, metaVal with
      | true, .ptr vt vtSz =>
        match Nat.beq vtSz ptrBytes with
        | true => encodeScalarBytes ⟨vt.offsetBytes, ptrBytes⟩ (.some (vt.allocId, vt.tag))
        | false => .none
      | true, .scalar metaSc =>
        encodeScalarBytes ⟨metaSc.bits, ptrBytes⟩ .none
      | _, _ => .none
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
    | .fnPtr _ _ _ _ => encodePtrHalf v
    | .rawPtr _ pointee =>
      let isWide :=
        match pointee with
        | .slice _ => true
        | .str => true
        | .dynamic _ => true
        | _ => false
      match isWide, v with
      | false, _ => encodePtrHalf v
      | true, .aggregate 0 (dataVal :: metaVal :: .nil) =>
        match encodePtrHalf dataVal, encodeWideMetaHalf metaVal with
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
      | false, _ => encodePtrHalf v
      | true, .aggregate 0 (dataVal :: metaVal :: .nil) =>
        match encodePtrHalf dataVal, encodeWideMetaHalf metaVal with
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
                | .none =>
                  match elemKind with
                  | .tuple ks => tupleFieldsByteSize ks
                  | _ => .none
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
                scalarLayoutByteWidth tagLayout ptrBytes,
                get? variantShapes varIdx
              with
              | .arbitrary outerOffsets _,
                .some tagSz,
                .some (.arbitrary varOffsets _) =>
                match get? outerOffsets tagField with
                | .none => .none
                | .some tagOff =>
                  match
                    resolveEnumDiscriminantForVariant
                      tagLayout
                      tagSz
                      l.variantDiscriminants
                      varIdx
                  with
                  | .none => .none
                  | .some tagBits =>
                    match encodeScalarBytes ⟨tagBits, tagSz⟩ .none with
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
surrogate or out-of-range scalar into `.char`, an incoherent or provenance-less
pointer image into `.ref` / `.fnPtr`, or an out-of-range niche value into
`.initialized` `ScalarLayout`). Never fabricates pointer provenance from plain
or incoherent integer bytes (`UCG#558` / `rust#148259`).
For `.adt` structs and tuples with `FieldsShape.arbitrary`, bytes at padding
offsets outside field spans are not read and may be `.uninit`, and explicit
`fieldLayouts` are preferred over hardcoded `layoutIdx := 0`.

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
    let ptrBytes := layoutPointerBytes layouts
    let decodePtrNoForgeLocal (isRef : Bool) (pointee : RigidTy) (bs : List AbstractByte) :
        Option Value :=
      let decodeData (dataBytes : List AbstractByte) : Option Value :=
        match Bool.and (Nat.blt 0 ptrBytes) (Nat.beq (length dataBytes) ptrBytes),
              decodeScalarBytes dataBytes false with
        | true, .some (sv, _) =>
          match abstractBytesCoherentPtrProv? dataBytes with
          | .some frag =>
            match Nat.beq frag.ptrBytes ptrBytes with
            | true => .some (.ptr { allocId := frag.allocId, offsetBytes := sv.bits } ptrBytes)
            | false =>
              match isRef with
              | true => .none
              | false => .some (.scalar ⟨sv.bits, ptrBytes⟩)
          | .none =>
            match isRef with
            | true => .none
            | false => .some (.scalar ⟨sv.bits, ptrBytes⟩)
        | _, _ => .none
      let wideMetaIsDyn : Option Bool :=
        match pointee with
        | .slice _ => .some false
        | .str => .some false
        | .dynamic _ => .some true
        | _ => .none
      match wideMetaIsDyn with
      | .none => decodeData bs
      | .some isDyn =>
        match Bool.and (Nat.blt 0 ptrBytes) (Nat.beq (length bs) (Nat.add ptrBytes ptrBytes)) with
        | false => .none
        | true =>
          let dataBytes := takeAbstractBytes ptrBytes bs
          let metaBytes := dropAbstractBytes ptrBytes bs
          let metaOpt : Option Value :=
            match decodeScalarBytes metaBytes false with
            | .none => .none
            | .some (metaSv, _) =>
              match isDyn with
              | true =>
                match abstractBytesCoherentPtrProv? metaBytes with
                | .some vtFrag =>
                  match Nat.beq vtFrag.ptrBytes ptrBytes with
                  | true =>
                    .some (.ptr { allocId := vtFrag.allocId, offsetBytes := metaSv.bits } ptrBytes)
                  | false =>
                    match isRef with
                    | true => .none
                    | false => .some (.scalar ⟨metaSv.bits, ptrBytes⟩)
                | .none =>
                  match isRef with
                  | true => .none
                  | false => .some (.scalar ⟨metaSv.bits, ptrBytes⟩)
              | false =>
                match abstractBytesHaveProv metaBytes with
                | true => .none
                | false => .some (.scalar ⟨metaSv.bits, ptrBytes⟩)
          match decodeData dataBytes, metaOpt with
          | .some dataVal, .some metaVal => .some (.aggregate 0 (dataVal :: metaVal :: .nil))
          | _, _ => .none
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
    | .fnPtr _ _ _ _ => decodePtrNoForgeLocal true (.tuple .nil) bytes
    | .rawPtr _ pointee => decodePtrNoForgeLocal false pointee bytes
    | .ref _ pointee => decodePtrNoForgeLocal true pointee bytes
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
            | .none =>
              match elemKind with
              | .tuple ks => tupleFieldsByteSize ks
              | _ => .none
        match elemSzOpt with
        | .none => .none
        | .some elemSz =>
          match Nat.beq (length bytes) (Nat.mul elemSz n) with
          | false => .none
          | true =>
            let elemLayoutIdx :=
              match tupleKindNeedsLayoutIdx elemKind with
              | false => 0
              | true =>
                match LayoutTable.lookup layouts ty.layoutIdx with
                | .some l =>
                  match l.fieldLayouts with
                  | fIdx :: _ => fIdx
                  | .nil => 0
                | .none => 0
            match
              decodeArrayChunksWith
                (fun chunk =>
                  decodeValueFromBytes fuel' layouts
                    { kind := elemKind, layoutIdx := elemLayoutIdx } chunk)
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
            match anyTupleKindNeedsLayoutIdx fieldKinds with
            | false =>
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
            | true =>
              match
                Bool.and
                  (Nat.beq (length l.fieldLayouts) (length offsets))
                  (Nat.beq (length fieldKinds) (length offsets))
              with
              | true =>
                let decodeWithLayout :=
                  fun (k : RigidTy) (fIdx : Nat) (bs : List AbstractByte) =>
                    decodeValueFromBytes fuel' layouts { kind := k, layoutIdx := fIdx } bs
                match
                  decodeTupleFieldsWithLayouts
                    decodeWithLayout
                    layouts
                    bytes
                    offsets
                    fieldKinds
                    l.fieldLayouts
                with
                | .some vals => .some (.aggregate 0 vals)
                | .none => .none
              | false =>
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
                    match scalarLayoutByteWidth s0 ptrBytes with
                    | .none => .none
                    | .some sz0 =>
                      match sliceAbstractBytes bytes off0.bytes sz0 with
                      | .none => .none
                      | .some slice0 =>
                        match decodeScalarLayoutBytes s0 slice0 ptrBytes with
                        | .some v0 => .some (.aggregate variantIdx (v0 :: .nil))
                        | .none => .none
                  | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
                    match scalarLayoutByteWidth s0 ptrBytes, scalarLayoutByteWidth s1 ptrBytes with
                    | .some sz0, .some sz1 =>
                      match
                        sliceAbstractBytes bytes off0.bytes sz0,
                        sliceAbstractBytes bytes off1.bytes sz1
                      with
                      | .some slice0, .some slice1 =>
                        match
                          decodeScalarLayoutBytes s0 slice0 ptrBytes,
                          decodeScalarLayoutBytes s1 slice1 ptrBytes
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
                | .scalar s0 => decodeScalarLayoutBytes s0 bytes ptrBytes
                | _ =>
                  match decodeScalarBytes bytes false with
                  | .some (sv, _) => .some (.scalar sv)
                  | .none => .none
            | .union fieldCount =>
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
                    .unit
                    (fHead :: fTail)
                .some (.aggregate variantIdx vals)
              | .nil =>
                let byArg : Option Value :=
                  match args with
                  | argKind :: .nil =>
                    match argKind with
                    | .adt _ _ => .none
                    | _ =>
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
                      match decodeScalarLayoutBytes (.union pk) bytes ptrBytes with
                      | .some v0 => v0
                      | .none => .unit
                    | .scalar s0 =>
                      match decodeScalarLayoutBytes s0 bytes ptrBytes with
                      | .some v0 => v0
                      | .none => .unit
                    | _ =>
                      match decodeScalarBytes bytes false with
                      | .some (sv, _) => .scalar sv
                      | .none => .unit
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
            match l.fields, scalarLayoutByteWidth tagLayout ptrBytes with
            | .arbitrary outerOffsets _, .some tagSz =>
              match get? outerOffsets tagField with
              | .none => .none
              | .some tagOff =>
                match sliceAbstractBytes bytes tagOff.bytes tagSz with
                | .none => .none
                | .some tagSlice =>
                  match decodeScalarLayoutBytes tagLayout tagSlice ptrBytes with
                  | .some (.scalar tagSc) =>
                    match resolveEnumVariantIdxByTag l.variantDiscriminants tagSc.bits with
                    | .some varIdx =>
                      match get? variantShapes varIdx with
                      | .some (.arbitrary varOffsets _) =>
                        match decodeFieldsBySpan bytes l.size.bytes varOffsets with
                        | .some vals => .some (.aggregate varIdx vals)
                        | .none => .none
                      | _ => .none
                    | .none => .none
                  | _ => .none
            | _, _ => .none
    | _ => .none

end Trusted.Rustc.V2026_06_01.MirSemantics
