/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Generated

/-!
# Ground-truth interpretation of a small MiniRust fragment

This module gives Lean meaning to a deliberately small set of MiniRust
features, written *directly against the mechanically generated MiniRust types*
(`MiniRustSpec.Gen.*`, generated from upstream MiniRust `d821c6e3`). Each
definition transcribes one upstream specr-lang function, and its doc comment
quotes the upstream code and cites `spec/<file>.md`. The upstream source is
vendored at `minirust/vendor/d821c6e3a3d358fa8a556774dc12b4aa5d0d65ed/`, and
`MiniRustSpec.Anchors` pins the token hash of every transcribed item so
that an upstream change breaks the build instead of silently diverging.

Nothing here was shaped to resemble Anneal's MIR semantics: the definitions
follow MiniRust's evaluation order, MiniRust's byte-level memory (stack locals
live in `BasicMemory` allocations and are (de)serialized through the
representation relation), MiniRust's data-race bookkeeping, and MiniRust's
stack-pop protocol. Differences from Anneal are stated in
`minirust/README.md` and the `MiniRustSpec.Correspondence` modules, not hidden
here.

## Interpreted fragment

* `Machine::step` for a machine whose enabled threads are exactly one thread
  (`spec/lang/machine.md`). The daemonic thread choice `pick(..)` then has a
  unique solution; with more than one enabled thread we report
  `Stop.unsupported` instead of resolving the choice.
* `Statement::Assign` and `Statement::PlaceMention`
  (`spec/lang/step/statements.md`).
* `PlaceExpr::Local` and `PlaceExpr::Index` (`spec/lang/step/expressions.md`),
  together with `Machine::ptr_offset_inbounds` (`spec/lang/step/operators.md`)
  and `Memory::dereferenceable` / `Memory::signed_dereferenceable`
  (`spec/mem/basic.md`, `spec/mem/interface.md`, `spec/mem/concurrent.md`).
* `ValueExpr::Constant` for `Constant::Int`/`Constant::Bool`,
  `ValueExpr::Tuple`, `ValueExpr::Load`,
  `ValueExpr::UnOp` with `UnOp::Int` (all `IntUnOp` variants: `Neg`, `BitNot`,
  `CountOnes`) and `UnOp::Cast(CastOp::IntToInt)`, and `ValueExpr::BinOp` with
  `BinOp::Int` (all `IntBinOp` variants: `Add`, `AddUnchecked`, `Sub`,
  `SubUnchecked`, `Mul`, `MulUnchecked`, `Div`, `DivExact`, `Rem`, `Shl`, `Shr`,
  `ShlUnchecked`, `ShrUnchecked`, `BitAnd`, `BitOr`, `BitXor`)
  (`spec/lang/step/expressions.md`, `spec/lang/step/operators.md`).
* `Terminator::Goto`, `Terminator::Switch`, `Terminator::Unreachable`, and
  `Terminator::Return` (`spec/lang/step/terminators.md`), including frame
  teardown, `storage_dead` of every local, and both stack-pop actions.
* The representation relation for `Type::Int`, `Type::Bool`, and `Type::Array`
  (`spec/lang/representation.md`), `Type::layout` for those types and
  `LayoutStrategy::compute_size_and_align` for `Sized` layouts
  (`spec/lang/types.md`, with `Machine::compute_size` from
  `spec/lang/machine.md`), and `BasicMemory`'s `load`, `store`, `deallocate`,
  `dereferenceable`, `signed_dereferenceable`, and `check_ptr`
  (`spec/mem/basic.md`, `spec/mem/interface.md`), wrapped by
  `ConcurrentMemory`'s access recording (`spec/mem/concurrent.md`).
* The `x86_64` target (`spec/prelude/target.md`) as the instance of `T` and
  `BasicMemory<x86_64>` as the instance of `M`.

Everything else returns `Stop.unsupported`, so the interpretation is partial
but never silently wrong.

## Effects

specr-lang functions return `Result`/`NdResult`. We use `Except Stop`:

* `Stop.ub` is `throw_ub!` (`TerminationInfo::Ub`),
* `Stop.deadlock` is `throw_deadlock!`,
* `Stop.specPanic` is a specr-lang `panic!`, failed `assert!`, `unwrap` of
  `None`, or out-of-range indexing. Upstream says such a panic "is a bug in the
  specification" (vendored `README.md`), so it signals an ill-formed input
  rather than program behavior,
* `Stop.unsupported` marks a construct outside the interpreted fragment.

The only non-deterministic operation reachable from this fragment is the thread
choice in `Machine::step` (allocation is not reachable: `StorageLive` is
outside the fragment); see `pickActiveThread`.
-/

namespace MiniRustSpec.Interp

open MiniRustSpec.Gen
open MiniRustSpec.LibSpecr

/-! ## Instantiation: `M = BasicMemory<x86_64>` -/

/-- The memory model: `BasicMemory<x86_64>` with `ProvExtra = AllocExtra = ()`
(the defaults of `struct BasicMemory<T: Target, ProvExtra = (), AllocExtra = ()>`,
`spec/mem/basic.md`). Its `Memory` instance (`instMemoryBasicMemory`, generated
from `impl<T: Target> Memory for BasicMemory<T>`) sets
`type Provenance = Provenance<()>`. -/
abbrev BM : Type := BasicMemory x86_64

/-- `M::Provenance` for `M = BM`: `(AllocId, ())`. -/
abbrev Prov : Type := Provenance Unit

/-- `ThinPointer<M::Provenance>`. -/
abbrev Ptr : Type := ThinPointer Prov

/-- `AbstractByte<M::Provenance>`. -/
abbrev Byte : Type := AbstractByte Prov

/-- `Value<M>`. -/
abbrev Val : Type := Value BM

/-- `StackFrame<M>`. -/
abbrev Frame : Type := StackFrame BM

/-- `Machine<M>`. -/
abbrev Mach : Type := Machine BM

/-! ## Effects -/

/-- Why an interpreted computation stopped; see the module docs. -/
inductive Stop : Type where
  | ub (msg : String)
  | deadlock
  | specPanic (msg : String)
  | unsupported (what : String)
  deriving DecidableEq

/-- `Result<T>` of specr-lang, plus the two non-behavior stops. -/
abbrev Interp (α : Type) : Type := Except Stop α

/-- `throw_ub!(msg)`. -/
def ub {α : Type} (msg : String) : Interp α := .error (.ub msg)

/-- A specr-lang panic (`panic!`, failed `assert!`, `unwrap` of `None`). -/
def specPanic {α : Type} (msg : String) : Interp α := .error (.specPanic msg)

/-- A construct outside the interpreted fragment. -/
def unsupported {α : Type} (what : String) : Interp α := .error (.unsupported what)

/-! ## `libspecr` operations

`libspecr` 0.1.41 (<https://docs.rs/libspecr/0.1.41>) is the support library
MiniRust is written against; it is not part of the MiniRust repository, so
these operations are hand-written from its documented behavior. -/

/-- `Size::bits()`: the number of bits in `s` bytes. -/
def Size.bits (s : Size) : Nat := 8 * s.bytes

/-- `Size::from_bytes(n)`: `Some` iff `n ≥ 0`. -/
def Size.from_bytes (n : Int) : Option Size :=
  if 0 ≤ n then some ⟨n.toNat⟩ else none

/-- `Size * Int` (`Mul<Int> for Size` in `libspecr`), which panics if the factor is negative. -/
def Size.mulInt (s : Size) (n : Int) : Interp Size :=
  if 0 ≤ n then pure ⟨s.bytes * n.toNat⟩
  else specPanic "Size * Int: negative factor"

/-- `Align::from_bytes(n)`: `Some` iff `n` is a power of two. -/
def alignFromBytes (n : Nat) : Option Align :=
  if n ≠ 0 ∧ n &&& (n - 1) = 0 then some ⟨n⟩ else none

/-- `Align::is_aligned(addr)`: `addr` is a multiple of the alignment. -/
def Align.is_aligned (a : Align) (addr : Int) : Bool := addr % (a.bytes : Int) == 0

/-- `Int::in_bounds(signed, size)`: whether `i` is representable as an integer
of the given signedness and size (unsigned: `[0, 2^bits)`; signed:
`[-2^(bits-1), 2^(bits-1))`). -/
def inBounds (i : Int) (signed : Signedness) (size : Size) : Bool :=
  match signed with
  | .Unsigned => decide (0 ≤ i) && decide (i < (2 : Int) ^ Size.bits size)
  | .Signed =>
    decide (-((2 : Int) ^ (Size.bits size - 1)) ≤ i) && decide (i < (2 : Int) ^ (Size.bits size - 1))

/-- `Int::bring_in_bounds(signed, size)`: reduce `i` modulo `2^bits` into the
representable range (two's complement wrapping). -/
def bringInBounds (i : Int) (signed : Signedness) (size : Size) : Int :=
  let m : Int := (2 : Int) ^ Size.bits size
  let r : Int := i % m
  match signed with
  | .Unsigned => r
  | .Signed => if r < (2 : Int) ^ (Size.bits size - 1) then r else r - m

/-- Termination measure for two's-complement bitwise recursion on `libspecr::Int`
(`num_bigint::BigInt`), measuring distance from the two sign-extension fixed
points `0` (`...000₂`) and `-1` (`...111₂`) of Euclidean floor division by `2`. -/
def intBitMeasure (x : Int) : Nat :=
  if x < 0 then (-x - 1).toNat else x.toNat

/-- Structural recursion over the two's-complement bits of `a : Int` until `a`
reaches one of the two sign-extension fixed points `0` (`...000₂`) or `-1`
(`...111₂`) of Euclidean floor division by `2`. -/
def intBitRec (onZero : Int → Int) (onNegOne : Int → Int) (bitFn : Int → Int → Int) :
    Nat → Int → Int → Int
  | 0, a, b => if a = 0 then onZero b else onNegOne b
  | n + 1, a, b =>
    if a = 0 then onZero b
    else if a = -1 then onNegOne b
    else 2 * intBitRec onZero onNegOne bitFn n (a / 2) (b / 2) + bitFn (a % 2) (b % 2)

/-- Two's-complement bitwise AND `left & right` on `libspecr::Int`. -/
def intBitAnd (a b : Int) : Int :=
  intBitRec (fun _ => 0) (fun b => b) (fun x y => if x = 1 ∧ y = 1 then 1 else 0) (intBitMeasure a) a b

/-- Two's-complement bitwise OR `left | right` on `libspecr::Int`. -/
def intBitOr (a b : Int) : Int :=
  intBitRec (fun b => b) (fun _ => -1) (fun x y => if x = 1 ∨ y = 1 then 1 else 0) (intBitMeasure a) a b

/-- Two's-complement bitwise XOR `left ^ right` on `libspecr::Int`. -/
def intBitXor (a b : Int) : Int :=
  intBitRec (fun b => b) (fun b => -b - 1) (fun x y => if x = y then 0 else 1) (intBitMeasure a) a b

/-- Little-endian bytes of the natural number `u`, `n` bytes long. -/
def leBytes (u : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => UInt8.ofNat (u % 256) :: leBytes (u / 256) n

/-- The natural number denoted by little-endian bytes. -/
def leValue : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leValue bs

/-- `Endianness::encode(signed, size, int) -> Option<List<u8>>`: the two's
complement encoding of `i` in `size` bytes, or `None` if `i` is out of bounds
for `(signed, size)`. -/
def Endianness.encode (e : Endianness) (signed : Signedness) (size : Size) (i : Int) :
    Option (List UInt8) :=
  if inBounds i signed size then
    let bytes := leBytes (i % (2 : Int) ^ Size.bits size).toNat size.bytes
    some (match e with
      | .LittleEndian => bytes
      | .BigEndian => bytes.reverse)
  else
    none

/-- `Endianness::decode(signed, bytes) -> Int`: the integer whose two's
complement encoding (with `bytes.len()` bytes) is `bytes`. -/
def Endianness.decode (e : Endianness) (signed : Signedness) (bytes : List UInt8) : Int :=
  let le := match e with
    | .LittleEndian => bytes
    | .BigEndian => bytes.reverse
  let u : Int := leValue le
  match signed with
  | .Unsigned => u
  | .Signed =>
    if u < (2 : Int) ^ (8 * bytes.length - 1) then u else u - (2 : Int) ^ (8 * bytes.length)

/-- `Map::get(k)`: the value bound to `k`, if any. -/
def mapGet {K V : Type} [DecidableEq K] (m : Map K V) (k : K) : Option V :=
  (m.entries.find? (fun e => decide (e.1 = k))).map Prod.snd

/-- `map[k]` (`Index` on `libspecr::Map`), which panics when `k` is unbound. -/
def mapIndex {K V : Type} [DecidableEq K] (m : Map K V) (k : K) (what : String) : Interp V :=
  match mapGet m k with
  | some v => pure v
  | none => specPanic s!"map index: missing key ({what})"

/-- `Map::remove(k)`: remove `k`, returning its value (if any). -/
def mapRemove {K V : Type} [DecidableEq K] (m : Map K V) (k : K) : Option V × Map K V :=
  (mapGet m k, ⟨m.entries.filter (fun e => !decide (e.1 = k))⟩)

/-- `Set::insert(x)`. -/
def setInsert {T : Type} [DecidableEq T] (s : Set T) (x : T) : Set T :=
  if s.elems.contains x then s else ⟨s.elems ++ [x]⟩

/-- `Set::contains(x)`. -/
def setContains {T : Type} [DecidableEq T] (s : Set T) (x : T) : Bool :=
  s.elems.contains x

/-- `list[i]` (`Index<Int>` on `libspecr::List`), which panics out of range. -/
def listIndex {T : Type} (xs : List T) (i : Int) (what : String) : Interp T :=
  if 0 ≤ i then
    match xs[i.toNat]? with
    | some x => pure x
    | none => specPanic s!"list index out of range ({what})"
  else specPanic s!"negative list index ({what})"

/-- `List::set(i, x)`, which panics out of range. -/
def listSet {T : Type} (xs : List T) (i : Int) (x : T) (what : String) : Interp (List T) :=
  if 0 ≤ i ∧ i.toNat < xs.length then pure (xs.set i.toNat x)
  else specPanic s!"List::set out of range ({what})"

/-- `List::subslice_with_length(start, len)`. -/
def subsliceWithLength {T : Type} (xs : List T) (start len : Int) : Interp (List T) :=
  if 0 ≤ start ∧ 0 ≤ len ∧ start + len ≤ xs.length then
    pure ((xs.drop start.toNat).take len.toNat)
  else specPanic "subslice_with_length out of range"

/-- `List::write_subslice_at_index(start, src)`. -/
def writeSubsliceAtIndex {T : Type} (xs : List T) (start : Int) (src : List T) :
    Interp (List T) :=
  if 0 ≤ start ∧ start + src.length ≤ xs.length then
    pure (xs.take start.toNat ++ src ++ xs.drop (start.toNat + src.length))
  else specPanic "write_subslice_at_index out of range"

/-! ## Target `x86_64` (`spec/prelude/target.md`)

> "impl Target for x86_64 {
>     const PTR_SIZE: Size = Size::from_bits_const(64).unwrap();
>     const PTR_ALIGN: Align = Align::from_bits_const(64).unwrap();
>     const INT_MAX_ALIGN: Align = Align::from_bits_const(128).unwrap();
>     const ENDIANNESS: Endianness = LittleEndian;
>     ..."
-/

/-- `x86_64::PTR_SIZE` = 64 bits:
> "const PTR_SIZE: Size = Size::from_bits_const(64).unwrap();" -/
def x86_64.PTR_SIZE : Size := ⟨8⟩
/-- `x86_64::INT_MAX_ALIGN` = 128 bits:
> "const INT_MAX_ALIGN: Align = Align::from_bits_const(128).unwrap();" -/
def x86_64.INT_MAX_ALIGN : Align := ⟨16⟩
/-- `x86_64::ENDIANNESS`:
> "const ENDIANNESS: Endianness = LittleEndian;" -/
def x86_64.ENDIANNESS : Endianness := .LittleEndian

/-! ## Types and layout (`spec/lang/types.md`) -/

/-- `IntType::can_represent`:
> "pub fn can_represent(&self, i: Int) -> bool { i.in_bounds(self.signed, self.size) }" -/
def IntType.can_represent (t : IntType) (i : Int) : Bool := inBounds i t.signed t.size

/-- `IntType::bring_in_bounds`:
> "pub fn bring_in_bounds(&self, i: Int) -> Int { i.bring_in_bounds(self.signed, self.size) }" -/
def IntType.bring_in_bounds (t : IntType) (i : Int) : Int := bringInBounds i t.signed t.size

/-- `IntType::align::<x86_64>`:
> "let natural_align = Align::from_bytes(size).unwrap();
>  natural_align.min(T::INT_MAX_ALIGN)" -/
def IntType.align (t : IntType) : Interp Align :=
  match alignFromBytes t.size.bytes with
  | some a => pure ⟨min a.bytes x86_64.INT_MAX_ALIGN.bytes⟩
  | none => specPanic "Align::from_bytes(size).unwrap()"

/-- `LayoutStrategy::expect_size` (`spec/lang/types.md`):
> "pub fn expect_size(self, msg: &str) -> Size {
>     match self {
>         LayoutStrategy::Sized(size, _) => size,
>         _ => panic!(\"expect_size called on unsized type: {msg}\"),
>     }
> }" -/
def LayoutStrategy.expect_size (l : LayoutStrategy) (msg : String) : Interp Size :=
  match l with
  | .Sized size _ => pure size
  | _ => specPanic s!"expect_size called on unsized type: {msg}"

/-- `LayoutStrategy::expect_align` (`spec/lang/types.md`):
> "pub fn expect_align(self, msg: &str) -> Align {
>     match self {
>         LayoutStrategy::Sized(_, align) => align,
>         _ => panic!(\"expect_align called on unsized type: {msg}\"),
>     }
> }" -/
def LayoutStrategy.expect_align (l : LayoutStrategy) (msg : String) : Interp Align :=
  match l with
  | .Sized _ align => pure align
  | _ => specPanic s!"expect_align called on unsized type: {msg}"

/-- `LayoutStrategy::compute_size_and_align` (`spec/lang/types.md`) for the
interpreted `Sized` layouts. The unsized strategies (`Slice`, `TraitObject`,
`Tuple`) are outside the fragment, and with only `Sized` layouts the `vtables`
lookup is never consulted, so it is not modelled:
> "pub fn compute_size_and_align<Provenance>(
>     self,
>     meta: Option<PointerMeta<Provenance>>,
>     vtables: impl FnOnce(ThinPointer<Provenance>) -> VTable,
> ) -> (Size, Align) {
>     match (self, meta) {
>         (LayoutStrategy::Sized(size, align), None) => (size, align),
>         ..
>         _ => panic!(\"pointer meta data does not match type\"),
>     }
> }" -/
def LayoutStrategy.compute_size_and_align (l : LayoutStrategy)
    (metadata : Option (PointerMeta Prov)) : Interp (Size × Align) :=
  match l, metadata with
  | .Sized size align, none => pure (size, align)
  | .Sized _ _, some _ => specPanic "pointer meta data does not match type"
  | _, _ => unsupported "LayoutStrategy::compute_size_and_align for an unsized layout"

/-- `Machine::compute_size` (`spec/lang/machine.md`), with the vtable lookup
omitted as in `LayoutStrategy.compute_size_and_align`:
> "fn compute_size(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Size {
>     let (size, _) = layout.compute_size_and_align(meta, self.vtable_lookup());
>     size
> }" -/
def computeSize (layout : LayoutStrategy) (metadata : Option (PointerMeta Prov)) :
    Interp Size := do
  let (size, _) ← LayoutStrategy.compute_size_and_align layout metadata
  pure size

/-- `Type::layout::<x86_64>` for the interpreted types:
> "Int(int_type) => Sized(int_type.size, int_type.align::<T>()),
>  Bool => Sized(Size::from_bytes_const(1), Align::ONE),
>  ..
>  Array { elem, count } => Sized(
>      elem.layout::<T>().expect_size(\"WF ensures array element is sized\") * count,
>      elem.layout::<T>().expect_align(\"WF ensures array element is sized\"),
>  )," -/
def Type.layout : «Type» → Interp LayoutStrategy
  | .Int t => do pure (.Sized t.size (← IntType.align t))
  | .Bool => pure (.Sized ⟨1⟩ ⟨1⟩)
  | .Array elem count => do
    let elemLayout ← Type.layout elem
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
    let elemAlign ← LayoutStrategy.expect_align elemLayout "WF ensures array element is sized"
    let size ← Size.mulInt elemSize count
    pure (.Sized size elemAlign)
  | _ => unsupported "Type::layout for a non-Int, non-Bool, non-Array type"

/-! ## Representation relation (`spec/lang/representation.md`) -/

/-- `AbstractByte::data` (`spec/mem/interface.md`):
> "pub fn data(self) -> Option<u8> {
>     match self {
>         AbstractByte::Uninit => None,
>         AbstractByte::Init(data, _) => Some(data),
>     }
> }" -/
def AbstractByte.data : Byte → Option UInt8
  | .Uninit => none
  | .Init b _ => some b

/-- `Type::decode` for `Bool`, `Int`, and `Array`:
> "fn decode<M: Memory>(Type::Bool: Self, bytes: ..) -> Option<Value<M>> {
>     if bytes.len() != 1 { panic!(..); }
>     ret(match bytes[0] {
>         AbstractByte::Init(0, _) => Value::Bool(false),
>         AbstractByte::Init(1, _) => Value::Bool(true),
>         _ => throw!(),
>     })
> }
> ..
> fn decode<M: Memory>(Type::Int(IntType { signed, size }): Self, bytes: ..) -> Option<Value<M>> {
>     if bytes.len() != size.bytes() { panic!(..); }
>     // Fails if any byte is `Uninit`.
>     let bytes_data: List<u8> = bytes.try_map(|b| b.data())?;
>     ret(Value::Int(M::T::ENDIANNESS.decode(signed, bytes_data)))
> }
> ..
> fn decode<M: Memory>(Type::Array { elem, count }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
>     let elem_size = elem.layout::<M::T>().expect_size(\"WF ensures array element is sized\");
>     let full_size = elem_size * count;
>
>     if bytes.len() != full_size.bytes() { panic!(\"decode of Type::Array with invalid length\"); }
>
>     let chunks: List<_> = (Int::ZERO..count).map(|i|
>         bytes.subslice_with_length(i*elem_size.bytes(), elem_size.bytes())
>     ).collect();
>
>     ret(Value::Tuple(
>         chunks.try_map(|elem_bytes| elem.decode::<M>(elem_bytes))?
>     ))
> }" -/
def Type.decode : «Type» → List Byte → Interp (Option Val)
  | .Bool, bytes =>
    if bytes.length ≠ 1 then specPanic "decode of Type::Bool with invalid length"
    else
      match bytes with
      | [.Init 0 _] => pure (some (.Bool false))
      | [.Init 1 _] => pure (some (.Bool true))
      | _ => pure none
  | .Int ⟨signed, size⟩, bytes =>
    if bytes.length ≠ size.bytes then specPanic "decode of Type::Int with invalid length"
    else
      match bytes.mapM AbstractByte.data with
      | some data => pure (some (.Int (Endianness.decode x86_64.ENDIANNESS signed data)))
      | none => pure none
  | .Array elem count, bytes => do
    let elemLayout ← Type.layout elem
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
    let fullSize ← Size.mulInt elemSize count
    if bytes.length ≠ fullSize.bytes then
      specPanic "decode of Type::Array with invalid length"
    else do
      let chunks ← (List.range count.toNat).mapM (fun i => do
        let byteOffset ← Size.mulInt elemSize (Int.ofNat i)
        subsliceWithLength bytes byteOffset.bytes elemSize.bytes)
      let decoded ← chunks.mapM (fun elemBytes => Type.decode elem elemBytes)
      pure ((decoded.mapM id).map Value.Tuple)
  | _, _ => unsupported "Type::decode for a non-Int, non-Bool, non-Array type"

/-- `Type::encode` for `Bool`, `Int`, and `Array`:
> "fn encode<M: Memory>(Type::Bool: Self, val: Value<M>) -> .. {
>     let Value::Bool(b) = val else { panic!() };
>     list![AbstractByte::Init(if b { 1 } else { 0 }, None)]
> }
> ..
> fn encode<M: Memory>(Type::Int(IntType { signed, size }): Self, val: Value<M>) -> .. {
>     let Value::Int(i) = val else { panic!() };
>     // `Endianness::encode` will do the integer's bound check.
>     let bytes_data = M::T::ENDIANNESS.encode(signed, size, i).unwrap();
>     bytes_data.map(|b| AbstractByte::Init(b, None))
> }
> ..
> fn encode<M: Memory>(Type::Array { elem, count }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
>     let Value::Tuple(values) = val else { panic!() };
>     assert_eq!(values.len(), count);
>     values.flat_map(|value| {
>         let bytes = elem.encode::<M>(value);
>         assert_eq!(bytes.len(), elem.layout::<M::T>().expect_size(\"WF ensures array element is sized\").bytes());
>         bytes
>     })
> }" -/
def Type.encode : «Type» → Val → Interp (List Byte)
  | .Bool, .Bool b => pure [.Init (if b then 1 else 0) none]
  | .Bool, _ => specPanic "encode: Type::Bool with a non-Bool value"
  | .Int ⟨signed, size⟩, .Int i =>
    match Endianness.encode x86_64.ENDIANNESS signed size i with
    | some data => pure (data.map (fun b => .Init b none))
    | none => specPanic "Endianness::encode(..).unwrap()"
  | .Int _, _ => specPanic "encode: Type::Int with a non-Int value"
  | .Array elem count, .Tuple values => do
    let elemLayout ← Type.layout elem
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
    if (values.length : Int) ≠ count then
      specPanic "encode: Type::Array length mismatch"
    else do
      let encoded ← values.mapM (fun value => do
        let bytes ← Type.encode elem value
        if bytes.length ≠ elemSize.bytes then
          specPanic "encode: Type::Array element byte length mismatch"
        else
          pure bytes)
      pure encoded.flatten
  | .Array _ _, _ => specPanic "encode: Type::Array with a non-Tuple value"
  | _, _ => unsupported "Type::encode for a non-Int, non-Bool, non-Array type"

/-- `Machine::check_value` for `Int`, `Bool`, and `Array`:
> "(Value::Int(i), Type::Int(int_ty)) => {
>     ensure_else_ub(int_ty.can_represent(i), \"Value::Int: invalid integer value\")?;
> }
> (Value::Bool(_), Type::Bool) => {},
> ..
> (Value::Tuple(vals), Type::Array { elem, count }) => {
>     ensure_else_ub(vals.len() == count, \"Value::Tuple: invalid number of elements\")?;
>     for val in vals {
>         self.check_value(val, elem)?;
>     }
> }
> ..
> _ => panic!(\"Value: value does not match type\")" -/
def checkValue : Val → «Type» → Interp Unit
  | .Int i, .Int t =>
    if IntType.can_represent t i then pure () else ub "Value::Int: invalid integer value"
  | .Bool _, .Bool => pure ()
  | .Tuple vals, .Array elem count =>
    if (vals.length : Int) = count then
      vals.forM (fun val => checkValue val elem)
    else
      ub "Value::Tuple: invalid number of elements"
  | _, .Int _ => specPanic "Value: value does not match type"
  | _, .Bool => specPanic "Value: value does not match type"
  | _, .Array _ _ => specPanic "Value: value does not match type"
  | _, _ => unsupported "check_value for a non-Int, non-Bool, non-Array type"

/-! ## `BasicMemory` (`spec/mem/basic.md`) -/

/-- `Allocation::size`:
> "fn size(self) -> Size { Size::from_bytes(self.data.len()).unwrap() }" -/
def Allocation.size (a : Allocation) : Size := ⟨a.data.length⟩

/-- `BasicMemory::check_ptr`:
> "fn check_ptr(&self, ptr: ThinPointer<..>, len: Size) -> Result<Option<(AllocId, ProvExtra, Size)>> {
>     // For zero-sized accesses, there is nothing to check.
>     // (Provenance monotonicity says that if we allow zero-sized accesses
>     // for `None` provenance we have to allow it for all provenance.)
>     if len.is_zero() { return ret(None); }
>     // We do not even have to check for null, since no allocation will ever
>     // contain that address.
>     // Now try to access the allocation information.
>     let Some((id, prov_extra)) = ptr.provenance else {
>         // An invalid pointer.
>         throw_ub!(\"dereferencing pointer without provenance\");
>     };
>     let allocation = self.allocations[id.0];
>     if !allocation.live { throw_ub!(\"dereferencing pointer to dead allocation\"); }
>     // Compute relative offset, and ensure we are in-bounds.
>     let offset_in_alloc = ptr.addr - allocation.addr;
>     if offset_in_alloc < 0 || offset_in_alloc + len.bytes() > allocation.size().bytes() {
>         throw_ub!(\"dereferencing pointer outside the bounds of its allocation\");
>     }
>     // All is good!
>     ret(Some((id, prov_extra, Offset::from_bytes(offset_in_alloc).unwrap())))
> }" -/
def BM.check_ptr (mem : BM) (ptr : Ptr) (len : Size) : Interp (Option (AllocId × Unit × Size)) :=
  if len.bytes = 0 then pure none
  else
    match ptr.provenance with
    | none => ub "dereferencing pointer without provenance"
    | some (id, provExtra) => do
      let allocation ← listIndex mem.allocations id._0 "self.allocations[id.0]"
      if !allocation.live then ub "dereferencing pointer to dead allocation"
      else
        let offsetInAlloc : Int := ptr.addr - allocation.addr
        if offsetInAlloc < 0 ∨ offsetInAlloc + len.bytes > (Allocation.size allocation).bytes then
          ub "dereferencing pointer outside the bounds of its allocation"
        else pure (some (id, provExtra, ⟨offsetInAlloc.toNat⟩))

/-- `BasicMemory::store` (with the trivial `handle_extra` used by
`impl Memory for BasicMemory<T>`):
> "if !align.is_aligned(ptr.addr) { throw_ub!(\"store to a misaligned pointer\"); }
>  let size = Size::from_bytes(bytes.len()).unwrap();
>  let Some((id, prov_extra, offset)) = self.check_ptr(ptr, size)? else { return ret(()); };
>  let mut allocation = self.allocations[id.0];
>  handle_extra(&mut allocation.extra, prov_extra, offset)?;
>  allocation.data.write_subslice_at_index(offset.bytes(), bytes);
>  self.allocations.set(id.0, allocation);" -/
def BM.store (mem : BM) (ptr : Ptr) (bytes : List Byte) (align : Align) : Interp BM :=
  if !Align.is_aligned align ptr.addr then ub "store to a misaligned pointer"
  else do
    match ← BM.check_ptr mem ptr ⟨bytes.length⟩ with
    | none => pure mem
    | some (id, _, offset) => do
      let allocation ← listIndex mem.allocations id._0 "self.allocations[id.0]"
      let data ← writeSubsliceAtIndex allocation.data offset.bytes bytes
      let allocations ← listSet mem.allocations id._0 { allocation with data := data } "set"
      pure { mem with allocations := allocations }

/-- `BasicMemory::load` (with the trivial `handle_extra`):
> "if !align.is_aligned(ptr.addr) { throw_ub!(\"load from a misaligned pointer\"); }
>  let Some((id, prov_extra, offset)) = self.check_ptr(ptr, len)? else { return ret(list![]); };
>  let mut allocation = self.allocations[id.0];
>  handle_extra(&mut allocation.extra, prov_extra, offset)?;
>  self.allocations.set(id.0, allocation);
>  ret(allocation.data.subslice_with_length(offset.bytes(), len.bytes()))" -/
def BM.load (mem : BM) (ptr : Ptr) (len : Size) (align : Align) : Interp (List Byte × BM) :=
  if !Align.is_aligned align ptr.addr then ub "load from a misaligned pointer"
  else do
    match ← BM.check_ptr mem ptr len with
    | none => pure ([], mem)
    | some (id, _, offset) => do
      let allocation ← listIndex mem.allocations id._0 "self.allocations[id.0]"
      let allocations ← listSet mem.allocations id._0 allocation "set"
      let bytes ← subsliceWithLength allocation.data offset.bytes len.bytes
      pure (bytes, { mem with allocations := allocations })

/-- `BasicMemory::deallocate` (with the trivial `handle_extra`):
> "let Some((id, prov_extra)) = ptr.provenance else { throw_ub!(\"deallocating invalid pointer\") };
>  let mut allocation = self.allocations[id.0];
>  if !allocation.live { throw_ub!(\"double-free\"); }
>  if ptr.addr != allocation.addr { throw_ub!(..); }
>  if kind != allocation.kind { throw_ub!(..); }
>  if size != allocation.size() { throw_ub!(..); }
>  if align != allocation.align { throw_ub!(..); }
>  handle_extra(&mut allocation.extra, prov_extra)?;
>  allocation.live = false;
>  self.allocations.set(id.0, allocation);" -/
def BM.deallocate (mem : BM) (ptr : Ptr) (kind : AllocationKind) (size : Size) (align : Align) :
    Interp BM :=
  match ptr.provenance with
  | none => ub "deallocating invalid pointer"
  | some (id, _) => do
    let allocation ← listIndex mem.allocations id._0 "self.allocations[id.0]"
    if !allocation.live then ub "double-free"
    else if ptr.addr ≠ allocation.addr then
      ub "deallocating with pointer not to the beginning of its allocation"
    else if kind ≠ allocation.kind then ub "deallocating with the wrong deallocation operation"
    else if size ≠ Allocation.size allocation then ub "deallocating with incorrect size information"
    else if align ≠ allocation.align then ub "deallocating with incorrect alignment information"
    else do
      let allocations ← listSet mem.allocations id._0 { allocation with live := false } "set"
      pure { mem with allocations := allocations }

/-- `BasicMemory::dereferenceable`:
> "fn dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Size) -> Result {
>     self.check_ptr(ptr, len)?;
>     ret(())
> }" -/
def BM.dereferenceable (mem : BM) (ptr : Ptr) (len : Size) : Interp Unit := do
  let _ ← BM.check_ptr mem ptr len
  pure ()

/-- `Memory::signed_dereferenceable` (`spec/mem/interface.md`):
> "fn signed_dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Int) -> Result {
>     if len > 0 {
>         self.dereferenceable(ptr, Size::from_bytes(len).unwrap())
>     } else {
>         let begin_ptr = ThinPointer { addr: ptr.addr + len, ..ptr };
>         self.dereferenceable(begin_ptr, Size::from_bytes(-len).unwrap())
>     }
> }" -/
def BM.signed_dereferenceable (mem : BM) (ptr : Ptr) (len : Int) : Interp Unit :=
  if len > 0 then
    match Size.from_bytes len with
    | some sz => BM.dereferenceable mem ptr sz
    | none => specPanic "Size::from_bytes(len).unwrap()"
  else
    let beginPtr : Ptr := { ptr with addr := ptr.addr + len }
    match Size.from_bytes (-len) with
    | some sz => BM.dereferenceable mem beginPtr sz
    | none => specPanic "Size::from_bytes(-len).unwrap()"

/-! ## `ConcurrentMemory` (`spec/mem/concurrent.md`) -/

/-- `ConcurrentMemory::store`:
> "let access = Access { ty: AccessType::Store, atomicity, addr: ptr.addr,
>                        len: Size::from_bytes(bytes.len()).unwrap(), };
>  self.accesses.push(access);
>  self.memory.store(ptr, bytes, align)" -/
def CM.store (cm : ConcurrentMemory BM) (ptr : Ptr) (bytes : List Byte) (align : Align)
    (atomicity : Atomicity) : Interp (ConcurrentMemory BM) := do
  let access : Access := ⟨.Store, atomicity, ptr.addr, ⟨bytes.length⟩⟩
  let memory ← BM.store cm.memory ptr bytes align
  pure { memory := memory, accesses := cm.accesses ++ [access] }

/-- `ConcurrentMemory::load`:
> "let access = Access { ty: AccessType::Load, atomicity, addr: ptr.addr, len, };
>  self.accesses.push(access);
>  self.memory.load(ptr, len, align)" -/
def CM.load (cm : ConcurrentMemory BM) (ptr : Ptr) (len : Size) (align : Align)
    (atomicity : Atomicity) : Interp (List Byte × ConcurrentMemory BM) := do
  let access : Access := ⟨.Load, atomicity, ptr.addr, len⟩
  let (bytes, memory) ← BM.load cm.memory ptr len align
  pure (bytes, { memory := memory, accesses := cm.accesses ++ [access] })

/-- `ConcurrentMemory::deallocate`:
> "pub fn deallocate(&mut self, ptr: ThinPointer<M::Provenance>, kind: AllocationKind, size: Size, align: Align) -> Result {
>     self.memory.deallocate(ptr, kind, size, align)
> }" -/
def CM.deallocate (cm : ConcurrentMemory BM) (ptr : Ptr) (kind : AllocationKind) (size : Size)
    (align : Align) : Interp (ConcurrentMemory BM) := do
  pure { cm with memory := ← BM.deallocate cm.memory ptr kind size align }

/-- `ConcurrentMemory::dereferenceable`:
> "pub fn dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Size) -> Result {
>     self.memory.dereferenceable(ptr, len)
> }" -/
def CM.dereferenceable (cm : ConcurrentMemory BM) (ptr : Ptr) (len : Size) : Interp Unit :=
  BM.dereferenceable cm.memory ptr len

/-- `ConcurrentMemory::signed_dereferenceable`:
> "pub fn signed_dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Int) -> Result {
>     self.memory.signed_dereferenceable(ptr, len)
> }" -/
def CM.signed_dereferenceable (cm : ConcurrentMemory BM) (ptr : Ptr) (len : Int) :
    Interp Unit :=
  BM.signed_dereferenceable cm.memory ptr len

/-- `Access::races`:
> "if self.ty == AccessType::Load && other.ty == AccessType::Load { return false; }
>  if self.atomicity == Atomicity::Atomic && other.atomicity == Atomicity::Atomic { return false; }
>  let end_addr = self.addr + self.len.bytes();
>  let other_end_addr = other.addr + other.len.bytes();
>  end_addr > other.addr && other_end_addr > self.addr" -/
def Access.races (a b : Access) : Bool :=
  if a.ty = .Load ∧ b.ty = .Load then false
  else if a.atomicity = .Atomic ∧ b.atomicity = .Atomic then false
  else decide (a.addr + a.len.bytes > b.addr) && decide (b.addr + b.len.bytes > a.addr)

/-- `ConcurrentMemory::check_data_races`:
> "if prev_sync_threads.contains(current_thread) { return Ok(()) }
>  for access in self.accesses {
>      if prev_accesses.any(|prev_access| access.races(prev_access)) { throw_ub!(\"Data race\"); }
>  }
>  Ok(())" -/
def CM.check_data_races (cm : ConcurrentMemory BM) (current : ThreadId)
    (prev : Set ThreadId × List Access) : Interp Unit :=
  if setContains prev.1 current then pure ()
  else if cm.accesses.any (fun a => prev.2.any (fun p => Access.races a p)) then ub "Data race"
  else pure ()

/-! ## Machine helpers (`spec/lang/machine.md`) -/

/-- `Machine::reset_data_race_tracking` (`spec/lang/machine.md`):
> "let mut prev_sync = self.synchronized_threads;
>  // Every thread is always synchronized with itself.
>  prev_sync.insert(self.active_thread);
>  // Reset access tracking list.
>  let prev_accesses = self.mem.reset_accesses();
>  (prev_sync, prev_accesses)"
with `ConcurrentMemory::reset_accesses` (`spec/mem/concurrent.md`):
> "let prev_accesses = self.accesses;
>  self.accesses = list![];
>  prev_accesses" -/
def resetDataRaceTracking (m : Mach) : (Set ThreadId × List Access) × Mach :=
  ((setInsert m.synchronized_threads m.active_thread, m.mem.accesses),
   { m with mem := { m.mem with accesses := [] } })

/-- The daemonic choice in `Machine::step`:
> "self.active_thread = pick(distr, |id: ThreadId| {
>      let Some(thread) = self.threads.get(id) else { return false; };
>      thread.state == ThreadState::Enabled
>  })?;"
The program must behave correctly for *every* `id` satisfying the predicate.
When exactly one thread is enabled that set is a singleton and the choice is
deterministic; otherwise we do not resolve the choice. -/
def pickActiveThread (m : Mach) : Interp ThreadId :=
  match (List.range m.threads.length).filter
      (fun i => match m.threads[i]? with
        | some t => decide (t.state = .Enabled)
        | none => false) with
  | [i] => pure (Int.ofNat i)
  | [] => unsupported "pick with no valid choice (no behavior)"
  | _ => unsupported "daemonic choice among several enabled threads"

/-- `Machine::active_thread`:
> "fn active_thread(&self) -> Thread<M> {
>     self.threads[self.active_thread]
> }" -/
def activeThread (m : Mach) : Interp (Thread BM) :=
  listIndex m.threads m.active_thread "self.threads[self.active_thread]"

/-- `Machine::cur_frame` and `Thread::cur_frame`:
> "fn cur_frame(&self) -> StackFrame<M> {
>     self.active_thread().cur_frame()
> }
> ..
> fn cur_frame(&self) -> StackFrame<M> {
>     self.stack.last().unwrap()
> }" -/
def curFrame (m : Mach) : Interp Frame := do
  let t ← activeThread m
  match t.stack.getLast? with
  | some f => pure f
  | none => specPanic "self.stack.last().unwrap()"

/-- `Machine::try_mutate_cur_frame` / `Thread::try_mutate_cur_frame` for a
frame update `f` that cannot fail:
> "if self.stack.is_empty() { panic!(..); }
>  let last_idx = self.stack.len() - 1;
>  self.stack.try_mutate_at(last_idx, f)" -/
def mutateCurFrame (m : Mach) (f : Frame → Frame) : Interp Mach := do
  let t ← activeThread m
  match t.stack.getLast? with
  | none => specPanic "`try_mutate_cur_frame` called on empty stack!"
  | some fr => do
    let t' : Thread BM := { t with stack := t.stack.dropLast ++ [f fr] }
    let threads ← listSet m.threads m.active_thread t' "mutate_at"
    pure { m with threads := threads }

/-- `StackFrame::jump_to_block` (`spec/lang/machine.md`):
> "self.next_block = b; self.next_stmt = Int::ZERO;"
and `Machine::jump_to_block` (`spec/lang/step/terminators.md`):
> "self.try_mutate_cur_frame(|frame, _mem| { frame.jump_to_block(block); ret(()) })" -/
def jumpToBlock (m : Mach) (b : BbName) : Interp Mach :=
  mutateCurFrame m (fun fr => { fr with next_block := b, next_stmt := 0 })

/-! ## Typed memory access (`spec/lang/representation.md`) -/

/-- `Machine::typed_load`:
> "let bytes = self.mem.load(ptr, ty.layout::<M::T>().expect_size(..), align, atomicity)?;
>  ret(match ty.decode::<M>(bytes) {
>      Some(val) => { self.check_value(val, ty)?; val }
>      None => throw_ub!(\"load at type {ty:?} but the data in memory violates the language invariant\"),
>  })" -/
def typedLoad (m : Mach) (ptr : Ptr) (ty : «Type») (align : Align) (atomicity : Atomicity) :
    Interp (Val × Mach) := do
  let size ← LayoutStrategy.expect_size (← Type.layout ty) "the callers ensure `ty` is sized"
  let (bytes, cm) ← CM.load m.mem ptr size align atomicity
  let m := { m with mem := cm }
  match ← Type.decode ty bytes with
  | some val => do checkValue val ty; pure (val, m)
  | none => ub "load at type but the data in memory violates the language invariant"

/-- `Machine::typed_store`:
> "assert!(self.check_value(val, ty).is_ok(), ..);
>  let bytes = ty.encode::<M>(val);
>  self.mem.store(ptr, bytes, align, atomicity)?;" -/
def typedStore (m : Mach) (ptr : Ptr) (val : Val) (ty : «Type») (align : Align)
    (atomicity : Atomicity) : Interp Mach := do
  match checkValue val ty with
  | .ok () => pure ()
  | .error _ => specPanic "trying to store a value which is ill-formed for its type"
  let bytes ← Type.encode ty val
  let cm ← CM.store m.mem ptr bytes align atomicity
  pure { m with mem := cm }

/-! ## Places and values (`spec/lang/step/expressions.md`) -/

/-- `Machine::place_load`:
> "if !place.aligned { throw_ub!(\"loading from a place based on a misaligned pointer\"); }
>  ret(self.typed_load(place.ptr.thin_pointer, ty, Align::ONE, Atomicity::None)?)" -/
def placeLoad (m : Mach) (place : Place BM) (ty : «Type») : Interp (Val × Mach) :=
  if !place.aligned then ub "loading from a place based on a misaligned pointer"
  else typedLoad m place.ptr.thin_pointer ty ⟨1⟩ .None

/-- `Machine::place_store` (`spec/lang/step/statements.md`):
> "if !place.aligned { throw_ub!(\"storing to a place based on a misaligned pointer\"); }
>  self.typed_store(place.ptr.thin_pointer, val, ty, Align::ONE, Atomicity::None)?;" -/
def placeStore (m : Mach) (place : Place BM) (val : Val) (ty : «Type») : Interp Mach :=
  if !place.aligned then ub "storing to a place based on a misaligned pointer"
  else typedStore m place.ptr.thin_pointer val ty ⟨1⟩ .None

/-- `Machine::eval_constant` for the constants without provenance:
> "Constant::Int(i) => Value::Int(i),
>  Constant::Bool(b) => Value::Bool(b)," -/
def evalConstant : Constant → Interp Val
  | .Int i => pure (.Int i)
  | .Bool b => pure (.Bool b)
  | _ => unsupported "eval_constant for a pointer constant"

/-! ## Operators (`spec/lang/step/operators.md`) -/

/-- Bit-extraction loop of `Machine::eval_count_ones` for `n` remaining bit
positions (`spec/lang/step/operators.md`). -/
def countOnesLoop : Nat → Int → Int → Int
  | 0, ones, _ => ones
  | n + 1, ones, remainingBits =>
    countOnesLoop n (ones + intBitAnd remainingBits 1) (remainingBits / 2)

/-- `Machine::eval_count_ones` (`spec/lang/step/operators.md`):
> "fn eval_count_ones(operand: Int, int_ty: IntType) -> Int {
>     let mut ones = Int::ZERO;
>     let mut remaining_bits = operand;
>     // Iterate once per bit in the bit width, afterwards the remaining bits are leading bits only.
>     for _ in Int::ZERO..int_ty.size.bits() {
>         // Extract the least significant bit and update `remaining_bits` to remove that bit.
>         ones += remaining_bits & Int::ONE;
>         remaining_bits >>= 1;
>     }
>     ones
> }" -/
def evalCountOnes (operand : Int) (intTy : IntType) : Int :=
  countOnesLoop (Size.bits intTy.size) 0 operand

/-- `Machine::eval_int_un_op` (`spec/lang/step/operators.md`):
> "fn eval_int_un_op(op: IntUnOp, operand: Int, operand_ty: IntType) -> Result<Int> {
>     use IntUnOp::*;
>     ret(match op {
>         // Put the result into the right range (in case of overflow).
>         Neg => operand_ty.bring_in_bounds(-operand),
>         // Put the result into the right range (in case of a unsigned numbers, which `!`
>         // makes negative by inverting all the leading zeros).
>         BitNot => operand_ty.bring_in_bounds(!operand),
>         // This can never overflow, as the total number of bits is below `u32::MAX`.
>         CountOnes => Self::eval_count_ones(operand, operand_ty),
>     })
> }"
On mathematical integers (`libspecr::Int` / `num_bigint::BigInt`), two's-complement
bitwise complement `!x` is `-x - 1`. -/
def evalIntUnOp (op : IntUnOp) (operand : Int) (operandTy : IntType) : Interp Int :=
  match op with
  | .Neg => pure (IntType.bring_in_bounds operandTy (-operand))
  | .BitNot => pure (IntType.bring_in_bounds operandTy (-operand - 1))
  | .CountOnes => pure (evalCountOnes operand operandTy)

/-- `Machine::eval_cast_op` for `CastOp::IntToInt` (`spec/lang/step/operators.md`):
> "fn eval_cast_op(&self, cast_op: CastOp, (operand, old_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
>     use CastOp::*;
>     match cast_op {
>         IntToInt(int_ty) => {
>             let Value::Int(operand) = operand else { panic!(\"non-integer input to int-to-int cast\") };
>             let result = int_ty.bring_in_bounds(operand);
>             ret((Value::Int(result), Type::Int(int_ty)))
>         }
>         ..
>     }
> }" -/
def evalCastOp (castOp : CastOp) (arg : Val × «Type») : Interp (Val × «Type») :=
  match castOp, arg with
  | .IntToInt intTy, (.Int operand, _) =>
    pure (.Int (IntType.bring_in_bounds intTy operand), .Int intTy)
  | .IntToInt _, _ => specPanic "non-integer input to int-to-int cast"
  | .Transmute _, _ => unsupported "eval_cast_op for CastOp::Transmute"

/-- `Machine::eval_un_op` for `UnOp::Int` and `UnOp::Cast` (`spec/lang/step/operators.md`):
> "fn eval_un_op(&self, UnOp::Int(op): UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
>     let Type::Int(int_ty) = op_ty else { panic!(\"non-integer input to integer operation\") };
>     let Value::Int(operand) = operand else { panic!(\"non-integer input to integer operation\") };
>     let ret_ty = match op {
>         IntUnOp::CountOnes => IntType { signed: Unsigned, size: Size::from_bytes(4).unwrap() },
>         _ => int_ty,
>     };
>     let result = Value::Int(Self::eval_int_un_op(op, operand, int_ty)?);
>     // Sanity-check that the result of `eval_int_un_op` is in-bounds.
>     self.check_value(result, Type::Int(ret_ty))
>         .expect(\"sanity check: result of UnOp::Int does not fit in the return type\");
>     ret((result, Type::Int(ret_ty)))
> }
> ..
> fn eval_un_op(&self, UnOp::Cast(cast_op): UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
>     ret(self.eval_cast_op(cast_op, (operand, op_ty))?)
> }" -/
def evalUnOp (op : UnOp) (arg : Val × «Type») : Interp (Val × «Type») :=
  match op, arg with
  | .Int op, (.Int operand, .Int intTy) => do
    let retTy := match op with
      | .CountOnes => ⟨.Unsigned, ⟨4⟩⟩
      | _ => intTy
    let result : Val := .Int (← evalIntUnOp op operand intTy)
    match checkValue result (.Int retTy) with
    | .ok () => pure (result, .Int retTy)
    | .error _ => specPanic "sanity check: result of UnOp::Int does not fit in the return type"
  | .Int _, _ => specPanic "non-integer input to integer operation"
  | .Cast castOp, arg => evalCastOp castOp arg
  | _, _ => unsupported "eval_un_op for an operator outside UnOp::Int and UnOp::Cast"

/-- `Machine::eval_int_bin_op` across all `IntBinOp` variants
(`spec/lang/step/operators.md`):
> "Add => left + right,
>  AddUnchecked => {
>      let result = left + right;
>      if !left_ty.can_represent(result) {
>          throw_ub!(\"overflow in unchecked add\");
>      }
>      result
>  }
>  Sub => left - right,
>  SubUnchecked => {
>      let result = left - right;
>      if !left_ty.can_represent(result) {
>          throw_ub!(\"overflow in unchecked sub\");
>      }
>      result
>  }
>  Mul => left * right,
>  MulUnchecked => {
>      let result = left * right;
>      if !left_ty.can_represent(result) {
>          throw_ub!(\"overflow in unchecked mul\");
>      }
>      result
>  }
>  Div => {
>      if right == 0 {
>          throw_ub!(\"division by zero\");
>      }
>      let result = left / right;
>      if !left_ty.can_represent(result) { // `int::MIN / -1` is UB
>          throw_ub!(\"overflow in division\");
>      }
>      result
>  }
>  DivExact => {
>      if right == 0 {
>          throw_ub!(\"division by zero\");
>      }
>      let result = left / right;
>      if !left_ty.can_represent(result) { // `int::MIN / -1` is UB
>          throw_ub!(\"overflow in division\");
>      }
>      if left % right != 0 {
>          throw_ub!(\"non-zero remainder in exact division\");
>      }
>      result
>  }
>  Rem => {
>      if right == 0 {
>          throw_ub!(\"modulus of remainder is zero\");
>      }
>      if !left_ty.can_represent(left / right) { // `int::MIN % -1` is UB
>          throw_ub!(\"overflow in remainder\");
>      }
>      left % right
>  }
>  Shl | Shr => {
>      let bits = left_ty.size.bits();
>      let offset = right.rem_euclid(bits);
>      match op {
>          Shl => left << offset,
>          Shr => left >> offset,
>          _ => panic!(),
>      }
>  }
>  ShlUnchecked | ShrUnchecked => {
>      let bits = left_ty.size.bits();
>      if right < 0 || right >= bits {
>          throw_ub!(\"overflow in unchecked shift\");
>      }
>      match op {
>          ShlUnchecked => left << right,
>          ShrUnchecked => left >> right,
>          _ => panic!(),
>      }
>  }
>  BitAnd => left & right,
>  BitOr => left | right,
>  BitXor => left ^ right,"
On `libspecr::Int` (`num_bigint::BigInt`), Rust's `/` and `%` round toward zero
(`Int.tdiv` and `Int.tmod`), Euclidean remainder `.rem_euclid(bits)` for
`bits > 0` is Lean's `right % bits` (`Int.emod`), two's-complement bit shifts
`left << k` and `left >> k` for `k ≥ 0` are `left * 2 ^ k` and Euclidean floor
division `left / 2 ^ k` (`Int.ediv`), and `&`, `|`, `^` are two's-complement
bitwise operations (`intBitAnd`, `intBitOr`, `intBitXor`). -/
def evalIntBinOp (op : IntBinOp) (left right : Int) (leftTy : IntType) : Interp Int :=
  match op with
  | .Add => pure (left + right)
  | .AddUnchecked =>
    let result := left + right
    if !IntType.can_represent leftTy result then ub "overflow in unchecked add"
    else pure result
  | .Sub => pure (left - right)
  | .SubUnchecked =>
    let result := left - right
    if !IntType.can_represent leftTy result then ub "overflow in unchecked sub"
    else pure result
  | .Mul => pure (left * right)
  | .MulUnchecked =>
    let result := left * right
    if !IntType.can_represent leftTy result then ub "overflow in unchecked mul"
    else pure result
  | .Div =>
    if right = 0 then ub "division by zero"
    else
      let result := Int.tdiv left right
      if !IntType.can_represent leftTy result then ub "overflow in division"
      else pure result
  | .DivExact =>
    if right = 0 then ub "division by zero"
    else
      let result := Int.tdiv left right
      if !IntType.can_represent leftTy result then ub "overflow in division"
      else if Int.tmod left right ≠ 0 then ub "non-zero remainder in exact division"
      else pure result
  | .Rem =>
    if right = 0 then ub "modulus of remainder is zero"
    else if !IntType.can_represent leftTy (Int.tdiv left right) then ub "overflow in remainder"
    else pure (Int.tmod left right)
  | .Shl =>
    let bits : Int := Size.bits leftTy.size
    let offset : Nat := (right % bits).toNat
    pure (left * (2 : Int) ^ offset)
  | .Shr =>
    let bits : Int := Size.bits leftTy.size
    let offset : Nat := (right % bits).toNat
    pure (left / (2 : Int) ^ offset)
  | .ShlUnchecked =>
    let bits : Int := Size.bits leftTy.size
    if right < 0 ∨ right ≥ bits then ub "overflow in unchecked shift"
    else pure (left * (2 : Int) ^ right.toNat)
  | .ShrUnchecked =>
    let bits : Int := Size.bits leftTy.size
    if right < 0 ∨ right ≥ bits then ub "overflow in unchecked shift"
    else pure (left / (2 : Int) ^ right.toNat)
  | .BitAnd => pure (intBitAnd left right)
  | .BitOr => pure (intBitOr left right)
  | .BitXor => pure (intBitXor left right)

/-- `Machine::eval_bin_op` for `BinOp::Int` (`spec/lang/step/operators.md`):
> "let Type::Int(int_ty) = l_ty else { panic!(\"non-integer input to integer operation\") };
>  let Value::Int(left) = left else { panic!(..) };
>  let Value::Int(right) = right else { panic!(..) };
>  // Perform the operation.
>  let result = Self::eval_int_bin_op(op, left, right, int_ty)?;
>  // Put the result into the right range (in case of overflow).
>  let result = int_ty.bring_in_bounds(result);
>  ret((Value::Int(result), Type::Int(int_ty)))" -/
def evalBinOp (op : BinOp) (l : Val × «Type») (r : Val × «Type») : Interp (Val × «Type») :=
  match op, l, r with
  | .Int op, (.Int left, .Int intTy), (.Int right, _) => do
    let result ← evalIntBinOp op left right intTy
    pure (.Int (IntType.bring_in_bounds intTy result), .Int intTy)
  | .Int _, _, _ => specPanic "non-integer input to integer operation"
  | _, _, _ => unsupported "eval_bin_op for a non-Int operator"

/-- `Machine::ptr_offset_inbounds` (`spec/lang/step/operators.md`):
> "fn ptr_offset_inbounds(&self, ptr: ThinPointer<M::Provenance>, offset: Int) -> Result<ThinPointer<M::Provenance>> {
>     // Ensure dereferenceability.
>     self.mem.signed_dereferenceable(ptr, offset)?;
>     // This also ensures that `offset` fits in an `isize`, since no allocation
>     // can be bigger than `isize`, and it ensures that the arithmetic does not overflow, since no
>     // allocation wraps around the edge of the address space.
>     assert!(offset.in_bounds(Signed, M::T::PTR_SIZE));
>     assert!((ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE));
>     // All checked!
>     ret(ThinPointer { addr: ptr.addr + offset, ..ptr })
> }" -/
def ptrOffsetInbounds (m : Mach) (ptr : Ptr) (offset : Int) : Interp Ptr := do
  CM.signed_dereferenceable m.mem ptr offset
  if !(inBounds offset .Signed x86_64.PTR_SIZE &&
       inBounds (ptr.addr + offset) .Unsigned x86_64.PTR_SIZE) then
    specPanic "ptr_offset_inbounds arithmetic overflow"
  else
    pure { ptr with addr := ptr.addr + offset }

/-! ## Place and value expressions (`spec/lang/step/expressions.md`) -/

mutual

/-- `Machine::eval_place` for `PlaceExpr::Local` and `PlaceExpr::Index`:
> "let ty = self.cur_frame().func.locals[name];
>  let Some(ptr) = self.cur_frame().locals.get(name) else {
>      throw_ub!(\"access to a dead local\");
>  };
>  ret((Place { ptr: ptr.widen(None), aligned: true }, ty))
>  ..
>  fn eval_place(&mut self, PlaceExpr::Index { root, index }: PlaceExpr) -> Result<(Place<M>, Type)> {
>      let (root, ty) = self.eval_place(root)?;
>      let (Value::Int(index), _) = self.eval_value(index)? else {
>          panic!(\"non-integer operand for array index\")
>      };
>      let (elem_ty, count) = match ty {
>          Type::Array { elem, count } => (elem, count),
>          ..
>          _ => panic!(\"index projection on non-indexable type\"),
>      };
>      if index < 0 || index >= count {
>          throw_ub!(\"access to out-of-bounds index\");
>      }
>
>      let elem_size = elem_ty.layout::<M::T>().expect_size(\"WF ensures array & slice elements are sized\");
>      let offset = index * elem_size;
>      assert!(
>          offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata),
>          \"sanity check: the indexed offset should not be outside what the type allows.\"
>      );
>
>      let ptr = self.ptr_offset_inbounds(root.ptr.thin_pointer, offset.bytes())?;
>      ret((Place { ptr: ptr.widen(None), ..root }, elem_ty))
>  }" -/
def evalPlace (m : Mach) : PlaceExpr → Interp ((Place BM × «Type») × Mach)
  | .Local name => do
    let fr ← curFrame m
    let ty ← mapIndex fr.func.locals name "self.cur_frame().func.locals[name]"
    match mapGet fr.locals name with
    | none => ub "access to a dead local"
    | some ptr => pure (({ ptr := { thin_pointer := ptr, metadata := none }, aligned := true }, ty), m)
  | .Index root index => do
    let ((rootPlace, ty), m) ← evalPlace m root
    let ((idxVal, _), m) ← evalValue m index
    let idx ← match idxVal with
      | .Int i => pure i
      | _ => specPanic "non-integer operand for array index"
    let (elemTy, count) ← match ty with
      | .Array elem count => pure (elem, count)
      | .Slice _ => unsupported "eval_place for PlaceExpr::Index on Type::Slice"
      | _ => specPanic "index projection on non-indexable type"
    if idx < 0 ∨ idx ≥ count then
      ub "access to out-of-bounds index"
    else do
      let elemLayout ← Type.layout elemTy
      let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
      let offset ← Size.mulInt elemSize idx
      let size ← computeSize (← Type.layout ty) rootPlace.ptr.metadata
      if offset.bytes ≤ size.bytes then
        let ptr ← ptrOffsetInbounds m rootPlace.ptr.thin_pointer offset.bytes
        pure (({ rootPlace with ptr := { thin_pointer := ptr, metadata := none } }, elemTy), m)
      else
        specPanic "sanity check: the indexed offset should not be outside what the type allows."
  | _ => unsupported "eval_place for a non-Local, non-Index place expression"

/-- Left-to-right element evaluation `exprs.try_map(|e| self.eval_value(e))?.map(|e| e.0)`
in `Machine::eval_value` for `ValueExpr::Tuple` (`spec/lang/step/expressions.md`):
> "let vals = exprs.try_map(|e| self.eval_value(e))?.map(|e| e.0);" -/
def evalValueList (m : Mach) : List ValueExpr → Interp (List Val × Mach)
  | [] => pure ([], m)
  | e :: es => do
    let ((v, _), m) ← evalValue m e
    let (vs, m) ← evalValueList m es
    pure (v :: vs, m)

/-- `Machine::eval_value` for `Constant`, `Tuple`, `Load`, `UnOp`, and `BinOp`:
> "fn eval_value(&mut self, ValueExpr::Constant(constant, ty): ValueExpr) -> .. {
>     ret((self.eval_constant(constant)?, ty))
> }
> ..
> fn eval_value(&mut self, ValueExpr::Tuple(exprs, ty): ValueExpr) -> Result<(Value<M>, Type)> {
>     let vals = exprs.try_map(|e| self.eval_value(e))?.map(|e| e.0);
>     ret((Value::Tuple(vals), ty))
> }
> ..
> fn eval_value(&mut self, ValueExpr::Load { source }: ValueExpr) -> .. {
>     let (place, ty) = self.eval_place(source)?;
>     // WF ensures all load expressions are sized.
>     let v = self.place_load(place, ty)?;
>     ret((v, ty))
> }
> ..
> fn eval_value(&mut self, ValueExpr::UnOp { operator, operand }: ValueExpr) -> .. {
>     ..
>     let operand = self.eval_value(operand)?;
>     ret(self.eval_un_op(operator, operand)?)
> }
> fn eval_value(&mut self, ValueExpr::BinOp { operator, left, right }: ValueExpr) -> .. {
>     ..
>     let left = self.eval_value(left)?;
>     let right = self.eval_value(right)?;
>     ret(self.eval_bin_op(operator, left, right)?)
> }" -/
def evalValue (m : Mach) : ValueExpr → Interp ((Val × «Type») × Mach)
  | .Constant c ty => do pure ((← evalConstant c, ty), m)
  | .Tuple exprs ty => do
    let (vals, m) ← evalValueList m exprs
    pure ((.Tuple vals, ty), m)
  | .Load source => do
    let ((place, ty), m) ← evalPlace m source
    let (v, m) ← placeLoad m place ty
    pure ((v, ty), m)
  | .UnOp operator operand => do
    let (arg, m) ← evalValue m operand
    pure (← evalUnOp operator arg, m)
  | .BinOp operator left right => do
    let (l, m) ← evalValue m left
    let (r, m) ← evalValue m right
    pure (← evalBinOp operator l r, m)
  | _ => unsupported "eval_value for an expression outside the fragment"

end

/-! ## Statements (`spec/lang/step/statements.md`) -/

/-- `Machine::eval_statement` for `Statement::Assign` and `Statement::PlaceMention`:
> "fn eval_statement(&mut self, Statement::Assign { destination, source }: Statement) -> NdResult {
>     let (place, ty) = self.eval_place(destination)?;
>     let (val, _) = self.eval_value(source)?;
>     self.place_store(place, val, ty)?;
>     ret(())
> }
> ..
> fn eval_statement(&mut self, Statement::PlaceMention(place): Statement) -> NdResult {
>     self.eval_place(place)?;
>     ret(())
> }" -/
def evalStatement (m : Mach) : Statement → Interp Mach
  | .Assign destination source => do
    let ((place, ty), m) ← evalPlace m destination
    let ((val, _), m) ← evalValue m source
    placeStore m place val ty
  | .PlaceMention place => do
    let (_, m) ← evalPlace m place
    pure m
  | _ => unsupported "eval_statement for a statement other than Assign/PlaceMention"

/-! ## Terminators (`spec/lang/step/terminators.md`) -/

/-- `StackFrame::storage_dead` (`spec/lang/step/statements.md`):
> "let pointee_size = self.func.locals[local].layout::<M::T>().expect_size(..);
>  let pointee_align = self.func.locals[local].layout::<M::T>().expect_align(..);
>  if let Some(ptr) = self.locals.remove(local) {
>      mem.deallocate(ptr, AllocationKind::Stack, pointee_size, pointee_align)?;
>  }
>  ret(())" -/
def storageDead (fr : Frame) (cm : ConcurrentMemory BM) (local_ : LocalName) :
    Interp (Frame × ConcurrentMemory BM) := do
  let ty ← mapIndex fr.func.locals local_ "self.func.locals[local]"
  let layout ← Type.layout ty
  let size ← LayoutStrategy.expect_size layout "WF ensures all locals are sized"
  let align ← LayoutStrategy.expect_align layout "WF ensures all locals are sized"
  let (removed, locals) := mapRemove fr.locals local_
  let fr := { fr with locals := locals }
  match removed with
  | some ptr => do pure (fr, ← CM.deallocate cm ptr .Stack size align)
  | none => pure (fr, cm)

/-- The teardown loop of `Terminator::Return`:
> "while let Some(local) = frame.locals.keys().next() {
>      frame.storage_dead(&mut self.mem, local)?;
>  }"
`keys().next()` takes the first key of the association list; each iteration
removes that key, so `fuel = entries.length` iterations always suffice. -/
def deallocAll : Nat → Frame → ConcurrentMemory BM → Interp (Frame × ConcurrentMemory BM)
  | fuel, fr, cm =>
    match fr.locals.entries with
    | [] => pure (fr, cm)
    | (local_, _) :: _ =>
      match fuel with
      | 0 => specPanic "teardown loop did not terminate"
      | fuel + 1 => do
        let (fr, cm) ← storageDead fr cm local_
        deallocAll fuel fr cm

/-- `Machine::terminate_active_thread`:
> "let active = self.active_thread;
>  // The main thread may not terminate, it must call the `Exit` intrinsic.
>  if active == 0 { throw_ub!(\"the start function must not return\"); }
>  self.threads.mutate_at(active, |thread| {
>      assert!(thread.stack.len() == 0);
>      thread.state = ThreadState::Terminated;
>  });
>  for i in ThreadId::ZERO..self.threads.len() {
>      if self.threads[i].state == ThreadState::BlockedOnJoin(active) {
>          self.synchronized_threads.insert(i);
>          self.threads.mutate_at(i, |thread| thread.state = ThreadState::Enabled)
>      }
>  }" -/
def terminateActiveThread (m : Mach) : Interp Mach := do
  let active := m.active_thread
  if active = 0 then ub "the start function must not return"
  else do
    let t ← activeThread m
    if t.stack.length ≠ 0 then specPanic "assertion failed: thread.stack.len() == 0"
    else do
      let threads ← listSet m.threads active { t with state := .Terminated } "mutate_at"
      let woken := (List.range threads.length).filter
        (fun i => match threads[i]? with
          | some th => decide (th.state = .BlockedOnJoin active)
          | none => false)
      let threads := threads.zipIdx.map (fun (th, i) =>
        if woken.contains i then { th with state := .Enabled } else th)
      let sync := woken.foldl (fun s i => setInsert s (Int.ofNat i)) m.synchronized_threads
      pure { m with threads := threads, synchronized_threads := sync }

/-- `Machine::eval_terminator` for `Terminator::Return`
(`spec/lang/step/terminators.md`):
> "let mut frame = self.mutate_cur_stack(|stack| stack.pop().unwrap());
>  let callee_ty = frame.func.locals[frame.func.ret];
>  let align = callee_ty.layout::<M::T>().expect_align(..);
>  let ret_val = self.typed_load(frame.locals[frame.func.ret], callee_ty, align, Atomicity::None)?;
>  // Deallocate everything.
>  while let Some(local) = frame.locals.keys().next() { frame.storage_dead(&mut self.mem, local)?; }
>  // Inform the memory model that this call has ended.
>  self.mem.end_call(frame.extra)?;
>  // Perform the stack pop action.
>  match frame.stack_pop_action {
>      StackPopAction::BottomOfStack => { self.terminate_active_thread()?; }
>      StackPopAction::BackToCaller { ret_val_ptr: caller_ret_ptr, next_block, .. } => {
>          assert!(self.active_thread().stack.len() > 0);
>          self.typed_store(caller_ret_ptr, ret_val, callee_ty, align, Atomicity::None,)?;
>          if let Some(next_block) = next_block { self.jump_to_block(next_block)?; }
>          else { throw_ub!(\"return from a function where caller did not specify next block\"); }
>      }
>  }
>  ret(())"
`end_call` is the default trait method (`ret(())`) for `BasicMemory`
(`spec/mem/interface.md`), so it is the identity here. -/
def evalReturn (m : Mach) : Interp Mach := do
  let t ← activeThread m
  let frame ← match t.stack.getLast? with
    | some f => pure f
    | none => specPanic "stack.pop().unwrap()"
  let threads ← listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop"
  let m := { m with threads := threads }
  let calleeTy ← mapIndex frame.func.locals frame.func.ret "frame.func.locals[frame.func.ret]"
  let align ← LayoutStrategy.expect_align (← Type.layout calleeTy) "the return value is a local and thus sized"
  let retPtr ← mapIndex frame.locals frame.func.ret "frame.locals[frame.func.ret]"
  let (retVal, m) ← typedLoad m retPtr calleeTy align .None
  let (frame, cm) ← deallocAll frame.locals.entries.length frame m.mem
  let m := { m with mem := cm }
  match frame.stack_pop_action with
  | .BottomOfStack => terminateActiveThread m
  | .BackToCaller nextBlock _ callerRetPtr => do
    let t ← activeThread m
    if t.stack.length = 0 then specPanic "assertion failed: self.active_thread().stack.len() > 0"
    else do
      let m ← typedStore m callerRetPtr retVal calleeTy align .None
      match nextBlock with
      | some nb => jumpToBlock m nb
      | none => ub "return from a function where caller did not specify next block"

/-- `Machine::eval_terminator` for `Goto`, `Switch`, `Unreachable`, and `Return`:
> "fn eval_terminator(&mut self, Terminator::Goto(block_name): Terminator) -> NdResult {
>     self.jump_to_block(block_name)?;
>     ret(())
> }
> ..
> fn eval_terminator(&mut self, Terminator::Switch { value, cases, fallback }: Terminator) -> NdResult {
>     let Value::Int(value) = self.eval_value(value)?.0 else { panic!(\"switch on a non-integer\"); };
>     let next = cases.get(value).unwrap_or(fallback);
>     self.jump_to_block(next)?;
>     ret(())
> }
> ..
> fn eval_terminator(&mut self, Terminator::Unreachable: Terminator) -> NdResult {
>     throw_ub!(\"reached unreachable code\");
> }" -/
def evalTerminator (m : Mach) : Terminator → Interp Mach
  | .Goto blockName => jumpToBlock m blockName
  | .Switch value cases fallback => do
    let ((v, _), m) ← evalValue m value
    match v with
    | .Int i => jumpToBlock m ((mapGet cases i).getD fallback)
    | _ => specPanic "switch on a non-integer"
  | .Unreachable => ub "reached unreachable code"
  | .Return => evalReturn m
  | _ => unsupported "eval_terminator for a terminator other than Goto/Switch/Unreachable/Return"

/-! ## The step function (`spec/lang/machine.md`) -/

/-- `Machine::step`:
> "if !self.threads.any(|thread| thread.state == ThreadState::Enabled) { throw_deadlock!(); }
>  // Reset the data race tracking *before* we change `active_thread`.
>  let prev_step_information = self.reset_data_race_tracking();
>  // Update current thread.
>  ..
>  self.active_thread = pick(distr, |id: ThreadId| { .. })?;
>  // Execute this step.
>  let frame = self.cur_frame();
>  let block = &frame.func.blocks[frame.next_block];
>  if frame.next_stmt == block.statements.len() {
>      // It is the terminator. Evaluating it will update `frame.next_block` and `frame.next_stmt`.
>      self.eval_terminator(block.terminator)?;
>  } else {
>      // Bump up PC, evaluate this statement.
>      let stmt = block.statements[frame.next_stmt];
>      self.eval_statement(stmt)?;
>      self.try_mutate_cur_frame(|frame, _mem| { frame.next_stmt += 1; ret(()) })?;
>  }
>  // Check for data races with the previous step.
>  self.mem.check_data_races(self.active_thread, prev_step_information)?;
>  ret(())" -/
def step (m : Mach) : Interp Mach := do
  if !(m.threads.any (fun t => decide (t.state = .Enabled))) then .error .deadlock
  else do
    let (prev, m) := resetDataRaceTracking m
    let tid ← pickActiveThread m
    let m := { m with active_thread := tid }
    let frame ← curFrame m
    let block ← mapIndex frame.func.blocks frame.next_block "frame.func.blocks[frame.next_block]"
    let m ← if frame.next_stmt = (block.statements.length : Int) then
        evalTerminator m block.terminator
      else do
        let stmt ← listIndex block.statements frame.next_stmt "block.statements[frame.next_stmt]"
        let m ← evalStatement m stmt
        mutateCurFrame m (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
    CM.check_data_races m.mem m.active_thread prev
    pure m

/-- Run `step` up to `n` times, stopping early at the first `Stop`. -/
def steps : Nat → Mach → Interp Mach
  | 0, m => pure m
  | n + 1, m => do steps n (← step m)

end MiniRustSpec.Interp
