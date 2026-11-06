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
* `Statement::Assign`, `Statement::PlaceMention`, `Statement::Deinit`
  (through `ConcurrentMemory::deinit`), `Statement::StorageLive`, and
  `Statement::StorageDead` (through `Machine::try_mutate_cur_frame`,
  `StackFrame::storage_live`, and `StackFrame::storage_dead`)
  (`spec/lang/step/statements.md`, `spec/lang/machine.md`).
* `PlaceExpr::Local`, `PlaceExpr::Field`, and `PlaceExpr::Deref`
  (`spec/lang/step/expressions.md`), including `Machine::ptr_offset_inbounds`
  (`spec/lang/step/operators.md`), `ThinPointer::wrapping_offset`,
  `ThinPointer::widen`, and `PtrType::safe_pointee` (`spec/mem/pointer.md`),
  `Memory::dereferenceable` and `Memory::signed_dereferenceable`
  (`spec/mem/basic.md`, `spec/mem/concurrent.md`, `spec/mem/interface.md`), and
  `Machine::vtable_lookup`, `Machine::compute_size`, and
  `Machine::compute_align` (`spec/lang/machine.md`).
* `ValueExpr::Constant` (all `Constant` variants: `Int`, `Bool`,
  `GlobalPointer`, `FnPointer`, `VTablePointer`, and
  `PointerWithoutProvenance`), `ValueExpr::Tuple`, `ValueExpr::Load`,
  `ValueExpr::UnOp` with `UnOp::Int` (all `IntUnOp` variants: `Neg`, `BitNot`,
  `CountOnes`) and `UnOp::Cast` (both `CastOp` variants: `IntToInt` and
  `Transmute`, the latter through `Machine::transmute`, i.e. `encode` at the
  old type followed by `decode` and `check_value` at the new type), and
  `ValueExpr::BinOp` with `BinOp::Int` (all `IntBinOp` variants: `Add`,
  `AddUnchecked`, `Sub`, `SubUnchecked`, `Mul`, `MulUnchecked`, `Div`,
  `DivExact`, `Rem`, `Shl`, `Shr`, `ShlUnchecked`, `ShrUnchecked`, `BitAnd`,
  `BitOr`, `BitXor`), `BinOp::IntWithOverflow` (all `IntBinOpWithOverflow`
  variants: `Add`, `Sub`, `Mul`, returning `(Value::Int(result), Value::Bool(overflow))`
  at `IntType::with_overflow`), and `BinOp::Rel` (all `RelOp` variants: `Lt`,
  `Gt`, `Le`, `Ge`, `Eq`, `Ne`, `Cmp`) on integers and Booleans
  (`spec/lang/step/expressions.md`, `spec/lang/step/operators.md`). MiniRust
  has no Boolean negation operator: `minimize` expresses `!b` with transmutes
  and integer subtraction (see `MiniRustSpec.Correspondence.Translate`), so
  `UnOp::Int` on a `Value::Bool` stays a spec panic, exactly as upstream.
* `Terminator::Goto`, `Terminator::Switch`, `Terminator::Unreachable`,
  `Terminator::Call` (including `Machine::fn_from_ptr`,
  `check_abi_compatibility`, `Machine::prepare_for_inplace_passing`,
  `Machine::eval_argument` for both `ByValue` and `InPlace`,
  `Machine::create_frame`, `Machine::eval_call`, and
  `Machine::mutate_cur_stack`), `Terminator::Return`
  (`spec/lang/step/terminators.md`, `spec/lang/machine.md`), including frame
  teardown, `storage_dead` of every local, and both stack-pop actions
  (`BottomOfStack` and `BackToCaller`), and `Terminator::Intrinsic`
  (`spec/lang/step/terminators.md`) with `unit_value`, `unit_type`, and
  `Machine::eval_intrinsic` for `IntrinsicOp::{Abort, Assume, Exit,
  PrintStdout, PrintStderr, Allocate, Deallocate, PointerExposeProvenance,
  GetUnwindPayload}` (with `Machine::exit`, `Machine::eval_print`,
  `IntPtrCast::expose`, and `BasicMemory::leak_check`;
  `spec/lang/step/intrinsics.md`, `spec/mem/intptrcast.md`,
  `spec/mem/basic.md`). `RawEq` and `PointerWithExposedProvenance` check their
  arguments and return type and then report `unsupported` (`RawEq` compares
  `Type`s and reads through `Machine::load_raw_data`; `int2ptr` resolves an
  angelic `predict` choice), as do the thread, lock, and atomic intrinsics.
* The representation relation (`Type::{decode, encode}`) for `Type::Int`,
  `Type::Bool`, sized and unsized `Type::Tuple`, `Type::Union`
  (`Type.encodeUnionChunks`), `Type::Enum` (including `decode_discriminant`
  and `encode_discriminant`), `Type::Slice`, and `Type::TraitObject`, and
  `Machine::check_value` (with `ensure_else_ub` and `checkUnionChunks`) for
  those types (`spec/lang/representation.md`); `Type::layout` across all nine
  `Type` variants together with `LayoutStrategy::meta_kind` and
  `PtrType::{safe_pointee, meta_kind}` (`spec/lang/types.md`,
  `spec/mem/pointer.md`); and `BasicMemory`'s `allocate`, `load`, `store`,
  `deallocate`, and `check_ptr` (`spec/mem/basic.md`), wrapped by
  `ConcurrentMemory`'s access recording (`spec/mem/concurrent.md`). The
  recursion of these definitions over nested types, tuple fields, union
  chunks, enum variants, and discriminator trees is structural (Lean `mutual`
  blocks), so the kernel evaluates them.
* The `x86_64` target (`spec/prelude/target.md`) as the instance of `T` and
  `BasicMemory<x86_64>` as the instance of `M`.

Everything else returns `Stop.unsupported`, so the interpretation is partial
but never silently wrong.

## Effects

specr-lang functions return `Result`/`NdResult`. We use `Except Stop`:

* `Stop.ub` is `throw_ub!` (`TerminationInfo::Ub`),
* `Stop.abort` is `throw_abort!` (`TerminationInfo::Abort`),
* `Stop.deadlock` is `throw_deadlock!`,
* `Stop.specPanic` is a specr-lang `panic!`, failed `assert!`, `unwrap` of
  `None`, or out-of-range indexing. Upstream says such a panic "is a bug in the
  specification" (vendored `README.md`), so it signals an ill-formed input
  rather than program behavior,
* `Stop.unsupported` marks a construct outside the interpreted fragment,
* `Stop.machineStop` is `throw_machine_stop!` (`TerminationInfo::MachineStop`)
  and `Stop.memoryLeak` is `throw_memory_leak!` (`TerminationInfo::MemoryLeak`),
  the two outcomes of the `Exit` intrinsic.

Two non-deterministic operations are reachable from this fragment. The thread
choice in `Machine::step` has a unique solution here (see
`pickActiveThread`). The address choice of `BasicMemory::allocate`, reached
through `Statement::StorageLive`, never does; `BM.pickAddr` documents the one
valid resolution the interpretation commits to.
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
  | abort
  | deadlock
  | specPanic (msg : String)
  | unsupported (what : String)
  | machineStop
  | memoryLeak
  deriving DecidableEq

/-- `Result<T>` of specr-lang, plus the two non-behavior stops. -/
abbrev Interp (α : Type) : Type := Except Stop α

/-- `throw_ub!(msg)`. -/
def ub {α : Type} (msg : String) : Interp α := .error (.ub msg)

/-- `throw_abort!()` (`spec/prelude/main.md`):
> "macro_rules! throw_abort {
>      () => {
>          do yeet TerminationInfo::Abort
>      }
>  }" -/
def abort {α : Type} : Interp α := .error .abort

/-- `throw_machine_stop!()` (`spec/prelude/main.md`):
> "macro_rules! throw_machine_stop {
>      () => {
>          do yeet TerminationInfo::MachineStop
>      };
>  }" -/
def machineStop {α : Type} : Interp α := .error .machineStop

/-- `throw_memory_leak!()` (`spec/prelude/main.md`):
> "macro_rules! throw_memory_leak {
>      () => {
>          do yeet TerminationInfo::MemoryLeak
>      };
>  }" -/
def memoryLeak {α : Type} : Interp α := .error .memoryLeak

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

/-- `Align::from_bytes(n)`: `Some` iff `n` is a power of two. -/
def alignFromBytes (n : Nat) : Option Align :=
  if n ≠ 0 ∧ n &&& (n - 1) = 0 then some ⟨n⟩ else none

/-- `Align::from_bytes(n)` on a mathematical integer `n : Int`: `Some` iff `n`
is a (positive) power of two. -/
def alignFromBytesInt (n : Int) : Option Align :=
  if n < 0 then none else alignFromBytes n.toNat

/-- `Size::from_bytes(n)` on a mathematical integer `n : Int`: `Some` iff `n`
is non-negative. -/
def sizeFromBytes (n : Int) : Option Size :=
  if n < 0 then none else some ⟨n.toNat⟩

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

/-- `Map::insert(k, v)` helper on association-list entries. -/
def mapInsert {K V : Type} [DecidableEq K] : List (K × V) → K → V → List (K × V)
  | [], k, v => [(k, v)]
  | (k', v') :: tail, k, v => if k' = k then (k, v) :: tail else (k', v') :: mapInsert tail k v

/-- `Map::insert(k, v)`. -/
def mapInsertMap {K V : Type} [DecidableEq K] (m : Map K V) (k : K) (v : V) : Map K V :=
  ⟨mapInsert m.entries k v⟩

/-- `PartialEq::eq` on `libspecr::Map`: extensional key-value equality
(independent of association-list entry order or shadowed bindings). -/
def mapEq {K V : Type} [DecidableEq K] (eqV : V → V → Bool) (m1 m2 : Map K V) : Bool :=
  m1.entries.all (fun (k, _) =>
    match mapGet m1 k, mapGet m2 k with
    | some v1, some v2 => eqV v1 v2
    | _, _ => false) &&
  m2.entries.all (fun (k, _) => (mapGet m1 k).isSome)

/-- Distinct key count `Map::len()` on `libspecr::Map`. -/
def mapLen {K V : Type} [DecidableEq K] (m : Map K V) : Nat :=
  (m.entries.map Prod.fst).eraseDups.length

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

/-- `Ord::cmp` on `libspecr::Int` (`num_bigint::BigInt`): the numeric order of
mathematical integers, so signedness never enters (`-1 < 0` even when the bit
pattern of `-1i8` is `255`). -/
def intCmp (a b : Int) : Ordering := if a < b then .lt else if a = b then .eq else .gt

/-- `Ord::cmp` on `bool` (Rust's `impl Ord for bool`): `false < true`. -/
def boolCmp (a b : Bool) : Ordering := intCmp (if a then 1 else 0) (if b then 1 else 0)

/-- `List::write_subslice_at_index(start, src)`. -/
def writeSubsliceAtIndex {T : Type} (xs : List T) (start : Int) (src : List T) :
    Interp (List T) :=
  if 0 ≤ start ∧ start + src.length ≤ xs.length then
    pure (xs.take start.toNat ++ src ++ xs.drop (start.toNat + src.length))
  else specPanic "write_subslice_at_index out of range"

/-- `Size::align_to(align)`: the least multiple of `align` that is at least
`s`, `Size::from_bytes(self.bytes().next_multiple_of(align.bytes()))`, where
`Int::next_multiple_of(other)` is `self.div_ceil(other) * other`. Alignments
are positive, so `div_ceil(s, a)` is `(s + a - 1) / a`. -/
def Size.align_to (s : Size) (a : Align) : Size :=
  ⟨(s.bytes + a.bytes - 1) / a.bytes * a.bytes⟩

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
/-- `x86_64::PTR_ALIGN` = 64 bits:
> "const PTR_ALIGN: Align = Align::from_bits_const(64).unwrap();" -/
def x86_64.PTR_ALIGN : Align := ⟨8⟩
/-- `x86_64::INT_MAX_ALIGN` = 128 bits:
> "const INT_MAX_ALIGN: Align = Align::from_bits_const(128).unwrap();" -/
def x86_64.INT_MAX_ALIGN : Align := ⟨16⟩
/-- `x86_64::ENDIANNESS`:
> "const ENDIANNESS: Endianness = LittleEndian;" -/
def x86_64.ENDIANNESS : Endianness := .LittleEndian

/-- `x86_64::valid_size` (`spec/prelude/target.md`):
> "fn valid_size(size: Size) -> bool {
>     size.bytes().in_bounds(Signed, Self::PTR_SIZE)
> }" -/
def x86_64.valid_size (size : Size) : Bool :=
  inBounds size.bytes .Signed x86_64.PTR_SIZE

/-! ## Types and layout (`spec/lang/types.md`) -/

/-- `IntType::can_represent`:
> "pub fn can_represent(&self, i: Int) -> bool { i.in_bounds(self.signed, self.size) }" -/
def IntType.can_represent (t : IntType) (i : Int) : Bool := inBounds i t.signed t.size

/-- `IntType::bring_in_bounds`:
> "pub fn bring_in_bounds(&self, i: Int) -> Int { i.bring_in_bounds(self.signed, self.size) }" -/
def IntType.bring_in_bounds (t : IntType) (i : Int) : Int := bringInBounds i t.signed t.size

/-- `IntType::I8`, the result type of `RelOp::Cmp`:
> "pub const I8: IntType = IntType { signed: Signedness::Signed, size: Size::from_bytes_const(1) };" -/
def IntType.I8 : IntType := ⟨.Signed, ⟨1⟩⟩

/-- `IntType::align::<x86_64>`:
> "let natural_align = Align::from_bytes(size).unwrap();
>  natural_align.min(T::INT_MAX_ALIGN)" -/
def IntType.align (t : IntType) : Interp Align :=
  match alignFromBytes t.size.bytes with
  | some a => pure ⟨min a.bytes x86_64.INT_MAX_ALIGN.bytes⟩
  | none => specPanic "Align::from_bytes(size).unwrap()"

/-- `IntType::with_overflow::<x86_64>` (`spec/lang/types.md`):
> "pub fn with_overflow<T: Target>(&self) -> Type {
>     // Define a tuple type with two fields: An integer followed directly by a boolean.
>     let fields = list![(Size::ZERO, Type::Int(*self)), (self.size, Type::Bool)];
>     // Alignment is always the one of the integer as boolean has align requirement 1.
>     let align = self.align::<T>();
>     // The total size is `self.size + 1` rounded up to the next multiple of `align`.
>     // Since `self.size` is already a multiple of `align`, we can compute this as follows:
>     let size = self.size + Size::from_bytes(align.bytes()).unwrap();
>     Type::Tuple {
>         sized_fields: fields,
>         sized_head_layout: TupleHeadLayout {
>             end: size,
>             align,
>             packed_align: None,
>         },
>         unsized_field: None,
>     }
> }" -/
def IntType.with_overflow (t : IntType) : Interp «Type» := do
  let size := t.size
  let align ← IntType.align t
  pure (.Tuple [(⟨0⟩, .Int t), (size, .Bool)] ⟨⟨size.bytes + align.bytes⟩, align, none⟩ none)

/-- `TupleHeadLayout::capped_tail_align` (`spec/lang/types.md`):
> "fn capped_tail_align(self, tail_align: Align) -> Align {
>     match self.packed_align {
>         Some(packed_align) => tail_align.min(packed_align),
>         None => tail_align,
>     }
> }" -/
def TupleHeadLayout.capped_tail_align (l : TupleHeadLayout) (tailAlign : Align) : Align :=
  match l.packed_align with
  | some packedAlign => ⟨min tailAlign.bytes packedAlign.bytes⟩
  | none => tailAlign

/-- `TupleHeadLayout::tail_offset` (`spec/lang/types.md`):
> "pub fn tail_offset(self, tail_align: Align) -> Offset {
>     let capped_tail_align = self.capped_tail_align(tail_align);
>     let tail_offset = self.end.align_to(capped_tail_align);
>     tail_offset
> }" -/
def TupleHeadLayout.tail_offset (l : TupleHeadLayout) (tailAlign : Align) : Offset :=
  let cappedTailAlign := TupleHeadLayout.capped_tail_align l tailAlign
  Size.align_to l.end cappedTailAlign

/-- `TupleHeadLayout::full_size_and_align` (`spec/lang/types.md`):
> "pub fn full_size_and_align(self, tail_size: Size, tail_align: Align) -> (Size, Align) {
>     let capped_tail_align = self.capped_tail_align(tail_align);
>     let align = capped_tail_align.max(self.align);
>     let tail_offset = self.tail_offset(tail_align);
>     let end = tail_offset + tail_size;
>     let size = end.align_to(align);
>     (size, align)
> }" -/
def TupleHeadLayout.full_size_and_align (l : TupleHeadLayout) (tailSize : Size) (tailAlign : Align) :
    Size × Align :=
  let cappedTailAlign := TupleHeadLayout.capped_tail_align l tailAlign
  let align : Align := ⟨max cappedTailAlign.bytes l.align.bytes⟩
  let tailOffset := TupleHeadLayout.tail_offset l tailAlign
  let end_ : Size := ⟨tailOffset.bytes + tailSize.bytes⟩
  let size := Size.align_to end_ align
  (size, align)

/-- `TupleHeadLayout::head_size_and_align` (`spec/lang/types.md`), the size
and alignment of a tuple without an unsized tail:
> "pub fn head_size_and_align(self) -> (Size, Align) {
>     // This is equivalent to `full_size_and_align(ZERO, ONE)`.
>     (self.end.align_to(self.align), self.align)
> }" -/
def TupleHeadLayout.head_size_and_align (l : TupleHeadLayout) : Size × Align :=
  (Size.align_to l.end l.align, l.align)

/-- `LayoutStrategy::is_sized` (`spec/lang/types.md`):
> "pub fn is_sized(self) -> bool {
>     matches!(self, LayoutStrategy::Sized(..))
> }" -/
def LayoutStrategy.is_sized : LayoutStrategy → Bool
  | .Sized _ _ => true
  | _ => false

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
  | _ => specPanic ("expect_size called on unsized type: " ++ msg)

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
  | _ => specPanic ("expect_align called on unsized type: " ++ msg)

/-- `LayoutStrategy::compute_size_and_align` (`spec/lang/types.md`):
> "pub fn compute_size_and_align<Provenance>(
>     self,
>     meta: Option<PointerMeta<Provenance>>,
>     vtables: impl FnOnce(ThinPointer<Provenance>) -> VTable,
> ) -> (Size, Align) {
>     match (self, meta) {
>         (LayoutStrategy::Sized(size, align), None) => (size, align),
>         (LayoutStrategy::Slice(elem_size, align), Some(PointerMeta::ElementCount(count))) => (count * elem_size, align),
>         (LayoutStrategy::TraitObject(..), Some(PointerMeta::VTablePointer(vtable_ptr))) => {
>             let vtable = vtables(vtable_ptr);
>             (vtable.size, vtable.align)
>         }
>         (LayoutStrategy::Tuple { head, tail }, Some(meta)) => {
>             let (tail_size, tail_align) = tail.compute_size_and_align(Some(meta), vtables);
>             head.full_size_and_align(tail_size, tail_align)
>         }
>         _ => panic!(\"pointer meta data does not match type\"),
>     }
> }" -/
def LayoutStrategy.compute_size_and_align (vtables : Ptr → Interp VTable) :
    LayoutStrategy → Option (PointerMeta Prov) → Interp (Size × Align)
  | .Sized size align, none => pure (size, align)
  | .Slice elemSize align, some (.ElementCount count) =>
    let bytes : Int := count * (elemSize.bytes : Int)
    if 0 ≤ bytes then pure (⟨bytes.toNat⟩, align)
    else specPanic "Size::from_bytes(count * elem_size.bytes()).unwrap()"
  | .TraitObject _, some (.VTablePointer vtablePtr) => do
    let vtable ← vtables vtablePtr
    pure (vtable.size, vtable.align)
  | .Tuple head tail, some metadata => do
    let (tailSize, tailAlign) ← LayoutStrategy.compute_size_and_align vtables tail (some metadata)
    pure (TupleHeadLayout.full_size_and_align head tailSize tailAlign)
  | _, _ => specPanic "pointer meta data does not match type"

/-- `LayoutStrategy::meta_kind` (`spec/lang/types.md`):
> "pub fn meta_kind(self) -> PointerMetaKind {
>     match self {
>         LayoutStrategy::Sized(..) => PointerMetaKind::None,
>         LayoutStrategy::Slice(..) => PointerMetaKind::ElementCount,
>         LayoutStrategy::TraitObject(trait_name) => PointerMetaKind::VTablePointer(trait_name),
>         LayoutStrategy::Tuple { tail, .. } => tail.meta_kind(),
>     }
> }" -/
def LayoutStrategy.meta_kind : LayoutStrategy → PointerMetaKind
  | .Sized _ _ => .None
  | .Slice _ _ => .ElementCount
  | .TraitObject traitName => .VTablePointer traitName
  | .Tuple _ tail => LayoutStrategy.meta_kind tail

/-- `PtrType::safe_pointee` (`spec/mem/pointer.md`):
> "pub fn safe_pointee(self) -> Option<PointeeInfo> {
>     match self {
>         PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => Some(pointee),
>         PtrType::Raw { .. } | PtrType::FnPtr | PtrType::VTablePtr(_) => None,
>     }
> }" -/
def PtrType.safe_pointee : PtrType → Option PointeeInfo
  | .Ref _ pointee | .Box pointee => some pointee
  | .Raw _ | .FnPtr | .VTablePtr _ => none

/-- `PtrType::meta_kind` (`spec/mem/pointer.md`):
> "pub fn meta_kind(self) -> PointerMetaKind {
>     match self {
>         PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => pointee.layout.meta_kind(),
>         PtrType::Raw { meta_kind, .. } => meta_kind,
>         PtrType::FnPtr | PtrType::VTablePtr(_) => PointerMetaKind::None,
>     }
> }" -/
def PtrType.meta_kind : PtrType → PointerMetaKind
  | .Ref _ pointee | .Box pointee => LayoutStrategy.meta_kind pointee.layout
  | .Raw metaKind => metaKind
  | .FnPtr | .VTablePtr _ => .None

/-- `Type::layout::<x86_64>` (`spec/lang/types.md`):
> "Int(int_type) => Sized(int_type.size, int_type.align::<T>()),
>  Bool => Sized(Size::from_bytes_const(1), Align::ONE),
>  Ptr(p) if p.meta_kind() == PointerMetaKind::None => Sized(T::PTR_SIZE, T::PTR_ALIGN),
>  Ptr(_) => Sized(libspecr::Int::from(2) * T::PTR_SIZE, T::PTR_ALIGN),
>  Union { size, align, .. } | Enum { size, align, .. } => Sized(size, align),
>  Tuple { sized_head_layout, unsized_field, .. } => match unsized_field {
>      None => {
>          let (size, align) = sized_head_layout.head_size_and_align();
>          Sized(size, align)
>      }
>      Some(tail_ty) => LayoutStrategy::Tuple {
>          head: sized_head_layout,
>          tail: tail_ty.layout::<T>(),
>      },
>  },
>  Array { elem, count } => Sized(
>      elem.layout::<T>().expect_size(\"WF ensures array element is sized\") * count,
>      elem.layout::<T>().expect_align(\"WF ensures array element is sized\"),
>  ),
>  Slice { elem } => LayoutStrategy::Slice(
>      elem.layout::<T>().expect_size(\"WF ensures slice element is sized\"),
>      elem.layout::<T>().expect_align(\"WF ensures array element is sized\"),
>  ),
>  TraitObject(trait_name) => LayoutStrategy::TraitObject(trait_name)," -/
def Type.layout : «Type» → Interp LayoutStrategy
  | .Int t => do pure (.Sized t.size (← IntType.align t))
  | .Bool => pure (.Sized ⟨1⟩ ⟨1⟩)
  | .Ptr p =>
    if PtrType.meta_kind p == .None then
      pure (.Sized x86_64.PTR_SIZE x86_64.PTR_ALIGN)
    else
      pure (.Sized ⟨2 * x86_64.PTR_SIZE.bytes⟩ x86_64.PTR_ALIGN)
  | .Union _ _ size align => pure (.Sized size align)
  | .Enum _ _ _ size align => pure (.Sized size align)
  | .Tuple _ headLayout none =>
    let (size, align) := TupleHeadLayout.head_size_and_align headLayout
    pure (.Sized size align)
  | .Tuple _ headLayout (some tailTy) => do
    pure (.Tuple headLayout (← Type.layout tailTy))
  | .Array elem count => do
    let elemSize ← LayoutStrategy.expect_size (← Type.layout elem)
      "WF ensures array element is sized"
    let align ← LayoutStrategy.expect_align (← Type.layout elem)
      "WF ensures array element is sized"
    let bytes : Int := (elemSize.bytes : Int) * count
    if 0 ≤ bytes then pure (.Sized ⟨bytes.toNat⟩ align)
    else specPanic "Size::from_bytes(elem_size.bytes() * count).unwrap()"
  | .Slice elem => do
    let size ← LayoutStrategy.expect_size (← Type.layout elem)
      "WF ensures slice element is sized"
    let align ← LayoutStrategy.expect_align (← Type.layout elem)
      "WF ensures array element is sized"
    pure (.Slice size align)
  | .TraitObject traitName => pure (.TraitObject traitName)

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

/-- `Type::decode` for `Int` (`spec/lang/representation.md`):
> "fn decode<M: Memory>(Type::Int(IntType { signed, size }): Self, bytes: ..) -> Option<Value<M>> {
>     if bytes.len() != size.bytes() { panic!(..); }
>     // Fails if any byte is `Uninit`.
>     let bytes_data: List<u8> = bytes.try_map(|b| b.data())?;
>     ret(Value::Int(M::T::ENDIANNESS.decode(signed, bytes_data)))
> }"
`Type.decode (.Int t)` is `Type.decodeInt t`; it is a definition of its own
because `decodeDiscriminant` decodes tags at `Type::Int`. -/
def Type.decodeInt : IntType → List Byte → Interp (Option Val)
  | ⟨signed, size⟩, bytes =>
    if bytes.length ≠ size.bytes then specPanic "decode of Type::Int with invalid length"
    else
      match bytes.mapM AbstractByte.data with
      | some data => pure (some (.Int (Endianness.decode x86_64.ENDIANNESS signed data)))
      | none => pure none

/-- `Type::encode` for `Int` (`spec/lang/representation.md`):
> "fn encode<M: Memory>(Type::Int(IntType { signed, size }): Self, val: Value<M>) -> .. {
>     let Value::Int(i) = val else { panic!() };
>     // `Endianness::encode` will do the integer's bound check.
>     let bytes_data = M::T::ENDIANNESS.encode(signed, size, i).unwrap();
>     bytes_data.map(|b| AbstractByte::Init(b, None))
> }"
`Type.encode (.Int t)` is `Type.encodeInt t`; it is a definition of its own
because `encodeDiscriminant` encodes tags at `Type::Int`. -/
def Type.encodeInt : IntType → Val → Interp (List Byte)
  | ⟨signed, size⟩, .Int i =>
    match Endianness.encode x86_64.ENDIANNESS signed size i with
    | some data => pure (data.map (fun b => .Init b none))
    | none => specPanic "Endianness::encode(..).unwrap()"
  | _, _ => specPanic "encode: Type::Int with a non-Int value"

mutual

/-- `decode_discriminant` (`spec/lang/representation.md`), which walks an
enum's `Discriminator` decision tree, reading tags through `accessor`:
> "fn decode_discriminant<M: Memory>(
>     mut accessor: impl FnMut(Offset, Size) -> Result<List<AbstractByte<M::Provenance>>>,
>     discriminator: Discriminator
> ) -> Result<Option<Int>> {
>     match discriminator {
>         Discriminator::Known(val) => ret(Some(val)),
>         Discriminator::Invalid => ret(None),
>         Discriminator::Branch { offset, value_type, children, fallback } => {
>             let bytes = accessor(offset, value_type.size)?;
>             let Some(Value::Int(val)) = Type::Int(value_type).decode::<M>(bytes)
>                 else { return ret(None); };
>             let next_discriminator = children.iter()
>                 .find_map(|((start, end), child)|
>                     if start <= val && val < end { Some(child) } else { None })
>                 .unwrap_or(fallback);
>             decode_discriminant::<M>(accessor, next_discriminator)
>         }
>     }
> }"
The state that the `FnMut` accessor mutates (for `Type::decode` at `Enum`,
`Unit`) is threaded through explicitly as `s : σ`. To keep the recursion
structural while only touching the branch that `val` selects, the `Branch`
case passes the continuation `decodeDiscriminant accessor fallback : σ →
Interp (Option Int × σ)` to `decodeDiscriminantChildren`, which invokes it
with the updated state `s` only when no child's range `[start, end)` contains
`val`. -/
def decodeDiscriminant {σ : Type}
    (accessor : σ → Offset → Size → Interp (List Byte × σ)) :
    Discriminator → σ → Interp (Option Int × σ)
  | .Known val, s => pure (some val, s)
  | .Invalid, s => pure (none, s)
  | .Branch offset valueType fallback ⟨children⟩, s => do
    let (bytes, s) ← accessor s offset valueType.size
    match ← Type.decodeInt valueType bytes with
    | some (.Int val) =>
      decodeDiscriminantChildren accessor val (decodeDiscriminant accessor fallback) children s
    | _ => pure (none, s)

/-- The choice of the next discriminator in `decode_discriminant`
(`spec/lang/representation.md`), followed by the recursive call:
> "let next_discriminator = children.iter()
>     .find_map(|((start, end), child)|
>         if start <= val && val < end { Some(child) } else { None })
>     .unwrap_or(fallback);
> decode_discriminant::<M>(accessor, next_discriminator)"
`onFallback` is the continuation for `fallback`, invoked with `s` only when
no child range contains `val`. -/
def decodeDiscriminantChildren {σ : Type}
    (accessor : σ → Offset → Size → Interp (List Byte × σ)) (val : Int)
    (onFallback : σ → Interp (Option Int × σ)) :
    List ((Int × Int) × Discriminator) → σ → Interp (Option Int × σ)
  | [], s => onFallback s
  | ((start, end_), child) :: rest, s =>
    if start ≤ val ∧ val < end_ then decodeDiscriminant accessor child s
    else decodeDiscriminantChildren accessor val onFallback rest s

end

/-- `encode_discriminant` (`spec/lang/representation.md`), which writes every
tag of a variant's `tagger` through `accessor`:
> "fn encode_discriminant<M: Memory>(
>     mut accessor: impl FnMut(Offset, List<AbstractByte<M::Provenance>>) -> Result,
>     tagger: Map<Offset, (IntType, Int)>
> ) -> Result<()> {
>     for (offset, (value_type, value)) in tagger.iter() {
>         let bytes = Type::Int(value_type).encode::<M>(Value::Int(value));
>         accessor(offset, bytes)?;
>     }
>     ret(())
> }"
The state that the `FnMut` accessor mutates (for `Type::encode` at `Enum`, the
bytes being encoded) is threaded through explicitly as `s : σ`. -/
def encodeDiscriminant {σ : Type} (accessor : σ → Offset → List Byte → Interp σ)
    (tagger : Map Offset (IntType × Int)) (s : σ) : Interp σ :=
  tagger.entries.foldlM (fun s entry => do
    let (offset, (valueType, value)) := entry
    let bytes ← Type.encodeInt valueType (.Int value)
    accessor s offset bytes) s

mutual

/-- `Type::decode` for `Bool`, `Int` (`Type.decodeInt`), `Tuple`, `Union`,
`Enum`, `Slice`, and `TraitObject` (`spec/lang/representation.md`):
> "fn decode<M: Memory>(Type::Bool: Self, bytes: ..) -> Option<Value<M>> {
>     if bytes.len() != 1 { panic!(..); }
>     ret(match bytes[0] {
>         AbstractByte::Init(0, _) => Value::Bool(false),
>         AbstractByte::Init(1, _) => Value::Bool(true),
>         _ => throw!(),
>     })
> }"
> "fn decode<M: Memory>(
>     Type::Tuple { sized_fields, sized_head_layout, unsized_field }: Self,
>     bytes: List<AbstractByte<M::Provenance>>
> ) -> Option<Value<M>> {
>     assert!(unsized_field.is_none(), \"decode of Type::Tuple with unsized field\");
>     let (size, _) = sized_head_layout.head_size_and_align();
>     if bytes.len() != size.bytes() { panic!(\"decode of Type::Tuple with invalid length\"); }
>     ret(Value::Tuple(
>         sized_fields.try_map(|(offset, ty)| { .. })?
>     ))
> }"
> "fn decode<M: Memory>(Type::Union { size, chunks, .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
>     if bytes.len() != size.bytes() { panic!(\"decode of Type::Union with invalid length\"); }
>     let mut chunk_data = list![];
>     // Store the data from each chunk.
>     for (offset, size) in chunks {
>         chunk_data.push(bytes.subslice_with_length(offset.bytes(), size.bytes()));
>     }
>     ret(Value::Union(chunk_data))
> }"
> "fn decode<M: Memory>(
>     Type::Enum { variants, discriminator, size, .. }: Self,
>     bytes: List<AbstractByte<M::Provenance>>
> ) -> Option<Value<M>> {
>     if bytes.len() != size.bytes() { panic!(\"decode of Type::Enum with invalid length\"); }
>     ..
>     let discriminant = decode_discriminant::<M>(
>         |offset, size| ret(bytes.subslice_with_length(offset.bytes(), size.bytes())),
>         discriminator
>     ).unwrap()?;
>     ..
>     let Some(value) = variants[discriminant].ty.decode(bytes)
>         else { return None };
>     Some(Value::Variant { discriminant, data: value })
> }"
> "fn decode<M: Memory>(Type::Slice { .. }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
>     panic!(\"decode of Type::Slice\")
> }"
> "fn decode<M: Memory>(Type::TraitObject(..): Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
>     panic!(\"decode of Type::TraitObject\")
> }"
The fields of a tuple are decoded by `Type.decodeFields` and the data of an
enum variant by `Type.decodeVariant`. `decode_discriminant` fails only if its
accessor does; this accessor fails only by panicking (`subsliceWithLength` out
of range), so `.unwrap()` is the propagation of that panic. Pointers and arrays
are outside the fragment. -/
def Type.decode : «Type» → List Byte → Interp (Option Val)
  | .Bool, bytes =>
    if bytes.length ≠ 1 then specPanic "decode of Type::Bool with invalid length"
    else
      match bytes with
      | [.Init 0 _] => pure (some (.Bool false))
      | [.Init 1 _] => pure (some (.Bool true))
      | _ => pure none
  | .Int t, bytes => Type.decodeInt t bytes
  | .Tuple fields headLayout unsizedField, bytes =>
    match unsizedField with
    | some _ => specPanic "decode of Type::Tuple with unsized field"
    | none =>
      let (size, _) := TupleHeadLayout.head_size_and_align headLayout
      if bytes.length ≠ size.bytes then specPanic "decode of Type::Tuple with invalid length"
      else do
        match ← Type.decodeFields fields bytes with
        | some vals => pure (some (.Tuple vals))
        | none => pure none
  | .Union _ chunks size _, bytes =>
    if bytes.length ≠ size.bytes then specPanic "decode of Type::Union with invalid length"
    else do
      let chunkData ← chunks.mapM (fun (offset, chunkSize) =>
        subsliceWithLength bytes offset.bytes chunkSize.bytes)
      pure (some (.Union chunkData))
  | .Enum ⟨variants⟩ _ discriminator size _, bytes =>
    if bytes.length ≠ size.bytes then specPanic "decode of Type::Enum with invalid length"
    else do
      let accessor := fun (_ : Unit) (offset : Offset) (size : Size) => do
        let bs ← subsliceWithLength bytes offset.bytes size.bytes
        pure (bs, ())
      match (← decodeDiscriminant accessor discriminator ()).1 with
      | none => pure none
      | some discriminant =>
        match ← Type.decodeVariant variants discriminant bytes with
        | some value => pure (some (.Variant discriminant value))
        | none => pure none
  | .Slice _, _ => specPanic "decode of Type::Slice"
  | .TraitObject _, _ => specPanic "decode of Type::TraitObject"
  | _, _ => unsupported "Type::decode for a pointer or array type"

/-- The fields of `Type::decode` for `Tuple` (`spec/lang/representation.md`),
each decoded from its own subslice:
> "sized_fields.try_map(|(offset, ty)| {
>     let subslice = bytes.subslice_with_length(
>         offset.bytes(),
>         ty.layout::<M::T>().expect_size(\"WF ensures all sized tuple fields are sized\").bytes()
>     );
>     ty.decode::<M>(subslice)
> })?"
`try_map` stops at the first field that does not decode (`None`). -/
def Type.decodeFields : List (Offset × «Type») → List Byte → Interp (Option (List Val))
  | [], _ => pure (some [])
  | (offset, ty) :: rest, bytes => do
    let size ← LayoutStrategy.expect_size (← Type.layout ty)
      "WF ensures all sized tuple fields are sized"
    let subslice ← subsliceWithLength bytes offset.bytes size.bytes
    match ← Type.decode ty subslice with
    | none => pure none
    | some v =>
      match ← Type.decodeFields rest bytes with
      | none => pure none
      | some vs => pure (some (v :: vs))

/-- The variant data of `Type::decode` for `Enum`
(`spec/lang/representation.md`):
> "let Some(value) = variants[discriminant].ty.decode(bytes)
>     else { return None };"
`variants[discriminant]` (`Index` on `libspecr::Map`) is the entry for
`discriminant` (the first one, as in `mapGet`) and panics if there is none,
as in `mapIndex`. -/
def Type.decodeVariant : List (Int × Variant) → Int → List Byte → Interp (Option Val)
  | [], _, _ => specPanic "map index: missing key (variants[discriminant])"
  | (d, ⟨ty, _⟩) :: rest, discriminant, bytes =>
    if d = discriminant then Type.decode ty bytes
    else Type.decodeVariant rest discriminant bytes

end

/-- The chunk loop of `Type::encode` for `Union`
(`spec/lang/representation.md`), which writes each chunk's bytes at its offset
into `bytes` (initially all `Uninit`):
> "for ((offset, size), data) in chunks.zip(chunk_data) {
>     assert_eq!(size.bytes(), data.len());
>     bytes.write_subslice_at_index(offset.bytes(), data);
> }" -/
def Type.encodeUnionChunks :
    List (Offset × Size) → List (List Byte) → List Byte → Interp (List Byte)
  | (offset, size) :: chunks, data :: chunkData, bytes =>
    if size.bytes ≠ data.length then
      specPanic "assertion failed: size.bytes() == data.len()"
    else do
      let bytes ← writeSubsliceAtIndex bytes offset.bytes data
      Type.encodeUnionChunks chunks chunkData bytes
  | _, _, bytes => pure bytes

mutual

/-- `Type::encode` for `Bool`, `Int` (`Type.encodeInt`), `Tuple`, `Union`,
`Enum`, `Slice`, and `TraitObject` (`spec/lang/representation.md`):
> "fn encode<M: Memory>(Type::Bool: Self, val: Value<M>) -> .. {
>     let Value::Bool(b) = val else { panic!() };
>     list![AbstractByte::Init(if b { 1 } else { 0 }, None)]
> }"
> "fn encode<M: Memory>(
>     Type::Tuple { sized_fields, sized_head_layout, unsized_field }: Self,
>     val: Value<M>
> ) -> List<AbstractByte<M::Provenance>> {
>     assert!(unsized_field.is_none(), \"encode of Type::Tuple with unsized field\");
>     let (size, _) = sized_head_layout.head_size_and_align();
>     let Value::Tuple(values) = val else { panic!() };
>     assert_eq!(values.len(), sized_fields.len());
>     let mut bytes = list![AbstractByte::Uninit; size.bytes()];
>     ..
>     bytes
> }"
> "fn encode<M: Memory>(Type::Union { size, chunks, .. }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
>     let Value::Union(chunk_data) = val else { panic!() };
>     assert_eq!(chunk_data.len(), chunks.len());
>     let mut bytes = list![AbstractByte::Uninit; size.bytes()];
>     ..
>     bytes
> }"
> "fn encode<M: Memory>(
>     Type::Enum { variants, .. }: Self,
>     val: Value<M>
> ) -> List<AbstractByte<M::Provenance>> {
>     ..
>     let (discriminant, data) = match val {
>         Value::Variant { discriminant, data } => (discriminant, data),
>         _ => panic!(),
>     };
>     ..
>     let Variant { ty: variant, tagger } = variants[discriminant];
>     let mut bytes = variant.encode(data);
>     ..
>     encode_discriminant::<M>(|offset, value_bytes| {
>         bytes.write_subslice_at_index(offset.bytes(), value_bytes);
>         ret(())
>     }, tagger).unwrap();
>     bytes
> }"
> "fn encode<M: Memory>(Type::Slice { .. }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
>     panic!(\"encode of Type::Slice\")
> }"
> "fn encode<M: Memory>(Type::TraitObject(..): Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
>     panic!(\"encode of Type::TraitObject\")
> }"
The fields of a tuple are encoded by `Type.encodeFields`, the chunks of a
union by `Type.encodeUnionChunks`, and the variant of an enum by
`Type.encodeVariant`. Pointers and arrays are outside the fragment. -/
def Type.encode : «Type» → Val → Interp (List Byte)
  | .Bool, .Bool b => pure [.Init (if b then 1 else 0) none]
  | .Bool, _ => specPanic "encode: Type::Bool with a non-Bool value"
  | .Int t, val => Type.encodeInt t val
  | .Tuple fields headLayout unsizedField, val =>
    match unsizedField with
    | some _ => specPanic "encode of Type::Tuple with unsized field"
    | none =>
      let (size, _) := TupleHeadLayout.head_size_and_align headLayout
      match val with
      | .Tuple values =>
        if values.length ≠ fields.length then
          specPanic "assertion failed: values.len() == sized_fields.len()"
        else Type.encodeFields fields values (List.replicate size.bytes .Uninit)
      | _ => specPanic "encode: Type::Tuple with a non-Tuple value"
  | .Union _ chunks size _, val =>
    match val with
    | .Union chunkData =>
      if chunkData.length ≠ chunks.length then
        specPanic "assertion failed: chunk_data.len() == chunks.len()"
      else Type.encodeUnionChunks chunks chunkData (List.replicate size.bytes .Uninit)
    | _ => specPanic "encode: Type::Union with a non-Union value"
  | .Enum ⟨variants⟩ _ _ _ _, val =>
    match val with
    | .Variant discriminant data => Type.encodeVariant variants discriminant data
    | _ => specPanic "encode: Type::Enum with a non-Variant value"
  | .Slice _, _ => specPanic "encode of Type::Slice"
  | .TraitObject _, _ => specPanic "encode of Type::TraitObject"
  | _, _ => unsupported "Type::encode for a pointer or array type"

/-- The field loop of `Type::encode` for `Tuple`
(`spec/lang/representation.md`), which writes each field's encoding at its
offset into `bytes` (initially all `Uninit`):
> "for ((offset, ty), value) in sized_fields.zip(values) {
>     bytes.write_subslice_at_index(offset.bytes(), ty.encode::<M>(value));
> }" -/
def Type.encodeFields : List (Offset × «Type») → List Val → List Byte → Interp (List Byte)
  | (offset, ty) :: fields, value :: values, bytes => do
    let fieldBytes ← Type.encode ty value
    let bytes ← writeSubsliceAtIndex bytes offset.bytes fieldBytes
    Type.encodeFields fields values bytes
  | _, _, bytes => pure bytes

/-- The variant of `Type::encode` for `Enum` (`spec/lang/representation.md`):
> "let Variant { ty: variant, tagger } = variants[discriminant];
> let mut bytes = variant.encode(data);"
followed by writing the tag with `encode_discriminant`, whose accessor writes
into `bytes` (`Map` indexing as in `Type.decodeVariant`). -/
def Type.encodeVariant : List (Int × Variant) → Int → Val → Interp (List Byte)
  | [], _, _ => specPanic "map index: missing key (variants[discriminant])"
  | (d, ⟨ty, tagger⟩) :: rest, discriminant, data =>
    if d = discriminant then do
      let bytes ← Type.encode ty data
      encodeDiscriminant
        (fun bytes offset valueBytes => writeSubsliceAtIndex bytes offset.bytes valueBytes)
        tagger bytes
    else Type.encodeVariant rest discriminant data

end

/-- `ensure_else_ub` (`spec/lang/representation.md`):
> "/// Ensures the given boolean is true or else raises UB.
> fn ensure_else_ub(b: bool, msg: &str) -> Result<()> {
>     if !b { throw_ub!(\"{}\", msg); }
>     ret(())
> }" -/
def ensureElseUb (b : Bool) (msg : String) : Interp Unit :=
  if !b then ub msg else pure ()

/-- The chunk loop of `check_value` for unions (`spec/lang/representation.md`):
> "for (data, (_, size)) in chunk_data.zip(chunks) {
>     ensure_else_ub(data.len() == size.bytes(), \"Value::Union: invalid chunk data\")?;
> }" -/
def checkUnionChunks : List (List Byte) → List (Offset × Size) → Interp Unit
  | data :: chunkData, (_, size) :: chunks => do
    ensureElseUb (data.length == size.bytes) "Value::Union: invalid chunk data"
    checkUnionChunks chunkData chunks
  | _, _ => pure ()

mutual

/-- `Machine::check_value` for `Int`, `Bool`, `Tuple`, `Union`, `Variant`,
`Slice`, and `TraitObject` (`spec/lang/representation.md`):
> "(Value::Int(i), Type::Int(int_ty)) => {
>     ensure_else_ub(int_ty.can_represent(i), \"Value::Int: invalid integer value\")?;
> }
> (Value::Bool(_), Type::Bool) => {},
> ..
> (Value::Tuple(vals), Type::Tuple { sized_fields, unsized_field, .. }) => {
>     assert!(unsized_field.is_none(), \"Value: unsized structs cannot be represented as values\");
>     ensure_else_ub(vals.len() == sized_fields.len(), \"Value::Tuple: invalid number of fields\")?;
>     ..
> }
> ..
> (Value::Union(chunk_data), Type::Union { chunks, .. }) => {
>     ensure_else_ub(chunk_data.len() == chunks.len(), \"Value::Union: invalid chunk size\")?;
>     ..
> }
> (Value::Variant { discriminant, data }, Type::Enum { variants, .. }) => {
>     ..
> }
> (_, Type::Slice { .. }) => panic!(\"Value: slices cannot be represented as values\"),
> (_, Type::TraitObject { .. }) => panic!(\"Value: trait objects cannot be represented as values\"),
> _ => panic!(\"Value: value does not match type\")"
The fields of a tuple are checked by `checkFields`, the chunks of a union by
`checkUnionChunks`, and the data of a variant by `checkVariant`. Pointers and
arrays are outside the fragment. -/
def checkValue : Val → «Type» → Interp Unit
  | .Int i, .Int t =>
    ensureElseUb (IntType.can_represent t i) "Value::Int: invalid integer value"
  | .Bool _, .Bool => pure ()
  | .Tuple vals, .Tuple fields _ unsizedField =>
    match unsizedField with
    | some _ => specPanic "Value: unsized structs cannot be represented as values"
    | none => do
      ensureElseUb (vals.length == fields.length) "Value::Tuple: invalid number of fields"
      checkFields vals fields
  | .Union chunkData, .Union _ chunks _ _ => do
    ensureElseUb (chunkData.length == chunks.length) "Value::Union: invalid chunk size"
    checkUnionChunks chunkData chunks
  | .Variant discriminant data, .Enum ⟨variants⟩ _ _ _ _ => checkVariant variants discriminant data
  | _, .Slice _ => specPanic "Value: slices cannot be represented as values"
  | _, .TraitObject _ => specPanic "Value: trait objects cannot be represented as values"
  | _, .Int _ => specPanic "Value: value does not match type"
  | _, .Bool => specPanic "Value: value does not match type"
  | _, .Tuple _ _ _ => specPanic "Value: value does not match type"
  | _, .Union _ _ _ _ => specPanic "Value: value does not match type"
  | _, .Enum _ _ _ _ _ => specPanic "Value: value does not match type"
  | _, _ => unsupported "check_value for a pointer or array type"

/-- The field loop of `check_value` for tuples (`spec/lang/representation.md`):
> "for (val, (_, ty)) in vals.zip(sized_fields) {
>     self.check_value(val, ty)?;
> }" -/
def checkFields : List Val → List (Offset × «Type») → Interp Unit
  | val :: vals, (_, ty) :: fields => do
    checkValue val ty
    checkFields vals fields
  | _, _ => pure ()

/-- The variant lookup of `check_value` for enums
(`spec/lang/representation.md`):
> "let Some(variant) = variants.get(discriminant) else {
>     throw_ub!(\"Value::Variant: invalid discrimant\");
> };
> self.check_value(data, variant.ty)?;"
`variants.get(discriminant)` is the first entry for `discriminant`, as in
`mapGet`. -/
def checkVariant : List (Int × Variant) → Int → Val → Interp Unit
  | [], _, _ => ub "Value::Variant: invalid discrimant"
  | (d, ⟨ty, _⟩) :: rest, discriminant, data =>
    if d = discriminant then checkValue data ty else checkVariant rest discriminant data

end

/-! ## `BasicMemory` (`spec/mem/basic.md`) -/

/-- `Allocation::size`:
> "fn size(self) -> Size { Size::from_bytes(self.data.len()).unwrap() }" -/
def Allocation.size (a : Allocation) : Size := ⟨a.data.length⟩

/-- `Allocation::overlaps` (`spec/mem/basic.md`):
> "fn overlaps(self, other_addr: Address, other_size: Size) -> bool {
>     let end_addr = self.addr + self.size().bytes();
>     let other_end_addr = other_addr + other_size.bytes();
>     if end_addr <= other_addr || other_end_addr <= self.addr {
>         // Our end is before their beginning, or vice versa -- we do not overlap.
>         // However, to make sure that each allocation has a unique address, we still
>         // report overlap if both allocations have the same address.
>         // FIXME: This is not necessarily realistic, e.g. for zero-sized stack variables.
>         // OTOH the function pointer logic currently relies on this.
>         self.addr == other_addr
>     } else {
>         true
>     }
> }" -/
def Allocation.overlaps (a : Allocation) (otherAddr : Address) (otherSize : Size) : Bool :=
  let endAddr : Int := a.addr + (Allocation.size a).bytes
  let otherEndAddr : Int := otherAddr + otherSize.bytes
  if endAddr ≤ otherAddr ∨ otherEndAddr ≤ a.addr then
    decide (a.addr = otherAddr)
  else
    true

/-- The predicate of the daemonic address choice in `BasicMemory::allocate`
(`spec/mem/basic.md`), transcribed test by test:
> "let addr = pick(distr, |addr: Address| {
>     // Pick a strictly positive integer...
>     if addr <= 0 { return false; }
>     // ... that is suitably aligned...
>     if !align.is_aligned(addr) { return false; }
>     // ... such that addr+size is in-bounds of a `usize`...
>     if !(addr+size.bytes()).in_bounds(Unsigned, T::PTR_SIZE) { return false; }
>     // ... and it does not overlap with any existing live allocation.
>     if self.allocations.any(|a| a.live && a.overlaps(addr, size)) { return false; }
>     // If all tests pass, we are good!
>     true
> })?;" -/
def BM.allocAddrOk (mem : BM) (size : Size) (align : Align) (addr : Int) : Bool :=
  if addr ≤ 0 then false
  else if !Align.is_aligned align addr then false
  else if !inBounds (addr + size.bytes) .Unsigned x86_64.PTR_SIZE then false
  else if mem.allocations.any (fun a => a.live && Allocation.overlaps a addr size) then false
  else true

/-- Candidate address number `k` of `BM.pickAddr`: `(k + 1) * 2^32`, a
value of the address distribution of `BasicMemory::allocate`
(`spec/mem/basic.md`) for every alignment up to `2^32`:
> "divisor: align.bytes(),"
Consecutive candidates are `2^32` bytes apart, so an allocation smaller than
`2^32` bytes overlaps at most one candidate. -/
def allocCandidate (k : Nat) : Int := ((k + 1 : Nat) : Int) * 2 ^ 32

/-- First fit among the candidates `allocCandidate k`, `allocCandidate (k+1)`,
.. (at most `fuel` of them): the first one that satisfies the predicate of
the address choice in `BasicMemory::allocate` (`spec/mem/basic.md`),
`BM.allocAddrOk`:
> "let addr = pick(distr, |addr: Address| {" -/
def firstFitAddr (mem : BM) (size : Size) (align : Align) : Nat → Nat → Option Int
  | 0, _ => none
  | fuel + 1, k =>
    if BM.allocAddrOk mem size align (allocCandidate k) then some (allocCandidate k)
    else firstFitAddr mem size align fuel (k + 1)

/-- How the interpretation resolves the daemonic address choice of
`BasicMemory::allocate` (`spec/mem/basic.md`):
> "// Pick a base address. We use daemonic non-deterministic choice,
>  // meaning the program has to cope with every possible choice.
>  // FIXME: This makes OOM (when there is no possible choice) into \"no behavior\",
>  // which is not what we want.
>  let distr = libspecr::IntDistribution {
>      start: Int::ONE,
>      end: Int::from(2).pow(T::PTR_SIZE.bits()),
>      divisor: align.bytes(),
>  };"
Unlike the thread choice in `Machine::step` (`pickActiveThread`), this choice
never has a unique solution, so the interpretation commits to one valid
resolution instead of reporting `Stop.unsupported`: the first of the
candidates `allocCandidate 0`, `allocCandidate 1`, .., that is, of the
`2^32 - 1` multiples of `2^32` in `[2^32, 2^64)`, that satisfies the `pick`
predicate (`BM.allocAddrOk`). An address returned here therefore satisfies
every test of the upstream predicate; when no candidate does, `BM.allocate`
reports `Stop.unsupported` rather than inventing an address. Results about
this interpretation hold for this resolution of the choice; the fragment
cannot observe addresses (it has no pointer-to-integer casts or pointer
comparisons), so the resolution affects which addresses locals receive, not
which values the program computes. -/
def BM.pickAddr (mem : BM) (size : Size) (align : Align) : Option Int :=
  firstFitAddr mem size align (2 ^ 32 - 1) 0

/-- `BasicMemory::allocate` (`spec/mem/basic.md`, with the address choice
resolved by `BM.pickAddr` and `()` for `prov_extra` and `alloc_extra` as in
`impl Memory for BasicMemory<T>`):
> "fn allocate(
>     &mut self,
>     kind: AllocationKind,
>     size: Size,
>     align: Align,
>     prov_extra: ProvExtra,
>     alloc_extra: AllocExtra,
> ) -> NdResult<ThinPointer<Provenance<ProvExtra>>> {
>     // Reject too large allocations. Size must fit in `isize`.
>     if !T::valid_size(size) {
>         throw_ub!(\"asking for a too large allocation\");
>     }
>     ..
>     // Compute allocation.
>     let allocation = Allocation {
>         addr,
>         align,
>         kind,
>         live: true,
>         data: list![AbstractByte::Uninit; size.bytes()],
>         extra: alloc_extra,
>     };
>
>     // Insert it into list, and remember where.
>     let id = AllocId(self.allocations.len());
>     self.allocations.push(allocation);
>
>     // And we are done!
>     ret(ThinPointer { addr, provenance: Some((id, prov_extra)) })
> }" -/
def BM.allocate (mem : BM) (kind : AllocationKind) (size : Size) (align : Align) :
    Interp (Ptr × BM) :=
  if !x86_64.valid_size size then ub "asking for a too large allocation"
  else
    match BM.pickAddr mem size align with
    | none => unsupported "allocate: no candidate address of the first-fit resolution is free"
    | some addr =>
      let allocation : Allocation := {
        addr := addr
        align := align
        kind := kind
        live := true
        data := List.replicate size.bytes .Uninit
        extra := ()
      }
      let id : AllocId := ⟨mem.allocations.length⟩
      let allocations := mem.allocations ++ [allocation]
      pure ({ addr := addr, provenance := some (id, ()) }, { mem with allocations := allocations })

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

/-- `ThinPointer::wrapping_offset::<x86_64>` (`spec/mem/pointer.md`):
> "pub fn wrapping_offset<T: Target>(self, offset: Int) -> Self {
>     let addr = self.addr + offset;
>     let addr = addr.bring_in_bounds(Unsigned, T::PTR_SIZE);
>     ThinPointer { addr, ..self }
> }" -/
def ThinPointer.wrapping_offset (ptr : Ptr) (offset : Int) : Ptr :=
  let addr := ptr.addr + offset
  let addr := bringInBounds addr .Unsigned x86_64.PTR_SIZE
  { ptr with addr := addr }

/-- `ThinPointer::widen` (`spec/mem/pointer.md`):
> "pub fn widen(self, metadata: Option<PointerMeta<Provenance>>) -> Pointer<Provenance> {
>     Pointer {
>         thin_pointer: self,
>         metadata,
>     }
> }" -/
def ThinPointer.widen (ptr : Ptr) (metadata : Option (PointerMeta Prov)) : Pointer Prov :=
  { thin_pointer := ptr, metadata := metadata }

/-- `BasicMemory::dereferenceable` (`spec/mem/basic.md`):
> "fn dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Size) -> Result {
>     self.check_ptr(ptr, len)?;
>     ret(())
> }" -/
def BM.dereferenceable (mem : BM) (ptr : Ptr) (len : Size) : Interp Unit := do
  let _ ← BM.check_ptr mem ptr len
  pure ()

/-- `Memory::signed_dereferenceable` for `BasicMemory` (`spec/mem/interface.md`):
> "fn signed_dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Int) -> Result {
>     if len > 0 {
>         self.dereferenceable(ptr, Size::from_bytes(len).unwrap())
>     } else {
>         // Compute a pointer to the beginning of the range, and check `dereferenceable` from there.
>         let begin_ptr = ThinPointer { addr: ptr.addr + len, ..ptr };
>         // `ptr.addr + len` might be negative, but then `dereferenceable` will surely fail.
>         self.dereferenceable(begin_ptr, Size::from_bytes(-len).unwrap())
>     }
> }" -/
def BM.signed_dereferenceable (mem : BM) (ptr : Ptr) (len : Int) : Interp Unit :=
  if len > 0 then
    BM.dereferenceable mem ptr ⟨len.toNat⟩
  else
    let beginPtr : Ptr := { ptr with addr := ptr.addr + len }
    BM.dereferenceable mem beginPtr ⟨(-len).toNat⟩

/-- `BasicMemory::deallocate` (`spec/mem/basic.md`, with the trivial
`handle_extra`):
> "let Some((id, prov_extra)) = ptr.provenance else { throw_ub!(\"deallocating invalid pointer\") };
>  let mut allocation = self.allocations[id.0];
>  if !allocation.live { throw_ub!(\"double-free\"); }
>  if ptr.addr != allocation.addr {
>      throw_ub!(\"deallocating with pointer not to the beginning of its allocation\");
>  }
>  if kind != allocation.kind {
>      throw_ub!(\"deallocating {:?} memory with {:?} deallocation operation\", allocation.kind, kind);
>  }
>  if size != allocation.size() {
>      throw_ub!(\"deallocating with incorrect size information\");
>  }
>  if align != allocation.align {
>      throw_ub!(\"deallocating with incorrect alignment information\");
>  }
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
    else if kind ≠ allocation.kind then
      let kindName : AllocationKind → String := fun
        | .Stack => "Stack" | .Heap => "Heap" | .Global => "Global"
        | .Function => "Function" | .VTable => "VTable"
      ub s!"deallocating {kindName allocation.kind} memory with {kindName kind} deallocation operation"
    else if size ≠ Allocation.size allocation then
      ub "deallocating with incorrect size information"
    else if align ≠ allocation.align then
      ub "deallocating with incorrect alignment information"
    else do
      let allocations ← listSet mem.allocations id._0 { allocation with live := false } "set"
      pure { mem with allocations := allocations }

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

/-- `ConcurrentMemory::allocate` (`spec/mem/concurrent.md`):
> "pub fn allocate(&mut self, kind: AllocationKind, size: Size, align: Align) -> NdResult<ThinPointer<M::Provenance>> {
>     self.memory.allocate(kind, size, align)
> }" -/
def CM.allocate (cm : ConcurrentMemory BM) (kind : AllocationKind) (size : Size) (align : Align) :
    Interp (Ptr × ConcurrentMemory BM) := do
  let (ptr, mem) ← BM.allocate cm.memory kind size align
  pure (ptr, { cm with memory := mem })

/-- `ConcurrentMemory::deallocate`:
> "pub fn deallocate(&mut self, ptr: ThinPointer<M::Provenance>, kind: AllocationKind, size: Size, align: Align) -> Result {
>     self.memory.deallocate(ptr, kind, size, align)
> }" -/
def CM.deallocate (cm : ConcurrentMemory BM) (ptr : Ptr) (kind : AllocationKind) (size : Size)
    (align : Align) : Interp (ConcurrentMemory BM) := do
  pure { cm with memory := ← BM.deallocate cm.memory ptr kind size align }

/-- `ConcurrentMemory::dereferenceable` (`spec/mem/concurrent.md`):
> "pub fn dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Size) -> Result {
>     self.memory.dereferenceable(ptr, len)
> }" -/
def CM.dereferenceable (cm : ConcurrentMemory BM) (ptr : Ptr) (len : Size) : Interp Unit :=
  BM.dereferenceable cm.memory ptr len

/-- `ConcurrentMemory::signed_dereferenceable` (`spec/mem/concurrent.md`):
> "pub fn signed_dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Int) -> Result {
>     self.memory.signed_dereferenceable(ptr, len)
> }" -/
def CM.signed_dereferenceable (cm : ConcurrentMemory BM) (ptr : Ptr) (len : Int) : Interp Unit :=
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

/-- `Machine::try_mutate_cur_frame` and `Thread::try_mutate_cur_frame`
(`spec/lang/machine.md`):
> "fn try_mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> NdResult<O>) -> NdResult<O> {
>     self.threads.try_mutate_at(self.active_thread, |thread| thread.try_mutate_cur_frame(|frame| f(frame, &mut self.mem)))
> }
> ..
> fn try_mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>) -> NdResult<O>) -> NdResult<O> {
>     if self.stack.is_empty() {
>         panic!(\"`try_mutate_cur_frame` called on empty stack!\");
>     }
>
>     let last_idx = self.stack.len() - 1;
>     self.stack.try_mutate_at(last_idx, f)
> }" -/
def tryMutateCurFrame (m : Mach)
    (f : Frame → ConcurrentMemory BM → Interp (Frame × ConcurrentMemory BM)) : Interp Mach := do
  let t ← activeThread m
  match t.stack.getLast? with
  | none => specPanic "`try_mutate_cur_frame` called on empty stack!"
  | some fr => do
    let (fr', cm') ← f fr m.mem
    let t' : Thread BM := { t with stack := t.stack.dropLast ++ [fr'] }
    let threads ← listSet m.threads m.active_thread t' "try_mutate_at"
    pure { m with mem := cm', threads := threads }

/-- `Machine::mutate_cur_stack` (`spec/lang/machine.md`):
> "fn mutate_cur_stack<O>(&mut self, f: impl FnOnce(&mut List<StackFrame<M>>) -> O) -> O {
>     self.threads.mutate_at(self.active_thread, |thread| f(&mut thread.stack))
> }" -/
def mutateCurStack {α : Type} (m : Mach) (f : List Frame → Interp (α × List Frame)) :
    Interp (α × Mach) := do
  let t ← activeThread m
  let (out, stack') ← f t.stack
  let threads ← listSet m.threads m.active_thread { t with stack := stack' } "mutate_at"
  pure (out, { m with threads := threads })

/-- `StackFrame::jump_to_block` (`spec/lang/machine.md`):
> "self.next_block = b; self.next_stmt = Int::ZERO;"
and `Machine::jump_to_block` (`spec/lang/step/terminators.md`):
> "self.try_mutate_cur_frame(|frame, _mem| { frame.jump_to_block(block); ret(()) })" -/
def jumpToBlock (m : Mach) (b : BbName) : Interp Mach :=
  mutateCurFrame m (fun fr => { fr with next_block := b, next_stmt := 0 })

/-- `Machine::fn_from_ptr` (`spec/lang/machine.md`):
> "fn fn_from_ptr(&self, ptr: Value<M>) -> Result<Function> {
>     if let Value::Ptr(Pointer { thin_pointer: thin_ptr, metadata }) = ptr {
>         if metadata.is_some() {
>             throw_ub!(\"invalid pointer for function lookup\");
>         }
>         let Some((func_name, _)) = self.fn_ptrs.iter().find(|(_, fn_ptr)| *fn_ptr == thin_ptr) else {
>             throw_ub!(\"invalid pointer for function lookup\");
>         };
>         ret(self.prog.functions[func_name])
>     } else {
>         throw_ub!(\"trying to look up a function based on a non-pointer value\");
>     }
> }" -/
def fnFromPtr (m : Mach) (ptr : Val) : Interp Function :=
  match ptr with
  | .Ptr ⟨thinPtr, metadata⟩ =>
    if metadata.isSome then ub "invalid pointer for function lookup"
    else
      match m.fn_ptrs.entries.find? (fun (_, (fnPtr : Ptr)) => decide (fnPtr = thinPtr)) with
      | some (funcName, _) => mapIndex m.prog.functions funcName "self.prog.functions[func_name]"
      | none => ub "invalid pointer for function lookup"
  | _ => ub "trying to look up a function based on a non-pointer value"

/-- `Machine::vtable_lookup` (`spec/lang/machine.md`):
> "fn vtable_lookup(&self) -> impl Fn(ThinPointer<M::Provenance>) -> VTable + 'static {
>     // This copies the data to return a static closure, as it is used in mutate functions, which mutably borrow self.
>     let ptrs = self.vtable_ptrs;
>     let vtables = self.prog.vtables;
>     move |ptr| {
>         let (name, _) = ptrs.iter().find(|(_, vtable_ptr)| *vtable_ptr == ptr).unwrap();
>         let vtable = vtables[name];
>         vtable
>     }
> }" -/
def vtableLookup (m : Mach) (ptr : Ptr) : Interp VTable := do
  match m.vtable_ptrs.entries.find? (fun (_, (vtablePtr : Ptr)) => decide (vtablePtr = ptr)) with
  | some (name, _) => mapIndex m.prog.vtables name "vtables[name]"
  | none => specPanic "ptrs.iter().find(|(_, vtable_ptr)| *vtable_ptr == ptr).unwrap()"

/-- `Machine::compute_size` (`spec/lang/machine.md`):
> "fn compute_size(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Size {
>     let (size, _) = layout.compute_size_and_align(meta, self.vtable_lookup());
>     size
> }" -/
def computeSize (m : Mach) (layout : LayoutStrategy) (metadata : Option (PointerMeta Prov)) :
    Interp Size := do
  let (size, _) ← LayoutStrategy.compute_size_and_align (vtableLookup m) layout metadata
  pure size

/-- `Machine::compute_align` (`spec/lang/machine.md`):
> "fn compute_align(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Align {
>     let (_, align) = layout.compute_size_and_align(meta, self.vtable_lookup());
>     align
> }" -/
def computeAlign (m : Mach) (layout : LayoutStrategy) (metadata : Option (PointerMeta Prov)) :
    Interp Align := do
  let (_, align) ← LayoutStrategy.compute_size_and_align (vtableLookup m) layout metadata
  pure align

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

/-- `Machine::transmute` (`spec/lang/representation.md`), which reinterprets
the bytes of `val : type1` at `type2`; it never inspects the value directly:
> "fn transmute(&self, val: Value<M>, type1: Type, type2: Type) -> Result<Value<M>> {
>     assert!(
>         type1.layout::<M::T>().expect_size(\"WF ensures sized operands\")
>             == type2.layout::<M::T>().expect_size(\"WF ensures sized operands\")
>     );
>     let bytes = type1.encode::<M>(val);
>     if let Some(raw_value) = type2.decode::<M>(bytes) {
>         self.check_value(raw_value, type2)?;
>         ret(raw_value)
>     } else {
>         throw_ub!(\"transmuted value is not valid at new type\")
>     }
> }" -/
def transmute (val : Val) (type1 type2 : «Type») : Interp Val := do
  let size1 ← LayoutStrategy.expect_size (← Type.layout type1) "WF ensures sized operands"
  let size2 ← LayoutStrategy.expect_size (← Type.layout type2) "WF ensures sized operands"
  if size1 ≠ size2 then specPanic "assertion failed: transmute between types of different size"
  else do
    let bytes ← Type.encode type1 val
    match ← Type.decode type2 bytes with
    | some rawValue => do checkValue rawValue type2; pure rawValue
    | none => ub "transmuted value is not valid at new type"

/-! ## Places and values (`spec/lang/step/expressions.md`) -/

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
  if !inBounds offset .Signed x86_64.PTR_SIZE then
    specPanic "assertion failed: offset.in_bounds(Signed, M::T::PTR_SIZE)"
  else if !inBounds (ptr.addr + offset) .Unsigned x86_64.PTR_SIZE then
    specPanic "assertion failed: (ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE)"
  else
    pure { ptr with addr := ptr.addr + offset }

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

/-- `Machine::eval_constant` (`spec/lang/step/expressions.md`):
> "fn eval_constant(&mut self, constant: Constant) -> Result<Value<M>> {
>     ret(match constant {
>         Constant::Int(i) => Value::Int(i),
>         Constant::Bool(b) => Value::Bool(b),
>         Constant::GlobalPointer(relocation) => {
>             let ptr = self.global_ptrs[relocation.name].wrapping_offset::<M::T>(relocation.offset.bytes());
>             Value::Ptr(ptr.widen(None))
>         },
>         Constant::FnPointer(fn_name) => {
>             let ptr = self.fn_ptrs[fn_name];
>             Value::Ptr(ptr.widen(None))
>         },
>         Constant::VTablePointer(vtable_name) => {
>             let ptr = self.vtable_ptrs[vtable_name];
>             Value::Ptr(ptr.widen(None))
>         },
>         Constant::PointerWithoutProvenance(addr) => {
>             Value::Ptr(ThinPointer {
>                 addr,
>                 provenance: None,
>             }.widen(None))
>         }
>     })
> }" -/
def evalConstant (m : Mach) : Constant → Interp Val
  | .Int i => pure (.Int i)
  | .Bool b => pure (.Bool b)
  | .GlobalPointer relocation => do
    let base ← mapIndex m.global_ptrs relocation.name "self.global_ptrs[relocation.name]"
    let ptr := ThinPointer.wrapping_offset base relocation.offset.bytes
    pure (.Ptr (ThinPointer.widen ptr none))
  | .FnPointer fnName => do
    let ptr ← mapIndex m.fn_ptrs fnName "self.fn_ptrs[fn_name]"
    pure (.Ptr (ThinPointer.widen ptr none))
  | .VTablePointer vtableName => do
    let ptr ← mapIndex m.vtable_ptrs vtableName "self.vtable_ptrs[vtable_name]"
    pure (.Ptr (ThinPointer.widen ptr none))
  | .PointerWithoutProvenance addr =>
    pure (.Ptr (ThinPointer.widen { addr := addr, provenance := none } none))

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

/-- `Machine::eval_cast_op` for both `CastOp` variants (`spec/lang/step/operators.md`):
> "fn eval_cast_op(&self, cast_op: CastOp, (operand, old_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
>     use CastOp::*;
>     match cast_op {
>         IntToInt(int_ty) => {
>             let Value::Int(operand) = operand else { panic!(\"non-integer input to int-to-int cast\") };
>             let result = int_ty.bring_in_bounds(operand);
>             ret((Value::Int(result), Type::Int(int_ty)))
>         }
>         Transmute(new_ty) => {
>             if old_ty.layout::<M::T>().expect_size(\"WF ensures transmutes are sized\")
>                 != new_ty.layout::<M::T>().expect_size(\"WF ensures transmutes are sized\")
>             {
>                 throw_ub!(\"transmute between types of different size\")
>             }
>             let val = self.transmute(operand, old_ty, new_ty)?;
>             ret((val, new_ty))
>         }
>     }
> }" -/
def evalCastOp (castOp : CastOp) (arg : Val × «Type») : Interp (Val × «Type») :=
  match castOp, arg with
  | .IntToInt intTy, (.Int operand, _) =>
    pure (.Int (IntType.bring_in_bounds intTy operand), .Int intTy)
  | .IntToInt _, _ => specPanic "non-integer input to int-to-int cast"
  | .Transmute newTy, (operand, oldTy) => do
    let oldSize ← LayoutStrategy.expect_size (← Type.layout oldTy) "WF ensures transmutes are sized"
    let newSize ← LayoutStrategy.expect_size (← Type.layout newTy) "WF ensures transmutes are sized"
    if oldSize ≠ newSize then ub "transmute between types of different size"
    else do
      let val ← transmute operand oldTy newTy
      pure (val, newTy)

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

/-- The arithmetic operation of `Machine::eval_bin_op` for
`BinOp::IntWithOverflow` (`spec/lang/step/operators.md`):
> "let result = match op {
>     IntBinOpWithOverflow::Add => left + right,
>     IntBinOpWithOverflow::Sub => left - right,
>     IntBinOpWithOverflow::Mul => left * right,
> };" -/
def evalIntBinOpWithOverflow (op : IntBinOpWithOverflow) (left right : Int) : Int :=
  match op with
  | .Add => left + right
  | .Sub => left - right
  | .Mul => left * right

/-- `Machine::eval_rel_op` (`spec/lang/step/operators.md`), which turns the
outcome of a comparison into the result value:
> "fn eval_rel_op(rel: RelOp, ord: std::cmp::Ordering) -> (Value<M>, Type) {
>     use RelOp::*;
>     match rel {
>         Lt => (Value::Bool(ord.is_lt()), Type::Bool),
>         Gt => (Value::Bool(ord.is_gt()), Type::Bool),
>         Le => (Value::Bool(ord.is_le()), Type::Bool),
>         Ge => (Value::Bool(ord.is_ge()), Type::Bool),
>         Eq => (Value::Bool(ord.is_eq()), Type::Bool),
>         Ne => (Value::Bool(ord.is_ne()), Type::Bool),
>         Cmp => {
>             let val = match ord {
>                 std::cmp::Ordering::Less => -1,
>                 std::cmp::Ordering::Equal => 0,
>                 std::cmp::Ordering::Greater => 1,
>             };
>             (Value::Int(Int::from(val)), Type::Int(IntType::I8))
>         }
>     }
> }"
Rust's `Ordering::is_le` is `!is_gt` and `is_ge` is `!is_lt`, which are
Lean's `Ordering.isLE` and `Ordering.isGE`. -/
def evalRelOp (rel : RelOp) (ord : Ordering) : Val × «Type» :=
  match rel with
  | .Lt => (.Bool ord.isLT, .Bool)
  | .Gt => (.Bool ord.isGT, .Bool)
  | .Le => (.Bool ord.isLE, .Bool)
  | .Ge => (.Bool ord.isGE, .Bool)
  | .Eq => (.Bool ord.isEq, .Bool)
  | .Ne => (.Bool ord.isNe, .Bool)
  | .Cmp =>
    let val : Int := match ord with
      | .lt => -1
      | .eq => 0
      | .gt => 1
    (.Int val, .Int IntType.I8)

/-- `Machine::eval_bin_op` for `BinOp::Int`, `BinOp::IntWithOverflow`, and
`BinOp::Rel` (`spec/lang/step/operators.md`):
> "let Type::Int(int_ty) = l_ty else { panic!(\"non-integer input to integer operation\") };
>  let Value::Int(left) = left else { panic!(..) };
>  let Value::Int(right) = right else { panic!(..) };
>  // Perform the operation.
>  let result = Self::eval_int_bin_op(op, left, right, int_ty)?;
>  // Put the result into the right range (in case of overflow).
>  let result = int_ty.bring_in_bounds(result);
>  ret((Value::Int(result), Type::Int(int_ty)))"
for `BinOp::IntWithOverflow`:
> "fn eval_bin_op(
>     &self,
>     BinOp::IntWithOverflow(op): BinOp,
>     (left, l_ty): (Value<M>, Type),
>     (right, _r_ty): (Value<M>, Type)
> ) -> Result<(Value<M>, Type)> {
>     let Type::Int(int_ty) = l_ty else { panic!(\"non-integer input to integer operation\") };
>     let Value::Int(left) = left else { panic!(\"non-integer input to integer operation\") };
>     let Value::Int(right) = right else { panic!(\"non-integer input to integer operation\") };
>
>     // Perform the operation.
>     let result = match op {
>         IntBinOpWithOverflow::Add => left + right,
>         IntBinOpWithOverflow::Sub => left - right,
>         IntBinOpWithOverflow::Mul => left * right,
>     };
>     let overflow = !int_ty.can_represent(result);
>     // Put the result into the right range (in case of overflow).
>     let result = int_ty.bring_in_bounds(result);
>     // Pack result and overflow bool into tuple.
>     let value = Value::Tuple(list![Value::Int::<M>(result), Value::Bool::<M>(overflow)]);
>     let ty = int_ty.with_overflow::<M::T>();
>     ret((value, ty))
> }"
and, for `BinOp::Rel`:
> "fn eval_bin_op(
>     &self,
>     BinOp::Rel(rel_op): BinOp,
>     (left, l_ty): (Value<M>, Type),
>     (right, _r_ty): (Value<M>, Type)
> ) -> Result<(Value<M>, Type)> {
>     let ord = match (l_ty, left, right) {
>         (Type::Int(_), Value::Int(left), Value::Int(right)) => {
>             left.cmp(&right)
>         }
>         (Type::Bool, Value::Bool(left), Value::Bool(right)) => {
>             left.cmp(&right)
>         }
>         (Type::Ptr(_), Value::Ptr(left), Value::Ptr(right)) => {
>             Self::compare_ptr(left, right)
>         }
>         _ => panic!(\"relational operator on incomparable type or value-type mismatch\"),
>     };
>     ret(Self::eval_rel_op(rel_op, ord))
> }"
Integers compare as mathematical integers (`intCmp`), so a signed operand is
ordered by its value, not by its bit pattern; Booleans compare with
`false < true` (`boolCmp`). Pointer comparison is outside the fragment. -/
def evalBinOp (op : BinOp) (l : Val × «Type») (r : Val × «Type») : Interp (Val × «Type») :=
  match op, l, r with
  | .Int op, (.Int left, .Int intTy), (.Int right, _) => do
    let result ← evalIntBinOp op left right intTy
    pure (.Int (IntType.bring_in_bounds intTy result), .Int intTy)
  | .Int _, _, _ => specPanic "non-integer input to integer operation"
  | .IntWithOverflow op, (.Int left, .Int intTy), (.Int right, _) => do
    let result := evalIntBinOpWithOverflow op left right
    let overflow := !IntType.can_represent intTy result
    let result := IntType.bring_in_bounds intTy result
    let value : Val := .Tuple [.Int result, .Bool overflow]
    let ty ← IntType.with_overflow intTy
    pure (value, ty)
  | .IntWithOverflow _, _, _ => specPanic "non-integer input to integer operation"
  | .Rel relOp, (left, lTy), (right, _) =>
    match lTy, left, right with
    | .Int _, .Int left, .Int right => pure (evalRelOp relOp (intCmp left right))
    | .Bool, .Bool left, .Bool right => pure (evalRelOp relOp (boolCmp left right))
    | .Ptr _, .Ptr _, .Ptr _ => unsupported "BinOp::Rel on pointers (compare_ptr)"
    | _, _, _ => specPanic "relational operator on incomparable type or value-type mismatch"
  | _, _, _ => unsupported "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel"

/-! ## Place and value expressions (`spec/lang/step/expressions.md`) -/

/-- The pointer checks and alignment computation of `Machine::eval_place` for
`PlaceExpr::Deref` once its operand has evaluated to `Value::Ptr(ptr)` at
`Type::Ptr(ptr_type)` (`spec/lang/step/expressions.md`):
> "if let Some(pointee) = ptr_type.safe_pointee() {
>      assert!(self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr));
>      self.mem.dereferenceable(ptr.thin_pointer, self.compute_size(pointee.layout, ptr.metadata))?;
>  }
>  let aligned = self.compute_align(ty.layout::<M::T>(), ptr.metadata).is_aligned(ptr.thin_pointer.addr);
>  ret((Place { ptr, aligned }, ty))"
Neither step changes the machine (`dereferenceable` only reads memory). -/
def derefPlace (m : Mach) (ptr : Pointer Prov) (ptrType : PtrType) (ty : «Type») :
    Interp (Place BM × «Type») := do
  match PtrType.safe_pointee ptrType with
  | some pointee => do
    let ptAlign ← computeAlign m pointee.layout ptr.metadata
    if !Align.is_aligned ptAlign ptr.thin_pointer.addr then
      specPanic "assertion failed: self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr)"
    else do
      let ptSize ← computeSize m pointee.layout ptr.metadata
      CM.dereferenceable m.mem ptr.thin_pointer ptSize
  | none => pure ()
  let placeAlign ← computeAlign m (← Type.layout ty) ptr.metadata
  let aligned := Align.is_aligned placeAlign ptr.thin_pointer.addr
  pure ({ ptr := ptr, aligned := aligned }, ty)

/-- The projection of `Machine::eval_place` for `PlaceExpr::Field` once the
root place `root` of type `ty` is known (`spec/lang/step/expressions.md`):
> "let (offset, field_ty) = match ty {
>      Type::Tuple { sized_fields, unsized_field, sized_head_layout } => {
>          if field >= 0 && field < sized_fields.len() {
>              sized_fields[field]
>          } else if field == sized_fields.len() {
>              let tail_ty = unsized_field.expect(\"field projection to non-existing unsized tail\");
>              let tail_align = self.compute_align(tail_ty.layout::<M::T>(), root.ptr.metadata);
>              let offset = sized_head_layout.tail_offset(tail_align);
>              (offset, tail_ty)
>          } else {
>              panic!(\"field projection to invalid field\");
>          }
>      }
>      Type::Union { fields, .. } => fields[field],
>      _ => panic!(\"field projection on non-projectable type\"),
>  };
>  assert!(offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata));
>
>  let ptr = self.ptr_offset_inbounds(root.ptr.thin_pointer, offset.bytes())?;
>  let ptr = if !field_ty.layout::<M::T>().is_sized() {
>      // Unsized fields should retain the metadata
>      ptr.widen(root.ptr.metadata)
>  } else {
>      ptr.widen(None)
>  };
>  ret((Place { ptr, ..root }, field_ty))"
None of these steps changes the machine. -/
def fieldPlace (m : Mach) (root : Place BM) (ty : «Type») (field : Int) :
    Interp (Place BM × «Type») := do
  let (offset, fieldTy) ← match ty with
    | .Tuple sizedFields sizedHeadLayout unsizedField =>
      if 0 ≤ field ∧ field < (sizedFields.length : Int) then
        listIndex sizedFields field "sized_fields[field]"
      else if field = (sizedFields.length : Int) then
        match unsizedField with
        | none => specPanic "field projection to non-existing unsized tail"
        | some tailTy => do
          let tailAlign ← computeAlign m (← Type.layout tailTy) root.ptr.metadata
          let offset := TupleHeadLayout.tail_offset sizedHeadLayout tailAlign
          pure (offset, tailTy)
      else
        specPanic "field projection to invalid field"
    | .Union fields _ _ _ => listIndex fields field "fields[field]"
    | _ => specPanic "field projection on non-projectable type"
  let rootSize ← computeSize m (← Type.layout ty) root.ptr.metadata
  if !(offset.bytes ≤ rootSize.bytes) then
    specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
  else do
    let ptr ← ptrOffsetInbounds m root.ptr.thin_pointer (offset.bytes : Int)
    let ptr := if !LayoutStrategy.is_sized (← Type.layout fieldTy) then
        ThinPointer.widen ptr root.ptr.metadata
      else
        ThinPointer.widen ptr none
    pure ({ root with ptr := ptr }, fieldTy)

mutual

/-- `Machine::eval_place` for `PlaceExpr::Local`, `PlaceExpr::Deref`, and
`PlaceExpr::Field` (`spec/lang/step/expressions.md`):
> "let ty = self.cur_frame().func.locals[name];
>  let Some(ptr) = self.cur_frame().locals.get(name) else {
>      throw_ub!(\"access to a dead local\");
>  };
>  ret((Place { ptr: ptr.widen(None), aligned: true }, ty))"
> "fn eval_place(&mut self, PlaceExpr::Deref { operand, ty }: PlaceExpr) -> Result<(Place<M>, Type)> {
>     let (Value::Ptr(ptr), Type::Ptr(ptr_type)) = self.eval_value(operand)? else {
>         panic!(\"dereferencing a non-pointer\")
>     };
>     if let Some(pointee) = ptr_type.safe_pointee() {
>         assert!(self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr));
>         self.mem.dereferenceable(ptr.thin_pointer, self.compute_size(pointee.layout, ptr.metadata))?;
>     }
>     let aligned = self.compute_align(ty.layout::<M::T>(), ptr.metadata).is_aligned(ptr.thin_pointer.addr);
>     ret((Place { ptr, aligned }, ty))
> }"
> "fn eval_place(&mut self, PlaceExpr::Field { root, field }: PlaceExpr) -> Result<(Place<M>, Type)> {
>     let (root, ty) = self.eval_place(root)?;
>     let (offset, field_ty) = match ty {
>         Type::Tuple { sized_fields, unsized_field, sized_head_layout } => {
>             if field >= 0 && field < sized_fields.len() {
>                 sized_fields[field]
>             } else if field == sized_fields.len() {
>                 let tail_ty = unsized_field.expect(\"field projection to non-existing unsized tail\");
>                 let tail_align = self.compute_align(tail_ty.layout::<M::T>(), root.ptr.metadata);
>                 let offset = sized_head_layout.tail_offset(tail_align);
>                 (offset, tail_ty)
>             } else {
>                 panic!(\"field projection to invalid field\");
>             }
>         }
>         Type::Union { fields, .. } => fields[field],
>         _ => panic!(\"field projection on non-projectable type\"),
>     };
>     assert!(offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata));
>
>     let ptr = self.ptr_offset_inbounds(root.ptr.thin_pointer, offset.bytes())?;
>     let ptr = if !field_ty.layout::<M::T>().is_sized() {
>         // Unsized fields should retain the metadata
>         ptr.widen(root.ptr.metadata)
>     } else {
>         ptr.widen(None)
>     };
>     ret((Place { ptr, ..root }, field_ty))
> }"
`eval_place` takes `&mut self` because `PlaceExpr::Deref` evaluates its
operand with `eval_value`, which may record memory accesses, so the
interpretation threads the machine through; the checks after the operand are
`derefPlace`, and the projection after the root of a `PlaceExpr::Field` is
`fieldPlace`. `PlaceExpr::Local` and `PlaceExpr::Field` return the machine
unchanged. -/
def evalPlace (m : Mach) : PlaceExpr → Interp ((Place BM × «Type») × Mach)
  | .Local name => do
    let fr ← curFrame m
    let ty ← mapIndex fr.func.locals name "self.cur_frame().func.locals[name]"
    match mapGet fr.locals name with
    | none => ub "access to a dead local"
    | some ptr => pure (({ ptr := ThinPointer.widen ptr none, aligned := true }, ty), m)
  | .Deref operand ty => do
    let ((val, opTy), m) ← evalValue m operand
    match val, opTy with
    | .Ptr ptr, .Ptr ptrType => do
      let r ← derefPlace m ptr ptrType ty
      pure (r, m)
    | _, _ => specPanic "dereferencing a non-pointer"
  | .Field root field => do
    let ((root, ty), m) ← evalPlace m root
    let r ← fieldPlace m root ty field
    pure (r, m)
  | _ => unsupported "eval_place for a place expression other than Local, Deref, or Field"

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
  | .Constant c ty => do pure ((← evalConstant m c, ty), m)
  | .Tuple exprs ty => do
    let (vals, m) ← evalValues m exprs
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

/-- The element loop of `Machine::eval_value` for `ValueExpr::Tuple`
(`spec/lang/step/expressions.md`):
> "let vals = exprs.try_map(|e| self.eval_value(e))?.map(|e| e.0);" -/
def evalValues (m : Mach) : List ValueExpr → Interp (List Val × Mach)
  | [] => pure ([], m)
  | e :: es => do
    let ((val, _), m) ← evalValue m e
    let (vals, m) ← evalValues m es
    pure (val :: vals, m)

end

/-! ## Statements (`spec/lang/step/statements.md`) -/

/-- `ConcurrentMemory::deinit` (`spec/lang/step/statements.md`):
> "fn deinit(&mut self, ptr: ThinPointer<M::Provenance>, len: Size, align: Align) -> Result {
>     self.store(ptr, list![AbstractByte::Uninit; len.bytes()], align, Atomicity::None)?;
>     ret(())
> }" -/
def CM.deinit (cm : ConcurrentMemory BM) (ptr : Ptr) (len : Size) (align : Align) :
    Interp (ConcurrentMemory BM) :=
  CM.store cm ptr (List.replicate len.bytes .Uninit) align .None

/-- `StackFrame::storage_dead` (`spec/lang/step/statements.md`):
> "fn storage_dead(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult {
>     let pointee_size = self.func.locals[local].layout::<M::T>().expect_size(\"WF ensures all locals are sized\");
>     let pointee_align = self.func.locals[local].layout::<M::T>().expect_align(\"WF ensures all locals are sized\");
>     if let Some(ptr) = self.locals.remove(local) {
>         mem.deallocate(ptr, AllocationKind::Stack, pointee_size, pointee_align)?;
>     }
>     ret(())
> }" -/
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

/-- `StackFrame::storage_live` (`spec/lang/step/statements.md`):
> "fn storage_live(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult {
>     // First remove the old storage, if any.
>     // This means the same address may be re-used for the new stoage.
>     self.storage_dead(mem, local)?;
>     // Then allocate the new storage.
>     let pointee_size = self.func.locals[local].layout::<M::T>().expect_size(\"WF ensures all locals are sized\");
>     let pointee_align = self.func.locals[local].layout::<M::T>().expect_align(\"WF ensures all locals are sized\");
>     let ptr = mem.allocate(AllocationKind::Stack, pointee_size, pointee_align)?;
>     self.locals.insert(local, ptr);
>     ret(())
> }" -/
def storageLive (fr : Frame) (cm : ConcurrentMemory BM) (local_ : LocalName) :
    Interp (Frame × ConcurrentMemory BM) := do
  let (fr2, cm2) ← storageDead fr cm local_
  let ty ← mapIndex fr2.func.locals local_ "self.func.locals[local]"
  let layout ← Type.layout ty
  let size ← LayoutStrategy.expect_size layout "WF ensures all locals are sized"
  let align ← LayoutStrategy.expect_align layout "WF ensures all locals are sized"
  let (ptr, cm3) ← CM.allocate cm2 .Stack size align
  let locals := mapInsertMap fr2.locals local_ ptr
  pure ({ fr2 with locals := locals }, cm3)

/-- `Machine::eval_statement` for `Statement::Assign`, `Statement::PlaceMention`,
`Statement::Deinit`, `Statement::StorageLive`, and `Statement::StorageDead`
(`spec/lang/step/statements.md`):
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
> }
> ..
> fn eval_statement(&mut self, Statement::Deinit { place }: Statement) -> NdResult {
>     let (p, ty) = self.eval_place(place)?;
>     if !p.aligned {
>         throw_ub!(\"de-initializing a place based on a misaligned pointer\");
>     }
>     // Alignment was already checked.
>     self.mem.deinit(p.ptr.thin_pointer, ty.layout::<M::T>().expect_size(\"WF ensures deinits are sized\"), Align::ONE)?;
>
>     ret(())
> }
> ..
> fn eval_statement(&mut self, Statement::StorageLive(local): Statement) -> NdResult {
>     self.try_mutate_cur_frame(|frame, mem| {
>         frame.storage_live(mem, local)
>     })
> }
>
> fn eval_statement(&mut self, Statement::StorageDead(local): Statement) -> NdResult {
>     self.try_mutate_cur_frame(|frame, mem| {
>         frame.storage_dead(mem, local)
>     })
> }" -/
def evalStatement (m : Mach) : Statement → Interp Mach
  | .Assign destination source => do
    let ((place, ty), m) ← evalPlace m destination
    let ((val, _), m) ← evalValue m source
    placeStore m place val ty
  | .PlaceMention place => do
    let (_, m) ← evalPlace m place
    pure m
  | .StorageLive local_ =>
    tryMutateCurFrame m (fun fr cm => storageLive fr cm local_)
  | .StorageDead local_ =>
    tryMutateCurFrame m (fun fr cm => storageDead fr cm local_)
  | .Deinit place => do
    let ((p, ty), m) ← evalPlace m place
    if !p.aligned then ub "de-initializing a place based on a misaligned pointer"
    else do
      let layout ← Type.layout ty
      let size ← LayoutStrategy.expect_size layout "WF ensures deinits are sized"
      let cm ← CM.deinit m.mem p.ptr.thin_pointer size ⟨1⟩
      pure { m with mem := cm }
  | _ => unsupported "eval_statement for a statement other than Assign/PlaceMention/StorageLive/StorageDead/Deinit"

/-! ## Terminators (`spec/lang/step/terminators.md`) -/

mutual

/-- Structural equality `caller_discriminator == callee_discriminator` on
`Discriminator` decision trees in `check_abi_compatibility`
(`spec/lang/step/terminators.md`), comparing `Branch` child maps extensionally:
> "caller_discriminator == callee_discriminator &&" -/
def discriminatorEq : Discriminator → Discriminator → Bool
  | .Known v1, .Known v2 => v1 == v2
  | .Invalid, .Invalid => true
  | .Branch off1 ty1 fb1 ⟨ch1⟩, .Branch off2 ty2 fb2 ch2 =>
    off1 == off2 && ty1 == ty2 && discriminatorEq fb1 fb2 &&
    discriminatorChildrenEq [] ch1 ch2 &&
    ch2.entries.all (fun (k, _) => (mapGet ⟨ch1⟩ k).isSome)
  | _, _ => false

/-- Child-map comparison of `discriminatorEq` (`spec/lang/step/terminators.md`),
checking each active `(start, end)` binding of `ch1` against `ch2`:
> "caller_discriminator == callee_discriminator &&" -/
def discriminatorChildrenEq (seen : List (Int × Int)) :
    List ((Int × Int) × Discriminator) → Map (Int × Int) Discriminator → Bool
  | [], _ => true
  | (k, d1) :: rest, ch2 =>
    if seen.contains k then
      discriminatorChildrenEq seen rest ch2
    else
      (match mapGet ch2 k with
       | some d2 => discriminatorEq d1 d2
       | none => false) &&
      discriminatorChildrenEq (k :: seen) rest ch2

end

mutual

/-- `check_abi_compatibility` (`spec/lang/step/terminators.md`):
> "fn check_abi_compatibility(
>     caller_ty: Type,
>     callee_ty: Type,
> ) -> bool {
>     match (caller_ty, callee_ty) {
>         (Type::Int(caller_ty), Type::Int(callee_ty)) =>
>             caller_ty == callee_ty,
>         (Type::Bool, Type::Bool) =>
>             true,
>         (Type::Ptr(caller_ty), Type::Ptr(callee_ty)) =>
>             caller_ty.meta_kind() == callee_ty.meta_kind(),
>         (Type::Tuple { sized_fields: caller_fields, sized_head_layout: caller_head_layout, unsized_field: caller_unsized_field },
>          Type::Tuple { sized_fields: callee_fields, sized_head_layout: callee_head_layout, unsized_field: callee_unsized_field }) => {
>             let (caller_size, caller_align) = caller_head_layout.head_size_and_align();
>             let (callee_size, callee_align) = callee_head_layout.head_size_and_align();
>             assert!(caller_unsized_field.is_none(), \"wf ensures all arugments are sized\");
>             assert!(callee_unsized_field.is_none(), \"wf ensures all arugments are sized\");
>             caller_fields.len() == callee_fields.len() &&
>             caller_fields.zip(callee_fields).all(|(caller_field, callee_field)|
>                 caller_field.0 == callee_field.0 && check_abi_compatibility(caller_field.1, callee_field.1)
>             ) &&
>             caller_size == callee_size &&
>             caller_align == callee_align
>         }
>         (Type::Array { elem: caller_elem, count: caller_count },
>          Type::Array { elem: callee_elem, count: callee_count }) =>
>             check_abi_compatibility(caller_elem, callee_elem) && caller_count == callee_count,
>         (Type::Union { fields: caller_fields, chunks: caller_chunks, size: caller_size, align: caller_align },
>          Type::Union { fields: callee_fields, chunks: callee_chunks, size: callee_size, align: callee_align }) =>
>             caller_fields.len() == callee_fields.len() &&
>             caller_fields.zip(callee_fields).all(|(caller_field, callee_field)|
>                 caller_field.0 == callee_field.0 && check_abi_compatibility(caller_field.1, callee_field.1)
>             ) &&
>             caller_chunks == callee_chunks &&
>             caller_size == callee_size &&
>             caller_align == callee_align,
>         (Type::Enum { variants: caller_variants, discriminator: caller_discriminator, discriminant_ty: caller_discriminant_ty, size: caller_size, align: caller_align },
>          Type::Enum { variants: callee_variants, discriminator: callee_discriminator, discriminant_ty: callee_discriminant_ty, size: callee_size, align: callee_align }) =>
>             caller_variants.len() == callee_variants.len() &&
>             caller_variants.iter().all(|(caller_discriminant, caller_variant)| {
>                 let Some(callee_variant) = callee_variants.get(caller_discriminant) else {
>                     return false;
>                 };
>                 check_abi_compatibility(caller_variant.ty, callee_variant.ty) &&
>                 caller_variant.tagger == callee_variant.tagger
>             }) &&
>             caller_discriminator == callee_discriminator &&
>             caller_discriminant_ty == callee_discriminant_ty &&
>             caller_size == callee_size &&
>             caller_align == callee_align,
>         _ =>
>             false
>     }
> }" -/
def checkAbiCompatibility : «Type» → «Type» → Interp Bool
  | .Int callerTy, .Int calleeTy => pure (callerTy == calleeTy)
  | .Bool, .Bool => pure true
  | .Ptr callerTy, .Ptr calleeTy =>
    pure (PtrType.meta_kind callerTy == PtrType.meta_kind calleeTy)
  | .Tuple callerFields callerHeadLayout callerUnsizedField,
    .Tuple calleeFields calleeHeadLayout calleeUnsizedField =>
    let (callerSize, callerAlign) := TupleHeadLayout.head_size_and_align callerHeadLayout
    let (calleeSize, calleeAlign) := TupleHeadLayout.head_size_and_align calleeHeadLayout
    if callerUnsizedField.isSome then
      specPanic "wf ensures all arugments are sized"
    else if calleeUnsizedField.isSome then
      specPanic "wf ensures all arugments are sized"
    else if callerFields.length ≠ calleeFields.length then
      pure false
    else do
      if !(← checkAbiFields callerFields calleeFields) then
        pure false
      else
        pure (callerSize == calleeSize && callerAlign == calleeAlign)
  | .Array callerElem callerCount, .Array calleeElem calleeCount => do
    if !(← checkAbiCompatibility callerElem calleeElem) then
      pure false
    else
      pure (callerCount == calleeCount)
  | .Union callerFields callerChunks callerSize callerAlign,
    .Union calleeFields calleeChunks calleeSize calleeAlign =>
    if callerFields.length ≠ calleeFields.length then
      pure false
    else do
      if !(← checkAbiFields callerFields calleeFields) then
        pure false
      else
        pure (callerChunks == calleeChunks && callerSize == calleeSize && callerAlign == calleeAlign)
  | .Enum ⟨callerVariants⟩ callerDiscrTy callerDiscriminator callerSize callerAlign,
    .Enum calleeVariants calleeDiscrTy calleeDiscriminator calleeSize calleeAlign =>
    if mapLen ⟨callerVariants⟩ ≠ mapLen calleeVariants then
      pure false
    else do
      if !(← checkAbiVariants [] callerVariants calleeVariants) then
        pure false
      else
        pure (discriminatorEq callerDiscriminator calleeDiscriminator &&
          callerDiscrTy == calleeDiscrTy &&
          callerSize == calleeSize &&
          callerAlign == calleeAlign)
  | _, _ => pure false

/-- The field-list comparison of `check_abi_compatibility` for `Tuple` and
`Union` (`spec/lang/step/terminators.md`):
> "caller_fields.zip(callee_fields).all(|(caller_field, callee_field)|
>     caller_field.0 == callee_field.0 && check_abi_compatibility(caller_field.1, callee_field.1)
> )" -/
def checkAbiFields : List (Offset × «Type») → List (Offset × «Type») → Interp Bool
  | (callerOff, callerTy) :: restCaller, (calleeOff, calleeTy) :: restCallee =>
    if callerOff ≠ calleeOff then
      pure false
    else do
      if !(← checkAbiCompatibility callerTy calleeTy) then
        pure false
      else
        checkAbiFields restCaller restCallee
  | _, _ => pure true

/-- The variant-map comparison of `check_abi_compatibility` for `Enum`
(`spec/lang/step/terminators.md`):
> "caller_variants.iter().all(|(caller_discriminant, caller_variant)| {
>     let Some(callee_variant) = callee_variants.get(caller_discriminant) else {
>         return false;
>     };
>     check_abi_compatibility(caller_variant.ty, callee_variant.ty) &&
>     caller_variant.tagger == callee_variant.tagger
> })" -/
def checkAbiVariants (seen : List Int) :
    List (Int × Variant) → Map Int Variant → Interp Bool
  | [], _ => pure true
  | (callerDiscr, ⟨callerVarTy, callerTagger⟩) :: rest, calleeVariants =>
    if seen.contains callerDiscr then
      checkAbiVariants seen rest calleeVariants
    else
      match mapGet calleeVariants callerDiscr with
      | none => pure false
      | some calleeVariant => do
        if !(← checkAbiCompatibility callerVarTy calleeVariant.ty) then
          pure false
        else if !mapEq (· == ·) callerTagger calleeVariant.tagger then
          pure false
        else
          checkAbiVariants (callerDiscr :: seen) rest calleeVariants

end

/-- `Machine::prepare_for_inplace_passing` (`spec/lang/step/terminators.md`):
> "fn prepare_for_inplace_passing(
>     &mut self,
>     place: Place<M>,
>     ty: Type,
> ) -> NdResult {
>     self.mem.deinit(
>         place.ptr.thin_pointer,
>         ty.layout::<M::T>().expect_size(\"WF ensures arguments and return types are sized\"),
>         ty.layout::<M::T>().expect_align(\"WF ensures arguments and return types are sized\")
>     )?;
>     ret(())
> }" -/
def prepareForInplacePassing (m : Mach) (place : Place BM) (ty : «Type») : Interp Mach := do
  let size ← LayoutStrategy.expect_size (← Type.layout ty)
    "WF ensures arguments and return types are sized"
  let align ← LayoutStrategy.expect_align (← Type.layout ty)
    "WF ensures arguments and return types are sized"
  let cm ← CM.deinit m.mem place.ptr.thin_pointer size align
  pure { m with mem := cm }

/-- `Machine::eval_argument` (`spec/lang/step/terminators.md`):
> "fn eval_argument(
>     &mut self,
>     val: ArgumentExpr,
> ) -> NdResult<(Value<M>, Type)> {
>     ret(match val {
>         ArgumentExpr::ByValue(value) => {
>             self.eval_value(value)?
>         }
>         ArgumentExpr::InPlace(place) => {
>             let (place, ty) = self.eval_place(place)?;
>             let value = self.place_load(place, ty)?;
>             self.prepare_for_inplace_passing(place, ty)?;
>             (value, ty)
>         }
>     })
> }" -/
def evalArgument (m : Mach) : ArgumentExpr → Interp ((Val × «Type») × Mach)
  | .ByValue value => evalValue m value
  | .InPlace place => do
    let ((place, ty), m) ← evalPlace m place
    let (value, m) ← placeLoad m place ty
    let m ← prepareForInplacePassing m place ty
    pure ((value, ty), m)

/-- The argument evaluation loop of `Terminator::Call`
(`spec/lang/step/terminators.md`):
> "let arguments = arguments.try_map(|arg| self.eval_argument(arg))?;" -/
def evalArguments (m : Mach) : List ArgumentExpr → Interp (List (Val × «Type») × Mach)
  | [] => pure ([], m)
  | arg :: args => do
    let (v, m) ← evalArgument m arg
    let (vs, m) ← evalArguments m args
    pure (v :: vs, m)

/-- The argument-local allocation loop of `Machine::create_frame`
(`spec/lang/step/terminators.md`):
> "for arg_local in func.args {
>     frame.storage_live(&mut self.mem, arg_local)?;
> }" -/
def allocFrameArgs (fr : Frame) (cm : ConcurrentMemory BM) :
    List LocalName → Interp (Frame × ConcurrentMemory BM)
  | [] => pure (fr, cm)
  | argLocal :: rest => do
    let (fr, cm) ← storageLive fr cm argLocal
    allocFrameArgs fr cm rest

/-- The argument-passing and ABI-checking loop of `Machine::create_frame`
(`spec/lang/step/terminators.md`):
> "for (callee_local, (caller_val, caller_ty)) in func.args.zip(caller_args) {
>     if !check_abi_compatibility(caller_ty, func.locals[callee_local]) {
>         throw_ub!(\"call ABI violation: argument types are not compatible\");
>     }
>     let align = caller_ty.layout::<M::T>().expect_align(\"WF ensures function arguments are sized\");
>     self.typed_store(frame.locals[callee_local], caller_val, caller_ty, align, Atomicity::None).unwrap();
> }" -/
def initFrameArgs (m : Mach) (frame : Frame) :
    List LocalName → List (Val × «Type») → Interp Mach
  | calleeLocal :: restLocals, (callerVal, callerTy) :: restArgs => do
    let calleeTy ← mapIndex frame.func.locals calleeLocal "func.locals[callee_local]"
    if !(← checkAbiCompatibility callerTy calleeTy) then
      ub "call ABI violation: argument types are not compatible"
    else do
      let align ← LayoutStrategy.expect_align (← Type.layout callerTy)
        "WF ensures function arguments are sized"
      let calleePtr ← mapIndex frame.locals calleeLocal "frame.locals[callee_local]"
      let m ← match typedStore m calleePtr callerVal callerTy align .None with
        | .ok m => pure m
        | .error (.unsupported w) => unsupported w
        | .error (.specPanic msg) => specPanic msg
        | .error _ => specPanic "self.typed_store(..).unwrap()"
      initFrameArgs m frame restLocals restArgs
  | _, _ => pure m

/-- `Machine::create_frame` (`spec/lang/step/terminators.md`):
> "fn create_frame(
>     &mut self,
>     func: Function,
>     stack_pop_action: StackPopAction<M>,
>     caller_conv: CallingConvention,
>     caller_ret_ty: Type,
>     caller_args: List<(Value<M>, Type)>,
> ) -> NdResult<StackFrame<M>> {
>     let mut frame = StackFrame {
>         func,
>         locals: Map::new(),
>         stack_pop_action,
>         next_block: func.start,
>         next_stmt: Int::ZERO,
>         extra: M::new_call(),
>     };
>     frame.storage_live(&mut self.mem, func.ret)?;
>     for arg_local in func.args {
>         frame.storage_live(&mut self.mem, arg_local)?;
>     }
>     if caller_conv != func.calling_convention {
>         throw_ub!(\"call ABI violation: calling conventions are not the same\");
>     }
>     if !check_abi_compatibility(caller_ret_ty, func.locals[func.ret]) {
>         throw_ub!(\"call ABI violation: return types are not compatible\");
>     }
>     if func.args.len() != caller_args.len() {
>         throw_ub!(\"call ABI violation: number of arguments does not agree\");
>     }
>     ..
>     ret(frame)
> }" -/
def createFrame (m : Mach) (func : Function) (stackPopAction : StackPopAction BM)
    (callerConv : CallingConvention) (callerRetTy : «Type»)
    (callerArgs : List (Val × «Type»)) : Interp (Frame × Mach) := do
  let frame : Frame := {
    func := func
    locals := ⟨[]⟩
    stack_pop_action := stackPopAction
    next_block := func.start
    next_stmt := 0
    extra := ()
  }
  let (frame, cm) ← storageLive frame m.mem func.ret
  let (frame, cm) ← allocFrameArgs frame cm func.args
  let m := { m with mem := cm }
  if callerConv ≠ func.calling_convention then
    ub "call ABI violation: calling conventions are not the same"
  else do
    let calleeRetTy ← mapIndex frame.func.locals frame.func.ret "func.locals[func.ret]"
    if !(← checkAbiCompatibility callerRetTy calleeRetTy) then
      ub "call ABI violation: return types are not compatible"
    else if func.args.length ≠ callerArgs.length then
      ub "call ABI violation: number of arguments does not agree"
    else do
      let m ← initFrameArgs m frame func.args callerArgs
      pure (frame, m)

/-- `Machine::eval_call` (`spec/lang/step/terminators.md`):
> "fn eval_call(
>     &mut self,
>     callee: Function,
>     caller_conv: CallingConvention,
>     arguments: List<(Value<M>, Type)>,
>     caller_ret: (Place<M>, Type),
>     next_block: Option<BbName>,
>     unwind_block: Option<BbName>,
> ) -> NdResult {
>     let (caller_ret_place, caller_ret_ty) = caller_ret;
>     let stack_pop_action = StackPopAction::BackToCaller {
>         next_block,
>         unwind_block,
>         ret_val_ptr: caller_ret_place.ptr.thin_pointer,
>     };
>     let frame = self.create_frame(
>         callee,
>         stack_pop_action,
>         caller_conv,
>         caller_ret_ty,
>         arguments,
>     )?;
>     self.mutate_cur_stack(|stack| stack.push(frame));
>     ret(())
> }" -/
def evalCall (m : Mach) (callee : Function) (callerConv : CallingConvention)
    (arguments : List (Val × «Type»)) (callerRet : Place BM × «Type»)
    (nextBlock : Option BbName) (unwindBlock : Option BbName) : Interp Mach := do
  let (callerRetPlace, callerRetTy) := callerRet
  let stackPopAction : StackPopAction BM :=
    .BackToCaller nextBlock unwindBlock callerRetPlace.ptr.thin_pointer
  let (frame, m) ← createFrame m callee stackPopAction callerConv callerRetTy arguments
  let (_, m) ← mutateCurStack m (fun stack => pure ((), stack ++ [frame]))
  pure m

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

/-! ## Intrinsics (`spec/lang/step/intrinsics.md`) -/

/-- `unit_value` (`spec/lang/step/intrinsics.md`):
> "fn unit_value<M: Memory>() -> Value<M> {
>      Value::Tuple(list![])
>  }" -/
def unitValue : Val :=
  .Tuple []

/-- `unit_type` (`spec/lang/step/intrinsics.md`):
> "fn unit_type() -> Type {
>      Type::Tuple { sized_fields: list![], sized_head_layout: TupleHeadLayout {
>          end: Size::ZERO, align: Align::ONE, packed_align: None,
>      }, unsized_field: None }
>  }" -/
def unitType : «Type» :=
  .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none

/-- `BasicMemory::leak_check` (`spec/mem/basic.md`):
> "fn leak_check(&self) -> Result {
>      use AllocationKind::*;
>      for allocation in self.allocations {
>          if allocation.live {
>              match allocation.kind {
>                  // These should all be gone.
>                  Heap => throw_memory_leak!(),
>                  // These we can still have at the end.
>                  Global | Function | Stack | VTable => {}
>              }
>          }
>      }
>      ret(())
>  }"
which `ConcurrentMemory::leak_check` forwards to (`spec/mem/concurrent.md`):
> "pub fn leak_check(&self) -> Result {
>      self.memory.leak_check()
>  }"
The loop stops at the first live `Heap` allocation; its order is irrelevant
because every iteration either continues or throws the same
`TerminationInfo::MemoryLeak`. -/
def CM.leak_check (cm : ConcurrentMemory BM) : Interp Unit :=
  if cm.memory.allocations.any (fun a => a.live && decide (a.kind = .Heap)) then memoryLeak
  else pure ()

/-- `Machine::exit` (`spec/lang/step/intrinsics.md`):
> "fn exit(&self) -> NdResult<!> {
>      // Check for memory leaks.
>      self.mem.leak_check()?;
>      // No leak found -- good, stop the machine.
>      throw_machine_stop!();
>  }"
`NdResult<!>` never returns normally, so the result type is arbitrary. -/
def machineExit {α : Type} (m : Mach) : Interp α := do
  CM.leak_check m.mem
  machineStop

/-- `Machine::eval_print` (`spec/lang/step/intrinsics.md`):
> "fn eval_print(
>      &mut self,
>      stream: DynWrite,
>      arguments: List<(Value<M>, Type)>,
>  ) -> Result {
>      for (arg, _) in arguments {
>          match arg {
>              Value::Int(i) => write!(stream, \"{}\\n\", i).unwrap(),
>              Value::Bool(b) => write!(stream, \"{}\\n\", b).unwrap(),
>              _ => throw_ub!(\"unsupported value for printing\"),
>          }
>      }
>
>      ret(())
>  }"
`DynWrite` records the written strings (`MiniRustSpec.LibSpecr.DynWrite`), so
the interpretation returns the extended sink; `Display` of a `libspecr::Int`
is its decimal expansion with a leading `-` when negative, which is Lean's
`toString` on `Int`. -/
def evalPrint (stream : DynWrite) : List (Val × «Type») → Interp DynWrite
  | [] => pure stream
  | (arg, _) :: rest =>
    match arg with
    | .Int i => evalPrint ⟨stream.written ++ [toString i ++ "\n"]⟩ rest
    | .Bool b => evalPrint ⟨stream.written ++ [toString b ++ "\n"]⟩ rest
    | _ => ub "unsupported value for printing"

/-- `IntPtrCast::expose` (`spec/mem/intptrcast.md`):
> "pub fn expose(&mut self, ptr: ThinPointer<Provenance>) {
>      if let Some(provenance) = ptr.provenance {
>          // Remember this provenance as having been exposed.
>          self.exposed.insert(provenance);
>      }
>  }" -/
def IntPtrCast.expose (ipc : IntPtrCast Prov) (ptr : Ptr) : IntPtrCast Prov :=
  match ptr.provenance with
  | some provenance => { ipc with exposed := setInsert ipc.exposed provenance }
  | none => ipc

/-- Structural equality on `LayoutStrategy` for `Type` comparison (`l_ty != r_ty`
in `IntrinsicOp::RawEq`, `spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {" -/
def layoutStrategyEq : LayoutStrategy → LayoutStrategy → Bool
  | .Sized s1 a1, .Sized s2 a2 => s1 == s2 && a1 == a2
  | .Slice s1 a1, .Slice s2 a2 => s1 == s2 && a1 == a2
  | .TraitObject t1, .TraitObject t2 => t1 == t2
  | .Tuple h1 t1, .Tuple h2 t2 => h1 == h2 && layoutStrategyEq t1 t2
  | _, _ => false

/-- Structural equality on `UnsafeCellStrategy` for `Type` comparison
(`spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {" -/
def unsafeCellStrategyEq : UnsafeCellStrategy → UnsafeCellStrategy → Bool
  | .Sized c1, .Sized c2 => c1 == c2
  | .Slice c1, .Slice c2 => c1 == c2
  | .TraitObject, .TraitObject => true
  | .Tuple h1 t1, .Tuple h2 t2 => h1 == h2 && unsafeCellStrategyEq t1 t2
  | _, _ => false

/-- Structural equality on `PointeeInfo` for `Type` comparison
(`spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {" -/
def pointeeInfoEq (p1 p2 : PointeeInfo) : Bool :=
  layoutStrategyEq p1.layout p2.layout &&
  p1.inhabited == p2.inhabited &&
  unsafeCellStrategyEq p1.unsafe_cells p2.unsafe_cells &&
  p1.freeze == p2.freeze &&
  p1.unpin == p2.unpin

/-- Structural equality on `PtrType` for `Type` comparison
(`spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {" -/
def ptrTypeEq : PtrType → PtrType → Bool
  | .Ref m1 p1, .Ref m2 p2 => m1 == m2 && pointeeInfoEq p1 p2
  | .Box p1, .Box p2 => pointeeInfoEq p1 p2
  | .Raw k1, .Raw k2 => k1 == k2
  | .FnPtr, .FnPtr => true
  | .VTablePtr t1, .VTablePtr t2 => t1 == t2
  | _, _ => false

mutual

/-- Structural equality `l_ty == r_ty` on MiniRust `Type` values (with
extensional comparison of `Enum` `variants`, `Variant.tagger`, and
`Discriminator` maps), used by `l_ty != r_ty` in `IntrinsicOp::RawEq`
(`spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {
>      throw_ub!(\"invalid arguments to `RawEq` intrinsic: types of arguments are not identical\");
>  }" -/
def typeEq : «Type» → «Type» → Bool
  | .Int t1, .Int t2 => t1 == t2
  | .Bool, .Bool => true
  | .Ptr p1, .Ptr p2 => ptrTypeEq p1 p2
  | .Tuple f1 h1 u1, .Tuple f2 h2 u2 =>
    typeFieldsEq f1 f2 && h1 == h2 && typeOptEq u1 u2
  | .Array e1 c1, .Array e2 c2 => typeEq e1 e2 && c1 == c2
  | .Slice e1, .Slice e2 => typeEq e1 e2
  | .Union f1 ch1 s1 a1, .Union f2 ch2 s2 a2 =>
    typeFieldsEq f1 f2 && ch1 == ch2 && s1 == s2 && a1 == a2
  | .Enum ⟨v1⟩ dt1 disc1 s1 a1, .Enum v2 dt2 disc2 s2 a2 =>
    mapLen ⟨v1⟩ == mapLen v2 &&
    typeVariantsEq [] v1 v2 &&
    dt1 == dt2 &&
    discriminatorEq disc1 disc2 &&
    s1 == s2 &&
    a1 == a2
  | .TraitObject t1, .TraitObject t2 => t1 == t2
  | _, _ => false

/-- Optional unsized-tail comparison for `Type::Tuple` in `typeEq`
(`spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {" -/
def typeOptEq : Option «Type» → Option «Type» → Bool
  | none, none => true
  | some t1, some t2 => typeEq t1 t2
  | _, _ => false

/-- Field-list comparison for `Type::Tuple` and `Type::Union` in `typeEq`
(`spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {" -/
def typeFieldsEq : List (Offset × «Type») → List (Offset × «Type») → Bool
  | [], [] => true
  | (o1, t1) :: r1, (o2, t2) :: r2 => o1 == o2 && typeEq t1 t2 && typeFieldsEq r1 r2
  | _, _ => false

/-- Extensional `Enum` variant-map comparison for `typeEq`
(`spec/lang/step/intrinsics.md`):
> "if l_ty != r_ty {" -/
def typeVariantsEq (seen : List Int) : List (Int × Variant) → Map Int Variant → Bool
  | [], _ => true
  | (d, ⟨vt1, tag1⟩) :: rest, v2 =>
    if seen.contains d then
      typeVariantsEq seen rest v2
    else
      (match mapGet v2 d with
       | some vt2 => typeEq vt1 vt2.ty && mapEq (· == ·) tag1 vt2.tagger
       | none => false) &&
      typeVariantsEq (d :: seen) rest v2

end

/-- `Machine::load_raw_data` (`spec/lang/step/intrinsics.md`):
> "fn load_raw_data(&mut self, ptr : Pointer<<M as Memory>::Provenance>, ptr_ty : PtrType) -> Result<List<u8>> {
>      let PtrType::Ref { pointee, .. } = ptr_ty else {
>          throw_ub!(\"invalid argument to `RawEq` intrinsic: not a reference\");
>      };
>      let PointeeInfo { layout: LayoutStrategy::Sized(size, align), .. } = pointee else {
>          throw_ub!(\"invalid argument to `RawEq` intrinsic: unsized pointee\");
>      };
>      let bytes = self.mem.load(ptr.thin_pointer, size, align, Atomicity::None)?;
>
>      let Some(data) = bytes.try_map(|byte| byte.data()) else {
>          throw_ub!(\"invalid argument to `RawEq` intrinsic: byte is uninitialized\");
>      };
>
>      Ok(data)
>  }" -/
def loadRawData (m : Mach) (ptr : Pointer Prov) (ptrTy : PtrType) :
    Interp (List UInt8 × Mach) :=
  match ptrTy with
  | .Ref _ pointee =>
    match pointee.layout with
    | .Sized size align => do
      let (bytes, cm) ← CM.load m.mem ptr.thin_pointer size align .None
      match bytes.mapM AbstractByte.data with
      | some data => pure (data, { m with mem := cm })
      | none => ub "invalid argument to `RawEq` intrinsic: byte is uninitialized"
    | _ => ub "invalid argument to `RawEq` intrinsic: unsized pointee"
  | _ => ub "invalid argument to `RawEq` intrinsic: not a reference"

/-- `Machine::eval_intrinsic` (`spec/lang/step/intrinsics.md`) for
`PointerExposeProvenance`, `PointerWithExposedProvenance`, `Exit`, `Abort`,
`Assume`, `PrintStdout`, `PrintStderr`, `Allocate`, `Deallocate`, `RawEq`,
and `GetUnwindPayload`:
> "fn eval_intrinsic(&mut self,
>      IntrinsicOp::PointerExposeProvenance: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if arguments.len() != 1 {
>          throw_ub!(\"invalid number of arguments for `PointerExposeProvenance` intrinsic\");
>      }
>      let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
>          throw_ub!(\"invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer\");
>      };
>      if ret_ty != Type::Int(IntType { signed: Unsigned, size: M::T::PTR_SIZE }) {
>          throw_ub!(\"invalid return type for `PointerExposeProvenance` intrinsic\")
>      }
>
>      self.intptrcast.expose(ptr);
>      ret(Value::Int(ptr.addr))
>  }
>
>  fn eval_intrinsic(&mut self,
>      IntrinsicOp::PointerWithExposedProvenance: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if arguments.len() != 1 {
>          throw_ub!(\"invalid number of arguments for `PointerWithExposedProvenance` intrinsic\");
>      }
>      let Value::Int(addr) = arguments[0].0 else {
>          throw_ub!(\"invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer\");
>      };
>      let Type::Ptr(ret_ptr_ty) = ret_ty else {
>          throw_ub!(\"invalid return type for `PointerWithExposedProvenance` intrinsic\");
>      };
>      if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
>          throw_ub!(\"unsized pointee requested for `PointerWithExposedProvenance` intrinsic\");
>      }
>
>      let ptr = self.intptrcast.int2ptr(addr)?;
>      ret(Value::Ptr(ptr.widen(None)))
>  }"
> "fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::Exit: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      self.exit()?
>  }"
> "fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::Abort: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      throw_abort!();
>  }"
> "fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::Assume: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if arguments.len() != 1 {
>          throw_ub!(\"invalid number of arguments for `Assume` intrinsic\");
>      }
>      let Value::Bool(b) = arguments[0].0 else {
>          throw_ub!(\"invalid argument for `Assume` intrinsic: not a Boolean\");
>      };
>      if ret_ty != unit_type() {
>          throw_ub!(\"invalid return type for `Assume` intrinsic\")
>      }
>
>      if !b {
>          throw_ub!(\"`Assume` intrinsic called on condition that is violated\");
>      }
>
>      ret(unit_value())
>  }"
> "fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::PrintStdout: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if ret_ty != unit_type() {
>          throw_ub!(\"invalid return type for `PrintStdout` intrinsic\")
>      }
>
>      self.eval_print(self.stdout, arguments)?;
>
>      ret(unit_value())
>  }
>
>  fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::PrintStderr: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if ret_ty != unit_type() {
>          throw_ub!(\"invalid return type for `PrintStderr` intrinsic\")
>      }
>
>      self.eval_print(self.stderr, arguments)?;
>
>      ret(unit_value())
>  }"
> "fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::Allocate: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if arguments.len() != 2 {
>          throw_ub!(\"invalid number of arguments for `Allocate` intrinsic\");
>      }
>
>      let Value::Int(size) = arguments[0].0 else {
>          throw_ub!(\"invalid first argument to `Allocate` intrinsic: not an integer\");
>      };
>      let Some(size) = Size::from_bytes(size) else {
>          throw_ub!(\"invalid size for `Allocate` intrinsic: negative size\");
>      };
>
>      let Value::Int(align) = arguments[1].0 else {
>          throw_ub!(\"invalid second argument to `Allocate` intrinsic: not an integer\");
>      };
>      let Some(align) = Align::from_bytes(align) else {
>          throw_ub!(\"invalid alignment for `Allocate` intrinsic: not a power of 2\");
>      };
>
>      let Type::Ptr(ret_ptr_ty) = ret_ty else {
>          throw_ub!(\"invalid return type for `Allocate` intrinsic\");
>      };
>      if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
>          throw_ub!(\"unsized pointee requested for `Allocate` intrinsic\");
>      }
>
>      let alloc = self.mem.allocate(AllocationKind::Heap, size, align)?;
>
>      ret(Value::Ptr(alloc.widen(None)))
>  }
>
>  fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::Deallocate: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if arguments.len() != 3 {
>          throw_ub!(\"invalid number of arguments for `Deallocate` intrinsic\");
>      }
>
>      let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
>          throw_ub!(\"invalid first argument to `Deallocate` intrinsic: not a thin pointer\");
>      };
>
>      let Value::Int(size) = arguments[1].0 else {
>          throw_ub!(\"invalid second argument to `Deallocate` intrinsic: not an integer\");
>      };
>      let Some(size) = Size::from_bytes(size) else {
>          throw_ub!(\"invalid size for `Deallocate` intrinsic: negative size\");
>      };
>
>      let Value::Int(align) = arguments[2].0 else {
>          throw_ub!(\"invalid third argument to `Deallocate` intrinsic: not an integer\");
>      };
>      let Some(align) = Align::from_bytes(align) else {
>          throw_ub!(\"invalid alignment for `Deallocate` intrinsic: not a power of 2\");
>      };
>
>      if ret_ty != unit_type() {
>          throw_ub!(\"invalid return type for `Deallocate` intrinsic\")
>      }
>
>      self.mem.deallocate(ptr, AllocationKind::Heap, size, align)?;
>
>      ret(unit_value())
>  }"
> "fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::RawEq: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if arguments.len() != 2 {
>          throw_ub!(\"invalid number of arguments for `RawEq` intrinsic\");
>      }
>      if ret_ty != Type::Bool {
>          throw_ub!(\"invalid return type for `RawEq` intrinsic\")
>      }
>
>      let (left, l_ty) = (arguments).index_at(0);
>      let (right, r_ty) = (arguments).index_at(1);
>
>      if l_ty != r_ty {
>          throw_ub!(\"invalid arguments to `RawEq` intrinsic: types of arguments are not identical\");
>      }
>
>      let Value::Ptr(left) = left else {
>          throw_ub!(\"invalid first argument to `RawEq` intrinsic: not a pointer\");
>      };
>
>      let Value::Ptr(right) = right else {
>          throw_ub!(\"invalid second argument to `RawEq` intrinsic: not a pointer\");
>      };
>
>      let Type::Ptr(l_ty) = l_ty else {
>          throw_ub!(\"invalid argument type to `RawEq` intrinsic: not a pointer\");
>      };
>
>      let left_data = self.load_raw_data(left, l_ty)?;
>      let right_data = self.load_raw_data(right, l_ty)?;
>
>      ret(Value::Bool(left_data == right_data))
>  }"
> "fn eval_intrinsic(
>      &mut self,
>      IntrinsicOp::GetUnwindPayload: IntrinsicOp,
>      arguments: List<(Value<M>, Type)>,
>      ret_ty: Type,
>  ) -> NdResult<Value<M>> {
>      if arguments.len() != 0 {
>          throw_ub!(\"invalid number of arguments for `GetUnwindPayload` intrinsic\");
>      }
>
>      let Type::Ptr(ret_ptr_ty) = ret_ty else {
>          throw_ub!(\"invalid return type for `GetUnwindPayload` intrinsic\");
>      };
>      if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
>          throw_ub!(\"invalid return type for `GetUnwindPayload` intrinsic\");
>      }
>
>      let Some(thin_pointer) = self.active_thread().unwind_payloads.last() else {
>          throw_ub!(\"GetUnwindPayload: the payload stack is empty\");
>      };
>
>      let payload_pointer = Value::Ptr(Pointer { thin_pointer, metadata: None });
>
>      ret(payload_pointer)
>  }"
`Type` has no derived decidable equality in the generated model, so `ret_ty !=
unit_type()` and `ret_ty != Type::Bool` match on the exact `unitType` and
`Type::Bool` terms while `l_ty != r_ty` in `RawEq` uses `typeEq`. Beyond the
quoted checks, `PointerWithExposedProvenance` (whose `int2ptr` resolves an
angelic `predict` choice) and the thread (`Spawn`, `Join`), lock, and atomic
intrinsics report `unsupported`. -/
def evalIntrinsic (m : Mach) (op : IntrinsicOp) (arguments : List (Val × «Type»))
    (retTy : «Type») : Interp (Val × Mach) :=
  match op with
  | .PointerExposeProvenance =>
    match arguments with
    | [(arg, _)] =>
      match arg with
      | .Ptr ⟨ptr, none⟩ =>
        match retTy with
        | .Int it =>
          if it = ⟨.Unsigned, x86_64.PTR_SIZE⟩ then
            pure (.Int ptr.addr, { m with intptrcast := IntPtrCast.expose m.intptrcast ptr })
          else
            ub "invalid return type for `PointerExposeProvenance` intrinsic"
        | _ => ub "invalid return type for `PointerExposeProvenance` intrinsic"
      | _ => ub "invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer"
    | _ => ub "invalid number of arguments for `PointerExposeProvenance` intrinsic"
  | .PointerWithExposedProvenance =>
    match arguments with
    | [(arg, _)] =>
      match arg with
      | .Int _ =>
        match retTy with
        | .Ptr retPtrTy =>
          if PtrType.meta_kind retPtrTy = .None then
            unsupported "IntPtrCast::int2ptr (an angelic `predict` choice)"
          else
            ub "unsized pointee requested for `PointerWithExposedProvenance` intrinsic"
        | _ => ub "invalid return type for `PointerWithExposedProvenance` intrinsic"
      | _ => ub "invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer"
    | _ => ub "invalid number of arguments for `PointerWithExposedProvenance` intrinsic"
  | .Exit => machineExit m
  | .Abort => abort
  | .Assume =>
    match arguments with
    | [(val, _)] =>
      match val with
      | .Bool b =>
        match retTy with
        | .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none =>
          if !b then
            ub "`Assume` intrinsic called on condition that is violated"
          else
            pure (unitValue, m)
        | _ => ub "invalid return type for `Assume` intrinsic"
      | _ => ub "invalid argument for `Assume` intrinsic: not a Boolean"
    | _ => ub "invalid number of arguments for `Assume` intrinsic"
  | .PrintStdout =>
    match retTy with
    | .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none => do
      let stdout ← evalPrint m.stdout arguments
      pure (unitValue, { m with stdout := stdout })
    | _ => ub "invalid return type for `PrintStdout` intrinsic"
  | .PrintStderr =>
    match retTy with
    | .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none => do
      let stderr ← evalPrint m.stderr arguments
      pure (unitValue, { m with stderr := stderr })
    | _ => ub "invalid return type for `PrintStderr` intrinsic"
  | .Allocate =>
    match arguments with
    | [(sizeV, _), (alignV, _)] =>
      match sizeV with
      | .Int size =>
        match sizeFromBytes size with
        | some size =>
          match alignV with
          | .Int align =>
            match alignFromBytesInt align with
            | some align =>
              match retTy with
              | .Ptr retPtrTy =>
                if PtrType.meta_kind retPtrTy = .None then do
                  let (alloc, cm) ← CM.allocate m.mem .Heap size align
                  pure (.Ptr (ThinPointer.widen alloc none), { m with mem := cm })
                else
                  ub "unsized pointee requested for `Allocate` intrinsic"
              | _ => ub "invalid return type for `Allocate` intrinsic"
            | none => ub "invalid alignment for `Allocate` intrinsic: not a power of 2"
          | _ => ub "invalid second argument to `Allocate` intrinsic: not an integer"
        | none => ub "invalid size for `Allocate` intrinsic: negative size"
      | _ => ub "invalid first argument to `Allocate` intrinsic: not an integer"
    | _ => ub "invalid number of arguments for `Allocate` intrinsic"
  | .Deallocate =>
    match arguments with
    | [(ptrV, _), (sizeV, _), (alignV, _)] =>
      match ptrV with
      | .Ptr ⟨ptr, none⟩ =>
        match sizeV with
        | .Int size =>
          match sizeFromBytes size with
          | some size =>
            match alignV with
            | .Int align =>
              match alignFromBytesInt align with
              | some align =>
                match retTy with
                | .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none => do
                  let cm ← CM.deallocate m.mem ptr .Heap size align
                  pure (unitValue, { m with mem := cm })
                | _ => ub "invalid return type for `Deallocate` intrinsic"
              | none => ub "invalid alignment for `Deallocate` intrinsic: not a power of 2"
            | _ => ub "invalid third argument to `Deallocate` intrinsic: not an integer"
          | none => ub "invalid size for `Deallocate` intrinsic: negative size"
        | _ => ub "invalid second argument to `Deallocate` intrinsic: not an integer"
      | _ => ub "invalid first argument to `Deallocate` intrinsic: not a thin pointer"
    | _ => ub "invalid number of arguments for `Deallocate` intrinsic"
  | .RawEq =>
    match arguments with
    | [(leftV, lTy), (rightV, rTy)] =>
      match retTy with
      | .Bool =>
        if !typeEq lTy rTy then
          ub "invalid arguments to `RawEq` intrinsic: types of arguments are not identical"
        else
          match leftV with
          | .Ptr leftPtr =>
            match rightV with
            | .Ptr rightPtr =>
              match lTy with
              | .Ptr lPtrTy => do
                let (leftData, m) ← loadRawData m leftPtr lPtrTy
                let (rightData, m) ← loadRawData m rightPtr lPtrTy
                pure (.Bool (leftData == rightData), m)
              | _ => ub "invalid argument type to `RawEq` intrinsic: not a pointer"
            | _ => ub "invalid second argument to `RawEq` intrinsic: not a pointer"
          | _ => ub "invalid first argument to `RawEq` intrinsic: not a pointer"
      | _ => ub "invalid return type for `RawEq` intrinsic"
    | _ => ub "invalid number of arguments for `RawEq` intrinsic"
  | .GetUnwindPayload =>
    if !arguments.isEmpty then
      ub "invalid number of arguments for `GetUnwindPayload` intrinsic"
    else
      match retTy with
      | .Ptr retPtrTy =>
        if PtrType.meta_kind retPtrTy = .None then do
          let t ← activeThread m
          match t.unwind_payloads.getLast? with
          | some thinPointer =>
            pure (.Ptr { thin_pointer := thinPointer, metadata := none }, m)
          | none => ub "GetUnwindPayload: the payload stack is empty"
        else
          ub "invalid return type for `GetUnwindPayload` intrinsic"
      | _ => ub "invalid return type for `GetUnwindPayload` intrinsic"
  | _ =>
    unsupported "eval_intrinsic for a thread, lock, or atomic intrinsic"

/-- Argument evaluation loop of `Terminator::Intrinsic`
(`spec/lang/step/terminators.md`):
> "let arguments = arguments.try_map(|arg| self.eval_value(arg))?;" -/
def evalIntrinsicArgs (m : Mach) : List ValueExpr → Interp (List (Val × «Type») × Mach)
  | [] => pure ([], m)
  | arg :: args => do
    let (v, m) ← evalValue m arg
    let (vs, m) ← evalIntrinsicArgs m args
    pure (v :: vs, m)

/-- `Machine::eval_terminator` for `Terminator::Intrinsic`
(`spec/lang/step/terminators.md`):
> "fn eval_terminator(
>      &mut self,
>      Terminator::Intrinsic { intrinsic, arguments, ret: ret_expr, next_block }: Terminator
>  ) -> NdResult {
>      let (ret_place, ret_ty) = self.eval_place(ret_expr)?;
>      let arguments = arguments.try_map(|arg| self.eval_value(arg))?;
>      let value = self.eval_intrinsic(intrinsic, arguments, ret_ty)?;
>      self.place_store(ret_place, value, ret_ty)?;
>      if let Some(next_block) = next_block {
>          self.jump_to_block(next_block)?;
>      } else {
>          throw_ub!(\"return from an intrinsic where caller did not specify next block\");
>      }
>      ret(())
>  }" -/
def evalIntrinsicTerminator (m : Mach) (intrinsic : IntrinsicOp) (arguments : List ValueExpr)
    (retExpr : PlaceExpr) (nextBlock : Option BbName) : Interp Mach := do
  let ((retPlace, retTy), m) ← evalPlace m retExpr
  let (argVals, m) ← evalIntrinsicArgs m arguments
  let (value, m) ← evalIntrinsic m intrinsic argVals retTy
  let m ← placeStore m retPlace value retTy
  match nextBlock with
  | some nb => jumpToBlock m nb
  | none => ub "return from an intrinsic where caller did not specify next block"

/-- `Machine::eval_terminator` for `Goto`, `Switch`, `Unreachable`, `Call`,
`Return`, and `Intrinsic` (`evalIntrinsicTerminator`)
(`spec/lang/step/terminators.md`):
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
> }
> ..
> fn eval_terminator(
>     &mut self,
>     Terminator::Call { callee, calling_convention: caller_conv, arguments, ret: ret_expr, next_block, unwind_block }: Terminator
> ) -> NdResult {
>     let (ret_place, ret_ty) = self.eval_place(ret_expr)?;
>     self.prepare_for_inplace_passing(ret_place, ret_ty)?;
>     let (callee_val, _) = self.eval_value(callee)?;
>     let callee = self.fn_from_ptr(callee_val)?;
>     let arguments = arguments.try_map(|arg| self.eval_argument(arg))?;
>     self.eval_call(
>         callee,
>         caller_conv,
>         arguments,
>         (ret_place, ret_ty),
>         next_block,
>         unwind_block,
>     )
> }" -/
def evalTerminator (m : Mach) : Terminator → Interp Mach
  | .Goto blockName => jumpToBlock m blockName
  | .Switch value cases fallback => do
    let ((v, _), m) ← evalValue m value
    match v with
    | .Int i => jumpToBlock m ((mapGet cases i).getD fallback)
    | _ => specPanic "switch on a non-integer"
  | .Unreachable => ub "reached unreachable code"
  | .Call callee callerConv arguments retExpr nextBlock unwindBlock => do
    let ((retPlace, retTy), m) ← evalPlace m retExpr
    let m ← prepareForInplacePassing m retPlace retTy
    let ((calleeVal, _), m) ← evalValue m callee
    let callee ← fnFromPtr m calleeVal
    let (arguments, m) ← evalArguments m arguments
    evalCall m callee callerConv arguments (retPlace, retTy) nextBlock unwindBlock
  | .Return => evalReturn m
  | .Intrinsic intrinsic arguments retExpr nextBlock =>
    evalIntrinsicTerminator m intrinsic arguments retExpr nextBlock
  | _ => unsupported "eval_terminator for a terminator other than Goto/Switch/Unreachable/Call/Return/Intrinsic"

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
