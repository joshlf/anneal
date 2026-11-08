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
* `Statement::Assign`, `Statement::PlaceMention`, `Statement::Validate`
  (through `Machine::retag_val` and `BasicMemory::retag_ptr`),
  `Statement::Deinit` (through `ConcurrentMemory::deinit`),
  `Statement::StorageLive`, and `Statement::StorageDead` (through
  `Machine::try_mutate_cur_frame`, `StackFrame::storage_live`, and
  `StackFrame::storage_dead`) (`spec/lang/step/statements.md`,
  `spec/lang/machine.md`).
* `PlaceExpr::Local`, `PlaceExpr::Field`, `PlaceExpr::Index`, and
  `PlaceExpr::Deref` (`spec/lang/step/expressions.md`),
  including `Machine::ptr_offset_inbounds` (`spec/lang/step/operators.md`),
  `ThinPointer::wrapping_offset` and `ThinPointer::widen`
  (`spec/mem/pointer.md`), `Memory::dereferenceable` and
  `Memory::signed_dereferenceable` (`spec/mem/basic.md`,
  `spec/mem/concurrent.md`, `spec/mem/interface.md`), and
  `Machine::vtable_lookup`, `Machine::compute_size`, and
  `Machine::compute_align` (`spec/lang/machine.md`).
* `ValueExpr::Constant` for `Constant::Int`/`Constant::Bool`/
  `Constant::PointerWithoutProvenance`, `ValueExpr::Tuple`, `ValueExpr::Load`,
  `ValueExpr::AddrOf` (with `check_value` at the pointer type and
  `BasicMemory`'s identity `retag_ptr`),
  `ValueExpr::UnOp` with `UnOp::Int` (all `IntUnOp` variants: `Neg`, `BitNot`,
  `CountOnes`), `UnOp::Cast` (both `CastOp` variants: `IntToInt` and
  `Transmute`, the latter through `Machine::transmute`, i.e. `encode` at the
  old type followed by `decode` and `check_value` at the new type), and
  `UnOp::GetThinPointer`, and
  `ValueExpr::BinOp` with `BinOp::Int` (all `IntBinOp` variants: `Add`,
  `AddUnchecked`, `Sub`, `SubUnchecked`, `Mul`, `MulUnchecked`, `Div`,
  `DivExact`, `Rem`, `Shl`, `Shr`, `ShlUnchecked`, `ShrUnchecked`, `BitAnd`,
  `BitOr`, `BitXor`), `BinOp::IntWithOverflow` (all `IntBinOpWithOverflow`
  variants: `Add`, `Sub`, `Mul`, returning `(Value::Int(result), Value::Bool(overflow))`
  at `IntType::with_overflow`), `BinOp::Rel` (all `RelOp` variants: `Lt`,
  `Gt`, `Le`, `Ge`, `Eq`, `Ne`, `Cmp`) on integers, Booleans, and pointers
  (`Machine::compare_ptr`), and `BinOp::PtrOffset` (in-bounds and wrapping)
  and `BinOp::PtrOffsetFrom`
  (`spec/lang/step/expressions.md`, `spec/lang/step/operators.md`). MiniRust
  has no Boolean negation operator: `minimize` expresses `!b` with transmutes
  and integer subtraction (see `MiniRustSpec.Correspondence.Translate`), so
  `UnOp::Int` on a `Value::Bool` stays a spec panic, exactly as upstream.
* `Terminator::Goto`, `Terminator::Switch`, `Terminator::Unreachable`,
  `Terminator::Return` (`spec/lang/step/terminators.md`), including frame
  teardown, `storage_dead` of every local, and both stack-pop actions, and
  `Terminator::Intrinsic` for the pointer provenance intrinsics
  `PointerExposeProvenance` and `PointerWithExposedProvenance`
  (`spec/lang/step/intrinsics.md`, `spec/mem/intptrcast.md`).
* The representation relation (`Type::{decode, encode}`) for `Type::Int`,
  `Type::Bool`, `Type::Ptr` (thin pointers through `decode_ptr` and
  `encode_ptr`, which carry provenance in `AbstractByte::Init`, and wide
  pointers through `PtrType::as_wide_pair`), sized and unsized `Type::Tuple`,
  `Type::Array`, `Type::Union`
  (`Type.encodeUnionChunks`), `Type::Enum` (including `decode_discriminant`
  and `encode_discriminant`), `Type::Slice`, and `Type::TraitObject`, and
  `Machine::check_value` (with `ensure_else_ub`, `checkUnionChunks`, and
  `check_ptr` / `check_ptr_metadata` for raw pointers and safe pointers
  `PtrType::Ref` / `PtrType::Box`) for
  those types (`spec/lang/representation.md`); `Type::layout` for all of them
  (`spec/lang/types.md`); `BasicMemory`'s `allocate`, `load`, `store`,
  `deallocate`, `dereferenceable`, `signed_dereferenceable`, `retag_ptr`,
  `leak_check`, and `check_ptr` (`spec/mem/basic.md`), wrapped by
  `ConcurrentMemory` (`spec/mem/concurrent.md`); and the full Tree Borrows
  memory model (`TreeBorrowsMemory`, `Node`, `Permission`, `PermissionUnprot`,
  `PermissionProt`, `Protected`, `cells_to_freeze_mask`,
  `UnsafeCellStrategy::freeze_mask`, and `ReborrowSettings::new` in
  `spec/mem/tree_borrows/{memory,tree,state_machine,state_machine_unprotected,state_machine_protected,reborrow_settings}.md`).
  The recursion of these definitions over nested types, tuple fields, array
  elements, union chunks, enum variants, discriminator trees, and borrow-tree
  children is structural (Lean `mutual` blocks), so the kernel evaluates them.
* The `x86_64` target (`spec/prelude/target.md`) as the instance of `T`, with
  both `BasicMemory<x86_64>` (`Mach` / `step` / `steps`) and polymorphic
  `Machine<M>` (`MemoryOps`, `stepM` / `stepsM`) instantiated at
  `BasicMemory<x86_64>` and `TreeBorrowsMemory<x86_64>` (`MachTB` / `stepTB` /
  `stepsTB`).

Everything else returns `Stop.unsupported`, so the interpretation is partial
but never silently wrong. In particular, `check_ptr` for vtable pointers
(`PtrType::VTablePtr`) and for safe pointers with provenance when no machine is
supplied (`m = none` on non-ZST pointees) returns `Stop.unsupported`.

## Effects

specr-lang functions return `Result`/`NdResult`. We use `Except Stop`:

* `Stop.ub` is `throw_ub!` (`TerminationInfo::Ub`),
* `Stop.deadlock` is `throw_deadlock!`,
* `Stop.specPanic` is a specr-lang `panic!`, failed `assert!`, `unwrap` of
  `None`, or out-of-range indexing. Upstream says such a panic "is a bug in the
  specification" (vendored `README.md`), so it signals an ill-formed input
  rather than program behavior,
* `Stop.unsupported` marks a construct outside the interpreted fragment.

Three non-deterministic operations are reachable from this fragment. The
thread choice in `Machine::step` has a unique solution here (see
`pickActiveThread`). The address choice of `BasicMemory::allocate`, reached
through `Statement::StorageLive`, never does; `BM.pickAddr` documents the one
valid resolution the interpretation commits to. The angelic provenance
prediction of an integer-to-pointer cast (`IntPtrCast::int2ptr`) does not
either; `int2ptrProvenance` documents its resolution and which results it
supports.
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

/-- `TreeBorrowsMemory<x86_64>`, whose `Memory` instance
(`instMemoryTreeBorrowsMemory`, generated from
`impl<T: Target> Memory for TreeBorrowsMemory<T>`,
`spec/mem/tree_borrows/memory.md`) sets
`type Provenance = TreeBorrowsProvenance` and
`type FrameExtra = TreeBorrowsFrameExtra`. -/
abbrev TBM : Type := TreeBorrowsMemory x86_64

/-- `Machine<TreeBorrowsMemory<x86_64>>`. -/
abbrev MachTB : Type := Machine TBM

/-! ## Effects -/

/-- Why an interpreted computation stopped; see the module docs. -/
inductive Stop : Type where
  | ub (msg : String)
  | deadlock
  | memoryLeak
  | specPanic (msg : String)
  | unsupported (what : String)
  deriving DecidableEq

/-- `Result<T>` of specr-lang, plus the two non-behavior stops. -/
abbrev Interp (α : Type) : Type := Except Stop α

/-- `throw_ub!(msg)`. -/
def ub {α : Type} (msg : String) : Interp α := .error (.ub msg)

/-- `throw_memory_leak!()`. -/
def memoryLeak {α : Type} : Interp α := .error .memoryLeak

/-- A specr-lang panic (`panic!`, failed `assert!`, `unwrap` of `None`). -/
def specPanic {α : Type} (msg : String) : Interp α := .error (.specPanic msg)

/-- A construct outside the interpreted fragment. -/
def unsupported {α : Type} (what : String) : Interp α := .error (.unsupported what)

/-- Operational methods of `trait Memory` (`spec/mem/interface.md`) over the
generated associated-type class `MiniRustSpec.Gen.Memory`, plus the provenance
filtering hook used by `IntPtrCast.int2ptrM`. -/
class MemoryOps (M : Type) [Memory M] where
  decEqProv : DecidableEq (Memory.Provenance M)
  new : Memory.Params M → M
  allocate : M → AllocationKind → Size → Align →
    Interp (ThinPointer (Memory.Provenance M) × M)
  deallocate : M → ThinPointer (Memory.Provenance M) → AllocationKind → Size → Align →
    Interp M
  store : M → ThinPointer (Memory.Provenance M) →
    List (AbstractByte (Memory.Provenance M)) → Align → Interp M
  load : M → ThinPointer (Memory.Provenance M) → Size → Align →
    Interp (List (AbstractByte (Memory.Provenance M)) × M)
  dereferenceable : M → ThinPointer (Memory.Provenance M) → Size → Interp Unit
  signed_dereferenceable : M → ThinPointer (Memory.Provenance M) → Int → Interp Unit
  retag_ptr : M → Memory.FrameExtra M → Pointer (Memory.Provenance M) →
    PtrType → Bool → Bool →
    (ThinPointer (Memory.Provenance M) → Interp VTable) →
    Interp (Pointer (Memory.Provenance M) × M × Memory.FrameExtra M)
  new_call : Memory.FrameExtra M
  end_call : M → Memory.FrameExtra M → Interp M
  leak_check : M → Interp Unit
  exposedInBounds : M → Set (Memory.Provenance M) → Int → List (Memory.Provenance M)

instance instDecEqMemoryProvenance (M : Type) [Memory M] [MemoryOps M] :
    DecidableEq (Memory.Provenance M) :=
  MemoryOps.decEqProv

/-! ## `libspecr` operations

`libspecr` 0.1.41 (<https://docs.rs/libspecr/0.1.41>) is the support library
MiniRust is written against; it is not part of the MiniRust repository, so
these operations are hand-written from its documented behavior. -/

/-- `Size::bits()`: the number of bits in `s` bytes. -/
def Size.bits (s : Size) : Nat := 8 * s.bytes

/-- `Size::from_bytes(n)`: `Some` iff `n ≥ 0`. -/
def Size.from_bytes (n : Int) : Option Size :=
  if 0 ≤ n then some ⟨n.toNat⟩ else none

/-- `Size * Int` (`Mul<Int> for Size` in `libspecr`:
`Size::from_bytes(self.bytes() * rhs).unwrap()`), which panics when the byte
product `self.bytes() * rhs` is negative (`< 0`). Note that `Size::ZERO * n =
Size::ZERO` even for negative `n`. -/
def Size.mulInt (s : Size) (n : Int) : Interp Size :=
  match Size.from_bytes ((s.bytes : Int) * n) with
  | some sz => pure sz
  | none => specPanic "Size * Int: negative byte count"

/-- `Size + Size` (`Add<Size> for Size` in `libspecr`). -/
def Size.add (a b : Size) : Size := ⟨a.bytes + b.bytes⟩

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

/-- `Map::insert(k, v)` helper on association-list entries. -/
def mapInsert {K V : Type} [DecidableEq K] : List (K × V) → K → V → List (K × V)
  | [], k, v => [(k, v)]
  | (k', v') :: tail, k, v => if k' = k then (k, v) :: tail else (k', v') :: mapInsert tail k v

/-- `Map::insert(k, v)`. -/
def mapInsertMap {K V : Type} [DecidableEq K] (m : Map K V) (k : K) (v : V) : Map K V :=
  ⟨mapInsert m.entries k v⟩

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

/-- `List::mutate_at(i, f)` lifted into `Interp`, which panics out of range. -/
def listMutateAt {T O : Type} (xs : List T) (i : Int) (what : String)
    (f : T → Interp (O × T)) : Interp (O × List T) := do
  let elem ← listIndex xs i what
  let (out, elem') ← f elem
  let xs' ← listSet xs i elem' what
  pure (out, xs')

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

/-- `List::try_map(f)` in `libspecr` lifted into `Interp`: applies `f`
left-to-right and short-circuits on the first element that returns `none`. -/
def tryMapM {α β : Type} [Monad m] (f : α → m (Option β)) : List α → m (Option (List β))
  | [] => pure (some [])
  | x :: xs => do
    match ← f x with
    | none => pure none
    | some y =>
      match ← tryMapM f xs with
      | none => pure none
      | some ys => pure (some (y :: ys))

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

/-- `IntType::usize_ty::<x86_64>` (`spec/lang/types.md`), the type of slice
lengths in pointer metadata and of the address that
`PointerExposeProvenance` returns:
> "pub fn usize_ty<T: Target>() -> Self {
>     IntType { signed: Signedness::Unsigned, size: T::PTR_SIZE }
> }" -/
def IntType.usize_ty : IntType := ⟨.Unsigned, x86_64.PTR_SIZE⟩

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
def LayoutStrategy.compute_size_and_align {Provenance : Type}
    (vtables : ThinPointer Provenance → Interp VTable) :
    LayoutStrategy → Option (PointerMeta Provenance) → Interp (Size × Align)
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

/-- `LayoutStrategy::meta_kind` (`spec/lang/types.md`), the kind of pointer
metadata needed to compute the size and alignment of a layout:
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

/-- `PtrType::safe_pointee` (`spec/mem/pointer.md`): references and boxes are
safe pointers and carry pointee information; raw, function, and vtable
pointers do not:
> "pub fn safe_pointee(self) -> Option<PointeeInfo> {
>     match self {
>         PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => Some(pointee),
>         PtrType::Raw { .. } | PtrType::FnPtr | PtrType::VTablePtr(_) => None,
>     }
> }" -/
def PtrType.safe_pointee : PtrType → Option PointeeInfo
  | .Ref _ pointee => some pointee
  | .Box pointee => some pointee
  | .Raw _ => none
  | .FnPtr => none
  | .VTablePtr _ => none

/-- `PtrType::meta_kind` (`spec/mem/pointer.md`):
> "pub fn meta_kind(self) -> PointerMetaKind {
>     match self {
>         PtrType::Ref { pointee, .. } | PtrType::Box { pointee, .. } => pointee.layout.meta_kind(),
>         PtrType::Raw { meta_kind, .. } => meta_kind,
>         PtrType::FnPtr | PtrType::VTablePtr(_) => PointerMetaKind::None,
>     }
> }" -/
def PtrType.meta_kind : PtrType → PointerMetaKind
  | .Ref _ pointee => LayoutStrategy.meta_kind pointee.layout
  | .Box pointee => LayoutStrategy.meta_kind pointee.layout
  | .Raw metaKind => metaKind
  | .FnPtr => .None
  | .VTablePtr _ => .None

/-- `Type::layout::<x86_64>` for the interpreted types (`spec/lang/types.md`):
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
>  TraitObject(trait_name) => LayoutStrategy::TraitObject(trait_name),"
A thin pointer (`meta_kind() == None`) is pointer-sized and pointer-aligned;
a wide pointer is a thin pointer followed by pointer-sized metadata. -/
def Type.layout : «Type» → Interp LayoutStrategy
  | .Int t => do pure (.Sized t.size (← IntType.align t))
  | .Bool => pure (.Sized ⟨1⟩ ⟨1⟩)
  | .Ptr p =>
    if PtrType.meta_kind p = .None then pure (.Sized x86_64.PTR_SIZE x86_64.PTR_ALIGN)
    else pure (.Sized ⟨2 * x86_64.PTR_SIZE.bytes⟩ x86_64.PTR_ALIGN)
  | .Union _ _ size align => pure (.Sized size align)
  | .Enum _ _ _ size align => pure (.Sized size align)
  | .Tuple _ headLayout none =>
    let (size, align) := TupleHeadLayout.head_size_and_align headLayout
    pure (.Sized size align)
  | .Tuple _ headLayout (some tailTy) => do
    pure (.Tuple headLayout (← Type.layout tailTy))
  | .Array elem count => do
    let elemLayout ← Type.layout elem
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
    let elemAlign ← LayoutStrategy.expect_align elemLayout "WF ensures array element is sized"
    let size ← Size.mulInt elemSize count
    pure (.Sized size elemAlign)
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

/-- `AbstractByte::provenance_frag` (`spec/mem/interface.md`):
> "pub fn provenance_frag(self) -> Option<ProvenanceFrag<Provenance>> {
>     match self {
>         AbstractByte::Uninit => None,
>         AbstractByte::Init(_, frag) => frag,
>     }
> }" -/
def AbstractByte.provenance_frag : Byte → Option (ProvenanceFrag Prov)
  | .Uninit => none
  | .Init _ frag => frag

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

/-- `ThinPointer::widen` (`spec/mem/pointer.md`):
> "pub fn widen(self, metadata: Option<PointerMeta<Provenance>>) -> Pointer<Provenance> {
>     Pointer {
>         thin_pointer: self,
>         metadata,
>     }
> }" -/
def ThinPointer.widen {Provenance : Type} (ptr : ThinPointer Provenance)
    (metadata : Option (PointerMeta Provenance)) : Pointer Provenance :=
  { thin_pointer := ptr, metadata := metadata }

/-- The provenance fold of `decode_ptr` (`spec/lang/representation.md`), which
keeps the provenance `acc` of byte `0` only while every byte `idx` carries a
fragment of that same provenance at position `idx`:
> "let provenance = bytes.fold_with_idx(
>     bytes[0].provenance_frag().map(|frag| frag.provenance),
>     |acc, idx, byte| {
>         // Crucially, if `acc` is ever `None`, it remains `None`.
>         if let Some(frag) = byte.provenance_frag() &&
>             frag.position == idx && Some(frag.provenance) == acc
>         {
>             acc
>         } else {
>             None
>         }
>     }
> );"
`fold_with_idx` visits the bytes in order, passing each one's index; `idx` is
the index of the first byte of `bytes`. -/
def decodePtrProvenance : Nat → Option Prov → List Byte → Option Prov
  | _, acc, [] => acc
  | idx, acc, byte :: rest =>
    let acc' : Option Prov :=
      match AbstractByte.provenance_frag byte with
      | some frag => if frag.position = (idx : Int) ∧ some frag.provenance = acc then acc else none
      | none => none
    decodePtrProvenance (idx + 1) acc' rest

/-- The start value of the provenance fold of `decode_ptr`
(`spec/lang/representation.md`), the provenance of the first byte's fragment:
> "bytes[0].provenance_frag().map(|frag| frag.provenance),"
`decodePtr` checks the length first, so `bytes` is never empty here. -/
def firstProvenance : List Byte → Option Prov
  | byte :: _ => (AbstractByte.provenance_frag byte).map (fun frag => frag.provenance)
  | [] => none

/-- `decode_ptr` (`spec/lang/representation.md`), which reads a thin pointer
from `PTR_SIZE` bytes: the address from the byte values and the provenance
from the bytes' provenance fragments (`decodePtrProvenance`):
> "fn decode_ptr<M: Memory>(bytes: List<AbstractByte<M::Provenance>>) -> Option<ThinPointer<M::Provenance>> {
>     if bytes.len() != M::T::PTR_SIZE.bytes() { panic!(\"decode of thin pointer with invalid length\"); }
>     // Convert into list of bytes; fail if any byte is uninitialized.
>     let bytes_data = bytes.try_map(|b| b.data())?;
>     let addr = M::T::ENDIANNESS.decode(Unsigned, bytes_data);
>     ..
>     ret(ThinPointer { addr, provenance })
> }" -/
def decodePtr (bytes : List Byte) : Interp (Option Ptr) :=
  if bytes.length ≠ x86_64.PTR_SIZE.bytes then specPanic "decode of thin pointer with invalid length"
  else
    match bytes.mapM AbstractByte.data with
    | none => pure none
    | some data =>
      let addr := Endianness.decode x86_64.ENDIANNESS .Unsigned data
      pure (some { addr := addr, provenance := decodePtrProvenance 0 (firstProvenance bytes) bytes })

/-- The bytes of `encode_ptr` (`spec/lang/representation.md`): byte `i` holds
the address byte `b` and, when the pointer has provenance, the fragment of
that provenance at position `i`:
> "bytes_data.map_with_idx(|i, b|
>     AbstractByte::Init(b, ptr.provenance.map(|provenance|
>         ProvenanceFrag { provenance, position: i }
>     ))
> )"
`idx` is the index of the first byte of `data`. -/
def encodePtrBytes (provenance : Option Prov) : Nat → List UInt8 → List Byte
  | _, [] => []
  | idx, b :: rest =>
    .Init b (provenance.map (fun p => { provenance := p, position := (idx : Int) })) ::
      encodePtrBytes provenance (idx + 1) rest

/-- `encode_ptr` (`spec/lang/representation.md`):
> "fn encode_ptr<M: Memory>(ptr: ThinPointer<M::Provenance>) -> List<AbstractByte<M::Provenance>> {
>     let bytes_data = M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap();
>     bytes_data.map_with_idx(|i, b|
>         AbstractByte::Init(b, ptr.provenance.map(|provenance|
>             ProvenanceFrag { provenance, position: i }
>         ))
>     )
> }"
`Endianness::encode` fails, and `unwrap` panics, exactly when the address is
not in `[0, 2^64)`; `check_ptr` (`checkPtr`) rejects such pointers before any
store. -/
def encodePtr (ptr : Ptr) : Interp (List Byte) :=
  match Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr with
  | some data => pure (encodePtrBytes ptr.provenance 0 data)
  | none => specPanic "M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap()"

/-- `PtrType::as_wide_pair::<x86_64>` (`spec/lang/representation.md`), which
views a wide pointer as the pair of a thin raw pointer and its metadata, or
returns `None` for a thin pointer:
> "pub fn as_wide_pair<T: Target>(self) -> Option<Type> {
>     if self.meta_kind() == PointerMetaKind::None {
>         return None;
>     }
>     let meta_ty = self.meta_kind().ty::<T>();
>     ..
>     let thin_pointer_field = (Offset::ZERO, Type::Ptr(PtrType::Raw { meta_kind: PointerMetaKind::None }));
>     let metadata_field = (T::PTR_SIZE, meta_ty);
>     ret(Type::Tuple {
>         sized_fields: list![thin_pointer_field, metadata_field],
>         sized_head_layout: TupleHeadLayout {
>             end: Int::from(2) * T::PTR_SIZE,
>             align: T::PTR_ALIGN,
>             packed_align: None,
>         },
>         unsized_field: None,
>     })
> }"
with `PointerMetaKind::ty::<x86_64>` (`spec/lang/representation.md`):
> "PointerMetaKind::ElementCount => Type::Int(IntType::usize_ty::<T>()),
>  PointerMetaKind::VTablePointer(trait_name) => Type::Ptr(PtrType::VTablePtr(trait_name)),"
Both metadata types are pointer-sized and pointer-aligned on `x86_64`, so the
elided `assert_eq!`s of `as_wide_pair` hold. -/
def PtrType.as_wide_pair (p : PtrType) : Option «Type» :=
  let metaTy : Option «Type» :=
    match PtrType.meta_kind p with
    | .None => none
    | .ElementCount => some (.Int IntType.usize_ty)
    | .VTablePointer traitName => some (.Ptr (.VTablePtr traitName))
  metaTy.map (fun metaTy =>
    .Tuple [(⟨0⟩, .Ptr (.Raw .None)), (x86_64.PTR_SIZE, metaTy)]
      ⟨⟨2 * x86_64.PTR_SIZE.bytes⟩, x86_64.PTR_ALIGN, none⟩ none)

/-- `PointerMetaKind::decode_value` (`spec/lang/representation.md`):
> "fn decode_value<M: Memory>(self, value: Value<M>) -> Option<PointerMeta<M::Provenance>> {
>     match (self, value) {
>         (PointerMetaKind::None, Value::Tuple(fields)) if fields.is_empty() => None,
>         (PointerMetaKind::ElementCount, Value::Int(count)) => Some(PointerMeta::ElementCount(count)),
>         (PointerMetaKind::VTablePointer(_), Value::Ptr(ptr)) if ptr.metadata.is_none() => Some(PointerMeta::VTablePointer(ptr.thin_pointer)),
>         _ => panic!(\"PointerMeta::decode_value called with invalid value\"),
>     }
> }" -/
def PointerMetaKind.decode_value : PointerMetaKind → Val → Interp (Option (PointerMeta Prov))
  | .None, .Tuple [] => pure none
  | .ElementCount, .Int count => pure (some (.ElementCount count))
  | .VTablePointer _, .Ptr ⟨thin, none⟩ => pure (some (.VTablePointer thin))
  | _, _ => specPanic "PointerMeta::decode_value called with invalid value"

/-- `PointerMetaKind::encode_as_value` (`spec/lang/representation.md`), for
the metadata of wide pointers (the thin case, `unit_value()`, is never
reached from `Type::encode`, which encodes thin pointers with `encode_ptr`):
> "fn encode_as_value<M: Memory>(self, meta: Option<PointerMeta<M::Provenance>>) -> Value<M> {
>     match (self, meta) {
>         (PointerMetaKind::None, None) => unit_value(),
>         (PointerMetaKind::ElementCount, Some(PointerMeta::ElementCount(count))) => Value::Int(count),
>         (PointerMetaKind::VTablePointer(_), Some(PointerMeta::VTablePointer(ptr))) => Value::Ptr(ptr.widen(None)),
>         _ => panic!(\"PointerMeta::encode_as_value called with invalid value\"),
>     }
> }" -/
def PointerMetaKind.encode_as_value : PointerMetaKind → Option (PointerMeta Prov) → Interp Val
  | .None, none => pure (.Tuple [])
  | .ElementCount, some (.ElementCount count) => pure (.Int count)
  | .VTablePointer _, some (.VTablePointer ptr) => pure (.Ptr { thin_pointer := ptr, metadata := none })
  | _, _ => specPanic "PointerMeta::encode_as_value called with invalid value"

/-- `Type::decode` at a metadata type of `PointerMetaKind::ty::<x86_64>`
(`spec/lang/representation.md`) other than the unit type:
> "PointerMetaKind::ElementCount => Type::Int(IntType::usize_ty::<T>()),
>  PointerMetaKind::VTablePointer(trait_name) => Type::Ptr(PtrType::VTablePtr(trait_name)),"
`Type::Int(usize)` decodes as an integer (`Type.decodeInt`), and the thin
pointer type `Type::Ptr(PtrType::VTablePtr(..))` with `decode_ptr` (see
`Type.decode`). -/
def decodeMetaField (metaKind : PointerMetaKind) (bytes : List Byte) : Interp (Option Val) :=
  match metaKind with
  | .ElementCount => Type.decodeInt IntType.usize_ty bytes
  | .VTablePointer _ => do
    match ← decodePtr bytes with
    | some ptr => pure (some (.Ptr { thin_pointer := ptr, metadata := none }))
    | none => pure none
  | .None => specPanic "as_wide_pair always returns a suitable metadata type"

/-- `Type::decode` for a wide pointer type (`spec/lang/representation.md`):
> "if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
>     // This will recursively call this decode function again, but with a thin pointer type.
>     let Value::Tuple(parts) = pair_ty.decode::<M>(bytes)? else {
>         panic!(\"as_wide_pair always returns a tuple type\");
>     };
>     let Value::Ptr(ptr) = parts[0] else {
>         panic!(\"as_wide_pair always returns tuple with the first field being a thin pointer\");
>     };
>     // This metadata might not be well-formed, but we are allowed to return ill-formed pointers here.
>     let meta = ptr_type.meta_kind().decode_value(parts[1]);
>     assert!(meta.is_some(), \"as_wide_pair always returns a suitable metadata type\");
>     ret(Value::Ptr(ptr.thin_pointer.widen(meta)))
> }"
The recursive `pair_ty.decode` is unrolled here so that `Type.decode` stays
structurally recursive: the pair type (`PtrType.as_wide_pair`) is a tuple of
size `2 * PTR_SIZE` without padding whose fields are the thin pointer at
offset `0` and the metadata at offset `PTR_SIZE`, so tuple decoding (a
length check that panics on a mismatch, followed by `try_map` over the
fields) checks the length, decodes the first `PTR_SIZE` bytes with
`decode_ptr`, and then decodes the metadata bytes (`decodeMetaField`). -/
def decodeWidePtr (metaKind : PointerMetaKind) (bytes : List Byte) : Interp (Option Val) :=
  if bytes.length ≠ 2 * x86_64.PTR_SIZE.bytes then
    specPanic "decode of Type::Tuple with invalid length"
  else do
    match ← decodePtr (bytes.take x86_64.PTR_SIZE.bytes) with
    | none => pure none
    | some thin =>
      match ← decodeMetaField metaKind (bytes.drop x86_64.PTR_SIZE.bytes) with
      | none => pure none
      | some metaVal => do
        let ptrMeta ← PointerMetaKind.decode_value metaKind metaVal
        match ptrMeta with
        | some _ => pure (some (.Ptr (ThinPointer.widen thin ptrMeta)))
        | none => specPanic "assertion failed: as_wide_pair always returns a suitable metadata type"

/-- `Type::encode` for a wide pointer type (`spec/lang/representation.md`):
> "if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
>     let thin_ptr_value = Value::Ptr(ptr.thin_pointer.widen(None));
>     let meta_data_value = ptr_type.meta_kind().encode_as_value::<M>(ptr.metadata);
>     let tuple = Value::Tuple(list![thin_ptr_value, meta_data_value]);
>
>     // This will recursively call this encode function again, but with a thin pointer type.
>     pair_ty.encode::<M>(tuple)
> }"
As in `decodeWidePtr`, the recursive `pair_ty.encode` is unrolled: the pair
has no padding, so its encoding is the thin pointer's `encode_ptr` bytes
followed by the metadata's encoding (`Type::Int(usize)` for an element count,
`encode_ptr` for a vtable pointer). -/
def encodeWidePtr (metaKind : PointerMetaKind) (ptr : Pointer Prov) : Interp (List Byte) := do
  let metaVal ← PointerMetaKind.encode_as_value metaKind ptr.metadata
  let thinBytes ← encodePtr ptr.thin_pointer
  let metaBytes ← match metaKind, metaVal with
    | .ElementCount, v => Type.encodeInt IntType.usize_ty v
    | .VTablePointer _, .Ptr ⟨vtablePtr, none⟩ => encodePtr vtablePtr
    | _, _ => specPanic "as_wide_pair always returns a suitable metadata type"
  pure (thinBytes ++ metaBytes)

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

/-- `Type::decode` for `Bool`, `Int` (`Type.decodeInt`), `Tuple`, `Array`,
`Union`, `Enum`, `Slice`, and `TraitObject` (`spec/lang/representation.md`):
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
> "fn decode<M: Memory>(Type::Array { elem, count }: Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
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
> "fn decode<M: Memory>(Type::Ptr(ptr_type): Self, bytes: List<AbstractByte<M::Provenance>>) -> Option<Value<M>> {
>     if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
>         ..
>     } else {
>         // Handle thin pointers.
>         let ptr = decode_ptr::<M>(bytes)?;
>         ret(Value::Ptr(ptr.widen(None)))
>     }
> }"
The fields of a tuple are decoded by `Type.decodeFields`, the data of an
enum variant by `Type.decodeVariant`, thin pointers by `decodePtr`, and wide
pointers by `decodeWidePtr`. `decode_discriminant` fails only if its
accessor does; this accessor fails only by panicking (`subsliceWithLength` out
of range), so `.unwrap()` is the propagation of that panic. -/
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
  | .Array elem count, bytes => do
    let elemLayout ← Type.layout elem
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
    let fullSize ← Size.mulInt elemSize count
    if bytes.length ≠ fullSize.bytes then
      specPanic "decode of Type::Array with invalid length"
    else do
      let chunks ← (List.range count.toNat).mapM (fun (i : Nat) =>
        subsliceWithLength bytes ((i : Int) * (elemSize.bytes : Int)) elemSize.bytes)
      let decoded ← tryMapM (fun elemBytes => Type.decode elem elemBytes) chunks
      pure (decoded.map Value.Tuple)
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
  | .Ptr ptrType, bytes =>
    match PtrType.as_wide_pair ptrType with
    | some _ => decodeWidePtr (PtrType.meta_kind ptrType) bytes
    | none => do
      match ← decodePtr bytes with
      | some ptr => pure (some (.Ptr (ThinPointer.widen ptr none)))
      | none => pure none

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

/-- `Type::encode` for `Bool`, `Int` (`Type.encodeInt`), `Tuple`, `Array`,
`Union`, `Enum`, `Slice`, and `TraitObject` (`spec/lang/representation.md`):
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
> "fn encode<M: Memory>(Type::Array { elem, count }: Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
>     let Value::Tuple(values) = val else { panic!() };
>     assert_eq!(values.len(), count);
>     values.flat_map(|value| {
>         let bytes = elem.encode::<M>(value);
>         assert_eq!(bytes.len(), elem.layout::<M::T>().expect_size(\"WF ensures array element is sized\").bytes());
>         bytes
>     })
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
> "fn encode<M: Memory>(Type::Ptr(ptr_type): Self, val: Value<M>) -> List<AbstractByte<M::Provenance>> {
>     let Value::Ptr(ptr) = val else { panic!(\"val is WF for a pointer\") };
>
>     if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
>         ..
>     } else {
>         // Handle thin pointers.
>         assert!(ptr.metadata.is_none(), \"ptr_type and value have mismatching metadata\");
>         encode_ptr::<M>(ptr.thin_pointer)
>     }
> }"
The fields of a tuple are encoded by `Type.encodeFields`, the chunks of a
union by `Type.encodeUnionChunks`, the variant of an enum by
`Type.encodeVariant`, thin pointers by `encodePtr`, and wide pointers by
`encodeWidePtr`. -/
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
  | .Array elem count, .Tuple values =>
    if (values.length : Int) ≠ count then
      specPanic "encode: Type::Array length mismatch"
    else do
      let encoded ← values.mapM (fun value => do
        let bytes ← Type.encode elem value
        let elemLayout ← Type.layout elem
        let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
        if bytes.length ≠ elemSize.bytes then
          specPanic "encode: Type::Array element byte length mismatch"
        else
          pure bytes)
      pure encoded.flatten
  | .Array _ _, _ => specPanic "encode: Type::Array with a non-Tuple value"
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
  | .Ptr ptrType, val =>
    match val with
    | .Ptr ptr =>
      match PtrType.as_wide_pair ptrType with
      | some _ => encodeWidePtr (PtrType.meta_kind ptrType) ptr
      | none =>
        match ptr.metadata with
        | none => encodePtr ptr.thin_pointer
        | some _ => specPanic "assertion failed: ptr_type and value have mismatching metadata"
    | _ => specPanic "val is WF for a pointer"

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

/-! ## `BasicMemory` (`spec/mem/basic.md`) -/

/-- `BasicMemory::new` (`spec/mem/basic.md`):
> "impl<T: Target, ProvExtra, AllocExtra> BasicMemory<T, ProvExtra, AllocExtra> {
>     fn new() -> Self {
>         Self { allocations: List::new(), _phantom: std::marker::PhantomData }
>     }
> }" -/
def BasicMemory.new {ProvExtra AllocExtra : Type} : BasicMemory x86_64 ProvExtra AllocExtra :=
  { allocations := [], _phantom := ⟨⟩ }

/-- `Allocation::size`:
> "fn size(self) -> Size { Size::from_bytes(self.data.len()).unwrap() }" -/
def Allocation.size {ProvExtra AllocExtra : Type} (a : Allocation ProvExtra AllocExtra) : Size :=
  ⟨a.data.length⟩

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
def Allocation.overlaps {ProvExtra AllocExtra : Type} (a : Allocation ProvExtra AllocExtra)
    (otherAddr : Address) (otherSize : Size) : Bool :=
  let endAddr : Int := a.addr + (Allocation.size a).bytes
  let otherEndAddr : Int := otherAddr + otherSize.bytes
  if endAddr ≤ otherAddr ∨ otherEndAddr ≤ a.addr then
    decide (a.addr = otherAddr)
  else
    true

/-- Polymorphic `BasicMemory::allocate` address-choice predicate (`spec/mem/basic.md`):
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
def BasicMemory.allocAddrOk {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra) (size : Size) (align : Align) (addr : Int) : Bool :=
  if addr ≤ 0 then false
  else if !Align.is_aligned align addr then false
  else if !inBounds (addr + size.bytes) .Unsigned x86_64.PTR_SIZE then false
  else if mem.allocations.any (fun a => a.live && Allocation.overlaps a addr size) then false
  else true

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
this interpretation hold for this resolution of the choice. A program can
observe addresses through pointer-to-integer casts
(`PointerExposeProvenance`), pointer comparisons (`comparePtr`), and the
alignment check of an access through a pointer whose type demands more
alignment than its allocation guarantees (the first-fit addresses are
multiples of `2^32`, so such a check always passes here although it fails
for other valid addresses); results about such programs hold for the
first-fit addresses only. -/
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

/-- First-fit candidate search for polymorphic `BasicMemory::allocate` (`spec/mem/basic.md`):
> "let addr = pick(distr, |addr: Address| {" -/
def BasicMemory.firstFitAddr {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra) (size : Size) (align : Align) :
    Nat → Nat → Option Int
  | 0, _ => none
  | fuel + 1, k =>
    if BasicMemory.allocAddrOk mem size align (allocCandidate k) then some (allocCandidate k)
    else BasicMemory.firstFitAddr mem size align fuel (k + 1)

/-- First-fit resolution of the daemonic address choice in polymorphic
`BasicMemory::allocate` (`spec/mem/basic.md`):
> "let distr = libspecr::IntDistribution {
>      start: Int::ONE,
>      end: Int::from(2).pow(T::PTR_SIZE.bits()),
>      divisor: align.bytes(),
>  };" -/
def BasicMemory.pickAddr {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra) (size : Size) (align : Align) : Option Int :=
  BasicMemory.firstFitAddr mem size align (2 ^ 32 - 1) 0

/-- Polymorphic `BasicMemory::allocate` (`spec/mem/basic.md`):
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
def BasicMemory.allocate {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra) (kind : AllocationKind) (size : Size)
    (align : Align) (provExtra : ProvExtra) (allocExtra : AllocExtra) :
    Interp (ThinPointer (Provenance ProvExtra) × BasicMemory x86_64 ProvExtra AllocExtra) :=
  if !x86_64.valid_size size then ub "asking for a too large allocation"
  else
    match BasicMemory.pickAddr mem size align with
    | none => unsupported "allocate: no candidate address of the first-fit resolution is free"
    | some addr =>
      let allocation : Allocation ProvExtra AllocExtra := {
        addr := addr
        align := align
        kind := kind
        live := true
        data := List.replicate size.bytes .Uninit
        extra := allocExtra
      }
      let id : AllocId := ⟨mem.allocations.length⟩
      let allocations := mem.allocations ++ [allocation]
      pure ({ addr := addr, provenance := some (id, provExtra) },
        { mem with allocations := allocations })

/-- Polymorphic `BasicMemory::deallocate` (`spec/mem/basic.md`) with `handle_extra`:
> "fn deallocate(
>     &mut self,
>     ptr: ThinPointer<Provenance<ProvExtra>>,
>     kind: AllocationKind,
>     size: Size,
>     align: Align,
>     handle_extra: impl FnOnce(&mut AllocExtra, ProvExtra) -> Result,
> ) -> Result {
>     let Some((id, prov_extra)) = ptr.provenance else {
>         throw_ub!(\"deallocating invalid pointer\")
>     };
>     // This lookup will definitely work, since AllocId cannot be faked.
>     let mut allocation = self.allocations[id.0];
>
>     // Check a bunch of things.
>     if !allocation.live {
>         throw_ub!(\"double-free\");
>     }
>     if ptr.addr != allocation.addr {
>         throw_ub!(\"deallocating with pointer not to the beginning of its allocation\");
>     }
>     if kind != allocation.kind {
>         throw_ub!(\"deallocating {:?} memory with {:?} deallocation operation\", allocation.kind, kind);
>     }
>     if size != allocation.size() {
>         throw_ub!(\"deallocating with incorrect size information\");
>     }
>     if align != allocation.align {
>         throw_ub!(\"deallocating with incorrect alignment information\");
>     }
>
>     // Check \"extra\" things.
>     handle_extra(&mut allocation.extra, prov_extra)?;
>
>     // Mark it as dead.
>     allocation.live = false;
>
>     // That's it!
>     self.allocations.set(id.0, allocation);
>
>     ret(())
> }" -/
def BasicMemory.deallocate {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (kind : AllocationKind) (size : Size)
    (align : Align) (handleExtra : AllocExtra → ProvExtra → Interp AllocExtra) :
    Interp (BasicMemory x86_64 ProvExtra AllocExtra) :=
  match ptr.provenance with
  | none => ub "deallocating invalid pointer"
  | some (id, provExtra) => do
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
      let extra' ← handleExtra allocation.extra provExtra
      let allocations ←
        listSet mem.allocations id._0 { allocation with live := false, extra := extra' } "set"
      pure { mem with allocations := allocations }

/-- Polymorphic `BasicMemory::check_ptr` (`spec/mem/basic.md`):
> "fn check_ptr(&self, ptr: ThinPointer<Provenance<ProvExtra>>, len: Size) -> Result<Option<(AllocId, ProvExtra, Size)>> {
>     if len.is_zero() {
>         return ret(None);
>     }
>     let Some((id, prov_extra)) = ptr.provenance else {
>         throw_ub!(\"dereferencing pointer without provenance\");
>     };
>     let allocation = self.allocations[id.0];
>     if !allocation.live {
>         throw_ub!(\"dereferencing pointer to dead allocation\");
>     }
>     let offset_in_alloc = ptr.addr - allocation.addr;
>     if offset_in_alloc < 0 || offset_in_alloc + len.bytes() > allocation.size().bytes() {
>         throw_ub!(\"dereferencing pointer outside the bounds of its allocation\");
>     }
>     ret(Some((id, prov_extra, Offset::from_bytes(offset_in_alloc).unwrap())))
> }" -/
def BasicMemory.check_ptr {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (len : Size) :
    Interp (Option (AllocId × ProvExtra × Size)) :=
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

/-- Polymorphic `BasicMemory::store` (`spec/mem/basic.md`) with `handle_extra`:
> "fn store(
>     &mut self,
>     ptr: ThinPointer<Provenance<ProvExtra>>,
>     bytes: List<AbstractByte<Provenance<ProvExtra>>>,
>     align: Align,
>     handle_extra: impl FnOnce(&mut AllocExtra, ProvExtra, Offset) -> Result,
> ) -> Result {
>     if !align.is_aligned(ptr.addr) {
>         throw_ub!(\"store to a misaligned pointer\");
>     }
>     let size = Size::from_bytes(bytes.len()).unwrap();
>     let Some((id, prov_extra, offset)) = self.check_ptr(ptr, size)? else {
>         return ret(());
>     };
>     let mut allocation = self.allocations[id.0];
>     handle_extra(&mut allocation.extra, prov_extra, offset)?;
>     allocation.data.write_subslice_at_index(offset.bytes(), bytes);
>     self.allocations.set(id.0, allocation);
>     ret(())
> }" -/
def BasicMemory.store {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra))
    (bytes : List (AbstractByte (Provenance ProvExtra))) (align : Align)
    (handleExtra : AllocExtra → ProvExtra → Offset → Interp AllocExtra) :
    Interp (BasicMemory x86_64 ProvExtra AllocExtra) :=
  if !Align.is_aligned align ptr.addr then ub "store to a misaligned pointer"
  else do
    match ← BasicMemory.check_ptr mem ptr ⟨bytes.length⟩ with
    | none => pure mem
    | some (id, provExtra, offset) => do
      let allocation ← listIndex mem.allocations id._0 "self.allocations[id.0]"
      let extra' ← handleExtra allocation.extra provExtra offset
      let data ← writeSubsliceAtIndex allocation.data offset.bytes bytes
      let allocations ←
        listSet mem.allocations id._0 { allocation with data := data, extra := extra' } "set"
      pure { mem with allocations := allocations }

/-- Polymorphic `BasicMemory::load` (`spec/mem/basic.md`) with `handle_extra`:
> "fn load(
>     &mut self,
>     ptr: ThinPointer<Provenance<ProvExtra>>,
>     len: Size,
>     align: Align,
>     handle_extra: impl FnOnce(&mut AllocExtra, ProvExtra, Offset) -> Result,
> ) -> Result<List<AbstractByte<Provenance<ProvExtra>>>> {
>     if !align.is_aligned(ptr.addr) {
>         throw_ub!(\"load from a misaligned pointer\");
>     }
>     let Some((id, prov_extra, offset)) = self.check_ptr(ptr, len)? else {
>         return ret(list![]);
>     };
>     let mut allocation = self.allocations[id.0];
>     handle_extra(&mut allocation.extra, prov_extra, offset)?;
>     self.allocations.set(id.0, allocation);
>     ret(allocation.data.subslice_with_length(offset.bytes(), len.bytes()))
> }" -/
def BasicMemory.load {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra)
    (ptr : ThinPointer (Provenance ProvExtra)) (len : Size) (align : Align)
    (handleExtra : AllocExtra → ProvExtra → Offset → Interp AllocExtra) :
    Interp (List (AbstractByte (Provenance ProvExtra)) × BasicMemory x86_64 ProvExtra AllocExtra) :=
  if !Align.is_aligned align ptr.addr then ub "load from a misaligned pointer"
  else do
    match ← BasicMemory.check_ptr mem ptr len with
    | none => pure ([], mem)
    | some (id, provExtra, offset) => do
      let allocation ← listIndex mem.allocations id._0 "self.allocations[id.0]"
      let extra' ← handleExtra allocation.extra provExtra offset
      let allocations ← listSet mem.allocations id._0 { allocation with extra := extra' } "set"
      let bytes ← subsliceWithLength allocation.data offset.bytes len.bytes
      pure (bytes, { mem with allocations := allocations })

/-- `BasicMemory::leak_check` (`spec/mem/basic.md`):
> "fn leak_check(&self) -> Result {
>     use AllocationKind::*;
>     for allocation in self.allocations {
>         if allocation.live {
>             match allocation.kind {
>                 // These should all be gone.
>                 Heap => throw_memory_leak!(),
>                 // These we can still have at the end.
>                 Global | Function | Stack | VTable => {}
>             }
>         }
>     }
>     ret(())
> }" -/
def BasicMemory.leak_check {ProvExtra AllocExtra : Type}
    (mem : BasicMemory x86_64 ProvExtra AllocExtra) : Interp Unit :=
  if mem.allocations.any (fun a => a.live && decide (a.kind = .Heap)) then
    memoryLeak
  else
    pure ()

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

/-- `StackFrame::jump_to_block` (`spec/lang/machine.md`):
> "self.next_block = b; self.next_stmt = Int::ZERO;"
and `Machine::jump_to_block` (`spec/lang/step/terminators.md`):
> "self.try_mutate_cur_frame(|frame, _mem| { frame.jump_to_block(block); ret(()) })" -/
def jumpToBlock (m : Mach) (b : BbName) : Interp Mach :=
  mutateCurFrame m (fun fr => { fr with next_block := b, next_stmt := 0 })

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

/-- `Machine::check_ptr_metadata` (`spec/lang/representation.md`):
> "fn check_ptr_metadata(&self, meta: Option<PointerMeta<M::Provenance>>, kind: PointerMetaKind) -> Result {
>     match (meta, kind) {
>         (None, PointerMetaKind::None) => {}
>         (Some(PointerMeta::ElementCount(num)), PointerMetaKind::ElementCount) =>
>             self.check_value(Value::Int(num), Type::Int(IntType::usize_ty::<M::T>()))?,
>         (Some(PointerMeta::VTablePointer(ptr)), PointerMetaKind::VTablePointer(trait_name)) => {
>             self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))?;
>         }
>         _ => throw_ub!(\"Value::Ptr: invalid metadata\"),
>     };
>
>     Ok(())
> }"
The integer check is `check_value` at `Type::Int`, inlined (it is
`ensure_else_ub(int_ty.can_represent(i), ..)`, see `checkValue`). Checking a
vtable pointer needs the machine's vtables (`Machine::vtable_from_ptr`), so it
is outside the fragment. -/
def checkPtrMetadata (ptrMeta : Option (PointerMeta Prov)) (kind : PointerMetaKind) : Interp Unit :=
  match ptrMeta, kind with
  | none, .None => pure ()
  | some (.ElementCount num), .ElementCount =>
    ensureElseUb (IntType.can_represent IntType.usize_ty num) "Value::Int: invalid integer value"
  | some (.VTablePointer _), .VTablePointer _ =>
    unsupported "check_ptr_metadata for vtable pointer metadata (Machine::vtable_from_ptr)"
  | _, _ => ub "Value::Ptr: invalid metadata"

/-- `Machine::check_ptr` (`spec/lang/representation.md`):
> "fn check_ptr(&self, ptr: Pointer<M::Provenance>, ptr_ty: PtrType) -> Result {
>     ensure_else_ub(ptr.thin_pointer.addr.in_bounds(Unsigned, M::T::PTR_SIZE), \"Value::Ptr: pointer out-of-bounds\")?;
>
>     // This has to be checked first, to ensure we can e.g. compute size/align below.
>     self.check_ptr_metadata(ptr.metadata, ptr_ty.meta_kind())?;
>
>     // Safe pointer, i.e. references, boxes
>     if let Some(pointee) = ptr_ty.safe_pointee() {
>         let size = self.compute_size(pointee.layout, ptr.metadata);
>         let align = self.compute_align(pointee.layout, ptr.metadata);
>         // The total size must be at most `isize::MAX`.
>         ensure_else_ub(size.bytes().in_bounds(Signed, M::T::PTR_SIZE), \"Value::Ptr: total size exeeds isize::MAX\")?;
>
>         // Safe pointers need to be non-null, aligned, dereferenceable, and not point to an uninhabited type.
>         // (Think: uninhabited types have impossible alignment.)
>         ensure_else_ub(ptr.thin_pointer.addr != 0, \"Value::Ptr: null safe pointer\")?;
>         ensure_else_ub(align.is_aligned(ptr.thin_pointer.addr), \"Value::Ptr: unaligned safe pointer\")?;
>         ensure_else_ub(pointee.inhabited, \"Value::Ptr: safe pointer to uninhabited type\")?;
>         ensure_else_ub(
>             self.mem.dereferenceable(ptr.thin_pointer, size).is_ok(),
>             \"Value::Ptr: non-dereferenceable safe pointer\"
>         )?;
>
>         // However, we do not care about the data stored wherever this pointer points to.
>     } else if let PtrType::VTablePtr(trait_name) = ptr_ty {
>         ..
>     }
>
>     Ok(())
> }"
A raw pointer is well formed when its address fits in a `usize` and its
metadata is well formed; nothing is required of its provenance or of the
memory it points to. A safe pointer (`PtrType::Ref` or `PtrType::Box`) must
also have a pointee size fitting in `isize::MAX`, a non-null aligned address,
an inhabited pointee, and dereferenceable memory (`CM.dereferenceable` when a
machine `m` is supplied). -/
def checkPtr (ptr : Pointer Prov) (ptrTy : PtrType) (m : Option Mach := none) : Interp Unit := do
  ensureElseUb (inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE)
    "Value::Ptr: pointer out-of-bounds"
  checkPtrMetadata ptr.metadata (PtrType.meta_kind ptrTy)
  match PtrType.safe_pointee ptrTy with
  | some pointee => do
    let lookup : Ptr → Interp VTable := match m with
      | some mach => vtableLookup mach
      | none => fun _ => unsupported "check_ptr for a trait-object safe pointer without a machine"
    let (size, align) ← LayoutStrategy.compute_size_and_align lookup pointee.layout ptr.metadata
    ensureElseUb (inBounds size.bytes .Signed x86_64.PTR_SIZE)
      "Value::Ptr: total size exeeds isize::MAX"
    ensureElseUb (ptr.thin_pointer.addr != 0)
      "Value::Ptr: null safe pointer"
    ensureElseUb (Align.is_aligned align ptr.thin_pointer.addr)
      "Value::Ptr: unaligned safe pointer"
    ensureElseUb pointee.inhabited
      "Value::Ptr: safe pointer to uninhabited type"
    match m with
    | some mach =>
      match CM.dereferenceable mach.mem ptr.thin_pointer size with
      | .ok () => pure ()
      | .error (.ub _) => ub "Value::Ptr: non-dereferenceable safe pointer"
      | .error e => .error e
    | none =>
      if size.bytes = 0 then pure ()
      else
        match ptr.thin_pointer.provenance with
        | none => ub "Value::Ptr: non-dereferenceable safe pointer"
        | some _ => unsupported "check_ptr for a safe pointer (Memory::dereferenceable)"
  | none =>
    match ptrTy with
    | .VTablePtr _ => unsupported "check_ptr for a vtable pointer (Machine::vtable_from_ptr)"
    | _ => pure ()

mutual

/-- `Machine::check_value` for `Int`, `Bool`, `Ptr`, `Tuple`, `Array`, `Union`,
`Variant`, `Slice`, and `TraitObject` (`spec/lang/representation.md`):
> "(Value::Int(i), Type::Int(int_ty)) => {
>     ensure_else_ub(int_ty.can_represent(i), \"Value::Int: invalid integer value\")?;
> }
> (Value::Bool(_), Type::Bool) => {},
> (Value::Ptr(ptr), Type::Ptr(ptr_ty)) => self.check_ptr(ptr, ptr_ty)?,
> (Value::Tuple(vals), Type::Tuple { sized_fields, unsized_field, .. }) => {
>     assert!(unsized_field.is_none(), \"Value: unsized structs cannot be represented as values\");
>     ensure_else_ub(vals.len() == sized_fields.len(), \"Value::Tuple: invalid number of fields\")?;
>     ..
> }
> (Value::Tuple(vals), Type::Array { elem, count }) => {
>     ensure_else_ub(vals.len() == count, \"Value::Tuple: invalid number of elements\")?;
>     for val in vals {
>         self.check_value(val, elem)?;
>     }
> }
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
`checkUnionChunks`, the data of a variant by `checkVariant`, and pointers by
`checkPtr`. -/
def checkValue (val : Val) (ty : «Type») (m : Option Mach := none) : Interp Unit :=
  match val, ty with
  | .Int i, .Int t =>
    ensureElseUb (IntType.can_represent t i) "Value::Int: invalid integer value"
  | .Bool _, .Bool => pure ()
  | .Ptr ptr, .Ptr ptrTy => checkPtr ptr ptrTy m
  | .Tuple vals, .Tuple fields _ unsizedField =>
    match unsizedField with
    | some _ => specPanic "Value: unsized structs cannot be represented as values"
    | none => do
      ensureElseUb (vals.length == fields.length) "Value::Tuple: invalid number of fields"
      checkFields vals fields m
  | .Tuple vals, .Array elem count => do
    ensureElseUb (decide ((vals.length : Int) = count)) "Value::Tuple: invalid number of elements"
    vals.forM (fun val => checkValue val elem m)
  | .Union chunkData, .Union _ chunks _ _ => do
    ensureElseUb (chunkData.length == chunks.length) "Value::Union: invalid chunk size"
    checkUnionChunks chunkData chunks
  | .Variant discriminant data, .Enum ⟨variants⟩ _ _ _ _ => checkVariant variants discriminant data m
  | _, .Slice _ => specPanic "Value: slices cannot be represented as values"
  | _, .TraitObject _ => specPanic "Value: trait objects cannot be represented as values"
  | _, .Int _ => specPanic "Value: value does not match type"
  | _, .Bool => specPanic "Value: value does not match type"
  | _, .Tuple _ _ _ => specPanic "Value: value does not match type"
  | _, .Array _ _ => specPanic "Value: value does not match type"
  | _, .Union _ _ _ _ => specPanic "Value: value does not match type"
  | _, .Enum _ _ _ _ _ => specPanic "Value: value does not match type"
  | _, .Ptr _ => specPanic "Value: value does not match type"

/-- The field loop of `check_value` for tuples (`spec/lang/representation.md`):
> "for (val, (_, ty)) in vals.zip(sized_fields) {
>     self.check_value(val, ty)?;
> }" -/
def checkFields : List Val → List (Offset × «Type») → (m : Option Mach := none) → Interp Unit
  | val :: vals, (_, ty) :: fields, m => do
    checkValue val ty m
    checkFields vals fields m
  | _, _, _ => pure ()

/-- The variant lookup of `check_value` for enums
(`spec/lang/representation.md`):
> "let Some(variant) = variants.get(discriminant) else {
>     throw_ub!(\"Value::Variant: invalid discrimant\");
> };
> self.check_value(data, variant.ty)?;"
`variants.get(discriminant)` is the first entry for `discriminant`, as in
`mapGet`. -/
def checkVariant : List (Int × Variant) → Int → Val → (m : Option Mach := none) → Interp Unit
  | [], _, _, _ => ub "Value::Variant: invalid discrimant"
  | (d, ⟨ty, _⟩) :: rest, discriminant, data, m =>
    if d = discriminant then checkValue data ty m else checkVariant rest discriminant data m

end

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
  | some val => do checkValue val ty (some m); pure (val, m)
  | none => ub "load at type but the data in memory violates the language invariant"

/-- `Machine::typed_store`:
> "assert!(self.check_value(val, ty).is_ok(), ..);
>  let bytes = ty.encode::<M>(val);
>  self.mem.store(ptr, bytes, align, atomicity)?;" -/
def typedStore (m : Mach) (ptr : Ptr) (val : Val) (ty : «Type») (align : Align)
    (atomicity : Atomicity) : Interp Mach := do
  match checkValue val ty (some m) with
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
def transmute (val : Val) (type1 type2 : «Type») (m : Option Mach := none) : Interp Val := do
  let size1 ← LayoutStrategy.expect_size (← Type.layout type1) "WF ensures sized operands"
  let size2 ← LayoutStrategy.expect_size (← Type.layout type2) "WF ensures sized operands"
  if size1 ≠ size2 then specPanic "assertion failed: transmute between types of different size"
  else do
    let bytes ← Type.encode type1 val
    match ← Type.decode type2 bytes with
    | some rawValue => do checkValue rawValue type2 m; pure rawValue
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

/-- `Machine::eval_constant` for the constants that need no global, function,
or vtable pointer of the machine:
> "Constant::Int(i) => Value::Int(i),
>  Constant::Bool(b) => Value::Bool(b),"
> "Constant::PointerWithoutProvenance(addr) => {
>     Value::Ptr(ThinPointer {
>         addr,
>         provenance: None,
>     }.widen(None))
> }" -/
def evalConstant : Constant → Interp Val
  | .Int i => pure (.Int i)
  | .Bool b => pure (.Bool b)
  | .PointerWithoutProvenance addr =>
    pure (.Ptr (ThinPointer.widen { addr := addr, provenance := none } none))
  | _ => unsupported "eval_constant for a global, function, or vtable pointer constant"

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
def evalCastOp (castOp : CastOp) (arg : Val × «Type») (m : Option Mach := none) :
    Interp (Val × «Type») :=
  match castOp, arg with
  | .IntToInt intTy, (.Int operand, _) =>
    pure (.Int (IntType.bring_in_bounds intTy operand), .Int intTy)
  | .IntToInt _, _ => specPanic "non-integer input to int-to-int cast"
  | .Transmute newTy, (operand, oldTy) => do
    let oldSize ← LayoutStrategy.expect_size (← Type.layout oldTy) "WF ensures transmutes are sized"
    let newSize ← LayoutStrategy.expect_size (← Type.layout newTy) "WF ensures transmutes are sized"
    if oldSize ≠ newSize then ub "transmute between types of different size"
    else do
      let val ← transmute operand oldTy newTy m
      pure (val, newTy)

/-- `Machine::eval_un_op` for `UnOp::Int`, `UnOp::Cast`, and
`UnOp::GetThinPointer` (`spec/lang/step/operators.md`):
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
> }"
and `UnOp::GetThinPointer`, which `minimize` emits for a `PtrToPtr` cast from
a wide to a thin raw pointer:
> "fn eval_un_op(&self, UnOp::GetThinPointer: UnOp, (operand, op_ty): (Value<M>, Type)) -> Result<(Value<M>, Type)> {
>     let Value::Ptr(ptr) = operand else { panic!(\"non-pointer GetThinPointer\") };
>
>     let thin_ptr = Pointer { metadata: None, ..ptr };
>     let thin_ptr_ty = PtrType::Raw { meta_kind: PointerMetaKind::None };
>     ret((Value::Ptr(thin_ptr), Type::Ptr(thin_ptr_ty)))
> }" -/
def evalUnOp (op : UnOp) (arg : Val × «Type») (m : Option Mach := none) :
    Interp (Val × «Type») :=
  match op, arg with
  | .Int op, (.Int operand, .Int intTy) => do
    let retTy := match op with
      | .CountOnes => ⟨.Unsigned, ⟨4⟩⟩
      | _ => intTy
    let result : Val := .Int (← evalIntUnOp op operand intTy)
    match checkValue result (.Int retTy) m with
    | .ok () => pure (result, .Int retTy)
    | .error _ => specPanic "sanity check: result of UnOp::Int does not fit in the return type"
  | .Int _, _ => specPanic "non-integer input to integer operation"
  | .Cast castOp, arg => evalCastOp castOp arg m
  | .GetThinPointer, (.Ptr ptr, _) => pure (.Ptr { ptr with metadata := none }, .Ptr (.Raw .None))
  | .GetThinPointer, _ => specPanic "non-pointer GetThinPointer"
  | _, _ => unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}"

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

/-- `Machine::compare_ptr` (`spec/lang/step/operators.md`), which orders
pointers by address and then by metadata, ignoring provenance:
> "fn compare_ptr(left: Pointer<M::Provenance>, right: Pointer<M::Provenance>) -> std::cmp::Ordering {
>     let thin_cmp = left.thin_pointer.addr.cmp(&right.thin_pointer.addr);
>     let meta_cmp = match (left.metadata, right.metadata) {
>         (None, None) => std::cmp::Ordering::Equal,
>         (Some(PointerMeta::ElementCount(l)), Some(PointerMeta::ElementCount(r))) => l.cmp(&r),
>         (Some(PointerMeta::VTablePointer(l)), Some(PointerMeta::VTablePointer(r))) => l.addr.cmp(&r.addr),
>         _ => panic!(\"unmatching metadata in wide pointer comparasion\"),
>     };
>     // Lexicographically compare on first the thin pointer and then the metadata
>     thin_cmp.then(meta_cmp)
> }"
Rust's `Ordering::then` keeps the first ordering unless it is `Equal`, as
Lean's `Ordering.then` does. -/
def comparePtr (left right : Pointer Prov) : Interp Ordering := do
  let thinCmp := intCmp left.thin_pointer.addr right.thin_pointer.addr
  let metaCmp ← match left.metadata, right.metadata with
    | none, none => pure Ordering.eq
    | some (.ElementCount l), some (.ElementCount r) => pure (intCmp l r)
    | some (.VTablePointer l), some (.VTablePointer r) => pure (intCmp l.addr r.addr)
    | _, _ => specPanic "unmatching metadata in wide pointer comparasion"
  pure (thinCmp.then metaCmp)

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
`false < true` (`boolCmp`), and pointers by address and metadata
(`comparePtr`). The pointer operators `BinOp::PtrOffset` and
`BinOp::PtrOffsetFrom` read the machine's memory and are evaluated by
`evalPtrOffset` and `evalPtrOffsetFrom` instead. -/
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
    | .Ptr _, .Ptr left, .Ptr right => do pure (evalRelOp relOp (← comparePtr left right))
    | _, _, _ => specPanic "relational operator on incomparable type or value-type mismatch"
  | _, _, _ => unsupported "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel"

/-! ## Pointer arithmetic (`spec/lang/step/operators.md`) -/

/-- `Machine::ptr_offset_wrapping` (`spec/lang/step/operators.md`):
> "/// Perform a wrapping offset on the given pointer. (Can never fail.)
> fn ptr_offset_wrapping(&self, ptr: ThinPointer<M::Provenance>, offset: Int) -> ThinPointer<M::Provenance> {
>     ptr.wrapping_offset::<M::T>(offset)
> }" -/
def ptrOffsetWrapping (ptr : Ptr) (offset : Int) : Ptr :=
  ThinPointer.wrapping_offset ptr offset

/-- `Machine::eval_bin_op` for `BinOp::PtrOffset` (`spec/lang/step/operators.md`),
which offsets a thin pointer by a byte count, either checking that the whole
range stays inside one live allocation (`inbounds`, `ptrOffsetInbounds`) or
wrapping around the address space (`ptrOffsetWrapping`). The result keeps the
type of the left operand:
> "fn eval_bin_op(
>     &self,
>     BinOp::PtrOffset { inbounds }: BinOp,
>     (left, l_ty): (Value<M>, Type),
>     (right, _r_ty): (Value<M>, Type)
> ) -> Result<(Value<M>, Type)> {
>     let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left else {
>         panic!(\"non-thin-pointer left input to `PtrOffset`\")
>     };
>     let Value::Int(right) = right else { panic!(\"non-integer right input to `PtrOffset`\") };
>
>     let offset_ptr = if inbounds {
>         self.ptr_offset_inbounds(left, right)?
>     } else {
>         self.ptr_offset_wrapping(left, right)
>     };
>     ret((Value::Ptr(offset_ptr.widen(None)), l_ty))
> }"
`self` is the machine after both operands were evaluated (`evalValue`). -/
def evalPtrOffset (m : Mach) (inbounds : Bool) (l r : Val × «Type») : Interp (Val × «Type») :=
  match l, r with
  | (.Ptr ⟨left, none⟩, lTy), (.Int right, _) => do
    let offsetPtr ← if inbounds then ptrOffsetInbounds m left right
      else pure (ptrOffsetWrapping left right)
    pure (.Ptr (ThinPointer.widen offsetPtr none), lTy)
  | (.Ptr ⟨_, none⟩, _), _ => specPanic "non-integer right input to `PtrOffset`"
  | _, _ => specPanic "non-thin-pointer left input to `PtrOffset`"

/-- `Machine::eval_bin_op` for `BinOp::PtrOffsetFrom`
(`spec/lang/step/operators.md`), the signed byte distance between two thin
pointers:
> "fn eval_bin_op(
>     &self,
>     BinOp::PtrOffsetFrom { inbounds, nonneg }: BinOp,
>     (left, l_ty): (Value<M>, Type),
>     (right, _r_ty): (Value<M>, Type)
> ) -> Result<(Value<M>, Type)> {
>     let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left else {
>         panic!(\"non-thin-pointer left input to `PtrOffsetFrom`\")
>     };
>     let Value::Ptr(Pointer { thin_pointer: right, metadata: None }) = right else {
>         panic!(\"non-thin-pointer right input to `PtrOffsetFrom`\")
>     };
>
>     let distance = left.addr - right.addr;
>     let distance = if inbounds {
>         // The \"gap\" between the two pointers must be dereferenceable from both of them.
>         // This check also ensures that the distance is inbounds of `isize`.
>         self.mem.signed_dereferenceable(left, -distance)?;
>         self.mem.signed_dereferenceable(right, distance)?;
>         // All checked!
>         distance
>     } else {
>         distance.bring_in_bounds(Signed, M::T::PTR_SIZE)
>     };
>
>     if nonneg && distance < Int::ZERO {
>         throw_ub!(\"PtrOffsetFrom: negative result with `nonneg` flag set\");
>     }
>
>     let isize_int = IntType { signed: Signed, size: M::T::PTR_SIZE };
>     ret((Value::Int(distance), Type::Int(isize_int)))
> }" -/
def evalPtrOffsetFrom (m : Mach) (inbounds nonneg : Bool) (l r : Val × «Type») :
    Interp (Val × «Type») :=
  match l, r with
  | (.Ptr ⟨left, none⟩, _), (.Ptr ⟨right, none⟩, _) => do
    let distance : Int := left.addr - right.addr
    let distance ← if inbounds then do
        CM.signed_dereferenceable m.mem left (-distance)
        CM.signed_dereferenceable m.mem right distance
        pure distance
      else pure (bringInBounds distance .Signed x86_64.PTR_SIZE)
    if nonneg && decide (distance < 0) then
      ub "PtrOffsetFrom: negative result with `nonneg` flag set"
    else
      pure (.Int distance, .Int ⟨.Signed, x86_64.PTR_SIZE⟩)
  | (.Ptr ⟨_, none⟩, _), _ => specPanic "non-thin-pointer right input to `PtrOffsetFrom`"
  | _, _ => specPanic "non-thin-pointer left input to `PtrOffsetFrom`"

/-- The retag of `ValueExpr::AddrOf`, `Machine::mutate_cur_frame` applied to
the memory model's `retag_ptr`. `Machine::mutate_cur_frame`
(`spec/lang/machine.md`) runs the closure on the active thread's current
frame:
> "fn mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> O) -> O {
>     self.threads.mutate_at(self.active_thread, |thread| thread.mutate_cur_frame(|frame| f(frame, &mut self.mem)))
> }"
> "fn mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>) -> O) -> O {
>     if self.stack.is_empty() {
>         panic!(\"`mutate_cur_frame` called on empty stack!\");
>     }
>
>     let last_idx = self.stack.len() - 1;
>     self.stack.mutate_at(last_idx, f)
> }"
and `BasicMemory` does not override the default `retag_ptr` of the `Memory`
trait (`spec/mem/interface.md`), which returns the pointer unchanged:
> "fn retag_ptr(
>     &mut self,
>     _frame_extra: &mut Self::FrameExtra,
>     ptr: Pointer<Self::Provenance>,
>     _ptr_type: PtrType,
>     _fn_entry: bool,
>     _fn_implicit_writes: bool,
>     _vtable_lookup: impl Fn(ThinPointer<Self::Provenance>) -> crate::lang::VTable + 'static,
> ) -> Result<Pointer<Self::Provenance>> {
>     ret(ptr)
> }"
The closure changes neither the frame nor memory, so the machine is
unchanged; only the panics of `mutate_at` (an out-of-range active thread) and
of `Thread::mutate_cur_frame` (an empty stack) remain. -/
def retagPtrBM (m : Mach) (ptr : Pointer Prov) : Interp (Pointer Prov) := do
  let t ← listIndex m.threads m.active_thread "self.threads.mutate_at(self.active_thread, ..)"
  if t.stack.isEmpty then specPanic "`mutate_cur_frame` called on empty stack!"
  else pure ptr

/-! ## Place and value expressions (`spec/lang/step/expressions.md`) -/

mutual

/-- `Machine::eval_place` for `PlaceExpr::Local`, `PlaceExpr::Field`,
`PlaceExpr::Index`, and `PlaceExpr::Deref` (`spec/lang/step/expressions.md`):
> "let ty = self.cur_frame().func.locals[name];
>  let Some(ptr) = self.cur_frame().locals.get(name) else {
>      throw_ub!(\"access to a dead local\");
>  };
>  ret((Place { ptr: ptr.widen(None), aligned: true }, ty))"
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
> }
>
> fn eval_place(&mut self, PlaceExpr::Index { root, index }: PlaceExpr) -> Result<(Place<M>, Type)> {
>     let (root, ty) = self.eval_place(root)?;
>     let (Value::Int(index), _) = self.eval_value(index)? else {
>         panic!(\"non-integer operand for array index\")
>     };
>     let (elem_ty, count) = match ty {
>         Type::Array { elem, count } => (elem, count),
>         Type::Slice { elem } => {
>             let Some(PointerMeta::ElementCount(count)) = root.ptr.metadata else {
>                 panic!(\"eval_place should always return a ptr which matches meta for the LayoutStrategy of ty\");
>             };
>             (elem, count)
>         }
>         _ => panic!(\"index projection on non-indexable type\"),
>     };
>     if index < 0 || index >= count {
>         throw_ub!(\"access to out-of-bounds index\");
>     }
>
>     let elem_size = elem_ty.layout::<M::T>().expect_size(\"WF ensures array & slice elements are sized\");
>     let offset = index * elem_size;
>     assert!(
>         offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata),
>         \"sanity check: the indexed offset should not be outside what the type allows.\"
>     );
>
>     let ptr = self.ptr_offset_inbounds(root.ptr.thin_pointer, offset.bytes())?;
>     ret((Place { ptr: ptr.widen(None), ..root }, elem_ty))
> }"
and for `PlaceExpr::Deref`, which turns a pointer value into a place. The
place of a raw pointer may be misaligned, null, or dangling: only loads and
stores through it check the alignment (`placeLoad`, `placeStore`) and the
memory (`BM.check_ptr`):
> "fn eval_place(&mut self, PlaceExpr::Deref { operand, ty }: PlaceExpr) -> Result<(Place<M>, Type)> {
>     let (Value::Ptr(ptr), Type::Ptr(ptr_type)) = self.eval_value(operand)? else {
>         panic!(\"dereferencing a non-pointer\")
>     };
>     // We know the pointer is valid for its type, but make sure safe pointers are also dereferenceable.
>     // (We don't do a full retag here, this is not considered creating a new pointer.)
>     if let Some(pointee) = ptr_type.safe_pointee() {
>         // this was already checked when the value got created
>         assert!(self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr));
>         self.mem.dereferenceable(ptr.thin_pointer, self.compute_size(pointee.layout, ptr.metadata))?;
>     }
>     // Check whether this pointer is sufficiently aligned.
>     // Don't error immediately though! Unaligned places can still be turned into raw pointers.
>     // However, they cannot be loaded from.
>     let aligned = self.compute_align(ty.layout::<M::T>(), ptr.metadata).is_aligned(ptr.thin_pointer.addr);
>
>     ret((Place { ptr, aligned }, ty))
> }" -/
def evalPlace (m : Mach) : PlaceExpr → Interp ((Place BM × «Type») × Mach)
  | .Local name => do
    let fr ← curFrame m
    let ty ← mapIndex fr.func.locals name "self.cur_frame().func.locals[name]"
    match mapGet fr.locals name with
    | none => ub "access to a dead local"
    | some ptr => pure (({ ptr := ThinPointer.widen ptr none, aligned := true }, ty), m)
  | .Field root field => do
    let ((root, ty), m) ← evalPlace m root
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
      pure (({ root with ptr := ptr }, fieldTy), m)
  | .Index root index => do
    let ((root, ty), m) ← evalPlace m root
    let ((idxVal, _), m) ← evalValue m index
    let idx ← match idxVal with
      | .Int i => pure i
      | _ => specPanic "non-integer operand for array index"
    let (elemTy, count) ← match ty with
      | .Array elem count => pure (elem, count)
      | .Slice elem =>
        match root.ptr.metadata with
        | some (.ElementCount count) => pure (elem, count)
        | _ => specPanic "eval_place should always return a ptr which matches meta for the LayoutStrategy of ty"
      | _ => specPanic "index projection on non-indexable type"
    if idx < 0 ∨ idx ≥ count then
      ub "access to out-of-bounds index"
    else do
      let elemLayout ← Type.layout elemTy
      let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
      let offset ← Size.mulInt elemSize idx
      let rootSize ← computeSize m (← Type.layout ty) root.ptr.metadata
      if offset.bytes ≤ rootSize.bytes then
        let ptr ← ptrOffsetInbounds m root.ptr.thin_pointer (offset.bytes : Int)
        pure (({ root with ptr := ThinPointer.widen ptr none }, elemTy), m)
      else
        specPanic "sanity check: the indexed offset should not be outside what the type allows."
  | .Deref operand ty => do
    let ((v, vTy), m) ← evalValue m operand
    match v, vTy with
    | .Ptr ptr, .Ptr ptrType => do
      match PtrType.safe_pointee ptrType with
      | some pointee => do
        let pointeeAlign ← computeAlign m pointee.layout ptr.metadata
        if !Align.is_aligned pointeeAlign ptr.thin_pointer.addr then
          specPanic "assertion failed: self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr)"
        else do
          let pointeeSize ← computeSize m pointee.layout ptr.metadata
          CM.dereferenceable m.mem ptr.thin_pointer pointeeSize
      | none => pure ()
      let align ← computeAlign m (← Type.layout ty) ptr.metadata
      pure (({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr }, ty), m)
    | _, _ => specPanic "dereferencing a non-pointer"
  | _ => unsupported "eval_place for a place expression other than Local, Deref, Field, or Index"

/-- `Machine::eval_value` for `Constant`, `Tuple`, `Load`, `AddrOf`, `UnOp`, and
`BinOp`:
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
> }"
and for `ValueExpr::AddrOf`, which turns a place into the pointer it denotes,
checks that this pointer is a valid value of the pointer type, and lets the
aliasing model retag it (`retagPtrBM`, the identity for `BasicMemory`):
> "fn eval_value(&mut self, ValueExpr::AddrOf { target, ptr_ty }: ValueExpr) -> Result<(Value<M>, Type)> {
>     let (place, _ty) = self.eval_place(target)?;
>
>     // Make sure the new pointer has a valid address.
>     // Remember that places are basically raw pointers so this is not guaranteed!
>     self.check_value(Value::Ptr(place.ptr), Type::Ptr(ptr_ty))?;
>
>     // Let the aliasing model know.
>     let lookup = self.vtable_lookup();
>     let ptr = self.mutate_cur_frame(|frame, mem| {
>         mem.retag_ptr(&mut frame.extra, place.ptr, ptr_ty, /* fn_entry */ false, /* fn_implicit_writes */ true, lookup)
>     })?;
>
>     ret((Value::Ptr(ptr), Type::Ptr(ptr_ty)))
> }"
`eval_un_op` threads `some m` (after evaluating `operand`) into `evalUnOp` so
`CastOp::Transmute` checks safe-pointer dereferenceability against `m.mem`.
`eval_bin_op` for `BinOp::PtrOffset` and `BinOp::PtrOffsetFrom` reads the
machine's memory, so those operators are evaluated by `evalPtrOffset` and
`evalPtrOffsetFrom` on the machine after both operands, and all others by the
machine-free `evalBinOp`. -/
def evalValue (m : Mach) : ValueExpr → Interp ((Val × «Type») × Mach)
  | .Constant c ty => do pure ((← evalConstant c, ty), m)
  | .Tuple exprs ty => do
    let (vals, m) ← evalValues m exprs
    pure ((.Tuple vals, ty), m)
  | .Load source => do
    let ((place, ty), m) ← evalPlace m source
    let (v, m) ← placeLoad m place ty
    pure ((v, ty), m)
  | .AddrOf target ptrTy => do
    let ((place, _), m) ← evalPlace m target
    checkValue (.Ptr place.ptr) (.Ptr ptrTy) (some m)
    let ptr ← retagPtrBM m place.ptr
    pure ((.Ptr ptr, .Ptr ptrTy), m)
  | .UnOp operator operand => do
    let (arg, m) ← evalValue m operand
    pure (← evalUnOp operator arg (some m), m)
  | .BinOp (.PtrOffset inbounds) left right => do
    let (l, m) ← evalValue m left
    let (r, m) ← evalValue m right
    pure (← evalPtrOffset m inbounds l r, m)
  | .BinOp (.PtrOffsetFrom inbounds nonneg) left right => do
    let (l, m) ← evalValue m left
    let (r, m) ← evalValue m right
    pure (← evalPtrOffsetFrom m inbounds nonneg l r, m)
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

mutual

/-- `Machine::retag_val` (`spec/lang/step/statements.md`, with `retagPtrBM` for
`BasicMemory`):
> "fn retag_val(&mut self, val: Value<M>, ty: Type, fn_entry: bool) -> Result<Value<M>> {
>     ret(match (val, ty) {
>         // no (identifiable) pointers
>         (Value::Int(..) | Value::Bool(..) | Value::Union(..), _) =>
>             val,
>         // base case
>         (Value::Ptr(ptr), Type::Ptr(ptr_type)) => {
>             let lookup = self.vtable_lookup();
>             let val = self.mutate_cur_frame(|frame, mem| { mem.retag_ptr(&mut frame.extra, ptr, ptr_type, fn_entry, frame.func.implicit_writes, lookup) })?;
>             Value::Ptr(val)
>         }
>         // recurse into tuples/arrays/enums
>         (Value::Tuple(vals), Type::Tuple { sized_fields, .. }) =>
>             Value::Tuple(vals.zip(sized_fields).try_map(|(val, (_offset, ty))| self.retag_val(val, ty, fn_entry))?),
>         (Value::Tuple(vals), Type::Array { elem: ty, .. }) =>
>             Value::Tuple(vals.try_map(|val| self.retag_val(val, ty, fn_entry))?),
>         (Value::Variant { discriminant, data }, Type::Enum { variants, .. }) =>
>             Value::Variant { discriminant, data: self.retag_val(data, variants[discriminant].ty, fn_entry)? },
>         _ =>
>             panic!(\"this value does not have that type\"),
>     })
> }" -/
def retagVal (m : Mach) (fnEntry : Bool) : Val → «Type» → Interp Val
  | .Int i, _ => pure (.Int i)
  | .Bool b, _ => pure (.Bool b)
  | .Union chunks, _ => pure (.Union chunks)
  | .Ptr ptr, .Ptr _ => do
    let ptr ← retagPtrBM m ptr
    pure (.Ptr ptr)
  | .Tuple vals, .Tuple sizedFields _ _ => do
    let vals ← retagTupleFields m fnEntry vals sizedFields
    pure (.Tuple vals)
  | .Tuple vals, .Array elemTy _ => do
    let vals ← vals.mapM (fun val => retagVal m fnEntry val elemTy)
    pure (.Tuple vals)
  | .Variant discriminant data, .Enum variants _ _ _ _ => do
    let variant ← mapIndex variants discriminant "variants[discriminant]"
    let data ← retagVal m fnEntry data variant.ty
    pure (.Variant discriminant data)
  | _, .Int _ => specPanic "this value does not have that type"
  | _, .Bool => specPanic "this value does not have that type"
  | _, .Union _ _ _ _ => specPanic "this value does not have that type"
  | _, .Ptr _ => specPanic "this value does not have that type"
  | _, .Tuple _ _ _ => specPanic "this value does not have that type"
  | _, .Array _ _ => specPanic "this value does not have that type"
  | _, .Enum _ _ _ _ _ => specPanic "this value does not have that type"
  | _, .Slice _ => specPanic "this value does not have that type"
  | _, .TraitObject _ => specPanic "this value does not have that type"

/-- The field loop of `Machine::retag_val` for `Type::Tuple`
(`spec/lang/step/statements.md`):
> "vals.zip(sized_fields).try_map(|(val, (_offset, ty))| self.retag_val(val, ty, fn_entry))?"
Note `libspecr::List::zip` asserts `self.len() == other.len()` and panics on
unequal list lengths. -/
def retagTupleFields (m : Mach) (fnEntry : Bool) : List Val → List (Offset × «Type») → Interp (List Val)
  | [], [] => pure []
  | val :: vals, (_, ty) :: fields => do
    let v ← retagVal m fnEntry val ty
    let vs ← retagTupleFields m fnEntry vals fields
    pure (v :: vs)
  | _, _ => specPanic "List::zip: lists have different lengths"

end

/-- `Machine::eval_statement` for `Statement::Assign`, `Statement::PlaceMention`,
`Statement::Validate`, `Statement::Deinit`, `Statement::StorageLive`, and
`Statement::StorageDead` (`spec/lang/step/statements.md`):
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
> fn eval_statement(&mut self, Statement::Validate { place, fn_entry }: Statement) -> NdResult {
>     let (place, ty) = self.eval_place(place)?;
>
>     // WF ensures all valid expressions are sized, so we can invoke the load.
>     // This also ensures the value in the place satsifies the language invariant.
>     let val = self.place_load(place, ty)?;
>     let val = self.retag_val(val, ty, fn_entry)?;
>     self.place_store(place, val, ty)?;
>
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
  | .Validate place fnEntry => do
    let ((p, ty), m) ← evalPlace m place
    let (val, m) ← placeLoad m p ty
    let val ← retagVal m fnEntry val ty
    placeStore m p val ty
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
  | _ => unsupported "eval_statement for a statement other than Assign/PlaceMention/Validate/StorageLive/StorageDead/Deinit"

/-! ## Tree Borrows reborrow settings (`spec/mem/tree_borrows/tree.md`, `spec/mem/tree_borrows/reborrow_settings.md`) -/

/-- `Protected::yes` (`spec/mem/tree_borrows/tree.md`):
> "impl Protected {
>     /// Check whether the node is either strongly or weakly protected.
>     fn yes(self) -> bool {
>         self != Protected::No
>     }
> }" -/
def Protected.yes (p : Protected) : Bool :=
  decide (p ≠ .No)

/-- The `padded_front.zip(padded_back)` loop of `cells_to_freeze_mask`
(`spec/mem/tree_borrows/reborrow_settings.md`):
> "for (current, next) in padded_front.zip(padded_back) {
>     // The `current` bytes are inside an UnsafeCell, and hence not frozen.
>     mask.append(list![false; current.1.bytes()]);
>     // The bytes until `next` are frozen.
>     let no_cell_size = next.0.bytes() - (current.0 + current.1).bytes();
>     mask.append(list![true; no_cell_size]);
> }" -/
def cellsToFreezeMaskLoop (current : Offset × Size) :
    List (Offset × Size) → List Bool → Interp (List Bool)
  | [], mask => pure mask
  | next :: rest, mask =>
    let cellBytes := List.replicate current.2.bytes false
    let noCellSize : Int := (next.1.bytes : Int) - ((current.1.bytes + current.2.bytes : Nat) : Int)
    if noCellSize < 0 then
      specPanic "cells_to_freeze_mask: overlapping or out-of-order UnsafeCell ranges"
    else
      let frozenBytes := List.replicate noCellSize.toNat true
      cellsToFreezeMaskLoop next rest (mask ++ cellBytes ++ frozenBytes)

/-- `cells_to_freeze_mask` (`spec/mem/tree_borrows/reborrow_settings.md`):
> "fn cells_to_freeze_mask(cells: List<(Offset, Size)>, size: Size) -> List<bool> {
>     let padded_front = std::iter::once((Offset::ZERO, Size::ZERO)).chain(cells.iter());
>     let padded_back = cells.iter().chain(std::iter::once((size, Size::ZERO)));
>     ..
>     let mut mask = List::new();
>     for (current, next) in padded_front.zip(padded_back) {
>         // The `current` bytes are inside an UnsafeCell, and hence not frozen.
>         mask.append(list![false; current.1.bytes()]);
>         // The bytes until `next` are frozen.
>         let no_cell_size = next.0.bytes() - (current.0 + current.1).bytes();
>         mask.append(list![true; no_cell_size]);
>     }
>     assert!(mask.len() == size.bytes());
>     mask
> }" -/
def cellsToFreezeMask (cells : List (Offset × Size)) (size : Size) : Interp (List Bool) := do
  let mask ← cellsToFreezeMaskLoop (⟨0⟩, ⟨0⟩) (cells ++ [(size, ⟨0⟩)]) []
  if mask.length ≠ size.bytes then
    specPanic "assertion failed: mask.len() == size.bytes()"
  else
    pure mask

/-- `UnsafeCellStrategy::freeze_mask` (`spec/mem/tree_borrows/reborrow_settings.md`):
> "fn freeze_mask(
>     self,
>     layout: LayoutStrategy,
>     ptr_metadata: Option<PointerMeta<TreeBorrowsProvenance>>,
>     vtable_lookup: impl Fn(ThinPointer<TreeBorrowsProvenance>) -> crate::lang::VTable + 'static,
> ) -> List<bool> {
>     match (self, layout, ptr_metadata) {
>         (UnsafeCellStrategy::Sized { cells }, LayoutStrategy::Sized(size, _align), ..) => {
>             cells_to_freeze_mask(cells, size)
>         },
>         (UnsafeCellStrategy::Slice { element_cells } , LayoutStrategy::Slice(size, _align), Some(PointerMeta::ElementCount(count))) => {
>             let element_mask = cells_to_freeze_mask(element_cells, size);
>             let mut mask = List::new();
>             for _ in Int::ZERO..count {
>                 mask.append(element_mask);
>             };
>             mask
>         },
>         (UnsafeCellStrategy::TraitObject, LayoutStrategy::TraitObject(_trait_name), Some(PointerMeta::VTablePointer(ptr))) => {
>             let vtable = vtable_lookup(ptr);
>             cells_to_freeze_mask(vtable.cells, vtable.size)
>         },
>         (UnsafeCellStrategy::Tuple { head_cells, tail_cells }, LayoutStrategy::Tuple { head, tail }, _) => {
>             let mut mask = cells_to_freeze_mask(head_cells, head.end);
>             mask.append(tail_cells.freeze_mask(tail, ptr_metadata, vtable_lookup));
>             mask
>         },
>         _ => panic!(\"Invalid LayoutStrategy and PointerMeta combination\"),
>     }
> }" -/
def UnsafeCellStrategy.freeze_mask {Provenance : Type}
    (vtableLookup : ThinPointer Provenance → Interp VTable) :
    UnsafeCellStrategy → LayoutStrategy → Option (PointerMeta Provenance) → Interp (List Bool)
  | .Sized cells, .Sized size _, _ =>
    cellsToFreezeMask cells size
  | .Slice elementCells, .Slice size _, some (.ElementCount count) => do
    let elementMask ← cellsToFreezeMask elementCells size
    pure ((List.replicate count.toNat elementMask).flatten)
  | .TraitObject, .TraitObject _, some (.VTablePointer ptr) => do
    let vtable ← vtableLookup ptr
    cellsToFreezeMask vtable.cells vtable.size
  | .Tuple headCells tailCells, .Tuple head tail, ptrMetadata => do
    let headMask ← cellsToFreezeMask headCells head.end
    let tailMask ← UnsafeCellStrategy.freeze_mask vtableLookup tailCells tail ptrMetadata
    pure (headMask ++ tailMask)
  | _, _, _ => specPanic "Invalid LayoutStrategy and PointerMeta combination"

/-- The per-byte permission closure `perm(inside, frozen)` of
`ReborrowSettings::new` (`spec/mem/tree_borrows/reborrow_settings.md`):
> "let perm = |inside: bool, frozen: bool| {
>     // Helper to choose the correct permission, based on protection.
>     let mk_perm = |unprot, prot| if protected.yes() { Permission::Prot(prot) } else { Permission::Unprot(unprot) };
>
>     match ptr_type {
>         // Shared references
>         PtrType::Ref { mutbl: Mutability::Immutable, .. } =>
>             if frozen {
>                 mk_perm(PermissionUnprot::Frozen, PermissionProt::Frozen { had_local_read: false })
>             } else {
>                 mk_perm(PermissionUnprot::Cell, PermissionProt::Cell)
>             },
>         // Mutable references and Boxes (Boxes are treated the same as mutable references)
>         PtrType::Ref { mutbl: Mutability::Mutable, .. } | PtrType::Box { .. } =>
>             if implicit_writes_enabled && inside {
>                 // The implicit write only happens on the inside.
>                 // `implicit_writes_enabled` implies `protected.yes()`, so this case is always protected.
>                 assert!(protected.yes());
>                 Permission::Prot(PermissionProt::Unique)
>             } else {
>                 // Unprotected interior-mutable references and boxes start in `ReservedIm`, but if they are protected we ignore the `Im`
>                 mk_perm(
>                   if frozen { PermissionUnprot::Reserved } else { PermissionUnprot::ReservedIm },
>                   PermissionProt::Reserved { had_local_read: false, had_foreign_read: false }
>                 )
>             },
>         // Cannot occur: `safe_pointee()` returns `None` for these variants.
>         PtrType::Raw { .. } | PtrType::FnPtr | PtrType::VTablePtr(_) => unreachable!(\"safe_pointee() returns None for Raw, FnPtr, and VTablePtr; should have returned early on function entry\"),
>     }
> };" -/
def ReborrowSettings.perm (ptrType : PtrType) (prot : Protected) (implicitWritesEnabled : Bool)
    (inside frozen : Bool) : Interp Permission :=
  let mkPerm (unprot : PermissionUnprot) (pprot : PermissionProt) : Permission :=
    if Protected.yes prot then .Prot pprot else .Unprot unprot
  match ptrType with
  | .Ref .Immutable _ =>
    if frozen then
      pure (mkPerm .Frozen (.Frozen false))
    else
      pure (mkPerm .Cell .Cell)
  | .Ref .Mutable _ | .Box _ =>
    if implicitWritesEnabled && inside then
      if !Protected.yes prot then
        specPanic "assertion failed: protected.yes()"
      else
        pure (.Prot .Unique)
    else
      let unprot : PermissionUnprot := if frozen then .Reserved else .ReservedIm
      pure (mkPerm unprot (.Reserved false false))
  | .Raw _ | .FnPtr | .VTablePtr _ =>
    specPanic "safe_pointee() returns None for Raw, FnPtr, and VTablePtr; should have returned early on function entry"

/-- `ReborrowSettings::new` (`spec/mem/tree_borrows/reborrow_settings.md`):
> "fn new(
>     ptr: Pointer<TreeBorrowsProvenance>,
>     ptr_type: PtrType,
>     fn_entry: bool,
>     params: TreeBorrowsParams,
>     fn_implicit_writes: bool, // wether implicit_writes are enabled for the currently evaluated function, or not
>     vtable_lookup: impl Fn(ThinPointer<TreeBorrowsProvenance>) -> crate::lang::VTable + 'static,
> ) -> Option<Self> {
>     // Returns None for `Raw`, `FnPtr` and `VTablePtr`, so `ptr_type` can only be `Ref` and `Box` from here.
>     let Some(pointee_info) = ptr_type.safe_pointee() else {
>         return None;
>     };
>     if matches!(ptr_type, PtrType::Ref { mutbl: Mutability::Mutable, pointee } | PtrType::Box { pointee } if !pointee.unpin) {
>         // Mutable reference / Box to pinning type: retagging is a NOP.
>         // FIXME: with `UnsafePinned`, this should do proper per-byte tracking.
>         return None;
>     }
>
>     // We protect upon function entry.
>     let protected = if fn_entry {
>         // Boxes are weakly protected, everything else strongly.
>         match ptr_type {
>             PtrType::Box { .. } => Protected::Weak,
>             _ => Protected::Strong,
>         }
>     } else {
>         Protected::No
>     };
>
>     // Implicit writes are performed for protected references, only if globally enabled (`params.implicit_writes`),
>     // and only if the function has not opted out via the `#[rustc_no_writable]` attribute (`fn_implicit_writes`).
>     let implicit_writes_enabled = protected.yes() && params.implicit_writes && fn_implicit_writes;
>     ..
>     let inside = pointee_info.unsafe_cells.freeze_mask(pointee_info.layout, ptr.metadata, vtable_lookup).map(|freeze|
>         perm(/* inside */ true, freeze)
>     );
>     let outside = perm(/* inside */ false, pointee_info.freeze);
>
>     Some(ReborrowSettings { protected, inside, outside })
> }" -/
def ReborrowSettings.new {Provenance : Type}
    (vtableLookup : ThinPointer Provenance → Interp VTable)
    (ptr : Pointer Provenance) (ptrType : PtrType) (fnEntry : Bool)
    (params : TreeBorrowsParams) (fnImplicitWrites : Bool) : Interp (Option ReborrowSettings) :=
  match PtrType.safe_pointee ptrType with
  | none => pure none
  | some pointeeInfo =>
    if (match ptrType with
        | .Ref .Mutable pointee | .Box pointee => !pointee.unpin
        | _ => false) then
      pure none
    else do
      let prot : Protected :=
        if fnEntry then
          match ptrType with
          | .Box _ => .Weak
          | _ => .Strong
        else
          .No
      let implicitWritesEnabled : Bool :=
        Protected.yes prot && params.implicit_writes && fnImplicitWrites
      let freezeMask ←
        UnsafeCellStrategy.freeze_mask vtableLookup pointeeInfo.unsafe_cells
          pointeeInfo.layout ptr.metadata
      let inside ← freezeMask.mapM (fun freeze =>
        ReborrowSettings.perm ptrType prot implicitWritesEnabled true freeze)
      let outside ← ReborrowSettings.perm ptrType prot implicitWritesEnabled false pointeeInfo.freeze
      pure (some { inside := inside, outside := outside, «protected» := prot })

/-! ## Tree Borrows unprotected state machine (`spec/mem/tree_borrows/state_machine_unprotected.md`) -/

/-- `PermissionUnprot::local_read` (`spec/mem/tree_borrows/state_machine_unprotected.md`):
> "fn local_read(self) -> Result<PermissionUnprot> {
>     ret(
>         match self {
>             PermissionUnprot::Disabled => throw_ub!(\"Tree Borrows: local read of Disabled reference\"),
>             // All other states are kept unchanged.
>             perm => perm,
>         }
>     )
> }" -/
def PermissionUnprot.local_read : PermissionUnprot → Interp PermissionUnprot
  | .Disabled => ub "Tree Borrows: local read of Disabled reference"
  | perm => pure perm

/-- `PermissionUnprot::local_write` (`spec/mem/tree_borrows/state_machine_unprotected.md`):
> "fn local_write(self) -> Result<PermissionUnprot> {
>     match self {
>         PermissionUnprot::Frozen => throw_ub!(\"Tree Borrows: local write of Frozen reference\"),
>         PermissionUnprot::Disabled => throw_ub!(\"Tree Borrows: local write of Disabled reference\"),
>         PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
>         _ => ret(PermissionUnprot::Unique),
>     }
> }" -/
def PermissionUnprot.local_write : PermissionUnprot → Interp PermissionUnprot
  | .Frozen => ub "Tree Borrows: local write of Frozen reference"
  | .Disabled => ub "Tree Borrows: local write of Disabled reference"
  | .Cell => pure .Cell
  | _ => pure .Unique

/-- `PermissionUnprot::foreign_read` (`spec/mem/tree_borrows/state_machine_unprotected.md`):
> "fn foreign_read(self) -> Result<PermissionUnprot> {
>     match self {
>         PermissionUnprot::Reserved => ret(PermissionUnprot::Reserved),
>         PermissionUnprot::Unique => ret(PermissionUnprot::Frozen),
>         // All other states are kept unchanged.
>         perm => ret(perm),
>     }
> }" -/
def PermissionUnprot.foreign_read : PermissionUnprot → Interp PermissionUnprot
  | .Reserved => pure .Reserved
  | .Unique => pure .Frozen
  | perm => pure perm

/-- `PermissionUnprot::foreign_write` (`spec/mem/tree_borrows/state_machine_unprotected.md`):
> "fn foreign_write(self) -> Result<PermissionUnprot> {
>     match self {
>         PermissionUnprot::Cell => ret(PermissionUnprot::Cell),
>         PermissionUnprot::ReservedIm => ret(PermissionUnprot::ReservedIm),
>         // All other states become Disabled.
>         _ => ret(PermissionUnprot::Disabled),
>     }
> }" -/
def PermissionUnprot.foreign_write : PermissionUnprot → Interp PermissionUnprot
  | .Cell => pure .Cell
  | .ReservedIm => pure .ReservedIm
  | _ => pure .Disabled

/-- `PermissionUnprot::transition` (`spec/mem/tree_borrows/state_machine_unprotected.md`):
> "fn transition(
>     self,
>     access_kind: AccessKind,
>     node_relation: NodeRelation,
> ) -> Result<PermissionUnprot> {
>     match (node_relation, access_kind) {
>         (NodeRelation::Local, AccessKind::Read) => self.local_read(),
>         (NodeRelation::Local, AccessKind::Write) => self.local_write(),
>         (NodeRelation::Foreign, AccessKind::Read) => self.foreign_read(),
>         (NodeRelation::Foreign, AccessKind::Write) => self.foreign_write(),
>     }
> }" -/
def PermissionUnprot.transition (self : PermissionUnprot) (accessKind : AccessKind)
    (nodeRelation : NodeRelation) : Interp PermissionUnprot :=
  match nodeRelation, accessKind with
  | .Local, .Read => PermissionUnprot.local_read self
  | .Local, .Write => PermissionUnprot.local_write self
  | .Foreign, .Read => PermissionUnprot.foreign_read self
  | .Foreign, .Write => PermissionUnprot.foreign_write self

/-- `PermissionUnprot::prevents_deallocation` (`spec/mem/tree_borrows/state_machine_unprotected.md`):
> "fn prevents_deallocation(&self) -> bool {
>     // Note: this is equivalent to `self.foreign_write().is_err()`, just like for protected
>     // references, since unprotected references never trigger UB for foreign accesses.
>     false
> }" -/
def PermissionUnprot.prevents_deallocation (_ : PermissionUnprot) : Bool :=
  false

/-- `PermissionUnprot::init_access` (`spec/mem/tree_borrows/state_machine_unprotected.md`):
> "fn init_access(self) -> Option<AccessKind> {
>     // Everything except for `Cell` gets an initial read access.
>     // We never perform implicit writes for unprotected references.
>     match self {
>         PermissionUnprot::Cell => None,
>         _ => Some(AccessKind::Read)
>     }
> }" -/
def PermissionUnprot.init_access : PermissionUnprot → Option AccessKind
  | .Cell => none
  | _ => some .Read

/-! ## Tree Borrows protected state machine (`spec/mem/tree_borrows/state_machine_protected.md`) -/

/-- `PermissionProt::local_read` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn local_read(self) -> Result<PermissionProt> {
>     match self {
>         PermissionProt::Cell => ret(PermissionProt::Cell),
>         PermissionProt::Reserved { had_foreign_read, .. } => ret(PermissionProt::Reserved { had_local_read: true, had_foreign_read }),
>         PermissionProt::Unique => ret(PermissionProt::Unique),
>         PermissionProt::Frozen { .. } => ret(PermissionProt::Frozen { had_local_read: true }),
>         PermissionProt::Disabled => throw_ub!(\"Tree Borrows: local read of protected Disabled reference\"),
>     }
> }" -/
def PermissionProt.local_read : PermissionProt → Interp PermissionProt
  | .Cell => pure .Cell
  | .Reserved _ hadForeignRead => pure (.Reserved true hadForeignRead)
  | .Unique => pure .Unique
  | .Frozen _ => pure (.Frozen true)
  | .Disabled => ub "Tree Borrows: local read of protected Disabled reference"

/-- `PermissionProt::local_write` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn local_write(self) -> Result<PermissionProt> {
>     match self {
>         PermissionProt::Cell => ret(PermissionProt::Cell),
>         PermissionProt::Unique => ret(PermissionProt::Unique),
>         PermissionProt::Reserved { had_foreign_read: false, .. } => ret(PermissionProt::Unique),
>         PermissionProt::Reserved { had_foreign_read: true, .. } =>
>             throw_ub!(\"Tree Borrows: local write to protected Reserved reference that had a foreign read\"),
>         PermissionProt::Frozen { .. } => throw_ub!(\"Tree Borrows: local write to protected Frozen reference\"),
>         // we don't know anymore if we were shared or mutable in this state
>         PermissionProt::Disabled => throw_ub!(\"Tree Borrows: local write to protected Disabled reference\"),
>     }
> }" -/
def PermissionProt.local_write : PermissionProt → Interp PermissionProt
  | .Cell => pure .Cell
  | .Unique => pure .Unique
  | .Reserved _ false => pure .Unique
  | .Reserved _ true => ub "Tree Borrows: local write to protected Reserved reference that had a foreign read"
  | .Frozen _ => ub "Tree Borrows: local write to protected Frozen reference"
  | .Disabled => ub "Tree Borrows: local write to protected Disabled reference"

/-- `PermissionProt::foreign_read` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn foreign_read(self) -> Result<PermissionProt> {
>     match self {
>         PermissionProt::Cell => ret(PermissionProt::Cell),
>         PermissionProt::Unique => throw_ub!(\"Tree Borrows: foreign read of protected Unique reference\"),
>         PermissionProt::Reserved { had_local_read, .. } => ret(PermissionProt::Reserved { had_local_read, had_foreign_read: true }),
>         // Frozen and Disabled are kept unchanged.
>         PermissionProt::Frozen { had_local_read } => ret(PermissionProt::Frozen { had_local_read }),
>         PermissionProt::Disabled => ret(PermissionProt::Disabled),
>     }
> }" -/
def PermissionProt.foreign_read : PermissionProt → Interp PermissionProt
  | .Cell => pure .Cell
  | .Unique => ub "Tree Borrows: foreign read of protected Unique reference"
  | .Reserved hadLocalRead _ => pure (.Reserved hadLocalRead true)
  | .Frozen hadLocalRead => pure (.Frozen hadLocalRead)
  | .Disabled => pure .Disabled

/-- `PermissionProt::foreign_write` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn foreign_write(self) -> Result<PermissionProt> {
>     match self {
>         PermissionProt::Cell => ret(PermissionProt::Cell),
>         PermissionProt::Frozen { had_local_read: true } | PermissionProt::Reserved { had_local_read: true, .. } =>
>                 throw_ub!(\"Tree Borrows: foreign write of protected {} reference which had a local read\", if matches!(self, PermissionProt::Frozen {..}) { \"Frozen\" } else { \"Reserved\" }),
>         PermissionProt::Unique =>
>                 throw_ub!(\"Tree Borrows: foreign read of protected Unique reference\"),
>
>         // not yet locally accessed states become Disabled
>         PermissionProt::Frozen { had_local_read: false } | PermissionProt::Reserved { had_local_read: false, .. } => ret(PermissionProt::Disabled),
>         PermissionProt::Disabled => ret(PermissionProt::Disabled),
>     }
> }" -/
def PermissionProt.foreign_write : PermissionProt → Interp PermissionProt
  | .Cell => pure .Cell
  | .Frozen true => ub "Tree Borrows: foreign write of protected Frozen reference which had a local read"
  | .Reserved true _ => ub "Tree Borrows: foreign write of protected Reserved reference which had a local read"
  | .Unique => ub "Tree Borrows: foreign read of protected Unique reference"
  | .Frozen false => pure .Disabled
  | .Reserved false _ => pure .Disabled
  | .Disabled => pure .Disabled

/-- `PermissionProt::transition` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn transition(
>     self,
>     access_kind: AccessKind,
>     node_relation: NodeRelation,
> ) -> Result<PermissionProt> {
>     match (node_relation, access_kind) {
>         (NodeRelation::Local, AccessKind::Read) => self.local_read(),
>         (NodeRelation::Local, AccessKind::Write) => self.local_write(),
>         (NodeRelation::Foreign, AccessKind::Read) => self.foreign_read(),
>         (NodeRelation::Foreign, AccessKind::Write) => self.foreign_write(),
>     }
> }" -/
def PermissionProt.transition (self : PermissionProt) (accessKind : AccessKind)
    (nodeRelation : NodeRelation) : Interp PermissionProt :=
  match nodeRelation, accessKind with
  | .Local, .Read => PermissionProt.local_read self
  | .Local, .Write => PermissionProt.local_write self
  | .Foreign, .Read => PermissionProt.foreign_read self
  | .Foreign, .Write => PermissionProt.foreign_write self

/-- `PermissionProt::init_access` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn init_access(self) -> Option<AccessKind> {
>     // Everything except for `Cell` gets an initial read access.
>     // `Unique` gets an initial write.
>     match self {
>         PermissionProt::Cell => None,
>         PermissionProt::Unique => Some(AccessKind::Write),
>         _ => Some(AccessKind::Read)
>     }
> }" -/
def PermissionProt.init_access : PermissionProt → Option AccessKind
  | .Cell => none
  | .Unique => some .Write
  | _ => some .Read

/-- `PermissionProt::unprotect` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn unprotect(self) -> (PermissionUnprot, Option<AccessKind>) {
>     match self {
>         PermissionProt::Unique => (PermissionUnprot::Unique, Some(AccessKind::Write)),
>         PermissionProt::Reserved { had_local_read: true, .. } => (PermissionUnprot::Reserved, Some(AccessKind::Read)),
>         PermissionProt::Reserved { had_local_read: false, .. } => (PermissionUnprot::Reserved, None),
>         PermissionProt::Frozen { had_local_read: true } => (PermissionUnprot::Frozen, Some(AccessKind::Read)),
>         PermissionProt::Frozen { had_local_read: false } => (PermissionUnprot::Frozen, None),
>         PermissionProt::Disabled => (PermissionUnprot::Disabled, None),
>
>         PermissionProt::Cell => (PermissionUnprot::Cell, None),
>     }
> }" -/
def PermissionProt.unprotect : PermissionProt → PermissionUnprot × Option AccessKind
  | .Unique => (.Unique, some .Write)
  | .Reserved true _ => (.Reserved, some .Read)
  | .Reserved false _ => (.Reserved, none)
  | .Frozen true => (.Frozen, some .Read)
  | .Frozen false => (.Frozen, none)
  | .Disabled => (.Disabled, none)
  | .Cell => (.Cell, none)

/-- `PermissionProt::prevents_deallocation` (`spec/mem/tree_borrows/state_machine_protected.md`):
> "fn prevents_deallocation(&self) -> bool {
>     match self {
>         PermissionProt::Unique => true,
>         PermissionProt::Reserved { had_local_read, .. } | PermissionProt::Frozen { had_local_read } => *had_local_read,
>
>         PermissionProt::Disabled => false,
>
>         // Cell never prevents deallocation
>         PermissionProt::Cell => false,
>     }
>     // Note: the above is equivalent to `self.foreign_write().is_err()`
> }" -/
def PermissionProt.prevents_deallocation : PermissionProt → Bool
  | .Unique => true
  | .Reserved hadLocalRead _ => hadLocalRead
  | .Frozen hadLocalRead => hadLocalRead
  | .Disabled => false
  | .Cell => false

/-! ## Tree Borrows combined state machine (`spec/mem/tree_borrows/state_machine.md`) -/

/-- `Permission::transition` (`spec/mem/tree_borrows/state_machine.md`):
> "fn transition(
>     &mut self,
>     access_kind: AccessKind,
>     node_relation: NodeRelation,
> ) -> Result {
>     match self {
>         Permission::Unprot(p) => {
>             *p = p.transition(access_kind, node_relation)?
>         },
>         Permission::Prot(p) => {
>             *p = p.transition(access_kind, node_relation)?
>         }
>     };
>     Ok(())
> }" -/
def Permission.transition : Permission → AccessKind → NodeRelation → Interp Permission
  | .Unprot p, accessKind, nodeRelation => do
    pure (.Unprot (← PermissionUnprot.transition p accessKind nodeRelation))
  | .Prot p, accessKind, nodeRelation => do
    pure (.Prot (← PermissionProt.transition p accessKind nodeRelation))

/-- `Permission::unprotect` (`spec/mem/tree_borrows/state_machine.md`):
> "fn unprotect(self) -> (Permission, Option<AccessKind>) {
>     match self {
>         // This method is only called on protected nodes.
>         Permission::Unprot(_) => unreachable!(),
>         Permission::Prot(p) => {
>             let (new_perm, access) = p.unprotect();
>             (Permission::Unprot(new_perm), access)
>         }
>     }
> }" -/
def Permission.unprotect : Permission → Interp (Permission × Option AccessKind)
  | .Unprot _ => specPanic "Permission::unprotect called on unprotected permission"
  | .Prot p =>
    let (newPerm, access) := PermissionProt.unprotect p
    pure (.Unprot newPerm, access)

/-- `Permission::prevents_deallocation` (`spec/mem/tree_borrows/state_machine.md`):
> "fn prevents_deallocation(&self) -> bool {
>     match self {
>         Permission::Unprot(p) => p.prevents_deallocation(),
>         Permission::Prot(p) => p.prevents_deallocation()
>     }
> }" -/
def Permission.prevents_deallocation : Permission → Bool
  | .Unprot p => PermissionUnprot.prevents_deallocation p
  | .Prot p => PermissionProt.prevents_deallocation p

/-- `Permission::matches_protector` (`spec/mem/tree_borrows/state_machine.md`):
> "fn matches_protector(&self, protected: Protected) -> bool {
>     if protected.yes() {
>         matches!(self, Permission::Prot(_))
>     } else {
>         matches!(self, Permission::Unprot(_))
>     }
> }" -/
def Permission.matches_protector (self : Permission) (prot : Protected) : Bool :=
  if Protected.yes prot then
    match self with
    | .Prot _ => true
    | .Unprot _ => false
  else
    match self with
    | .Unprot _ => true
    | .Prot _ => false

/-- `Permission::init_access` (`spec/mem/tree_borrows/state_machine.md`):
> "fn init_access(self) -> Option<AccessKind> {
>     match self {
>         Permission::Unprot(p) => p.init_access(),
>         Permission::Prot(p) => p.init_access()
>     }
> }" -/
def Permission.init_access : Permission → Option AccessKind
  | .Unprot p => PermissionUnprot.init_access p
  | .Prot p => PermissionProt.init_access p

/-! ## Tree Borrows tree operations (`spec/mem/tree_borrows/tree.md`) -/

/-- Range loop of `Node::transition` (`spec/mem/tree_borrows/tree.md`):
> "for offset in offset_start..offset_start + size.bytes() {
>     self.permissions.mutate_at(offset, |permission|{
>         permission.transition(access_kind, node_relation)
>     })?;
> }" -/
def Node.transitionRange (nodeRelation : NodeRelation) (accessKind : AccessKind) (offset : Nat) :
    Nat → List Permission → Interp (List Permission)
  | 0, perms => pure perms
  | rem + 1, perms => do
    let (_, perms') ←
      listMutateAt perms (Int.ofNat offset) "Node::transition" (fun permission => do
        let p' ← Permission.transition permission accessKind nodeRelation
        pure ((), p'))
    Node.transitionRange nodeRelation accessKind (offset + 1) rem perms'

/-- `Node::transition` (`spec/mem/tree_borrows/tree.md`):
> "fn transition(
>     &mut self,
>     node_relation: NodeRelation,
>     access_kind: AccessKind,
>     offset_in_alloc: Offset,
>     size: Size,
> ) -> Result {
>     let offset_start = offset_in_alloc.bytes();
>     for offset in offset_start..offset_start + size.bytes() {
>         self.permissions.mutate_at(offset, |permission|{
>             permission.transition(access_kind, node_relation)
>         })?;
>     }
>     ret(())
> }" -/
def Node.transition (self : Node) (nodeRelation : NodeRelation) (accessKind : AccessKind)
    (offsetInAlloc : Offset) (size : Size) : Interp Node := do
  let perms' ←
    Node.transitionRange nodeRelation accessKind offsetInAlloc.bytes size.bytes self.permissions
  pure { self with permissions := perms' }

mutual

/-- `Node::access` (`spec/mem/tree_borrows/tree.md`):
> "fn access(
>     &mut self,
>     path: Option<Path>, // self -> accessed node
>     access_kind: AccessKind,
>     offset_in_alloc: Offset,
>     size: Size,
> ) -> Result {
>     let node_relation = if path.is_some() { NodeRelation::Local } else { NodeRelation::Foreign };
>     self.transition(node_relation, access_kind, offset_in_alloc, size)?;
>     for child_id in Int::ZERO..self.children.len() {
>         let sub_path = match path.and_then(|p| p.split_first()) {
>             Some((head, tail)) if head == child_id => Some(tail),
>             _ => None,
>         };
>         self.children.mutate_at(child_id, |child| {
>             child.access(sub_path, access_kind, offset_in_alloc, size)
>         })?;
>     }
>     ret(())
> }" -/
def Node.access : Node → Option Path → AccessKind → Offset → Size → Interp Node
  | ⟨children, permissions, prot⟩, path, accessKind, offsetInAlloc, size => do
    let nodeRelation : NodeRelation := if path.isSome then .Local else .Foreign
    let self1 ←
      Node.transition ⟨children, permissions, prot⟩ nodeRelation accessKind offsetInAlloc size
    let children' ← Node.accessChildren 0 path accessKind offsetInAlloc size children
    pure { self1 with children := children' }

/-- Child loop of `Node::access` (`spec/mem/tree_borrows/tree.md`):
> "for child_id in Int::ZERO..self.children.len() {
>     let sub_path = match path.and_then(|p| p.split_first()) {
>         Some((head, tail)) if head == child_id => Some(tail),
>         _ => None,
>     };
>     self.children.mutate_at(child_id, |child| {
>         child.access(sub_path, access_kind, offset_in_alloc, size)
>     })?;
> }" -/
def Node.accessChildren (childId : Int) (path : Option Path) (accessKind : AccessKind)
    (offsetInAlloc : Offset) (size : Size) : List Node → Interp (List Node)
  | [] => pure []
  | child :: rest => do
    let subPath : Option Path :=
      match path with
      | some (head :: tail) => if head == childId then some tail else none
      | _ => none
    let child' ← Node.access child subPath accessKind offsetInAlloc size
    let rest' ← Node.accessChildren (childId + 1) path accessKind offsetInAlloc size rest
    pure (child' :: rest')

end

/-- `Node::is_leaf` (`spec/mem/tree_borrows/tree.md`):
> "fn is_leaf(&self) -> bool {
>     self.children.len() == Int::ZERO
> }" -/
def Node.is_leaf (self : Node) : Bool :=
  self.children.isEmpty

/-- `Node::access_node` (`spec/mem/tree_borrows/tree.md`):
> "fn access_node<O>(&mut self, path: Path, f: impl FnOnce(&mut Self) -> O) -> O {
>     let Some((sub_root_id, sub_path)) = path.split_first() else {
>         return f(self);
>     };
>     if self.is_leaf() { panic!(\"Node::access_node: invalid node path\"); }
>     self.children.mutate_at(sub_root_id, |child| child.access_node(sub_path, f))
> }" -/
def Node.access_node {O : Type} (f : Node → Interp (O × Node)) :
    Path → Node → Interp (O × Node)
  | [], self => f self
  | subRootId :: subPath, self =>
    if Node.is_leaf self then
      specPanic "Node::access_node: invalid node path"
    else do
      let (out, children') ←
        listMutateAt self.children subRootId "Node::access_node" (Node.access_node f subPath)
      pure (out, { self with children := children' })

/-- `Node::add_node` (`spec/mem/tree_borrows/tree.md`):
> "fn add_node(&mut self, parent_path: Path, child: Node) -> Path {
>     let child_idx = self.access_node(parent_path, |node| {
>         let child_idx = node.children.len();
>         node.children.push(child);
>         child_idx
>     });
>
>     let mut child_path = parent_path;
>     child_path.push(child_idx);
>
>     child_path
> }" -/
def Node.add_node (self : Node) (parentPath : Path) (child : Node) : Interp (Path × Node) := do
  let (childIdx, self') ←
    Node.access_node (fun node =>
      let childIdx : Int := node.children.length
      pure (childIdx, { node with children := node.children ++ [child] })) parentPath self
  pure (parentPath ++ [childIdx], self')

/-- Per-offset loop of `Node::release_protector` (`spec/mem/tree_borrows/tree.md`):
> "for (offset, access) in accesses.iter().enumerate() {
>     // If it is None, this means we do nothing.
>     let Some(access) = access else { continue };
>     // Otherwise we perform the requested access
>     self.permissions.mutate_at(Int::from(offset), |permission| {
>         // Perform state transition on `self`.
>         permission.transition(access, node_relation)
>     })?;
> }" -/
def Node.releaseProtectorPermissions (nodeRelation : NodeRelation) (offset : Nat) :
    List (Option AccessKind) → List Permission → Interp (List Permission)
  | [], perms => pure perms
  | none :: rest, perms =>
    Node.releaseProtectorPermissions nodeRelation (offset + 1) rest perms
  | some access :: rest, perms => do
    let (_, perms') ←
      listMutateAt perms (Int.ofNat offset) "Node::release_protector" (fun permission => do
        let p' ← Permission.transition permission access nodeRelation
        pure ((), p'))
    Node.releaseProtectorPermissions nodeRelation (offset + 1) rest perms'

mutual

/-- `Node::release_protector` (`spec/mem/tree_borrows/tree.md`):
> "fn release_protector(
>     &mut self,
>     path: Option<Path>, // self -> protected node
>     accesses: &List<Option<AccessKind>>,
> ) -> Result {
>     let node_relation = if path.is_some() { NodeRelation::Local } else { NodeRelation::Foreign };
>     if path.is_some_and(|p| p.is_empty()) {
>         self.protected = Protected::No;
>         return ret(());
>     }
>     for (offset, access) in accesses.iter().enumerate() {
>         let Some(access) = access else { continue };
>         self.permissions.mutate_at(Int::from(offset), |permission| {
>             permission.transition(access, node_relation)
>         })?;
>     }
>     for child_id in Int::ZERO..self.children.len() {
>         let sub_path = match path.and_then(|p| p.split_first()) {
>             Some((head, tail)) if head == child_id => Some(tail),
>             _ => None,
>         };
>         self.children.mutate_at(child_id, |child| { child.release_protector(sub_path, accesses) })?;
>     }
>     ret(())
> }" -/
def Node.release_protector : Node → Option Path → List (Option AccessKind) → Interp Node
  | ⟨children, permissions, prot⟩, path, accesses =>
    match path with
    | some [] => pure { children := children, permissions := permissions, «protected» := .No }
    | _ => do
      let nodeRelation : NodeRelation := if path.isSome then .Local else .Foreign
      let perms' ← Node.releaseProtectorPermissions nodeRelation 0 accesses permissions
      let children' ← Node.releaseProtectorChildren 0 path accesses children
      pure { children := children', permissions := perms', «protected» := prot }

/-- Child loop of `Node::release_protector` (`spec/mem/tree_borrows/tree.md`):
> "for child_id in Int::ZERO..self.children.len() {
>     let sub_path = match path.and_then(|p| p.split_first()) {
>         Some((head, tail)) if head == child_id => Some(tail),
>         _ => None,
>     };
>     self.children.mutate_at(child_id, |child| { child.release_protector(sub_path, accesses) })?;
> }" -/
def Node.releaseProtectorChildren (childId : Int) (path : Option Path)
    (accesses : List (Option AccessKind)) : List Node → Interp (List Node)
  | [] => pure []
  | child :: rest => do
    let subPath : Option Path :=
      match path with
      | some (head :: tail) => if head == childId then some tail else none
      | _ => none
    let child' ← Node.release_protector child subPath accesses
    let rest' ← Node.releaseProtectorChildren (childId + 1) path accesses rest
    pure (child' :: rest')

end

mutual

/-- `Node::contains_strong_protector_preventing_deallocation` (`spec/mem/tree_borrows/tree.md`):
> "fn contains_strong_protector_preventing_deallocation(&self) -> bool {
>     (self.protected == Protected::Strong
>         && self
>             .permissions
>             .any(|st| st.prevents_deallocation()))
>         || self.children.any(|child| child.contains_strong_protector_preventing_deallocation())
> }" -/
def Node.contains_strong_protector_preventing_deallocation : Node → Bool
  | ⟨children, permissions, prot⟩ =>
    (decide (prot = .Strong) && permissions.any Permission.prevents_deallocation) ||
      Node.anyChildPreventsDeallocation children

/-- Child disjunction of `Node::contains_strong_protector_preventing_deallocation`
(`spec/mem/tree_borrows/tree.md`):
> "self.children.any(|child| child.contains_strong_protector_preventing_deallocation())" -/
def Node.anyChildPreventsDeallocation : List Node → Bool
  | [] => false
  | child :: rest =>
    Node.contains_strong_protector_preventing_deallocation child ||
      Node.anyChildPreventsDeallocation rest

end

/-! ## Tree Borrows memory (`spec/mem/tree_borrows/memory.md`) -/

/-- `TreeBorrowsFrameExtra::new` (`spec/mem/tree_borrows/memory.md`):
> "impl TreeBorrowsFrameExtra {
>     fn new() -> Self { Self { protectors: List::new() } }
> }" -/
def TreeBorrowsFrameExtra.new : TreeBorrowsFrameExtra :=
  { protectors := [] }

/-- Initial inside-permission access loop of `TreeBorrowsMemory::reborrow`
(`spec/mem/tree_borrows/memory.md`):
> "for (idx, perm) in settings.inside.iter().enumerate() {
>     let idx = Int::from(idx);
>     let idx = Size::from_bytes(idx).unwrap();
>     if let Some(access) = perm.init_access() {
>         allocation.extra.root.access(Some(child_path), access, offset+idx, Offset::from_bytes_const(1))?
>     }
> }" -/
def TreeBorrowsMemory.reborrowInitAccess (childPath : Path) (offset : Offset) (idx : Nat) :
    List Permission → Node → Interp Node
  | [], root => pure root
  | perm :: rest, root => do
    let root' ←
      match Permission.init_access perm with
      | some access =>
        Node.access root (some childPath) access (Size.add offset ⟨idx⟩) ⟨1⟩
      | none =>
        pure root
    TreeBorrowsMemory.reborrowInitAccess childPath offset (idx + 1) rest root'

/-- `TreeBorrowsMemory::reborrow` (`spec/mem/tree_borrows/memory.md`):
> "fn reborrow(
>     &mut self,
>     ptr: ThinPointer<TreeBorrowsProvenance>,
>     settings: ReborrowSettings,
>     frame_extra: &mut TreeBorrowsFrameExtra,
> ) -> Result<ThinPointer<TreeBorrowsProvenance>> {
>     let pointee_size = Size::from_bytes(settings.inside.len()).unwrap();
>     self.mem.check_ptr(ptr, pointee_size)?;
>     let Some((alloc_id, parent_path)) = ptr.provenance else {
>         assert!(pointee_size.is_zero());
>         return ret(ptr);
>     };
>     let child_path = self.mem.allocations.mutate_at(alloc_id.0, |allocation| {
>         let alloc_size = allocation.size();
>         let offset = Offset::from_bytes(ptr.addr - allocation.addr).unwrap();
>         let mut permissions = list![settings.outside; alloc_size.bytes()];
>         if settings.inside.len() > 0 {
>             permissions.write_subslice_at_index(
>                 offset.bytes(),
>                 settings.inside,
>             );
>         }
>         let child_node = Node {
>             children: List::new(),
>             permissions,
>             protected: settings.protected,
>         };
>         assert!(child_node.permissions.all(|x| x.matches_protector(child_node.protected)));
>         let child_path = allocation.extra.root.add_node(parent_path, child_node);
>         for (idx, perm) in settings.inside.iter().enumerate() {
>             let idx = Int::from(idx);
>             let idx = Size::from_bytes(idx).unwrap();
>             if let Some(access) = perm.init_access() {
>                 allocation.extra.root.access(Some(child_path), access, offset+idx, Offset::from_bytes_const(1))?
>             }
>         }
>         ret::<Result<Path>>(child_path)
>     })?;
>     if settings.protected.yes() { frame_extra.protectors.push((alloc_id, child_path)); }
>     ret(ThinPointer {
>         provenance: Some((alloc_id, child_path)),
>         ..ptr
>     })
> }" -/
def TreeBorrowsMemory.reborrow (tbm : TreeBorrowsMemory x86_64)
    (ptr : ThinPointer TreeBorrowsProvenance) (settings : ReborrowSettings)
    (frameExtra : TreeBorrowsFrameExtra) :
    Interp (ThinPointer TreeBorrowsProvenance × TreeBorrowsMemory x86_64 × TreeBorrowsFrameExtra) := do
  let pointeeSize : Size := ⟨settings.inside.length⟩
  let _ ← BasicMemory.check_ptr tbm.mem ptr pointeeSize
  match ptr.provenance with
  | none =>
    if pointeeSize.bytes ≠ 0 then
      specPanic "assertion failed: pointee_size.is_zero()"
    else
      pure (ptr, tbm, frameExtra)
  | some (allocId, parentPath) => do
    let (childPath, allocations') ←
      listMutateAt tbm.mem.allocations allocId._0 "TreeBorrowsMemory::reborrow" (fun allocation => do
        let allocSize := Allocation.size allocation
        let offset ←
          match Size.from_bytes (ptr.addr - allocation.addr) with
          | some o => pure o
          | none => specPanic "Offset::from_bytes(ptr.addr - allocation.addr).unwrap()"
        let permissions := List.replicate allocSize.bytes settings.outside
        let permissions ←
          if settings.inside.length > 0 then
            writeSubsliceAtIndex permissions offset.bytes settings.inside
          else
            pure permissions
        let childNode : Node := {
          children := []
          permissions := permissions
          «protected» := settings.«protected»
        }
        if !(childNode.permissions.all (fun x => Permission.matches_protector x childNode.«protected»)) then
          specPanic "assertion failed: child_node.permissions.all(|x| x.matches_protector(child_node.protected))"
        else do
          let (childPath, root1) ← Node.add_node allocation.extra.root parentPath childNode
          let root2 ←
            TreeBorrowsMemory.reborrowInitAccess childPath offset 0 settings.inside root1
          pure (childPath, { allocation with extra := { root := root2 } }))
    let frameExtra' : TreeBorrowsFrameExtra :=
      if Protected.yes settings.«protected» then
        { protectors := frameExtra.protectors ++ [(allocId, childPath)] }
      else
        frameExtra
    let mem' := { tbm.mem with allocations := allocations' }
    pure ({ ptr with provenance := some (allocId, childPath) }, { tbm with mem := mem' }, frameExtra')

/-- `TreeBorrowsMemory::release_protector` (`spec/mem/tree_borrows/memory.md`):
> "fn release_protector(&mut self, provenance: TreeBorrowsProvenance) -> Result {
>     let (alloc_id, path) = provenance;
>     self.mem.allocations.mutate_at(alloc_id.0, |allocation| {
>         let protector_accesses : List<_> = allocation.extra.root.access_node(path, |node| {
>             assert!(node.protected.yes());
>             let list_of_perms_and_accesses = node.permissions.map(|x| x.unprotect());
>             node.permissions = list_of_perms_and_accesses.map(|(perm, _acc)| perm);
>             list_of_perms_and_accesses.map(|(_perm, acc)| acc)
>         });
>
>         if !allocation.live {
>             return ret(());
>         }
>
>         allocation.extra.root.release_protector(Some(path), &protector_accesses)
>     })
> }" -/
def TreeBorrowsMemory.release_protector (tbm : TreeBorrowsMemory x86_64)
    (provenance : TreeBorrowsProvenance) : Interp (TreeBorrowsMemory x86_64) := do
  let (allocId, path) := provenance
  let (_, allocations') ←
    listMutateAt tbm.mem.allocations allocId._0 "TreeBorrowsMemory::release_protector"
      (fun allocation => do
        let (protectorAccesses, root1) ←
          Node.access_node (fun node => do
            if !Protected.yes node.«protected» then
              specPanic "assertion failed: node.protected.yes()"
            else do
              let pairs ← node.permissions.mapM Permission.unprotect
              let perms := pairs.map Prod.fst
              let accesses := pairs.map Prod.snd
              pure (accesses, { node with permissions := perms })) path allocation.extra.root
        if !allocation.live then
          pure ((), { allocation with extra := { root := root1 } })
        else do
          let root2 ← Node.release_protector root1 (some path) protectorAccesses
          pure ((), { allocation with extra := { root := root2 } }))
  pure { tbm with mem := { tbm.mem with allocations := allocations' } }

/-- `TreeBorrowsMemory::new` (`spec/mem/tree_borrows/memory.md`):
> "fn new(params: TreeBorrowsParams) -> Self {
>     Self { mem: BasicMemory::new(), params }
> }" -/
def TreeBorrowsMemory.new (params : TreeBorrowsParams) : TreeBorrowsMemory x86_64 :=
  { mem := BasicMemory.new, params := params }

/-- `TreeBorrowsMemory::allocate` (`spec/mem/tree_borrows/memory.md`):
> "fn allocate(&mut self, kind: AllocationKind, size: Size, align: Align) -> NdResult<ThinPointer<Self::Provenance>>  {
>     let root = Node {
>         children: List::new(),
>         permissions: list![Permission::Unprot(PermissionUnprot::Unique); size.bytes()],
>         protected: Protected::No,
>     };
>     let path = Path::new();
>     let extra = TreeBorrowsAllocationExtra { root };
>     self.mem.allocate(kind, size, align, path, extra)
> }" -/
def TreeBorrowsMemory.allocate (tbm : TreeBorrowsMemory x86_64) (kind : AllocationKind)
    (size : Size) (align : Align) :
    Interp (ThinPointer TreeBorrowsProvenance × TreeBorrowsMemory x86_64) := do
  let root : Node := {
    children := []
    permissions := List.replicate size.bytes (.Unprot .Unique)
    «protected» := .No
  }
  let path : Path := []
  let extra : TreeBorrowsAllocationExtra := { root := root }
  let (ptr, mem') ← BasicMemory.allocate tbm.mem kind size align path extra
  pure (ptr, { tbm with mem := mem' })

/-- `TreeBorrowsMemory::deallocate` (`spec/mem/tree_borrows/memory.md`):
> "fn deallocate(&mut self, ptr: ThinPointer<Self::Provenance>, kind: AllocationKind, size: Size, align: Align) -> Result {
>     self.mem.deallocate(ptr, kind, size, align, |extra, path| {
>         extra.root.access(Some(path), AccessKind::Write, Offset::ZERO, size)?;
>         if extra.root.contains_strong_protector_preventing_deallocation() {
>             throw_ub!(\"Tree Borrows: deallocating strongly protected allocation\")
>         }
>         ret(())
>     })
> }" -/
def TreeBorrowsMemory.deallocate (tbm : TreeBorrowsMemory x86_64)
    (ptr : ThinPointer TreeBorrowsProvenance) (kind : AllocationKind) (size : Size)
    (align : Align) : Interp (TreeBorrowsMemory x86_64) := do
  let mem' ←
    BasicMemory.deallocate tbm.mem ptr kind size align (fun extra path => do
      let root' ← Node.access extra.root (some path) .Write ⟨0⟩ size
      if Node.contains_strong_protector_preventing_deallocation root' then
        ub "Tree Borrows: deallocating strongly protected allocation"
      else
        pure { root := root' })
  pure { tbm with mem := mem' }

/-- `TreeBorrowsMemory::load` (`spec/mem/tree_borrows/memory.md`):
> "fn load(&mut self, ptr: ThinPointer<Self::Provenance>, len: Size, align: Align) -> Result<List<AbstractByte<Self::Provenance>>> {
>     self.mem.load(ptr, len, align, |extra, path, offset| {
>         extra.root.access(Some(path), AccessKind::Read, offset, len)
>     })
> }" -/
def TreeBorrowsMemory.load (tbm : TreeBorrowsMemory x86_64)
    (ptr : ThinPointer TreeBorrowsProvenance) (len : Size) (align : Align) :
    Interp (List (AbstractByte TreeBorrowsProvenance) × TreeBorrowsMemory x86_64) := do
  let (bytes, mem') ←
    BasicMemory.load tbm.mem ptr len align (fun extra path offset => do
      let root' ← Node.access extra.root (some path) .Read offset len
      pure { root := root' })
  pure (bytes, { tbm with mem := mem' })

/-- `TreeBorrowsMemory::store` (`spec/mem/tree_borrows/memory.md`):
> "fn store(&mut self, ptr: ThinPointer<Self::Provenance>, bytes: List<AbstractByte<Self::Provenance>>, align: Align) -> Result {
>     let size = Size::from_bytes(bytes.len()).unwrap();
>     self.mem.store(ptr, bytes, align, |extra, path, offset| {
>         extra.root.access(Some(path), AccessKind::Write, offset, size)
>     })
> }" -/
def TreeBorrowsMemory.store (tbm : TreeBorrowsMemory x86_64)
    (ptr : ThinPointer TreeBorrowsProvenance)
    (bytes : List (AbstractByte TreeBorrowsProvenance)) (align : Align) :
    Interp (TreeBorrowsMemory x86_64) := do
  let size : Size := ⟨bytes.length⟩
  let mem' ←
    BasicMemory.store tbm.mem ptr bytes align (fun extra path offset => do
      let root' ← Node.access extra.root (some path) .Write offset size
      pure { root := root' })
  pure { tbm with mem := mem' }

/-- `TreeBorrowsMemory::dereferenceable` (`spec/mem/tree_borrows/memory.md`):
> "fn dereferenceable(&self, ptr: ThinPointer<Self::Provenance>, len: Size) -> Result {
>     self.mem.check_ptr(ptr, len)?;
>     ret(())
> }" -/
def TreeBorrowsMemory.dereferenceable (tbm : TreeBorrowsMemory x86_64)
    (ptr : ThinPointer TreeBorrowsProvenance) (len : Size) : Interp Unit := do
  let _ ← BasicMemory.check_ptr tbm.mem ptr len
  pure ()

/-- `Memory::signed_dereferenceable` for `TreeBorrowsMemory` (`spec/mem/interface.md`):
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
def TreeBorrowsMemory.signed_dereferenceable (tbm : TreeBorrowsMemory x86_64)
    (ptr : ThinPointer TreeBorrowsProvenance) (len : Int) : Interp Unit :=
  if len > 0 then
    TreeBorrowsMemory.dereferenceable tbm ptr ⟨len.toNat⟩
  else
    let beginPtr : ThinPointer TreeBorrowsProvenance := { ptr with addr := ptr.addr + len }
    TreeBorrowsMemory.dereferenceable tbm beginPtr ⟨(-len).toNat⟩

/-- `TreeBorrowsMemory::retag_ptr` (`spec/mem/tree_borrows/memory.md`):
> "fn retag_ptr(
>     &mut self,
>     frame_extra: &mut Self::FrameExtra,
>     ptr: Pointer<Self::Provenance>,
>     ptr_type: PtrType,
>     fn_entry: bool,
>     fn_implicit_writes: bool,
>     vtable_lookup: impl Fn(ThinPointer<Self::Provenance>) -> crate::lang::VTable + 'static,
> ) -> Result<Pointer<Self::Provenance>> {
>     ret(if let Some(perms) = ReborrowSettings::new(ptr, ptr_type, fn_entry, self.params, fn_implicit_writes, vtable_lookup) {
>         self.reborrow(ptr.thin_pointer, perms, frame_extra)?.widen(ptr.metadata)
>     } else {
>         ptr
>     })
> }" -/
def TreeBorrowsMemory.retag_ptr (tbm : TreeBorrowsMemory x86_64)
    (frameExtra : TreeBorrowsFrameExtra) (ptr : Pointer TreeBorrowsProvenance)
    (ptrType : PtrType) (fnEntry fnImplicitWrites : Bool)
    (vtableLookup : ThinPointer TreeBorrowsProvenance → Interp VTable) :
    Interp (Pointer TreeBorrowsProvenance × TreeBorrowsMemory x86_64 × TreeBorrowsFrameExtra) := do
  match ← ReborrowSettings.new vtableLookup ptr ptrType fnEntry tbm.params fnImplicitWrites with
  | some perms =>
    let (thin', tbm', frameExtra') ←
      TreeBorrowsMemory.reborrow tbm ptr.thin_pointer perms frameExtra
    pure (ThinPointer.widen thin' ptr.metadata, tbm', frameExtra')
  | none =>
    pure (ptr, tbm, frameExtra)

/-- `TreeBorrowsMemory::new_call` (`spec/mem/tree_borrows/memory.md`):
> "fn new_call() -> Self::FrameExtra {  Self::FrameExtra::new() }" -/
def TreeBorrowsMemory.new_call : TreeBorrowsFrameExtra :=
  TreeBorrowsFrameExtra.new

/-- `TreeBorrowsMemory::end_call` (`spec/mem/tree_borrows/memory.md`):
> "fn end_call(&mut self, extra: Self::FrameExtra) -> Result {
>     extra.protectors.try_map(|provenance| self.release_protector(provenance))?;
>     ret(())
> }" -/
def TreeBorrowsMemory.end_call (tbm : TreeBorrowsMemory x86_64)
    (extra : TreeBorrowsFrameExtra) : Interp (TreeBorrowsMemory x86_64) :=
  extra.protectors.foldlM (fun acc prov => TreeBorrowsMemory.release_protector acc prov) tbm

/-- `TreeBorrowsMemory::leak_check` (`spec/mem/tree_borrows/memory.md`):
> "fn leak_check(&self) -> Result {
>     self.mem.leak_check()
> }" -/
def TreeBorrowsMemory.leak_check (tbm : TreeBorrowsMemory x86_64) : Interp Unit :=
  BasicMemory.leak_check tbm.mem

/-! ## Integer-pointer casts (`spec/mem/intptrcast.md`) -/

/-- `IntPtrCast::expose` (`spec/mem/intptrcast.md`), which records the
provenance of a pointer cast to an integer:
> "pub fn expose(&mut self, ptr: ThinPointer<Provenance>) {
>     if let Some(provenance) = ptr.provenance {
>         // Remember this provenance as having been exposed.
>         self.exposed.insert(provenance);
>     }
> }" -/
def IntPtrCast.expose (ipc : IntPtrCast Prov) (ptr : Ptr) : IntPtrCast Prov :=
  match ptr.provenance with
  | some provenance => { exposed := setInsert ipc.exposed provenance }
  | none => ipc

/-- The provenances that the prediction in `IntPtrCast::int2ptr`
(`spec/mem/intptrcast.md`) resolves among (`int2ptrProvenance`). The
prediction admits only exposed provenances:
> "|p| self.exposed.contains(p),"
and of those, these are the ones of live allocations whose address range,
including the one-past-the-end address, contains `addr`. -/
def int2ptrCandidates (allocs : List Gen.Allocation) (exposed : Set Prov) (addr : Int) :
    List Prov :=
  (allocs.zipIdx.filter (fun (a, i) =>
      a.live && decide (a.addr ≤ addr) && decide (addr ≤ a.addr + (Allocation.size a).bytes) &&
        setContains exposed (⟨(i : Int)⟩, ()))).map (fun (_, i) => (⟨(i : Int)⟩, ()))

/-- How the interpretation resolves the angelic prediction of
`IntPtrCast::int2ptr` (`spec/mem/intptrcast.md`):
> "pub fn int2ptr(&self, addr: Int) -> NdResult<ThinPointer<Provenance>> {
>     // Predict a suitable provenance. It must be either `None` or already exposed.
>     let provenance = predict(|prov: Option<Provenance>| {
>         prov.map_or(
>             true, // `None` is always an option
>             |p| self.exposed.contains(p),
>         )
>     })?;
>
>     // Construct a pointer with that provenance.
>     ret(ThinPointer { addr, provenance })
> }"
`predict` is an angelic choice: if some admissible provenance makes the rest
of the execution well-defined, MiniRust picks it. In `BasicMemory`, provenance
is monotone (`spec/lang/representation.md`: every zero-sized operation and
zero-offset `ptr_offset_inbounds` succeeds before inspecting provenance, and
integer byte decoding ignores provenance fragments, so `Some(p)` succeeds in
every continuation where `None` succeeds):

* if `exposed` is empty, `None` is the unique admissible provenance;
* if `exposed` is a singleton `[p]`, `Some(p)` dominates `None` in `BasicMemory`
  by provenance monotonicity (`int2ptr_singleton_offset_checkPtr_optimal`), so
  `Some(p)` is exact for every `BasicMemory` continuation — even when `addr`
  lies temporarily outside allocation `p` before a wrapping offset brings it
  back in bounds (note: in `TreeBorrowsMemory`, if `addr < alloc.addr`, a
  zero-sized reborrow `&*(ptr as *const ())` under `Some(p)` hits
  `Stop.specPanic "Offset::from_bytes(ptr.addr - allocation.addr).unwrap()"`
  whereas `None` succeeds; see `int2ptrSingletonZstNegOffset_tb_specPanic_vs_none_ok`);
* if `exposed` contains two or more provenances, `int2ptrCandidates` selects the
  live exposed allocations whose range `[addr_a, addr_a + size_a]` contains
  `addr`: a unique candidate `[p]` resolves to `Some(p)`, while zero or multiple
  in-bounds candidates stop with `Stop.unsupported` rather than fabricating UB
  by guessing `None` or choosing arbitrarily between adjacent allocations.

Every provenance returned is admissible (`None` or in `exposed`), so any run
that completes under `int2ptrProvenance` is a valid angelic run. When two or
more provenances are exposed and `int2ptrCandidates` picks the unique one
containing `addr`, a UB result holds for that resolution (which differs from
angelic choice only if a later wrapping offset moves the pointer into a
different exposed allocation). -/
def int2ptrProvenance (m : Mach) (addr : Int) : Interp (Option Prov) :=
  match m.intptrcast.exposed.elems with
  | [] => pure none
  | [p] => pure (some p)
  | _ =>
    match int2ptrCandidates m.mem.memory.allocations m.intptrcast.exposed addr with
    | [p] => pure (some p)
    | [] =>
      unsupported "int2ptr: multiple exposed allocations and none contains the address (angelic choice)"
    | _ =>
      unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)"

/-- `IntPtrCast::int2ptr` (`spec/mem/intptrcast.md`) with the provenance
predicted by `int2ptrProvenance`:
> "// Construct a pointer with that provenance.
> ret(ThinPointer { addr, provenance })" -/
def IntPtrCast.int2ptr (m : Mach) (addr : Int) : Interp Ptr := do
  let provenance ← int2ptrProvenance m addr
  pure { addr := addr, provenance := provenance }

/-! ## Intrinsics (`spec/lang/step/intrinsics.md`) -/

/-- `Machine::eval_intrinsic` for the pointer provenance intrinsics
`IntrinsicOp::PointerExposeProvenance` and
`IntrinsicOp::PointerWithExposedProvenance` (`spec/lang/step/intrinsics.md`),
to which `minimize` translates MIR's `PointerExposeProvenance` and
`PointerWithExposedProvenance` casts:
> "fn eval_intrinsic(&mut self,
>     IntrinsicOp::PointerExposeProvenance: IntrinsicOp,
>     arguments: List<(Value<M>, Type)>,
>     ret_ty: Type,
> ) -> NdResult<Value<M>> {
>     if arguments.len() != 1 {
>         throw_ub!(\"invalid number of arguments for `PointerExposeProvenance` intrinsic\");
>     }
>     let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
>         throw_ub!(\"invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer\");
>     };
>     if ret_ty != Type::Int(IntType { signed: Unsigned, size: M::T::PTR_SIZE }) {
>         throw_ub!(\"invalid return type for `PointerExposeProvenance` intrinsic\")
>     }
>
>     self.intptrcast.expose(ptr);
>     ret(Value::Int(ptr.addr))
> }
>
> fn eval_intrinsic(&mut self,
>     IntrinsicOp::PointerWithExposedProvenance: IntrinsicOp,
>     arguments: List<(Value<M>, Type)>,
>     ret_ty: Type,
> ) -> NdResult<Value<M>> {
>     if arguments.len() != 1 {
>         throw_ub!(\"invalid number of arguments for `PointerWithExposedProvenance` intrinsic\");
>     }
>     let Value::Int(addr) = arguments[0].0 else {
>         throw_ub!(\"invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer\");
>     };
>     let Type::Ptr(ret_ptr_ty) = ret_ty else {
>         throw_ub!(\"invalid return type for `PointerWithExposedProvenance` intrinsic\");
>     };
>     if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
>         throw_ub!(\"unsized pointee requested for `PointerWithExposedProvenance` intrinsic\");
>     }
>
>     let ptr = self.intptrcast.int2ptr(addr)?;
>     ret(Value::Ptr(ptr.widen(None)))
> }"
Every other intrinsic is outside the fragment. -/
def evalIntrinsic (m : Mach) (intrinsic : IntrinsicOp) (arguments : List (Val × «Type»))
    (retTy : «Type») : Interp (Val × Mach) :=
  match intrinsic with
  | .PointerExposeProvenance =>
    if arguments.length ≠ 1 then
      ub "invalid number of arguments for `PointerExposeProvenance` intrinsic"
    else
      match arguments with
      | [(.Ptr ⟨ptr, none⟩, _)] =>
        match retTy with
        | .Int ⟨.Unsigned, ⟨8⟩⟩ =>
          pure (.Int ptr.addr, { m with intptrcast := IntPtrCast.expose m.intptrcast ptr })
        | _ => ub "invalid return type for `PointerExposeProvenance` intrinsic"
      | _ => ub "invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer"
  | .PointerWithExposedProvenance =>
    if arguments.length ≠ 1 then
      ub "invalid number of arguments for `PointerWithExposedProvenance` intrinsic"
    else
      match arguments with
      | [(.Int addr, _)] =>
        match retTy with
        | .Ptr retPtrTy =>
          if PtrType.meta_kind retPtrTy ≠ .None then
            ub "unsized pointee requested for `PointerWithExposedProvenance` intrinsic"
          else do
            let ptr ← IntPtrCast.int2ptr m addr
            pure (.Ptr (ThinPointer.widen ptr none), m)
        | _ => ub "invalid return type for `PointerWithExposedProvenance` intrinsic"
      | _ => ub "invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer"
  | _ => unsupported "eval_intrinsic for an intrinsic other than the pointer provenance intrinsics"

/-- The argument loop of `Terminator::Intrinsic`
(`spec/lang/step/terminators.md`), which keeps each argument's type:
> "let arguments = arguments.try_map(|arg| self.eval_value(arg))?;" -/
def evalArgs (m : Mach) : List ValueExpr → Interp (List (Val × «Type») × Mach)
  | [] => pure ([], m)
  | e :: es => do
    let (arg, m) ← evalValue m e
    let (args, m) ← evalArgs m es
    pure (arg :: args, m)

/-! ## Terminators (`spec/lang/step/terminators.md`) -/

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

/-- `Machine::eval_terminator` for `Goto`, `Switch`, `Unreachable`, `Return`,
and `Intrinsic`:
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
> }"
and for `Intrinsic` (with `evalIntrinsic`):
> "fn eval_terminator(
>     &mut self,
>     Terminator::Intrinsic { intrinsic, arguments, ret: ret_expr, next_block }: Terminator
> ) -> NdResult {
>     // First evaluate return place (left-to-right evaluation).
>     let (ret_place, ret_ty) = self.eval_place(ret_expr)?;
>
>     // Evaluate all arguments.
>     let arguments = arguments.try_map(|arg| self.eval_value(arg))?;
>
>     // Run the actual intrinsic.
>     let value = self.eval_intrinsic(intrinsic, arguments, ret_ty)?;
>
>     // Store return value.
>     // `eval_intrinsic` above must guarantee that `value` has the right type.
>     self.place_store(ret_place, value, ret_ty)?;
>
>     // Jump to next block.
>     if let Some(next_block) = next_block {
>         self.jump_to_block(next_block)?;
>     } else {
>         throw_ub!(\"return from an intrinsic where caller did not specify next block\");
>     }
>
>     ret(())
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
  | .Intrinsic intrinsic arguments retExpr nextBlock => do
    let ((retPlace, retTy), m) ← evalPlace m retExpr
    let (args, m) ← evalArgs m arguments
    let (value, m) ← evalIntrinsic m intrinsic args retTy
    let m ← placeStore m retPlace value retTy
    match nextBlock with
    | some nb => jumpToBlock m nb
    | none => ub "return from an intrinsic where caller did not specify next block"
  | _ => unsupported "eval_terminator for a terminator other than Goto/Switch/Unreachable/Return/Intrinsic"

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

/-! ## Polymorphic `Machine<M>` execution (`spec/lang/machine.md`)

The definitions below generalize `Machine` execution from `BM =
BasicMemory<x86_64>` to any `M` carrying `[Memory M] [MemoryOps M]`, wiring
`ValueExpr::AddrOf`, `Statement::Validate` (`retag_val`), and
`Terminator::Return` (`end_call`) through `ConcurrentMemory<M>` and
instantiating both `BM` (`instMemoryOpsBM`, proved unconditionally equal to
`step` / `steps` in `Correspondence/Pointers.lean`) and
`TBM = TreeBorrowsMemory<x86_64>` (`instMemoryOpsTBM`, `stepTB`, `stepsTB`). -/

/-- Exposed provenances in `TreeBorrowsMemory` whose allocation is live and
contains `addr` (`spec/mem/intptrcast.md`), paralleling `int2ptrCandidates`:
> "|p| self.exposed.contains(p)," -/
def tbmExposedInBounds (tbm : TBM) (exposed : Set TreeBorrowsProvenance) (addr : Int) :
    List TreeBorrowsProvenance :=
  exposed.elems.filter (fun (id, _) =>
    if 0 ≤ id._0 then
      match tbm.mem.allocations[id._0.toNat]? with
      | some a =>
        a.live && decide (a.addr ≤ addr) && decide (addr ≤ a.addr + (Allocation.size a).bytes)
      | none => false
    else false)

/-- `MemoryOps` instance for `BM = BasicMemory<x86_64>` (`spec/mem/basic.md`,
`spec/mem/interface.md`). -/
instance instMemoryOpsBM : MemoryOps BM where
  decEqProv := (inferInstance : DecidableEq Prov)
  new := fun () => BasicMemory.new
  allocate := BM.allocate
  deallocate := BM.deallocate
  store := BM.store
  load := BM.load
  dereferenceable := BM.dereferenceable
  signed_dereferenceable := BM.signed_dereferenceable
  retag_ptr := fun mem frameExtra ptr _ _ _ _ => pure (ptr, mem, frameExtra)
  new_call := ()
  end_call := fun mem _ => pure mem
  leak_check := BasicMemory.leak_check
  exposedInBounds := fun mem exposed addr => int2ptrCandidates mem.allocations exposed addr

/-- `MemoryOps` instance for `TBM = TreeBorrowsMemory<x86_64>`
(`spec/mem/tree_borrows/memory.md`, `spec/mem/interface.md`). -/
instance instMemoryOpsTBM : MemoryOps TBM where
  decEqProv := (inferInstance : DecidableEq TreeBorrowsProvenance)
  new := TreeBorrowsMemory.new
  allocate := TreeBorrowsMemory.allocate
  deallocate := TreeBorrowsMemory.deallocate
  store := TreeBorrowsMemory.store
  load := TreeBorrowsMemory.load
  dereferenceable := TreeBorrowsMemory.dereferenceable
  signed_dereferenceable := TreeBorrowsMemory.signed_dereferenceable
  retag_ptr := TreeBorrowsMemory.retag_ptr
  new_call := TreeBorrowsMemory.new_call
  end_call := TreeBorrowsMemory.end_call
  leak_check := TreeBorrowsMemory.leak_check
  exposedInBounds := tbmExposedInBounds

/-- Polymorphic `AbstractByte::data` (`spec/mem/interface.md`); see `AbstractByte.data`:
> "pub fn data(self) -> Option<u8> {
>     match self {
>         AbstractByte::Uninit => None,
>         AbstractByte::Init(data, _) => Some(data),
>     }
> }" -/
def AbstractByte.dataM {Provenance : Type} : AbstractByte Provenance → Option UInt8
  | .Uninit => none
  | .Init b _ => some b

/-- Polymorphic `AbstractByte::provenance_frag` (`spec/mem/interface.md`); see
`AbstractByte.provenance_frag`:
> "pub fn provenance_frag(self) -> Option<ProvenanceFrag<Provenance>> {
>     match self {
>         AbstractByte::Uninit => None,
>         AbstractByte::Init(_, frag) => frag,
>     }
> }" -/
def AbstractByte.provenance_fragM {Provenance : Type} :
    AbstractByte Provenance → Option (ProvenanceFrag Provenance)
  | .Uninit => none
  | .Init _ frag => frag

/-- Polymorphic `Type::decode` for `Int` (`spec/lang/representation.md`); see `Type.decodeInt`:
> "fn decode<M: Memory>(Type::Int(IntType { signed, size }): Self, bytes: ..) -> Option<Value<M>> {
>     if bytes.len() != size.bytes() { panic!(..); }
>     // Fails if any byte is `Uninit`.
>     let bytes_data: List<u8> = bytes.try_map(|b| b.data())?;
>     ret(Value::Int(M::T::ENDIANNESS.decode(signed, bytes_data)))
> }" -/
def Type.decodeIntM {M : Type} [Memory M] :
    IntType → List (AbstractByte (Memory.Provenance M)) → Interp (Option (Value M))
  | ⟨signed, size⟩, bytes =>
    if bytes.length ≠ size.bytes then specPanic "decode of Type::Int with invalid length"
    else
      match bytes.mapM AbstractByte.dataM with
      | some data => pure (some (.Int (Endianness.decode x86_64.ENDIANNESS signed data)))
      | none => pure none

/-- Polymorphic `Type::encode` for `Int` (`spec/lang/representation.md`); see `Type.encodeInt`:
> "fn encode<M: Memory>(Type::Int(IntType { signed, size }): Self, val: Value<M>) -> .. {
>     let Value::Int(i) = val else { panic!() };
>     // `Endianness::encode` will do the integer's bound check.
>     let bytes_data = M::T::ENDIANNESS.encode(signed, size, i).unwrap();
>     bytes_data.map(|b| AbstractByte::Init(b, None))
> }" -/
def Type.encodeIntM {M : Type} [Memory M] :
    IntType → Value M → Interp (List (AbstractByte (Memory.Provenance M)))
  | ⟨signed, size⟩, .Int i =>
    match Endianness.encode x86_64.ENDIANNESS signed size i with
    | some data => pure (data.map (fun b => .Init b none))
    | none => specPanic "Endianness::encode(..).unwrap()"
  | _, _ => specPanic "encode: Type::Int with a non-Int value"

/-- Polymorphic provenance fold of `decode_ptr` (`spec/lang/representation.md`);
see `decodePtrProvenance`:
> "let provenance = bytes.fold_with_idx(
>     bytes[0].provenance_frag().map(|frag| frag.provenance),
>     |acc, idx, byte| {
>         // Crucially, if `acc` is ever `None`, it remains `None`.
>         if let Some(frag) = byte.provenance_frag() &&
>             frag.position == idx && Some(frag.provenance) == acc
>         {
>             acc
>         } else {
>             None
>         }
>     }
> );" -/
def decodePtrProvenanceM {M : Type} [Memory M] [MemoryOps M] :
    Nat → Option (Memory.Provenance M) → List (AbstractByte (Memory.Provenance M)) →
    Option (Memory.Provenance M)
  | _, acc, [] => acc
  | idx, acc, byte :: rest =>
    let acc' : Option (Memory.Provenance M) :=
      match AbstractByte.provenance_fragM byte with
      | some frag =>
        if frag.position = (idx : Int) ∧ some frag.provenance = acc then acc else none
      | none => none
    decodePtrProvenanceM (idx + 1) acc' rest

/-- Polymorphic initial provenance of `decode_ptr` (`spec/lang/representation.md`);
see `firstProvenance`:
> "bytes[0].provenance_frag().map(|frag| frag.provenance)," -/
def firstProvenanceM {M : Type} [Memory M] :
    List (AbstractByte (Memory.Provenance M)) → Option (Memory.Provenance M)
  | byte :: _ => (AbstractByte.provenance_fragM byte).map (fun frag => frag.provenance)
  | [] => none

/-- Polymorphic `decode_ptr` (`spec/lang/representation.md`); see `decodePtr`:
> "let provenance = bytes.fold_with_idx(
>     bytes[0].provenance_frag().map(|frag| frag.provenance),
>     |acc, idx, byte| {
>         // Crucially, if `acc` is ever `None`, it remains `None`.
>         if let Some(frag) = byte.provenance_frag() &&
>             frag.position == idx && Some(frag.provenance) == acc
>         {
>             acc
>         } else {
>             None
>         }
>     }
> );" -/
def decodePtrM {M : Type} [Memory M] [MemoryOps M]
    (bytes : List (AbstractByte (Memory.Provenance M))) :
    Interp (Option (ThinPointer (Memory.Provenance M))) :=
  if bytes.length ≠ x86_64.PTR_SIZE.bytes then specPanic "decode of thin pointer with invalid length"
  else
    match bytes.mapM AbstractByte.dataM with
    | none => pure none
    | some data =>
      let addr := Endianness.decode x86_64.ENDIANNESS .Unsigned data
      pure (some { addr := addr, provenance := decodePtrProvenanceM (M := M) 0 (firstProvenanceM (M := M) bytes) bytes })

/-- Polymorphic byte list of `encode_ptr` (`spec/lang/representation.md`); see `encodePtrBytes`:
> "bytes_data.map_with_idx(|i, b|
>     AbstractByte::Init(b, ptr.provenance.map(|provenance|
>         ProvenanceFrag { provenance, position: i }
>     ))
> )" -/
def encodePtrBytesM {M : Type} [Memory M] (provenance : Option (Memory.Provenance M)) :
    Nat → List UInt8 → List (AbstractByte (Memory.Provenance M))
  | _, [] => []
  | idx, b :: rest =>
    .Init b (provenance.map (fun p => { provenance := p, position := (idx : Int) })) ::
      encodePtrBytesM provenance (idx + 1) rest

/-- Polymorphic `encode_ptr` (`spec/lang/representation.md`); see `encodePtr`:
> "bytes_data.map_with_idx(|i, b|
>     AbstractByte::Init(b, ptr.provenance.map(|provenance|
>         ProvenanceFrag { provenance, position: i }
>     ))
> )" -/
def encodePtrM {M : Type} [Memory M] (ptr : ThinPointer (Memory.Provenance M)) :
    Interp (List (AbstractByte (Memory.Provenance M))) :=
  match Endianness.encode x86_64.ENDIANNESS .Unsigned x86_64.PTR_SIZE ptr.addr with
  | some data => pure (encodePtrBytesM (M := M) ptr.provenance 0 data)
  | none => specPanic "M::T::ENDIANNESS.encode(Unsigned, M::T::PTR_SIZE, ptr.addr).unwrap()"

/-- Polymorphic `PointerMetaKind::decode_value` (`spec/lang/representation.md`);
see `PointerMetaKind.decode_value`:
> "fn decode_value<M: Memory>(self, value: Value<M>) -> Option<PointerMeta<M::Provenance>> {
>     match (self, value) {
>         (PointerMetaKind::None, Value::Tuple(fields)) if fields.is_empty() => None,
>         (PointerMetaKind::ElementCount, Value::Int(count)) => Some(PointerMeta::ElementCount(count)),
>         (PointerMetaKind::VTablePointer(_), Value::Ptr(ptr)) if ptr.metadata.is_none() => Some(PointerMeta::VTablePointer(ptr.thin_pointer)),
>         _ => panic!(\"PointerMeta::decode_value called with invalid value\"),
>     }
> }" -/
def PointerMetaKind.decode_valueM {M : Type} [Memory M] :
    PointerMetaKind → Value M → Interp (Option (PointerMeta (Memory.Provenance M)))
  | .None, .Tuple [] => pure none
  | .ElementCount, .Int count => pure (some (.ElementCount count))
  | .VTablePointer _, .Ptr ⟨thin, none⟩ => pure (some (.VTablePointer thin))
  | _, _ => specPanic "PointerMeta::decode_value called with invalid value"

/-- Polymorphic `PointerMetaKind::encode_as_value` (`spec/lang/representation.md`);
see `PointerMetaKind.encode_as_value`:
> "fn encode_as_value<M: Memory>(self, meta: Option<PointerMeta<M::Provenance>>) -> Value<M> {
>     match (self, meta) {
>         (PointerMetaKind::None, None) => unit_value(),
>         (PointerMetaKind::ElementCount, Some(PointerMeta::ElementCount(count))) => Value::Int(count),
>         (PointerMetaKind::VTablePointer(_), Some(PointerMeta::VTablePointer(ptr))) => Value::Ptr(ptr.widen(None)),
>         _ => panic!(\"PointerMeta::encode_as_value called with invalid value\"),
>     }
> }" -/
def PointerMetaKind.encode_as_valueM {M : Type} [Memory M] :
    PointerMetaKind → Option (PointerMeta (Memory.Provenance M)) → Interp (Value M)
  | .None, none => pure (.Tuple [])
  | .ElementCount, some (.ElementCount count) => pure (.Int count)
  | .VTablePointer _, some (.VTablePointer ptr) => pure (.Ptr { thin_pointer := ptr, metadata := none })
  | _, _ => specPanic "PointerMeta::encode_as_value called with invalid value"

/-- Polymorphic metadata field decoder (`spec/lang/representation.md`); see `decodeMetaField`:
> "PointerMetaKind::ElementCount => Type::Int(IntType::usize_ty::<T>()),
>  PointerMetaKind::VTablePointer(trait_name) => Type::Ptr(PtrType::VTablePtr(trait_name))," -/
def decodeMetaFieldM {M : Type} [Memory M] [MemoryOps M] (metaKind : PointerMetaKind)
    (bytes : List (AbstractByte (Memory.Provenance M))) : Interp (Option (Value M)) :=
  match metaKind with
  | .ElementCount => Type.decodeIntM IntType.usize_ty bytes
  | .VTablePointer _ => do
    match ← decodePtrM (M := M) bytes with
    | some ptr => pure (some (.Ptr { thin_pointer := ptr, metadata := none }))
    | none => pure none
  | .None => specPanic "as_wide_pair always returns a suitable metadata type"

/-- Polymorphic wide-pointer decoder (`spec/lang/representation.md`); see `decodeWidePtr`:
> "if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
>     // This will recursively call this decode function again, but with a thin pointer type.
>     let Value::Tuple(parts) = pair_ty.decode::<M>(bytes)? else {
>         panic!(\"as_wide_pair always returns a tuple type\");
>     };
>     let Value::Ptr(ptr) = parts[0] else {
>         panic!(\"as_wide_pair always returns tuple with the first field being a thin pointer\");
>     };
>     // This metadata might not be well-formed, but we are allowed to return ill-formed pointers here.
>     let meta = ptr_type.meta_kind().decode_value(parts[1]);
>     assert!(meta.is_some(), \"as_wide_pair always returns a suitable metadata type\");
>     ret(Value::Ptr(ptr.thin_pointer.widen(meta)))
> }" -/
def decodeWidePtrM {M : Type} [Memory M] [MemoryOps M] (metaKind : PointerMetaKind)
    (bytes : List (AbstractByte (Memory.Provenance M))) : Interp (Option (Value M)) :=
  if bytes.length ≠ 2 * x86_64.PTR_SIZE.bytes then
    specPanic "decode of Type::Tuple with invalid length"
  else do
    match ← decodePtrM (M := M) (bytes.take x86_64.PTR_SIZE.bytes) with
    | none => pure none
    | some thin =>
      match ← decodeMetaFieldM (M := M) metaKind (bytes.drop x86_64.PTR_SIZE.bytes) with
      | none => pure none
      | some metaVal => do
        let ptrMeta ← PointerMetaKind.decode_valueM metaKind metaVal
        match ptrMeta with
        | some _ => pure (some (.Ptr (ThinPointer.widen thin ptrMeta)))
        | none => specPanic "assertion failed: as_wide_pair always returns a suitable metadata type"

/-- Polymorphic wide-pointer encoder (`spec/lang/representation.md`); see `encodeWidePtr`:
> "if let Some(pair_ty) = ptr_type.as_wide_pair::<M::T>() {
>     let thin_ptr_value = Value::Ptr(ptr.thin_pointer.widen(None));
>     let meta_data_value = ptr_type.meta_kind().encode_as_value::<M>(ptr.metadata);
>     let tuple = Value::Tuple(list![thin_ptr_value, meta_data_value]);
>
>     // This will recursively call this encode function again, but with a thin pointer type.
>     pair_ty.encode::<M>(tuple)
> }" -/
def encodeWidePtrM {M : Type} [Memory M] (metaKind : PointerMetaKind)
    (ptr : Pointer (Memory.Provenance M)) : Interp (List (AbstractByte (Memory.Provenance M))) := do
  let metaVal ← PointerMetaKind.encode_as_valueM (M := M) metaKind ptr.metadata
  let thinBytes ← encodePtrM (M := M) ptr.thin_pointer
  let metaBytes ← match metaKind, metaVal with
    | .ElementCount, v => Type.encodeIntM (M := M) IntType.usize_ty v
    | .VTablePointer _, .Ptr ⟨vtablePtr, none⟩ => encodePtrM (M := M) vtablePtr
    | _, _ => specPanic "as_wide_pair always returns a suitable metadata type"
  pure (thinBytes ++ metaBytes)

mutual

/-- Polymorphic `decode_discriminant` (`spec/lang/representation.md`); see `decodeDiscriminant`:
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
> }" -/
def decodeDiscriminantM {M : Type} [Memory M] {σ : Type}
    (accessor : σ → Offset → Size → Interp (List (AbstractByte (Memory.Provenance M)) × σ)) :
    Discriminator → σ → Interp (Option Int × σ)
  | .Known val, s => pure (some val, s)
  | .Invalid, s => pure (none, s)
  | .Branch offset valueType fallback ⟨children⟩, s => do
    let (bytes, s) ← accessor s offset valueType.size
    match ← Type.decodeIntM (M := M) valueType bytes with
    | some (.Int val) =>
      decodeDiscriminantChildrenM (M := M) accessor val
        (decodeDiscriminantM (M := M) accessor fallback) children s
    | _ => pure (none, s)

/-- Polymorphic child dispatch of `decode_discriminant` (`spec/lang/representation.md`);
see `decodeDiscriminantChildren`:
> "let next_discriminator = children.iter()
>     .find_map(|((start, end), child)|
>         if start <= val && val < end { Some(child) } else { None })
>     .unwrap_or(fallback);
> decode_discriminant::<M>(accessor, next_discriminator)" -/
def decodeDiscriminantChildrenM {M : Type} [Memory M] {σ : Type}
    (accessor : σ → Offset → Size → Interp (List (AbstractByte (Memory.Provenance M)) × σ))
    (val : Int) (onFallback : σ → Interp (Option Int × σ)) :
    List ((Int × Int) × Discriminator) → σ → Interp (Option Int × σ)
  | [], s => onFallback s
  | ((start, end_), child) :: rest, s =>
    if start ≤ val ∧ val < end_ then decodeDiscriminantM (M := M) accessor child s
    else decodeDiscriminantChildrenM (M := M) accessor val onFallback rest s

end

/-- Polymorphic `encode_discriminant` (`spec/lang/representation.md`); see `encodeDiscriminant`:
> "fn encode_discriminant<M: Memory>(
>     mut accessor: impl FnMut(Offset, List<AbstractByte<M::Provenance>>) -> Result,
>     tagger: Map<Offset, (IntType, Int)>
> ) -> Result<()> {
>     for (offset, (value_type, value)) in tagger.iter() {
>         let bytes = Type::Int(value_type).encode::<M>(Value::Int(value));
>         accessor(offset, bytes)?;
>     }
>     ret(())
> }" -/
def encodeDiscriminantM {M : Type} [Memory M] {σ : Type}
    (accessor : σ → Offset → List (AbstractByte (Memory.Provenance M)) → Interp σ)
    (tagger : Map Offset (IntType × Int)) (s : σ) : Interp σ :=
  tagger.entries.foldlM (fun s entry => do
    let (offset, (valueType, value)) := entry
    let bytes ← Type.encodeIntM (M := M) valueType (.Int value)
    accessor s offset bytes) s

mutual

/-- Polymorphic `Type::decode` (`spec/lang/representation.md`); see `Type.decode`:
> "fn decode<M: Memory>(Type::Int(IntType { signed, size }): Self, bytes: ..) -> Option<Value<M>> {
>     if bytes.len() != size.bytes() { panic!(..); }
>     // Fails if any byte is `Uninit`.
>     let bytes_data: List<u8> = bytes.try_map(|b| b.data())?;
>     ret(Value::Int(M::T::ENDIANNESS.decode(signed, bytes_data)))
> }" -/
def Type.decodeM {M : Type} [Memory M] [MemoryOps M] :
    «Type» → List (AbstractByte (Memory.Provenance M)) → Interp (Option (Value M))
  | .Bool, bytes =>
    if bytes.length ≠ 1 then specPanic "decode of Type::Bool with invalid length"
    else
      match bytes with
      | [.Init 0 _] => pure (some (.Bool false))
      | [.Init 1 _] => pure (some (.Bool true))
      | _ => pure none
  | .Int t, bytes => Type.decodeIntM t bytes
  | .Tuple fields headLayout unsizedField, bytes =>
    match unsizedField with
    | some _ => specPanic "decode of Type::Tuple with unsized field"
    | none =>
      let (size, _) := TupleHeadLayout.head_size_and_align headLayout
      if bytes.length ≠ size.bytes then specPanic "decode of Type::Tuple with invalid length"
      else do
        match ← Type.decodeFieldsM fields bytes with
        | some vals => pure (some (.Tuple vals))
        | none => pure none
  | .Array elem count, bytes => do
    let elemLayout ← Type.layout elem
    let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
    let fullSize ← Size.mulInt elemSize count
    if bytes.length ≠ fullSize.bytes then
      specPanic "decode of Type::Array with invalid length"
    else do
      let chunks ← (List.range count.toNat).mapM (fun (i : Nat) =>
        subsliceWithLength bytes ((i : Int) * (elemSize.bytes : Int)) elemSize.bytes)
      let decoded ← tryMapM (fun elemBytes => Type.decodeM elem elemBytes) chunks
      pure (decoded.map Value.Tuple)
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
      match (← decodeDiscriminantM (M := M) accessor discriminator ()).1 with
      | none => pure none
      | some discriminant =>
        match ← Type.decodeVariantM variants discriminant bytes with
        | some value => pure (some (.Variant discriminant value))
        | none => pure none
  | .Slice _, _ => specPanic "decode of Type::Slice"
  | .TraitObject _, _ => specPanic "decode of Type::TraitObject"
  | .Ptr ptrType, bytes =>
    match PtrType.as_wide_pair ptrType with
    | some _ => decodeWidePtrM (PtrType.meta_kind ptrType) bytes
    | none => do
      match ← decodePtrM (M := M) bytes with
      | some ptr => pure (some (.Ptr (ThinPointer.widen ptr none)))
      | none => pure none

/-- Polymorphic tuple-field loop of `Type::decode` (`spec/lang/representation.md`);
see `Type.decodeFields`:
> "sized_fields.try_map(|(offset, ty)| {
>     let subslice = bytes.subslice_with_length(
>         offset.bytes(),
>         ty.layout::<M::T>().expect_size(\"WF ensures all sized tuple fields are sized\").bytes()
>     );
>     ty.decode::<M>(subslice)
> })?" -/
def Type.decodeFieldsM {M : Type} [Memory M] [MemoryOps M] :
    List (Offset × «Type») → List (AbstractByte (Memory.Provenance M)) →
    Interp (Option (List (Value M)))
  | [], _ => pure (some [])
  | (offset, ty) :: rest, bytes => do
    let size ← LayoutStrategy.expect_size (← Type.layout ty)
      "WF ensures all sized tuple fields are sized"
    let subslice ← subsliceWithLength bytes offset.bytes size.bytes
    match ← Type.decodeM ty subslice with
    | none => pure none
    | some v =>
      match ← Type.decodeFieldsM rest bytes with
      | none => pure none
      | some vs => pure (some (v :: vs))

/-- Polymorphic enum-variant lookup of `Type::decode` (`spec/lang/representation.md`);
see `Type.decodeVariant`:
> "let Some(value) = variants[discriminant].ty.decode(bytes)
>     else { return None };" -/
def Type.decodeVariantM {M : Type} [Memory M] [MemoryOps M] :
    List (Int × Variant) → Int → List (AbstractByte (Memory.Provenance M)) →
    Interp (Option (Value M))
  | [], _, _ => specPanic "map index: missing key (variants[discriminant])"
  | (d, ⟨ty, _⟩) :: rest, discriminant, bytes =>
    if d = discriminant then Type.decodeM ty bytes
    else Type.decodeVariantM rest discriminant bytes

end

/-- Polymorphic union-chunk loop of `Type::encode` (`spec/lang/representation.md`);
see `Type.encodeUnionChunks`:
> "for ((offset, size), data) in chunks.zip(chunk_data) {
>     assert_eq!(size.bytes(), data.len());
>     bytes.write_subslice_at_index(offset.bytes(), data);
> }" -/
def Type.encodeUnionChunksM {M : Type} [Memory M] :
    List (Offset × Size) → List (List (AbstractByte (Memory.Provenance M))) →
    List (AbstractByte (Memory.Provenance M)) →
    Interp (List (AbstractByte (Memory.Provenance M)))
  | (offset, size) :: chunks, data :: chunkData, bytes =>
    if size.bytes ≠ data.length then
      specPanic "assertion failed: size.bytes() == data.len()"
    else do
      let bytes ← writeSubsliceAtIndex bytes offset.bytes data
      Type.encodeUnionChunksM (M := M) chunks chunkData bytes
  | _, _, bytes => pure bytes

mutual

/-- Polymorphic `Type::encode` (`spec/lang/representation.md`); see `Type.encode`:
> "fn encode<M: Memory>(Type::Int(IntType { signed, size }): Self, val: Value<M>) -> .. {
>     let Value::Int(i) = val else { panic!() };
>     // `Endianness::encode` will do the integer's bound check.
>     let bytes_data = M::T::ENDIANNESS.encode(signed, size, i).unwrap();
>     bytes_data.map(|b| AbstractByte::Init(b, None))
> }" -/
def Type.encodeM {M : Type} [Memory M] :
    «Type» → Value M → Interp (List (AbstractByte (Memory.Provenance M)))
  | .Bool, .Bool b => pure [.Init (if b then 1 else 0) none]
  | .Bool, _ => specPanic "encode: Type::Bool with a non-Bool value"
  | .Int t, val => Type.encodeIntM t val
  | .Tuple fields headLayout unsizedField, val =>
    match unsizedField with
    | some _ => specPanic "encode of Type::Tuple with unsized field"
    | none =>
      let (size, _) := TupleHeadLayout.head_size_and_align headLayout
      match val with
      | .Tuple values =>
        if values.length ≠ fields.length then
          specPanic "assertion failed: values.len() == sized_fields.len()"
        else Type.encodeFieldsM fields values (List.replicate size.bytes .Uninit)
      | _ => specPanic "encode: Type::Tuple with a non-Tuple value"
  | .Array elem count, .Tuple values =>
    if (values.length : Int) ≠ count then
      specPanic "encode: Type::Array length mismatch"
    else do
      let encoded ← values.mapM (fun value => do
        let bytes ← Type.encodeM elem value
        let elemLayout ← Type.layout elem
        let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array element is sized"
        if bytes.length ≠ elemSize.bytes then
          specPanic "encode: Type::Array element byte length mismatch"
        else
          pure bytes)
      pure encoded.flatten
  | .Array _ _, _ => specPanic "encode: Type::Array with a non-Tuple value"
  | .Union _ chunks size _, val =>
    match val with
    | .Union chunkData =>
      if chunkData.length ≠ chunks.length then
        specPanic "assertion failed: chunk_data.len() == chunks.len()"
      else Type.encodeUnionChunksM (M := M) chunks chunkData (List.replicate size.bytes .Uninit)
    | _ => specPanic "encode: Type::Union with a non-Union value"
  | .Enum ⟨variants⟩ _ _ _ _, val =>
    match val with
    | .Variant discriminant data => Type.encodeVariantM variants discriminant data
    | _ => specPanic "encode: Type::Enum with a non-Variant value"
  | .Slice _, _ => specPanic "encode of Type::Slice"
  | .TraitObject _, _ => specPanic "encode of Type::TraitObject"
  | .Ptr ptrType, val =>
    match val with
    | .Ptr ptr =>
      match PtrType.as_wide_pair ptrType with
      | some _ => encodeWidePtrM (M := M) (PtrType.meta_kind ptrType) ptr
      | none =>
        match ptr.metadata with
        | none => encodePtrM (M := M) ptr.thin_pointer
        | some _ => specPanic "assertion failed: ptr_type and value have mismatching metadata"
    | _ => specPanic "val is WF for a pointer"

/-- Polymorphic tuple-field loop of `Type::encode` (`spec/lang/representation.md`);
see `Type.encodeFields`:
> "for ((offset, ty), value) in sized_fields.zip(values) {
>     bytes.write_subslice_at_index(offset.bytes(), ty.encode::<M>(value));
> }" -/
def Type.encodeFieldsM {M : Type} [Memory M] :
    List (Offset × «Type») → List (Value M) → List (AbstractByte (Memory.Provenance M)) →
    Interp (List (AbstractByte (Memory.Provenance M)))
  | (offset, ty) :: fields, value :: values, bytes => do
    let fieldBytes ← Type.encodeM ty value
    let bytes ← writeSubsliceAtIndex bytes offset.bytes fieldBytes
    Type.encodeFieldsM fields values bytes
  | _, _, bytes => pure bytes

/-- Polymorphic enum-variant encoder of `Type::encode` (`spec/lang/representation.md`);
see `Type.encodeVariant`:
> "let Variant { ty: variant, tagger } = variants[discriminant];
> let mut bytes = variant.encode(data);" -/
def Type.encodeVariantM {M : Type} [Memory M] :
    List (Int × Variant) → Int → Value M → Interp (List (AbstractByte (Memory.Provenance M)))
  | [], _, _ => specPanic "map index: missing key (variants[discriminant])"
  | (d, ⟨ty, tagger⟩) :: rest, discriminant, data =>
    if d = discriminant then do
      let bytes ← Type.encodeM ty data
      encodeDiscriminantM (M := M)
        (fun bytes offset valueBytes => writeSubsliceAtIndex bytes offset.bytes valueBytes)
        tagger bytes
    else Type.encodeVariantM rest discriminant data

end

/-- Polymorphic union-chunk check of `check_value` (`spec/lang/representation.md`);
see `checkUnionChunks`:
> "for (data, (_, size)) in chunk_data.zip(chunks) {
>     ensure_else_ub(data.len() == size.bytes(), \"Value::Union: invalid chunk data\")?;
> }" -/
def checkUnionChunksM {Provenance : Type} :
    List (List (AbstractByte Provenance)) → List (Offset × Size) → Interp Unit
  | data :: chunkData, (_, size) :: chunks => do
    ensureElseUb (data.length == size.bytes) "Value::Union: invalid chunk data"
    checkUnionChunksM chunkData chunks
  | _, _ => pure ()

/-- Polymorphic `ThinPointer::wrapping_offset::<x86_64>` (`spec/mem/pointer.md`);
see `ThinPointer.wrapping_offset`:
> "pub fn wrapping_offset<T: Target>(self, offset: Int) -> Self {
>     let addr = self.addr + offset;
>     let addr = addr.bring_in_bounds(Unsigned, T::PTR_SIZE);
>     ThinPointer { addr, ..self }
> }" -/
def ThinPointer.wrapping_offsetM {Provenance : Type} (ptr : ThinPointer Provenance)
    (offset : Int) : ThinPointer Provenance :=
  let addr := ptr.addr + offset
  let addr := bringInBounds addr .Unsigned x86_64.PTR_SIZE
  { ptr with addr := addr }

/-- `ConcurrentMemory::new` (`spec/mem/concurrent.md`):
> "pub fn new(params: M::Params) -> Self {
>     Self {
>         memory: M::new(params),
>         accesses: list![],
>     }
> }" -/
def ConcurrentMemory.new {M : Type} [Memory M] [MemoryOps M] (params : Memory.Params M) :
    ConcurrentMemory M :=
  { memory := MemoryOps.new params, accesses := [] }

/-- Polymorphic `ConcurrentMemory::store` (`spec/mem/concurrent.md`); see `CM.store`:
> "let access = Access { ty: AccessType::Store, atomicity, addr: ptr.addr,
>                        len: Size::from_bytes(bytes.len()).unwrap(), };
>  self.accesses.push(access);
>  self.memory.store(ptr, bytes, align)" -/
def ConcurrentMemory.store {M : Type} [Memory M] [MemoryOps M] (cm : ConcurrentMemory M)
    (ptr : ThinPointer (Memory.Provenance M))
    (bytes : List (AbstractByte (Memory.Provenance M))) (align : Align)
    (atomicity : Atomicity) : Interp (ConcurrentMemory M) := do
  let access : Access := ⟨.Store, atomicity, ptr.addr, ⟨bytes.length⟩⟩
  let memory ← MemoryOps.store cm.memory ptr bytes align
  pure { memory := memory, accesses := cm.accesses ++ [access] }

/-- Polymorphic `ConcurrentMemory::load` (`spec/mem/concurrent.md`); see `CM.load`:
> "let access = Access { ty: AccessType::Load, atomicity, addr: ptr.addr, len, };
>  self.accesses.push(access);
>  self.memory.load(ptr, len, align)" -/
def ConcurrentMemory.load {M : Type} [Memory M] [MemoryOps M] (cm : ConcurrentMemory M)
    (ptr : ThinPointer (Memory.Provenance M)) (len : Size) (align : Align)
    (atomicity : Atomicity) :
    Interp (List (AbstractByte (Memory.Provenance M)) × ConcurrentMemory M) := do
  let access : Access := ⟨.Load, atomicity, ptr.addr, len⟩
  let (bytes, memory) ← MemoryOps.load cm.memory ptr len align
  pure (bytes, { memory := memory, accesses := cm.accesses ++ [access] })

/-- Polymorphic `ConcurrentMemory::allocate` (`spec/mem/concurrent.md`); see `CM.allocate`:
> "pub fn allocate(&mut self, kind: AllocationKind, size: Size, align: Align) -> NdResult<ThinPointer<M::Provenance>> {
>     self.memory.allocate(kind, size, align)
> }" -/
def ConcurrentMemory.allocate {M : Type} [Memory M] [MemoryOps M] (cm : ConcurrentMemory M)
    (kind : AllocationKind) (size : Size) (align : Align) :
    Interp (ThinPointer (Memory.Provenance M) × ConcurrentMemory M) := do
  let (ptr, mem) ← MemoryOps.allocate cm.memory kind size align
  pure (ptr, { cm with memory := mem })

/-- Polymorphic `ConcurrentMemory::deallocate` (`spec/mem/concurrent.md`); see `CM.deallocate`:
> "pub fn deallocate(&mut self, ptr: ThinPointer<M::Provenance>, kind: AllocationKind, size: Size, align: Align) -> Result {
>     self.memory.deallocate(ptr, kind, size, align)
> }" -/
def ConcurrentMemory.deallocate {M : Type} [Memory M] [MemoryOps M] (cm : ConcurrentMemory M)
    (ptr : ThinPointer (Memory.Provenance M)) (kind : AllocationKind) (size : Size)
    (align : Align) : Interp (ConcurrentMemory M) := do
  pure { cm with memory := ← MemoryOps.deallocate cm.memory ptr kind size align }

/-- Polymorphic `ConcurrentMemory::dereferenceable` (`spec/mem/concurrent.md`);
see `CM.dereferenceable`:
> "pub fn dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Size) -> Result {
>     self.memory.dereferenceable(ptr, len)
> }" -/
def ConcurrentMemory.dereferenceable {M : Type} [Memory M] [MemoryOps M]
    (cm : ConcurrentMemory M) (ptr : ThinPointer (Memory.Provenance M)) (len : Size) :
    Interp Unit :=
  MemoryOps.dereferenceable cm.memory ptr len

/-- Polymorphic `ConcurrentMemory::signed_dereferenceable` (`spec/mem/concurrent.md`);
see `CM.signed_dereferenceable`:
> "pub fn signed_dereferenceable(&self, ptr: ThinPointer<M::Provenance>, len: Int) -> Result {
>     self.memory.signed_dereferenceable(ptr, len)
> }" -/
def ConcurrentMemory.signed_dereferenceable {M : Type} [Memory M] [MemoryOps M]
    (cm : ConcurrentMemory M) (ptr : ThinPointer (Memory.Provenance M)) (len : Int) :
    Interp Unit :=
  MemoryOps.signed_dereferenceable cm.memory ptr len

/-- `ConcurrentMemory::retag_ptr` (`spec/mem/concurrent.md`):
> "pub fn retag_ptr(
>     &mut self,
>     frame_extra: &mut M::FrameExtra,
>     ptr: Pointer<M::Provenance>,
>     ptr_type: PtrType,
>     fn_entry: bool,
>     fn_implicit_writes: bool,
>     vtable_lookup: impl Fn(ThinPointer<M::Provenance>) -> crate::lang::VTable + 'static,
> ) -> Result<Pointer<M::Provenance>> {
>     self.memory.retag_ptr(frame_extra, ptr, ptr_type, fn_entry, fn_implicit_writes, vtable_lookup)
> }" -/
def ConcurrentMemory.retag_ptr {M : Type} [Memory M] [MemoryOps M]
    (cm : ConcurrentMemory M) (frameExtra : Memory.FrameExtra M)
    (ptr : Pointer (Memory.Provenance M)) (ptrType : PtrType)
    (fnEntry fnImplicitWrites : Bool)
    (vtableLookup : ThinPointer (Memory.Provenance M) → Interp VTable) :
    Interp (Pointer (Memory.Provenance M) × ConcurrentMemory M × Memory.FrameExtra M) := do
  let (ptr', mem', extra') ←
    MemoryOps.retag_ptr cm.memory frameExtra ptr ptrType fnEntry fnImplicitWrites vtableLookup
  pure (ptr', { cm with memory := mem' }, extra')

/-- `ConcurrentMemory::end_call` (`spec/mem/concurrent.md`):
> "pub fn end_call(&mut self, extra: M::FrameExtra) -> Result {
>     self.memory.end_call(extra)
> }" -/
def ConcurrentMemory.end_call {M : Type} [Memory M] [MemoryOps M]
    (cm : ConcurrentMemory M) (extra : Memory.FrameExtra M) : Interp (ConcurrentMemory M) := do
  pure { cm with memory := ← MemoryOps.end_call cm.memory extra }

/-- `ConcurrentMemory::leak_check` (`spec/mem/concurrent.md`):
> "pub fn leak_check(&self) -> Result {
>     self.memory.leak_check()
> }" -/
def ConcurrentMemory.leak_check {M : Type} [Memory M] [MemoryOps M]
    (cm : ConcurrentMemory M) : Interp Unit :=
  MemoryOps.leak_check cm.memory

/-- Polymorphic `ConcurrentMemory::check_data_races` (`spec/mem/concurrent.md`);
see `CM.check_data_races`:
> "if prev_sync_threads.contains(current_thread) { return Ok(()) }
>  for access in self.accesses {
>      if prev_accesses.any(|prev_access| access.races(prev_access)) { throw_ub!(\"Data race\"); }
>  }
>  Ok(())" -/
def ConcurrentMemory.check_data_races {M : Type} [Memory M] (cm : ConcurrentMemory M)
    (current : ThreadId) (prev : Set ThreadId × List Access) : Interp Unit :=
  if setContains prev.1 current then pure ()
  else if cm.accesses.any (fun a => prev.2.any (fun p => Access.races a p)) then ub "Data race"
  else pure ()

/-- Polymorphic `ConcurrentMemory::deinit` (`spec/lang/step/statements.md`); see `CM.deinit`:
> "fn deinit(&mut self, ptr: ThinPointer<M::Provenance>, len: Size, align: Align) -> Result {
>     self.store(ptr, list![AbstractByte::Uninit; len.bytes()], align, Atomicity::None)?;
>     ret(())
> }" -/
def ConcurrentMemory.deinit {M : Type} [Memory M] [MemoryOps M] (cm : ConcurrentMemory M)
    (ptr : ThinPointer (Memory.Provenance M)) (len : Size) (align : Align) :
    Interp (ConcurrentMemory M) :=
  ConcurrentMemory.store cm ptr (List.replicate len.bytes .Uninit) align .None

/-- Polymorphic `Machine::reset_data_race_tracking` (`spec/lang/machine.md`);
see `resetDataRaceTracking`:
> "let mut prev_sync = self.synchronized_threads;
>  // Every thread is always synchronized with itself.
>  prev_sync.insert(self.active_thread);
>  // Reset access tracking list.
>  let prev_accesses = self.mem.reset_accesses();
>  (prev_sync, prev_accesses)" -/
def resetDataRaceTrackingM {M : Type} [Memory M] (m : Machine M) :
    (Set ThreadId × List Access) × Machine M :=
  ((setInsert m.synchronized_threads m.active_thread, m.mem.accesses),
   { m with mem := { m.mem with accesses := [] } })

/-- Polymorphic thread choice in `Machine::step` (`spec/lang/machine.md`);
see `pickActiveThread`:
> "self.active_thread = pick(distr, |id: ThreadId| {
>      let Some(thread) = self.threads.get(id) else { return false; };
>      thread.state == ThreadState::Enabled
>  })?;" -/
def pickActiveThreadM {M : Type} [Memory M] (m : Machine M) : Interp ThreadId :=
  match (List.range m.threads.length).filter
      (fun i => match m.threads[i]? with
        | some t => decide (t.state = .Enabled)
        | none => false) with
  | [i] => pure (Int.ofNat i)
  | [] => unsupported "pick with no valid choice (no behavior)"
  | _ => unsupported "daemonic choice among several enabled threads"

/-- Polymorphic `Machine::active_thread` (`spec/lang/machine.md`); see `activeThread`:
> "fn active_thread(&self) -> Thread<M> {
>     self.threads[self.active_thread]
> }" -/
def activeThreadM {M : Type} [Memory M] (m : Machine M) : Interp (Thread M) :=
  listIndex m.threads m.active_thread "self.threads[self.active_thread]"

/-- Polymorphic `Machine::cur_frame` (`spec/lang/machine.md`); see `curFrame`:
> "fn cur_frame(&self) -> StackFrame<M> {
>     self.active_thread().cur_frame()
> }
> ..
> fn cur_frame(&self) -> StackFrame<M> {
>     self.stack.last().unwrap()
> }" -/
def curFrameM {M : Type} [Memory M] (m : Machine M) : Interp (StackFrame M) := do
  let t ← activeThreadM m
  match t.stack.getLast? with
  | some f => pure f
  | none => specPanic "self.stack.last().unwrap()"

/-- Polymorphic `Machine::try_mutate_cur_frame` for a pure frame update
(`spec/lang/machine.md`); see `mutateCurFrame`:
> "if self.stack.is_empty() { panic!(..); }
>  let last_idx = self.stack.len() - 1;
>  self.stack.try_mutate_at(last_idx, f)" -/
def mutateCurFrameM {M : Type} [Memory M] (m : Machine M) (f : StackFrame M → StackFrame M) :
    Interp (Machine M) := do
  let t ← activeThreadM m
  match t.stack.getLast? with
  | none => specPanic "`try_mutate_cur_frame` called on empty stack!"
  | some fr => do
    let t' : Thread M := { t with stack := t.stack.dropLast ++ [f fr] }
    let threads ← listSet m.threads m.active_thread t' "mutate_at"
    pure { m with threads := threads }

/-- Polymorphic `Machine::mutate_cur_frame` returning `(O, Machine<M>)`
(`spec/lang/machine.md`), used by `ValueExpr::AddrOf` and `Machine::retag_val`:
> "fn mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>, &mut ConcurrentMemory<M>) -> O) -> O {
>     self.threads.mutate_at(self.active_thread, |thread| thread.mutate_cur_frame(|frame| f(frame, &mut self.mem)))
> }"
> "fn mutate_cur_frame<O>(&mut self, f: impl FnOnce(&mut StackFrame<M>) -> O) -> O {
>     if self.stack.is_empty() {
>         panic!(\"`mutate_cur_frame` called on empty stack!\");
>     }
>
>     let last_idx = self.stack.len() - 1;
>     self.stack.mutate_at(last_idx, f)
> }" -/
def mutateCurFrameOutM {M : Type} {α : Type} [Memory M] (m : Machine M)
    (f : StackFrame M → ConcurrentMemory M → Interp (α × StackFrame M × ConcurrentMemory M)) :
    Interp (α × Machine M) := do
  let t ← listIndex m.threads m.active_thread "self.threads.mutate_at(self.active_thread, ..)"
  match t.stack.getLast? with
  | none => specPanic "`mutate_cur_frame` called on empty stack!"
  | some fr => do
    let (out, fr', cm') ← f fr m.mem
    let t' : Thread M := { t with stack := t.stack.dropLast ++ [fr'] }
    let threads ← listSet m.threads m.active_thread t' "mutate_at"
    pure (out, { m with mem := cm', threads := threads })

/-- Polymorphic `Machine::try_mutate_cur_frame` (`spec/lang/machine.md`);
see `tryMutateCurFrame`:
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
def tryMutateCurFrameM {M : Type} [Memory M] (m : Machine M)
    (f : StackFrame M → ConcurrentMemory M → Interp (StackFrame M × ConcurrentMemory M)) :
    Interp (Machine M) := do
  let t ← activeThreadM m
  match t.stack.getLast? with
  | none => specPanic "`try_mutate_cur_frame` called on empty stack!"
  | some fr => do
    let (fr', cm') ← f fr m.mem
    let t' : Thread M := { t with stack := t.stack.dropLast ++ [fr'] }
    let threads ← listSet m.threads m.active_thread t' "try_mutate_at"
    pure { m with mem := cm', threads := threads }

/-- Polymorphic `Machine::jump_to_block` (`spec/lang/machine.md`); see `jumpToBlock`:
> "self.next_block = b; self.next_stmt = Int::ZERO;" -/
def jumpToBlockM {M : Type} [Memory M] (m : Machine M) (b : BbName) : Interp (Machine M) :=
  mutateCurFrameM m (fun fr => { fr with next_block := b, next_stmt := 0 })

/-- Polymorphic `Machine::vtable_lookup` (`spec/lang/machine.md`); see `vtableLookup`:
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
def vtableLookupM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) : Interp VTable := do
  match m.vtable_ptrs.entries.find?
      (fun (_, (vtablePtr : ThinPointer (Memory.Provenance M))) => decide (vtablePtr = ptr)) with
  | some (name, _) => mapIndex m.prog.vtables name "vtables[name]"
  | none => specPanic "ptrs.iter().find(|(_, vtable_ptr)| *vtable_ptr == ptr).unwrap()"

/-- Polymorphic `Machine::compute_size` (`spec/lang/machine.md`); see `computeSize`:
> "fn compute_size(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Size {
>     let (size, _) = layout.compute_size_and_align(meta, self.vtable_lookup());
>     size
> }" -/
def computeSizeM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (layout : LayoutStrategy)
    (metadata : Option (PointerMeta (Memory.Provenance M))) : Interp Size := do
  let (size, _) ← LayoutStrategy.compute_size_and_align (vtableLookupM m) layout metadata
  pure size

/-- Polymorphic `Machine::compute_align` (`spec/lang/machine.md`); see `computeAlign`:
> "fn compute_align(&self, layout: LayoutStrategy, meta: Option<PointerMeta<M::Provenance>>) -> Align {
>     let (_, align) = layout.compute_size_and_align(meta, self.vtable_lookup());
>     align
> }" -/
def computeAlignM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (layout : LayoutStrategy)
    (metadata : Option (PointerMeta (Memory.Provenance M))) : Interp Align := do
  let (_, align) ← LayoutStrategy.compute_size_and_align (vtableLookupM m) layout metadata
  pure align

/-- Polymorphic `Machine::check_ptr_metadata` (`spec/lang/representation.md`);
see `checkPtrMetadata`:
> "fn check_ptr_metadata(&self, meta: Option<PointerMeta<M::Provenance>>, kind: PointerMetaKind) -> Result {
>     match (meta, kind) {
>         (None, PointerMetaKind::None) => {}
>         (Some(PointerMeta::ElementCount(num)), PointerMetaKind::ElementCount) =>
>             self.check_value(Value::Int(num), Type::Int(IntType::usize_ty::<M::T>()))?,
>         (Some(PointerMeta::VTablePointer(ptr)), PointerMetaKind::VTablePointer(trait_name)) => {
>             self.check_ptr(ptr.widen(None), PtrType::VTablePtr(trait_name))?;
>         }
>         _ => throw_ub!(\"Value::Ptr: invalid metadata\"),
>     };
>
>     Ok(())
> }" -/
def checkPtrMetadataM {Provenance : Type} (ptrMeta : Option (PointerMeta Provenance))
    (kind : PointerMetaKind) : Interp Unit :=
  match ptrMeta, kind with
  | none, .None => pure ()
  | some (.ElementCount num), .ElementCount =>
    ensureElseUb (IntType.can_represent IntType.usize_ty num) "Value::Int: invalid integer value"
  | some (.VTablePointer _), .VTablePointer _ =>
    unsupported "check_ptr_metadata for vtable pointer metadata (Machine::vtable_from_ptr)"
  | _, _ => ub "Value::Ptr: invalid metadata"

/-- Polymorphic `Machine::check_ptr` (`spec/lang/representation.md`); see `checkPtr`:
> "fn check_ptr(&self, ptr: Pointer<M::Provenance>, ptr_ty: PtrType) -> Result {
>     ensure_else_ub(ptr.thin_pointer.addr.in_bounds(Unsigned, M::T::PTR_SIZE), \"Value::Ptr: pointer out-of-bounds\")?;
>
>     // This has to be checked first, to ensure we can e.g. compute size/align below.
>     self.check_ptr_metadata(ptr.metadata, ptr_ty.meta_kind())?;
>
>     // Safe pointer, i.e. references, boxes
>     if let Some(pointee) = ptr_ty.safe_pointee() {
>         let size = self.compute_size(pointee.layout, ptr.metadata);
>         let align = self.compute_align(pointee.layout, ptr.metadata);
>         // The total size must be at most `isize::MAX`.
>         ensure_else_ub(size.bytes().in_bounds(Signed, M::T::PTR_SIZE), \"Value::Ptr: total size exeeds isize::MAX\")?;
>
>         // Safe pointers need to be non-null, aligned, dereferenceable, and not point to an uninhabited type.
>         // (Think: uninhabited types have impossible alignment.)
>         ensure_else_ub(ptr.thin_pointer.addr != 0, \"Value::Ptr: null safe pointer\")?;
>         ensure_else_ub(align.is_aligned(ptr.thin_pointer.addr), \"Value::Ptr: unaligned safe pointer\")?;
>         ensure_else_ub(pointee.inhabited, \"Value::Ptr: safe pointer to uninhabited type\")?;
>         ensure_else_ub(
>             self.mem.dereferenceable(ptr.thin_pointer, size).is_ok(),
>             \"Value::Ptr: non-dereferenceable safe pointer\"
>         )?;
>
>         // However, we do not care about the data stored wherever this pointer points to.
>     } else if let PtrType::VTablePtr(trait_name) = ptr_ty {
>         ..
>     }
>
>     Ok(())
> }" -/
def checkPtrM {M : Type} [Memory M] [MemoryOps M] (ptr : Pointer (Memory.Provenance M))
    (ptrTy : PtrType) (m : Option (Machine M) := none) : Interp Unit := do
  ensureElseUb (inBounds ptr.thin_pointer.addr .Unsigned x86_64.PTR_SIZE)
    "Value::Ptr: pointer out-of-bounds"
  checkPtrMetadataM ptr.metadata (PtrType.meta_kind ptrTy)
  match PtrType.safe_pointee ptrTy with
  | some pointee => do
    let lookup : ThinPointer (Memory.Provenance M) → Interp VTable := match m with
      | some mach => vtableLookupM mach
      | none => fun _ => unsupported "check_ptr for a trait-object safe pointer without a machine"
    let (size, align) ← LayoutStrategy.compute_size_and_align lookup pointee.layout ptr.metadata
    ensureElseUb (inBounds size.bytes .Signed x86_64.PTR_SIZE)
      "Value::Ptr: total size exeeds isize::MAX"
    ensureElseUb (ptr.thin_pointer.addr != 0)
      "Value::Ptr: null safe pointer"
    ensureElseUb (Align.is_aligned align ptr.thin_pointer.addr)
      "Value::Ptr: unaligned safe pointer"
    ensureElseUb pointee.inhabited
      "Value::Ptr: safe pointer to uninhabited type"
    match m with
    | some mach =>
      match ConcurrentMemory.dereferenceable mach.mem ptr.thin_pointer size with
      | .ok () => pure ()
      | .error (.ub _) => ub "Value::Ptr: non-dereferenceable safe pointer"
      | .error e => .error e
    | none =>
      if size.bytes = 0 then pure ()
      else
        match ptr.thin_pointer.provenance with
        | none => ub "Value::Ptr: non-dereferenceable safe pointer"
        | some _ => unsupported "check_ptr for a safe pointer (Memory::dereferenceable)"
  | none =>
    match ptrTy with
    | .VTablePtr _ => unsupported "check_ptr for a vtable pointer (Machine::vtable_from_ptr)"
    | _ => pure ()

mutual

/-- Polymorphic `Machine::check_value` (`spec/lang/representation.md`); see `checkValue`:
> "(Value::Int(i), Type::Int(int_ty)) => {
>     ensure_else_ub(int_ty.can_represent(i), \"Value::Int: invalid integer value\")?;
> }
> (Value::Bool(_), Type::Bool) => {},
> (Value::Ptr(ptr), Type::Ptr(ptr_ty)) => self.check_ptr(ptr, ptr_ty)?,
> (Value::Tuple(vals), Type::Tuple { sized_fields, unsized_field, .. }) => {
>     assert!(unsized_field.is_none(), \"Value: unsized structs cannot be represented as values\");
>     ensure_else_ub(vals.len() == sized_fields.len(), \"Value::Tuple: invalid number of fields\")?;
>     ..
> }
> (Value::Tuple(vals), Type::Array { elem, count }) => {
>     ensure_else_ub(vals.len() == count, \"Value::Tuple: invalid number of elements\")?;
>     for val in vals {
>         self.check_value(val, elem)?;
>     }
> }
> (Value::Union(chunk_data), Type::Union { chunks, .. }) => {
>     ensure_else_ub(chunk_data.len() == chunks.len(), \"Value::Union: invalid chunk size\")?;
>     ..
> }
> (Value::Variant { discriminant, data }, Type::Enum { variants, .. }) => {
>     ..
> }
> (_, Type::Slice { .. }) => panic!(\"Value: slices cannot be represented as values\"),
> (_, Type::TraitObject { .. }) => panic!(\"Value: trait objects cannot be represented as values\"),
> _ => panic!(\"Value: value does not match type\")" -/
def checkValueM {M : Type} [Memory M] [MemoryOps M] (val : Value M) (ty : «Type»)
    (m : Option (Machine M) := none) : Interp Unit :=
  match val, ty with
  | .Int i, .Int t =>
    ensureElseUb (IntType.can_represent t i) "Value::Int: invalid integer value"
  | .Bool _, .Bool => pure ()
  | .Ptr ptr, .Ptr ptrTy => checkPtrM ptr ptrTy m
  | .Tuple vals, .Tuple fields _ unsizedField =>
    match unsizedField with
    | some _ => specPanic "Value: unsized structs cannot be represented as values"
    | none => do
      ensureElseUb (vals.length == fields.length) "Value::Tuple: invalid number of fields"
      checkFieldsM vals fields m
  | .Tuple vals, .Array elem count => do
    ensureElseUb (decide ((vals.length : Int) = count)) "Value::Tuple: invalid number of elements"
    vals.forM (fun val => checkValueM val elem m)
  | .Union chunkData, .Union _ chunks _ _ => do
    ensureElseUb (chunkData.length == chunks.length) "Value::Union: invalid chunk size"
    checkUnionChunksM chunkData chunks
  | .Variant discriminant data, .Enum ⟨variants⟩ _ _ _ _ => checkVariantM variants discriminant data m
  | _, .Slice _ => specPanic "Value: slices cannot be represented as values"
  | _, .TraitObject _ => specPanic "Value: trait objects cannot be represented as values"
  | _, .Int _ => specPanic "Value: value does not match type"
  | _, .Bool => specPanic "Value: value does not match type"
  | _, .Tuple _ _ _ => specPanic "Value: value does not match type"
  | _, .Array _ _ => specPanic "Value: value does not match type"
  | _, .Union _ _ _ _ => specPanic "Value: value does not match type"
  | _, .Enum _ _ _ _ _ => specPanic "Value: value does not match type"
  | _, .Ptr _ => specPanic "Value: value does not match type"

/-- Polymorphic tuple-field loop of `check_value` (`spec/lang/representation.md`);
see `checkFields`:
> "for (val, (_, ty)) in vals.zip(sized_fields) {
>     self.check_value(val, ty)?;
> }" -/
def checkFieldsM {M : Type} [Memory M] [MemoryOps M] :
    List (Value M) → List (Offset × «Type») → (m : Option (Machine M) := none) → Interp Unit
  | val :: vals, (_, ty) :: fields, m => do
    checkValueM val ty m
    checkFieldsM vals fields m
  | _, _, _ => pure ()

/-- Polymorphic enum-variant check of `check_value` (`spec/lang/representation.md`);
see `checkVariant`:
> "let Some(variant) = variants.get(discriminant) else {
>     throw_ub!(\"Value::Variant: invalid discrimant\");
> };
> self.check_value(data, variant.ty)?;" -/
def checkVariantM {M : Type} [Memory M] [MemoryOps M] :
    List (Int × Variant) → Int → Value M → (m : Option (Machine M) := none) → Interp Unit
  | [], _, _, _ => ub "Value::Variant: invalid discrimant"
  | (d, ⟨ty, _⟩) :: rest, discriminant, data, m =>
    if d = discriminant then checkValueM data ty m else checkVariantM rest discriminant data m

end

/-- Polymorphic `Machine::typed_load` (`spec/lang/representation.md`); see `typedLoad`:
> "let bytes = self.mem.load(ptr, ty.layout::<M::T>().expect_size(..), align, atomicity)?;
>  ret(match ty.decode::<M>(bytes) {
>      Some(val) => { self.check_value(val, ty)?; val }
>      None => throw_ub!(\"load at type {ty:?} but the data in memory violates the language invariant\"),
>  })" -/
def typedLoadM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (ty : «Type») (align : Align)
    (atomicity : Atomicity) : Interp (Value M × Machine M) := do
  let size ← LayoutStrategy.expect_size (← Type.layout ty) "the callers ensure `ty` is sized"
  let (bytes, cm) ← ConcurrentMemory.load m.mem ptr size align atomicity
  let m := { m with mem := cm }
  match ← Type.decodeM (M := M) ty bytes with
  | some val => do checkValueM val ty (some m); pure (val, m)
  | none => ub "load at type but the data in memory violates the language invariant"

/-- Polymorphic `Machine::typed_store` (`spec/lang/representation.md`); see `typedStore`:
> "assert!(self.check_value(val, ty).is_ok(), ..);
>  let bytes = ty.encode::<M>(val);
>  self.mem.store(ptr, bytes, align, atomicity)?;" -/
def typedStoreM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (val : Value M) (ty : «Type») (align : Align)
    (atomicity : Atomicity) : Interp (Machine M) := do
  match checkValueM val ty (some m) with
  | .ok () => pure ()
  | .error _ => specPanic "trying to store a value which is ill-formed for its type"
  let bytes ← Type.encodeM ty val
  let cm ← ConcurrentMemory.store m.mem ptr bytes align atomicity
  pure { m with mem := cm }

/-- Polymorphic `Machine::transmute` (`spec/lang/representation.md`); see `transmute`:
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
def transmuteM {M : Type} [Memory M] [MemoryOps M] (val : Value M) (type1 type2 : «Type»)
    (m : Option (Machine M) := none) : Interp (Value M) := do
  let size1 ← LayoutStrategy.expect_size (← Type.layout type1) "WF ensures sized operands"
  let size2 ← LayoutStrategy.expect_size (← Type.layout type2) "WF ensures sized operands"
  if size1 ≠ size2 then specPanic "assertion failed: transmute between types of different size"
  else do
    let bytes ← Type.encodeM type1 val
    match ← Type.decodeM (M := M) type2 bytes with
    | some rawValue => do checkValueM rawValue type2 m; pure rawValue
    | none => ub "transmuted value is not valid at new type"

/-- Polymorphic `Machine::ptr_offset_inbounds` (`spec/lang/step/operators.md`);
see `ptrOffsetInbounds`:
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
def ptrOffsetInboundsM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (ptr : ThinPointer (Memory.Provenance M)) (offset : Int) :
    Interp (ThinPointer (Memory.Provenance M)) := do
  ConcurrentMemory.signed_dereferenceable m.mem ptr offset
  if !inBounds offset .Signed x86_64.PTR_SIZE then
    specPanic "assertion failed: offset.in_bounds(Signed, M::T::PTR_SIZE)"
  else if !inBounds (ptr.addr + offset) .Unsigned x86_64.PTR_SIZE then
    specPanic "assertion failed: (ptr.addr + offset).in_bounds(Unsigned, M::T::PTR_SIZE)"
  else
    pure { ptr with addr := ptr.addr + offset }

/-- Polymorphic `Machine::place_load` (`spec/lang/step/expressions.md`); see `placeLoad`:
> "if !place.aligned { throw_ub!(\"loading from a place based on a misaligned pointer\"); }
>  ret(self.typed_load(place.ptr.thin_pointer, ty, Align::ONE, Atomicity::None)?)" -/
def placeLoadM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (place : Place M)
    (ty : «Type») : Interp (Value M × Machine M) :=
  if !place.aligned then ub "loading from a place based on a misaligned pointer"
  else typedLoadM m place.ptr.thin_pointer ty ⟨1⟩ .None

/-- Polymorphic `Machine::place_store` (`spec/lang/step/statements.md`); see `placeStore`:
> "if !place.aligned { throw_ub!(\"storing to a place based on a misaligned pointer\"); }
>  self.typed_store(place.ptr.thin_pointer, val, ty, Align::ONE, Atomicity::None)?;" -/
def placeStoreM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (place : Place M)
    (val : Value M) (ty : «Type») : Interp (Machine M) :=
  if !place.aligned then ub "storing to a place based on a misaligned pointer"
  else typedStoreM m place.ptr.thin_pointer val ty ⟨1⟩ .None

/-- Polymorphic `Machine::eval_constant` (`spec/lang/step/expressions.md`); see `evalConstant`:
> "Constant::Int(i) => Value::Int(i),
>  Constant::Bool(b) => Value::Bool(b)," -/
def evalConstantM {M : Type} [Memory M] : Constant → Interp (Value M)
  | .Int i => pure (.Int i)
  | .Bool b => pure (.Bool b)
  | .PointerWithoutProvenance addr =>
    pure (.Ptr (ThinPointer.widen { addr := addr, provenance := none } none))
  | _ => unsupported "eval_constant for a global, function, or vtable pointer constant"

/-- Polymorphic `Machine::eval_cast_op` (`spec/lang/step/operators.md`); see `evalCastOp`:
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
def evalCastOpM {M : Type} [Memory M] [MemoryOps M] (castOp : CastOp)
    (arg : Value M × «Type») (m : Option (Machine M) := none) : Interp (Value M × «Type») :=
  match castOp, arg with
  | .IntToInt intTy, (.Int operand, _) =>
    pure (.Int (IntType.bring_in_bounds intTy operand), .Int intTy)
  | .IntToInt _, _ => specPanic "non-integer input to int-to-int cast"
  | .Transmute newTy, (operand, oldTy) => do
    let oldSize ← LayoutStrategy.expect_size (← Type.layout oldTy) "WF ensures transmutes are sized"
    let newSize ← LayoutStrategy.expect_size (← Type.layout newTy) "WF ensures transmutes are sized"
    if oldSize ≠ newSize then ub "transmute between types of different size"
    else do
      let val ← transmuteM operand oldTy newTy m
      pure (val, newTy)

/-- Polymorphic `Machine::eval_un_op` (`spec/lang/step/operators.md`); see `evalUnOp`:
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
def evalUnOpM {M : Type} [Memory M] [MemoryOps M] (op : UnOp) (arg : Value M × «Type»)
    (m : Option (Machine M) := none) : Interp (Value M × «Type») :=
  match op, arg with
  | .Int op, (.Int operand, .Int intTy) => do
    let retTy := match op with
      | .CountOnes => ⟨.Unsigned, ⟨4⟩⟩
      | _ => intTy
    let result : Value M := .Int (← evalIntUnOp op operand intTy)
    match checkValueM result (.Int retTy) m with
    | .ok () => pure (result, .Int retTy)
    | .error _ => specPanic "sanity check: result of UnOp::Int does not fit in the return type"
  | .Int _, _ => specPanic "non-integer input to integer operation"
  | .Cast castOp, arg => evalCastOpM castOp arg m
  | .GetThinPointer, (.Ptr ptr, _) => pure (.Ptr { ptr with metadata := none }, .Ptr (.Raw .None))
  | .GetThinPointer, _ => specPanic "non-pointer GetThinPointer"
  | _, _ => unsupported "eval_un_op for an operator outside UnOp::{Int, Cast, GetThinPointer}"

/-- Polymorphic `Machine::eval_rel_op` (`spec/lang/step/operators.md`); see `evalRelOp`:
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
> }" -/
def evalRelOpM {M : Type} [Memory M] (rel : RelOp) (ord : Ordering) : Value M × «Type» :=
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

/-- Polymorphic `Machine::compare_ptr` (`spec/lang/step/operators.md`); see `comparePtr`:
> "fn compare_ptr(left: Pointer<M::Provenance>, right: Pointer<M::Provenance>) -> std::cmp::Ordering {
>     let thin_cmp = left.thin_pointer.addr.cmp(&right.thin_pointer.addr);
>     let meta_cmp = match (left.metadata, right.metadata) {
>         (None, None) => std::cmp::Ordering::Equal,
>         (Some(PointerMeta::ElementCount(l)), Some(PointerMeta::ElementCount(r))) => l.cmp(&r),
>         (Some(PointerMeta::VTablePointer(l)), Some(PointerMeta::VTablePointer(r))) => l.addr.cmp(&r.addr),
>         _ => panic!(\"unmatching metadata in wide pointer comparasion\"),
>     };
>     // Lexicographically compare on first the thin pointer and then the metadata
>     thin_cmp.then(meta_cmp)
> }" -/
def comparePtrM {Provenance : Type} (left right : Pointer Provenance) : Interp Ordering := do
  let thinCmp := intCmp left.thin_pointer.addr right.thin_pointer.addr
  let metaCmp ← match left.metadata, right.metadata with
    | none, none => pure Ordering.eq
    | some (.ElementCount l), some (.ElementCount r) => pure (intCmp l r)
    | some (.VTablePointer l), some (.VTablePointer r) => pure (intCmp l.addr r.addr)
    | _, _ => specPanic "unmatching metadata in wide pointer comparasion"
  pure (thinCmp.then metaCmp)

/-- Polymorphic `Machine::eval_bin_op` (`spec/lang/step/operators.md`); see `evalBinOp`:
> "let Type::Int(int_ty) = l_ty else { panic!(\"non-integer input to integer operation\") };
>  let Value::Int(left) = left else { panic!(..) };
>  let Value::Int(right) = right else { panic!(..) };
>  // Perform the operation.
>  let result = Self::eval_int_bin_op(op, left, right, int_ty)?;
>  // Put the result into the right range (in case of overflow).
>  let result = int_ty.bring_in_bounds(result);
>  ret((Value::Int(result), Type::Int(int_ty)))" -/
def evalBinOpM {M : Type} [Memory M] (op : BinOp) (l r : Value M × «Type») :
    Interp (Value M × «Type») :=
  match op, l, r with
  | .Int op, (.Int left, .Int intTy), (.Int right, _) => do
    let result ← evalIntBinOp op left right intTy
    pure (.Int (IntType.bring_in_bounds intTy result), .Int intTy)
  | .Int _, _, _ => specPanic "non-integer input to integer operation"
  | .IntWithOverflow op, (.Int left, .Int intTy), (.Int right, _) => do
    let result := evalIntBinOpWithOverflow op left right
    let overflow := !IntType.can_represent intTy result
    let result := IntType.bring_in_bounds intTy result
    let value : Value M := .Tuple [.Int result, .Bool overflow]
    let ty ← IntType.with_overflow intTy
    pure (value, ty)
  | .IntWithOverflow _, _, _ => specPanic "non-integer input to integer operation"
  | .Rel relOp, (left, lTy), (right, _) =>
    match lTy, left, right with
    | .Int _, .Int left, .Int right => pure (evalRelOpM relOp (intCmp left right))
    | .Bool, .Bool left, .Bool right => pure (evalRelOpM relOp (boolCmp left right))
    | .Ptr _, .Ptr left, .Ptr right => do pure (evalRelOpM relOp (← comparePtrM left right))
    | _, _, _ => specPanic "relational operator on incomparable type or value-type mismatch"
  | _, _, _ => unsupported "eval_bin_op for an operator outside BinOp::Int, BinOp::IntWithOverflow, and BinOp::Rel"

/-- Polymorphic `Machine::ptr_offset_wrapping` (`spec/lang/step/operators.md`);
see `ptrOffsetWrapping`:
> "/// Perform a wrapping offset on the given pointer. (Can never fail.)
> fn ptr_offset_wrapping(&self, ptr: ThinPointer<M::Provenance>, offset: Int) -> ThinPointer<M::Provenance> {
>     ptr.wrapping_offset::<M::T>(offset)
> }" -/
def ptrOffsetWrappingM {Provenance : Type} (ptr : ThinPointer Provenance) (offset : Int) :
    ThinPointer Provenance :=
  ThinPointer.wrapping_offsetM ptr offset

/-- Polymorphic `Machine::eval_bin_op` for `BinOp::PtrOffset` (`spec/lang/step/operators.md`);
see `evalPtrOffset`:
> "fn eval_bin_op(
>     &self,
>     BinOp::PtrOffset { inbounds }: BinOp,
>     (left, l_ty): (Value<M>, Type),
>     (right, _r_ty): (Value<M>, Type)
> ) -> Result<(Value<M>, Type)> {
>     let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left else {
>         panic!(\"non-thin-pointer left input to `PtrOffset`\")
>     };
>     let Value::Int(right) = right else { panic!(\"non-integer right input to `PtrOffset`\") };
>
>     let offset_ptr = if inbounds {
>         self.ptr_offset_inbounds(left, right)?
>     } else {
>         self.ptr_offset_wrapping(left, right)
>     };
>     ret((Value::Ptr(offset_ptr.widen(None)), l_ty))
> }" -/
def evalPtrOffsetM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (inbounds : Bool)
    (l r : Value M × «Type») : Interp (Value M × «Type») :=
  match l, r with
  | (.Ptr ⟨left, none⟩, lTy), (.Int right, _) => do
    let offsetPtr ← if inbounds then ptrOffsetInboundsM m left right
      else pure (ptrOffsetWrappingM left right)
    pure (.Ptr (ThinPointer.widen offsetPtr none), lTy)
  | (.Ptr ⟨_, none⟩, _), _ => specPanic "non-integer right input to `PtrOffset`"
  | _, _ => specPanic "non-thin-pointer left input to `PtrOffset`"

/-- Polymorphic `Machine::eval_bin_op` for `BinOp::PtrOffsetFrom`
(`spec/lang/step/operators.md`); see `evalPtrOffsetFrom`:
> "fn eval_bin_op(
>     &self,
>     BinOp::PtrOffsetFrom { inbounds, nonneg }: BinOp,
>     (left, l_ty): (Value<M>, Type),
>     (right, _r_ty): (Value<M>, Type)
> ) -> Result<(Value<M>, Type)> {
>     let Value::Ptr(Pointer { thin_pointer: left, metadata: None }) = left else {
>         panic!(\"non-thin-pointer left input to `PtrOffsetFrom`\")
>     };
>     let Value::Ptr(Pointer { thin_pointer: right, metadata: None }) = right else {
>         panic!(\"non-thin-pointer right input to `PtrOffsetFrom`\")
>     };
>
>     let distance = left.addr - right.addr;
>     let distance = if inbounds {
>         // The \"gap\" between the two pointers must be dereferenceable from both of them.
>         // This check also ensures that the distance is inbounds of `isize`.
>         self.mem.signed_dereferenceable(left, -distance)?;
>         self.mem.signed_dereferenceable(right, distance)?;
>         // All checked!
>         distance
>     } else {
>         distance.bring_in_bounds(Signed, M::T::PTR_SIZE)
>     };
>
>     if nonneg && distance < Int::ZERO {
>         throw_ub!(\"PtrOffsetFrom: negative result with `nonneg` flag set\");
>     }
>
>     let isize_int = IntType { signed: Signed, size: M::T::PTR_SIZE };
>     ret((Value::Int(distance), Type::Int(isize_int)))
> }" -/
def evalPtrOffsetFromM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (inbounds nonneg : Bool) (l r : Value M × «Type») : Interp (Value M × «Type») :=
  match l, r with
  | (.Ptr ⟨left, none⟩, _), (.Ptr ⟨right, none⟩, _) => do
    let distance : Int := left.addr - right.addr
    let distance ← if inbounds then do
        ConcurrentMemory.signed_dereferenceable m.mem left (-distance)
        ConcurrentMemory.signed_dereferenceable m.mem right distance
        pure distance
      else pure (bringInBounds distance .Signed x86_64.PTR_SIZE)
    if nonneg && decide (distance < 0) then
      ub "PtrOffsetFrom: negative result with `nonneg` flag set"
    else
      pure (.Int distance, .Int ⟨.Signed, x86_64.PTR_SIZE⟩)
  | (.Ptr ⟨_, none⟩, _), _ => specPanic "non-thin-pointer right input to `PtrOffsetFrom`"
  | _, _ => specPanic "non-thin-pointer left input to `PtrOffsetFrom`"

mutual

/-- Polymorphic `Machine::eval_place` (`spec/lang/step/expressions.md`); see `evalPlace`:
> "let ty = self.cur_frame().func.locals[name];
>  let Some(ptr) = self.cur_frame().locals.get(name) else {
>      throw_ub!(\"access to a dead local\");
>  };
>  ret((Place { ptr: ptr.widen(None), aligned: true }, ty))" -/
def evalPlaceM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    PlaceExpr → Interp ((Place M × «Type») × Machine M)
  | .Local name => do
    let fr ← curFrameM m
    let ty ← mapIndex fr.func.locals name "self.cur_frame().func.locals[name]"
    match mapGet fr.locals name with
    | none => ub "access to a dead local"
    | some ptr => pure (({ ptr := ThinPointer.widen ptr none, aligned := true }, ty), m)
  | .Field root field => do
    let ((root, ty), m) ← evalPlaceM m root
    let (offset, fieldTy) ← match ty with
      | .Tuple sizedFields sizedHeadLayout unsizedField =>
        if 0 ≤ field ∧ field < (sizedFields.length : Int) then
          listIndex sizedFields field "sized_fields[field]"
        else if field = (sizedFields.length : Int) then
          match unsizedField with
          | none => specPanic "field projection to non-existing unsized tail"
          | some tailTy => do
            let tailAlign ← computeAlignM m (← Type.layout tailTy) root.ptr.metadata
            let offset := TupleHeadLayout.tail_offset sizedHeadLayout tailAlign
            pure (offset, tailTy)
        else
          specPanic "field projection to invalid field"
      | .Union fields _ _ _ => listIndex fields field "fields[field]"
      | _ => specPanic "field projection on non-projectable type"
    let rootSize ← computeSizeM m (← Type.layout ty) root.ptr.metadata
    if !(offset.bytes ≤ rootSize.bytes) then
      specPanic "assertion failed: offset <= self.compute_size(ty.layout::<M::T>(), root.ptr.metadata)"
    else do
      let ptr ← ptrOffsetInboundsM m root.ptr.thin_pointer (offset.bytes : Int)
      let ptr := if !LayoutStrategy.is_sized (← Type.layout fieldTy) then
          ThinPointer.widen ptr root.ptr.metadata
        else
          ThinPointer.widen ptr none
      pure (({ root with ptr := ptr }, fieldTy), m)
  | .Index root index => do
    let ((root, ty), m) ← evalPlaceM m root
    let ((idxVal, _), m) ← evalValueM m index
    let idx ← match idxVal with
      | .Int i => pure i
      | _ => specPanic "non-integer operand for array index"
    let (elemTy, count) ← match ty with
      | .Array elem count => pure (elem, count)
      | .Slice elem =>
        match root.ptr.metadata with
        | some (.ElementCount count) => pure (elem, count)
        | _ => specPanic "eval_place should always return a ptr which matches meta for the LayoutStrategy of ty"
      | _ => specPanic "index projection on non-indexable type"
    if idx < 0 ∨ idx ≥ count then
      ub "access to out-of-bounds index"
    else do
      let elemLayout ← Type.layout elemTy
      let elemSize ← LayoutStrategy.expect_size elemLayout "WF ensures array & slice elements are sized"
      let offset ← Size.mulInt elemSize idx
      let rootSize ← computeSizeM m (← Type.layout ty) root.ptr.metadata
      if offset.bytes ≤ rootSize.bytes then
        let ptr ← ptrOffsetInboundsM m root.ptr.thin_pointer (offset.bytes : Int)
        pure (({ root with ptr := ThinPointer.widen ptr none }, elemTy), m)
      else
        specPanic "sanity check: the indexed offset should not be outside what the type allows."
  | .Deref operand ty => do
    let ((v, vTy), m) ← evalValueM m operand
    match v, vTy with
    | .Ptr ptr, .Ptr ptrType => do
      match PtrType.safe_pointee ptrType with
      | some pointee => do
        let pointeeAlign ← computeAlignM m pointee.layout ptr.metadata
        if !Align.is_aligned pointeeAlign ptr.thin_pointer.addr then
          specPanic "assertion failed: self.compute_align(pointee.layout, ptr.metadata).is_aligned(ptr.thin_pointer.addr)"
        else do
          let pointeeSize ← computeSizeM m pointee.layout ptr.metadata
          ConcurrentMemory.dereferenceable m.mem ptr.thin_pointer pointeeSize
      | none => pure ()
      let align ← computeAlignM m (← Type.layout ty) ptr.metadata
      pure (({ ptr := ptr, aligned := Align.is_aligned align ptr.thin_pointer.addr }, ty), m)
    | _, _ => specPanic "dereferencing a non-pointer"
  | _ => unsupported "eval_place for a place expression other than Local, Deref, Field, or Index"

/-- Polymorphic `Machine::eval_value` (`spec/lang/step/expressions.md`), wiring
`ValueExpr::AddrOf` through `ConcurrentMemory.retag_ptr`:
> "let lookup = self.vtable_lookup();
> let ptr = self.mutate_cur_frame(|frame, mem| {
>     mem.retag_ptr(&mut frame.extra, place.ptr, ptr_ty, /* fn_entry */ false, /* fn_implicit_writes */ true, lookup)
> })?;" -/
def evalValueM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    ValueExpr → Interp ((Value M × «Type») × Machine M)
  | .Constant c ty => do pure ((← evalConstantM c, ty), m)
  | .Tuple exprs ty => do
    let (vals, m) ← evalValuesM m exprs
    pure ((.Tuple vals, ty), m)
  | .Load source => do
    let ((place, ty), m) ← evalPlaceM m source
    let (v, m) ← placeLoadM m place ty
    pure ((v, ty), m)
  | .AddrOf target ptrTy => do
    let ((place, _), m) ← evalPlaceM m target
    checkValueM (.Ptr place.ptr) (.Ptr ptrTy) (some m)
    let lookup := vtableLookupM m
    let (ptr, m) ← mutateCurFrameOutM m (fun fr cm => do
      let (ptr', cm', extra') ←
        ConcurrentMemory.retag_ptr cm fr.extra place.ptr ptrTy false true lookup
      pure (ptr', { fr with extra := extra' }, cm'))
    pure ((.Ptr ptr, .Ptr ptrTy), m)
  | .UnOp operator operand => do
    let (arg, m) ← evalValueM m operand
    pure (← evalUnOpM operator arg (some m), m)
  | .BinOp (.PtrOffset inbounds) left right => do
    let (l, m) ← evalValueM m left
    let (r, m) ← evalValueM m right
    pure (← evalPtrOffsetM m inbounds l r, m)
  | .BinOp (.PtrOffsetFrom inbounds nonneg) left right => do
    let (l, m) ← evalValueM m left
    let (r, m) ← evalValueM m right
    pure (← evalPtrOffsetFromM m inbounds nonneg l r, m)
  | .BinOp operator left right => do
    let (l, m) ← evalValueM m left
    let (r, m) ← evalValueM m right
    pure (← evalBinOpM operator l r, m)
  | _ => unsupported "eval_value for an expression outside the fragment"

/-- Polymorphic tuple-element loop of `Machine::eval_value` (`spec/lang/step/expressions.md`);
see `evalValues`:
> "let vals = exprs.try_map(|e| self.eval_value(e))?.map(|e| e.0);" -/
def evalValuesM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    List ValueExpr → Interp (List (Value M) × Machine M)
  | [] => pure ([], m)
  | e :: es => do
    let ((val, _), m) ← evalValueM m e
    let (vals, m) ← evalValuesM m es
    pure (val :: vals, m)

end

/-- Polymorphic `StackFrame::storage_dead` (`spec/lang/step/statements.md`);
see `storageDead`:
> "fn storage_dead(&mut self, mem: &mut ConcurrentMemory<M>, local: LocalName) -> NdResult {
>     let pointee_size = self.func.locals[local].layout::<M::T>().expect_size(\"WF ensures all locals are sized\");
>     let pointee_align = self.func.locals[local].layout::<M::T>().expect_align(\"WF ensures all locals are sized\");
>     if let Some(ptr) = self.locals.remove(local) {
>         mem.deallocate(ptr, AllocationKind::Stack, pointee_size, pointee_align)?;
>     }
>     ret(())
> }" -/
def storageDeadM {M : Type} [Memory M] [MemoryOps M] (fr : StackFrame M)
    (cm : ConcurrentMemory M) (local_ : LocalName) :
    Interp (StackFrame M × ConcurrentMemory M) := do
  let ty ← mapIndex fr.func.locals local_ "self.func.locals[local]"
  let layout ← Type.layout ty
  let size ← LayoutStrategy.expect_size layout "WF ensures all locals are sized"
  let align ← LayoutStrategy.expect_align layout "WF ensures all locals are sized"
  let (removed, locals) := mapRemove fr.locals local_
  let fr := { fr with locals := locals }
  match removed with
  | some ptr => do pure (fr, ← ConcurrentMemory.deallocate cm ptr .Stack size align)
  | none => pure (fr, cm)

/-- Polymorphic `StackFrame::storage_live` (`spec/lang/step/statements.md`);
see `storageLive`:
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
def storageLiveM {M : Type} [Memory M] [MemoryOps M] (fr : StackFrame M)
    (cm : ConcurrentMemory M) (local_ : LocalName) :
    Interp (StackFrame M × ConcurrentMemory M) := do
  let (fr2, cm2) ← storageDeadM fr cm local_
  let ty ← mapIndex fr2.func.locals local_ "self.func.locals[local]"
  let layout ← Type.layout ty
  let size ← LayoutStrategy.expect_size layout "WF ensures all locals are sized"
  let align ← LayoutStrategy.expect_align layout "WF ensures all locals are sized"
  let (ptr, cm3) ← ConcurrentMemory.allocate cm2 .Stack size align
  let locals := mapInsertMap fr2.locals local_ ptr
  pure ({ fr2 with locals := locals }, cm3)

mutual

/-- Polymorphic `Machine::retag_val` (`spec/lang/step/statements.md`), threading
`Machine<M>` through compound values and retagging pointers via `ConcurrentMemory.retag_ptr`:
> "(Value::Ptr(ptr), Type::Ptr(ptr_type)) => {
>     let lookup = self.vtable_lookup();
>     let val = self.mutate_cur_frame(|frame, mem| { mem.retag_ptr(&mut frame.extra, ptr, ptr_type, fn_entry, frame.func.implicit_writes, lookup) })?;
>     Value::Ptr(val)
> }" -/
def retagValM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (fnEntry : Bool) :
    Value M → «Type» → Interp (Value M × Machine M)
  | .Int i, _ => pure (.Int i, m)
  | .Bool b, _ => pure (.Bool b, m)
  | .Union chunks, _ => pure (.Union chunks, m)
  | .Ptr ptr, .Ptr ptrType => do
    let lookup := vtableLookupM m
    let (ptr', m) ← mutateCurFrameOutM m (fun fr cm => do
      let (ptr', cm', extra') ←
        ConcurrentMemory.retag_ptr cm fr.extra ptr ptrType fnEntry fr.func.implicit_writes lookup
      pure (ptr', { fr with extra := extra' }, cm'))
    pure (.Ptr ptr', m)
  | .Tuple vals, .Tuple sizedFields _ _ => do
    let (vals, m) ← retagTupleFieldsM m fnEntry vals sizedFields
    pure (.Tuple vals, m)
  | .Tuple vals, .Array elemTy _ => do
    let (vals, m) ← retagArrayElemsM m fnEntry elemTy vals
    pure (.Tuple vals, m)
  | .Variant discriminant data, .Enum variants _ _ _ _ => do
    let variant ← mapIndex variants discriminant "variants[discriminant]"
    let (data, m) ← retagValM m fnEntry data variant.ty
    pure (.Variant discriminant data, m)
  | _, .Int _ => specPanic "this value does not have that type"
  | _, .Bool => specPanic "this value does not have that type"
  | _, .Union _ _ _ _ => specPanic "this value does not have that type"
  | _, .Ptr _ => specPanic "this value does not have that type"
  | _, .Tuple _ _ _ => specPanic "this value does not have that type"
  | _, .Array _ _ => specPanic "this value does not have that type"
  | _, .Enum _ _ _ _ _ => specPanic "this value does not have that type"
  | _, .Slice _ => specPanic "this value does not have that type"
  | _, .TraitObject _ => specPanic "this value does not have that type"

/-- Polymorphic tuple-field loop of `Machine::retag_val` (`spec/lang/step/statements.md`);
see `retagTupleFields`:
> "vals.zip(sized_fields).try_map(|(val, (_offset, ty))| self.retag_val(val, ty, fn_entry))?" -/
def retagTupleFieldsM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (fnEntry : Bool) :
    List (Value M) → List (Offset × «Type») → Interp (List (Value M) × Machine M)
  | [], [] => pure ([], m)
  | val :: vals, (_, ty) :: fields => do
    let (v, m) ← retagValM m fnEntry val ty
    let (vs, m) ← retagTupleFieldsM m fnEntry vals fields
    pure (v :: vs, m)
  | _, _ => specPanic "List::zip: lists have different lengths"

/-- Polymorphic array-element loop of `Machine::retag_val` (`spec/lang/step/statements.md`):
> "vals.try_map(|val| self.retag_val(val, ty, fn_entry))?" -/
def retagArrayElemsM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (fnEntry : Bool)
    (elemTy : «Type») : List (Value M) → Interp (List (Value M) × Machine M)
  | [] => pure ([], m)
  | val :: vals => do
    let (v, m) ← retagValM m fnEntry val elemTy
    let (vs, m) ← retagArrayElemsM m fnEntry elemTy vals
    pure (v :: vs, m)

end

/-- Polymorphic `Machine::eval_statement` (`spec/lang/step/statements.md`);
see `evalStatement`:
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
> fn eval_statement(&mut self, Statement::Validate { place, fn_entry }: Statement) -> NdResult {
>     let (place, ty) = self.eval_place(place)?;
>
>     // WF ensures all valid expressions are sized, so we can invoke the load.
>     // This also ensures the value in the place satsifies the language invariant.
>     let val = self.place_load(place, ty)?;
>     let val = self.retag_val(val, ty, fn_entry)?;
>     self.place_store(place, val, ty)?;
>
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
def evalStatementM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    Statement → Interp (Machine M)
  | .Assign destination source => do
    let ((place, ty), m) ← evalPlaceM m destination
    let ((val, _), m) ← evalValueM m source
    placeStoreM m place val ty
  | .PlaceMention place => do
    let (_, m) ← evalPlaceM m place
    pure m
  | .Validate place fnEntry => do
    let ((p, ty), m) ← evalPlaceM m place
    let (val, m) ← placeLoadM m p ty
    let (val, m) ← retagValM m fnEntry val ty
    placeStoreM m p val ty
  | .StorageLive local_ =>
    tryMutateCurFrameM m (fun fr cm => storageLiveM fr cm local_)
  | .StorageDead local_ =>
    tryMutateCurFrameM m (fun fr cm => storageDeadM fr cm local_)
  | .Deinit place => do
    let ((p, ty), m) ← evalPlaceM m place
    if !p.aligned then ub "de-initializing a place based on a misaligned pointer"
    else do
      let layout ← Type.layout ty
      let size ← LayoutStrategy.expect_size layout "WF ensures deinits are sized"
      let cm ← ConcurrentMemory.deinit m.mem p.ptr.thin_pointer size ⟨1⟩
      pure { m with mem := cm }
  | _ => unsupported "eval_statement for a statement other than Assign/PlaceMention/Validate/StorageLive/StorageDead/Deinit"

/-- Polymorphic `IntPtrCast::expose` (`spec/mem/intptrcast.md`); see `IntPtrCast.expose`:
> "pub fn expose(&mut self, ptr: ThinPointer<Provenance>) {
>     if let Some(provenance) = ptr.provenance {
>         // Remember this provenance as having been exposed.
>         self.exposed.insert(provenance);
>     }
> }" -/
def IntPtrCast.exposeM {Provenance : Type} [DecidableEq Provenance]
    (ipc : IntPtrCast Provenance) (ptr : ThinPointer Provenance) : IntPtrCast Provenance :=
  match ptr.provenance with
  | some provenance => { exposed := setInsert ipc.exposed provenance }
  | none => ipc

/-- Polymorphic provenance resolution for `IntPtrCast::int2ptr` (`spec/mem/intptrcast.md`);
see `int2ptrProvenance`:
> "pub fn int2ptr(&self, addr: Int) -> NdResult<ThinPointer<Provenance>> {
>     // Predict a suitable provenance. It must be either `None` or already exposed.
>     let provenance = predict(|prov: Option<Provenance>| {
>         prov.map_or(
>             true, // `None` is always an option
>             |p| self.exposed.contains(p),
>         )
>     })?;
>
>     // Construct a pointer with that provenance.
>     ret(ThinPointer { addr, provenance })
> }" -/
def int2ptrProvenanceM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (addr : Int) :
    Interp (Option (Memory.Provenance M)) :=
  match m.intptrcast.exposed.elems with
  | [] => pure none
  | [p] => pure (some p)
  | _ =>
    match MemoryOps.exposedInBounds m.mem.memory m.intptrcast.exposed addr with
    | [p] => pure (some p)
    | [] =>
      unsupported "int2ptr: multiple exposed allocations and none contains the address (angelic choice)"
    | _ =>
      unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)"

/-- Polymorphic `IntPtrCast::int2ptr` (`spec/mem/intptrcast.md`); see `IntPtrCast.int2ptr`:
> "// Construct a pointer with that provenance.
> ret(ThinPointer { addr, provenance })" -/
def IntPtrCast.int2ptrM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) (addr : Int) :
    Interp (ThinPointer (Memory.Provenance M)) := do
  let provenance ← int2ptrProvenanceM m addr
  pure { addr := addr, provenance := provenance }

/-- Polymorphic `Machine::eval_intrinsic` (`spec/lang/step/intrinsics.md`);
see `evalIntrinsic`:
> "fn eval_intrinsic(&mut self,
>     IntrinsicOp::PointerExposeProvenance: IntrinsicOp,
>     arguments: List<(Value<M>, Type)>,
>     ret_ty: Type,
> ) -> NdResult<Value<M>> {
>     if arguments.len() != 1 {
>         throw_ub!(\"invalid number of arguments for `PointerExposeProvenance` intrinsic\");
>     }
>     let Value::Ptr(Pointer { thin_pointer: ptr, metadata: None }) = arguments[0].0 else {
>         throw_ub!(\"invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer\");
>     };
>     if ret_ty != Type::Int(IntType { signed: Unsigned, size: M::T::PTR_SIZE }) {
>         throw_ub!(\"invalid return type for `PointerExposeProvenance` intrinsic\")
>     }
>
>     self.intptrcast.expose(ptr);
>     ret(Value::Int(ptr.addr))
> }
>
> fn eval_intrinsic(&mut self,
>     IntrinsicOp::PointerWithExposedProvenance: IntrinsicOp,
>     arguments: List<(Value<M>, Type)>,
>     ret_ty: Type,
> ) -> NdResult<Value<M>> {
>     if arguments.len() != 1 {
>         throw_ub!(\"invalid number of arguments for `PointerWithExposedProvenance` intrinsic\");
>     }
>     let Value::Int(addr) = arguments[0].0 else {
>         throw_ub!(\"invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer\");
>     };
>     let Type::Ptr(ret_ptr_ty) = ret_ty else {
>         throw_ub!(\"invalid return type for `PointerWithExposedProvenance` intrinsic\");
>     };
>     if ret_ptr_ty.meta_kind() != PointerMetaKind::None {
>         throw_ub!(\"unsized pointee requested for `PointerWithExposedProvenance` intrinsic\");
>     }
>
>     let ptr = self.intptrcast.int2ptr(addr)?;
>     ret(Value::Ptr(ptr.widen(None)))
> }" -/
def evalIntrinsicM {M : Type} [Memory M] [MemoryOps M] (m : Machine M)
    (intrinsic : IntrinsicOp) (arguments : List (Value M × «Type»))
    (retTy : «Type») : Interp (Value M × Machine M) :=
  match intrinsic with
  | .PointerExposeProvenance =>
    if arguments.length ≠ 1 then
      ub "invalid number of arguments for `PointerExposeProvenance` intrinsic"
    else
      match arguments with
      | [(.Ptr ⟨ptr, none⟩, _)] =>
        match retTy with
        | .Int ⟨.Unsigned, ⟨8⟩⟩ =>
          pure (.Int ptr.addr, { m with intptrcast := IntPtrCast.exposeM m.intptrcast ptr })
        | _ => ub "invalid return type for `PointerExposeProvenance` intrinsic"
      | _ => ub "invalid argument for `PointerExposeProvenance` intrinsic: not a thin pointer"
  | .PointerWithExposedProvenance =>
    if arguments.length ≠ 1 then
      ub "invalid number of arguments for `PointerWithExposedProvenance` intrinsic"
    else
      match arguments with
      | [(.Int addr, _)] =>
        match retTy with
        | .Ptr retPtrTy =>
          if PtrType.meta_kind retPtrTy ≠ .None then
            ub "unsized pointee requested for `PointerWithExposedProvenance` intrinsic"
          else do
            let ptr ← IntPtrCast.int2ptrM m addr
            pure (.Ptr (ThinPointer.widen ptr none), m)
        | _ => ub "invalid return type for `PointerWithExposedProvenance` intrinsic"
      | _ => ub "invalid argument for `PointerWithExposedProvenance` intrinsic: not an integer"
  | _ => unsupported "eval_intrinsic for an intrinsic other than the pointer provenance intrinsics"

/-- Polymorphic argument loop of `Terminator::Intrinsic` (`spec/lang/step/terminators.md`);
see `evalArgs`:
> "let arguments = arguments.try_map(|arg| self.eval_value(arg))?;" -/
def evalArgsM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    List ValueExpr → Interp (List (Value M × «Type») × Machine M)
  | [] => pure ([], m)
  | e :: es => do
    let (arg, m) ← evalValueM m e
    let (args, m) ← evalArgsM m es
    pure (arg :: args, m)

/-- Polymorphic teardown loop of `Terminator::Return` (`spec/lang/step/terminators.md`);
see `deallocAll`:
> "while let Some(local) = frame.locals.keys().next() {
>      frame.storage_dead(&mut self.mem, local)?;
>  }" -/
def deallocAllM {M : Type} [Memory M] [MemoryOps M] :
    Nat → StackFrame M → ConcurrentMemory M → Interp (StackFrame M × ConcurrentMemory M)
  | fuel, fr, cm =>
    match fr.locals.entries with
    | [] => pure (fr, cm)
    | (local_, _) :: _ =>
      match fuel with
      | 0 => specPanic "teardown loop did not terminate"
      | fuel + 1 => do
        let (fr, cm) ← storageDeadM fr cm local_
        deallocAllM fuel fr cm

/-- Polymorphic `Machine::terminate_active_thread` (`spec/lang/step/terminators.md`);
see `terminateActiveThread`:
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
def terminateActiveThreadM {M : Type} [Memory M] (m : Machine M) : Interp (Machine M) := do
  let active := m.active_thread
  if active = 0 then ub "the start function must not return"
  else do
    let t ← activeThreadM m
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

/-- Polymorphic `Machine::eval_terminator` for `Terminator::Return`
(`spec/lang/step/terminators.md`), invoking `self.mem.end_call(frame.extra)?`
after local teardown:
> "// Inform the memory model that this call has ended.
> self.mem.end_call(frame.extra)?;" -/
def evalReturnM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) : Interp (Machine M) := do
  let t ← activeThreadM m
  let frame ← match t.stack.getLast? with
    | some f => pure f
    | none => specPanic "stack.pop().unwrap()"
  let threads ← listSet m.threads m.active_thread { t with stack := t.stack.dropLast } "pop"
  let m := { m with threads := threads }
  let calleeTy ← mapIndex frame.func.locals frame.func.ret "frame.func.locals[frame.func.ret]"
  let align ← LayoutStrategy.expect_align (← Type.layout calleeTy) "the return value is a local and thus sized"
  let retPtr ← mapIndex frame.locals frame.func.ret "frame.locals[frame.func.ret]"
  let (retVal, m) ← typedLoadM m retPtr calleeTy align .None
  let (frame, cm) ← deallocAllM frame.locals.entries.length frame m.mem
  let cm ← ConcurrentMemory.end_call cm frame.extra
  let m := { m with mem := cm }
  match frame.stack_pop_action with
  | .BottomOfStack => terminateActiveThreadM m
  | .BackToCaller nextBlock _ callerRetPtr => do
    let t ← activeThreadM m
    if t.stack.length = 0 then specPanic "assertion failed: self.active_thread().stack.len() > 0"
    else do
      let m ← typedStoreM m callerRetPtr retVal calleeTy align .None
      match nextBlock with
      | some nb => jumpToBlockM m nb
      | none => ub "return from a function where caller did not specify next block"

/-- Polymorphic `Machine::eval_terminator` (`spec/lang/step/terminators.md`);
see `evalTerminator`:
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
def evalTerminatorM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) :
    Terminator → Interp (Machine M)
  | .Goto blockName => jumpToBlockM m blockName
  | .Switch value cases fallback => do
    let ((v, _), m) ← evalValueM m value
    match v with
    | .Int i => jumpToBlockM m ((mapGet cases i).getD fallback)
    | _ => specPanic "switch on a non-integer"
  | .Unreachable => ub "reached unreachable code"
  | .Return => evalReturnM m
  | .Intrinsic intrinsic arguments retExpr nextBlock => do
    let ((retPlace, retTy), m) ← evalPlaceM m retExpr
    let (args, m) ← evalArgsM m arguments
    let (value, m) ← evalIntrinsicM m intrinsic args retTy
    let m ← placeStoreM m retPlace value retTy
    match nextBlock with
    | some nb => jumpToBlockM m nb
    | none => ub "return from an intrinsic where caller did not specify next block"
  | _ => unsupported "eval_terminator for a terminator other than Goto/Switch/Unreachable/Return/Intrinsic"

/-- Polymorphic `Machine::step` (`spec/lang/machine.md`); see `step`:
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
def stepM {M : Type} [Memory M] [MemoryOps M] (m : Machine M) : Interp (Machine M) := do
  if !(m.threads.any (fun t => decide (t.state = .Enabled))) then .error .deadlock
  else do
    let (prev, m) := resetDataRaceTrackingM m
    let tid ← pickActiveThreadM m
    let m := { m with active_thread := tid }
    let frame ← curFrameM m
    let block ← mapIndex frame.func.blocks frame.next_block "frame.func.blocks[frame.next_block]"
    let m ← if frame.next_stmt = (block.statements.length : Int) then
        evalTerminatorM m block.terminator
      else do
        let stmt ← listIndex block.statements frame.next_stmt "block.statements[frame.next_stmt]"
        let m ← evalStatementM m stmt
        mutateCurFrameM m (fun fr => { fr with next_stmt := fr.next_stmt + 1 })
    ConcurrentMemory.check_data_races m.mem m.active_thread prev
    pure m

/-- Run `stepM` up to `n` times, stopping early at the first `Stop` (`spec/lang/machine.md`):
> "pub fn step(&mut self) -> NdResult {" -/
def stepsM {M : Type} [Memory M] [MemoryOps M] : Nat → Machine M → Interp (Machine M)
  | 0, m => pure m
  | n + 1, m => do stepsM n (← stepM m)

/-- Single step of `Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`) (`spec/lang/machine.md`):
> "pub fn step(&mut self) -> NdResult {" -/
def stepTB (m : MachTB) : Interp MachTB := stepM m

/-- Run `stepTB` up to `n` times on `MachTB`, stopping early at the first `Stop` (`spec/lang/machine.md`):
> "pub fn step(&mut self) -> NdResult {" -/
def stepsTB (n : Nat) (m : MachTB) : Interp MachTB := stepsM n m

end MiniRustSpec.Interp
