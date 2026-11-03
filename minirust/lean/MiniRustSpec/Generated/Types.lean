/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.

GENERATED FILE -- DO NOT EDIT. Regenerate with
`cargo run -p anneal-minirust-gen -- generate`.

Shallow embedding of MiniRust data definitions (commit `d821c6e3`):
every `struct`, `enum`, and `type` alias becomes a Lean `structure`, `inductive`,
or `abbrev`; traits become classes of their associated types and trait impls
the matching instances. See `crates/anneal-minirust-gen/src/shallow.rs` for the
mapping rules and `minirust/coverage.json` for items that are not shallowly
embedded (with reasons).
-/

import MiniRustSpec.Meta.LibSpecr

namespace MiniRustSpec.Gen

open MiniRustSpec

/--
Shallow class: associated types only. Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:642` (MiniRust `d821c6e3`).
-/
class DefinedRelation (Self : Type) : Type 1 where

/--
Associated types of `impl DefinedRelation for List < T >`.

Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:705` (MiniRust `d821c6e3`).
-/
instance instDefinedRelationList {T : Type} [DefinedRelation T] : DefinedRelation (List T) := {}

/--
Associated types of `impl DefinedRelation for Option < T >`.

Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:738` (MiniRust `d821c6e3`).
-/
instance instDefinedRelationOption {T : Type} [DefinedRelation T] : DefinedRelation (Option T) := {}

/-- Source: `spec/lang/step/locks.md:14` (MiniRust `d821c6e3`). -/
abbrev LockId : Type := Int

/-- Source: `spec/lang/syntax.md:97` (MiniRust `d821c6e3`). -/
inductive IntUnOp : Type where
  /-- Negate an integer value arithmetically (`x` becomes `-x`). -/
  | Neg
  /-- Bitwise-invert an integer value -/
  | BitNot
  /-- Used for the intrinsic ˋctpopˋ. -/
  | CountOnes
deriving instance DecidableEq for IntUnOp

/-- Source: `spec/lang/syntax.md:136` (MiniRust `d821c6e3`). -/
inductive IntBinOp : Type where
  /-- Add two integer values. -/
  | Add
  /--
  Add two integer values.
  Throws UB on overflow.
  -/
  | AddUnchecked
  /-- Subtract two integer values. -/
  | Sub
  /--
  Subtract two integer values.
  Throws UB on overflow.
  -/
  | SubUnchecked
  /-- Multiply two integer values. -/
  | Mul
  /--
  Multiply two integer values.
  Throws UB on overflow.
  -/
  | MulUnchecked
  /--
  Divide two integer values.
  UB on division by zero and on `int::MIN / -1`.
  -/
  | Div
  /--
  Divide two integer values.
  UB on division by zero, on `int::MIN / -1`, and on a non-zero remainder.
  -/
  | DivExact
  /--
  Remainder of a division, the `%` operator.
  UB if the modulos (right operand) is zero and on `int::MIN % -1`.
  -/
  | Rem
  /-- Shift left `<<` -/
  | Shl
  /--
  Shift left `<<`
  Throws UB if right operand not in range 0..left::BITS.
  -/
  | ShlUnchecked
  /-- Shift right `>>` (logical shift for unsigned integers, arithmetic shift for signed integers) -/
  | Shr
  /--
  Shift right `>>` (logical shift for unsigned integers, arithmetic shift for signed integers)
  Throws UB if right operand not in range 0..left::BITS.
  -/
  | ShrUnchecked
  /-- Bitwise-and two integer values. -/
  | BitAnd
  /-- Bitwise-or two integer values. -/
  | BitOr
  /-- Bitwise-xor two integer values. -/
  | BitXor
deriving instance DecidableEq for IntBinOp

/-- Source: `spec/lang/syntax.md:178` (MiniRust `d821c6e3`). -/
inductive IntBinOpWithOverflow : Type where
  /--
  Add two integer values, returns a tuple of the result integer
  and a bool indicating whether the calculation overflowed.
  -/
  | Add
  /--
  Subtract two integer values, returns a tuple of the result integer
  and a bool indicating whether the calculation overflowed.
  -/
  | Sub
  /--
  Multiply two integers, returns a tuple of the result integer
  and a bool indicating whether the calculation overflowed.
  -/
  | Mul
deriving instance DecidableEq for IntBinOpWithOverflow

/--
A relational operator indicates how two values are to be compared.
Unless noted otherwise, these all return a Boolean.

Source: `spec/lang/syntax.md:189` (MiniRust `d821c6e3`).
-/
inductive RelOp : Type where
  /-- less than -/
  | Lt
  /-- greater than -/
  | Gt
  /-- less than or equal -/
  | Le
  /-- greater than or equal -/
  | Ge
  /-- equal -/
  | Eq
  /-- inequal -/
  | Ne
  /--
  The three-way comparison; returns an i8:
  * -1 if left <  right
  *  0 if left == right
  * +1 if left >  right
  -/
  | Cmp
deriving instance DecidableEq for RelOp

/--
The `CallingConvention` defines how function arguments and return values are passed.

The assumption is that if caller and callee agree on the calling convention, and all arguments and the return types
pass `check_abi_compatibility`, then this implies they are ABI-compatible on real implementations.

Source: `spec/lang/syntax.md:398` (MiniRust `d821c6e3`).
-/
inductive CallingConvention : Type where
  | Rust
  | C
deriving instance DecidableEq for CallingConvention

/-- Source: `spec/lang/syntax.md:406` (MiniRust `d821c6e3`). -/
inductive IntrinsicLockOp : Type where
  | Acquire
  | Release
  | Create
deriving instance DecidableEq for IntrinsicLockOp

/--
The intrinsic operations supported by MiniRust.
Generally we only make things intrinsics if they cannot be operands, i.e.
they are non-deterministic or mutate the global state.
We also make them intrinsic if they return `()`, because an operand that
does not return anything is kind of odd.

Source: `spec/lang/syntax.md:412` (MiniRust `d821c6e3`).
-/
inductive IntrinsicOp : Type where
  | Abort
  | Assume
  | Exit
  | PrintStdout
  | PrintStderr
  | Allocate
  | Deallocate
  | Spawn
  | Join
  /--
  Determines whether the raw bytes pointed to by two pointers are equal.
  (Can't be an operand because it reads from memory.)
  -/
  | RawEq
  | AtomicStore
  | AtomicLoad
  | AtomicCompareExchange
  | AtomicFetchAndOp (_0 : IntBinOp)
  | Lock (_0 : IntrinsicLockOp)
  /--
  'Expose' the provenance a pointer so that it can later be cast to an integer.
  The address part of the pointer is stored in `destination`.
  -/
  | PointerExposeProvenance
  /-- Create a new pointer from the given address with some previously exposed provenance. -/
  | PointerWithExposedProvenance
  /-- Access the current unwinding payload. UB if not currently unwinding. -/
  | GetUnwindPayload
deriving instance DecidableEq for IntrinsicOp

/--
Opaque types of names for functions, vtables, trait methods, and globals.
The internal representations of these types do not matter.

Source: `spec/lang/syntax.md:450` (MiniRust `d821c6e3`).
-/
structure FnName : Type where
  _0 : LibSpecr.Name
deriving instance DecidableEq for FnName

/-- Source: `spec/lang/syntax.md:453` (MiniRust `d821c6e3`). -/
structure GlobalName : Type where
  _0 : LibSpecr.Name
deriving instance DecidableEq for GlobalName

/-- Source: `spec/lang/syntax.md:454` (MiniRust `d821c6e3`). -/
structure VTableName : Type where
  _0 : LibSpecr.Name
deriving instance DecidableEq for VTableName

/-- Source: `spec/lang/syntax.md:455` (MiniRust `d821c6e3`). -/
structure TraitMethodName : Type where
  _0 : LibSpecr.Name
deriving instance DecidableEq for TraitMethodName

/--
Opaque types of names for local variables and basic blocks.

Source: `spec/lang/syntax.md:471` (MiniRust `d821c6e3`).
-/
structure LocalName : Type where
  _0 : LibSpecr.Name
deriving instance DecidableEq for LocalName

/-- Source: `spec/lang/syntax.md:473` (MiniRust `d821c6e3`). -/
structure BbName : Type where
  _0 : LibSpecr.Name
deriving instance DecidableEq for BbName

/--
The kind of a basic block in the CFG.

Source: `spec/lang/syntax.md:502` (MiniRust `d821c6e3`).
-/
inductive BbKind : Type where
  /-- Regular blocks may use `Return` and `StartUnwind` but not `ResumeUnwind`. -/
  | Regular
  /-- Cleanup blocks may use `ResumeUnwind` but not `Return` or `StartUnwind`. -/
  | Cleanup
  /--
  Catch blocks may use neither `Return` nor `ResumeUnwind` nor `StartUnwind`. 
  Catch blocks may branch to regular blocks.
  -/
  | Catch
  /-- `Terminate` blocks may use neither `Return` nor `ResumeUnwind` nor `StartUnwind`. -/
  | Terminate
deriving instance DecidableEq for BbKind

/-- Source: `spec/lang/types.md:94` (MiniRust `d821c6e3`). -/
structure IntType : Type where
  signed : LibSpecr.Signedness
  size : LibSpecr.Size
deriving instance DecidableEq for IntType

/-- Source: `spec/mem/basic.md:18` (MiniRust `d821c6e3`). -/
structure AllocId : Type where
  _0 : Int
deriving instance DecidableEq for AllocId

/-- Source: `spec/mem/basic.md:20` (MiniRust `d821c6e3`). -/
abbrev Provenance (Extra : Type) : Type := (AllocId × Extra)

/--
The different kinds of atomicity.

Source: `spec/mem/concurrent.md:14` (MiniRust `d821c6e3`).
-/
inductive Atomicity : Type where
  /-- A sequentially consistent atomic access. -/
  | Atomic
  /-- A non-atomic memory access. -/
  | None
deriving instance DecidableEq for Atomicity

/--
Internal type used to track the type of a memory access.

Source: `spec/mem/concurrent.md:23` (MiniRust `d821c6e3`).
-/
inductive AccessType : Type where
  | Store
  | Load
deriving instance DecidableEq for AccessType

/--
The ID of a thread is an index into the machine's `threads` list.

Source: `spec/mem/concurrent.md:131` (MiniRust `d821c6e3`).
-/
abbrev ThreadId : Type := Int

/-- Source: `spec/lang/machine.md:112` (MiniRust `d821c6e3`). -/
inductive ThreadState : Type where
  /-- The thread is enabled and can get executed. -/
  | Enabled
  /-- The thread is trying to join another thread and is blocked until that thread finishes. -/
  | BlockedOnJoin (_0 : ThreadId)
  /-- The thread is waiting to acquire a lock. -/
  | BlockedOnLock (_0 : LockId)
  /-- The thread has terminated. -/
  | Terminated
deriving instance DecidableEq for ThreadState

/-- Source: `spec/lang/step/locks.md:9` (MiniRust `d821c6e3`). -/
inductive LockState : Type where
  | Unlocked
  | LockedBy (_0 : ThreadId)
deriving instance DecidableEq for LockState

/--
A one-byte provenance fragment stores the provenance and which position
in the pointer this fragment had.

Source: `spec/mem/interface.md:21` (MiniRust `d821c6e3`).
-/
structure ProvenanceFrag (Provenance : Type) : Type where
  provenance : Provenance
  position : Int
deriving instance DecidableEq for ProvenanceFrag

/-- Source: `spec/mem/interface.md:28` (MiniRust `d821c6e3`). -/
inductive AbstractByte (Provenance : Type) : Type where
  /-- An uninitialized byte. -/
  | Uninit
  /-- An initialized byte, optionally with some provenance (if it is encoding a pointer). -/
  | Init (_0 : UInt8) (_1 : (Option (ProvenanceFrag Provenance)))
deriving instance DecidableEq for AbstractByte

/--
Associated types of `impl DefinedRelation for AbstractByte < Provenance >`.

Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:652` (MiniRust `d821c6e3`).
-/
instance instDefinedRelationAbstractByte {Provenance : Type} : DefinedRelation (AbstractByte Provenance) := {}

/--
The "kind" of an allocation is used to distinguish, for instance, stack from heap memory.

Source: `spec/mem/interface.md:59` (MiniRust `d821c6e3`).
-/
inductive AllocationKind : Type where
  /-- Memory for a stack variable. -/
  | Stack
  /-- Memory allocated with the AM heap intrinsics. -/
  | Heap
  /-- Memory for a global variable. -/
  | Global
  /-- Memory for a function. -/
  | Function
  /-- Memory for a vtable. -/
  | VTable
deriving instance DecidableEq for AllocationKind

/--
*Note*: All memory operations can be non-deterministic, which means that
executing the same operation on the same memory can have different results.
We also let read operations potentially mutate memory (they actually can
change the current state in concurrent memory models and in Stacked Borrows).

Shallow class: associated types only. Omitted (deep embedding only): fn `new`, fn `allocate`, fn `deallocate`, fn `store`, fn `load`, fn `dereferenceable`, fn `signed_dereferenceable`, fn `retag_ptr`, fn `new_call`, fn `end_call`, fn `leak_check`.

Source: `spec/mem/interface.md:73` (MiniRust `d821c6e3`).
-/
class Memory (Self : Type) : Type 1 where
  /--
  The target information.
  This doesn't really belong to the memory, but avoids having to quantify over both
  memory and target everywhere.
  -/
  T : Type
  /-- The type of pointer provenance. -/
  Provenance : Type
  /-- Extra information for each stack frame. -/
  FrameExtra : Type
  /-- Parameters controlling memory model behavior, passed at construction time. -/
  Params : Type

/-- Source: `spec/mem/intptrcast.md:13` (MiniRust `d821c6e3`). -/
structure IntPtrCast (Provenance : Type) : Type where
  /-- The set of exposed provenance. -/
  exposed : (LibSpecr.Set Provenance)
deriving instance DecidableEq for IntPtrCast

/--
An "address" is a location in memory. This corresponds to the actual
location in the real program.
We make it a mathematical integer, but of course it is bounded by the size
of the address space.

Source: `spec/mem/pointer.md:22` (MiniRust `d821c6e3`).
-/
abbrev Address : Type := Int

/-- Source: `spec/mem/basic.md:26` (MiniRust `d821c6e3`). -/
structure Allocation (ProvExtra : Type := Unit) (AllocExtra : Type := Unit) : Type where
  /-- The data stored in this allocation. -/
  data : (List (AbstractByte (Provenance ProvExtra)))
  /--
  The address where this allocation starts.
  This is never 0, and `addr + data.len()` fits into a `usize`.
  -/
  addr : Address
  /--
  The alignment that was requested for this allocation.
  `addr` will be a multiple of this.
  -/
  align : LibSpecr.Align
  /-- The kind of this allocation. -/
  kind : AllocationKind
  /-- Whether this allocation is still live. -/
  live : Bool
  /-- Additional information needed for the memory model -/
  extra : AllocExtra
deriving instance DecidableEq for Allocation

/--
Access contains all information the data race detection needs about a single access.

Source: `spec/mem/concurrent.md:29` (MiniRust `d821c6e3`).
-/
structure Access : Type where
  ty : AccessType
  atomicity : Atomicity
  addr : Address
  len : LibSpecr.Size
deriving instance DecidableEq for Access

/-- Source: `spec/mem/concurrent.md:7` (MiniRust `d821c6e3`). -/
structure ConcurrentMemory (M : Type) [Memory M] : Type where
  memory : M
  /-- List of all memory access done by the active thread in the current step. -/
  accesses : (List Access)

/--
A "thin pointer" is an address together with its Provenance.
Provenance can be absent; those pointers are
invalid for all non-zero-sized accesses.

Source: `spec/mem/pointer.md:28` (MiniRust `d821c6e3`).
-/
structure ThinPointer (Provenance : Type) : Type where
  addr : Address
  provenance : (Option Provenance)
deriving instance DecidableEq for ThinPointer

/--
Defines the behavior when the function returns or resumes unwinding.

Source: `spec/lang/machine.md:77` (MiniRust `d821c6e3`).
-/
inductive StackPopAction (M : Type) [Memory M] : Type where
  /-- This is the bottom of the stack, there is nothing left to do in this thread. -/
  | BottomOfStack
  /-- Go back to the caller. -/
  | BackToCaller (next_block : (Option BbName)) (unwind_block : (Option BbName)) (ret_val_ptr : (ThinPointer (Memory.Provenance M)))

/--
Associated types of `impl DefinedRelation for ThinPointer < Provenance >`.

Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:674` (MiniRust `d821c6e3`).
-/
instance instDefinedRelationThinPointer {Provenance : Type} : DefinedRelation (ThinPointer Provenance) := {}

/--
The runtime metadata that can be stored in a wide pointer.

Source: `spec/mem/pointer.md:36` (MiniRust `d821c6e3`).
-/
inductive PointerMeta (Provenance : Type) : Type where
  /-- The metadata counts the number of elements in the slice. -/
  | ElementCount (_0 : Int)
  /--
  The metadata points to a vtable referred at this location.
  This must point to a valid vtable and it is a spec bug if it doesn't.
  -/
  | VTablePointer (_0 : (ThinPointer Provenance))
deriving instance DecidableEq for PointerMeta

/--
Associated types of `impl DefinedRelation for PointerMeta < Provenance >`.

Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:685` (MiniRust `d821c6e3`).
-/
instance instDefinedRelationPointerMeta {Provenance : Type} : DefinedRelation (PointerMeta Provenance) := {}

/--
A "pointer" is the thin pointer with optionally some metadata, making it a wide pointer.
This corresponds to the Rust raw pointer types, as well as references and boxes.

Source: `spec/mem/pointer.md:45` (MiniRust `d821c6e3`).
-/
structure Pointer (Provenance : Type) : Type where
  thin_pointer : (ThinPointer Provenance)
  metadata : (Option (PointerMeta Provenance))
deriving instance DecidableEq for Pointer

/--
Associated types of `impl DefinedRelation for Pointer < Provenance >`.

Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:694` (MiniRust `d821c6e3`).
-/
instance instDefinedRelationPointer {Provenance : Type} : DefinedRelation (Pointer Provenance) := {}

-- `Value` is self-recursive.
/-- Source: `spec/lang/values.md:7` (MiniRust `d821c6e3`). -/
inductive Value (M : Type) [Memory M] : Type where
  /-- A mathematical integer, used for `i*`/`u*` types. -/
  | Int (_0 : Int)
  /-- A Boolean value, used for `bool`. -/
  | Bool (_0 : Bool)
  /-- A pointer value, used for references and raw pointers. -/
  | Ptr (_0 : (Pointer (Memory.Provenance M)))
  /-- An n-tuple, used for arrays, structs, tuples (including unit). -/
  | Tuple (_0 : (List (Value M)))
  /-- A variant of a sum type, used for enums. -/
  | Variant (discriminant : Int) (data : (Value M))
  /-- Unions are represented as "lists of chunks", where each chunk is just a raw list of bytes. -/
  | Union (_0 : (List (List (AbstractByte (Memory.Provenance M)))))

/--
Associated types of `impl DefinedRelation for Value < M >`.

Omitted (deep embedding only): fn `le_defined`.

Source: `spec/lang/representation.md:715` (MiniRust `d821c6e3`).
-/
instance instDefinedRelationValue {M : Type} [Memory M] : DefinedRelation (Value M) := {}

/-- Source: `spec/lang/values.md:35` (MiniRust `d821c6e3`). -/
structure Place (M : Type) [Memory M] : Type where
  ptr : (Pointer (Memory.Provenance M))
  aligned : Bool

/--
A "trait name" is an identifier for the trait a vtable is for.
This depends on the defined methods and the marker traits.

Source: `spec/mem/pointer.md:141` (MiniRust `d821c6e3`).
-/
structure TraitName : Type where
  _0 : LibSpecr.Name
deriving instance DecidableEq for TraitName

/--
The statically known kind of metadata stored in a pointer.
This determines the type of the metadata, while `Option<PointerMeta>` determines its value.

Source: `spec/mem/pointer.md:145` (MiniRust `d821c6e3`).
-/
inductive PointerMetaKind : Type where
  | None
  | ElementCount
  | VTablePointer (_0 : TraitName)
deriving instance DecidableEq for PointerMetaKind

/--
The index of a child in the list of child nodes.

Source: `spec/mem/tree_borrows/memory.md:38` (MiniRust `d821c6e3`).
-/
abbrev ChildId : Type := Int

/--
A path from the root of a tree to some node inside the tree.

Source: `spec/mem/tree_borrows/memory.md:40` (MiniRust `d821c6e3`).
-/
abbrev Path : Type := (List ChildId)

/-- Source: `spec/mem/tree_borrows/memory.md:47` (MiniRust `d821c6e3`). -/
abbrev TreeBorrowsProvenance : Type := (AllocId × Path)

/--
Global parameters controlling Tree Borrows behavior.

Source: `spec/mem/tree_borrows/memory.md:53` (MiniRust `d821c6e3`).
-/
structure TreeBorrowsParams : Type where
  /-- Whether implicit writes are enabled or not. -/
  implicit_writes : Bool
deriving instance DecidableEq for TreeBorrowsParams

/-- Source: `spec/mem/tree_borrows/memory.md:67` (MiniRust `d821c6e3`). -/
structure TreeBorrowsFrameExtra : Type where
  /-- Our per-frame state is the list of nodes that are protected by this call. -/
  protectors : (List TreeBorrowsProvenance)
deriving instance DecidableEq for TreeBorrowsFrameExtra

/-- Source: `spec/mem/tree_borrows/state_machine_protected.md:7` (MiniRust `d821c6e3`). -/
inductive PermissionProt : Type where
  /-- Represents a shared reference to interior mutable data. -/
  | Cell
  /-- The various flavours of `Reserved` correspond to a protected/noalias node where no writes happened yet. -/
  | Reserved (had_local_read : Bool) (had_foreign_read : Bool)
  /-- Represents an activated (written to) mutable reference, i.e. it must actually be unique right now. -/
  | Unique
  /-- Represents a shared (immutable) reference. -/
  | Frozen (had_local_read : Bool)
  /-- Represents a reference that experienced a foreign write. It can not be used locally anymore. -/
  | Disabled
deriving instance DecidableEq for PermissionProt

/-- Source: `spec/mem/tree_borrows/state_machine_unprotected.md:6` (MiniRust `d821c6e3`). -/
inductive PermissionUnprot : Type where
  /-- Represents a shared reference to interior mutable data. -/
  | Cell
  /-- Represents a two-phase borrow during its reservation phase -/
  | Reserved
  /-- Represents a interior mutable two-phase borrow during its reservation phase -/
  | ReservedIm
  /-- Represents an activated (written to) mutable reference, i.e. it must actually be unique right now -/
  | Unique
  /-- Represents a shared (immutable) reference -/
  | Frozen
  /-- Represents a dead reference -/
  | Disabled
deriving instance DecidableEq for PermissionUnprot

/-- Source: `spec/mem/tree_borrows/state_machine.md:11` (MiniRust `d821c6e3`). -/
inductive Permission : Type where
  | Unprot (_0 : PermissionUnprot)
  | Prot (_0 : PermissionProt)
deriving instance DecidableEq for Permission

/-- Source: `spec/mem/tree_borrows/tree.md:14` (MiniRust `d821c6e3`). -/
inductive Protected : Type where
  | Strong
  | Weak
  | No
deriving instance DecidableEq for Protected

/-- Source: `spec/mem/tree_borrows/reborrow_settings.md:7` (MiniRust `d821c6e3`). -/
structure ReborrowSettings : Type where
  /--
  The permissions to set "inside" the data the reference points to (indexed
  related to the reference).
  -/
  inside : (List Permission)
  /-- The permission to set for the "outside" part. -/
  outside : Permission
  /-- Whether and which protector to set. -/
  «protected» : Protected
deriving instance DecidableEq for ReborrowSettings

-- `Node` is self-recursive.
/-- Source: `spec/mem/tree_borrows/tree.md:31` (MiniRust `d821c6e3`). -/
structure Node : Type where
  children : (List Node)
  /-- State for each location. -/
  permissions : (List Permission)
  /--
  Indicates whether the node is protected by a function call,
  i.e., whether the original reference passed as an argument of a function call.
  This will be some kind of protection (weak or strong) if and only if this node is in
  some frame's `extra.protectors` list.
  There is an invariant between this field and the `permissions`:
  If `protected.yes()`, then all states in `permissions` must be `Permission::Prot()`.
  If `!protected.yes()`, they must all be `Permission::Unprot()`.
  -/
  «protected» : Protected

/-- Source: `spec/mem/tree_borrows/memory.md:14` (MiniRust `d821c6e3`). -/
structure TreeBorrowsAllocationExtra : Type where
  root : Node

/-- Source: `spec/mem/tree_borrows/tree.md:51` (MiniRust `d821c6e3`). -/
inductive NodeRelation : Type where
  | Local
  | Foreign
deriving instance DecidableEq for NodeRelation

/-- Source: `spec/mem/tree_borrows/tree.md:60` (MiniRust `d821c6e3`). -/
inductive AccessKind : Type where
  | Read
  | Write
deriving instance DecidableEq for AccessKind

/--
When a non-negative integer is used as an offset into an allocation or type
rather than to describe the size of an object or type, use this type instead
of `Size` for extra clarity.

Source: `spec/prelude/main.md:12` (MiniRust `d821c6e3`).
-/
abbrev Offset : Type := LibSpecr.Size

/--
A pointer into a global allocation.

Source: `spec/lang/syntax.md:527` (MiniRust `d821c6e3`).
-/
structure Relocation : Type where
  /-- The name of the global allocation we are pointing into. -/
  name : GlobalName
  /-- The offset within that allocation. -/
  offset : Offset
deriving instance DecidableEq for Relocation

/--
Constants are basically values, but cannot have explicit provenance.
Currently we do not support Ptr and Union constants.

Source: `spec/lang/syntax.md:80` (MiniRust `d821c6e3`).
-/
inductive Constant : Type where
  /-- A mathematical integer, used for `i*`/`u*` types. -/
  | Int (_0 : Int)
  /-- A Boolean value, used for `bool`. -/
  | Bool (_0 : Bool)
  /-- A pointer pointing into a global allocation with a given offset. -/
  | GlobalPointer (_0 : Relocation)
  /-- A pointer pointing to a function. -/
  | FnPointer (_0 : FnName)
  /-- A pointer pointing to a vtable. -/
  | VTablePointer (_0 : VTableName)
  /-- A pointer with constant address, not pointing into any allocation. -/
  | PointerWithoutProvenance (_0 : Address)
deriving instance DecidableEq for Constant

/--
A global allocation.

Source: `spec/lang/syntax.md:515` (MiniRust `d821c6e3`).
-/
structure Global : Type where
  /-- The raw bytes of the allocation. `None` represents uninitialized bytes. -/
  bytes : (List (Option UInt8))
  /--
  Cross-references pointing to other global allocations,
  together with an offset, expressing where this allocation should put the pointer.
  Note that the pointers created due to relocations overwrite the data given by `bytes`.
  -/
  relocations : (List (Offset × Relocation))
  /-- The alignment with which this global shall be allocated. -/
  align : LibSpecr.Align
deriving instance DecidableEq for Global

/--
A vtable for a trait-type pair.
This is pointed to by the trait object metadata.

Source: `spec/lang/syntax.md:535` (MiniRust `d821c6e3`).
-/
structure VTable : Type where
  /--
  What trait this vtable is for.
  All vtables for this trait name have implementation for same set of methods.
  -/
  trait_name : TraitName
  /-- The size of the type. -/
  size : LibSpecr.Size
  /-- The alignment of the type. -/
  align : LibSpecr.Align
  /-- Offset and sizes of `UnsafeCell` in this vtable. -/
  cells : (List (Offset × LibSpecr.Size))
  /-- The implementations of trait methods. -/
  methods : (LibSpecr.Map TraitMethodName FnName)
deriving instance DecidableEq for VTable

-- `Discriminator` is self-recursive.
/--
The decision tree that computes the discriminant out of the tag for a specific
enum type.

Source: `spec/lang/types.md:111` (MiniRust `d821c6e3`).
-/
inductive Discriminator : Type where
  /-- We know the discriminant. -/
  | Known (_0 : Int)
  /-- Tag decoding failed, there is no valid discriminant. -/
  | Invalid
  /-- We don't know the discriminant, so we branch on the value of a specific value. -/
  | Branch (offset : Offset) (value_type : IntType) (fallback : Discriminator) (children : (LibSpecr.Map (Int × Int) Discriminator))

/--
Describes what is needed to define the layout of the sized head of a tuple `(head.., tail)`.

Source: `spec/mem/pointer.md:77` (MiniRust `d821c6e3`).
-/
structure TupleHeadLayout : Type where
  /--
  The offset where the head ends and tail starts.
  This is the end of the last sized field; it is *not* necessarily aligned to `align`.
  -/
  «end» : Offset
  /-- The alignment of the head. This is the maximal alignment of any sized field and capped to the packed alignment. -/
  align : LibSpecr.Align
  /--
  If this is `Some(a)` the alignment of the tail will be capped at this value.
  Must be `None` for sized tuples.
  -/
  packed_align : (Option LibSpecr.Align)
deriving instance DecidableEq for TupleHeadLayout

-- `LayoutStrategy` is self-recursive.
/--
Describes how the size and align of the value can be determined.

Source: `spec/mem/pointer.md:91` (MiniRust `d821c6e3`).
-/
inductive LayoutStrategy : Type where
  /-- The type is statically `Sized` with the given size and align. -/
  | Sized (_0 : LibSpecr.Size) (_1 : LibSpecr.Align)
  /--
  The type contains zero or more elements of the inner layout.
  The total size is a multiple of the element size and the align is exactly the element align.
  -/
  | Slice (_0 : LibSpecr.Size) (_1 : LibSpecr.Align)
  /--
  The size of the type must be looked up in the VTable of a wide pointer.
  Additionally, the vtable must be for the given trait.
  -/
  | TraitObject (_0 : TraitName)
  /-- The type consists of a sized head an unsized tail. -/
  | Tuple (head : TupleHeadLayout) (tail : LayoutStrategy)

-- `UnsafeCellStrategy` is self-recursive.
/--
Describes where in a potentially unsized type the UnsafeCell are.
Separate from `LayoutStrategy` since we must be able to compute `LayoutStrategy` from a
MiniRust `Type`, but that does not have enough information for an `UnsafeCellStrategy`.
FIXME: maybe it should?

Source: `spec/mem/pointer.md:109` (MiniRust `d821c6e3`).
-/
inductive UnsafeCellStrategy : Type where
  /-- List of offsets and sizes of `UnsafeCell`s. -/
  | Sized (cells : (List (Offset × LibSpecr.Size)))
  /--
  Since the elements of a slice have the same type, we only keep track of the
  UnsafeCell's of one element, we can then "repeat" this for the rest of the slice.
  -/
  | Slice (element_cells : (List (Offset × LibSpecr.Size)))
  /-- The bytes for UnsafeCell's must be looked up in the VTable. -/
  | TraitObject
  /-- A Tuple consists of a sized head an unsized tail. -/
  | Tuple (head_cells : (List (Offset × LibSpecr.Size))) (tail_cells : UnsafeCellStrategy)

/--
Describes what we know about data behind a pointer.

Source: `spec/mem/pointer.md:129` (MiniRust `d821c6e3`).
-/
structure PointeeInfo : Type where
  layout : LayoutStrategy
  inhabited : Bool
  /-- Indicates where the `UnsafeCell` in this type are, which permit interior mutability. -/
  unsafe_cells : UnsafeCellStrategy
  /--
  Whether the pointee implements the `Freeze` trait. This is used to determine
  whether the bytes "outside" the pointee have interior mutability.
  -/
  freeze : Bool
  unpin : Bool

/--
Stores all the information that we need to know about a pointer.

Source: `spec/mem/pointer.md:153` (MiniRust `d821c6e3`).
-/
inductive PtrType : Type where
  | Ref (mutbl : LibSpecr.Mutability) (pointee : PointeeInfo)
  | Box (pointee : PointeeInfo)
  | Raw (meta_kind : PointerMetaKind)
  | FnPtr
  /-- This is a "stand-alone" vtable pointer, something that does not exist in surface Rust. -/
  | VTablePtr (_0 : TraitName)

/-- Source: `spec/lang/syntax.md:211` (MiniRust `d821c6e3`). -/
inductive BinOp : Type where
  /-- An operation on integers (both must have the same type); returns an integer of the same type. -/
  | Int (_0 : IntBinOp)
  /--
  An operation on integers (both must have the same type); returns a tuple of integer of the same type
  and a boolean that is true if the result is not equal to the infinite-precision result.
  -/
  | IntWithOverflow (_0 : IntBinOpWithOverflow)
  /--
  Compares two values according to the given relational operator. Both must have the same type,
  and they must both be integers, Booleans, or pointers.
  -/
  | Rel (_0 : RelOp)
  /--
  Add a byte-offset to a pointer (with or without inbounds requirement).
  Takes a pointer as left operand and an integer as right operand;
  returns a pointer.
  FIXME: should we make this in units of the pointee size? The thing is, for
  raw pointers we do not have the pointee type...
  -/
  | PtrOffset (inbounds : Bool)
  /--
  Compute the distance between two pointers in bytes (with or without inbounds requirement).
  Takes two pointers; returns a signed pointer-sized integer.
  If `nonneg` is true, it is UB for the result to be negative.
  -/
  | PtrOffsetFrom (inbounds : Bool) (nonneg : Bool)
  /--
  This corresponds to `core::ptr::from_raw_parts`
  and takes a thin pointer and matching metadata to construct a pointer of the given type.
  When the target type is a thin pointer and the metadata is `()`, this is just a pointer cast.
  -/
  | ConstructWidePointer (_0 : PtrType)

-- Recursive group (emitted as one `mutual` block): `Type`, `Fields`, `Variant`.
-- Type aliases expanded inside this block (rule 4): `Fields`.
mutual

/--
The types of MiniRust.

Source: `spec/lang/types.md:20` (MiniRust `d821c6e3`).
-/
inductive «Type» : Type where
  | Int (_0 : IntType)
  | Bool
  /--
  `Ptr` represents all pointer types: references, raw pointers, boxes, function and vtable pointers.
  A pointer type does *not* need the full pointee type, since (de)serializing a pointer does not
  require knowledge about the pointee. We only track the metadata kind and basic pointee information
  like size and alignment that is required to check reference validity. This also means types have a finite
  representation even when the Rust type is recursive.
  -/
  | Ptr (_0 : PtrType)
  /-- "Tuple" is used for all heterogeneous types, i.e., both Rust tuples and structs. -/
  | Tuple (sized_fields : ((List (Offset × «Type»)))) (sized_head_layout : TupleHeadLayout) (unsized_field : (Option «Type»))
  | Array (elem : «Type») (count : Int)
  /--
  Slices, i.e. `[T]` are unsized types which therefore cannot be represented as values.
  This type is also used for strings: `str` are treated as `[u8]`.
  -/
  | Slice (elem : «Type»)
  | Union (fields : ((List (Offset × «Type»)))) (chunks : (List (Offset × LibSpecr.Size))) (size : LibSpecr.Size) (align : LibSpecr.Align)
  | Enum (variants : (LibSpecr.Map Int Variant)) (discriminant_ty : IntType) (discriminator : Discriminator) (size : LibSpecr.Size) (align : LibSpecr.Align)
  /-- A `dyn TraitName`. Commonly only used behind a pointer. -/
  | TraitObject (_0 : TraitName)

/-- Source: `spec/lang/types.md:101` (MiniRust `d821c6e3`). -/
structure Variant : Type where
  /-- The actual type of the variant. -/
  ty : «Type»
  /--
  The information on where to store which values to write the tag.
  MUST NOT touch any bytes written by the actual type of the variant and vice
  versa. This is because we allow references/pointers to (enum) fields which
  should be able to dereference without having to deal with the tag.
  -/
  tagger : (LibSpecr.Map Offset (IntType × Int))

end

/-- Source: `spec/lang/types.md:99` (MiniRust `d821c6e3`). -/
abbrev Fields : Type := (List (Offset × «Type»))

/-- Source: `spec/lang/syntax.md:105` (MiniRust `d821c6e3`). -/
inductive CastOp : Type where
  /-- Argument can be any integer type; returns the given integer type. -/
  | IntToInt (_0 : IntType)
  /--
  Transmute the value to a different type.
  The program is well-formed even if the output type has a different size than the
  input type, but the operation is UB in that case.
  -/
  | Transmute (_0 : «Type»)

/-- Source: `spec/lang/syntax.md:113` (MiniRust `d821c6e3`). -/
inductive UnOp : Type where
  /-- An operation on an integer; returns an integer of the same type. -/
  | Int (_0 : IntUnOp)
  /-- A form of cast; the return type is given by the specific cast operation. -/
  | Cast (_0 : CastOp)
  /-- Returns a raw pointer with same thin pointer as the operand, but without the metadata. -/
  | GetThinPointer
  /--
  Returns the metadata of a pointer as a value.
  The return type is given by `PointerMetaKind::ty()`, e.g., for a thin pointer this is `()`.
  -/
  | GetMetadata
  /--
  Returns the dynamic size of the type given the pointer metadata.
  The operand must be a matching metadata for the type. For sized types this is `()`.
  -/
  | ComputeSize (_0 : «Type»)
  /--
  Returns the dynamic alignment of the type given the pointer metadata.
  The operand must be a matching metadata for the type. For sized types this is `()`.
  -/
  | ComputeAlign (_0 : «Type»)
  /--
  Lookup the function pointer for a trait object method.
  The operand must be a pointer to a vtable as returned by `Constant::VTablePointer`.
  The parameter specifies which method of the vtable to look up.
  -/
  | VTableMethodLookup (_0 : TraitMethodName)

-- Recursive group (emitted as one `mutual` block): `ValueExpr`, `PlaceExpr`.
mutual

/--
A "value expression" evaluates to a `Value`.

Source: `spec/lang/syntax.md:16` (MiniRust `d821c6e3`).
-/
inductive ValueExpr : Type where
  /-- Just return a constant value. -/
  | Constant (_0 : Constant) (_1 : «Type»)
  /-- An n-tuple, used for arrays, structs, tuples (including unit). -/
  | Tuple (_0 : (List ValueExpr)) (_1 : «Type»)
  /-- A `Union` value. -/
  | Union (field : Int) (expr : ValueExpr) (union_ty : «Type»)
  /-- A variant of an enum type. -/
  | Variant (discriminant : Int) (data : ValueExpr) (enum_ty : «Type»)
  /--
  Read the discriminant of an enum type.
  As we don't need to know the validity of the inner data
  we don't fully load the variant value.
  -/
  | GetDiscriminant (place : PlaceExpr)
  /-- Load a value from memory. -/
  | Load (source : PlaceExpr)
  /-- Create a pointer (raw pointer or reference) to a place. -/
  | AddrOf (target : PlaceExpr) (ptr_ty : PtrType)
  /-- Unary operators. -/
  | UnOp (operator : UnOp) (operand : ValueExpr)
  /-- Binary operators. -/
  | BinOp (operator : BinOp) (left : ValueExpr) (right : ValueExpr)

/--
A "place expression" evaluates to a `Place`.

Source: `spec/lang/syntax.md:241` (MiniRust `d821c6e3`).
-/
inductive PlaceExpr : Type where
  /-- Denotes a local variable. -/
  | Local (_0 : LocalName)
  /-- Dereference a value (of pointer/reference type). -/
  | Deref (operand : ValueExpr) (ty : «Type»)
  /-- Project to a field. -/
  | Field (root : PlaceExpr) (field : Int)
  /-- Index to an array or slice element. -/
  | Index (root : PlaceExpr) (index : ValueExpr)
  /-- Enum variant downcast. -/
  | Downcast (root : PlaceExpr) (discriminant : Int)

end

/-- Source: `spec/lang/syntax.md:285` (MiniRust `d821c6e3`). -/
inductive Statement : Type where
  /-- Copy value from `source` to `destination`. -/
  | Assign (destination : PlaceExpr) (source : ValueExpr)
  /--
  Evaluate a place without accessing it.
  This is the result of translating e.g. `let _ = place;`.
  -/
  | PlaceMention (_0 : PlaceExpr)
  /-- Set the discriminant of the variant at `destination` to `value`. -/
  | SetDiscriminant (destination : PlaceExpr) (value : Int)
  /--
  Ensure that `place` contains a valid value of its type (else UB).
  Also perform retagging and ensure safe pointers are dereferenceable.

  The frontend is generally expected to generate this for all function argument,
  and possibly in more places.
  -/
  | Validate (place : PlaceExpr) (fn_entry : Bool)
  /-- De-initialize a place. -/
  | Deinit (place : PlaceExpr)
  /-- Allocate the backing store for this local. -/
  | StorageLive (_0 : LocalName)
  /-- Deallocate the backing store for this local. -/
  | StorageDead (_0 : LocalName)

/--
Function arguments can be passed by-value or in-place.

Source: `spec/lang/syntax.md:387` (MiniRust `d821c6e3`).
-/
inductive ArgumentExpr : Type where
  /--
  Pass a copy of this value to the function.

  Technically this could be encoded by generating a fresh temporary, copying the value there, and doing in-place passing.
  FIXME: is it worth providing this mode anyway?
  -/
  | ByValue (_0 : ValueExpr)
  /-- Pass the argument value in-place; the contents of this place may be altered arbitrarily by the callee. -/
  | InPlace (_0 : PlaceExpr)

/-- Source: `spec/lang/syntax.md:320` (MiniRust `d821c6e3`). -/
inductive Terminator : Type where
  /-- Just jump to the next block. -/
  | Goto (_0 : BbName)
  /--
  `value` needs to evaluate to a `Value::Int`.
  `cases` map those values to blocks to jump to and therefore have to have the equivalent type.
  If no value matches we fall back to the block given in `fallback`.
  -/
  | Switch (value : ValueExpr) (cases : (LibSpecr.Map Int BbName)) (fallback : BbName)
  /-- If this is ever executed, we have UB. -/
  | Unreachable
  /--
  Invoke the given intrinsic operation with the given arguments.

  Intrinsics are langauge primitives that can have arbitrary side-effects, including divergence.
  -/
  | Intrinsic (intrinsic : IntrinsicOp) (arguments : (List ValueExpr)) (ret : PlaceExpr) (next_block : (Option BbName))
  /-- Call the given function with the given arguments. -/
  | Call (callee : ValueExpr) (calling_convention : CallingConvention) (arguments : (List ArgumentExpr)) (ret : PlaceExpr) (next_block : (Option BbName)) (unwind_block : (Option BbName))
  /-- Return from the current function. -/
  | Return
  /-- Starts unwinding, jump to the indicated cleanup block. -/
  | StartUnwind (unwind_payload : ValueExpr) (unwind_block : BbName)
  /--
  Stops unwinding, jump to the indicated regular block.
  This also removes the topmost unwinding payload.
  UB if not currently unwinding.
  -/
  | StopUnwind (_0 : BbName)
  /-- Ends this function call. The unwinding should continue at the caller's stack frame. -/
  | ResumeUnwind

/--
A basic block is a sequence of statements followed by a terminator.

Source: `spec/lang/syntax.md:495` (MiniRust `d821c6e3`).
-/
structure BasicBlock : Type where
  statements : (List Statement)
  terminator : Terminator
  kind : BbKind

/--
A MiniRust function.

Source: `spec/lang/syntax.md:475` (MiniRust `d821c6e3`).
-/
structure Function : Type where
  /-- The locals of this function, and their type. -/
  locals : (LibSpecr.Map LocalName «Type»)
  /-- A list of locals that are initially filled with the function arguments. -/
  args : (List LocalName)
  /-- The name of a local that holds the return value when the function returns. -/
  ret : LocalName
  /-- The call calling convention of this function. -/
  calling_convention : CallingConvention
  /-- Associate each basic block name with the associated block. -/
  blocks : (LibSpecr.Map BbName BasicBlock)
  /-- The basic block where execution starts. -/
  start : BbName
  /-- Whether implicit writes are enabled for this function. -/
  implicit_writes : Bool

/--
The data that makes up a stack frame.

Source: `spec/lang/machine.md:54` (MiniRust `d821c6e3`).
-/
structure StackFrame (M : Type) [Memory M] : Type where
  /-- The function this stack frame belongs to. -/
  func : Function
  /-- For each live local, the location in memory where its value is stored. -/
  locals : (LibSpecr.Map LocalName (ThinPointer (Memory.Provenance M)))
  /-- Expresses what happens after the callee (this function) returns or resumes unwinding. -/
  stack_pop_action : (StackPopAction M)
  /--
  `next_block` and `next_stmt` describe the next statement/terminator to execute (the "program counter").
  `next_block` identifies the basic block,
  -/
  next_block : BbName
  /--
  If `next_stmt` is equal to the number of statements in this block (an
  out-of-bounds index in the statement list), it refers to the terminator.
  -/
  next_stmt : Int
  /-- The memory model is given the ability to track some extra per-frame data. -/
  extra : (Memory.FrameExtra M)

/-- Source: `spec/lang/machine.md:99` (MiniRust `d821c6e3`). -/
structure Thread (M : Type) [Memory M] : Type where
  /--
  The stack. This is only the "control" part of the stack; the "data" part
  lives in memory (and stack and memory are completely disjoint concepts
  in the Abstract Machine).
  -/
  stack : (List (StackFrame M))
  /-- Stores whether the thread is ready to run, blocked, or terminated. -/
  state : ThreadState
  /-- Stores the unwind payloads. -/
  unwind_payloads : (List (ThinPointer (Memory.Provenance M)))

/--
A closed MiniRust program.

Source: `spec/lang/syntax.md:457` (MiniRust `d821c6e3`).
-/
structure Program : Type where
  /-- Associate a function with each declared function name. -/
  functions : (LibSpecr.Map FnName Function)
  /-- The function where execution starts. -/
  start : FnName
  /-- Associate each global name with the associated global. -/
  globals : (LibSpecr.Map GlobalName Global)
  /-- Stores all traits and method names which are available for dynamic dispatch. -/
  traits : (LibSpecr.Map TraitName (LibSpecr.Set TraitMethodName))
  /-- Store the vtables with method tables and layout information. -/
  vtables : (LibSpecr.Map VTableName VTable)

/--
This type contains everything that needs to be tracked during the execution
of a MiniRust program.

Source: `spec/lang/machine.md:11` (MiniRust `d821c6e3`).
-/
structure Machine (M : Type) [Memory M] : Type where
  /-- The program we are executing. -/
  prog : Program
  /-- The contents of memory. -/
  mem : (ConcurrentMemory M)
  /-- The state of the integer-pointer cast subsystem. -/
  intptrcast : (IntPtrCast (Memory.Provenance M))
  /-- The threads (in particular, their stacks). -/
  threads : (List (Thread M))
  /-- The currently / most recently active thread. -/
  active_thread : ThreadId
  /--
  A set of threads that have been synchronized.
  A thread being added here in a given step means that if the very next step is
  by that thread, we do *not* do data race detection: there was synchronization
  between these two steps, so any potential accesses are not racing.
  -/
  synchronized_threads : (LibSpecr.Set ThreadId)
  /-- The Locks -/
  locks : (List LockState)
  /-- Stores a pointer to each of the global allocations, which are all `Sized`. -/
  global_ptrs : (LibSpecr.Map GlobalName (ThinPointer (Memory.Provenance M)))
  /-- Stores a pointer for each function name. -/
  fn_ptrs : (LibSpecr.Map FnName (ThinPointer (Memory.Provenance M)))
  /-- Stores a pointer for each vtable. -/
  vtable_ptrs : (LibSpecr.Map VTableName (ThinPointer (Memory.Provenance M)))
  /-- This is where the `PrintStdout` intrinsic writes to. -/
  stdout : LibSpecr.DynWrite
  /-- This is where the `PrintStderr` intrinsic writes to. -/
  stderr : LibSpecr.DynWrite

/-- Source: `spec/prelude/main.md:21` (MiniRust `d821c6e3`). -/
inductive TerminationInfo : Type where
  /-- The execution encountered undefined behaviour. -/
  | Ub (_0 : String)
  /-- The program was executed and the machine stopped without error. -/
  | MachineStop
  /-- The program terminated with a panic -/
  | Abort
  /-- The program was ill-formed. -/
  | IllFormed (_0 : String)
  /-- The program did not terminate but no thread can make progress. -/
  | Deadlock
  /-- The program terminated successfully but memory was leaked. -/
  | MemoryLeak
deriving instance DecidableEq for TerminationInfo

/--
All operations are fallible, so they return `Result`.  If they fail, that
means the program caused UB or put the machine to a halt.

Source: `spec/prelude/main.md:17` (MiniRust `d821c6e3`).
-/
abbrev Result (T : Type := Unit) : Type := (Except TerminationInfo T)

/--
Shallow class: associated types only. Omitted (deep embedding only): const `PTR_SIZE`, const `PTR_ALIGN`, const `INT_MAX_ALIGN`, const `ENDIANNESS`, const `MAX_ATOMIC_SIZE`, fn `valid_size`.

Source: `spec/prelude/target.md:9` (MiniRust `d821c6e3`).
-/
class Target (Self : Type) : Type 1 where

/-- Source: `spec/mem/basic.md:47` (MiniRust `d821c6e3`). -/
structure BasicMemory (T : Type) [Target T] (ProvExtra : Type := Unit) (AllocExtra : Type := Unit) : Type where
  allocations : (List (Allocation ProvExtra AllocExtra))
  _phantom : (LibSpecr.PhantomData T)

/--
Associated types of `impl Memory for BasicMemory < T >`.

Omitted (deep embedding only): fn `new`, fn `allocate`, fn `deallocate`, fn `store`, fn `load`, fn `dereferenceable`, fn `new_call`, fn `leak_check`.

Source: `spec/mem/basic.md:305` (MiniRust `d821c6e3`).
-/
instance instMemoryBasicMemory {T : Type} [Target T] : Memory (BasicMemory T Unit Unit) where
  Provenance := (Provenance Unit)
  T := T
  FrameExtra := Unit
  Params := Unit

/-- Source: `spec/mem/tree_borrows/memory.md:62` (MiniRust `d821c6e3`). -/
structure TreeBorrowsMemory (T : Type) [Target T] : Type where
  params : TreeBorrowsParams
  mem : (BasicMemory T Path TreeBorrowsAllocationExtra)

/--
Associated types of `impl Memory for TreeBorrowsMemory < T >`.

Omitted (deep embedding only): fn `new`, fn `allocate`, fn `deallocate`, fn `load`, fn `store`, fn `dereferenceable`, fn `retag_ptr`, fn `new_call`, fn `end_call`, fn `leak_check`.

Source: `spec/mem/tree_borrows/memory.md:184` (MiniRust `d821c6e3`).
-/
instance instMemoryTreeBorrowsMemory {T : Type} [Target T] : Memory (TreeBorrowsMemory T) where
  Provenance := TreeBorrowsProvenance
  FrameExtra := TreeBorrowsFrameExtra
  T := T
  Params := TreeBorrowsParams

/-- Source: `spec/prelude/target.md:32` (MiniRust `d821c6e3`). -/
structure x86_64 : Type where
deriving instance DecidableEq for x86_64

/--
Associated types of `impl Target for x86_64`.

Omitted (deep embedding only): const `PTR_SIZE`, const `PTR_ALIGN`, const `INT_MAX_ALIGN`, const `ENDIANNESS`, const `MAX_ATOMIC_SIZE`, fn `valid_size`.

Source: `spec/prelude/target.md:35` (MiniRust `d821c6e3`).
-/
instance instTargetx86_64 : Target x86_64 := {}

end MiniRustSpec.Gen
