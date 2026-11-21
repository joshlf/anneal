/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.Translate
import Trusted.MirSemantics
import Trusted.VerificationResult

/-!
# Volatile and unaligned raw-pointer intrinsics: Trusted MIR semantics and MiniRust

`Trusted.Rustc.V2026_06_01.MirSemantics` (`Terminators.lean`) gives an operational semantics to
the seven volatile memory intrinsics `core::intrinsics::{unaligned_volatile_load,
unaligned_volatile_store, volatile_load, volatile_store, volatile_copy_nonoverlapping_memory,
volatile_copy_memory, volatile_set_memory}` (`evalVolatileMemIntrinsicCall`) and to the four
unlinked helpers `core::ptr::{read_unaligned, write_unaligned, read_volatile, write_volatile}`
(`evalUnlinkedPtrAccessCall?`). This module relates that semantics to MiniRust's typed and
byte-level memory model, for both `Mach = Machine<BasicMemory<x86_64>>` and
`MachTB = Machine<TreeBorrowsMemory<x86_64>>`.

## The MiniRust-side model

MiniRust has no notion of a volatile access and no `memcpy` / `memset` intrinsic, so the
MiniRust side of every statement is one of the following definitions (Section 0), each stated
once per memory:

* `unaligned_volatile_load`, `read_unaligned`: `mrLoad false`, a `typedLoad` at `Align ⟨1⟩`.
* `unaligned_volatile_store`, `write_unaligned`: `mrStore false`, a `typedStore` at `Align ⟨1⟩`.
* `volatile_load`, `read_volatile`: `mrLoad true`, a `typedLoad` at `align_of::<T>()`.
* `volatile_store`, `write_volatile`: `mrStore true`, a `typedStore` at `align_of::<T>()`.
* `volatile_copy_memory(dst, src, count)`: `mrCopy`, a `load` of `count * size_of::<T>()` bytes
  at `src` (a snapshot) followed by a `store` of those bytes at `dst`, both at
  `align_of::<T>()`.
* `volatile_copy_nonoverlapping_memory(dst, src, count)`: `mrCopy` under the precondition
  `mrRangesOverlap dst src (count * size_of::<T>()) = false`.
* `volatile_set_memory(dst, val, count)`: `mrSet`, a `store` of `count * size_of::<T>()` copies
  of `AbstractByte::Init(val, None)` at `dst` at `align_of::<T>()`.

`mrLoadTB`, `mrStoreTB`, `mrCopyTB` and `mrSetTB` are the same definitions over
`typedLoadM` / `typedStoreM` / `ConcurrentMemory.load` / `ConcurrentMemory.store` at
`M := TreeBorrowsMemory x86_64`.

On the Trusted side, `trustedVolatileAction kind` and `trustedUnlinkedAction` (Section 3) name
the `RawPtrCallAction` that `evalVolatileMemIntrinsicCall` / `evalUnlinkedPtrAccessCall?` hand
to `finishRawPtrCallAction` (`trustedVolatileAction_spec`, `trustedUnlinkedAction_spec`), so a
statement about these actions is a statement about the terminator step.

## Value and data correspondence

* Integers: a Trusted `Value.scalar ⟨bits, w⟩` at MIR integer type `t` corresponds to MiniRust
  `Value::Int (intFromBits bits it)` with `it = intTypeOf t` (`Translate.lean`), and both are
  represented by the little-endian bytes `leBytes bits w`.
* Memory: the lockstep fixtures are functions of one byte list `bs`. The Trusted `[u8; 8]`
  local holds `vbU8s bs`, and the MiniRust allocation holds `vbPlain bs`; a Trusted pointer
  `(tag, offset)` corresponds to the MiniRust address `base + offset` with the allocation's
  provenance.
* Pointers: Trusted pointer bytes carry the allocation-relative offset and `(allocId, tag)`;
  MiniRust pointer bytes carry the absolute address and one provenance fragment per byte.

## What is proved

1. **Alignment first** (Sections 1 and 4). MiniRust `load` / `store` on both memories, the typed
   forms and the four models report UB on a misaligned address before any other check, for
   every length (including `0`), provenance and allocation state. Trusted reports `.fault .ub`
   whenever `rawPtrTargetAligned?` answers `some false`, also for a zero-sized element and for
   `count = 0`, and the unaligned forms never consult alignment. On a shared address both
   sides agree symbolically (`volatile_{load,store,copy,set}_misaligned_parity`), and concrete
   lockstep witnesses cover `count = 0` and a zero-sized element type.
2. **Byte codec and bit validity** (Sections 8 and 10). Symbolic decode agreement, encode
   agreement and round trip at the integer types of width 1, 2, 4, 8 and 16 bytes (and at
   `usize` / `isize` on the 64-bit fixture table); `bool` validity for every byte value;
   uninitialised bytes; pointers with provenance; `NonZero`; `char`; and the uninhabited `!`.
3. **In-allocation unaligned accesses** (Sections 5 and 11). Lockstep at every byte offset of a
   `[u8; 8]` allocation, and UB agreement for out-of-bounds, dead allocation, null pointer,
   uninitialised bytes and Tree Borrows permission conflicts.
4. **Copy and set** (Sections 6, 9 and 11). `(dst, src, count)` argument order; the MiniRust
   model is a `memmove` for every overlap (`mr_copy_is_memmove`); lockstep against Trusted for
   every in-bounds `(dst, src, count)` on the fixture; overlap of the non-overlapping variant
   is UB exactly where `mrRangesOverlap` holds; `volatile_set_memory` is a repeated-byte fill.
5. **Aligned addresses outside all allocations** (Section 7). An aligned provenance-less
   non-zero-sized volatile load or store is `.fault .unsupported` in Trusted, the step is
   `MirStepNode.unsupported`, and `MirNoUBTree` fails; MiniRust reports UB for the same access.
   Trusted therefore never claims such an access is defined, and never claims it is UB.

## Divergences

Each of the following is stated and proved rather than hidden:

* **Placement of an allocation** (`placement_dependent_alignment_witness`). Trusted has no
  concrete addresses and requires alignment in every placement of the allocation, so a pointer
  into an `align(1)` local is misaligned for `u32` at every offset. MiniRust checks the
  concrete address, so the same access is UB at one admissible base address and defined at
  another.
* **Zero-sized access through a null pointer** (`divergence_null_zst_read_write_unaligned`).
  Trusted applies the documented contract of `read_unaligned` / `write_unaligned` ("a null
  pointer is never valid") and reports `.ub`; MiniRust accepts every zero-sized access. The
  volatile intrinsics accept the null pointer on both sides.
* **Fail-closed classification.** Where Trusted cannot decide, it reports `.unsupported`, and
  MiniRust reports either UB (`NonZero` loaded through bytes, `lockstep_nonzero_validity`;
  aligned addresses outside all allocations, Section 7) or a defined result (pointer bytes
  read at an integer type lose their provenance, `lockstep_pointer_bytes_provenance`).
* **`char`** (`lockstep_char_validity`). MiniRust has no `char` type and `translateTy` rejects
  it; the validity invariant of `char` corresponds to a MiniRust enum whose discriminator
  branches on the 4-byte value (`vbMrChar`), while at MiniRust's plain `u32` a surrogate is an
  ordinary integer.
* **Storing at `!`** (`lockstep_never_uninhabited`). Trusted reports `.ub`; MiniRust has no
  value of the empty enum, so every `typedStore` at that type is a specification panic.
* **`typedStore` checks the value first.** MiniRust's `typedStore` panics on an ill-formed
  value before it reaches `store`, so the alignment theorems for stores assume
  `checkValue` and `Type.encode` succeed.

## Proof method

Symbolic theorems are proved by unfolding and rewriting. Concrete witnesses on the Trusted side
and MiniRust error results are closed by `rfl`. MiniRust success results carry a machine whose
type has no decidable equality, so they are observed through small decidable projections
(`loadedInt`, `storedBytes`, `decodedInt?`, ...) and decided by kernel reduction
(`decide +kernel`); each projection has a soundness lemma (`loadedInt_sound`, ...) that turns
the observation back into an equation on the result.
-/

namespace MiniRustSpec.Correspondence.VolatileBridge

-- `DecidableEq` of the observation types (`Option (Int × List (List (AbstractByte _)))`, ...)
-- is derived through several structure instances and exceeds the default instance size.
set_option synthInstance.maxSize 1024

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirSemantics
open MiniRustSpec

/-! ## 0. The MiniRust-side model -/

/-- The alignment a raw-pointer access of `ty` is performed at: `align_of::<T>()`
(`Type.layout`) when the access requires alignment, and `1` otherwise. -/
def mrAccessAlign (requiresAlign : Bool) (ty : Gen.«Type») : Interp.Interp LibSpecr.Align :=
  match requiresAlign with
  | true => do
    Interp.LayoutStrategy.expect_align (← Interp.Type.layout ty) "volatile access of a sized type"
  | false => pure ⟨1⟩

/-- MiniRust model on `Mach` of a typed raw-pointer load: `typedLoad` at `mrAccessAlign`
(`requiresAlign = false`: `unaligned_volatile_load`, `read_unaligned`; `true`: `volatile_load`,
`read_volatile`). -/
def mrLoad (requiresAlign : Bool) (m : Interp.Mach) (ptr : Interp.Ptr) (ty : Gen.«Type») :
    Interp.Interp (Interp.Val × Interp.Mach) := do
  let align ← mrAccessAlign requiresAlign ty
  Interp.typedLoad m ptr ty align .None

/-- `mrLoad` on `MachTB`: `typedLoadM` at `M := TreeBorrowsMemory x86_64`. -/
def mrLoadTB (requiresAlign : Bool) (m : Interp.MachTB)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (ty : Gen.«Type») :
    Interp.Interp (Gen.Value Interp.TBM × Interp.MachTB) := do
  let align ← mrAccessAlign requiresAlign ty
  Interp.typedLoadM m ptr ty align .None

/-- MiniRust model on `Mach` of a typed raw-pointer store: `typedStore` at `mrAccessAlign`
(`requiresAlign = false`: `unaligned_volatile_store`, `write_unaligned`; `true`:
`volatile_store`, `write_volatile`). -/
def mrStore (requiresAlign : Bool) (m : Interp.Mach) (ptr : Interp.Ptr) (val : Interp.Val)
    (ty : Gen.«Type») : Interp.Interp Interp.Mach := do
  let align ← mrAccessAlign requiresAlign ty
  Interp.typedStore m ptr val ty align .None

/-- `mrStore` on `MachTB`: `typedStoreM` at `M := TreeBorrowsMemory x86_64`. -/
def mrStoreTB (requiresAlign : Bool) (m : Interp.MachTB)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (val : Gen.Value Interp.TBM)
    (ty : Gen.«Type») : Interp.Interp Interp.MachTB := do
  let align ← mrAccessAlign requiresAlign ty
  Interp.typedStoreM m ptr val ty align .None

/-- MiniRust model on `Mach` of `volatile_copy_memory::<T>(dst, src, count)`: `load` of
`count * size_of::<T>()` bytes at `src`, then `store` of those bytes at `dst`, both at
`align_of::<T>()`. The loaded bytes are a snapshot, so overlapping ranges behave as `memmove`. -/
def mrCopy (m : Interp.Mach) (dst src : Interp.Ptr) (count : Nat) (ty : Gen.«Type») :
    Interp.Interp Interp.Mach := do
  let layout ← Interp.Type.layout ty
  let size ← Interp.LayoutStrategy.expect_size layout "volatile copy of a sized type"
  let align ← Interp.LayoutStrategy.expect_align layout "volatile copy of a sized type"
  let (bytes, cm) ← Interp.CM.load m.mem src ⟨count * size.bytes⟩ align .None
  let cm' ← Interp.CM.store cm dst bytes align .None
  pure { m with mem := cm' }

/-- `mrCopy` on `MachTB`: `ConcurrentMemory.load` then `ConcurrentMemory.store` at
`M := TreeBorrowsMemory x86_64`. -/
def mrCopyTB (m : Interp.MachTB) (dst src : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (count : Nat) (ty : Gen.«Type») : Interp.Interp Interp.MachTB := do
  let layout ← Interp.Type.layout ty
  let size ← Interp.LayoutStrategy.expect_size layout "volatile copy of a sized type"
  let align ← Interp.LayoutStrategy.expect_align layout "volatile copy of a sized type"
  let (bytes, cm) ← Interp.ConcurrentMemory.load m.mem src ⟨count * size.bytes⟩ align .None
  let cm' ← Interp.ConcurrentMemory.store cm dst bytes align .None
  pure { m with mem := cm' }

/-- MiniRust model on `Mach` of `volatile_set_memory::<T>(dst, val, count)`: `store` of
`count * size_of::<T>()` copies of `AbstractByte::Init(val, None)` at `dst` at `align_of::<T>()`. -/
def mrSet (m : Interp.Mach) (dst : Interp.Ptr) (val : UInt8) (count : Nat) (ty : Gen.«Type») :
    Interp.Interp Interp.Mach := do
  let layout ← Interp.Type.layout ty
  let size ← Interp.LayoutStrategy.expect_size layout "volatile set of a sized type"
  let align ← Interp.LayoutStrategy.expect_align layout "volatile set of a sized type"
  let cm' ← Interp.CM.store m.mem dst (List.replicate (count * size.bytes) (.Init val none))
    align .None
  pure { m with mem := cm' }

/-- `mrSet` on `MachTB`: `ConcurrentMemory.store` at `M := TreeBorrowsMemory x86_64`. -/
def mrSetTB (m : Interp.MachTB) (dst : Gen.ThinPointer Gen.TreeBorrowsProvenance) (val : UInt8)
    (count : Nat) (ty : Gen.«Type») : Interp.Interp Interp.MachTB := do
  let layout ← Interp.Type.layout ty
  let size ← Interp.LayoutStrategy.expect_size layout "volatile set of a sized type"
  let align ← Interp.LayoutStrategy.expect_align layout "volatile set of a sized type"
  let cm' ← Interp.ConcurrentMemory.store m.mem dst
    (List.replicate (count * size.bytes) (.Init val none)) align .None
  pure { m with mem := cm' }

/-! ## 1. Alignment first: symbolic theorems (item 1)

### MiniRust: `load` / `store`, the typed forms and the models -/

/-- `BasicMemory::load` reports UB on a misaligned address before any other check: for every
memory, provenance and length (including `0`). -/
theorem mr_bm_load_misaligned_ub (mem : Interp.BM) (ptr : Interp.Ptr) (len : LibSpecr.Size)
    (align : LibSpecr.Align) (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.BM.load mem ptr len align = .error (.ub "load from a misaligned pointer") := by
  unfold Interp.BM.load
  rw [h]
  rfl

/-- `BasicMemory::store` reports UB on a misaligned address before any other check: for every
memory, provenance and byte list (including `[]`). -/
theorem mr_bm_store_misaligned_ub (mem : Interp.BM) (ptr : Interp.Ptr) (bytes : List Interp.Byte)
    (align : LibSpecr.Align) (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.BM.store mem ptr bytes align = .error (.ub "store to a misaligned pointer") := by
  unfold Interp.BM.store
  rw [h]
  rfl

/-- `TreeBorrowsMemory::load` reports UB on a misaligned address before any other check, in
particular before any Tree Borrows access. -/
theorem mr_tbm_load_misaligned_ub (tbm : Interp.TBM)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (len : LibSpecr.Size)
    (align : LibSpecr.Align) (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.TreeBorrowsMemory.load tbm ptr len align =
      .error (.ub "load from a misaligned pointer") := by
  unfold Interp.TreeBorrowsMemory.load Interp.BasicMemory.load
  rw [h]
  rfl

/-- `TreeBorrowsMemory::store` reports UB on a misaligned address before any other check, in
particular before any Tree Borrows access. -/
theorem mr_tbm_store_misaligned_ub (tbm : Interp.TBM)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (align : LibSpecr.Align) (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.TreeBorrowsMemory.store tbm ptr bytes align =
      .error (.ub "store to a misaligned pointer") := by
  unfold Interp.TreeBorrowsMemory.store Interp.BasicMemory.store
  rw [h]
  rfl

/-- A zero-sized `BasicMemory::load` at an aligned address succeeds and leaves the memory
unchanged, for every provenance (also none) and every allocation state (also dead). -/
theorem mr_bm_load_zero_len_ok (mem : Interp.BM) (ptr : Interp.Ptr) (align : LibSpecr.Align)
    (h : Interp.Align.is_aligned align ptr.addr = true) :
    Interp.BM.load mem ptr ⟨0⟩ align = .ok ([], mem) := by
  unfold Interp.BM.load Interp.BM.check_ptr
  rw [h]
  rfl

/-- A zero-sized `BasicMemory::store` at an aligned address succeeds and leaves the memory
unchanged, for every provenance and allocation state. -/
theorem mr_bm_store_zero_len_ok (mem : Interp.BM) (ptr : Interp.Ptr) (align : LibSpecr.Align)
    (h : Interp.Align.is_aligned align ptr.addr = true) :
    Interp.BM.store mem ptr [] align = .ok mem := by
  unfold Interp.BM.store Interp.BM.check_ptr
  rw [h]
  rfl

/-- A zero-sized `TreeBorrowsMemory::load` at an aligned address succeeds and leaves the memory
unchanged, for every provenance and allocation state. -/
theorem mr_tbm_load_zero_len_ok (tbm : Interp.TBM)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (align : LibSpecr.Align)
    (h : Interp.Align.is_aligned align ptr.addr = true) :
    Interp.TreeBorrowsMemory.load tbm ptr ⟨0⟩ align = .ok ([], tbm) := by
  unfold Interp.TreeBorrowsMemory.load Interp.BasicMemory.load Interp.BasicMemory.check_ptr
  rw [h]
  rfl

/-- A zero-sized `TreeBorrowsMemory::store` at an aligned address succeeds and leaves the memory
unchanged, for every provenance and allocation state. -/
theorem mr_tbm_store_zero_len_ok (tbm : Interp.TBM)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (align : LibSpecr.Align)
    (h : Interp.Align.is_aligned align ptr.addr = true) :
    Interp.TreeBorrowsMemory.store tbm ptr [] align = .ok tbm := by
  unfold Interp.TreeBorrowsMemory.store Interp.BasicMemory.store Interp.BasicMemory.check_ptr
  rw [h]
  rfl

/-- `typedLoad` at a sized type reports the alignment UB of `load` for a misaligned pointer,
whatever the size of the type (including `0`). -/
theorem mr_typedLoad_misaligned_ub (m : Interp.Mach) (ptr : Interp.Ptr) (ty : Gen.«Type»)
    (size : LibSpecr.Size) (tyAlign align : LibSpecr.Align) (atomicity : Gen.Atomicity)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.typedLoad m ptr ty align atomicity =
      .error (.ub "load from a misaligned pointer") := by
  have hb := mr_bm_load_misaligned_ub m.mem.memory ptr size align h
  simp [Interp.typedLoad, hLay, Interp.LayoutStrategy.expect_size, Interp.CM.load, hb,
    bind, Except.bind, pure, Except.pure]

/-- `typedStore` of a well-formed, encodable value reports the alignment UB of `store` for a
misaligned pointer. (`typedStore` checks the value before it reaches `store`.) -/
theorem mr_typedStore_misaligned_ub (m : Interp.Mach) (ptr : Interp.Ptr) (val : Interp.Val)
    (ty : Gen.«Type») (bytes : List Interp.Byte) (align : LibSpecr.Align)
    (atomicity : Gen.Atomicity)
    (hChk : Interp.checkValue val ty (some m) = .ok ())
    (hEnc : Interp.Type.encode ty val = .ok bytes)
    (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.typedStore m ptr val ty align atomicity =
      .error (.ub "store to a misaligned pointer") := by
  have hb := mr_bm_store_misaligned_ub m.mem.memory ptr bytes align h
  simp [Interp.typedStore, hChk, hEnc, Interp.CM.store, hb, bind, Except.bind]

/-- `typedLoadM` on `MachTB` reports the alignment UB of `load` for a misaligned pointer. -/
theorem mr_typedLoadM_tb_misaligned_ub (m : Interp.MachTB)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (ty : Gen.«Type»)
    (size : LibSpecr.Size) (tyAlign align : LibSpecr.Align) (atomicity : Gen.Atomicity)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.typedLoadM m ptr ty align atomicity =
      .error (.ub "load from a misaligned pointer") := by
  have hb : Interp.MemoryOps.load m.mem.memory ptr size align =
      .error (.ub "load from a misaligned pointer") :=
    mr_tbm_load_misaligned_ub m.mem.memory ptr size align h
  simp [Interp.typedLoadM, hLay, Interp.LayoutStrategy.expect_size, Interp.ConcurrentMemory.load,
    hb, bind, Except.bind, pure, Except.pure]

/-- `typedStoreM` on `MachTB` of a well-formed, encodable value reports the alignment UB of
`store` for a misaligned pointer. -/
theorem mr_typedStoreM_tb_misaligned_ub (m : Interp.MachTB)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (val : Gen.Value Interp.TBM)
    (ty : Gen.«Type») (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (align : LibSpecr.Align) (atomicity : Gen.Atomicity)
    (hChk : Interp.checkValueM val ty (some m) = .ok ())
    (hEnc : Interp.Type.encodeM (M := Interp.TBM) ty val = .ok bytes)
    (h : Interp.Align.is_aligned align ptr.addr = false) :
    Interp.typedStoreM m ptr val ty align atomicity =
      .error (.ub "store to a misaligned pointer") := by
  have hb : Interp.MemoryOps.store m.mem.memory ptr bytes align =
      .error (.ub "store to a misaligned pointer") :=
    mr_tbm_store_misaligned_ub m.mem.memory ptr bytes align h
  simp [Interp.typedStoreM, hChk, hEnc, Interp.ConcurrentMemory.store, hb, bind, Except.bind]

/-- The volatile load model `mrLoad true` reports UB for a pointer misaligned for
`align_of::<T>()`, whatever `size_of::<T>()` is. -/
theorem mr_load_misaligned_ub (m : Interp.Mach) (ptr : Interp.Ptr) (ty : Gen.«Type»)
    (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign ptr.addr = false) :
    mrLoad true m ptr ty = .error (.ub "load from a misaligned pointer") := by
  have ht := mr_typedLoad_misaligned_ub m ptr ty size tyAlign tyAlign .None hLay h
  simp [mrLoad, mrAccessAlign, hLay, Interp.LayoutStrategy.expect_align, ht,
    bind, Except.bind, pure, Except.pure]

/-- `mr_load_misaligned_ub` on `MachTB`. -/
theorem mr_loadTB_misaligned_ub (m : Interp.MachTB)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (ty : Gen.«Type»)
    (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign ptr.addr = false) :
    mrLoadTB true m ptr ty = .error (.ub "load from a misaligned pointer") := by
  have ht := mr_typedLoadM_tb_misaligned_ub m ptr ty size tyAlign tyAlign .None hLay h
  simp [mrLoadTB, mrAccessAlign, hLay, Interp.LayoutStrategy.expect_align, ht,
    bind, Except.bind, pure, Except.pure]

/-- The volatile store model `mrStore true` of a well-formed, encodable value reports UB for a
pointer misaligned for `align_of::<T>()`. -/
theorem mr_store_misaligned_ub (m : Interp.Mach) (ptr : Interp.Ptr) (val : Interp.Val)
    (ty : Gen.«Type») (bytes : List Interp.Byte) (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hChk : Interp.checkValue val ty (some m) = .ok ())
    (hEnc : Interp.Type.encode ty val = .ok bytes)
    (h : Interp.Align.is_aligned tyAlign ptr.addr = false) :
    mrStore true m ptr val ty = .error (.ub "store to a misaligned pointer") := by
  have ht := mr_typedStore_misaligned_ub m ptr val ty bytes tyAlign .None hChk hEnc h
  simp [mrStore, mrAccessAlign, hLay, Interp.LayoutStrategy.expect_align, ht,
    bind, Except.bind, pure, Except.pure]

/-- `mr_store_misaligned_ub` on `MachTB`. -/
theorem mr_storeTB_misaligned_ub (m : Interp.MachTB)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (val : Gen.Value Interp.TBM)
    (ty : Gen.«Type») (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hChk : Interp.checkValueM val ty (some m) = .ok ())
    (hEnc : Interp.Type.encodeM (M := Interp.TBM) ty val = .ok bytes)
    (h : Interp.Align.is_aligned tyAlign ptr.addr = false) :
    mrStoreTB true m ptr val ty = .error (.ub "store to a misaligned pointer") := by
  have ht := mr_typedStoreM_tb_misaligned_ub m ptr val ty bytes tyAlign .None hChk hEnc h
  simp [mrStoreTB, mrAccessAlign, hLay, Interp.LayoutStrategy.expect_align, ht,
    bind, Except.bind, pure, Except.pure]

/-- `mrCopy` reports UB for a misaligned `src`, for every `count` (including `0`). -/
theorem mr_copy_src_misaligned_ub (m : Interp.Mach) (dst src : Interp.Ptr) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign src.addr = false) :
    mrCopy m dst src count ty = .error (.ub "load from a misaligned pointer") := by
  have hb := mr_bm_load_misaligned_ub m.mem.memory src ⟨count * size.bytes⟩ tyAlign h
  simp [mrCopy, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.CM.load, hb, bind, Except.bind, pure, Except.pure]

/-- `mrCopy` reports UB for a misaligned `dst` once the source load succeeded. -/
theorem mr_copy_dst_misaligned_ub (m : Interp.Mach) (dst src : Interp.Ptr) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (bytes : List Interp.Byte) (cm : Gen.ConcurrentMemory Interp.BM)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hLoad : Interp.CM.load m.mem src ⟨count * size.bytes⟩ tyAlign .None = .ok (bytes, cm))
    (h : Interp.Align.is_aligned tyAlign dst.addr = false) :
    mrCopy m dst src count ty = .error (.ub "store to a misaligned pointer") := by
  have hb := mr_bm_store_misaligned_ub cm.memory dst bytes tyAlign h
  simp [mrCopy, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    hLoad, Interp.CM.store, hb, bind, Except.bind, pure, Except.pure]

/-- A zero-byte `mrCopy` (`count = 0` or a zero-sized element) with a misaligned `dst` or `src`
is UB. -/
theorem mr_copy_zero_misaligned_ub (m : Interp.Mach) (dst src : Interp.Ptr) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hZero : count * size.bytes = 0)
    (h : Interp.Align.is_aligned tyAlign dst.addr = false ∨
      Interp.Align.is_aligned tyAlign src.addr = false) :
    ∃ msg, mrCopy m dst src count ty = .error (.ub msg) := by
  cases hs : Interp.Align.is_aligned tyAlign src.addr with
  | false => exact ⟨_, mr_copy_src_misaligned_ub m dst src count ty size tyAlign hLay hs⟩
  | true =>
    have hd : Interp.Align.is_aligned tyAlign dst.addr = false := by
      rcases h with h | h
      · exact h
      · rw [hs] at h; cases h
    refine ⟨_, mr_copy_dst_misaligned_ub m dst src count ty size tyAlign []
      { memory := m.mem.memory,
        accesses := m.mem.accesses ++ [⟨.Load, .None, src.addr, ⟨count * size.bytes⟩⟩] }
      hLay ?_ hd⟩
    simp [Interp.CM.load, hZero, mr_bm_load_zero_len_ok _ _ _ hs, bind, Except.bind, pure,
      Except.pure]

/-- `mrSet` reports UB for a misaligned `dst`, for every `count` (including `0`). -/
theorem mr_set_misaligned_ub (m : Interp.Mach) (dst : Interp.Ptr) (val : UInt8) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign dst.addr = false) :
    mrSet m dst val count ty = .error (.ub "store to a misaligned pointer") := by
  have hb := mr_bm_store_misaligned_ub m.mem.memory dst
    (List.replicate (count * size.bytes) (.Init val none)) tyAlign h
  simp [mrSet, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.CM.store, hb, bind, Except.bind, pure, Except.pure]

/-- `mr_copy_src_misaligned_ub` on `MachTB`. -/
theorem mr_copyTB_src_misaligned_ub (m : Interp.MachTB)
    (dst src : Gen.ThinPointer Gen.TreeBorrowsProvenance) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign src.addr = false) :
    mrCopyTB m dst src count ty = .error (.ub "load from a misaligned pointer") := by
  have hb : Interp.MemoryOps.load m.mem.memory src ⟨count * size.bytes⟩ tyAlign =
      .error (.ub "load from a misaligned pointer") :=
    mr_tbm_load_misaligned_ub m.mem.memory src ⟨count * size.bytes⟩ tyAlign h
  simp [mrCopyTB, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.ConcurrentMemory.load, hb, bind, Except.bind, pure, Except.pure]

/-- `mr_copy_dst_misaligned_ub` on `MachTB`. -/
theorem mr_copyTB_dst_misaligned_ub (m : Interp.MachTB)
    (dst src : Gen.ThinPointer Gen.TreeBorrowsProvenance) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (cm : Gen.ConcurrentMemory Interp.TBM)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hLoad : Interp.ConcurrentMemory.load m.mem src ⟨count * size.bytes⟩ tyAlign .None =
      .ok (bytes, cm))
    (h : Interp.Align.is_aligned tyAlign dst.addr = false) :
    mrCopyTB m dst src count ty = .error (.ub "store to a misaligned pointer") := by
  have hb : Interp.MemoryOps.store cm.memory dst bytes tyAlign =
      .error (.ub "store to a misaligned pointer") :=
    mr_tbm_store_misaligned_ub cm.memory dst bytes tyAlign h
  simp [mrCopyTB, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    hLoad, Interp.ConcurrentMemory.store, hb, bind, Except.bind, pure, Except.pure]

/-- `mr_copy_zero_misaligned_ub` on `MachTB`. -/
theorem mr_copyTB_zero_misaligned_ub (m : Interp.MachTB)
    (dst src : Gen.ThinPointer Gen.TreeBorrowsProvenance) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hZero : count * size.bytes = 0)
    (h : Interp.Align.is_aligned tyAlign dst.addr = false ∨
      Interp.Align.is_aligned tyAlign src.addr = false) :
    ∃ msg, mrCopyTB m dst src count ty = .error (.ub msg) := by
  cases hs : Interp.Align.is_aligned tyAlign src.addr with
  | false => exact ⟨_, mr_copyTB_src_misaligned_ub m dst src count ty size tyAlign hLay hs⟩
  | true =>
    have hd : Interp.Align.is_aligned tyAlign dst.addr = false := by
      rcases h with h | h
      · exact h
      · rw [hs] at h; cases h
    have hl : Interp.MemoryOps.load m.mem.memory src ⟨0⟩ tyAlign = .ok ([], m.mem.memory) :=
      mr_tbm_load_zero_len_ok m.mem.memory src tyAlign hs
    refine ⟨_, mr_copyTB_dst_misaligned_ub m dst src count ty size tyAlign []
      { memory := m.mem.memory,
        accesses := m.mem.accesses ++ [⟨.Load, .None, src.addr, ⟨count * size.bytes⟩⟩] }
      hLay ?_ hd⟩
    simp [Interp.ConcurrentMemory.load, hZero, hl, bind, Except.bind, pure, Except.pure]

/-- `mr_set_misaligned_ub` on `MachTB`. -/
theorem mr_setTB_misaligned_ub (m : Interp.MachTB)
    (dst : Gen.ThinPointer Gen.TreeBorrowsProvenance) (val : UInt8) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign dst.addr = false) :
    mrSetTB m dst val count ty = .error (.ub "store to a misaligned pointer") := by
  have hb : Interp.MemoryOps.store m.mem.memory dst
      (List.replicate (count * size.bytes) (.Init val none)) tyAlign =
      .error (.ub "store to a misaligned pointer") :=
    mr_tbm_store_misaligned_ub m.mem.memory dst _ tyAlign h
  simp [mrSetTB, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.ConcurrentMemory.store, hb, bind, Except.bind, pure, Except.pure]

/-! ### Trusted: `rawPtrTargetAligned? = some false` is `.fault .ub` -/

/-- The unaligned forms never consult alignment: with required alignment `1`,
`rawPtrTargetAligned?` answers `some true` for every pointer and every target. -/
theorem trusted_unaligned_never_consults_alignment
    (callStack : List SavedCallerFrame) (locals' : List LocalSlot)
    (decls : List LocalDecl) (layouts : LayoutTable) (arg : RawPtrArg) (tgt : RawPtrTarget) :
    rawPtrTargetAligned? callStack locals' decls layouts 1 arg tgt = .some true := rfl

/-- On a provenance-less address, Trusted's alignment answer is MiniRust's `Align::is_aligned`. -/
theorem trusted_addr_alignment_parity
    (callStack : List SavedCallerFrame) (locals' : List LocalSlot)
    (decls : List LocalDecl) (layouts : LayoutTable) (reqAlign addr : Nat) (tgt : RawPtrTarget)
    (hpos : 0 < reqAlign) :
    rawPtrTargetAligned? callStack locals' decls layouts reqAlign (.addr addr) tgt =
      .some (Interp.Align.is_aligned ⟨reqAlign⟩ (addr : Int)) := by
  unfold rawPtrTargetAligned? Interp.Align.is_aligned
  cases hb : Nat.ble reqAlign 1 with
  | true =>
    have h1 : reqAlign = 1 := by
      have := Nat.le_of_ble_eq_true hb
      omega
    subst h1
    simp
  | false =>
    have hmod : ((addr : Int) % (reqAlign : Int) == 0) = Nat.beq (Nat.mod addr reqAlign) 0 := by
      rw [← Int.natCast_emod]
      show (((addr % reqAlign : Nat) : Int) == 0) = Nat.beq (addr % reqAlign) 0
      generalize addr % reqAlign = k
      cases k with
      | zero => rfl
      | succ k => rfl
    simp [hmod]

/-- On a global allocation target with positive recorded alignment, Trusted's
`rawPtrTargetAligned?` requires `reqAlign ≤ alloc.align.bytes` and `ptr.offsetBytes % reqAlign = 0`
(alignment in every admissible placement of the global). -/
theorem trusted_global_target_aligned_iff
    (callStack : List SavedCallerFrame) (locals' : List LocalSlot)
    (decls : List LocalDecl) (layouts : LayoutTable)
    (reqAlign : Nat) (ptr : ProvenancePtr) (alloc : CapturedAllocation)
    (hReq : 1 < reqAlign) (hAllocPos : 0 < alloc.align.bytes) :
    rawPtrTargetAligned? callStack locals' decls layouts reqAlign (.prov ptr)
        (.global ptr alloc) =
      .some (decide (reqAlign ≤ alloc.align.bytes ∧ ptr.offsetBytes % reqAlign = 0)) := by
  have hble1 : Nat.ble reqAlign 1 = false := by
    cases h : Nat.ble reqAlign 1 with
    | false => rfl
    | true => exact absurd (Nat.le_of_ble_eq_true h) (by omega)
  have hbeq0 : Nat.beq alloc.align.bytes 0 = false := by
    cases h : alloc.align.bytes with
    | zero => omega
    | succ _ => rfl
  unfold rawPtrTargetAligned?
  rw [hble1]
  dsimp only
  rw [hbeq0]
  dsimp only
  cases hle : Nat.ble reqAlign alloc.align.bytes with
  | false =>
    have hnot : ¬ (reqAlign ≤ alloc.align.bytes) := by
      intro h
      rw [Nat.ble_eq_true_of_le h] at hle
      cases hle
    simp [hnot]
  | true =>
    have hle' : reqAlign ≤ alloc.align.bytes := Nat.le_of_ble_eq_true hle
    have hmod : Nat.beq (Nat.mod ptr.offsetBytes reqAlign) 0 =
        decide (ptr.offsetBytes % reqAlign = 0) := by
      change Nat.beq (ptr.offsetBytes % reqAlign) 0 = decide (ptr.offsetBytes % reqAlign = 0)
      cases ptr.offsetBytes % reqAlign <;> rfl
    simp [hle', hmod]

/-- A raw-pointer load that requires alignment is `.fault .ub` whenever `rawPtrTargetAligned?`
answers `some false`: before the null, inhabitedness, size and target checks, hence also for a
zero-sized `T`. -/
theorem trusted_load_misaligned_ub
    (isVolatile : Bool) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame) (activeProtectors : List Nat)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (srcVal : Value) (locals' : List LocalSlot)
    (srcArg : RawPtrArg) (elemTy : Ty) (size align : Nat)
    (hArg : rawPtrArgOfValue? (layoutPointerBytes layouts) srcVal = .some srcArg)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMis : rawPtrTargetAligned? callStack locals' decls layouts align srcArg
      (classifyRawPtrTarget borrows globals srcArg) = .some false) :
    rawPtrLoadAction isVolatile true borrows globals callStack activeProtectors target decls
      layouts argOps [srcVal] locals' = .fault .ub := by
  simp only [rawPtrLoadAction, hArg, hLay, hMis]

/-- A raw-pointer store that requires alignment is `.fault .ub` whenever `rawPtrTargetAligned?`
answers `some false`, whatever the stored value and `size_of::<T>()` are. -/
theorem trusted_store_misaligned_ub
    (isVolatile : Bool) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame) (callerLocals : List LocalSlot)
    (activeProtectors : List Nat)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (dstVal val : Value) (locals' : List LocalSlot)
    (dstArg : RawPtrArg) (elemTy : Ty) (size align : Nat)
    (hArg : rawPtrArgOfValue? (layoutPointerBytes layouts) dstVal = .some dstArg)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMis : rawPtrTargetAligned? callStack locals' decls layouts align dstArg
      (classifyRawPtrTarget borrows globals dstArg) = .some false) :
    rawPtrStoreAction isVolatile true borrows globals callStack callerLocals activeProtectors
      target decls layouts argOps [dstVal, val] locals' = .fault .ub := by
  simp only [rawPtrStoreAction, hArg, hLay, hMis]

/-- A volatile copy is `.fault .ub` whenever `rawPtrTargetAligned?` answers `some false` for
`dst` or for `src`, for every `count` (including `0`) and every `size_of::<T>()`. -/
theorem trusted_copy_misaligned_ub
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (dstVal srcVal : Value) (countSc : ScalarInt)
    (locals' : List LocalSlot)
    (dstArg srcArg : RawPtrArg) (elemTy : Ty) (size align : Nat)
    (hCnt : Nat.beq countSc.sizeBytes (layoutPointerBytes layouts) = true)
    (hDst : rawPtrArgOfValue? (layoutPointerBytes layouts) dstVal = .some dstArg)
    (hSrc : rawPtrArgOfValue? (layoutPointerBytes layouts) srcVal = .some srcArg)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMis :
      rawPtrTargetAligned? callStack locals' decls layouts align dstArg
        (classifyRawPtrTarget borrows globals dstArg) = .some false ∨
      rawPtrTargetAligned? callStack locals' decls layouts align srcArg
        (classifyRawPtrTarget borrows globals srcArg) = .some false) :
    volatileCopyPlan borrows globals callStack target decls layouts argOps
      [dstVal, srcVal, .scalar countSc] locals' = .fault .ub := by
  simp only [volatileCopyPlan, hCnt, hDst, hSrc, hLay]
  generalize rawPtrTargetAligned? callStack locals' decls layouts align dstArg
    (classifyRawPtrTarget borrows globals dstArg) = ad at hMis ⊢
  generalize rawPtrTargetAligned? callStack locals' decls layouts align srcArg
    (classifyRawPtrTarget borrows globals srcArg) = as at hMis ⊢
  cases (signedHalfModulus (layoutPointerBytes layouts)).ble (countSc.bits.mul size) with
  | true => rfl
  | false =>
    rcases hMis with h | h
    · subst h; rfl
    · subst h
      cases ad with
      | none => rfl
      | some b => cases b <;> rfl

/-- `volatile_set_memory` is `.fault .ub` whenever `rawPtrTargetAligned?` answers `some false`
for `dst`, for every `count` (including `0`) and every `size_of::<T>()`. -/
theorem trusted_set_misaligned_ub
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (dstVal : Value) (valSc countSc : ScalarInt)
    (locals' : List LocalSlot)
    (dstArg : RawPtrArg) (elemTy : Ty) (size align : Nat)
    (hVal : Bool.and (Nat.beq valSc.sizeBytes 1)
      (Bool.and (Nat.blt valSc.bits 256)
        (Nat.beq countSc.sizeBytes (layoutPointerBytes layouts))) = true)
    (hDst : rawPtrArgOfValue? (layoutPointerBytes layouts) dstVal = .some dstArg)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMis : rawPtrTargetAligned? callStack locals' decls layouts align dstArg
      (classifyRawPtrTarget borrows globals dstArg) = .some false) :
    volatileSetPlan borrows globals callStack target decls layouts argOps
      [dstVal, .scalar valSc, .scalar countSc] locals' = .fault .ub := by
  simp only [volatileSetPlan, hVal, hDst, hLay, hMis]
  cases (signedHalfModulus (layoutPointerBytes layouts)).ble (countSc.bits.mul size) <;> rfl

/-- `mrCopy` with a misaligned `dst` or `src` never succeeds: it reports one of the two alignment
UBs, or the error with which the load at the (aligned) source itself fails. -/
theorem mr_copy_misaligned_error (m : Interp.Mach) (dst src : Interp.Ptr) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign dst.addr = false ∨
      Interp.Align.is_aligned tyAlign src.addr = false) :
    ∃ e, mrCopy m dst src count ty = .error e ∧
      (e = .ub "load from a misaligned pointer" ∨ e = .ub "store to a misaligned pointer" ∨
        Interp.CM.load m.mem src ⟨count * size.bytes⟩ tyAlign .None = .error e) := by
  cases hs : Interp.Align.is_aligned tyAlign src.addr with
  | false =>
    exact ⟨_, mr_copy_src_misaligned_ub m dst src count ty size tyAlign hLay hs, Or.inl rfl⟩
  | true =>
    have hd : Interp.Align.is_aligned tyAlign dst.addr = false := by
      rcases h with h | h
      · exact h
      · rw [hs] at h; cases h
    cases hl : Interp.CM.load m.mem src ⟨count * size.bytes⟩ tyAlign .None with
    | error e =>
      refine ⟨e, ?_, Or.inr (Or.inr rfl)⟩
      simp [mrCopy, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
        hl, bind, Except.bind, pure, Except.pure]
    | ok r =>
      obtain ⟨bytes, cm⟩ := r
      exact ⟨_, mr_copy_dst_misaligned_ub m dst src count ty size tyAlign bytes cm hLay hl hd,
        Or.inr (Or.inl rfl)⟩

/-- `mr_copy_misaligned_error` on `MachTB`. -/
theorem mr_copyTB_misaligned_error (m : Interp.MachTB)
    (dst src : Gen.ThinPointer Gen.TreeBorrowsProvenance) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (h : Interp.Align.is_aligned tyAlign dst.addr = false ∨
      Interp.Align.is_aligned tyAlign src.addr = false) :
    ∃ e, mrCopyTB m dst src count ty = .error e ∧
      (e = .ub "load from a misaligned pointer" ∨ e = .ub "store to a misaligned pointer" ∨
        Interp.ConcurrentMemory.load m.mem src ⟨count * size.bytes⟩ tyAlign .None = .error e) := by
  cases hs : Interp.Align.is_aligned tyAlign src.addr with
  | false =>
    exact ⟨_, mr_copyTB_src_misaligned_ub m dst src count ty size tyAlign hLay hs, Or.inl rfl⟩
  | true =>
    have hd : Interp.Align.is_aligned tyAlign dst.addr = false := by
      rcases h with h | h
      · exact h
      · rw [hs] at h; cases h
    cases hl : Interp.ConcurrentMemory.load m.mem src ⟨count * size.bytes⟩ tyAlign .None with
    | error e =>
      refine ⟨e, ?_, Or.inr (Or.inr rfl)⟩
      simp [mrCopyTB, hLay, Interp.LayoutStrategy.expect_size,
        Interp.LayoutStrategy.expect_align, hl, bind, Except.bind, pure, Except.pure]
    | ok r =>
      obtain ⟨bytes, cm⟩ := r
      exact ⟨_, mr_copyTB_dst_misaligned_ub m dst src count ty size tyAlign bytes cm hLay hl hd,
        Or.inr (Or.inl rfl)⟩

/-! ### Both sides on a shared address -/

/-- A pointer-sized scalar is a provenance-less raw-pointer argument. -/
private theorem rawPtrArgOfValue_addr (pb addr : Nat) :
    rawPtrArgOfValue? pb (.scalar ⟨addr, pb⟩) = .some (.addr addr) := by
  simp [rawPtrArgOfValue?, Nat.beq_refl]

/-- `trusted_addr_alignment_parity` at an address MiniRust calls misaligned. -/
private theorem trusted_addr_misaligned
    (callStack : List SavedCallerFrame) (locals' : List LocalSlot)
    (decls : List LocalDecl) (layouts : LayoutTable) (align addr : Nat) (tgt : RawPtrTarget)
    (hpos : 0 < align)
    (hMis : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = false) :
    rawPtrTargetAligned? callStack locals' decls layouts align (.addr addr) tgt = .some false := by
  rw [trusted_addr_alignment_parity callStack locals' decls layouts align addr tgt hpos, hMis]

/-- Alignment-first parity of `volatile_load` on a shared address `addr`: if `addr` is not a
multiple of `align_of::<T>()`, the Trusted step is `MirStepNode.fail .ub` and the MiniRust
model reports the alignment UB on both memories. Nothing else is assumed: the sizes (possibly
`0`), the memories and the MiniRust provenance are arbitrary. -/
theorem volatile_load_misaligned_parity
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align addr : Nat)
    (m : Interp.Mach) (prov : Option Interp.Prov)
    (mtb : Interp.MachTB) (provTB : Option Gen.TreeBorrowsProvenance)
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hpos : 0 < align)
    (hMis : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = false) :
    evalVolatileMemIntrinsicCall .volatileLoad s target decls layouts argOps
        [.scalar ⟨addr, layoutPointerBytes layouts⟩] locals' destination targetBb =
      MirStepNode.fail .ub ∧
    mrLoad true m ⟨addr, prov⟩ mty = .error (.ub "load from a misaligned pointer") ∧
    mrLoadTB true mtb ⟨addr, provTB⟩ mty = .error (.ub "load from a misaligned pointer") := by
  have hT := trusted_load_misaligned_ub true s.memory.borrows s.memory.globals
    s.memory.callStack s.memory.activeProtectors target decls layouts argOps _ locals' _ elemTy
    size align (rawPtrArgOfValue_addr (layoutPointerBytes layouts) addr) hLay
    (trusted_addr_misaligned s.memory.callStack locals' decls layouts align addr _ hpos hMis)
  refine ⟨?_, mr_load_misaligned_ub m _ mty msize ⟨align⟩ hMLay hMis,
    mr_loadTB_misaligned_ub mtb _ mty msize ⟨align⟩ hMLay hMis⟩
  simp only [evalVolatileMemIntrinsicCall, evalRawPtrLoadCall, hT, finishRawPtrCallAction]

/-- Alignment-first parity of `volatile_store` on a shared misaligned address, for every Trusted
value and every well-formed, encodable MiniRust value. -/
theorem volatile_store_misaligned_parity
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align addr : Nat) (val : Value)
    (m : Interp.Mach) (prov : Option Interp.Prov) (mval : Interp.Val)
    (mbytes : List Interp.Byte)
    (mtb : Interp.MachTB) (provTB : Option Gen.TreeBorrowsProvenance)
    (mvalTB : Gen.Value Interp.TBM)
    (mbytesTB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hChk : Interp.checkValue mval mty (some m) = .ok ())
    (hEnc : Interp.Type.encode mty mval = .ok mbytes)
    (hChkTB : Interp.checkValueM mvalTB mty (some mtb) = .ok ())
    (hEncTB : Interp.Type.encodeM (M := Interp.TBM) mty mvalTB = .ok mbytesTB)
    (hpos : 0 < align)
    (hMis : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = false) :
    evalVolatileMemIntrinsicCall .volatileStore s target decls layouts argOps
        [.scalar ⟨addr, layoutPointerBytes layouts⟩, val] locals' destination targetBb =
      MirStepNode.fail .ub ∧
    mrStore true m ⟨addr, prov⟩ mval mty = .error (.ub "store to a misaligned pointer") ∧
    mrStoreTB true mtb ⟨addr, provTB⟩ mvalTB mty =
      .error (.ub "store to a misaligned pointer") := by
  have hT := trusted_store_misaligned_ub true s.memory.borrows s.memory.globals
    s.memory.callStack s.memory.callerLocals s.memory.activeProtectors target decls layouts
    argOps _ val locals' _ elemTy size align
    (rawPtrArgOfValue_addr (layoutPointerBytes layouts) addr) hLay
    (trusted_addr_misaligned s.memory.callStack locals' decls layouts align addr _ hpos hMis)
  refine ⟨?_, mr_store_misaligned_ub m _ mval mty mbytes msize ⟨align⟩ hMLay hChk hEnc hMis,
    mr_storeTB_misaligned_ub mtb _ mvalTB mty mbytesTB msize ⟨align⟩ hMLay hChkTB hEncTB hMis⟩
  simp only [evalVolatileMemIntrinsicCall, evalRawPtrStoreCall, hT, finishRawPtrCallAction]

/-- Alignment-first parity of both volatile copies on shared addresses: if `dst` or `src` is
misaligned, the Trusted step is `MirStepNode.fail .ub` for every `count` (including `0`), and
the MiniRust model fails on both memories (`mr_copy_misaligned_error`). -/
theorem volatile_copy_misaligned_parity
    (nonOverlapping : Bool)
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align dstAddr srcAddr count : Nat)
    (m : Interp.Mach) (dstProv srcProv : Option Interp.Prov)
    (mtb : Interp.MachTB) (dstProvTB srcProvTB : Option Gen.TreeBorrowsProvenance)
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hpos : 0 < align)
    (hMis : Interp.Align.is_aligned ⟨align⟩ (dstAddr : Int) = false ∨
      Interp.Align.is_aligned ⟨align⟩ (srcAddr : Int) = false) :
    evalVolatileCopyMemoryCall nonOverlapping s target decls layouts argOps
        [.scalar ⟨dstAddr, layoutPointerBytes layouts⟩,
         .scalar ⟨srcAddr, layoutPointerBytes layouts⟩,
         .scalar ⟨count, layoutPointerBytes layouts⟩] locals' destination targetBb =
      MirStepNode.fail .ub ∧
    (∃ e, mrCopy m ⟨dstAddr, dstProv⟩ ⟨srcAddr, srcProv⟩ count mty = .error e ∧
      (e = .ub "load from a misaligned pointer" ∨ e = .ub "store to a misaligned pointer" ∨
        Interp.CM.load m.mem ⟨srcAddr, srcProv⟩ ⟨count * msize.bytes⟩ ⟨align⟩ .None =
          .error e)) ∧
    (∃ e, mrCopyTB mtb ⟨dstAddr, dstProvTB⟩ ⟨srcAddr, srcProvTB⟩ count mty = .error e ∧
      (e = .ub "load from a misaligned pointer" ∨ e = .ub "store to a misaligned pointer" ∨
        Interp.ConcurrentMemory.load mtb.mem ⟨srcAddr, srcProvTB⟩ ⟨count * msize.bytes⟩ ⟨align⟩
          .None = .error e)) := by
  have hT := trusted_copy_misaligned_ub s.memory.borrows s.memory.globals s.memory.callStack
    target decls layouts argOps (.scalar ⟨dstAddr, layoutPointerBytes layouts⟩)
    (.scalar ⟨srcAddr, layoutPointerBytes layouts⟩) ⟨count, layoutPointerBytes layouts⟩ locals'
    (.addr dstAddr) (.addr srcAddr) elemTy size align (Nat.beq_refl _)
    (rawPtrArgOfValue_addr _ dstAddr) (rawPtrArgOfValue_addr _ srcAddr) hLay
    (hMis.imp
      (trusted_addr_misaligned s.memory.callStack locals' decls layouts align dstAddr _ hpos)
      (trusted_addr_misaligned s.memory.callStack locals' decls layouts align srcAddr _ hpos))
  refine ⟨?_, mr_copy_misaligned_error m _ _ count mty msize ⟨align⟩ hMLay hMis,
    mr_copyTB_misaligned_error mtb _ _ count mty msize ⟨align⟩ hMLay hMis⟩
  simp only [evalVolatileCopyMemoryCall, hT]

/-- Alignment-first parity of `volatile_set_memory` on a shared misaligned address, for every
byte value and every `count` (including `0`). -/
theorem volatile_set_misaligned_parity
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align addr val count : Nat)
    (m : Interp.Mach) (prov : Option Interp.Prov)
    (mtb : Interp.MachTB) (provTB : Option Gen.TreeBorrowsProvenance)
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hVal : val < 256)
    (hpos : 0 < align)
    (hMis : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = false) :
    evalVolatileMemIntrinsicCall .volatileSetMemory s target decls layouts argOps
        [.scalar ⟨addr, layoutPointerBytes layouts⟩, .scalar ⟨val, 1⟩,
         .scalar ⟨count, layoutPointerBytes layouts⟩] locals' destination targetBb =
      MirStepNode.fail .ub ∧
    mrSet m ⟨addr, prov⟩ (UInt8.ofNat val) count mty =
      .error (.ub "store to a misaligned pointer") ∧
    mrSetTB mtb ⟨addr, provTB⟩ (UInt8.ofNat val) count mty =
      .error (.ub "store to a misaligned pointer") := by
  have hV : Bool.and (Nat.beq 1 1)
      (Bool.and (Nat.blt val 256)
        (Nat.beq (layoutPointerBytes layouts) (layoutPointerBytes layouts))) = true := by
    simp [Nat.beq_refl, Nat.blt]
    omega
  have hT := trusted_set_misaligned_ub s.memory.borrows s.memory.globals s.memory.callStack
    target decls layouts argOps (.scalar ⟨addr, layoutPointerBytes layouts⟩) ⟨val, 1⟩
    ⟨count, layoutPointerBytes layouts⟩ locals' (.addr addr) elemTy size align hV
    (rawPtrArgOfValue_addr _ addr) hLay
    (trusted_addr_misaligned s.memory.callStack locals' decls layouts align addr _ hpos hMis)
  refine ⟨?_, mr_set_misaligned_ub m _ _ count mty msize ⟨align⟩ hMLay hMis,
    mr_setTB_misaligned_ub mtb _ _ count mty msize ⟨align⟩ hMLay hMis⟩
  simp only [evalVolatileMemIntrinsicCall, evalVolatileSetMemoryCall, hT]

/-! ## 2. Fixtures

One `[u8; 8]` object seen by all three semantics: the Trusted local `_1` (`vbLocals bs`,
borrowed by tag `10`), and one 8-byte MiniRust stack allocation (`vbMach (vbPlain bs)`,
`vbMachTB (vbPlain bs)`). -/

/-- Layout of `u8`. -/
def vbLU8 : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 0xFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Layout of `u32`. -/
def vbLU32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Layout of `u64` / `usize`. -/
def vbLU64 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.int 64 false) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Layout of `bool`. -/
def vbLBool : TypeLayout :=
  { size := ⟨1⟩, align := ⟨1⟩,
    backendRepr := .scalar (.initialized (.int 8 false) ⟨0, 1⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Layout of a thin pointer. -/
def vbLPtr : TypeLayout :=
  { size := ⟨8⟩, align := ⟨8⟩,
    backendRepr := .scalar (.initialized (.pointer 0) ⟨0, 0xFFFFFFFFFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Layout of `()`. -/
def vbLUnit : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

/-- Layout of `!`. -/
def vbLNever : TypeLayout :=
  { size := ⟨0⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .primitive, variants := .empty, isUninhabited := true }

/-- Layout of a zero-sized `#[repr(align(4))]` struct. -/
def vbLZstAlign4 : TypeLayout :=
  { size := ⟨0⟩, align := ⟨4⟩,
    backendRepr := .memory,
    fields := .arbitrary [] [], variants := .single 0, isUninhabited := false }

/-- Layout of `[u8; 8]`. -/
def vbLArrU8_8 : TypeLayout :=
  { size := ⟨8⟩, align := ⟨1⟩,
    backendRepr := .memory,
    fields := .array ⟨1⟩ 8, variants := .single 0, isUninhabited := false,
    fieldLayouts := [0] }

/-- Layout of `NonZeroU32`: a `u32` with valid range `1..=u32::MAX`. -/
def vbLNonZeroU32 : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨1, 0xFFFFFFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- Layout of `char`. -/
def vbLChar : TypeLayout :=
  { size := ⟨4⟩, align := ⟨4⟩,
    backendRepr := .scalar (.initialized (.int 32 false) ⟨0, 0x10FFFF⟩),
    fields := .primitive, variants := .single 0, isUninhabited := false }

/-- The 64-bit little-endian layout table of the fixtures. -/
def vbTbl : LayoutTable :=
  { pointerBits := 64,
    isLittleEndian := true,
    entries := [
      vbLU8,          -- 0
      vbLU32,         -- 1
      vbLU64,         -- 2
      vbLBool,        -- 3
      vbLPtr,         -- 4
      vbLUnit,        -- 5
      vbLNever,       -- 6
      vbLZstAlign4,   -- 7
      vbLArrU8_8,     -- 8
      vbLNonZeroU32,  -- 9
      vbLChar         -- 10
    ] }

/-- `u8`. -/
def vbTyU8 : Ty := ⟨.uint .u8, 0⟩
/-- `u32`. -/
def vbTyU32 : Ty := ⟨.uint .u32, 1⟩
/-- `u64`. -/
def vbTyU64 : Ty := ⟨.uint .u64, 2⟩
/-- `bool`. -/
def vbTyBool : Ty := ⟨.bool, 3⟩
/-- `*const u32`. -/
def vbTyPtrU32 : Ty := ⟨.rawPtr .not (.uint .u32), 4⟩
/-- `()`. -/
def vbTyUnit : Ty := ⟨.tuple [], 5⟩
/-- `!`. -/
def vbTyNever : Ty := ⟨.never, 6⟩
/-- A zero-sized `#[repr(align(4))]` struct. -/
def vbTyZstAlign4 : Ty := ⟨.adt "Zst4" [], 7⟩
/-- `[u8; 8]`. -/
def vbTyArrU8_8 : Ty := ⟨.array (.uint .u8) 8, 8⟩
/-- `NonZeroU32`. -/
def vbTyNonZeroU32 : Ty := ⟨.adt "NonZeroU32" [], 9⟩
/-- `char`. -/
def vbTyChar : Ty := ⟨.char, 10⟩

/-- A mutable local declaration of type `ty`. -/
def vbDecl (ty : Ty) : LocalDecl :=
  { mutability := .mut, ty := ty, debugName := .none }

/-- The resolved call target `defPath::<ty>`. -/
def vbTarget (defPath : String) (ty : Ty) : ResolvedCallTarget :=
  { defPath := defPath, typeArgs := [ty.kind], isIndirect := false }

/-- The Tree Borrows entry of a pointer with tag `tag` to the whole local `_1`. -/
def vbEntry (tag : Nat) (perm : TreeBorrowPerm := .active) (dead : Bool := false) : BorrowEntry :=
  { tag := tag, targetLocal := 1, targetProjection := [], perm := perm,
    targetFrameDepth := 0, allocDead := dead }

/-- The Trusted `[u8; N]` value with bytes `bs`. -/
def vbU8s (bs : List UInt8) : Value :=
  .aggregate 0 (bs.map (fun b => .scalar ⟨b.toNat, 1⟩))

/-- Base address of the MiniRust fixture allocation: `2^32`, the first address MiniRust's
first-fit allocator hands out (`allocCandidate 0`). -/
def vbBase : Int := 4294967296

/-- The empty MiniRust program. -/
def vbProg : Gen.Program :=
  { functions := ⟨[]⟩, start := ⟨⟨0⟩⟩, globals := ⟨[]⟩, traits := ⟨[]⟩, vtables := ⟨[]⟩ }

/-- A `Mach` whose memory is one stack allocation with bytes `data` at address `base`
(`align(1)`, as for `[u8; N]`), live or dead. -/
def vbMach (data : List Interp.Byte) (live : Bool := true) (base : Int := vbBase) :
    Interp.Mach :=
  { prog := vbProg,
    mem :=
      { memory :=
          { allocations :=
              [{ data := data, addr := base, align := ⟨1⟩, kind := .Stack, live := live,
                 extra := () }],
            _phantom := ⟨⟩ },
        accesses := [] },
    intptrcast := { exposed := ⟨[]⟩ },
    threads := [], active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [],
    global_ptrs := ⟨[]⟩, fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩,
    stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- A `MachTB` whose memory is one stack allocation with bytes `data` at address `base`, whose
Tree Borrows tree is a root with permission `perm` on every byte. -/
def vbMachTB (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (perm : Gen.Permission := .Unprot .Unique) (live : Bool := true) (base : Int := vbBase) :
    Interp.MachTB :=
  { prog := vbProg,
    mem :=
      { memory :=
          { params := { implicit_writes := false },
            mem :=
              { allocations :=
                  [{ data := data, addr := base, align := ⟨1⟩, kind := .Stack, live := live,
                     extra :=
                       { root :=
                           { children := [],
                             permissions := List.replicate data.length perm,
                             «protected» := .No } } }],
                _phantom := ⟨⟩ } },
        accesses := [] },
    intptrcast := { exposed := ⟨[]⟩ },
    threads := [], active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [],
    global_ptrs := ⟨[]⟩, fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩,
    stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- The `Mach` pointer to byte `off` of the fixture allocation. -/
def vbPtr (off : Int) (base : Int := vbBase) : Interp.Ptr := ⟨base + off, some (⟨0⟩, ())⟩

/-- The `MachTB` pointer to byte `off` of the fixture allocation, with the root's provenance. -/
def vbPtrTB (off : Int) (base : Int := vbBase) : Gen.ThinPointer Gen.TreeBorrowsProvenance :=
  ⟨base + off, some (⟨0⟩, [])⟩

/-- `m` with `accesses` appended to the data-race log of its memory. -/
def vbLog {M : Type} [Gen.Memory M] (m : Gen.Machine M) (accesses : List Gen.Access) :
    Gen.Machine M :=
  { m with mem := { m.mem with accesses := m.mem.accesses ++ accesses } }

/-- A zero-sized MiniRust type with alignment `4`. -/
def vbMrZst4 : Gen.«Type» := .Tuple [] ⟨⟨0⟩, ⟨4⟩, none⟩ none

/-- The Trusted memory whose only borrow is `vbEntry 10 perm dead`. -/
def vbMem (perm : TreeBorrowPerm := .active) (dead : Bool := false) : Memory :=
  { borrows := [vbEntry 10 perm dead] }

/-- Local declarations `_0 : retTy`, `_1 : [u8; 8]`. -/
def vbDecls (retTy : Ty) : List LocalDecl := [vbDecl retTy, vbDecl vbTyArrU8_8]

/-- Local slots: `_0` uninitialised, `_1 = vbU8s bs`. -/
def vbLocals (bs : List UInt8) : List LocalSlot := [.uninit, .init (vbU8s bs)]

/-- The Trusted pointer with tag `10` to byte `off` of `_1`. -/
def vbTPtr (off : Nat) : Value := .ptr ⟨10, off⟩ 8

/-- The `usize` value `n`. -/
def vbUsize (n : Nat) : Value := .scalar ⟨n, 8⟩

/-- MiniRust provenance-free initialised bytes. -/
def vbPlain {P : Type} (bs : List UInt8) : List (Gen.AbstractByte P) :=
  bs.map (fun b => .Init b none)

/-- MiniRust `u32`. -/
def vbMrU32 : Gen.«Type» := .Int ⟨.Unsigned, ⟨4⟩⟩

/-- The bytes of the `[u8; 8]` fixture. -/
def vbArr8 : List UInt8 := [0xAA, 0x78, 0x56, 0x34, 0x12, 0xBB, 0xCC, 0xDD]

/-! ## 3. The Trusted actions behind the terminator step -/

/-- The `RawPtrCallAction` of a volatile copy on memory `mem`: `volatileCopyPlan` followed, for
tracked stack pointers, by `volatileCopyStackAction`. -/
def trustedCopyAction (nonOverlapping : Bool) (mem : Memory) (target : ResolvedCallTarget)
    (decls : List LocalDecl) (layouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot) : RawPtrCallAction :=
  match
    volatileCopyPlan mem.borrows mem.globals mem.callStack target decls layouts argOps argVals
      locals'
  with
  | .fault kind => .fault kind
  | .noCopy => .ret .unit
  | .copyStack srcPtr dstPtr srcEntry dstEntry elemTy count byteCount =>
    volatileCopyStackAction nonOverlapping mem.borrows mem.callStack mem.callerLocals
      mem.activeProtectors decls layouts locals' srcPtr dstPtr srcEntry dstEntry elemTy count
      byteCount

/-- The `RawPtrCallAction` of `volatile_set_memory` on memory `mem`: `volatileSetPlan` followed,
for a tracked stack pointer, by `volatileSetStackAction`. -/
def trustedSetAction (mem : Memory) (target : ResolvedCallTarget)
    (decls : List LocalDecl) (layouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot) : RawPtrCallAction :=
  match
    volatileSetPlan mem.borrows mem.globals mem.callStack target decls layouts argOps argVals
      locals'
  with
  | .fault kind => .fault kind
  | .noWrite => .ret .unit
  | .setStack dstPtr dstEntry valByte byteCount =>
    volatileSetStackAction mem.borrows mem.callStack mem.callerLocals mem.activeProtectors decls
      layouts locals' dstPtr dstEntry valByte byteCount

/-- The `RawPtrCallAction` of each of the seven volatile memory intrinsics on memory `mem`. -/
def trustedVolatileAction (kind : RustIntrinsicKind) (mem : Memory)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot) :
    RawPtrCallAction :=
  match kind with
  | .unalignedVolatileLoad =>
    rawPtrLoadAction true false mem.borrows mem.globals mem.callStack mem.activeProtectors
      target decls layouts argOps argVals locals'
  | .unalignedVolatileStore =>
    rawPtrStoreAction true false mem.borrows mem.globals mem.callStack mem.callerLocals
      mem.activeProtectors target decls layouts argOps argVals locals'
  | .volatileLoad =>
    rawPtrLoadAction true true mem.borrows mem.globals mem.callStack mem.activeProtectors
      target decls layouts argOps argVals locals'
  | .volatileStore =>
    rawPtrStoreAction true true mem.borrows mem.globals mem.callStack mem.callerLocals
      mem.activeProtectors target decls layouts argOps argVals locals'
  | .volatileCopyNonOverlappingMemory =>
    trustedCopyAction true mem target decls layouts argOps argVals locals'
  | .volatileCopyMemory =>
    trustedCopyAction false mem target decls layouts argOps argVals locals'
  | .volatileSetMemory =>
    trustedSetAction mem target decls layouts argOps argVals locals'
  | _ => .fault .unsupported

/-- `evalVolatileMemIntrinsicCall` completes `trustedVolatileAction` with
`finishRawPtrCallAction`, for every intrinsic kind and every state. -/
theorem trustedVolatileAction_spec (kind : RustIntrinsicKind) (s : MachineState)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalVolatileMemIntrinsicCall kind s target decls layouts argOps argVals locals' destination
        targetBb =
      finishRawPtrCallAction s locals' destination targetBb
        (trustedVolatileAction kind s.memory target decls layouts argOps argVals locals') := by
  cases kind <;> first
    | rfl
    | (simp only [evalVolatileMemIntrinsicCall, evalVolatileCopyMemoryCall,
        trustedVolatileAction, trustedCopyAction]
       cases volatileCopyPlan s.memory.borrows s.memory.globals s.memory.callStack target decls
         layouts argOps argVals locals' <;> rfl)
    | (simp only [evalVolatileMemIntrinsicCall, evalVolatileSetMemoryCall,
        trustedVolatileAction, trustedSetAction]
       cases volatileSetPlan s.memory.borrows s.memory.globals s.memory.callStack target decls
         layouts argOps argVals locals' <;> rfl)

/-- The `RawPtrCallAction` of each of the four unlinked `core::ptr` helpers on memory `mem`
(`none` for any other callee). -/
def trustedUnlinkedAction (mem : Memory) (target : ResolvedCallTarget)
    (decls : List LocalDecl) (layouts : LayoutTable) (argOps : List Operand)
    (argVals : List Value) (locals' : List LocalSlot) : Option RawPtrCallAction :=
  match stringEq target.defPath "core::ptr::read_unaligned" with
  | true =>
    .some (rawPtrLoadAction false false mem.borrows mem.globals mem.callStack
      mem.activeProtectors target decls layouts argOps argVals locals')
  | false =>
    match stringEq target.defPath "core::ptr::write_unaligned" with
    | true =>
      .some (rawPtrStoreAction false false mem.borrows mem.globals mem.callStack
        mem.callerLocals mem.activeProtectors target decls layouts argOps argVals locals')
    | false =>
      match stringEq target.defPath "core::ptr::read_volatile" with
      | true =>
        .some (rawPtrLoadAction true true mem.borrows mem.globals mem.callStack
          mem.activeProtectors target decls layouts argOps argVals locals')
      | false =>
        match stringEq target.defPath "core::ptr::write_volatile" with
        | true =>
          .some (rawPtrStoreAction true true mem.borrows mem.globals mem.callStack
            mem.callerLocals mem.activeProtectors target decls layouts argOps argVals locals')
        | false => .none

/-- `evalUnlinkedPtrAccessCall?` completes `trustedUnlinkedAction` with
`finishRawPtrCallAction`, for every call target and every state. -/
theorem trustedUnlinkedAction_spec (s : MachineState)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (argVals : List Value) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx) :
    evalUnlinkedPtrAccessCall? s target decls layouts argOps argVals locals' destination
        targetBb =
      (trustedUnlinkedAction s.memory target decls layouts argOps argVals locals').map
        (finishRawPtrCallAction s locals' destination targetBb) := by
  simp only [evalUnlinkedPtrAccessCall?, trustedUnlinkedAction]
  cases stringEq target.defPath "core::ptr::read_unaligned" <;>
  cases stringEq target.defPath "core::ptr::write_unaligned" <;>
  cases stringEq target.defPath "core::ptr::read_volatile" <;>
  cases stringEq target.defPath "core::ptr::write_volatile" <;> rfl

/-! ## 4. Alignment first: lockstep witnesses, `count = 0` and zero-sized types (item 1) -/

/-- Misaligned `volatile_load::<u32>` at byte offset `1` of `[u8; 8]`: UB on Trusted, `Mach`
and `MachTB`. -/
theorem lockstep_volatile_load_misaligned :
    trustedVolatileAction .volatileLoad vbMem
        (vbTarget "core::intrinsics::volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl []
        [vbTPtr 1] (vbLocals vbArr8) = .fault .ub ∧
    mrLoad true (vbMach (vbPlain vbArr8)) (vbPtr 1) vbMrU32 =
      .error (.ub "load from a misaligned pointer") ∧
    mrLoadTB true (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) vbMrU32 =
      .error (.ub "load from a misaligned pointer") :=
  ⟨rfl, rfl, rfl⟩

/-- Misaligned `volatile_load` of a zero-sized `align(4)` type: UB on all three although no
byte is read. -/
theorem lockstep_volatile_load_zst_misaligned :
    trustedVolatileAction .volatileLoad vbMem
        (vbTarget "core::intrinsics::volatile_load" vbTyZstAlign4) (vbDecls vbTyZstAlign4)
        vbTbl [] [vbTPtr 1] (vbLocals vbArr8) = .fault .ub ∧
    mrLoad true (vbMach (vbPlain vbArr8)) (vbPtr 1) vbMrZst4 =
      .error (.ub "load from a misaligned pointer") ∧
    mrLoadTB true (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) vbMrZst4 =
      .error (.ub "load from a misaligned pointer") :=
  ⟨rfl, rfl, rfl⟩

/-- Misaligned `volatile_store::<u32>` at byte offset `1` of `[u8; 8]`: UB on all three. -/
theorem lockstep_volatile_store_misaligned :
    trustedVolatileAction .volatileStore vbMem
        (vbTarget "core::intrinsics::volatile_store" vbTyU32) (vbDecls vbTyUnit) vbTbl []
        [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    mrStore true (vbMach (vbPlain vbArr8)) (vbPtr 1) (.Int 0x04030201) vbMrU32 =
      .error (.ub "store to a misaligned pointer") ∧
    mrStoreTB true (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) (.Int 0x04030201) vbMrU32 =
      .error (.ub "store to a misaligned pointer") :=
  ⟨rfl, rfl, rfl⟩

/-- Misaligned `volatile_store` of a zero-sized `align(4)` value: UB on all three although no
byte is written. -/
theorem lockstep_volatile_store_zst_misaligned :
    trustedVolatileAction .volatileStore vbMem
        (vbTarget "core::intrinsics::volatile_store" vbTyZstAlign4)
        [vbDecl vbTyUnit, vbDecl vbTyArrU8_8, vbDecl vbTyZstAlign4] vbTbl []
        [vbTPtr 1, .aggregate 0 []] (vbLocals vbArr8) = .fault .ub ∧
    mrStore true (vbMach (vbPlain vbArr8)) (vbPtr 1) (.Tuple []) vbMrZst4 =
      .error (.ub "store to a misaligned pointer") ∧
    mrStoreTB true (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) (.Tuple []) vbMrZst4 =
      .error (.ub "store to a misaligned pointer") :=
  ⟨rfl, rfl, rfl⟩

/-- Misaligned `volatile_copy_nonoverlapping_memory` / `volatile_copy_memory` with `count = 0`:
UB on all three, for a misaligned `dst` and for a misaligned `src`. -/
theorem lockstep_volatile_copy_count0_misaligned :
    trustedVolatileAction .volatileCopyNonOverlappingMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_nonoverlapping_memory" vbTyU32)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 1, vbTPtr 4, vbUsize 0] (vbLocals vbArr8) =
      .fault .ub ∧
    trustedVolatileAction .volatileCopyMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_memory" vbTyU32)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 1, vbTPtr 4, vbUsize 0] (vbLocals vbArr8) =
      .fault .ub ∧
    mrCopy (vbMach (vbPlain vbArr8)) (vbPtr 1) (vbPtr 4) 0 vbMrU32 =
      .error (.ub "store to a misaligned pointer") ∧
    mrCopy (vbMach (vbPlain vbArr8)) (vbPtr 4) (vbPtr 1) 0 vbMrU32 =
      .error (.ub "load from a misaligned pointer") ∧
    mrCopyTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) (vbPtrTB 4) 0 vbMrU32 =
      .error (.ub "store to a misaligned pointer") ∧
    mrCopyTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 4) (vbPtrTB 1) 0 vbMrU32 =
      .error (.ub "load from a misaligned pointer") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Misaligned volatile copies of three zero-sized `align(4)` elements: UB on all three. -/
theorem lockstep_volatile_copy_zst_misaligned :
    trustedVolatileAction .volatileCopyNonOverlappingMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_nonoverlapping_memory" vbTyZstAlign4)
        [vbDecl vbTyUnit, vbDecl vbTyArrU8_8, vbDecl vbTyZstAlign4] vbTbl []
        [vbTPtr 1, vbTPtr 4, vbUsize 3] (vbLocals vbArr8) = .fault .ub ∧
    trustedVolatileAction .volatileCopyMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_memory" vbTyZstAlign4)
        [vbDecl vbTyUnit, vbDecl vbTyArrU8_8, vbDecl vbTyZstAlign4] vbTbl []
        [vbTPtr 1, vbTPtr 4, vbUsize 3] (vbLocals vbArr8) = .fault .ub ∧
    mrCopy (vbMach (vbPlain vbArr8)) (vbPtr 1) (vbPtr 4) 3 vbMrZst4 =
      .error (.ub "store to a misaligned pointer") ∧
    mrCopyTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) (vbPtrTB 4) 3 vbMrZst4 =
      .error (.ub "store to a misaligned pointer") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Misaligned `volatile_set_memory` with `count = 0` and with a zero-sized `align(4)` element:
UB on all three. -/
theorem lockstep_volatile_set_count0_and_zst_misaligned :
    trustedVolatileAction .volatileSetMemory vbMem
        (vbTarget "core::intrinsics::volatile_set_memory" vbTyU32)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 1, .scalar ⟨0xAB, 1⟩, vbUsize 0] (vbLocals vbArr8) =
      .fault .ub ∧
    trustedVolatileAction .volatileSetMemory vbMem
        (vbTarget "core::intrinsics::volatile_set_memory" vbTyZstAlign4)
        [vbDecl vbTyUnit, vbDecl vbTyArrU8_8, vbDecl vbTyZstAlign4] vbTbl []
        [vbTPtr 1, .scalar ⟨0xAB, 1⟩, vbUsize 3] (vbLocals vbArr8) = .fault .ub ∧
    mrSet (vbMach (vbPlain vbArr8)) (vbPtr 1) 0xAB 0 vbMrU32 =
      .error (.ub "store to a misaligned pointer") ∧
    mrSet (vbMach (vbPlain vbArr8)) (vbPtr 1) 0xAB 3 vbMrZst4 =
      .error (.ub "store to a misaligned pointer") ∧
    mrSetTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) 0xAB 0 vbMrU32 =
      .error (.ub "store to a misaligned pointer") ∧
    mrSetTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) 0xAB 3 vbMrZst4 =
      .error (.ub "store to a misaligned pointer") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The bytes of every allocation of a `Mach`. -/
def machBytes (m : Interp.Mach) : List (List Interp.Byte) :=
  m.mem.memory.allocations.map (·.data)

/-- The bytes of every allocation of a `MachTB`. -/
def machBytesTB (m : Interp.MachTB) : List (List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) :=
  m.mem.memory.mem.allocations.map (·.data)

/-- Decidable observation of a typed load on `Mach`: the loaded integer and the bytes of every
allocation afterwards (`none` unless the load returned an integer). -/
def loadedInt (r : Interp.Interp (Interp.Val × Interp.Mach)) :
    Option (Int × List (List Interp.Byte)) :=
  match r with
  | .ok (.Int i, m') => some (i, machBytes m')
  | _ => none

/-- `loadedInt` on `MachTB`. -/
def loadedIntTB (r : Interp.Interp (Gen.Value Interp.TBM × Interp.MachTB)) :
    Option (Int × List (List (Gen.AbstractByte Gen.TreeBorrowsProvenance))) :=
  match r with
  | .ok (.Int i, m') => some (i, machBytesTB m')
  | _ => none

/-- `loadedInt r = some (i, bs)` means `r` returned `Value::Int i` and a machine with bytes `bs`. -/
theorem loadedInt_sound {r : Interp.Interp (Interp.Val × Interp.Mach)} {i : Int}
    {bs : List (List Interp.Byte)} (h : loadedInt r = some (i, bs)) :
    ∃ m', r = .ok (.Int i, m') ∧ machBytes m' = bs := by
  cases r with
  | error e => cases h
  | ok p =>
    obtain ⟨v, m'⟩ := p
    cases v with
    | Int j =>
      simp only [loadedInt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m', rfl, rfl⟩
    | _ => cases h

/-- `loadedInt_sound` on `MachTB`. -/
theorem loadedIntTB_sound {r : Interp.Interp (Gen.Value Interp.TBM × Interp.MachTB)} {i : Int}
    {bs : List (List (Gen.AbstractByte Gen.TreeBorrowsProvenance))}
    (h : loadedIntTB r = some (i, bs)) :
    ∃ m', r = .ok (.Int i, m') ∧ machBytesTB m' = bs := by
  cases r with
  | error e => cases h
  | ok p =>
    obtain ⟨v, m'⟩ := p
    cases v with
    | Int j =>
      simp only [loadedIntTB, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m', rfl, rfl⟩
    | _ => cases h

/-- Decidable observation of a store, copy or set on `Mach`: the bytes of every allocation
afterwards (`none` on any error). -/
def storedBytes (r : Interp.Interp Interp.Mach) : Option (List (List Interp.Byte)) :=
  match r with
  | .ok m' => some (machBytes m')
  | .error _ => none

/-- `storedBytes` on `MachTB`. -/
def storedBytesTB (r : Interp.Interp Interp.MachTB) :
    Option (List (List (Gen.AbstractByte Gen.TreeBorrowsProvenance))) :=
  match r with
  | .ok m' => some (machBytesTB m')
  | .error _ => none

/-- `storedBytes r = some bs` means `r` succeeded with a machine with bytes `bs`. -/
theorem storedBytes_sound {r : Interp.Interp Interp.Mach} {bs : List (List Interp.Byte)}
    (h : storedBytes r = some bs) : ∃ m', r = .ok m' ∧ machBytes m' = bs := by
  cases r with
  | error e => cases h
  | ok m' =>
    simp only [storedBytes, Option.some.injEq] at h
    exact ⟨m', rfl, h⟩

/-- `storedBytes_sound` on `MachTB`. -/
theorem storedBytesTB_sound {r : Interp.Interp Interp.MachTB}
    {bs : List (List (Gen.AbstractByte Gen.TreeBorrowsProvenance))}
    (h : storedBytesTB r = some bs) : ∃ m', r = .ok m' ∧ machBytesTB m' = bs := by
  cases r with
  | error e => cases h
  | ok m' =>
    simp only [storedBytesTB, Option.some.injEq] at h
    exact ⟨m', rfl, h⟩

/-- Trusted requires alignment in every placement of an allocation, MiniRust at the concrete
address. `volatile_load::<u32>` at byte offset `0` of an `align(1)` `[u8; 8]` is `.fault .ub`
in Trusted; in MiniRust it is defined when the allocation sits at `2^32` and UB when it sits
at `2^32 + 1`, an equally admissible address for an `align(1)` allocation. -/
theorem placement_dependent_alignment_witness :
    trustedVolatileAction .volatileLoad vbMem
        (vbTarget "core::intrinsics::volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl []
        [vbTPtr 0] (vbLocals vbArr8) = .fault .ub ∧
    (∃ m', mrLoad true (vbMach (vbPlain vbArr8)) (vbPtr 0) vbMrU32 = .ok (.Int 0x345678AA, m') ∧
      machBytes m' = [vbPlain vbArr8]) ∧
    mrLoad true (vbMach (vbPlain vbArr8) true (vbBase + 1)) (vbPtr 0 (vbBase + 1)) vbMrU32 =
      .error (.ub "load from a misaligned pointer") ∧
    (∃ m', mrLoadTB true (vbMachTB (vbPlain vbArr8)) (vbPtrTB 0) vbMrU32 =
        .ok (.Int 0x345678AA, m') ∧ machBytesTB m' = [vbPlain vbArr8]) ∧
    mrLoadTB true (vbMachTB (vbPlain vbArr8) (.Unprot .Unique) true (vbBase + 1))
        (vbPtrTB 0 (vbBase + 1)) vbMrU32 =
      .error (.ub "load from a misaligned pointer") :=
  ⟨rfl, loadedInt_sound (by decide +kernel), rfl, loadedIntTB_sound (by decide +kernel), rfl⟩

/-! ## 5. In-allocation unaligned accesses at byte offset 1 of `[u8; 8]` (item 3) -/

/-- `unaligned_volatile_load::<u32>` and `read_unaligned::<u32>` at byte offset `1` of `[u8; 8]`
return `0x12345678` on Trusted, `Mach` and `MachTB`, and leave the bytes unchanged. -/
theorem lockstep_unaligned_load_offset1 :
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl
        [] [vbTPtr 1] (vbLocals vbArr8) =
      .retBorrows [vbEntry 10] (.scalar ⟨0x12345678, 4⟩) ∧
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::read_unaligned" vbTyU32)
        (vbDecls vbTyU32) vbTbl [] [vbTPtr 1] (vbLocals vbArr8) =
      .some (.retBorrows [vbEntry 10] (.scalar ⟨0x12345678, 4⟩)) ∧
    (∃ m', mrLoad false (vbMach (vbPlain vbArr8)) (vbPtr 1) vbMrU32 =
        .ok (.Int 0x12345678, m') ∧ machBytes m' = [vbPlain vbArr8]) ∧
    (∃ m', mrLoadTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) vbMrU32 =
        .ok (.Int 0x12345678, m') ∧ machBytesTB m' = [vbPlain vbArr8]) :=
  ⟨rfl, rfl, loadedInt_sound (by decide +kernel), loadedIntTB_sound (by decide +kernel)⟩

/-- `unaligned_volatile_store::<u32>` and `write_unaligned::<u32>` of `0x04030201` at byte offset
`1` of `[u8; 8]` splice the same four bytes into bytes `1..5` on Trusted, `Mach` and `MachTB`
and preserve the neighbouring bytes. -/
theorem lockstep_unaligned_store_offset1 :
    trustedVolatileAction .unalignedVolatileStore vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) =
      .retStack [vbEntry 10] (vbLocals [0xAA, 0x01, 0x02, 0x03, 0x04, 0xBB, 0xCC, 0xDD])
        [] [] .unit ∧
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::write_unaligned" vbTyU32)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) =
      .some (.retStack [vbEntry 10]
        (vbLocals [0xAA, 0x01, 0x02, 0x03, 0x04, 0xBB, 0xCC, 0xDD]) [] [] .unit) ∧
    (∃ m', mrStore false (vbMach (vbPlain vbArr8)) (vbPtr 1) (.Int 0x04030201) vbMrU32 =
        .ok m' ∧
      machBytes m' = [vbPlain [0xAA, 0x01, 0x02, 0x03, 0x04, 0xBB, 0xCC, 0xDD]]) ∧
    (∃ m', mrStoreTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) (.Int 0x04030201) vbMrU32 =
        .ok m' ∧
      machBytesTB m' = [vbPlain [0xAA, 0x01, 0x02, 0x03, 0x04, 0xBB, 0xCC, 0xDD]]) :=
  ⟨rfl, rfl, storedBytes_sound (by decide +kernel), storedBytesTB_sound (by decide +kernel)⟩

/-- An unaligned `u32` load or store at byte offset `6` of `[u8; 8]` leaves the allocation: UB on
all three. -/
theorem lockstep_unaligned_out_of_bounds_ub :
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl
        [] [vbTPtr 6] (vbLocals vbArr8) = .fault .ub ∧
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::read_unaligned" vbTyU32)
        (vbDecls vbTyU32) vbTbl [] [vbTPtr 6] (vbLocals vbArr8) = .some (.fault .ub) ∧
    trustedVolatileAction .unalignedVolatileStore vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 6, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    mrLoad false (vbMach (vbPlain vbArr8)) (vbPtr 6) vbMrU32 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    mrStore false (vbMach (vbPlain vbArr8)) (vbPtr 6) (.Int 0x04030201) vbMrU32 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    mrLoadTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB 6) vbMrU32 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") ∧
    mrStoreTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB 6) (.Int 0x04030201) vbMrU32 =
      .error (.ub "dereferencing pointer outside the bounds of its allocation") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An unaligned access through a pointer to a deallocated allocation (Trusted `allocDead`, or a
`StorageDead` local; MiniRust `live = false`) is UB on all three. -/
theorem lockstep_unaligned_dead_allocation_ub :
    trustedVolatileAction .unalignedVolatileLoad (vbMem .active true)
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl
        [] [vbTPtr 1] (vbLocals vbArr8) = .fault .ub ∧
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl
        [] [vbTPtr 1] [.uninit, .dead] = .fault .ub ∧
    trustedVolatileAction .unalignedVolatileStore (vbMem .active true)
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    mrLoad false (vbMach (vbPlain vbArr8) false) (vbPtr 1) vbMrU32 =
      .error (.ub "dereferencing pointer to dead allocation") ∧
    mrStore false (vbMach (vbPlain vbArr8) false) (vbPtr 1) (.Int 0x04030201) vbMrU32 =
      .error (.ub "dereferencing pointer to dead allocation") ∧
    mrLoadTB false (vbMachTB (vbPlain vbArr8) (.Unprot .Unique) false) (vbPtrTB 1) vbMrU32 =
      .error (.ub "dereferencing pointer to dead allocation") ∧
    mrStoreTB false (vbMachTB (vbPlain vbArr8) (.Unprot .Unique) false) (vbPtrTB 1)
        (.Int 0x04030201) vbMrU32 =
      .error (.ub "dereferencing pointer to dead allocation") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The null pointer of `Mach`. -/
def vbNull : Interp.Ptr := ⟨0, none⟩

/-- The null pointer of `MachTB`. -/
def vbNullTB : Gen.ThinPointer Gen.TreeBorrowsProvenance := ⟨0, none⟩

/-- MiniRust `()`. -/
def vbMrUnit : Gen.«Type» := .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none

/-- `read_unaligned::<u32>` / `write_unaligned::<u32>` through a null pointer: UB on all three. -/
theorem lockstep_unaligned_null_nonzst_ub :
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::read_unaligned" vbTyU32)
        (vbDecls vbTyU32) vbTbl [] [vbUsize 0] (vbLocals vbArr8) = .some (.fault .ub) ∧
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::write_unaligned" vbTyU32)
        (vbDecls vbTyUnit) vbTbl [] [vbUsize 0, .scalar ⟨7, 4⟩] (vbLocals vbArr8) =
      .some (.fault .ub) ∧
    mrLoad false (vbMach (vbPlain vbArr8)) vbNull vbMrU32 =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrStore false (vbMach (vbPlain vbArr8)) vbNull (.Int 7) vbMrU32 =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrLoadTB false (vbMachTB (vbPlain vbArr8)) vbNullTB vbMrU32 =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrStoreTB false (vbMachTB (vbPlain vbArr8)) vbNullTB (.Int 7) vbMrU32 =
      .error (.ub "dereferencing pointer without provenance") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Divergence on zero-sized accesses through a null pointer. Trusted reports `.ub` for
`read_unaligned::<()>` / `write_unaligned::<()>` (the documented contract: a null pointer is
never valid), while MiniRust accepts every zero-sized access on both memories. The volatile
intrinsics accept the null pointer in Trusted too, in agreement with MiniRust. -/
theorem divergence_null_zst_read_write_unaligned :
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::read_unaligned" vbTyUnit)
        (vbDecls vbTyUnit) vbTbl [] [vbUsize 0] (vbLocals vbArr8) = .some (.fault .ub) ∧
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::write_unaligned" vbTyUnit)
        (vbDecls vbTyUnit) vbTbl [] [vbUsize 0, .unit] (vbLocals vbArr8) = .some (.fault .ub) ∧
    trustedVolatileAction .volatileLoad vbMem
        (vbTarget "core::intrinsics::volatile_load" vbTyUnit) (vbDecls vbTyUnit) vbTbl []
        [vbUsize 0] (vbLocals vbArr8) = .ret .unit ∧
    trustedVolatileAction .unalignedVolatileStore vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyUnit) (vbDecls vbTyUnit)
        vbTbl [] [vbUsize 0, .unit] (vbLocals vbArr8) = .ret .unit ∧
    mrLoad false (vbMach (vbPlain vbArr8)) vbNull vbMrUnit =
      .ok (.Tuple [],
        vbLog (vbMach (vbPlain vbArr8)) [⟨.Load, .None, 0, ⟨0⟩⟩]) ∧
    mrStore false (vbMach (vbPlain vbArr8)) vbNull (.Tuple []) vbMrUnit =
      .ok (vbLog (vbMach (vbPlain vbArr8)) [⟨.Store, .None, 0, ⟨0⟩⟩]) ∧
    mrLoadTB false (vbMachTB (vbPlain vbArr8)) vbNullTB vbMrUnit =
      .ok (.Tuple [],
        vbLog (vbMachTB (vbPlain vbArr8)) [⟨.Load, .None, 0, ⟨0⟩⟩]) ∧
    mrStoreTB false (vbMachTB (vbPlain vbArr8)) vbNullTB (.Tuple []) vbMrUnit =
      .ok (vbLog (vbMachTB (vbPlain vbArr8)) [⟨.Store, .None, 0, ⟨0⟩⟩]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `n` uninitialised MiniRust bytes. -/
def vbUninit {P : Type} (n : Nat) : List (Gen.AbstractByte P) := List.replicate n .Uninit

/-- An unaligned `u32` load of uninitialised memory is UB on all three. -/
theorem lockstep_unaligned_uninit_ub :
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl
        [] [vbTPtr 1] [.uninit, .uninit] = .fault .ub ∧
    trustedUnlinkedAction vbMem (vbTarget "core::ptr::read_unaligned" vbTyU32)
        (vbDecls vbTyU32) vbTbl [] [vbTPtr 1] [.uninit, .uninit] = .some (.fault .ub) ∧
    mrLoad false (vbMach (vbUninit 8)) (vbPtr 1) vbMrU32 =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    mrLoadTB false (vbMachTB (vbUninit 8)) (vbPtrTB 1) vbMrU32 =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Tree Borrows permission conflicts of unaligned accesses: a write through a `Frozen` pointer
and a read or write through a `Disabled` pointer are UB in Trusted and on `MachTB`; a read
through a `Frozen` pointer is allowed by both. -/
theorem lockstep_tree_borrows_conflict_ub :
    -- frozen write
    trustedVolatileAction .unalignedVolatileStore (vbMem .frozen)
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    mrStoreTB false (vbMachTB (vbPlain vbArr8) (.Unprot .Frozen)) (vbPtrTB 1) (.Int 0x04030201)
        vbMrU32 = .error (.ub "Tree Borrows: local write of Frozen reference") ∧
    -- disabled read
    trustedVolatileAction .unalignedVolatileLoad (vbMem .disabled)
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl
        [] [vbTPtr 1] (vbLocals vbArr8) = .fault .ub ∧
    mrLoadTB false (vbMachTB (vbPlain vbArr8) (.Unprot .Disabled)) (vbPtrTB 1) vbMrU32 =
      .error (.ub "Tree Borrows: local read of Disabled reference") ∧
    -- disabled write
    trustedVolatileAction .unalignedVolatileStore (vbMem .disabled)
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    mrStoreTB false (vbMachTB (vbPlain vbArr8) (.Unprot .Disabled)) (vbPtrTB 1)
        (.Int 0x04030201) vbMrU32 =
      .error (.ub "Tree Borrows: local write of Disabled reference") ∧
    -- frozen read is allowed on both
    trustedVolatileAction .unalignedVolatileLoad (vbMem .frozen)
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32) vbTbl
        [] [vbTPtr 1] (vbLocals vbArr8) =
      .retBorrows [vbEntry 10 .frozen] (.scalar ⟨0x12345678, 4⟩) ∧
    (∃ m', mrLoadTB false (vbMachTB (vbPlain vbArr8) (.Unprot .Frozen)) (vbPtrTB 1) vbMrU32 =
        .ok (.Int 0x12345678, m') ∧ machBytesTB m' = [vbPlain vbArr8]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, loadedIntTB_sound (by decide +kernel)⟩

/-- Trusted memory with parent tag `10` (`active`) and a strongly-protected child tag `11`
(`protector = some 1`, `1 ∈ activeProtectors`) aliasing the whole local `_1`. -/
def vbMemProt (childPerm : TreeBorrowPerm := .reserved) : Memory :=
  { borrows :=
      [{ tag := 11, targetLocal := 1, targetProjection := [], perm := childPerm,
         protector := .some 1, parentTag := .some 10, targetFrameDepth := 0 },
       vbEntry 10],
    activeProtectors := [1] }

/-- `MachTB` whose single stack allocation has a two-node Tree Borrows tree: root `Unique`
(accessed via `vbPtrTB`) and one `Protected.Strong` child (`path = [0]`) with permission
`childPerm` on every byte. -/
def vbMachTBProt (data : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (childPerm : Gen.Permission := .Prot (.Reserved true false))
    (live : Bool := true) (base : Int := vbBase) : Interp.MachTB :=
  { prog := vbProg,
    mem :=
      { memory :=
          { params := { implicit_writes := false },
            mem :=
              { allocations :=
                  [{ data := data, addr := base, align := ⟨1⟩, kind := .Stack, live := live,
                     extra :=
                       { root :=
                           { children :=
                               [{ children := [],
                                  permissions := List.replicate data.length childPerm,
                                  «protected» := .Strong }],
                             permissions := List.replicate data.length (.Unprot .Unique),
                             «protected» := .No } } }],
                _phantom := ⟨⟩ } },
        accesses := [] },
    intptrcast := { exposed := ⟨[]⟩ },
    threads := [], active_thread := 0, synchronized_threads := ⟨[]⟩, locks := [],
    global_ptrs := ⟨[]⟩, fn_ptrs := ⟨[]⟩, vtable_ptrs := ⟨[]⟩,
    stdout := ⟨[]⟩, stderr := ⟨[]⟩ }

/-- Active-protector Tree Borrows conflicts in lockstep between Trusted and `MachTB`:
a foreign write through parent pointer `vbTPtr`/`vbPtrTB` while a child tag is strongly protected
with `Reserved` (had local read), `Frozen` (had local read), or `Unique`/`active` is UB on both
Trusted and `MachTB`, for both unaligned (`u32` at offset 1) and aligned volatile (`u8` at offset 1)
stores; a foreign read of a protected `Unique`/`active` child is UB on both; and a foreign read of
a protected `Reserved` or `Frozen` child is allowed on both. -/
theorem lockstep_tree_borrows_protector_conflict_ub :
    -- Foreign write to protected Reserved (unaligned u32 & aligned volatile u8)
    trustedVolatileAction .unalignedVolatileStore (vbMemProt .reserved)
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    trustedVolatileAction .volatileStore (vbMemProt .reserved)
        (vbTarget "core::intrinsics::volatile_store" vbTyU8) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x5A, 1⟩] (vbLocals vbArr8) = .fault .ub ∧
    trustedUnlinkedAction (vbMemProt .reserved)
        (vbTarget "core::ptr::write_unaligned" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .some (.fault .ub) ∧
    mrStoreTB false (vbMachTBProt (vbPlain vbArr8) (.Prot (.Reserved true false))) (vbPtrTB 1)
        (.Int 0x04030201) vbMrU32 =
      .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") ∧
    mrStoreTB true (vbMachTBProt (vbPlain vbArr8) (.Prot (.Reserved true false))) (vbPtrTB 1)
        (.Int 0x5A) (.Int ⟨.Unsigned, ⟨1⟩⟩) =
      .error (.ub "Tree Borrows: foreign write of protected Reserved reference which had a local read") ∧
    -- Foreign write to protected Frozen
    trustedVolatileAction .unalignedVolatileStore (vbMemProt .frozen)
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
        vbTbl [] [vbTPtr 1, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    mrStoreTB false (vbMachTBProt (vbPlain vbArr8) (.Prot (.Frozen true))) (vbPtrTB 1)
        (.Int 0x04030201) vbMrU32 =
      .error (.ub "Tree Borrows: foreign write of protected Frozen reference which had a local read") ∧
    -- Foreign read of protected Unique/active is UB on both
    trustedVolatileAction .unalignedVolatileLoad (vbMemProt .active)
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32)
        vbTbl [] [vbTPtr 1] (vbLocals vbArr8) = .fault .ub ∧
    mrLoadTB false (vbMachTBProt (vbPlain vbArr8) (.Prot .Unique)) (vbPtrTB 1) vbMrU32 =
      .error (.ub "Tree Borrows: foreign read of protected Unique reference") ∧
    -- Positive control: foreign read of protected Reserved is allowed on both (and marks
    -- the protected child's foreign-read conflict latch: `reservedFrz true` / `had_foreign_read = true`)
    trustedVolatileAction .unalignedVolatileLoad (vbMemProt .reserved)
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32)
        vbTbl [] [vbTPtr 1] (vbLocals vbArr8) =
      .retBorrows
        [{ tag := 11, targetLocal := 1, targetProjection := [], perm := .reservedFrz true,
           protector := .some 1, parentTag := .some 10, targetFrameDepth := 0 },
         vbEntry 10] (.scalar ⟨0x12345678, 4⟩) ∧
    (∃ m', mrLoadTB false (vbMachTBProt (vbPlain vbArr8) (.Prot (.Reserved true false)))
        (vbPtrTB 1) vbMrU32 = .ok (.Int 0x12345678, m') ∧ machBytesTB m' = [vbPlain vbArr8]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, loadedIntTB_sound (by decide +kernel)⟩

/-! ## 6. Copy and set: lockstep witnesses (item 4) -/

/-- MiniRust `u8`. -/
def vbMrU8 : Gen.«Type» := .Int ⟨.Unsigned, ⟨1⟩⟩

/-- Argument order `(dst, src, count)`: `volatile_copy_nonoverlapping_memory::<u8>(p + 4, p, 4)`
copies bytes `0..4` to bytes `4..8` (and not the other way round) on Trusted, `Mach` and
`MachTB`. -/
theorem lockstep_volatile_copy_dst_src_count_order :
    trustedVolatileAction .volatileCopyNonOverlappingMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_nonoverlapping_memory" vbTyU8)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 4, vbTPtr 0, vbUsize 4] (vbLocals vbArr8) =
      .retStack [vbEntry 10] (vbLocals [0xAA, 0x78, 0x56, 0x34, 0xAA, 0x78, 0x56, 0x34])
        [] [] .unit ∧
    (∃ m', mrCopy (vbMach (vbPlain vbArr8)) (vbPtr 4) (vbPtr 0) 4 vbMrU8 = .ok m' ∧
      machBytes m' = [vbPlain [0xAA, 0x78, 0x56, 0x34, 0xAA, 0x78, 0x56, 0x34]]) ∧
    (∃ m', mrCopyTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 4) (vbPtrTB 0) 4 vbMrU8 = .ok m' ∧
      machBytesTB m' = [vbPlain [0xAA, 0x78, 0x56, 0x34, 0xAA, 0x78, 0x56, 0x34]]) :=
  ⟨rfl, storedBytes_sound (by decide +kernel), storedBytesTB_sound (by decide +kernel)⟩

/-- Overlapping `volatile_copy_memory::<u8>` is a `memmove` on Trusted, `Mach` and `MachTB`, for
a forward overlap (`dst > src`) and a backward overlap (`dst < src`): the destination receives
the source bytes as they were before the call. -/
theorem lockstep_volatile_copy_memory_memmove :
    -- forward overlap: dst > src
    trustedVolatileAction .volatileCopyMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_memory" vbTyU8)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 2, vbTPtr 0, vbUsize 4] (vbLocals vbArr8) =
      .retStack [vbEntry 10] (vbLocals [0xAA, 0x78, 0xAA, 0x78, 0x56, 0x34, 0xCC, 0xDD])
        [] [] .unit ∧
    (∃ m', mrCopy (vbMach (vbPlain vbArr8)) (vbPtr 2) (vbPtr 0) 4 vbMrU8 = .ok m' ∧
      machBytes m' = [vbPlain [0xAA, 0x78, 0xAA, 0x78, 0x56, 0x34, 0xCC, 0xDD]]) ∧
    (∃ m', mrCopyTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 2) (vbPtrTB 0) 4 vbMrU8 = .ok m' ∧
      machBytesTB m' = [vbPlain [0xAA, 0x78, 0xAA, 0x78, 0x56, 0x34, 0xCC, 0xDD]]) ∧
    -- backward overlap: dst < src
    trustedVolatileAction .volatileCopyMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_memory" vbTyU8)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 0, vbTPtr 2, vbUsize 4] (vbLocals vbArr8) =
      .retStack [vbEntry 10] (vbLocals [0x56, 0x34, 0x12, 0xBB, 0x12, 0xBB, 0xCC, 0xDD])
        [] [] .unit ∧
    (∃ m', mrCopy (vbMach (vbPlain vbArr8)) (vbPtr 0) (vbPtr 2) 4 vbMrU8 = .ok m' ∧
      machBytes m' = [vbPlain [0x56, 0x34, 0x12, 0xBB, 0x12, 0xBB, 0xCC, 0xDD]]) ∧
    (∃ m', mrCopyTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 0) (vbPtrTB 2) 4 vbMrU8 = .ok m' ∧
      machBytesTB m' = [vbPlain [0x56, 0x34, 0x12, 0xBB, 0x12, 0xBB, 0xCC, 0xDD]]) :=
  ⟨rfl, storedBytes_sound (by decide +kernel), storedBytesTB_sound (by decide +kernel),
   rfl, storedBytes_sound (by decide +kernel), storedBytesTB_sound (by decide +kernel)⟩

/-- `volatile_set_memory::<u8>(p + 1, 0xAB, 3)` fills bytes `1..4` with `0xAB` on Trusted, `Mach`
and `MachTB`. -/
theorem lockstep_volatile_set_memory_fill :
    trustedVolatileAction .volatileSetMemory vbMem
        (vbTarget "core::intrinsics::volatile_set_memory" vbTyU8)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 1, .scalar ⟨0xAB, 1⟩, vbUsize 3] (vbLocals vbArr8) =
      .retStack [vbEntry 10] (vbLocals [0xAA, 0xAB, 0xAB, 0xAB, 0x12, 0xBB, 0xCC, 0xDD])
        [] [] .unit ∧
    (∃ m', mrSet (vbMach (vbPlain vbArr8)) (vbPtr 1) 0xAB 3 vbMrU8 = .ok m' ∧
      machBytes m' = [vbPlain [0xAA, 0xAB, 0xAB, 0xAB, 0x12, 0xBB, 0xCC, 0xDD]]) ∧
    (∃ m', mrSetTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) 0xAB 3 vbMrU8 = .ok m' ∧
      machBytesTB m' = [vbPlain [0xAA, 0xAB, 0xAB, 0xAB, 0x12, 0xBB, 0xCC, 0xDD]]) :=
  ⟨rfl, storedBytes_sound (by decide +kernel), storedBytesTB_sound (by decide +kernel)⟩

/-- MiniRust-side overlap predicate of `volatile_copy_nonoverlapping_memory`: the byte ranges
`[dst, dst + n)` and `[src, src + n)` of absolute addresses intersect. -/
def mrRangesOverlap (dst src : Int) (n : Nat) : Bool :=
  decide (n ≠ 0 ∧ src < dst + n ∧ dst < src + n)

/-- Trusted's overlap test on allocation-relative offsets is `mrRangesOverlap` on the absolute
addresses, for every placement `base` of the allocation. -/
theorem overlap_predicate_parity (base : Int) (srcOff dstOff n : Nat) :
    byteRangesOverlapBool srcOff n dstOff n =
      mrRangesOverlap (base + dstOff) (base + srcOff) n := by
  unfold byteRangesOverlapBool mrRangesOverlap
  rw [Bool.eq_iff_iff]
  cases n with
  | zero => simp
  | succ k =>
    have hk : Nat.beq (k + 1) 0 = false := rfl
    simp [Nat.ble_eq, hk]
    omega

/-- `volatile_copy_nonoverlapping_memory::<u8>(p + 2, p, 4)` is `.fault .ub` in Trusted, and the
MiniRust-side overlap predicate holds for the corresponding pointers; it fails for the
non-overlapping call of `lockstep_volatile_copy_dst_src_count_order`. -/
theorem lockstep_volatile_copy_nonoverlapping_overlap_ub :
    trustedVolatileAction .volatileCopyNonOverlappingMemory vbMem
        (vbTarget "core::intrinsics::volatile_copy_nonoverlapping_memory" vbTyU8)
        (vbDecls vbTyUnit) vbTbl [] [vbTPtr 2, vbTPtr 0, vbUsize 4] (vbLocals vbArr8) =
      .fault .ub ∧
    mrRangesOverlap (vbPtr 2).addr (vbPtr 0).addr 4 = true ∧
    mrRangesOverlap (vbPtrTB 2).addr (vbPtrTB 0).addr 4 = true ∧
    mrRangesOverlap (vbPtr 4).addr (vbPtr 0).addr 4 = false :=
  ⟨rfl, by decide, by decide, by decide⟩

/-! ## 7. One-way soundness on aligned addresses outside all allocations (item 5) -/

/-- A volatile load of a non-zero-sized inhabited `T` through a provenance-less address that is
aligned (when alignment is required) is `.fault .unsupported`: never a return, never
`.fault .ub`. -/
theorem trusted_volatile_load_mmio_unsupported
    (requiresAlign : Bool) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame) (activeProtectors : List Nat)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot)
    (addr : Nat) (elemTy : Ty) (size align : Nat)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hpos : 0 < align)
    (hAl : requiresAlign = true → Interp.Align.is_aligned ⟨align⟩ (addr : Int) = true)
    (hInh : rawPtrTyIsUninhabited layouts elemTy = false)
    (hSize : size ≠ 0) :
    rawPtrLoadAction true requiresAlign borrows globals callStack activeProtectors target decls
      layouts argOps [.scalar ⟨addr, layoutPointerBytes layouts⟩] locals' =
        .fault .unsupported := by
  have hSz : Nat.beq size 0 = false := by
    cases size with
    | zero => exact absurd rfl hSize
    | succ k => rfl
  cases requiresAlign with
  | false =>
    simp [rawPtrLoadAction, rawPtrArgOfValue?, Nat.beq_refl, hLay, classifyRawPtrTarget,
      trusted_unaligned_never_consults_alignment, hInh, hSz]
  | true =>
    have hA := trusted_addr_alignment_parity callStack locals' decls layouts align addr .outside
      hpos
    rw [hAl rfl] at hA
    simp [rawPtrLoadAction, rawPtrArgOfValue?, Nat.beq_refl, hLay, classifyRawPtrTarget, hA,
      hInh, hSz]

/-- A volatile store of a valid value of a non-zero-sized inhabited `T` through a provenance-less
address that is aligned (when alignment is required) is `.fault .unsupported`. -/
theorem trusted_volatile_store_mmio_unsupported
    (requiresAlign : Bool) (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame) (callerLocals : List LocalSlot)
    (activeProtectors : List Nat)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot)
    (addr : Nat) (val : Value) (elemTy : Ty) (size align : Nat)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hpos : 0 < align)
    (hAl : requiresAlign = true → Interp.Align.is_aligned ⟨align⟩ (addr : Int) = true)
    (hInh : rawPtrTyIsUninhabited layouts elemTy = false)
    (hVal : rawPtrStoreValueFault? layouts elemTy val = .none)
    (hSize : size ≠ 0) :
    rawPtrStoreAction true requiresAlign borrows globals callStack callerLocals activeProtectors
      target decls layouts argOps [.scalar ⟨addr, layoutPointerBytes layouts⟩, val] locals' =
        .fault .unsupported := by
  have hSz : Nat.beq size 0 = false := by
    cases size with
    | zero => exact absurd rfl hSize
    | succ k => rfl
  cases requiresAlign with
  | false =>
    simp [rawPtrStoreAction, rawPtrArgOfValue?, Nat.beq_refl, hLay, classifyRawPtrTarget,
      trusted_unaligned_never_consults_alignment, hInh, hVal, hSz]
  | true =>
    have hA := trusted_addr_alignment_parity callStack locals' decls layouts align addr .outside
      hpos
    rw [hAl rfl] at hA
    simp [rawPtrStoreAction, rawPtrArgOfValue?, Nat.beq_refl, hLay, classifyRawPtrTarget, hA,
      hInh, hVal, hSz]

/-- MiniRust: a non-zero-sized `BasicMemory::load` through a pointer without provenance is UB. -/
theorem mr_bm_load_no_provenance_ub (mem : Interp.BM) (addr : Int) (len : LibSpecr.Size)
    (align : LibSpecr.Align) (hAl : Interp.Align.is_aligned align addr = true)
    (hLen : len.bytes ≠ 0) :
    Interp.BM.load mem ⟨addr, none⟩ len align =
      .error (.ub "dereferencing pointer without provenance") := by
  simp [Interp.BM.load, Interp.BM.check_ptr, hAl, hLen, Interp.ub, bind, Except.bind]

/-- MiniRust: a non-zero-sized `BasicMemory::store` through a pointer without provenance is UB. -/
theorem mr_bm_store_no_provenance_ub (mem : Interp.BM) (addr : Int) (bytes : List Interp.Byte)
    (align : LibSpecr.Align) (hAl : Interp.Align.is_aligned align addr = true)
    (hLen : bytes.length ≠ 0) :
    Interp.BM.store mem ⟨addr, none⟩ bytes align =
      .error (.ub "dereferencing pointer without provenance") := by
  simp [Interp.BM.store, Interp.BM.check_ptr, hAl, hLen, Interp.ub, bind, Except.bind]

/-- MiniRust: a non-zero-sized `TreeBorrowsMemory::load` through a pointer without provenance
is UB. -/
theorem mr_tbm_load_no_provenance_ub (tbm : Interp.TBM) (addr : Int) (len : LibSpecr.Size)
    (align : LibSpecr.Align) (hAl : Interp.Align.is_aligned align addr = true)
    (hLen : len.bytes ≠ 0) :
    Interp.TreeBorrowsMemory.load tbm ⟨addr, none⟩ len align =
      .error (.ub "dereferencing pointer without provenance") := by
  simp [Interp.TreeBorrowsMemory.load, Interp.BasicMemory.load, Interp.BasicMemory.check_ptr,
    hAl, hLen, Interp.ub, bind, Except.bind]

/-- MiniRust: a non-zero-sized `TreeBorrowsMemory::store` through a pointer without provenance
is UB. -/
theorem mr_tbm_store_no_provenance_ub (tbm : Interp.TBM) (addr : Int)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (align : LibSpecr.Align) (hAl : Interp.Align.is_aligned align addr = true)
    (hLen : bytes.length ≠ 0) :
    Interp.TreeBorrowsMemory.store tbm ⟨addr, none⟩ bytes align =
      .error (.ub "dereferencing pointer without provenance") := by
  simp [Interp.TreeBorrowsMemory.store, Interp.BasicMemory.store, Interp.BasicMemory.check_ptr,
    hAl, hLen, Interp.ub, bind, Except.bind]

/-- One-way soundness of `volatile_load` on an aligned address outside all allocations: the
Trusted step is `MirStepNode.unsupported`, where MiniRust reports UB on both memories. Trusted
is the more conservative of the two: it neither returns a value nor reports UB. -/
theorem volatile_load_mmio_one_way_soundness
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align addr : Nat)
    (m : Interp.Mach) (mtb : Interp.MachTB) (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hpos : 0 < align)
    (hAl : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = true)
    (hInh : rawPtrTyIsUninhabited layouts elemTy = false)
    (hSize : size ≠ 0) (hMSize : msize.bytes ≠ 0) :
    evalVolatileMemIntrinsicCall .volatileLoad s target decls layouts argOps
        [.scalar ⟨addr, layoutPointerBytes layouts⟩] locals' destination targetBb =
      MirStepNode.unsupported ∧
    mrLoad true m ⟨addr, none⟩ mty =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrLoadTB true mtb ⟨addr, none⟩ mty =
      .error (.ub "dereferencing pointer without provenance") := by
  have hT := trusted_volatile_load_mmio_unsupported true s.memory.borrows s.memory.globals
    s.memory.callStack s.memory.activeProtectors target decls layouts argOps locals' addr elemTy
    size align hLay hpos (fun _ => hAl) hInh hSize
  have hb := mr_bm_load_no_provenance_ub m.mem.memory addr msize ⟨align⟩ hAl hMSize
  have hbTB : Interp.MemoryOps.load mtb.mem.memory
      (⟨addr, none⟩ : Gen.ThinPointer Gen.TreeBorrowsProvenance) msize ⟨align⟩ =
      .error (.ub "dereferencing pointer without provenance") :=
    mr_tbm_load_no_provenance_ub mtb.mem.memory addr msize ⟨align⟩ hAl hMSize
  refine ⟨?_, ?_, ?_⟩
  · rw [trustedVolatileAction_spec]
    simp only [trustedVolatileAction, hT]
    rfl
  · simp [mrLoad, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedLoad,
      Interp.LayoutStrategy.expect_size, Interp.CM.load, hb, bind, Except.bind, pure, Except.pure]
  · simp [mrLoadTB, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedLoadM,
      Interp.LayoutStrategy.expect_size, Interp.ConcurrentMemory.load, hbTB, bind, Except.bind,
      pure, Except.pure]

/-- A state whose step is a fault node (`MirStepNode.fail`, in particular
`MirStepNode.unsupported`) falsifies `MirNoUBTree`. -/
theorem mirStep_fail_not_noUB (body : CapturedMir) (s : MachineState) (fk : FailureKind)
    (h : stepMirFn body s = MirStepNode.fail fk) :
    ¬ MirNoUBTree (mirTree body s) := by
  intro hsafe
  have hobs : (mirTree body s).observe =
      (stepMirFn body s).map (ITree.cofix (stepMirState body)) := by
    simp [mirTree, ITree.observe_cofix, stepMirState]
  rw [h] at hobs
  exact hsafe [] (mirTree body s) (.refl _) ⟨mirTree body s, _, _, .refl _, hobs, trivial⟩

/-- One-way soundness of `volatile_store` on an aligned address outside all allocations: the
Trusted step is `MirStepNode.unsupported`, where MiniRust reports UB on both memories. -/
theorem volatile_store_mmio_one_way_soundness
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align addr : Nat) (val : Value)
    (m : Interp.Mach) (mval : Interp.Val) (mbytes : List Interp.Byte)
    (mtb : Interp.MachTB) (mvalTB : Gen.Value Interp.TBM)
    (mbytesTB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hChk : Interp.checkValue mval mty (some m) = .ok ())
    (hEnc : Interp.Type.encode mty mval = .ok mbytes)
    (hChkTB : Interp.checkValueM mvalTB mty (some mtb) = .ok ())
    (hEncTB : Interp.Type.encodeM (M := Interp.TBM) mty mvalTB = .ok mbytesTB)
    (hpos : 0 < align)
    (hAl : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = true)
    (hInh : rawPtrTyIsUninhabited layouts elemTy = false)
    (hVal : rawPtrStoreValueFault? layouts elemTy val = .none)
    (hSize : size ≠ 0) (hMLen : mbytes.length ≠ 0) (hMLenTB : mbytesTB.length ≠ 0) :
    evalVolatileMemIntrinsicCall .volatileStore s target decls layouts argOps
        [.scalar ⟨addr, layoutPointerBytes layouts⟩, val] locals' destination targetBb =
      MirStepNode.unsupported ∧
    mrStore true m ⟨addr, none⟩ mval mty =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrStoreTB true mtb ⟨addr, none⟩ mvalTB mty =
      .error (.ub "dereferencing pointer without provenance") := by
  have hT := trusted_volatile_store_mmio_unsupported true s.memory.borrows s.memory.globals
    s.memory.callStack s.memory.callerLocals s.memory.activeProtectors target decls layouts
    argOps locals' addr val elemTy size align hLay hpos (fun _ => hAl) hInh hVal hSize
  have hb := mr_bm_store_no_provenance_ub m.mem.memory addr mbytes ⟨align⟩ hAl hMLen
  have hbTB : Interp.MemoryOps.store mtb.mem.memory
      (⟨addr, none⟩ : Gen.ThinPointer Gen.TreeBorrowsProvenance) mbytesTB ⟨align⟩ =
      .error (.ub "dereferencing pointer without provenance") :=
    mr_tbm_store_no_provenance_ub mtb.mem.memory addr mbytesTB ⟨align⟩ hAl hMLenTB
  refine ⟨?_, ?_, ?_⟩
  · rw [trustedVolatileAction_spec]
    simp only [trustedVolatileAction, hT]
    rfl
  · simp [mrStore, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedStore,
      hChk, hEnc, Interp.CM.store, hb, bind, Except.bind, pure, Except.pure]
  · simp [mrStoreTB, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align,
      Interp.typedStoreM, hChkTB, hEncTB, Interp.ConcurrentMemory.store, hbTB, bind,
      Except.bind, pure, Except.pure]

/-- A caller body whose only block calls `fnPath::<tyArgs>(args) -> _0` and continues at `bb1`. -/
def vbCallBody (decls : List LocalDecl) (fnPath : String) (tyArgs : List RigidTy)
    (args : List Operand) : CapturedMir :=
  { defPath := "volatile_bridge::caller",
    phase := .runtimePostCleanup,
    role := .subject,
    argCount := 0,
    localDecls := decls,
    basicBlocks :=
      [{ statements := [],
         terminator :=
           { kind :=
               .call (.constant { ty := ⟨.fnDef fnPath tyArgs, 5⟩, val := .zeroSized }) args
                 ⟨0, []⟩ (.some 1) .continue_,
             span := "" },
         isCleanup := false }],
    fnAbi := { args := [], ret := { layout := vbLUnit, mode := .ignore },
               conv := .rust, canUnwind := false },
    layouts := vbTbl,
    allocations := [] }

/-- The state at the start of block `0` with slots `locals` and empty memory. -/
def vbState (locals : List LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := locals }, memory := {} }

/-- `_0 = fnPath::<u32>(copy _1)` with `_1 : *const u32`. -/
def vbMmioLoadBody (fnPath : String) : CapturedMir :=
  vbCallBody [vbDecl vbTyU32, vbDecl vbTyPtrU32] fnPath [.uint .u32] [.copy ⟨1, []⟩]

/-- `_0 = fnPath::<u32>(copy _1, copy _2)` with `_1 : *const u32`, `_2 : u32`. -/
def vbMmioStoreBody (fnPath : String) : CapturedMir :=
  vbCallBody [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] fnPath [.uint .u32]
    [.copy ⟨1, []⟩, .copy ⟨2, []⟩]

/-- `_1` holds the provenance-less address `addr`. -/
def vbMmioLoadState (addr : Nat) : MachineState :=
  vbState [.uninit, .init (.scalar ⟨addr, 8⟩)]

/-- `_1` holds the provenance-less address `addr`, `_2` the `u32` bit pattern `bits`. -/
def vbMmioStoreState (addr bits : Nat) : MachineState :=
  vbState [.uninit, .init (.scalar ⟨addr, 8⟩), .init (.scalar ⟨bits, 4⟩)]

/-- `stepMirFn` (through `evalTerminator`) on a call of `volatile_load::<u32>` or
`read_volatile::<u32>` at any 4-aligned provenance-less address is `MirStepNode.unsupported`. -/
theorem mmio_volatile_load_step_unsupported (addr : Nat)
    (hAl : Interp.Align.is_aligned ⟨4⟩ (addr : Int) = true) :
    stepMirFn (vbMmioLoadBody "core::intrinsics::volatile_load") (vbMmioLoadState addr) =
      MirStepNode.unsupported ∧
    stepMirFn (vbMmioLoadBody "core::ptr::read_volatile") (vbMmioLoadState addr) =
      MirStepNode.unsupported := by
  have h1 : stepMirFn (vbMmioLoadBody "core::intrinsics::volatile_load")
      (vbMmioLoadState addr) =
      evalVolatileMemIntrinsicCall .volatileLoad (vbMmioLoadState addr)
        (vbTarget "core::intrinsics::volatile_load" vbTyU32)
        [vbDecl vbTyU32, vbDecl vbTyPtrU32] vbTbl [.copy ⟨1, []⟩]
        [.scalar ⟨addr, layoutPointerBytes vbTbl⟩]
        [.uninit, .init (.scalar ⟨addr, 8⟩)] ⟨0, []⟩ 1 := rfl
  have h2 : stepMirFn (vbMmioLoadBody "core::ptr::read_volatile") (vbMmioLoadState addr) =
      evalVolatileMemIntrinsicCall .volatileLoad (vbMmioLoadState addr)
        (vbTarget "core::ptr::read_volatile" vbTyU32)
        [vbDecl vbTyU32, vbDecl vbTyPtrU32] vbTbl [.copy ⟨1, []⟩]
        [.scalar ⟨addr, layoutPointerBytes vbTbl⟩]
        [.uninit, .init (.scalar ⟨addr, 8⟩)] ⟨0, []⟩ 1 := rfl
  rw [h1, h2]
  exact ⟨(volatile_load_mmio_one_way_soundness _ _ _ _ _ _ _ _ _ 4 4 addr (vbMach [])
      (vbMachTB []) vbMrU32 ⟨4⟩ rfl rfl (by decide) hAl rfl (by decide) (by decide)).1,
    (volatile_load_mmio_one_way_soundness _ _ _ _ _ _ _ _ _ 4 4 addr (vbMach [])
      (vbMachTB []) vbMrU32 ⟨4⟩ rfl rfl (by decide) hAl rfl (by decide) (by decide)).1⟩

/-- `stepMirFn` (through `evalTerminator`) on a call of `volatile_store::<u32>` or
`write_volatile::<u32>` of any `u32` at any 4-aligned provenance-less address is
`MirStepNode.unsupported`. -/
theorem mmio_volatile_store_step_unsupported (addr bits : Nat)
    (hAl : Interp.Align.is_aligned ⟨4⟩ (addr : Int) = true) :
    stepMirFn (vbMmioStoreBody "core::intrinsics::volatile_store") (vbMmioStoreState addr bits) =
      MirStepNode.unsupported ∧
    stepMirFn (vbMmioStoreBody "core::ptr::write_volatile") (vbMmioStoreState addr bits) =
      MirStepNode.unsupported := by
  have h1 : stepMirFn (vbMmioStoreBody "core::intrinsics::volatile_store")
      (vbMmioStoreState addr bits) =
      finishRawPtrCallAction (vbMmioStoreState addr bits)
        [.uninit, .init (.scalar ⟨addr, 8⟩), .init (.scalar ⟨bits, 4⟩)] ⟨0, []⟩ 1
        (rawPtrStoreAction true true [] [] [] [] []
          (vbTarget "core::intrinsics::volatile_store" vbTyU32)
          [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] vbTbl
          [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
          [.scalar ⟨addr, layoutPointerBytes vbTbl⟩, .scalar ⟨bits, 4⟩]
          [.uninit, .init (.scalar ⟨addr, 8⟩), .init (.scalar ⟨bits, 4⟩)]) := rfl
  have h2 : stepMirFn (vbMmioStoreBody "core::ptr::write_volatile")
      (vbMmioStoreState addr bits) =
      finishRawPtrCallAction (vbMmioStoreState addr bits)
        [.uninit, .init (.scalar ⟨addr, 8⟩), .init (.scalar ⟨bits, 4⟩)] ⟨0, []⟩ 1
        (rawPtrStoreAction true true [] [] [] [] []
          (vbTarget "core::ptr::write_volatile" vbTyU32)
          [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] vbTbl
          [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
          [.scalar ⟨addr, layoutPointerBytes vbTbl⟩, .scalar ⟨bits, 4⟩]
          [.uninit, .init (.scalar ⟨addr, 8⟩), .init (.scalar ⟨bits, 4⟩)]) := rfl
  rw [h1, h2,
    trusted_volatile_store_mmio_unsupported true [] [] [] [] [] _ _ vbTbl _ _ addr _ _ 4 4 rfl
      (by decide) (fun _ => hAl) rfl rfl (by decide),
    trusted_volatile_store_mmio_unsupported true [] [] [] [] [] _ _ vbTbl _ _ addr _ _ 4 4 rfl
      (by decide) (fun _ => hAl) rfl rfl (by decide)]
  exact ⟨rfl, rfl⟩

/-- The four volatile calls at an aligned provenance-less address falsify `MirNoUBTree`: Trusted
certifies no execution of them. -/
theorem mmio_volatile_not_noUB (addr bits : Nat)
    (hAl : Interp.Align.is_aligned ⟨4⟩ (addr : Int) = true) :
    ¬ MirNoUBTree (mirTree (vbMmioLoadBody "core::intrinsics::volatile_load")
        (vbMmioLoadState addr)) ∧
    ¬ MirNoUBTree (mirTree (vbMmioLoadBody "core::ptr::read_volatile")
        (vbMmioLoadState addr)) ∧
    ¬ MirNoUBTree (mirTree (vbMmioStoreBody "core::intrinsics::volatile_store")
        (vbMmioStoreState addr bits)) ∧
    ¬ MirNoUBTree (mirTree (vbMmioStoreBody "core::ptr::write_volatile")
        (vbMmioStoreState addr bits)) :=
  ⟨mirStep_fail_not_noUB _ _ .unsupported (mmio_volatile_load_step_unsupported addr hAl).1,
   mirStep_fail_not_noUB _ _ .unsupported (mmio_volatile_load_step_unsupported addr hAl).2,
   mirStep_fail_not_noUB _ _ .unsupported (mmio_volatile_store_step_unsupported addr bits hAl).1,
   mirStep_fail_not_noUB _ _ .unsupported (mmio_volatile_store_step_unsupported addr bits hAl).2⟩

/-- A non-zero-byte volatile copy whose `dst` and `src` are aligned provenance-less addresses
(and whose byte count fits `isize::MAX`) fails closed in Trusted with `.fault .unsupported`. -/
theorem trusted_volatile_copy_mmio_unsupported
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot)
    (dstAddr srcAddr count : Nat) (elemTy : Ty) (size align : Nat)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hpos : 0 < align)
    (hDstAl : Interp.Align.is_aligned ⟨align⟩ (dstAddr : Int) = true)
    (hSrcAl : Interp.Align.is_aligned ⟨align⟩ (srcAddr : Int) = true)
    (hSmall : count * size < signedHalfModulus (layoutPointerBytes layouts))
    (hNonZero : count * size ≠ 0) :
    volatileCopyPlan borrows globals callStack target decls layouts argOps
      [.scalar ⟨dstAddr, layoutPointerBytes layouts⟩,
       .scalar ⟨srcAddr, layoutPointerBytes layouts⟩,
       .scalar ⟨count, layoutPointerBytes layouts⟩] locals' = .fault .unsupported := by
  have hBle : Nat.ble (signedHalfModulus (layoutPointerBytes layouts)) (Nat.mul count size) =
      false := by
    cases h : Nat.ble (signedHalfModulus (layoutPointerBytes layouts)) (Nat.mul count size) with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      change signedHalfModulus (layoutPointerBytes layouts) ≤ count * size at this
      omega
  have hZero : Nat.beq (Nat.mul count size) 0 = false := by
    change Nat.beq (count * size) 0 = false
    cases h : count * size with
    | zero => exact absurd h hNonZero
    | succ _ => rfl
  have hDA := trusted_addr_alignment_parity callStack locals' decls layouts align dstAddr .outside
    hpos
  rw [hDstAl] at hDA
  have hSA := trusted_addr_alignment_parity callStack locals' decls layouts align srcAddr .outside
    hpos
  rw [hSrcAl] at hSA
  unfold volatileCopyPlan
  dsimp only
  rw [Nat.beq_refl, rawPtrArgOfValue_addr, rawPtrArgOfValue_addr]
  dsimp only
  rw [hLay]
  dsimp only
  rw [hBle]
  dsimp only
  simp only [classifyRawPtrTarget, hDA, hSA, hZero]

/-- A non-zero-byte `volatile_set_memory` whose `dst` is an aligned provenance-less address
(and whose byte count fits `isize::MAX`) fails closed in Trusted with `.fault .unsupported`. -/
theorem trusted_volatile_set_mmio_unsupported
    (borrows : List BorrowEntry) (globals : List CapturedAllocation)
    (callStack : List SavedCallerFrame)
    (target : ResolvedCallTarget) (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (locals' : List LocalSlot)
    (dstAddr count : Nat) (val : UInt8) (elemTy : Ty) (size align : Nat)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hpos : 0 < align)
    (hDstAl : Interp.Align.is_aligned ⟨align⟩ (dstAddr : Int) = true)
    (hSmall : count * size < signedHalfModulus (layoutPointerBytes layouts))
    (hNonZero : count * size ≠ 0) :
    volatileSetPlan borrows globals callStack target decls layouts argOps
      [.scalar ⟨dstAddr, layoutPointerBytes layouts⟩,
       .scalar ⟨val.toNat, 1⟩,
       .scalar ⟨count, layoutPointerBytes layouts⟩] locals' = .fault .unsupported := by
  have hValLt : Nat.blt val.toNat 256 = true := Nat.ble_eq_true_of_le val.toNat_lt
  have hBle : Nat.ble (signedHalfModulus (layoutPointerBytes layouts)) (Nat.mul count size) =
      false := by
    cases h : Nat.ble (signedHalfModulus (layoutPointerBytes layouts)) (Nat.mul count size) with
    | false => rfl
    | true =>
      have := Nat.le_of_ble_eq_true h
      change signedHalfModulus (layoutPointerBytes layouts) ≤ count * size at this
      omega
  have hZero : Nat.beq (Nat.mul count size) 0 = false := by
    change Nat.beq (count * size) 0 = false
    cases h : count * size with
    | zero => exact absurd h hNonZero
    | succ _ => rfl
  have hDA := trusted_addr_alignment_parity callStack locals' decls layouts align dstAddr .outside
    hpos
  rw [hDstAl] at hDA
  unfold volatileSetPlan
  dsimp only
  rw [Nat.beq_refl, hValLt, Nat.beq_refl, Bool.and_true, Bool.and_true, rawPtrArgOfValue_addr]
  dsimp only
  rw [hLay]
  dsimp only
  rw [hBle]
  dsimp only
  simp only [classifyRawPtrTarget, hDA, hZero]

/-- One-way soundness of `volatile_copy_nonoverlapping_memory` and `volatile_copy_memory` on
aligned addresses outside all allocations: Trusted steps to `MirStepNode.unsupported` for both
intrinsics, where MiniRust (`mrCopy` / `mrCopyTB`) reports UB on both memories. -/
theorem volatile_copy_mmio_one_way_soundness
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align dstAddr srcAddr count : Nat)
    (m : Interp.Mach) (mtb : Interp.MachTB) (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hpos : 0 < align)
    (hDstAl : Interp.Align.is_aligned ⟨align⟩ (dstAddr : Int) = true)
    (hSrcAl : Interp.Align.is_aligned ⟨align⟩ (srcAddr : Int) = true)
    (hSmall : count * size < signedHalfModulus (layoutPointerBytes layouts))
    (hNonZero : count * size ≠ 0) (hMNonZero : count * msize.bytes ≠ 0) :
    evalVolatileMemIntrinsicCall .volatileCopyNonOverlappingMemory s target decls layouts argOps
        [.scalar ⟨dstAddr, layoutPointerBytes layouts⟩,
         .scalar ⟨srcAddr, layoutPointerBytes layouts⟩,
         .scalar ⟨count, layoutPointerBytes layouts⟩] locals' destination targetBb =
      MirStepNode.unsupported ∧
    evalVolatileMemIntrinsicCall .volatileCopyMemory s target decls layouts argOps
        [.scalar ⟨dstAddr, layoutPointerBytes layouts⟩,
         .scalar ⟨srcAddr, layoutPointerBytes layouts⟩,
         .scalar ⟨count, layoutPointerBytes layouts⟩] locals' destination targetBb =
      MirStepNode.unsupported ∧
    mrCopy m ⟨dstAddr, none⟩ ⟨srcAddr, none⟩ count mty =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrCopyTB mtb ⟨dstAddr, none⟩ ⟨srcAddr, none⟩ count mty =
      .error (.ub "dereferencing pointer without provenance") := by
  have hT := trusted_volatile_copy_mmio_unsupported s.memory.borrows s.memory.globals
    s.memory.callStack target decls layouts argOps locals' dstAddr srcAddr count elemTy size align
    hLay hpos hDstAl hSrcAl hSmall hNonZero
  have hb := mr_bm_load_no_provenance_ub m.mem.memory srcAddr ⟨count * msize.bytes⟩ ⟨align⟩ hSrcAl
    hMNonZero
  have hbTB : Interp.MemoryOps.load mtb.mem.memory
      (⟨srcAddr, none⟩ : Gen.ThinPointer Gen.TreeBorrowsProvenance)
      ⟨count * msize.bytes⟩ ⟨align⟩ =
      .error (.ub "dereferencing pointer without provenance") :=
    mr_tbm_load_no_provenance_ub mtb.mem.memory srcAddr ⟨count * msize.bytes⟩ ⟨align⟩ hSrcAl
      hMNonZero
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [trustedVolatileAction_spec]
    simp only [trustedVolatileAction, trustedCopyAction, hT]
    rfl
  · rw [trustedVolatileAction_spec]
    simp only [trustedVolatileAction, trustedCopyAction, hT]
    rfl
  · simp [mrCopy, hMLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
      Interp.CM.load, hb, bind, Except.bind, pure, Except.pure]
  · simp [mrCopyTB, hMLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
      Interp.ConcurrentMemory.load, hbTB, bind, Except.bind, pure, Except.pure]

/-- One-way soundness of `volatile_set_memory` on an aligned address outside all allocations:
Trusted steps to `MirStepNode.unsupported`, where MiniRust (`mrSet` / `mrSetTB`) reports UB on
both memories. -/
theorem volatile_set_mmio_one_way_soundness
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align dstAddr count : Nat) (val : UInt8)
    (m : Interp.Mach) (mtb : Interp.MachTB) (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hpos : 0 < align)
    (hDstAl : Interp.Align.is_aligned ⟨align⟩ (dstAddr : Int) = true)
    (hSmall : count * size < signedHalfModulus (layoutPointerBytes layouts))
    (hNonZero : count * size ≠ 0) (hMNonZero : count * msize.bytes ≠ 0) :
    evalVolatileMemIntrinsicCall .volatileSetMemory s target decls layouts argOps
        [.scalar ⟨dstAddr, layoutPointerBytes layouts⟩,
         .scalar ⟨val.toNat, 1⟩,
         .scalar ⟨count, layoutPointerBytes layouts⟩] locals' destination targetBb =
      MirStepNode.unsupported ∧
    mrSet m ⟨dstAddr, none⟩ val count mty =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrSetTB mtb ⟨dstAddr, none⟩ val count mty =
      .error (.ub "dereferencing pointer without provenance") := by
  have hT := trusted_volatile_set_mmio_unsupported s.memory.borrows s.memory.globals
    s.memory.callStack target decls layouts argOps locals' dstAddr count val elemTy size align
    hLay hpos hDstAl hSmall hNonZero
  have hlen : (List.replicate (count * msize.bytes)
      (Gen.AbstractByte.Init val none : Interp.Byte)).length ≠ 0 := by
    rw [List.length_replicate]; exact hMNonZero
  have hlenTB : (List.replicate (count * msize.bytes)
      (Gen.AbstractByte.Init val none : Gen.AbstractByte Gen.TreeBorrowsProvenance)).length ≠ 0 := by
    rw [List.length_replicate]; exact hMNonZero
  have hb := mr_bm_store_no_provenance_ub m.mem.memory dstAddr _ ⟨align⟩ hDstAl hlen
  have hbTB : Interp.MemoryOps.store mtb.mem.memory
      (⟨dstAddr, none⟩ : Gen.ThinPointer Gen.TreeBorrowsProvenance)
      (List.replicate (count * msize.bytes) (.Init val none)) ⟨align⟩ =
      .error (.ub "dereferencing pointer without provenance") :=
    mr_tbm_store_no_provenance_ub mtb.mem.memory dstAddr _ ⟨align⟩ hDstAl hlenTB
  refine ⟨?_, ?_, ?_⟩
  · rw [trustedVolatileAction_spec]
    simp only [trustedVolatileAction, trustedSetAction, hT]
    rfl
  · simp [mrSet, hMLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
      Interp.CM.store, hb, bind, Except.bind, pure, Except.pure]
  · simp [mrSetTB, hMLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
      Interp.ConcurrentMemory.store, hbTB, bind, Except.bind, pure, Except.pure]

/-- Symbolic misaligned-pointer parity for `core::ptr::read_volatile` and
`core::ptr::write_volatile` via `evalUnlinkedPtrAccessCall?`: when Trusted's
`rawPtrTargetAligned?` rejects alignment and MiniRust's `Align.is_aligned` is `false`, Trusted
faults with `.ub` and MiniRust reports the misaligned-load/store UB on both `Mach` and `MachTB`. -/
theorem unlinked_read_write_volatile_misaligned_parity
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (ptrVal storeVal : Value) (ptrArg : RawPtrArg) (elemTy : Ty) (size align : Nat)
    (m : Interp.Mach) (mptr : Interp.Ptr) (mval : Interp.Val) (mbytes : List Interp.Byte)
    (mtb : Interp.MachTB) (mptrTB : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (mvalTB : Gen.Value Interp.TBM)
    (mbytesTB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hArg : rawPtrArgOfValue? (layoutPointerBytes layouts) ptrVal = .some ptrArg)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMis : rawPtrTargetAligned? s.memory.callStack locals' decls layouts align ptrArg
      (classifyRawPtrTarget s.memory.borrows s.memory.globals ptrArg) = .some false)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hMMis : Interp.Align.is_aligned ⟨align⟩ mptr.addr = false)
    (hMMisTB : Interp.Align.is_aligned ⟨align⟩ mptrTB.addr = false)
    (hChk : Interp.checkValue mval mty (some m) = .ok ())
    (hEnc : Interp.Type.encode mty mval = .ok mbytes)
    (hChkTB : Interp.checkValueM mvalTB mty (some mtb) = .ok ())
    (hEncTB : Interp.Type.encodeM (M := Interp.TBM) mty mvalTB = .ok mbytesTB) :
    (target.defPath = "core::ptr::read_volatile" →
      evalUnlinkedPtrAccessCall? s target decls layouts argOps [ptrVal] locals' destination
          targetBb = some (MirStepNode.fail .ub) ∧
      mrLoad true m mptr mty = .error (.ub "load from a misaligned pointer") ∧
      mrLoadTB true mtb mptrTB mty = .error (.ub "load from a misaligned pointer")) ∧
    (target.defPath = "core::ptr::write_volatile" →
      evalUnlinkedPtrAccessCall? s target decls layouts argOps [ptrVal, storeVal] locals'
          destination targetBb = some (MirStepNode.fail .ub) ∧
      mrStore true m mptr mval mty = .error (.ub "store to a misaligned pointer") ∧
      mrStoreTB true mtb mptrTB mvalTB mty = .error (.ub "store to a misaligned pointer")) := by
  constructor
  · intro hPath
    have hT := trusted_load_misaligned_ub true s.memory.borrows s.memory.globals
      s.memory.callStack s.memory.activeProtectors target decls layouts argOps ptrVal locals'
      ptrArg elemTy size align hArg hLay hMis
    refine ⟨?_, ?_, ?_⟩
    · rw [trustedUnlinkedAction_spec]
      simp only [trustedUnlinkedAction, hPath]
      have h1 : stringEq "core::ptr::read_volatile" "core::ptr::read_unaligned" = false := rfl
      have h2 : stringEq "core::ptr::read_volatile" "core::ptr::write_unaligned" = false := rfl
      have h3 : stringEq "core::ptr::read_volatile" "core::ptr::read_volatile" = true := rfl
      rw [h1, h2, h3]
      dsimp only
      rw [hT]; rfl
    · exact mr_load_misaligned_ub m mptr mty msize ⟨align⟩ hMLay hMMis
    · exact mr_loadTB_misaligned_ub mtb mptrTB mty msize ⟨align⟩ hMLay hMMisTB
  · intro hPath
    have hT := trusted_store_misaligned_ub true s.memory.borrows s.memory.globals
      s.memory.callStack s.memory.callerLocals s.memory.activeProtectors target decls layouts
      argOps ptrVal storeVal locals' ptrArg elemTy size align hArg hLay hMis
    refine ⟨?_, ?_, ?_⟩
    · rw [trustedUnlinkedAction_spec]
      simp only [trustedUnlinkedAction, hPath]
      have h1 : stringEq "core::ptr::write_volatile" "core::ptr::read_unaligned" = false := rfl
      have h2 : stringEq "core::ptr::write_volatile" "core::ptr::write_unaligned" = false := rfl
      have h3 : stringEq "core::ptr::write_volatile" "core::ptr::read_volatile" = false := rfl
      have h4 : stringEq "core::ptr::write_volatile" "core::ptr::write_volatile" = true := rfl
      rw [h1, h2, h3, h4]
      dsimp only
      rw [hT]; rfl
    · exact mr_store_misaligned_ub m mptr mval mty mbytes msize ⟨align⟩ hMLay hChk hEnc hMMis
    · exact mr_storeTB_misaligned_ub mtb mptrTB mvalTB mty mbytesTB msize ⟨align⟩ hMLay hChkTB
        hEncTB hMMisTB

/-- Symbolic Item 5 MMIO one-way soundness for `core::ptr::read_volatile` and
`core::ptr::write_volatile` via `evalUnlinkedPtrAccessCall?`: at any aligned provenance-less
address for a non-zero-sized inhabited `T`, Trusted fails closed with `MirStepNode.unsupported`
where MiniRust reports UB on both `Mach` and `MachTB`. -/
theorem unlinked_read_write_volatile_mmio_one_way_soundness
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align addr : Nat) (val : Value)
    (m : Interp.Mach) (mval : Interp.Val) (mbytes : List Interp.Byte)
    (mtb : Interp.MachTB) (mvalTB : Gen.Value Interp.TBM)
    (mbytesTB : List (Gen.AbstractByte Gen.TreeBorrowsProvenance))
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hpos : 0 < align)
    (hAl : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = true)
    (hInh : rawPtrTyIsUninhabited layouts elemTy = false)
    (hVal : rawPtrStoreValueFault? layouts elemTy val = .none)
    (hSize : size ≠ 0) (hMSize : msize.bytes ≠ 0)
    (hChk : Interp.checkValue mval mty (some m) = .ok ())
    (hEnc : Interp.Type.encode mty mval = .ok mbytes)
    (hChkTB : Interp.checkValueM mvalTB mty (some mtb) = .ok ())
    (hEncTB : Interp.Type.encodeM (M := Interp.TBM) mty mvalTB = .ok mbytesTB)
    (hMLen : mbytes.length ≠ 0) (hMLenTB : mbytesTB.length ≠ 0) :
    (target.defPath = "core::ptr::read_volatile" →
      evalUnlinkedPtrAccessCall? s target decls layouts argOps
          [.scalar ⟨addr, layoutPointerBytes layouts⟩] locals' destination targetBb =
        some MirStepNode.unsupported ∧
      mrLoad true m ⟨addr, none⟩ mty =
        .error (.ub "dereferencing pointer without provenance") ∧
      mrLoadTB true mtb ⟨addr, none⟩ mty =
        .error (.ub "dereferencing pointer without provenance")) ∧
    (target.defPath = "core::ptr::write_volatile" →
      evalUnlinkedPtrAccessCall? s target decls layouts argOps
          [.scalar ⟨addr, layoutPointerBytes layouts⟩, val] locals' destination targetBb =
        some MirStepNode.unsupported ∧
      mrStore true m ⟨addr, none⟩ mval mty =
        .error (.ub "dereferencing pointer without provenance") ∧
      mrStoreTB true mtb ⟨addr, none⟩ mvalTB mty =
        .error (.ub "dereferencing pointer without provenance")) := by
  constructor
  · intro hPath
    have hT := trusted_volatile_load_mmio_unsupported true s.memory.borrows s.memory.globals
      s.memory.callStack s.memory.activeProtectors target decls layouts argOps locals' addr
      elemTy size align hLay hpos (fun _ => hAl) hInh hSize
    have hb := mr_bm_load_no_provenance_ub m.mem.memory addr msize ⟨align⟩ hAl hMSize
    have hbTB : Interp.MemoryOps.load mtb.mem.memory
        (⟨addr, none⟩ : Gen.ThinPointer Gen.TreeBorrowsProvenance) msize ⟨align⟩ =
        .error (.ub "dereferencing pointer without provenance") :=
      mr_tbm_load_no_provenance_ub mtb.mem.memory addr msize ⟨align⟩ hAl hMSize
    refine ⟨?_, ?_, ?_⟩
    · rw [trustedUnlinkedAction_spec]
      simp only [trustedUnlinkedAction, hPath]
      have h1 : stringEq "core::ptr::read_volatile" "core::ptr::read_unaligned" = false := rfl
      have h2 : stringEq "core::ptr::read_volatile" "core::ptr::write_unaligned" = false := rfl
      have h3 : stringEq "core::ptr::read_volatile" "core::ptr::read_volatile" = true := rfl
      rw [h1, h2, h3]
      dsimp only
      rw [hT]; rfl
    · simp [mrLoad, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedLoad,
        Interp.LayoutStrategy.expect_size, Interp.CM.load, hb, bind, Except.bind, pure, Except.pure]
    · simp [mrLoadTB, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedLoadM,
        Interp.LayoutStrategy.expect_size, Interp.ConcurrentMemory.load, hbTB, bind, Except.bind,
        pure, Except.pure]
  · intro hPath
    have hT := trusted_volatile_store_mmio_unsupported true s.memory.borrows s.memory.globals
      s.memory.callStack s.memory.callerLocals s.memory.activeProtectors target decls layouts
      argOps locals' addr val elemTy size align hLay hpos (fun _ => hAl) hInh hVal hSize
    have hb := mr_bm_store_no_provenance_ub m.mem.memory addr mbytes ⟨align⟩ hAl hMLen
    have hbTB : Interp.MemoryOps.store mtb.mem.memory
        (⟨addr, none⟩ : Gen.ThinPointer Gen.TreeBorrowsProvenance) mbytesTB ⟨align⟩ =
        .error (.ub "dereferencing pointer without provenance") :=
      mr_tbm_store_no_provenance_ub mtb.mem.memory addr mbytesTB ⟨align⟩ hAl hMLenTB
    refine ⟨?_, ?_, ?_⟩
    · rw [trustedUnlinkedAction_spec]
      simp only [trustedUnlinkedAction, hPath]
      have h1 : stringEq "core::ptr::write_volatile" "core::ptr::read_unaligned" = false := rfl
      have h2 : stringEq "core::ptr::write_volatile" "core::ptr::write_unaligned" = false := rfl
      have h3 : stringEq "core::ptr::write_volatile" "core::ptr::read_volatile" = false := rfl
      have h4 : stringEq "core::ptr::write_volatile" "core::ptr::write_volatile" = true := rfl
      rw [h1, h2, h3, h4]
      dsimp only
      rw [hT]; rfl
    · simp [mrStore, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedStore,
        hChk, hEnc, Interp.CM.store, hb, bind, Except.bind, pure, Except.pure]
    · simp [mrStoreTB, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align,
        Interp.typedStoreM, hChkTB, hEncTB, Interp.ConcurrentMemory.store, hbTB, bind,
        Except.bind, pure, Except.pure]

/-- Store-value-free misaligned-pointer parity for `core::ptr::read_volatile` via
`evalUnlinkedPtrAccessCall?`: unlike `unlinked_read_write_volatile_misaligned_parity` (which
quantifies `mval` / `mbytes` with `checkValue` and `Type.encode` across the whole conjunction),
this theorem needs no inhabitant or encodable value of `mty` and therefore applies non-vacuously to
every MiniRust type — including uninhabited enums such as `#[repr(u32)] enum Empty4 {}`, where
`checkValue` is always an error yet both Trusted and MiniRust (`typedLoad` / `typedLoadM`) still
check pointer alignment first and report misaligned-load UB. -/
theorem unlinked_read_volatile_misaligned_parity_any_ty
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (ptrVal : Value) (ptrArg : RawPtrArg) (elemTy : Ty) (size align : Nat)
    (m : Interp.Mach) (mptr : Interp.Ptr)
    (mtb : Interp.MachTB) (mptrTB : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hPath : target.defPath = "core::ptr::read_volatile")
    (hArg : rawPtrArgOfValue? (layoutPointerBytes layouts) ptrVal = .some ptrArg)
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMis : rawPtrTargetAligned? s.memory.callStack locals' decls layouts align ptrArg
      (classifyRawPtrTarget s.memory.borrows s.memory.globals ptrArg) = .some false)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hMMis : Interp.Align.is_aligned ⟨align⟩ mptr.addr = false)
    (hMMisTB : Interp.Align.is_aligned ⟨align⟩ mptrTB.addr = false) :
    evalUnlinkedPtrAccessCall? s target decls layouts argOps [ptrVal] locals' destination
        targetBb = some (MirStepNode.fail .ub) ∧
    mrLoad true m mptr mty = .error (.ub "load from a misaligned pointer") ∧
    mrLoadTB true mtb mptrTB mty = .error (.ub "load from a misaligned pointer") := by
  have hT := trusted_load_misaligned_ub true s.memory.borrows s.memory.globals
    s.memory.callStack s.memory.activeProtectors target decls layouts argOps ptrVal locals'
    ptrArg elemTy size align hArg hLay hMis
  refine ⟨?_, mr_load_misaligned_ub m mptr mty msize ⟨align⟩ hMLay hMMis,
    mr_loadTB_misaligned_ub mtb mptrTB mty msize ⟨align⟩ hMLay hMMisTB⟩
  rw [trustedUnlinkedAction_spec]
  simp only [trustedUnlinkedAction, hPath]
  have h1 : stringEq "core::ptr::read_volatile" "core::ptr::read_unaligned" = false := rfl
  have h2 : stringEq "core::ptr::read_volatile" "core::ptr::write_unaligned" = false := rfl
  have h3 : stringEq "core::ptr::read_volatile" "core::ptr::read_volatile" = true := rfl
  rw [h1, h2, h3]
  dsimp only
  rw [hT]; rfl

/-- Store-value-free Item 5 MMIO one-way soundness for `core::ptr::read_volatile` via
`evalUnlinkedPtrAccessCall?`: requires no `val`, `rawPtrStoreValueFault?`, `checkValue`, or
`Type.encode` hypotheses on either Trusted or MiniRust. -/
theorem unlinked_read_volatile_mmio_one_way_soundness
    (s : MachineState) (target : ResolvedCallTarget) (decls : List LocalDecl)
    (layouts : LayoutTable) (argOps : List Operand) (locals' : List LocalSlot)
    (destination : Place) (targetBb : BasicBlockIdx)
    (elemTy : Ty) (size align addr : Nat)
    (m : Interp.Mach) (mtb : Interp.MachTB)
    (mty : Gen.«Type») (msize : LibSpecr.Size)
    (hPath : target.defPath = "core::ptr::read_volatile")
    (hLay : resolveRawPtrElemLayout target decls layouts argOps = .ok elemTy size align)
    (hMLay : Interp.Type.layout mty = .ok (.Sized msize ⟨align⟩))
    (hpos : 0 < align)
    (hAl : Interp.Align.is_aligned ⟨align⟩ (addr : Int) = true)
    (hInh : rawPtrTyIsUninhabited layouts elemTy = false)
    (hSize : size ≠ 0) (hMSize : msize.bytes ≠ 0) :
    evalUnlinkedPtrAccessCall? s target decls layouts argOps
        [.scalar ⟨addr, layoutPointerBytes layouts⟩] locals' destination targetBb =
      some MirStepNode.unsupported ∧
    mrLoad true m ⟨addr, none⟩ mty =
      .error (.ub "dereferencing pointer without provenance") ∧
    mrLoadTB true mtb ⟨addr, none⟩ mty =
      .error (.ub "dereferencing pointer without provenance") := by
  have hT := trusted_volatile_load_mmio_unsupported true s.memory.borrows s.memory.globals
    s.memory.callStack s.memory.activeProtectors target decls layouts argOps locals' addr
    elemTy size align hLay hpos (fun _ => hAl) hInh hSize
  have hb := mr_bm_load_no_provenance_ub m.mem.memory addr msize ⟨align⟩ hAl hMSize
  have hbTB : Interp.MemoryOps.load mtb.mem.memory
      (⟨addr, none⟩ : Gen.ThinPointer Gen.TreeBorrowsProvenance) msize ⟨align⟩ =
      .error (.ub "dereferencing pointer without provenance") :=
    mr_tbm_load_no_provenance_ub mtb.mem.memory addr msize ⟨align⟩ hAl hMSize
  refine ⟨?_, ?_, ?_⟩
  · rw [trustedUnlinkedAction_spec]
    simp only [trustedUnlinkedAction, hPath]
    have h1 : stringEq "core::ptr::read_volatile" "core::ptr::read_unaligned" = false := rfl
    have h2 : stringEq "core::ptr::read_volatile" "core::ptr::write_unaligned" = false := rfl
    have h3 : stringEq "core::ptr::read_volatile" "core::ptr::read_volatile" = true := rfl
    rw [h1, h2, h3]
    dsimp only
    rw [hT]; rfl
  · simp [mrLoad, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedLoad,
      Interp.LayoutStrategy.expect_size, Interp.CM.load, hb, bind, Except.bind, pure, Except.pure]
  · simp [mrLoadTB, mrAccessAlign, hMLay, Interp.LayoutStrategy.expect_align, Interp.typedLoadM,
      Interp.LayoutStrategy.expect_size, Interp.ConcurrentMemory.load, hbTB, bind, Except.bind,
      pure, Except.pure]

/-- `_0 = fnPath::<u32>(copy _1, copy _2, copy _3)` with `_1, _2 : *const u32`, `_3 : usize`. -/
def vbMmioCopyBody (fnPath : String) : CapturedMir :=
  vbCallBody [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyPtrU32, vbDecl ⟨.uint .usize, 2⟩]
    fnPath [.uint .u32] [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩]

/-- `_0 = volatile_set_memory::<u32>(copy _1, copy _2, copy _3)`. -/
def vbMmioSetBody : CapturedMir :=
  vbCallBody [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU8, vbDecl ⟨.uint .usize, 2⟩]
    "core::intrinsics::volatile_set_memory" [.uint .u32]
    [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩]

/-- `_1 = dstAddr`, `_2 = srcAddr`, `_3 = 1usize`. -/
def vbMmioCopyState (dstAddr srcAddr : Nat) : MachineState :=
  vbState [.uninit, .init (.scalar ⟨dstAddr, 8⟩), .init (.scalar ⟨srcAddr, 8⟩),
    .init (.scalar ⟨1, 8⟩)]

/-- `_1 = dstAddr`, `_2 = val`, `_3 = 1usize`. -/
def vbMmioSetState (dstAddr : Nat) (val : UInt8) : MachineState :=
  vbState [.uninit, .init (.scalar ⟨dstAddr, 8⟩), .init (.scalar ⟨val.toNat, 1⟩),
    .init (.scalar ⟨1, 8⟩)]

/-- `stepMirFn` on `volatile_copy_nonoverlapping_memory`, `volatile_copy_memory`, and
`volatile_set_memory` at any 4-aligned provenance-less addresses (`count = 1`) is
`MirStepNode.unsupported`. -/
theorem mmio_volatile_copy_set_step_unsupported (dstAddr srcAddr : Nat) (val : UInt8)
    (hDstAl : Interp.Align.is_aligned ⟨4⟩ (dstAddr : Int) = true)
    (hSrcAl : Interp.Align.is_aligned ⟨4⟩ (srcAddr : Int) = true) :
    stepMirFn (vbMmioCopyBody "core::intrinsics::volatile_copy_nonoverlapping_memory")
        (vbMmioCopyState dstAddr srcAddr) = MirStepNode.unsupported ∧
    stepMirFn (vbMmioCopyBody "core::intrinsics::volatile_copy_memory")
        (vbMmioCopyState dstAddr srcAddr) = MirStepNode.unsupported ∧
    stepMirFn vbMmioSetBody (vbMmioSetState dstAddr val) = MirStepNode.unsupported := by
  have h1 : stepMirFn (vbMmioCopyBody "core::intrinsics::volatile_copy_nonoverlapping_memory")
      (vbMmioCopyState dstAddr srcAddr) =
      evalVolatileMemIntrinsicCall .volatileCopyNonOverlappingMemory
        (vbMmioCopyState dstAddr srcAddr)
        (vbTarget "core::intrinsics::volatile_copy_nonoverlapping_memory" vbTyU32)
        [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyPtrU32, vbDecl ⟨.uint .usize, 2⟩] vbTbl
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩]
        [.scalar ⟨dstAddr, layoutPointerBytes vbTbl⟩,
         .scalar ⟨srcAddr, layoutPointerBytes vbTbl⟩,
         .scalar ⟨1, layoutPointerBytes vbTbl⟩]
        [.uninit, .init (.scalar ⟨dstAddr, 8⟩), .init (.scalar ⟨srcAddr, 8⟩),
         .init (.scalar ⟨1, 8⟩)] ⟨0, []⟩ 1 := rfl
  have h2 : stepMirFn (vbMmioCopyBody "core::intrinsics::volatile_copy_memory")
      (vbMmioCopyState dstAddr srcAddr) =
      evalVolatileMemIntrinsicCall .volatileCopyMemory
        (vbMmioCopyState dstAddr srcAddr)
        (vbTarget "core::intrinsics::volatile_copy_memory" vbTyU32)
        [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyPtrU32, vbDecl ⟨.uint .usize, 2⟩] vbTbl
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩]
        [.scalar ⟨dstAddr, layoutPointerBytes vbTbl⟩,
         .scalar ⟨srcAddr, layoutPointerBytes vbTbl⟩,
         .scalar ⟨1, layoutPointerBytes vbTbl⟩]
        [.uninit, .init (.scalar ⟨dstAddr, 8⟩), .init (.scalar ⟨srcAddr, 8⟩),
         .init (.scalar ⟨1, 8⟩)] ⟨0, []⟩ 1 := rfl
  have h3 : stepMirFn vbMmioSetBody (vbMmioSetState dstAddr val) =
      evalVolatileMemIntrinsicCall .volatileSetMemory
        (vbMmioSetState dstAddr val)
        (vbTarget "core::intrinsics::volatile_set_memory" vbTyU32)
        [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU8, vbDecl ⟨.uint .usize, 2⟩] vbTbl
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩, .copy ⟨3, []⟩]
        [.scalar ⟨dstAddr, layoutPointerBytes vbTbl⟩,
         .scalar ⟨val.toNat, 1⟩,
         .scalar ⟨1, layoutPointerBytes vbTbl⟩]
        [.uninit, .init (.scalar ⟨dstAddr, 8⟩), .init (.scalar ⟨val.toNat, 1⟩),
         .init (.scalar ⟨1, 8⟩)] ⟨0, []⟩ 1 := rfl
  rw [h1, h2, h3]
  exact
    ⟨(volatile_copy_mmio_one_way_soundness _ _ _ _ _ _ _ _ _ 4 4 dstAddr srcAddr 1 (vbMach [])
        (vbMachTB []) vbMrU32 ⟨4⟩ rfl rfl (by decide) hDstAl hSrcAl (by decide) (by decide)
        (by decide)).1,
     (volatile_copy_mmio_one_way_soundness _ _ _ _ _ _ _ _ _ 4 4 dstAddr srcAddr 1 (vbMach [])
        (vbMachTB []) vbMrU32 ⟨4⟩ rfl rfl (by decide) hDstAl hSrcAl (by decide) (by decide)
        (by decide)).2.1,
     (volatile_set_mmio_one_way_soundness _ _ _ _ _ _ _ _ _ 4 4 dstAddr 1 val (vbMach [])
        (vbMachTB []) vbMrU32 ⟨4⟩ rfl rfl (by decide) hDstAl (by decide) (by decide)
        (by decide)).1⟩

/-- The three volatile copy/set intrinsics at aligned provenance-less addresses falsify
`MirNoUBTree`: Trusted certifies no execution of them. -/
theorem mmio_volatile_copy_set_not_noUB (dstAddr srcAddr : Nat) (val : UInt8)
    (hDstAl : Interp.Align.is_aligned ⟨4⟩ (dstAddr : Int) = true)
    (hSrcAl : Interp.Align.is_aligned ⟨4⟩ (srcAddr : Int) = true) :
    ¬ MirNoUBTree (mirTree (vbMmioCopyBody "core::intrinsics::volatile_copy_nonoverlapping_memory")
        (vbMmioCopyState dstAddr srcAddr)) ∧
    ¬ MirNoUBTree (mirTree (vbMmioCopyBody "core::intrinsics::volatile_copy_memory")
        (vbMmioCopyState dstAddr srcAddr)) ∧
    ¬ MirNoUBTree (mirTree vbMmioSetBody (vbMmioSetState dstAddr val)) :=
  ⟨mirStep_fail_not_noUB _ _ .unsupported
      (mmio_volatile_copy_set_step_unsupported dstAddr srcAddr val hDstAl hSrcAl).1,
   mirStep_fail_not_noUB _ _ .unsupported
      (mmio_volatile_copy_set_step_unsupported dstAddr srcAddr val hDstAl hSrcAl).2.1,
   mirStep_fail_not_noUB _ _ .unsupported
      (mmio_volatile_copy_set_step_unsupported dstAddr srcAddr val hDstAl hSrcAl).2.2⟩

/-! ## 8. Byte codec and bit validity (item 2) -/

/-- Trusted provenance-free initialised bytes. -/
def tPlain (bs : List UInt8) : List AbstractByte := bs.map (fun b => .init b .none)

/-- A comparison of a natural number with a power of two decides the same over `Int`. -/
private theorem ite_int_nat_lt (u e : Nat) (a b : Int) :
    (if (u : Int) < (2 : Int) ^ e then a else b) = (if u < 2 ^ e then a else b) := by
  have key : ((u : Int) < (2 : Int) ^ e) ↔ (u < 2 ^ e) := by
    have h : ((u : Int) < ((2 ^ e : Nat) : Int)) ↔ (u < 2 ^ e) := Int.ofNat_lt
    rw [Int.natCast_pow] at h
    exact h
  by_cases h : u < 2 ^ e
  · simp only [h, key.mpr h, ↓reduceIte]
  · have h' : ¬ ((u : Int) < (2 : Int) ^ e) := fun h' => h (key.mp h')
    simp only [h, h', ↓reduceIte]

/-- MiniRust's little-endian `Endianness::decode` of `bs` is `intFromBits` of the little-endian
value of `bs`, for both signednesses and every length. -/
theorem mr_endianness_decode_eq_intFromBits (sg : LibSpecr.Signedness) (bs : List UInt8) :
    Interp.Endianness.decode .LittleEndian sg bs =
      intFromBits (Interp.leValue bs) ⟨sg, ⟨bs.length⟩⟩ := by
  cases sg with
  | Unsigned => rfl
  | Signed => exact ite_int_nat_lt (Interp.leValue bs) (8 * bs.length - 1) _ _

/-- Decode agreement at the MIR integer type `ty` on the provenance-free bytes `bs`: Trusted's
raw-pointer decode yields the scalar with bits `leValue bs`, and MiniRust's `Type::decode` at
the translated integer type yields the corresponding integer (`intFromBits`). -/
def IntDecodeAgree (layouts : LayoutTable) (ty : Ty) (bs : List UInt8) : Prop :=
  ∃ it, intTypeOf ty = some it ∧ it.size.bytes = bs.length ∧
    rawPtrDecodeBytes layouts ty (tPlain bs) =
      .ok (.scalar ⟨Interp.leValue bs, bs.length⟩) ∧
    Interp.Type.decode (.Int it) (vbPlain bs) =
      .ok (some (.Int (intFromBits (Interp.leValue bs) it)))

/-- `IntDecodeAgree` from the two decodes. -/
private theorem intDecodeAgree_of (layouts : LayoutTable) (ty : Ty) (sg : LibSpecr.Signedness)
    (bs : List UInt8)
    (hit : intTypeOf ty = some ⟨sg, ⟨bs.length⟩⟩)
    (hT : rawPtrDecodeBytes layouts ty (tPlain bs) =
      .ok (.scalar ⟨Interp.leValue bs, bs.length⟩))
    (hM : Interp.Type.decode (.Int ⟨sg, ⟨bs.length⟩⟩) (vbPlain bs) =
      .ok (some (.Int (Interp.Endianness.decode .LittleEndian sg bs)))) :
    IntDecodeAgree layouts ty bs :=
  ⟨_, hit, rfl, hT, by rw [hM, mr_endianness_decode_eq_intFromBits]⟩

/-- Decode agreement for all bytes, at the unsigned and signed integer types of width 1, 2, 4,
8 and 16 bytes, for every little-endian layout table. -/
theorem codec_int_decode_agreement (layouts : LayoutTable) (idx : LayoutIdx)
    (hLE : layouts.isLittleEndian = true)
    (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : UInt8) :
    IntDecodeAgree layouts ⟨.uint .u8, idx⟩ [b0] ∧
    IntDecodeAgree layouts ⟨.int .i8, idx⟩ [b0] ∧
    IntDecodeAgree layouts ⟨.uint .u16, idx⟩ [b0, b1] ∧
    IntDecodeAgree layouts ⟨.int .i16, idx⟩ [b0, b1] ∧
    IntDecodeAgree layouts ⟨.uint .u32, idx⟩ [b0, b1, b2, b3] ∧
    IntDecodeAgree layouts ⟨.int .i32, idx⟩ [b0, b1, b2, b3] ∧
    IntDecodeAgree layouts ⟨.uint .u64, idx⟩ [b0, b1, b2, b3, b4, b5, b6, b7] ∧
    IntDecodeAgree layouts ⟨.int .i64, idx⟩ [b0, b1, b2, b3, b4, b5, b6, b7] ∧
    IntDecodeAgree layouts ⟨.uint .u128, idx⟩
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] ∧
    IntDecodeAgree layouts ⟨.int .i128, idx⟩
      [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact intDecodeAgree_of _ _ _ _ rfl (by simp only [rawPtrDecodeBytes, hLE]; rfl) rfl

/-- A MiniRust type with the validity invariant of `NonZeroU32`: an enum with one variant
`u32` whose discriminator branches on the 4-byte value and is `Invalid` outside `1..2^32`. -/
def vbMrNonZeroU32 : Gen.«Type» :=
  .Enum ⟨[(0, ⟨vbMrU32, ⟨[]⟩⟩)]⟩ ⟨.Unsigned, ⟨4⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨4⟩⟩ .Invalid ⟨[((1, 4294967296), .Known 0)]⟩) ⟨4⟩ ⟨4⟩

/-- A MiniRust type with the validity invariant of `char`: an enum with one variant `u32` whose
discriminator is `Invalid` outside `0..0xD800` and `0xE000..0x110000`. -/
def vbMrChar : Gen.«Type» :=
  .Enum ⟨[(0, ⟨vbMrU32, ⟨[]⟩⟩)]⟩ ⟨.Unsigned, ⟨4⟩⟩
    (.Branch ⟨0⟩ ⟨.Unsigned, ⟨4⟩⟩ .Invalid
      ⟨[((0, 0xD800), .Known 0), ((0xE000, 0x110000), .Known 0)]⟩) ⟨4⟩ ⟨4⟩

/-- MiniRust's translation of `!`: the enum without variants. -/
def vbMrNever : Gen.«Type» := .Enum ⟨[]⟩ ⟨.Unsigned, ⟨1⟩⟩ .Invalid ⟨0⟩ ⟨1⟩

/-- `r` is the Trusted decode fault `.ub`. -/
def tDecodeIsUb : RawPtrLoadResult → Bool
  | .fault .ub => true
  | _ => false

/-- `r` is MiniRust's "no value of this type" decode result `.ok none` (UB on a typed load). -/
def mDecodeIsInvalid : Interp.Interp (Option Interp.Val) → Bool
  | .ok none => true
  | _ => false

/-- `tDecodeIsUb r = true` means `r = .fault .ub`. -/
theorem tDecodeIsUb_sound {r : RawPtrLoadResult} (h : tDecodeIsUb r = true) :
    r = .fault .ub := by
  cases r with
  | ok v => cases h
  | fault k => cases k <;> first | rfl | cases h

/-- `mDecodeIsInvalid r = true` means `r = .ok none`. -/
theorem mDecodeIsInvalid_sound {r : Interp.Interp (Option Interp.Val)}
    (h : mDecodeIsInvalid r = true) : r = .ok none := by
  cases r with
  | error e => cases h
  | ok o =>
    cases o with
    | none => rfl
    | some v => cases h

/-- `bool` validity for every byte value `n < 256`: `0` and `1` decode to `false` and `true` on
both sides, and every other byte is `.fault .ub` in Trusted and "no value" in MiniRust. -/
theorem codec_bool_validity_all_bytes (n : Nat) (hn : n < 256) :
    (n ≤ 1 →
      rawPtrDecodeBytes vbTbl vbTyBool (tPlain [UInt8.ofNat n]) = .ok (.scalar ⟨n, 1⟩) ∧
      Interp.Type.decode .Bool (vbPlain [UInt8.ofNat n]) =
        .ok (some (.Bool (decide (n = 1))))) ∧
    (1 < n →
      rawPtrDecodeBytes vbTbl vbTyBool (tPlain [UInt8.ofNat n]) = .fault .ub ∧
      Interp.Type.decode .Bool (vbPlain [UInt8.ofNat n]) = .ok none) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h01 : n = 0 ∨ n = 1 := by omega
    rcases h01 with rfl | rfl <;> exact ⟨rfl, rfl⟩
  · have all : ∀ k, k < 256 → 1 < k →
        tDecodeIsUb (rawPtrDecodeBytes vbTbl vbTyBool (tPlain [UInt8.ofNat k])) = true ∧
        mDecodeIsInvalid (Interp.Type.decode .Bool (vbPlain [UInt8.ofNat k])) = true := by
      decide +kernel
    exact ⟨tDecodeIsUb_sound (all n hn h).1, mDecodeIsInvalid_sound (all n hn h).2⟩

/-- `bool` validity for every byte value `n < 256`, generalized over every little-endian
`LayoutTable` and `LayoutIdx`. -/
theorem codec_bool_validity_all_bytes_general (layouts : LayoutTable) (idx : LayoutIdx)
    (hLE : layouts.isLittleEndian = true) (n : Nat) (hn : n < 256) :
    (n ≤ 1 →
      rawPtrDecodeBytes layouts ⟨.bool, idx⟩ (tPlain [UInt8.ofNat n]) = .ok (.scalar ⟨n, 1⟩) ∧
      Interp.Type.decode .Bool (vbPlain [UInt8.ofNat n]) =
        .ok (some (.Bool (decide (n = 1))))) ∧
    (1 < n →
      rawPtrDecodeBytes layouts ⟨.bool, idx⟩ (tPlain [UInt8.ofNat n]) = .fault .ub ∧
      Interp.Type.decode .Bool (vbPlain [UInt8.ofNat n]) = .ok none) := by
  have heq : rawPtrDecodeBytes layouts ⟨.bool, idx⟩ (tPlain [UInt8.ofNat n]) =
      rawPtrDecodeBytes vbTbl vbTyBool (tPlain [UInt8.ofNat n]) := by
    simp only [rawPtrDecodeBytes, hLE, vbTbl, vbTyBool]
    rfl
  rw [heq]
  exact codec_bool_validity_all_bytes n hn

/-- A `u32` with one uninitialised byte, at any of the four positions and whatever the other
bytes are, is `.fault .ub` in Trusted and "no value" in MiniRust. -/
theorem codec_uninit_byte_invalid (b0 b1 b2 : UInt8) :
    rawPtrDecodeBytes vbTbl vbTyU32 [.uninit, .init b0 .none, .init b1 .none, .init b2 .none] =
      .fault .ub ∧
    rawPtrDecodeBytes vbTbl vbTyU32 [.init b0 .none, .uninit, .init b1 .none, .init b2 .none] =
      .fault .ub ∧
    rawPtrDecodeBytes vbTbl vbTyU32 [.init b0 .none, .init b1 .none, .uninit, .init b2 .none] =
      .fault .ub ∧
    rawPtrDecodeBytes vbTbl vbTyU32 [.init b0 .none, .init b1 .none, .init b2 .none, .uninit] =
      .fault .ub ∧
    Interp.Type.decode vbMrU32 [.Uninit, .Init b0 none, .Init b1 none, .Init b2 none] =
      .ok none ∧
    Interp.Type.decode vbMrU32 [.Init b0 none, .Uninit, .Init b1 none, .Init b2 none] =
      .ok none ∧
    Interp.Type.decode vbMrU32 [.Init b0 none, .Init b1 none, .Uninit, .Init b2 none] =
      .ok none ∧
    Interp.Type.decode vbMrU32 [.Init b0 none, .Init b1 none, .Init b2 none, .Uninit] =
      .ok none :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `r.toOption = some a` means `r = .ok a`. -/
theorem interp_ok_of_toOption {α : Type} {r : Interp.Interp α} {a : α}
    (h : r.toOption = some a) : r = .ok a := by
  cases r with
  | error e => cases h
  | ok x =>
    simp only [Except.toOption, Option.some.injEq] at h
    rw [h]

/-- The integer a MiniRust decode produced (`none` if it produced anything else). -/
def decodedInt? : Interp.Interp (Option Interp.Val) → Option Int
  | .ok (some (.Int i)) => some i
  | _ => none

/-- `decodedInt? r = some i` means `r = .ok (some (Value::Int i))`. -/
theorem decodedInt_sound {r : Interp.Interp (Option Interp.Val)} {i : Int}
    (h : decodedInt? r = some i) : r = .ok (some (.Int i)) := by
  cases r with
  | error e => cases h
  | ok o =>
    cases o with
    | none => cases h
    | some v =>
      cases v with
      | Int j =>
        simp only [decodedInt?, Option.some.injEq] at h
        rw [h]
      | _ => cases h

/-- `i32`. -/
def vbTyI32 : Ty := ⟨.int .i32, 1⟩

/-- MiniRust `i32`. -/
def vbMrI32 : Gen.«Type» := .Int ⟨.Signed, ⟨4⟩⟩

/-- Concrete encode and decode lockstep for `0x12345678u32` and `-6i32`. -/
theorem lockstep_int_encode_round_trip :
    -- `0x12345678u32`
    rawPtrEncodeValue? [] vbTbl vbTyU32 (.scalar ⟨0x12345678, 4⟩) =
      .some (tPlain [0x78, 0x56, 0x34, 0x12]) ∧
    Interp.Type.encode vbMrU32 (.Int (intFromBits 0x12345678 ⟨.Unsigned, ⟨4⟩⟩)) =
      .ok (vbPlain [0x78, 0x56, 0x34, 0x12]) ∧
    rawPtrDecodeBytes vbTbl vbTyU32 (tPlain [0x78, 0x56, 0x34, 0x12]) =
      .ok (.scalar ⟨0x12345678, 4⟩) ∧
    Interp.Type.decode vbMrU32 (vbPlain [0x78, 0x56, 0x34, 0x12]) =
      .ok (some (.Int (intFromBits 0x12345678 ⟨.Unsigned, ⟨4⟩⟩))) ∧
    -- `-6i32`, bit pattern `0xFFFFFFFA`
    intFromBits 0xFFFFFFFA ⟨.Signed, ⟨4⟩⟩ = -6 ∧
    rawPtrEncodeValue? [] vbTbl vbTyI32 (.scalar ⟨0xFFFFFFFA, 4⟩) =
      .some (tPlain [0xFA, 0xFF, 0xFF, 0xFF]) ∧
    Interp.Type.encode vbMrI32 (.Int (-6)) = .ok (vbPlain [0xFA, 0xFF, 0xFF, 0xFF]) ∧
    rawPtrDecodeBytes vbTbl vbTyI32 (tPlain [0xFA, 0xFF, 0xFF, 0xFF]) =
      .ok (.scalar ⟨0xFFFFFFFA, 4⟩) ∧
    Interp.Type.decode vbMrI32 (vbPlain [0xFA, 0xFF, 0xFF, 0xFF]) = .ok (some (.Int (-6))) := by
  exact ⟨rfl, interp_ok_of_toOption (by decide +kernel), rfl,
    decodedInt_sound (by decide +kernel), by decide, rfl,
    interp_ok_of_toOption (by decide +kernel), rfl, decodedInt_sound (by decide +kernel)⟩

/-- Trusted initialised bytes carrying the provenance `(allocId, tag)`. -/
def tProv (allocId tag : Nat) (bs : List UInt8) : List AbstractByte :=
  bs.map (fun b => .init b (.some (allocId, tag)))

/-- The pointer a MiniRust decode produced (`none` if it produced anything else). -/
def decodedPtr? : Interp.Interp (Option Interp.Val) → Option (Gen.Pointer Interp.Prov)
  | .ok (some (.Ptr p)) => some p
  | _ => none

/-- `decodedPtr? r = some p` means `r = .ok (some (Value::Ptr p))`. -/
theorem decodedPtr_sound {r : Interp.Interp (Option Interp.Val)} {p : Gen.Pointer Interp.Prov}
    (h : decodedPtr? r = some p) : r = .ok (some (.Ptr p)) := by
  cases r with
  | error e => cases h
  | ok o =>
    cases o with
    | none => cases h
    | some v =>
      cases v with
      | Ptr q =>
        simp only [decodedPtr?, Option.some.injEq] at h
        rw [h]
      | _ => cases h

/-- Pointer bytes. A pointer with provenance round-trips through its bytes on both sides;
provenance-free bytes decode to a provenance-less address on both sides; pointer bytes read at
an integer type fail closed in Trusted and lose their provenance in MiniRust. -/
theorem lockstep_pointer_bytes_provenance :
    -- Trusted: allocation-relative offset in the byte values, `(allocId, tag)` on every byte.
    rawPtrEncodeValue? [] vbTbl vbTyPtrU32 (.ptr ⟨10, 4⟩ 8) =
      .some (tProv 10 10 [4, 0, 0, 0, 0, 0, 0, 0]) ∧
    rawPtrDecodeBytes vbTbl vbTyPtrU32 (tProv 10 10 [4, 0, 0, 0, 0, 0, 0, 0]) =
      .ok (.ptr ⟨10, 4⟩ 8) ∧
    -- MiniRust: absolute address `vbBase + 4` in the byte values, one fragment per byte.
    Interp.Type.encode (.Ptr (.Raw .None)) (.Ptr ⟨vbPtr 4, none⟩) =
      .ok (Interp.encodePtrBytes (some (⟨0⟩, ())) 0 [4, 0, 0, 0, 1, 0, 0, 0]) ∧
    Interp.Type.decode (.Ptr (.Raw .None))
        (Interp.encodePtrBytes (some (⟨0⟩, ())) 0 [4, 0, 0, 0, 1, 0, 0, 0]) =
      .ok (some (.Ptr ⟨vbPtr 4, none⟩)) ∧
    -- Provenance-free bytes at a raw-pointer type: a provenance-less address on both sides.
    rawPtrDecodeBytes vbTbl vbTyPtrU32 (tPlain [4, 0, 0, 0, 1, 0, 0, 0]) =
      .ok (.scalar ⟨0x100000004, 8⟩) ∧
    Interp.Type.decode (.Ptr (.Raw .None)) (vbPlain [4, 0, 0, 0, 1, 0, 0, 0]) =
      .ok (some (.Ptr ⟨⟨0x100000004, none⟩, none⟩)) ∧
    -- Pointer bytes at an integer type: Trusted fails closed, MiniRust drops the provenance.
    rawPtrDecodeBytes vbTbl ⟨.uint .usize, 2⟩ (tProv 10 10 [4, 0, 0, 0, 0, 0, 0, 0]) =
      .fault .unsupported ∧
    Interp.Type.decode (.Int ⟨.Unsigned, ⟨8⟩⟩)
        (Interp.encodePtrBytes (some (⟨0⟩, ())) 0 [4, 0, 0, 0, 1, 0, 0, 0]) =
      .ok (some (.Int 0x100000004)) :=
  ⟨rfl, rfl, interp_ok_of_toOption (by decide +kernel), decodedPtr_sound (by decide +kernel),
   rfl, decodedPtr_sound (by decide +kernel), rfl, decodedInt_sound (by decide +kernel)⟩

/-- Bytes whose bytes `1..5` are zero. -/
def vbZeroMid : List UInt8 := [0xAA, 0x00, 0x00, 0x00, 0x00, 0x07, 0x00, 0x00]

/-- `NonZeroU32`. The value `0` is invalid on both sides: Trusted's validity predicate rejects
it and storing it is `.fault .ub`; MiniRust's niche type has no value for the zero bytes, so a
typed load of them is UB. Trusted's load of the zero bytes through the byte decoder fails
closed (`.fault .unsupported`). -/
theorem lockstep_nonzero_validity :
    rawPtrValueValid? 16 vbTbl vbTyNonZeroU32 (.scalar ⟨0, 4⟩) = .some false ∧
    rawPtrValueValid? 16 vbTbl vbTyNonZeroU32 (.scalar ⟨7, 4⟩) = .some true ∧
    rawPtrDecodeBytes vbTbl vbTyNonZeroU32 (tPlain [7, 0, 0, 0]) = .ok (.scalar ⟨7, 4⟩) ∧
    Interp.Type.decode vbMrNonZeroU32 (vbPlain [7, 0, 0, 0]) =
      .ok (some (.Variant 0 (.Int 7))) ∧
    rawPtrDecodeBytes vbTbl vbTyNonZeroU32 (tPlain [0, 0, 0, 0]) = .fault .unsupported ∧
    Interp.Type.decode vbMrNonZeroU32 (vbPlain [0, 0, 0, 0]) = .ok none ∧
    trustedVolatileAction .unalignedVolatileStore vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyNonZeroU32)
        [vbDecl vbTyUnit, vbDecl vbTyArrU8_8, vbDecl vbTyNonZeroU32] vbTbl []
        [vbTPtr 1, .scalar ⟨0, 4⟩] (vbLocals vbArr8) = .fault .ub ∧
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyNonZeroU32)
        [vbDecl vbTyNonZeroU32, vbDecl vbTyArrU8_8] vbTbl []
        [vbTPtr 1] (vbLocals vbZeroMid) = .fault .unsupported ∧
    mrLoad false (vbMach (vbPlain vbZeroMid)) (vbPtr 1) vbMrNonZeroU32 =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    mrLoadTB false (vbMachTB (vbPlain vbZeroMid)) (vbPtrTB 1) vbMrNonZeroU32 =
      .error (.ub "load at type but the data in memory violates the language invariant") :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The `(discriminant, integer payload)` of the enum value a MiniRust decode produced. -/
def decodedVariantInt? : Interp.Interp (Option Interp.Val) → Option (Int × Int)
  | .ok (some (.Variant d (.Int i))) => some (d, i)
  | _ => none

/-- `decodedVariantInt? r = some (d, i)` means
`r = .ok (some (Value::Variant d (Value::Int i)))`. -/
theorem decodedVariantInt_sound {r : Interp.Interp (Option Interp.Val)} {d i : Int}
    (h : decodedVariantInt? r = some (d, i)) : r = .ok (some (.Variant d (.Int i))) := by
  cases r with
  | error e => cases h
  | ok o =>
    cases o with
    | none => cases h
    | some v =>
      cases v with
      | Variant d' data =>
        cases data with
        | Int j =>
          simp only [decodedVariantInt?, Option.some.injEq, Prod.mk.injEq] at h
          rw [h.1, h.2]
        | _ => cases h
      | _ => cases h

/-- `char`. MiniRust has no `char` type (`translateTy` rejects it). Against the niche type
`vbMrChar`, surrogates and out-of-range code points are invalid on both sides and the
neighbouring scalar values are valid on both; at MiniRust's plain `u32` the surrogate bit
pattern is an ordinary integer. -/
theorem lockstep_char_validity :
    translateTy vbTbl vbTyChar = none ∧
    -- surrogates and out-of-range code points are invalid on both sides
    rawPtrDecodeBytes vbTbl vbTyChar (tPlain [0x00, 0xD8, 0x00, 0x00]) = .fault .ub ∧
    Interp.Type.decode vbMrChar (vbPlain [0x00, 0xD8, 0x00, 0x00]) = .ok none ∧
    rawPtrDecodeBytes vbTbl vbTyChar (tPlain [0xFF, 0xDF, 0x00, 0x00]) = .fault .ub ∧
    Interp.Type.decode vbMrChar (vbPlain [0xFF, 0xDF, 0x00, 0x00]) = .ok none ∧
    rawPtrDecodeBytes vbTbl vbTyChar (tPlain [0x00, 0x00, 0x11, 0x00]) = .fault .ub ∧
    Interp.Type.decode vbMrChar (vbPlain [0x00, 0x00, 0x11, 0x00]) = .ok none ∧
    -- the neighbouring scalar values are valid on both sides
    rawPtrDecodeBytes vbTbl vbTyChar (tPlain [0xFF, 0xD7, 0x00, 0x00]) =
      .ok (.scalar ⟨0xD7FF, 4⟩) ∧
    Interp.Type.decode vbMrChar (vbPlain [0xFF, 0xD7, 0x00, 0x00]) =
      .ok (some (.Variant 0 (.Int 0xD7FF))) ∧
    rawPtrDecodeBytes vbTbl vbTyChar (tPlain [0x00, 0xE0, 0x00, 0x00]) =
      .ok (.scalar ⟨0xE000, 4⟩) ∧
    Interp.Type.decode vbMrChar (vbPlain [0x00, 0xE0, 0x00, 0x00]) =
      .ok (some (.Variant 0 (.Int 0xE000))) ∧
    rawPtrDecodeBytes vbTbl vbTyChar (tPlain [0xFF, 0xFF, 0x10, 0x00]) =
      .ok (.scalar ⟨0x10FFFF, 4⟩) ∧
    Interp.Type.decode vbMrChar (vbPlain [0xFF, 0xFF, 0x10, 0x00]) =
      .ok (some (.Variant 0 (.Int 0x10FFFF))) ∧
    -- at MiniRust's plain `u32` the surrogate bit pattern is an ordinary integer
    Interp.Type.decode vbMrU32 (vbPlain [0x00, 0xD8, 0x00, 0x00]) = .ok (some (.Int 0xD800)) :=
  ⟨rfl, rfl, mDecodeIsInvalid_sound (by decide +kernel),
   rfl, mDecodeIsInvalid_sound (by decide +kernel),
   rfl, mDecodeIsInvalid_sound (by decide +kernel),
   rfl, decodedVariantInt_sound (by decide +kernel),
   rfl, decodedVariantInt_sound (by decide +kernel),
   rfl, decodedVariantInt_sound (by decide +kernel),
   decodedInt_sound (by decide +kernel)⟩

/-- Bytes starting `0x00, 0x01, 0x02`. -/
def vbBoolBytes : List UInt8 := [0x00, 0x01, 0x02, 0xAA, 0x12, 0xBB, 0xCC, 0xDD]

/-- An unaligned `bool` load of the byte `2` is UB on Trusted, `Mach` and `MachTB`; of the byte
`1` it is `true` on all three. -/
theorem lockstep_bool_invalid_bit_pattern_ub :
    -- byte `2` is not a `bool`: UB on all three
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyBool) (vbDecls vbTyBool) vbTbl
        [] [vbTPtr 2] (vbLocals vbBoolBytes) = .fault .ub ∧
    mrLoad false (vbMach (vbPlain vbBoolBytes)) (vbPtr 2) .Bool =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    mrLoadTB false (vbMachTB (vbPlain vbBoolBytes)) (vbPtrTB 2) .Bool =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    -- byte `1` is `true` on all three
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyBool) (vbDecls vbTyBool) vbTbl
        [] [vbTPtr 1] (vbLocals vbBoolBytes) = .retBorrows [vbEntry 10] (.scalar ⟨1, 1⟩) ∧
    mrLoad false (vbMach (vbPlain vbBoolBytes)) (vbPtr 1) .Bool =
      .ok (.Bool true, vbLog (vbMach (vbPlain vbBoolBytes)) [⟨.Load, .None, vbBase + 1, ⟨1⟩⟩]) ∧
    mrLoadTB false (vbMachTB (vbPlain vbBoolBytes)) (vbPtrTB 1) .Bool =
      .ok (.Bool true,
        vbLog (vbMachTB (vbPlain vbBoolBytes)) [⟨.Load, .None, vbBase + 1, ⟨1⟩⟩]) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The uninhabited `!`. An unaligned load at `!` is UB on all three. An unaligned store at `!`
is `.fault .ub` in Trusted; MiniRust has no value of the empty enum, so every store at that
type is a specification panic on both memories. -/
theorem lockstep_never_uninhabited :
    trustedVolatileAction .unalignedVolatileLoad vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyNever)
        [vbDecl vbTyNever, vbDecl vbTyArrU8_8] vbTbl [] [vbTPtr 1] (vbLocals vbArr8) =
      .fault .ub ∧
    trustedVolatileAction .unalignedVolatileStore vbMem
        (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyNever)
        [vbDecl vbTyUnit, vbDecl vbTyArrU8_8, vbDecl vbTyNever] vbTbl [] [vbTPtr 1, .unit]
        (vbLocals vbArr8) = .fault .ub ∧
    mrLoad false (vbMach (vbPlain vbArr8)) (vbPtr 1) vbMrNever =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    mrLoadTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB 1) vbMrNever =
      .error (.ub "load at type but the data in memory violates the language invariant") ∧
    (∀ (m : Interp.Mach) (ptr : Interp.Ptr) (v : Interp.Val),
      mrStore false m ptr v vbMrNever =
        .error (.specPanic "trying to store a value which is ill-formed for its type")) ∧
    (∀ (m : Interp.MachTB) (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
        (v : Gen.Value Interp.TBM),
      mrStoreTB false m ptr v vbMrNever =
        .error (.specPanic "trying to store a value which is ill-formed for its type")) :=
  ⟨rfl, rfl, rfl, rfl, fun m ptr v => by cases v <;> rfl, fun m ptr v => by cases v <;> rfl⟩

/-! ## 9. The MiniRust copy model is `memmove`, the set model a fill (item 4) -/

/-- `BasicMemory::check_ptr` of a non-zero-sized in-bounds access into the live allocation `a`
returns its offset. -/
theorem mr_bm_check_ptr_in_bounds (mem : Interp.BM) (ptr : Interp.Ptr) (n : Nat)
    (i : Nat) (a : Gen.Allocation) (o : Nat)
    (hn : n ≠ 0)
    (hprov : ptr.provenance = some (⟨(i : Int)⟩, ()))
    (hget : mem.allocations[i]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr + (o : Int)) (hbound : o + n ≤ a.data.length) :
    Interp.BM.check_ptr mem ptr ⟨n⟩ = .ok (some (⟨(i : Int)⟩, (), ⟨o⟩)) := by
  have hoff : a.addr + (o : Int) - a.addr = (o : Int) := by
    rw [Int.add_comm]; exact Int.add_sub_cancel _ _
  simp [Interp.BM.check_ptr, hn, hprov, Interp.listIndex, hget, hlive, haddr, hoff,
    Interp.Allocation.size, bind, Except.bind, pure, Except.pure]
  intro h
  omega

/-- A non-zero-sized aligned in-bounds `BasicMemory::load` returns the bytes of the allocation at
the pointer's offset and leaves the memory unchanged. -/
theorem mr_bm_load_in_bounds (mem : Interp.BM) (ptr : Interp.Ptr) (n : Nat)
    (align : LibSpecr.Align) (i : Nat) (a : Gen.Allocation) (o : Nat)
    (hn : n ≠ 0)
    (hal : Interp.Align.is_aligned align ptr.addr = true)
    (hprov : ptr.provenance = some (⟨(i : Int)⟩, ()))
    (hget : mem.allocations[i]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr + (o : Int)) (hbound : o + n ≤ a.data.length) :
    Interp.BM.load mem ptr ⟨n⟩ align = .ok ((a.data.drop o).take n, mem) := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp hget
  have hset : mem.allocations.set i a = mem.allocations := by
    rw [← hai]; exact List.set_getElem_self hi
  have hck := mr_bm_check_ptr_in_bounds mem ptr n i a o hn hprov hget hlive haddr hbound
  have hb' : (o : Int) + (n : Int) ≤ (a.data.length : Int) := by omega
  simp [Interp.BM.load, hal, hck, Interp.listIndex, Interp.listSet, hi, hai, hset,
    Interp.subsliceWithLength, hb', bind, Except.bind, pure, Except.pure]

/-- A non-empty aligned in-bounds `BasicMemory::store` splices the bytes into the allocation at
the pointer's offset and changes nothing else. -/
theorem mr_bm_store_in_bounds (mem : Interp.BM) (ptr : Interp.Ptr) (bytes : List Interp.Byte)
    (align : LibSpecr.Align) (i : Nat) (a : Gen.Allocation) (o : Nat)
    (hn : bytes.length ≠ 0)
    (hal : Interp.Align.is_aligned align ptr.addr = true)
    (hprov : ptr.provenance = some (⟨(i : Int)⟩, ()))
    (hget : mem.allocations[i]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr + (o : Int)) (hbound : o + bytes.length ≤ a.data.length) :
    Interp.BM.store mem ptr bytes align =
      .ok { mem with
            allocations := mem.allocations.set i
              { a with data := a.data.take o ++ bytes ++ a.data.drop (o + bytes.length) } } := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp hget
  have hck := mr_bm_check_ptr_in_bounds mem ptr bytes.length i a o hn hprov hget hlive haddr
    hbound
  have hb' : (o : Int) + (bytes.length : Int) ≤ (a.data.length : Int) := by omega
  simp [Interp.BM.store, hal, hck, Interp.listIndex, Interp.listSet, hi, hai,
    Interp.writeSubsliceAtIndex, hb', bind, Except.bind, pure, Except.pure]

/-- The MiniRust copy model is a `memmove`. For source and destination ranges inside one live
allocation with data `d`, in any relative position (disjoint, forward or backward overlap),
`mrCopy` succeeds and the allocation's data becomes
`d.take dstOff ++ (d.drop srcOff).take n ++ d.drop (dstOff + n)`: the destination receives the
source bytes of `d` as they were before the call. -/
theorem mr_copy_is_memmove (m : Interp.Mach) (dst src : Interp.Ptr) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (i : Nat) (a : Gen.Allocation) (srcOff dstOff : Nat)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hn : count * size.bytes ≠ 0)
    (hsal : Interp.Align.is_aligned tyAlign src.addr = true)
    (hdal : Interp.Align.is_aligned tyAlign dst.addr = true)
    (hsprov : src.provenance = some (⟨(i : Int)⟩, ()))
    (hdprov : dst.provenance = some (⟨(i : Int)⟩, ()))
    (hget : m.mem.memory.allocations[i]? = some a) (hlive : a.live = true)
    (hsaddr : src.addr = a.addr + (srcOff : Int))
    (hdaddr : dst.addr = a.addr + (dstOff : Int))
    (hsb : srcOff + count * size.bytes ≤ a.data.length)
    (hdb : dstOff + count * size.bytes ≤ a.data.length) :
    ∃ m', mrCopy m dst src count ty = .ok m' ∧
      m'.mem.memory.allocations = m.mem.memory.allocations.set i
        { a with
          data := a.data.take dstOff ++ (a.data.drop srcOff).take (count * size.bytes) ++
            a.data.drop (dstOff + count * size.bytes) } := by
  have hload := mr_bm_load_in_bounds m.mem.memory src (count * size.bytes) tyAlign i a srcOff hn
    hsal hsprov hget hlive hsaddr hsb
  have hlen : ((a.data.drop srcOff).take (count * size.bytes)).length = count * size.bytes := by
    simp [List.length_take, List.length_drop]
    omega
  have hstore := mr_bm_store_in_bounds m.mem.memory dst
    ((a.data.drop srcOff).take (count * size.bytes)) tyAlign i a dstOff
    (by rw [hlen]; exact hn) hdal hdprov hget hlive hdaddr (by rw [hlen]; exact hdb)
  rw [hlen] at hstore
  refine ⟨{ m with
            mem :=
              { memory :=
                  { m.mem.memory with
                    allocations := m.mem.memory.allocations.set i
                      { a with
                        data := a.data.take dstOff ++
                          (a.data.drop srcOff).take (count * size.bytes) ++
                          a.data.drop (dstOff + count * size.bytes) } },
                accesses :=
                  m.mem.accesses ++ [⟨.Load, .None, src.addr, ⟨count * size.bytes⟩⟩] ++
                    [⟨.Store, .None, dst.addr, ⟨count * size.bytes⟩⟩] } }, ?_, rfl⟩
  simp [mrCopy, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.CM.load, hload, Interp.CM.store, hstore, hlen, bind, Except.bind, pure, Except.pure]

/-- The MiniRust set model is a repeated-byte fill: `mrSet` succeeds and the allocation's data
becomes `d.take dstOff ++ List.replicate n (Init val none) ++ d.drop (dstOff + n)`. -/
theorem mr_set_is_fill (m : Interp.Mach) (dst : Interp.Ptr) (val : UInt8) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (i : Nat) (a : Gen.Allocation) (dstOff : Nat)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hn : count * size.bytes ≠ 0)
    (hdal : Interp.Align.is_aligned tyAlign dst.addr = true)
    (hdprov : dst.provenance = some (⟨(i : Int)⟩, ()))
    (hget : m.mem.memory.allocations[i]? = some a) (hlive : a.live = true)
    (hdaddr : dst.addr = a.addr + (dstOff : Int))
    (hdb : dstOff + count * size.bytes ≤ a.data.length) :
    ∃ m', mrSet m dst val count ty = .ok m' ∧
      m'.mem.memory.allocations = m.mem.memory.allocations.set i
        { a with
          data := a.data.take dstOff ++ List.replicate (count * size.bytes) (.Init val none) ++
            a.data.drop (dstOff + count * size.bytes) } := by
  have hlen : (List.replicate (count * size.bytes)
      (Gen.AbstractByte.Init val none : Interp.Byte)).length = count * size.bytes :=
    List.length_replicate
  have hstore := mr_bm_store_in_bounds m.mem.memory dst
    (List.replicate (count * size.bytes) (.Init val none)) tyAlign i a dstOff
    (by rw [hlen]; exact hn) hdal hdprov hget hlive hdaddr (by rw [hlen]; exact hdb)
  rw [hlen] at hstore
  refine ⟨{ m with
            mem :=
              { memory :=
                  { m.mem.memory with
                    allocations := m.mem.memory.allocations.set i
                      { a with
                        data := a.data.take dstOff ++
                          List.replicate (count * size.bytes) (.Init val none) ++
                          a.data.drop (dstOff + count * size.bytes) } },
                accesses :=
                  m.mem.accesses ++ [⟨.Store, .None, dst.addr, ⟨count * size.bytes⟩⟩] } },
    ?_, rfl⟩
  simp [mrSet, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.CM.store, hstore, bind, Except.bind, pure, Except.pure]

/-- `BasicMemory::check_ptr` inside `TreeBorrowsMemory` for a non-zero-sized in-bounds access into
live allocation `a` returns its allocation id, path, and byte offset. -/
theorem mr_tbm_check_ptr_in_bounds (tbm : Interp.TBM)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (n : Nat)
    (i : Nat) (path : Gen.Path)
    (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (o : Nat)
    (hn : n ≠ 0)
    (hprov : ptr.provenance = some (⟨(i : Int)⟩, path))
    (hget : tbm.mem.allocations[i]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr + (o : Int)) (hbound : o + n ≤ a.data.length) :
    Interp.BasicMemory.check_ptr tbm.mem ptr ⟨n⟩ = .ok (some (⟨(i : Int)⟩, path, ⟨o⟩)) := by
  have hoff : a.addr + (o : Int) - a.addr = (o : Int) := by
    rw [Int.add_comm]; exact Int.add_sub_cancel _ _
  simp [Interp.BasicMemory.check_ptr, hn, hprov, Interp.listIndex, hget, hlive, haddr, hoff,
    Interp.Allocation.size, bind, Except.bind, pure, Except.pure]
  intro h
  omega

/-- A non-zero-sized aligned in-bounds `TreeBorrowsMemory::load` returns the bytes of allocation
`a` at offset `o` and updates only `a.extra.root` according to `Node::access`. -/
theorem mr_tbm_load_in_bounds (tbm : Interp.TBM)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance) (n : Nat) (align : LibSpecr.Align)
    (i : Nat) (path : Gen.Path)
    (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (o : Nat) (root' : Gen.Node)
    (hn : n ≠ 0)
    (hal : Interp.Align.is_aligned align ptr.addr = true)
    (hprov : ptr.provenance = some (⟨(i : Int)⟩, path))
    (hget : tbm.mem.allocations[i]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr + (o : Int)) (hbound : o + n ≤ a.data.length)
    (hacc : Interp.Node.access a.extra.root (some path) .Read ⟨o⟩ ⟨n⟩ = .ok root') :
    Interp.TreeBorrowsMemory.load tbm ptr ⟨n⟩ align =
      .ok ((a.data.drop o).take n,
        { tbm with
          mem := { tbm.mem with
            allocations := tbm.mem.allocations.set i { a with extra := { root := root' } } } }) := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp hget
  have hck := mr_tbm_check_ptr_in_bounds tbm ptr n i path a o hn hprov hget hlive haddr hbound
  have hb' : (o : Int) + (n : Int) ≤ (a.data.length : Int) := by omega
  simp [Interp.TreeBorrowsMemory.load, Interp.BasicMemory.load, hal, hck, Interp.listIndex,
    Interp.listSet, hi, hai, hacc, Interp.subsliceWithLength, hb', bind, Except.bind, pure,
    Except.pure]

/-- A non-empty aligned in-bounds `TreeBorrowsMemory::store` splices `bytes` into allocation `a`
at offset `o` and updates `a.extra.root` according to `Node::access`. -/
theorem mr_tbm_store_in_bounds (tbm : Interp.TBM)
    (ptr : Gen.ThinPointer Gen.TreeBorrowsProvenance)
    (bytes : List (Gen.AbstractByte Gen.TreeBorrowsProvenance)) (align : LibSpecr.Align)
    (i : Nat) (path : Gen.Path)
    (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (o : Nat) (root' : Gen.Node)
    (hn : bytes.length ≠ 0)
    (hal : Interp.Align.is_aligned align ptr.addr = true)
    (hprov : ptr.provenance = some (⟨(i : Int)⟩, path))
    (hget : tbm.mem.allocations[i]? = some a) (hlive : a.live = true)
    (haddr : ptr.addr = a.addr + (o : Int)) (hbound : o + bytes.length ≤ a.data.length)
    (hacc : Interp.Node.access a.extra.root (some path) .Write ⟨o⟩ ⟨bytes.length⟩ = .ok root') :
    Interp.TreeBorrowsMemory.store tbm ptr bytes align =
      .ok { tbm with
            mem := { tbm.mem with
              allocations := tbm.mem.allocations.set i
                { a with
                  data := a.data.take o ++ bytes ++ a.data.drop (o + bytes.length),
                  extra := { root := root' } } } } := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp hget
  have hck := mr_tbm_check_ptr_in_bounds tbm ptr bytes.length i path a o hn hprov hget hlive
    haddr hbound
  have hb' : (o : Int) + (bytes.length : Int) ≤ (a.data.length : Int) := by omega
  simp [Interp.TreeBorrowsMemory.store, Interp.BasicMemory.store, hal, hck, Interp.listIndex,
    Interp.listSet, hi, hai, hacc, Interp.writeSubsliceAtIndex, hb', bind, Except.bind, pure,
    Except.pure]

private theorem node_transitionRange_replicate_unique (kind : Gen.AccessKind) (len : Nat) :
    ∀ (n o : Nat), o + n ≤ len →
      Interp.Node.transitionRange .Local kind o n (List.replicate len (.Unprot .Unique)) =
        .ok (List.replicate len (.Unprot .Unique))
  | 0, _, _ => rfl
  | rem + 1, o, h => by
    have ho : o < len := by omega
    have hlen : o < (List.replicate len (Gen.Permission.Unprot .Unique)).length := by
      simpa using ho
    have hget : (List.replicate len (Gen.Permission.Unprot .Unique))[o]? = some (.Unprot .Unique) := by
      rw [List.getElem?_eq_getElem hlen, List.getElem_replicate]
    have hset : (List.replicate len (Gen.Permission.Unprot .Unique)).set o (.Unprot .Unique) =
        List.replicate len (.Unprot .Unique) := by
      calc (List.replicate len (Gen.Permission.Unprot .Unique)).set o (.Unprot .Unique)
          = (List.replicate len (Gen.Permission.Unprot .Unique)).set o
              (List.replicate len (Gen.Permission.Unprot .Unique))[o] := by
            rw [List.getElem_replicate]
        _ = List.replicate len (.Unprot .Unique) := List.set_getElem_self hlen
    have htr : Interp.Permission.transition (.Unprot .Unique) kind .Local =
        .ok (.Unprot .Unique) := by
      cases kind <;> rfl
    have h0 : (0 : Int) ≤ Int.ofNat o := Int.natCast_nonneg o
    have htn : (Int.ofNat o).toNat = o := rfl
    unfold Interp.Node.transitionRange
    simp only [Interp.listMutateAt, Interp.listIndex, Interp.listSet, h0, ↓reduceIte, htn, hget,
      htr, hset, List.length_replicate, ho, bind, Except.bind, pure, Except.pure]
    exact node_transitionRange_replicate_unique kind len rem (o + 1) (by omega)

/-- On a leaf root node whose permissions are all unprotected `Unique`, any in-bounds local read
or write succeeds and leaves the borrow tree unchanged. -/
theorem mr_tbm_node_access_root_unique (kind : Gen.AccessKind) (len o n : Nat) (h : o + n ≤ len) :
    let root : Gen.Node :=
      { children := [], permissions := List.replicate len (.Unprot .Unique), «protected» := .No }
    Interp.Node.access root (some []) kind ⟨o⟩ ⟨n⟩ = .ok root := by
  intro root
  simp only [root, Interp.Node.access, Interp.Node.transition, Option.isSome_some, ↓reduceIte,
    node_transitionRange_replicate_unique kind len n o h, Interp.Node.accessChildren,
    bind, Except.bind, pure, Except.pure]

/-- Symbolic `memmove` on `MachTB`: for source and destination ranges inside one live allocation
with permitted Tree Borrows read and write transitions, `mrCopyTB` succeeds and the allocation's
data becomes `a.data.take dstOff ++ (a.data.drop srcOff).take n ++ a.data.drop (dstOff + n)` for
every relative overlap (disjoint, forward, or backward). -/
theorem mr_copyTB_is_memmove (m : Interp.MachTB)
    (dst src : Gen.ThinPointer Gen.TreeBorrowsProvenance) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (i : Nat) (srcPath dstPath : Gen.Path)
    (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (srcOff dstOff : Nat)
    (root1 root2 : Gen.Node)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hn : count * size.bytes ≠ 0)
    (hsal : Interp.Align.is_aligned tyAlign src.addr = true)
    (hdal : Interp.Align.is_aligned tyAlign dst.addr = true)
    (hsprov : src.provenance = some (⟨(i : Int)⟩, srcPath))
    (hdprov : dst.provenance = some (⟨(i : Int)⟩, dstPath))
    (hget : m.mem.memory.mem.allocations[i]? = some a) (hlive : a.live = true)
    (hsaddr : src.addr = a.addr + (srcOff : Int))
    (hdaddr : dst.addr = a.addr + (dstOff : Int))
    (hsb : srcOff + count * size.bytes ≤ a.data.length)
    (hdb : dstOff + count * size.bytes ≤ a.data.length)
    (hRead : Interp.Node.access a.extra.root (some srcPath) .Read ⟨srcOff⟩ ⟨count * size.bytes⟩ =
      .ok root1)
    (hWrite : Interp.Node.access root1 (some dstPath) .Write ⟨dstOff⟩ ⟨count * size.bytes⟩ =
      .ok root2) :
    ∃ m', mrCopyTB m dst src count ty = .ok m' ∧
      m'.mem.memory.mem.allocations = m.mem.memory.mem.allocations.set i
        { a with
          data := a.data.take dstOff ++ (a.data.drop srcOff).take (count * size.bytes) ++
            a.data.drop (dstOff + count * size.bytes),
          extra := { root := root2 } } := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hget
  have hload : Interp.MemoryOps.load m.mem.memory src ⟨count * size.bytes⟩ tyAlign =
      .ok ((a.data.drop srcOff).take (count * size.bytes),
        { m.mem.memory with
          mem := { m.mem.memory.mem with
            allocations := m.mem.memory.mem.allocations.set i { a with extra := { root := root1 } } } }) :=
    mr_tbm_load_in_bounds m.mem.memory src (count * size.bytes) tyAlign i srcPath a srcOff root1
      hn hsal hsprov hget hlive hsaddr hsb hRead
  have hlen : ((a.data.drop srcOff).take (count * size.bytes)).length = count * size.bytes := by
    simp [List.length_take, List.length_drop]
    omega
  let a1 : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra :=
    { a with extra := { root := root1 } }
  let tbm1 : Interp.TBM :=
    { m.mem.memory with
      mem := { m.mem.memory.mem with
        allocations := m.mem.memory.mem.allocations.set i a1 } }
  have hget1 : tbm1.mem.allocations[i]? = some a1 := by
    simp [tbm1, List.getElem?_set_self hi]
  have hstore : Interp.MemoryOps.store tbm1 dst ((a.data.drop srcOff).take (count * size.bytes))
      tyAlign =
      .ok { tbm1 with
            mem := { tbm1.mem with
              allocations := tbm1.mem.allocations.set i
                { a1 with
                  data := a.data.take dstOff ++ (a.data.drop srcOff).take (count * size.bytes) ++
                    a.data.drop (dstOff + count * size.bytes),
                  extra := { root := root2 } } } } := by
    have hst := mr_tbm_store_in_bounds tbm1 dst ((a.data.drop srcOff).take (count * size.bytes))
      tyAlign i dstPath a1 dstOff root2 (by rw [hlen]; exact hn) hdal hdprov hget1 hlive hdaddr
      (by rw [hlen]; exact hdb) (by rw [hlen]; exact hWrite)
    rw [hlen] at hst
    exact hst
  have hsetset : tbm1.mem.allocations.set i
      { a1 with
        data := a.data.take dstOff ++ (a.data.drop srcOff).take (count * size.bytes) ++
          a.data.drop (dstOff + count * size.bytes),
        extra := { root := root2 } } =
      m.mem.memory.mem.allocations.set i
        { a with
          data := a.data.take dstOff ++ (a.data.drop srcOff).take (count * size.bytes) ++
            a.data.drop (dstOff + count * size.bytes),
          extra := { root := root2 } } := by
    simp [tbm1, a1]
  refine ⟨{ m with
            mem :=
              { memory :=
                  { tbm1 with
                    mem := { tbm1.mem with
                      allocations := tbm1.mem.allocations.set i
                        { a1 with
                          data := a.data.take dstOff ++
                            (a.data.drop srcOff).take (count * size.bytes) ++
                            a.data.drop (dstOff + count * size.bytes),
                          extra := { root := root2 } } } },
                accesses :=
                  m.mem.accesses ++ [⟨.Load, .None, src.addr, ⟨count * size.bytes⟩⟩] ++
                    [⟨.Store, .None, dst.addr, ⟨count * size.bytes⟩⟩] } },
    ?_, hsetset⟩
  simp [mrCopyTB, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.ConcurrentMemory.load, hload, Interp.ConcurrentMemory.store, hstore, hlen, tbm1, a1,
    bind, Except.bind, pure, Except.pure]

/-- Symbolic repeated-byte fill on `MachTB`: `mrSetTB` succeeds under any permitted write
transition and splices `List.replicate (count * size.bytes) (.Init val none)` into allocation `i`. -/
theorem mr_setTB_is_fill (m : Interp.MachTB)
    (dst : Gen.ThinPointer Gen.TreeBorrowsProvenance) (val : UInt8) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (i : Nat) (dstPath : Gen.Path)
    (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (dstOff : Nat) (root' : Gen.Node)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hn : count * size.bytes ≠ 0)
    (hdal : Interp.Align.is_aligned tyAlign dst.addr = true)
    (hdprov : dst.provenance = some (⟨(i : Int)⟩, dstPath))
    (hget : m.mem.memory.mem.allocations[i]? = some a) (hlive : a.live = true)
    (hdaddr : dst.addr = a.addr + (dstOff : Int))
    (hdb : dstOff + count * size.bytes ≤ a.data.length)
    (hWrite : Interp.Node.access a.extra.root (some dstPath) .Write ⟨dstOff⟩ ⟨count * size.bytes⟩ =
      .ok root') :
    ∃ m', mrSetTB m dst val count ty = .ok m' ∧
      m'.mem.memory.mem.allocations = m.mem.memory.mem.allocations.set i
        { a with
          data := a.data.take dstOff ++ List.replicate (count * size.bytes) (.Init val none) ++
            a.data.drop (dstOff + count * size.bytes),
          extra := { root := root' } } := by
  have hlen : (List.replicate (count * size.bytes)
      (Gen.AbstractByte.Init val none : Gen.AbstractByte Gen.TreeBorrowsProvenance)).length =
      count * size.bytes :=
    List.length_replicate
  have hstore : Interp.MemoryOps.store m.mem.memory dst
      (List.replicate (count * size.bytes) (.Init val none)) tyAlign =
      .ok { m.mem.memory with
            mem := { m.mem.memory.mem with
              allocations := m.mem.memory.mem.allocations.set i
                { a with
                  data := a.data.take dstOff ++
                    List.replicate (count * size.bytes) (.Init val none) ++
                    a.data.drop (dstOff + count * size.bytes),
                  extra := { root := root' } } } } := by
    have hst := mr_tbm_store_in_bounds m.mem.memory dst
      (List.replicate (count * size.bytes) (.Init val none)) tyAlign i dstPath a dstOff root'
      (by rw [hlen]; exact hn) hdal hdprov hget hlive hdaddr (by rw [hlen]; exact hdb)
      (by rw [hlen]; exact hWrite)
    rw [hlen] at hst
    exact hst
  refine ⟨{ m with
            mem :=
              { memory :=
                  { m.mem.memory with
                    mem := { m.mem.memory.mem with
                      allocations := m.mem.memory.mem.allocations.set i
                        { a with
                          data := a.data.take dstOff ++
                            List.replicate (count * size.bytes) (.Init val none) ++
                            a.data.drop (dstOff + count * size.bytes),
                          extra := { root := root' } } } },
                accesses :=
                  m.mem.accesses ++ [⟨.Store, .None, dst.addr, ⟨count * size.bytes⟩⟩] } },
    ?_, rfl⟩
  simp [mrSetTB, hLay, Interp.LayoutStrategy.expect_size, Interp.LayoutStrategy.expect_align,
    Interp.ConcurrentMemory.store, hstore, bind, Except.bind, pure, Except.pure]

/-- Unconditional `memmove` corollary on `MachTB` for a single-node unprotected-`Unique` borrow
tree (no `Node::access` hypothesis required). -/
theorem mr_copyTB_root_unique_is_memmove (m : Interp.MachTB)
    (dst src : Gen.ThinPointer Gen.TreeBorrowsProvenance) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (i : Nat) (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (srcOff dstOff : Nat)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hn : count * size.bytes ≠ 0)
    (hsal : Interp.Align.is_aligned tyAlign src.addr = true)
    (hdal : Interp.Align.is_aligned tyAlign dst.addr = true)
    (hsprov : src.provenance = some (⟨(i : Int)⟩, []))
    (hdprov : dst.provenance = some (⟨(i : Int)⟩, []))
    (hget : m.mem.memory.mem.allocations[i]? = some a) (hlive : a.live = true)
    (hroot : a.extra.root =
      { children := [], permissions := List.replicate a.data.length (.Unprot .Unique),
        «protected» := .No })
    (hsaddr : src.addr = a.addr + (srcOff : Int))
    (hdaddr : dst.addr = a.addr + (dstOff : Int))
    (hsb : srcOff + count * size.bytes ≤ a.data.length)
    (hdb : dstOff + count * size.bytes ≤ a.data.length) :
    ∃ m', mrCopyTB m dst src count ty = .ok m' ∧
      m'.mem.memory.mem.allocations = m.mem.memory.mem.allocations.set i
        { a with
          data := a.data.take dstOff ++ (a.data.drop srcOff).take (count * size.bytes) ++
            a.data.drop (dstOff + count * size.bytes) } := by
  have hRead : Interp.Node.access a.extra.root (some []) .Read ⟨srcOff⟩ ⟨count * size.bytes⟩ =
      .ok a.extra.root := by
    rw [hroot]
    exact mr_tbm_node_access_root_unique .Read a.data.length srcOff (count * size.bytes) hsb
  have hWrite : Interp.Node.access a.extra.root (some []) .Write ⟨dstOff⟩ ⟨count * size.bytes⟩ =
      .ok a.extra.root := by
    rw [hroot]
    exact mr_tbm_node_access_root_unique .Write a.data.length dstOff (count * size.bytes) hdb
  exact mr_copyTB_is_memmove m dst src count ty size tyAlign i [] [] a srcOff dstOff
    a.extra.root a.extra.root hLay hn hsal hdal hsprov hdprov hget hlive hsaddr hdaddr hsb hdb
    hRead hWrite

/-- Unconditional repeated-byte fill corollary on `MachTB` for a single-node unprotected-`Unique`
borrow tree (no `Node::access` hypothesis required). -/
theorem mr_setTB_root_unique_is_fill (m : Interp.MachTB)
    (dst : Gen.ThinPointer Gen.TreeBorrowsProvenance) (val : UInt8) (count : Nat)
    (ty : Gen.«Type») (size : LibSpecr.Size) (tyAlign : LibSpecr.Align)
    (i : Nat) (a : Gen.Allocation Gen.Path Gen.TreeBorrowsAllocationExtra) (dstOff : Nat)
    (hLay : Interp.Type.layout ty = .ok (.Sized size tyAlign))
    (hn : count * size.bytes ≠ 0)
    (hdal : Interp.Align.is_aligned tyAlign dst.addr = true)
    (hdprov : dst.provenance = some (⟨(i : Int)⟩, []))
    (hget : m.mem.memory.mem.allocations[i]? = some a) (hlive : a.live = true)
    (hroot : a.extra.root =
      { children := [], permissions := List.replicate a.data.length (.Unprot .Unique),
        «protected» := .No })
    (hdaddr : dst.addr = a.addr + (dstOff : Int))
    (hdb : dstOff + count * size.bytes ≤ a.data.length) :
    ∃ m', mrSetTB m dst val count ty = .ok m' ∧
      m'.mem.memory.mem.allocations = m.mem.memory.mem.allocations.set i
        { a with
          data := a.data.take dstOff ++ List.replicate (count * size.bytes) (.Init val none) ++
            a.data.drop (dstOff + count * size.bytes) } := by
  have hWrite : Interp.Node.access a.extra.root (some []) .Write ⟨dstOff⟩ ⟨count * size.bytes⟩ =
      .ok a.extra.root := by
    rw [hroot]
    exact mr_tbm_node_access_root_unique .Write a.data.length dstOff (count * size.bytes) hdb
  exact mr_setTB_is_fill m dst val count ty size tyAlign i [] a dstOff a.extra.root hLay hn hdal
    hdprov hget hlive hdaddr hdb hWrite

/-- Reading of the spliced buffer `d.take t ++ snap ++ d.drop (t + |snap|)`: the destination
range holds exactly `snap`, the bytes before and after it are those of `d`, and the length is
that of `d`. -/
theorem splice_spec {T : Type} (d snap : List T) (t : Nat) (h : t + snap.length ≤ d.length) :
    ((d.take t ++ snap ++ d.drop (t + snap.length)).drop t).take snap.length = snap ∧
    (d.take t ++ snap ++ d.drop (t + snap.length)).take t = d.take t ∧
    (d.take t ++ snap ++ d.drop (t + snap.length)).drop (t + snap.length) =
      d.drop (t + snap.length) ∧
    (d.take t ++ snap ++ d.drop (t + snap.length)).length = d.length := by
  have ht : (d.take t).length = t := by
    rw [List.length_take]; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [List.append_assoc, ht]
  · simp [List.append_assoc, ht]
  · simp [List.drop_append, ht]
  · simp [List.length_append, List.length_drop, ht]
    omega

/-! ## 10. Integer encode agreement and round trip (item 2) -/

/-- `UInt8.ofNat` truncates modulo `256`. -/
private theorem u8_ofNat_mod (x : Nat) : UInt8.ofNat (x % 256) = UInt8.ofNat x := by
  apply UInt8.toNat_inj.mp
  rw [UInt8.toNat_ofNat', UInt8.toNat_ofNat']
  omega

/-- A value below `256` survives `UInt8.ofNat`. -/
private theorem u8_toNat_ofNat_mod (x : Nat) : (UInt8.ofNat (x % 256)).toNat = x % 256 := by
  rw [UInt8.toNat_ofNat']
  omega

/-- Trusted's little-endian byte encoder produces MiniRust's `leBytes`, for every bit pattern and
width. -/
theorem trusted_encode_le_eq_leBytes (bits w : Nat) :
    encodeLittleEndianBytes bits w .none = tPlain (Interp.leBytes bits w) := by
  induction w generalizing bits with
  | zero => rfl
  | succ n ih =>
    have h := ih (bits / 256)
    simp only [tPlain] at h
    simp only [encodeLittleEndianBytes, Interp.leBytes, tPlain, List.map_cons, u8_ofNat_mod]
    exact congrArg _ h

/-- `leValue` inverts `leBytes` on every value that fits the width. -/
theorem leValue_leBytes (u n : Nat) (h : u < 256 ^ n) :
    Interp.leValue (Interp.leBytes u n) = u := by
  induction n generalizing u with
  | zero =>
    simp only [Nat.pow_zero] at h
    simp only [Interp.leBytes, Interp.leValue]
    omega
  | succ n ih =>
    have hdiv : u / 256 < 256 ^ n := by
      rw [Nat.pow_succ] at h
      omega
    simp only [Interp.leBytes, Interp.leValue, u8_toNat_ofNat_mod, ih _ hdiv]
    omega

/-- `Int::in_bounds(Unsigned, size)` as a proposition. -/
private theorem inBounds_unsigned_iff (i : Int) (size : LibSpecr.Size) :
    Interp.inBounds i .Unsigned size = true ↔ 0 ≤ i ∧ i < (2 : Int) ^ Interp.Size.bits size := by
  simp [Interp.inBounds]

/-- `Int::in_bounds(Signed, size)` as a proposition. -/
private theorem inBounds_signed_iff (i : Int) (size : LibSpecr.Size) :
    Interp.inBounds i .Signed size = true ↔
      -((2 : Int) ^ (Interp.Size.bits size - 1)) ≤ i ∧
        i < (2 : Int) ^ (Interp.Size.bits size - 1) := by
  simp [Interp.inBounds]

/-- At the widths 1, 2, 4, 8 and 16, `intFromBits u` is in bounds and reduces to `u` modulo
`2^bits`. -/
private theorem mr_encode_wrap (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16)
    (sg : LibSpecr.Signedness) (u : Nat) (hu : u < 256 ^ w) :
    Interp.inBounds (intFromBits u ⟨sg, ⟨w⟩⟩) sg ⟨w⟩ = true ∧
    ((intFromBits u ⟨sg, ⟨w⟩⟩) % (2 : Int) ^ Interp.Size.bits ⟨w⟩).toNat = u := by
  cases sg with
  | Unsigned =>
    rw [inBounds_unsigned_iff]
    rcases hw with rfl | rfl | rfl | rfl | rfl <;>
      simp [intFromBits, Interp.Size.bits] at hu ⊢ <;> omega
  | Signed =>
    rw [inBounds_signed_iff]
    rcases hw with rfl | rfl | rfl | rfl | rfl <;>
      simp [intFromBits, Interp.Size.bits] at hu ⊢ <;> split <;> omega

/-- Encode agreement at the MIR integer type `ty` of width `w`: for every bit pattern that fits
the width, Trusted's raw-pointer encoder and MiniRust's `Type::encode` of the corresponding
integer (`intFromBits`) produce the same little-endian bytes `leBytes bits w`. -/
def IntEncodeAgree (layouts : LayoutTable) (ty : Ty) (w : Nat) : Prop :=
  ∃ it, intTypeOf ty = some it ∧ it.size.bytes = w ∧
    ∀ (decls : List LocalDecl) (bits : Nat), bits < 256 ^ w →
      rawPtrEncodeValue? decls layouts ty (.scalar ⟨bits, w⟩) =
        .some (tPlain (Interp.leBytes bits w)) ∧
      Interp.Type.encode (.Int it) (.Int (intFromBits bits it)) =
        .ok (vbPlain (Interp.leBytes bits w))

/-- `IntEncodeAgree` at a translated integer type of width 1, 2, 4, 8 or 16. -/
private theorem intEncodeAgree_of (layouts : LayoutTable) (ty : Ty) (sg : LibSpecr.Signedness)
    (w : Nat) (hw : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16)
    (hLE : layouts.isLittleEndian = true)
    (hit : intTypeOf ty = some ⟨sg, ⟨w⟩⟩) :
    IntEncodeAgree layouts ty w := by
  refine ⟨_, hit, rfl, fun decls bits hb => ⟨?_, ?_⟩⟩
  · have hw0 : Nat.beq w 0 = false := by
      rcases hw with rfl | rfl | rfl | rfl | rfl <;> rfl
    simp [rawPtrEncodeValue?, hLE, encodeUntypedValueToBytes, encodeScalarBytes, hw0,
      trusted_encode_le_eq_leBytes]
  · obtain ⟨h1, h2⟩ := mr_encode_wrap w hw sg bits hb
    simp [Interp.Type.encode, Interp.Type.encodeInt, Interp.Endianness.encode, h1, h2,
      Interp.x86_64.ENDIANNESS, vbPlain, pure, Except.pure]

/-- Encode agreement for every representable bit pattern, at the unsigned and signed integer
types of width 1, 2, 4, 8 and 16 bytes, for every little-endian layout table. -/
theorem codec_int_encode_agreement (layouts : LayoutTable) (idx : LayoutIdx)
    (hLE : layouts.isLittleEndian = true) :
    IntEncodeAgree layouts ⟨.uint .u8, idx⟩ 1 ∧
    IntEncodeAgree layouts ⟨.int .i8, idx⟩ 1 ∧
    IntEncodeAgree layouts ⟨.uint .u16, idx⟩ 2 ∧
    IntEncodeAgree layouts ⟨.int .i16, idx⟩ 2 ∧
    IntEncodeAgree layouts ⟨.uint .u32, idx⟩ 4 ∧
    IntEncodeAgree layouts ⟨.int .i32, idx⟩ 4 ∧
    IntEncodeAgree layouts ⟨.uint .u64, idx⟩ 8 ∧
    IntEncodeAgree layouts ⟨.int .i64, idx⟩ 8 ∧
    IntEncodeAgree layouts ⟨.uint .u128, idx⟩ 16 ∧
    IntEncodeAgree layouts ⟨.int .i128, idx⟩ 16 :=
  ⟨intEncodeAgree_of _ _ _ 1 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 1 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 2 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 2 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 4 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 4 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 8 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 8 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 16 (by decide) hLE rfl,
   intEncodeAgree_of _ _ _ 16 (by decide) hLE rfl⟩

/-- `leBytes u n` has `n` bytes. -/
theorem leBytes_length (u n : Nat) : (Interp.leBytes u n).length = n := by
  induction n generalizing u with
  | zero => rfl
  | succ n ih => simp only [Interp.leBytes, List.length_cons, ih]

/-- Round trip at the MIR integer type `ty` of width `w`: decoding the encoding `leBytes bits w`
of a bit pattern that fits the width returns the scalar `bits` in Trusted and the
corresponding integer (`intFromBits`) in MiniRust. -/
def IntRoundTrip (layouts : LayoutTable) (ty : Ty) (w : Nat) : Prop :=
  ∃ it, intTypeOf ty = some it ∧ it.size.bytes = w ∧
    ∀ bits : Nat, bits < 256 ^ w →
      rawPtrDecodeBytes layouts ty (tPlain (Interp.leBytes bits w)) = .ok (.scalar ⟨bits, w⟩) ∧
      Interp.Type.decode (.Int it) (vbPlain (Interp.leBytes bits w)) =
        .ok (some (.Int (intFromBits bits it)))

/-- `IntRoundTrip` from decode agreement on the bytes `leBytes bits w`. -/
private theorem intRoundTrip_of (layouts : LayoutTable) (ty : Ty) (sg : LibSpecr.Signedness)
    (w : Nat) (hit : intTypeOf ty = some ⟨sg, ⟨w⟩⟩)
    (hdec : ∀ bits, IntDecodeAgree layouts ty (Interp.leBytes bits w)) :
    IntRoundTrip layouts ty w := by
  refine ⟨_, hit, rfl, fun bits hb => ?_⟩
  obtain ⟨it, hit', _, hT, hM⟩ := hdec bits
  rw [hit] at hit'
  cases hit'
  rw [leValue_leBytes bits w hb, leBytes_length] at hT
  rw [leValue_leBytes bits w hb] at hM
  exact ⟨hT, hM⟩

/-- Round trip for every representable bit pattern, at the unsigned and signed integer types of
width 1, 2, 4, 8 and 16 bytes, for every little-endian layout table. -/
theorem codec_int_round_trip (layouts : LayoutTable) (idx : LayoutIdx)
    (hLE : layouts.isLittleEndian = true) :
    IntRoundTrip layouts ⟨.uint .u8, idx⟩ 1 ∧
    IntRoundTrip layouts ⟨.int .i8, idx⟩ 1 ∧
    IntRoundTrip layouts ⟨.uint .u16, idx⟩ 2 ∧
    IntRoundTrip layouts ⟨.int .i16, idx⟩ 2 ∧
    IntRoundTrip layouts ⟨.uint .u32, idx⟩ 4 ∧
    IntRoundTrip layouts ⟨.int .i32, idx⟩ 4 ∧
    IntRoundTrip layouts ⟨.uint .u64, idx⟩ 8 ∧
    IntRoundTrip layouts ⟨.int .i64, idx⟩ 8 ∧
    IntRoundTrip layouts ⟨.uint .u128, idx⟩ 16 ∧
    IntRoundTrip layouts ⟨.int .i128, idx⟩ 16 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact intRoundTrip_of _ _ _ _ rfl (fun bits =>
      intDecodeAgree_of _ _ _ _ rfl (by simp only [rawPtrDecodeBytes, hLE]; rfl) rfl)

/-- `usize` and `isize` on the 64-bit fixture table: decode agreement for all bytes, and encode
agreement and round trip for every bit pattern. (Trusted decodes these two types on a separate
path, which reads the pointer width of the layout table.) -/
theorem codec_usize_isize_agreement (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    IntDecodeAgree vbTbl ⟨.uint .usize, 2⟩ [b0, b1, b2, b3, b4, b5, b6, b7] ∧
    IntDecodeAgree vbTbl ⟨.int .isize, 2⟩ [b0, b1, b2, b3, b4, b5, b6, b7] ∧
    IntEncodeAgree vbTbl ⟨.uint .usize, 2⟩ 8 ∧
    IntEncodeAgree vbTbl ⟨.int .isize, 2⟩ 8 ∧
    IntRoundTrip vbTbl ⟨.uint .usize, 2⟩ 8 ∧
    IntRoundTrip vbTbl ⟨.int .isize, 2⟩ 8 :=
  ⟨intDecodeAgree_of _ _ _ _ rfl rfl rfl,
   intDecodeAgree_of _ _ _ _ rfl rfl rfl,
   intEncodeAgree_of _ _ _ 8 (by decide) rfl rfl,
   intEncodeAgree_of _ _ _ 8 (by decide) rfl rfl,
   intRoundTrip_of _ _ _ _ rfl (fun _ => intDecodeAgree_of _ _ _ _ rfl rfl rfl),
   intRoundTrip_of _ _ _ _ rfl (fun _ => intDecodeAgree_of _ _ _ _ rfl rfl rfl)⟩

/-- `usize` and `isize` generalized over every 64-bit little-endian `LayoutTable` and `LayoutIdx`:
decode agreement for all bytes, encode agreement, and round trip for every representable bit
pattern. -/
theorem codec_usize_isize_agreement_general (layouts : LayoutTable) (idx : LayoutIdx)
    (hLE : layouts.isLittleEndian = true) (hPtr : layouts.pointerBits = 64)
    (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    IntDecodeAgree layouts ⟨.uint .usize, idx⟩ [b0, b1, b2, b3, b4, b5, b6, b7] ∧
    IntDecodeAgree layouts ⟨.int .isize, idx⟩ [b0, b1, b2, b3, b4, b5, b6, b7] ∧
    IntEncodeAgree layouts ⟨.uint .usize, idx⟩ 8 ∧
    IntEncodeAgree layouts ⟨.int .isize, idx⟩ 8 ∧
    IntRoundTrip layouts ⟨.uint .usize, idx⟩ 8 ∧
    IntRoundTrip layouts ⟨.int .isize, idx⟩ 8 := by
  have hpb : layoutPointerBytes layouts = 8 := by
    unfold layoutPointerBytes; rw [hPtr]
  have hdecU : ∀ (bs : List UInt8), bs.length = 8 →
      rawPtrDecodeBytes layouts ⟨.uint .usize, idx⟩ (tPlain bs) =
        .ok (.scalar ⟨Interp.leValue bs, bs.length⟩) := by
    intro bs hlen
    match bs, hlen with
    | [x0, x1, x2, x3, x4, x5, x6, x7], _ =>
      simp only [rawPtrDecodeBytes, hLE, hpb]
      rfl
  have hdecI : ∀ (bs : List UInt8), bs.length = 8 →
      rawPtrDecodeBytes layouts ⟨.int .isize, idx⟩ (tPlain bs) =
        .ok (.scalar ⟨Interp.leValue bs, bs.length⟩) := by
    intro bs hlen
    match bs, hlen with
    | [x0, x1, x2, x3, x4, x5, x6, x7], _ =>
      simp only [rawPtrDecodeBytes, hLE, hpb]
      rfl
  refine
    ⟨intDecodeAgree_of _ _ _ _ rfl (hdecU _ rfl) rfl,
     intDecodeAgree_of _ _ _ _ rfl (hdecI _ rfl) rfl,
     intEncodeAgree_of _ _ _ 8 (by decide) hLE rfl,
     intEncodeAgree_of _ _ _ 8 (by decide) hLE rfl,
     intRoundTrip_of _ _ _ _ rfl (fun bits =>
       intDecodeAgree_of _ _ _ _ rfl (hdecU _ (leBytes_length bits 8)) rfl),
     intRoundTrip_of _ _ _ _ rfl (fun bits =>
       intDecodeAgree_of _ _ _ _ rfl (hdecI _ (leBytes_length bits 8)) rfl)⟩

/-! ### An instance of Section 7 at the address `0x4000_0000` (item 5) -/

/-- The address `0x4000_0000` is aligned for `u32` and belongs to no allocation: instances of
`volatile_load_mmio_one_way_soundness` and `volatile_store_mmio_one_way_soundness` on the
fixtures. Trusted steps to `MirStepNode.unsupported`; MiniRust reports UB on both memories. -/
theorem lockstep_mmio_aligned_0x40000000 :
    (evalVolatileMemIntrinsicCall .volatileLoad (vbMmioLoadState 0x40000000)
        (vbTarget "core::intrinsics::volatile_load" vbTyU32) [vbDecl vbTyU32, vbDecl vbTyPtrU32]
        vbTbl [.copy ⟨1, []⟩] [.scalar ⟨0x40000000, layoutPointerBytes vbTbl⟩]
        [.uninit, .init (.scalar ⟨0x40000000, 8⟩)] ⟨0, []⟩ 1 = MirStepNode.unsupported ∧
      mrLoad true (vbMach (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ vbMrU32 =
        .error (.ub "dereferencing pointer without provenance") ∧
      mrLoadTB true (vbMachTB (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ vbMrU32 =
        .error (.ub "dereferencing pointer without provenance")) ∧
    (evalVolatileMemIntrinsicCall .volatileStore (vbMmioStoreState 0x40000000 0xCAFEBABE)
        (vbTarget "core::intrinsics::volatile_store" vbTyU32)
        [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] vbTbl
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
        [.scalar ⟨0x40000000, layoutPointerBytes vbTbl⟩, .scalar ⟨0xCAFEBABE, 4⟩]
        [.uninit, .init (.scalar ⟨0x40000000, 8⟩), .init (.scalar ⟨0xCAFEBABE, 4⟩)] ⟨0, []⟩ 1 =
          MirStepNode.unsupported ∧
      mrStore true (vbMach (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ (.Int 0xCAFEBABE)
          vbMrU32 = .error (.ub "dereferencing pointer without provenance") ∧
      mrStoreTB true (vbMachTB (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ (.Int 0xCAFEBABE)
          vbMrU32 = .error (.ub "dereferencing pointer without provenance")) :=
  ⟨volatile_load_mmio_one_way_soundness _ _ _ _ _ _ _ _ _ 4 4 0x40000000 _ _ vbMrU32 ⟨4⟩
      rfl rfl (by decide) (by decide) rfl (by decide) (by decide),
   volatile_store_mmio_one_way_soundness _ _ _ _ _ _ _ _ _ 4 4 0x40000000 _ _ _
      (vbPlain [0xBE, 0xBA, 0xFE, 0xCA]) _ _ (vbPlain [0xBE, 0xBA, 0xFE, 0xCA]) vbMrU32 ⟨4⟩
      rfl rfl (interp_ok_of_toOption (by decide +kernel))
      (interp_ok_of_toOption (by decide +kernel)) (interp_ok_of_toOption (by decide +kernel))
      (interp_ok_of_toOption (by decide +kernel))
      (by decide) (by decide) rfl rfl (by decide) (by decide) (by decide)⟩

/-- Uninhabited 4-aligned MiniRust enum (`#[repr(u32)] enum Empty4 {}`, size `0`, align `4`). -/
def vbMrNeverAlign4 : Gen.«Type» := .Enum ⟨[]⟩ ⟨.Unsigned, ⟨4⟩⟩ .Invalid ⟨0⟩ ⟨4⟩

/-- Non-vacuity instantiation of `unlinked_read_volatile_misaligned_parity_any_ty` (including on
the uninhabited 4-aligned enum `vbMrNeverAlign4`, where `checkValue` is never `.ok ()` so
`unlinked_read_write_volatile_misaligned_parity`'s store-value precondition is false),
`unlinked_read_write_volatile_misaligned_parity`, `unlinked_read_volatile_mmio_one_way_soundness`,
and `unlinked_read_write_volatile_mmio_one_way_soundness`. -/
theorem wit_unlinked_read_write_volatile_misaligned_and_mmio :
    (∀ v, Interp.checkValue v vbMrNeverAlign4 (some (vbMach (vbPlain vbArr8))) ≠ .ok ()) ∧
    (evalUnlinkedPtrAccessCall? (vbMmioLoadState 0x40000001)
        (vbTarget "core::ptr::read_volatile" vbTyZstAlign4)
        [vbDecl vbTyZstAlign4, vbDecl ⟨.rawPtr .not vbTyZstAlign4.kind, 4⟩] vbTbl
        [.copy ⟨1, []⟩] [.scalar ⟨0x40000001, 8⟩]
        [.uninit, .init (.scalar ⟨0x40000001, 8⟩)] ⟨0, []⟩ 1 =
      some (MirStepNode.fail .ub) ∧
      mrLoad true (vbMach (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩ vbMrNeverAlign4 =
        .error (.ub "load from a misaligned pointer") ∧
      mrLoadTB true (vbMachTB (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩ vbMrNeverAlign4 =
        .error (.ub "load from a misaligned pointer")) ∧
    (evalUnlinkedPtrAccessCall? (vbMmioStoreState 0x40000001 0xCAFEBABE)
        (vbTarget "core::ptr::write_volatile" vbTyU32)
        [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] vbTbl
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
        [.scalar ⟨0x40000001, 8⟩, .scalar ⟨0xCAFEBABE, 4⟩]
        [.uninit, .init (.scalar ⟨0x40000001, 8⟩), .init (.scalar ⟨0xCAFEBABE, 4⟩)] ⟨0, []⟩ 1 =
      some (MirStepNode.fail .ub) ∧
      mrStore true (vbMach (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩ (.Int 0xCAFEBABE)
        vbMrU32 = .error (.ub "store to a misaligned pointer") ∧
      mrStoreTB true (vbMachTB (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩ (.Int 0xCAFEBABE)
        vbMrU32 = .error (.ub "store to a misaligned pointer")) ∧
    (evalUnlinkedPtrAccessCall? (vbMmioLoadState 0x40000000)
        (vbTarget "core::ptr::read_volatile" vbTyU32)
        [vbDecl vbTyU32, vbDecl vbTyPtrU32] vbTbl
        [.copy ⟨1, []⟩] [.scalar ⟨0x40000000, layoutPointerBytes vbTbl⟩]
        [.uninit, .init (.scalar ⟨0x40000000, 8⟩)] ⟨0, []⟩ 1 =
      some MirStepNode.unsupported ∧
      mrLoad true (vbMach (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ vbMrU32 =
        .error (.ub "dereferencing pointer without provenance") ∧
      mrLoadTB true (vbMachTB (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ vbMrU32 =
        .error (.ub "dereferencing pointer without provenance")) ∧
    (evalUnlinkedPtrAccessCall? (vbMmioStoreState 0x40000000 0xCAFEBABE)
        (vbTarget "core::ptr::write_volatile" vbTyU32)
        [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] vbTbl
        [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
        [.scalar ⟨0x40000000, layoutPointerBytes vbTbl⟩, .scalar ⟨0xCAFEBABE, 4⟩]
        [.uninit, .init (.scalar ⟨0x40000000, 8⟩), .init (.scalar ⟨0xCAFEBABE, 4⟩)] ⟨0, []⟩ 1 =
      some MirStepNode.unsupported ∧
      mrStore true (vbMach (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ (.Int 0xCAFEBABE)
        vbMrU32 = .error (.ub "dereferencing pointer without provenance") ∧
      mrStoreTB true (vbMachTB (vbPlain vbArr8)) ⟨(0x40000000 : Nat), none⟩ (.Int 0xCAFEBABE)
        vbMrU32 = .error (.ub "dereferencing pointer without provenance")) :=
  ⟨(fun v => by cases v <;> intro h <;> cases h),
   unlinked_read_volatile_misaligned_parity_any_ty _ _ _ _ _ _ _ _ _ (.addr 0x40000001)
     vbTyZstAlign4 0 4 (vbMach (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩
     (vbMachTB (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩ vbMrNeverAlign4 ⟨0⟩
     rfl rfl rfl rfl rfl (by decide) (by decide),
   (unlinked_read_write_volatile_misaligned_parity
     (vbMmioStoreState 0x40000001 0xCAFEBABE)
     (vbTarget "core::ptr::write_volatile" vbTyU32)
     [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] vbTbl
     [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
     [.uninit, .init (.scalar ⟨0x40000001, 8⟩), .init (.scalar ⟨0xCAFEBABE, 4⟩)] ⟨0, []⟩ 1
     (.scalar ⟨0x40000001, 8⟩) (.scalar ⟨0xCAFEBABE, 4⟩) (.addr 0x40000001)
     vbTyU32 4 4 (vbMach (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩
     (.Int 0xCAFEBABE) (vbPlain [0xBE, 0xBA, 0xFE, 0xCA])
     (vbMachTB (vbPlain vbArr8)) ⟨(0x40000001 : Nat), none⟩
     (.Int 0xCAFEBABE) (vbPlain [0xBE, 0xBA, 0xFE, 0xCA]) vbMrU32 ⟨4⟩
     rfl rfl rfl rfl (by decide) (by decide)
     (interp_ok_of_toOption (by decide +kernel)) (interp_ok_of_toOption (by decide +kernel))
     (interp_ok_of_toOption (by decide +kernel)) (interp_ok_of_toOption (by decide +kernel))).2 rfl,
   unlinked_read_volatile_mmio_one_way_soundness _ _ _ _ _ _ _ _ vbTyU32 4 4 0x40000000
     (vbMach (vbPlain vbArr8)) (vbMachTB (vbPlain vbArr8))
     vbMrU32 ⟨4⟩ rfl rfl rfl (by decide) (by decide) rfl (by decide) (by decide),
   (unlinked_read_write_volatile_mmio_one_way_soundness
     (vbMmioStoreState 0x40000000 0xCAFEBABE)
     (vbTarget "core::ptr::write_volatile" vbTyU32)
     [vbDecl vbTyUnit, vbDecl vbTyPtrU32, vbDecl vbTyU32] vbTbl
     [.copy ⟨1, []⟩, .copy ⟨2, []⟩]
     [.uninit, .init (.scalar ⟨0x40000000, 8⟩), .init (.scalar ⟨0xCAFEBABE, 4⟩)] ⟨0, []⟩ 1
     vbTyU32 4 4 0x40000000 (.scalar ⟨0xCAFEBABE, 4⟩)
     (vbMach (vbPlain vbArr8)) (.Int 0xCAFEBABE) (vbPlain [0xBE, 0xBA, 0xFE, 0xCA])
     (vbMachTB (vbPlain vbArr8)) (.Int 0xCAFEBABE) (vbPlain [0xBE, 0xBA, 0xFE, 0xCA])
     vbMrU32 ⟨4⟩
     rfl rfl (by decide) (by decide) rfl rfl (by decide) (by decide)
     (interp_ok_of_toOption (by decide +kernel)) (interp_ok_of_toOption (by decide +kernel))
     (interp_ok_of_toOption (by decide +kernel)) (interp_ok_of_toOption (by decide +kernel))
     (by decide) (by decide)).2 rfl⟩

/-! ## 11. Bounded-exhaustive lockstep on the `[u8; 8]` fixture (items 3 and 4) -/

/-- `memmove` on a buffer: bytes `[dstOff, dstOff + n)` are replaced by the original bytes
`[srcOff, srcOff + n)`. -/
def memmoveSpec {T : Type} (bs : List T) (dstOff srcOff n : Nat) : List T :=
  bs.take dstOff ++ (bs.drop srcOff).take n ++ bs.drop (dstOff + n)

/-- Fill on a buffer: bytes `[dstOff, dstOff + n)` are replaced by `v`. -/
def fillSpec {T : Type} (bs : List T) (dstOff n : Nat) (v : T) : List T :=
  bs.take dstOff ++ List.replicate n v ++ bs.drop (dstOff + n)

/-- The bytes of the `[u8; N]` local `_1` in a Trusted slot list (`none` if `_1` is not an
initialised aggregate of one-byte scalars). -/
def trustedLocalBytes? : List LocalSlot → Option (List Nat)
  | [_, .init (.aggregate 0 vals)] =>
    vals.mapM (fun v =>
      match v with
      | .scalar sc => if sc.sizeBytes = 1 then some sc.bits else none
      | _ => none)
  | _ => none

/-- Decidable observation of a Trusted copy, set or store action on the fixture: the bytes of
`_1` afterwards. A return without a memory change (`.ret .unit`) leaves the bytes `orig`. -/
def trustedActionBytes? (orig : List UInt8) : RawPtrCallAction → Option (List Nat)
  | .ret .unit => some (orig.map UInt8.toNat)
  | .retStack _ locals _ _ .unit => trustedLocalBytes? locals
  | _ => none

/-- The Trusted action is `.fault .ub`. -/
def trustedActionIsUb : RawPtrCallAction → Bool
  | .fault .ub => true
  | _ => false

/-- `trustedActionIsUb a = true` means `a = .fault .ub`. -/
theorem trustedActionIsUb_sound {a : RawPtrCallAction} (h : trustedActionIsUb a = true) :
    a = .fault .ub := by
  cases a with
  | fault k => cases k <;> first | rfl | cases h
  | _ => cases h

/-- `trustedActionBytes? orig a = some bs` means `a` returned `()`, either without a memory
change (and `bs` are the bytes `orig`) or with slots whose `_1` holds the bytes `bs`. -/
theorem trustedActionBytes_sound {orig : List UInt8} {a : RawPtrCallAction} {bs : List Nat}
    (h : trustedActionBytes? orig a = some bs) :
    (a = .ret .unit ∧ bs = orig.map UInt8.toNat) ∨
    ∃ borrows locals callStack callerLocals,
      a = .retStack borrows locals callStack callerLocals .unit ∧
        trustedLocalBytes? locals = some bs := by
  cases a with
  | fault k => cases h
  | retBorrows b v => cases h
  | ret v =>
    cases v with
    | unit =>
      simp only [trustedActionBytes?, Option.some.injEq] at h
      exact Or.inl ⟨rfl, h.symm⟩
    | _ => cases h
  | retStack b l cs cl v =>
    cases v with
    | unit => exact Or.inr ⟨b, l, cs, cl, rfl, h⟩
    | _ => cases h

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
/-- `volatile_copy_memory::<u8>(p + d, p + s, n)` on the `[u8; 8]` fixture, for every in-bounds
`(d, s, n)` (disjoint, forward overlap, backward overlap, `n = 0`): Trusted, `Mach` and
`MachTB` all produce the bytes `memmoveSpec vbArr8 d s n`. -/
theorem lockstep_volatile_copy_memory_exhaustive :
    ∀ d, d < 9 → ∀ s, s < 9 → ∀ n, n < 9 → d + n ≤ 8 → s + n ≤ 8 →
      trustedActionBytes? vbArr8
          (trustedVolatileAction .volatileCopyMemory vbMem
            (vbTarget "core::intrinsics::volatile_copy_memory" vbTyU8) (vbDecls vbTyUnit)
            vbTbl [] [vbTPtr d, vbTPtr s, vbUsize n] (vbLocals vbArr8)) =
        some ((memmoveSpec vbArr8 d s n).map UInt8.toNat) ∧
      storedBytes (mrCopy (vbMach (vbPlain vbArr8)) (vbPtr d) (vbPtr s) n vbMrU8) =
        some [vbPlain (memmoveSpec vbArr8 d s n)] ∧
      storedBytesTB (mrCopyTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB d) (vbPtrTB s) n vbMrU8) =
        some [vbPlain (memmoveSpec vbArr8 d s n)] := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
/-- `volatile_copy_nonoverlapping_memory::<u8>(p + d, p + s, n)` on the fixture, for every
in-bounds `(d, s, n)`: Trusted reports `.fault .ub` exactly when the MiniRust-side overlap
predicate holds, and otherwise produces the bytes `memmoveSpec vbArr8 d s n`. -/
theorem lockstep_volatile_copy_nonoverlapping_exhaustive :
    ∀ d, d < 9 → ∀ s, s < 9 → ∀ n, n < 9 → d + n ≤ 8 → s + n ≤ 8 →
      trustedActionIsUb
          (trustedVolatileAction .volatileCopyNonOverlappingMemory vbMem
            (vbTarget "core::intrinsics::volatile_copy_nonoverlapping_memory" vbTyU8)
            (vbDecls vbTyUnit) vbTbl [] [vbTPtr d, vbTPtr s, vbUsize n] (vbLocals vbArr8)) =
        mrRangesOverlap (vbPtr d).addr (vbPtr s).addr n ∧
      (mrRangesOverlap (vbPtr d).addr (vbPtr s).addr n = false →
        trustedActionBytes? vbArr8
            (trustedVolatileAction .volatileCopyNonOverlappingMemory vbMem
              (vbTarget "core::intrinsics::volatile_copy_nonoverlapping_memory" vbTyU8)
              (vbDecls vbTyUnit) vbTbl [] [vbTPtr d, vbTPtr s, vbUsize n] (vbLocals vbArr8)) =
          some ((memmoveSpec vbArr8 d s n).map UInt8.toNat)) := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
/-- `volatile_set_memory::<u8>(p + d, 0xAB, n)` on the fixture, for every in-bounds `(d, n)`:
Trusted, `Mach` and `MachTB` all produce the bytes `fillSpec vbArr8 d n 0xAB`. -/
theorem lockstep_volatile_set_memory_exhaustive :
    ∀ d, d < 9 → ∀ n, n < 9 → d + n ≤ 8 →
      trustedActionBytes? vbArr8
          (trustedVolatileAction .volatileSetMemory vbMem
            (vbTarget "core::intrinsics::volatile_set_memory" vbTyU8) (vbDecls vbTyUnit)
            vbTbl [] [vbTPtr d, .scalar ⟨0xAB, 1⟩, vbUsize n] (vbLocals vbArr8)) =
        some ((fillSpec vbArr8 d n 0xAB).map UInt8.toNat) ∧
      storedBytes (mrSet (vbMach (vbPlain vbArr8)) (vbPtr d) 0xAB n vbMrU8) =
        some [vbPlain (fillSpec vbArr8 d n 0xAB)] ∧
      storedBytesTB (mrSetTB (vbMachTB (vbPlain vbArr8)) (vbPtrTB d) 0xAB n vbMrU8) =
        some [vbPlain (fillSpec vbArr8 d n 0xAB)] := by
  decide +kernel

/-- The `(bits, sizeBytes)` of the scalar a Trusted load action returned. -/
def trustedActionScalar? : RawPtrCallAction → Option (Nat × Nat)
  | .retBorrows _ (.scalar sc) => some (sc.bits, sc.sizeBytes)
  | .ret (.scalar sc) => some (sc.bits, sc.sizeBytes)
  | _ => none

/-- The MiniRust outcome is UB. -/
def interpIsUb {α : Type} : Interp.Interp α → Bool
  | .error (.ub _) => true
  | _ => false

/-- `interpIsUb r = true` means `r` is a UB error. -/
theorem interpIsUb_sound {α : Type} {r : Interp.Interp α} (h : interpIsUb r = true) :
    ∃ msg, r = .error (.ub msg) := by
  cases r with
  | ok a => cases h
  | error e =>
    cases e with
    | ub msg => exact ⟨msg, rfl⟩
    | _ => cases h

/-- `trustedActionScalar? a = some (bits, size)` means `a` returned the scalar `⟨bits, size⟩`. -/
theorem trustedActionScalar_sound {a : RawPtrCallAction} {bits size : Nat}
    (h : trustedActionScalar? a = some (bits, size)) :
    a = .ret (.scalar ⟨bits, size⟩) ∨
      ∃ borrows, a = .retBorrows borrows (.scalar ⟨bits, size⟩) := by
  cases a with
  | fault k => cases h
  | retStack b l cs cl v => cases h
  | ret v =>
    cases v with
    | scalar sc =>
      simp only [trustedActionScalar?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl rfl
    | _ => cases h
  | retBorrows b v =>
    cases v with
    | scalar sc =>
      simp only [trustedActionScalar?, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨b, rfl⟩
    | _ => cases h

set_option maxRecDepth 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
set_option synthInstance.maxSize 100000 in
/-- Unaligned `u32` load and store at every byte offset `o < 12` of the `[u8; 8]` fixture. In
bounds (`o + 4 ≤ 8`) the three semantics load the same integer, the little-endian value of
bytes `o..o + 4`, and store the same four bytes at `o..o + 4`. Out of bounds all three report
UB. -/
theorem lockstep_unaligned_load_store_exhaustive :
    ∀ o, o < 12 →
      (o + 4 ≤ 8 →
        trustedActionScalar?
            (trustedVolatileAction .unalignedVolatileLoad vbMem
              (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32)
              vbTbl [] [vbTPtr o] (vbLocals vbArr8)) =
          some (Interp.leValue ((vbArr8.drop o).take 4), 4) ∧
        loadedInt (mrLoad false (vbMach (vbPlain vbArr8)) (vbPtr o) vbMrU32) =
          some (Int.ofNat (Interp.leValue ((vbArr8.drop o).take 4)), [vbPlain vbArr8]) ∧
        loadedIntTB (mrLoadTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB o) vbMrU32) =
          some (Int.ofNat (Interp.leValue ((vbArr8.drop o).take 4)), [vbPlain vbArr8]) ∧
        trustedActionBytes? vbArr8
            (trustedVolatileAction .unalignedVolatileStore vbMem
              (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
              vbTbl [] [vbTPtr o, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8)) =
          some ((vbArr8.take o ++ [1, 2, 3, 4] ++ vbArr8.drop (o + 4)).map UInt8.toNat) ∧
        storedBytes (mrStore false (vbMach (vbPlain vbArr8)) (vbPtr o) (.Int 0x04030201)
            vbMrU32) =
          some [vbPlain (vbArr8.take o ++ [1, 2, 3, 4] ++ vbArr8.drop (o + 4))] ∧
        storedBytesTB (mrStoreTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB o)
            (.Int 0x04030201) vbMrU32) =
          some [vbPlain (vbArr8.take o ++ [1, 2, 3, 4] ++ vbArr8.drop (o + 4))]) ∧
      (8 < o + 4 →
        trustedActionIsUb
            (trustedVolatileAction .unalignedVolatileLoad vbMem
              (vbTarget "core::intrinsics::unaligned_volatile_load" vbTyU32) (vbDecls vbTyU32)
              vbTbl [] [vbTPtr o] (vbLocals vbArr8)) = true ∧
        interpIsUb (mrLoad false (vbMach (vbPlain vbArr8)) (vbPtr o) vbMrU32) = true ∧
        interpIsUb (mrLoadTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB o) vbMrU32) = true ∧
        trustedActionIsUb
            (trustedVolatileAction .unalignedVolatileStore vbMem
              (vbTarget "core::intrinsics::unaligned_volatile_store" vbTyU32) (vbDecls vbTyUnit)
              vbTbl [] [vbTPtr o, .scalar ⟨0x04030201, 4⟩] (vbLocals vbArr8)) = true ∧
        interpIsUb (mrStore false (vbMach (vbPlain vbArr8)) (vbPtr o) (.Int 0x04030201)
            vbMrU32) = true ∧
        interpIsUb (mrStoreTB false (vbMachTB (vbPlain vbArr8)) (vbPtrTB o) (.Int 0x04030201)
            vbMrU32) = true) := by
  decide +kernel

/-
Public theorems of this module, for registration in `MiniRustSpec/Audit.lean`.

Item 1 (alignment first):
  mr_bm_load_misaligned_ub, mr_bm_store_misaligned_ub, mr_tbm_load_misaligned_ub,
  mr_tbm_store_misaligned_ub, mr_bm_load_zero_len_ok, mr_bm_store_zero_len_ok,
  mr_tbm_load_zero_len_ok, mr_tbm_store_zero_len_ok, mr_typedLoad_misaligned_ub,
  mr_typedStore_misaligned_ub, mr_typedLoadM_tb_misaligned_ub, mr_typedStoreM_tb_misaligned_ub,
  mr_load_misaligned_ub, mr_loadTB_misaligned_ub, mr_store_misaligned_ub,
  mr_storeTB_misaligned_ub, mr_copy_src_misaligned_ub, mr_copy_dst_misaligned_ub,
  mr_copy_zero_misaligned_ub, mr_set_misaligned_ub, mr_copyTB_src_misaligned_ub,
  mr_copyTB_dst_misaligned_ub, mr_copyTB_zero_misaligned_ub, mr_setTB_misaligned_ub,
  trusted_unaligned_never_consults_alignment, trusted_addr_alignment_parity,
  trusted_global_target_aligned_iff, trusted_load_misaligned_ub, trusted_store_misaligned_ub,
  trusted_copy_misaligned_ub, trusted_set_misaligned_ub, mr_copy_misaligned_error,
  mr_copyTB_misaligned_error,
  volatile_load_misaligned_parity, volatile_store_misaligned_parity,
  volatile_copy_misaligned_parity, volatile_set_misaligned_parity,
  lockstep_volatile_load_misaligned, lockstep_volatile_load_zst_misaligned,
  lockstep_volatile_store_misaligned, lockstep_volatile_store_zst_misaligned,
  lockstep_volatile_copy_count0_misaligned, lockstep_volatile_copy_zst_misaligned,
  lockstep_volatile_set_count0_and_zst_misaligned, placement_dependent_alignment_witness

Item 2 (byte codec and bit validity):
  mr_endianness_decode_eq_intFromBits, codec_int_decode_agreement, codec_bool_validity_all_bytes,
  codec_bool_validity_all_bytes_general, codec_uninit_byte_invalid,
  lockstep_int_encode_round_trip, lockstep_pointer_bytes_provenance,
  lockstep_nonzero_validity, lockstep_char_validity, lockstep_bool_invalid_bit_pattern_ub,
  lockstep_never_uninhabited, trusted_encode_le_eq_leBytes, leValue_leBytes,
  codec_int_encode_agreement, leBytes_length, codec_int_round_trip, codec_usize_isize_agreement,
  codec_usize_isize_agreement_general

Item 3 (in-allocation unaligned accesses):
  lockstep_unaligned_load_offset1, lockstep_unaligned_store_offset1,
  lockstep_unaligned_out_of_bounds_ub, lockstep_unaligned_dead_allocation_ub,
  lockstep_unaligned_null_nonzst_ub, divergence_null_zst_read_write_unaligned,
  lockstep_unaligned_uninit_ub, lockstep_tree_borrows_conflict_ub,
  lockstep_tree_borrows_protector_conflict_ub, lockstep_unaligned_load_store_exhaustive

Item 4 (copy / set):
  lockstep_volatile_copy_dst_src_count_order, lockstep_volatile_copy_memory_memmove,
  lockstep_volatile_set_memory_fill, overlap_predicate_parity,
  lockstep_volatile_copy_nonoverlapping_overlap_ub, mr_bm_check_ptr_in_bounds,
  mr_bm_load_in_bounds, mr_bm_store_in_bounds, mr_copy_is_memmove, mr_set_is_fill,
  mr_tbm_check_ptr_in_bounds, mr_tbm_load_in_bounds, mr_tbm_store_in_bounds,
  mr_tbm_node_access_root_unique, mr_copyTB_is_memmove, mr_setTB_is_fill,
  mr_copyTB_root_unique_is_memmove, mr_setTB_root_unique_is_fill, splice_spec,
  lockstep_volatile_copy_memory_exhaustive, lockstep_volatile_copy_nonoverlapping_exhaustive,
  lockstep_volatile_set_memory_exhaustive

Item 5 (aligned addresses outside all allocations):
  trusted_volatile_load_mmio_unsupported, trusted_volatile_store_mmio_unsupported,
  trusted_volatile_copy_mmio_unsupported, trusted_volatile_set_mmio_unsupported,
  mr_bm_load_no_provenance_ub, mr_bm_store_no_provenance_ub, mr_tbm_load_no_provenance_ub,
  mr_tbm_store_no_provenance_ub, volatile_load_mmio_one_way_soundness, mirStep_fail_not_noUB,
  volatile_store_mmio_one_way_soundness, volatile_copy_mmio_one_way_soundness,
  volatile_set_mmio_one_way_soundness, mmio_volatile_load_step_unsupported,
  mmio_volatile_store_step_unsupported, mmio_volatile_not_noUB,
  mmio_volatile_copy_set_step_unsupported, mmio_volatile_copy_set_not_noUB,
  lockstep_mmio_aligned_0x40000000, unlinked_read_write_volatile_misaligned_parity,
  unlinked_read_volatile_misaligned_parity_any_ty,
  unlinked_read_write_volatile_mmio_one_way_soundness,
  unlinked_read_volatile_mmio_one_way_soundness,
  wit_unlinked_read_write_volatile_misaligned_and_mmio

Infrastructure (Trusted action specs, observation soundness):
  trustedVolatileAction_spec, trustedUnlinkedAction_spec, loadedInt_sound, loadedIntTB_sound,
  storedBytes_sound, storedBytesTB_sound, tDecodeIsUb_sound, mDecodeIsInvalid_sound,
  interp_ok_of_toOption, decodedInt_sound, decodedPtr_sound, decodedVariantInt_sound,
  trustedActionIsUb_sound, trustedActionBytes_sound, interpIsUb_sound, trustedActionScalar_sound
-/

end MiniRustSpec.Correspondence.VolatileBridge
