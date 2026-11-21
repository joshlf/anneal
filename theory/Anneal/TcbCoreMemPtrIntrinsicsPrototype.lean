/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import Trusted.Effect
import Trusted.ITree
import Trusted.Sequence
import Trusted.Rustc.V2026_06_01.Layout
import Trusted.Rustc.V2026_06_01.MirAst.Types
import Trusted.Rustc.V2026_06_01.MirAst.Places
import Trusted.Rustc.V2026_06_01.MirAst.Rvalues
import Trusted.Rustc.V2026_06_01.MirAst.Statements
import Trusted.Rustc.V2026_06_01.MirAst.Terminators
import Trusted.Rustc.V2026_06_01.MirAst.Body
import Trusted.Rustc.V2026_06_01.MirSemantics.State
import Trusted.Rustc.V2026_06_01.MirSemantics.Scalars
import Trusted.Rustc.V2026_06_01.MirSemantics.Bytes
import Trusted.Rustc.V2026_06_01.MirSemantics.Places
import Trusted.Rustc.V2026_06_01.MirSemantics.Statements
import Trusted.Rustc.V2026_06_01.MirSemantics.Terminators

namespace Anneal.TcbCoreMemPtrIntrinsicsPrototype

open Trusted.Refinement
open Trusted.Effect
open Trusted.ITree
open Trusted.Sequence
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-!
# Candidate TCB Operational Semantics for 8 Core Memory and Pointer Intrinsics

This standalone prototype module defines and validates drop-in candidate TCB
operational definitions over the real `Trusted.Rustc.V2026_06_01.MirSemantics`
state and AST types (`MachineState`, `Memory`, `LocalSlot`, `Value`,
`AbstractByte`, `ProvenancePtr`, `BorrowEntry`, `CapturedAllocation`,
`MirStepNode`, `FailureKind`, `LocalDecl`, `LayoutTable`, `Operand`, `Place`,
`RigidTy`, `ResolvedCallTarget`) for the eight core memory and pointer
intrinsics currently returning `.none` / `.unsupported` in
`Terminators.classifyRustIntrinsic?`:

1. `core::intrinsics::copy` (overlapping `memmove`)
2. `core::intrinsics::compare_bytes` (`memcmp`)
3. `core::intrinsics::raw_eq`
4. `core::intrinsics::typed_swap_nonoverlapping`
5. `core::intrinsics::ptr_offset_from`
6. `core::intrinsics::ptr_offset_from_unsigned`
7. `core::intrinsics::ptr_mask`
8. `core::intrinsics::black_box`

Every definition is total, structurally/fuel-bounded without `partial` or
`unsafe`, kernel-reducible, and documented with verbatim Rust Reference 1.98.0
and `library/core/src/intrinsics/mod.rs` citations matching the TCB conventions
of `Trusted.Rustc.V2026_06_01.MirSemantics.Terminators`.

This module is strictly a pre-promotion prototype: it is intentionally not
imported by `Anneal.lean` and does not modify `trusted/lean/`.
-/

/-! ## Section 1: Intrinsic Classification -/

/--
Candidate extension of `RustIntrinsicKind` adding the eight core memory and
pointer intrinsics to the existing 27 modeled `core::intrinsics::*` paths.

Only canonical `core::intrinsics::*` paths are recognized; wrapper functions
such as `core::ptr::copy`, `core::mem::swap`, or `core::hint::black_box` remain
ordinary MIR callees with their own precondition checks.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."
-/
inductive RustIntrinsicKindProto : Type where
  /-- One of the 27 existing `Trusted.Rustc.V2026_06_01.MirSemantics.RustIntrinsicKind` paths. -/
  | base (kind : RustIntrinsicKind) : RustIntrinsicKindProto
  /-- `core::intrinsics::copy`: overlapping byte copy (`memmove`). -/
  | copy : RustIntrinsicKindProto
  /-- `core::intrinsics::compare_bytes`: unsigned bytewise lexicographic comparison (`memcmp`). -/
  | compareBytes : RustIntrinsicKindProto
  /-- `core::intrinsics::raw_eq`: bytewise equality over initialized bytes of `&T`. -/
  | rawEq : RustIntrinsicKindProto
  /-- `core::intrinsics::typed_swap_nonoverlapping`: typed non-overlapping swap. -/
  | typedSwapNonOverlapping : RustIntrinsicKindProto
  /-- `core::intrinsics::ptr_offset_from`: signed same-allocation element distance. -/
  | ptrOffsetFrom : RustIntrinsicKindProto
  /-- `core::intrinsics::ptr_offset_from_unsigned`: non-negative same-allocation element distance. -/
  | ptrOffsetFromUnsigned : RustIntrinsicKindProto
  /-- `core::intrinsics::ptr_mask`: strict-provenance address masking without exposure. -/
  | ptrMask : RustIntrinsicKindProto
  /-- `core::intrinsics::black_box`: semantic identity preserving value, provenance, and validity. -/
  | blackBox : RustIntrinsicKindProto

/--
Classify a canonical `DefPath` into `RustIntrinsicKindProto`, recognizing the 8
new `core::intrinsics::*` paths and delegating the existing 27 paths to
`classifyRustIntrinsic?`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L1-L80>

> "Compiler intrinsics."
-/
@[reducible]
def classifyRustIntrinsicProto? (defPath : DefPath) : Option RustIntrinsicKindProto :=
  match stringEq defPath "core::intrinsics::copy" with
  | true => .some .copy
  | false =>
    match stringEq defPath "core::intrinsics::compare_bytes" with
    | true => .some .compareBytes
    | false =>
      match stringEq defPath "core::intrinsics::raw_eq" with
      | true => .some .rawEq
      | false =>
        match stringEq defPath "core::intrinsics::typed_swap_nonoverlapping" with
        | true => .some .typedSwapNonOverlapping
        | false =>
          match stringEq defPath "core::intrinsics::ptr_offset_from" with
          | true => .some .ptrOffsetFrom
          | false =>
            match stringEq defPath "core::intrinsics::ptr_offset_from_unsigned" with
            | true => .some .ptrOffsetFromUnsigned
            | false =>
              match stringEq defPath "core::intrinsics::ptr_mask" with
              | true => .some .ptrMask
              | false =>
                match stringEq defPath "core::intrinsics::black_box" with
                | true => .some .blackBox
                | false =>
                  match classifyRustIntrinsic? defPath with
                  | .some k => .some (.base k)
                  | .none => .none

/-! ## Section 2: Shared Low-Level Pointer, Alignment, Layout & Memory Helpers -/

/--
Decoded thin pointer argument: either a provenance-carrying `ProvenancePtr` or a
provenance-free integer address (such as `null`, `ptr::without_provenance`, or
an unexposed `usize as *const T` scalar).
-/
inductive PtrArgProto : Type where
  /-- Tracked pointer carrying allocation/borrow provenance and relative offset. -/
  | prov (ptr : ProvenancePtr) : PtrArgProto
  /-- Provenance-free integer address in `[0, 2^(8 * ptrBytes))`. -/
  | addr (bits : Nat) : PtrArgProto

/--
Decode a thin pointer argument value of target pointer width `ptrBytes`.
Rejects wide pointers, non-pointer scalars of wrong byte width, `.unit`, and
`.uninit` with `.none`.
-/
@[reducible]
def decodeThinPtrArgProto? (ptrBytes : Nat) : Value → Option PtrArgProto
  | .ptr p sz =>
    match Nat.beq sz ptrBytes with
    | true => .some (.prov p)
    | false => .none
  | .scalar sc =>
    match Nat.beq sc.sizeBytes ptrBytes with
    | true => .some (.addr (wrapScalarBits sc.bits (scalarModulus ptrBytes)))
    | false => .none
  | _ => .none

/--
Test whether `ptrArg` represents a null pointer (address `0` with no live
stack/global/function allocation backing it).

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "//! * A [null] pointer is *never* valid for reads/writes.
> //! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes.
> //!   The following points are only concerned with non-zero-sized accesses."
-/
@[reducible]
def isNullPtrArgProto (mem : Memory) : PtrArgProto → Bool
  | .addr bits => Nat.beq bits 0
  | .prov p =>
    match lookupBorrow mem.borrows p.tag with
    | .some _ => false
    | .none =>
      match lookupGlobalAlloc mem.globals p.allocId with
      | .some _ => false
      | .none =>
        match lookupFnPtr mem.fnPtrs p.allocId with
        | .some _ => false
        | .none => Bool.and (Nat.beq p.allocId 0) (Nat.beq p.offsetBytes 0)

/--
Resolve the pointee `RigidTy` `T` for a generic memory/pointer intrinsic
(`copy<T>`, `raw_eq<T>`, `typed_swap_nonoverlapping<T>`, `ptr_offset_from<T>`,
`ptr_offset_from_unsigned<T>`), consulting `target.typeArgs` first and falling
back to the pointee type of the first (or second) pointer operand in `argOps`.
-/
@[reducible]
def resolveMemIntrinsicPointeeTyProto?
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand) :
    Option RigidTy :=
  match target.typeArgs with
  | elemTy :: .nil => .some elemTy
  | .nil =>
    match argOps with
    | op0 :: rest =>
      match operandPointeeTy bodyLocalDecls bodyLayouts op0 with
      | .some pt => .some pt.kind
      | .none =>
        match rest with
        | op1 :: _ =>
          match operandPointeeTy bodyLocalDecls bodyLayouts op1 with
          | .some pt => .some pt.kind
          | .none => .none
        | .nil => .none
    | .nil => .none
  | _ :: _ :: _ => .none

/--
Test whether `n` is a positive power of two (`1, 2, 4, 8, ...`), using the
layout `Align.isPowerOfTwoBytes` predicate.
-/
@[reducible]
def isPowerOfTwoNatProto (n : Nat) : Bool :=
  Align.isPowerOfTwoBytes ⟨n⟩

/-- Higher-order list `any` helper so fuel-recursive functions remain purely structurally recursive. -/
@[reducible]
def anyListTrueProto {α : Type} (p : α → Bool) : List α → Bool
  | .nil => false
  | x :: rest =>
    match p x with
    | true => true
    | false => anyListTrueProto p rest

/--
Test whether `ty` is uninhabited (`!` or an ADT whose `LayoutTable` entry sets
`isUninhabited = true` or `variants = .empty`).

Reference (The Rust Reference, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "- A value of an uninhabited type (e.g. `!` or an enum with no variants)."
-/
@[reducible]
def isUninhabitedRigidTyProto
    (localDecls : List LocalDecl)
    (layouts : LayoutTable) :
    Nat → RigidTy → Bool
  | .zero, _ => false
  | .succ fuel', ty =>
    match ty with
    | .never => true
    | .array elem (.succ _) => isUninhabitedRigidTyProto localDecls layouts fuel' elem
    | .tuple ks => anyListTrueProto (isUninhabitedRigidTyProto localDecls layouts fuel') ks
    | .adt _ _ =>
      match findDeclLayoutForRigidTy localDecls layouts ty with
      | .some l =>
        match l.isUninhabited with
        | true => true
        | false =>
          match l.variants with
          | .empty => true
          | _ => false
      | .none => false
    | _ => false

/--
Test whether `ty` is a `FieldsShape.union` ADT in `localDecls` / `layouts`.
-/
@[reducible]
def rigidTyIsUnionProto
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy) :
    Bool :=
  match ty with
  | .adt _ _ =>
    match findDeclLayoutForRigidTy localDecls layouts ty with
    | .some l =>
      match l.fields with
      | .union _ => true
      | _ => false
    | .none => false
  | _ => false

/--
Resolve a `RigidTy` to a `Ty` carrying its `LayoutIdx` when a matching local
declaration exists in `localDecls`.
-/
@[reducible]
def resolveRigidTyWithDeclsProto
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (kind : RigidTy) :
    Ty :=
  resolveTyWithLocalDecls localDecls layouts { kind := kind, layoutIdx := unresolvedLayoutIdx layouts }

/--
Resolve the `(localDecls, layouts)` owning a stack borrow `entry` across both
the active frame and suspended caller frames.
-/
@[reducible]
def borrowTargetDeclsAndLayoutsProto
    (callStack : List SavedCallerFrame)
    (activeDecls : List LocalDecl)
    (activeLayouts : LayoutTable)
    (entry : BorrowEntry) :
    List LocalDecl × LayoutTable :=
  match callStack with
  | .nil => (activeDecls, activeLayouts)
  | _ :: _ =>
    match frameLocalDeclsAndLayoutsAtDepth callStack activeDecls activeLayouts entry.targetFrameDepth with
    | .some dl => dl
    | .none => (.nil, activeLayouts)

/--
Check that thin pointer `ptrArg` satisfies ABI alignment `reqAlign` (for all
valid placements of its backing allocation, matching Miri's symbolic alignment
check `Miri.Memory.checkPtrAlign` and `Terminators.writeBytesDstAddrAligned`).

When `reqAlign <= 1`, always returns `true`. Rejects:
- provenance-free addresses whose value is not a multiple of `reqAlign`;
- global allocations with `alloc.align.bytes < reqAlign` or misaligned offset;
- stack borrows whose enclosing place alignment is below `reqAlign` (e.g.
  `#[repr(packed)]` fields or lower-aligned stack locals) or whose total byte
  offset `placeOff + ptr.offsetBytes` is not a multiple of `reqAlign`.

Reference (The Rust Reference, "Size and Alignment"):
<https://doc.rust-lang.org/1.98.0/reference/type-layout.html#size-and-alignment>

> "A value of alignment n must only be stored at an address that is a multiple
> of n."
-/
def checkPtrArgAlignedProto
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrArg : PtrArgProto)
    (reqAlign : Nat) :
    Bool :=
  match Nat.ble reqAlign 1 with
  | true => true
  | false =>
    match ptrArg with
    | .addr bits => isAlignedOffset bits reqAlign
    | .prov p =>
      match lookupBorrow s.memory.borrows p.tag with
      | .some entry =>
        let (targetDecls, targetLayouts) :=
          borrowTargetDeclsAndLayoutsProto s.memory.callStack bodyLocalDecls bodyLayouts entry
        let walkOk : Bool :=
          match get? targetDecls entry.targetLocal with
          | .some rootDecl =>
            checkTargetPlaceAlignWalk
              targetDecls
              targetLayouts
              reqAlign
              p.offsetBytes
              (.some rootDecl.ty)
              .none
              .none
              entry.targetProjection
          | .none => isAlignedOffset p.offsetBytes reqAlign
        let offsetOk : Bool :=
          match borrowPlaceByteOffset? locals s.memory.callerLocals bodyLocalDecls bodyLayouts entry s.memory.callStack with
          | .some placeOff => isAlignedOffset (Nat.add placeOff p.offsetBytes) reqAlign
          | .none =>
            match entry.targetProjection with
            | .nil => isAlignedOffset p.offsetBytes reqAlign
            | _ :: _ => true
        Bool.and walkOk offsetOk
      | .none =>
        match lookupGlobalAlloc s.memory.globals p.allocId with
        | .some alloc =>
          Bool.and (Nat.ble reqAlign alloc.align.bytes) (isAlignedOffset p.offsetBytes reqAlign)
        | .none => isAlignedOffset p.offsetBytes reqAlign

/-! ## Section 3: Tree Borrows Read and Write Helpers -/

/--
Check Tree Borrows read permissions and apply the read permission transition for
a non-zero read through borrow tag `tag` (with entry `entry` in `borrows`) over
byte range `[accessOff, accessOff + accessLen)`.

Returns `.none` on any Tree Borrows read UB:
1. `entry.perm = .disabled`;
2. any ancestor of `entry` rejects a child read (`treeBorrowAncestorsChildAccessUB .read`);
3. any overlapping foreign entry in `borrows` faults on foreign read (e.g. a
   protected `.unique` or `.reservedIM` borrow, via `hasTreeReadUB`).

Otherwise returns `.some borrows'` with foreign `.unique` borrows frozen and
protected foreign `.reservedFrz false` borrows marked conflicted.

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
-/
def borrowsAfterReadAccessProto
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
    (tag : Nat)
    (entry : BorrowEntry)
    (accessOff accessLen : Nat) :
    Option (List BorrowEntry) :=
  match entry.perm with
  | .disabled => .none
  | _ =>
    let ancReadUB : Bool :=
      match borrows with
      | _ :: _ :: _ => treeBorrowAncestorsChildAccessUB .read borrows entry.parentTag
      | _ => false
    match ancReadUB with
    | true => .none
    | false =>
      let rOff :=
        match Nat.beq entry.rangeLen 0 with
        | true => accessOff
        | false => entry.rangeOffset
      let rLen :=
        match Nat.beq entry.rangeLen 0 with
        | true => accessLen
        | false => entry.rangeLen
      let readUB : Bool :=
        hasTreeReadUB
          borrows
          borrows
          activeProtectors
          entry.targetLocal
          (.some tag)
          entry.targetProjection
          rOff
          rLen
          entry.targetFrameDepth
      match readUB with
      | true => .none
      | false =>
        .some
          (freezeTreeBorrowsOnReadAtProj
            borrows
            borrows
            entry.targetLocal
            (.some tag)
            entry.targetProjection
            rOff
            rLen
            activeProtectors
            entry.targetFrameDepth)

/--
Check Tree Borrows write permissions and apply the write permission transition
for a non-zero write through borrow tag `tag` (with entry `entry` looked up in
the *current* post-read `borrows`) over byte range `[accessOff, accessOff + accessLen)`.

Returns `.none` on any Tree Borrows write UB:
1. `entry.perm` is `.frozen`, `.disabled`, or protected conflicted `.reservedFrz true`;
2. any ancestor of `entry` rejects a child write (`treeBorrowAncestorsChildAccessUB .write`);
3. any overlapping foreign protected borrow would be disabled
   (`hasProtectedTreeWriteConflict`).

Otherwise returns `.some borrows'` with self/ancestor reservations activated to
`.unique` and conflicting overlapping foreign borrows disabled.

Reference (Miri Tree Borrows implementation,
`src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs>
-/
def borrowsAfterWriteAccessProto
    (borrows : List BorrowEntry)
    (activeProtectors : List Nat)
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
      let wOff :=
        match Nat.beq entry.rangeLen 0 with
        | true => accessOff
        | false => entry.rangeOffset
      let wLen :=
        match Nat.beq entry.rangeLen 0 with
        | true => accessLen
        | false => entry.rangeLen
      let protConflict : Bool :=
        match activeProtectors with
        | .nil => false
        | _ :: _ =>
          hasProtectedTreeWriteConflict
            borrows
            borrows
            activeProtectors
            entry.targetLocal
            (.some tag)
            entry.targetProjection
            wOff
            wLen
            entry.targetFrameDepth
      match protConflict with
      | true => .none
      | false =>
        .some
          (invalidateTreeBorrowsAtProj
            borrows
            borrows
            entry.targetLocal
            (.some tag)
            entry.targetProjection
            wOff
            wLen
            entry.targetFrameDepth)

/-! ## Section 4: Unified Allocation Resolution & Abstract-Byte Storage Codec -/

/--
Canonical allocation identity for container-level same-allocation and
overlap/disjointness checks: either a stack/caller local `(frameDepth, localIdx)`
or a global allocation `allocId`.
-/
inductive AllocKeyProto : Type where
  /-- Stack or caller-owned local `(frameDepth, localIdx)`. -/
  | stack (frameDepth : Nat) (localIdx : LocalIdx) : AllocKeyProto
  /-- Global allocation `allocId` in `Memory.globals`. -/
  | global (allocId : AllocId) : AllocKeyProto
  deriving DecidableEq

/--
Resolved live memory endpoint backing a thin pointer argument.
-/
structure ResolvedMemEndpointProto : Type where
  /-- Canonical root allocation identity. -/
  key : AllocKeyProto
  /-- Byte offset of the pointer from byte `0` of the root allocation. -/
  effOffset : Nat
  /-- Total byte size of the root allocation. -/
  allocSize : Nat
  /-- Lower byte bound accessible through this provenance (`0` unless ranged borrow). -/
  accessLower : Nat
  /-- Exclusive upper byte bound accessible through this provenance. -/
  accessUpper : Nat
  /-- Whether writes to this allocation are permitted (`false` for immutable globals). -/
  writable : Bool
  /-- Backing borrow `(tag, entry)` for stack/caller locals, or `.none` for globals. -/
  borrowInfo? : Option (Nat × BorrowEntry)
  /-- `LocalDecl`s of the frame owning this local (empty for globals / caller referents). -/
  targetDecls : List LocalDecl
  /-- `LayoutTable` of the frame owning this local. -/
  targetLayouts : LayoutTable
  /-- Declared root type of the local allocation, if known. -/
  rootTyOpt : Option Ty
  /-- Current `LocalSlot` of the local allocation, if stack/caller-backed. -/
  rootSlot? : Option LocalSlot
  /-- Backing `CapturedAllocation`, if global-backed. -/
  globalAlloc? : Option CapturedAllocation

/-- Three-way outcome for internal resolution / byte-codec helpers. -/
inductive ProtoRes (α : Type) : Type where
  | ok (val : α) : ProtoRes α
  | ub : ProtoRes α
  | unsupported : ProtoRes α

/--
Resolve a thin pointer argument `ptrArg` to a live memory endpoint in
`(s, locals, borrows)`. Dangling, dead, provenance-free, or unknown-allocation
pointers return `.ub`; live stack borrows whose layout or projection offset
cannot be determined fail closed with `.unsupported`.
-/
def resolveLiveMemEndpointProto
    (s : MachineState)
    (locals : List LocalSlot)
    (borrows : List BorrowEntry)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrArg : PtrArgProto) :
    ProtoRes ResolvedMemEndpointProto :=
  match ptrArg with
  | .addr _ => .ub
  | .prov p =>
    match lookupBorrow borrows p.tag with
    | .some entry =>
      match entry.allocDead with
      | true => .ub
      | false =>
        let slotOpt :=
          readFrameLocalSlot
            locals
            s.memory.callStack
            s.memory.callerLocals
            entry.targetFrameDepth
            entry.targetLocal
        match slotOpt with
        | .none => .ub
        | .some .dead => .ub
        | .some slot =>
          let (targetDecls, targetLayouts) :=
            borrowTargetDeclsAndLayoutsProto s.memory.callStack bodyLocalDecls bodyLayouts entry
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
            let rootTyOpt : Option Ty :=
              match get? targetDecls entry.targetLocal with
              | .some decl => .some (resolveTyWithLocalDecls targetDecls targetLayouts decl.ty)
              | .none => .none
            let rootSizeOpt : Option Nat :=
              match rootTyOpt with
              | .some rTy =>
                match intrinsicRigidTyByteSize targetDecls targetLayouts rTy.kind with
                | .some sz => .some sz
                | .none => rigidTyByteSize targetLayouts rTy
              | .none =>
                match slot with
                | .init v => valueDefaultByteSize v
                | _ => .none
            match rootSizeOpt with
            | .none => .unsupported
            | .some rootSize =>
              let accessLower :=
                match Nat.beq entry.rangeLen 0 with
                | true => 0
                | false => entry.rangeOffset
              let accessUpper :=
                match Nat.beq entry.rangeLen 0 with
                | true => rootSize
                | false =>
                  let rEnd := Nat.add entry.rangeOffset entry.rangeLen
                  match Nat.ble rEnd rootSize with
                  | true => rEnd
                  | false => rootSize
              .ok
                { key := .stack entry.targetFrameDepth entry.targetLocal
                  effOffset := effOff
                  allocSize := rootSize
                  accessLower := accessLower
                  accessUpper := accessUpper
                  writable := true
                  borrowInfo? := .some (p.tag, entry)
                  targetDecls := targetDecls
                  targetLayouts := targetLayouts
                  rootTyOpt := rootTyOpt
                  rootSlot? := .some slot
                  globalAlloc? := .none }
    | .none =>
      match lookupGlobalAlloc s.memory.globals p.allocId with
      | .some alloc =>
        let allocSz := length alloc.bytes
        let writable :=
          match alloc.mutability with
          | .mut => true
          | .not => false
        .ok
          { key := .global alloc.allocId
            effOffset := p.offsetBytes
            allocSize := allocSz
            accessLower := 0
            accessUpper := allocSz
            writable := writable
            borrowInfo? := .none
            targetDecls := .nil
            targetLayouts := bodyLayouts
            rootTyOpt := .none
            rootSlot? := .none
            globalAlloc? := .some alloc }
      | .none => .ub

/--
Check whether byte slice `[ep.effOffset, ep.effOffset + len)` lies completely
within `[ep.accessLower, ep.accessUpper]` of `ep`.
-/
@[reducible]
def endpointRangeInBoundsProto (ep : ResolvedMemEndpointProto) (len : Nat) : Bool :=
  Bool.and
    (Nat.ble ep.accessLower ep.effOffset)
    (Nat.ble (Nat.add ep.effOffset len) ep.accessUpper)

/--
Test whether `v` is a leaf value whose untyped byte encoding
(`encodeUntypedValueToBytes`) is exact: a zero-sized unit, a scalar, a thin
pointer, or a field-less aggregate. The byte width of a leaf is intrinsic to
the value, so no layout information is needed to place its bytes.
-/
@[reducible]
def isLeafValueProto : Value → Bool
  | .unit => true
  | .scalar _ => true
  | .ptr _ _ => true
  | .aggregate _ .nil => true
  | _ => false

/-- Test whether every value in `vs` is a leaf (`isLeafValueProto`) or `Value.uninit`. -/
@[reducible]
def allLeafOrUninitValuesProto : List Value → Bool
  | .nil => true
  | .uninit :: rest => allLeafOrUninitValuesProto rest
  | v :: rest =>
    match isLeafValueProto v with
    | true => allLeafOrUninitValuesProto rest
    | false => false

/--
Test whether `vs` is array-shaped: every element is a `Value.scalar` or
`Value.ptr` of the same byte width `sz`.
-/
@[reducible]
def allSameSizeLeafValuesProto (sz : Nat) : List Value → Bool
  | .nil => true
  | .scalar sc :: rest =>
    match Nat.beq sc.sizeBytes sz with
    | true => allSameSizeLeafValuesProto sz rest
    | false => false
  | .ptr _ pSz :: rest =>
    match Nat.beq pSz sz with
    | true => allSameSizeLeafValuesProto sz rest
    | false => false
  | _ :: _ => false

/--
Test whether an untyped root value (a caller-owned referent with no `LocalDecl`)
has a byte image determined by the value alone: a leaf, or an array-shaped
aggregate of equal-width scalars / pointers (a byte or word buffer). Every other
untyped aggregate could contain padding, reordered fields, or an enum tag, so
its image is unknown.
-/
@[reducible]
def untypedValueHasExactByteImageProto : Value → Bool
  | .aggregate 0 (.scalar sc :: rest) => allSameSizeLeafValuesProto sc.sizeBytes rest
  | .aggregate 0 (.ptr _ pSz :: rest) => allSameSizeLeafValuesProto pSz rest
  | v => isLeafValueProto v

/--
Test whether every populated field value of a union has a byte image
determined by the value alone (`untypedValueHasExactByteImageProto`: a leaf or
an array-shaped buffer such as the `[u8; N]` payload of `MaybeUninit<[u8; N]>`),
or is `Value.uninit`. Union fields all start at offset `0`, so such a field's
bytes are placed exactly by `encodeUnionStorageBytes`; any other nested
aggregate would be encoded without its padding.
-/
@[reducible]
def allUnionFieldValuesExactProto : List Value → Bool
  | .nil => true
  | .uninit :: rest => allUnionFieldValuesExactProto rest
  | v :: rest =>
    match untypedValueHasExactByteImageProto v with
    | true => allUnionFieldValuesExactProto rest
    | false => false

/--
Higher-order at-offset field writer enforcing an EXACT byte length per field:
field `i` (described by key `keys[i]`, a field type or a field layout index) is
encoded by `encodeField`, must be exactly `fieldSize keys[i]` bytes long, and is
written at `offsets[i]` into `buf`. Any unknown field size, length mismatch, or
out-of-range write yields `.none`.

`Bytes.encodeFieldsAtOffsetsWith` writes whatever byte list the field encoder
returns, so a nested aggregate encoded without its padding is silently placed
at the field offset; this helper rejects that.
-/
@[reducible]
def encodeFieldsAtOffsetsExactWith {κ : Type}
    (encodeField : κ → Value → Option (List AbstractByte))
    (fieldSize : κ → Option Nat) :
    List Size → List κ → List Value → List AbstractByte → Option (List AbstractByte)
  | .nil, .nil, .nil, buf => .some buf
  | off :: offRest, k :: kRest, fv :: fvRest, buf =>
    match encodeField k fv, fieldSize k with
    | .some fb, .some fSz =>
      match Nat.beq (length fb) fSz with
      | false => .none
      | true =>
        match writeAbstractBytesAt buf off.bytes fb with
        | .none => .none
        | .some buf' =>
          encodeFieldsAtOffsetsExactWith encodeField fieldSize offRest kRest fvRest buf'
    | _, _ => .none
  | _, _, _, _ => .none

/--
At-offset writer for fields whose types and layouts are unknown: every field
value must be a leaf (`isLeafValueProto`), whose byte width is intrinsic, and is
written at its layout offset. A nested aggregate yields `.none`.
-/
@[reducible]
def encodeLeafFieldsAtOffsetsProto :
    List Size → List Value → List AbstractByte → Option (List AbstractByte)
  | .nil, .nil, buf => .some buf
  | off :: offRest, fv :: fvRest, buf =>
    match isLeafValueProto fv with
    | false => .none
    | true =>
      match encodeUntypedValueToBytes 2 fv with
      | .none => .none
      | .some fb =>
        match writeAbstractBytesAt buf off.bytes fb with
        | .none => .none
        | .some buf' => encodeLeafFieldsAtOffsetsProto offRest fvRest buf'
  | _, _, _ => .none

/--
Exact layout-directed byte encoder: encode `v` at `LayoutTable` entry `lIdx`,
taking every field offset, element stride, and nested field layout from the
table (`TypeLayout.fields` and `TypeLayout.fieldLayouts`), never from a guess.

- `Value.uninit` encodes as `size` uninitialized bytes.
- A primitive entry takes a leaf of exactly `size` bytes.
- An array entry (`FieldsShape.array`) needs its element layout
  (`fieldLayouts = [elemIdx]`) and encodes `count` elements of exactly `stride`
  bytes each.
- A struct-like entry (`FieldsShape.arbitrary`, single variant) writes each
  field at its offset: by its field layout when `fieldLayouts` is recorded
  (exact length enforced), else only when every field value is a leaf (this
  covers a wide pointer's `(data, metadata)` pair).
- A union entry takes `encodeUnionStorageBytes` when every populated field is a
  leaf or an array-shaped buffer (`allUnionFieldValuesExactProto`; its fields
  share offset `0`, and their widths are intrinsic).
- Multi-variant enums and every unlisted shape yield `.none`: the caller fails
  closed with `.unsupported` rather than fabricating a byte image.
-/
def encodeValueAtLayoutIdxProto :
    Nat → LayoutTable → Nat → Value → Option (List AbstractByte)
  | .zero, _, _, _ => .none
  | .succ fuel', layouts, lIdx, v =>
    match LayoutTable.lookup layouts lIdx with
    | .none => .none
    | .some l =>
      match v with
      | .uninit => .some (replicateUninitBytes l.size.bytes)
      | _ =>
        match l.variants with
        | .single _ =>
          let checkSize := fun (bsOpt : Option (List AbstractByte)) =>
            match bsOpt with
            | .some bs =>
              match Nat.beq (length bs) l.size.bytes with
              | true => .some bs
              | false => .none
            | .none => .none
          match l.fields with
          | .primitive =>
            match isLeafValueProto v with
            | true => checkSize (encodeUntypedValueToBytes 2 v)
            | false => .none
          | .union _ =>
            match v with
            | .aggregate _ fieldVals =>
              match allUnionFieldValuesExactProto fieldVals with
              | true => .some (encodeUnionStorageBytes layouts l.size.bytes .none fieldVals)
              | false => .none
            | _ => .none
          | .array stride count =>
            match v, l.fieldLayouts with
            | .aggregate 0 elems, elemIdx :: .nil =>
              match Nat.beq (length elems) count with
              | false => .none
              | true =>
                checkSize
                  (encodeListWith
                    (encodeValueAtLayoutIdxProto fuel' layouts elemIdx)
                    stride.bytes
                    elems)
            | _, _ => .none
          | .arbitrary offsets _ =>
            match v with
            | .aggregate _ (fv :: fvRest) =>
              let fieldVals := fv :: fvRest
              match Nat.beq (length l.fieldLayouts) (length offsets) with
              | true =>
                encodeFieldsAtOffsetsExactWith
                  (encodeValueAtLayoutIdxProto fuel' layouts)
                  (fun fIdx =>
                    match LayoutTable.lookup layouts fIdx with
                    | .some fl => .some fl.size.bytes
                    | .none => .none)
                  offsets
                  l.fieldLayouts
                  fieldVals
                  (replicateUninitBytes l.size.bytes)
              | false =>
                encodeLeafFieldsAtOffsetsProto
                  offsets
                  fieldVals
                  (replicateUninitBytes l.size.bytes)
            | .aggregate _ .nil | .unit =>
              match offsets with
              | .nil => .some (replicateUninitBytes l.size.bytes)
              | _ :: _ => .none
            | _ => .none
        | _ => .none

/--
Exact raw byte encoder for a runtime `Value` at type `ty`: the result is either
the precise byte image of `v` in memory or `.none` (callers fail closed with
`.unsupported`). It never falls back to a sequential, padding-free guess.

1. `Value.uninit` encodes as `replicateUninitBytes size` (preserving the exact
   byte width of uninitialized fields in partially initialized aggregates).
2. Scalar and pointer kinds use `Bytes.encodeValueToBytes`, plus the raw bytes
   of a `bool` / `char` slot holding an invalid bit pattern (so typed validators
   such as `typed_swap_nonoverlapping` observe the invalid byte and report
   `.ub` rather than `.unsupported`).
3. Arrays encode each element at the element type with its exact element size.
4. Tuples require their `LayoutTable` entry and write every field at its layout
   offset with its exact field size, leaving inter-field and trailing padding
   as `AbstractByte.uninit`.
5. ADTs and closures are encoded from their layout entry alone
   (`encodeValueAtLayoutIdxProto`): their generic arguments are not their field
   types. A multi-variant enum is delegated to `Bytes.encodeValueToBytes` only
   when every payload value is a leaf.

`Bytes.encodeValueToBytes` is deliberately not used for composite types: it
encodes nested field types at `layoutIdx := 0`, treats an ADT's generic
arguments as its field types, and encodes untyped nested aggregates back to
back, so a nested padded struct (`struct Outer { inner: (u8, u32) }`) would be
laid out without its padding.
-/
def encodeRawValueBytesProto :
    Nat → List LocalDecl → LayoutTable → Ty → Value → Option (List AbstractByte)
  | .zero, _, _, _, _ => .none
  | .succ fuel', localDecls, layouts, ty, v =>
    let normTy := normalizeCodecTy ty
    match v with
    | .uninit =>
      match intrinsicRigidTyByteSize localDecls layouts normTy.kind with
      | .some sz => .some (replicateUninitBytes sz)
      | .none =>
        match rigidTyByteSize layouts normTy with
        | .some sz => .some (replicateUninitBytes sz)
        | .none => .none
    | _ =>
      match normTy.kind with
      | .array elemKind n =>
        match v with
        | .aggregate 0 elems =>
          match Nat.beq (length elems) n with
          | false => .none
          | true =>
            let elemTy := resolveRigidTyWithDeclsProto localDecls layouts elemKind
            match intrinsicRigidTyByteSize localDecls layouts elemKind with
            | .none => .none
            | .some elemSz =>
              encodeListWith
                (fun e => encodeRawValueBytesProto fuel' localDecls layouts elemTy e)
                elemSz
                elems
        | _ => .none
      | .tuple (kHead :: kTail) =>
        let fieldKinds := kHead :: kTail
        match v with
        | .aggregate 0 fieldVals =>
          match LayoutTable.lookup layouts normTy.layoutIdx with
          | .some l =>
            match l.fields with
            | .arbitrary offsets _ =>
              encodeFieldsAtOffsetsExactWith
                (fun (k : RigidTy) (fv : Value) =>
                  encodeRawValueBytesProto fuel' localDecls layouts
                    (resolveRigidTyWithDeclsProto localDecls layouts k) fv)
                (intrinsicRigidTyByteSize localDecls layouts)
                offsets
                fieldKinds
                fieldVals
                (replicateUninitBytes l.size.bytes)
            | _ => .none
          | .none => .none
        | _ => .none
      | .adt _ _ | .closure _ _ =>
        match encodeValueAtLayoutIdxProto fuel' layouts normTy.layoutIdx v with
        | .some bs => .some bs
        | .none =>
          match LayoutTable.lookup layouts normTy.layoutIdx, v with
          | .some { variants := .multiple _ _ _, .. }, .aggregate _ payload =>
            match allLeafOrUninitValuesProto payload with
            | true => encodeValueToBytes fuel' layouts normTy v
            | false => .none
          | _, _ => .none
      | _ =>
        match encodeValueToBytes fuel' layouts normTy v with
        | .some bs => .some bs
        | .none =>
          match normTy.kind, v with
          -- Preserve raw bytes of invalid `bool` / `char` scalars for raw reads & typed validation.
          | .bool, .scalar sv =>
            match Nat.beq sv.sizeBytes 1 with
            | true => encodeScalarBytes sv .none
            | false => .none
          | .char, .scalar sv =>
            match Nat.beq sv.sizeBytes 4 with
            | true => encodeScalarBytes sv .none
            | false => .none
          | _, _ => .none

/-- Bytewise equality of two `AbstractByte`s (initialization, value, and provenance). -/
@[reducible]
def abstractByteEqProto : AbstractByte → AbstractByte → Bool
  | .uninit, .uninit => true
  | .init a pa, .init b pb =>
    match Nat.beq a.toBitVec.toNat b.toBitVec.toNat with
    | false => false
    | true =>
      match pa, pb with
      | .none, .none => true
      | .some (aId, aTag), .some (bId, bTag) => Bool.and (Nat.beq aId bId) (Nat.beq aTag bTag)
      | _, _ => false
  | _, _ => false

/--
`abstractBytesRefineProto stored intended`: `stored` is `intended` with zero or
more bytes replaced by `AbstractByte.uninit`, and every other byte equal in
value and provenance.

Used to accept a decoded `Value` only when re-encoding it reproduces the bytes
that were meant to be stored. Demoting a byte to `.uninit` is the one allowed
difference (a structured `Value` cannot hold an initialized padding byte): it
can only turn a later read of that byte into `.ub`, never change a result or
make an invalid value valid.
-/
@[reducible]
def abstractBytesRefineProto : List AbstractByte → List AbstractByte → Bool
  | .nil, .nil => true
  | .uninit :: sRest, _ :: iRest => abstractBytesRefineProto sRest iRest
  | sByte :: sRest, iByte :: iRest =>
    match abstractByteEqProto sByte iByte with
    | true => abstractBytesRefineProto sRest iRest
    | false => false
  | _, _ => false

/--
Read the full abstract byte buffer of resolved endpoint `ep` (length
`ep.allocSize`).
-/
def readRootAbstractBytesProto (ep : ResolvedMemEndpointProto) : ProtoRes (List AbstractByte) :=
  match ep.globalAlloc? with
  | .some alloc =>
    match globalAllocSliceToAbstractBytes alloc 0 ep.allocSize with
    | .some bs => .ok bs
    | .none => .ub
  | .none =>
    match ep.rootSlot? with
    | .some .uninit => .ok (replicateUninitBytes ep.allocSize)
    | .some (.init rootVal) =>
      match ep.key with
      | .stack _ localIdx =>
        match localDeclIsUnion ep.targetDecls ep.targetLayouts localIdx with
        | true =>
          let unionFields : List Value :=
            match rootVal with
            | .aggregate _ fs => fs
            | other => other :: .nil
          -- Union fields share offset `0`; a populated field's bytes are exact
          -- only when it is a leaf or an array-shaped buffer (any other nested
          -- aggregate would be encoded untyped, without its padding).
          match allUnionFieldValuesExactProto unionFields with
          | true => .ok (encodeUnionStorageBytes ep.targetLayouts ep.allocSize .none unionFields)
          | false => .unsupported
        | false =>
          match ep.rootTyOpt with
          | .some rTy =>
            match encodeRawValueBytesProto defaultCodecFuel ep.targetDecls ep.targetLayouts rTy rootVal with
            | .some bs =>
              match Nat.beq (length bs) ep.allocSize with
              | true => .ok bs
              | false => .unsupported
            | .none => .unsupported
          | .none =>
            -- Untyped caller-owned referent: only a leaf or an array-shaped
            -- buffer has a byte image determined by the value alone.
            match untypedValueHasExactByteImageProto rootVal with
            | false => .unsupported
            | true =>
              match encodeUntypedValueToBytes defaultCodecFuel rootVal with
              | .some bs =>
                match Nat.beq (length bs) ep.allocSize with
                | true => .ok bs
                | false => .unsupported
              | .none => .unsupported
      | .global _ => .unsupported
    | _ => .ub

/-- Test whether every `AbstractByte` in `bs` is `.uninit`. -/
@[reducible]
def allBytesUninitProto : List AbstractByte → Bool
  | .nil => true
  | .uninit :: rest => allBytesUninitProto rest
  | .init _ _ :: _ => false

/--
Decode a byte sequence into a `Value` for a non-union root local when all bytes
are valid, or when an array/struct/tuple has individual all-`.uninit` fields
(decoded as `Value.uninit`). Returns `.none` if any scalar/field has invalid
bit patterns or partial initialization that cannot be represented in `LocalSlot`
(callers fail closed with `.unsupported`).
-/
def decodePartialUninitValueProto :
    Nat → List LocalDecl → LayoutTable → Ty → List AbstractByte → Option Value
  | .zero, _, _, _, _ => .none
  | .succ fuel', localDecls, layouts, ty, bytes =>
    let normTy := normalizeCodecTy ty
    match decodeValueFromBytes fuel' layouts normTy bytes with
    | .some v => .some v
    | .none =>
      match allBytesUninitProto bytes with
      | true => .some .uninit
      | false =>
        match normTy.kind with
        | .array elemKind n =>
          match intrinsicRigidTyByteSize localDecls layouts elemKind with
          | .none => .none
          | .some elemSz =>
            match Nat.beq (length bytes) (Nat.mul elemSz n) with
            | false => .none
            | true =>
              let elemTy := resolveRigidTyWithDeclsProto localDecls layouts elemKind
              match
                decodeArrayChunksWith
                  (fun chunk => decodePartialUninitValueProto fuel' localDecls layouts elemTy chunk)
                  elemSz
                  n
                  bytes
              with
              | .some elems => .some (.aggregate 0 elems)
              | .none => .none
        | .tuple (kHead :: kTail) =>
          let fieldKinds := kHead :: kTail
          let decodeTyped := fun (k : RigidTy) (bs : List AbstractByte) =>
            decodePartialUninitValueProto fuel' localDecls layouts
              (resolveRigidTyWithDeclsProto localDecls layouts k) bs
          let sizeOfKind := fun (k : RigidTy) =>
            intrinsicRigidTyByteSize localDecls layouts k
          match LayoutTable.lookup layouts normTy.layoutIdx with
          | .some l =>
            match Nat.beq (length bytes) l.size.bytes, l.fields with
            | true, .arbitrary offsets _ =>
              match decodeFieldsAtOffsetsWith decodeTyped sizeOfKind bytes offsets fieldKinds with
              | .some vals => .some (.aggregate 0 vals)
              | .none => .none
            | _, _ => .none
          | .none =>
            match decodeSeqFieldsWith decodeTyped sizeOfKind fieldKinds bytes with
            | .some vals => .some (.aggregate 0 vals)
            | .none => .none
        | _ => .none

/--
Convert a `List AbstractByte` back into a `CapturedAllocation`'s byte mask and
relocation list.
-/
def abstractBytesToGlobalDataProto
    (ptrBytes : Nat)
    (absBytes : List AbstractByte) :
    List (Option UInt8) × List (Nat × ProvenancePtr) :=
  let rawMask : List (Option UInt8) :=
    let rec toMask : List AbstractByte → List (Option UInt8)
      | .nil => .nil
      | .uninit :: rest => .none :: toMask rest
      | .init b _ :: rest => .some b :: toMask rest
    toMask absBytes
  let relocs : List (Nat × ProvenancePtr) :=
    let rec scan : Nat → Nat → List AbstractByte → List (Nat × ProvenancePtr)
      | .zero, _, _ => .nil
      | .succ _, _, .nil => .nil
      | .succ fuel', off, bs =>
        match Nat.ble ptrBytes (length bs) with
        | false => .nil
        | true =>
          let chunk := takeAbstractBytes ptrBytes bs
          match decodeScalarBytes chunk false with
          | .some (sv, .some (allocId, _)) =>
            (off, { allocId := allocId, offsetBytes := sv.bits }) ::
              scan fuel' (Nat.add off ptrBytes) (dropAbstractBytes ptrBytes bs)
          | _ =>
            match bs with
            | .nil => .nil
            | _ :: rest => scan fuel' (Nat.add off 1) rest
    scan (length absBytes) 0 absBytes
  (rawMask, relocs)

/--
Update the global allocation with `allocId` in `globals`.
-/
def updateGlobalAllocProto :
    List CapturedAllocation → AllocId → CapturedAllocation → Option (List CapturedAllocation)
  | .nil, _, _ => .none
  | a :: rest, allocId, updated =>
    match Nat.beq a.allocId allocId with
    | true => .some (updated :: rest)
    | false =>
      match updateGlobalAllocProto rest allocId updated with
      | .some rest' => .some (a :: rest')
      | .none => .none

/--
Commit an updated root abstract byte buffer `updatedBytes` back to the backing
storage of endpoint `ep`, updating either the owning stack/caller frame's
`LocalSlot` or the mutable global allocation in `globals`.

A stack local stores a structured `Value`, so the bytes are decoded at the
local's declared type and the decoded value is accepted only when it
**round-trips**: re-encoding it with the exact encoder
(`encodeRawValueBytesProto`) must reproduce `updatedBytes`, up to bytes demoted
to `.uninit` (`abstractBytesRefineProto`). A decode that would misplace a field,
drop a pointer fragment's provenance, or strip provenance from an integer slot
therefore fails closed with `.unsupported` instead of storing a value whose
memory image differs from the bytes written. A union local whose decoded
fields do not round-trip is reset to its uninitialized state, which refines
every byte image.
-/
def commitRootAbstractBytesProto
    (locals : List LocalSlot)
    (callStack : List SavedCallerFrame)
    (callerLocals : List LocalSlot)
    (globals : List CapturedAllocation)
    (ptrBytes : Nat)
    (ep : ResolvedMemEndpointProto)
    (updatedBytes : List AbstractByte) :
    ProtoRes (List LocalSlot × List SavedCallerFrame × List LocalSlot × List CapturedAllocation) :=
  match ep.key with
  | .global allocId =>
    match ep.writable, ep.globalAlloc? with
    | false, _ => .ub
    | true, .some alloc =>
      let (rawMask, relocs) := abstractBytesToGlobalDataProto ptrBytes updatedBytes
      let alloc' : CapturedAllocation := { alloc with bytes := rawMask, relocations := relocs }
      match updateGlobalAllocProto globals allocId alloc' with
      | .some globals' => .ok (locals, callStack, callerLocals, globals')
      | .none => .ub
    | true, .none => .ub
  | .stack frameDepth localIdx =>
    let newSlotRes : ProtoRes LocalSlot :=
      match allBytesUninitProto updatedBytes with
      | true =>
        match localDeclIsUnion ep.targetDecls ep.targetLayouts localIdx with
        | false => .ok .uninit
        | true =>
          let (uVar, uFields) : VariantIdx × List Value :=
            match ep.rootSlot? with
            | .some (.init (.aggregate vIdx fs)) => (vIdx, fs)
            | _ => (0, .nil)
          .ok (.init (.aggregate uVar (resetUnionFields uFields)))
      | false =>
        match localDeclIsUnion ep.targetDecls ep.targetLayouts localIdx with
        | true =>
          let (uVar, uFields) : VariantIdx × List Value :=
            match ep.rootSlot? with
            | .some (.init (.aggregate vIdx fs)) => (vIdx, fs)
            | .some (.init other) => (0, other :: .nil)
            | _ => (0, .nil)
          let decodedOpt : Option Value :=
            match ep.rootTyOpt with
            | .some rTy => decodeValueFromBytes defaultCodecFuel ep.targetLayouts rTy updatedBytes
            | .none => .none
          let decodedFields : List Value :=
            match decodedOpt with
            | .some (.aggregate _ fs) => fs
            | .some other => other :: .nil
            | .none => .nil
          let roundTrips : Bool :=
            match decodedOpt with
            | .none => false
            | .some _ =>
              Bool.and
                (allUnionFieldValuesExactProto decodedFields)
                (abstractBytesRefineProto
                  (encodeUnionStorageBytes ep.targetLayouts ep.allocSize .none decodedFields)
                  updatedBytes)
          match decodedOpt, roundTrips with
          | .some dv, true => .ok (.init dv)
          | _, _ => .ok (.init (.aggregate uVar (resetUnionFields uFields)))
        | false =>
          match ep.rootTyOpt with
          | .some rTy =>
            match decodePartialUninitValueProto defaultCodecFuel ep.targetDecls ep.targetLayouts rTy updatedBytes with
            | .some dv =>
              -- Round-trip guard: store `dv` only if its exact byte image is the
              -- intended bytes (up to demoting bytes to `.uninit`).
              match encodeRawValueBytesProto defaultCodecFuel ep.targetDecls ep.targetLayouts rTy dv with
              | .some stored =>
                match abstractBytesRefineProto stored updatedBytes with
                | true => .ok (.init dv)
                | false => .unsupported
              | .none => .unsupported
            | .none => .unsupported
          | .none =>
            match ep.rootSlot? with
            | .some (.init (.scalar oldSc)) =>
              match decodeScalarBytes updatedBytes false with
              | .some (sv, .none) =>
                match Nat.beq sv.sizeBytes oldSc.sizeBytes with
                | true => .ok (.init (.scalar sv))
                | false => .unsupported
              | _ => .unsupported
            | .some (.init (.ptr _ oldSz)) =>
              match decodeScalarBytes updatedBytes false with
              | .some (sv, .some (aid, _)) =>
                match Nat.beq sv.sizeBytes oldSz with
                | true => .ok (.init (.ptr { allocId := aid, offsetBytes := sv.bits } oldSz))
                | false => .unsupported
              | _ => .unsupported
            | _ => .unsupported
    match newSlotRes with
    | .ub => .ub
    | .unsupported => .unsupported
    | .ok newSlot =>
      match writeFrameLocalSlot locals callStack callerLocals frameDepth localIdx newSlot with
      | .some (locals', callStack', callerLocals') =>
        .ok (locals', callStack', callerLocals', globals)
      | .none => .ub

/-! ## Section 5: Destination Return Helper (Supporting Diverging `target = none`) -/

/--
Write an intrinsic return value `retVal` to `destination` and transition to
`targetOpt`:
- When `targetOpt = .none` (diverging call to a returning intrinsic), faults
  with `MirStepNode.fail .ub` matching Miri's `returnToBlock choice none`;
- Checks active function-entry protectors on direct (non-deref) destination
  writes before delegating to `Terminators.writeIntrinsicReturn`.

Reference (`compiler/rustc_middle/src/mir/syntax.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/compiler/rustc_middle/src/mir/syntax.rs#L800-L814>

> "Call { ... destination: Place<'tcx>, target: Option<BasicBlock>, ... }"
-/
def writeIntrinsicReturnProto
    (s : MachineState)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx)
    (retVal : Value)
    (bodyLocalDecls : List LocalDecl := .nil)
    (bodyLayouts : LayoutTable := emptyLayoutTable) :
    MirStepNode :=
  match targetOpt with
  | .none => MirStepNode.fail .ub
  | .some targetBb =>
    match destination.projection with
    | .deref :: _ =>
      writeIntrinsicReturn s locals' destination targetBb retVal
    | proj =>
      let protConflict : Bool :=
        match s.memory.activeProtectors with
        | .nil => false
        | _ :: _ =>
          let resolvedProj :=
            match proj with
            | .nil => .nil
            | _ :: _ =>
              resolveBorrowWriteLocalProj bodyLocalDecls bodyLayouts locals' destination.local_ proj
          hasProtectedWriteConflict
            s.memory.borrows
            s.memory.activeProtectors
            destination.local_
            .none
            resolvedProj
            0
            0
            (length s.memory.callStack)
      match protConflict with
      | true => MirStepNode.fail .ub
      | false => writeIntrinsicReturn s locals' destination targetBb retVal

/-! ## Section 6: Intrinsic 1 — `core::intrinsics::copy` (Overlapping `memmove`) -/

/--
Core memory-effect evaluator for `core::intrinsics::copy<T>(src, dst, count)`
(overlapping `memmove`), advancing the statement counter via `advanceStmt` on
success so it can be used both by statement-form stepping (`evalCopyStmtProto`)
and call-form wrapping (`evalCopyProto` via `finishMemIntrinsicCall`).

Exact operational order (aligned with `lean-miri` `Intrinsics.copyWith ... false`
at `Miri/Interpreter/Intrinsics.lean:143-161` and `MemoryState.memCopyRepeatedly`):
1. Validate argument shapes (`src`, `dst` thin pointers of width `ptrBytes`;
   `count` a `usize` scalar) and resolve sized `T` (`elemSize`, `elemAlign`).
2. Overflow check: `elemSize * count <= isize::MAX` (else `.ub`).
3. ABI alignment (`align_of::<T>()`) checks on BOTH `src` and `dst` **even when
   `elemSize * count == 0`** (a misaligned pointer is `.ub` even at 0 bytes).
4. If `totalBytes == 0`: succeed without touching memory or borrow permissions.
   No validity requirement applies to a zero-byte copy, so aligned dangling,
   provenance-free, and null pointers all succeed as a no-op: the pinned
   `ptr::copy` contract requires validity "or that number must be 0", and
   `Miri.Memory.checkAndDerefPtr` (`Miri/Memory/Access.lean:134-150`) returns
   `none` for a zero-sized access before resolving the pointer
   (`zero_sized_check_skips_resolution`). A null pointer with `totalBytes > 0`
   faults `.ub` in Phase A / Phase B (no live allocation backs it).
5. **Phase A (Source Read & Snapshot)**: resolve live `src`, verify
   `[srcEffOff, srcEffOff + totalBytes)` in bounds, apply Tree Borrows read
   check and transition (`borrowsAfterReadAccessProto` -> `borrows₁`), and
   extract the full `totalBytes`-byte snapshot (preserving `.uninit` bytes and
   pointer provenance).
6. **Phase B (Destination Write on `borrows₁`)**: resolve live writable `dst`
   in the **post-read** borrow state `borrows₁` (so a `dst` tag frozen by Phase
   A's read faults `.ub`!), verify `[dstEffOff, dstEffOff + totalBytes)` in
   bounds, apply Tree Borrows write check and transition
   (`borrowsAfterWriteAccessProto` -> `borrows₂`), patch the snapshot into
   `dst`'s root buffer (supporting arbitrary forward/backward/identical overlap
   without clobbering unread source bytes), and commit.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L3030-L3039>

> "/// This is an accidentally-stable alias to [`ptr::copy`]; use that instead."
> "pub const unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize);"

Reference (`core::ptr::copy` documentation, `library/core/src/ptr/mod.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L554-L589>

> "/// Copies `count * size_of::<T>()` bytes from `src` to `dst`. The source
> /// and destination may overlap."
>
> "/// Copying takes place as if the bytes were copied from `src`
> /// to a temporary array and then copied from the array to `dst`.
> ///
> /// The copy is \"untyped\" in the sense that data may be uninitialized or otherwise violate the
> /// requirements of `T`. The initialization state is preserved exactly."
>
> "/// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * `src` must be [valid] for reads of `count * size_of::<T>()` bytes or that number must be 0.
> ///
> /// * `dst` must be [valid] for writes of `count * size_of::<T>()` bytes or that number must be 0,
> ///   and `dst` must remain valid even when `src` is read for `count * size_of::<T>()` bytes. (This
> ///   means if the memory ranges overlap, the `dst` pointer must not be invalidated by `src` reads.)
> ///
> /// * Both `src` and `dst` must be properly aligned."
>
> "/// Note that even if the effectively copied size (`count * size_of::<T>()`) is
> /// `0`, the pointers must be properly aligned."
-/
def evalCopyMemoryProto
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | srcVal :: dstVal :: .scalar countSc :: .nil =>
    match
      decodeThinPtrArgProto? ptrBytes srcVal,
      decodeThinPtrArgProto? ptrBytes dstVal,
      Nat.beq countSc.sizeBytes ptrBytes
    with
    | .some srcPtrArg, .some dstPtrArg, true =>
      match resolveMemIntrinsicPointeeTyProto? target bodyLocalDecls bodyLayouts argOps with
      | .none => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
      | .some elemTy =>
        match
          intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
          intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
        with
        | .some elemSize, .some elemAlign =>
          let count := wrapScalarBits countSc.bits (scalarModulus ptrBytes)
          let totalBytes := Nat.mul elemSize count
          let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
          match Nat.ble totalBytes isizeMax with
          | false => MirStepNode.fail .ub
          | true =>
            -- Alignment is checked even for zero bytes; validity (including non-null)
            -- is only required when `totalBytes > 0` ("or that number must be 0").
            let ptrsAligned :=
              Bool.and
                (checkPtrArgAlignedProto s locals' bodyLocalDecls bodyLayouts srcPtrArg elemAlign)
                (checkPtrArgAlignedProto s locals' bodyLocalDecls bodyLayouts dstPtrArg elemAlign)
            match ptrsAligned with
            | false => MirStepNode.fail .ub
            | true =>
              match Nat.beq totalBytes 0 with
              | true => MirStepNode.step (advanceStmt s locals')
              | false =>
                -- Phase A: validate src liveness/bounds, TB read, extract full byte snapshot.
                match resolveLiveMemEndpointProto s locals' s.memory.borrows bodyLocalDecls bodyLayouts srcPtrArg with
                | .ub => MirStepNode.fail .ub
                | .unsupported => MirStepNode.unsupported
                | .ok srcEp =>
                  match endpointRangeInBoundsProto srcEp totalBytes with
                  | false => MirStepNode.fail .ub
                  | true =>
                    let borrowsAfterReadOpt : Option (List BorrowEntry) :=
                      match srcEp.borrowInfo? with
                      | .none => .some s.memory.borrows
                      | .some (srcTag, srcEntry) =>
                        borrowsAfterReadAccessProto
                          s.memory.borrows
                          s.memory.activeProtectors
                          srcTag
                          srcEntry
                          srcEp.effOffset
                          totalBytes
                    match borrowsAfterReadOpt with
                    | .none => MirStepNode.fail .ub
                    | .some borrows₁ =>
                      match readRootAbstractBytesProto srcEp with
                      | .ub => MirStepNode.fail .ub
                      | .unsupported => MirStepNode.unsupported
                      | .ok srcRootBytes =>
                        match sliceAbstractBytes srcRootBytes srcEp.effOffset totalBytes with
                        | .none => MirStepNode.fail .ub
                        | .some snapshot =>
                          -- Phase B: validate dst on post-read `borrows₁`, TB write, patch & commit.
                          match resolveLiveMemEndpointProto s locals' borrows₁ bodyLocalDecls bodyLayouts dstPtrArg with
                          | .ub => MirStepNode.fail .ub
                          | .unsupported => MirStepNode.unsupported
                          | .ok dstEp =>
                            match Bool.and dstEp.writable (endpointRangeInBoundsProto dstEp totalBytes) with
                            | false => MirStepNode.fail .ub
                            | true =>
                              let borrowsAfterWriteOpt : Option (List BorrowEntry) :=
                                match dstEp.borrowInfo? with
                                | .none => .some borrows₁
                                | .some (dstTag, dstEntryAfter) =>
                                  borrowsAfterWriteAccessProto
                                    borrows₁
                                    s.memory.activeProtectors
                                    dstTag
                                    dstEntryAfter
                                    dstEp.effOffset
                                    totalBytes
                              match borrowsAfterWriteOpt with
                              | .none => MirStepNode.fail .ub
                              | .some borrows₂ =>
                                match readRootAbstractBytesProto dstEp with
                                | .ub => MirStepNode.fail .ub
                                | .unsupported => MirStepNode.unsupported
                                | .ok dstRootBytes =>
                                  match writeAbstractBytesAt dstRootBytes dstEp.effOffset snapshot with
                                  | .none => MirStepNode.fail .ub
                                  | .some updatedDstBytes =>
                                    match
                                      commitRootAbstractBytesProto
                                        locals'
                                        s.memory.callStack
                                        s.memory.callerLocals
                                        s.memory.globals
                                        ptrBytes
                                        dstEp
                                        updatedDstBytes
                                    with
                                    | .ub => MirStepNode.fail .ub
                                    | .unsupported => MirStepNode.unsupported
                                    | .ok (locals₂, callStack', callerLocals', globals') =>
                                      MirStepNode.step
                                        (advanceStmt
                                          s
                                          locals₂
                                          { s.memory with
                                            borrows := borrows₂
                                            callStack := callStack'
                                            callerLocals := callerLocals'
                                            globals := globals' })
        | _, _ => intrinsicUnresolvedLayoutStep elemTy
    | _, _, _ => MirStepNode.fail .ub
  | _ => MirStepNode.fail .ub

/--
Statement-level wrapper for an overlapping `copy(src, dst, count)` intrinsic
(analogous to `Statements.evalCopyNonOverlapping`), evaluating `src`, `dst`, and
`count` left-to-right before executing `evalCopyMemoryProto`.

Note: Upstream `rustc 1.98.0` (`compiler/rustc_middle/src/mir/syntax.rs`)
defines `NonDivergingIntrinsic` with only `Assume` and `CopyNonOverlapping`;
`core::intrinsics::copy` is lowered as `TerminatorKind::Call`. This wrapper is
provided for symmetry with `Statements.evalCopyNonOverlapping` should a future
dialect also lower `copy` as a statement intrinsic.
-/
def evalCopyStmtProto
    (s : MachineState)
    (src dst count : Operand)
    (localDecls : List LocalDecl := .nil)
    (layouts : LayoutTable := emptyLayoutTable)
    (typeArgs : List RigidTy := .nil) :
    MirStepNode :=
  match
    evalOperands
      s.frame.locals
      (src :: dst :: count :: .nil)
      s.memory.borrows
      s.memory.globals
      layouts
      s.memory.callerLocals
      localDecls
      s.memory.callStack
  with
  | .ub => MirStepNode.fail .ub
  | .unsupported => MirStepNode.unsupported
  | .ok argVals locals' =>
    let syntheticTarget : ResolvedCallTarget :=
      { defPath := "core::intrinsics::copy"
        typeArgs := typeArgs
        fnSig := .none
        isIndirect := false }
    evalCopyMemoryProto s syntheticTarget localDecls layouts (src :: dst :: count :: .nil) argVals locals'

/--
Call-form evaluator for `core::intrinsics::copy<T>(src, dst, count)`.
Runs `evalCopyMemoryProto`, then writes `()` to `destination` and transitions
to `targetOpt` (`.fail .ub` when `targetOpt = .none`).
-/
def evalCopyProto
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  match evalCopyMemoryProto s target bodyLocalDecls bodyLayouts argOps argVals locals' with
  | .tau (.running s') =>
    writeIntrinsicReturnProto { s with memory := s'.memory } s'.frame.locals destination targetOpt .unit
      bodyLocalDecls bodyLayouts
  | other => other

/-! ## Section 7: Raw Byte Stripping & Comparison Helpers (`compare_bytes` & `raw_eq`) -/

/--
Outcome of stripping provenance from a slice of `AbstractByte`s
(`Miri.Memory.Allocation.getBytesStripProvenance` at `Miri/Memory/Allocation.lean:349-370`):
- `.ub`: at least one byte in the slice is `AbstractByte.uninit` (checked
  across the ENTIRE slice first, before provenance!);
- `.unsupported`: all bytes are initialized, but at least one byte carries
  relative pointer provenance (`.init _ (.some _)`), whose absolute virtual
  address bits are not uniquely determined without a concrete address layout;
- `.ok bytes`: all bytes are initialized provenance-free `UInt8` values.
-/
inductive StripBytesResultProto : Type where
  | ok (bytes : List UInt8) : StripBytesResultProto
  | ub : StripBytesResultProto
  | unsupported : StripBytesResultProto
  deriving DecidableEq

/-- Test whether any byte in `bs` is `AbstractByte.uninit`. -/
@[reducible]
def hasUninitByteProto : List AbstractByte → Bool
  | .nil => false
  | .uninit :: _ => true
  | .init _ _ :: rest => hasUninitByteProto rest

/-- Test whether any byte in `bs` is initialized and carries pointer provenance. -/
@[reducible]
def hasProvByteProto : List AbstractByte → Bool
  | .nil => false
  | .uninit :: rest => hasProvByteProto rest
  | .init _ (.some _) :: _ => true
  | .init _ .none :: rest => hasProvByteProto rest

/--
Extract concrete provenance-free `UInt8` values from an already-initialized byte
list, returning `.none` if any byte carries `.some _` provenance.
-/
@[reducible]
def extractNoProvBytesProto : List AbstractByte → Option (List UInt8)
  | .nil => .some .nil
  | .uninit :: _ => .none
  | .init _ (.some _) :: _ => .none
  | .init b .none :: rest =>
    match extractNoProvBytesProto rest with
    | .some tail => .some (b :: tail)
    | .none => .none

/--
Model `Allocation::get_bytes_strip_provenance` under relative-offset provenance
(`Miri/Memory/Allocation.lean:349-370`):
1. Check initialization across the ENTIRE slice first (`hasUninitByteProto`):
   any `.uninit` byte anywhere in the slice triggers `.ub`;
2. Check provenance: any provenance-carrying byte fails closed with
   `.unsupported` (matching `Allocation.getBytesStripProvenance` under
   `offsetIsAddr = false`, never fabricating synthetic virtual addresses);
3. Otherwise return the concrete `List UInt8`.
-/
@[reducible]
def stripProvenanceBytesProto (bs : List AbstractByte) : StripBytesResultProto :=
  match hasUninitByteProto bs with
  | true => .ub
  | false =>
    match extractNoProvBytesProto bs with
    | .some u8s => .ok u8s
    | .none => .unsupported

/--
Lexicographic unsigned byte comparison (`0..255`), 1-to-1 with
`Miri.Interpreter.Intrinsics.bytesCompare` (`Miri/Interpreter/Intrinsics.lean:174-176`).
-/
@[reducible]
def compareUnsignedBytesProto : List UInt8 → List UInt8 → Ordering
  | .nil, .nil => .eq
  | .nil, _ :: _ => .lt
  | _ :: _, .nil => .gt
  | a :: as, b :: bs =>
    let an := a.toBitVec.toNat
    let bn := b.toBitVec.toNat
    match Nat.beq an bn with
    | true => compareUnsignedBytesProto as bs
    | false =>
      match Nat.blt an bn with
      | true => .lt
      | false => .gt

/--
Encode an `Ordering` as canonical two's-complement `i32` (`ScalarInt` of width
`4`): `-1` = `0xFFFF_FFFF` (`4294967295`), `0` = `0`, `1` = `1`.
-/
@[reducible]
def orderingToI32ScalarProto : Ordering → ScalarInt
  | .lt => ⟨4294967295, 4⟩
  | .eq => ⟨0, 4⟩
  | .gt => ⟨1, 4⟩

/-- Exact bytewise equality on `List UInt8`. -/
@[reducible]
def u8ListEqProto : List UInt8 → List UInt8 → Bool
  | .nil, .nil => true
  | a :: as, b :: bs =>
    match Nat.beq a.toBitVec.toNat b.toBitVec.toNat with
    | true => u8ListEqProto as bs
    | false => false
  | _, _ => false

/-! ## Section 8: Intrinsic 2 — `core::intrinsics::compare_bytes` (`memcmp`) -/

/--
Evaluate `core::intrinsics::compare_bytes(left: *const u8, right: *const u8, bytes: usize) -> i32`.

Exact semantics (aligned with `Miri/Interpreter/Intrinsics.lean:174-187, 427`):
1. Validates `left`, `right` as thin pointers of width `ptrBytes` and `bytes` as
   a `usize` scalar with `bytes <= isize::MAX` (else `.ub`: no allocation is
   valid for reads of more bytes).
2. Null `left` or `right` faults `.ub` for EVERY `bytes`, including `bytes == 0`:
   the pinned contract requires both pointers to be "[valid] for reads of
   `bytes` bytes", and a null pointer "is *never* valid for reads/writes".
   This is the one point where the candidate is deliberately STRICTER than
   `lean-miri`: `Miri.Memory.checkAndDerefPtr` (`Miri/Memory/Access.lean:134-150`)
   returns `none` for every zero-sized access before resolving the pointer, so
   `compareBytes` on a null pointer with `bytes == 0` returns `0` there. Miri
   detects a subset of documented library UB; a trusted specification must not
   accept an execution the pinned `core` contract declares undefined.
3. When `bytes == 0` and both pointers are non-null, writes `0 : i32` without
   dereferencing memory (dangling and provenance-free non-null pointers succeed:
   "For memory accesses of [size zero][zst], *every* non-null pointer is valid").
4. When `bytes > 0`:
   - Eagerly validates and reads ALL `bytes` from `left` (live, in bounds, Tree
     Borrows read -> `borrows₁`, full initialization + provenance check);
   - Eagerly validates and reads ALL `bytes` from `right` on `borrows₁` (live,
     in bounds, Tree Borrows read -> `borrows₂`, full initialization +
     provenance check);
   - Because BOTH full slices are read eagerly before comparing, an `.uninit` or
     out-of-bounds byte at index `k > 0` ALWAYS faults `.ub` even if byte `0`
     already differs!
5. Compares the unsigned byte sequences lexicographically (`0..255`) and writes
   `-1 : i32`, `0 : i32`, or `1 : i32` to `destination` with `borrows := borrows₂`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2320-L2337>

> "/// Lexicographically compare `[left, left + bytes)` and `[right, right + bytes)`
> /// as unsigned bytes, returning negative if `left` is less, zero if all the
> /// bytes match, or positive if `left` is greater.
> ///
> /// This underlies things like `<[u8]>::cmp`, and will usually lower to `memcmp`.
> ///
> /// # Safety
> ///
> /// `left` and `right` must each be [valid] for reads of `bytes` bytes.
> ///
> /// Note that this applies to the whole range, not just until the first byte
> /// that differs.  That allows optimizations that can read in large chunks."

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "//! * A [null] pointer is *never* valid for reads/writes.
> //! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes.
> //!   The following points are only concerned with non-zero-sized accesses."
-/
def evalCompareBytesProto
    (s : MachineState)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | leftVal :: rightVal :: .scalar countSc :: .nil =>
    match
      decodeThinPtrArgProto? ptrBytes leftVal,
      decodeThinPtrArgProto? ptrBytes rightVal,
      Nat.beq countSc.sizeBytes ptrBytes
    with
    | .some leftPtrArg, .some rightPtrArg, true =>
      let count := wrapScalarBits countSc.bits (scalarModulus ptrBytes)
      let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
      match Nat.ble count isizeMax with
      | false => MirStepNode.fail .ub
      | true =>
        let nonNull :=
          Bool.and
            (Bool.not (isNullPtrArgProto s.memory leftPtrArg))
            (Bool.not (isNullPtrArgProto s.memory rightPtrArg))
        match nonNull with
        | false => MirStepNode.fail .ub
        | true =>
          match Nat.beq count 0 with
          | true =>
            writeIntrinsicReturnProto s locals' destination targetOpt (.scalar ⟨0, 4⟩)
              bodyLocalDecls bodyLayouts
          | false =>
            -- Eager full-slice read of `left`:
            match resolveLiveMemEndpointProto s locals' s.memory.borrows bodyLocalDecls bodyLayouts leftPtrArg with
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
            | .ok leftEp =>
              match endpointRangeInBoundsProto leftEp count with
              | false => MirStepNode.fail .ub
              | true =>
                let borrows₁Opt : Option (List BorrowEntry) :=
                  match leftEp.borrowInfo? with
                  | .none => .some s.memory.borrows
                  | .some (lTag, lEntry) =>
                    borrowsAfterReadAccessProto
                      s.memory.borrows
                      s.memory.activeProtectors
                      lTag
                      lEntry
                      leftEp.effOffset
                      count
                match borrows₁Opt with
                | .none => MirStepNode.fail .ub
                | .some borrows₁ =>
                  match readRootAbstractBytesProto leftEp with
                  | .ub => MirStepNode.fail .ub
                  | .unsupported => MirStepNode.unsupported
                  | .ok leftRootBytes =>
                    match sliceAbstractBytes leftRootBytes leftEp.effOffset count with
                    | .none => MirStepNode.fail .ub
                    | .some leftAbsSlice =>
                      match stripProvenanceBytesProto leftAbsSlice with
                      | .ub => MirStepNode.fail .ub
                      | .unsupported => MirStepNode.unsupported
                      | .ok leftBytes =>
                        -- Eager full-slice read of `right` under `borrows₁`:
                        match resolveLiveMemEndpointProto s locals' borrows₁ bodyLocalDecls bodyLayouts rightPtrArg with
                        | .ub => MirStepNode.fail .ub
                        | .unsupported => MirStepNode.unsupported
                        | .ok rightEp =>
                          match endpointRangeInBoundsProto rightEp count with
                          | false => MirStepNode.fail .ub
                          | true =>
                            let borrows₂Opt : Option (List BorrowEntry) :=
                              match rightEp.borrowInfo? with
                              | .none => .some borrows₁
                              | .some (rTag, rEntry) =>
                                borrowsAfterReadAccessProto
                                  borrows₁
                                  s.memory.activeProtectors
                                  rTag
                                  rEntry
                                  rightEp.effOffset
                                  count
                            match borrows₂Opt with
                            | .none => MirStepNode.fail .ub
                            | .some borrows₂ =>
                              match readRootAbstractBytesProto rightEp with
                              | .ub => MirStepNode.fail .ub
                              | .unsupported => MirStepNode.unsupported
                              | .ok rightRootBytes =>
                                match sliceAbstractBytes rightRootBytes rightEp.effOffset count with
                                | .none => MirStepNode.fail .ub
                                | .some rightAbsSlice =>
                                  match stripProvenanceBytesProto rightAbsSlice with
                                  | .ub => MirStepNode.fail .ub
                                  | .unsupported => MirStepNode.unsupported
                                  | .ok rightBytes =>
                                    let ord := compareUnsignedBytesProto leftBytes rightBytes
                                    let retSc := orderingToI32ScalarProto ord
                                    writeIntrinsicReturnProto
                                      { s with memory := { s.memory with borrows := borrows₂ } }
                                      locals'
                                      destination
                                      targetOpt
                                      (.scalar retSc)
                                      bodyLocalDecls
                                      bodyLayouts
    | _, _, _ => MirStepNode.fail .ub
  | _ => MirStepNode.fail .ub

/-! ## Section 9: Intrinsic 3 — `core::intrinsics::raw_eq` -/

/--
Evaluate `core::intrinsics::raw_eq<T>(a: &T, b: &T) -> bool`.

Exact semantics (aligned with `Miri/Interpreter/Intrinsics.lean:188-197, 428`
and `MiniRustSpec.Interp.evalIntrinsic ... .RawEq`):
1. Resolves pointee type `T`; rejects unsized or layout-unknown `T` fail-closed
   with `MirStepNode.unsupported` (matching Miri line 190 `invalid`).
2. Validates `a` and `b` as thin non-null pointers of width `ptrBytes` aligned
   to `align_of::<T>()` (misaligned or null -> `.ub`, even for ZSTs). Both
   arguments are references (`&T`), so non-null and alignment are validity
   invariants of the argument values themselves; `Intrinsics.rawEq` only
   re-checks alignment (line 193) because Miri validates `&T` operands when
   they are passed.
3. For ZST `T` (`size_of::<T>() == 0`), returns `true` (`ScalarInt ⟨1, 1⟩`).
4. For `size_of::<T>() > 0`:
   - Reads ALL `size_of::<T>()` bytes from `a` (in-bounds, live, Tree Borrows
     read -> `borrows₁`), then ALL `size_of::<T>()` bytes from `b` on `borrows₁`
     (in-bounds, live, Tree Borrows read -> `borrows₂`).
   - ANY `.uninit` byte anywhere in `[0, size_of::<T>())` — including struct or
     enum padding bytes or uninitialized `MaybeUninit`/union bytes — triggers
     `.fail .ub`!
   - Any provenance-carrying byte fails closed with `.unsupported`.
   - Writes `boolToScalar (aBytes == bBytes)` to `destination`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2293-L2318>

> "/// Determines whether the raw bytes of the two values are equal."
>
> "/// Since this works by comparing the underlying bytes, the actual `T` is
> /// not particularly important.  It will be used for its size and alignment,
> /// but any validity restrictions will be ignored, not enforced.
> ///
> /// # Safety
> ///
> /// It's UB to call this if any of the *bytes* in `*a` or `*b` are uninitialized.
> /// Note that this is a stricter criterion than just the *values* being
> /// fully-initialized: if `T` has padding, it's UB to call this intrinsic.
> ///
> /// At compile-time, it is furthermore UB to call this if any of the bytes
> /// in `*a` or `*b` have provenance."

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "- A reference or `Box<T>` must be aligned and non-null, it cannot be dangling, and it must point to a valid value (in case of dynamically sized types, using the actual dynamic type of the pointee as determined by the metadata). Note that the last point (about pointing to a valid value) remains a subject of some debate."
-/
def evalRawEqProto
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | aVal :: bVal :: .nil =>
    match resolveMemIntrinsicPointeeTyProto? target bodyLocalDecls bodyLayouts argOps with
    | .none => MirStepNode.unsupported
    | .some elemTy =>
      match isUnsizedRigidTy 8 elemTy with
      | true => MirStepNode.unsupported
      | false =>
        match
          intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
          intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
        with
        | .some elemSize, .some elemAlign =>
          let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
          match Nat.ble elemSize isizeMax with
          | false => MirStepNode.fail .ub
          | true =>
            match
              decodeThinPtrArgProto? ptrBytes aVal,
              decodeThinPtrArgProto? ptrBytes bVal
            with
            | .some aPtrArg, .some bPtrArg =>
              let ptrsOk :=
                Bool.and
                  (Bool.not (isNullPtrArgProto s.memory aPtrArg))
                  (Bool.and
                    (Bool.not (isNullPtrArgProto s.memory bPtrArg))
                    (Bool.and
                      (checkPtrArgAlignedProto s locals' bodyLocalDecls bodyLayouts aPtrArg elemAlign)
                      (checkPtrArgAlignedProto s locals' bodyLocalDecls bodyLayouts bPtrArg elemAlign)))
              match ptrsOk with
              | false => MirStepNode.fail .ub
              | true =>
                match Nat.beq elemSize 0 with
                | true =>
                  match isUninhabitedRigidTyProto bodyLocalDecls bodyLayouts 8 elemTy with
                  | true => MirStepNode.fail .ub
                  | false =>
                    writeIntrinsicReturnProto s locals' destination targetOpt (.scalar (boolToScalar true))
                      bodyLocalDecls bodyLayouts
                | false =>
                  -- Read `a`:
                  match resolveLiveMemEndpointProto s locals' s.memory.borrows bodyLocalDecls bodyLayouts aPtrArg with
                  | .ub => MirStepNode.fail .ub
                  | .unsupported => MirStepNode.unsupported
                  | .ok aEp =>
                    match endpointRangeInBoundsProto aEp elemSize with
                    | false => MirStepNode.fail .ub
                    | true =>
                      let borrows₁Opt : Option (List BorrowEntry) :=
                        match aEp.borrowInfo? with
                        | .none => .some s.memory.borrows
                        | .some (aTag, aEntry) =>
                          borrowsAfterReadAccessProto
                            s.memory.borrows
                            s.memory.activeProtectors
                            aTag
                            aEntry
                            aEp.effOffset
                            elemSize
                      match borrows₁Opt with
                      | .none => MirStepNode.fail .ub
                      | .some borrows₁ =>
                        match readRootAbstractBytesProto aEp with
                        | .ub => MirStepNode.fail .ub
                        | .unsupported => MirStepNode.unsupported
                        | .ok aRootBytes =>
                          match sliceAbstractBytes aRootBytes aEp.effOffset elemSize with
                          | .none => MirStepNode.fail .ub
                          | .some aAbsSlice =>
                            match stripProvenanceBytesProto aAbsSlice with
                            | .ub => MirStepNode.fail .ub
                            | .unsupported => MirStepNode.unsupported
                            | .ok aBytes =>
                              -- Read `b` under `borrows₁`:
                              match resolveLiveMemEndpointProto s locals' borrows₁ bodyLocalDecls bodyLayouts bPtrArg with
                              | .ub => MirStepNode.fail .ub
                              | .unsupported => MirStepNode.unsupported
                              | .ok bEp =>
                                match endpointRangeInBoundsProto bEp elemSize with
                                | false => MirStepNode.fail .ub
                                | true =>
                                  let borrows₂Opt : Option (List BorrowEntry) :=
                                    match bEp.borrowInfo? with
                                    | .none => .some borrows₁
                                    | .some (bTag, bEntry) =>
                                      borrowsAfterReadAccessProto
                                        borrows₁
                                        s.memory.activeProtectors
                                        bTag
                                        bEntry
                                        bEp.effOffset
                                        elemSize
                                  match borrows₂Opt with
                                  | .none => MirStepNode.fail .ub
                                  | .some borrows₂ =>
                                    match readRootAbstractBytesProto bEp with
                                    | .ub => MirStepNode.fail .ub
                                    | .unsupported => MirStepNode.unsupported
                                    | .ok bRootBytes =>
                                      match sliceAbstractBytes bRootBytes bEp.effOffset elemSize with
                                      | .none => MirStepNode.fail .ub
                                      | .some bAbsSlice =>
                                        match stripProvenanceBytesProto bAbsSlice with
                                        | .ub => MirStepNode.fail .ub
                                        | .unsupported => MirStepNode.unsupported
                                        | .ok bBytes =>
                                          let eq := u8ListEqProto aBytes bBytes
                                          writeIntrinsicReturnProto
                                            { s with memory := { s.memory with borrows := borrows₂ } }
                                            locals'
                                            destination
                                            targetOpt
                                            (.scalar (boolToScalar eq))
                                            bodyLocalDecls
                                            bodyLayouts
            | _, _ => MirStepNode.fail .ub
        | _, _ => MirStepNode.unsupported
  | _ => MirStepNode.fail .ub

/-! ## Section 10: Intrinsic 4 — `core::intrinsics::typed_swap_nonoverlapping` -/

/--
Three-way typed validity outcome for byte slices swapped by
`typed_swap_nonoverlapping<T>`:
- `.valid`: byte slice satisfies the Rust validity invariant of `T`;
- `.ub`: byte slice violates the Rust validity invariant of `T` (e.g. `.uninit`
  for scalars/pointers/refs, invalid `bool` `>= 2`, surrogate/out-of-range
  `char`, null `&T` / `fn(...)`, or uninhabited type);
- `.unsupported`: layout validity for an exotic ADT cannot be determined from
  `LayoutTable` (fail closed rather than silently accepting invalid values).
-/
inductive TypedBytesValidityProto : Type where
  | valid : TypedBytesValidityProto
  | ub : TypedBytesValidityProto
  | unsupported : TypedBytesValidityProto
  deriving DecidableEq

/-- Combine two `TypedBytesValidityProto` checks (`.ub` takes precedence over `.unsupported`). -/
@[reducible]
def combineTypedValidityProto :
    TypedBytesValidityProto → TypedBytesValidityProto → TypedBytesValidityProto
  | .ub, _ => .ub
  | _, .ub => .ub
  | .unsupported, _ => .unsupported
  | _, .unsupported => .unsupported
  | .valid, .valid => .valid

/--
Validate a raw `AbstractByte` slice against a `ScalarLayout` descriptor
(enforcing initialization and `validRange` for `.initialized`, while allowing
arbitrary bytes for `.union`).

A non-pointer scalar (integer, float, `bool`, `char`, enum tag) whose bytes
carry pointer provenance fails closed with `.unsupported`: a typed copy at a
non-pointer type strips the provenance and leaves the absolute address bits
(`Miri.Interpreter.Intrinsics.typedSwap` validates with provenance reset,
`Intrinsics.lean:209-211`), and `MirSemantics` allocations have no concrete
base address from which to compute those bits or to range-check them.
-/
@[reducible]
def validateScalarLayoutBytesProto
    (sl : ScalarLayout)
    (bytes : List AbstractByte) :
    TypedBytesValidityProto :=
  match sl with
  | .union _ => .valid
  | .initialized pk validRange =>
    match scalarLayoutByteWidth sl with
    | .none => .unsupported
    | .some sz =>
      match Nat.beq (length bytes) sz with
      | false => .ub
      | true =>
        match decodeScalarBytes bytes false with
        | .none => .ub
        | .some (sv, prov) =>
          match pk with
          | .pointer _ =>
            match prov with
            | .some _ => .valid
            | .none =>
              match wrappingRangeContains validRange sv.bits with
              | true => .valid
              | false => .ub
          | _ =>
            match prov with
            | .some _ => .unsupported
            | .none =>
              match wrappingRangeContains validRange sv.bits with
              | true => .valid
              | false => .ub

/--
Validate an integer or float scalar slice of byte width `sz`: every byte must be
initialized (else `.ub`); bytes carrying pointer provenance fail closed with
`.unsupported` (see `validateScalarLayoutBytesProto`).
-/
@[reducible]
def validateInitNoProvScalarBytesProto
    (sz : Nat)
    (bytes : List AbstractByte) :
    TypedBytesValidityProto :=
  match Bool.and (Nat.beq (length bytes) sz) (Bool.not (hasUninitByteProto bytes)) with
  | false => .ub
  | true =>
    match hasProvByteProto bytes with
    | true => .unsupported
    | false => .valid

/-- Higher-order field validator by `fieldLayouts` so `validateTypedBytesForLayoutIdxProto` is purely structurally recursive on fuel. -/
@[reducible]
def validateLayoutFieldsWith
    (layouts : LayoutTable)
    (bytes : List AbstractByte)
    (checkOne : Nat → List AbstractByte → TypedBytesValidityProto) :
    List Size → List Nat → TypedBytesValidityProto
  | .nil, .nil => .valid
  | off :: offRest, fIdx :: fRest =>
    match LayoutTable.lookup layouts fIdx with
    | .none => .unsupported
    | .some fl =>
      match sliceAbstractBytes bytes off.bytes fl.size.bytes with
      | .none => .ub
      | .some fSlice =>
        combineTypedValidityProto
          (checkOne fIdx fSlice)
          (validateLayoutFieldsWith layouts bytes checkOne offRest fRest)
  | _, _ => .unsupported

/-- Higher-order array element chunk validator (structurally recursive on element count). -/
@[reducible]
def validateArrayChunksWith
    (elemSz : Nat)
    (checkOne : List AbstractByte → TypedBytesValidityProto) :
    Nat → List AbstractByte → TypedBytesValidityProto
  | .zero, .nil => .valid
  | .succ k, bs =>
    match Nat.ble elemSz (length bs) with
    | false => .ub
    | true =>
      let chunk := takeAbstractBytes elemSz bs
      let rest := dropAbstractBytes elemSz bs
      combineTypedValidityProto
        (checkOne chunk)
        (validateArrayChunksWith elemSz checkOne k rest)
  | _, _ => .ub

/-- Higher-order field validator at explicit layout offsets (structurally recursive on offset list). -/
@[reducible]
def validateTypedFieldsAtOffsetsWith
    (sizeOfKind : RigidTy → Option Nat)
    (bytes : List AbstractByte)
    (checkOne : RigidTy → List AbstractByte → TypedBytesValidityProto) :
    List Size → List RigidTy → TypedBytesValidityProto
  | .nil, .nil => .valid
  | off :: offRest, k :: kRest =>
    match sizeOfKind k with
    | .none => .unsupported
    | .some fSz =>
      match sliceAbstractBytes bytes off.bytes fSz with
      | .none => .ub
      | .some fSlice =>
        combineTypedValidityProto
          (checkOne k fSlice)
          (validateTypedFieldsAtOffsetsWith sizeOfKind bytes checkOne offRest kRest)
  | _, _ => .unsupported

/-- Higher-order sequential field validator when no layout offsets are available. -/
@[reducible]
def validateSeqTypedFieldsWith
    (sizeOfKind : RigidTy → Option Nat)
    (checkOne : RigidTy → List AbstractByte → TypedBytesValidityProto) :
    List RigidTy → List AbstractByte → TypedBytesValidityProto
  | .nil, .nil => .valid
  | k :: kRest, bs =>
    match sizeOfKind k with
    | .none => .unsupported
    | .some fSz =>
      match Nat.ble fSz (length bs) with
      | false => .ub
      | true =>
        combineTypedValidityProto
          (checkOne k (takeAbstractBytes fSz bs))
          (validateSeqTypedFieldsWith sizeOfKind checkOne kRest (dropAbstractBytes fSz bs))
  | _, _ => .ub

/--
Validate that `bytes` (length `size_of::<T>()`) is a valid typed bit
representation for `ty : RigidTy` (enforcing `kani#5205` and Miri's `typedSwap`
typed-copy + `validatePlace` checks at `Miri/Interpreter/Intrinsics.lean:205-212`).

- Scalar integers, floats, and raw pointers require every byte initialized (`.init`).
- `bool` requires a single initialized byte in `{0, 1}`.
- `char` requires 4 initialized bytes forming a Unicode scalar value (`isValidCharCode`).
- References `&T`/`&mut T` and `fn(...)` require initialized non-null pointer bytes.
- Arrays, tuples, and structs validate every field at its layout offset while
  **permitting `.uninit` padding bytes**. ADT field types are taken from the
  ADT's `LayoutTable` entry (`fieldLayouts`), never from its generic arguments.
- Unions (`FieldsShape.union`, e.g. `MaybeUninit<T>`) permit `.uninit` bytes.
- Non-pointer scalars whose bytes carry pointer provenance, multi-variant
  enums, and ADTs without sufficient layout metadata fail closed with
  `.unsupported`.

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."
-/
def validateTypedBytesForLayoutIdxProto :
    Nat → LayoutTable → Nat → List AbstractByte → TypedBytesValidityProto
  | .zero, _, _, _ => .unsupported
  | .succ fuel', layouts, lIdx, bytes =>
    match LayoutTable.lookup layouts lIdx with
    | .none => .unsupported
    | .some l =>
      match Bool.or l.isUninhabited (Bool.not (Nat.beq (length bytes) l.size.bytes)) with
      | true => .ub
      | false =>
        match l.variants with
        | .empty => .ub
        | .single _ =>
          match l.fields with
          | .union _ => .valid
          | .primitive =>
            match Nat.beq l.size.bytes 0 with
            | true => .valid
            | false =>
              match l.backendRepr with
              | .scalar s0 => validateScalarLayoutBytesProto s0 bytes
              | _ => .unsupported
          | .arbitrary .nil _ => .valid
          | .arbitrary offsets _ =>
            match Nat.beq (length l.fieldLayouts) (length offsets) with
            | true =>
              validateLayoutFieldsWith
                layouts
                bytes
                (validateTypedBytesForLayoutIdxProto fuel' layouts)
                offsets
                l.fieldLayouts
            | false =>
              match offsets, l.backendRepr with
              | off0 :: .nil, .scalar s0 =>
                match scalarLayoutByteWidth s0 with
                | .some sz0 =>
                  match sliceAbstractBytes bytes off0.bytes sz0 with
                  | .some slice0 => validateScalarLayoutBytesProto s0 slice0
                  | .none => .ub
                | .none => .unsupported
              | off0 :: off1 :: .nil, .scalarPair s0 s1 =>
                match scalarLayoutByteWidth s0, scalarLayoutByteWidth s1 with
                | .some sz0, .some sz1 =>
                  match sliceAbstractBytes bytes off0.bytes sz0, sliceAbstractBytes bytes off1.bytes sz1 with
                  | .some slice0, .some slice1 =>
                    combineTypedValidityProto
                      (validateScalarLayoutBytesProto s0 slice0)
                      (validateScalarLayoutBytesProto s1 slice1)
                  | _, _ => .ub
                | _, _ => .unsupported
              | _, _ => .unsupported
          | .array stride count =>
            -- Element validity (not mere initialization) decides array validity:
            -- padding inside elements may be `.uninit`, while an initialized
            -- element can still be invalid (`bool = 2`). Without the element
            -- layout (`fieldLayouts = [elemIdx]`), fail closed.
            match l.fieldLayouts with
            | elemIdx :: .nil =>
              validateArrayChunksWith
                stride.bytes
                (validateTypedBytesForLayoutIdxProto fuel' layouts elemIdx)
                count
                bytes
            | _ => .unsupported
        | .multiple tagLayout tagField _ =>
          match l.fields, scalarLayoutByteWidth tagLayout with
          | .arbitrary outerOffsets _, .some tagSz =>
            match get? outerOffsets tagField with
            | .none => .unsupported
            | .some tagOff =>
              match sliceAbstractBytes bytes tagOff.bytes tagSz with
              | .none => .ub
              | .some tagSlice =>
                match validateScalarLayoutBytesProto tagLayout tagSlice with
                | .ub => .ub
                | .unsupported => .unsupported
                | .valid =>
                  match decodeScalarBytes tagSlice false with
                  | .none => .ub
                  | .some (tagSc, _) =>
                    match resolveEnumVariantIdxByTag l.variantDiscriminants tagSc.bits with
                    | .none => .ub
                    | .some _ => .unsupported
          | _, _ => .unsupported

/--
Validate raw abstract bytes `bytes` against a `RigidTy` `ty` under
`(localDecls, layouts)`.
-/
def validateTypedBytesProto :
    Nat → List LocalDecl → LayoutTable → RigidTy → List AbstractByte → TypedBytesValidityProto
  | .zero, _, _, _, _ => .unsupported
  | .succ fuel', localDecls, layouts, ty, bytes =>
    match ty with
    | .never => .ub
    | .bool =>
      match bytes with
      | .init b .none :: .nil =>
        match Nat.ble b.toBitVec.toNat 1 with
        | true => .valid
        | false => .ub
      | .init _ (.some _) :: .nil => .unsupported
      | _ => .ub
    | .char =>
      match Nat.beq (length bytes) 4 with
      | false => .ub
      | true =>
        match decodeScalarBytes bytes false with
        | .some (sv, .none) =>
          match isValidCharCode sv.bits with
          | true => .valid
          | false => .ub
        | .some (_, .some _) => .unsupported
        | .none => .ub
    | .uint w =>
      match intCastTargetBytes (.uint w) with
      | .some sz => validateInitNoProvScalarBytesProto sz bytes
      | .none => .unsupported
    | .int w =>
      match intCastTargetBytes (.int w) with
      | .some sz => validateInitNoProvScalarBytesProto sz bytes
      | .none => .unsupported
    | .float fk =>
      let sz :=
        match fk with
        | .f16 => 2 | .f32 => 4 | .f64 => 8 | .f128 => 16
      validateInitNoProvScalarBytesProto sz bytes
    | .tuple .nil | .fnDef _ _ =>
      match bytes with
      | .nil => .valid
      | _ :: _ => .ub
    | .rawPtr _ pointee =>
      let expectedSz :=
        match pointee with
        | .slice _ | .str | .dynamic _ => 16
        | _ => layoutPointerBytes layouts
      match Bool.and (Nat.beq (length bytes) expectedSz) (Bool.not (hasUninitByteProto bytes)) with
      | true => .valid
      | false => .ub
    | .ref _ pointee =>
      let isWide :=
        match pointee with
        | .slice _ | .str | .dynamic _ => true
        | _ => false
      let ptrBytes := layoutPointerBytes layouts
      match isWide with
      | false =>
        match Nat.beq (length bytes) ptrBytes with
        | false => .ub
        | true =>
          match decodeScalarBytes bytes false with
          | .none => .ub
          | .some (sv, prov) =>
            match prov with
            | .some _ => .valid
            | .none =>
              match Nat.beq sv.bits 0 with
              | true => .ub
              | false => .valid
      | true =>
        match Nat.beq (length bytes) (Nat.mul 2 ptrBytes) with
        | false => .ub
        | true =>
          let dataSlice := takeAbstractBytes ptrBytes bytes
          let metaSlice := dropAbstractBytes ptrBytes bytes
          match decodeScalarBytes dataSlice false, decodeScalarBytes metaSlice false with
          | .some (dataSv, prov), .some _ =>
            match prov with
            | .some _ => .valid
            | .none =>
              match Nat.beq dataSv.bits 0 with
              | true => .ub
              | false => .valid
          | _, _ => .ub
    | .fnPtr _ _ _ _ =>
      let ptrBytes := layoutPointerBytes layouts
      match Nat.beq (length bytes) ptrBytes with
      | false => .ub
      | true =>
        match decodeScalarBytes bytes false with
        | .none => .ub
        | .some (sv, prov) =>
          match prov with
          | .some _ => .valid
          | .none =>
            match Nat.beq sv.bits 0 with
            | true => .ub
            | false => .valid
    | .array elemKind n =>
      match Nat.beq n 0 with
      | true =>
        match bytes with
        | .nil => .valid
        | _ :: _ => .ub
      | false =>
        match intrinsicRigidTyByteSize localDecls layouts elemKind with
        | .none => .unsupported
        | .some elemSz =>
          match Nat.beq (length bytes) (Nat.mul elemSz n) with
          | false => .ub
          | true =>
            validateArrayChunksWith
              elemSz
              (validateTypedBytesProto fuel' localDecls layouts elemKind)
              n
              bytes
    | .tuple (kHead :: kTail) =>
      let fieldKinds := kHead :: kTail
      let resolved := resolveRigidTyWithDeclsProto localDecls layouts ty
      match LayoutTable.lookup layouts resolved.layoutIdx with
      | .some l =>
        match Nat.beq (length bytes) l.size.bytes, l.fields with
        | true, .arbitrary offsets _ =>
          validateTypedFieldsAtOffsetsWith
            (intrinsicRigidTyByteSize localDecls layouts)
            bytes
            (validateTypedBytesProto fuel' localDecls layouts)
            offsets
            fieldKinds
        | false, _ => .ub
        | _, _ => .unsupported
      | .none =>
        validateSeqTypedFieldsWith
          (intrinsicRigidTyByteSize localDecls layouts)
          (validateTypedBytesProto fuel' localDecls layouts)
          fieldKinds
          bytes
    | .adt _ _ =>
      -- Field types come from the ADT's layout entry (`fieldLayouts`), never from
      -- its generic arguments: `struct W<T>(*const T)` has one generic argument
      -- and one field, yet the field is a pointer, not a `T`.
      let resolved := resolveRigidTyWithDeclsProto localDecls layouts ty
      validateTypedBytesForLayoutIdxProto fuel' layouts resolved.layoutIdx bytes
    | _ => .unsupported

/--
The bytes that a typed copy of `slice` at type `ty` stores into endpoint `ep`.

`Miri.Interpreter.Intrinsics.typedSwap` moves both values with typed copies and
validates the destination with padding reset (`Intrinsics.lean:205-212`), so the
padding bytes of the stored value are uninitialized whatever the source held.

- A stack or caller local stores a structured `Value`, which has no padding
  bytes: committing `slice` already yields uninitialized padding, so the slice
  is stored as is.
- A global allocation stores raw bytes, so the stored image is the exact
  re-encoding of the value decoded from `slice` at `ty`: equal to `slice` on
  every value byte and `.uninit` on padding. When the value cannot be decoded
  and re-encoded exactly, the result is `.none` (callers fail closed with
  `.unsupported`) rather than a raw copy that would keep padding initialized.
-/
def typedCopyStoredBytesProto
    (localDecls : List LocalDecl)
    (layouts : LayoutTable)
    (ty : RigidTy)
    (ep : ResolvedMemEndpointProto)
    (slice : List AbstractByte) :
    Option (List AbstractByte) :=
  match ep.globalAlloc? with
  | .none => .some slice
  | .some _ =>
    let rTy := resolveRigidTyWithDeclsProto localDecls layouts ty
    match decodePartialUninitValueProto defaultCodecFuel localDecls layouts rTy slice with
    | .none => .none
    | .some v =>
      match encodeRawValueBytesProto defaultCodecFuel localDecls layouts rTy v with
      | .some stored =>
        match abstractBytesRefineProto stored slice with
        | true => .some stored
        | false => .none
      | .none => .none

/--
Evaluate `core::intrinsics::typed_swap_nonoverlapping<T>(x: *mut T, y: *mut T)`.

Exact semantics (aligned with `Miri/Interpreter/Intrinsics.lean:199-214, 429`):
1. Resolves pointee type `T`; rejects unsized or layout-unknown `T` fail-closed
   with `MirStepNode.unsupported`.
2. Checks non-null and ABI alignment (`align_of::<T>()`) of both `x` and `y`
   even when `size_of::<T>() == 0`. Null is `.ub` for every `T` because the
   pinned contract requires both pointers to be "[valid] for both reads and
   writes" and a null pointer "is *never* valid for reads/writes". For ZST `T`
   this is deliberately STRICTER than `lean-miri`, whose zero-sized
   `copyOp` / `memCopy` accesses skip pointer resolution
   (`Miri.Memory.checkAndDerefPtr`, `Miri/Memory/Access.lean:134-150`).
3. For uninhabited `T` (`!` or empty ADT), faults `.fail .ub` even at size `0`.
4. For inhabited ZST `T` (`size_of::<T>() == 0`), aligned non-null pointers
   succeed as a no-op (matching Miri `memCopy ... size=0 nonoverlapping=true`).
5. For `size_of::<T>() > 0`:
   - Resolves live writable endpoints `xEp` and `yEp`, verifying both ranges
     `[xEffOff, xEffOff + size)` and `[yEffOff, yEffOff + size)` are in bounds.
   - **Same-tag disjointness vs. overlap**: checks container identity
     (`xEp.key == yEp.key`) and exact byte-range disjointness
     `rangesDisjoint xEp.effOffset size yEp.effOffset size`. Two disjoint
     elements of the same allocation sharing the SAME provenance tag succeed,
     while any overlapping byte ranges fault `.fail .ub`!
   - **Typed validity (`kani#5205`)**: validates BOTH `xBytes` and `yBytes` at
     type `T` via `validateTypedBytesProto` (rejecting `.uninit` scalars,
     invalid `bool`/`char`, null `&T`, while allowing padding and unions).
   - **Tree Borrows ordering**: applies `read(x) -> read(y) -> write(x) -> write(y)`
     on the evolving borrow table so borrow conflicts fault `.fail .ub`.
   - **Typed-copy images**: each place receives the typed-copy image of the
     other value (`typedCopyStoredBytesProto`): padding bytes are stored
     uninitialized (lines 205-212 validate with padding reset), also in global
     allocations, which keep raw bytes.
   - **Atomic same-container commit**: when `xEp.key == yEp.key`, patches both
     disjoint spans into the shared root buffer before committing once; when
     `xEp.key != yEp.key`, commits `x` then `y`.

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2545-L2573>

> "/// Non-overlapping *typed* swap of a single value.
> ///
> /// The codegen backends will replace this with a better implementation when
> /// `T` is a simple type that can be loaded and stored as an immediate.
> ///
> /// The stabilized form of this intrinsic is [`crate::mem::swap`].
> ///
> /// # Safety
> /// Behavior is undefined if any of the following conditions are violated:
> ///
> /// * Both `x` and `y` must be [valid] for both reads and writes.
> ///
> /// * Both `x` and `y` must be properly aligned.
> ///
> /// * The region of memory beginning at `x` must *not* overlap with the region of memory
> ///   beginning at `y`.
> ///
> /// * The memory pointed by `x` and `y` must both contain values of type `T`."

Reference (`library/core/src/ptr/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/mod.rs#L18-L20>

> "//! * A [null] pointer is *never* valid for reads/writes.
> //! * For memory accesses of [size zero][zst], *every* non-null pointer is valid for reads/writes.
> //!   The following points are only concerned with non-zero-sized accesses."
-/
def evalTypedSwapNonOverlappingProto
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | xVal :: yVal :: .nil =>
    match resolveMemIntrinsicPointeeTyProto? target bodyLocalDecls bodyLayouts argOps with
    | .none => MirStepNode.unsupported
    | .some elemTy =>
      match isUnsizedRigidTy 8 elemTy with
      | true => MirStepNode.unsupported
      | false =>
        match
          intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy,
          intrinsicRigidTyAlign bodyLocalDecls bodyLayouts elemTy
        with
        | .some elemSize, .some elemAlign =>
          let isizeMax := Nat.sub (signedHalfModulus ptrBytes) 1
          match Nat.ble elemSize isizeMax with
          | false => MirStepNode.fail .ub
          | true =>
            match
              decodeThinPtrArgProto? ptrBytes xVal,
              decodeThinPtrArgProto? ptrBytes yVal
            with
            | .some xPtrArg, .some yPtrArg =>
              let ptrsOk :=
                Bool.and
                  (Bool.not (isNullPtrArgProto s.memory xPtrArg))
                  (Bool.and
                    (Bool.not (isNullPtrArgProto s.memory yPtrArg))
                    (Bool.and
                      (checkPtrArgAlignedProto s locals' bodyLocalDecls bodyLayouts xPtrArg elemAlign)
                      (checkPtrArgAlignedProto s locals' bodyLocalDecls bodyLayouts yPtrArg elemAlign)))
              match ptrsOk with
              | false => MirStepNode.fail .ub
              | true =>
                match isUninhabitedRigidTyProto bodyLocalDecls bodyLayouts 8 elemTy with
                | true => MirStepNode.fail .ub
                | false =>
                  match Nat.beq elemSize 0 with
                  | true =>
                    writeIntrinsicReturnProto s locals' destination targetOpt .unit
                      bodyLocalDecls bodyLayouts
                  | false =>
                    -- Resolve both live writable endpoints:
                    match
                      resolveLiveMemEndpointProto s locals' s.memory.borrows bodyLocalDecls bodyLayouts xPtrArg,
                      resolveLiveMemEndpointProto s locals' s.memory.borrows bodyLocalDecls bodyLayouts yPtrArg
                    with
                    | .ub, _ => MirStepNode.fail .ub
                    | _, .ub => MirStepNode.fail .ub
                    | .unsupported, _ => MirStepNode.unsupported
                    | _, .unsupported => MirStepNode.unsupported
                    | .ok xEp, .ok yEp =>
                      let boundsAndWritable :=
                        Bool.and
                          (Bool.and xEp.writable yEp.writable)
                          (Bool.and
                            (endpointRangeInBoundsProto xEp elemSize)
                            (endpointRangeInBoundsProto yEp elemSize))
                      match boundsAndWritable with
                      | false => MirStepNode.fail .ub
                      | true =>
                        -- Container-first disjointness (allows same-tag disjoint ranges!):
                        let disjointOk : Bool :=
                          match decide (xEp.key = yEp.key) with
                          | false => true
                          | true => rangesDisjoint xEp.effOffset elemSize yEp.effOffset elemSize
                        match disjointOk with
                        | false => MirStepNode.fail .ub
                        | true =>
                          -- Tree Borrows ordering: read(x) -> read(y) -> write(x) -> write(y)
                          let borrowsAfterXReadOpt : Option (List BorrowEntry) :=
                            match xEp.borrowInfo? with
                            | .none => .some s.memory.borrows
                            | .some (xTag, xEntry) =>
                              borrowsAfterReadAccessProto
                                s.memory.borrows s.memory.activeProtectors
                                xTag xEntry xEp.effOffset elemSize
                          match borrowsAfterXReadOpt with
                          | .none => MirStepNode.fail .ub
                          | .some borrows₁ =>
                            let borrowsAfterYReadOpt : Option (List BorrowEntry) :=
                              match yEp.borrowInfo? with
                              | .none => .some borrows₁
                              | .some (yTag, _) =>
                                match lookupBorrow borrows₁ yTag with
                                | .none => .none
                                | .some yEntry₁ =>
                                  borrowsAfterReadAccessProto
                                    borrows₁ s.memory.activeProtectors
                                    yTag yEntry₁ yEp.effOffset elemSize
                            match borrowsAfterYReadOpt with
                            | .none => MirStepNode.fail .ub
                            | .some borrows₂ =>
                              let borrowsAfterXWriteOpt : Option (List BorrowEntry) :=
                                match xEp.borrowInfo? with
                                | .none => .some borrows₂
                                | .some (xTag, _) =>
                                  match lookupBorrow borrows₂ xTag with
                                  | .none => .none
                                  | .some xEntry₂ =>
                                    borrowsAfterWriteAccessProto
                                      borrows₂ s.memory.activeProtectors
                                      xTag xEntry₂ xEp.effOffset elemSize
                              match borrowsAfterXWriteOpt with
                              | .none => MirStepNode.fail .ub
                              | .some borrows₃ =>
                                let borrowsAfterYWriteOpt : Option (List BorrowEntry) :=
                                  match yEp.borrowInfo? with
                                  | .none => .some borrows₃
                                  | .some (yTag, _) =>
                                    match lookupBorrow borrows₃ yTag with
                                    | .none => .none
                                    | .some yEntry₃ =>
                                      borrowsAfterWriteAccessProto
                                        borrows₃ s.memory.activeProtectors
                                        yTag yEntry₃ yEp.effOffset elemSize
                                match borrowsAfterYWriteOpt with
                                | .none => MirStepNode.fail .ub
                                | .some borrows₄ =>
                                  -- Extract both byte slices and enforce typed validity:
                                  match readRootAbstractBytesProto xEp, readRootAbstractBytesProto yEp with
                                  | .ub, _ | _, .ub => MirStepNode.fail .ub
                                  | .unsupported, _ | _, .unsupported => MirStepNode.unsupported
                                  | .ok xRootBytes, .ok yRootBytes =>
                                    match
                                      sliceAbstractBytes xRootBytes xEp.effOffset elemSize,
                                      sliceAbstractBytes yRootBytes yEp.effOffset elemSize
                                    with
                                    | .some xSlice, .some ySlice =>
                                      let valCheck :=
                                        combineTypedValidityProto
                                          (validateTypedBytesProto defaultCodecFuel bodyLocalDecls bodyLayouts elemTy xSlice)
                                          (validateTypedBytesProto defaultCodecFuel bodyLocalDecls bodyLayouts elemTy ySlice)
                                      match valCheck with
                                      | .ub => MirStepNode.fail .ub
                                      | .unsupported => MirStepNode.unsupported
                                      | .valid =>
                                        -- Commit swapped bytes (same container vs distinct containers).
                                        -- Each place receives the typed-copy image of the other value.
                                        let commitRes :
                                            ProtoRes (List LocalSlot × List SavedCallerFrame × List LocalSlot × List CapturedAllocation) :=
                                          match
                                            typedCopyStoredBytesProto bodyLocalDecls bodyLayouts elemTy xEp ySlice,
                                            typedCopyStoredBytesProto bodyLocalDecls bodyLayouts elemTy yEp xSlice
                                          with
                                          | .some xNew, .some yNew =>
                                            match decide (xEp.key = yEp.key) with
                                            | true =>
                                              match writeAbstractBytesAt xRootBytes xEp.effOffset xNew with
                                              | .none => .ub
                                              | .some buf1 =>
                                                match writeAbstractBytesAt buf1 yEp.effOffset yNew with
                                                | .none => .ub
                                                | .some buf2 =>
                                                  commitRootAbstractBytesProto
                                                    locals' s.memory.callStack s.memory.callerLocals s.memory.globals
                                                    ptrBytes xEp buf2
                                            | false =>
                                              match writeAbstractBytesAt xRootBytes xEp.effOffset xNew with
                                              | .none => .ub
                                              | .some xUpdated =>
                                                match writeAbstractBytesAt yRootBytes yEp.effOffset yNew with
                                                | .none => .ub
                                                | .some yUpdated =>
                                                  match
                                                    commitRootAbstractBytesProto
                                                      locals' s.memory.callStack s.memory.callerLocals s.memory.globals
                                                      ptrBytes xEp xUpdated
                                                  with
                                                  | .ub => .ub
                                                  | .unsupported => .unsupported
                                                  | .ok (loc1, cs1, cl1, gl1) =>
                                                    commitRootAbstractBytesProto
                                                      loc1 cs1 cl1 gl1 ptrBytes yEp yUpdated
                                          | _, _ => .unsupported
                                        match commitRes with
                                        | .ub => MirStepNode.fail .ub
                                        | .unsupported => MirStepNode.unsupported
                                        | .ok (locals₂, callStack', callerLocals', globals') =>
                                          writeIntrinsicReturnProto
                                            { s with
                                              memory :=
                                                { s.memory with
                                                  borrows := borrows₄
                                                  callStack := callStack'
                                                  callerLocals := callerLocals'
                                                  globals := globals' } }
                                            locals₂
                                            destination
                                            targetOpt
                                            .unit
                                            bodyLocalDecls
                                            bodyLayouts
                                    | _, _ => MirStepNode.fail .ub
            | _, _ => MirStepNode.fail .ub
        | _, _ => MirStepNode.unsupported
  | _ => MirStepNode.fail .ub

/-! ## Section 11: Intrinsics 5 & 6 — `ptr_offset_from` & `ptr_offset_from_unsigned` -/

/--
Pure distance-range and exact-divisibility kernel for `ptr_offset_from`
(`unsigned = false`) and `ptr_offset_from_unsigned` (`unsigned = true`),
1-to-1 with `Miri/Interpreter/Intrinsics.lean:239-273`.

Given non-negative offsets `ptrOff` and `originOff` within the same live
allocation (or equal provenance-free addresses), pointee byte size `elemSize`,
and pointer width `ptrBytes`:
- `elemSize == 0` -> `.none` (UB: division by zero on ZST pointee);
- `distance := Int.ofNat ptrOff - Int.ofNat originOff`;
- `isizeMax := Int.ofNat (signedHalfModulus ptrBytes - 1)`;
- For `unsigned = true`: requires `0 <= distance <= isizeMax` (negative distance
  or `distance > isize::MAX` -> `.none` UB);
- For `unsigned = false`: requires `-isizeMax <= distance <= isizeMax` (note
  that `distance == isize::MIN = -2^(ptrBits - 1)` is strictly `< -isizeMax` and
  therefore returns `.none` UB, matching Miri line 248!);
- Requires `distance.natAbs % elemSize == 0` (exact division, else `.none` UB);
- Encodes the quotient as canonical `usize` (unsigned) or two's-complement
  `isize` (signed) `ScalarInt` of width `ptrBytes`.

Note: `ptr_offset_from` does NOT require `ptrOff` or `originOff` to be aligned
to `align_of::<T>()`, only that their byte difference is an exact multiple of
`size_of::<T>()`.
-/
@[reducible]
def evalPtrOffsetFromDistanceProto
    (ptrOff originOff elemSize ptrBytes : Nat)
    (unsigned : Bool) :
    Option ScalarInt :=
  match Nat.beq elemSize 0 with
  | true => .none
  | false =>
    let distance : Int := Int.ofNat ptrOff - Int.ofNat originOff
    let halfMod := signedHalfModulus ptrBytes
    let isizeMax : Int := Int.ofNat (Nat.sub halfMod 1)
    let rangeOk : Bool :=
      match unsigned with
      | true => decide (0 ≤ distance ∧ distance ≤ isizeMax)
      | false => decide (-isizeMax ≤ distance ∧ distance ≤ isizeMax)
    match rangeOk with
    | false => .none
    | true =>
      let mag : Nat := distance.natAbs
      match Nat.beq (Nat.mod mag elemSize) 0 with
      | false => .none
      | true =>
        let quotMag : Nat := Nat.div mag elemSize
        match unsigned with
        | true => .some ⟨quotMag, ptrBytes⟩
        | false =>
          match decide (0 ≤ distance) with
          | true => .some ⟨quotMag, ptrBytes⟩
          | false =>
            let modulus := scalarModulus ptrBytes
            .some ⟨Nat.sub modulus quotMag, ptrBytes⟩

/--
Test whether tracked pointer `p` is a provenance-free synthetic address: its
`allocId` is `0` and neither a borrow tag `0` nor a global allocation `0`
backs it (the `MirSemantics` encoding of an integer-derived pointer value kept
in `Value.ptr` form; `recordExposedAllocId` likewise treats `allocId = 0` as
"synthetic provenance-less addresses rather than a real allocation").
-/
@[reducible]
def isUnbackedZeroProvProto (mem : Memory) (p : ProvenancePtr) : Bool :=
  Bool.and (Nat.beq p.allocId 0)
    (Bool.and
      (match lookupBorrow mem.borrows 0 with | .none => true | .some _ => false)
      (match lookupGlobalAlloc mem.globals 0 with | .none => true | .some _ => false))

/--
Normalize a thin pointer argument so that both encodings of a provenance-free
address (`Value.scalar` bits and an unbacked `allocId = 0` `Value.ptr`) become
`PtrArgProto.addr` of the address modulo `2^(8 * ptrBytes)`.
-/
@[reducible]
def normalizePtrArgProto (mem : Memory) (ptrBytes : Nat) : PtrArgProto → PtrArgProto
  | .addr bits => .addr bits
  | .prov p =>
    match isUnbackedZeroProvProto mem p with
    | true => .addr (wrapScalarBits p.offsetBytes (scalarModulus ptrBytes))
    | false => .prov p

/--
Root local `(frameDepth, localIdx)` of a tracked stack pointer `p` whose
allocation is no longer live (`BorrowEntry.allocDead`, or a missing / dead
`LocalSlot`), or `.none` when `p` has no borrow entry or its allocation is live.

A dead tag does not record which storage generation of the local it belonged
to (`StorageDead` followed by `StorageLive` reuses the same local index for a
new allocation), so two distinct dead tags of one root may or may not denote
the same allocation.
-/
@[reducible]
def deadStackRootProto?
    (s : MachineState)
    (locals : List LocalSlot)
    (p : ProvenancePtr) :
    Option (Nat × LocalIdx) :=
  match lookupBorrow s.memory.borrows p.tag with
  | .none => .none
  | .some entry =>
    let isDead : Bool :=
      match entry.allocDead with
      | true => true
      | false =>
        match
          readFrameLocalSlot
            locals
            s.memory.callStack
            s.memory.callerLocals
            entry.targetFrameDepth
            entry.targetLocal
        with
        | .none => true
        | .some .dead => true
        | .some _ => false
    match isDead with
    | true => .some (entry.targetFrameDepth, entry.targetLocal)
    | false => .none

/--
Same-allocation offset resolution for `ptr_offset_from` /
`ptr_offset_from_unsigned`, 1-to-1 with the non-address-provenance branch of
`Miri.Interpreter.Intrinsics.pointerOffsetFrom` (`Intrinsics.lean:223-232`)
followed by its two directed `checkSignedAccess` calls (lines 250-262).

Returns the pair of offsets `(ptrOff, originOff)` relative to a common base:

- **Two provenance-free addresses** (line 228): the addresses themselves. Equal
  addresses succeed (distance `0`: `checkSignedAccess _ 0` performs no
  check); unequal addresses are `.ub` (no allocation backs the range).
- **Mixed tracked / provenance-free** (line 232): `.ub`.
- **The same tracked pointer** (identical provenance and offset): `(0, 0)`
  WITHOUT any liveness or bounds requirement. Both arguments "point to the
  same address", which the pinned `offset_from` contract accepts
  unconditionally, and the distance-`0` `checkSignedAccess` calls skip pointer
  resolution (`Miri.Memory.checkAndDerefPtr` returns `none` for size `0`), so a
  dangling or out-of-bounds pointer compared with itself is not UB.
- **Two tracked pointers into one live allocation** (`AllocKeyProto` equality,
  line 229-231): equal effective offsets succeed without a bounds check (same
  address again, even under distinct Tree Borrows tags); otherwise BOTH
  endpoints must lie in `[0, allocSize]` (lines 250-262 check
  `[origin, origin + distance]` and `[ptr, ptr - distance]`), else `.ub`.
  Tree Borrows permissions are irrelevant: no memory is accessed.
- **Different allocations** (line 230), or exactly one dead allocation: `.ub`.
- **Two distinct dead tags of the same root local**: fail closed with
  `.unsupported`. Within one storage generation they share an allocation
  (distance `0` succeeds, non-zero distance is `.ub`); across generations they
  do not (`.ub`); `BorrowEntry` does not record the generation
  (`deadStackRootProto?`). Sharing a tag pins the generation, so the same dead
  tag at two different offsets is `.ub`.
- An undeterminable sub-place offset or root size is `.unsupported`.
-/
def resolvePtrOffsetFromOffsetsProto
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrArg originArg : PtrArgProto) :
    ProtoRes (Nat × Nat) :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match
    normalizePtrArgProto s.memory ptrBytes ptrArg,
    normalizePtrArgProto s.memory ptrBytes originArg
  with
  | .addr aBits, .addr bBits =>
    match Nat.beq aBits bBits with
    | true => .ok (aBits, bBits)
    | false => .ub
  | .prov _, .addr _ => .ub
  | .addr _, .prov _ => .ub
  | .prov pPtr, .prov oPtr =>
    match Bool.and (Nat.beq pPtr.allocId oPtr.allocId) (Nat.beq pPtr.offsetBytes oPtr.offsetBytes) with
    | true => .ok (0, 0)
    | false =>
      match
        resolveLiveMemEndpointProto s locals s.memory.borrows bodyLocalDecls bodyLayouts (.prov pPtr),
        resolveLiveMemEndpointProto s locals s.memory.borrows bodyLocalDecls bodyLayouts (.prov oPtr)
      with
      | .ok pEp, .ok oEp =>
        match decide (pEp.key = oEp.key) with
        | false => .ub
        | true =>
          match Nat.beq pEp.effOffset oEp.effOffset with
          | true => .ok (pEp.effOffset, oEp.effOffset)
          | false =>
            match
              Bool.and
                (Nat.ble pEp.effOffset pEp.allocSize)
                (Nat.ble oEp.effOffset oEp.allocSize)
            with
            | true => .ok (pEp.effOffset, oEp.effOffset)
            | false => .ub
      | .ub, .ub =>
        match Nat.beq pPtr.allocId oPtr.allocId with
        | true => .ub
        | false =>
          match deadStackRootProto? s locals pPtr, deadStackRootProto? s locals oPtr with
          | .some (pDepth, pLocal), .some (oDepth, oLocal) =>
            match Bool.and (Nat.beq pDepth oDepth) (Nat.beq pLocal oLocal) with
            | true => .unsupported
            | false => .ub
          | _, _ => .ub
      | .ub, _ => .ub
      | _, .ub => .ub
      | _, _ => .unsupported

/--
Evaluate `core::intrinsics::ptr_offset_from<T>(ptr, origin) -> isize`
(`unsigned = false`) and `core::intrinsics::ptr_offset_from_unsigned<T>(ptr, origin) -> usize`
(`unsigned = true`).

Exact semantics (aligned with `Miri/Interpreter/Intrinsics.lean:217-274, 439-440`
and `MiniRustSpec.Interp.evalPtrOffsetFrom`):
1. Resolves pointee type `T` and byte size `elemSize` (ZST `elemSize == 0` -> `.ub`;
   unsized -> `.ub`; unresolvable ADT -> `.unsupported`).
2. Decodes `ptr` and `origin` as thin pointers of width `ptrBytes`.
3. Same-allocation & directed in-bounds verification
   (`resolvePtrOffsetFromOffsetsProto`, `Intrinsics.lean:223-232, 250-262`):
   - two provenance-free integer pointers: equal addresses yield distance `0`,
     unequal addresses fault `.ub`;
   - the same tracked pointer (identical provenance and offset) yields distance
     `0` even when dangling or out of bounds ("point to the same address");
   - two tracked pointers must share one live allocation; a non-zero distance
     additionally requires BOTH endpoints in `[0, allocSize]` (inclusive of
     one-past-the-end);
   - cross-allocation, mixed tracked/provenance-free, dead-allocation, and
     out-of-bounds non-zero ranges ALL fault `.fail .ub`; two distinct dead
     tags of one root local fail closed with `.unsupported`.
4. Delegates range (`[-isize::MAX, isize::MAX]` signed, `[0, isize::MAX]`
   unsigned, rejecting `distance == isize::MIN` and unsigned underflow) and exact
   element-size divisibility to `evalPtrOffsetFromDistanceProto`.
5. Leaves `s.memory` completely unchanged (pointer arithmetic performs no memory
   access and does not expose provenance).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2268-L2278>

> "/// See documentation of `<*const T>::offset_from` for details."
> "pub const unsafe fn ptr_offset_from<T>(ptr: *const T, base: *const T) -> isize;"
>
> "/// See documentation of `<*const T>::offset_from_unsigned` for details."
> "pub const unsafe fn ptr_offset_from_unsigned<T>(ptr: *const T, base: *const T) -> usize;"

Reference (`<*const T>::offset_from` and `<*const T>::offset_from_unsigned`
documentation, `library/core/src/ptr/const_ptr.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L527-L574>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L665-L679>

> "/// Calculates the distance between two pointers within the same allocation. The returned value is in
> /// units of T: the distance in bytes divided by `size_of::<T>()`."
>
> "/// If any of the following conditions are violated, the result is Undefined Behavior:
> ///
> /// * `self` and `origin` must either
> ///
> ///   * point to the same address, or
> ///   * both be [derived from][crate::ptr#provenance] a pointer to the same [allocation], and the memory range between
> ///     the two pointers must be in bounds of that object. (See below for an example.)
> ///
> /// * The distance between the pointers, in bytes, must be an exact multiple
> ///   of the size of `T`.
> ///
> /// As a consequence, the absolute distance between the pointers, in bytes, computed on
> /// mathematical integers (without \"wrapping around\"), cannot overflow an `isize`. This is
> /// implied by the in-bounds requirement, and the fact that no allocation can be larger
> /// than `isize::MAX` bytes."
>
> "/// This function panics if `T` is a Zero-Sized Type (\"ZST\")."
>
> "/// - The distance between the pointers must be non-negative (`self >= origin`)
> ///
> /// - *All* the safety conditions of [`offset_from`](#method.offset_from)
> ///   apply to this method as well; see it for the full details.
> ///
> /// Importantly, despite the return type of this method being able to represent
> /// a larger offset, it's still *not permitted* to pass pointers which differ
> /// by more than `isize::MAX` *bytes*.  As such, the result of this method will
> /// always be less than or equal to `isize::MAX as usize`."
-/
def evalPtrOffsetFromProto
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx)
    (unsigned : Bool) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | ptrVal :: originVal :: .nil =>
    match
      decodeThinPtrArgProto? ptrBytes ptrVal,
      decodeThinPtrArgProto? ptrBytes originVal
    with
    | .some ptrArg, .some originArg =>
      match resolveMemIntrinsicPointeeTyProto? target bodyLocalDecls bodyLayouts argOps with
      | .none => intrinsicMissingPointeeStep bodyLocalDecls bodyLayouts argOps
      | .some elemTy =>
        match intrinsicRigidTyByteSize bodyLocalDecls bodyLayouts elemTy with
        | .none => intrinsicUnresolvedLayoutStep elemTy
        | .some elemSize =>
          -- ZST pointee is always UB (division by zero in exact_div).
          match Nat.beq elemSize 0 with
          | true => MirStepNode.fail .ub
          | false =>
            let offsetsRes : ProtoRes (Nat × Nat) :=
              resolvePtrOffsetFromOffsetsProto s locals' bodyLocalDecls bodyLayouts ptrArg originArg
            match offsetsRes with
            | .ub => MirStepNode.fail .ub
            | .unsupported => MirStepNode.unsupported
            | .ok (ptrOff, originOff) =>
              match evalPtrOffsetFromDistanceProto ptrOff originOff elemSize ptrBytes unsigned with
              | .none => MirStepNode.fail .ub
              | .some resSc =>
                writeIntrinsicReturnProto s locals' destination targetOpt (.scalar resSc)
                  bodyLocalDecls bodyLayouts
    | _, _ => MirStepNode.fail .ub
  | _ => MirStepNode.fail .ub

/-! ## Section 12: Intrinsic 7 — `core::intrinsics::ptr_mask` (Strict Provenance) -/

/--
Determine the guaranteed power-of-two byte alignment `allocAlign` and sub-place
byte offset `placeOff` of a tracked `ProvenancePtr`'s root allocation.
Returns `.none` when the allocation's alignment guarantee or sub-place offset
cannot be determined.
-/
def resolvePtrAllocAlignAndPlaceOffProto
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (p : ProvenancePtr) :
    Option (Nat × Nat) :=
  match lookupBorrow s.memory.borrows p.tag with
  | .some entry =>
    let (targetDecls, targetLayouts) :=
      borrowTargetDeclsAndLayoutsProto s.memory.callStack bodyLocalDecls bodyLayouts entry
    match
      get? targetDecls entry.targetLocal,
      borrowPlaceByteOffset? locals s.memory.callerLocals bodyLocalDecls bodyLayouts entry s.memory.callStack
    with
    | .some rootDecl, .some placeOff =>
      let rootTy := resolveTyWithLocalDecls targetDecls targetLayouts rootDecl.ty
      match tyExactByteAlign? targetDecls targetLayouts rootTy with
      | .some a =>
        match isPowerOfTwoNatProto a with
        | true => .some (a, placeOff)
        | false => .none
      | .none => .none
    | _, _ => .none
  | .none =>
    match lookupGlobalAlloc s.memory.globals p.allocId with
    | .some alloc =>
      match isPowerOfTwoNatProto alloc.align.bytes with
      | true => .some (alloc.align.bytes, 0)
      | false => .none
    | .none => .none

/--
Test whether `maskBits` (in `[0, 2^(8 * ptrBytes))`) is **base-address
invariant** for every allocation base address aligned to power-of-two
`allocAlign`: namely, every bit at position `>= log2(allocAlign)` in `maskBits`
is `1`, equivalently `(2^(8 * ptrBytes) - 1) - maskBits < allocAlign`.

Examples on 64-bit (`allocAlign = 8`):
- `mask = !7 = 0xFFFF_FFFF_FFFF_FFF8`: `allOnes - mask = 7 < 8` (`true`, the
  exact `zerocopy` aligned-pointer masking idiom!);
- `mask = !3 = 0xFFFF_FFFF_FFFF_FFFC`: `allOnes - mask = 3 < 8` (`true`);
- `mask = !0 = 0xFFFF_FFFF_FFFF_FFFF`: `allOnes - mask = 0 < 8` (`true`);
- `mask = !8` or `mask = 0x7`: clears bits above `allocAlign`, which depend on
  the unknown symbolic `baseAddr` (`false` -> fail closed `.unsupported`!).
-/
@[reducible]
def isBaseAddrInvariantMaskProto (ptrBytes allocAlign maskBits : Nat) : Bool :=
  let allOnes := Nat.sub (scalarModulus ptrBytes) 1
  Bool.and (isPowerOfTwoNatProto allocAlign) (Nat.blt (Nat.sub allOnes maskBits) allocAlign)

/--
Core pointer-masking transition supporting BOTH:
- **Symbolic base-address mode (`concreteBaseAddr? = .none`, default TCB mode)**:
  - Provenance-free integer pointers (`.addr bits` or unbacked `allocId = 0`):
    masks directly via `bitwiseAndBits (8 * ptrBytes) bits maskBits`.
  - Tracked pointers with provenance (`.prov p`): resolves `(allocAlign, placeOff)`;
    when `isBaseAddrInvariantMaskProto ptrBytes allocAlign maskBits` holds and
    `placeOff + p.offsetBytes < 2^(8 * ptrBytes)` and the masked total offset is
    `>= placeOff`, updates `offsetBytes` to `maskedTotal - placeOff` while
    **preserving `p.allocId` and `p.tag`** without exposing provenance!
    Whenever `maskBits` clears bits at or above `allocAlign` (depending on the
    unknown symbolic `baseAddr`) or would underflow below `placeOff`, fails
    closed with `.unsupported`.
- **Concrete base-address mode (`concreteBaseAddr? = .some baseAddr`)**:
  - When the caller/environment pins a concrete allocation base address
    `baseAddr` (aligned to `allocAlign`, with `baseAddr + placeOff + p.offsetBytes < 2^W`),
    computes `newAddr = (baseAddr + placeOff + p.offsetBytes) & maskBits`
    (1-to-1 with `Miri/Interpreter/Intrinsics.lean:508`), returning
    `{ p with offsetBytes := newAddr - (baseAddr + placeOff) }` whenever
    `newAddr >= baseAddr + placeOff` (or `.unsupported` if the mask pulled the
    address below `baseAddr + placeOff`, which a non-negative relative `Nat`
    `offsetBytes` cannot represent).
-/
def evalPtrMaskValueProto
    (s : MachineState)
    (locals : List LocalSlot)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (ptrArg : PtrArgProto)
    (maskSc : ScalarInt)
    (concreteBaseAddr? : Option Nat := .none) :
    ProtoRes Value :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match Nat.beq maskSc.sizeBytes ptrBytes with
  | false => .ub
  | true =>
    let ptrBits := Nat.mul ptrBytes 8
    let modulus := scalarModulus ptrBytes
    let maskBits := wrapScalarBits maskSc.bits modulus
    match ptrArg with
    | .addr bits =>
      let masked := bitwiseAndBits ptrBits bits maskBits
      .ok (.scalar ⟨masked, ptrBytes⟩)
    | .prov p =>
      let isUnbackedZero :=
        Bool.and (Nat.beq p.allocId 0)
          (Bool.and
            (match lookupBorrow s.memory.borrows 0 with | .none => true | .some _ => false)
            (match lookupGlobalAlloc s.memory.globals 0 with | .none => true | .some _ => false))
      match isUnbackedZero with
      | true =>
        let oldAddr := wrapScalarBits p.offsetBytes modulus
        let masked := bitwiseAndBits ptrBits oldAddr maskBits
        .ok (.ptr { allocId := 0, offsetBytes := masked } ptrBytes)
      | false =>
        match resolvePtrAllocAlignAndPlaceOffProto s locals bodyLocalDecls bodyLayouts p with
        | .none => .unsupported
        | .some (allocAlign, placeOff) =>
          let totalRelOff := Nat.add placeOff p.offsetBytes
          match concreteBaseAddr? with
          | .none =>
            -- Sound symbolic base-address mode: only allow masks invariant under all `allocAlign`-aligned bases.
            match
              Bool.and
                (isBaseAddrInvariantMaskProto ptrBytes allocAlign maskBits)
                (Nat.blt totalRelOff modulus)
            with
            | false => .unsupported
            | true =>
              let maskedTotal := bitwiseAndBits ptrBits totalRelOff maskBits
              match Nat.ble placeOff maskedTotal with
              | false => .unsupported
              | true =>
                .ok (.ptr { allocId := p.allocId, offsetBytes := Nat.sub maskedTotal placeOff } ptrBytes)
          | .some baseAddr =>
            -- Concrete base-address mode: exact `(baseAddr + totalRelOff) & mask`.
            let absBase := Nat.add baseAddr placeOff
            let absOld := Nat.add baseAddr totalRelOff
            match
              Bool.and
                (isAlignedOffset baseAddr allocAlign)
                (Nat.blt absOld modulus)
            with
            | false => .unsupported
            | true =>
              let absNew := bitwiseAndBits ptrBits absOld maskBits
              match Nat.ble absBase absNew with
              | false => .unsupported
              | true =>
                .ok (.ptr { allocId := p.allocId, offsetBytes := Nat.sub absNew absBase } ptrBytes)

/--
Evaluate `core::intrinsics::ptr_mask<T>(ptr: *const T, mask: usize) -> *const T`.

Preserves `ProvenancePtr.allocId` and Tree Borrows `ProvenancePtr.tag` and
NEVER modifies `s.memory.exposedAllocIds` (strict provenance, non-exposing).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L944-L954>

> "/// Masks out bits of the pointer according to a mask.
> ///
> /// Note that, unlike most intrinsics, this is safe to call;
> /// it does not require an `unsafe` block.
> /// Therefore, implementations must not require the user to uphold
> /// any safety invariants.
> ///
> /// Consider using [`pointer::mask`] instead."

Reference (`<*const T>::mask` documentation, `library/core/src/ptr/const_ptr.rs`
at commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/ptr/const_ptr.rs#L489-L494>

> "/// Masks out bits of the pointer according to a mask.
> ///
> /// This is convenience for `ptr.map_addr(|a| a & mask)`.
> ///
> /// For non-`Sized` pointees this operation changes only the data pointer,
> /// leaving the metadata untouched."
-/
def evalPtrMaskProto
    (s : MachineState)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx)
    (concreteBaseAddr? : Option Nat := .none) :
    MirStepNode :=
  let ptrBytes := layoutPointerBytes bodyLayouts
  match argVals with
  | ptrVal :: .scalar maskSc :: .nil =>
    match decodeThinPtrArgProto? ptrBytes ptrVal with
    | .none => MirStepNode.fail .ub
    | .some ptrArg =>
      match evalPtrMaskValueProto s locals' bodyLocalDecls bodyLayouts ptrArg maskSc concreteBaseAddr? with
      | .ub => MirStepNode.fail .ub
      | .unsupported => MirStepNode.unsupported
      | .ok maskedVal =>
        writeIntrinsicReturnProto s locals' destination targetOpt maskedVal
          bodyLocalDecls bodyLayouts
  | _ => MirStepNode.fail .ub

/-! ## Section 13: Intrinsic 8 — `core::intrinsics::black_box` -/

/--
Validate `v` as a valid Rust value of optional type `tyOpt` for `black_box<T>`
(preserving `.uninit` inside union/`MaybeUninit` types while rejecting bare
`Value.uninit`, non-union aggregates containing `Value.uninit`, uninhabited
types, invalid `bool`/`char` bit patterns, and null thin references).

Reference (The Rust Reference 1.98.0, "Behavior considered undefined — Invalid values"):
<https://doc.rust-lang.org/1.98.0/reference/behavior-considered-undefined.html#invalid-values>

> "The Rust compiler assumes that all values produced during program execution
> are “valid”, and producing an invalid value is hence immediate UB."
-/
def validateBlackBoxValueProto
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (mem : Memory)
    (tyOpt : Option RigidTy)
    (v : Value) :
    Bool :=
  match tyOpt with
  | .none => Bool.not (valueContainsUninit v)
  | .some ty =>
    match isUninhabitedRigidTyProto bodyLocalDecls bodyLayouts 8 ty with
    | true => false
    | false =>
      match rigidTyIsUnionProto bodyLocalDecls bodyLayouts ty with
      | true => true
      | false =>
        match valueContainsUninit v with
        | true => false
        | false =>
          let resolvedTy := resolveRigidTyWithDeclsProto bodyLocalDecls bodyLayouts ty
          match validateValueForTy? bodyLayouts (.some resolvedTy) v with
          | false => false
          | true =>
            match ty with
            | .ref _ pointee =>
              let isWide :=
                match pointee with
                | .slice _ | .str | .dynamic _ => true
                | _ => false
              match isWide with
              | true => true
              | false =>
                match decodeThinPtrArgProto? (layoutPointerBytes bodyLayouts) v with
                | .some pArg => Bool.not (isNullPtrArgProto mem pArg)
                | .none => false
            | _ => true

/--
Evaluate `core::intrinsics::black_box<T>(dummy: T) -> T`.

Exact semantics (aligned with `Miri/Interpreter/Intrinsics.lean:441`
`h.copyOp choice (← arg args 0) dest`):
1. Requires exactly one argument `dummyVal` (else `.fail .ub`).
2. Resolves `T` from `target.typeArgs`, `argOps`, or `destination` and enforces
   Rust typed validity (`validateBlackBoxValueProto`: rejects uninit scalars,
   invalid `bool`/`char`, null `&T`, uninhabited `!`, while preserving union /
   `MaybeUninit` uninit values, pointer `allocId` + Tree Borrows `tag`, and
   compound structs/arrays verbatim).
3. Writes `dummyVal` to `destination` via `writeIntrinsicReturnProto` (full
   place projection + Tree Borrows write + protector checks) and jumps to
   `targetOpt` (`.fail .ub` if `targetOpt = .none`).

Reference (`library/core/src/intrinsics/mod.rs` at commit
`14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/intrinsics/mod.rs#L2339-L2345>

> "/// See documentation of [`std::hint::black_box`] for details."
> "pub const fn black_box<T>(dummy: T) -> T;"

Reference (`core::hint::black_box` documentation, `library/core/src/hint.rs` at
commit `14210df0e27ccd7d9e6a05b8085cbd438e4bbc65`):
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/hint.rs#L315-L321>
<https://github.com/rust-lang/rust/blob/14210df0e27ccd7d9e6a05b8085cbd438e4bbc65/library/core/src/hint.rs#L486>

> "/// An identity function that *__hints__* to the compiler to be maximally pessimistic about what
> /// `black_box` could do.
> ///
> /// Unlike [`std::convert::identity`], a Rust compiler is encouraged to assume that `black_box` can
> /// use `dummy` in any possible valid way that Rust code is allowed to without introducing undefined
> /// behavior in the calling code. This property makes `black_box` useful for writing code in which
> /// certain optimizations are not desired, such as benchmarks."
>
> "/// During constant evaluation, `black_box` is treated as a no-op."
-/
def evalBlackBoxProto
    (s : MachineState)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx) :
    MirStepNode :=
  match argVals with
  | dummyVal :: .nil =>
    let tyOpt : Option RigidTy :=
      match target.typeArgs with
      | t :: _ => .some t
      | .nil =>
        match argOps with
        | op0 :: _ =>
          match operandTy bodyLocalDecls bodyLayouts op0 with
          | .some ty => .some ty.kind
          | .none =>
            match placeTy bodyLocalDecls bodyLayouts destination with
            | .some dTy => .some dTy.kind
            | .none => .none
        | .nil =>
          match placeTy bodyLocalDecls bodyLayouts destination with
          | .some dTy => .some dTy.kind
          | .none => .none
    match validateBlackBoxValueProto bodyLocalDecls bodyLayouts s.memory tyOpt dummyVal with
    | false => MirStepNode.fail .ub
    | true =>
      writeIntrinsicReturnProto s locals' destination targetOpt dummyVal
        bodyLocalDecls bodyLayouts
  | _ => MirStepNode.fail .ub

/-! ## Section 14: Drop-In Candidate Direct Intrinsic Dispatcher -/

/--
Drop-in candidate extension of `Terminators.evalDirectRustIntrinsic?`
dispatching all 8 new core memory and pointer intrinsics alongside the existing
27 modeled `core::intrinsics::*` paths.

Supports both normal (`targetOpt = .some targetBb`) and diverging
(`targetOpt = .none`) calls: returning normally from any of the 8 new returning
intrinsics into `targetOpt = .none` faults with `MirStepNode.fail .ub`.
-/
@[reducible]
def evalDirectRustIntrinsicProto?
    (s : MachineState)
    (currentBody : Option CapturedMir)
    (target : ResolvedCallTarget)
    (bodyLocalDecls : List LocalDecl)
    (bodyLayouts : LayoutTable)
    (argOps : List Operand)
    (argVals : List Value)
    (locals' : List LocalSlot)
    (destination : Place)
    (targetOpt : Option BasicBlockIdx)
    (unwind : UnwindAction) :
    Option MirStepNode :=
  match classifyRustIntrinsicProto? target.defPath with
  | .none => .none
  | .some .copy =>
    .some (evalCopyProto s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | .some .compareBytes =>
    .some (evalCompareBytesProto s bodyLocalDecls bodyLayouts argVals locals' destination targetOpt)
  | .some .rawEq =>
    .some (evalRawEqProto s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | .some .typedSwapNonOverlapping =>
    .some (evalTypedSwapNonOverlappingProto s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | .some .ptrOffsetFrom =>
    .some (evalPtrOffsetFromProto s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt false)
  | .some .ptrOffsetFromUnsigned =>
    .some (evalPtrOffsetFromProto s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt true)
  | .some .ptrMask =>
    .some (evalPtrMaskProto s bodyLocalDecls bodyLayouts argVals locals' destination targetOpt)
  | .some .blackBox =>
    .some (evalBlackBoxProto s target bodyLocalDecls bodyLayouts argOps argVals locals' destination targetOpt)
  | .some (.base _) =>
    match targetOpt with
    | .some targetBb =>
      evalDirectRustIntrinsic? s currentBody target bodyLocalDecls bodyLayouts argOps argVals locals'
        destination targetBb unwind
    | .none => .some (MirStepNode.fail .ub)

/-! ## Section 15: Mathematical & `lean-miri` Reference Alignment Theorems -/

/--
`LeanMiri` spec mirror of `Miri.Interpreter.Intrinsics.bytesCompare`
(`lean-miri/vendor/Miri/Interpreter/Intrinsics.lean:174-176`).
-/
def miriBytesCompareSpec : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => if a == b then miriBytesCompareSpec as bs else compare a b

/--
**`LeanMiri` Alignment Theorem (`compare_bytes` byte comparator)**:
`compareUnsignedBytesProto` agrees identically on all byte lists with
`Miri.Interpreter.Intrinsics.bytesCompare` (`Intrinsics.lean:174-176`).
-/
theorem compareUnsignedBytesProto_eq_miriBytesCompareSpec :
    ∀ xs ys : List UInt8, compareUnsignedBytesProto xs ys = miriBytesCompareSpec xs ys
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | a :: as, b :: bs => by
    simp only [compareUnsignedBytesProto, miriBytesCompareSpec]
    have hEq : Nat.beq a.toBitVec.toNat b.toBitVec.toNat = (a == b) := by
      cases a with | ofBitVec av =>
      cases b with | ofBitVec bv =>
      by_cases h : av.toNat = bv.toNat
      · have hab : av = bv := BitVec.eq_of_toNat_eq h
        subst hab
        simp
      · have hne : (UInt8.ofBitVec av == UInt8.ofBitVec bv) = false := by
          simp only [BEq.beq]
          exact decide_eq_false (fun h' => h (congrArg (fun x => x.toBitVec.toNat) h'))
        have hbeq : Nat.beq av.toNat bv.toNat = false := by
          cases hb : Nat.beq av.toNat bv.toNat
          · rfl
          · exact absurd (Nat.beq_eq.mp hb) h
        rw [hbeq, hne]
    rw [hEq]
    cases hAB : (a == b)
    · simp only [Bool.false_eq_true, ↓reduceIte]
      have hne : a.toBitVec.toNat ≠ b.toBitVec.toNat := by
        intro heq
        have h1 : a = b := by
          cases a; cases b
          congr
          exact BitVec.eq_of_toNat_eq heq
        subst h1
        simp at hAB
      change (match Nat.blt a.toBitVec.toNat b.toBitVec.toNat with | true => Ordering.lt | false => Ordering.gt) =
        compare a b
      simp only [compare, Ord.compare, compareOfLessAndEq]
      have hltIff : (a < b) ↔ (a.toBitVec.toNat < b.toBitVec.toNat) := by
        rw [UInt8.lt_iff_toBitVec_lt, BitVec.lt_def]
      have heqIff : (a = b) ↔ (a.toBitVec.toNat = b.toBitVec.toNat) := by
        constructor
        · intro h; rw [h]
        · intro h; cases a; cases b; congr; exact BitVec.eq_of_toNat_eq h
      by_cases hlt : a.toBitVec.toNat < b.toBitVec.toNat
      · have h1 : Nat.blt a.toBitVec.toNat b.toBitVec.toNat = true := Nat.blt_eq.mpr hlt
        rw [h1]
        have h2 : a < b := hltIff.mpr hlt
        simp [h2]
      · have h1 : Nat.blt a.toBitVec.toNat b.toBitVec.toNat = false := by
          cases hb : Nat.blt a.toBitVec.toNat b.toBitVec.toNat
          · rfl
          · exact absurd (Nat.blt_eq.mp hb) hlt
        rw [h1]
        have h2 : ¬ (a < b) := fun h => hlt (hltIff.mp h)
        have h3 : ¬ (a = b) := fun h => hne (heqIff.mp h)
        simp [h2, h3]
    · simp only [↓reduceIte]
      exact compareUnsignedBytesProto_eq_miriBytesCompareSpec as bs

/--
**Soundness of `bitwiseAndBits` vs `Nat.land` on `W`-bit unsigned integers**:
For all `W`, `a`, `b`, `bitwiseAndBits W a b = (a &&& b) % 2 ^ W`.
-/
theorem bitwiseAndBits_eq_land_mod :
    ∀ W a b : Nat, bitwiseAndBits W a b = (a &&& b) % 2 ^ W
  | 0, _, _ => by simp [bitwiseAndBits, Nat.mod_one]
  | k + 1, a, b => by
    have ih := bitwiseAndBits_eq_land_mod k (a / 2) (b / 2)
    unfold bitwiseAndBits
    change (match Bool.and (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with | true => 1 | false => 0) +
      2 * bitwiseAndBits k (a / 2) (b / 2) = (a &&& b) % 2 ^ (k + 1)
    rw [ih]
    have hBit :
        (match Bool.and (Nat.beq (a % 2) 1) (Nat.beq (b % 2) 1) with | true => 1 | false => 0) =
        (a &&& b) % 2 := by
      have ha : a % 2 = 0 ∨ a % 2 = 1 := Nat.mod_two_eq_zero_or_one a
      have hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
      have hland : (a &&& b) % 2 = (a % 2) &&& (b % 2) := by
        simpa using (Nat.and_mod_two_pow (a := a) (b := b) (n := 1))
      rw [hland]
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]
    rw [hBit]
    have hDiv : (a &&& b) / 2 = (a / 2) &&& (b / 2) := by
      simpa using (Nat.and_div_two_pow (a := a) (b := b) (n := 1))
    rw [← hDiv]
    have hPow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [hPow]
    have hDecomp : ∀ x : Nat, x % 2 + 2 * ((x / 2) % 2 ^ k) = x % (2 * 2 ^ k) := by
      intro x
      exact Nat.mod_mul.symm
    exact hDecomp (a &&& b)

/--
Helper: if `(2^W - 1) - mask < 2^m` and `mask < 2^W`, then for every bit
position `i` with `m ≤ i < W`, `Nat.testBit mask i = true`.
-/
theorem testBit_mask_high_ones (W m mask i : Nat)
    (hMaskLt : mask < 2 ^ W)
    (hMaskHigh : (2 ^ W - 1) - mask < 2 ^ m)
    (hm : m ≤ i) (hi : i < W) :
    mask.testBit i = true := by
  have hComp : (2 ^ W - 1) - mask + mask = 2 ^ W - 1 := by omega
  -- If bit i of mask were false, then `(2^W - 1) - mask` would be >= 2^i >= 2^m.
  -- Prove by examining `mask / 2^m`!
  have hmW : m ≤ W := Nat.le_of_lt (Nat.lt_of_le_of_lt hm hi)
  have hPowSplit : 2 ^ W = 2 ^ m * 2 ^ (W - m) := by
    rw [← Nat.pow_add, Nat.add_sub_of_le hmW]
  have hMaskDiv : mask / 2 ^ m = 2 ^ (W - m) - 1 := by
    have h1 : mask ≥ 2 ^ W - 2 ^ m := by omega
    have h2 : mask < 2 ^ m * 2 ^ (W - m) := by rw [← hPowSplit]; exact hMaskLt
    have h3 : 2 ^ m * (2 ^ (W - m) - 1) ≤ mask := by
      have : 2 ^ m * (2 ^ (W - m) - 1) = 2 ^ m * 2 ^ (W - m) - 2 ^ m := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      rw [this, ← hPowSplit]
      exact h1
    have hPos : 0 < 2 ^ m := Nat.pow_pos (by decide)
    have hLo : 2 ^ (W - m) - 1 ≤ mask / 2 ^ m := by
      exact (Nat.le_div_iff_mul_le hPos).mpr (by rw [Nat.mul_comm]; exact h3)
    have hHi : mask / 2 ^ m < 2 ^ (W - m) := by
      exact (Nat.div_lt_iff_lt_mul hPos).mpr (by rw [Nat.mul_comm]; exact h2)
    omega
  have hShift : mask.testBit i = (mask / 2 ^ m).testBit (i - m) := by
    rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel hm]
  rw [hShift, hMaskDiv]
  have hSubLt : i - m < W - m := by omega
  rw [Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hSubLt

/--
**Universal Base-Address Invariance Theorem for `ptr_mask`**:
For ANY word width `W`, alignment exponent `m`, allocation base address
`baseAddr` aligned to `2^m` (`baseAddr % 2^m = 0`), relative offset `relOff`,
and mask `mask < 2^W` that leaves all bits `≥ m` set (`(2^W - 1) - mask < 2^m`):

`bitwiseAndBits W (baseAddr + relOff) mask = baseAddr + bitwiseAndBits W relOff mask`

whenever `baseAddr + relOff < 2^W`. This kernel-proves that symbolic-base
`evalPtrMaskProto` on `zerocopy`-style alignment masks (`!(align - 1)`) agrees
identically with concrete-address Miri `ptr_mask` (`Miri/Interpreter/Intrinsics.lean:508`)
under EVERY valid allocator placement of `baseAddr`!
-/
theorem ptrMask_baseAddr_invariant (W m baseAddr relOff mask : Nat)
    (hBaseAlign : baseAddr % 2 ^ m = 0)
    (hMaskLt : mask < 2 ^ W)
    (hMaskHigh : (2 ^ W - 1) - mask < 2 ^ m)
    (hSumLt : baseAddr + relOff < 2 ^ W) :
    bitwiseAndBits W (baseAddr + relOff) mask =
      baseAddr + bitwiseAndBits W relOff mask := by
  rw [bitwiseAndBits_eq_land_mod, bitwiseAndBits_eq_land_mod]
  have hRelLt : relOff < 2 ^ W := by omega
  have hLhsLt : (baseAddr + relOff) &&& mask < 2 ^ W :=
    Nat.lt_of_le_of_lt Nat.and_le_right hMaskLt
  have hRelAndLt : relOff &&& mask < 2 ^ W :=
    Nat.lt_of_le_of_lt Nat.and_le_right hMaskLt
  rw [Nat.mod_eq_of_lt hLhsLt, Nat.mod_eq_of_lt hRelAndLt]
  -- Split `baseAddr = q * 2^m` and `relOff = rH * 2^m + rL` with `rL < 2^m`.
  have hPos : 0 < 2 ^ m := Nat.pow_pos (by decide)
  have hBaseEq : baseAddr = 2 ^ m * (baseAddr / 2 ^ m) := by
    have := Nat.div_add_mod baseAddr (2 ^ m)
    omega
  -- Prove bitwise equality at every bit `i` via `Nat.eq_of_testBit_eq`!
  have hTbLt : ∀ n k : Nat, n < 2 ^ k → n.testBit k = false := by
    intro n k hlt
    simp [Nat.testBit, Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hiW : i < W
  · by_cases him : i < m
    · -- Low bits `i < m`: `baseAddr` is 0 in all bits `< m`, so adding `baseAddr`
      -- (a multiple of `2^m`) does not affect bits `< m` on either side!
      have hModAdd : ∀ x : Nat, (baseAddr + x) % 2 ^ m = x % 2 ^ m := by
        intro x
        rw [hBaseEq, Nat.mul_add_mod]
      have hBitLow : ∀ x : Nat, (baseAddr + x).testBit i = x.testBit i := by
        intro x
        have h1 : (baseAddr + x).testBit i = ((baseAddr + x) % 2 ^ m).testBit i := by
          rw [Nat.testBit_mod_two_pow, decide_eq_true him, Bool.true_and]
        have h2 : x.testBit i = (x % 2 ^ m).testBit i := by
          rw [Nat.testBit_mod_two_pow, decide_eq_true him, Bool.true_and]
        rw [h1, hModAdd x, ← h2]
      rw [Nat.testBit_and, hBitLow relOff, hBitLow (relOff &&& mask), Nat.testBit_and]
    · -- High bits `m ≤ i < W`: bit `i` of `mask` is `true`, and `relOff &&& mask`
      -- has the same quotient mod `2^m` as `relOff`!
      have hge : m ≤ i := Nat.le_of_not_lt him
      have hMaskBit : mask.testBit i = true :=
        testBit_mask_high_ones W m mask i hMaskLt hMaskHigh hge hiW
      rw [Nat.testBit_and, hMaskBit, Bool.and_true]
      -- Show `(baseAddr + (relOff &&& mask)) / 2^m = (baseAddr + relOff) / 2^m`
      have hRelDiv : (relOff &&& mask) / 2 ^ m = relOff / 2 ^ m := by
        apply Nat.eq_of_testBit_eq
        intro j
        rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.testBit_and]
        have hComm : j + m = m + j := Nat.add_comm j m
        rw [hComm]
        by_cases hmj : m + j < W
        · have hmb : mask.testBit (m + j) = true :=
            testBit_mask_high_ones W m mask (m + j) hMaskLt hMaskHigh (Nat.le_add_right m j) hmj
          rw [hmb, Bool.and_true]
        · have hZero : relOff.testBit (m + j) = false :=
            hTbLt relOff (m + j) (Nat.lt_of_lt_of_le hRelLt (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hmj)))
          rw [hZero, Bool.false_and]
      have hAddDiv : ∀ x : Nat, (baseAddr + x) / 2 ^ m = baseAddr / 2 ^ m + x / 2 ^ m := by
        intro x
        have hTmp : (2 ^ m * (baseAddr / 2 ^ m) + x) / 2 ^ m = baseAddr / 2 ^ m + x / 2 ^ m :=
          Nat.mul_add_div hPos (baseAddr / 2 ^ m) x
        rw [← hBaseEq] at hTmp
        exact hTmp
      have hShiftL : (baseAddr + relOff).testBit i = ((baseAddr + relOff) / 2 ^ m).testBit (i - m) := by
        rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel hge]
      have hShiftR : (baseAddr + (relOff &&& mask)).testBit i =
          ((baseAddr + (relOff &&& mask)) / 2 ^ m).testBit (i - m) := by
        rw [Nat.testBit_div_two_pow, Nat.sub_add_cancel hge]
      rw [hShiftL, hShiftR, hAddDiv relOff, hAddDiv (relOff &&& mask), hRelDiv]
  · -- Bits `i ≥ W`: both sides are `< 2^W`, so bit `i` is `false` on both sides!
    have hGeW : W ≤ i := Nat.le_of_not_lt hiW
    have hPowLe : 2 ^ W ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hGeW
    have hRhsLt : baseAddr + (relOff &&& mask) < 2 ^ W := by
      have hLe : relOff &&& mask ≤ relOff := Nat.and_le_left
      omega
    rw [hTbLt _ i (Nat.lt_of_lt_of_le hLhsLt hPowLe),
        hTbLt _ i (Nat.lt_of_lt_of_le hRhsLt hPowLe)]

/--
**`ptr_mask` Non-Exposure & Provenance-Preservation Theorem**:
For every machine state `s`, local frame, pointer `p`, mask `maskSc`, and
optional concrete base address `concreteBaseAddr?`, whenever `evalPtrMaskProto`
succeeds on a tracked `ProvenancePtr` `p` (not unbacked `allocId = 0`), the
resulting `MachineState` preserves `s.memory.exposedAllocIds` unchanged (strict
provenance, never exposing `p.allocId`), and the returned pointer preserves both
`p.allocId` and `p.tag`!
-/
theorem evalPtrMaskValueProto_preserves_provenance
    (s : MachineState) (locals : List LocalSlot)
    (decls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (maskSc : ScalarInt)
    (concreteBaseAddr? : Option Nat) (v : Value)
    (hOk : evalPtrMaskValueProto s locals decls layouts (.prov p) maskSc concreteBaseAddr? = .ok v) :
    ∃ newOff, v = .ptr { allocId := p.allocId, offsetBytes := newOff } (layoutPointerBytes layouts) := by
  unfold evalPtrMaskValueProto at hOk
  dsimp only at hOk
  split at hOk
  · cases hOk
  · split at hOk
    · rename_i hZero
      cases hOk
      have hA : p.allocId = 0 := by
        cases hEq0 : Nat.beq p.allocId 0
        · rw [hEq0] at hZero; cases hZero
        · exact Nat.beq_eq.mp hEq0
      rw [hA]
      exact ⟨_, rfl⟩
    · split at hOk
      · cases hOk
      · cases concreteBaseAddr? with
        | none =>
          dsimp only at hOk
          split at hOk
          · cases hOk
          · split at hOk
            · cases hOk
            · cases hOk
              exact ⟨_, rfl⟩
        | some baseAddr =>
          dsimp only at hOk
          split at hOk
          · cases hOk
          · split at hOk
            · cases hOk
            · cases hOk
              exact ⟨_, rfl⟩

/--
**`ptr_mask` Concrete-vs-Symbolic Equivalence Theorem**:
Whenever symbolic-base `evalPtrMaskValueProto ... .none` succeeds on a tracked
pointer `p` (with allocation alignment `allocAlign`), concrete-base
`evalPtrMaskValueProto ... (.some baseAddr)` produces the **exact same pointer**
for EVERY valid `allocAlign`-aligned `baseAddr` with
`baseAddr + placeOff + p.offsetBytes < 2^(8 * ptrBytes)`!
-/
theorem evalPtrMaskValueProto_symbolic_eq_concrete
    (s : MachineState) (locals : List LocalSlot)
    (decls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) (maskSc : ScalarInt)
    (allocAlign placeOff baseAddr : Nat) (v : Value)
    (hNotZero :
      Bool.and (Nat.beq p.allocId 0)
        (Bool.and
          (match lookupBorrow s.memory.borrows 0 with | .none => true | .some _ => false)
          (match lookupGlobalAlloc s.memory.globals 0 with | .none => true | .some _ => false)) = false)
    (hResolve : resolvePtrAllocAlignAndPlaceOffProto s locals decls layouts p = .some (allocAlign, placeOff))
    (hPow2 : ∃ m, allocAlign = 2 ^ m)
    (hBaseAligned : baseAddr % allocAlign = 0)
    (hSumLt : baseAddr + (placeOff + p.offsetBytes) < scalarModulus (layoutPointerBytes layouts))
    (hSym : evalPtrMaskValueProto s locals decls layouts (.prov p) maskSc .none = .ok v) :
    evalPtrMaskValueProto s locals decls layouts (.prov p) maskSc (.some baseAddr) = .ok v := by
  have hModPow : ∀ n : Nat, scalarModulus n = 2 ^ (n * 8) := by
    intro n
    induction n with
    | zero => rfl
    | succ k ih =>
      simp only [scalarModulus]
      rw [ih]
      have : (k + 1) * 8 = 8 + k * 8 := by omega
      rw [this, Nat.pow_add]
      rfl
  unfold evalPtrMaskValueProto at hSym ⊢
  dsimp only at hSym ⊢
  split at hSym
  · cases hSym
  · rename_i hSz
    rw [hNotZero] at hSym ⊢
    dsimp only at hSym ⊢
    rw [hResolve] at hSym ⊢
    dsimp only at hSym ⊢
    rcases hPow2 with ⟨m, rfl⟩
    split at hSym
    · cases hSym
    · rename_i hCond
      split at hSym
      · cases hSym
      · rename_i hPlaceLe
        have hInv : isBaseAddrInvariantMaskProto (layoutPointerBytes layouts) (2 ^ m)
            (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))) = true := by
          cases h1 : isBaseAddrInvariantMaskProto (layoutPointerBytes layouts) (2 ^ m)
              (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)))
          · rw [h1] at hCond; cases hCond
          · rfl
        have hMaskHigh :
            (2 ^ (layoutPointerBytes layouts * 8) - 1) -
              wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)) < 2 ^ m := by
          unfold isBaseAddrInvariantMaskProto at hInv
          dsimp only at hInv
          have hBlt :
              Nat.blt
                (Nat.sub (Nat.sub (scalarModulus (layoutPointerBytes layouts)) 1)
                  (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))))
                (2 ^ m) = true := by
            cases hLt : Nat.blt
                (Nat.sub (Nat.sub (scalarModulus (layoutPointerBytes layouts)) 1)
                  (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))))
                (2 ^ m)
            · rw [hLt] at hInv
              cases hP : isPowerOfTwoNatProto (2 ^ m) <;> rw [hP] at hInv <;> cases hInv
            · rfl
          have hLtNat :
              (scalarModulus (layoutPointerBytes layouts) - 1) -
                wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)) < 2 ^ m :=
            Nat.blt_eq.mp hBlt
          rw [← hModPow]
          exact hLtNat
        have hMaskLt :
            wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)) <
              2 ^ (layoutPointerBytes layouts * 8) := by
          rw [← hModPow]
          unfold wrapScalarBits
          have hPos : 0 < scalarModulus (layoutPointerBytes layouts) := by
            rw [hModPow]; exact Nat.pow_pos (by decide)
          cases hBle : Nat.ble (scalarModulus (layoutPointerBytes layouts)) maskSc.bits
          · dsimp only
            have hNotLe : ¬ (scalarModulus (layoutPointerBytes layouts) ≤ maskSc.bits) := fun h => by
              rw [Nat.ble_eq.mpr h] at hBle; cases hBle
            omega
          · dsimp only
            exact Nat.mod_lt _ hPos
        have hSumLtPow : baseAddr + (placeOff + p.offsetBytes) < 2 ^ (layoutPointerBytes layouts * 8) := by
          rw [← hModPow]; exact hSumLt
        have hEqBits :=
          ptrMask_baseAddr_invariant
            (layoutPointerBytes layouts * 8) m baseAddr (placeOff + p.offsetBytes)
            (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)))
            hBaseAligned hMaskLt hMaskHigh hSumLtPow
        have hAlignBool : isAlignedOffset baseAddr (2 ^ m) = true := by
          unfold isAlignedOffset
          have hNe : Nat.beq (2 ^ m) 0 = false := by
            have hnz : 2 ^ m ≠ 0 := Nat.ne_of_gt (Nat.pow_pos (by decide))
            cases hb : Nat.beq (2 ^ m) 0
            · rfl
            · exact absurd (Nat.beq_eq.mp hb) hnz
          rw [hNe]
          exact Nat.beq_eq.mpr hBaseAligned
        have hSumBool :
            Nat.blt (Nat.add baseAddr (Nat.add placeOff p.offsetBytes))
              (scalarModulus (layoutPointerBytes layouts)) = true :=
          Nat.blt_eq.mpr hSumLt
        have hConj : Bool.and (isAlignedOffset baseAddr (2 ^ m))
            (Nat.blt (Nat.add baseAddr (Nat.add placeOff p.offsetBytes))
              (scalarModulus (layoutPointerBytes layouts))) = true := by
          rw [hAlignBool, hSumBool]; rfl
        rw [hConj]
        dsimp only
        change (match Nat.ble (baseAddr + placeOff)
            (bitwiseAndBits (layoutPointerBytes layouts * 8) (baseAddr + (placeOff + p.offsetBytes))
              (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)))) with
          | false => ProtoRes.unsupported
          | true => ProtoRes.ok (Value.ptr {
              allocId := p.allocId
              offsetBytes := Nat.sub
                (bitwiseAndBits (layoutPointerBytes layouts * 8) (baseAddr + (placeOff + p.offsetBytes))
                  (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))))
                (baseAddr + placeOff) } (layoutPointerBytes layouts))) = .ok v
        rw [hEqBits]
        have hLe : placeOff ≤ bitwiseAndBits (layoutPointerBytes layouts * 8)
            (placeOff + p.offsetBytes)
            (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))) :=
          Nat.ble_eq.mp hPlaceLe
        have hLe2 : Nat.ble (baseAddr + placeOff)
            (baseAddr + bitwiseAndBits (layoutPointerBytes layouts * 8)
              (placeOff + p.offsetBytes)
              (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)))) = true :=
          Nat.ble_eq.mpr (by omega)
        rw [hLe2]
        have hSub :
            Nat.sub (baseAddr + bitwiseAndBits (layoutPointerBytes layouts * 8)
              (placeOff + p.offsetBytes)
              (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))))
              (baseAddr + placeOff) =
            Nat.sub (bitwiseAndBits (layoutPointerBytes layouts * 8)
              (placeOff + p.offsetBytes)
              (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))))
              placeOff := by
          change (baseAddr + bitwiseAndBits (layoutPointerBytes layouts * 8)
              (placeOff + p.offsetBytes)
              (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts)))) -
              (baseAddr + placeOff) =
            bitwiseAndBits (layoutPointerBytes layouts * 8)
              (placeOff + p.offsetBytes)
              (wrapScalarBits maskSc.bits (scalarModulus (layoutPointerBytes layouts))) -
              placeOff
          omega
        rw [hSub]
        exact hSym

/--
**`ptr_offset_from` / `ptr_offset_from_unsigned` Algebraic Soundness Theorem**:
1. ZST (`elemSize = 0`) always returns `.none` (UB);
2. `ptr_offset_from_unsigned` with `ptrOff < originOff` always returns `.none` (UB);
3. `distance == isize::MIN` (`ptrOff = 0, originOff = 2^(8*ptrBytes - 1)`) always
   returns `.none` (UB) for both signed and unsigned;
4. Unaligned endpoints with `|ptrOff - originOff| % elemSize = 0` in valid range
   always succeed regardless of `ptrOff % elemSize`!
-/
theorem evalPtrOffsetFromDistanceProto_zst_ub (ptrOff originOff ptrBytes : Nat) (unsigned : Bool) :
    evalPtrOffsetFromDistanceProto ptrOff originOff 0 ptrBytes unsigned = .none := rfl

theorem evalPtrOffsetFromDistanceProto_unsigned_underflow_ub
    (ptrOff originOff elemSize ptrBytes : Nat) (hLt : ptrOff < originOff) :
    evalPtrOffsetFromDistanceProto ptrOff originOff elemSize ptrBytes true = .none := by
  unfold evalPtrOffsetFromDistanceProto
  cases hZ : Nat.beq elemSize 0
  · have hNeg : ¬ (0 ≤ (Int.ofNat ptrOff - Int.ofNat originOff)) := by
      change ¬ (0 ≤ ((ptrOff : Int) - (originOff : Int)))
      omega
    have hDec : decide (0 ≤ (Int.ofNat ptrOff - Int.ofNat originOff) ∧
        (Int.ofNat ptrOff - Int.ofNat originOff) ≤ Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)) = false :=
      decide_eq_false (fun h => hNeg h.1)
    simp only [hDec]
  · rfl

theorem evalPtrOffsetFromDistanceProto_isizeMin_ub
    (elemSize ptrBytes : Nat) (hPtrPos : 0 < ptrBytes) (unsigned : Bool) :
    evalPtrOffsetFromDistanceProto 0 (signedHalfModulus ptrBytes) elemSize ptrBytes unsigned = .none := by
  unfold evalPtrOffsetFromDistanceProto
  cases hZ : Nat.beq elemSize 0
  · have hHalfPos : 0 < signedHalfModulus ptrBytes := by
      unfold signedHalfModulus
      have hModPos : 2 ≤ scalarModulus ptrBytes := by
        cases ptrBytes with
        | zero => omega
        | succ k =>
          have h1 : 1 ≤ scalarModulus k := by
            induction k with
            | zero => decide
            | succ j ih =>
              change 1 ≤ 256 * scalarModulus j
              omega
          change 2 ≤ 256 * scalarModulus k
          omega
      change 0 < scalarModulus ptrBytes / 2
      omega
    cases unsigned
    · have hNotIn : ¬ (-(Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)) ≤
          (Int.ofNat 0 - Int.ofNat (signedHalfModulus ptrBytes))) := by
        change ¬ (-(((signedHalfModulus ptrBytes - 1 : Nat) : Int)) ≤ ((0 : Int) - (signedHalfModulus ptrBytes : Int)))
        omega
      have hDec : decide (-(Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)) ≤
          (Int.ofNat 0 - Int.ofNat (signedHalfModulus ptrBytes)) ∧
          (Int.ofNat 0 - Int.ofNat (signedHalfModulus ptrBytes)) ≤
          Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)) = false :=
        decide_eq_false (fun h => hNotIn h.1)
      simp only [hDec]
    · have hNotIn : ¬ (0 ≤ (Int.ofNat 0 - Int.ofNat (signedHalfModulus ptrBytes))) := by
        change ¬ (0 ≤ ((0 : Int) - (signedHalfModulus ptrBytes : Int)))
        omega
      have hDec : decide (0 ≤ (Int.ofNat 0 - Int.ofNat (signedHalfModulus ptrBytes)) ∧
          (Int.ofNat 0 - Int.ofNat (signedHalfModulus ptrBytes)) ≤
          Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)) = false :=
        decide_eq_false (fun h => hNotIn h.1)
      simp only [hDec]
  · rfl

/--
`LeanMiri` spec mirror of the distance computation and range checks of
`Miri.Interpreter.Intrinsics.pointerOffsetFrom`
(`lean-miri/vendor/Miri/Interpreter/Intrinsics.lean:239-249`) on two `usize`
offsets `aOff`, `bOff` below `modulus = 2^(8 * ptrBytes)`:

- line 239: `SubWithOverflow` on `usize` yields the wrapped difference
  `value = (aOff - bOff) mod modulus` and `overflow = (aOff < bOff)`;
- lines 242-244: `toTargetIsize` reinterprets `value` as a two's-complement
  `isize` `distance`;
- lines 245-248: when `overflow`, the unsigned intrinsic is UB, and the signed
  intrinsic is UB if `distance >= 0` or `distance == isize::MIN`;
- line 249: otherwise (no overflow) a negative `distance` is UB.

Returns `some distance` when no check fails and `none` on UB.
-/
def miriPtrOffsetFromDistanceSpec (aOff bOff modulus : Nat) (unsigned : Bool) : Option Int :=
  let value : Nat := (aOff + modulus - bOff) % modulus
  let distance : Int :=
    if value < modulus / 2 then (value : Int) else (value : Int) - (modulus : Int)
  if aOff < bOff then
    if unsigned = true then none
    else if 0 ≤ distance ∨ distance = -((modulus / 2 : Nat) : Int) then none
    else some distance
  else if distance < 0 then none
  else some distance

/--
The range-checked byte distance of `evalPtrOffsetFromDistanceProto`:
`some (ptrOff - originOff)` when the mathematical difference lies in
`[-isize::MAX, isize::MAX]` (signed) or `[0, isize::MAX]` (unsigned), else
`none`.
-/
@[reducible]
def ptrOffsetFromCheckedDistanceProto (ptrOff originOff ptrBytes : Nat) (unsigned : Bool) : Option Int :=
  let distance : Int := Int.ofNat ptrOff - Int.ofNat originOff
  let isizeMax : Int := Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)
  let rangeOk : Bool :=
    match unsigned with
    | true => decide (0 ≤ distance ∧ distance ≤ isizeMax)
    | false => decide (-isizeMax ≤ distance ∧ distance ≤ isizeMax)
  match rangeOk with
  | false => .none
  | true => .some distance

/-- For a non-zero byte width, `scalarModulus n = 2 * signedHalfModulus n` with a positive half. -/
theorem scalarModulus_eq_two_mul_half (n : Nat) (hn : 0 < n) :
    scalarModulus n = 2 * signedHalfModulus n ∧ 0 < signedHalfModulus n := by
  cases n with
  | zero => omega
  | succ k =>
    have h1 : 1 ≤ scalarModulus k := by
      induction k with
      | zero => decide
      | succ j ih =>
        change 1 ≤ 256 * scalarModulus j
        omega
    unfold signedHalfModulus
    change 256 * scalarModulus k = 2 * ((256 * scalarModulus k) / 2) ∧ 0 < (256 * scalarModulus k) / 2
    omega

/--
Core of `miriPtrOffsetFromDistanceSpec_eq_checkedDistanceProto` over an even
modulus `2 * H`: the `SubWithOverflow` / `toTargetIsize` case analysis of
`Intrinsics.lean:239-249` accepts exactly the mathematical differences in
`[-(H - 1), H - 1]` (signed) or `[0, H - 1]` (unsigned) and returns that
difference.
-/
theorem miriPtrOffsetFromDistanceSpec_core (a b H : Nat) (u : Bool)
    (hH : 0 < H) (ha : a < 2 * H) (hb : b < 2 * H) :
    miriPtrOffsetFromDistanceSpec a b (2 * H) u =
      (match (match u with
          | true => decide (0 ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int))
          | false => decide (-((H - 1 : Nat) : Int) ≤ (a : Int) - (b : Int) ∧
              (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int))) with
        | false => none
        | true => some ((a : Int) - (b : Int))) := by
  have hHalf : 2 * H / 2 = H := by omega
  unfold miriPtrOffsetFromDistanceSpec
  simp only [hHalf]
  by_cases hLt : a < b
  · have hVal : (a + 2 * H - b) % (2 * H) = a + 2 * H - b := Nat.mod_eq_of_lt (by omega)
    have hCast : ((a + 2 * H - b : Nat) : Int) = (a : Int) - (b : Int) + 2 * (H : Int) := by omega
    rw [hVal, ite_eq_left hLt]
    cases u
    · by_cases hSmall : a + 2 * H - b < H
      · have hP : ¬ (-((H - 1 : Nat) : Int) ≤ (a : Int) - (b : Int) ∧
            (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
        rw [ite_eq_left hSmall, decide_eq_false hP]
        have hNonneg : (0 : Int) ≤ ((a + 2 * H - b : Nat) : Int) := Int.natCast_nonneg _
        simp [hNonneg]
      · by_cases hMin : b - a = H
        · have hP : ¬ (-((H - 1 : Nat) : Int) ≤ (a : Int) - (b : Int) ∧
              (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
          have hEq : ((a + 2 * H - b : Nat) : Int) - ((2 * H : Nat) : Int) = -((H : Nat) : Int) := by omega
          rw [ite_eq_right hSmall, decide_eq_false hP, hEq]
          simp
        · have hP : (-((H - 1 : Nat) : Int) ≤ (a : Int) - (b : Int) ∧
              (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
          have hEq : ((a + 2 * H - b : Nat) : Int) - ((2 * H : Nat) : Int) = (a : Int) - (b : Int) := by omega
          have hNeg : ¬ ((0 : Int) ≤ (a : Int) - (b : Int) ∨ (a : Int) - (b : Int) = -((H : Nat) : Int)) := by omega
          rw [ite_eq_right hSmall, decide_eq_true hP, hEq, ite_eq_right hNeg]
          simp
    · have hP : ¬ (0 ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
      rw [decide_eq_false hP]
      simp
  · have hGe : b ≤ a := Nat.le_of_not_lt hLt
    have hVal : (a + 2 * H - b) % (2 * H) = a - b := by
      have h1 : a + 2 * H - b = (a - b) + 2 * H := by omega
      rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    have hCast : ((a - b : Nat) : Int) = (a : Int) - (b : Int) := by omega
    rw [hVal, ite_eq_right hLt]
    by_cases hSmall : a - b < H
    · have hNotNeg : ¬ (((a - b : Nat) : Int) < 0) := by omega
      rw [ite_eq_left hSmall, ite_eq_right hNotNeg, hCast]
      cases u
      · have hP : (-((H - 1 : Nat) : Int) ≤ (a : Int) - (b : Int) ∧
            (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
        rw [decide_eq_true hP]
      · have hP : (0 ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
        rw [decide_eq_true hP]
    · have hIsNeg : ((a - b : Nat) : Int) - ((2 * H : Nat) : Int) < 0 := by omega
      rw [ite_eq_right hSmall, ite_eq_left hIsNeg]
      cases u
      · have hP : ¬ (-((H - 1 : Nat) : Int) ≤ (a : Int) - (b : Int) ∧
            (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
        rw [decide_eq_false hP]
      · have hP : ¬ (0 ≤ (a : Int) - (b : Int) ∧ (a : Int) - (b : Int) ≤ ((H - 1 : Nat) : Int)) := by omega
        rw [decide_eq_false hP]

/--
**`LeanMiri` Alignment Theorem (`ptr_offset_from` distance and range checks)**:
for every pointer width `ptrBytes > 0` and all offsets below
`2^(8 * ptrBytes)`, the wrapping `usize` subtraction, `isize` reinterpretation,
and overflow / underflow / `isize::MIN` checks of `Intrinsics.lean:239-249`
agree with the mathematical-integer range check of the prototype
(`ptrOffsetFromCheckedDistanceProto`), for both the signed and the unsigned
intrinsic.
-/
theorem miriPtrOffsetFromDistanceSpec_eq_checkedDistanceProto
    (aOff bOff ptrBytes : Nat) (unsigned : Bool)
    (hPtr : 0 < ptrBytes)
    (hA : aOff < scalarModulus ptrBytes) (hB : bOff < scalarModulus ptrBytes) :
    miriPtrOffsetFromDistanceSpec aOff bOff (scalarModulus ptrBytes) unsigned =
      ptrOffsetFromCheckedDistanceProto aOff bOff ptrBytes unsigned := by
  obtain ⟨hM, hH⟩ := scalarModulus_eq_two_mul_half ptrBytes hPtr
  rw [hM] at hA hB ⊢
  exact miriPtrOffsetFromDistanceSpec_core aOff bOff (signedHalfModulus ptrBytes) unsigned hH hA hB


/--
The exact-division tail of `evalPtrOffsetFromDistanceProto`: `none` unless
`elemSize` divides `|distance|`; otherwise the quotient encoded as a `usize`
(unsigned, or non-negative signed) or as a two's-complement `isize` (negative).
-/
@[reducible]
def ptrOffsetFromExactDivProto (distance : Int) (elemSize ptrBytes : Nat) (unsigned : Bool) :
    Option ScalarInt :=
  let mag : Nat := distance.natAbs
  match Nat.beq (Nat.mod mag elemSize) 0 with
  | false => .none
  | true =>
    let quotMag : Nat := Nat.div mag elemSize
    match unsigned with
    | true => .some ⟨quotMag, ptrBytes⟩
    | false =>
      match decide (0 ≤ distance) with
      | true => .some ⟨quotMag, ptrBytes⟩
      | false => .some ⟨Nat.sub (scalarModulus ptrBytes) quotMag, ptrBytes⟩

/--
`evalPtrOffsetFromDistanceProto` factors as the ZST check, then the range check
(`ptrOffsetFromCheckedDistanceProto`), then the exact division
(`ptrOffsetFromExactDivProto`).
-/
theorem evalPtrOffsetFromDistanceProto_eq_checked_then_exactDiv (a b sz n : Nat) (u : Bool) :
    evalPtrOffsetFromDistanceProto a b sz n u =
      (match Nat.beq sz 0 with
       | true => .none
       | false =>
         match ptrOffsetFromCheckedDistanceProto a b n u with
         | .none => .none
         | .some distance => ptrOffsetFromExactDivProto distance sz n u) := by
  unfold evalPtrOffsetFromDistanceProto ptrOffsetFromCheckedDistanceProto ptrOffsetFromExactDivProto
  cases Nat.beq sz 0
  · dsimp only
    cases u
    · dsimp only
      cases decide (-Int.ofNat (Nat.sub (signedHalfModulus n) 1) ≤ Int.ofNat a - Int.ofNat b ∧
          Int.ofNat a - Int.ofNat b ≤ Int.ofNat (Nat.sub (signedHalfModulus n) 1)) <;> rfl
    · dsimp only
      cases decide (0 ≤ Int.ofNat a - Int.ofNat b ∧
          Int.ofNat a - Int.ofNat b ≤ Int.ofNat (Nat.sub (signedHalfModulus n) 1)) <;> rfl
  · rfl

/--
`LeanMiri` spec mirror of the final exact division of
`Miri.Interpreter.Intrinsics.pointerOffsetFrom` (`Intrinsics.lean:263-273`,
`IntegerArithmeticIntrinsic.exactDiv`) at the result layout (`isize` or
`usize`, both `ptrBytes` wide): division by zero and a non-zero remainder are
UB (`none`); otherwise the truncated quotient `distance / elemSize` is written
as a `ptrBytes`-wide two's-complement scalar.
-/
def miriPtrOffsetFromExactDivSpec (distance : Int) (elemSize ptrBytes : Nat) : Option ScalarInt :=
  if elemSize = 0 then none
  else if distance.tmod (elemSize : Int) ≠ 0 then none
  else
    some ⟨((distance.tdiv (elemSize : Int)) % (scalarModulus ptrBytes : Int)).toNat, ptrBytes⟩

/--
**`LeanMiri` Alignment Theorem (`ptr_offset_from` exact division)**: on every
in-range distance (non-negative for the unsigned intrinsic) and non-zero
`elemSize`, the prototype's magnitude-based exact division agrees with the
truncated signed division and remainder of `Intrinsics.lean:263-273`.
-/
theorem ptrOffsetFromExactDivProto_eq_miriSpec
    (distance : Int) (elemSize ptrBytes : Nat) (unsigned : Bool)
    (hSz : elemSize ≠ 0)
    (hPtr : 0 < ptrBytes)
    (hLo : -((signedHalfModulus ptrBytes - 1 : Nat) : Int) ≤ distance)
    (hHi : distance ≤ ((signedHalfModulus ptrBytes - 1 : Nat) : Int))
    (hUnsigned : unsigned = true → 0 ≤ distance) :
    ptrOffsetFromExactDivProto distance elemSize ptrBytes unsigned =
      miriPtrOffsetFromExactDivSpec distance elemSize ptrBytes := by
  obtain ⟨hM, hH⟩ := scalarModulus_eq_two_mul_half ptrBytes hPtr
  unfold ptrOffsetFromExactDivProto miriPtrOffsetFromExactDivSpec
  rw [ite_eq_right hSz]
  dsimp only
  have hSzPos : 0 < elemSize := Nat.pos_of_ne_zero hSz
  have hModIff : distance.tmod (elemSize : Int) = 0 ↔ distance.natAbs % elemSize = 0 := by
    have h := Int.natAbs_tmod distance (elemSize : Int)
    rw [Int.natAbs_natCast] at h
    constructor
    · intro h0; rw [← h, h0]; rfl
    · intro h0; rw [h0] at h; exact Int.natAbs_eq_zero.mp h
  by_cases hRem : distance.natAbs % elemSize = 0
  · have hBeq : Nat.beq (Nat.mod distance.natAbs elemSize) 0 = true := Nat.beq_eq.mpr hRem
    have hT : ¬ (distance.tmod (elemSize : Int) ≠ 0) := fun h => h (hModIff.mpr hRem)
    rw [hBeq, ite_eq_right hT]
    dsimp only
    have hQLe : distance.natAbs / elemSize ≤ distance.natAbs := Nat.div_le_self _ _
    rcases Int.natAbs_eq distance with hd | hd
    · -- distance = ↑k ≥ 0
      have hNonneg : 0 ≤ distance := by omega
      have hQ : distance.tdiv (elemSize : Int) = ((distance.natAbs / elemSize : Nat) : Int) := by
        conv => lhs; rw [hd]
        exact (Int.ofNat_tdiv _ _).symm
      have hEmod : ((distance.natAbs / elemSize : Nat) : Int) % (scalarModulus ptrBytes : Int) =
          ((distance.natAbs / elemSize : Nat) : Int) :=
        Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
      rw [hQ, hEmod, Int.toNat_natCast]
      cases unsigned
      · rw [decide_eq_true hNonneg]; rfl
      · rfl
    · by_cases hZero : distance = 0
      · subst hZero
        cases unsigned <;> simp <;> exact Nat.zero_div elemSize
      · -- distance = -↑k < 0
        have hNeg : ¬ (0 ≤ distance) := by omega
        have hU : unsigned = false := by
          cases unsigned
          · rfl
          · exact absurd (hUnsigned rfl) hNeg
        subst hU
        have hQ : distance.tdiv (elemSize : Int) = -((distance.natAbs / elemSize : Nat) : Int) := by
          conv => lhs; rw [hd]
          rw [Int.neg_tdiv, ← Int.ofNat_tdiv]
        have hMagPos : 0 < distance.natAbs := by omega
        have hDvd : elemSize ∣ distance.natAbs := Nat.dvd_of_mod_eq_zero hRem
        have hQPos : 0 < distance.natAbs / elemSize :=
          Nat.div_pos (Nat.le_of_dvd hMagPos hDvd) hSzPos
        have hEmod : (-((distance.natAbs / elemSize : Nat) : Int)) % (scalarModulus ptrBytes : Int) =
            ((scalarModulus ptrBytes - distance.natAbs / elemSize : Nat) : Int) := by
          have h1 : (-((distance.natAbs / elemSize : Nat) : Int)) % (scalarModulus ptrBytes : Int) =
              (-((distance.natAbs / elemSize : Nat) : Int) + (scalarModulus ptrBytes : Int)) %
                (scalarModulus ptrBytes : Int) := by
            rw [Int.add_emod_right]
          rw [h1]
          have h2 : (-((distance.natAbs / elemSize : Nat) : Int) + (scalarModulus ptrBytes : Int)) =
              ((scalarModulus ptrBytes - distance.natAbs / elemSize : Nat) : Int) := by omega
          rw [h2]
          exact Int.emod_eq_of_lt (Int.natCast_nonneg _) (by omega)
        rw [hQ, hEmod, Int.toNat_natCast, decide_eq_false hNeg]
        rfl
  · have hBeq : Nat.beq (Nat.mod distance.natAbs elemSize) 0 = false := by
      cases hb : Nat.beq (Nat.mod distance.natAbs elemSize) 0
      · rfl
      · exact absurd (Nat.beq_eq.mp hb) hRem
    have hT : distance.tmod (elemSize : Int) ≠ 0 := fun h => hRem (hModIff.mp h)
    rw [hBeq, ite_eq_left hT]


/--
A distance accepted by `ptrOffsetFromCheckedDistanceProto` lies in
`[-isize::MAX, isize::MAX]`, and is non-negative for the unsigned intrinsic.
-/
theorem ptrOffsetFromCheckedDistanceProto_some_range (a b n : Nat) (u : Bool) (d : Int)
    (h : ptrOffsetFromCheckedDistanceProto a b n u = .some d) :
    -((signedHalfModulus n - 1 : Nat) : Int) ≤ d ∧
      d ≤ ((signedHalfModulus n - 1 : Nat) : Int) ∧ (u = true → 0 ≤ d) := by
  unfold ptrOffsetFromCheckedDistanceProto at h
  cases u
  · dsimp only at h
    by_cases hP : (-Int.ofNat (Nat.sub (signedHalfModulus n) 1) ≤ Int.ofNat a - Int.ofNat b ∧
        Int.ofNat a - Int.ofNat b ≤ Int.ofNat (Nat.sub (signedHalfModulus n) 1))
    · rw [decide_eq_true hP] at h
      cases h
      exact ⟨hP.1, hP.2, fun hU => absurd hU (by decide)⟩
    · rw [decide_eq_false hP] at h
      cases h
  · dsimp only at h
    by_cases hP : (0 ≤ Int.ofNat a - Int.ofNat b ∧
        Int.ofNat a - Int.ofNat b ≤ Int.ofNat (Nat.sub (signedHalfModulus n) 1))
    · rw [decide_eq_true hP] at h
      cases h
      refine ⟨?_, hP.2, fun _ => hP.1⟩
      have h0 := hP.1
      have hNonneg : (0 : Int) ≤ ((signedHalfModulus n - 1 : Nat) : Int) := Int.natCast_nonneg _
      omega
    · rw [decide_eq_false hP] at h
      cases h

/--
**`LeanMiri` Alignment Theorem (`ptr_offset_from` / `ptr_offset_from_unsigned`
arithmetic, `Intrinsics.lean:239-249, 263-273`)**: for every pointer width
`ptrBytes > 0`, all offsets below `2^(8 * ptrBytes)`, every pointee size
(including the ZST size `0`), and both intrinsics, the prototype's pure
distance kernel `evalPtrOffsetFromDistanceProto` returns exactly what the
`lean-miri` computation returns: `SubWithOverflow` on `usize`, `isize`
reinterpretation, the overflow / underflow / `isize::MIN` checks, then
`exactDiv` by the pointee size (division by zero and inexact division are UB).
-/
theorem evalPtrOffsetFromDistanceProto_eq_miriSpec
    (aOff bOff elemSize ptrBytes : Nat) (unsigned : Bool)
    (hPtr : 0 < ptrBytes)
    (hA : aOff < scalarModulus ptrBytes) (hB : bOff < scalarModulus ptrBytes) :
    evalPtrOffsetFromDistanceProto aOff bOff elemSize ptrBytes unsigned =
      (match miriPtrOffsetFromDistanceSpec aOff bOff (scalarModulus ptrBytes) unsigned with
       | .none => .none
       | .some distance => miriPtrOffsetFromExactDivSpec distance elemSize ptrBytes) := by
  rw [evalPtrOffsetFromDistanceProto_eq_checked_then_exactDiv,
    miriPtrOffsetFromDistanceSpec_eq_checkedDistanceProto aOff bOff ptrBytes unsigned hPtr hA hB]
  cases hZ : Nat.beq elemSize 0
  · have hSz : elemSize ≠ 0 := fun h0 => by rw [h0] at hZ; cases hZ
    dsimp only
    cases hC : ptrOffsetFromCheckedDistanceProto aOff bOff ptrBytes unsigned with
    | none => rfl
    | some distance =>
      obtain ⟨hLo, hHi, hU⟩ :=
        ptrOffsetFromCheckedDistanceProto_some_range aOff bOff ptrBytes unsigned distance hC
      exact ptrOffsetFromExactDivProto_eq_miriSpec distance elemSize ptrBytes unsigned hSz hPtr hLo hHi hU
  · have hSz : elemSize = 0 := Nat.beq_eq.mp hZ
    dsimp only
    cases hC : ptrOffsetFromCheckedDistanceProto aOff bOff ptrBytes unsigned with
    | none => rfl
    | some distance =>
      unfold miriPtrOffsetFromExactDivSpec
      dsimp only
      rw [ite_eq_left hSz]

/-- `abstractByteEqProto` is reflexive. -/
theorem abstractByteEqProto_refl (b : AbstractByte) : abstractByteEqProto b b = true := by
  cases b with
  | uninit => rfl
  | init v prov =>
    have h : Nat.beq v.toBitVec.toNat v.toBitVec.toNat = true := Nat.beq_refl _
    cases prov with
    | none =>
      change (match Nat.beq v.toBitVec.toNat v.toBitVec.toNat with
        | false => false
        | true => true) = true
      rw [h]
    | some p =>
      obtain ⟨aId, aTag⟩ := p
      change (match Nat.beq v.toBitVec.toNat v.toBitVec.toNat with
        | false => false
        | true => Bool.and (Nat.beq aId aId) (Nat.beq aTag aTag)) = true
      rw [h, Nat.beq_refl, Nat.beq_refl]
      rfl

/--
**Round-trip guard completeness on exact images**: every byte list refines
itself, so `commitRootAbstractBytesProto` never rejects a decoded value whose
exact re-encoding equals the bytes written.
-/
theorem abstractBytesRefineProto_refl :
    ∀ bs : List AbstractByte, abstractBytesRefineProto bs bs = true
  | [] => rfl
  | .uninit :: rest => by
    change abstractBytesRefineProto rest rest = true
    exact abstractBytesRefineProto_refl rest
  | .init v p :: rest => by
    change (match abstractByteEqProto (.init v p) (.init v p) with
      | true => abstractBytesRefineProto rest rest
      | false => false) = true
    rw [abstractByteEqProto_refl]
    exact abstractBytesRefineProto_refl rest

/--
**`ptr_offset_from` Same-Address Theorem (offset resolution)**: in EVERY machine
state, for EVERY tracked pointer `p` (live, dead, dangling, out of bounds, or
of unknown provenance), comparing `p` with itself resolves to a pair of equal
offsets, never to `.ub` or `.unsupported`. This is the "point to the same
address" clause of the pinned `offset_from` contract and the distance-`0`
`checkSignedAccess` no-op of `Intrinsics.lean:250-262`.
-/
theorem resolvePtrOffsetFromOffsetsProto_same_pointer
    (s : MachineState) (locals : List LocalSlot) (decls : List LocalDecl) (layouts : LayoutTable)
    (p : ProvenancePtr) :
    ∃ off, resolvePtrOffsetFromOffsetsProto s locals decls layouts (.prov p) (.prov p) =
      .ok (off, off) := by
  unfold resolvePtrOffsetFromOffsetsProto normalizePtrArgProto
  dsimp only
  cases isUnbackedZeroProvProto s.memory p
  · dsimp only
    rw [Nat.beq_refl, Nat.beq_refl]
    exact ⟨0, rfl⟩
  · dsimp only
    rw [Nat.beq_refl]
    exact ⟨_, rfl⟩

/--
**`ptr_offset_from` Same-Address Theorem (distance kernel)**: equal offsets with
a non-ZST pointee always yield element distance `0`, for both the signed and
the unsigned intrinsic and every pointer width.
-/
theorem evalPtrOffsetFromDistanceProto_same_offset (off elemSize ptrBytes : Nat) (unsigned : Bool)
    (hSz : elemSize ≠ 0) :
    evalPtrOffsetFromDistanceProto off off elemSize ptrBytes unsigned = .some ⟨0, ptrBytes⟩ := by
  have hZ : Nat.beq elemSize 0 = false := by
    cases hb : Nat.beq elemSize 0
    · rfl
    · exact absurd (Nat.beq_eq.mp hb) hSz
  have hNonneg : (0 : Int) ≤ Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1) := Int.natCast_nonneg _
  have hC : ptrOffsetFromCheckedDistanceProto off off ptrBytes unsigned = .some 0 := by
    unfold ptrOffsetFromCheckedDistanceProto
    dsimp only
    rw [Int.sub_self]
    cases unsigned
    · have hP : (-Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1) ≤ 0 ∧
          (0 : Int) ≤ Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)) := ⟨by omega, hNonneg⟩
      rw [decide_eq_true hP]
    · have hP : ((0 : Int) ≤ 0 ∧ (0 : Int) ≤ Int.ofNat (Nat.sub (signedHalfModulus ptrBytes) 1)) :=
        ⟨Int.le_refl 0, hNonneg⟩
      rw [decide_eq_true hP]
  rw [evalPtrOffsetFromDistanceProto_eq_checked_then_exactDiv, hZ]
  dsimp only
  rw [hC]
  dsimp only
  have hMod : Nat.beq (Nat.mod (Int.natAbs 0) elemSize) 0 = true := by
    change Nat.beq (0 % elemSize) 0 = true
    rw [Nat.zero_mod]
    rfl
  have hDiv : Nat.div (Int.natAbs 0) elemSize = 0 := Nat.zero_div elemSize
  unfold ptrOffsetFromExactDivProto
  dsimp only
  rw [hMod]
  dsimp only
  rw [hDiv]
  cases unsigned <;> rfl

/--
**`black_box` Preservation Theorem**:
On a direct non-deref local destination `_0` with no active protectors,
`evalBlackBoxProto` on any valid non-uninit value `v` (including scalars,
provenance pointers preserving `allocId`/`tag`, and compound aggregates) writes
`v` verbatim into `_0` and jumps to `targetBb` without mutating `s.memory`.
-/
theorem evalBlackBoxProto_valid_direct_dest
    (s : MachineState) (target : ResolvedCallTarget)
    (decls : List LocalDecl) (layouts : LayoutTable)
    (argOps : List Operand) (v : Value) (locals' locals'' : List LocalSlot)
    (dstLocal : Local) (targetBb : BasicBlockIdx)
    (hNoProt : s.memory.activeProtectors = .nil)
    (hNoBorrows : s.memory.borrows = .nil)
    (hValid : validateBlackBoxValueProto decls layouts s.memory
      (match target.typeArgs with
       | t :: _ => .some t
       | .nil =>
         match argOps with
         | op0 :: _ =>
           match operandTy decls layouts op0 with
           | .some ty => .some ty.kind
           | .none =>
             match placeTy decls layouts { local_ := dstLocal, projection := .nil } with
             | .some dTy => .some dTy.kind
             | .none => .none
         | .nil =>
           match placeTy decls layouts { local_ := dstLocal, projection := .nil } with
           | .some dTy => .some dTy.kind
           | .none => .none) v = true)
    (hWrite : writePlaceValue locals' .nil { local_ := dstLocal, projection := .nil } v
      (callStack := s.memory.callStack) = .ok locals'') :
    evalBlackBoxProto s target decls layouts argOps [v] locals'
      { local_ := dstLocal, projection := .nil } (.some targetBb) =
      MirStepNode.step {
        frame := { s.frame with blockIdx := targetBb, stmtIdx := 0, locals := locals'' }
        memory := s.memory } := by
  unfold evalBlackBoxProto
  dsimp only
  rw [hValid]
  unfold writeIntrinsicReturnProto writeIntrinsicReturn
  dsimp only
  rw [hNoProt, hNoBorrows, hWrite]
  unfold invalidateDirectDestWriteBorrows
  rw [hNoBorrows]

end Anneal.TcbCoreMemPtrIntrinsicsPrototype
