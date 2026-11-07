/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM1_4

/-!
# Pointer & Allocation Correspondence for `LM-3.1`

Connects Anneal's raw-pointer and local-allocation representation in
`Trusted.Rustc.V2026_06_01.MirSemantics` (`ProvenancePtr`, `Value.ptr`,
`BorrowEntry`) to `lean-miri`'s `Miri.Memory.Pointer AnnealProv` and stack
allocations.

* `AllocMapRel`: ties each address-taken Anneal local (through the borrow tag of
  a pointer to it) to its `lean-miri` stack allocation `allocId`, whose base
  address is `annealStackBaseAddr allocId = allocId.value <<< 32`.
* `PtrRel`: relates an Anneal `ProvenancePtr` whose tag names an `allocMap`
  entry to the `lean-miri` pointer at the same offset into that entry's
  allocation.
* `LocalRelLM3_1`, `FrameRelLM3_1`, `StateRelLM3_1`, `StepRelLM3_1`: `LocalRel`,
  `FrameRel`, `StateRel`, and `StepRel` extended with raw-pointer locals and
  with the borrow entries those pointers own. With an empty `allocMap`,
  `StateRelLM3_1` is exactly `StateRel` (`StateRel.toLM3_1`,
  `StateRelLM3_1.toStateRel`), and `StepRel.toLM3_1` lifts every `LM-1.x` step.
* Exact characterizations of `Miri.Memory.checkAndDerefPtr` and
  `Miri.Interpreter.ptrOffsetInbounds` on pointers into stack allocations.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. `AllocMapRel` and `PtrRel` Invariants -/

/-- Entry in the `(localIdx ↔ allocId)` correspondence table relating an Anneal
address-taken local `localIdx` (and its borrow tag `tag` in `s.memory.borrows`)
to its `lean-miri` stack allocation `allocId`. -/
structure AllocMapEntry where
  tag : Nat
  localIdx : Local
  allocId : Miri.Memory.AllocId
  perm : TreeBorrowPerm

namespace AllocMapEntry

/-- Convert an `AllocMapEntry` to the corresponding root `BorrowEntry` in
`s.memory.borrows` (whole local, no projection, no parent, unranged). -/
def toBorrowEntry (e : AllocMapEntry) : BorrowEntry :=
  { tag := e.tag
    targetLocal := e.localIdx
    targetProjection := .nil
    perm := e.perm }

/-- Update `e.perm` on a write to `targetLocal` (either directly when
`writerTag = none`, or through pointer tag `some wTag`), mirroring
`MirSemantics.updateBorrowPerm`. -/
def updateOnWrite (e : AllocMapEntry) (targetLocal : Local)
    (writerTag : Option Nat) : AllocMapEntry :=
  { e with perm := (updateBorrowPerm e.toBorrowEntry targetLocal writerTag).perm }

/-- Update `e.perm` on a deref read of `targetLocal` through pointer tag `rTag`,
freezing foreign `.active` borrows to `.frozen` while leaving self reads and
non-`.active` borrows unchanged, mirroring `updateBorrowPermOnReadAtProj`. -/
def updateOnRead (e : AllocMapEntry) (targetLocal : Local) (rTag : Nat) :
    AllocMapEntry :=
  match Nat.beq e.localIdx targetLocal with
  | false => e
  | true =>
    match Nat.beq rTag e.tag with
    | true => e
    | false =>
      match e.perm with
      | .active => { e with perm := .frozen }
      | _ => e

theorem toBorrowEntry_updateOnWrite (e : AllocMapEntry) (targetLocal : Local)
    (writerTag : Option Nat) :
    (e.updateOnWrite targetLocal writerTag).toBorrowEntry =
      updateBorrowPerm e.toBorrowEntry targetLocal writerTag := by
  unfold updateOnWrite toBorrowEntry updateBorrowPerm
  dsimp only
  cases Nat.beq e.localIdx targetLocal with
  | false => rfl
  | true =>
    dsimp only
    cases writerTag with
    | none => cases e.perm <;> rfl
    | some wTag =>
      dsimp only
      cases Nat.beq e.tag wTag with
      | false => rfl
      | true => cases e.perm <;> rfl

end AllocMapEntry

/-- Map `AllocMapEntry.updateOnWrite` across `allocMap`. -/
def updateAllocMapOnWrite (allocMap : List AllocMapEntry) (targetLocal : Local)
    (writerTag : Option Nat) : List AllocMapEntry :=
  allocMap.map (fun e => e.updateOnWrite targetLocal writerTag)

/-- Map `AllocMapEntry.updateOnRead` across `allocMap` when `allocMap` has two
or more entries (matching `MirSemantics.evalRvalue`, which runs
`freezeDerefReadBorrowsAt` on `b₁ :: b₂ :: _`). -/
def updateAllocMapOnDerefRead (allocMap : List AllocMapEntry)
    (targetLocal : Local) (rTag : Nat) : List AllocMapEntry :=
  match allocMap with
  | e₁ :: e₂ :: rest =>
    (e₁ :: e₂ :: rest).map (fun e => e.updateOnRead targetLocal rTag)
  | _ => allocMap

/-- Shape invariant for a `lean-miri` stack allocation backing a primitive
scalar local of size `sz`: mutable, exact byte size `sz`, empty provenance map,
and lazy whole-range initialization mask (`InitMask.new sz b` for `b : Bool`). -/
structure StackScalarAllocShape {P E : Type} (sz : Miri.ABI.Size)
    (alloc : Miri.Memory.Allocation P E) : Prop where
  byteSize_eq : alloc.byteSize = sz
  len_eq : alloc.len = sz.bytes.toNat
  mutability_eq : alloc.mutability = .Mut
  provenanceMap_eq : alloc.provenanceMap = Miri.Memory.ProvenanceMap.new
  initMask_lazy : ∃ b : Bool, alloc.initializationMask = Miri.Memory.InitMask.new sz b

/-- Lookup the `AllocMapEntry` for borrow tag `tag` in `allocMap`. -/
def lookupAllocMapByTag : List AllocMapEntry → Nat → Option AllocMapEntry
  | .nil, _ => none
  | e :: rest, t => if Nat.beq e.tag t then some e else lookupAllocMapByTag rest t

/-- Lookup the `AllocId` associated with `localIdx` in `allocMap`. -/
def lookupAllocMapByLocal : List AllocMapEntry → Local → Option Miri.Memory.AllocId
  | .nil, _ => none
  | e :: rest, loc => if Nat.beq e.localIdx loc then some e.allocId else lookupAllocMapByLocal rest loc

/-- Bijection and synchronization invariant between Anneal's borrow/local table
and `lean-miri`'s stack allocations in `m`:

1. **Tag uniqueness**: Every entry in `allocMap` has a distinct borrow `tag`.
2. **Local-to-AllocId functional consistency**: Any two entries in `allocMap`
   for the same `localIdx` name the same `allocId`.
3. **AllocId-to-Local injectivity**: Any two entries in `allocMap` naming the
   same `allocId` refer to the same `localIdx`.
4. **Declared primitive-scalar target**: Every `e ∈ allocMap` targets a declared
   local of primitive scalar type (`IsPrimScalarTy`).
5. **Valid base address (`id <<< 32`)**: Every `e ∈ allocMap` has
   `e.allocId.value.toNat < 2 ^ 32` and
   `m.machine.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId)`.
6. **Borrow-table synchronization**: For every `e ∈ allocMap`,
   `lookupBorrow s.memory.borrows e.tag = some e.toBorrowEntry` and
   `e.tag < s.memory.nextTag`.
7. **Live vs. Dead local & stack allocation synchronization**: For every
   `e ∈ allocMap` and root frame `topFrame` (`m.stack.frames = #[topFrame]`):
   * `e.allocId` appears at most once in `m.machine.memory.live`.
   * If `get? s.frame.locals e.localIdx = some slot` with `slot ≠ .dead`, then
     `topFrame.locals[e.localIdx]? = some ⟨.live (.indirect (stackAllocPlace e.allocId)), lay⟩`
     and `m.machine.memory.live.find? (·.1 == e.allocId) = some (e.allocId, localAlloc)`
     with `StackScalarAllocShape` on `localAlloc.allocation`.
   * If `get? s.frame.locals e.localIdx = some .dead`, then
     `m.machine.memory.live.find? (fun x => x.1 == e.allocId) = none`. -/
structure AllocMapRel
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Prop where
  /-- Distinct borrow tags across `allocMap`. -/
  tags_nodup : (allocMap.map AllocMapEntry.tag).Nodup
  /-- Functional consistency from `localIdx` to `allocId`. -/
  local_to_alloc_unique :
    ∀ e₁ ∈ allocMap, ∀ e₂ ∈ allocMap, e₁.localIdx = e₂.localIdx → e₁.allocId = e₂.allocId
  /-- Injectivity from `allocId` to `localIdx`. -/
  alloc_to_local_injective :
    ∀ e₁ ∈ allocMap, ∀ e₂ ∈ allocMap, e₁.allocId = e₂.allocId → e₁.localIdx = e₂.localIdx
  /-- Every mapped local is a declared primitive-scalar local in `body`. -/
  target_decl :
    ∀ e ∈ allocMap, ∃ decl, get? body.localDecls e.localIdx = some decl ∧ IsPrimScalarTy decl.ty
  /-- Every mapped `allocId` fits below `2^32` and `nextAllocId` and has its
  `id <<< 32` base address cached in `m.machine.addresses`. -/
  base_addr_valid :
    ∀ e ∈ allocMap,
      e.allocId.value.toNat < 2 ^ 32 ∧
      e.allocId.value.toNat < m.machine.memory.nextAllocId.toNat ∧
      m.machine.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId)
  /-- Every entry in `allocMap` resolves in `s.memory.borrows` to the same
  `targetLocal` and `perm`, with `tag < s.memory.nextTag`. -/
  borrow_sync :
    ∀ e ∈ allocMap,
      e.tag < s.memory.nextTag ∧
      lookupBorrow s.memory.borrows e.tag =
        some { tag := e.tag, targetLocal := e.localIdx, targetProjection := .nil, perm := e.perm }
  /-- Each mapped `allocId` has at most one entry in `m.machine.memory.live`. -/
  live_key_unique :
    ∀ e ∈ allocMap, ∀ la₁ la₂,
      (e.allocId, la₁) ∈ m.machine.memory.live.toList →
      (e.allocId, la₂) ∈ m.machine.memory.live.toList →
      la₁ = la₂
  /-- Live locals are backed by `stackAllocPlace e.allocId` in `topFrame` and by
  a `StackScalarAllocShape` entry in `m.machine.memory.live`; dead locals have
  `e.allocId` absent from `m.machine.memory.live`. -/
  local_alloc_sync :
    ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ e ∈ allocMap,
        (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead →
          (∃ lay, topFrame.locals[e.localIdx]? =
            some ⟨.live (.indirect (stackAllocPlace e.allocId)), lay⟩) ∧
          (∀ v, slot = .init v → ∃ sc, v = .scalar sc) ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl →
            ∃ localAlloc,
              m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
                some (e.allocId, localAlloc) ∧
              localAlloc.kind = .stack ∧
              localAlloc.allocation.align = (translateTy decl.ty body.layouts).layout.align.abi ∧
              StackScalarAllocShape (translateTy decl.ty body.layouts).layout.size
                localAlloc.allocation)) ∧
        (get? s.frame.locals e.localIdx = some .dead →
          m.machine.memory.live.find? (fun x => x.1 == e.allocId) = none)

namespace AllocMapRel

/-- The empty `AllocMap` trivially satisfies `AllocMapRel` in any state. -/
theorem nil (body : CapturedMir) (s : MachineState) (m : AnnealStepState) :
    AllocMapRel body s m [] where
  tags_nodup := by simp
  local_to_alloc_unique := by intro _ h; cases h
  alloc_to_local_injective := by intro _ h; cases h
  target_decl := by intro _ h; cases h
  base_addr_valid := by intro _ h; cases h
  borrow_sync := by intro _ h; cases h
  live_key_unique := by intro _ h; cases h
  local_alloc_sync := by intro _ _ _ h; cases h

end AllocMapRel

/-- Simulation relation between an Anneal `ProvenancePtr` (`allocId`,
`offsetBytes`) and a `lean-miri` `Miri.Memory.Pointer AnnealProv` (`offset`,
`provenance`).

Anneal records a raw pointer's borrow tag in `p.allocId` (`p.tag`), so the
tag must name an `allocMap` entry, and `mptr` must point into that entry's
`lean-miri` stack allocation: `mptr.provenance` is `.concrete allocId borTag`,
`allocId.value.toNat < 2^32`, `p.offsetBytes < 2^32`, and `mptr.offset` is
`Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat p.offsetBytes)`
(that is, `(allocId.value <<< 32) + p.offsetBytes`, with no 64-bit
wraparound). A tag outside `allocMap` relates to no `lean-miri` pointer: such a
tag has no borrow entry in Anneal (`StateRelLM3_1.borrows_tracked`), so
relating it to some allocation that `lean-miri` might still consider live
would let a dereference succeed in `lean-miri` that fails in Anneal. -/
inductive PtrRel
    (allocMap : List AllocMapEntry)
    (p : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv) : Prop where
  | mk
      (allocId : Miri.Memory.AllocId)
      (borTag : Miri.Memory.BorTag)
      (prov_eq : mptr.provenance = .concrete allocId borTag)
      (id_lt_2pow32 : allocId.value.toNat < 2 ^ 32)
      (offset_lt_2pow32 : p.offsetBytes < 2 ^ 32)
      (addr_eq :
        mptr.offset =
          Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat p.offsetBytes))
      (target_rel : ∃ e ∈ allocMap, e.tag = p.tag ∧ e.allocId = allocId) :
      PtrRel allocMap p mptr

namespace PtrRel

/-- `PtrRel` survives extending `allocMap` with another entry. -/
theorem mono_cons {allocMap : List AllocMapEntry} {p : ProvenancePtr}
    {mptr : Miri.Memory.Pointer AnnealProv} (e : AllocMapEntry)
    (h : PtrRel allocMap p mptr) : PtrRel (e :: allocMap) p mptr := by
  cases h with
  | mk allocId borTag hprov hid hoff haddr htarget =>
    obtain ⟨e', he', htag, halloc⟩ := htarget
    exact .mk allocId borTag hprov hid hoff haddr
      ⟨e', List.mem_cons_of_mem e he', htag, halloc⟩

/-- No `lean-miri` pointer is related to an Anneal pointer when `allocMap` is
empty. -/
theorem not_nil {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv} :
    ¬ PtrRel [] p mptr := by
  intro h
  cases h with
  | mk _ _ _ _ _ _ htarget =>
    obtain ⟨_, he, _⟩ := htarget
    cases he

/-- A pointer freshly created at offset `0` from `stackAllocPlace id` satisfies
`PtrRel` with `{ allocId := e.tag, offsetBytes := 0 }` whenever `e ∈ allocMap`. -/
theorem of_stackAllocPlace
    {allocMap : List AllocMapEntry} {e : AllocMapEntry}
    (he : e ∈ allocMap)
    (hlt : e.allocId.value.toNat < 2 ^ 32) :
    PtrRel allocMap
      { allocId := e.tag, offsetBytes := 0 }
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ :=
  .mk e.allocId Miri.Memory.BorTag.one rfl hlt (by show 0 < 2 ^ 32; decide)
    (by simp [UInt64.add_zero])
    ⟨e, he, rfl, rfl⟩

/-- No 64-bit addition overflow occurs in `annealStackBaseAddr allocId + offsetBytes`
when `allocId.value.toNat < 2^32` and `offsetBytes < 2^32`. -/
theorem base_add_offset_lt_u64
    (allocId : Miri.Memory.AllocId) (offsetBytes : Nat)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32) :
    (annealStackBaseAddr allocId).toNat + offsetBytes < 2 ^ 64 := by
  have hbase : (annealStackBaseAddr allocId).toNat = allocId.value.toNat * 2 ^ 32 := by
    unfold annealStackBaseAddr
    rw [UInt64.toNat_shiftLeft]
    have hlt64 : allocId.value.toNat * 2 ^ 32 < 2 ^ 64 := by omega
    simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt64]
  omega

/-- Under `allocId.value.toNat < 2^32`, `offsetBytes < 2^32`, and
`mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId)`,
`annealResolvePtr` resolves a pointer at `annealStackBaseAddr allocId + offsetBytes`
to `allocId` and relative offset `Size.ofBytes (UInt64.ofNat offsetBytes)`. -/
theorem resolvePtr_concrete_eq
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag) (offsetBytes : Nat)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (signedSize : Int) :
    annealResolvePtr mach
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      signedSize =
      .ok ⟨allocId, Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes), borTag⟩ := by
  have hno_ovf := base_add_offset_lt_u64 allocId offsetBytes hid hoff
  have hoff_lt : offsetBytes < 2 ^ 64 := by omega
  have hu64 : (UInt64.ofNat offsetBytes).toNat = offsetBytes :=
    UInt64.toNat_ofNat_of_lt hoff_lt
  have hadd_toNat :
      (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes).toNat =
        (annealStackBaseAddr allocId).toNat + offsetBytes := by
    rw [UInt64.toNat_add, hu64, Nat.mod_eq_of_lt hno_ovf]
  have hle_raw :
      annealStackBaseAddr allocId ≤
        annealStackBaseAddr allocId + UInt64.ofNat offsetBytes := by
    rw [UInt64.le_iff_toNat_le, hadd_toNat]
    omega
  have hle : annealStackBaseAddr allocId ≤
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes)).bytes :=
    hle_raw
  have hsub :
      (Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes)).bytes -
        annealStackBaseAddr allocId = UInt64.ofNat offsetBytes := by
    apply UInt64.toNat_inj.mp
    change ((annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) -
      annealStackBaseAddr allocId).toNat = (UInt64.ofNat offsetBytes).toNat
    rw [UInt64.toNat_sub_of_le _ _ hle_raw, hadd_toNat, hu64]
    omega
  unfold annealResolvePtr
  simp [hbase, hle, hsub]

/-- `PtrRel` survives any transformation of `allocMap` that preserves `.tag`
and `.allocId` on every entry. -/
theorem map_preserve {allocMap : List AllocMapEntry}
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (halloc : ∀ e, (f e).allocId = e.allocId)
    {p : ProvenancePtr} {mptr : Miri.Memory.Pointer AnnealProv}
    (h : PtrRel allocMap p mptr) : PtrRel (allocMap.map f) p mptr := by
  cases h with
  | mk allocId borTag hprov hid hoff haddr htarget =>
    obtain ⟨e, he, het, hea⟩ := htarget
    refine .mk allocId borTag hprov hid hoff haddr
      ⟨f e, List.mem_map_of_mem he, ?_, ?_⟩
    · rw [htag, het]
    · rw [halloc, hea]

end PtrRel

/-! ## 3. Pointer-Aware Local, Frame, and State Relations -/

/-- `LocalRel` extended with raw-pointer locals.

`LM-1.x` relates every immediate local through `ImmediateRel`, which has no
pointer case, so no state in which a local holds a raw pointer satisfies
`StateRel`. `LocalRelLM3_1` adds exactly that case: an initialized local of
raw-pointer type holds `.ptr p 8` in Anneal and the immediate scalar
`Scalar.fromPointer annealTargetDataLayout mptr` in `lean-miri`, with
`PtrRel allocMap p mptr`. Every other local is related by `LocalRel` itself, so
the `LM-1.x` facts about it carry over unchanged. -/
inductive LocalRelLM3_1
    (mach : AnnealMachine) (allocMap : List AllocMapEntry)
    (decl : LocalDecl) (layouts : LayoutTable) :
    LocalSlot → Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout → Prop where
  /-- A local related by `LocalRel`. -/
  | base {slot : LocalSlot}
      {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout} :
      LocalRel mach decl layouts slot mls →
      LocalRelLM3_1 mach allocMap decl layouts slot mls
  /-- An immediate raw-pointer local. -/
  | rawPtr (p : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv)
      (cachedLayout : Option Miri.Interpreter.LocalLayout)
      (mutability : Mutability) (pointeeKind : RigidTy) :
      (∀ l ∈ cachedLayout, l = translateTy decl.ty layouts) →
      decl.ty.kind = .rawPtr mutability pointeeKind →
      PtrRel allocMap p mptr →
      LocalRelLM3_1 mach allocMap decl layouts (.init (.ptr p 8))
        ⟨.live (.immediate
            (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          cachedLayout⟩

/-- `FrameRel` with locals related by `LocalRelLM3_1`. -/
structure FrameRelLM3_1
    (body : CapturedMir) (mach : AnnealMachine) (allocMap : List AllocMapEntry)
    (af : StackFrame)
    (mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) : Prop where
  /-- `mf.body` is the translation of `body`. -/
  body_eq : mf.body = translateBody body
  /-- `mf.location` is `.mir ⟨af.blockIdx, af.stmtIdx⟩`. -/
  location_eq : mf.location = .mir ⟨af.blockIdx, af.stmtIdx⟩
  /-- `af.locals` has one slot per declared local. -/
  af_locals_len : af.locals.length = body.localDecls.length
  /-- `mf.locals` has one state per declared local. -/
  mf_locals_size : mf.locals.size = body.localDecls.length
  /-- Pointwise correspondence of every local via `LocalRelLM3_1`. -/
  locals_rel :
    ∀ (i : Nat) (decl : LocalDecl) (slot : LocalSlot)
      (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout),
      get? body.localDecls i = some decl →
      get? af.locals i = some slot →
      mf.locals[i]? = some mls →
      LocalRelLM3_1 mach allocMap decl body.layouts slot mls

/-- Simulation relation between an Anneal `MachineState` and a single-frame
`AnnealStepState` in which locals may hold raw pointers to address-taken locals.

`StateRel` requires `s.memory.borrows = .nil`, but Anneal's `Rvalue.rawPtr`
pushes a borrow entry, so no state reached by taking an address satisfies
`StateRel`. `StateRelLM3_1` keeps every other `StateRel` field and replaces
`borrows_nil` by:

* `borrows_eq`: `s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry`
  (every borrow entry is the root borrow of the corresponding `allocMap` entry:
  whole local, no projection, default range and parent), and
* `alloc_rel`: `AllocMapRel`, which ties each entry's tag, local, permission,
  allocation, and base address together across the two machines.

With `allocMap = []` both fields force `borrows = .nil` and every pointer
local is impossible, so `StateRelLM3_1 body s m []` is equivalent to
`StateRel body s m` (`StateRel.toLM3_1` and `StateRelLM3_1.toStateRel`). -/
inductive StateRelLM3_1
    (body : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Prop where
  | mk
      (topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (frames_eq : m.stack.frames = #[topFrame])
      (returnContinuation_eq : topFrame.returnContinuation = .stop false)
      (returnPlace_eq :
        ∃ retLay,
          topFrame.returnPlace =
            .frameLocal 0 0 none retLay topFrame.localsIdentity)
      (frame_rel : FrameRelLM3_1 body m.machine allocMap s.frame topFrame)
      (activeCallee_none : s.memory.activeCallee = none)
      (callStack_nil : s.memory.callStack = .nil)
      (activeProtectors_nil : s.memory.activeProtectors = .nil)
      (callerLocals_nil : s.memory.callerLocals = .nil)
      (borrows_eq : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry)
      (alloc_rel : AllocMapRel body s m allocMap)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM3_1 body s m allocMap

namespace StateRelLM3_1

/-- Every borrow entry in `s.memory.borrows` comes from an `allocMap` entry. -/
theorem borrows_tracked {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} (h : StateRelLM3_1 body s m allocMap) :
    ∀ b ∈ s.memory.borrows, ∃ e ∈ allocMap, b = e.toBorrowEntry := by
  rcases h with ⟨_, _, _, _, _, _, _, _, _, hbor, _, _⟩
  intro b hb
  rw [hbor] at hb
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hb
  exact ⟨e, he, rfl⟩

end StateRelLM3_1

/-- Outcome correspondence for one step between `StateRelLM3_1`-related
states, mirroring `StepRel`: both machines take a normal step to states related
under `allocMap`, both return from the root frame with related return values,
or both report undefined behavior. -/
inductive StepRelLM3_1 (body : CapturedMir) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) :
    MirStepNode → Miri.Interpreter.StepResult AnnealStepState Bool → Prop where
  /-- Normal intra-frame step to `StateRelLM3_1`-related states. -/
  | step (s' : MachineState) (m' : AnnealStepState) :
      StateRelLM3_1 body s' m' allocMap →
      StepRelLM3_1 body m allocMap (MirStepNode.step s') (m', .ok true)
  /-- Normal root-frame return, as in `StepRel.retRoot`. -/
  | retRoot (decl0 : LocalDecl) (retVal : Value)
      (imm0 : Miri.Interpreter.Immediate AnnealProv)
      (mem' : Memory) (m' : AnnealStepState) :
      get? body.localDecls 0 = some decl0 →
      annealControlHooks.returnOperand () m = (m, .ok (.immediate imm0)) →
      ImmediateRel decl0.ty body.layouts retVal imm0 →
      m' = { m with stack := ⟨#[]⟩ } →
      StepRelLM3_1 body m allocMap (MirStepNode.retNormal retVal mem') (m', .ok true)
  /-- Both machines report undefined behavior. -/
  | ub (m' : AnnealStepState) (msg : String) :
      StepRelLM3_1 body m allocMap (MirStepNode.fail .ub)
        (m', .error (.undefinedBehavior msg))

/-- Every `FrameRel` is a `FrameRelLM3_1` for any `allocMap`. -/
theorem FrameRel.toLM3_1 {body : CapturedMir} {mach : AnnealMachine}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRel body mach af mf) (allocMap : List AllocMapEntry) :
    FrameRelLM3_1 body mach allocMap af mf where
  body_eq := h.body_eq
  location_eq := h.location_eq
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls :=
    .base (h.locals_rel i decl slot mls hdecl hslot hmls)

/-- With an empty `allocMap`, `LocalRelLM3_1` is `LocalRel`. -/
theorem LocalRelLM3_1.toLocalRel_nil {mach : AnnealMachine} {decl : LocalDecl}
    {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_1 mach [] decl layouts slot mls) :
    LocalRel mach decl layouts slot mls := by
  cases h with
  | base h => exact h
  | rawPtr _ _ _ _ _ _ _ hptr => exact absurd hptr PtrRel.not_nil

/-- Cached layout in a `LocalRelLM3_1`-related `LocalState` always agrees with
`translateTy decl.ty layouts`. -/
theorem LocalRelLM3_1.layout_eq {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls) :
    ∀ l, mls.layout = some l → l = translateTy decl.ty layouts := by
  cases h with
  | base hb => exact hb.layout_eq
  | rawPtr _ _ _ _ _ hc _ _ => exact hc

/-- Cached layout membership version of `LocalRelLM3_1.layout_eq`. -/
theorem LocalRelLM3_1.cachedLayout_eq {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls) :
    ∀ l ∈ mls.layout, l = translateTy decl.ty layouts := by
  cases h with
  | base hb => exact hb.cachedLayout_eq
  | rawPtr _ _ _ _ _ hc _ _ => exact hc

/-- `LocalRelLM3_1` survives extending `allocMap` with another entry. -/
theorem LocalRelLM3_1.mono_cons {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (e : AllocMapEntry) {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls) :
    LocalRelLM3_1 mach (e :: allocMap) decl layouts slot mls := by
  cases h with
  | base hb => exact .base hb
  | rawPtr p mptr cl mutability pointeeKind hc hty hptr =>
    exact .rawPtr p mptr cl mutability pointeeKind hc hty (hptr.mono_cons e)

/-- `LocalRelLM3_1` survives any `allocMap` map that preserves `.tag` and
`.allocId`. -/
theorem LocalRelLM3_1.map_preserve {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (halloc : ∀ e, (f e).allocId = e.allocId)
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls) :
    LocalRelLM3_1 mach (allocMap.map f) decl layouts slot mls := by
  cases h with
  | base hb => exact .base hb
  | rawPtr p mptr cl mutability pointeeKind hc hty hptr =>
    exact .rawPtr p mptr cl mutability pointeeKind hc hty (hptr.map_preserve f htag halloc)

/-- A local related by `LocalRelLM3_1` owns, if anything, a live allocation. -/
theorem LocalRelLM3_1.allocLive {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls) :
    LocalAllocLive mach.memory mls.value := by
  cases h with
  | base hb => exact hb.allocLive
  | rawPtr _ _ _ _ _ _ _ _ =>
    intro mp hv
    cases hv

/-- Deallocating the allocation of one local keeps the `LocalRelLM3_1` of every
local that owns a different allocation. -/
theorem LocalRelLM3_1.of_dealloc {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {v : Miri.Interpreter.LocalValue AnnealProv}
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls)
    (hdisj : ∀ mp mp', v = .live (.indirect mp) → mls.value = .live (.indirect mp') →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠
        mp'.ptr.provenance.bind Miri.Memory.Provenance.getAllocId) :
    LocalRelLM3_1 { mach with memory := deallocLocalMemory mach.memory v }
      allocMap decl layouts slot mls := by
  cases h with
  | base hb => exact .base (hb.of_dealloc hdisj)
  | rawPtr p mptr cl mutability pointeeKind hc hty hptr =>
    exact .rawPtr p mptr cl mutability pointeeKind hc hty hptr

/-- Look up a declared local in `FrameRelLM3_1`-related frames. -/
theorem FrameRelLM3_1.lookup_local
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_1 body mach allocMap af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl) :
    ∃ (slot : LocalSlot) (mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout)
      (_ : idx < af.locals.length) (hlt_mf : idx < mf.locals.size),
      get? af.locals idx = some slot ∧
      mf.locals[idx]? = some mls ∧
      mf.locals[idx]'hlt_mf = mls ∧
      LocalRelLM3_1 mach allocMap decl body.layouts slot mls := by
  have hlt_body : idx < body.localDecls.length := by
    rw [get?_eq_getElem?] at hdecl
    exact (List.getElem?_eq_some_iff.mp hdecl).1
  have hlt_af : idx < af.locals.length := by
    rw [hfr.af_locals_len]; exact hlt_body
  have hlt_mf : idx < mf.locals.size := by
    rw [hfr.mf_locals_size]; exact hlt_body
  have hslot : get? af.locals idx = some (af.locals[idx]'hlt_af) := by
    rw [get?_eq_getElem?, List.getElem?_eq_getElem hlt_af]
  have hmls : mf.locals[idx]? = some (mf.locals[idx]'hlt_mf) :=
    Array.getElem?_eq_getElem hlt_mf
  exact ⟨af.locals[idx]'hlt_af, mf.locals[idx]'hlt_mf, hlt_af, hlt_mf, hslot, hmls, rfl,
    hfr.locals_rel idx decl _ _ hdecl hslot hmls⟩

/-- Memoizing a local's layout preserves `FrameRelLM3_1`. -/
theorem FrameRelLM3_1.cache_local_layout
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_1 body mach allocMap af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < mf.locals.size) :
    FrameRelLM3_1 body mach allocMap af
      (cacheFrameLocalLayout mf idx hlt (translateTy decl.ty body.layouts)) where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := by rw [cacheFrameLocalLayout_size, hfr.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    dsimp only [cacheFrameLocalLayout] at hmls_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, Option.some.injEq] at hmls_i
      have hdecl_eq : decl = decl_i := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i
      subst hdecl_eq hmls_i
      generalize hls0 : (mf.locals[idx]'hlt) = mls0
      have hmls0 : mf.locals[idx]? = some mls0 := by
        rw [← hls0]; exact Array.getElem?_eq_getElem hlt
      have hrel0 := hfr.locals_rel idx decl slot_i mls0 hdecl hslot_i hmls0
      cases hrel0 with
      | base hb =>
        cases hb with
        | dead _ _ =>
          exact .base (.dead _ (fun _ hl => (Option.some.inj hl).symm))
        | immediate _ imm _ _ hv =>
          exact .base (.immediate slot_i imm _ (fun _ hl => (Option.some.inj hl).symm) hv)
        | indirect _ mp _ _ hne hmp =>
          exact .base (.indirect slot_i mp _ (fun _ hl => (Option.some.inj hl).symm) hne hmp)
      | rawPtr p mptr _ mutability pointeeKind _ hty hptr =>
        exact .rawPtr p mptr _ mutability pointeeKind
          (fun _ hl => (Option.some.inj hl).symm) hty hptr
    · simp only [h_eq, ↓reduceIte] at hmls_i
      exact hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

/-- `FrameRelLM3_1` survives any `allocMap` map that preserves `.tag` and
`.allocId`. -/
theorem FrameRelLM3_1.map_preserve
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (halloc : ∀ e, (f e).allocId = e.allocId)
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_1 body mach allocMap af mf) :
    FrameRelLM3_1 body mach (allocMap.map f) af mf where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := hfr.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls :=
    (hfr.locals_rel i decl slot mls hdecl hslot hmls).map_preserve f htag halloc

/-- `FrameRelLM3_1` survives extending `allocMap` with another entry. -/
theorem FrameRelLM3_1.mono_cons
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    (e : AllocMapEntry)
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_1 body mach allocMap af mf) :
    FrameRelLM3_1 body mach (e :: allocMap) af mf where
  body_eq := hfr.body_eq
  location_eq := hfr.location_eq
  af_locals_len := hfr.af_locals_len
  mf_locals_size := hfr.mf_locals_size
  locals_rel i decl slot mls hdecl hslot hmls :=
    (hfr.locals_rel i decl slot mls hdecl hslot hmls).mono_cons e

/-- `StateRelLM3_1` survives memoizing a local's declared layout in the root
frame, as `annealEvalPlace` and `annealEvalOperand` do. -/
theorem StateRelLM3_1.cache_layout
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} {decl : LocalDecl} (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < tf.locals.size) :
    StateRelLM3_1 body s
      { m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt
          (translateTy decl.ty body.layouts)]⟩ }
      allocMap := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with htf
  subst htf
  refine .mk _ rfl hretCont hretPlace (hfr.cache_local_layout hdecl hlt) hcal hstack hprot
    hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro topFrame htop e he
    injection htop with h₁
    injection h₁ with h₂
    subst h₂
    obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
    refine ⟨fun slot hslot hne => ?_, hdead_e⟩
    obtain ⟨⟨lay, hlay⟩, hshape⟩ := hlive_e slot hslot hne
    refine ⟨?_, hshape⟩
    by_cases hk : idx = e.localIdx
    · subst hk
      refine ⟨some (translateTy decl.ty body.layouts), ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_self]
      have hget : tf.locals[e.localIdx]? = some (tf.locals[e.localIdx]'hlt) :=
        Array.getElem?_eq_getElem hlt
      rw [hget] at hlay
      injection hlay with hls
      rw [hls]
    · refine ⟨lay, ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ hk]
      exact hlay
  · apply MemoryAllocDisjoint.mono_layout hdisj
    intro k
    by_cases hk : k = idx
    · subst hk
      refine ⟨translateTy decl.ty body.layouts, ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt]
      rfl
    · refine ⟨(tf.locals[k]?).bind (fun x => x.layout), ?_⟩
      dsimp only [cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]
      cases tf.locals[k]? <;> rfl

/-- `StateRel` embeds into `StateRelLM3_1` with the empty `allocMap`. -/
theorem StateRel.toLM3_1 {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) : StateRelLM3_1 body s m [] := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller,
    hdisj⟩
  exact .mk tf hframes hretCont hretPlace (hfr.toLM3_1 []) hcal hstack hprot hcaller hbor
    (AllocMapRel.nil body s m) hdisj

/-- `StateRelLM3_1` with the empty `allocMap` is `StateRel`: the extension is
conservative. -/
theorem StateRelLM3_1.toStateRel {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} (h : StateRelLM3_1 body s m []) : StateRel body s m := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor,
    _, hdisj⟩
  exact .mk tf hframes hretCont hretPlace
    ⟨hfr.body_eq, hfr.location_eq, hfr.af_locals_len, hfr.mf_locals_size,
      fun i decl slot mls hdecl hslot hmls =>
        (hfr.locals_rel i decl slot mls hdecl hslot hmls).toLocalRel_nil⟩
    hcal hstack hbor hprot hcaller hdisj

/-- `StepRel` between pointer-free states is `StepRelLM3_1` with the empty
`allocMap`. -/
theorem StepRel.toLM3_1 {body : CapturedMir} {m : AnnealStepState}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (h : StepRel body m aRes mRes) : StepRelLM3_1 body m [] aRes mRes := by
  cases h with
  | step s' m' hrel => exact .step s' m' (StateRel.toLM3_1 hrel)
  | retRoot decl0 retVal imm0 mem' m' hdecl hret himm hm =>
    exact .retRoot decl0 retVal imm0 mem' m' hdecl hret himm hm
  | ub m' msg => exact .ub m' msg

/-- Replace one local of `FrameRelLM3_1`-related frames by `LocalRelLM3_1`-related
values. -/
theorem FrameRelLM3_1.update_local
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hrel : FrameRelLM3_1 body mach allocMap af mf)
    {idx : Nat} {decl : LocalDecl}
    (hdecl : get? body.localDecls idx = some decl)
    {hlt_mf : idx < mf.locals.size}
    (newSlot : LocalSlot) (newVal : Miri.Interpreter.LocalValue AnnealProv)
    (hnew : LocalRelLM3_1 mach allocMap decl body.layouts newSlot
      { mf.locals[idx]'hlt_mf with value := newVal }) :
    FrameRelLM3_1 body mach allocMap
      { af with locals := af.locals.set idx newSlot }
      { mf with locals := mf.locals.set idx { mf.locals[idx]'hlt_mf with value := newVal } hlt_mf } where
  body_eq := hrel.body_eq
  location_eq := hrel.location_eq
  af_locals_len := by rw [List.length_set, hrel.af_locals_len]
  mf_locals_size := by rw [Array.size_set, hrel.mf_locals_size]
  locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i := by
    have hlt_af : idx < af.locals.length := by
      rw [hrel.af_locals_len, ← hrel.mf_locals_size]; exact hlt_mf
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : idx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      exact hrel.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i

/-! ## 4. Exact `checkAndDerefPtr`, `checkPtrAlign`, and `ptrOffsetInbounds` Lemmas -/

/-- Public mirror of `Miri.Memory.fitsI64` (which is `private` in `Miri.Memory.Access`
but definitionally equal). -/
def fitsI64Pub (value : Int) : Bool :=
  -(2 ^ 63 : Int) ≤ value && value < (2 ^ 63 : Int)

theorem fitsI64Pub_eq_true_of_bounds {signedSize : Int}
    (hlo : -(2 ^ 63 : Int) ≤ signedSize) (hhi : signedSize < 2 ^ 63) :
    fitsI64Pub signedSize = true := by
  unfold fitsI64Pub
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
  exact ⟨hlo, hhi⟩

/-- Unfolding equation for `Miri.Memory.checkAndDerefPtr` on any non-zero
`signedSize` within `[-2^63, 2^63)`. -/
theorem checkAndDerefPtr_nonzero_eq {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic)
    (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int)
    (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (hlo : -(2 ^ 63 : Int) ≤ signedSize)
    (hhi : signedSize < 2 ^ 63)
    (hne0 : signedSize ≠ 0) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize msg resolve lookup =
      match resolve ptr signedSize with
      | .error addr => .error (.danglingIntegerPointer addr signedSize msg)
      | .ok resolved =>
        match lookup resolved.allocId with
        | .error (.deadAllocation id) => .error (.allocationLookup (.deadAllocation id))
        | .error (.unavailable id) => .error (.allocationLookup (.unavailable id))
        | .ok allocation =>
          if allocation.kind == .dead then
            .error (.allocationLookup (.deadAllocation resolved.allocId))
          else
            match Miri.Memory.checkedBounds target
                resolved.allocId allocation.size resolved.offset signedSize msg with
            | .ok () => .ok (some ⟨resolved, allocation⟩)
            | .error e => .error e := by
  have hfits : fitsI64Pub signedSize = true := fitsI64Pub_eq_true_of_bounds hlo hhi
  have hbeq0 : (signedSize == 0) = false := beq_eq_false_iff_ne.mpr hne0
  change (do
    if !fitsI64Pub signedSize then
      throw (Miri.Memory.AccessError.signedSizeOutsideI64 signedSize)
    if signedSize == 0 then return none
    let resolved ← match resolve ptr signedSize with
      | .ok resolved => pure resolved
      | .error address =>
        throw (Miri.Memory.AccessError.danglingIntegerPointer address signedSize msg)
    let allocation ← match lookup resolved.allocId with
      | .ok allocation => pure allocation
      | .error (.deadAllocation id) =>
        throw (Miri.Memory.AccessError.allocationLookup (.deadAllocation id))
      | .error (.unavailable id) =>
        throw (Miri.Memory.AccessError.allocationLookup (.unavailable id))
    if allocation.kind == Miri.Memory.AllocationKind.dead then
      throw (Miri.Memory.AccessError.allocationLookup (.deadAllocation resolved.allocId))
    Miri.Memory.checkedBounds target
      resolved.allocId allocation.size resolved.offset signedSize msg
    return (some ({ pointer := resolved, allocation := allocation } :
      Miri.Memory.CheckedPointerAccess ProvExtra))) = _
  simp only [hfits, hbeq0, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  cases hres : resolve ptr signedSize with
  | error addr => rfl
  | ok resolved =>
    simp only []
    cases hlook : lookup resolved.allocId with
    | error err =>
      cases err <;> rfl
    | ok allocation =>
      simp only []
      by_cases hkind : (allocation.kind == Miri.Memory.AllocationKind.dead) = true
      · simp only [hkind, ↓reduceIte]
      · have hkindf : (allocation.kind == Miri.Memory.AllocationKind.dead) = false :=
          Bool.eq_false_iff.mpr hkind
        cases hcb : Miri.Memory.checkedBounds target
            resolved.allocId allocation.size resolved.offset signedSize msg <;>
          simp only [hkindf, Bool.false_eq_true, ↓reduceIte]

theorem checkAndDerefPtr_nonzero_lookup_ok {Prov ProvExtra : Type}
    (target : Miri.Memory.PointerArithmetic)
    (ptr : Miri.Memory.Pointer (Option Prov))
    (signedSize : Int)
    (msg : Miri.Memory.CheckInAllocMsg)
    (resolve : Miri.Memory.PointerResolver Prov ProvExtra)
    (lookup : Miri.Memory.LiveAllocationLookup)
    (allocId : Miri.Memory.AllocId)
    (offset : Miri.ABI.Size)
    (extra : ProvExtra)
    (allocSize : Miri.ABI.Size)
    (allocAlign : Miri.ABI.Align)
    (allocMut : Miri.Memory.Mutability)
    (hlo : -(2 ^ 63 : Int) ≤ signedSize)
    (hhi : signedSize < 2 ^ 63)
    (hne0 : signedSize ≠ 0)
    (hres : resolve ptr signedSize = .ok ⟨allocId, offset, extra⟩)
    (hlook : lookup allocId = .ok ⟨allocSize, allocAlign, .liveData, allocMut⟩) :
    Miri.Memory.checkAndDerefPtr target ptr signedSize msg resolve lookup =
      match Miri.Memory.checkedBounds target
          allocId allocSize offset signedSize msg with
      | .ok () =>
        .ok (some ⟨⟨allocId, offset, extra⟩, ⟨allocSize, allocAlign, .liveData, allocMut⟩⟩)
      | .error e => .error e := by
  rw [checkAndDerefPtr_nonzero_eq target ptr signedSize msg resolve lookup hlo hhi hne0, hres]
  dsimp only
  rw [hlook]
  rfl

/-- Unfolding equation for `Miri.Memory.checkedBounds` on a non-negative access
size `(sizeBytes : Int)` with `sizeBytes < 2^63`. -/
theorem checkedBounds_ofNat_eq
    (target : Miri.Memory.PointerArithmetic)
    (id : Miri.Memory.AllocId)
    (allocationSize offset : Miri.ABI.Size)
    (sizeBytes : Nat)
    (msg : Miri.Memory.CheckInAllocMsg)
    (hfit : (sizeBytes : Int) < 2 ^ 63) :
    Miri.Memory.checkedBounds target id allocationSize offset (sizeBytes : Int) msg =
      if offset.bytes.toNat + sizeBytes ≤ allocationSize.bytes.toNat then
        .ok ()
      else
        match target.signExtendToTargetIsize offset.bytes with
        | .ok signedOffset =>
          .error (.pointerOutOfBounds id allocationSize
            signedOffset.toInt (sizeBytes : Int) msg)
        | .error e => .error (.pointerArithmetic e) := by
  have hlo : -(2 ^ 63 : Int) ≤ (sizeBytes : Int) :=
    Int.le_trans (by decide) (Int.natCast_nonneg sizeBytes)
  have hfits : fitsI64Pub (sizeBytes : Int) = true :=
    fitsI64Pub_eq_true_of_bounds hlo hfit
  change (do
    if !fitsI64Pub (sizeBytes : Int) then
      throw (Miri.Memory.AccessError.signedSizeOutsideI64 (sizeBytes : Int))
    let offsetNat := offset.bytes.toNat
    let allocationNat := allocationSize.bytes.toNat
    let inBounds := if (sizeBytes : Int) >= 0 then
        offsetNat + (sizeBytes : Int).toNat ≤ allocationNat
      else
        let amount := (-(sizeBytes : Int)).toNat
        amount ≤ offsetNat && offsetNat ≤ allocationNat
    if !inBounds then
      let signedOffset ←
        (target.signExtendToTargetIsize offset.bytes).mapError
          Miri.Memory.AccessError.pointerArithmetic
      throw (Miri.Memory.AccessError.pointerOutOfBounds id allocationSize
        signedOffset.toInt (sizeBytes : Int) msg)) = _
  rw [hfits]
  by_cases hib : offset.bytes.toNat + sizeBytes ≤ allocationSize.bytes.toNat
  · simp [hib, pure, Except.pure]
  · simp [hib]
    cases hse : target.signExtendToTargetIsize offset.bytes <;>
      simp [Except.mapError, bind, Except.bind, throw, throwThe, MonadExceptOf.throw]

theorem checkedBounds_ofNat_inbounds
    (target : Miri.Memory.PointerArithmetic)
    (id : Miri.Memory.AllocId)
    (allocationSize offset : Miri.ABI.Size)
    (sizeBytes : Nat)
    (msg : Miri.Memory.CheckInAllocMsg)
    (hfit : (sizeBytes : Int) < 2 ^ 63)
    (hinbounds : offset.bytes.toNat + sizeBytes ≤ allocationSize.bytes.toNat) :
    Miri.Memory.checkedBounds target id allocationSize offset (sizeBytes : Int) msg =
      .ok () := by
  rw [checkedBounds_ofNat_eq target id allocationSize offset sizeBytes msg hfit]
  simp only [hinbounds, ↓reduceIte]

theorem checkedBounds_ofNat_oob
    (target : Miri.Memory.PointerArithmetic)
    (id : Miri.Memory.AllocId)
    (allocationSize offset : Miri.ABI.Size)
    (sizeBytes : Nat)
    (msg : Miri.Memory.CheckInAllocMsg)
    (hfit : (sizeBytes : Int) < 2 ^ 63)
    (hoob : allocationSize.bytes.toNat < offset.bytes.toNat + sizeBytes) :
    Miri.Memory.checkedBounds target id allocationSize offset (sizeBytes : Int) msg =
      match target.signExtendToTargetIsize offset.bytes with
      | .ok signedOffset =>
        .error (.pointerOutOfBounds id allocationSize
          signedOffset.toInt (sizeBytes : Int) msg)
      | .error e => .error (.pointerArithmetic e) := by
  have hnot_ib : ¬ (offset.bytes.toNat + sizeBytes ≤ allocationSize.bytes.toNat) :=
    Nat.not_le.mpr hoob
  rw [checkedBounds_ofNat_eq target id allocationSize offset sizeBytes msg hfit]
  simp only [hnot_ib, ↓reduceIte]

theorem int64_toInt_ofInt_of_lt_u32
    (offsetBytes : Nat) (hoff : offsetBytes < 2 ^ 32) :
    (Int64.ofInt (offsetBytes : Int)).toInt = (offsetBytes : Int) := by
  rw [Int64.toInt_ofInt]
  have hlo64 : -(Int64.size / 2 : Int) ≤ (offsetBytes : Int) :=
    Int.le_trans (by decide) (Int.natCast_nonneg offsetBytes)
  have hhi64 : (offsetBytes : Int) < (Int64.size + 1) / 2 := by
    have hnat : offsetBytes < 9223372036854775808 :=
      Nat.lt_trans hoff (by decide)
    exact Int.ofNat_lt.mpr hnat
  exact Int.bmod_eq_of_le hlo64 hhi64

theorem annealPointerArithmetic_signExtendToTargetIsize_ofNat
    (offsetBytes : Nat) (hoff : offsetBytes < 2 ^ 32) :
    annealPointerArithmetic.signExtendToTargetIsize (UInt64.ofNat offsetBytes) =
      .ok (Int64.ofInt (offsetBytes : Int)) ∧
    (Int64.ofInt (offsetBytes : Int)).toInt = (offsetBytes : Int) := by
  have hoff_lt64 : offsetBytes < 2 ^ 64 :=
    Nat.lt_trans hoff (Nat.pow_lt_pow_right (by decide) (by decide))
  have hoff_u64 : (UInt64.ofNat offsetBytes).toNat = offsetBytes :=
    UInt64.toNat_ofNat_of_lt hoff_lt64
  refine ⟨?_, int64_toInt_ofInt_of_lt_u32 offsetBytes hoff⟩
  unfold Miri.Memory.PointerArithmetic.signExtendToTargetIsize annealPointerArithmetic
  have hse64 := size_signExtend_translateSizeBytes (sz := 8) (by simp [ValidScalarBytes])
    (BitVec.ofNat 128 (UInt64.ofNat offsetBytes).toNat)
  change (match (translateSizeBytes 8).signExtend
        (BitVec.ofNat 128 (UInt64.ofNat offsetBytes).toNat) with
      | .ok v =>
        if -(2 ^ 63 : Int) ≤ v ∧ v < (2 ^ 63 : Int) then .ok (Int64.ofInt v)
        else .error Miri.Memory.PointerError.signedConversionOverflow
      | .error e => .error (.sourceSizeError e)) =
    Except.ok (Int64.ofInt (offsetBytes : Int))
  rw [hse64, hoff_u64]
  dsimp only
  have hlt64 : offsetBytes < 2 ^ (8 * 8) :=
    Nat.lt_trans hoff (Nat.pow_lt_pow_right (by decide) (by decide))
  have hlt128 : offsetBytes < 2 ^ 128 :=
    Nat.lt_trans hoff (Nat.pow_lt_pow_right (by decide) (by decide))
  have hbv : (BitVec.ofNat 128 offsetBytes).toNat % 2 ^ (8 * 8) = offsetBytes := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128, Nat.mod_eq_of_lt hlt64]
  rw [hbv]
  have hdec : decodeBitsInt true 8 offsetBytes = (offsetBytes : Int) := by
    unfold decodeBitsInt
    have hlt63 : offsetBytes < 2 ^ (8 * 8 - 1) :=
      Nat.lt_trans hoff (Nat.pow_lt_pow_right (by decide) (by decide))
    simp only [hlt63, ↓reduceIte]
  rw [hdec]
  have hbounds : -(2 ^ 63 : Int) ≤ (offsetBytes : Int) ∧ (offsetBytes : Int) < (2 ^ 63 : Int) := by
    refine ⟨Int.le_trans (by decide) (Int.natCast_nonneg offsetBytes), ?_⟩
    have h63 : offsetBytes < 9223372036854775808 :=
      Nat.lt_trans hoff (by decide)
    exact Int.ofNat_lt.mpr h63
  simp only [hbounds, and_self, ↓reduceIte]

/-- A null or provenance-less integer pointer (`ptr.provenance = none`) fails
`Miri.Memory.checkAndDerefPtr` with `AccessError.danglingIntegerPointer` for
every non-zero access size `0 < signedSize < 2^63`. -/
theorem checkAndDerefPtr_withoutProvenance_err
    (mach : AnnealMachine) (addr : UInt64) (signedSize : Int)
    (msg : Miri.Memory.CheckInAllocMsg)
    (hpos : 0 < signedSize) (hfit : signedSize < 2 ^ 63) :
    Miri.Memory.checkAndDerefPtr
      annealPointerArithmetic
      (Miri.Memory.Pointer.withoutProvenance addr)
      signedSize
      msg
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .error (.danglingIntegerPointer addr signedSize msg) := by
  rw [checkAndDerefPtr_nonzero_eq _ _ _ _ _ _ (by omega) hfit (by omega)]
  rfl

/-- Dereferencing a pointer to a deallocated allocation
(`mach.memory.live.find? (fun x => x.1 == allocId) = none`, e.g. after
`StorageDead`) fails `Miri.Memory.checkAndDerefPtr` with
`AccessError.allocationLookup (.deadAllocation allocId)`. -/
theorem checkAndDerefPtr_deadAlloc_err
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag) (offsetBytes : Nat)
    (signedSize : Int) (msg : Miri.Memory.CheckInAllocMsg)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hdead : mach.memory.live.find? (fun entry => entry.1 == allocId) = none)
    (hpos : 0 < signedSize) (hfit : signedSize < 2 ^ 63) :
    Miri.Memory.checkAndDerefPtr
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      signedSize
      msg
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .error (.allocationLookup (.deadAllocation allocId)) := by
  rw [checkAndDerefPtr_nonzero_eq _ _ _ _ _ _ (by omega) hfit (by omega)]
  rw [PtrRel.resolvePtr_concrete_eq allocId borTag offsetBytes hid hoff hbase signedSize]
  unfold annealLookupAlloc
  simp [hdead]

/-- An in-bounds non-negative access (`offsetBytes + sizeBytes ≤ localAlloc.allocation.byteSize.bytes.toNat`)
on a live allocation succeeds in `Miri.Memory.checkAndDerefPtr`. -/
theorem checkAndDerefPtr_live_inbounds_ok
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag) (offsetBytes sizeBytes : Nat)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (msg : Miri.Memory.CheckInAllocMsg)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hpos : 0 < sizeBytes) (hfit : (sizeBytes : Int) < 2 ^ 63)
    (hinbounds : offsetBytes + sizeBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) :
    Miri.Memory.checkAndDerefPtr
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (sizeBytes : Int)
      msg
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .ok (some
        { pointer := ⟨allocId, Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes), borTag⟩
          allocation :=
            { size := localAlloc.allocation.byteSize
              align := localAlloc.allocation.align
              kind := .liveData
              mutability := localAlloc.allocation.mutability } }) := by
  have hlo : -(2 ^ 63 : Int) ≤ (sizeBytes : Int) :=
    Int.le_trans (by decide) (Int.natCast_nonneg sizeBytes)
  have hne0 : (sizeBytes : Int) ≠ 0 := Int.ne_of_gt (Int.natCast_pos.mpr hpos)
  have hres :=
    PtrRel.resolvePtr_concrete_eq allocId borTag offsetBytes hid hoff hbase (sizeBytes : Int)
  have hlook :
      annealLookupAlloc mach allocId =
        .ok
          { size := localAlloc.allocation.byteSize
            align := localAlloc.allocation.align
            kind := .liveData
            mutability := localAlloc.allocation.mutability } := by
    unfold annealLookupAlloc
    rw [hlive]
  rw [checkAndDerefPtr_nonzero_lookup_ok _ _ _ _ _ _ _ _ _ _ _ _ hlo hfit hne0 hres hlook]
  have hoff_lt64 : offsetBytes < 2 ^ 64 :=
    Nat.lt_trans hoff (Nat.pow_lt_pow_right (by decide) (by decide))
  have hoff_bytes :
      (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes)).bytes.toNat = offsetBytes :=
    UInt64.toNat_ofNat_of_lt hoff_lt64
  have hinbounds' :
      (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes)).bytes.toNat + sizeBytes ≤
        localAlloc.allocation.byteSize.bytes.toNat := by
    rw [hoff_bytes]; exact hinbounds
  rw [checkedBounds_ofNat_inbounds _ _ _ _ _ _ hfit hinbounds']

/-- An out-of-bounds positive access (`localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + sizeBytes`)
on a live allocation fails `Miri.Memory.checkAndDerefPtr` with
`AccessError.pointerOutOfBounds`. -/
theorem checkAndDerefPtr_live_oob_err
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag) (offsetBytes sizeBytes : Nat)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (msg : Miri.Memory.CheckInAllocMsg)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hpos : 0 < sizeBytes) (hfit : (sizeBytes : Int) < 2 ^ 63)
    (hoob : localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + sizeBytes) :
    Miri.Memory.checkAndDerefPtr
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (sizeBytes : Int)
      msg
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .error (.pointerOutOfBounds allocId localAlloc.allocation.byteSize
        (offsetBytes : Int) (sizeBytes : Int) msg) := by
  have hlo : -(2 ^ 63 : Int) ≤ (sizeBytes : Int) :=
    Int.le_trans (by decide) (Int.natCast_nonneg sizeBytes)
  have hne0 : (sizeBytes : Int) ≠ 0 := Int.ne_of_gt (Int.natCast_pos.mpr hpos)
  have hres :=
    PtrRel.resolvePtr_concrete_eq allocId borTag offsetBytes hid hoff hbase (sizeBytes : Int)
  have hlook :
      annealLookupAlloc mach allocId =
        .ok
          { size := localAlloc.allocation.byteSize
            align := localAlloc.allocation.align
            kind := .liveData
            mutability := localAlloc.allocation.mutability } := by
    unfold annealLookupAlloc
    rw [hlive]
  rw [checkAndDerefPtr_nonzero_lookup_ok _ _ _ _ _ _ _ _ _ _ _ _ hlo hfit hne0 hres hlook]
  have hoff_lt64 : offsetBytes < 2 ^ 64 :=
    Nat.lt_trans hoff (Nat.pow_lt_pow_right (by decide) (by decide))
  have hoff_bytes :
      (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes)).bytes.toNat = offsetBytes :=
    UInt64.toNat_ofNat_of_lt hoff_lt64
  have hoob' :
      localAlloc.allocation.byteSize.bytes.toNat <
        (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes)).bytes.toNat + sizeBytes := by
    rw [hoff_bytes]; exact hoob
  obtain ⟨hse, hi64⟩ := annealPointerArithmetic_signExtendToTargetIsize_ofNat offsetBytes hoff
  have hse' :
      annealPointerArithmetic.signExtendToTargetIsize
        (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes)).bytes =
        .ok (Int64.ofInt (offsetBytes : Int)) := hse
  rw [checkedBounds_ofNat_oob _ _ _ _ _ _ hfit hoob', hse']
  dsimp only
  rw [hi64]

/-- `annealPointerArithmetic.truncateToTargetUsize` is the identity on all 64-bit
unsigned addresses. -/
theorem annealPointerArithmetic_truncateToTargetUsize_eq (value : UInt64) :
    annealPointerArithmetic.truncateToTargetUsize value = .ok value := by
  unfold Miri.Memory.PointerArithmetic.truncateToTargetUsize annealPointerArithmetic
  have htr := size_truncate_translateSizeBytes (sz := 8) (by simp [ValidScalarBytes])
    (BitVec.ofNat 128 value.toNat)
  change (match (translateSizeBytes 8).truncate (BitVec.ofNat 128 value.toNat) with
      | .ok v =>
        if v.toNat < 2 ^ 64 then Except.ok (UInt64.ofNat v.toNat)
        else Except.error Miri.Memory.PointerError.unsignedConversionOverflow
      | .error e => Except.error (.sourceSizeError e)) = Except.ok value
  rw [htr]
  dsimp only
  have hlt64 : value.toNat < 2 ^ 64 := UInt64.toNat_lt value
  have hlt64' : value.toNat < 2 ^ (8 * 8) := hlt64
  have hlt128 : value.toNat < 2 ^ 128 :=
    Nat.lt_trans hlt64 (Nat.pow_lt_pow_right (by decide) (by decide))
  have hbv :
      (BitVec.ofNat 128 ((BitVec.ofNat 128 value.toNat).toNat % 2 ^ (8 * 8))).toNat =
        value.toNat := by
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128,
      Nat.mod_eq_of_lt hlt64', Nat.mod_eq_of_lt hlt128]
  rw [hbv]
  simp only [hlt64, ↓reduceIte, UInt64.ofNat_toNat]

/-- `Pointer.wrappingOffset` under `annealPointerArithmetic` always succeeds with
64-bit wrapping addition on `ptr.offset.bytes`. -/
theorem wrappingOffset_annealPointerArithmetic_eq {Prov : Type}
    (ptr : Miri.Memory.Pointer Prov) (offset : Miri.ABI.Size) :
    ptr.wrappingOffset offset annealPointerArithmetic =
      .ok { ptr with offset := Miri.ABI.Size.ofBytes (ptr.offset.bytes + offset.bytes) } := by
  unfold Miri.Memory.Pointer.wrappingOffset
  rw [annealPointerArithmetic_truncateToTargetUsize_eq]
  rfl

theorem int64_toUInt64_ofInt_of_lt_u32
    (deltaBytes : Nat) :
    (Int64.ofInt (deltaBytes : Int)).toUInt64 = UInt64.ofNat deltaBytes := rfl

/-- `Pointer.wrappingSignedOffset` for a non-negative `deltaBytes` under
`annealPointerArithmetic` adds `UInt64.ofNat deltaBytes` to `ptr.offset.bytes`. -/
theorem wrappingSignedOffset_annealPointerArithmetic_ofNat {Prov : Type}
    (ptr : Miri.Memory.Pointer Prov) (deltaBytes : Nat) :
    ptr.wrappingSignedOffset (Int64.ofInt (deltaBytes : Int)) annealPointerArithmetic =
      .ok { ptr with offset := Miri.ABI.Size.ofBytes (ptr.offset.bytes + UInt64.ofNat deltaBytes) } := by
  unfold Miri.Memory.Pointer.wrappingSignedOffset
  rw [int64_toUInt64_ofInt_of_lt_u32 deltaBytes]
  exact wrappingOffset_annealPointerArithmetic_eq ptr (Miri.ABI.Size.ofBytes (UInt64.ofNat deltaBytes))

/-- Zero-offset `Miri.Interpreter.ptrOffsetInbounds` (including `count = 0` or a
zero-sized pointee type `size = 0`) succeeds on every pointer without resolving
provenance or looking up an allocation. -/
theorem ptrOffsetInbounds_zero_ok
    (mach : AnnealMachine) (ptr : Miri.Memory.Pointer (Option AnnealProv)) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      ptr
      0
      (annealResolvePtr mach)
      (annealLookupAlloc mach) = .ok ptr := by
  unfold Miri.Interpreter.ptrOffsetInbounds Miri.Memory.checkPtrAccessSigned
  have h0 : (0 : Int64).toInt = 0 := rfl
  have h0u : (0 : Int64).toUInt64 = 0 := rfl
  rw [h0, Miri.Memory.zero_sized_check_skips_resolution]
  unfold Miri.Memory.Pointer.wrappingSignedOffset
  rw [wrappingOffset_annealPointerArithmetic_eq]
  rcases ptr with ⟨⟨bytes⟩, prov⟩
  simp [Miri.ABI.Size.ofBytes, Except.mapError, bind, Except.bind, pure, Except.pure, h0u]

/-- Non-zero `Miri.Interpreter.ptrOffsetInbounds` on a provenance-less pointer
fails with `PointerOffsetError.access (.danglingIntegerPointer ...)`. -/
theorem ptrOffsetInbounds_withoutProvenance_err
    (mach : AnnealMachine) (addr : UInt64) (deltaBytes : Nat)
    (hpos : 0 < deltaBytes) (hdelta : deltaBytes < 2 ^ 32) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      (Miri.Memory.Pointer.withoutProvenance addr)
      (Int64.ofInt (deltaBytes : Int))
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .error (.access (.danglingIntegerPointer addr (deltaBytes : Int) .inboundsPointerArithmetic)) := by
  unfold Miri.Interpreter.ptrOffsetInbounds Miri.Memory.checkPtrAccessSigned
  rw [int64_toInt_ofInt_of_lt_u32 deltaBytes hdelta]
  have hpos' : (0 : Int) < (deltaBytes : Int) := Int.natCast_pos.mpr hpos
  have hfit : (deltaBytes : Int) < 2 ^ 63 := by
    have h63 : deltaBytes < 9223372036854775808 := Nat.lt_trans hdelta (by decide)
    exact Int.ofNat_lt.mpr h63
  rw [checkAndDerefPtr_withoutProvenance_err mach addr (deltaBytes : Int)
    .inboundsPointerArithmetic hpos' hfit]
  rfl

/-- Non-zero `Miri.Interpreter.ptrOffsetInbounds` on a deallocated allocation
fails with `PointerOffsetError.access (.allocationLookup (.deadAllocation allocId))`. -/
theorem ptrOffsetInbounds_deadAlloc_err
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes deltaBytes : Nat)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hpos : 0 < deltaBytes) (hdelta : deltaBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hdead : mach.memory.live.find? (fun entry => entry.1 == allocId) = none) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (Int64.ofInt (deltaBytes : Int))
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .error (.access (.allocationLookup (.deadAllocation allocId))) := by
  unfold Miri.Interpreter.ptrOffsetInbounds Miri.Memory.checkPtrAccessSigned
  rw [int64_toInt_ofInt_of_lt_u32 deltaBytes hdelta]
  have hpos' : (0 : Int) < (deltaBytes : Int) := Int.natCast_pos.mpr hpos
  have hfit : (deltaBytes : Int) < 2 ^ 63 := by
    have h63 : deltaBytes < 9223372036854775808 := Nat.lt_trans hdelta (by decide)
    exact Int.ofNat_lt.mpr h63
  rw [checkAndDerefPtr_deadAlloc_err allocId borTag offsetBytes (deltaBytes : Int)
    .inboundsPointerArithmetic hid hoff hbase hdead hpos' hfit]
  rfl

/-- In-bounds `Miri.Interpreter.ptrOffsetInbounds` (`offsetBytes + deltaBytes ≤ alloc.byteSize`,
including `deltaBytes = 0`) on a live allocation succeeds and advances the pointer
offset to `annealStackBaseAddr allocId + UInt64.ofNat (offsetBytes + deltaBytes)`. -/
theorem ptrOffsetInbounds_live_inbounds_ok
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes deltaBytes : Nat)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hdelta : deltaBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hinbounds : offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (Int64.ofInt (deltaBytes : Int))
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .ok
        ⟨Miri.ABI.Size.ofBytes
          (annealStackBaseAddr allocId + UInt64.ofNat (offsetBytes + deltaBytes)),
          some (.concrete allocId borTag)⟩ := by
  by_cases h0 : deltaBytes = 0
  · subst h0
    simpa [Nat.add_zero] using
      ptrOffsetInbounds_zero_ok mach
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩
  · have hpos : 0 < deltaBytes := Nat.pos_of_ne_zero h0
    have hfit : (deltaBytes : Int) < 2 ^ 63 := by
      have h63 : deltaBytes < 9223372036854775808 := Nat.lt_trans hdelta (by decide)
      exact Int.ofNat_lt.mpr h63
    unfold Miri.Interpreter.ptrOffsetInbounds Miri.Memory.checkPtrAccessSigned
    rw [int64_toInt_ofInt_of_lt_u32 deltaBytes hdelta]
    rw [checkAndDerefPtr_live_inbounds_ok allocId borTag offsetBytes deltaBytes localAlloc
      .inboundsPointerArithmetic hid hoff hbase hlive hpos hfit hinbounds]
    rw [wrappingSignedOffset_annealPointerArithmetic_ofNat _ deltaBytes]
    simp only [Except.mapError, bind, Except.bind, pure, Except.pure, Miri.ABI.Size.ofBytes]
    have hadd :
        annealStackBaseAddr allocId + UInt64.ofNat offsetBytes + UInt64.ofNat deltaBytes =
          annealStackBaseAddr allocId + UInt64.ofNat (offsetBytes + deltaBytes) := by
      rw [UInt64.add_assoc, UInt64.ofNat_add]
    rw [hadd]

/-- Out-of-bounds `Miri.Interpreter.ptrOffsetInbounds` (`alloc.byteSize < offsetBytes + deltaBytes`)
on a live allocation fails with `PointerOffsetError.access (.pointerOutOfBounds ...)`. -/
theorem ptrOffsetInbounds_live_oob_err
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes deltaBytes : Nat)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hpos : 0 < deltaBytes)
    (hdelta : deltaBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hoob : localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + deltaBytes) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (Int64.ofInt (deltaBytes : Int))
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .error (.access (.pointerOutOfBounds allocId localAlloc.allocation.byteSize
        (offsetBytes : Int) (deltaBytes : Int) .inboundsPointerArithmetic)) := by
  have hfit : (deltaBytes : Int) < 2 ^ 63 := by
    have h63 : deltaBytes < 9223372036854775808 := Nat.lt_trans hdelta (by decide)
    exact Int.ofNat_lt.mpr h63
  unfold Miri.Interpreter.ptrOffsetInbounds Miri.Memory.checkPtrAccessSigned
  rw [int64_toInt_ofInt_of_lt_u32 deltaBytes hdelta]
  rw [checkAndDerefPtr_live_oob_err allocId borTag offsetBytes deltaBytes localAlloc
    .inboundsPointerArithmetic hid hoff hbase hlive hpos hfit hoob]
  rfl

/-- Exact iff characterization of `Miri.Interpreter.ptrOffsetInbounds` on a live
allocation with `offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat`:
it succeeds if and only if `offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat`. -/
theorem ptrOffsetInbounds_live_iff
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes deltaBytes : Nat)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hdelta : deltaBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hoff_in : offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) :
    (∃ ptr',
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) = .ok ptr') ↔
      offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat := by
  constructor
  · rintro ⟨ptr', hok⟩
    refine Classical.byContradiction fun hnot => ?_
    have hoob : localAlloc.allocation.byteSize.bytes.toNat < offsetBytes + deltaBytes :=
      Nat.lt_of_not_le hnot
    have hpos : 0 < deltaBytes := by omega
    rw [ptrOffsetInbounds_live_oob_err allocId borTag offsetBytes deltaBytes localAlloc
      hid hoff hpos hdelta hbase hlive hoob] at hok
    cases hok
  · intro hinbounds
    exact ⟨_, ptrOffsetInbounds_live_inbounds_ok allocId borTag offsetBytes deltaBytes localAlloc
      hid hoff hdelta hbase hlive hinbounds⟩

/-! ### Alignment & Deref Access Lemmas -/

/-- `(annealStackBaseAddr allocId + offsetBytes) &&& 7 == 0` equals `offsetBytes % 8 == 0`
when `allocId.value.toNat < 2 ^ 32` and `offsetBytes < 2 ^ 32`. -/
theorem annealStackBaseAddr_add_isAligned_eight
    (allocId : Miri.Memory.AllocId) (offsetBytes : Nat)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32) :
    (Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes)).isAligned
      Miri.ABI.Align.EIGHT =
      .ok (offsetBytes % 8 == 0) := by
  have haddr : (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes).toNat =
      allocId.value.toNat * 2 ^ 32 + offsetBytes := by
    have hbase : (annealStackBaseAddr allocId).toNat = allocId.value.toNat * 2 ^ 32 := by
      unfold annealStackBaseAddr
      rw [UInt64.toNat_shiftLeft]
      have hlt64 : allocId.value.toNat * 2 ^ 32 < 2 ^ 64 := by omega
      simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hlt64]
    have hoff_lt : offsetBytes < 2 ^ 64 := by omega
    have hoff_u64 : (UInt64.ofNat offsetBytes).toNat = offsetBytes :=
      UInt64.toNat_ofNat_of_lt hoff_lt
    have hsum_lt : allocId.value.toNat * 2 ^ 32 + offsetBytes < 2 ^ 64 := by omega
    rw [UInt64.toNat_add, hbase, hoff_u64, Nat.mod_eq_of_lt hsum_lt]
  have hand : ((annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) &&& 7).toNat =
      offsetBytes % 8 := by
    rw [UInt64.toNat_and, haddr]
    have h7 : (7 : UInt64).toNat = 2 ^ 3 - 1 := by decide
    rw [h7, Nat.and_two_pow_sub_one_eq_mod]
    show (allocId.value.toNat * 2 ^ 32 + offsetBytes) % 8 = offsetBytes % 8
    omega
  unfold Miri.ABI.Size.isAligned Miri.ABI.Align.bytes Miri.ABI.Align.EIGHT
  dsimp only [bind, Except.bind, pure, Except.pure]
  change Except.ok (((annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) &&& 7) == 0) =
    Except.ok (offsetBytes % 8 == 0)
  congr 1
  by_cases h0 : offsetBytes % 8 = 0
  · have hu : (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) &&& 7 = 0 := by
      apply UInt64.toNat_inj.mp
      rw [hand, h0]
      rfl
    simp [hu, h0]
  · have hu : (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes) &&& 7 ≠ 0 := by
      intro hc
      have := congrArg UInt64.toNat hc
      rw [hand] at this
      exact h0 this
    rw [beq_false_of_ne hu, beq_false_of_ne h0]

/-- `Size.isAligned` returns `.ok true` for `.EIGHT` when `offsetBytes % 8 = 0`. -/
theorem size_isAligned_eight_of_aligned
    (allocId : Miri.Memory.AllocId) (offsetBytes : Nat)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (haligned : offsetBytes % 8 = 0) :
    (Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes)).isAligned
      Miri.ABI.Align.EIGHT = .ok true := by
  rw [annealStackBaseAddr_add_isAligned_eight allocId offsetBytes hid hoff]
  simp [haligned]

/-- `Size.isAligned` returns `.ok false` for `.EIGHT` when `offsetBytes % 8 ≠ 0`. -/
theorem size_isAligned_eight_of_misaligned
    (allocId : Miri.Memory.AllocId) (offsetBytes : Nat)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hmis : offsetBytes % 8 ≠ 0) :
    (Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes)).isAligned
      Miri.ABI.Align.EIGHT = .ok false := by
  rw [annealStackBaseAddr_add_isAligned_eight allocId offsetBytes hid hoff]
  rw [beq_false_of_ne hmis]

/-! ## 5. Borrow-Table Synchronization & `StackScalarAllocShape` Lemmas -/

/-- Under `(allocMap.map AllocMapEntry.tag).Nodup`, `lookupBorrow` on
`allocMap.map AllocMapEntry.toBorrowEntry` resolves every `e ∈ allocMap` to
`some e.toBorrowEntry`. -/
theorem lookupBorrow_map_toBorrowEntry_of_nodup
    {allocMap : List AllocMapEntry}
    (hnodup : (allocMap.map AllocMapEntry.tag).Nodup)
    {e : AllocMapEntry} (he : e ∈ allocMap) :
    lookupBorrow (allocMap.map AllocMapEntry.toBorrowEntry) e.tag =
      some e.toBorrowEntry := by
  induction allocMap with
  | nil => cases he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnot_mem, htl_nodup⟩ := hnodup
    cases he with
    | head _ =>
      show (match Nat.beq e.tag e.tag with
        | true => some e.toBorrowEntry
        | false => lookupBorrow (tl.map AllocMapEntry.toBorrowEntry) e.tag) =
        some e.toBorrowEntry
      rw [Nat.beq_refl]
    | tail _ hmem =>
      have hne : hd.tag ≠ e.tag := fun heq =>
        hnot_mem (heq ▸ List.mem_map_of_mem hmem)
      have hbeq : Nat.beq hd.tag e.tag = false := by
        cases h : Nat.beq hd.tag e.tag
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h) hne
      show (match Nat.beq hd.tag e.tag with
        | true => some hd.toBorrowEntry
        | false => lookupBorrow (tl.map AllocMapEntry.toBorrowEntry) e.tag) =
        some e.toBorrowEntry
      rw [hbeq]
      exact ih htl_nodup hmem

/-- `invalidateConflictingBorrows` on `allocMap.map AllocMapEntry.toBorrowEntry`
equals `(updateAllocMapOnWrite allocMap targetLocal writerTag).map AllocMapEntry.toBorrowEntry`. -/
theorem invalidateConflictingBorrows_map_toBorrowEntry
    (allocMap : List AllocMapEntry) (targetLocal : Local) (writerTag : Option Nat) :
    invalidateConflictingBorrows (allocMap.map AllocMapEntry.toBorrowEntry) targetLocal writerTag =
      (updateAllocMapOnWrite allocMap targetLocal writerTag).map AllocMapEntry.toBorrowEntry := by
  induction allocMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, invalidateConflictingBorrows_cons, updateAllocMapOnWrite,
      AllocMapEntry.toBorrowEntry_updateOnWrite, ih]

/-- For a root borrow list `borrows` where every entry has `parentTag = none`,
`isBorrowDescendantOrSelf borrows wTag ancTag` equals `Nat.beq wTag ancTag`. -/
theorem isBorrowDescendantOrSelf_root_eq_beq
    {borrows : List BorrowEntry}
    (hroot : ∀ b ∈ borrows, b.parentTag = none)
    (wTag ancTag : Nat) :
    isBorrowDescendantOrSelf borrows wTag ancTag = Nat.beq wTag ancTag := by
  unfold isBorrowDescendantOrSelf
  cases hlen : length borrows with
  | zero => rfl
  | succ fuel =>
    unfold isBorrowDescendantOrSelfAux
    cases hbeq : Nat.beq wTag ancTag
    · dsimp only
      cases hlook : lookupBorrow borrows wTag with
      | none => rfl
      | some entry =>
        have hmem : entry ∈ borrows := by
          clear hlen hroot
          induction borrows with
          | nil => cases hlook
          | cons hd tl ih =>
            unfold lookupBorrow at hlook
            cases hb : Nat.beq hd.tag wTag
            · rw [hb] at hlook
              exact List.mem_cons_of_mem hd (ih hlook)
            · rw [hb] at hlook
              injection hlook with h
              subst h
              exact List.Mem.head _
        dsimp only
        rw [hroot entry hmem]
    · rfl

theorem parentTag_toBorrowEntry (e : AllocMapEntry) :
    e.toBorrowEntry.parentTag = none := rfl

theorem targetProjection_toBorrowEntry (e : AllocMapEntry) :
    e.toBorrowEntry.targetProjection = .nil := rfl

/-- `invalidateTreeBorrowsAtProj` on root borrows at `.nil` (`0`, `0`) coincides
with `invalidateConflictingBorrows`. -/
theorem invalidateTreeBorrowsAtProj_map_toBorrowEntry
    (allMap subMap : List AllocMapEntry) (targetLocal : Local) (wTag : Nat) :
    invalidateTreeBorrowsAtProj
      (allMap.map AllocMapEntry.toBorrowEntry)
      (subMap.map AllocMapEntry.toBorrowEntry)
      targetLocal (some wTag) .nil 0 0 =
      (updateAllocMapOnWrite subMap targetLocal (some wTag)).map AllocMapEntry.toBorrowEntry := by
  have hroot : ∀ b ∈ allMap.map AllocMapEntry.toBorrowEntry, b.parentTag = none := by
    intro b hb
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
    rfl
  induction subMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons, updateAllocMapOnWrite]
    unfold invalidateTreeBorrowsAtProj updateBorrowPermTreeAtProj resolveTreeBorrowWriterTag
    dsimp only
    rw [show hd.toBorrowEntry.tag = hd.tag from rfl,
      isBorrowDescendantOrSelf_root_eq_beq hroot wTag hd.tag]
    cases h : Nat.beq wTag hd.tag with
    | false =>
      dsimp only
      rw [updateBorrowPermAtProj_nil_eq_updateBorrowPerm _ _ _ rfl,
        ← AllocMapEntry.toBorrowEntry_updateOnWrite, ih]
      rfl
    | true =>
      dsimp only
      rw [← Nat.eq_of_beq_eq_true h, updateBorrowPermAtProj_nil_eq_updateBorrowPerm _ _ _ rfl,
        ← AllocMapEntry.toBorrowEntry_updateOnWrite, ih]
      rfl

/-- `invalidateDerefWriteBorrows` at `⟨ptrLoc, [.deref]⟩` (`restProj = []`) on
`allocMap.map AllocMapEntry.toBorrowEntry` equals
`(updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)).map AllocMapEntry.toBorrowEntry`. -/
theorem invalidateDerefWriteBorrows_map_toBorrowEntry
    (locals₁ : List LocalSlot) (allocMap : List AllocMapEntry)
    (hnodup : (allocMap.map AllocMapEntry.tag).Nodup)
    (ptrLoc : Local) (ptrVal : ProvenancePtr) (sz : Nat)
    (e : AllocMapEntry) (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hptr : get? locals₁ ptrLoc = some (.init (.ptr ptrVal sz))) :
    invalidateDerefWriteBorrows locals₁ (allocMap.map AllocMapEntry.toBorrowEntry)
      ⟨ptrLoc, [.deref]⟩ .nil =
      (updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)).map
        AllocMapEntry.toBorrowEntry := by
  have hlook := lookupBorrow_map_toBorrowEntry_of_nodup hnodup he
  rw [htag] at hlook
  match allocMap with
  | [] => cases he
  | [single] =>
    unfold invalidateDerefWriteBorrows
    simp only [List.map_cons, List.map_nil] at hlook ⊢
    rw [hptr]
    dsimp only
    rw [hlook]
    dsimp only [AllocMapEntry.toBorrowEntry, appendProjections]
    exact invalidateConflictingBorrows_map_toBorrowEntry [single] e.localIdx (some ptrVal.tag)
  | e₁ :: e₂ :: rest =>
    unfold invalidateDerefWriteBorrows
    simp only [List.map_cons] at hlook ⊢
    rw [hptr]
    dsimp only
    rw [hlook]
    dsimp only [AllocMapEntry.toBorrowEntry, appendProjections]
    exact invalidateTreeBorrowsAtProj_map_toBorrowEntry (e₁ :: e₂ :: rest) (e₁ :: e₂ :: rest)
      e.localIdx ptrVal.tag

/-- `freezeTreeBorrowsOnReadAtProj` on root borrows at `.nil` (`0`, `0`) maps
`AllocMapEntry.updateOnRead`. -/
theorem freezeTreeBorrowsOnReadAtProj_map_toBorrowEntry
    (allMap subMap : List AllocMapEntry) (targetLocal : Local) (rTag : Nat) :
    freezeTreeBorrowsOnReadAtProj
      (allMap.map AllocMapEntry.toBorrowEntry)
      (subMap.map AllocMapEntry.toBorrowEntry)
      targetLocal (some rTag) .nil 0 0 =
      (subMap.map (fun e => e.updateOnRead targetLocal rTag)).map
        AllocMapEntry.toBorrowEntry := by
  have hroot : ∀ b ∈ allMap.map AllocMapEntry.toBorrowEntry, b.parentTag = none := by
    intro b hb
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hb
    rfl
  induction subMap with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.map_cons]
    unfold freezeTreeBorrowsOnReadAtProj updateBorrowPermOnReadAtProj
    rw [ ← ih]
    congr 1
    unfold AllocMapEntry.updateOnRead
    have hoverlap : borrowEntryOverlapsWrite hd.toBorrowEntry .nil 0 0 = true := rfl
    have htl_eq : hd.toBorrowEntry.targetLocal = hd.localIdx := rfl
    have htag_eq : hd.toBorrowEntry.tag = hd.tag := rfl
    rw [htl_eq]
    cases Nat.beq hd.localIdx targetLocal with
    | false => rfl
    | true =>
      dsimp only
      rw [hoverlap]
      dsimp only
      rw [htag_eq, isBorrowDescendantOrSelf_root_eq_beq hroot rTag hd.tag]
      cases Nat.beq rTag hd.tag with
      | true => rfl
      | false =>
        rcases hd with ⟨_, _, _, perm⟩
        cases perm <;> rfl

/-- `freezeDerefReadBorrowsAt` on `e₁ :: e₂ :: rest` matches
`updateAllocMapOnDerefRead`. -/
theorem freezeDerefReadBorrowsAt_map_toBorrowEntry
    (locals : List LocalSlot) (e₁ e₂ : AllocMapEntry) (rest : List AllocMapEntry)
    (hnodup : ((e₁ :: e₂ :: rest).map AllocMapEntry.tag).Nodup)
    (ptrLoc : Local) (ptrVal : ProvenancePtr) (sz : Nat)
    (e : AllocMapEntry) (he : e ∈ (e₁ :: e₂ :: rest)) (htag : e.tag = ptrVal.tag)
    (hptr : get? locals ptrLoc = some (.init (.ptr ptrVal sz))) :
    freezeDerefReadBorrowsAt locals ptrLoc .nil
      ((e₁ :: e₂ :: rest).map AllocMapEntry.toBorrowEntry) =
      (updateAllocMapOnDerefRead (e₁ :: e₂ :: rest) e.localIdx ptrVal.tag).map
        AllocMapEntry.toBorrowEntry := by
  have hlook := lookupBorrow_map_toBorrowEntry_of_nodup hnodup he
  rw [htag] at hlook
  unfold freezeDerefReadBorrowsAt updateAllocMapOnDerefRead
  rw [hptr]
  dsimp only
  rw [hlook]
  dsimp only [AllocMapEntry.toBorrowEntry, appendProjections]
  exact freezeTreeBorrowsOnReadAtProj_map_toBorrowEntry (e₁ :: e₂ :: rest) (e₁ :: e₂ :: rest)
    e.localIdx ptrVal.tag

/-! ### `StackScalarAllocShape`, Scalar Overwrite, and Uninitialized Read Lemmas -/

private def ptrAlloc_raw {P E : Type} (a : Miri.Memory.Allocation P E) : Array UInt8 :=
  Miri.Memory.Allocation.casesOn (motive := fun _ => Array UInt8) a
    (fun raw _ _ _ _ _ _ _ => raw)

private def ptrAlloc_pointerSize (layout : Miri.ABI.TargetDataLayout) : Miri.ABI.Size :=
  Miri.ABI.Size.fromBits layout.pointerWidth.bits

private def ptrAlloc_targetUIntBytes (layout : Miri.ABI.TargetDataLayout)
    (size : Miri.ABI.Size) (bits : Miri.ABI.U128) :
    Except Miri.Memory.AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

private def ptrAlloc_readTargetUInt (layout : Miri.ABI.TargetDataLayout)
    (bytes : Array UInt8) : Except Miri.Memory.AllocError Miri.ABI.U128 := do
  if bytes.size > 16 then
    throw (.scalarBytesTooWide (Miri.ABI.Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def ptrAlloc_checkedSlice {P E : Type} (allocation : Miri.Memory.Allocation P E)
    (range : Miri.Memory.AllocRange) : Except Miri.Memory.AllocError (Array UInt8) := do
  if (ptrAlloc_raw allocation).size != allocation.byteSize.bytes.toNat then
    throw (.storageLengthMismatch allocation.byteSize (ptrAlloc_raw allocation).size)
  let finish ← range.endExclusive |>.mapError Miri.Memory.AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.byteSize.bytes then
    throw (.outOfBounds range allocation.byteSize)
  return (ptrAlloc_raw allocation).extract range.start.bytes.toNat finish.bytes.toNat

private theorem ptrAlloc_getBytesUnchecked_eq {P E : Type}
    (allocation : Miri.Memory.Allocation P E) (range : Miri.Memory.AllocRange) :
    Miri.Memory.Allocation.getBytesUnchecked allocation range =
      ptrAlloc_checkedSlice allocation range := rfl

private def ptrAlloc_readScalar {P E : Type} [DecidableEq P] [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    Except Miri.Memory.AllocError (Miri.Memory.Scalar P) := do
  match ← (allocation.initializationMask.isRangeInitialized range).mapError
      Miri.Memory.AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← Miri.Memory.Allocation.getBytesUnchecked allocation range
  let bits ← ptrAlloc_readTargetUInt layout bytes
  if readProvenance then
    let targetSize := ptrAlloc_pointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenanceMap.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Miri.Memory.Scalar.fromPointer layout
        (Miri.Memory.Pointer.new provenance (Miri.ABI.Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
  else
    if Miri.Memory.PointerProvenance.offsetIsAddr (Prov := P) then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    let isEmpty ←
      (allocation.provenanceMap.rangeEmpty range (ptrAlloc_pointerSize layout)).mapError
        Miri.Memory.AllocError.provenance
    if isEmpty then
      let scalar ← (Miri.Memory.Scalar.fromUInt bits range.size).mapError
        Miri.Memory.AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

private theorem ptrAlloc_readScalar_eq {P E : Type} [DecidableEq P]
    [Miri.Memory.PointerProvenance P]
    (allocation : Miri.Memory.Allocation P E) (layout : Miri.ABI.TargetDataLayout)
    (range : Miri.Memory.AllocRange) (readProvenance : Bool) :
    allocation.readScalar layout range readProvenance =
      ptrAlloc_readScalar allocation layout range readProvenance := rfl

private def ptrAlloc_leBytes (x n : Nat) : Array UInt8 :=
  ((List.range' 0 n).map fun i => UInt8.ofNat ((x / 2 ^ (8 * i)) % 256)).toArray

private theorem ptrAlloc_leBytes_size (x n : Nat) : (ptrAlloc_leBytes x n).size = n := by
  simp [ptrAlloc_leBytes]

private theorem ptrAlloc_encode_loop (x : Nat) (l : List Nat) (acc : Array UInt8) :
    forIn (m := Except Miri.Memory.AllocError) l acc
        (fun index (r : Array UInt8) => pure (ForInStep.yield
          (r.push (UInt8.ofNat (x / 2 ^ (8 * index) % 256))))) =
      .ok (acc ++ (l.map fun i => UInt8.ofNat (x / 2 ^ (8 * i) % 256)).toArray) := by
  induction l generalizing acc with
  | nil => simp [pure, Except.pure]
  | cons i l ih =>
    rw [List.forIn_cons, pure_bind]
    simp only
    rw [ih]
    congr 1
    apply Array.toList_inj.mp
    simp

private theorem ptrAlloc_targetUIntBytes_spec (size : Miri.ABI.Size) (bits : Miri.ABI.U128)
    (hle : size.bytes.toNat ≤ 16) :
    ptrAlloc_targetUIntBytes annealTargetDataLayout size bits =
      .ok (ptrAlloc_leBytes bits.toNat size.bytes.toNat) := by
  have small : ¬ size.bytes > 16 := by
    simp only [GT.gt, UInt64.lt_iff_toNat_lt]
    simpa using Nat.not_lt.mpr hle
  have hendian : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  unfold ptrAlloc_targetUIntBytes
  simp only [small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', hendian,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, bind_pure]
  rw [ptrAlloc_encode_loop]
  simp [ptrAlloc_leBytes]

private def ptrAlloc_leSum (x k : Nat) : Nat → Nat
  | 0 => 0
  | m + 1 => x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) + ptrAlloc_leSum x (k + 1) m

private theorem ptrAlloc_leSum_spec (x : Nat) :
    ∀ m k, x % 2 ^ (8 * k) + ptrAlloc_leSum x k m = x % 2 ^ (8 * (k + m)) := by
  intro m
  induction m with
  | zero => intro k; simp [ptrAlloc_leSum]
  | succ m ih =>
    intro k
    have hstep : x % 2 ^ (8 * k) + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k) =
        x % 2 ^ (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mod_mul]
      simp only [show (2 : Nat) ^ 8 = 256 by rfl]
      rw [Nat.mul_comm (2 ^ (8 * k))]
    simp only [ptrAlloc_leSum]
    rw [← Nat.add_assoc, hstep, ih (k + 1), show k + 1 + m = k + (m + 1) by omega]

private theorem ptrAlloc_decode_loop (x n : Nat)
    (f : Nat → Nat → Except Miri.Memory.AllocError (ForInStep Nat))
    (hf : ∀ index s, index < n →
      f index s = .ok (.yield (s + x / 2 ^ (8 * index) % 256 * 2 ^ (8 * index)))) :
    ∀ m k acc, k + m ≤ n →
      forIn (List.range' k m) acc f = .ok (acc + ptrAlloc_leSum x k m) := by
  intro m
  induction m with
  | zero => intro k acc _; simp [ptrAlloc_leSum, pure, Except.pure]
  | succ m ih =>
    intro k acc hkm
    rw [List.range'_succ, List.forIn_cons, hf k acc (by omega)]
    simp only [ptrAlloc_leSum]
    rw [show (Except.ok (ForInStep.yield (acc + x / 2 ^ (8 * k) % 256 * 2 ^ (8 * k))) :
        Except Miri.Memory.AllocError (ForInStep Nat)) = pure (ForInStep.yield _) from rfl,
      pure_bind]
    simp only
    rw [ih (k + 1) _ (by omega), Nat.add_assoc]

private theorem ptrAlloc_readTargetUInt_leBytes (x n : Nat) (hn : n ≤ 16) :
    ptrAlloc_readTargetUInt annealTargetDataLayout (ptrAlloc_leBytes x n) =
      .ok (BitVec.ofNat 128 (x % 2 ^ (8 * n))) := by
  have small : ¬ n > 16 := by omega
  have hendian : (annealTargetDataLayout.endian == Miri.ABI.Endian.little) = true := rfl
  have hlsize : (ptrAlloc_leBytes x n).size = n := by simp [ptrAlloc_leBytes]
  unfold ptrAlloc_readTargetUInt
  simp only [hlsize, small, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range',
    hendian, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [ptrAlloc_decode_loop x n _ ?hf n 0 0 (by omega)]
  · have := ptrAlloc_leSum_spec x n 0
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
    simp [this, pure, Except.pure, bind, Except.bind]
  · intro index s hi
    have hb : (x / 2 ^ (8 * index) % 256) < 256 := Nat.mod_lt _ (by decide)
    simp [ptrAlloc_leBytes, hi, pure, Except.pure, Nat.mod_eq_of_lt hb]

private theorem ptrAlloc_allocRange_end (size : Miri.ABI.Size) :
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO size).endExclusive = .ok size := by
  cases size
  simp [Miri.Memory.AllocRange.endExclusive, Miri.Memory.AllocRange.end, Miri.Memory.allocRange,
    Miri.ABI.Size.ZERO, Miri.ABI.Size.add, Miri.ABI.Size.ofBytes, Except.mapError]

private theorem ptrAlloc_scalarModulus_eq_two_pow (sz : Nat) :
    scalarModulus sz = 2 ^ (8 * sz) := by
  induction sz with
  | zero => rfl
  | succ k ih =>
    show 256 * scalarModulus k = 2 ^ (8 * (k + 1))
    rw [ih, show 8 * (k + 1) = 8 * k + 8 by omega, Nat.pow_add, Nat.mul_comm]

private theorem ptrAlloc_fromUInt {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) :
    Miri.Memory.Scalar.fromUInt (Prov := AnnealProv) (BitVec.ofNat 128 sc.bits)
        (translateSizeBytes sc.sizeBytes) = .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  obtain ⟨msc', htry, hrel'⟩ := tryFromUInt_of_valid_canonical hrel.validBytes hrel.canonical
  have heq : msc' = msc := by
    cases msc'; cases msc
    have hd := hrel'.data_eq.trans hrel.data_eq.symm
    have hs := hrel'.size_eq.trans hrel.size_eq.symm
    simp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
    subst hd hs; rfl
  subst heq
  unfold Miri.Memory.Scalar.fromUInt
  simp [htry, Except.mapError, bind, Except.bind, pure, Except.pure]

namespace StackScalarAllocShape

/-- A fresh `Allocation.tryNew size align .Uninit annealZeroedStorage` tagged
with `extra` satisfies `StackScalarAllocShape size` and has alignment `align`. -/
theorem of_tryNew {E : Type} {size : Miri.ABI.Size} {align : Miri.ABI.Align}
    {allocation : Miri.Memory.Allocation AnnealProv Unit} (extra : E)
    (h : Miri.Memory.Allocation.tryNew size align .Uninit annealZeroedStorage = .ok allocation) :
    (allocation.withExtra extra).align = align ∧
    StackScalarAllocShape size (allocation.withExtra extra) := by
  have h' : Miri.Memory.Allocation.tryNew size align .Uninit
      (fun n _ => some (Array.replicate n.bytes.toNat 0)) = .ok allocation := h
  obtain ⟨hprov, hmask⟩ := Miri.Memory.Allocation.tryNew_uninit_shape size align allocation h'
  have hspec := freshStackAlloc_spec h
  have halloc_eq :
      (allocation.withExtra extra).len = size.bytes.toNat ∧
      (allocation.withExtra extra).align = align := by
    have h1 := h
    unfold Miri.Memory.Allocation.tryNew at h1
    simp only [bind, Except.bind] at h1
    split at h1
    · cases h1
    · rename_i v hv
      change (do
        let bytes ← (Miri.ABI.Align.bytes align).mapError Miri.Memory.AllocError.alignment
        let normalized ← (Miri.ABI.Align.fromBytes bytes).mapError Miri.Memory.AllocError.alignment
        if normalized == align then return align
        throw (Miri.Memory.AllocError.alignment (.tooLarge bytes))) = .ok v at hv
      cases hb : Miri.ABI.Align.bytes align with
      | error _ => simp [hb, bind, Except.bind, Except.mapError] at hv
      | ok b =>
        cases hf : Miri.ABI.Align.fromBytes b with
        | error _ => simp [hb, hf, bind, Except.bind, Except.mapError] at hv
        | ok n =>
          simp only [hb, hf, bind, Except.bind, Except.mapError, pure, Except.pure] at hv
          by_cases hn : n = align
          · subst hn
            obtain ⟨a0, h0, _, hlen0, _, _, halign0⟩ :=
              Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) size n b hb hf
            rw [h'] at h0
            injection h0 with ha
            subst ha
            cases allocation
            exact ⟨hlen0, halign0⟩
          · simp [hn, throw, throwThe, MonadExceptOf.throw] at hv
  exact ⟨halloc_eq.2, ⟨hspec.1, halloc_eq.1, hspec.2.1, hprov, ⟨false, hmask⟩⟩⟩

/-- Overwriting a `StackScalarAllocShape` allocation at offset `0` with a
`ScalarRel`-related scalar succeeds, preserves `StackScalarAllocShape` and
`align`, marks the whole range initialized, and reads back `.fromScalarInt msc`. -/
theorem writeScalar_readScalar {E : Type} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) {A : Miri.Memory.Allocation AnnealProv E}
    (hshape : StackScalarAllocShape (translateSizeBytes sc.sizeBytes) A) :
    ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
          (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () alloc' ∧
      alloc'.align = A.align ∧
      StackScalarAllocShape (translateSizeBytes sc.sizeBytes) alloc' ∧
      alloc'.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
        .ok (.ok ()) ∧
      alloc'.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
        .ok (Miri.Memory.Scalar.fromScalarInt msc) := by
  rcases hshape with ⟨hsz, hlen, hmut, hprov, ⟨initBool, hmask⟩⟩
  have hn : (translateSizeBytes sc.sizeBytes).bytes.toNat = sc.sizeBytes := by
    rcases hrel.validBytes with h | h | h | h | h <;> rw [h] <;> rfl
  have hn16 : (translateSizeBytes sc.sizeBytes).bytes.toNat ≤ 16 := by
    rw [hn]; rcases hrel.validBytes with h | h | h | h | h <;> omega
  have hrange :
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)).size =
        translateSizeBytes sc.sizeBytes := rfl
  have hconv :
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toBitsOrPtrInternal
          (translateSizeBytes sc.sizeBytes) = .ok (.bits (BitVec.ofNat 128 sc.bits)) := by
    unfold Miri.Memory.Scalar.toBitsOrPtrInternal
    simp only [Miri.Memory.Scalar.fromScalarInt, hrel.toBits_eq, Except.mapError, bind,
      Except.bind, pure, Except.pure]
  have hend := ptrAlloc_allocRange_end (translateSizeBytes sc.sizeBytes)
  have hraw : (ptrAlloc_raw A).size = (translateSizeBytes sc.sizeBytes).bytes.toNat := hlen
  have hslice : Miri.Memory.Allocation.getBytesUnchecked A
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
      .ok ((ptrAlloc_raw A).extract 0 (translateSizeBytes sc.sizeBytes).bytes.toNat) := by
    change ptrAlloc_checkedSlice A _ = _
    unfold ptrAlloc_checkedSlice
    simp only [hraw, hsz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hend,
      Except.mapError, bind, Except.bind]
    simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure]
  unfold Miri.Memory.Allocation.getBytesUnchecked at hslice
  have hmask2 : A.initializationMask.setRange
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) true =
      .ok (Miri.Memory.InitMask.new (translateSizeBytes sc.sizeBytes) true) := by
    rw [hmask]
    exact Miri.Memory.InitMask.full_overwrite_stays_lazy _ _ initBool true _ hend rfl
      (UInt64.le_refl _)
  unfold Miri.Memory.Allocation.initializationMask at hmask2
  unfold Miri.Memory.Allocation.provenanceMap at hprov
  have htoNat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    rw [BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    have hle128 : scalarModulus sc.sizeBytes ≤ 2 ^ 128 := by
      rw [ptrAlloc_scalarModulus_eq_two_pow]
      exact Nat.pow_le_pow_right (by decide)
        (by rcases hrel.validBytes with h | h | h | h | h <;> omega)
    have hcan := hrel.canonical
    omega
  obtain ⟨alloc', hw, halign', hsz', hlen_out, hmut', hprov', hmask', hraw'⟩ :
      ∃ alloc' : Miri.Memory.Allocation AnnealProv E,
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
            (Miri.Memory.Scalar.fromScalarInt msc) A = .ok () alloc' ∧
        alloc'.align = A.align ∧
        alloc'.byteSize = translateSizeBytes sc.sizeBytes ∧
        alloc'.len = (translateSizeBytes sc.sizeBytes).bytes.toNat ∧
        alloc'.mutability = .Mut ∧
        alloc'.provenanceMap = Miri.Memory.ProvenanceMap.new ∧
        alloc'.initializationMask =
          Miri.Memory.InitMask.new (translateSizeBytes sc.sizeBytes) true ∧
        ptrAlloc_raw alloc' =
          ptrAlloc_leBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat := by
    rw [hrel.size_eq]
    unfold Miri.Memory.Allocation.writeScalar
    simp only [hmut, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hrange, hconv, pure_bind]
    rw [hslice]
    simp only [hmask2]
    rw [hprov, Miri.Memory.ProvenanceMap.clear_new _ _ _ _ ?pos hend]
    case pos => decide
    simp only []
    split
    · rename_i data hdata
      have hdata' : ptrAlloc_targetUIntBytes annealTargetDataLayout
          (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .ok data := hdata
      rw [ptrAlloc_targetUIntBytes_spec _ _ hn16] at hdata'
      cases hdata'
      have hstart : (Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (translateSizeBytes sc.sizeBytes)).start.bytes.toNat = 0 := rfl
      have hlbytes : (ptrAlloc_leBytes (BitVec.ofNat 128 sc.bits).toNat
          (translateSizeBytes sc.sizeBytes).bytes.toNat).size =
          (translateSizeBytes sc.sizeBytes).bytes.toNat := by simp [ptrAlloc_leBytes]
      have hlen' := hlen; unfold Miri.Memory.Allocation.len at hlen'
      have hsz_u := hsz; unfold Miri.Memory.Allocation.byteSize at hsz_u
      simp only [hstart, hlbytes, hlen', hsz_u, Array.size_append, Array.size_extract,
        Nat.min_self, Nat.zero_add, Nat.sub_self, Nat.add_zero, Nat.zero_min,
        bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
      · simp [Miri.Memory.Allocation.len, ptrAlloc_leBytes, hlen']
      · simp [ptrAlloc_raw, htoNat, hlen']
    · rename_i err herr
      have herr' : ptrAlloc_targetUIntBytes annealTargetDataLayout
          (translateSizeBytes sc.sizeBytes) (BitVec.ofNat 128 sc.bits) = .error err := herr
      rw [ptrAlloc_targetUIntBytes_spec _ _ hn16] at herr'
      cases herr'
  refine ⟨alloc', hw, halign', ⟨hsz', hlen_out, hmut', hprov', ⟨true, hmask'⟩⟩, ?_, ?_⟩
  · rw [hmask']
    exact Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend (UInt64.le_refl _)
  · have hslice_read : ptrAlloc_checkedSlice alloc'
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) =
        .ok (ptrAlloc_leBytes sc.bits (translateSizeBytes sc.sizeBytes).bytes.toNat) := by
      have hrawsize : (ptrAlloc_raw alloc').size =
          (translateSizeBytes sc.sizeBytes).bytes.toNat := by
        rw [hraw', ptrAlloc_leBytes_size]
      unfold ptrAlloc_checkedSlice
      simp only [hrawsize, hsz', bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, hend,
        Except.mapError, bind, Except.bind]
      simp [Miri.Memory.allocRange, Miri.ABI.Size.ZERO, pure, Except.pure, hraw',
        ptrAlloc_leBytes_size]
    have hoff : Miri.Memory.PointerProvenance.offsetIsAddr AnnealProv = true := rfl
    have hmod : sc.bits % 2 ^ (8 * (translateSizeBytes sc.sizeBytes).bytes.toNat) = sc.bits := by
      rw [hn, ← ptrAlloc_scalarModulus_eq_two_pow]
      exact Nat.mod_eq_of_lt hrel.canonical
    rw [ptrAlloc_readScalar_eq]
    unfold ptrAlloc_readScalar
    rw [hmask', Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend (UInt64.le_refl _)]
    simp only [Except.mapError, bind, Except.bind]
    rw [ptrAlloc_getBytesUnchecked_eq, hslice_read]
    simp only []
    rw [ptrAlloc_readTargetUInt_leBytes _ _ hn16, hmod]
    simp only [Bool.false_eq_true, ↓reduceIte, hoff, hrange, ptrAlloc_fromUInt hrel]

/-- Reading an uninitialized `StackScalarAllocShape` allocation (where
`isRangeInitialized ≠ .ok (.ok ())` and `sz ≠ ZERO`) fails `readScalar` with
`.error (.invalidUninitBytes _)`. -/
theorem uninit_readScalar_err {E : Type} {sz : Miri.ABI.Size}
    {A : Miri.Memory.Allocation AnnealProv E}
    (hshape : StackScalarAllocShape sz A)
    (huninit : A.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) ≠ .ok (.ok ()))
    (readProvenance : Bool) :
    ∃ info, A.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) readProvenance =
      .error (.invalidUninitBytes info) := by
  rcases hshape with ⟨_, _, _, _, ⟨b, hmask⟩⟩
  have hend := ptrAlloc_allocRange_end sz
  cases b with
  | true =>
    exfalso
    apply huninit
    rw [hmask]
    exact Miri.Memory.InitMask.lazy_initialized_query _ _ _ hend (UInt64.le_refl _)
  | false =>
    change ∃ info, ptrAlloc_readScalar A annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sz) readProvenance =
      .error (.invalidUninitBytes info)
    unfold ptrAlloc_readScalar
    rw [hmask, Miri.Memory.InitMask.lazy_uninitialized_query sz _ sz hend (UInt64.le_refl _)]
    exact ⟨_, rfl⟩

end StackScalarAllocShape

/-- Updating `id`'s allocation in `mach.memory.live` via `setLiveAllocation`
preserves `MemPlaceRel` on any `MemPlace` pointing to a distinct allocation
`allocId ≠ id`. -/
theorem MemPlaceRel.of_setLiveAllocation_ne
    {mach : AnnealMachine} {id : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {newMem : AnnealMemory}
    (hfind : mach.memory.live.find? (fun x => x.1 == id) = some (id, localAlloc))
    (hset : mach.memory.setLiveAllocation id alloc' = .ok newMem)
    {ty : Ty} {layouts : LayoutTable} {optVal : Option Value}
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hmp : MemPlaceRel mach ty layouts optVal mp)
    (hne : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    MemPlaceRel { mach with memory := newMem } ty layouts optVal mp := by
  have hmem_eq := Miri.Memory.MemoryState.setLiveAllocation_of_find
    mach.memory id localAlloc alloc' hfind
  rw [hmem_eq] at hset
  injection hset with hnm
  subst hnm
  cases hmp with
  | mk allocId tag baseAddr relOffset la hprov hmis hmeta hl hb hovf hptr hmut halign
      hbounds huninit hval hscalar =>
    have hne_id : allocId ≠ id := by
      intro heq
      apply hne
      rw [hprov, heq]; rfl
    refine .mk allocId tag baseAddr relOffset la hprov hmis hmeta ?_ hb hovf hptr hmut
      halign hbounds huninit hval hscalar
    simp only [Array.toList_push, List.mem_append, Array.toList_filter, List.mem_filter]
    exact Or.inl ⟨hl, by simp [hne_id]⟩

/-- Updating `id`'s allocation in `mach.memory.live` via `setLiveAllocation`
preserves `LocalRelLM3_1` for any local that does not own `id`. -/
theorem LocalRelLM3_1.of_setLiveAllocation_ne
    {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {id : Miri.Memory.AllocId}
    {localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {newMem : AnnealMemory}
    (hfind : mach.memory.live.find? (fun x => x.1 == id) = some (id, localAlloc))
    (hset : mach.memory.setLiveAllocation id alloc' = .ok newMem)
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls)
    (hne : ∀ mp, mls.value = .live (.indirect mp) →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    LocalRelLM3_1 { mach with memory := newMem } allocMap decl layouts slot mls := by
  cases h with
  | rawPtr p mptr cl mutability pointeeKind hc hty hptr =>
    exact .rawPtr p mptr cl mutability pointeeKind hc hty hptr
  | base hb =>
    cases hb with
    | dead cl hc => exact .base (.dead cl hc)
    | immediate slot imm cl hc hv => exact .base (.immediate slot imm cl hc hv)
    | indirect slot mp cl hc hnd hmp =>
      exact .base (.indirect slot mp cl hc hnd
        (hmp.of_setLiveAllocation_ne hfind hset (hne mp rfl)))

end LeanMiriSpec.Correspondence
