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

/-! ## 1. Pointer Resolution & Live Allocation Lookup Callbacks -/

/-- 64-bit target pointer arithmetic context (`pointerSize = 8` bytes). -/
def annealPointerArithmetic : Miri.Memory.PointerArithmetic :=
  { pointerSize := Miri.ABI.Size.ofBytes 8 }

/-- Resolve a `Miri.Memory.Pointer (Option AnnealProv)` against the cached base
addresses in `mach.addresses` (`Miri.Memory.PointerResolver`).

* A pointer without provenance (`ptr.provenance = none`, such as a null or
  integer-cast pointer) fails with `.error ptr.offset.bytes`, which
  `Miri.Memory.checkAndDerefPtr` reports as
  `AccessError.danglingIntegerPointer`.
* A pointer with concrete provenance `some (.concrete allocId borTag)` resolves
  to allocation-relative offset `ptr.offset.bytes - baseAddr` when
  `mach.lookupBaseAddr allocId = some baseAddr` and `baseAddr ≤ ptr.offset.bytes`. -/
def annealResolvePtr (mach : AnnealMachine) :
    Miri.Memory.PointerResolver AnnealProv Miri.Memory.BorTag :=
  fun ptr _signedSize =>
    match ptr.provenance with
    | none => .error ptr.offset.bytes
    | some (.concrete allocId borTag) =>
      match mach.lookupBaseAddr allocId with
      | some baseAddr =>
        if baseAddr ≤ ptr.offset.bytes then
          .ok ⟨allocId, Miri.ABI.Size.ofBytes (ptr.offset.bytes - baseAddr), borTag⟩
        else
          .error ptr.offset.bytes
      | none => .error ptr.offset.bytes
    | some .wildcard => .error ptr.offset.bytes

/-- Look up live allocation metadata for `allocId` in `mach.memory.live`
(`Miri.Memory.LiveAllocationLookup`).

If `allocId` has been deallocated (for example, by `StorageDead`), it is absent
from `mach.memory.live` and this lookup returns
`.error (.deadAllocation allocId)`, which `Miri.Memory.checkAndDerefPtr`
reports as `AccessError.allocationLookup (.deadAllocation allocId)`. -/
def annealLookupAlloc (mach : AnnealMachine) : Miri.Memory.LiveAllocationLookup :=
  fun allocId =>
    match mach.memory.live.find? (fun entry => entry.1 == allocId) with
    | some (_, localAlloc) =>
      .ok
        { size := localAlloc.allocation.byteSize
          align := localAlloc.allocation.align
          kind := .liveData
          mutability := localAlloc.allocation.mutability }
    | none => .error (.deadAllocation allocId)

/-! ## 2. `AllocMapRel` and `PtrRel` Invariants -/

/-- Entry in the `(localIdx ↔ allocId)` correspondence table relating an Anneal
address-taken local `localIdx` (and its borrow tag `tag` in `s.memory.borrows`)
to its `lean-miri` stack allocation `allocId`. -/
structure AllocMapEntry where
  tag : Nat
  localIdx : Local
  allocId : Miri.Memory.AllocId
  perm : TreeBorrowPerm

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

1. **Local-to-AllocId functional consistency**: Any two entries in `allocMap`
   for the same `localIdx` name the same `allocId`.
2. **AllocId-to-Local injectivity**: Any two entries in `allocMap` naming the
   same `allocId` refer to the same `localIdx`.
3. **Valid base address (`id <<< 32`)**: Every `e ∈ allocMap` has
   `e.allocId.value.toNat < 2 ^ 32` and
   `m.machine.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId)`.
4. **Borrow-table synchronization**: For every `e ∈ allocMap`,
   `lookupBorrow s.memory.borrows e.tag = some { tag := e.tag, targetLocal := e.localIdx, targetProjection := .nil, perm := e.perm }`
   and `e.tag < s.memory.nextTag`.
5. **Live vs. Dead local synchronization**: For every `e ∈ allocMap` and root
   frame `topFrame` (`m.stack.frames = #[topFrame]`):
   * If `get? s.frame.locals e.localIdx = some slot` with `slot ≠ .dead`, then
     `topFrame.locals[e.localIdx]? = some ⟨.live (.indirect (stackAllocPlace e.allocId)), lay⟩`.
   * If `get? s.frame.locals e.localIdx = some .dead`, then
     `m.machine.memory.live.find? (fun x => x.1 == e.allocId) = none`. -/
structure AllocMapRel
    (body : CapturedMir)
    (s : MachineState)
    (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Prop where
  /-- Functional consistency from `localIdx` to `allocId`. -/
  local_to_alloc_unique :
    ∀ e₁ ∈ allocMap, ∀ e₂ ∈ allocMap, e₁.localIdx = e₂.localIdx → e₁.allocId = e₂.allocId
  /-- Injectivity from `allocId` to `localIdx`. -/
  alloc_to_local_injective :
    ∀ e₁ ∈ allocMap, ∀ e₂ ∈ allocMap, e₁.allocId = e₂.allocId → e₁.localIdx = e₂.localIdx
  /-- Every mapped `allocId` fits below `2^32` and has its `id <<< 32` base
  address cached in `m.machine.addresses`. -/
  base_addr_valid :
    ∀ e ∈ allocMap,
      e.allocId.value.toNat < 2 ^ 32 ∧
      m.machine.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId)
  /-- Every entry in `allocMap` resolves in `s.memory.borrows` to the same
  `targetLocal` and `perm`, with `tag < s.memory.nextTag`. -/
  borrow_sync :
    ∀ e ∈ allocMap,
      e.tag < s.memory.nextTag ∧
      lookupBorrow s.memory.borrows e.tag =
        some { tag := e.tag, targetLocal := e.localIdx, targetProjection := .nil, perm := e.perm }
  /-- Live locals are backed by `stackAllocPlace e.allocId` in `topFrame`; dead
  locals have `e.allocId` absent from `m.machine.memory.live`. -/
  local_alloc_sync :
    ∀ topFrame, m.stack.frames = #[topFrame] →
      ∀ e ∈ allocMap,
        (∀ slot, get? s.frame.locals e.localIdx = some slot → slot ≠ .dead →
          ∃ lay, topFrame.locals[e.localIdx]? =
            some ⟨.live (.indirect (stackAllocPlace e.allocId)), lay⟩) ∧
        (get? s.frame.locals e.localIdx = some .dead →
          m.machine.memory.live.find? (fun x => x.1 == e.allocId) = none)

namespace AllocMapRel

/-- The empty `AllocMap` trivially satisfies `AllocMapRel` in any state. -/
theorem nil (body : CapturedMir) (s : MachineState) (m : AnnealStepState) :
    AllocMapRel body s m [] where
  local_to_alloc_unique := by intro _ h; cases h
  alloc_to_local_injective := by intro _ h; cases h
  base_addr_valid := by intro _ h; cases h
  borrow_sync := by intro _ h; cases h
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

* `borrows_tracked`: each borrow entry is the root borrow of an `allocMap`
  entry (whole local, no projection, default range and parent), and
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
      (borrows_tracked :
        ∀ b ∈ s.memory.borrows, ∃ e ∈ allocMap,
          b = { tag := e.tag, targetLocal := e.localIdx, targetProjection := .nil,
                perm := e.perm })
      (alloc_rel : AllocMapRel body s m allocMap)
      (memoryAllocDisjoint : MemoryAllocDisjoint topFrame) :
      StateRelLM3_1 body s m allocMap

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

/-- `StateRel` embeds into `StateRelLM3_1` with the empty `allocMap`. -/
theorem StateRel.toLM3_1 {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (h : StateRel body s m) : StateRelLM3_1 body s m [] := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller,
    hdisj⟩
  refine .mk tf hframes hretCont hretPlace (hfr.toLM3_1 []) hcal hstack hprot hcaller ?_
    (AllocMapRel.nil body s m) hdisj
  intro b hb
  rw [hbor] at hb
  cases hb

/-- `StateRelLM3_1` with the empty `allocMap` is `StateRel`: the extension is
conservative. -/
theorem StateRelLM3_1.toStateRel {body : CapturedMir} {s : MachineState}
    {m : AnnealStepState} (h : StateRelLM3_1 body s m []) : StateRel body s m := by
  rcases h with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, htracked,
    _, hdisj⟩
  have hbor : s.memory.borrows = .nil := by
    cases hb : s.memory.borrows with
    | nil => rfl
    | cons b rest =>
      obtain ⟨_, he, _⟩ := htracked b (by rw [hb]; exact List.Mem.head _)
      cases he
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

end LeanMiriSpec.Correspondence
