/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM1_4
import LeanMiriSpec.Correspondence.PtrLM3_1

/-!
# `LM-3.1`: Raw Pointers, `AddrOf` + `forceAllocation`, `Deref`, `BinOp.Offset`, `PtrToPtr` & Expose Casts

Correspondence results between Anneal's `Trusted.Rustc.V2026_06_01.MirSemantics`
and `lean-miri` for the raw-pointer fragment (`LM-3.1`). They are stated over
`StateRelLM3_1` and `StepRelLM3_1` (`PtrLM3_1`), the pointer-aware extensions of
`StateRel` and `StepRel`: `StateRel` itself admits neither a borrow entry nor a
local holding a pointer, so no state reached by taking an address satisfies it.

1. **`_d = &raw (const|mut) _t` (`step_rawPtr_addrOf_simulation`)**: one real
   step of `stepMirFn` and of `Miri.Interpreter.Step.step` under
   `annealStepHooks`, from a pointer-free `StateRel` state. `forceAllocation`
   moves an immediate `_t` into the fresh allocation `nextAllocId`
   (`forceAllocation_promote_eq`, then `LM-1.4`'s
   `forceAllocation_preserves_StateRel`), `MemPlace.toRef` produces the pointer,
   and the resulting states are related by `StateRelLM3_1` under the new
   `allocMap` entry; a dead `_t` or `_d` is undefined behavior in both machines.
2. **`PlaceElem.Deref` (`evalProjection_deref_simulation`)**: lemmas relating
   Anneal's dereferencing reads and writes to `evalDerefReadScalarMiri` and
   `evalDerefWriteScalarMiri`. These two functions compose `lean-miri`'s memory
   checks (`checkAndDerefPtr`, `Size.isAligned`, `Allocation.readScalar` /
   `writeScalar`) but are not the interpreter's own `Deref` place path, which
   `annealStepHooks` does not yet implement; the successful cases take the
   `lean-miri` read or write result as a premise.
3. **`BinOp.Offset` (`evalBinOp_offset_inbounds_simulation`)**: Anneal's offset
   and `lean-miri`'s `ptrOffsetInbounds` on byte deltas. Anneal never reports
   undefined behavior for `Offset` (it adds the raw count to `offsetBytes`, with
   neither a bounds check nor scaling by the pointee size), whereas `lean-miri`
   reports it for out-of-bounds offsets; see `WitLM3_1` for a kernel-checked
   consequence.
4. **`CastKind.PtrToPtr` (`evalCast_ptrToPtr_simulation`)**: Anneal's cast and
   `Miri.Interpreter.Cast.ptrToPtr` both keep the pointer. The exposure casts
   are related only on the Anneal side (`evalRvalue_expose_withExposed_roundtrip`):
   Anneal's exposed address `allocId * 65536 + offsetBytes` is not `lean-miri`'s
   address `(allocId <<< 32) + offset`.
5. **Composed step (`step_stmt_lm3_1_simulation`)**: the `LM-1.4` statement forms
   (lifted to `StepRelLM3_1 []`) and the address-of form, as one real-step
   theorem.
-/

namespace LeanMiriSpec.Correspondence

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics

/-! ## 1. Extended Value Relation for Raw Pointers (`ImmediateRelLM3_1`) -/

/-- `ImmediateRel` extended with raw-pointer immediates related by `PtrRel allocMap`. -/
inductive ImmediateRelLM3_1
    (allocMap : List AllocMapEntry)
    (ty : Ty)
    (layouts : LayoutTable) :
    Value → Miri.Interpreter.Immediate AnnealProv → Prop where
  /-- Any scalar/unit/pair related by `ImmediateRel` is related by `ImmediateRelLM3_1`. -/
  | of_immediateRel {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv} :
      ImmediateRel ty layouts v imm →
      ImmediateRelLM3_1 allocMap ty layouts v imm
  /-- A raw pointer value `.ptr p 8` at type `.rawPtr mutability pointeeKind` is related
  to `.scalar (Scalar.fromPointer annealTargetDataLayout mptr)` when `PtrRel allocMap p mptr`. -/
  | rawPtr
      (mutability : Mutability)
      (pointeeKind : RigidTy)
      (p : ProvenancePtr)
      (mptr : Miri.Memory.Pointer AnnealProv) :
      ty.kind = .rawPtr mutability pointeeKind →
      PtrRel allocMap p mptr →
      ImmediateRelLM3_1 allocMap ty layouts
        (.ptr p 8)
        (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))

namespace ImmediateRelLM3_1

/-- `ImmediateRelLM3_1` survives extending `allocMap` with another entry. -/
theorem mono_cons
    {allocMap : List AllocMapEntry} (e : AllocMapEntry)
    {ty : Ty} {layouts : LayoutTable}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (h : ImmediateRelLM3_1 allocMap ty layouts v imm) :
    ImmediateRelLM3_1 (e :: allocMap) ty layouts v imm := by
  cases h with
  | of_immediateRel himm => exact .of_immediateRel himm
  | rawPtr mutability pointeeKind p mptr hty hptr =>
    exact .rawPtr mutability pointeeKind p mptr hty (hptr.mono_cons e)

end ImmediateRelLM3_1

/-! ## 2. `LM-3.1` Cast & Rvalue Hooks -/

/-- Extended `CastTypeInfo` classifier that maps encoded raw pointers (`TyId = 40`),
references (`TyId = 41`), and function pointers (`TyId = 42`) in addition to all
scalar integer/bool/char types from `castTypeInfoOfEncodedTyId`. -/
def castTypeInfoOfEncodedTyIdLM3_1 (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.CastTypeInfo :=
  match tyId with
  | 40 => .ok (.rawPointer 1)
  | 41 => .ok (.reference 1)
  | 42 => .ok .fnPointer
  | _ => castTypeInfoOfEncodedTyId tyId

/-- `annealCastHooks` with `castTypeInfoOfEncodedTyIdLM3_1` as the type
classifier, so that `Miri.Interpreter.Cast.ptrToPtr` recognizes raw pointers.
The pointee argument of `.rawPointer` is a placeholder: `encodeTyId` maps every
raw pointer type to `TyId = 40`, so the pointee is not recoverable, and
`ptrToPtr` does not inspect it. The provenance-exposure leaves stay those of
`annealCastHooks`, which fail closed: Anneal's exposed addresses
(`allocId * 65536 + offsetBytes`) do not correspond to `lean-miri` addresses. -/
def annealCastHooksLM3_1 (layouts : LayoutTable := emptyLayoutTable) :
    Miri.Interpreter.CastHooks
      AnnealProv
      AnnealStepState
      Unit
      (Miri.Interpreter.RuntimePlace AnnealProv) :=
  { annealCastHooks layouts with
    typeInfo := fun _ tyId =>
      match castTypeInfoOfEncodedTyIdLM3_1 tyId with
      | .ok info => pure info
      | .error err => throw err }

/-- Evaluate a dereference read (`*ptr`) in `lean-miri`:
1. Validates pointer bounds and liveness via `Miri.Memory.checkAndDerefPtr`;
2. Validates pointer alignment against `(translateTy pointeeTy layouts).layout.align.abi`
   via `Miri.ABI.Size.isAligned`;
3. Reads the scalar from the resolved live allocation at its allocation-relative
   offset via `Allocation.readScalar`. -/
def evalDerefReadScalarMiri
    (mach : AnnealMachine)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (size : Miri.ABI.Size) (align : Miri.ABI.Align) :
    Except Miri.Interpreter.StepError (Miri.Memory.Scalar AnnealProv) :=
  match Miri.Memory.checkAndDerefPtr
      annealPointerArithmetic
      ⟨mptr.offset, some mptr.provenance⟩
      (size.bytes.toNat : Int)
      .memoryAccess
      (annealResolvePtr mach)
      (annealLookupAlloc mach) with
  | .error _ => .error (.undefinedBehavior "pointer dereference check failed")
  | .ok none => .error (.unsupported "zero-sized scalar deref read")
  | .ok (some checked) =>
    match mptr.offset.isAligned align with
    | .error _ => .error (.invalidProgram "invalid alignment on deref read")
    | .ok false => .error (.undefinedBehavior "alignment check failed on deref read")
    | .ok true =>
      match mach.memory.live.find? (fun entry => entry.1 == checked.pointer.allocId) with
      | none => .error (.undefinedBehavior "deref read of non-live allocation")
      | some (_, localAlloc) =>
        match localAlloc.allocation.readScalar
            annealTargetDataLayout
            (Miri.Memory.allocRange checked.pointer.offset size)
            false with
        | .ok sc => .ok sc
        | .error _ => .error (.undefinedBehavior "deref read of uninitialized or invalid scalar bytes")

/-- Evaluate a dereference write (`*ptr = val`) in `lean-miri`:
1. Validates pointer bounds and liveness via `Miri.Memory.checkAndDerefPtr`;
2. Validates pointer alignment against `(translateTy pointeeTy layouts).layout.align.abi`
   via `Miri.ABI.Size.isAligned`;
3. Writes the scalar into the resolved live allocation at its allocation-relative
   offset via `Miri.Memory.Allocation.writeScalar`. -/
def evalDerefWriteScalarMiri
    (mach : AnnealMachine)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (size : Miri.ABI.Size) (align : Miri.ABI.Align)
    (sc : Miri.Memory.Scalar AnnealProv) :
    Except Miri.Interpreter.StepError
      (Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :=
  match Miri.Memory.checkAndDerefPtr
      annealPointerArithmetic
      ⟨mptr.offset, some mptr.provenance⟩
      (size.bytes.toNat : Int)
      .memoryAccess
      (annealResolvePtr mach)
      (annealLookupAlloc mach) with
  | .error _ => .error (.undefinedBehavior "pointer dereference check failed")
  | .ok none => .error (.unsupported "zero-sized scalar deref write")
  | .ok (some checked) =>
    match mptr.offset.isAligned align with
    | .error _ => .error (.invalidProgram "invalid alignment on deref write")
    | .ok false => .error (.undefinedBehavior "alignment check failed on deref write")
    | .ok true =>
      match mach.memory.live.find? (fun entry => entry.1 == checked.pointer.allocId) with
      | none => .error (.undefinedBehavior "deref write to non-live allocation")
      | some (_, localAlloc) =>
        match Miri.Memory.Allocation.writeScalar
            annealTargetDataLayout
            (Miri.Memory.allocRange checked.pointer.offset sc.size)
            sc
            localAlloc.allocation with
        | .ok () alloc' => .ok alloc'
        | .error _ _ => .error (.undefinedBehavior "deref write of scalar failed")

/-! ## 3. Deliverable 1: `Rvalue.RawPtr` (`AddrOf`) + `forceAllocation` Simulation -/

/-- Compute the Tree Borrows permission assigned to `&raw (const|mut) _target`. -/
def rawPtrPerm (localDecls : List LocalDecl) (layouts : LayoutTable)
    (mutability : Mutability) (targetIdx : Local) : TreeBorrowPerm :=
  match mutability with
  | .not => sharedBorrowPerm localDecls layouts ⟨targetIdx, .nil⟩
  | .mut => .active

/-- Anneal's `evalRvalue (.rawPtr mutability ⟨targetIdx, .nil⟩)` on a live local
allocates a fresh borrow entry with `tag := s.memory.nextTag` and returns
`.ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)`. -/
theorem evalRvalue_rawPtr_live_eq
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (mutability : Mutability) (targetIdx : Local) (slot : LocalSlot)
    (hslot : get? s.frame.locals targetIdx = some slot)
    (hlive : slot ≠ .dead) :
    let perm : TreeBorrowPerm := rawPtrPerm localDecls layouts mutability targetIdx
    let entry : BorrowEntry :=
      { tag := s.memory.nextTag
        targetLocal := targetIdx
        targetProjection := .nil
        perm := perm }
    evalRvalue s.frame.locals (.rawPtr mutability ⟨targetIdx, .nil⟩) s.memory localDecls layouts =
      .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)
        s.frame.locals
        { s.memory with
          borrows := .cons entry s.memory.borrows
          nextTag := s.memory.nextTag + 1 } := by
  intro perm entry
  cases slot with
  | dead => exact absurd rfl hlive
  | uninit =>
    unfold evalRvalue
    dsimp only []
    rw [hslot]
    rfl
  | init v =>
    unfold evalRvalue
    dsimp only []
    rw [hslot]
    rfl

/-- Anneal's `evalRvalue (.rawPtr mutability ⟨targetIdx, .nil⟩)` on a `.dead` local
fails with `.ub`. -/
theorem evalRvalue_rawPtr_dead_eq
    (s : MachineState) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (mutability : Mutability) (targetIdx : Local)
    (hdead : get? s.frame.locals targetIdx = some .dead) :
    evalRvalue s.frame.locals (.rawPtr mutability ⟨targetIdx, .nil⟩) s.memory localDecls layouts =
      .ub := by
  unfold evalRvalue
  dsimp only []
  rw [hdead]

/-! ### Allocator and type premises for moving a local into memory -/

/-- Well-formedness of `lean-miri`'s allocation-id supply under which
`MemoryState.reserveAllocId` issues `nextAllocId` (the premises of
`Miri.Memory.MemoryState.reserve_of_highWater`), together with the bound
`nextAllocId < 2^32` under which the base address `annealStackBaseAddr id`
(`id <<< 32`) of the issued id neither wraps nor overlaps another stack
allocation.

These are facts about the `lean-miri` memory, not about the statement being
executed: `MemoryState.empty` satisfies them (`AllocIdSupplyReady.empty`), and
they fail only once `2^32 - 1` allocation ids have been issued. -/
structure AllocIdSupplyReady (mem : AnnealMemory) : Prop where
  /-- The id supply is not exhausted. -/
  available : mem.idSupplyExhausted = false
  /-- The next id is a valid (non-zero) `AllocId`. -/
  nonzero : mem.nextAllocId ≠ 0
  /-- The optional source-id world is not exhausted. -/
  sourceAvailable : mem.sourceAllocIdWorldActive = true → mem.sourceAllocIdExhausted = false
  /-- The optional source-id world has a non-zero next id. -/
  sourceNonzero : mem.sourceAllocIdWorldActive = true → mem.sourceAllocIdNext ≠ 0
  /-- Every issued id lies below the high-water mark. -/
  issued : ∀ id ∈ mem.issuedIds, id.value.toNat < mem.nextAllocId.toNat
  /-- Every live allocation id lies below the high-water mark. -/
  live : ∀ row ∈ mem.live, row.1.value.toNat < mem.nextAllocId.toNat
  /-- Every global allocation id lies below the high-water mark. -/
  global : ∀ row ∈ mem.globals, row.allocId.value.toNat < mem.nextAllocId.toNat
  /-- Every dead allocation id lies below the high-water mark. -/
  dead : ∀ row ∈ mem.dead, row.allocId.value.toNat < mem.nextAllocId.toNat
  /-- The next id leaves room for its `id <<< 32` base address. -/
  below_2pow32 : mem.nextAllocId.toNat < 2 ^ 32

namespace AllocIdSupplyReady

/-- `reserveAllocId` issues `nextAllocId`. -/
theorem reserve_eq {mem : AnnealMemory} (h : AllocIdSupplyReady mem) :
    ∃ mem', mem.reserveAllocId = (mem', .ok ⟨mem.nextAllocId, h.nonzero⟩) :=
  Miri.Memory.MemoryState.reserve_of_highWater mem h.available h.nonzero h.sourceAvailable
    h.sourceNonzero h.issued h.live h.global h.dead

/-- The empty `lean-miri` memory is ready to issue allocation ids. -/
theorem empty : AllocIdSupplyReady (Miri.Memory.MemoryState.empty : AnnealMemory) where
  available := rfl
  nonzero := by decide
  sourceAvailable := by decide
  sourceNonzero := by decide
  issued := by decide
  live := by decide
  global := by decide
  dead := by decide
  below_2pow32 := by decide

end AllocIdSupplyReady

/-- The layout of a primitive scalar type (`bool`, `char`, or an integer type)
is sized, and `Allocation.tryNew` creates a fresh zeroed allocation for it. -/
theorem IsPrimScalarTy.layout_ok {ty : Ty} {layouts : LayoutTable} (h : IsPrimScalarTy ty) :
    (translateTy ty layouts).layout.isSized = true ∧
    ∃ allocation : Miri.Memory.Allocation AnnealProv Unit,
      Miri.Memory.Allocation.tryNew (translateTy ty layouts).layout.size
        (translateTy ty layouts).layout.align.abi .Uninit annealZeroedStorage = .ok allocation := by
  rcases h with h | h | ⟨it, h⟩ | ⟨ut, h⟩
  · simp only [translateTy, h]
    exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 1 rfl rfl).imp
      fun _ h => h.1⟩
  · simp only [translateTy, h]
    exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 4 rfl rfl).imp
      fun _ h => h.1⟩
  · cases it <;> simp only [translateTy, h]
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 1 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 2 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 4 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 8 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 16 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 8 rfl rfl).imp
        fun _ h => h.1⟩
  · cases ut <;> simp only [translateTy, h]
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 1 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 2 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 4 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 8 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 16 rfl rfl).imp
        fun _ h => h.1⟩
    · exact ⟨rfl, (Miri.Memory.Allocation.tryNew_replicate_full _ _ 8 rfl rfl).imp
        fun _ h => h.1⟩

/-! ### Forward evaluation of `forceAllocation` on an immediate local -/

/-- `annealPlaceHooks.allocateStack` succeeds once `Allocation.tryNew` and
`reserveAllocId` do, returning `stackAllocPlace id`. -/
theorem annealPlaceHooks_allocateStack_ok {ld : List LocalDecl} {ly : LayoutTable}
    {stk : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mach : AnnealMachine} {layout : Miri.Interpreter.LocalLayout}
    {allocation : Miri.Memory.Allocation AnnealProv Unit} {mem' : AnnealMemory}
    {id : Miri.Memory.AllocId}
    (htry : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      annealZeroedStorage = .ok allocation)
    (hres : mach.memory.reserveAllocId = (mem', .ok id)) :
    (annealPlaceHooks ld ly).allocateStack () layout ⟨stk, mach⟩ =
      .ok ⟨stackAllocPlace id, layout⟩
        ⟨stk, stackAllocMachine mach mem' id (allocation.withExtra none)⟩ := by
  simp only [annealPlaceHooks, htry, hres, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set, pure, EStateM.pure]
  rfl

/-- `annealPlaceHooks.writeMemoryNoValidate` of a scalar into the fresh
allocation `id` stores the result of `Allocation.writeScalar` at offset `0`. -/
theorem annealPlaceHooks_writeMemoryNoValidate_ok {ld : List LocalDecl} {ly : LayoutTable}
    {stk : Miri.Interpreter.Stack AnnealProv Miri.Interpreter.LocalLayout Unit}
    {mach : AnnealMachine} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {a0 alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {layout : Miri.Interpreter.LocalLayout} {sc : Miri.Memory.Scalar AnnealProv}
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc a0 = .ok () alloc') :
    (annealPlaceHooks ld ly).writeMemoryNoValidate () (.scalar sc) ⟨stackAllocPlace id, layout⟩
        ⟨stk, stackAllocMachine mach mem' id a0⟩ =
      .ok () ⟨stk, stackAllocMachine mach mem' id alloc'⟩ := by
  have hbase := lookupBaseAddr_stackAllocMachine_self mach mem' id a0
  have hidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := a0 } : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive : (stackAllocMachine mach mem' id a0).memory.live =
      mem'.live.push (id, ⟨.stack, a0⟩) := rfl
  have hoff : Miri.ABI.Size.ofBytes
      ((Miri.ABI.Size.ofBytes (annealStackBaseAddr id)).bytes - annealStackBaseAddr id) =
      Miri.ABI.Size.ZERO := by
    simp [Miri.ABI.Size.ofBytes, Miri.ABI.Size.ZERO]
  simp only [annealPlaceHooks]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, stackAllocPlace,
    Option.bind, Miri.Memory.Provenance.getAllocId, hbase, hlive, hidx,
    Array.getElem?_push_size, hoff, hw, pure, EStateM.pure, set, MonadStateOf.set, EStateM.set,
    array_push_set!_size]
  rfl

/-- Forward evaluation of `Miri.Interpreter.forceAllocation` under
`annealPlaceHooks` on a live immediate local whose layout is already cached:
it reserves `id`, creates the fresh stack allocation `alloc'` (holding the
local's scalar, if it has one), and makes the local memory-backed at
`stackAllocPlace id`, leaving every other local unchanged. -/
theorem forceAllocation_promote_eq
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} {decl : LocalDecl} (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < tf.locals.size)
    (hlay : (tf.locals[idx]'hlt).layout = some (translateTy decl.ty body.layouts))
    {value : Miri.Interpreter.Immediate AnnealProv}
    (hval : (tf.locals[idx]'hlt).value = .live (.immediate value))
    (hsized : (translateTy decl.ty body.layouts).layout.isSized = true)
    {allocation : Miri.Memory.Allocation AnnealProv Unit}
    (htry : Miri.Memory.Allocation.tryNew (translateTy decl.ty body.layouts).layout.size
      (translateTy decl.ty body.layouts).layout.align.abi .Uninit annealZeroedStorage =
        .ok allocation)
    {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id))
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hfill : (value = .uninit ∧ alloc' = allocation.withExtra none) ∨
      ∃ sc, value = .scalar sc ∧
        Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc (allocation.withExtra none) =
          .ok () alloc') :
    Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) ()
        ⟨.local 0 idx none tf.localsIdentity, translateTy decl.ty body.layouts⟩ m =
      .ok ⟨stackAllocPlace id, translateTy decl.ty body.layouts⟩
        { stack := ⟨#[{ tf with
            locals := tf.locals.set idx
              { tf.locals[idx]'hlt with value := .live (.indirect (stackAllocPlace id)) } hlt }]⟩
          machine := stackAllocMachine m.machine mem' id alloc' } := by
  rcases m with ⟨⟨frames⟩, mach⟩
  dsimp only at hframes hres ⊢
  subst hframes
  have hcache : ∀ l, (tf.locals[idx]'hlt).layout = some l →
      l = translateTy decl.ty body.layouts := by
    intro l h; rw [hlay] at h; exact (Option.some.inj h).symm
  have hgo : tf.getLocalOperand idx = .ok (.immediate value) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hval, bind, Except.bind, pure, Except.pure, Except.mapError]
  have hpl := placeLayoutOfLocal_eq (m := ⟨⟨#[tf]⟩, mach⟩) rfl hlt hdecl hcache
  rw [cacheFrameLocalLayout_of_cached tf hlt hlay] at hpl
  have hfresh := (reserveAllocId_ok_live hres).2
  rw [← (reserveAllocId_ok_live hres).1] at hfresh
  unfold Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
    bind, EStateM.bind, annealPlaceHooks_frameIndex_eq (m := ⟨⟨#[tf]⟩, mach⟩) rfl]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
    annealPlaceHooks_getFrame_eq (m := ⟨⟨#[tf]⟩, mach⟩) rfl]
  rw [hgo, Miri.Interpreter.stackLift_ok]
  simp only [pure, EStateM.pure]
  rw [EStateM.bind_apply_ok hpl]
  simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [EStateM.bind_apply_ok (annealPlaceHooks_allocateStack_ok htry hres)]
  rcases hfill with ⟨rfl, rfl⟩ | ⟨sc, rfl, hw⟩
  · simp only [EStateM.bind, pure, EStateM.pure, annealPlaceHooks_afterLocalMovedToMemory_eq,
      annealPlaceHooks_getFrame_mk, frame_setLocalOperand_live hlt hval,
      Miri.Interpreter.stackLift_ok, annealPlaceHooks_setFrame_mk]
  · dsimp only
    rw [EStateM.bind_apply_ok (annealPlaceHooks_writeMemoryNoValidate_ok hfresh hw)]
    simp only [EStateM.bind, pure, EStateM.pure, annealPlaceHooks_afterLocalMovedToMemory_eq,
      annealPlaceHooks_getFrame_mk, frame_setLocalOperand_live hlt hval,
      Miri.Interpreter.stackLift_ok, annealPlaceHooks_setFrame_mk]

/-! ### The `RawPtr` arm of `evalRvalueIntoPlace` under `annealRvalueHooks` -/

/-- `evalRvalueIntoPlace` of `Rvalue.RawPtr` under `annealRvalueHooks`, once the
destination and source places are evaluated and `annealForceAllocation` moves
the source into memory: `MemPlace.toRef` turns the memory place into a pointer
immediate and `annealWriteImmediate` stores it in the destination.
`annealRvalueHooks.retagPtrValue` returns `none`, so the pointer is written
unchanged; Tree Borrows retagging is outside this fragment. -/
theorem evalRvalueIntoPlace_rawPtr_ok
    {ld : List LocalDecl} {ly : LayoutTable} {kind : Miri.MIR.RawPtrKind}
    (hkind : kind ≠ .FakeForPtrMetadata)
    {dst src : Miri.MIR.Place} {m m₁ m₂ m₃ : AnnealStepState}
    {dest srcPlace : Miri.Interpreter.RuntimePlace AnnealProv}
    {mp : Miri.Interpreter.MemPlace AnnealProv} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hdst : annealEvalPlace ld ly dst m = .ok dest m₁)
    (hsrc : annealEvalPlace ld ly src m₁ = .ok srcPlace m₂)
    (hforce : annealForceAllocation ld ly srcPlace m₂ = .ok mp m₃)
    (href : mp.toRef annealTargetDataLayout = .ok imm) :
    Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks ld ly) () (.RawPtr kind src) dst m =
      annealWriteImmediate imm dest m₃ := by
  have hkind' : (kind != .FakeForPtrMetadata) = true := by simpa using hkind
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  simp only [bind, EStateM.bind, hdst, pure, EStateM.pure, hsrc, hforce, href, hkind',
    Bool.not_false, Bool.true_and, ↓reduceIte, Option.getD_none]

/-- `evalRvalueIntoPlace` of `Rvalue.RawPtr` under `annealRvalueHooks` fails
with the error, and keeps the state, of a failing `annealForceAllocation`. -/
theorem evalRvalueIntoPlace_rawPtr_force_error
    {ld : List LocalDecl} {ly : LayoutTable} {kind : Miri.MIR.RawPtrKind}
    {dst src : Miri.MIR.Place} {m m₁ m₂ m₃ : AnnealStepState}
    {dest srcPlace : Miri.Interpreter.RuntimePlace AnnealProv}
    {err : Miri.Interpreter.StepError}
    (hdst : annealEvalPlace ld ly dst m = .ok dest m₁)
    (hsrc : annealEvalPlace ld ly src m₁ = .ok srcPlace m₂)
    (hforce : annealForceAllocation ld ly srcPlace m₂ = .error err m₃) :
    Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks ld ly) () (.RawPtr kind src) dst m =
      .error err m₃ := by
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  simp only [bind, EStateM.bind, hdst, pure, EStateM.pure, hsrc, hforce]

/-- `annealForceAllocation` of a dead local reports undefined behavior and
keeps the state: `forceAllocation`'s `StackError.localExpectedLive` is
rustc's `err_ub!(DeadLocal)`. -/
theorem annealForceAllocation_dead_eq
    {ld : List LocalDecl} {ly : LayoutTable} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} (hlt : idx < tf.locals.size)
    (hdead : (tf.locals[idx]'hlt).value = .dead)
    (lay : Miri.Interpreter.LocalLayout) :
    annealForceAllocation ld ly ⟨.local 0 idx none tf.localsIdentity, lay⟩ m =
      .error (.undefinedBehavior "address of dead local") m := by
  have hgo : tf.getLocalOperand idx = .error (.localExpectedLive idx) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hdead, bind, Except.bind, pure, Except.pure, Except.mapError]
  unfold annealForceAllocation Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
    bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure, annealPlaceHooks_getFrame_eq hframes,
    hgo]
  rfl

/-- `MemPlace.toRef` of `stackAllocPlace id` is the thin pointer scalar to the
base of `id` with tag `BorTag.one`. -/
theorem stackAllocPlace_toRef (id : Miri.Memory.AllocId) :
    (stackAllocPlace id).toRef annealTargetDataLayout =
      .ok (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr id), .concrete id Miri.Memory.BorTag.one⟩)) :=
  rfl

/-! ### Layout memoization preserves `StateRel` -/

/-- `StateRel` survives memoizing a local's declared layout in the root frame,
as `annealEvalPlace` does. -/
theorem StateRel.cache_layout {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} {decl : LocalDecl} (hdecl : get? body.localDecls idx = some decl)
    (hlt : idx < tf.locals.size) :
    StateRel body s
      { m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt
          (translateTy decl.ty body.layouts)]⟩ } := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₀
  injection h₀ with htf
  subst htf
  refine StateRel.mk _ rfl hretCont hretPlace (hfr.cache_local_layout hdecl hlt) hcal hstack hbor
    hprot hcaller ?_
  apply MemoryAllocDisjoint.mono_layout hdisj
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

/-- `FrameRelLM3_1` survives advancing both machines to the next statement. -/
theorem FrameRelLM3_1.advance
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : FrameRelLM3_1 body mach allocMap af mf) :
    FrameRelLM3_1 body mach allocMap
      { af with stmtIdx := Nat.add af.stmtIdx 1 }
      { mf with location := .mir ⟨af.blockIdx, af.stmtIdx + 1⟩ } where
  body_eq := h.body_eq
  location_eq := rfl
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel := h.locals_rel

/-! ### Step simulation for `_d = &raw (const|mut) _t` -/

/-- The borrow entry that Anneal's `Rvalue.rawPtr` pushes for
`&raw (const|mut) _target` at tag `tag`. -/
def rawPtrBorrowEntry (localDecls : List LocalDecl) (layouts : LayoutTable)
    (mutability : Mutability) (targetIdx : Local) (tag : Nat) : BorrowEntry :=
  { tag := tag
    targetLocal := targetIdx
    targetProjection := .nil
    perm := rawPtrPerm localDecls layouts mutability targetIdx }

/-- The `allocMap` entry that records `&raw (const|mut) _target` at tag `tag`
as pointing into the `lean-miri` allocation `allocId`. -/
def rawPtrAllocMapEntry (localDecls : List LocalDecl) (layouts : LayoutTable)
    (mutability : Mutability) (targetIdx : Local) (tag : Nat)
    (allocId : Miri.Memory.AllocId) : AllocMapEntry :=
  { tag := tag
    localIdx := targetIdx
    allocId := allocId
    perm := rawPtrPerm localDecls layouts mutability targetIdx }

/-- **`step_rawPtr_addrOf_simulation` (`LM-3.1` Deliverable 1)**: one real step
of `_d = &raw (const|mut) _t` in both machines, from a pointer-free state
(`StateRel`, in particular no borrows) whose `_t` is an immediate local of
primitive scalar type.

Anneal's `stepMirFn` and `lean-miri`'s `Miri.Interpreter.Step.step` under
`annealStepHooks` (whose `RawPtr` arm runs `annealForceAllocation` and
`MemPlace.toRef`) are related by `StepRelLM3_1`:

* If `_t` is live, `forceAllocation` moves it into the fresh allocation
  `id = nextAllocId` (`forceAllocation_promote_eq`, after which
  `forceAllocation_preserves_StateRel` relates every local again), Anneal pushes
  the root borrow with tag `nextTag`, and both machines store the new pointer in
  `_d`. The resulting states are related by `StateRelLM3_1` under the single
  `allocMap` entry `(nextTag, _t, id, perm)`: `_d` is a `PtrRel`-related raw
  pointer to offset `0` of `id`, and `_t` is memory-backed at
  `stackAllocPlace id`. If `_d` is dead, both machines instead report undefined
  behavior.
* If `_t` is dead, both machines report undefined behavior.

No outcome of either machine is assumed. `hsupply` is a well-formedness fact
about `lean-miri`'s allocation-id supply that `MemoryState.empty` satisfies. -/
theorem step_rawPtr_addrOf_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : LocalDecl} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr mutability pointeeKind)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    StepRelLM3_1 body m
      [rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩]
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller, hdisj⟩ :=
    id hstate
  obtain ⟨himm_dst, himm_tgt⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  -- `annealEvalPlace` memoizes the layouts of `_d` and then `_t`.
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.layout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRel body m.machine s.frame tfa := hfr.cache_local_layout hdecl_dst hlt_d
  have hstate_a : StateRel body s { m with stack := ⟨#[tfa]⟩ } :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_t, mls_t, hlt_af_t, hlt_t, hslot_t, hmls_t, hmls_t_eq, hloc_t⟩ :=
    hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.layout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hstate_b : StateRel body s { m with stack := ⟨#[tfb]⟩ } :=
    hstate_a.cache_layout rfl hdecl_tgt hlt_t
  have hkind : translateRawPtrKind mutability ≠ .FakeForPtrMetadata := by
    cases mutability <;> decide
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.RawPtr (translateRawPtrKind mutability) ⟨targetIdx, #[]⟩) ⟨dstIdx, #[]⟩) m := rfl
  have hval_tb : (tfb.locals[targetIdx]'(by rw [cacheFrameLocalLayout_size]; exact hlt_t)).value =
      mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  cases hloc_t with
  | indirect _ mp _ _ _ _ =>
    exact absurd rfl (himm_tgt.cache_layout hlt_d _ _ hmls_t mp)
  | dead cl _ =>
    -- `_t` is dead: both machines report undefined behavior.
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt
      dsimp only
      rw [evalRvalue_rawPtr_dead_eq s body.localDecls body.layouts mutability targetIdx hslot_t]
    have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl
      (by rw [cacheFrameLocalLayout_size]; exact hlt_t) hval_tb
      (translateTy targetDecl.ty body.layouts)
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [evalRvalueIntoPlace_rawPtr_force_error hdst_eval htgt_eval hforce]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  | immediate slot imm cl hcl hval =>
    -- `_t` is live: `forceAllocation` moves it into the fresh allocation `id`.
    have hslot_ne_dead : slot_t ≠ .dead := by
      rcases hval with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> simp
    have hlt_tb : targetIdx < tfb.locals.size := by
      rw [cacheFrameLocalLayout_size]; exact hlt_t
    have hlay_tb : (tfb.locals[targetIdx]'hlt_tb).layout =
        some (translateTy targetDecl.ty body.layouts) := by
      simp [tfb, cacheFrameLocalLayout]
    obtain ⟨hsized, allocation, htry⟩ := htgt_ty.layout_ok (layouts := body.layouts)
    obtain ⟨mem', hres⟩ := hsupply.reserve_eq
    obtain ⟨alloc', hfill⟩ : ∃ alloc' : Miri.Memory.Allocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree),
        (imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
        ∃ sc, imm = .scalar sc ∧
          Miri.Memory.Allocation.writeScalar annealTargetDataLayout
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc (allocation.withExtra none) =
            .ok () alloc' := by
      rcases hval with ⟨_, rfl⟩ | ⟨v, _, himmRel⟩
      · exact ⟨_, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨sc, msc, _, rfl, hrel, hsz, _, _⟩ := himmRel.of_primitive_scalar htgt_ty
        have htry' : Miri.Memory.Allocation.tryNew (translateSizeBytes sc.sizeBytes)
            (translateTy targetDecl.ty body.layouts).layout.align.abi .Uninit
            annealZeroedStorage = .ok allocation := by
          rw [← hsz]; exact htry
        obtain ⟨alloc'', hw, -⟩ := freshStackAlloc_writeScalar_readScalar hrel htry'
        exact ⟨alloc'', Or.inr ⟨_, rfl, hw⟩⟩
    have hforce₀ := forceAllocation_promote_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hdecl_tgt
      hlt_tb hlay_tb hval_tb hsized htry hres hfill
    -- LM-1.4's coalescing theorem relates every local of the new state again.
    obtain ⟨hstate_c, -⟩ := forceAllocation_preserves_StateRel hstate_b hforce₀
    obtain ⟨tfc, hframes_c, -, -, hfrc, -, -, -, -, -, hdisj_c⟩ := hstate_c
    injection hframes_c with hfc₁
    injection hfc₁ with hfc₂
    subst hfc₂
    have hforce : annealForceAllocation body.localDecls body.layouts
        ⟨.local 0 targetIdx none tfa.localsIdentity, translateTy targetDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok (stackAllocPlace ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)
          { stack := ⟨#[{ tfb with
              locals := tfb.locals.set targetIdx
                { tfb.locals[targetIdx]'hlt_tb with
                  value := .live (.indirect
                    (stackAllocPlace ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)) }
                hlt_tb }]⟩
            machine := stackAllocMachine m.machine mem'
              ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ alloc' } := by
      unfold annealForceAllocation
      erw [hforce₀]
    have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval htgt_eval hforce
      (stackAllocPlace_toRef ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)
    have hdc_eq₀ : ({ tfb with
        locals := tfb.locals.set targetIdx
          { tfb.locals[targetIdx]'hlt_tb with
            value := .live (.indirect
              (stackAllocPlace ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)) }
          hlt_tb } : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[dstIdx]? =
        some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
      simp only [tfb, tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_ne _ (Ne.symm hne),
        Array.getElem?_set_self, hmls_d_eq]
    have htgt_c : ({ tfb with
        locals := tfb.locals.set targetIdx
          { tfb.locals[targetIdx]'hlt_tb with
            value := .live (.indirect
              (stackAllocPlace ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)) }
          hlt_tb } : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[targetIdx]? =
        some ⟨.live (.indirect (stackAllocPlace ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)),
          some (translateTy targetDecl.ty body.layouts)⟩ := by
      simp only [Array.getElem?_set_self]
      rw [← hlay_tb]
    generalize htfc : ({ tfb with
        locals := tfb.locals.set targetIdx
          { tfb.locals[targetIdx]'hlt_tb with
            value := .live (.indirect
              (stackAllocPlace ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)) }
          hlt_tb } : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) = tfc
      at hrv hfrc hdisj_c hdc_eq₀ htgt_c
    generalize hmachc : stackAllocMachine m.machine mem'
      ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ alloc' = machc at hrv hfrc
    -- `_d` is untouched by the promotion of `_t`.
    have hdc_eq := hdc_eq₀
    obtain ⟨hlt_dc, -⟩ := Array.getElem?_eq_some_iff.mp hdc_eq
    cases hloc_d with
    | indirect _ mp _ _ _ _ =>
      exact absurd rfl (himm_dst _ hmls_d mp)
    | dead cld _ =>
      -- `_d` is dead: both machines report undefined behavior at the write.
      have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
      have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only
        rw [evalRvalue_rawPtr_live_eq s body.localDecls body.layouts mutability targetIdx slot_t
          hslot_t hslot_ne_dead]
        dsimp only
        rw [hslot_d]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
          (⟨⟨#[tfc]⟩, machc⟩, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [hrv, annealWriteImmediate_dead (m := ⟨⟨#[tfc]⟩, machc⟩) rfl hget_dc]
      rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    | immediate _ oldImm cld _ hvald =>
      -- `_d` is live: both machines store the new pointer in `_d` and step.
      have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩),
            .concrete ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ Miri.Memory.BorTag.one⟩))
        (m := ⟨⟨#[tfc]⟩, machc⟩) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
          ({ (⟨⟨#[tfc]⟩, machc⟩ : AnnealStepState) with
              stack := ⟨#[{ tfc with
                locals := tfc.locals.set dstIdx
                  { tfc.locals[dstIdx]'hlt_dc with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr
                            ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩),
                          .concrete ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
                            Miri.Memory.BorTag.one⟩))) }
                  hlt_dc }]⟩ },
            .ok ()) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [hrv, hw]
      have hloc_c : tfc.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfrc.location_eq
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hloc_c]
      have hslot_d_ne : slot_d ≠ .dead := by
        rcases hvald with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> simp
      have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
          body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s
              (s.frame.locals.set dstIdx (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
              { s.memory with
                borrows :=
                  [rawPtrBorrowEntry body.localDecls body.layouts mutability targetIdx
                    s.memory.nextTag]
                nextTag := s.memory.nextTag + 1 }) := by
        unfold evalStmt
        dsimp only
        rw [evalRvalue_rawPtr_live_eq s body.localDecls body.layouts mutability targetIdx slot_t
          hslot_t hslot_ne_dead]
        dsimp only
        rw [hslot_d]
        have hbeq : Nat.beq targetIdx dstIdx = false := by
          cases h : Nat.beq targetIdx dstIdx
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h).symm hne
        rcases hvald with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;>
        · simp only [set?_eq_some_set hlt_af_d, hprot, hbor, invalidateConflictingBorrows_cons,
            invalidateConflictingBorrows_nil, updateBorrowPerm, hbeq, rawPtrBorrowEntry]
      rw [ha]
      apply StepRelLM3_1.step
      have hretCont_c : tfc.returnContinuation = .stop false := by
        rw [← htfc]; exact hretCont
      have hretPlace_c : ∃ retLay,
          tfc.returnPlace = .frameLocal 0 0 none retLay tfc.localsIdentity := by
        rw [← htfc]; exact hretPlace
      have hptr := PtrRel.of_stackAllocPlace
        (allocMap := [rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx
          s.memory.nextTag ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩])
        (e := rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx
          s.memory.nextTag ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩)
        (List.Mem.head []) hsupply.below_2pow32
      have hdc' : tfc.locals[dstIdx]'hlt_dc =
          ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
        have h := Array.getElem?_eq_getElem hlt_dc
        rw [hdc_eq] at h
        exact (Option.some.inj h).symm
      have hnew : LocalRelLM3_1 machc
          [rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx
            s.memory.nextTag ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩]
          dstDecl body.layouts (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
          { tfc.locals[dstIdx]'hlt_dc with
            value := .live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr
                    ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩),
                  .concrete ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
                    Miri.Memory.BorTag.one⟩))) } := by
        rw [hdc']
        exact .rawPtr _ _ _ mutability pointeeKind (fun l hl => (Option.some.inj hl).symm)
          hdst_ty hptr
      have hfrd := (hfrc.toLM3_1 [rawPtrAllocMapEntry body.localDecls body.layouts mutability
        targetIdx s.memory.nextTag ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩]).update_local
        hdecl_dst _ _ hnew
      refine .mk _ rfl hretCont_c hretPlace_c hfrd.advance hcal hstack hprot hcaller ?_ ?_ ?_
      · -- The only borrow is the new root borrow.
        intro b hb
        have hb' : b = rawPtrBorrowEntry body.localDecls body.layouts mutability targetIdx
            s.memory.nextTag := by
          simpa [advanceStmt] using hb
        subst hb'
        exact ⟨_, List.Mem.head _, rfl⟩
      · refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro e₁ h₁ e₂ h₂ _
          rw [List.mem_singleton] at h₁ h₂
          rw [h₁, h₂]
        · intro e₁ h₁ e₂ h₂ _
          rw [List.mem_singleton] at h₁ h₂
          rw [h₁, h₂]
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          refine ⟨hsupply.below_2pow32, ?_⟩
          show machc.lookupBaseAddr _ = _
          rw [← hmachc]
          exact lookupBaseAddr_stackAllocMachine_self _ _ _ _
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          refine ⟨Nat.lt_succ_self _, ?_⟩
          simp [advanceStmt, lookupBorrow, rawPtrBorrowEntry, rawPtrAllocMapEntry]
        · intro topFrame htop e he
          rw [List.mem_singleton] at he
          subst he
          injection htop with h₁
          injection h₁ with h₂
          subst h₂
          refine ⟨fun _ _ _ => ⟨some (translateTy targetDecl.ty body.layouts), ?_⟩,
            fun hdead => ?_⟩
          · show (tfc.locals.set dstIdx _ hlt_dc)[targetIdx]? = _
            rw [Array.getElem?_set_ne _ hne]
            exact htgt_c
          · exfalso
            have h' : get? (s.frame.locals.set dstIdx
                (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) targetIdx =
                some .dead := hdead
            rw [get?_eq_getElem?, List.getElem?_set_ne hne, ← get?_eq_getElem?, hslot_t] at h'
            exact hslot_ne_dead (Option.some.inj h')
      · apply MemoryAllocDisjoint.mono_immediate hdisj_c
        intro k
        by_cases hk : k = dstIdx
        · subst hk
          right
          refine ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr
                  ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩),
                .concrete ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
                  Miri.Memory.BorTag.one⟩),
            some (translateTy dstDecl.ty body.layouts), ?_⟩
          show (tfc.locals.set k _ hlt_dc)[k]? = _
          rw [Array.getElem?_set_self, hdc']
        · left
          show (tfc.locals.set dstIdx _ hlt_dc)[k]? = _
          rw [Array.getElem?_set_ne _ (Ne.symm hk)]

/-! ## 4. Deliverable 2: `PlaceElem.Deref` (`*ptr`) Reads, Writes, and UB Simulation -/

/-- `8 < 2 ^ 63` in `Int`, proved via `Nat` comparison (`Int.ofNat_lt.mpr`). -/
theorem eight_lt_two_pow_63 : ((8 : Nat) : Int) < 2 ^ 63 :=
  Int.ofNat_lt.mpr (by decide)

/-- Valid in-bounds aligned deref read of an initialized scalar local succeeds in
both Anneal (`evalOperand`) and `lean-miri` (`evalDerefReadScalarMiri`). -/
theorem evalProjection_deref_read_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hmap : AllocMapRel body s m allocMap)
    (ptrLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (pointeeTy : Ty)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hsz8 : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8)
    (halign8 : (translateTy pointeeTy body.layouts).layout.align.abi = Miri.ABI.Align.EIGHT)
    (e : AllocMapEntry) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (he : e ∈ allocMap)
    (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled)
    (hmptr : mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
      .concrete e.allocId Miri.Memory.BorTag.one⟩)
    (htarget_slot : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hfind : m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hsz_alloc : localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8)
    (hread_sc : localAlloc.allocation.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) false =
      .ok (.fromScalarInt msc)) :
    evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
      .ok (.scalar sc) s.frame.locals ∧
    evalDerefReadScalarMiri m.machine mptr
      (translateTy pointeeTy body.layouts).layout.size
      (translateTy pointeeTy body.layouts).layout.align.abi =
      .ok (.fromScalarInt msc) := by
  have hbor := (hmap.borrow_sync e he).2
  have hanneal :
      evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
        .ok (.scalar sc) s.frame.locals := by
    unfold evalOperand readProjectedValue
    dsimp only []
    rw [hptr_slot]
    dsimp only []
    rw [← htag, hbor]
    dsimp only []
    cases hperm_c : e.perm
    · rw [htarget_slot]
    · rw [htarget_slot]
    · rw [htarget_slot]
    · exact absurd hperm_c hperm
  refine ⟨hanneal, ?_⟩
  rw [hsz8, halign8, hmptr]
  obtain ⟨hid_lt, hbase⟩ := hmap.base_addr_valid e he
  have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
  unfold evalDerefReadScalarMiri
  dsimp only []
  rw [hsz8_nat]
  have hchk := checkAndDerefPtr_live_inbounds_ok
    e.allocId Miri.Memory.BorTag.one 0 8 localAlloc .memoryAccess
    hid_lt (by show 0 < 2 ^ 32; decide) hbase hfind (by decide) eight_lt_two_pow_63
    (by rw [hsz_alloc]; decide)
  have hadd0 : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId :=
    UInt64.add_zero _
  rw [hadd0] at hchk
  rw [hchk]
  dsimp only []
  have hal : (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId)).isAligned
      Miri.ABI.Align.EIGHT = .ok true := by
    have h0 := size_isAligned_eight_of_aligned e.allocId 0
      hid_lt (by show 0 < 2 ^ 32; decide) rfl
    simpa using h0
  rw [hal]
  dsimp only []
  rw [hfind]
  dsimp only []
  have hzero_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hzero_sz, hread_sc]

/-- Valid in-bounds aligned deref write of a scalar to a live local succeeds in
both Anneal (`writePlaceValue`) and `lean-miri` (`evalDerefWriteScalarMiri`). -/
theorem evalProjection_deref_write_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hmap : AllocMapRel body s m allocMap)
    (ptrLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (pointeeTy : Ty)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hsz8 : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8)
    (halign8 : (translateTy pointeeTy body.layouts).layout.align.abi = Miri.ABI.Align.EIGHT)
    (e : AllocMapEntry) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
    (oldSlot : LocalSlot) (locals' : List LocalSlot)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (he : e ∈ allocMap)
    (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active)
    (hmptr : mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
      .concrete e.allocId Miri.Memory.BorTag.one⟩)
    (htarget_slot : get? s.frame.locals e.localIdx = some oldSlot)
    (hold_live : oldSlot ≠ .dead)
    (hset : set? s.frame.locals e.localIdx (.init (.scalar sc)) = some locals')
    (hfind : m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hsz_alloc : localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8)
    (hwrite_sc : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
      (.fromScalarInt msc) localAlloc.allocation = .ok () alloc') :
    writePlaceValue s.frame.locals s.memory.borrows ⟨ptrLoc, .cons .deref .nil⟩ (.scalar sc) =
      .ok locals' ∧
    evalDerefWriteScalarMiri m.machine mptr
      (translateTy pointeeTy body.layouts).layout.size
      (translateTy pointeeTy body.layouts).layout.align.abi
      (.fromScalarInt msc) = .ok alloc' := by
  have hbor := (hmap.borrow_sync e he).2
  have hanneal :
      writePlaceValue s.frame.locals s.memory.borrows ⟨ptrLoc, .cons .deref .nil⟩ (.scalar sc) =
        .ok locals' := by
    unfold writePlaceValue
    dsimp only []
    rw [hptr_slot]
    dsimp only []
    rw [← htag, hbor, hperm]
    dsimp only []
    rw [htarget_slot]
    cases oldSlot with
    | dead => exact absurd rfl hold_live
    | uninit =>
      dsimp only []
      rw [hset]
    | init _ =>
      dsimp only []
      rw [hset]
  refine ⟨hanneal, ?_⟩
  rw [hsz8, halign8, hmptr]
  obtain ⟨hid_lt, hbase⟩ := hmap.base_addr_valid e he
  have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
  unfold evalDerefWriteScalarMiri
  dsimp only []
  rw [hsz8_nat]
  have hchk := checkAndDerefPtr_live_inbounds_ok
    e.allocId Miri.Memory.BorTag.one 0 8 localAlloc .memoryAccess
    hid_lt (by show 0 < 2 ^ 32; decide) hbase hfind (by decide) eight_lt_two_pow_63
    (by rw [hsz_alloc]; decide)
  have hadd0 : annealStackBaseAddr e.allocId + UInt64.ofNat 0 = annealStackBaseAddr e.allocId :=
    UInt64.add_zero _
  rw [hadd0] at hchk
  rw [hchk]
  dsimp only []
  have hal : (Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId)).isAligned
      Miri.ABI.Align.EIGHT = .ok true := by
    have h0 := size_isAligned_eight_of_aligned e.allocId 0
      hid_lt (by show 0 < 2 ^ 32; decide) rfl
    simpa using h0
  rw [hal]
  dsimp only []
  rw [hfind]
  dsimp only []
  have hzero_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  have hsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size = msc.size := rfl
  rw [hzero_sz, hsc_sz, hwrite_sc]

/-- Dangling / dead allocation deref UB (use-after-`StorageDead`). -/
theorem evalProjection_deref_deadAlloc_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (ptrLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (pointeeTy : Ty)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hsz8 : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8)
    (entry : BorrowEntry) (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (hbor : lookupBorrow s.memory.borrows ptrVal.tag = some entry)
    (hperm : entry.perm ≠ .disabled)
    (hdead : get? s.frame.locals entry.targetLocal = some .dead)
    (hmptr : mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
      .concrete allocId borTag⟩)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : ptrVal.offsetBytes < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hnot_live : m.machine.memory.live.find? (fun x => x.1 == allocId) = none) :
    evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub ∧
    ∃ msg, evalDerefReadScalarMiri m.machine mptr
      (translateTy pointeeTy body.layouts).layout.size
      (translateTy pointeeTy body.layouts).layout.align.abi =
      .error (.undefinedBehavior msg) := by
  refine ⟨?_, ?_⟩
  · unfold evalOperand
    dsimp only []
    rw [hptr_slot]
    dsimp only []
    rw [hbor]
    dsimp only []
    cases hperm_c : entry.perm
    · rw [hdead]
    · rw [hdead]
    · rw [hdead]
    · exact absurd hperm_c hperm
  · rw [hsz8, hmptr]
    have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
    unfold evalDerefReadScalarMiri
    dsimp only []
    rw [hsz8_nat]
    have hchk := checkAndDerefPtr_deadAlloc_err
      allocId borTag ptrVal.offsetBytes ((8 : Nat) : Int) .memoryAccess
      hid hoff hbase hnot_live (by decide) eight_lt_two_pow_63
    refine ⟨"pointer dereference check failed", ?_⟩
    rw [hchk]

/-- Out-of-bounds deref UB in Anneal and `lean-miri`. -/
theorem evalProjection_deref_oob_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (ptrLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (pointeeTy : Ty)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hsz8 : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8)
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hbor_none : lookupBorrow s.memory.borrows ptrVal.tag = none)
    (hglob_none : lookupGlobalAlloc s.memory.globals ptrVal.allocId = none)
    (hmptr : mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
      .concrete allocId borTag⟩)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : ptrVal.offsetBytes < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hoob : localAlloc.allocation.byteSize.bytes.toNat < ptrVal.offsetBytes + 8) :
    evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub ∧
    ∃ msg, evalDerefReadScalarMiri m.machine mptr
      (translateTy pointeeTy body.layouts).layout.size
      (translateTy pointeeTy body.layouts).layout.align.abi =
      .error (.undefinedBehavior msg) := by
  refine ⟨?_, ?_⟩
  · unfold evalOperand
    dsimp only []
    rw [hptr_slot]
    dsimp only []
    rw [hbor_none]
    dsimp only []
    rw [hglob_none]
  · rw [hsz8, hmptr]
    have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
    unfold evalDerefReadScalarMiri
    dsimp only []
    rw [hsz8_nat]
    have hchk := checkAndDerefPtr_live_oob_err
      allocId borTag ptrVal.offsetBytes 8 localAlloc .memoryAccess
      hid hoff hbase hlive (by decide) eight_lt_two_pow_63 hoob
    refine ⟨"pointer dereference check failed", ?_⟩
    rw [hchk]

/-- Misaligned deref UB in `lean-miri`. -/
theorem evalProjection_deref_misaligned_ub
    {body : CapturedMir} {m : AnnealStepState}
    (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (pointeeTy : Ty)
    (hsz8 : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8)
    (halign8 : (translateTy pointeeTy body.layouts).layout.align.abi = Miri.ABI.Align.EIGHT)
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hmptr : mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
      .concrete allocId borTag⟩)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : ptrVal.offsetBytes < 2 ^ 32)
    (hbase : m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hinbounds : ptrVal.offsetBytes + 8 ≤ localAlloc.allocation.byteSize.bytes.toNat)
    (hmis : ptrVal.offsetBytes % 8 ≠ 0) :
    ∃ msg, evalDerefReadScalarMiri m.machine mptr
      (translateTy pointeeTy body.layouts).layout.size
      (translateTy pointeeTy body.layouts).layout.align.abi =
      .error (.undefinedBehavior msg) := by
  rw [hsz8, halign8, hmptr]
  have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
  unfold evalDerefReadScalarMiri
  dsimp only []
  rw [hsz8_nat]
  have hchk := checkAndDerefPtr_live_inbounds_ok
    allocId borTag ptrVal.offsetBytes 8 localAlloc .memoryAccess
    hid hoff hbase hlive (by decide) eight_lt_two_pow_63 hinbounds
  have hal := size_isAligned_eight_of_misaligned allocId ptrVal.offsetBytes hid hoff hmis
  refine ⟨"alignment check failed on deref read", ?_⟩
  rw [hchk]
  dsimp only []
  rw [hal]

/-- **`evalProjection_deref_simulation` (`LM-3.1` Deliverable 2)**: the
dereference lemmas below, bundled. Every clause compares Anneal's
`evalOperand` / `writePlaceValue` with the stand-ins `evalDerefReadScalarMiri` /
`evalDerefWriteScalarMiri`, not with `Miri.Interpreter.Step.step`.

1. **Read and write of an 8-byte scalar local through its `allocMap` entry**:
   Anneal reads `.scalar sc` (or writes through an `.active` entry); the stand-in
   returns the `lean-miri` read or write result that the clause takes as a
   premise. The clauses fix `mptr` to the base of `e.allocId` rather than
   deriving it from `PtrRel` and `StateRelLM3_1`, and they do not relate `sc` to
   the `lean-miri` scalar.
2. **Dangling read**: Anneal's target local is `.dead` and `lean-miri`'s
   allocation is absent from `memory.live`; both report undefined behavior.
3. **Unknown tag**: Anneal finds neither a borrow nor a global for the tag, and
   the stand-in rejects a read past the end of a live allocation. The two
   pointers are not related by `PtrRel`; in particular this is not an
   out-of-bounds read through one pointer. Anneal's dereference of a tracked
   stack pointer ignores `offsetBytes`, so it does not report out-of-bounds
   reads at all (`WitLM3_1.wit_lm3_1_anneal_offset_deref_divergence`).
4. **Misaligned read**: the stand-in rejects a misaligned 8-byte read (no
   Anneal counterpart is stated). -/
theorem evalProjection_deref_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hmap : AllocMapRel body s m allocMap)
    (ptrLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (pointeeTy : Ty)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hsz8 : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8)
    (halign8 : (translateTy pointeeTy body.layouts).layout.align.abi = Miri.ABI.Align.EIGHT) :
    -- (1) Valid in-bounds aligned deref read of an initialized scalar local
    (∀ (e : AllocMapEntry) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind),
      e ∈ allocMap →
      e.tag = ptrVal.tag →
      e.perm ≠ .disabled →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ →
      get? s.frame.locals e.localIdx = some (.init (.scalar sc)) →
      m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
        some (e.allocId, localAlloc) →
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8 →
      localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) false =
        .ok (.fromScalarInt msc) →
      evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
        .ok (.scalar sc) s.frame.locals ∧
      evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .ok (.fromScalarInt msc)) ∧
    -- (2) Valid in-bounds aligned deref write of a scalar to a live local
    (∀ (e : AllocMapEntry) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
       (oldSlot : LocalSlot) (locals' : List LocalSlot)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind)
       (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      e ∈ allocMap →
      e.tag = ptrVal.tag →
      e.perm = .active →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ →
      get? s.frame.locals e.localIdx = some oldSlot →
      oldSlot ≠ .dead →
      set? s.frame.locals e.localIdx (.init (.scalar sc)) = some locals' →
      m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
        some (e.allocId, localAlloc) →
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8 →
      Miri.Memory.Allocation.writeScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO msc.size)
        (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' →
      writePlaceValue s.frame.locals s.memory.borrows ⟨ptrLoc, .cons .deref .nil⟩ (.scalar sc) =
        .ok locals' ∧
      evalDerefWriteScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi
        (.fromScalarInt msc) = .ok alloc') ∧
    -- (3) Dangling / dead allocation deref UB (use-after-StorageDead)
    (∀ (entry : BorrowEntry) (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag),
      lookupBorrow s.memory.borrows ptrVal.tag = some entry →
      entry.perm ≠ .disabled →
      get? s.frame.locals entry.targetLocal = some .dead →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete allocId borTag⟩ →
      allocId.value.toNat < 2 ^ 32 →
      ptrVal.offsetBytes < 2 ^ 32 →
      m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = none →
      evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub ∧
      ∃ msg, evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .error (.undefinedBehavior msg)) ∧
    -- (4) Out-of-bounds deref UB
    (∀ (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind),
      lookupBorrow s.memory.borrows ptrVal.tag = none →
      lookupGlobalAlloc s.memory.globals ptrVal.allocId = none →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete allocId borTag⟩ →
      allocId.value.toNat < 2 ^ 32 →
      ptrVal.offsetBytes < 2 ^ 32 →
      m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc) →
      localAlloc.allocation.byteSize.bytes.toNat < ptrVal.offsetBytes + 8 →
      evalOperand s.frame.locals (.copy ⟨ptrLoc, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub ∧
      ∃ msg, evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .error (.undefinedBehavior msg)) ∧
    -- (5) Misaligned deref UB
    (∀ (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
       (localAlloc :
         Miri.Memory.LocalAllocation
           AnnealProv
           (Option Miri.TreeBorrows.BorrowTree)
           Miri.Memory.MiriMemoryKind),
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
        .concrete allocId borTag⟩ →
      allocId.value.toNat < 2 ^ 32 →
      ptrVal.offsetBytes < 2 ^ 32 →
      m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) →
      m.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc) →
      ptrVal.offsetBytes + 8 ≤ localAlloc.allocation.byteSize.bytes.toNat →
      ptrVal.offsetBytes % 8 ≠ 0 →
      ∃ msg, evalDerefReadScalarMiri m.machine mptr
        (translateTy pointeeTy body.layouts).layout.size
        (translateTy pointeeTy body.layouts).layout.align.abi =
        .error (.undefinedBehavior msg)) :=
  ⟨evalProjection_deref_read_ok hmap ptrLoc ptrVal mptr pointeeTy hptr_slot hsz8 halign8,
   evalProjection_deref_write_ok hmap ptrLoc ptrVal mptr pointeeTy hptr_slot hsz8 halign8,
   evalProjection_deref_deadAlloc_ub ptrLoc ptrVal mptr pointeeTy hptr_slot hsz8,
   evalProjection_deref_oob_ub ptrLoc ptrVal mptr pointeeTy hptr_slot hsz8,
   evalProjection_deref_misaligned_ub ptrVal mptr pointeeTy hsz8 halign8⟩

/-! ## 5. Deliverable 3: `BinOp.Offset` (`inbounds` vs. `wrapping`) Simulation -/

/-- Anneal's `evalRvalue (.binaryOp .offset lhsOp rhsOp)` on a raw pointer `.ptr ptrVal 8`
and scalar offset `offsetSc` adds `offsetSc.bits` to `ptrVal.offsetBytes`. -/
theorem evalRvalue_binOp_offset_eq
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ptrLoc offLoc : Local) (ptrVal : ProvenancePtr) (offsetSc : MirAst.ScalarInt)
    (hptr : get? locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hoff : get? locals offLoc = some (.init (.scalar offsetSc))) :
    evalRvalue locals
      (.binaryOp .offset (.copy ⟨ptrLoc, .nil⟩) (.copy ⟨offLoc, .nil⟩))
      mem localDecls layouts =
      .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + offsetSc.bits } 8)
        locals mem := by
  unfold evalRvalue evalOperand readProjectedValue
  dsimp only []
  rw [hptr]
  dsimp only []
  rw [hoff]
  rfl

/-- **`evalBinOp_offset_inbounds_simulation` (`LM-3.1` Deliverable 3)**:
`BinOp.Offset` by a byte count `deltaBytes` in Anneal, against `lean-miri`'s
`Miri.Interpreter.ptrOffsetInbounds` and `Pointer.wrappingSignedOffset`, for a
`PtrRel`-related pointer into the live allocation `localAlloc`:

1. `ptrOffsetInbounds` succeeds exactly when
   `ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize`
   (including `deltaBytes = 0`).
2. In that case Anneal's `evalRvalue (.binaryOp .offset ...)` and
   `ptrOffsetInbounds` produce `PtrRel`-related pointers.
3. Otherwise `ptrOffsetInbounds` reports `pointerOutOfBounds`, while
   `wrappingSignedOffset` computes the wrapped address.

The theorem does not run `lean-miri`'s `BinaryOp` arm, which first scales the
count by the pointee size and reports overflow; `annealScalarOpsHooks` does not
yet implement `pointerBinary`. Anneal itself adds the unscaled count and never
reports undefined behavior, so for an out-of-bounds offset the two semantics
disagree (`WitLM3_1.wit_lm3_1_anneal_offset_deref_divergence`). -/
theorem evalBinOp_offset_inbounds_simulation
    {s : MachineState} {mach : AnnealMachine}
    {allocMap : List AllocMapEntry}
    (ptrLoc offLoc : Local)
    (ptrVal : ProvenancePtr) (mptr : Miri.Memory.Pointer AnnealProv)
    (deltaBytes : Nat) (offsetSc : MirAst.ScalarInt)
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (localAlloc :
      Miri.Memory.LocalAllocation
        AnnealProv
        (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hptr_rel : PtrRel allocMap ptrVal mptr)
    (hprov : mptr.provenance = .concrete allocId borTag)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hoff_in : ptrVal.offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat)
    (hdelta : deltaBytes < 2 ^ 32)
    (hsc_bits : offsetSc.bits = deltaBytes)
    (hptr_slot : get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hoff_slot : get? s.frame.locals offLoc = some (.init (.scalar offsetSc))) :
    -- (1) Exact in-bounds success characterization (iff)
    ((∃ ptr',
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr.offset, some mptr.provenance⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) = .ok ptr') ↔
      ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) ∧
    -- (2) In-bounds lockstep evaluation and PtrRel preservation
    (ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat →
      ptrVal.offsetBytes + deltaBytes < 2 ^ 32 →
      let mptr' : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes
          (annealStackBaseAddr allocId + UInt64.ofNat (ptrVal.offsetBytes + deltaBytes)),
          .concrete allocId borTag⟩
      evalRvalue s.frame.locals
        (.binaryOp .offset (.copy ⟨ptrLoc, .nil⟩) (.copy ⟨offLoc, .nil⟩))
        s.memory [] emptyLayoutTable =
        .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + deltaBytes } 8)
          s.frame.locals s.memory ∧
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr.offset, some mptr.provenance⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .ok ⟨mptr'.offset, some mptr'.provenance⟩ ∧
      PtrRel allocMap
        { ptrVal with offsetBytes := ptrVal.offsetBytes + deltaBytes }
        mptr') ∧
    -- (3) Out-of-bounds UB in ptrOffsetInbounds vs. wrappingSignedOffset success
    (localAlloc.allocation.byteSize.bytes.toNat < ptrVal.offsetBytes + deltaBytes →
      0 < deltaBytes →
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr.offset, some mptr.provenance⟩
        (Int64.ofInt (deltaBytes : Int))
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .error (.access (.pointerOutOfBounds allocId localAlloc.allocation.byteSize
          (Int.ofNat ptrVal.offsetBytes) (Int.ofNat deltaBytes) .inboundsPointerArithmetic)) ∧
      (⟨mptr.offset, some mptr.provenance⟩ : Miri.Memory.Pointer (Option AnnealProv)).wrappingSignedOffset
        (Int64.ofInt (deltaBytes : Int)) annealPointerArithmetic =
        .ok ⟨Miri.ABI.Size.ofBytes
          ((annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes) + UInt64.ofNat deltaBytes),
          some (Miri.Memory.Provenance.concrete allocId borTag)⟩) := by
  cases hptr_rel with
  | mk allocId' borTag' hprov' hid hoff haddr htarget =>
    rw [hprov] at hprov'
    injection hprov' with hid_eq htag_eq
    subst hid_eq htag_eq
    rw [haddr, hprov]
    refine ⟨?_, ?_, ?_⟩
    · exact ptrOffsetInbounds_live_iff allocId borTag ptrVal.offsetBytes deltaBytes localAlloc
        hid hoff hdelta hbase hlive hoff_in
    · intro hinbounds hsum_lt
      refine ⟨?_, ?_, ?_⟩
      · rw [← hsc_bits]
        exact evalRvalue_binOp_offset_eq s.frame.locals s.memory [] emptyLayoutTable
          ptrLoc offLoc ptrVal offsetSc hptr_slot hoff_slot
      · exact ptrOffsetInbounds_live_inbounds_ok allocId borTag ptrVal.offsetBytes deltaBytes
          localAlloc hid hoff hdelta hbase hlive hinbounds
      · exact .mk allocId borTag rfl hid hsum_lt rfl htarget
    · intro hoob hpos
      exact ⟨ptrOffsetInbounds_live_oob_err allocId borTag ptrVal.offsetBytes deltaBytes
        localAlloc hid hoff hpos hdelta hbase hlive hoob,
        wrappingSignedOffset_annealPointerArithmetic_ofNat
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat ptrVal.offsetBytes),
            some (Miri.Memory.Provenance.concrete allocId borTag)⟩ deltaBytes⟩

/-! ## 6. Deliverable 4: `CastKind.PtrToPtr` & Pointer/Integer Exposure Casts Simulation -/

/-- Anneal's `evalRvalue (.cast .ptrToPtr ...)` preserves a `.ptr ptrVal 8` value. -/
theorem evalRvalue_cast_ptrToPtr_eq
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (srcLoc : Local) (ptrVal : ProvenancePtr) (targetTy : Ty)
    (hsrc : get? locals srcLoc = some (.init (.ptr ptrVal 8))) :
    evalRvalue locals (.cast .ptrToPtr (.copy ⟨srcLoc, .nil⟩) targetTy) mem localDecls layouts =
      .ok (.ptr ptrVal 8) locals mem := by
  unfold evalRvalue evalOperand readProjectedValue
  dsimp only []
  rw [hsrc]

/-- `Miri.Interpreter.Cast.ptrToPtr` under `annealCastHooksLM3_1` on a thin raw pointer
(`translateTy srcTy layouts` to `translateTy dstTy layouts`) preserves the pointer
immediate and updates the layout to `translateTy dstTy layouts`. -/
theorem miri_cast_ptrToPtr_eq
    (layouts : LayoutTable) (m : AnnealStepState)
    (srcMut dstMut : Mutability) (srcPointee dstPointee : RigidTy)
    (srcTy dstTy : Ty)
    (hsrcTy : srcTy.kind = .rawPtr srcMut srcPointee)
    (hdstTy : dstTy.kind = .rawPtr dstMut dstPointee)
    (mptr : Miri.Memory.Pointer AnnealProv) :
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooksLM3_1 layouts)
      ()
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy srcTy layouts⟩
      (translateTy dstTy layouts)
      m =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy dstTy layouts⟩ m := by
  have hsrc_enc : (translateTy srcTy layouts).ty = 40 := by
    unfold translateTy encodeTyId
    rw [hsrcTy]
  have hdst_enc : (translateTy dstTy layouts).ty = 40 := by
    unfold translateTy encodeTyId
    rw [hdstTy]
  have hsrc_sz : (translateTy srcTy layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
    unfold translateTy
    rw [hsrcTy]
    rfl
  have hdst_sz : (translateTy dstTy layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
    unfold translateTy
    rw [hdstTy]
    rfl
  unfold Miri.Interpreter.Cast.ptrToPtr annealCastHooksLM3_1
  simp only [hsrc_enc, hdst_enc, hsrc_sz, hdst_sz, castTypeInfoOfEncodedTyIdLM3_1,
    bind, EStateM.bind, pure, EStateM.pure]
  rfl

/-- Anneal's `.pointerExposeProvenance` followed by `.pointerWithExposedProvenance`
round-trips any `ProvenancePtr` with `offsetBytes < 65536`. -/
theorem evalRvalue_expose_withExposed_roundtrip
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (ptrLoc intLoc : Local) (ptrVal : ProvenancePtr) (usizeTy ptrTy : Ty)
    (hoff : ptrVal.offsetBytes < 65536)
    (hptr : get? locals ptrLoc = some (.init (.ptr ptrVal 8)))
    (hint : get? locals intLoc =
      some (.init (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩))) :
    evalRvalue locals (.cast .pointerExposeProvenance (.copy ⟨ptrLoc, .nil⟩) usizeTy)
      mem localDecls layouts =
      .ok (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩) locals mem ∧
    evalRvalue locals (.cast .pointerWithExposedProvenance (.copy ⟨intLoc, .nil⟩) ptrTy)
      mem localDecls layouts =
      .ok (.ptr ptrVal 8) locals mem := by
  constructor
  · unfold evalRvalue evalOperand readProjectedValue
    dsimp only []
    rw [hptr]
    rfl
  · rcases ptrVal with ⟨id, off⟩
    dsimp only at hoff hint
    unfold evalRvalue evalOperand readProjectedValue
    dsimp only []
    rw [hint]
    dsimp only []
    have hdiv : Nat.div (id * 65536 + off) 65536 = id := by
      change (id * 65536 + off) / 65536 = id
      have hcomm : id * 65536 + off = off + 65536 * id := by
        rw [Nat.add_comm, Nat.mul_comm]
      rw [hcomm, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hoff, Nat.zero_add]
    have hmod : Nat.mod (id * 65536 + off) 65536 = off := by
      change (id * 65536 + off) % 65536 = off
      have hcomm : id * 65536 + off = off + 65536 * id := by
        rw [Nat.add_comm, Nat.mul_comm]
      rw [hcomm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hoff]
    rw [hdiv, hmod]

/-- **`evalCast_ptrToPtr_simulation` (`LM-3.1` Deliverable 4)**: casting a
raw pointer `.ptr ptrVal 8` from `srcTy` to `dstTy` (both raw-pointer types)
keeps the pointer in Anneal's `evalRvalue` and in
`Miri.Interpreter.Cast.ptrToPtr` under `annealCastHooksLM3_1`, so the results
stay related by `ImmediateRelLM3_1`. This is `lean-miri`'s cast leaf, not
`Miri.Interpreter.Step.step`: `annealRvalueHooks.cast` still uses
`annealCastHooks`, whose classifier rejects raw pointers. -/
theorem evalCast_ptrToPtr_simulation
    {allocMap : List AllocMapEntry}
    (locals : List LocalSlot) (mem : Memory)
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (m : AnnealStepState)
    (srcLoc : Local) (ptrVal : ProvenancePtr)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (srcMut dstMut : Mutability) (srcPointee dstPointee : RigidTy)
    (srcTy dstTy : Ty)
    (hsrcTy : srcTy.kind = .rawPtr srcMut srcPointee)
    (hdstTy : dstTy.kind = .rawPtr dstMut dstPointee)
    (hsrc_slot : get? locals srcLoc = some (.init (.ptr ptrVal 8)))
    (hptr_rel : PtrRel allocMap ptrVal mptr) :
    evalRvalue locals (.cast .ptrToPtr (.copy ⟨srcLoc, .nil⟩) dstTy) mem localDecls layouts =
      .ok (.ptr ptrVal 8) locals mem ∧
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooksLM3_1 layouts)
      ()
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy srcTy layouts⟩
      (translateTy dstTy layouts)
      m =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy dstTy layouts⟩ m ∧
    ImmediateRelLM3_1 allocMap dstTy layouts
      (.ptr ptrVal 8)
      (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) :=
  ⟨evalRvalue_cast_ptrToPtr_eq locals mem localDecls layouts srcLoc ptrVal dstTy hsrc_slot,
   miri_cast_ptrToPtr_eq layouts m srcMut dstMut srcPointee dstPointee srcTy dstTy
     hsrcTy hdstTy mptr,
   .rawPtr dstMut dstPointee ptrVal mptr hdstTy hptr_rel⟩

/-! ## 7. Deliverable 5: Composed `LM-3.1` Statement Simulation (`step_stmt_lm3_1_simulation`) -/

/-- Statement forms covered by `step_stmt_lm3_1_simulation` from a pointer-free
root frame:

* `lm1_4`: every `LM-1.4` statement form (`StorageLive`, `StorageDead` other
  than `_0`, `PlaceMention` of a live local, and `_d = move _s` between
  immediate locals), whose `StepRel` step lifts to `StepRelLM3_1 []`;
* `rawPtrAddrOf`: `_d = &raw (const|mut) _t` into an immediate raw-pointer local
  `_d` from an immediate local `_t` of primitive scalar type
  (`step_rawPtr_addrOf_simulation`). -/
inductive WellTypedLM3_1Stmt (body : CapturedMir) (m : AnnealStepState) : Statement → Prop where
  | lm1_4 {stmt : Statement} :
      (∀ topFrame, m.stack.frames = #[topFrame] → WellTypedLM1_4Stmt body topFrame stmt) →
      WellTypedLM3_1Stmt body m stmt
  | rawPtrAddrOf
      (dstIdx targetIdx : Local) (mutability : Mutability) (pointeeKind : RigidTy)
      (dstDecl targetDecl : LocalDecl) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls targetIdx = some targetDecl →
      dstDecl.ty.kind = .rawPtr mutability pointeeKind →
      IsPrimScalarTy targetDecl.ty →
      dstIdx ≠ targetIdx →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx) →
      WellTypedLM3_1Stmt body m
        ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩

/-- **`step_stmt_lm3_1_simulation` (`LM-3.1` Deliverable 5)**: every statement
satisfying `WellTypedLM3_1Stmt` at the current location of a `StateRel`-related
pointer-free state steps in lockstep under `Miri.Interpreter.Step.step`
(`annealStepHooks`) and Anneal's `stepMirFn`, landing in `StateRelLM3_1`-related
states (or reporting undefined behavior in both machines). The `LM-1.4` forms
keep the empty `allocMap`; `_d = &raw (const|mut) _t` extends it by the entry
for the new pointer. -/
theorem step_stmt_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (hstate : StateRel body s m)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_1Stmt body m stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    ∃ allocMap : List AllocMapEntry,
      StepRelLM3_1 body m allocMap
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | lm1_4 hwt =>
    exact ⟨[], (step_stmt_lm1_4_simulation hstate hphase hbb hstmt hwt).toLM3_1⟩
  | rawPtrAddrOf dstIdx targetIdx mutability pointeeKind dstDecl targetDecl span
      hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm =>
    exact ⟨_, step_rawPtr_addrOf_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty
      htgt_ty hne himm hsupply⟩

end LeanMiriSpec.Correspondence
