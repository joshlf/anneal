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

1. **`_d = &raw (const|mut) p` (`step_rawPtr_addrOf_simulation`,
   `step_rawPtr_addrOf_lm3_1_simulation`,
   `step_rawPtr_addrOf_indirect_lm3_1_simulation`,
   `step_rawPtr_deref_zero_offset_correspondence`,
   `step_rawPtr_deref_null_divergence`,
   `step_rawPtr_deref_nonzero_offset_divergence`,
   `step_rawPtr_deref_perm_divergence`)**: real-step correspondence and
   divergence characterizations for taking the raw address of an immediate
   local, an already-promoted local, or a dereferenced pointer place `*_p`
   (together with `step_storageLive_lm3_1_simulation`,
   `step_storageDead_lm3_1_simulation`, and
   `step_rawPtr_use_lm3_1_simulation` for copying and moving raw pointers).
2. **`PlaceElem.Deref` (`step_deref_read_simulation`,
   `step_deref_write_simulation`, `step_deref_oob_miri_ub`,
   `step_deref_misaligned_miri_ub`, `lookupDerefPointeeLayout_decl_eq_encoded`,
   `evalProjection_deref_simulation`)**: real-step `Miri.Interpreter.Step.step`
   (`annealStepHooks`) and `stepMirFn` correspondence for `_d = (copy|move) *_p`
   and `*_p = .use op`, declaration/TyId pointee-layout coherence, and real-step
   divergence theorems for out-of-bounds, misaligned, and invalid `bool`/`char`
   dereferences as well as `PlaceMention(*_p)`.
3. **`BinOp.Offset` (`step_binOp_offset_simulation`,
   `step_binOp_offset_move_simulation`,
   `step_binOp_offset_oob_dangling_miri_ub`,
   `step_binOp_offset_scalar_zero_divergence`,
   `step_binOp_offset_scalar_nonzero_divergence`,
   `evalBinOp_offset_inbounds_simulation`)**: real-step lockstep simulation of
   `_d = Offset((copy|move) _p, rhsOp)` on byte-sized raw pointers for in-bounds
   and zero offsets, paired with real-step divergence theorems on out-of-bounds
   or dangling offsets, non-byte strides, negative `isize` offsets, and
   provenance-less integer-scalar pointers.
4. **`CastKind.PtrToPtr` & Exposure Casts (`step_cast_ptrToPtr_simulation`,
   `step_cast_ptrToPtr_move_simulation`, `step_cast_ptrToPtr_scalar_divergence`,
   `step_cast_expose_provenance_scalar_simulation`,
   `step_cast_expose_provenance_ptr_unsupported`,
   `step_cast_with_exposed_provenance_divergence`,
   `evalCast_ptrToPtr_simulation`, `evalRvalue_expose_withExposed_roundtrip`)**:
   real-step lockstep simulation of `_d = (copy|move) _s as *(const|mut) T`
   (`PtrToPtr`) and provenance-less `PointerExposeProvenance`, paired with
   real-step divergence characterizations for provenance-less `PtrToPtr` casts
   and provenance-exposing / exposed-address casts.
5. **Composed step & terminators (`step_stmt_lm3_1_simulation`,
   `step_stmt_lm3_1_state_simulation`,
   `step_terminator_goto_return_lm3_1_simulation`)**: composed real-step
   statement and root-terminator simulation across pointer-free `StateRel` and
   general `StateRelLM3_1` states.
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

/-- Legacy `CastTypeInfo` classifier retained for the leaf helper
`evalCast_ptrToPtr_simulation` (`StatementPins` compatibility). In the real
`annealStepHooks` / `annealCastHooks` (`Translate.lean`), thin raw pointers use
`encodeRawPtrTyId` (`TyId = 60..82`, `isThinRawPtrPointee`) while non-thin raw
pointers (`TyId = 40`) fail closed (`castTypeInfoOfEncodedTyId_nonThin_err`);
see `evalCast_ptrToPtr_annealCastHooks_simulation` and
`step_cast_ptrToPtr_simulation`. -/
def castTypeInfoOfEncodedTyIdLM3_1 (tyId : Miri.MIR.TyId) :
    Except Miri.Interpreter.StepError Miri.Interpreter.CastTypeInfo :=
  match tyId with
  | 40 => .ok (.rawPointer 1)
  | 41 => .ok (.reference 1)
  | 42 => .ok .fnPointer
  | _ => castTypeInfoOfEncodedTyId tyId

/-- Legacy `annealCastHooks` wrapper using `castTypeInfoOfEncodedTyIdLM3_1`,
retained solely for `evalCast_ptrToPtr_simulation` (`StatementPins`
compatibility). Real execution (`annealStepHooks`) uses `annealCastHooks`
directly (`evalCast_ptrToPtr_annealCastHooks_simulation`,
`step_cast_ptrToPtr_simulation`), which rejects `TyId = 40` non-thin raw
pointers and fails closed on provenance exposure. -/
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

theorem find?_push_fresh {α : Type} (live : Array (Miri.Memory.AllocId × α))
    (id : Miri.Memory.AllocId) (la : α)
    (hfresh : live.any (fun x => x.1 == id) = false) :
    (live.push (id, la)).find? (fun x => x.1 == id) = some (id, la) := by
  rw [← Array.find?_toList, Array.toList_push, List.find?_append]
  have hnone : live.toList.find? (fun x => x.1 == id) = none := by
    rw [List.find?_eq_none]
    intro x hx hbeq
    have hany : live.any (fun y => y.1 == id) = true := by
      rw [← Array.any_toList, List.any_eq_true]
      exact ⟨x, hx, hbeq⟩
    rw [hfresh] at hany
    cases hany
  rw [hnone]
  simp

theorem mem_push_fresh_eq {α : Type} (live : Array (Miri.Memory.AllocId × α))
    (id : Miri.Memory.AllocId) (la x : α)
    (hfresh : live.any (fun y => y.1 == id) = false)
    (hmem : (id, x) ∈ (live.push (id, la)).toList) :
    x = la := by
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hmem
  rcases hmem with hin | heq
  · exfalso
    have hany : live.any (fun y => y.1 == id) = true := by
      rw [← Array.any_toList, List.any_eq_true]
      exact ⟨(id, x), hin, beq_self_eq_true id⟩
    rw [hfresh] at hany
    cases hany
  · exact (Prod.mk.inj heq).2

theorem reserveAllocId_ok_nextAllocId {mem mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (h : mem.reserveAllocId = (mem', .ok id)) :
    id.value = mem.nextAllocId ∧ mem'.nextAllocId = mem.nextAllocId + 1 := by
  unfold Miri.Memory.MemoryState.reserveAllocId at h
  simp only [Id.run] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i allocId hof
        split at h
        · cases h
        · injection h with hmem hid
          injection hid with hid
          subst hid hmem
          have hval : allocId.value = mem.nextAllocId := by
            unfold Miri.Memory.AllocId.ofUInt64 at hof
            split at hof
            · cases hof
            · injection hof with heq
              exact (congrArg Miri.Memory.AllocId.value heq).symm
          refine ⟨hval, ?_⟩
          by_cases hact : mem.sourceAllocIdWorldActive = true <;> simp [hact]

theorem nextAllocId_lt_after_reserve {mem mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    (h : mem.reserveAllocId = (mem', .ok id))
    (hlt32 : mem.nextAllocId.toNat < 2 ^ 32) :
    mem.nextAllocId.toNat < mem'.nextAllocId.toNat := by
  obtain ⟨_, hnext⟩ := reserveAllocId_ok_nextAllocId h
  rw [hnext, UInt64.toNat_add]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1]
  have hlt64 : mem.nextAllocId.toNat + 1 < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt hlt64]
  omega

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
    obtain ⟨halign0, hshape0⟩ :=
      StackScalarAllocShape.of_tryNew (none : Option Miri.TreeBorrows.BorrowTree) htry
    obtain ⟨mem', hres⟩ := hsupply.reserve_eq
    have hfresh_mem' : mem'.live.any
        (fun x => x.1 == (⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ : Miri.Memory.AllocId)) =
        false := by
      have hf := (reserveAllocId_ok_live hres).2
      rw [← (reserveAllocId_ok_live hres).1] at hf
      exact hf
    have hslot_t_sc : ∀ v, slot_t = .init v → ∃ sc, v = .scalar sc := by
      intro v hv
      rcases hval with ⟨h, _⟩ | ⟨v', hv', himmRel⟩
      · rw [h] at hv; cases hv
      · rw [hv'] at hv
        injection hv with hveq
        subst hveq
        obtain ⟨sc, _, rfl, -⟩ := himmRel.of_primitive_scalar htgt_ty
        exact ⟨sc, rfl⟩
    obtain ⟨alloc', hfill, halign_alloc', hshape_alloc'⟩ :
        ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
          ((imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
            ∃ sc, imm = .scalar sc ∧
              Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc
                (allocation.withExtra none) = .ok () alloc') ∧
          alloc'.align = (translateTy targetDecl.ty body.layouts).layout.align.abi ∧
          StackScalarAllocShape (translateTy targetDecl.ty body.layouts).layout.size alloc' := by
      rcases hval with ⟨_, rfl⟩ | ⟨v, _, himmRel⟩
      · exact ⟨_, Or.inl ⟨rfl, rfl⟩, halign0, hshape0⟩
      · obtain ⟨sc, msc, _, rfl, hrel, hsz, _, _⟩ := himmRel.of_primitive_scalar htgt_ty
        have hshape0' :
            StackScalarAllocShape (translateSizeBytes sc.sizeBytes) (allocation.withExtra none) :=
          hsz ▸ hshape0
        obtain ⟨alloc'', hw, halign'', hshape'', -⟩ :=
          StackScalarAllocShape.writeScalar_readScalar hrel hshape0'
        exact ⟨alloc'', Or.inr ⟨_, rfl, hw⟩, halign''.trans halign0, hsz.symm ▸ hshape''⟩
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
      · -- `s'.memory.borrows = allocMap'.map AllocMapEntry.toBorrowEntry`.
        rfl
      · refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro e₁ h₁ e₂ h₂ _
          rw [List.mem_singleton] at h₁ h₂
          rw [h₁, h₂]
        · intro e₁ h₁ e₂ h₂ _
          rw [List.mem_singleton] at h₁ h₂
          rw [h₁, h₂]
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          exact ⟨targetDecl, hdecl_tgt, htgt_ty⟩
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          refine ⟨hsupply.below_2pow32, ?_, ?_⟩
          · show m.machine.memory.nextAllocId.toNat < machc.memory.nextAllocId.toNat
            rw [← hmachc]
            dsimp only [stackAllocMachine]
            exact nextAllocId_lt_after_reserve hres hsupply.below_2pow32
          · show machc.lookupBaseAddr _ = _
            rw [← hmachc]
            exact lookupBaseAddr_stackAllocMachine_self _ _ _ _
        · intro e he
          rw [List.mem_singleton] at he
          subst he
          refine ⟨Nat.lt_succ_self _, ?_⟩
          simp [advanceStmt, lookupBorrow, rawPtrBorrowEntry, rawPtrAllocMapEntry]
        · intro e he la₁ la₂ hla₁ hla₂
          rw [List.mem_singleton] at he
          subst he
          show la₁ = la₂
          rw [← hmachc] at hla₁ hla₂
          have h1 := mem_push_fresh_eq mem'.live _ _ la₁ hfresh_mem' hla₁
          have h2 := mem_push_fresh_eq mem'.live _ _ la₂ hfresh_mem' hla₂
          exact h1.trans h2.symm
        · intro topFrame htop e he
          rw [List.mem_singleton] at he
          subst he
          injection htop with h₁
          injection h₁ with h₂
          subst h₂
          have hslot_after :
              get? (s.frame.locals.set dstIdx
                (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) targetIdx =
              some slot_t := by
            rw [get?_eq_getElem?, List.getElem?_set_ne hne, ← get?_eq_getElem?, hslot_t]
          refine ⟨fun slot hslot _ => ?_, fun hdead => ?_⟩
          · dsimp only [advanceStmt, rawPtrAllocMapEntry] at hslot
            rw [hslot_after] at hslot
            injection hslot with hseq
            subst hseq
            refine ⟨⟨some (translateTy targetDecl.ty body.layouts), ?_⟩, hslot_t_sc, ?_⟩
            · show (tfc.locals.set dstIdx _ hlt_dc)[targetIdx]? = _
              rw [Array.getElem?_set_ne _ hne]
              exact htgt_c
            · intro decl_t hdecl_t'
              dsimp only [rawPtrAllocMapEntry] at hdecl_t'
              rw [hdecl_tgt] at hdecl_t'
              injection hdecl_t' with hdeq
              subst hdeq
              refine ⟨⟨.stack, alloc'⟩, ?_, rfl, halign_alloc', hshape_alloc'⟩
              show machc.memory.live.find? _ = _
              rw [← hmachc]
              exact find?_push_fresh mem'.live _ _ hfresh_mem'
          · exfalso
            dsimp only [advanceStmt, rawPtrAllocMapEntry] at hdead
            rw [hslot_after] at hdead
            exact hslot_ne_dead (Option.some.inj hdead)
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
  obtain ⟨hid_lt, _, hbase⟩ := hmap.base_addr_valid e he
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
  obtain ⟨hid_lt, _, hbase⟩ := hmap.base_addr_valid e he
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

/-- **`evalProjection_deref_simulation` (`LM-3.1` Leaf-Level Deref Bundle)**:
leaf-level companion to `step_deref_read_simulation`,
`step_deref_write_simulation`, `step_deref_oob_miri_ub`, and
`step_deref_misaligned_miri_ub`, comparing Anneal's `evalOperand` /
`writePlaceValue` directly against the memory-access specification helpers
`evalDerefReadScalarMiri` / `evalDerefWriteScalarMiri`:

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

This leaf-level theorem characterizes `ptrOffsetInbounds` directly; see
`step_binOp_offset_simulation` and `step_binOp_offset_oob_dangling_miri_ub` for
the full `Miri.Interpreter.Step.step` (`annealStepHooks`) correspondence and
divergence theorems (`WitLM3_1.wit_lm3_1_anneal_offset_deref_divergence`). -/
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

theorem castTypeInfoOfEncodedTyId_encodeRawPtrTyId (pointee : RigidTy)
    (hthin : isThinRawPtrPointee pointee = true) :
    ∃ inner, castTypeInfoOfEncodedTyId (encodeRawPtrTyId pointee) = .ok (.rawPointer inner) := by
  cases pointee <;>
    simp [isThinRawPtrPointee, encodeRawPtrTyId, castTypeInfoOfEncodedTyId] at hthin ⊢
  all_goals (try cases ‹IntTy› <;> exact ⟨_, rfl⟩)
  all_goals (try cases ‹UintTy› <;> exact ⟨_, rfl⟩)
  all_goals (try cases ‹FloatTy› <;> exact ⟨_, rfl⟩)
  all_goals (try (cases ‹List RigidTy›; exact ⟨_, rfl⟩; simp at hthin))

theorem castTypeInfoOfEncodedTyId_nonThin_err (pointee : RigidTy)
    (hnot : isThinRawPtrPointee pointee = false) :
    ∃ msg, castTypeInfoOfEncodedTyId (encodeRawPtrTyId pointee) =
      .error (.unsupported msg) := by
  have henc : encodeRawPtrTyId pointee = 40 := by
    cases pointee <;> simp [isThinRawPtrPointee, encodeRawPtrTyId] at hnot ⊢
    case tuple fs =>
      cases fs with
      | nil => simp at hnot
      | cons _ _ => rfl
  rw [henc]
  exact ⟨_, rfl⟩

theorem castTypeInfoOfEncodedTyIdLM3_1_encodeRawPtrTyId (pointee : RigidTy) :
    ∃ inner, castTypeInfoOfEncodedTyIdLM3_1 (encodeRawPtrTyId pointee) = .ok (.rawPointer inner) := by
  unfold encodeRawPtrTyId
  split <;> exact ⟨_, rfl⟩

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
  have hsrc_enc : (translateTy srcTy layouts).ty = encodeRawPtrTyId srcPointee := by
    unfold translateTy encodeTyId
    rw [hsrcTy]
  have hdst_enc : (translateTy dstTy layouts).ty = encodeRawPtrTyId dstPointee := by
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
  obtain ⟨i₁, hi₁⟩ := castTypeInfoOfEncodedTyIdLM3_1_encodeRawPtrTyId srcPointee
  obtain ⟨i₂, hi₂⟩ := castTypeInfoOfEncodedTyIdLM3_1_encodeRawPtrTyId dstPointee
  unfold Miri.Interpreter.Cast.ptrToPtr annealCastHooksLM3_1
  simp only [hsrc_enc, hdst_enc, hsrc_sz, hdst_sz, hi₁, hi₂,
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

/-- **`evalCast_ptrToPtr_simulation` (`LM-3.1` Leaf-Level `PtrToPtr` Cast)**:
casting a raw pointer `.ptr ptrVal 8` from `srcTy` to `dstTy` (both raw-pointer
types) keeps the pointer in Anneal's `evalRvalue` and in
`Miri.Interpreter.Cast.ptrToPtr`, preserving `ImmediateRelLM3_1`; see
`step_cast_ptrToPtr_simulation` for the full `Miri.Interpreter.Step.step`
correspondence under `annealStepHooks`. -/
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

/-! ## 7. Real-Step `LM-3.1` State Transitions (`StorageDead`, `StorageLive`, `AddrOf`) -/

theorem LocalRelLM3_1.of_live_base
    {mach mach' : AnnealMachine} {allocMap : List AllocMapEntry}
    {decl : LocalDecl} {layouts : LayoutTable} {slot : LocalSlot}
    {mls : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : LocalRelLM3_1 mach allocMap decl layouts slot mls) :
    LocalRelLM3_1 mach' allocMap decl layouts slot mls := by
  cases h with
  | base hb => exact .base (hb.of_live_base hlive hbase)
  | rawPtr p mptr cl mutability pointeeKind hc hty hptr =>
    exact .rawPtr p mptr cl mutability pointeeKind hc hty hptr

theorem FrameRelLM3_1.of_live_base
    {body : CapturedMir} {mach mach' : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hlive : ∀ e, e ∈ mach.memory.live.toList → e ∈ mach'.memory.live.toList)
    (hbase : ∀ a la, (a, la) ∈ mach.memory.live.toList →
      mach'.lookupBaseAddr a = mach.lookupBaseAddr a)
    (h : FrameRelLM3_1 body mach allocMap af mf) :
    FrameRelLM3_1 body mach' allocMap af mf where
  body_eq := h.body_eq
  location_eq := h.location_eq
  af_locals_len := h.af_locals_len
  mf_locals_size := h.mf_locals_size
  locals_rel i d sl ml hd hs hm := (h.locals_rel i d sl ml hd hs hm).of_live_base hlive hbase

theorem FrameRelLM3_1.indirect_allocId
    {body : CapturedMir} {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {af : StackFrame} {mf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hfr : FrameRelLM3_1 body mach allocMap af mf)
    {j : Nat} {mp : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hj : mf.locals[j]? = some ⟨.live (.indirect mp), lay⟩) :
    ∃ a la, mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId = some a ∧
      (a, la) ∈ mach.memory.live.toList := by
  obtain ⟨hlt_j, _⟩ := Array.getElem?_eq_some_iff.mp hj
  have hlt_d : j < body.localDecls.length := by rw [← hfr.mf_locals_size]; exact hlt_j
  have hdecl : get? body.localDecls j = some (body.localDecls[j]'hlt_d) :=
    List.getElem?_eq_getElem hlt_d
  obtain ⟨_, mls, _, _, _, hmls, _, hloc⟩ := hfr.lookup_local hdecl
  rw [hj] at hmls
  cases hmls
  cases hloc with
  | base hb =>
    cases hb with
    | indirect _ _ _ _ _ hmp =>
      obtain ⟨allocId, tag, _, _, localAlloc, hprov, _, _, hl, _⟩ := hmp
      exact ⟨allocId, localAlloc, by rw [hprov]; rfl, hl⟩

/-- Any live immediate local in a `StateRelLM3_1`-related frame is absent from
`allocMap`: every live mapped local is memory-backed (`local_alloc_sync`). -/
theorem StateRelLM3_1.immediate_not_in_allocMap
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Local} {slot : LocalSlot}
    (hslot : get? s.frame.locals idx = some slot)
    (hne_dead : slot ≠ .dead)
    (himm : IsImmediateFrameLocal tf idx) :
    ∀ e ∈ allocMap, e.localIdx ≠ idx := by
  rcases hstate with ⟨_, _, _, _, _, _, _, _, _, _, halloc, _⟩
  intro e he heq
  subst heq
  obtain ⟨⟨lay, hlay⟩, _⟩ := (halloc.local_alloc_sync tf hframes e he).1
    slot hslot hne_dead
  exact himm _ hlay (stackAllocPlace e.allocId) rfl

theorem updateAllocMapOnWrite_eq_of_not_mem
    (allocMap : List AllocMapEntry) (idx : Local) (writerTag : Option Nat)
    (hnot : ∀ e ∈ allocMap, e.localIdx ≠ idx) :
    updateAllocMapOnWrite allocMap idx writerTag = allocMap := by
  induction allocMap with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd.localIdx ≠ idx := hnot hd (List.Mem.head tl)
    have hbeq : Nat.beq hd.localIdx idx = false := by
      cases h : Nat.beq hd.localIdx idx
      · rfl
      · exact absurd (Nat.eq_of_beq_eq_true h) hne
    change hd.updateOnWrite idx writerTag :: updateAllocMapOnWrite tl idx writerTag = hd :: tl
    rw [ih (fun e he => hnot e (List.mem_cons_of_mem hd he))]
    congr 1
    unfold AllocMapEntry.updateOnWrite updateBorrowPerm AllocMapEntry.toBorrowEntry
    simp [hbeq]

theorem invalidateConflictingBorrows_eq_of_not_mem
    {borrows : List BorrowEntry} {allocMap : List AllocMapEntry}
    (hbor : borrows = allocMap.map AllocMapEntry.toBorrowEntry)
    (idx : Local) (writerTag : Option Nat)
    (hnot : ∀ e ∈ allocMap, e.localIdx ≠ idx) :
    invalidateConflictingBorrows borrows idx writerTag = borrows := by
  rw [hbor, invalidateConflictingBorrows_map_toBorrowEntry,
    updateAllocMapOnWrite_eq_of_not_mem allocMap idx writerTag hnot]

private theorem list_filter_ne_find? {β : Type}
    (l : List (Miri.Memory.AllocId × β))
    {id₀ id : Miri.Memory.AllocId} (hne : id₀ ≠ id) :
    (l.filter (fun entry => entry.1 != id₀)).find? (fun x => x.1 == id) =
      l.find? (fun x => x.1 == id) := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    by_cases hid : (hd.1 == id) = true
    · have hhd : hd.1 = id := beq_iff_eq.mp hid
      have hne' : (hd.1 != id₀) = true := by
        rw [hhd, bne_iff_ne]
        exact Ne.symm hne
      simp only [List.filter, hne', List.find?, hid]
    · have hidf : (hd.1 == id) = false := Bool.eq_false_iff.mpr hid
      cases hkeep : hd.1 != id₀ <;> simp only [List.filter, hkeep, List.find?, hidf, ih]

private theorem list_filter_self_find?_none {β : Type}
    (l : List (Miri.Memory.AllocId × β)) (id : Miri.Memory.AllocId) :
    (l.filter (fun entry => entry.1 != id)).find? (fun x => x.1 == id) = none := by
  rw [List.find?_eq_none]
  intro x hx
  rw [List.mem_filter] at hx
  have hne : x.1 ≠ id := bne_iff_ne.mp hx.2
  exact beq_eq_false_iff_ne.mpr hne ▸ Bool.false_ne_true

private theorem deallocLocalMemory_nextAllocId
    (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv) :
    (deallocLocalMemory mem v).nextAllocId = mem.nextAllocId := by
  unfold deallocLocalMemory
  cases v with
  | dead => rfl
  | live op =>
    cases op with
    | immediate _ => rfl
    | indirect mp =>
      dsimp only []
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId <;> rfl

private theorem deallocLocalMemory_sublist
    (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv)
    {x : Miri.Memory.AllocId ×
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hx : x ∈ (deallocLocalMemory mem v).live.toList) :
    x ∈ mem.live.toList := by
  unfold deallocLocalMemory at hx
  cases v with
  | dead => exact hx
  | live op =>
    cases op with
    | immediate _ => exact hx
    | indirect mp =>
      dsimp only [] at hx
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none =>
        rw [hid] at hx
        exact hx
      | some id =>
        rw [hid] at hx
        dsimp only [] at hx
        rw [Array.toList_filter, List.mem_filter] at hx
        exact hx.1

private theorem deallocLocalMemory_find?_self
    (mem : AnnealMemory) (id : Miri.Memory.AllocId) :
    (deallocLocalMemory mem (.live (.indirect (stackAllocPlace id)))).live.find?
      (fun x => x.1 == id) = none := by
  unfold deallocLocalMemory stackAllocPlace
  dsimp only [Option.bind, Miri.Memory.Provenance.getAllocId]
  rw [← Array.find?_toList, Array.toList_filter]
  exact list_filter_self_find?_none mem.live.toList id

private theorem deallocLocalMemory_find?_ne
    (mem : AnnealMemory) (v : Miri.Interpreter.LocalValue AnnealProv)
    (id : Miri.Memory.AllocId)
    (hne : ∀ mp, v = .live (.indirect mp) →
      mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some id) :
    (deallocLocalMemory mem v).live.find? (fun x => x.1 == id) =
      mem.live.find? (fun x => x.1 == id) := by
  unfold deallocLocalMemory
  cases v with
  | dead => rfl
  | live op =>
    cases op with
    | immediate _ => rfl
    | indirect mp =>
      have hne_mp := hne mp rfl
      dsimp only []
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none => rfl
      | some id₀ =>
        have hne₀ : id₀ ≠ id := fun heq => hne_mp (hid.trans (congrArg some heq))
        dsimp only []
        rw [← Array.find?_toList, ← Array.find?_toList, Array.toList_filter]
        exact list_filter_ne_find? mem.live.toList hne₀

/-- **`step_storageDead_lm3_1_simulation`**: `StorageDead(loc)` (`loc ≠ 0`) from
any `StateRelLM3_1`-related state — whether `loc` is immediate or was promoted
by `&raw _loc` and referenced by live raw pointers in `allocMap` — steps in
lockstep in Anneal (`stepMirFn`) and `lean-miri` (`Miri.Interpreter.Step.step`
under `annealStepHooks`), marking `loc` `.dead` in Anneal and freeing `loc`'s
stack allocation in `lean-miri` while keeping `allocMap` synchronized so any
subsequent dereference of a pointer to `loc` triggers dangling-pointer UB in
both machines. -/
theorem step_storageDead_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_prot, ht_caller, ht_bor,
      halloc, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s ⟨.storageDead loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .dead)) := by
    unfold evalStmt
    dsimp only
    rw [hslot, set?_eq_some_set hlt_af]
  rw [ha]
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne0 hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq]
  apply StepRelLM3_1.step
  let mach' : AnnealMachine :=
    { m.machine with
      memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
  have hnew : LocalRelLM3_1 mach' allocMap decl body.layouts .dead
      { topFrame.locals[loc]'hlt_mf with value := .dead } := by
    rw [hmls_eq]
    exact .base (.dead mls.layout hloc.cachedLayout_eq)
  have hfr' : FrameRelLM3_1 body mach' allocMap
      { s.frame with locals := s.frame.locals.set loc .dead }
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .dead } hlt_mf } := by
    refine ⟨hfr.body_eq, hfr.location_eq,
      by rw [List.length_set, hfr.af_locals_len],
      by rw [Array.size_set, hfr.mf_locals_size], ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : loc = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      apply (hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj loc i mp mp' (topFrame.locals[loc]'hlt_mf).layout mls_i.layout h_eq
      · rw [Array.getElem?_eq_getElem hlt_mf, ← hv]
      · rw [hmls_i, ← hv']
  refine .mk _ rfl ht_ret ht_retp hfr'.advance hcal_none ht_stack ht_prot ht_caller ht_bor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, ?_, halloc.borrow_sync, ?_, ?_⟩
    · intro e he
      obtain ⟨h32, hnext, hbase⟩ := halloc.base_addr_valid e he
      exact ⟨h32, by simpa [mach', deallocLocalMemory_nextAllocId] using hnext, hbase⟩
    · intro e he la₁ la₂ hla₁ hla₂
      exact halloc.live_key_unique e he la₁ la₂
        (deallocLocalMemory_sublist _ _ hla₁)
        (deallocLocalMemory_sublist _ _ hla₂)
    · intro tf' htf' e he
      injection htf' with h₁
      injection h₁ with h₂
      subst h₂
      obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync topFrame hframes e he
      by_cases heloc : loc = e.localIdx
      · have hget_dead :
            get? (advanceStmt s (s.frame.locals.set loc .dead)).frame.locals e.localIdx =
              some .dead := by
          dsimp only [advanceStmt]
          rw [← heloc, get?_eq_getElem?, List.getElem?_set_self hlt_af]
        refine ⟨fun slot' hslot' hne_d => ?_, fun _ => ?_⟩
        · rw [hget_dead] at hslot'
          exact absurd (Option.some.inj hslot').symm hne_d
        · by_cases hs_dead : slot = .dead
          · subst hs_dead
            have hv_dead : (topFrame.locals[loc]'hlt_mf).value = .dead := by
              rw [hmls_eq]
              cases hloc with
              | base hb =>
                cases hb with
                | dead _ _ => rfl
                | immediate _ _ _ _ hv =>
                  rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
                | indirect _ _ _ _ hne _ => exact absurd rfl hne
            show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
              _ = none
            rw [hv_dead]
            exact hdead_e (heloc ▸ hslot)
          · obtain ⟨⟨lay, hlay⟩, _⟩ := hlive_e slot (heloc ▸ hslot) hs_dead
            have hv_ind : (topFrame.locals[loc]'hlt_mf).value =
                .live (.indirect (stackAllocPlace e.allocId)) := by
              rw [← heloc, Array.getElem?_eq_getElem hlt_mf] at hlay
              injection hlay with hls
              rw [hls]
            show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
              _ = none
            rw [hv_ind]
            exact deallocLocalMemory_find?_self m.machine.memory e.allocId
      · have hget_ne :
            get? (advanceStmt s (s.frame.locals.set loc .dead)).frame.locals e.localIdx =
              get? s.frame.locals e.localIdx := by
          dsimp only [advanceStmt]
          rw [get?_eq_getElem?, List.getElem?_set_ne heloc, ← get?_eq_getElem?]
        refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
        · rw [hget_ne] at hslot'
          obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
          have hne_alloc : ∀ mp, (topFrame.locals[loc]'hlt_mf).value = .live (.indirect mp) →
              mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some e.allocId := by
            intro mp hv
            have hd := hdisj loc e.localIdx mp (stackAllocPlace e.allocId)
              (topFrame.locals[loc]'hlt_mf).layout lay heloc
              (by rw [Array.getElem?_eq_getElem hlt_mf, ← hv]) hlay
            simpa [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId] using hd
          refine ⟨⟨lay, ?_⟩, hsc, fun decl_e hdecl_e => ?_⟩
          · dsimp only
            rw [Array.getElem?_set_ne _ heloc]
            exact hlay
          · obtain ⟨la, hfind, hkind, halign, hsh⟩ := hshape decl_e hdecl_e
            refine ⟨la, ?_, hkind, halign, hsh⟩
            show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
              _ = _
            rw [deallocLocalMemory_find?_ne _ _ _ hne_alloc]
            exact hfind
        · rw [hget_ne] at hdead'
          have hfind0 := hdead_e hdead'
          show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
            _ = none
          rw [Array.find?_eq_none] at hfind0 ⊢
          intro x hx
          exact hfind0 x (Array.mem_toList_iff.mp
            (deallocLocalMemory_sublist _ _ (Array.mem_toList_iff.mpr hx)))
  · intro i j mp_i mp_j lay_i lay_j hij hi hj
    dsimp only at hi hj
    rw [Array.getElem?_set] at hi hj
    by_cases hi_loc : loc = i
    · subst hi_loc; simp only [↓reduceIte] at hi; cases hi
    · by_cases hj_loc : loc = j
      · subst hj_loc; simp only [↓reduceIte] at hj; cases hj
      · simp only [hi_loc, hj_loc, ↓reduceIte] at hi hj
        exact hdisj i j mp_i mp_j lay_i lay_j hij hi hj

/-- **`step_storageLive_lm3_1_simulation`**: `StorageLive(loc)` for any declared
local `loc` not tracked in `allocMap` (`∀ e ∈ allocMap, e.localIdx ≠ loc`) steps
in lockstep from any `StateRelLM3_1`-related state. -/
theorem step_storageLive_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hnot_mapped : ∀ e ∈ allocMap, e.localIdx ≠ loc) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, ht_ret, ht_retp, hfr, hcal_none, ht_stack, ht_prot, ht_caller, ht_bor,
      halloc, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal_none hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot, mls, hlt_af, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have ha : evalStmt s ⟨.storageLive loc, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s (s.frame.locals.set loc .uninit)) := by
    unfold evalStmt
    dsimp only
    rw [hslot, set?_eq_some_set hlt_af]
  rw [ha]
  have hty : ∃ ty, topFrame.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hlive : LocalAllocLive m.machine.memory (topFrame.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ topFrame with
            locals := topFrame.locals.set loc
              { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageLive_any_eq hframes hlt_mf hty hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq]
  apply StepRelLM3_1.step
  let mach' : AnnealMachine :=
    { m.machine with
      memory := deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value }
  have hnew : LocalRelLM3_1 mach' allocMap decl body.layouts .uninit
      { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } := by
    rw [hmls_eq]
    exact .base (.immediate .uninit .uninit mls.layout hloc.cachedLayout_eq (Or.inl ⟨rfl, rfl⟩))
  have hfr' : FrameRelLM3_1 body mach' allocMap
      { s.frame with locals := s.frame.locals.set loc .uninit }
      { topFrame with
        locals := topFrame.locals.set loc
          { topFrame.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf } := by
    refine ⟨hfr.body_eq, hfr.location_eq,
      by rw [List.length_set, hfr.af_locals_len],
      by rw [Array.size_set, hfr.mf_locals_size], ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    rw [Array.getElem?_set] at hmls_i
    by_cases h_eq : loc = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af, Option.some.injEq] at hslot_i hmls_i
      have hdecl_eq : decl_i = decl := by
        rw [hdecl] at hdecl_i; exact Option.some.inj hdecl_i.symm
      subst hdecl_eq hslot_i hmls_i
      exact hnew
    · simp only [h_eq, ↓reduceIte] at hslot_i hmls_i
      apply (hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).of_dealloc
      intro mp mp' hv hv'
      apply hdisj loc i mp mp' (topFrame.locals[loc]'hlt_mf).layout mls_i.layout h_eq
      · rw [Array.getElem?_eq_getElem hlt_mf, ← hv]
      · rw [hmls_i, ← hv']
  refine .mk _ rfl ht_ret ht_retp hfr'.advance hcal_none ht_stack ht_prot ht_caller ht_bor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, ?_, halloc.borrow_sync, ?_, ?_⟩
    · intro e he
      obtain ⟨h32, hnext, hbase⟩ := halloc.base_addr_valid e he
      exact ⟨h32, by simpa [mach', deallocLocalMemory_nextAllocId] using hnext, hbase⟩
    · intro e he la₁ la₂ hla₁ hla₂
      exact halloc.live_key_unique e he la₁ la₂
        (deallocLocalMemory_sublist _ _ hla₁)
        (deallocLocalMemory_sublist _ _ hla₂)
    · intro tf' htf' e he
      injection htf' with h₁
      injection h₁ with h₂
      subst h₂
      have heloc : loc ≠ e.localIdx := Ne.symm (hnot_mapped e he)
      obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync topFrame hframes e he
      have hget_ne :
          get? (advanceStmt s (s.frame.locals.set loc .uninit)).frame.locals e.localIdx =
            get? s.frame.locals e.localIdx := by
        dsimp only [advanceStmt]
        rw [get?_eq_getElem?, List.getElem?_set_ne heloc, ← get?_eq_getElem?]
      refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
      · rw [hget_ne] at hslot'
        obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
        have hne_alloc : ∀ mp, (topFrame.locals[loc]'hlt_mf).value = .live (.indirect mp) →
            mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId ≠ some e.allocId := by
          intro mp hv
          have hd := hdisj loc e.localIdx mp (stackAllocPlace e.allocId)
            (topFrame.locals[loc]'hlt_mf).layout lay heloc
            (by rw [Array.getElem?_eq_getElem hlt_mf, ← hv]) hlay
          simpa [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId] using hd
        refine ⟨⟨lay, ?_⟩, hsc, fun decl_e hdecl_e => ?_⟩
        · dsimp only
          rw [Array.getElem?_set_ne _ heloc]
          exact hlay
        · obtain ⟨la, hfind, hkind, halign, hsh⟩ := hshape decl_e hdecl_e
          refine ⟨la, ?_, hkind, halign, hsh⟩
          show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
            _ = _
          rw [deallocLocalMemory_find?_ne _ _ _ hne_alloc]
          exact hfind
      · rw [hget_ne] at hdead'
        have hfind0 := hdead_e hdead'
        show (deallocLocalMemory m.machine.memory (topFrame.locals[loc]'hlt_mf).value).live.find?
          _ = none
        rw [Array.find?_eq_none] at hfind0 ⊢
        intro x hx
        exact hfind0 x (Array.mem_toList_iff.mp
          (deallocLocalMemory_sublist _ _ (Array.mem_toList_iff.mpr hx)))
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : loc = k
    · subst hk
      right
      exact ⟨.uninit, (topFrame.locals[loc]'hlt_mf).layout, by
        simp only [Array.getElem?_set, ↓reduceIte]⟩
    · left
      simp only [hk, Array.getElem?_set, ↓reduceIte]

/-- **`step_rawPtr_addrOf_lm3_1_simulation`**: general `StateRelLM3_1` version
of `_d = &raw (const|mut) _t` (with arbitrary existing raw pointers in
`allocMap`). When `_t` is a live immediate primitive-scalar local and `_d` is a
live immediate raw-pointer local (`_d ≠ _t`), `forceAllocation` promotes `_t`
into fresh stack allocation `nextAllocId`, Anneal pushes the fresh root borrow
`nextTag`, and `allocMap` extends by the new entry while preserving every
existing `allocMap` invariant. -/
theorem step_rawPtr_addrOf_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc,
    hdisj⟩ := id hstate
  obtain ⟨himm_dst, himm_tgt⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRelLM3_1 body m.machine allocMap s.frame tfa :=
    hfr.cache_local_layout hdecl_dst hlt_d
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_t, mls_t, hlt_af_t, hlt_t, hslot_t, hmls_t, hmls_t_eq, hloc_t⟩ :=
    hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.cachedLayout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
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
  | rawPtr _ _ _ _ _ _ hty_raw _ =>
    exfalso
    rcases htgt_ty with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hty_raw <;> cases hty_raw
  | base hloc_t_b =>
    cases hloc_t_b with
    | indirect _ mp _ _ _ _ =>
      exact absurd rfl (himm_tgt.cache_layout hlt_d _ _ hmls_t mp)
    | dead cl _ =>
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
    | immediate _ imm _ _ hval =>
      have hslot_ne_dead : slot_t ≠ .dead := by
        rcases hval with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> simp
      have hnot_tgt : ∀ e ∈ allocMap, e.localIdx ≠ targetIdx :=
        hstate.immediate_not_in_allocMap hframes hslot_t hslot_ne_dead himm_tgt
      have hlt_tb : targetIdx < tfb.locals.size := by
        rw [cacheFrameLocalLayout_size]; exact hlt_t
      have hlay_tb : (tfb.locals[targetIdx]'hlt_tb).layout =
          some (translateTy targetDecl.ty body.layouts) := by
        simp [tfb, cacheFrameLocalLayout]
      obtain ⟨hsized, allocation, htry⟩ := htgt_ty.layout_ok (layouts := body.layouts)
      obtain ⟨hsz_eq0, hmut0, halign_pow0, huninit0⟩ := freshStackAlloc_spec htry
      obtain ⟨halign0, hshape0⟩ :=
        StackScalarAllocShape.of_tryNew (none : Option Miri.TreeBorrows.BorrowTree) htry
      obtain ⟨mem', hres⟩ := hsupply.reserve_eq
      let freshId : Miri.Memory.AllocId := ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
      have hfresh_mem' : mem'.live.any (fun x => x.1 == freshId) = false := by
        have hf := (reserveAllocId_ok_live hres).2
        rw [← (reserveAllocId_ok_live hres).1] at hf
        exact hf
      have hslot_t_sc : ∀ v, slot_t = .init v → ∃ sc, v = .scalar sc := by
        intro v hv
        rcases hval with ⟨h, _⟩ | ⟨v', hv', himmRel⟩
        · rw [h] at hv; cases hv
        · rw [hv'] at hv
          injection hv with hveq
          subst hveq
          obtain ⟨sc, _, rfl, -⟩ := himmRel.of_primitive_scalar htgt_ty
          exact ⟨sc, rfl⟩
      obtain ⟨alloc', hfill, halign_alloc', hshape_alloc', hnew_tgt⟩ :
          ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
            ((imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
              ∃ sc, imm = .scalar sc ∧
                Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                  (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc
                  (allocation.withExtra none) = .ok () alloc') ∧
            alloc'.align = (translateTy targetDecl.ty body.layouts).layout.align.abi ∧
            StackScalarAllocShape (translateTy targetDecl.ty body.layouts).layout.size alloc' ∧
            LocalRelLM3_1 (stackAllocMachine m.machine mem' freshId alloc') allocMap
              targetDecl body.layouts slot_t
              { tfb.locals[targetIdx]'hlt_tb with
                value := .live (.indirect (stackAllocPlace freshId)) } := by
        have hlay_c : ∀ l ∈ (tfb.locals[targetIdx]'hlt_tb).layout,
            l = translateTy targetDecl.ty body.layouts := by
          rw [hlay_tb]; intro l hl; exact (Option.some.inj hl).symm
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · refine ⟨allocation.withExtra none, Or.inl ⟨rfl, rfl⟩, halign0, hshape0,
            .base (.indirect .uninit (stackAllocPlace freshId) _ hlay_c (by simp) ?_)⟩
          exact stackAlloc_memPlaceRel hmut0 halign_pow0 hsz_eq0
            (fun _ hnz => huninit0 hnz)
            (fun _ hv => nomatch hv)
            (fun _ hv => nomatch hv)
        · obtain ⟨sc, msc, rfl, rfl, hrel, hsz, hbool, hchar⟩ :=
            himmRel.of_primitive_scalar htgt_ty
          have hshape0' :
              StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
                (allocation.withExtra none) :=
            hsz ▸ hshape0
          have htry' : Miri.Memory.Allocation.tryNew (translateSizeBytes sc.sizeBytes)
              (translateTy targetDecl.ty body.layouts).layout.align.abi .Uninit
              annealZeroedStorage = .ok allocation := hsz ▸ htry
          obtain ⟨alloc'', hw'', hsize'', hmut'', hinit'', hread''⟩ :=
            freshStackAlloc_writeScalar_readScalar hrel htry'
          obtain ⟨alloc₃, hw₃, halign₃, hshape₃, -⟩ :=
            StackScalarAllocShape.writeScalar_readScalar hrel hshape0'
          have halloc_eq : alloc₃ = alloc'' := by
            have h := hw₃.symm.trans hw''
            injection h
          subst halloc_eq
          refine ⟨alloc₃, Or.inr ⟨_, rfl, hw₃⟩, halign₃.trans halign0, hsz.symm ▸ hshape₃,
            .base (.indirect (.init (.scalar sc)) (stackAllocPlace freshId) _ hlay_c (by simp) ?_)⟩
          apply stackAlloc_memPlaceRel hmut'' halign_pow0 (by rw [hsize'', hsz])
          · intro h; cases h
          · intro _ _ _; rw [hsz]; exact hinit''
          · intro sc₂ hv
            injection hv with hv
            injection hv with hv
            subst hv
            exact ⟨hsz, hbool, hchar, msc, hrel, by rw [hsz]; exact hread''⟩
      have hforce₀ := forceAllocation_promote_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hdecl_tgt
        hlt_tb hlay_tb hval_tb hsized htry hres hfill
      obtain ⟨hlive_sub, hfreshne, hbase_sub⟩ :=
        stackAllocMachine_live_base (mach := m.machine) alloc' hres
      obtain ⟨tfb', hframes_b, -, -, hfrb, -, -, -, -, -, -, hdisj_b⟩ := hstate_b
      injection hframes_b with hfb₁
      injection hfb₁ with hfb₂
      subst hfb₂
      have hfrc₀ := (hfrb.of_live_base hlive_sub hbase_sub).update_local hdecl_tgt slot_t
        (.live (.indirect (stackAllocPlace freshId))) hnew_tgt
      have hset_self : s.frame.locals.set targetIdx slot_t = s.frame.locals := by
        obtain ⟨_, hget⟩ := List.getElem_of_getElem? hslot_t
        rw [← hget, List.set_getElem_self]
      rw [hset_self] at hfrc₀
      have hdisj_c₀ : MemoryAllocDisjoint
          { tfb with
            locals := tfb.locals.set targetIdx
              { tfb.locals[targetIdx]'hlt_tb with
                value := .live (.indirect (stackAllocPlace freshId)) } hlt_tb } := by
        intro i j mp_i mp_j lay_i lay_j hij hi hj
        dsimp only at hi hj
        rw [Array.getElem?_set] at hi hj
        by_cases hi_idx : targetIdx = i
        · subst hi_idx
          have hj_idx : targetIdx ≠ j := hij
          simp only [hj_idx, ↓reduceIte] at hj
          simp only [↓reduceIte] at hi
          obtain ⟨a, la, ha, hla⟩ := hfrb.indirect_allocId hj
          injection hi with hi
          injection hi with hv _
          injection hv with hv
          injection hv with hv
          subst hv
          rw [ha]
          simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
            Option.some.injEq]
          exact fun h => hfreshne a la hla h.symm
        · simp only [hi_idx, ↓reduceIte] at hi
          by_cases hj_idx : targetIdx = j
          · subst hj_idx
            simp only [↓reduceIte] at hj
            obtain ⟨a, la, ha, hla⟩ := hfrb.indirect_allocId hi
            injection hj with hj
            injection hj with hv _
            injection hv with hv
            injection hv with hv
            subst hv
            rw [ha]
            simp only [stackAllocPlace, Option.bind, Miri.Memory.Provenance.getAllocId, ne_eq,
              Option.some.injEq]
            exact hfreshne a la hla
          · simp only [hj_idx, ↓reduceIte] at hj
            exact hdisj_b i j mp_i mp_j lay_i lay_j hij hi hj
      have hforce : annealForceAllocation body.localDecls body.layouts
          ⟨.local 0 targetIdx none tfa.localsIdentity, translateTy targetDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .ok (stackAllocPlace freshId)
            { stack := ⟨#[{ tfb with
                locals := tfb.locals.set targetIdx
                  { tfb.locals[targetIdx]'hlt_tb with
                    value := .live (.indirect (stackAllocPlace freshId)) } hlt_tb }]⟩
              machine := stackAllocMachine m.machine mem' freshId alloc' } := by
        unfold annealForceAllocation
        erw [hforce₀]
      have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval htgt_eval hforce
        (stackAllocPlace_toRef freshId)
      have hdc_eq₀ : ({ tfb with
          locals := tfb.locals.set targetIdx
            { tfb.locals[targetIdx]'hlt_tb with
              value := .live (.indirect (stackAllocPlace freshId)) }
            hlt_tb } :
          Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[dstIdx]? =
          some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
        simp only [tfb, tfa, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_ne _ (Ne.symm hne),
          Array.getElem?_set_self, hmls_d_eq]
      have htgt_c : ({ tfb with
          locals := tfb.locals.set targetIdx
            { tfb.locals[targetIdx]'hlt_tb with
              value := .live (.indirect (stackAllocPlace freshId)) }
            hlt_tb } :
          Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[targetIdx]? =
          some ⟨.live (.indirect (stackAllocPlace freshId)),
            some (translateTy targetDecl.ty body.layouts)⟩ := by
        simp only [Array.getElem?_set_self]
        rw [← hlay_tb]
      have hother_c : ∀ k, k ≠ dstIdx → k ≠ targetIdx →
          ({ tfb with
            locals := tfb.locals.set targetIdx
              { tfb.locals[targetIdx]'hlt_tb with
                value := .live (.indirect (stackAllocPlace freshId)) }
              hlt_tb } :
            Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit).locals[k]? =
          tf.locals[k]? := by
        intro k hkd hkt
        simp only [tfb, tfa, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hkt), Array.getElem?_set_ne _ (Ne.symm hkt),
          Array.getElem?_set_ne _ (Ne.symm hkd)]
      generalize htfc : ({ tfb with
          locals := tfb.locals.set targetIdx
            { tfb.locals[targetIdx]'hlt_tb with
              value := .live (.indirect (stackAllocPlace freshId)) }
            hlt_tb } : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) = tfc
        at hrv hfrc₀ hdisj_c₀ hdc_eq₀ htgt_c hother_c
      generalize hmachc : stackAllocMachine m.machine mem' freshId alloc' = machc at hrv hfrc₀
      have hdc_eq := hdc_eq₀
      obtain ⟨hlt_dc, -⟩ := Array.getElem?_eq_some_iff.mp hdc_eq
      -- Helper handling both immediate and existing-rawPtr `_d` when `_d` is live.
      have hlive_dst_step :
          ∀ oldImm, mls_d.value = .live (.immediate oldImm) → slot_d ≠ .dead →
            StepRelLM3_1 body m
              (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx
                s.memory.nextTag freshId :: allocMap)
              (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
                body.localDecls body.layouts)
              (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
        intro oldImm hmls_d_imm hslot_d_ne
        have hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx :=
          hstate.immediate_not_in_allocMap hframes hslot_d hslot_d_ne himm_dst
        have hdc_imm : { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } =
            ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
          rcases mls_d with ⟨mv, _⟩
          dsimp only at hmls_d_imm
          subst hmls_d_imm
          rfl
        rw [hdc_imm] at hdc_eq
        have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
              .concrete freshId Miri.Memory.BorTag.one⟩))
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
                          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                            .concrete freshId Miri.Memory.BorTag.one⟩))) }
                    hlt_dc }]⟩ },
              .ok ()) := by
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [hrv, hw]
        have hloc_c : tfc.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfrc₀.location_eq
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
          hloc_c]
        let newEntry := rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx
          s.memory.nextTag freshId
        have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
            body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s
                (s.frame.locals.set dstIdx
                  (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                { s.memory with
                  borrows := newEntry.toBorrowEntry :: s.memory.borrows
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
          have hinv_tail := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
          cases slot_d with
          | dead => exact absurd rfl hslot_d_ne
          | uninit =>
            simp only [set?_eq_some_set hlt_af_d, hprot, invalidateConflictingBorrows_cons,
              updateBorrowPerm, hbeq, newEntry, rawPtrAllocMapEntry,
              AllocMapEntry.toBorrowEntry, hinv_tail]
          | init v =>
            simp only [set?_eq_some_set hlt_af_d, hprot, invalidateConflictingBorrows_cons,
              updateBorrowPerm, hbeq, newEntry, rawPtrAllocMapEntry,
              AllocMapEntry.toBorrowEntry, hinv_tail]
        rw [ha]
        apply StepRelLM3_1.step
        have hretCont_c : tfc.returnContinuation = .stop false := by
          rw [← htfc]; exact hretCont
        have hretPlace_c : ∃ retLay,
            tfc.returnPlace = .frameLocal 0 0 none retLay tfc.localsIdentity := by
          rw [← htfc]; exact hretPlace
        have hptr := PtrRel.of_stackAllocPlace
          (allocMap := newEntry :: allocMap) (e := newEntry)
          (List.Mem.head allocMap) hsupply.below_2pow32
        have hdc' : tfc.locals[dstIdx]'hlt_dc =
            ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
          have h := Array.getElem?_eq_getElem hlt_dc
          rw [hdc_eq] at h
          exact (Option.some.inj h).symm
        have hnew : LocalRelLM3_1 machc (newEntry :: allocMap) dstDecl body.layouts
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
            { tfc.locals[dstIdx]'hlt_dc with
              value := .live (.immediate (.scalar
                (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                  ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                    .concrete freshId Miri.Memory.BorTag.one⟩))) } := by
          rw [hdc']
          exact .rawPtr _ _ _ mutability pointeeKind (fun l hl => (Option.some.inj hl).symm)
            hdst_ty hptr
        have hfrd := (hfrc₀.mono_cons newEntry).update_local hdecl_dst _ _ hnew
        have hnodup_new : ((newEntry :: allocMap).map AllocMapEntry.tag).Nodup := by
          simp only [List.map_cons, List.nodup_cons]
          refine ⟨?_, halloc.tags_nodup⟩
          intro hmem
          obtain ⟨e, he, htag_eq⟩ := List.mem_map.mp hmem
          have hlt_tag := (halloc.borrow_sync e he).1
          dsimp only [newEntry, rawPtrAllocMapEntry] at htag_eq
          omega
        have hne_fresh : ∀ e ∈ allocMap, e.allocId ≠ freshId := by
          intro e he heq
          have hlt_id := (halloc.base_addr_valid e he).2.1
          rw [heq] at hlt_id
          exact Nat.lt_irrefl _ hlt_id
        refine .mk _ rfl hretCont_c hretPlace_c hfrd.advance hcal hstack hprot hcaller
          (by simp [advanceStmt, hbor, newEntry]) ?_ ?_
        · refine ⟨hnodup_new, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · intro e₁ h₁ e₂ h₂ hloc_eq
            rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
              rcases List.mem_cons.mp h₂ with rfl | hm₂
            · rfl
            · exact absurd hloc_eq.symm (hnot_tgt e₂ hm₂)
            · exact absurd hloc_eq (hnot_tgt e₁ hm₁)
            · exact halloc.local_to_alloc_unique e₁ hm₁ e₂ hm₂ hloc_eq
          · intro e₁ h₁ e₂ h₂ hid_eq
            rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
              rcases List.mem_cons.mp h₂ with rfl | hm₂
            · rfl
            · exact absurd hid_eq.symm (hne_fresh e₂ hm₂)
            · exact absurd hid_eq (hne_fresh e₁ hm₁)
            · exact halloc.alloc_to_local_injective e₁ hm₁ e₂ hm₂ hid_eq
          · intro e he
            rcases List.mem_cons.mp he with rfl | hm
            · exact ⟨targetDecl, hdecl_tgt, htgt_ty⟩
            · exact halloc.target_decl e hm
          · have hnext_lt : m.machine.memory.nextAllocId.toNat < machc.memory.nextAllocId.toNat := by
              rw [← hmachc]
              dsimp only [stackAllocMachine]
              exact nextAllocId_lt_after_reserve hres hsupply.below_2pow32
            intro e he
            rcases List.mem_cons.mp he with rfl | hm
            · refine ⟨hsupply.below_2pow32, hnext_lt, ?_⟩
              rw [← hmachc]
              exact lookupBaseAddr_stackAllocMachine_self _ _ _ _
            · obtain ⟨h32, hlt_old, hbase_old⟩ := halloc.base_addr_valid e hm
              refine ⟨h32, Nat.lt_trans hlt_old hnext_lt, ?_⟩
              rw [← hmachc, lookupBaseAddr_stackAllocMachine_ne _ _ _ (hne_fresh e hm)]
              exact hbase_old
          · intro e he
            have hlook_all := lookupBorrow_map_toBorrowEntry_of_nodup hnodup_new he
            rcases List.mem_cons.mp he with rfl | hm
            · exact ⟨Nat.lt_succ_self _,
                by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
            · exact ⟨Nat.lt_trans (halloc.borrow_sync e hm).1 (Nat.lt_succ_self _),
                by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
          · intro e he la₁ la₂ hla₁ hla₂
            rw [← hmachc] at hla₁ hla₂
            rcases List.mem_cons.mp he with rfl | hm
            · have h1 := mem_push_fresh_eq mem'.live _ _ la₁ hfresh_mem' hla₁
              have h2 := mem_push_fresh_eq mem'.live _ _ la₂ hfresh_mem' hla₂
              exact h1.trans h2.symm
            · have hne_id := hne_fresh e hm
              have hlive_eq := (reserveAllocId_ok_live hres).1
              have hin1 : (e.allocId, la₁) ∈ m.machine.memory.live.toList := by
                simp only [stackAllocMachine, Array.toList_push, List.mem_append,
                  List.mem_singleton] at hla₁
                rcases hla₁ with h | h
                · rwa [hlive_eq] at h
                · exact absurd (Prod.mk.inj h).1 hne_id
              have hin2 : (e.allocId, la₂) ∈ m.machine.memory.live.toList := by
                simp only [stackAllocMachine, Array.toList_push, List.mem_append,
                  List.mem_singleton] at hla₂
                rcases hla₂ with h | h
                · rwa [hlive_eq] at h
                · exact absurd (Prod.mk.inj h).1 hne_id
              exact halloc.live_key_unique e hm la₁ la₂ hin1 hin2
          · intro topFrame htop e he
            injection htop with h₁
            injection h₁ with h₂
            subst h₂
            have hlive_eq := (reserveAllocId_ok_live hres).1
            rcases List.mem_cons.mp he with rfl | hm
            · have hslot_after :
                  get? (s.frame.locals.set dstIdx
                    (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                    targetIdx = some slot_t := by
                rw [get?_eq_getElem?, List.getElem?_set_ne hne, ← get?_eq_getElem?, hslot_t]
              refine ⟨fun slot hslot _ => ?_, fun hdead => ?_⟩
              · dsimp only [advanceStmt, newEntry, rawPtrAllocMapEntry] at hslot
                rw [hslot_after] at hslot
                injection hslot with hseq
                subst hseq
                refine ⟨⟨some (translateTy targetDecl.ty body.layouts), ?_⟩, hslot_t_sc, ?_⟩
                · show (tfc.locals.set dstIdx _ hlt_dc)[targetIdx]? = _
                  rw [Array.getElem?_set_ne _ hne]
                  exact htgt_c
                · intro decl_t hdecl_t'
                  dsimp only [newEntry, rawPtrAllocMapEntry] at hdecl_t'
                  rw [hdecl_tgt] at hdecl_t'
                  injection hdecl_t' with hdeq
                  subst hdeq
                  refine ⟨⟨.stack, alloc'⟩, ?_, rfl, halign_alloc', hshape_alloc'⟩
                  show machc.memory.live.find? _ = _
                  rw [← hmachc]
                  exact find?_push_fresh mem'.live _ _ hfresh_mem'
              · exfalso
                dsimp only [advanceStmt, newEntry, rawPtrAllocMapEntry] at hdead
                rw [hslot_after] at hdead
                exact hslot_ne_dead (Option.some.inj hdead)
            · have hne_d : dstIdx ≠ e.localIdx := Ne.symm (hnot_dst e hm)
              have hne_t : e.localIdx ≠ targetIdx := hnot_tgt e hm
              have hne_id : e.allocId ≠ freshId := hne_fresh e hm
              obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e hm
              have hslot_after :
                  get? (advanceStmt s
                    (s.frame.locals.set dstIdx
                      (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                    { s.memory with
                      borrows := newEntry.toBorrowEntry :: s.memory.borrows
                      nextTag := s.memory.nextTag + 1 }).frame.locals e.localIdx =
                  get? s.frame.locals e.localIdx := by
                dsimp only [advanceStmt]
                rw [get?_eq_getElem?, List.getElem?_set_ne hne_d, ← get?_eq_getElem?]
              have hfind_push :
                  machc.memory.live.find? (fun x => x.1 == e.allocId) =
                    m.machine.memory.live.find? (fun x => x.1 == e.allocId) := by
                rw [← hmachc]
                show (mem'.live.push (freshId, ⟨.stack, alloc'⟩)).find?
                  (fun x => x.1 == e.allocId) = _
                rw [Array.find?_push, hlive_eq]
                cases h : m.machine.memory.live.find? (fun x => x.1 == e.allocId) with
                | some v => rfl
                | none =>
                  dsimp only []
                  rw [beq_false_of_ne (Ne.symm hne_id)]
                  rfl
              refine ⟨fun slot hslot hne_dead => ?_, fun hdead => ?_⟩
              · rw [hslot_after] at hslot
                obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot hslot hne_dead
                refine ⟨⟨lay, ?_⟩, hsc, fun decl_e hdecl_e => ?_⟩
                · show (tfc.locals.set dstIdx _ hlt_dc)[e.localIdx]? = _
                  rw [Array.getElem?_set_ne _ hne_d, hother_c e.localIdx (Ne.symm hne_d) hne_t]
                  exact hlay
                · obtain ⟨la, hfind0, hkind0, halign0', hsh0⟩ := hshape decl_e hdecl_e
                  exact ⟨la, hfind_push.trans hfind0, hkind0, halign0', hsh0⟩
              · rw [hslot_after] at hdead
                exact hfind_push.trans (hdead_e hdead)
        · apply MemoryAllocDisjoint.mono_immediate hdisj_c₀
          intro k
          by_cases hk : k = dstIdx
          · subst hk
            right
            refine ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                  .concrete freshId Miri.Memory.BorTag.one⟩),
              some (translateTy dstDecl.ty body.layouts), ?_⟩
            show (tfc.locals.set k _ hlt_dc)[k]? = _
            rw [Array.getElem?_set_self, hdc']
          · left
            show (tfc.locals.set dstIdx _ hlt_dc)[k]? = _
            rw [Array.getElem?_set_ne _ (Ne.symm hk)]
      cases hloc_d with
      | rawPtr p mptr _ _ _ _ _ _ =>
        exact hlive_dst_step _ rfl (by simp)
      | base hloc_d_b =>
        cases hloc_d_b with
        | indirect _ mp _ _ _ _ =>
          exact absurd rfl (himm_dst _ hmls_d mp)
        | dead _ _ =>
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
              (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
              m =
              (⟨⟨#[tfc]⟩, machc⟩, .error (.undefinedBehavior "write to dead local")) := by
            rw [hm_stmt]
            unfold Miri.Interpreter.runRvalue
            rw [hrv, annealWriteImmediate_dead (m := ⟨⟨#[tfc]⟩, machc⟩) rfl hget_dc]
          rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
            hm_err]
          exact .ub _ _
        | immediate _ oldImm _ _ hvald =>
          have hslot_d_ne : slot_d ≠ .dead := by
            rcases hvald with ⟨rfl, _⟩ | ⟨v, rfl, _⟩ <;> simp
          exact hlive_dst_step oldImm rfl hslot_d_ne

/-- **`evalRvalue_rawPtr_addrOf_simulation` (`LM-3.1` Deliverable 1)**: the
brief's name for the address-of step theorem, `step_rawPtr_addrOf_lm3_1_simulation`:
from any `StateRelLM3_1` state, `_d = &raw (const|mut) _t` on an immediate local
`_t` of primitive scalar type steps in lockstep under `Miri.Interpreter.Step.step`
and `stepMirFn`, promoting `_t` to the fresh allocation `nextAllocId` through
`forceAllocation`, extending `allocMap` by the new pointer's entry, or reporting
undefined behavior in both machines. -/
theorem evalRvalue_rawPtr_addrOf_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩ :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  step_rawPtr_addrOf_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt hdst_ty
    htgt_ty hne himm hsupply

/-! ## 8. Real-Step `PlaceElem.Deref` (`*ptr`) Reads, Writes, and UB Simulation -/

theorem IsPrimScalarTy.translateTy_layoutIdx {ty : Ty} (h : IsPrimScalarTy ty)
    (layouts : LayoutTable) :
    translateTy { kind := ty.kind, layoutIdx := 0 } layouts = translateTy ty layouts := by
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · simp [translateTy, encodeTyId, hk]
  · simp [translateTy, encodeTyId, hk]
  · cases it <;> simp [translateTy, encodeTyId, hk]
  · cases ut <;> simp [translateTy, encodeTyId, hk]

theorem IsPrimScalarTy.size_align_ok {ty : Ty} (h : IsPrimScalarTy ty)
    (layouts : LayoutTable) :
    Miri.Memory.sizeAsI64 (translateTy ty layouts).layout.size =
      .ok ((translateTy ty layouts).layout.size.bytes.toNat : Int) ∧
    (0 : Int) < ((translateTy ty layouts).layout.size.bytes.toNat : Int) ∧
    ((translateTy ty layouts).layout.size.bytes.toNat : Int) < 2 ^ 63 ∧
    annealScalarReadProvenance (translateTy ty layouts).layout.backendRepr = some false ∧
    (translateTy ty layouts).layout.align.abi.pow2 ≤ 29 ∧
    (translateTy ty layouts).layout.size ≠ Miri.ABI.Size.ZERO := by
  rcases h with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · simp only [translateTy, hk]
    exact ⟨rfl, by decide, Int.ofNat_lt.mpr (by decide), rfl, by decide, by decide⟩
  · simp only [translateTy, hk]
    exact ⟨rfl, by decide, Int.ofNat_lt.mpr (by decide), rfl, by decide, by decide⟩
  · cases it <;> simp only [translateTy, hk] <;>
      exact ⟨rfl, by decide, Int.ofNat_lt.mpr (by decide), rfl, by decide, by decide⟩
  · cases ut <;> simp only [translateTy, hk] <;>
      exact ⟨rfl, by decide, Int.ofNat_lt.mpr (by decide), rfl, by decide, by decide⟩

theorem ImmediateRel.of_ty_kind_eq {ty₁ ty₂ : Ty} {layouts : LayoutTable}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hprim : IsPrimScalarTy ty₁) (hkind : ty₁.kind = ty₂.kind)
    (h : ImmediateRel ty₁ layouts v imm) :
    ImmediateRel ty₂ layouts v imm := by
  have hprim₂ : IsPrimScalarTy ty₂ := by
    rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hkind ▸ hk)
    · exact Or.inr (Or.inl (hkind ▸ hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hkind ▸ hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hkind ▸ hk⟩))
  have htr : translateTy ty₁ layouts = translateTy ty₂ layouts := by
    rw [← hprim.translateTy_layoutIdx layouts, ← hprim₂.translateTy_layoutIdx layouts, hkind]
  cases h with
  | unit hz => exact .unit (htr ▸ hz)
  | scalar sc msc hrel hsz hbool hchar =>
    exact .scalar sc msc hrel (htr ▸ hsz) (fun hb => hbool (hkind.trans hb))
      (fun hc => hchar (hkind.trans hc))
  | scalarPair p1 p2 s1 s2 hs1 hs2 hk =>
    exfalso
    rcases hprim with hb | hb | ⟨_, hb⟩ | ⟨_, hb⟩ <;>
      (rcases hk with ⟨_, hts⟩ | ⟨_, _, hts⟩ <;> rw [hb] at hts <;> cases hts)

theorem lookupDerefPointeeLayout_rawPtr_eq
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {ptrIdx : Local} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? localDecls ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (ptrLay : Miri.Interpreter.LocalLayout) :
    lookupDerefPointeeLayout localDecls layouts ptrIdx ptrLay =
      some (translateTy { kind := pointeeKind, layoutIdx := 0 } layouts) := by
  have hexact : derefPointeeKindHasExactLayout pointeeKind = true := by
    rcases hpk with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> (dsimp only at h; rw [h]; rfl)
  unfold lookupDerefPointeeLayout
  rw [hdecl]
  dsimp only []
  rw [hty]
  dsimp only []
  rw [hexact]
  rfl

theorem annealOffsetMisalignment_ok_of_pow2
    (offset : Miri.ABI.Size) (align : Miri.ABI.Align) (hpow : align.pow2 ≤ 29) :
    ∃ mismatch, annealOffsetMisalignment offset align = .ok mismatch := by
  have hp : ¬ align.pow2 ≥ 64 := by omega
  have his : ∃ b, offset.isAligned align = .ok b := by
    unfold Miri.ABI.Size.isAligned Miri.ABI.Align.bytes
    simp only [hp, ↓reduceIte, bind, Except.bind, pure, Except.pure]
    exact ⟨_, rfl⟩
  obtain ⟨b, hb⟩ := his
  unfold annealOffsetMisalignment
  rw [hb]
  cases b <;> exact ⟨_, rfl⟩

theorem annealOffsetMisalignment_stackBase_eq_none
    (id : Miri.Memory.AllocId) (align : Miri.ABI.Align) (hpow : align.pow2 ≤ 29) :
    annealOffsetMisalignment (Miri.ABI.Size.ofBytes (annealStackBaseAddr id)) align =
      .ok none := by
  unfold annealOffsetMisalignment
  rw [annealStackBaseAddr_isAligned id align hpow]

theorem annealOffsetMisalignment_of_misaligned
    (offset : Miri.ABI.Size) (align : Miri.ABI.Align)
    (hmis : offset.isAligned align = .ok false) :
    annealOffsetMisalignment offset align =
      .ok (some ⟨Miri.ABI.Align.maxAlignedFactor offset, align⟩) := by
  unfold annealOffsetMisalignment
  rw [hmis]

theorem scalar_fromPointer_toPointer_eq (mptr : Miri.Memory.Pointer AnnealProv) :
    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr).toPointer
      annealTargetDataLayout = .ok mptr.withOptionalProvenance := rfl

theorem scalar_fromScalarInt_toPointer_eq
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8) :
    (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toPointer
      annealTargetDataLayout =
      .ok (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) := by
  have hbits : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc.bits) := by
    have hb := hrel.toBits_eq
    rw [hsz8] at hb
    exact hb
  have hlt64 : sc.bits < 2 ^ 64 := by
    have hcan := hrel.canonical
    rw [hsz8] at hcan
    simpa [scalarModulus] using hcan
  have hbv_nat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
    rw [BitVec.toNat_ofNat]
    omega
  let dummyPtr : Miri.Memory.Pointer AnnealProv := ⟨Miri.ABI.Size.ZERO, .wildcard⟩
  have hp_sz : (Miri.Memory.Scalar.fromPointer annealTargetDataLayout dummyPtr).size =
      Miri.ABI.Size.ofBytes 8 := rfl
  unfold Miri.Memory.Scalar.toPointer
  rw [← Miri.Memory.Scalar.fromPointer_size annealTargetDataLayout dummyPtr, hp_sz]
  unfold Miri.Memory.Scalar.toBitsOrPtrInternal Miri.Memory.Scalar.fromScalarInt
  simp only [hbits, Except.mapError, bind, Except.bind, pure, Except.pure,
    throw, throwThe, MonadExceptOf.throw, hbv_nat]
  exact ite_eq_right_iff.mpr fun h => absurd h (by omega)

/-- Exhaustive case split for an immediate raw-pointer local `ptrIdx` related by
`LocalRelLM3_1`: it is `.dead`, `.uninit`, a provenance-less 8-byte integer
scalar (such as a null/forged integer pointer), or a provenance-tracked
`PtrRel` pointer. -/
theorem LocalRelLM3_1.rawPtr_immediate_cases
    {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {ptrDecl : LocalDecl} {layouts : LayoutTable}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    {slot_p : LocalSlot}
    {mls_p : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    (hloc : LocalRelLM3_1 mach allocMap ptrDecl layouts slot_p mls_p)
    (hnot_ind : ∀ mp, mls_p.value ≠ .live (.indirect mp)) :
    (slot_p = .dead ∧ mls_p.value = .dead) ∨
    (slot_p = .uninit ∧ mls_p.value = .live (.immediate .uninit)) ∨
    (∃ sc msc, slot_p = .init (.scalar sc) ∧ sc.sizeBytes = 8 ∧ ScalarRel sc msc ∧
      mls_p.value = .live (.immediate (.scalar (.fromScalarInt msc)))) ∨
    (∃ ptrVal mptr, slot_p = .init (.ptr ptrVal 8) ∧ PtrRel allocMap ptrVal mptr ∧
      mls_p.value = .live (.immediate (.scalar
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))) := by
  cases hloc with
  | rawPtr ptrVal mptr _ _ _ _ _ hptr =>
    exact Or.inr (Or.inr (Or.inr ⟨ptrVal, mptr, rfl, hptr, rfl⟩))
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (hnot_ind mp)
    | dead _ _ => exact Or.inl ⟨rfl, rfl⟩
    | immediate _ _ _ _ hv =>
      rcases hv with ⟨rfl, rfl⟩ | ⟨v, rfl, himm⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · cases himm with
        | unit hz =>
          exfalso
          simp only [translateTy, hty] at hz
          cases hz
        | scalarPair _ _ _ _ _ _ hk =>
          exfalso
          rcases hk with ⟨_, h⟩ | ⟨_, _, h⟩ <;> rw [hty] at h <;> cases h
        | scalar sc msc hrel hsz _ _ =>
          have hsz8 : sc.sizeBytes = 8 := by
            simp only [translateTy, hty, translateSizeBytes] at hsz
            have hb_eq : (8 : UInt64) = UInt64.ofNat sc.sizeBytes :=
              congrArg Miri.ABI.Size.bytes hsz
            have hcan := hrel.validBytes
            rcases hcan with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb_eq ⊢ <;>
              first | rfl | cases hb_eq
          exact Or.inr (Or.inr (Or.inl ⟨sc, msc, rfl, hsz8, hrel, rfl⟩))

theorem evalStatement_assign_use_eq
    (ld : List LocalDecl) (ly : LayoutTable)
    (dst : Place) (op : MirAst.Operand) (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks ld ly) ()
      (translateStmt ⟨.assign dst (.use op), span⟩) m =
      Miri.Interpreter.runRvalue
        (do
          let destPlace ← annealEvalPlace ld ly (translatePlace dst)
          let opTy ← annealEvalOperand ld ly (translateOperand op) (some destPlace.layout)
          let imm ← annealReadImmediate opTy
          annealWriteImmediate imm.imm destPlace) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, annealStepHooks]
  apply runRvalue_eq_of_eq
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt]

theorem annealWriteImmediate_memory_eq
    {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (val : Miri.Interpreter.Immediate AnnealProv)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    annealWriteImmediate val ⟨.memory mp, lay⟩ m = annealWriteMemoryPlace val mp lay m := by
  unfold annealWriteImmediate
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    stack_currentFrame?_singleton m.stack tf hframes]

theorem annealEvalOperand_deref_dead
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {ptrIdx : Nat} {ptrDecl : LocalDecl} {lay : Option Miri.Interpreter.LocalLayout}
    {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : ptrIdx < tf.locals.size)
    (hdecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hmls : tf.locals[ptrIdx]'hlt = ⟨.dead, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy ptrDecl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩)) known m =
      .error (.undefinedBehavior "read of dead local")
        { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt
            (translateTy ptrDecl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (tf.locals[ptrIdx]'hlt).layout = some l →
      l = translateTy ptrDecl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal tf hlt (translateTy ptrDecl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_dead _ hget_c
  rcases hopKind with rfl | rfl <;>
  · unfold translateOperand translatePlace annealEvalOperand
    simp only [List.map, List.toArray, Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, stack_currentFrame?_singleton m.stack tf hframes,
      Option.isNone_some, hres, hgop]
    rfl

theorem annealEvalOperand_deref_live
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {ptrIdx : Nat} {ptrDecl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {known : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : ptrIdx < tf.locals.size)
    (hdecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hmls : tf.locals[ptrIdx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy ptrDecl.ty body.layouts) :
    annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩)) known m =
      (do
        let (mp, pLay) ← annealDerefOperandToMemPlace body.localDecls body.layouts
          ptrIdx opVal (translateTy ptrDecl.ty body.layouts)
        return (⟨.indirect mp, pLay⟩ : Miri.Interpreter.OpTy AnnealProv))
        { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt
            (translateTy ptrDecl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (tf.locals[ptrIdx]'hlt).layout = some l →
      l = translateTy ptrDecl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := known) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal tf hlt (translateTy ptrDecl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  rcases hopKind with rfl | rfl <;>
  · unfold translateOperand translatePlace translateProjectionElem annealEvalOperand
    simp only [List.map, Bool.false_eq_true, ↓reduceIte,
      get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack tf hframes,
      Option.isNone_some, hres, hgop]

theorem annealEvalPlace_deref_dead
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {ptrIdx : Nat} {ptrDecl : LocalDecl} {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : ptrIdx < tf.locals.size)
    (hdecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hmls : tf.locals[ptrIdx]'hlt = ⟨.dead, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy ptrDecl.ty body.layouts) :
    annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
      .error (.undefinedBehavior "read of dead local")
        { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt
            (translateTy ptrDecl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (tf.locals[ptrIdx]'hlt).layout = some l →
      l = translateTy ptrDecl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal tf hlt (translateTy ptrDecl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_dead _ hget_c
  have hne_empty : (!([Miri.MIR.ProjectionElem.Deref].toArray).isEmpty) = true := rfl
  unfold translatePlace translateProjectionElem annealEvalPlace
  simp only [List.map, hne_empty, ↓reduceIte, Bool.false_eq_true,
    get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
    Pure.pure, stack_currentFrame?_singleton m.stack tf hframes,
    Option.isNone_some, hres, hgop]
  rfl

theorem annealEvalPlace_deref_live
    {body : CapturedMir} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {ptrIdx : Nat} {ptrDecl : LocalDecl}
    {opVal : Miri.Interpreter.Operand AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    (hframes : m.stack.frames = #[tf])
    (hlt : ptrIdx < tf.locals.size)
    (hdecl : get? body.localDecls ptrIdx = some ptrDecl)
    (hmls : tf.locals[ptrIdx]'hlt = ⟨.live opVal, lay⟩)
    (hcache : ∀ l, lay = some l → l = translateTy ptrDecl.ty body.layouts) :
    annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
      (do
        let (mp, pLay) ← annealDerefOperandToMemPlace body.localDecls body.layouts
          ptrIdx opVal (translateTy ptrDecl.ty body.layouts)
        return (⟨.memory mp, pLay⟩ : Miri.Interpreter.RuntimePlace AnnealProv))
        { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt
            (translateTy ptrDecl.ty body.layouts)]⟩ } := by
  have hcache' : ∀ l, (tf.locals[ptrIdx]'hlt).layout = some l →
      l = translateTy ptrDecl.ty body.layouts := by
    rw [hmls]; exact hcache
  have hres := annealResolveAndCacheLocalLayout_eq (known := none) hframes hlt hdecl hcache'
  have hget_c := cacheFrameLocalLayout_getLocal tf hlt (translateTy ptrDecl.ty body.layouts)
  rw [hmls] at hget_c
  have hgop := frame_getLocalOperand_live _ hget_c
  have hne_empty : (!([Miri.MIR.ProjectionElem.Deref].toArray).isEmpty) = true := rfl
  unfold translatePlace translateProjectionElem annealEvalPlace
  simp only [List.map, hne_empty, ↓reduceIte, Bool.false_eq_true,
    get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
    Pure.pure, EStateM.pure, stack_currentFrame?_singleton m.stack tf hframes,
    Option.isNone_some, hres, hgop]

theorem annealDerefOperandToMemPlace_uninit
    {ld : List LocalDecl} {ly : LayoutTable}
    {ptrIdx : Local} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    annealDerefOperandToMemPlace ld ly ptrIdx (.immediate .uninit) ptrLay st =
      .error (.undefinedBehavior "read of uninitialized local") st := by
  unfold annealDerefOperandToMemPlace
  rw [lookupDerefPointeeLayout_rawPtr_eq hdecl hty hpk ptrLay]
  rfl

theorem annealDerefOperandToMemPlace_scalarInt
    {ld : List LocalDecl} {ly : LayoutTable}
    {ptrIdx : Local} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hprim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc msc) (hsz8 : sc.sizeBytes = 8)
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    ∃ mismatch,
      annealDerefOperandToMemPlace ld ly ptrIdx (.immediate (.scalar (.fromScalarInt msc)))
          ptrLay st =
        .ok (⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits), .none, mismatch⟩,
          translateTy { kind := pointeeKind, layoutIdx := 0 } ly) st := by
  obtain ⟨_, _, _, _, hpow, _⟩ := hprim.size_align_ok ly
  obtain ⟨mismatch, hmis⟩ := annealOffsetMisalignment_ok_of_pow2
    (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)).offset _ hpow
  refine ⟨mismatch, ?_⟩
  unfold annealDerefOperandToMemPlace
  rw [lookupDerefPointeeLayout_rawPtr_eq hdecl hty hprim ptrLay]
  simp only [annealReadImmediate, Miri.Interpreter.Immediate.toScalar,
    scalar_fromScalarInt_toPointer_eq hrel hsz8,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  rw [hmis]
  rfl

theorem annealDerefOperandToMemPlace_pointer
    {ld : List LocalDecl} {ly : LayoutTable}
    {ptrIdx : Local} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? ld ptrIdx = some ptrDecl)
    (hty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hpk : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (mptr : Miri.Memory.Pointer AnnealProv)
    {mismatch : Option Miri.Memory.Misalignment}
    (hmis : annealOffsetMisalignment mptr.offset
      (translateTy { kind := pointeeKind, layoutIdx := 0 } ly).layout.align.abi = .ok mismatch)
    (ptrLay : Miri.Interpreter.LocalLayout) (st : AnnealStepState) :
    annealDerefOperandToMemPlace ld ly ptrIdx
        (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))
        ptrLay st =
      .ok (⟨mptr.withOptionalProvenance, .none, mismatch⟩,
        translateTy { kind := pointeeKind, layoutIdx := 0 } ly) st := by
  unfold annealDerefOperandToMemPlace
  rw [lookupDerefPointeeLayout_rawPtr_eq hdecl hty hpk ptrLay]
  simp only [annealReadImmediate, Miri.Interpreter.Immediate.toScalar,
    scalar_fromPointer_toPointer_eq mptr,
    Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]
  have hoff_eq : mptr.withOptionalProvenance.offset = mptr.offset := rfl
  rw [hoff_eq, hmis]
  rfl

theorem annealReadMemoryPlace_of_check_err
    (mplace : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) (n : Int) (st : AnnealStepState)
    (hsz : Miri.Memory.sizeAsI64 lay.layout.size = .ok n)
    (e : Miri.Memory.AccessError)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic mplace.ptr n
      .memoryAccess (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .error e) :
    annealReadMemoryPlace mplace lay st =
      .error (.undefinedBehavior "pointer dereference check failed") st := by
  unfold annealReadMemoryPlace
  dsimp only []
  rw [hsz]
  dsimp only []
  rw [hchk]

theorem annealWriteMemoryPlace_of_check_err
    (val : Miri.Interpreter.Immediate AnnealProv)
    (mplace : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) (n : Int) (st : AnnealStepState)
    (hsz : Miri.Memory.sizeAsI64 lay.layout.size = .ok n)
    (e : Miri.Memory.AccessError)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic mplace.ptr n
      .memoryAccess (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .error e) :
    annealWriteMemoryPlace val mplace lay st =
      .error (.undefinedBehavior "pointer dereference check failed") st := by
  unfold annealWriteMemoryPlace
  dsimp only []
  rw [hsz]
  dsimp only []
  rw [hchk]

theorem annealReadMemoryPlace_of_check_ok_misaligned
    (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (bad : Miri.Memory.Misalignment)
    (lay : Miri.Interpreter.LocalLayout) (n : Int) (st : AnnealStepState)
    (hsz : Miri.Memory.sizeAsI64 lay.layout.size = .ok n)
    (checked : Option (Miri.Memory.CheckedPointerAccess Miri.Memory.BorTag))
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr n
      .memoryAccess (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .ok checked) :
    annealReadMemoryPlace ⟨ptr, .none, some bad⟩ lay st =
      .error (.undefinedBehavior "misaligned pointer dereference") st := by
  unfold annealReadMemoryPlace
  dsimp only []
  rw [hsz]
  dsimp only []
  rw [hchk]

theorem annealValidateScalarForTyId_of_scalarRel
    {ty : Ty} {ly : LayoutTable} {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hprim : IsPrimScalarTy ty)
    (hrel : ScalarRel sc msc)
    (hbool : ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    annealValidateScalarForTyId (translateTy ty ly).ty (.fromScalarInt msc) = true := by
  have htoSi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt = .ok msc :=
    rfl
  rcases hprim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
  · obtain ⟨hsz, hb⟩ := hbool hk
    have hty1 : (translateTy ty ly).ty = 1 := by unfold translateTy encodeTyId; rw [hk]
    have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 1 := by
      rw [hrel.size_eq, hsz]; rfl
    rw [hty1]
    rcases hb with hb0 | hb1
    · simp only [annealValidateScalarForTyId, htoSi, hmsc_sz, hrel.data_eq, hb0]; decide
    · simp only [annealValidateScalarForTyId, htoSi, hmsc_sz, hrel.data_eq, hb1]; decide
  · obtain ⟨hsz, hc⟩ := hchar hk
    have hty2 : (translateTy ty ly).ty = 2 := by unfold translateTy encodeTyId; rw [hk]
    have hmsc_sz : msc.size = Miri.ABI.Size.ofBytes 4 := by
      rw [hrel.size_eq, hsz]; rfl
    have hlt128 : sc.bits < 2 ^ 128 := by
      have hcan := hrel.canonical
      rw [hsz] at hcan
      have hm4 : scalarModulus 4 = 2 ^ 32 := rfl
      omega
    have hdata_nat : msc.data.toNat = sc.bits := by
      rw [hrel.data_eq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
    rw [hty2]
    simp only [annealValidateScalarForTyId, htoSi, hmsc_sz, hdata_nat, hc]
    decide
  · cases it <;>
    · have hty_eq : (translateTy ty ly).ty = (translateTy { kind := ty.kind, layoutIdx := 0 } ly).ty :=
        by unfold translateTy encodeTyId; rw [hk]
      rw [hty_eq, hk]; rfl
  · cases ut <;>
    · have hty_eq : (translateTy ty ly).ty = (translateTy { kind := ty.kind, layoutIdx := 0 } ly).ty :=
        by unfold translateTy encodeTyId; rw [hk]
      rw [hty_eq, hk]; rfl

theorem annealReadMemoryPlace_of_check_ok_aligned
    (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (lay : Miri.Interpreter.LocalLayout) (n : Int) (readProv : Bool) (st : AnnealStepState)
    (allocId : Miri.Memory.AllocId) (offset : Miri.ABI.Size)
    (localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (access : Miri.Memory.CheckedPointerAccess Miri.Memory.BorTag)
    (hsz : Miri.Memory.sizeAsI64 lay.layout.size = .ok n)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr n
      .memoryAccess (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .ok (some access))
    (hprov : annealScalarReadProvenance lay.layout.backendRepr = some readProv)
    (haid : access.pointer.allocId = allocId)
    (hoff_eq : access.pointer.offset = offset)
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc)) :
    annealReadMemoryPlace ⟨ptr, .none, none⟩ lay st =
      match localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange offset lay.layout.size) readProv with
      | .ok sc =>
        if annealValidateScalarForTyId lay.ty sc then
          .ok ⟨.scalar sc, lay⟩ st
        else
          .error (.undefinedBehavior "reading invalid value") st
      | .error (.invalidUninitBytes _) =>
        .error (.undefinedBehavior "read of uninitialized memory") st
      | .error (.readPointerAsInt _) | .error (.readPartialPointer _) =>
        .error (.unsupported "pointer-bytes-as-int memory read in scalar/pointer fragment") st
      | .error _ => .error (.invalidProgram "memory read error") st := by
  unfold annealReadMemoryPlace
  dsimp only []
  rw [hsz]
  dsimp only []
  rw [hchk]
  dsimp only []
  rw [hprov]
  dsimp only []
  rw [haid, hoff_eq, hfind]
  rfl

theorem annealWriteMemoryPlace_of_check_ok_scalar
    (ptr : Miri.Memory.Pointer (Option AnnealProv))
    (lay : Miri.Interpreter.LocalLayout) (n : Int) (st : AnnealStepState)
    (allocId : Miri.Memory.AllocId)
    (localAlloc : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (access : Miri.Memory.CheckedPointerAccess Miri.Memory.BorTag)
    (sc : Miri.Memory.Scalar AnnealProv)
    (alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (nextMem : Miri.Memory.MemoryState AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind)
    (hsz : Miri.Memory.sizeAsI64 lay.layout.size = .ok n)
    (hchk : Miri.Memory.checkAndDerefPtr annealPointerArithmetic ptr n
      .memoryAccess (annealResolvePtr st.machine) (annealLookupAlloc st.machine) = .ok (some access))
    (hmut : (access.allocation.mutability != Miri.Memory.Mutability.Mut) = false)
    (haid : access.pointer.allocId = allocId)
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hsc_sz : (sc.size != lay.layout.size) = false)
    (hval : annealValidateScalarForTyId lay.ty sc = true)
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange access.pointer.offset lay.layout.size) sc localAlloc.allocation =
      .ok () alloc')
    (hset : st.machine.memory.setLiveAllocation allocId alloc' = .ok nextMem) :
    annealWriteMemoryPlace (.scalar sc) ⟨ptr, .none, none⟩ lay st =
      .ok () { st with machine := { st.machine with memory := nextMem } } := by
  unfold annealWriteMemoryPlace
  dsimp only []
  rw [hsz]
  dsimp only []
  rw [hchk]
  dsimp only []
  rw [hmut]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [haid, hfind]
  rw [hsc_sz]
  dsimp only [Bool.false_eq_true, ↓reduceIte]
  rw [hval]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hw, hset]

theorem annealReadMemoryPlace_withoutProv_ub
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    (addr : UInt64) (mismatch : Option Miri.Memory.Misalignment) (st : AnnealStepState) :
    ∃ msg, annealReadMemoryPlace
        ⟨Miri.Memory.Pointer.withoutProvenance addr, .none, mismatch⟩
        (translateTy ty ly) st =
      .error (.undefinedBehavior msg) st := by
  obtain ⟨hsz, hgt0, hlt63, _, _, _⟩ := hprim.size_align_ok ly
  exact ⟨_, annealReadMemoryPlace_of_check_err _ _ _ st hsz _
    (checkAndDerefPtr_withoutProvenance_err st.machine addr _ .memoryAccess hgt0 hlt63)⟩

theorem annealWriteMemoryPlace_withoutProv_ub
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    (val : Miri.Interpreter.Immediate AnnealProv)
    (addr : UInt64) (mismatch : Option Miri.Memory.Misalignment) (st : AnnealStepState) :
    ∃ msg, annealWriteMemoryPlace val
        ⟨Miri.Memory.Pointer.withoutProvenance addr, .none, mismatch⟩
        (translateTy ty ly) st =
      .error (.undefinedBehavior msg) st := by
  obtain ⟨hsz, hgt0, hlt63, _, _, _⟩ := hprim.size_align_ok ly
  exact ⟨_, annealWriteMemoryPlace_of_check_err val _ _ _ st hsz _
    (checkAndDerefPtr_withoutProvenance_err st.machine addr _ .memoryAccess hgt0 hlt63)⟩

theorem annealReadMemoryPlace_dead_ub
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag} {offsetBytes : Nat}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hdead : st.machine.memory.live.find? (fun x => x.1 == allocId) = none)
    (mismatch : Option Miri.Memory.Misalignment) :
    ∃ msg, annealReadMemoryPlace
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
           some (.concrete allocId borTag)⟩, .none, mismatch⟩
        (translateTy ty ly) st =
      .error (.undefinedBehavior msg) st := by
  obtain ⟨hsz, hgt0, hlt63, _, _, _⟩ := hprim.size_align_ok ly
  exact ⟨_, annealReadMemoryPlace_of_check_err _ _ _ st hsz _
    (checkAndDerefPtr_deadAlloc_err allocId borTag offsetBytes _ .memoryAccess
      hid hoff hbase hdead hgt0 hlt63)⟩

theorem annealWriteMemoryPlace_dead_ub
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    (val : Miri.Interpreter.Immediate AnnealProv)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag} {offsetBytes : Nat}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hdead : st.machine.memory.live.find? (fun x => x.1 == allocId) = none)
    (mismatch : Option Miri.Memory.Misalignment) :
    ∃ msg, annealWriteMemoryPlace val
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩, .none, mismatch⟩
        (translateTy ty ly) st =
      .error (.undefinedBehavior msg) st := by
  obtain ⟨hsz, hgt0, hlt63, _, _, _⟩ := hprim.size_align_ok ly
  exact ⟨_, annealWriteMemoryPlace_of_check_err val _ _ _ st hsz _
    (checkAndDerefPtr_deadAlloc_err allocId borTag offsetBytes _ .memoryAccess
      hid hoff hbase hdead hgt0 hlt63)⟩

theorem annealReadMemoryPlace_oob_ub
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag} {offsetBytes : Nat}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hoob : localAlloc.allocation.byteSize.bytes.toNat <
      offsetBytes + (translateTy ty ly).layout.size.bytes.toNat)
    (mismatch : Option Miri.Memory.Misalignment) :
    ∃ msg, annealReadMemoryPlace
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩, .none, mismatch⟩
        (translateTy ty ly) st =
      .error (.undefinedBehavior msg) st := by
  obtain ⟨hsz, hgt0, hlt63, _, _, _⟩ := hprim.size_align_ok ly
  exact ⟨_, annealReadMemoryPlace_of_check_err _ _ _ st hsz _
    (checkAndDerefPtr_live_oob_err allocId borTag offsetBytes _ localAlloc .memoryAccess
      hid hoff hbase hfind (Int.ofNat_lt.mp hgt0) hlt63 hoob)⟩

theorem annealReadMemoryPlace_misaligned_ub
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag} {offsetBytes : Nat}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hinbounds : offsetBytes + (translateTy ty ly).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (bad : Miri.Memory.Misalignment) :
    ∃ msg, annealReadMemoryPlace
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
          some (.concrete allocId borTag)⟩, .none, some bad⟩
        (translateTy ty ly) st =
      .error (.undefinedBehavior msg) st := by
  obtain ⟨hsz, hgt0, hlt63, _, _, _⟩ := hprim.size_align_ok ly
  exact ⟨_, annealReadMemoryPlace_of_check_ok_misaligned _ bad _ _ st hsz _
    (checkAndDerefPtr_live_inbounds_ok allocId borTag offsetBytes _ localAlloc .memoryAccess
      hid hoff hbase hfind (Int.ofNat_lt.mp hgt0) hlt63 hinbounds)⟩

theorem annealReadMemoryPlace_zero_offset_eq
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hsz_eq : localAlloc.allocation.byteSize = (translateTy ty ly).layout.size) :
    annealReadMemoryPlace
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId),
          some (.concrete allocId borTag)⟩, .none, none⟩
        (translateTy ty ly) st =
      match localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty ly).layout.size) false with
      | .ok sc =>
        if annealValidateScalarForTyId (translateTy ty ly).ty sc then
          .ok ⟨.scalar sc, translateTy ty ly⟩ st
        else
          .error (.undefinedBehavior "reading invalid value") st
      | .error (.invalidUninitBytes _) =>
        .error (.undefinedBehavior "read of uninitialized memory") st
      | .error (.readPointerAsInt _) | .error (.readPartialPointer _) =>
        .error (.unsupported "pointer-bytes-as-int memory read in scalar/pointer fragment") st
      | .error _ => .error (.invalidProgram "memory read error") st := by
  obtain ⟨hsz, hgt0, hlt63, hprov_flag, _, _⟩ := hprim.size_align_ok ly
  have hinb : 0 + (translateTy ty ly).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hsz_eq]; exact Nat.le_refl _
  have hchk := checkAndDerefPtr_live_inbounds_ok allocId borTag 0
    (translateTy ty ly).layout.size.bytes.toNat localAlloc .memoryAccess
    hid (by show 0 < 2 ^ 32; decide) hbase hfind (Int.ofNat_lt.mp hgt0) hlt63 hinb
  have hoff0_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hoff0_sz, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at hchk
  exact annealReadMemoryPlace_of_check_ok_aligned _ _ _ false st allocId Miri.ABI.Size.ZERO
    localAlloc _ hsz hchk hprov_flag rfl rfl hfind

theorem annealWriteMemoryPlace_zero_offset_scalar_ok
    {ty : Ty} {ly : LayoutTable} (hprim : IsPrimScalarTy ty)
    {allocId : Miri.Memory.AllocId} {borTag : Miri.Memory.BorTag}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    {st : AnnealStepState}
    (hid : allocId.value.toNat < 2 ^ 32)
    (hbase : st.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hfind : st.machine.memory.live.find? (fun x => x.1 == allocId) = some (allocId, localAlloc))
    (hmut : localAlloc.allocation.mutability = .Mut)
    (hsz_eq : localAlloc.allocation.byteSize = (translateTy ty ly).layout.size)
    {msc : Miri.Memory.ScalarInt}
    (hmsc_sz : msc.size = (translateTy ty ly).layout.size)
    (hval : annealValidateScalarForTyId (translateTy ty ly).ty (.fromScalarInt msc) = true)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy ty ly).layout.size)
      (.fromScalarInt msc) localAlloc.allocation = .ok () alloc') :
    annealWriteMemoryPlace (.scalar (.fromScalarInt msc))
        ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId),
          some (.concrete allocId borTag)⟩, .none, none⟩
        (translateTy ty ly) st =
      .ok () { st with machine := { st.machine with
        memory := { st.machine.memory with
          live := (st.machine.memory.live.filter (fun x => x.1 != allocId)).push
            (allocId, ⟨localAlloc.kind, alloc'⟩) } } } := by
  obtain ⟨hsz, hgt0, hlt63, _, _, _⟩ := hprim.size_align_ok ly
  have hinb : 0 + (translateTy ty ly).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat := by
    rw [Nat.zero_add, hsz_eq]; exact Nat.le_refl _
  have hchk := checkAndDerefPtr_live_inbounds_ok allocId borTag 0
    (translateTy ty ly).layout.size.bytes.toNat localAlloc .memoryAccess
    hid (by show 0 < 2 ^ 32; decide) hbase hfind (Int.ofNat_lt.mp hgt0) hlt63 hinb
  have hoff0_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
  rw [hoff0_sz, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at hchk
  have hset := Miri.Memory.MemoryState.setLiveAllocation_of_find
    st.machine.memory allocId localAlloc alloc' hfind
  have hsc_sz : ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size !=
      (translateTy ty ly).layout.size) = false := by
    rw [Miri.Memory.Scalar.fromScalarInt_size, hmsc_sz, bne_self_eq_false]
  have hmut_bne : (localAlloc.allocation.mutability != Miri.Memory.Mutability.Mut) = false := by
    rw [hmut]; rfl
  exact annealWriteMemoryPlace_of_check_ok_scalar _ _ _ st allocId localAlloc _ _ alloc' _
    hsz hchk hmut_bne rfl hfind hsc_sz hval hw hset

/-- Perm-only map on `allocMap` + writing a live immediate local `dstIdx`
(`dstIdx` absent from `allocMap`) preserves `StateRelLM3_1`. -/
theorem StateRelLM3_1.advance_write_immediate_perm_map
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (f : AllocMapEntry → AllocMapEntry)
    (htag : ∀ e, (f e).tag = e.tag)
    (hloc_idx : ∀ e, (f e).localIdx = e.localIdx)
    (halloc_id : ∀ e, (f e).allocId = e.allocId)
    {dstIdx : Local} {dstDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx)
    {hlt_d : dstIdx < tf.locals.size}
    {oldImm newImm : Miri.Interpreter.Immediate AnnealProv}
    (hd_imm : (tf.locals[dstIdx]'hlt_d).value = .live (.immediate oldImm))
    {newSlot : LocalSlot}
    (hnew : LocalRelLM3_1 m.machine (allocMap.map f) dstDecl body.layouts newSlot
      { tf.locals[dstIdx]'hlt_d with value := .live (.immediate newImm) })
    {mem' : Memory}
    (hmem_cal : mem'.activeCallee = none)
    (hmem_stack : mem'.callStack = .nil)
    (hmem_prot : mem'.activeProtectors = .nil)
    (hmem_caller : mem'.callerLocals = .nil)
    (hmem_bor : mem'.borrows = (allocMap.map f).map AllocMapEntry.toBorrowEntry)
    (hmem_next : mem'.nextTag = s.memory.nextTag) :
    StateRelLM3_1 body
      (advanceStmt s (s.frame.locals.set dstIdx newSlot) mem')
      { m with stack := ⟨#[{ { tf with
          locals := tf.locals.set dstIdx
            { tf.locals[dstIdx]'hlt_d with value := .live (.immediate newImm) } hlt_d } with
          location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩ }
      (allocMap.map f) := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, _, _, _, _, _, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  have hfr' := ((hfr.map_preserve f htag halloc_id).update_local hdecl_dst newSlot
    (.live (.immediate newImm)) hnew).advance
  have hnodup' : ((allocMap.map f).map AllocMapEntry.tag).Nodup := by
    have hmap_tag : (allocMap.map f).map AllocMapEntry.tag = allocMap.map AllocMapEntry.tag := by
      rw [List.map_map]
      exact List.map_congr_left (fun e _ => htag e)
    rw [hmap_tag]
    exact halloc.tags_nodup
  refine .mk _ rfl hretCont hretPlace hfr' hmem_cal hmem_stack hmem_prot hmem_caller hmem_bor
    ?_ ?_
  · refine ⟨hnodup', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro e₁ h₁ e₂ h₂ heq
      obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
      rw [hloc_idx, hloc_idx] at heq
      rw [halloc_id, halloc_id]
      exact halloc.local_to_alloc_unique x₁ hx₁ x₂ hx₂ heq
    · intro e₁ h₁ e₂ h₂ heq
      obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
      obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
      rw [halloc_id, halloc_id] at heq
      rw [hloc_idx, hloc_idx]
      exact halloc.alloc_to_local_injective x₁ hx₁ x₂ hx₂ heq
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      rw [hloc_idx]
      exact halloc.target_decl e he
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      rw [halloc_id]
      exact halloc.base_addr_valid e he
    · intro e' he'
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      have hlook := lookupBorrow_map_toBorrowEntry_of_nodup hnodup' he'
      refine ⟨?_, ?_⟩
      · dsimp only [advanceStmt]
        rw [hmem_next, htag]
        exact (halloc.borrow_sync e he).1
      · dsimp only [advanceStmt]
        rw [hmem_bor]
        simpa [AllocMapEntry.toBorrowEntry] using hlook
    · intro e' he' la₁ la₂ hla₁ hla₂
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      rw [halloc_id] at hla₁ hla₂
      exact halloc.live_key_unique e he la₁ la₂ hla₁ hla₂
    · intro tf' htf' e' he'
      injection htf' with h₁
      injection h₁ with h₂
      subst h₂
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp he'
      have hne_d : dstIdx ≠ e.localIdx := Ne.symm (hnot_dst e he)
      obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
      have hget_ne :
          get? (advanceStmt s (s.frame.locals.set dstIdx newSlot) mem').frame.locals
            (f e).localIdx = get? s.frame.locals e.localIdx := by
        dsimp only [advanceStmt]
        rw [hloc_idx, get?_eq_getElem?, List.getElem?_set_ne hne_d, ← get?_eq_getElem?]
      refine ⟨fun slot' hslot' hne_dead => ?_, fun hdead' => ?_⟩
      · rw [hget_ne] at hslot'
        obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_dead
        refine ⟨⟨lay, ?_⟩, hsc, ?_⟩
        · dsimp only []
          rw [hloc_idx, halloc_id, Array.getElem?_set_ne _ hne_d]
          exact hlay
        · intro decl_e hdecl_e
          rw [hloc_idx] at hdecl_e
          rw [halloc_id]
          exact hshape decl_e hdecl_e
      · rw [hget_ne] at hdead'
        rw [halloc_id]
        exact hdead_e hdead'
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : k = dstIdx
    · subst hk
      right
      refine ⟨newImm, (tf.locals[k]'hlt_d).layout, ?_⟩
      dsimp only []
      rw [Array.getElem?_set_self]
    · left
      dsimp only []
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]

/-- Evaluate a `WellTypedScalarOperand` (`constScalar` or `copyLocal` of an
immediate primitive-scalar local) from a `StateRelLM3_1`-related state. -/
theorem evalOperand_scalar_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (hprim : IsPrimScalarTy ty)
    (known : Option Miri.Interpreter.LocalLayout) :
    (∃ m' msg,
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ub ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m = .error (.undefinedBehavior msg) m') ∨
    (∃ sc msc tf',
      evalOperand s.frame.locals op s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) s.frame.locals ∧
      (annealEvalOperand body.localDecls body.layouts (translateOperand op) known >>=
        annealReadImmediate) m =
        .ok ⟨.scalar (.fromScalarInt msc), translateTy ty body.layouts⟩
          { m with stack := ⟨#[tf']⟩ } ∧
      StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap ∧
      ImmediateRel ty body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) ∧
      tf'.localsIdentity = tf.localsIdentity ∧
      (∀ (k : Nat), (tf'.locals[k]?).map Miri.Interpreter.LocalState.value =
        (tf.locals[k]?).map Miri.Interpreter.LocalState.value)) := by
  rcases id hstate with
    ⟨tf₀, hframes₀, _, _, hfr, _, _, _, hcaller, _, _, _⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  have hsame : { m with stack := ⟨#[tf]⟩ } = m :=
    stepState_with_same_singleton m tf hframes
  cases hop with
  | constScalar c sc hval hprim_c hsz hcan hlaysz hbool hchar =>
    obtain ⟨msc, htry, hrel⟩ := tryFromUInt_of_valid_canonical hsz hcan
    have heval_a :
        evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals = .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand
      dsimp only
      rw [hval]; rfl
    have heval_m : annealEvalOperand body.localDecls body.layouts
        (translateOperand (.constant c)) known m =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩ m := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hval]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton m.stack tf hframes, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry, hprim_c.layoutOfEncoded]
    right
    refine ⟨sc, msc, tf, heval_a, ?_, by rw [hsame]; exact hstate,
      .scalar sc msc hrel hlaysz hbool hchar, rfl, fun _ => rfl⟩
    rw [EStateM.bind_eq_ok heval_m, hsame]
    rfl
  | copyLocal idx decl hdecl hsz_nz himm =>
    obtain ⟨slot, mls, _, hlt_mf, hslot, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hcache := hloc.cachedLayout_eq
    have himm' := himm mls hmls
    have htr : translateOperand (.copy ⟨idx, .nil⟩) = .Copy ⟨idx, #[]⟩ := rfl
    cases hloc with
    | rawPtr _ _ _ _ _ _ hty_raw _ =>
      exfalso
      rcases hprim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm' mp)
      | dead _ _ =>
        left
        refine ⟨{ m with stack := ⟨#[cacheFrameLocalLayout tf idx hlt_mf
            (translateTy decl.ty body.layouts)]⟩ }, "read of dead local", ?_, ?_⟩
        · simp [evalOperand, hslot]
        · rw [htr]
          exact EStateM.bind_eq_error (annealEvalOperand_copy_dead hframes hlt_mf hdecl hmls_eq hcache)
      | immediate _ imm _ _ hval =>
        let tf' := cacheFrameLocalLayout tf idx hlt_mf (translateTy decl.ty body.layouts)
        have hstate' : StateRelLM3_1 body s { m with stack := ⟨#[tf']⟩ } allocMap :=
          hstate.cache_layout hframes hdecl hlt_mf
        rcases hval with ⟨rfl, rfl⟩ | ⟨v, rfl, himmRel⟩
        · left
          refine ⟨{ m with stack := ⟨#[tf']⟩ }, "read of uninitialized local", ?_, ?_⟩
          · simp [evalOperand, hslot]
          · rw [htr, EStateM.bind_eq_ok
              (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
            rfl
        · obtain ⟨sc, msc, rfl, rfl, hrel, hsz_sc, hbool, hchar⟩ :=
            himmRel.of_primitive_scalar hprim
          right
          refine ⟨sc, msc, tf', ?_, ?_, hstate',
            .scalar sc msc hrel hsz_sc hbool hchar, rfl, ?_⟩
          · simp [evalOperand, readProjectedValue, hslot]
          · rw [htr, EStateM.bind_eq_ok
              (annealEvalOperand_copy_live hframes hlt_mf hdecl hmls_eq hcache)]
            rfl
          · intro k
            simp only [tf', cacheFrameLocalLayout]
            by_cases hki : idx = k
            · subst hki
              rw [Array.getElem?_set_self, Array.getElem?_eq_getElem hlt_mf]
              rfl
            · rw [Array.getElem?_set_ne _ hki]

/-- Extract the uninitialized-mask and scalar-read facts from `LocalRelLM3_1`
when `mls_t` is `.indirect (stackAllocPlace e.allocId)` without substituting
`mls_t` into the `LocalRel` index before `cases` (avoiding expensive `LocalState`
`noConfusion` unification). -/
theorem LocalRelLM3_1.indirect_stackAllocPlace_spec
    {mach : AnnealMachine} {allocMap : List AllocMapEntry}
    {tgtDecl : LocalDecl} {layouts : LayoutTable}
    {slot_t : LocalSlot}
    {mls_t : Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout}
    {lay_t : Option Miri.Interpreter.LocalLayout}
    {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hloc_t : LocalRelLM3_1 mach allocMap tgtDecl layouts slot_t mls_t)
    (hmls_eq : mls_t = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_t⟩)
    (hbase : mach.lookupBaseAddr e.allocId = some (annealStackBaseAddr e.allocId))
    (hfind_la : mach.memory.live.find? (fun x => x.1 == e.allocId) = some (e.allocId, localAlloc))
    (huniq : ∀ la₁ la₂, (e.allocId, la₁) ∈ mach.memory.live.toList →
      (e.allocId, la₂) ∈ mach.memory.live.toList → la₁ = la₂)
    (hnz : (translateTy tgtDecl.ty layouts).layout.size ≠ Miri.ABI.Size.ZERO) :
    (slot_t = .uninit →
      localAlloc.allocation.initializationMask.isRangeInitialized
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO
          (translateTy tgtDecl.ty layouts).layout.size) ≠ .ok (.ok ())) ∧
    (∀ sc, slot_t = .init (.scalar sc) →
      (translateTy tgtDecl.ty layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
      (tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
      (tgtDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
      ∃ msc, ScalarRel sc msc ∧
        localAlloc.allocation.readScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy tgtDecl.ty layouts).layout.size) false =
          .ok (.fromScalarInt msc)) := by
  have hval_eq : mls_t.value = .live (.indirect (stackAllocPlace e.allocId)) := by
    rw [hmls_eq]
  cases hloc_t with
  | rawPtr _ _ _ _ _ _ _ _ => cases hval_eq
  | base hb =>
    cases hb with
    | dead _ _ => cases hval_eq
    | immediate _ _ _ _ _ => cases hval_eq
    | indirect _ mp _ _ _ hmp_t =>
      dsimp only at hval_eq
      injection hval_eq with h1
      injection h1 with hmp_eq
      subst hmp_eq
      cases hmp_t with
      | mk aId bTag bAddr rOff la_mp hprov_mp _ _ hl_mp hb_mp hovf_mp hptr_mp _ _ _
          hun_mp _ hsc_mp =>
        have haId : aId = e.allocId := by
          dsimp only [stackAllocPlace] at hprov_mp
          injection hprov_mp with hp1
          injection hp1 with hp2 _
          exact hp2.symm
        subst haId
        have hfind_mem := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some hfind_la)
        have hla_eq : la_mp = localAlloc := huniq la_mp localAlloc hl_mp hfind_mem
        subst hla_eq
        have hr0 : rOff = Miri.ABI.Size.ZERO := by
          have hb_eq : bAddr = annealStackBaseAddr e.allocId := by
            rw [hbase] at hb_mp; exact Option.some.inj hb_mp.symm
          subst hb_eq
          have hroff_nat : rOff.bytes.toNat = 0 := by
            have h := MemPlaceRel.relOffset_bytes_eq hovf_mp hptr_mp
            have hoff_b : (stackAllocPlace e.allocId).ptr.offset.bytes =
                annealStackBaseAddr e.allocId := rfl
            rw [hoff_b, Nat.sub_self] at h
            exact h
          have hr0_u : rOff.bytes = 0 := UInt64.toNat_inj.mp hroff_nat
          cases rOff; dsimp only at hr0_u; subst hr0_u; rfl
        subst hr0
        exact ⟨fun hs => hun_mp (by rw [hs]) hnz, fun sc hs => hsc_mp sc (by rw [hs])⟩

/-- Per-entry map applied to `allocMap` on a deref read when `allocMap` has two
or more entries (`updateAllocMapOnDerefRead allocMap targetLocal rTag =
allocMap.map (derefReadMapFn allocMap targetLocal rTag)`). -/
def derefReadMapFn (allocMap : List AllocMapEntry) (targetLocal : Local) (rTag : Nat) :
    AllocMapEntry → AllocMapEntry :=
  match allocMap with
  | _ :: _ :: _ => fun x => x.updateOnRead targetLocal rTag
  | _ => id

theorem derefReadMapFn_tag (allocMap : List AllocMapEntry) (targetLocal : Local) (rTag : Nat)
    (x : AllocMapEntry) :
    (derefReadMapFn allocMap targetLocal rTag x).tag = x.tag := by
  unfold derefReadMapFn AllocMapEntry.updateOnRead
  cases allocMap with
  | nil => rfl
  | cons _ tail =>
    cases tail with
    | nil => rfl
    | cons _ _ =>
      dsimp only
      cases Nat.beq x.localIdx targetLocal with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.beq rTag x.tag with
        | true => rfl
        | false =>
          dsimp only
          cases x.perm <;> rfl

theorem derefReadMapFn_localIdx (allocMap : List AllocMapEntry) (targetLocal : Local)
    (rTag : Nat) (x : AllocMapEntry) :
    (derefReadMapFn allocMap targetLocal rTag x).localIdx = x.localIdx := by
  unfold derefReadMapFn AllocMapEntry.updateOnRead
  cases allocMap with
  | nil => rfl
  | cons _ tail =>
    cases tail with
    | nil => rfl
    | cons _ _ =>
      dsimp only
      cases Nat.beq x.localIdx targetLocal with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.beq rTag x.tag with
        | true => rfl
        | false =>
          dsimp only
          cases x.perm <;> rfl

theorem derefReadMapFn_allocId (allocMap : List AllocMapEntry) (targetLocal : Local)
    (rTag : Nat) (x : AllocMapEntry) :
    (derefReadMapFn allocMap targetLocal rTag x).allocId = x.allocId := by
  unfold derefReadMapFn AllocMapEntry.updateOnRead
  cases allocMap with
  | nil => rfl
  | cons _ tail =>
    cases tail with
    | nil => rfl
    | cons _ _ =>
      dsimp only
      cases Nat.beq x.localIdx targetLocal with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.beq rTag x.tag with
        | true => rfl
        | false =>
          dsimp only
          cases x.perm <;> rfl

theorem lookupAllocMapByTag_of_mem_nodup
    {allocMap : List AllocMapEntry}
    (hnodup : (allocMap.map AllocMapEntry.tag).Nodup)
    {e : AllocMapEntry} (he : e ∈ allocMap) {t : Nat} (ht : e.tag = t) :
    lookupAllocMapByTag allocMap t = some e := by
  induction allocMap with
  | nil => cases he
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    unfold lookupAllocMapByTag
    rcases List.mem_cons.mp he with rfl | hmem
    · simp [← ht]
    · have hne : Nat.beq hd.tag t = false := by
        cases h : Nat.beq hd.tag t
        · rfl
        · have heq := (Nat.eq_of_beq_eq_true h).trans ht.symm
          exact absurd (heq ▸ List.mem_map_of_mem hmem) hnodup.1
      rw [hne]
      exact ih hnodup.2 hmem

/-- Computable post-step `allocMap'` for `_d = (copy|move) *_p`: freezes foreign
active borrows on the target local when `_p` holds a tracked pointer and
`allocMap` has `≥ 2` entries, and leaves `allocMap` unchanged otherwise. -/
def derefReadNextAllocMap (locals : List LocalSlot) (allocMap : List AllocMapEntry)
    (ptrIdx : Local) : List AllocMapEntry :=
  match get? locals ptrIdx with
  | some (.init (.ptr ptrVal 8)) =>
    match lookupAllocMapByTag allocMap ptrVal.tag with
    | some e => allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)
    | none => allocMap
  | _ => allocMap

/-- **`step_deref_read_simulation_explicit` (`LM-3.1` Deliverable 2 — Explicit `allocMap'` Deref Read)**:
one real step of `_d = copy *_p` or `_d = move *_p` from any `StateRelLM3_1`-related
state under the computable post-step borrow table
`derefReadNextAllocMap s.frame.locals allocMap ptrIdx`. -/
theorem step_deref_read_simulation_explicit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal, get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl → decl.ty.kind = dstDecl.ty.kind)) :
    StepRelLM3_1 body m (derefReadNextAllocMap s.frame.locals allocMap ptrIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_ptr⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts ⟨dstIdx, .nil⟩
    (opKind ⟨ptrIdx, .cons .deref .nil⟩) span m
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval : annealEvalPlace body.localDecls body.layouts (translatePlace ⟨dstIdx, .nil⟩) m =
      .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d
            (translateTy dstDecl.ty body.layouts)]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨tfa', hframes_a, _, _, hfra, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
  injection hframes_a with hfa₁
  injection hfa₁ with hfa₂
  subst hfa₂
  obtain ⟨slot_p, mls_p, _, hlt_p, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ :=
    hfra.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l →
      l = translateTy ptrDecl.ty body.layouts := hloc_p.cachedLayout_eq
  have himm_ptr_a := (himm_ptr.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)) _ hmls_p
  let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_p (translateTy ptrDecl.ty body.layouts)
  have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
    hstate_a.cache_layout rfl hdecl_ptr hlt_p
  obtain ⟨tfb', hframes_b, _, _, hfrb, _, _, _, _, _, halloc_b, _⟩ := id hstate_b
  injection hframes_b with hfb₁
  injection hfb₁ with hfb₂
  subst hfb₂
  have hprim0 : IsPrimScalarTy { kind := dstDecl.ty.kind, layoutIdx := 0 } := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
    · exact Or.inr (Or.inr (Or.inl ⟨it, hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hk⟩))
  have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
      translateTy dstDecl.ty body.layouts :=
    hdst_prim.translateTy_layoutIdx body.layouts
  rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_ptr_a with
    ⟨rfl, hmp_dead⟩ | ⟨rfl, hmp_uninit⟩ |
    ⟨sc_p, msc_p, rfl, hsz8_p, hrel_p, hmp_sc⟩ |
    ⟨ptrVal, mptr, rfl, hptr_rel, hmp_ptr⟩
  · -- Case 1: `_p` is `.dead` -> UB in both.
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      rcases hopKind with rfl | rfl <;>
        simp [evalStmt, evalRvalue, evalOperand, hslot_p]
    have hmls_dead : tfa.locals[ptrIdx]'hlt_p = ⟨.dead, mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨_, _⟩; dsimp only at hmp_dead; subst hmp_dead; rfl
    have hop_err := annealEvalOperand_deref_dead hopKind (m := { m with stack := ⟨#[tfa]⟩ })
      rfl hlt_p hdecl_ptr hmls_dead hcache_p
      (known := some (translateTy dstDecl.ty body.layouts))
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hop_err]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 2: `_p` is `.uninit` -> UB in both.
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      rcases hopKind with rfl | rfl <;>
        simp [evalStmt, evalRvalue, evalOperand, hslot_p]
    have hmls_un : tfa.locals[ptrIdx]'hlt_p = ⟨.live (.immediate .uninit), mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨_, _⟩; dsimp only at hmp_uninit; subst hmp_uninit; rfl
    have hop_un := annealEvalOperand_deref_live hopKind (m := { m with stack := ⟨#[tfa]⟩ })
      rfl hlt_p hdecl_ptr hmls_un hcache_p
      (known := some (translateTy dstDecl.ty body.layouts))
    have hder_un := annealDerefOperandToMemPlace_uninit (ly := body.layouts) hdecl_ptr hptr_ty hdst_prim
      (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]
      have hop_err : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_un, EStateM.bind_eq_error hder_un]
      rw [EStateM.bind_eq_error hop_err]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 3: `_p` holds a provenance-less integer/null scalar -> UB in both.
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      rcases hopKind with rfl | rfl <;>
        simp [evalStmt, evalRvalue, evalOperand, hslot_p]
    have hmls_sc : tfa.locals[ptrIdx]'hlt_p =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_p))), mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨_, _⟩; dsimp only at hmp_sc; subst hmp_sc; rfl
    have hop_sc := annealEvalOperand_deref_live hopKind (m := { m with stack := ⟨#[tfa]⟩ })
      rfl hlt_p hdecl_ptr hmls_sc hcache_p
      (known := some (translateTy dstDecl.ty body.layouts))
    obtain ⟨mismatch, hder_sc⟩ := annealDerefOperandToMemPlace_scalarInt hdecl_ptr hptr_ty hprim0
      hrel_p hsz8_p (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
    rw [hlay0_eq] at hder_sc
    obtain ⟨msg, hread_ub⟩ := annealReadMemoryPlace_withoutProv_ub hdst_prim
      (UInt64.ofNat sc_p.bits) mismatch { m with stack := ⟨#[tfb]⟩ }
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior msg)) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]
      have hop_ok : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.indirect ⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc_p.bits),
            .none, mismatch⟩, translateTy dstDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_sc, EStateM.bind_eq_ok hder_sc]; rfl
      rw [EStateM.bind_eq_ok hop_ok]
      dsimp only [annealReadImmediate]
      rw [EStateM.bind_eq_error hread_ub]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 4: `_p` holds a `PtrRel`-related pointer `ptrVal` / `mptr`.
    have hmls_ptr : tfa.locals[ptrIdx]'hlt_p =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨_, _⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
    have hop_ptr := annealEvalOperand_deref_live hopKind (m := { m with stack := ⟨#[tfa]⟩ })
      rfl hlt_p hdecl_ptr hmls_ptr hcache_p
      (known := some (translateTy dstDecl.ty body.layouts))
    rcases hptr_rel with ⟨allocId, borTag, hprov_eq, hid_lt, hoff_lt, haddr_eq, ⟨e, he, htag, rfl⟩⟩
    obtain ⟨_, _, hbase⟩ := halloc_a.base_addr_valid e he
    obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc_a.target_decl e he
    obtain ⟨slot_t, mls_t, _, _, hslot_t, hmls_t, _, hloc_t⟩ := hfrb.lookup_local hdecl_tgt
    obtain ⟨hlive_e, hdead_e⟩ := halloc_b.local_alloc_sync tfb rfl e he
    have hbor_look := (halloc_a.borrow_sync e he).2
    by_cases ht_dead : slot_t = .dead
    · -- Subcase 4a: pointee local `e.localIdx` is `.dead` -> dangling UB in both!
      subst ht_dead
      have ha : evalStmt s
          ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        have hop_ub : evalOperand s.frame.locals (opKind ⟨ptrIdx, .cons .deref .nil⟩)
            s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub := by
          rcases hopKind with rfl | rfl <;>
          · unfold evalOperand readProjectedValue
            dsimp only []
            rw [hslot_p, hcaller]
            dsimp only []
            rw [← htag, hbor_look]
            dsimp only []
            cases e.perm <;> simp [hslot_t]
        unfold evalStmt evalRvalue
        dsimp only []
        rw [hop_ub]
      obtain ⟨_, _, _, _, hpow, _⟩ := hprim0.size_align_ok body.layouts
      obtain ⟨mismatch, hmis⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset _ hpow
      have hder_ok := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hdst_prim mptr hmis
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      rw [hlay0_eq] at hder_ok
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
            some (.concrete e.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq haddr_eq ⊢
        subst hprov_eq haddr_eq
        rfl
      rw [hmptr_opt] at hder_ok
      obtain ⟨msg, hread_ub⟩ := annealReadMemoryPlace_dead_ub (ly := body.layouts)
        (borTag := borTag) hdst_prim hid_lt hoff_lt hbase
        (hdead_e hslot_t) mismatch (st := { m with stack := ⟨#[tfb]⟩ })
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
          m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior msg)) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]
        have hop_ok : annealEvalOperand body.localDecls body.layouts
            (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩))
            (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
            .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes
                (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
                some (.concrete e.allocId borTag)⟩, .none, mismatch⟩,
              translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
          rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
        rw [EStateM.bind_eq_ok hop_ok]
        dsimp only [annealReadImmediate]
        rw [EStateM.bind_eq_error hread_ub]
      rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · -- Subcase 4b: pointee local `e.localIdx` is live (`slot_t ≠ .dead`).
      have ht_ne_some_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
        rw [hslot_t]; intro h; exact ht_dead (Option.some.inj h)
      obtain ⟨hoff0, hperm_ok, hkind_tgt⟩ := hlive_ptr ptrVal hslot_p e he htag ht_ne_some_dead
      have htgt_kind_eq : tgtDecl.ty.kind = dstDecl.ty.kind := hkind_tgt tgtDecl hdecl_tgt
      have htr_tgt : translateTy tgtDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
        rw [← htgt_prim.translateTy_layoutIdx body.layouts, htgt_kind_eq, hlay0_eq]
      obtain ⟨⟨lay_t, hlay_t⟩, hsc_t, hshape_f⟩ :=
        hlive_e slot_t hslot_t ht_dead
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hshape_f tgtDecl hdecl_tgt
      rw [htr_tgt] at hshape_la
      have hmptr_zero : mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId) := by
        rw [haddr_eq, hoff0, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
      obtain ⟨_, _, _, _, hpow, hnz_sz⟩ := hdst_prim.size_align_ok body.layouts
      have hmis0 : annealOffsetMisalignment mptr.offset
          (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok none := by
        rw [hlay0_eq, hmptr_zero]
        exact annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow
      have hder_ok := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hdst_prim mptr hmis0
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      rw [hlay0_eq] at hder_ok
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
            some (.concrete e.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_zero ⊢
        subst hprov_eq hmptr_zero
        rfl
      rw [hmptr_opt] at hder_ok
      have hop_ok : annealEvalOperand body.localDecls body.layouts
          (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              some (.concrete e.allocId borTag)⟩, .none, none⟩,
            translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
      have hread_eq := annealReadMemoryPlace_zero_offset_eq hdst_prim hid_lt hbase hfind_la
        hshape_la.1 (borTag := borTag) (st := { m with stack := ⟨#[tfb]⟩ })
      -- Inspect `LocalRelLM3_1` at `e.localIdx` (which is `.indirect (stackAllocPlace e.allocId)`).
      rw [hlay_t] at hmls_t
      have hmls_t_eq' : mls_t = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_t⟩ :=
        Option.some.inj hmls_t.symm
      obtain ⟨hun_la', hsc_la'⟩ := hloc_t.indirect_stackAllocPlace_spec hmls_t_eq' hbase hfind_la
        (halloc_a.live_key_unique e he) (htr_tgt ▸ hnz_sz)
      have hun_la : slot_t = .uninit →
          localAlloc.allocation.initializationMask.isRangeInitialized
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO
              (translateTy dstDecl.ty body.layouts).layout.size) ≠ .ok (.ok ()) := by
        rw [← htr_tgt]; exact hun_la'
      have hsc_la : ∀ sc, slot_t = .init (.scalar sc) →
          (translateTy tgtDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes ∧
          (tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1)) ∧
          (tgtDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) ∧
          ∃ msc, ScalarRel sc msc ∧
            localAlloc.allocation.readScalar annealTargetDataLayout
              (Miri.Memory.allocRange Miri.ABI.Size.ZERO
                (translateTy dstDecl.ty body.layouts).layout.size) false =
              .ok (.fromScalarInt msc) := by
        intro sc hs
        rw [← htr_tgt]
        exact hsc_la' sc hs
      cases hs_t : slot_t with
      | dead => exact absurd hs_t ht_dead
      | uninit =>
            -- Subcase 4b-i: pointee is `.uninit` -> UB in both!
            have ha : evalStmt s
                ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
                body.localDecls body.layouts = MirStepNode.fail .ub := by
              have hop_ub : evalOperand s.frame.locals (opKind ⟨ptrIdx, .cons .deref .nil⟩)
                  s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals = .ub := by
                rcases hopKind with rfl | rfl <;>
                · unfold evalOperand readProjectedValue
                  dsimp only []
                  rw [hslot_p, hcaller]
                  dsimp only []
                  rw [← htag, hbor_look]
                  dsimp only []
                  cases hp : e.perm <;> simp [hslot_t, hs_t]
              unfold evalStmt evalRvalue
              dsimp only []
              rw [hop_ub]
            obtain ⟨info, hread_err⟩ := hshape_la.uninit_readScalar_err (hun_la hs_t) false
            have hread_m : annealReadMemoryPlace
                ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                  some (.concrete e.allocId borTag)⟩, .none, none⟩
                (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ } =
                .error (.undefinedBehavior "read of uninitialized memory")
                  { m with stack := ⟨#[tfb]⟩ } := by
              rw [hread_eq, hread_err]
            have hm_err : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt
                  ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
                m =
                ({ m with stack := ⟨#[tfb]⟩ },
                  .error (.undefinedBehavior "read of uninitialized memory")) := by
              rw [hm_stmt]
              unfold Miri.Interpreter.runRvalue
              rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
              dsimp only [annealReadImmediate]
              rw [EStateM.bind_eq_error hread_m]
            rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
              hm_err]
            exact .ub _ _
          | init v_t =>
            -- Subcase 4b-ii: pointee holds initialized scalar `sc_t`.
            obtain ⟨sc_t, rfl⟩ := hsc_t v_t hs_t
            obtain ⟨hsz_t, hbool_t, hchar_t, msc_t, hrel_t, hread_ok⟩ := hsc_la sc_t hs_t
            have hop_anneal : evalOperand s.frame.locals (opKind ⟨ptrIdx, .cons .deref .nil⟩)
                s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
                .ok (.scalar sc_t) s.frame.locals := by
              rcases hopKind with rfl | rfl <;>
              · unfold evalOperand readProjectedValue
                dsimp only []
                rw [hslot_p]
                dsimp only []
                rw [← htag, hbor_look]
                dsimp only []
                cases hp : e.perm
                · rw [hslot_t, hs_t]
                · rw [hslot_t, hs_t]
                · rw [hslot_t, hs_t]
                · exact absurd hp hperm_ok
            have himm_dst_rel : ImmediateRel dstDecl.ty body.layouts (.scalar sc_t)
                (.scalar (.fromScalarInt msc_t)) :=
              ImmediateRel.of_ty_kind_eq htgt_prim htgt_kind_eq
                (.scalar sc_t msc_t hrel_t hsz_t hbool_t hchar_t)
            -- Destination local `_d` in `tfb`:
            have hpd_ne : ptrIdx ≠ dstIdx := by
              intro hpd
              subst hpd
              rw [hdecl_dst] at hdecl_ptr
              injection hdecl_ptr with hd_eq
              subst hd_eq
              rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
                rw [hk] at hptr_ty <;> cases hptr_ty
            have hlt_db : dstIdx < tfb.locals.size := by
              simp only [tfb, tfa, cacheFrameLocalLayout_size]; exact hlt_d
            have hdb_get : tfb.locals[dstIdx]? =
                some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
              simp only [tfb, tfa, cacheFrameLocalLayout]
              rw [Array.getElem?_set_ne _ hpd_ne, Array.getElem?_set_self, hmls_d_eq]
            have hdb_elem : tfb.locals[dstIdx]'hlt_db =
                { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } :=
              Option.some.inj ((Array.getElem?_eq_getElem hlt_db).symm.trans hdb_get)
            have hd_Lay : (tfb.locals[dstIdx]'hlt_db).layout =
                some (translateTy dstDecl.ty body.layouts) := by
              rw [hdb_elem]
            have hd_Val : (tfb.locals[dstIdx]'hlt_db).value = mls_d.value := by
              rw [hdb_elem]
            -- Compute Anneal's `evalRvalue` borrow update (`allocMap.map f_read`).
            have hf_tag : ∀ x, (derefReadMapFn allocMap e.localIdx ptrVal.tag x).tag = x.tag :=
              derefReadMapFn_tag allocMap e.localIdx ptrVal.tag
            have hf_loc : ∀ x,
                (derefReadMapFn allocMap e.localIdx ptrVal.tag x).localIdx = x.localIdx :=
              derefReadMapFn_localIdx allocMap e.localIdx ptrVal.tag
            have hf_aid : ∀ x,
                (derefReadMapFn allocMap e.localIdx ptrVal.tag x).allocId = x.allocId :=
              derefReadMapFn_allocId allocMap e.localIdx ptrVal.tag
            have hrv_anneal :
                evalRvalue s.frame.locals (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩))
                  s.memory body.localDecls body.layouts =
                .ok (.scalar sc_t) s.frame.locals
                  { s.memory with
                    borrows := (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)).map
                      AllocMapEntry.toBorrowEntry } := by
              unfold evalRvalue
              dsimp only []
              rw [hop_anneal]
              match hm_cases : allocMap with
              | [] => exact False.elim (List.not_mem_nil he)
              | [single] =>
                have hbor1 : s.memory.borrows = [single.toBorrowEntry] := by
                  simpa using hbor
                rcases hopKind with rfl | rfl <;>
                · rw [hbor1]
                  simp only [List.map_cons, List.map_nil, derefReadMapFn, id_eq]
                  rw [← hbor1]
              | e₁ :: e₂ :: rest =>
                have hfrz := freezeDerefReadBorrowsAt_map_toBorrowEntry s.frame.locals e₁ e₂ rest
                  (hm_cases ▸ halloc_a.tags_nodup) ptrIdx ptrVal 8 e (hm_cases ▸ he) htag hslot_p
                rcases hopKind with rfl | rfl <;>
                · simp only [hbor, List.map_cons] at hfrz ⊢
                  rw [hfrz]
                  simp only [derefReadMapFn, updateAllocMapOnDerefRead, List.map_cons]
            have hval_t : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
                (.fromScalarInt msc_t) = true :=
              annealValidateScalarForTyId_of_scalarRel hdst_prim hrel_t
                (fun hb => hbool_t (htgt_kind_eq.trans hb))
                (fun hc => hchar_t (htgt_kind_eq.trans hc))
            have hread_m : annealReadMemoryPlace
                ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                  some (.concrete e.allocId borTag)⟩, .none, none⟩
                (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ } =
                .ok ⟨.scalar (.fromScalarInt msc_t), translateTy dstDecl.ty body.layouts⟩
                  { m with stack := ⟨#[tfb]⟩ } := by
              rw [hread_eq, hread_ok]
              dsimp only []
              rw [hval_t]
              rfl
            -- Case split on whether `_d` is `.dead` or live immediate.
            have hnext_eq : derefReadNextAllocMap s.frame.locals allocMap ptrIdx =
                allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag) := by
              simp only [derefReadNextAllocMap, hslot_p,
                lookupAllocMapByTag_of_mem_nodup halloc_a.tags_nodup he htag]
            have hd_live_helper :
                ∀ oldImm, mls_d.value = .live (.immediate oldImm) → slot_d ≠ .dead →
                  StepRelLM3_1 body m (derefReadNextAllocMap s.frame.locals allocMap ptrIdx)
                    (evalStmt s
                      ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
                      body.localDecls body.layouts)
                    (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) ()
                      m) := by
              intro oldImm hmd_imm hsd_ne
              have hnot_dst : ∀ x ∈ allocMap, x.localIdx ≠ dstIdx :=
                hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_dst
              have hnot_dst' :
                  ∀ x ∈ allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag),
                    x.localIdx ≠ dstIdx := by
                intro x hx
                obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
                rw [hf_loc]
                exact hnot_dst y hy
              have hdb_eq : tfb.locals[dstIdx]? =
                  some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
                rw [hdb_get]
                rcases mls_d with ⟨v0, l0⟩
                dsimp only at hmd_imm
                subst hmd_imm
                rfl
              have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_eq
              have hw_ok := annealWriteImmediate_live
                (val := .scalar (.fromScalarInt msc_t))
                (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
                (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
              have hm_ok : Miri.Interpreter.Step.evalStatement
                  (annealStepHooks body.localDecls body.layouts) ()
                  (translateStmt
                    ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
                  m =
                  ({ m with stack := ⟨#[{ tfb with
                      locals := tfb.locals.set dstIdx
                        { tfb.locals[dstIdx]'hlt_db with
                          value := .live (.immediate (.scalar (.fromScalarInt msc_t))) }
                        hlt_db }]⟩ },
                    .ok ()) := by
                rw [hm_stmt]
                unfold Miri.Interpreter.runRvalue
                rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
                dsimp only [annealReadImmediate]
                rw [EStateM.bind_eq_ok hread_m, hw_ok]
              have hloc_b : tfb.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
                hfrb.location_eq
              rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
                rfl hloc_b]
              have hinv_d := invalidateConflictingBorrows_eq_of_not_mem
                (borrows := (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)).map
                  AllocMapEntry.toBorrowEntry) rfl
                dstIdx none hnot_dst'
              have ha_ok : evalStmt s
                  ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
                  body.localDecls body.layouts =
                  MirStepNode.step
                    (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc_t)))
                      { s.memory with
                        borrows := (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag)).map
                          AllocMapEntry.toBorrowEntry }) := by
                unfold evalStmt
                dsimp only []
                rw [hrv_anneal]
                dsimp only []
                rw [hslot_d]
                cases slot_d with
                | dead => exact absurd rfl hsd_ne
                | uninit =>
                  simp only [set?_eq_some_set hlt_af_d, hprot, hinv_d]
                | init _ =>
                  simp only [set?_eq_some_set hlt_af_d, hprot, hinv_d]
              rw [ha_ok, hnext_eq]
              apply StepRelLM3_1.step
              have hnew_d :
                  LocalRelLM3_1 m.machine
                    (allocMap.map (derefReadMapFn allocMap e.localIdx ptrVal.tag))
                    dstDecl body.layouts (.init (.scalar sc_t))
                    { tfb.locals[dstIdx]'hlt_db with
                      value := .live (.immediate (.scalar (.fromScalarInt msc_t))) } :=
                .base (.immediate (.init (.scalar sc_t)) (.scalar (.fromScalarInt msc_t)) _
                  (by rw [hd_Lay]; intro l hl; exact (Option.some.inj hl).symm)
                  (Or.inr ⟨.scalar sc_t, rfl, himm_dst_rel⟩))
              exact hstate_b.advance_write_immediate_perm_map rfl
                (derefReadMapFn allocMap e.localIdx ptrVal.tag) hf_tag hf_loc hf_aid
                hdecl_dst hnot_dst (hd_Val.trans hmd_imm) hnew_d
                hcal hstack hprot hcaller rfl rfl
            cases hloc_d with
            | rawPtr _ _ _ _ _ _ hty_raw _ =>
              exfalso
              rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;>
                rw [hk] at hty_raw <;> cases hty_raw
            | base hloc_d_b =>
              cases hloc_d_b with
              | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst _ hmls_d mp)
              | dead _ _ =>
                have hdb_dead : tfb.locals[dstIdx]? =
                    some ⟨.dead, some (translateTy dstDecl.ty body.layouts)⟩ := by
                  rw [Array.getElem?_eq_getElem hlt_db]
                  rcases hls : tfb.locals[dstIdx]'hlt_db with ⟨v0, l0⟩
                  rw [hls] at hd_Val hd_Lay
                  dsimp only at hd_Val hd_Lay
                  rw [hd_Val, hd_Lay]
                have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_dead
                have ha_ub : evalStmt s
                    ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
                    body.localDecls body.layouts = MirStepNode.fail .ub := by
                  unfold evalStmt
                  dsimp only []
                  rw [hrv_anneal]
                  dsimp only []
                  rw [hslot_d]
                have hm_err : Miri.Interpreter.Step.evalStatement
                    (annealStepHooks body.localDecls body.layouts) ()
                    (translateStmt
                      ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
                    m =
                    ({ m with stack := ⟨#[tfb]⟩ },
                      .error (.undefinedBehavior "write to dead local")) := by
                  rw [hm_stmt]
                  unfold Miri.Interpreter.runRvalue
                  rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
                  dsimp only [annealReadImmediate]
                  rw [EStateM.bind_eq_ok hread_m,
                    annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ }) rfl hget_db]
                rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb
                  hstmt hm_err]
                exact .ub _ _
              | immediate _ oldImm _ _ hvald =>
                have hsd_ne : slot_d ≠ .dead := by
                  rcases hvald with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp
                exact hd_live_helper oldImm rfl hsd_ne

/-- **`step_deref_read_simulation` (`LM-3.1` Deliverable 2 — Real-Step Deref Read)**:
existential-`allocMap'` corollary of `step_deref_read_simulation_explicit`. -/
theorem step_deref_read_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal, get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      ∀ e ∈ allocMap, e.tag = ptrVal.tag →
        get? s.frame.locals e.localIdx ≠ some .dead →
          ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
          (∀ decl, get? body.localDecls e.localIdx = some decl → decl.ty.kind = dstDecl.ty.kind)) :
    ∃ allocMap',
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨_, step_deref_read_simulation_explicit hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_prim himm hlive_ptr⟩

theorem WellTypedScalarOperand.of_cacheFrameLocalLayout
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (k : Nat) (hlt : k < tf.locals.size) (lay : Miri.Interpreter.LocalLayout) :
    WellTypedScalarOperand body (cacheFrameLocalLayout tf k hlt lay) op ty := by
  cases hop with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    exact .constScalar c sc hval hprim hsz hcan hlaysz hbool hchar
  | copyLocal idx decl hdecl hsz_nz himm =>
    refine .copyLocal idx decl hdecl hsz_nz ?_
    intro mls hmls mp hmp
    simp only [cacheFrameLocalLayout] at hmls
    by_cases hki : k = idx
    · subst hki
      rw [Array.getElem?_set_self] at hmls
      injection hmls with hm
      rw [← hm] at hmp
      exact himm (tf.locals[k]'hlt) (Array.getElem?_eq_getElem hlt) mp hmp
    · rw [Array.getElem?_set_ne _ hki] at hmls
      exact himm mls hmls mp hmp

theorem evalRvalue_use_scalarOperand_eq
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (locals : List LocalSlot) (mem : Memory) :
    evalRvalue locals (.use op) mem body.localDecls body.layouts =
      match evalOperand locals op mem.borrows mem.globals body.layouts mem.callerLocals with
      | .ok v locals' => .ok v locals' mem
      | .ub => .ub
      | .unsupported => .unsupported := by
  cases hop <;>
  · unfold evalRvalue
    dsimp only []
    cases evalOperand locals _ mem.borrows mem.globals body.layouts mem.callerLocals <;> rfl

private theorem live_find_filter_push_self {β : Type}
    (live : Array (Miri.Memory.AllocId × β))
    (id : Miri.Memory.AllocId) (newLa : β) :
    ((live.filter (fun x => x.1 != id)).push (id, newLa)).find? (fun x => x.1 == id) =
      some (id, newLa) := by
  rw [Array.find?_push, ← Array.find?_toList, Array.toList_filter,
    list_filter_self_find?_none]
  simp

private theorem live_find_filter_push_ne {β : Type}
    (live : Array (Miri.Memory.AllocId × β))
    {id₀ id : Miri.Memory.AllocId} (hne : id₀ ≠ id) (newLa : β) :
    ((live.filter (fun x => x.1 != id₀)).push (id₀, newLa)).find? (fun x => x.1 == id) =
      live.find? (fun x => x.1 == id) := by
  rw [Array.find?_push, ← Array.find?_toList, Array.toList_filter,
    list_filter_ne_find? live.toList hne, Array.find?_toList]
  cases live.find? (fun x => x.1 == id) with
  | some _ => rfl
  | none => simp [beq_false_of_ne hne]

/-- Overwriting `e.allocId`'s live stack allocation at offset `0` with scalar
`sc` (`msc`) and mapping `f` (preserving `.tag`, `.localIdx`, `.allocId`) across
`allocMap` preserves `StateRelLM3_1`. -/
theorem StateRelLM3_1.advance_write_deref_scalar
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (f : AllocMapEntry → AllocMapEntry)
    (hf_tag : ∀ x, (f x).tag = x.tag)
    (hf_loc : ∀ x, (f x).localIdx = x.localIdx)
    (hf_aid : ∀ x, (f x).allocId = x.allocId)
    {e : AllocMapEntry} (he : e ∈ allocMap)
    {tgtDecl : LocalDecl} (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_prim : IsPrimScalarTy tgtDecl.ty)
    {slot_t : LocalSlot} (hslot_t : get? s.frame.locals e.localIdx = some slot_t)
    (ht_ne_dead : slot_t ≠ .dead)
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hkind_la : localAlloc.kind = .stack)
    (halign_la : localAlloc.allocation.align =
      (translateTy tgtDecl.ty body.layouts).layout.align.abi)
    {sc : MirAst.ScalarInt} {msc : Miri.Memory.ScalarInt}
    (hrel_sc : ScalarRel sc msc)
    (hsz_tgt : (translateTy tgtDecl.ty body.layouts).layout.size = translateSizeBytes sc.sizeBytes)
    (hbool_tgt : tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar_tgt : tgtDecl.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true)
    {alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    (halign_alloc' : alloc'.align = localAlloc.allocation.align)
    (hshape_alloc' : StackScalarAllocShape (translateSizeBytes sc.sizeBytes) alloc')
    (hinit_alloc' : alloc'.initializationMask.isRangeInitialized
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) = .ok (.ok ()))
    (hread_alloc' : alloc'.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateSizeBytes sc.sizeBytes)) false =
      .ok (.fromScalarInt msc)) :
    StateRelLM3_1 body
      (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
        { s.memory with
          borrows := (allocMap.map f).map AllocMapEntry.toBorrowEntry })
      { stack := ⟨#[{ tf with location := .mir ⟨s.frame.blockIdx, s.frame.stmtIdx + 1⟩ }]⟩
        machine := { m.machine with
          memory := { m.machine.memory with
            live := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
              (e.allocId, ⟨localAlloc.kind, alloc'⟩) } } }
      (allocMap.map f) := by
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, _, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  let newLive := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
    (e.allocId, ⟨localAlloc.kind, alloc'⟩)
  let newMem : AnnealMemory := { m.machine.memory with live := newLive }
  let mach' : AnnealMachine := { m.machine with memory := newMem }
  have hset_mem : m.machine.memory.setLiveAllocation e.allocId alloc' = .ok newMem :=
    Miri.Memory.MemoryState.setLiveAllocation_of_find m.machine.memory e.allocId localAlloc
      alloc' hfind_la
  obtain ⟨⟨lay_e, hlay_e⟩, _, _⟩ := (halloc.local_alloc_sync tf hframes e he).1 slot_t hslot_t
    ht_ne_dead
  obtain ⟨_, _, hbase_e⟩ := halloc.base_addr_valid e he
  obtain ⟨_, _, _, _, hpow_t, _⟩ := htgt_prim.size_align_ok body.layouts
  have hlt_af_e : e.localIdx < s.frame.locals.length := by
    cases h : s.frame.locals[e.localIdx]? with
    | none => rw [get?_eq_getElem?, h] at hslot_t; cases hslot_t
    | some _ => exact (List.getElem?_eq_some_iff.mp h).1
  have hloc_e0 := hfr.locals_rel e.localIdx tgtDecl slot_t
    ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_e⟩ hdecl_tgt hslot_t hlay_e
  have hnew_mp : MemPlaceRel mach' tgtDecl.ty body.layouts (some (.scalar sc))
      (stackAllocPlace e.allocId) := by
    refine .mk e.allocId Miri.Memory.BorTag.one (annealStackBaseAddr e.allocId)
      Miri.ABI.Size.ZERO ⟨localAlloc.kind, alloc'⟩
      rfl rfl rfl ?_ hbase_e ?_ ?_ hshape_alloc'.mutability_eq ?_ ?_ ?_ ?_ ?_
    · exact Array.mem_toList_iff.mpr (Array.mem_push_self ..)
    · simp only [Miri.ABI.Size.ZERO, UInt64.toNat_zero, Nat.add_zero]
      exact (annealStackBaseAddr e.allocId).toBitVec.isLt
    · simp [stackAllocPlace, Miri.ABI.Size.ZERO]
    · exact annealStackBaseAddr_isAligned e.allocId _ hpow_t
    · simp [Miri.ABI.Size.ZERO, hshape_alloc'.byteSize_eq, hsz_tgt]
    · intro h; cases h
    · intros; rw [hsz_tgt]; exact hinit_alloc'
    · intro sc' hs'
      injection hs' with hv
      injection hv with hsc_eq
      subst hsc_eq
      exact ⟨hsz_tgt, hbool_tgt, hchar_tgt, msc, hrel_sc, hsz_tgt ▸ hread_alloc'⟩
  have hnew_e : LocalRelLM3_1 mach' (allocMap.map f) tgtDecl body.layouts (.init (.scalar sc))
      ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_e⟩ :=
    .base (.indirect (.init (.scalar sc)) (stackAllocPlace e.allocId) lay_e
      hloc_e0.cachedLayout_eq (by simp) hnew_mp)
  have hfr' : FrameRelLM3_1 body mach' (allocMap.map f)
      { s.frame with locals := s.frame.locals.set e.localIdx (.init (.scalar sc)) } tf := by
    refine ⟨hfr.body_eq, hfr.location_eq, by rw [List.length_set, hfr.af_locals_len],
      hfr.mf_locals_size, ?_⟩
    intro i decl_i slot_i mls_i hdecl_i hslot_i hmls_i
    rw [get?_eq_getElem?, List.getElem?_set] at hslot_i
    by_cases h_eq : e.localIdx = i
    · subst h_eq
      simp only [↓reduceIte, hlt_af_e, Option.some.injEq] at hslot_i
      have hdecl_eq : decl_i = tgtDecl := by
        rw [hdecl_tgt] at hdecl_i; exact Option.some.inj hdecl_i.symm
      have hmls_eq : mls_i = ⟨.live (.indirect (stackAllocPlace e.allocId)), lay_e⟩ := by
        rw [hlay_e] at hmls_i; exact Option.some.inj hmls_i.symm
      subst hdecl_eq hslot_i hmls_eq
      exact hnew_e
    · simp only [h_eq, ↓reduceIte] at hslot_i
      rw [← get?_eq_getElem?] at hslot_i
      have hloc_i := (hfr.locals_rel i decl_i slot_i mls_i hdecl_i hslot_i hmls_i).map_preserve
        f hf_tag hf_aid
      apply hloc_i.of_setLiveAllocation_ne hfind_la hset_mem
      intro mp hv
      have hmls_ind : tf.locals[i]? = some ⟨.live (.indirect mp), mls_i.layout⟩ := by
        rcases mls_i with ⟨v0, l0⟩
        dsimp only at hv
        subst hv
        exact hmls_i
      have hd := hdisj e.localIdx i (stackAllocPlace e.allocId) mp lay_e mls_i.layout h_eq
        hlay_e hmls_ind
      exact fun heq => hd (by simpa [stackAllocPlace, Option.bind,
        Miri.Memory.Provenance.getAllocId] using heq.symm)
  have hnodup' : ((allocMap.map f).map AllocMapEntry.tag).Nodup := by
    have hmap_tag : (allocMap.map f).map AllocMapEntry.tag = allocMap.map AllocMapEntry.tag := by
      rw [List.map_map]
      exact List.map_congr_left (fun x _ => hf_tag x)
    rw [hmap_tag]
    exact halloc.tags_nodup
  refine .mk _ rfl hretCont hretPlace hfr'.advance hcal hstack hprot hcaller rfl ?_ hdisj
  refine ⟨hnodup', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e₁ h₁ e₂ h₂ heq
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
    rw [hf_loc, hf_loc] at heq
    rw [hf_aid, hf_aid]
    exact halloc.local_to_alloc_unique x₁ hx₁ x₂ hx₂ heq
  · intro e₁ h₁ e₂ h₂ heq
    obtain ⟨x₁, hx₁, rfl⟩ := List.mem_map.mp h₁
    obtain ⟨x₂, hx₂, rfl⟩ := List.mem_map.mp h₂
    rw [hf_aid, hf_aid] at heq
    rw [hf_loc, hf_loc]
    exact halloc.alloc_to_local_injective x₁ hx₁ x₂ hx₂ heq
  · intro e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_loc]
    exact halloc.target_decl x hx
  · intro e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_aid]
    exact halloc.base_addr_valid x hx
  · intro e' he'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    have hlook := lookupBorrow_map_toBorrowEntry_of_nodup hnodup' he'
    refine ⟨?_, ?_⟩
    · dsimp only [advanceStmt]
      rw [hf_tag]
      exact (halloc.borrow_sync x hx).1
    · dsimp only [advanceStmt]
      simpa [AllocMapEntry.toBorrowEntry] using hlook
  · intro e' he' la₁ la₂ hla₁ hla₂
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_aid] at hla₁ hla₂
    dsimp only [] at hla₁ hla₂
    simp only [Array.toList_push, List.mem_append, List.mem_singleton,
      Array.toList_filter, List.mem_filter] at hla₁ hla₂
    by_cases ha : x.allocId = e.allocId
    · rw [ha] at hla₁ hla₂
      rcases hla₁ with ⟨_, hb⟩ | h1
      · simp at hb
      · rcases hla₂ with ⟨_, hb⟩ | h2
        · simp at hb
        · exact (Prod.mk.inj h1).2.trans (Prod.mk.inj h2).2.symm
    · rcases hla₁ with ⟨hl₁, _⟩ | h1
      · rcases hla₂ with ⟨hl₂, _⟩ | h2
        · exact halloc.live_key_unique x hx la₁ la₂ hl₁ hl₂
        · exact absurd (Prod.mk.inj h2).1 ha
      · exact absurd (Prod.mk.inj h1).1 ha
  · intro tf' htf' e' he'
    injection htf' with h₁
    injection h₁ with h₂
    subst h₂
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he'
    rw [hf_loc, hf_aid]
    by_cases hx_eq : x.localIdx = e.localIdx
    · have ha_eq : x.allocId = e.allocId := halloc.local_to_alloc_unique x hx e he hx_eq
      rw [hx_eq, ha_eq]
      have hget_self :
          get? (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
            { s.memory with borrows := (allocMap.map f).map AllocMapEntry.toBorrowEntry }).frame.locals
            e.localIdx = some (.init (.scalar sc)) := by
        dsimp only [advanceStmt]
        rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_e]
      refine ⟨fun slot' hslot' _ => ?_, fun hdead' => ?_⟩
      · rw [hget_self] at hslot'
        injection hslot' with hs'
        subst hs'
        refine ⟨⟨lay_e, hlay_e⟩, fun v hv => ⟨sc, (by injection hv : Value.scalar sc = v).symm⟩,
          fun decl_e hdecl_e => ?_⟩
        rw [hdecl_tgt] at hdecl_e
        injection hdecl_e with hd_eq
        subst hd_eq
        exact ⟨⟨localAlloc.kind, alloc'⟩,
          live_find_filter_push_self m.machine.memory.live e.allocId _,
          hkind_la, halign_alloc'.trans halign_la, hsz_tgt ▸ hshape_alloc'⟩
      · rw [hget_self] at hdead'; cases hdead'
    · have ha_ne : e.allocId ≠ x.allocId := fun ha =>
        hx_eq (halloc.alloc_to_local_injective x hx e he ha.symm)
      obtain ⟨hlive_x, hdead_x⟩ := halloc.local_alloc_sync tf hframes x hx
      have hget_ne :
          get? (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
            { s.memory with borrows := (allocMap.map f).map AllocMapEntry.toBorrowEntry }).frame.locals
            x.localIdx = get? s.frame.locals x.localIdx := by
        dsimp only [advanceStmt]
        rw [get?_eq_getElem?, List.getElem?_set_ne (Ne.symm hx_eq), ← get?_eq_getElem?]
      have hfind_ne := live_find_filter_push_ne m.machine.memory.live ha_ne
        (⟨localAlloc.kind, alloc'⟩ : Miri.Memory.LocalAllocation AnnealProv
          (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind)
      refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
      · rw [hget_ne] at hslot'
        obtain ⟨⟨lay_x, hlay_x⟩, hsc_x, hsh_x⟩ := hlive_x slot' hslot' hne_d
        refine ⟨⟨lay_x, hlay_x⟩, hsc_x, fun decl_x hdecl_x => ?_⟩
        obtain ⟨la_x, hf_x, hk_x, hal_x, hs_x⟩ := hsh_x decl_x hdecl_x
        exact ⟨la_x, hfind_ne.trans hf_x, hk_x, hal_x, hs_x⟩
      · rw [hget_ne] at hdead'
        exact hfind_ne.trans (hdead_x hdead')

private theorem estate_bind_assoc {ε σ α β γ : Type}
    (ma : EStateM ε σ α) (f : α → EStateM ε σ β) (g : β → EStateM ε σ γ) (s : σ) :
    (ma >>= fun a => f a >>= g) s = ((ma >>= f) >>= g) s := by
  simp only [Bind.bind, EStateM.bind]
  cases ma s <;> rfl

private theorem allocMap_mem_tag_injective
    {allocMap : List AllocMapEntry}
    (hnodup : (allocMap.map AllocMapEntry.tag).Nodup)
    {e₁ e₂ : AllocMapEntry} (h₁ : e₁ ∈ allocMap) (h₂ : e₂ ∈ allocMap)
    (htag : e₁.tag = e₂.tag) : e₁ = e₂ := by
  induction allocMap with
  | nil => cases h₁
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp h₁ with rfl | h₁' <;>
      rcases List.mem_cons.mp h₂ with rfl | h₂'
    · rfl
    · exact absurd (htag ▸ List.mem_map_of_mem h₂') hnodup.1
    · exact absurd (htag.symm ▸ List.mem_map_of_mem h₁') hnodup.1
    · exact ih hnodup.2 h₁' h₂'

/-- Computable post-step `allocMap'` for `*_p = .use op`: updates borrows on
the target local via `updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)`
when `_p` holds a tracked pointer, and leaves `allocMap` unchanged otherwise. -/
def derefWriteNextAllocMap (locals : List LocalSlot) (allocMap : List AllocMapEntry)
    (ptrIdx : Local) : List AllocMapEntry :=
  match get? locals ptrIdx with
  | some (.init (.ptr ptrVal 8)) =>
    match lookupAllocMapByTag allocMap ptrVal.tag with
    | some e => updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)
    | none => allocMap
  | _ => allocMap

/-- **`step_deref_write_simulation_explicit` (`LM-3.1` Explicit `allocMap'` Deref Write)**:
Execute `*_p = .use op` from any `StateRelLM3_1`-related state through BOTH
Anneal's `stepMirFn` and `lean-miri`'s `Miri.Interpreter.Step.step` under the
computable post-step borrow table `derefWriteNextAllocMap s.frame.locals allocMap ptrIdx`. -/
theorem step_deref_write_simulation_explicit
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {ptrDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    StepRelLM3_1 body m (derefWriteNextAllocMap s.frame.locals allocMap ptrIdx)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, hcaller, hbor, halloc, _⟩ := id hstate
  have himm_p := himm_ptr tf hframes
  have hop_tf := hop tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨ptrIdx, .cons .deref .nil⟩ op span m
  obtain ⟨slot_p, mls_p, _, hlt_p, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ :=
    hfr.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  let tfa := cacheFrameLocalLayout tf ptrIdx hlt_p (translateTy ptrDecl.ty body.layouts)
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_ptr hlt_p
  have hop_tfa : WellTypedScalarOperand body tfa op valTy :=
    hop_tf.of_cacheFrameLocalLayout ptrIdx hlt_p (translateTy ptrDecl.ty body.layouts)
  have hpt_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 } := by
    rcases hval_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind ▸ hk)
    · exact Or.inr (Or.inl (hval_kind ▸ hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind ▸ hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind ▸ hk⟩))
  have hlay0_eq : translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts =
      translateTy valTy body.layouts := by
    have h1 := hval_prim.translateTy_layoutIdx body.layouts
    rw [hval_kind] at h1
    exact h1
  -- Helper: if `_p` is `.dead` or `.uninit`, Anneal ALWAYS fails with `.ub` on `*_p = .use op`
  -- (either when evaluating `op`, or when `writePlaceValue` inspects `_p`).
  have hanneal_bad_ptr :
      (slot_p = .dead ∨ slot_p = .uninit) →
      evalStmt s ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
    intro hbad
    rcases evalOperand_scalar_lm3_1_simulation hstate hframes hop_tf hval_prim none with
      ⟨_, _, hop_ub, _⟩ | ⟨sc, _, _, hop_ok, _, _, _, _⟩
    · unfold evalStmt
      dsimp only []
      rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
    · unfold evalStmt
      dsimp only []
      rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
      dsimp only [evalPlaceWrite, writePlaceValue]
      rw [hprot]
      dsimp only []
      rcases hbad with hs | hs <;> rw [hslot_p, hs, hcaller]
  rcases hloc_p.rawPtr_immediate_cases hptr_ty (himm_p mls_p hmls_p) with
    ⟨hsp_dead, hmp_dead⟩ | ⟨hsp_un, hmp_un⟩ |
    ⟨sc_p, msc_p, hsp_sc, hsz8_p, hrel_p, hmp_sc⟩ |
    ⟨ptrVal, mptr, hsp_ptr, hptrRel, hmp_ptr⟩
  · -- Case 1: `_p` is `.dead` -> UB in both!
    have hmls_p' : tf.locals[ptrIdx]'hlt_p = ⟨.dead, mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_dead; subst hmp_dead; rfl
    have hdst_err := annealEvalPlace_deref_dead hframes hlt_p hdecl_ptr hmls_p' hcache_p
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hdst_err]
    rw [hanneal_bad_ptr (Or.inl hsp_dead),
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 2: `_p` is `.uninit` -> UB in both!
    have hmls_p' : tf.locals[ptrIdx]'hlt_p = ⟨.live (.immediate .uninit), mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_un; subst hmp_un; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_p hdecl_ptr hmls_p' hcache_p
    have hder_err := annealDerefOperandToMemPlace_uninit (ly := body.layouts) hdecl_ptr hptr_ty
      (by unfold IsPrimScalarTy at hval_prim ⊢; rw [← hval_kind]; exact hval_prim)
      (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfa]⟩ }
    have hdst_err : annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
        .error (.undefinedBehavior "read of uninitialized local") { m with stack := ⟨#[tfa]⟩ } := by
      rw [hdst_live, EStateM.bind_eq_error hder_err]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_error hdst_err]
    rw [hanneal_bad_ptr (Or.inr hsp_un),
      miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 3: `_p` holds a provenance-less integer scalar -> UB (either in `op` or on write)!
    have hmls_p' : tf.locals[ptrIdx]'hlt_p =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_p))), mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_sc; subst hmp_sc; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_p hdecl_ptr hmls_p' hcache_p
    obtain ⟨mismatch, hder_ok⟩ := annealDerefOperandToMemPlace_scalarInt hdecl_ptr hptr_ty
      hpt_prim hrel_p hsz8_p (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfa]⟩ }
    rw [hlay0_eq] at hder_ok
    have hdst_ok : annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
        .ok ⟨.memory ⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc_p.bits),
            .none, mismatch⟩, translateTy valTy body.layouts⟩
          { m with stack := ⟨#[tfa]⟩ } := by
      rw [hdst_live, EStateM.bind_eq_ok hder_ok]; rfl
    rcases evalOperand_scalar_lm3_1_simulation hstate_a rfl hop_tfa hval_prim
        (some (translateTy valTy body.layouts)) with
      ⟨m_op, msg_op, hop_ub, hm_op_ub⟩ | ⟨sc, msc, tf', hop_ok, hm_op_ok, _, _, _⟩
    · have ha_ub : evalStmt s ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
          (m_op, .error (.undefinedBehavior msg_op)) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_ok]
        dsimp only []
        rw [estate_bind_assoc, EStateM.bind_eq_error hm_op_ub]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have ha_ub : evalStmt s ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
        dsimp only [evalPlaceWrite, writePlaceValue]; rw [hprot]; dsimp only []
        rw [hslot_p, hsp_sc, hcaller]
      obtain ⟨msg_w, hw_err⟩ := annealWriteMemoryPlace_withoutProv_ub (ly := body.layouts)
        hval_prim (.scalar (.fromScalarInt msc)) (UInt64.ofNat sc_p.bits) mismatch
        { m with stack := ⟨#[tf']⟩ }
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
          ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior msg_w)) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_ok]
        dsimp only []
        rw [estate_bind_assoc, EStateM.bind_eq_ok hm_op_ok,
          annealWriteImmediate_memory_eq rfl, hw_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
  · -- Case 4: `_p` holds `.ptr ptrVal 8` related by `PtrRel allocMap ptrVal mptr`.
    have hmls_p' : tf.locals[ptrIdx]'hlt_p =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
    have hdst_live := annealEvalPlace_deref_live hframes hlt_p hdecl_ptr hmls_p' hcache_p
    obtain ⟨_, _, _, _, hpow_pt, _⟩ := hpt_prim.size_align_ok body.layouts
    obtain ⟨mismatch_any, hmis_any⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset
      (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi hpow_pt
    have hder_any := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty
      (by unfold IsPrimScalarTy at hval_prim ⊢; rw [← hval_kind]; exact hval_prim) mptr hmis_any
      (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfa]⟩ }
    rw [hlay0_eq] at hder_any
    have hdst_any : annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
        .ok ⟨.memory ⟨mptr.withOptionalProvenance, .none, mismatch_any⟩,
            translateTy valTy body.layouts⟩
          { m with stack := ⟨#[tfa]⟩ } := by
      rw [hdst_live, EStateM.bind_eq_ok hder_any]; rfl
    -- Evaluate `op` on `{ m with stack := ⟨#[tfa]⟩ }`:
    rcases evalOperand_scalar_lm3_1_simulation hstate_a rfl hop_tfa hval_prim
        (some (translateTy valTy body.layouts)) with
      ⟨m_op, msg_op, hop_ub, hm_op_ub⟩ | ⟨sc, msc, tf', hop_ok, hm_op_ok, hstate_tf', himm_sc, _⟩
    · -- Subcase 4a: `op` fails with UB in both!
      have ha_ub : evalStmt s ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
          (m_op, .error (.undefinedBehavior msg_op)) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_any]
        dsimp only []
        rw [estate_bind_assoc, EStateM.bind_eq_error hm_op_ub]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · -- Subcase 4b: `op` succeeded with `sc` (`msc`) and `tf'`.
      subst hsp_ptr
      rcases hptrRel with ⟨_, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, ⟨e, he, htag, rfl⟩⟩
      obtain ⟨tgtDecl, hdecl_tgt, htgt_prim⟩ := halloc.target_decl e he
      obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he
      have hbor_look : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by
        rw [← htag, hbor]
        exact lookupBorrow_map_toBorrowEntry_of_nodup halloc.tags_nodup he
      rcases id hstate_tf' with ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩
      injection hframes_tf' with h1_tf
      injection h1_tf with h2_tf
      subst h2_tf
      obtain ⟨slot_t, _, hlt_af_t, _, hslot_t, _, _, _⟩ := hfr_tf'.lookup_local hdecl_tgt
      obtain ⟨hlive_sync, hdead_sync⟩ := halloc_tf'.local_alloc_sync tf' rfl e he
      by_cases ht_dead : slot_t = .dead
      · -- Subcase 4b-i: `e.localIdx` is `.dead` (dangling pointer) -> UB in both!
        have hfind_none : m.machine.memory.live.find? (fun x => x.1 == e.allocId) = none :=
          hdead_sync (hslot_t.trans (congrArg some ht_dead))
        have hmptr_opt : mptr.withOptionalProvenance =
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              some (.concrete e.allocId borTag)⟩ := by
          rcases mptr with ⟨off, prov⟩
          dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
          subst hprov_eq hmptr_off; rfl
        obtain ⟨msg_d, hw_dead⟩ := annealWriteMemoryPlace_dead_ub (ly := body.layouts) hval_prim
          (.scalar (.fromScalarInt msc)) hid_lt hoff_lt hbase hfind_none mismatch_any
          (borTag := borTag) (st := { m with stack := ⟨#[tf']⟩ })
        have ha_ub : evalStmt s ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
          dsimp only [evalPlaceWrite, writePlaceValue]; rw [hprot]; dsimp only []
          rw [hslot_p]; dsimp only []
          rw [hbor_look]; dsimp only [AllocMapEntry.toBorrowEntry]
          cases hp : e.perm <;> simp [hslot_t, ht_dead, hcaller]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
            ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior msg_d)) := by
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_any]
          dsimp only []
          rw [estate_bind_assoc, EStateM.bind_eq_ok hm_op_ok,
            annealWriteImmediate_memory_eq rfl, hmptr_opt, hw_dead]
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
          hm_err]
        exact .ub _ _
      · -- Subcase 4b-ii: `e.localIdx` is live (`slot_t ≠ .dead`) -> lockstep write!
        have hs_not_dead : get? s.frame.locals e.localIdx ≠ some .dead := by
          rw [hslot_t]; exact fun h => ht_dead (Option.some.inj h)
        obtain ⟨hoff0, hperm_ok, htgt_kind⟩ :=
          hlive_ptr ptrVal e tgtDecl hslot_p he htag hdecl_tgt hs_not_dead
        have htr_tgt : translateTy tgtDecl.ty body.layouts = translateTy valTy body.layouts := by
          rw [← htgt_prim.translateTy_layoutIdx body.layouts,
            ← hval_prim.translateTy_layoutIdx body.layouts, htgt_kind, hval_kind]
        obtain ⟨_, _, hshape_fn⟩ := hlive_sync slot_t hslot_t ht_dead
        obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ :=
          hshape_fn tgtDecl hdecl_tgt
        obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
          himm_sc.of_primitive_scalar hval_prim
        injection hsc_eq with hsc_eq'
        subst hsc_eq'
        have hmsc_eq' : msc = msc' := by
          injection hmsc_eq with h1
          unfold Miri.Memory.Scalar.fromScalarInt at h1
          injection h1 with h2
          injection h2 with h3
        subst hmsc_eq'
        have hmptr_zero : mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId) := by
          rw [hmptr_off, hoff0, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
        have hmis0_eq : mismatch_any = none := by
          have hm0 : annealOffsetMisalignment mptr.offset
              (translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts).layout.align.abi =
              .ok none := by
            rw [hmptr_zero]
            exact annealOffsetMisalignment_stackBase_eq_none e.allocId _ hpow_pt
          rw [hm0] at hmis_any
          exact (Except.ok.inj hmis_any).symm
        subst hmis0_eq
        have hmptr_opt : mptr.withOptionalProvenance =
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
              some (.concrete e.allocId borTag)⟩ := by
          rcases mptr with ⟨off, prov⟩
          dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_zero ⊢
          subst hprov_eq hmptr_zero; rfl
        have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
            localAlloc.allocation := by
          rw [← hsz_sc, ← htr_tgt]; exact hshape_la
        obtain ⟨alloc', hw_alloc, halign_alloc', hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
          hshape_sc.writeScalar_readScalar hrel_sc
        have hmsc_sz : msc.size = (translateTy valTy body.layouts).layout.size := by
          rw [hrel_sc.size_eq, ← hsz_sc]
        have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (translateTy valTy body.layouts).layout.size)
            (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' := by
          rw [← hmsc_sz]; exact hw_alloc
        have hval_sc : annealValidateScalarForTyId (translateTy valTy body.layouts).ty
            (.fromScalarInt msc) = true :=
          annealValidateScalarForTyId_of_scalarRel hval_prim hrel_sc hbool_val hchar_val
        have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hval_prim hid_lt hbase hfind_la
          hshape_la.mutability_eq (htr_tgt ▸ hshape_la.byteSize_eq) hmsc_sz hval_sc hw_alloc_lay
          (borTag := borTag) (st := { m with stack := ⟨#[tf']⟩ })
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩) m =
            ({ stack := ⟨#[tf']⟩
               machine := { m.machine with
                 memory := { m.machine.memory with
                   live := (m.machine.memory.live.filter (fun x => x.1 != e.allocId)).push
                     (e.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_any]
          dsimp only []
          rw [estate_bind_assoc, EStateM.bind_eq_ok hm_op_ok,
            annealWriteImmediate_memory_eq rfl, hmptr_opt, hw_m]
        have hloc_tf' : tf'.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ :=
          hfr_tf'.location_eq
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok
          rfl hloc_tf']
        have hinv_bor := invalidateDerefWriteBorrows_map_toBorrowEntry s.frame.locals allocMap
          halloc.tags_nodup ptrIdx ptrVal 8 e he htag hslot_p
        rw [← hbor] at hinv_bor
        have ha_ok : evalStmt s ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩
            body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s (s.frame.locals.set e.localIdx (.init (.scalar sc)))
                { s.memory with
                  borrows := (updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag)).map
                    AllocMapEntry.toBorrowEntry }) := by
          unfold evalStmt
          dsimp only []
          rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
          dsimp only [evalPlaceWrite, writePlaceValue]
          rw [hprot]
          dsimp only []
          rw [hslot_p]
          dsimp only []
          rw [hbor_look]
          dsimp only [AllocMapEntry.toBorrowEntry]
          rcases hperm_ok with hp | hp <;> rw [hp] <;> dsimp only [] <;>
          · rw [hslot_t]
            cases slot_t with
            | dead => exact absurd rfl ht_dead
            | uninit => simp only [set?_eq_some_set hlt_af_t, hinv_bor]
            | init _ => simp only [set?_eq_some_set hlt_af_t, hinv_bor]
        have hnext_eq : derefWriteNextAllocMap s.frame.locals allocMap ptrIdx =
            updateAllocMapOnWrite allocMap e.localIdx (some ptrVal.tag) := by
          simp only [derefWriteNextAllocMap, hslot_p,
            lookupAllocMapByTag_of_mem_nodup halloc.tags_nodup he htag]
        rw [ha_ok, hnext_eq]
        apply StepRelLM3_1.step
        have hsz_tgt : (translateTy tgtDecl.ty body.layouts).layout.size =
            translateSizeBytes sc.sizeBytes := by
          rw [htr_tgt, hsz_sc]
        have hbool_tgt : tgtDecl.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) :=
          fun hb => hbool_val (hval_kind.trans (htgt_kind.symm.trans hb))
        have hchar_tgt : tgtDecl.ty.kind = .char →
            sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true :=
          fun hc => hchar_val (hval_kind.trans (htgt_kind.symm.trans hc))
        exact hstate_tf'.advance_write_deref_scalar rfl
          (fun x => x.updateOnWrite e.localIdx (some ptrVal.tag))
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          he hdecl_tgt htgt_prim hslot_t ht_dead hfind_la hkind_la halign_la
          hrel_sc hsz_tgt hbool_tgt hchar_tgt halign_alloc' hshape_alloc' hinit_alloc'
          hread_alloc'

/-- **`step_deref_write_simulation` (`LM-3.1` Real-Step `PlaceElem.Deref` Write)**:
existential-`allocMap'` corollary of `step_deref_write_simulation_explicit`. -/
theorem step_deref_write_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩)
    {ptrDecl : LocalDecl} {mutability : Mutability} {pointeeKind : RigidTy}
    {valTy : Ty}
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hval_prim : IsPrimScalarTy valTy)
    (hval_kind : valTy.kind = pointeeKind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hlive_ptr : ∀ ptrVal e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      get? s.frame.locals e.localIdx ≠ some .dead →
      ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
        tgtDecl.ty.kind = pointeeKind) :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) :=
  ⟨_, step_deref_write_simulation_explicit hstate hphase hbb hstmt hdecl_ptr hptr_ty hval_prim
    hval_kind hop himm_ptr hlive_ptr⟩

/-- **`step_deref_oob_miri_ub` (`LM-3.1` Out-of-Bounds Deref UB)**:
When `_p` holds a live pointer `ptrVal` (`e ∈ allocMap`, `e.tag = ptrVal.tag`)
whose byte offset exceeds the backing stack allocation's bounds
(`localAlloc.allocation.byteSize.bytes.toNat < ptrVal.offsetBytes +
pointeeSize`), executing `_d = copy *_p` or `_d = move *_p` under
`Miri.Interpreter.Step.step` (`annealStepHooks`) raises
`StepError.undefinedBehavior`. -/
theorem step_deref_oob_miri_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hoob : localAlloc.allocation.byteSize.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat) :
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  have himm_p := himm_ptr tf hframes
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (opKind ⟨ptrIdx, .cons .deref .nil⟩) span m
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRelLM3_1 body m.machine allocMap s.frame tfa :=
    hfr.cache_local_layout hdecl_dst hlt_d
  obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
    hfra.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
    himm_p.cache_layout hlt_d _ mls_p hmls_pa
  let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
  have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
      translateTy dstDecl.ty body.layouts := hdst_prim.translateTy_layoutIdx body.layouts
  have hsp_eq : slot_p = .init (.ptr ptrVal 8) := by
    rw [hslot_p] at hslot_pa; exact Option.some.inj hslot_pa.symm
  subst hsp_eq
  rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
  · cases h
  · cases h
  · cases h
  · injection hp_eq with hv_eq
    injection hv_eq with hpv_eq _
    subst hpv_eq
    obtain ⟨_, borTag, hprov_eq, _, hoff_lt, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
    have he_eq : e' = e :=
      allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
    subst he_eq
    obtain ⟨hid_lt, _, hbase⟩ := halloc.base_addr_valid e' he'
    have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_p.layout⟩ := by
      rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
    have hop_ptr := annealEvalOperand_deref_live hopKind
      (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
      rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
    obtain ⟨_, _, _, _, hpow, _⟩ := hdst_prim.size_align_ok body.layouts
    obtain ⟨mismatch, hmis⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset
      (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.align.abi
      (hlay0_eq ▸ hpow)
    have hder_ok := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hdst_prim mptr hmis
      (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
    rw [hlay0_eq] at hder_ok
    have hmptr_opt : mptr.withOptionalProvenance =
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
          some (.concrete e'.allocId borTag)⟩ := by
      rcases mptr with ⟨off, prov⟩
      dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
      subst hprov_eq hmptr_off; rfl
    rw [hmptr_opt] at hder_ok
    have hop_ok : annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩))
        (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
        .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
            some (.concrete e'.allocId borTag)⟩, .none, mismatch⟩,
          translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
      rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
    obtain ⟨msg, hread_err⟩ := annealReadMemoryPlace_oob_ub hdst_prim hid_lt hoff_lt hbase
      hfind_la hoob mismatch (borTag := borTag) (st := { m with stack := ⟨#[tfb]⟩ })
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior msg)) := by
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
      rw [hm_stmt, htr_dst]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
      dsimp only [annealReadImmediate]
      rw [EStateM.bind_eq_error hread_err]
    exact ⟨_, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      hm_err⟩

/-- **`step_deref_misaligned_miri_ub` (`LM-3.1` Misaligned Deref UB)**:
When `_p` holds a live in-bounds pointer `ptrVal` (`e ∈ allocMap`,
`e.tag = ptrVal.tag`) whose address fails `Size.isAligned` for the pointee's ABI
alignment (for example `ptrVal.offsetBytes % 8 ≠ 0` at alignment `8`), executing
`_d = copy *_p` or `_d = move *_p` under `Miri.Interpreter.Step.step`
(`annealStepHooks`) raises `StepError.undefinedBehavior`. -/
theorem step_deref_misaligned_miri_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {opKind : Place → MirAst.Operand}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (hmis : (Miri.ABI.Size.ofBytes
        (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok false) :
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  have himm_p := himm_ptr tf hframes
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (opKind ⟨ptrIdx, .cons .deref .nil⟩) span m
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRelLM3_1 body m.machine allocMap s.frame tfa :=
    hfr.cache_local_layout hdecl_dst hlt_d
  obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
    hfra.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
    himm_p.cache_layout hlt_d _ mls_p hmls_pa
  let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
  have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
      translateTy dstDecl.ty body.layouts := hdst_prim.translateTy_layoutIdx body.layouts
  have hsp_eq : slot_p = .init (.ptr ptrVal 8) := by
    rw [hslot_p] at hslot_pa; exact Option.some.inj hslot_pa.symm
  subst hsp_eq
  rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
    ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
  · cases h
  · cases h
  · cases h
  · injection hp_eq with hv_eq
    injection hv_eq with hpv_eq _
    subst hpv_eq
    obtain ⟨_, borTag, hprov_eq, _, hoff_lt, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
    have he_eq : e' = e :=
      allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
    subst he_eq
    obtain ⟨hid_lt, _, hbase⟩ := halloc.base_addr_valid e' he'
    have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_p.layout⟩ := by
      rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
    have hop_ptr := annealEvalOperand_deref_live hopKind
      (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
      rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
    have hmis_eq : annealOffsetMisalignment mptr.offset
        (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.align.abi =
        .ok (some ⟨Miri.ABI.Align.maxAlignedFactor mptr.offset,
          (translateTy dstDecl.ty body.layouts).layout.align.abi⟩) := by
      rw [hlay0_eq, hmptr_off]
      exact annealOffsetMisalignment_of_misaligned _ _ hmis
    have hder_ok := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hdst_prim mptr hmis_eq
      (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
    rw [hlay0_eq] at hder_ok
    have hmptr_opt : mptr.withOptionalProvenance =
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
          some (.concrete e'.allocId borTag)⟩ := by
      rcases mptr with ⟨off, prov⟩
      dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
      subst hprov_eq hmptr_off; rfl
    rw [hmptr_opt] at hder_ok
    let bad : Miri.Memory.Misalignment :=
      ⟨Miri.ABI.Align.maxAlignedFactor mptr.offset,
        (translateTy dstDecl.ty body.layouts).layout.align.abi⟩
    have hop_ok : annealEvalOperand body.localDecls body.layouts
        (translateOperand (opKind ⟨ptrIdx, .cons .deref .nil⟩))
        (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
        .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
            some (.concrete e'.allocId borTag)⟩, .none, some bad⟩,
          translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
      rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
    obtain ⟨msg, hread_err⟩ := annealReadMemoryPlace_misaligned_ub hdst_prim hid_lt hoff_lt hbase
      hfind_la hinbounds bad (borTag := borTag) (st := { m with stack := ⟨#[tfb]⟩ })
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
        m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior msg)) := by
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
      rw [hm_stmt, htr_dst]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
      dsimp only [annealReadImmediate]
      rw [EStateM.bind_eq_error hread_err]
    exact ⟨_, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      hm_err⟩

/-- **`step_deref_oob_divergence`**: in `StateRelLM3_1`-related states where
`_d = copy *_p` reads past the end of the pointee's allocation, Anneal's
`stepMirFn` takes a normal step that stores the pointee local's whole value in
`_d`, while `lean-miri`'s `Miri.Interpreter.Step.step` reports undefined
behavior (`step_deref_oob_miri_ub`). Anneal's dereference of a tracked stack
pointer reads the borrowed local and ignores both `offsetBytes` and the pointee
type, so this out-of-bounds read is defined in Anneal's trusted semantics but
undefined in Rust. -/
theorem step_deref_oob_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hoob : localAlloc.allocation.byteSize.bytes.toNat <
      ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat)
    (hperm : e.perm ≠ .disabled)
    {sc : MirAst.ScalarInt}
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) := by
  refine ⟨?_, step_deref_oob_miri_ub hstate (opKind := MirAst.Operand.copy) (Or.inl rfl) hbb
    hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty himm_ptr hslot_p he htag hfind_la hoob⟩
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  have hlookup := (halloc.borrow_sync e he).2
  rw [htag] at hlookup
  obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
  have hread : evalOperand s.frame.locals (.copy ⟨ptrIdx, .cons .deref .nil⟩)
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
      .ok (.scalar sc) s.frame.locals := by
    unfold evalOperand
    dsimp only []
    rw [hslot_p]
    dsimp only []
    rw [hlookup]
    dsimp only []
    cases hp : e.perm with
    | disabled => exact absurd hp hperm
    | _ => simp only [htarget]; rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  unfold evalStmt
  dsimp only []
  unfold evalRvalue
  dsimp only []
  rw [hread]
  dsimp only []
  have hset := set?_eq_some_set hlt_af_d (LocalSlot.init (.scalar sc))
  have hget_set : get? (s.frame.locals.set dstIdx (.init (.scalar sc))) dstIdx =
      some (.init (.scalar sc)) := by
    rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
  cases hb : s.memory.borrows with
  | nil =>
    simp only [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
  | cons b₁ rest =>
    cases rest with
    | nil =>
      simp only [hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | cons b₂ rest' =>
      simp only [hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩

/-! ## 9. Deliverable 5: Composed `LM-3.1` Statement Simulation (`step_stmt_lm3_1_simulation`) -/

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

/-! ## 10. Real-Step `CastKind.PtrToPtr` & `BinOp.Offset` Simulation -/

theorem StateRelLM3_1.frame_rel_singleton
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf]) :
    FrameRelLM3_1 body m.machine allocMap s.frame tf := by
  obtain ⟨tf', hframes', _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [hframes] at hframes'
  injection hframes' with h1
  injection h1 with h2
  subst h2
  exact hfr

theorem evalStatement_assign_cast_ptrToPtr_eq
    (ld : List LocalDecl) (ly : LayoutTable)
    (dst : Place) (op : MirAst.Operand) (castTy : Ty) (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks ld ly) ()
      (translateStmt ⟨.assign dst (.cast .ptrToPtr op castTy), span⟩) m =
      Miri.Interpreter.runRvalue
        (do
          let destPlace ← annealEvalPlace ld ly (translatePlace dst)
          let src ← annealEvalOperand ld ly (translateOperand op) none
          Miri.Interpreter.Cast.cast (annealCastHooks ly) () 16 src .PtrToPtr
            (encodeTyId castTy) destPlace) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, translateCastKind, annealStepHooks]
  apply runRvalue_eq_of_eq
  unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
  dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, pure, EStateM.pure, bind, EStateM.bind]

theorem miri_cast_ptrToPtr_annealCastHooks_eq
    (layouts : LayoutTable) (m : AnnealStepState)
    (srcMut dstMut : Mutability) (srcPointee dstPointee : RigidTy)
    (srcTy dstTy : Ty)
    (hsrcTy : srcTy.kind = .rawPtr srcMut srcPointee)
    (hdstTy : dstTy.kind = .rawPtr dstMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (mptr : Miri.Memory.Pointer AnnealProv) :
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooks layouts)
      ()
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy srcTy layouts⟩
      (translateTy dstTy layouts)
      m =
      .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy dstTy layouts⟩ m := by
  have hsrc_enc : (translateTy srcTy layouts).ty = encodeRawPtrTyId srcPointee := by
    unfold translateTy encodeTyId
    rw [hsrcTy]
  have hdst_enc : (translateTy dstTy layouts).ty = encodeRawPtrTyId dstPointee := by
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
  obtain ⟨i₁, hi₁⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId srcPointee hsrc_thin
  obtain ⟨i₂, hi₂⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId dstPointee hdst_thin
  unfold Miri.Interpreter.Cast.ptrToPtr annealCastHooks
  simp only [hsrc_enc, hdst_enc, hsrc_sz, hdst_sz, hi₁, hi₂,
    bind, EStateM.bind, pure, EStateM.pure]
  rfl

theorem miri_cast_dispatch_ptrToPtr_eq
    (layouts : LayoutTable)
    (srcMut dstMut castMut : Mutability) (srcPointee dstPointee : RigidTy)
    (srcTy dstTy castTy : Ty)
    (hsrcTy : srcTy.kind = .rawPtr srcMut srcPointee)
    (hdstTy : dstTy.kind = .rawPtr dstMut dstPointee)
    (hcastTy : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (srcOp : Miri.Interpreter.Operand AnnealProv)
    (destVal : Miri.Interpreter.RuntimePlaceRef AnnealProv) :
    Miri.Interpreter.Cast.cast (annealCastHooks layouts) () 16
      ⟨srcOp, translateTy srcTy layouts⟩ .PtrToPtr (encodeTyId castTy)
      ⟨destVal, translateTy dstTy layouts⟩ =
      (do
        let value ← annealReadImmediate ⟨srcOp, translateTy srcTy layouts⟩
        let result ← Miri.Interpreter.Cast.ptrToPtr (annealCastHooks layouts) () value
          (translateTy dstTy layouts)
        annealWriteImmediate result.imm ⟨destVal, translateTy dstTy layouts⟩) := by
  have hsrc_enc : (translateTy srcTy layouts).ty = encodeRawPtrTyId srcPointee := by
    unfold translateTy encodeTyId
    rw [hsrcTy]
  have hdst_enc : (translateTy dstTy layouts).ty = encodeRawPtrTyId dstPointee := by
    unfold translateTy encodeTyId
    rw [hdstTy]
  have hcast_enc : encodeTyId castTy = encodeRawPtrTyId dstPointee := by
    unfold encodeTyId
    rw [hcastTy]
  have hsrc_lay : (translateTy srcTy layouts).layout = pointerLayoutData false := by
    unfold translateTy
    rw [hsrcTy]
  obtain ⟨i₁, hi₁⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId srcPointee hsrc_thin
  funext st
  unfold Miri.Interpreter.Cast.cast annealCastHooks
  simp only [hsrc_enc, hdst_enc, hcast_enc, hsrc_lay, pointerLayoutData, hi₁, beq_self_eq_true,
    ↓reduceIte, Bool.false_eq_true, bind, EStateM.bind, pure, EStateM.pure]

/-- **`step_cast_ptrToPtr_simulation` (`LM-3.1` Real-Step `CastKind.PtrToPtr`)**:
execute `_d = _s as *(const|mut) V` (`CastKind.PtrToPtr`) between thin
raw-pointer types (`isThinRawPtrPointee`) from any `StateRelLM3_1`-related state
where `_s` and `_d` are immediate raw-pointer locals (`_s` does not hold a
provenance-less integer scalar):
1. If `_s` is `.dead` or `.uninit`, BOTH machines raise UB (`StepRelLM3_1.ub`).
2. If `_s` holds `.ptr ptrVal 8` and `_d` is `.dead`, BOTH machines raise UB
   (`StepRelLM3_1.ub`).
3. If `_s` holds `.ptr ptrVal 8` and `_d` is live, BOTH machines copy the
   pointer (preserving provenance, `offsetBytes`, and `PtrRel allocMap`) into
   `_d` and advance to `stmtIdx + 1` in `StateRelLM3_1`. -/
theorem step_cast_ptrToPtr_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    {srcMut dstMut castMut : Mutability} {srcPointee dstPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hno_int : ∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_src⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_cast_ptrToPtr_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (.copy ⟨srcIdx, .nil⟩) castTy span m
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval : annealEvalPlace body.localDecls body.layouts (translatePlace ⟨dstIdx, .nil⟩) m =
      .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d
            (translateTy dstDecl.ty body.layouts)]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx := by
    intro mls hmls mp hmp
    simp only [tfa, cacheFrameLocalLayout] at hmls
    by_cases hds : dstIdx = srcIdx
    · subst hds
      rw [Array.getElem?_set_self] at hmls
      injection hmls with hm
      rw [← hm] at hmp
      exact himm_dst (tf.locals[dstIdx]'hlt_d) (Array.getElem?_eq_getElem hlt_d) mp hmp
    · rw [Array.getElem?_set_ne _ hds] at hmls
      exact himm_src mls hmls mp hmp
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
    hstate_a.cache_layout rfl hdecl_src hlt_sa
  have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  rcases hloc_s.rawPtr_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨hss_dead, hms_dead⟩ | ⟨hss_un, hms_un⟩ |
    ⟨sc_s, _, hss_sc, _, _, _⟩ |
    ⟨ptrVal, mptr, hss_ptr, hptrRel, hms_ptr⟩
  · -- Case 1: `_s` is `.dead` -> UB in both!
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_dead; subst hms_dead; rfl
    have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand
      dsimp only []
      rw [hslot_s, hss_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 2: `_s` is `.uninit` -> UB in both!
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_un; subst hms_un; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand
      dsimp only []
      rw [hslot_s, hss_un]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_src]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        miri_cast_dispatch_ptrToPtr_eq body.layouts srcMut dstMut castMut srcPointee dstPointee
          srcDecl.ty dstDecl.ty castTy hsrc_ty hdst_ty hcast_ty hsrc_thin]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 3: `_s` holds integer scalar -> excluded by `hno_int`
    exact absurd (hslot_s.trans (congrArg some hss_sc)) (hno_int sc_s)
  · -- Case 4: `_s` holds live pointer `.ptr ptrVal 8`!
    have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_ptr; subst hms_ptr; rfl
    have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have hrv_anneal := evalRvalue_cast_ptrToPtr_eq s.frame.locals s.memory body.localDecls
      body.layouts srcIdx ptrVal castTy (hslot_s.trans (congrArg some hss_ptr))
    have hlt_db : dstIdx < tfb.locals.size := by
      simp only [tfb, tfa, cacheFrameLocalLayout, Array.size_set]; exact hlt_d
    have hd_val_lay : (tfb.locals[dstIdx]'hlt_db).value = mls_d.value ∧
        (tfb.locals[dstIdx]'hlt_db).layout = some (translateTy dstDecl.ty body.layouts) := by
      simp only [tfb, tfa, cacheFrameLocalLayout]
      by_cases hsd : srcIdx = dstIdx
      · subst hsd
        have hdecl_eq : srcDecl = dstDecl := Option.some.inj (hdecl_src.symm.trans hdecl_dst)
        subst hdecl_eq
        simp [hmls_d_eq]
      · simp [Array.getElem_set, hsd, hmls_d_eq]
    have hd_Val := hd_val_lay.1
    have hd_Lay := hd_val_lay.2
    have hcast_ok := miri_cast_ptrToPtr_annealCastHooks_eq body.layouts
      { m with stack := ⟨#[tfb]⟩ } srcMut dstMut srcPointee dstPointee srcDecl.ty dstDecl.ty
      hsrc_ty hdst_ty hsrc_thin hdst_thin mptr
    have hread_src : annealReadImmediate
        ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
          translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } := rfl
    have hd_live_helper : ∀ oldImm, mls_d.value = .live (.immediate oldImm) →
        slot_d ≠ .dead →
        StepRelLM3_1 body m allocMap
          (evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
            body.localDecls body.layouts)
          (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
      intro oldImm hmd_imm hsd_ne
      have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
        hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_dst
      have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
      have hdb_live : tfb.locals[dstIdx]? =
          some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
        rw [Array.getElem?_eq_getElem hlt_db]
        rcases hls : tfb.locals[dstIdx]'hlt_db with ⟨v0, l0⟩
        rw [hls] at hd_Val hd_Lay
        dsimp only at hd_Val hd_Lay
        rw [hd_Val, hmd_imm, hd_Lay]
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_live
      have hw_ok := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar
                    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                hlt_db }]⟩ },
            .ok ()) := by
        rw [hm_stmt, htr_src]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
          miri_cast_dispatch_ptrToPtr_eq body.layouts srcMut dstMut castMut srcPointee dstPointee
            srcDecl.ty dstDecl.ty castTy hsrc_ty hdst_ty hcast_ty hsrc_thin,
          EStateM.bind_eq_ok hread_src, EStateM.bind_eq_ok hcast_ok, hw_ok]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr.location_eq]
      have ha_ok : evalStmt s
          ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
          body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s (s.frame.locals.set dstIdx (.init (.ptr ptrVal 8))) s.memory) := by
        unfold evalStmt
        dsimp only []
        rw [hrv_anneal]
        dsimp only []
        rw [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_ne
        | uninit =>
          simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
          congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
        | init _ =>
          simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
          congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
      rw [ha_ok]
      refine .step _ _ ?_
      have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts
          (.init (.ptr ptrVal 8))
          { tfb.locals[dstIdx]'hlt_db with
            value := .live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) } := by
        rw [List.map_id]
        exact .rawPtr ptrVal mptr _ dstMut dstPointee
          (by rw [hd_Lay]; intro l hl; exact (Option.some.inj hl).symm)
          hdst_ty hptrRel
      have hstep_rel := hstate_b.advance_write_immediate_perm_map rfl id
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        hdecl_dst hnot_dst (hd_Val.trans hmd_imm) hnew_d
        hcal hstack hprot hcaller (by rw [List.map_id]; exact hbor) rfl
      rw [List.map_id] at hstep_rel
      exact hstep_rel
    rcases hloc_d.rawPtr_immediate_cases hdst_ty (himm_dst mls_d hmls_d) with
      ⟨hsd_dead, hmd_dead⟩ | ⟨hsd_un, hmd_un⟩ |
      ⟨_, msc_d, hsd_sc, _, _, hmd_sc⟩ |
      ⟨_, mptr_d, hsd_ptr, _, hmd_ptr⟩
    · have hdb_dead : tfb.locals[dstIdx]? =
          some ⟨.dead, some (translateTy dstDecl.ty body.layouts)⟩ := by
        rw [Array.getElem?_eq_getElem hlt_db]
        rcases hls : tfb.locals[dstIdx]'hlt_db with ⟨v0, l0⟩
        rw [hls] at hd_Val hd_Lay
        dsimp only at hd_Val hd_Lay
        rw [hd_Val, hmd_dead, hd_Lay]
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_dead
      have ha_ub : evalStmt s
          ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only []
        rw [hrv_anneal]
        dsimp only []
        rw [hslot_d, hsd_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt, htr_src]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
          miri_cast_dispatch_ptrToPtr_eq body.layouts srcMut dstMut castMut srcPointee dstPointee
            srcDecl.ty dstDecl.ty castTy hsrc_ty hdst_ty hcast_ty hsrc_thin,
          EStateM.bind_eq_ok hread_src, EStateM.bind_eq_ok hcast_ok,
          annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
            rfl hget_db]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      exact .ub _ _
    · exact hd_live_helper .uninit hmd_un (by rw [hsd_un]; simp)
    · exact hd_live_helper (.scalar (.fromScalarInt msc_d)) hmd_sc (by rw [hsd_sc]; simp)
    · exact hd_live_helper (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr_d))
        hmd_ptr (by rw [hsd_ptr]; simp)

theorem evalStatement_assign_binOp_offset_eq
    (ld : List LocalDecl) (ly : LayoutTable)
    (dst : Place) (lhs rhs : MirAst.Operand) (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks ld ly) ()
      (translateStmt ⟨.assign dst (.binaryOp .offset lhs rhs), span⟩) m =
      Miri.Interpreter.runRvalue
        (do
          let dest ← annealEvalPlace ld ly (translatePlace dst)
          let layout := dest.layout
          let left ← annealEvalOperand ld ly (translateOperand lhs) (some layout)
          let left ← annealReadImmediate left
          let right ← annealEvalOperand ld ly (translateOperand rhs) none
          let right ← annealReadImmediate right
          let result ← Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks ld ly) () .Offset left right
          assertRvalueLayoutPub result.layout layout
          annealWriteImmediate result.imm dest) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, translateBinOp, annealStepHooks]
  apply runRvalue_eq_of_eq
  rw [evalRvalueIntoPlace_binaryOp_def]
  unfold annealRvalueHooks
  simp only [Miri.MIR.BinOp.leftHomogeneous, Miri.MIR.BinOp.rightHomogeneous,
    ↓reduceIte, Bool.false_eq_true]

theorem scalarOps_binary_offset_byte_eq
    (ld : List LocalDecl) (ly : LayoutTable)
    {ptrTy rhsTy : Ty} {mutability : Mutability} {pointeeKind : RigidTy}
    (hptr_ty : ptrTy.kind = .rawPtr mutability pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (mptr : Miri.Memory.Pointer AnnealProv)
    (rightInt : Miri.Memory.ScalarInt) :
    Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Offset
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy ptrTy ly⟩
      ⟨.scalar (.fromScalarInt rightInt), translateTy rhsTy ly⟩ =
      annealPointerBinary ly .Offset
        ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
          translateTy ptrTy ly⟩
        ⟨.scalar (.fromScalarInt rightInt), translateTy rhsTy ly⟩ := by
  have hptr_enc : (translateTy ptrTy ly).ty = encodeRawPtrTyId pointeeKind := by
    unfold translateTy encodeTyId; rw [hptr_ty]
  have hrhs_enc : (translateTy rhsTy ly).ty = encodeTyId rhsTy := rfl
  funext st
  rw [scalarOps_binary_def]
  unfold annealScalarOpsHooks
  rcases hpt with hpt | hpt <;> rcases hrhs_ty with hrhs | hrhs
  · have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
    have hr : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
    simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
  · have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
    have hr : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
    simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
  · have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
    have hr : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
    simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
  · have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
    have hr : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
    simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]

private theorem mulWithOverflow_stride_one_eq
    {sc : MirAst.ScalarInt} {rightInt : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc rightInt) (hsc_sz : sc.sizeBytes = 8) (hbits : sc.bits < 2 ^ 32)
    (rightKind : Miri.MIR.IntegerKind)
    (hkind : rightKind = .usize ∨ rightKind = .isize) :
    ∃ scaledInt : Miri.Memory.ScalarInt,
      Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨rightInt, ⟨Miri.ABI.Size.ofBytes 8, rightKind⟩⟩
        ⟨Miri.Memory.ScalarInt.ofUInt64 1, ⟨Miri.ABI.Size.ofBytes 8, rightKind⟩⟩ =
        .ok (.withOverflow scaledInt false) ∧
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) scaledInt).toTargetIsize
        annealPointerArithmetic.pointerSize =
        .ok (Int64.ofInt (sc.bits : Int)) := by
  have hrel1 : ScalarRel ⟨1, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 1) :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  have hsz_eq : sc.sizeBytes = (⟨1, 8⟩ : MirAst.ScalarInt).sizeBytes := hsc_sz
  have hbin : Miri.Interpreter.IntegerOps.binary .MulWithOverflow
      ⟨rightInt, ⟨Miri.ABI.Size.ofBytes 8, rightKind⟩⟩
      ⟨Miri.Memory.ScalarInt.ofUInt64 1, ⟨Miri.ABI.Size.ofBytes 8, rightKind⟩⟩ =
      arithmeticInt .MulWithOverflow
        (decodeBitsInt rightKind.signed sc.sizeBytes sc.bits)
        (decodeBitsInt rightKind.signed sc.sizeBytes 1)
        ⟨translateSizeBytes sc.sizeBytes, rightKind⟩ := by
    have hb := integerOps_binary_sameType_eq hrel hrel1 hsz_eq rightKind .MulWithOverflow rfl
    rw [hsc_sz] at hb ⊢
    exact hb
  have hdec_l : decodeBitsInt rightKind.signed 8 sc.bits = (sc.bits : Int) := by
    unfold decodeBitsInt
    cases rightKind.signed
    · rfl
    · simp only [↓reduceIte]
      have hlt63 : sc.bits < 2 ^ (8 * 8 - 1) := by omega
      simp [hlt63]
  have hdec_r : decodeBitsInt rightKind.signed 8 1 = 1 := by
    unfold decodeBitsInt
    cases rightKind.signed <;> rfl
  have hv8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨scaledInt, lossy, htr, hrel_s, hovf⟩ :=
    truncateInt_spec hv8 rightKind (sc.bits : Int)
  have hmod : ((sc.bits : Int) % (2 : Int) ^ (8 * 8)).toNat = sc.bits := by
    have hpow : (2 : Int) ^ (8 * 8) = ((2 ^ 64 : Nat) : Int) := by decide
    rw [hpow]
    have hlt64 : (sc.bits : Int) < ((2 ^ 64 : Nat) : Int) := Int.ofNat_lt.mpr (by omega)
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) hlt64, Int.toNat_natCast]
  rw [hmod] at hrel_s
  have hcan_rep : canRepresentInt rightKind.signed 8 (sc.bits : Int) = true := by
    unfold canRepresentInt
    rcases hkind with rfl | rfl
    · have hsign : Miri.MIR.IntegerKind.usize.signed = false := rfl
      rw [hsign]
      simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
      exact ⟨Int.natCast_nonneg _, by omega⟩
    · have hsign : Miri.MIR.IntegerKind.isize.signed = true := rfl
      rw [hsign]
      simp only [↓reduceIte, decide_eq_true_eq]
      exact ⟨by omega, by omega⟩
  rw [hcan_rep, Bool.not_true] at hovf
  have harith : arithmeticInt .MulWithOverflow (sc.bits : Int) 1
      ⟨translateSizeBytes 8, rightKind⟩ = .ok (.withOverflow scaledInt false) := by
    rw [arithmeticInt_nonDivRem_eq .MulWithOverflow (sc.bits : Int) 1 8 rightKind rfl rfl]
    simp only [Int.mul_one, htr, scalarResultInt, hovf, Miri.MIR.BinOp.isUnchecked,
      Miri.MIR.BinOp.isOverflowing, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
  refine ⟨scaledInt, ?_, ?_⟩
  · rw [hbin, hsc_sz, hdec_l, hdec_r]
    exact harith
  · have hp_sz : annealPointerArithmetic.pointerSize = Miri.ABI.Size.ofBytes 8 := rfl
    have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) scaledInt).toScalarInt =
        .ok scaledInt := rfl
    have hbz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
    have hsz8 : Miri.ABI.Size.ofBytes 8 =
        translateSizeBytes (⟨sc.bits, 8⟩ : MirAst.ScalarInt).sizeBytes := rfl
    have htb : scaledInt.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc.bits) := by
      rw [hsz8]; exact hrel_s.toBits_eq
    have hse : (Miri.ABI.Size.ofBytes 8).signExtend (BitVec.ofNat 128 sc.bits) =
        .ok (sc.bits : Int) := by
      rw [hsz8, size_signExtend_translateSizeBytes hv8]
      have hbv := bitVec_ofNat_toNat_of_valid hv8 hrel_s.canonical
      have hlt64 : sc.bits < 2 ^ (8 * 8) := by omega
      rw [hbv, Nat.mod_eq_of_lt hlt64]
      unfold decodeBitsInt
      have hlt63 : sc.bits < 2 ^ (8 * 8 - 1) := by omega
      simp [hlt63]
    unfold Miri.Memory.Scalar.toTargetIsize Miri.Memory.Scalar.toInt Miri.Memory.Scalar.toBits
    simp only [hp_sz, hbz, Bool.false_eq_true, ↓reduceIte, hsi, htb, hse,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    have hfit : (((sc.bits : Int) < -(2 ^ 63 : Int)) || ((sc.bits : Int) ≥ (2 ^ 63 : Int))) = false := by
      rw [Bool.or_eq_false_iff, decide_eq_false_iff_not, decide_eq_false_iff_not]
      exact ⟨by omega, by omega⟩
    rw [hfit]
    rfl

theorem annealPointerBinary_byte_eq
    (ly : LayoutTable)
    {ptrTy rhsTy : Ty} {mutability : Mutability} {pointeeKind : RigidTy}
    (hptr_ty : ptrTy.kind = .rawPtr mutability pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    {sc : MirAst.ScalarInt} {rightInt : Miri.Memory.ScalarInt}
    (hrel : ScalarRel sc rightInt) (hsc_sz : sc.sizeBytes = 8) (hbits : sc.bits < 2 ^ 32)
    (mptr : Miri.Memory.Pointer AnnealProv) (st : AnnealStepState) :
    annealPointerBinary ly .Offset
      ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
        translateTy ptrTy ly⟩
      ⟨.scalar (.fromScalarInt rightInt), translateTy rhsTy ly⟩ st =
      match Miri.Interpreter.ptrOffsetInbounds annealPointerArithmetic
          mptr.withOptionalProvenance (Int64.ofInt (sc.bits : Int))
          (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
      | .error (.access _) => .error (.undefinedBehavior "pointer Offset out of bounds") st
      | .error (.pointer _) => .error (.invalidProgram "pointer Offset arithmetic error") st
      | .ok nextPtr =>
        match Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout nextPtr with
        | .error err => .error (Miri.Interpreter.ScalarOps.scalarError err) st
        | .ok result => .ok ⟨.scalar result, translateTy ptrTy ly⟩ st := by
  have hptr_enc : (translateTy ptrTy ly).ty = encodeRawPtrTyId pointeeKind := by
    unfold translateTy encodeTyId; rw [hptr_ty]
  have htb : rightInt.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc.bits) := by
    have hsz : Miri.ABI.Size.ofBytes 8 = translateSizeBytes sc.sizeBytes := by rw [hsc_sz]; rfl
    rw [hsz]; exact hrel.toBits_eq
  have hfrom1 : Miri.Memory.Scalar.fromInt (Prov := AnnealProv) 1 (Miri.ABI.Size.ofBytes 8) =
      .ok (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 1)) := rfl
  have htoInt64 : (Int64.ofInt (sc.bits : Int)).toInt < 0 ↔ False := by
    rw [int64_toInt_ofInt_of_lt_u32 sc.bits hbits]
    exact ⟨fun h => by omega, False.elim⟩
  have hlt0_false : decide ((Int64.ofInt (sc.bits : Int)).toInt < 0) = false :=
    decide_eq_false htoInt64.mp
  unfold annealPointerBinary
  have hop_ne : (Miri.MIR.BinOp.Offset != .Offset) = false := rfl
  have htoSc_l : (Miri.Interpreter.Immediate.scalar
      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)).toScalar =
      .ok (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) := rfl
  have htoSc_r : (Miri.Interpreter.Immediate.scalar
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) rightInt)).toScalar =
      .ok (.fromScalarInt rightInt) := rfl
  have htoSi_r : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) rightInt).toScalarInt =
      .ok rightInt := rfl
  have htoSi_1 : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv)
      (Miri.Memory.ScalarInt.ofUInt64 1)).toScalarInt =
      .ok (Miri.Memory.ScalarInt.ofUInt64 1) := rfl
  rcases hpt with hpt | hpt <;> rcases hrhs_ty with hrhs | hrhs
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel hsc_sz hbits .usize (Or.inl rfl)
    have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 false := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 20 ly =
        { ty := 20, layout := scalarLayoutData 1 false } := rfl
    have hisSized : (!(({ ty := 20, layout := scalarLayoutData 1 false } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 20, layout := scalarLayoutData 1 false } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 false).backendRepr.isSigned = .ok false := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l,
      scalar_fromPointer_toPointer_eq mptr, hp, rawPtrPointeeEncodedTyId?, hpt_lay,
      hisSized, hr_ty, hr_lay, classifyEncodedTyId, htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 false).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 false).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel hsc_sz hbits .isize (Or.inr rfl)
    have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 true := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 20 ly =
        { ty := 20, layout := scalarLayoutData 1 false } := rfl
    have hisSized : (!(({ ty := 20, layout := scalarLayoutData 1 false } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 20, layout := scalarLayoutData 1 false } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 true).backendRepr.isSigned = .ok true := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l,
      scalar_fromPointer_toPointer_eq mptr, hp, rawPtrPointeeEncodedTyId?, hpt_lay,
      hisSized, hr_ty, hr_lay, classifyEncodedTyId, htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 true).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 false).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel hsc_sz hbits .usize (Or.inl rfl)
    have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 false := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 10 ly =
        { ty := 10, layout := scalarLayoutData 1 true } := rfl
    have hisSized : (!(({ ty := 10, layout := scalarLayoutData 1 true } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 10, layout := scalarLayoutData 1 true } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 false).backendRepr.isSigned = .ok false := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l,
      scalar_fromPointer_toPointer_eq mptr, hp, rawPtrPointeeEncodedTyId?, hpt_lay,
      hisSized, hr_ty, hr_lay, classifyEncodedTyId, htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 false).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 true).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel hsc_sz hbits .isize (Or.inr rfl)
    have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 true := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 10 ly =
        { ty := 10, layout := scalarLayoutData 1 true } := rfl
    have hisSized : (!(({ ty := 10, layout := scalarLayoutData 1 true } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 10, layout := scalarLayoutData 1 true } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 true).backendRepr.isSigned = .ok true := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l,
      scalar_fromPointer_toPointer_eq mptr, hp, rawPtrPointeeEncodedTyId?, hpt_lay,
      hisSized, hr_ty, hr_lay, classifyEncodedTyId, htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 true).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 true).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl

theorem evalRvalue_binOp_offset_scalarOperand_eq
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {rhsOp : MirAst.Operand} {rhsTy : Ty}
    (hop : WellTypedScalarOperand body tf rhsOp rhsTy)
    (locals : List LocalSlot) (mem : Memory)
    (ptrIdx : Local) (ptrVal : ProvenancePtr)
    (hptr : get? locals ptrIdx = some (.init (.ptr ptrVal 8))) :
    evalRvalue locals (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp) mem body.localDecls
      body.layouts =
      match evalOperand locals rhsOp mem.borrows mem.globals body.layouts mem.callerLocals with
      | .ok (.scalar sc) locals' =>
        .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8) locals' mem
      | .ok _ _ => .unsupported
      | .ub => .ub
      | .unsupported => .unsupported := by
  cases hop <;>
  · unfold evalRvalue
    have hlhs : evalOperand locals (.copy ⟨ptrIdx, .nil⟩) mem.borrows mem.globals body.layouts
        mem.callerLocals = .ok (.ptr ptrVal 8) locals := by
      simp [evalOperand, readProjectedValue, hptr]
    dsimp only []
    rw [hlhs]
    dsimp only []
    cases hr : evalOperand locals _ mem.borrows mem.globals body.layouts mem.callerLocals with
    | ub => rfl
    | unsupported => rfl
    | ok v locs' => cases v <;> rfl

/-- **`step_binOp_offset_simulation` (`LM-3.1` Real-Step `BinOp.Offset` Simulation)**:
execute `_d = Offset(copy _p, rhsOp)` on a byte-sized raw pointer (`*const u8`,
`*mut u8`, `*const i8`, `*mut i8`) and `usize`/`isize` offset `rhsOp` from any
`StateRelLM3_1`-related state (`_p` not holding a provenance-less scalar):
1. If `_p` is `.dead`/`.uninit` or `rhsOp` is `.dead`/`.uninit`, BOTH machines
   raise UB (`StepRelLM3_1.ub`).
2. If `_p` holds `.ptr ptrVal 8` and `rhsOp` evaluates to `sc` such that EITHER
   `sc.bits = 0` (which is defined even on dangling pointers!) OR `_p`'s target
   local `e.localIdx` is live (`get? s.frame.locals e.localIdx ≠ some .dead`) and
   `ptrVal.offsetBytes + sc.bits ≤ (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat`:
   BOTH machines evaluate the offset to `ptrVal.offsetBytes + sc.bits` (preserving
   provenance and `PtrRel allocMap`), raising UB if `_d` is `.dead` or stepping
   in lockstep to `StateRelLM3_1`-related states if `_d` is live. -/
theorem step_binOp_offset_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : LocalDecl} {ptrMut dstMut : Mutability} {pointeeKind : RigidTy}
    {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hinbounds : ∀ ptrVal sc e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
        s.memory.callerLocals = .ok (.scalar sc) s.frame.locals →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      sc.bits = 0 ∨
        (get? s.frame.locals e.localIdx ≠ some .dead ∧
          ptrVal.offsetBytes + sc.bits ≤
            (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, _⟩ := id hstate
  obtain ⟨himm_dst, himm_ptr⟩ := himm tf hframes
  have hop_tf := hop_rhs tf hframes
  have hrhs_prim : IsPrimScalarTy rhsTy := by
    rcases hrhs_ty with hk | hk
    · exact Or.inr (Or.inr (Or.inr ⟨.usize, hk⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.isize, hk⟩))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_binOp_offset_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (.copy ⟨ptrIdx, .nil⟩) rhsOp span m
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval : annealEvalPlace body.localDecls body.layouts (translatePlace ⟨dstIdx, .nil⟩) m =
      .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d
            (translateTy dstDecl.ty body.layouts)]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa : WellTypedScalarOperand body tfa rhsOp rhsTy :=
    hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  have himm_p_tfa : IsImmediateFrameLocal tfa ptrIdx := by
    intro mls hmls mp hmp
    simp only [tfa, cacheFrameLocalLayout] at hmls
    by_cases hdp : dstIdx = ptrIdx
    · subst hdp
      rw [Array.getElem?_set_self] at hmls
      injection hmls with hm
      rw [← hm] at hmp
      exact himm_dst (tf.locals[dstIdx]'hlt_d) (Array.getElem?_eq_getElem hlt_d) mp hmp
    · rw [Array.getElem?_set_ne _ hdp] at hmls
      exact himm_ptr mls hmls mp hmp
  let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
  have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
    hstate_a.cache_layout rfl hdecl_ptr hlt_pa
  have hop_tfb : WellTypedScalarOperand body tfb rhsOp rhsTy :=
    hop_tfa.of_cacheFrameLocalLayout ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
  have htr_lhs : translateOperand (.copy ⟨ptrIdx, .nil⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
  have hlay_eq : translateTy ptrDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    unfold translateTy encodeTyId
    rw [hptr_ty, hdst_ty]
  rcases hloc_p.rawPtr_immediate_cases hptr_ty (himm_p_tfa mls_p hmls_p) with
    ⟨hsp_dead, hmp_dead⟩ | ⟨hsp_un, hmp_un⟩ |
    ⟨sc_p, _, hsp_sc, _, _, _⟩ |
    ⟨ptrVal, mptr, hsp_ptr, hptrRel, hmp_ptr⟩
  · -- Case 1: `_p` is `.dead` -> UB in both!
    have hmls_p' : tfa.locals[ptrIdx]'hlt_pa = ⟨.dead, mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_dead; subst hmp_dead; rfl
    have hlhs_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand
      dsimp only []
      rw [hslot_p, hsp_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_lhs]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hlhs_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · -- Case 2: `_p` is `.uninit` -> UB in both!
    have hmls_p' : tfa.locals[ptrIdx]'hlt_pa = ⟨.live (.immediate .uninit), mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_un; subst hmp_un; rfl
    have hlhs_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand
      dsimp only []
      rw [hslot_p, hsp_un]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_lhs]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · exact absurd (hslot_p.trans (congrArg some hsp_sc)) (hno_int sc_p)
  · -- Case 4: `_p` holds live `.ptr ptrVal 8`!
    have hmls_p' : tfa.locals[ptrIdx]'hlt_pa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
    have hlhs_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
    have hread_lhs : annealReadImmediate
        ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy ptrDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
          translateTy ptrDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } := rfl
    have hsp_full : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) :=
      hslot_p.trans (congrArg some hsp_ptr)
    rcases evalOperand_scalar_lm3_1_simulation hstate_b rfl hop_tfb hrhs_prim none with
      ⟨m_rhs, msg_rhs, hrhs_ub, hm_rhs_ub⟩ |
      ⟨sc, msc, tfc, hrhs_ok, hm_rhs_ok, hstate_c, hrel_imm, hloc_id_c, htfc_preserve⟩
    · -- Subcase 4a: `rhsOp` fails with UB in both!
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
          (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt
        dsimp only []
        rw [evalRvalue_binOp_offset_scalarOperand_eq hop_tf s.frame.locals s.memory
          ptrIdx ptrVal hsp_full, hrhs_ub]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt
            ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
          (m_rhs, .error (.undefinedBehavior msg_rhs)) := by
        rw [hm_stmt, htr_lhs]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
          EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_error hm_rhs_ub]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · -- Subcase 4b: `rhsOp` evaluates to `sc` (`msc`)!
      have hsc_rel : ScalarRel sc msc ∧ sc.sizeBytes = 8 := by
        cases hrel_imm with
        | scalar _ _ hrel hsz _ _ =>
          have hlay_rhs : (translateTy rhsTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
            rcases hrhs_ty with hk | hk <;> (unfold translateTy; rw [hk]; rfl)
          rw [hlay_rhs] at hsz
          have hb : (8 : UInt64) = UInt64.ofNat sc.sizeBytes := congrArg Miri.ABI.Size.bytes hsz
          have hcan := hrel.validBytes
          have hsz8 : sc.sizeBytes = 8 := by
            rcases hcan with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb ⊢ <;> first | rfl | cases hb
          exact ⟨hrel, hsz8⟩
      obtain ⟨allocId, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, e, he_mem, he_tag, he_aid⟩ :=
        hptrRel
      subst he_aid
      obtain ⟨tgtDecl, htgt_decl, htgt_prim⟩ := halloc.target_decl e he_mem
      have hsc_cases := hinbounds ptrVal sc e tgtDecl hsp_full hrhs_ok he_mem he_tag htgt_decl
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
            some (.concrete e.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
        subst hprov_eq hmptr_off; rfl
      have hptr_step : sc.bits < 2 ^ 32 ∧
          ptrVal.offsetBytes + sc.bits < 2 ^ 32 ∧
          Miri.Interpreter.ptrOffsetInbounds annealPointerArithmetic
            mptr.withOptionalProvenance (Int64.ofInt (sc.bits : Int))
            (annealResolvePtr m.machine) (annealLookupAlloc m.machine) =
            .ok ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes + sc.bits)),
              some (.concrete e.allocId borTag)⟩ := by
        rcases hsc_cases with hbits0 | ⟨hlive_e, hinb_e⟩
        · refine ⟨by omega, by omega, ?_⟩
          rw [hmptr_opt, hbits0]
          simpa [Nat.add_zero] using
            ptrOffsetInbounds_zero_ok m.machine
              ⟨Miri.ABI.Size.ofBytes
                (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
                some (.concrete e.allocId borTag)⟩
        · obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local htgt_decl
          have ht_ne_dead : slot_t ≠ .dead := fun hd => hlive_e (hslot_t.trans (congrArg some hd))
          obtain ⟨_, _, hsh_t⟩ :=
            (halloc.local_alloc_sync tf hframes e he_mem).1 slot_t hslot_t ht_ne_dead
          obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_t tgtDecl htgt_decl
          obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he_mem
          have htgt_le16 : (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat ≤ 16 := by
            rcases htgt_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
            · simp only [translateTy, hk]; decide
            · simp only [translateTy, hk]; decide
            · cases it <;> (simp only [translateTy, hk]; decide)
            · cases ut <;> (simp only [translateTy, hk]; decide)
          have hsz_nat : localAlloc.allocation.byteSize.bytes.toNat ≤ 16 := by
            rw [hshape_la.byteSize_eq]; exact htgt_le16
          have hinb_la : ptrVal.offsetBytes + sc.bits ≤
              localAlloc.allocation.byteSize.bytes.toNat := by
            rw [hshape_la.byteSize_eq]; exact hinb_e
          have hbits_lt : sc.bits < 2 ^ 32 := by omega
          have hsum_lt : ptrVal.offsetBytes + sc.bits < 2 ^ 32 := by omega
          refine ⟨hbits_lt, hsum_lt, ?_⟩
          rw [hmptr_opt]
          exact ptrOffsetInbounds_live_inbounds_ok e.allocId borTag ptrVal.offsetBytes sc.bits
            localAlloc hid_lt hoff_lt hbits_lt hbase hfind_la hinb_la
      obtain ⟨hbits_lt, hsum_lt, hpoff_ok⟩ := hptr_step
      let mptr' : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes
          (annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes + sc.bits)),
          .concrete e.allocId borTag⟩
      have hptrRel' : PtrRel allocMap
          { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } mptr' :=
        .mk e.allocId borTag rfl hid_lt hsum_lt rfl ⟨e, he_mem, he_tag, rfl⟩
      have hbin_ok : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
          ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            translateTy ptrDecl.ty body.layouts⟩
          ⟨.scalar (.fromScalarInt msc), translateTy rhsTy body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } =
          .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr'),
            translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tfc]⟩ } := by
        rw [scalarOps_binary_offset_byte_eq body.localDecls body.layouts hptr_ty hpt hrhs_ty,
          annealPointerBinary_byte_eq body.layouts hptr_ty hpt hrhs_ty hsc_rel.1 hsc_rel.2
            hbits_lt mptr { m with stack := ⟨#[tfc]⟩ },
          hpoff_ok]
        rfl
      have hassert_ok : assertRvalueLayoutPub (translateTy ptrDecl.ty body.layouts)
          (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfc]⟩ } =
          .ok () { m with stack := ⟨#[tfc]⟩ } := by
        unfold assertRvalueLayoutPub
        simp [hlay_eq, pure, EStateM.pure]
      have hrv_anneal : evalRvalue s.frame.locals
          (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp) s.memory body.localDecls body.layouts =
          .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8)
            s.frame.locals s.memory := by
        rw [evalRvalue_binOp_offset_scalarOperand_eq hop_tf s.frame.locals s.memory
          ptrIdx ptrVal hsp_full, hrhs_ok]
      have hfr_c := hstate_c.frame_rel_singleton rfl
      obtain ⟨_, mls_dc, _, hlt_dc, _, hmls_dc, hmls_dc_eq, hloc_dc⟩ :=
        hfr_c.lookup_local hdecl_dst
      have hd_tfb : (tfb.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
          some mls_d.value := by
        simp only [tfb, tfa, cacheFrameLocalLayout]
        by_cases hpd : ptrIdx = dstIdx
        · subst hpd
          simp [Array.getElem?_set_self, Array.getElem_set_self, hmls_d_eq]
        · rw [Array.getElem?_set_ne _ hpd, Array.getElem?_set_self]
          simp [hmls_d_eq]
      have hd_Val : mls_dc.value = mls_d.value := by
        have hp_c := htfc_preserve dstIdx
        rw [hd_tfb, hmls_dc] at hp_c
        injection hp_c
      have hd_live_helper : ∀ oldImm, mls_d.value = .live (.immediate oldImm) →
          slot_d ≠ .dead →
          StepRelLM3_1 body m allocMap
            (evalStmt s
              ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩
              body.localDecls body.layouts)
            (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
        intro oldImm hmd_imm hsd_ne
        have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
          hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_dst
        have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
        have hdc_live : tfc.locals[dstIdx]? =
            some ⟨.live (.immediate oldImm), mls_dc.layout⟩ := by
          rw [hmls_dc]
          rcases mls_dc with ⟨vd, ld⟩
          dsimp only at hd_Val
          rw [hd_Val, hmd_imm]
        have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_live
        have hw_ok := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr'))
          (m := { m with stack := ⟨#[tfc]⟩ }) (id0 := tfc.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
        have hloc_id_tf : tfc.localsIdentity = tf.localsIdentity := hloc_id_c
        rw [hloc_id_tf] at hw_ok
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt
              ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
            ({ m with stack := ⟨#[{ tfc with
                locals := tfc.locals.set dstIdx
                  { tfc.locals[dstIdx]'hlt_dc with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr'))) }
                  hlt_dc }]⟩ },
              .ok ()) := by
          rw [hm_stmt, htr_lhs]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
            EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_ok hm_rhs_ok,
            EStateM.bind_eq_ok hbin_ok, EStateM.bind_eq_ok hassert_ok]
          dsimp only []
          rw [hw_ok]
          simp only [hloc_id_tf]
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
          hfr_c.location_eq]
        have ha_ok : evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩
            body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s
                (s.frame.locals.set dstIdx
                  (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8)))
                s.memory) := by
          unfold evalStmt
          dsimp only []
          rw [hrv_anneal]
          dsimp only []
          rw [hslot_d]
          cases slot_d with
          | dead => exact absurd rfl hsd_ne
          | uninit =>
            simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
            congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
          | init _ =>
            simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
            congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
        rw [ha_ok]
        refine .step _ _ ?_
        have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts
            (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8))
            { tfc.locals[dstIdx]'hlt_dc with
              value := .live (.immediate (.scalar
                (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr'))) } := by
          rw [List.map_id]
          exact .rawPtr _ mptr' _ dstMut pointeeKind
            (by rw [hmls_dc_eq]; exact hloc_dc.cachedLayout_eq)
            hdst_ty hptrRel'
        have hval_dc : (tfc.locals[dstIdx]'hlt_dc).value = .live (.immediate oldImm) := by
          rw [hmls_dc_eq, hd_Val, hmd_imm]
        have hstep_rel := hstate_c.advance_write_immediate_perm_map rfl id
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          hdecl_dst hnot_dst hval_dc hnew_d
          hcal hstack hprot hcaller (by rw [List.map_id]; exact hbor) rfl
        rw [List.map_id] at hstep_rel
        exact hstep_rel
      rcases hloc_d.rawPtr_immediate_cases hdst_ty (himm_dst mls_d hmls_d) with
        ⟨hsd_dead, hmd_dead⟩ | ⟨hsd_un, hmd_un⟩ |
        ⟨_, msc_d, hsd_sc, _, _, hmd_sc⟩ |
        ⟨_, mptr_d, hsd_ptr, _, hmd_ptr⟩
      · have hdc_dead : tfc.locals[dstIdx]? = some ⟨.dead, mls_dc.layout⟩ := by
          rw [hmls_dc]
          rcases mls_dc with ⟨vd, ld⟩
          dsimp only at hd_Val
          rw [hd_Val, hmd_dead]
        have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_dead
        have ha_ub : evalStmt s
            ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt
          dsimp only []
          rw [hrv_anneal]
          dsimp only []
          rw [hslot_d, hsd_dead]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt
              ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
            ({ m with stack := ⟨#[tfc]⟩ },
              .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt, htr_lhs]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
            EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_ok hm_rhs_ok,
            EStateM.bind_eq_ok hbin_ok, EStateM.bind_eq_ok hassert_ok,
            annealWriteImmediate_dead (m := { m with stack := ⟨#[tfc]⟩ }) (id0 := tf.localsIdentity)
              rfl hget_dc]
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
          hm_err]
        exact .ub _ _
      · exact hd_live_helper .uninit hmd_un (by rw [hsd_un]; simp)
      · exact hd_live_helper (.scalar (.fromScalarInt msc_d)) hmd_sc (by rw [hsd_sc]; simp)
      · exact hd_live_helper (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr_d))
          hmd_ptr (by rw [hsd_ptr]; simp)

/-- **`step_binOp_offset_oob_dangling_miri_ub` (`LM-3.1` Real-Step `BinOp.Offset`
Out-of-Bounds / Dangling Divergence)**:
when `_p` holds a `StateRelLM3_1`-related byte-sized raw pointer `.ptr ptrVal 8`
targeting `e ∈ allocMap`, `rhsOp` evaluates to a positive count `0 < sc.bits < 2^32`,
`_d` is live immediate, and EITHER `e.localIdx` is `.dead` (dangling pointer
after `StorageDead`) OR `ptrVal.offsetBytes + sc.bits` exceeds `e.localIdx`'s
byte size:
1. Anneal's `stepMirFn body s` SUCCEEDS (`MirStepNode.step`), advancing
   `ptrVal.offsetBytes` by `sc.bits` without checking bounds or liveness; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` under `annealStepHooks` FAILS WITH
   `StepError.undefinedBehavior`. -/
theorem step_binOp_offset_oob_dangling_miri_ub
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl tgtDecl : LocalDecl}
    {ptrMut : Mutability} {pointeeKind : RigidTy} {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {sc : MirAst.ScalarInt} {e : AllocMapEntry}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he_mem : e ∈ allocMap)
    (he_tag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (hpos : 0 < sc.bits)
    (hbits_lt : sc.bits < 2 ^ 32)
    (hbad : get? s.frame.locals e.localIdx = some .dead ∨
      (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat <
        ptrVal.offsetBytes + sc.bits) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8)))
          s.memory) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, hbor, halloc, _⟩ := id hstate
  obtain ⟨himm_dst, himm_ptr⟩ := himm tf hframes
  have hop_tf := hop_rhs tf hframes
  have hrhs_prim : IsPrimScalarTy rhsTy := by
    rcases hrhs_ty with hk | hk
    · exact Or.inr (Or.inr (Or.inr ⟨.usize, hk⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.isize, hk⟩))
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
  have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
    hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_dst
  have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
  refine ⟨?_, ?_⟩
  · -- (1) Anneal steps!
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt
    dsimp only []
    rw [evalRvalue_binOp_offset_scalarOperand_eq hop_tf s.frame.locals s.memory
      ptrIdx ptrVal hptr_slot, hrhs_eval]
    dsimp only []
    rw [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit =>
      simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
    | init _ =>
      simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
  · -- (2) `lean-miri` reports `StepError.undefinedBehavior`!
    have hm_stmt := evalStatement_assign_binOp_offset_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (.copy ⟨ptrIdx, .nil⟩) rhsOp span m
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval : annealEvalPlace body.localDecls body.layouts (translatePlace ⟨dstIdx, .nil⟩) m =
        .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d
              (translateTy dstDecl.ty body.layouts)]⟩ } :=
      annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
      hstate.cache_layout hframes hdecl_dst hlt_d
    have hop_tfa : WellTypedScalarOperand body tfa rhsOp rhsTy :=
      hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ :=
      hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_p_tfa : IsImmediateFrameLocal tfa ptrIdx := by
      intro mls hmls mp hmp
      simp only [tfa, cacheFrameLocalLayout] at hmls
      by_cases hdp : dstIdx = ptrIdx
      · subst hdp
        rw [Array.getElem?_set_self] at hmls
        injection hmls with hm
        rw [← hm] at hmp
        exact himm_dst (tf.locals[dstIdx]'hlt_d) (Array.getElem?_eq_getElem hlt_d) mp hmp
      · rw [Array.getElem?_set_ne _ hdp] at hmls
        exact himm_ptr mls hmls mp hmp
    let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
    have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
      hstate_a.cache_layout rfl hdecl_ptr hlt_pa
    have hop_tfb : WellTypedScalarOperand body tfb rhsOp rhsTy :=
      hop_tfa.of_cacheFrameLocalLayout ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_p.symm.trans hptr_slot)
    rcases hloc_p.rawPtr_immediate_cases hptr_ty (himm_p_tfa mls_p hmls_p) with
      ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, h1, _, _, _⟩ |
      ⟨ptrVal', mptr, hsp_ptr, hptrRel, hmp_ptr⟩
    · rw [hsp_eq] at h1; cases h1
    · rw [hsp_eq] at h1; cases h1
    · rw [hsp_eq] at h1; cases h1
    · rw [hsp_eq] at hsp_ptr
      injection hsp_ptr with hp1
      injection hp1 with hpv_eq
      subst hpv_eq
      have hmls_p' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      have hlhs_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
      rcases evalOperand_scalar_lm3_1_simulation hstate_b rfl hop_tfb hrhs_prim none with
        ⟨_, _, hrhs_ub, _⟩ | ⟨sc', msc, tfc, hrhs_ok, hm_rhs_ok, _, hrel_imm, _⟩
      · rw [hrhs_eval] at hrhs_ub; cases hrhs_ub
      · rw [hrhs_eval] at hrhs_ok
        injection hrhs_ok with hv_eq _
        injection hv_eq with hsc_eq
        subst hsc_eq
        have hsc_rel : ScalarRel sc msc ∧ sc.sizeBytes = 8 := by
          cases hrel_imm with
          | scalar _ _ hrel hsz _ _ =>
            have hlay_rhs : (translateTy rhsTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
              rcases hrhs_ty with hk | hk <;> (unfold translateTy; rw [hk]; rfl)
            rw [hlay_rhs] at hsz
            have hb : (8 : UInt64) = UInt64.ofNat sc.sizeBytes := congrArg Miri.ABI.Size.bytes hsz
            have hcan := hrel.validBytes
            have hsz8 : sc.sizeBytes = 8 := by
              rcases hcan with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb ⊢ <;> first | rfl | cases hb
            exact ⟨hrel, hsz8⟩
        obtain ⟨allocId, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, e', he'_mem, he'_tag, he'_aid⟩ :=
          hptrRel
        subst he'_aid
        have he_eq : e' = e :=
          allocMap_mem_tag_injective halloc.tags_nodup he'_mem he_mem (he'_tag.trans he_tag.symm)
        subst he_eq
        obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e' he'_mem
        have hmptr_opt : mptr.withOptionalProvenance =
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
              some (.concrete e'.allocId borTag)⟩ := by
          rcases mptr with ⟨off, prov⟩
          dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
          subst hprov_eq hmptr_off; rfl
        have hpoff_err : ∃ accErr, Miri.Interpreter.ptrOffsetInbounds annealPointerArithmetic
            mptr.withOptionalProvenance (Int64.ofInt (sc.bits : Int))
            (annealResolvePtr m.machine) (annealLookupAlloc m.machine) =
            .error (.access accErr) := by
          rw [hmptr_opt]
          rcases hbad with ht_dead | hoob
          · have hdead_la := (halloc.local_alloc_sync tf hframes e' he'_mem).2 ht_dead
            exact ⟨_, ptrOffsetInbounds_deadAlloc_err e'.allocId borTag ptrVal.offsetBytes sc.bits
              hid_lt hoff_lt hpos hbits_lt hbase hdead_la⟩
          · by_cases ht_dead : get? s.frame.locals e'.localIdx = some .dead
            · have hdead_la := (halloc.local_alloc_sync tf hframes e' he'_mem).2 ht_dead
              exact ⟨_, ptrOffsetInbounds_deadAlloc_err e'.allocId borTag ptrVal.offsetBytes sc.bits
                hid_lt hoff_lt hpos hbits_lt hbase hdead_la⟩
            · obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
              have ht_ne_dead : slot_t ≠ .dead :=
                fun hd => ht_dead (hslot_t.trans (congrArg some hd))
              obtain ⟨_, _, hsh_t⟩ :=
                (halloc.local_alloc_sync tf hframes e' he'_mem).1 slot_t hslot_t ht_ne_dead
              obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_t tgtDecl hdecl_tgt
              have hoob_la : localAlloc.allocation.byteSize.bytes.toNat <
                  ptrVal.offsetBytes + sc.bits := by
                rw [hshape_la.byteSize_eq]; exact hoob
              exact ⟨_, ptrOffsetInbounds_live_oob_err e'.allocId borTag ptrVal.offsetBytes sc.bits
                localAlloc hid_lt hoff_lt hpos hbits_lt hbase hfind_la hoob_la⟩
        obtain ⟨accErr, hpoff_err⟩ := hpoff_err
        have hbin_err : Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
            ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
              translateTy ptrDecl.ty body.layouts⟩
            ⟨.scalar (.fromScalarInt msc), translateTy rhsTy body.layouts⟩
            { m with stack := ⟨#[tfc]⟩ } =
            .error (.undefinedBehavior "pointer Offset out of bounds")
              { m with stack := ⟨#[tfc]⟩ } := by
          rw [scalarOps_binary_offset_byte_eq body.localDecls body.layouts hptr_ty hpt hrhs_ty,
            annealPointerBinary_byte_eq body.layouts hptr_ty hpt hrhs_ty hsc_rel.1 hsc_rel.2
              hbits_lt mptr { m with stack := ⟨#[tfc]⟩ },
            hpoff_err]
        have htr_lhs : translateOperand (.copy ⟨ptrIdx, .nil⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
        have hread_lhs : annealReadImmediate
            ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
              translateTy ptrDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } =
            .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
              translateTy ptrDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := rfl
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt
              ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
            ({ m with stack := ⟨#[tfc]⟩ },
              .error (.undefinedBehavior "pointer Offset out of bounds")) := by
          rw [hm_stmt, htr_lhs]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
            EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_ok hm_rhs_ok,
            EStateM.bind_eq_error hbin_err]
        exact ⟨_, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
          hm_err⟩

/-! ## 10A. `AllocIdSupplyReady` Preservation & Re-Borrow `&raw` on Promoted Locals -/

namespace AllocIdSupplyReady

/-- Any memory transition that preserves the id-supply cursors, `issuedIds`,
`globals`, and `dead` while keeping all `live` keys below `nextAllocId`
preserves `AllocIdSupplyReady`. -/
theorem of_nonAlloc {mem mem' : AnnealMemory}
    (h : AllocIdSupplyReady mem)
    (havail : mem'.idSupplyExhausted = mem.idSupplyExhausted)
    (hnext : mem'.nextAllocId = mem.nextAllocId)
    (hsrc_act : mem'.sourceAllocIdWorldActive = mem.sourceAllocIdWorldActive)
    (hsrc_exh : mem'.sourceAllocIdExhausted = mem.sourceAllocIdExhausted)
    (hsrc_nxt : mem'.sourceAllocIdNext = mem.sourceAllocIdNext)
    (hissued : mem'.issuedIds = mem.issuedIds)
    (hglobals : mem'.globals = mem.globals)
    (hdead : mem'.dead = mem.dead)
    (hlive : ∀ row ∈ mem'.live, row.1.value.toNat < mem.nextAllocId.toNat) :
    AllocIdSupplyReady mem' where
  available := havail.trans h.available
  nonzero := hnext ▸ h.nonzero
  sourceAvailable hact := hsrc_exh.trans (h.sourceAvailable (hsrc_act.symm.trans hact))
  sourceNonzero hact := hsrc_nxt ▸ h.sourceNonzero (hsrc_act.symm.trans hact)
  issued id hid := hnext ▸ h.issued id (hissued ▸ hid)
  live row hrow := hnext ▸ hlive row hrow
  global row hrow := hnext ▸ h.global row (hglobals ▸ hrow)
  dead row hrow := hnext ▸ h.dead row (hdead ▸ hrow)
  below_2pow32 := hnext ▸ h.below_2pow32

/-- `deallocLocalMemory` (`StorageLive` / `StorageDead`) preserves `AllocIdSupplyReady`. -/
theorem of_deallocLocalMemory {mem : AnnealMemory}
    (h : AllocIdSupplyReady mem)
    (v : Miri.Interpreter.LocalValue AnnealProv) :
    AllocIdSupplyReady (deallocLocalMemory mem v) := by
  cases v with
  | dead => exact h
  | live op =>
    cases op with
    | immediate _ => exact h
    | indirect mp =>
      dsimp only [deallocLocalMemory]
      cases hid : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none => exact h
      | some id =>
        dsimp only []
        refine h.of_nonAlloc rfl rfl rfl rfl rfl rfl rfl rfl ?_
        intro row hrow
        rw [← Array.mem_toList_iff, Array.toList_filter, List.mem_filter] at hrow
        exact h.live row (Array.mem_toList_iff.mp hrow.1)

/-- Updating an existing live allocation (`setLiveAllocation` / deref write)
preserves `AllocIdSupplyReady`. -/
theorem of_setLive {mem : AnnealMemory}
    (h : AllocIdSupplyReady mem)
    {id : Miri.Memory.AllocId}
    (hid_lt : id.value.toNat < mem.nextAllocId.toNat)
    (newLa : Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
      Miri.Memory.MiriMemoryKind) :
    AllocIdSupplyReady
      { mem with live := (mem.live.filter (fun x => x.1 != id)).push (id, newLa) } := by
  refine h.of_nonAlloc rfl rfl rfl rfl rfl rfl rfl rfl ?_
  intro row hrow
  rcases Array.mem_push.mp hrow with hflt | rfl
  · rw [← Array.mem_toList_iff, Array.toList_filter, List.mem_filter] at hflt
    exact h.live row (Array.mem_toList_iff.mp hflt.1)
  · exact hid_lt

/-- Promoting a local into a fresh stack allocation via `reserveAllocId` +
`stackAllocMachine` preserves `AllocIdSupplyReady` whenever `nextAllocId + 1 < 2^32`
(and the optional source-id cursor does not wrap to `0`). -/
theorem of_stackAllocMachine {mach : AnnealMachine} {mem' : AnnealMemory}
    {id : Miri.Memory.AllocId}
    (h : AllocIdSupplyReady mach.memory)
    (hroom : mach.memory.nextAllocId.toNat + 1 < 2 ^ 32)
    (hsrc : mach.memory.sourceAllocIdWorldActive = true →
      mach.memory.sourceAllocIdNext + 1 ≠ 0)
    (hres : mach.memory.reserveAllocId = (mem', .ok id))
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AllocIdSupplyReady (stackAllocMachine mach mem' id alloc).memory ∧
    (stackAllocMachine mach mem' id alloc).memory.nextAllocId = mach.memory.nextAllocId + 1 ∧
    (stackAllocMachine mach mem' id alloc).memory.sourceAllocIdWorldActive =
      mach.memory.sourceAllocIdWorldActive := by
  have hlt64 : mach.memory.nextAllocId.toNat + 1 < 2 ^ 64 := by omega
  have hnext_toNat :
      (mach.memory.nextAllocId + 1).toNat = mach.memory.nextAllocId.toNat + 1 := by
    rw [UInt64.toNat_add, show (1 : UInt64).toNat = 1 from rfl, Nat.mod_eq_of_lt hlt64]
  have hnext_nz : mach.memory.nextAllocId + 1 ≠ 0 := by
    intro hz
    have h0 : (mach.memory.nextAllocId + 1).toNat = 0 := by rw [hz]; rfl
    omega
  unfold Miri.Memory.MemoryState.reserveAllocId at hres
  simp only [Id.run] at hres
  split at hres
  · cases hres
  · split at hres
    · cases hres
    · split at hres
      · cases hres
      · rename_i allocId hof
        split at hres
        · cases hres
        · injection hres with hmem hid
          injection hid with hid_eq
          subst hid_eq hmem
          have hval : allocId.value = mach.memory.nextAllocId := by
            unfold Miri.Memory.AllocId.ofUInt64 at hof
            split at hof
            · cases hof
            · injection hof with heq
              exact (congrArg Miri.Memory.AllocId.value heq).symm
          by_cases hact : mach.memory.sourceAllocIdWorldActive = true
          · dsimp only [stackAllocMachine]
            simp only [hact, ↓reduceIte]
            refine And.intro ?_ ⟨trivial, trivial⟩
            refine ⟨h.available, hnext_nz, fun _ => h.sourceAvailable hact,
              fun _ => hsrc hact, ?_, ?_, ?_, ?_, ?_⟩
            · intro x hx
              dsimp only []
              have hx' : x ∈ mach.memory.issuedIds.push allocId := hx
              rcases Array.mem_push.mp hx' with hm | rfl
              · have := h.issued x hm; rw [hnext_toNat]; omega
              · rw [hval, hnext_toNat]; omega
            · intro row hrow
              dsimp only [] at hrow ⊢
              rcases Array.mem_push.mp hrow with hm | rfl
              · have := h.live row hm; rw [hnext_toNat]; omega
              · rw [hval, hnext_toNat]; omega
            · intro row hrow
              dsimp only [] at hrow ⊢
              have := h.global row hrow; rw [hnext_toNat]; omega
            · intro row hrow
              dsimp only [] at hrow ⊢
              have := h.dead row hrow; rw [hnext_toNat]; omega
            · dsimp only []; rw [hnext_toNat]; exact hroom
          · have hact_f : mach.memory.sourceAllocIdWorldActive = false :=
              Bool.eq_false_iff.mpr hact
            dsimp only [stackAllocMachine]
            simp only [hact_f, Bool.false_eq_true, ↓reduceIte]
            refine And.intro ?_ ⟨trivial, trivial⟩
            refine AllocIdSupplyReady.mk h.available hnext_nz
              (fun h1 => by cases h1) (fun h1 => by cases h1) ?_ ?_ ?_ ?_ ?_
            · intro x hx
              dsimp only []
              have hx' : x ∈ mach.memory.issuedIds.push allocId := hx
              rcases Array.mem_push.mp hx' with hm | rfl
              · have := h.issued x hm; rw [hnext_toNat]; omega
              · rw [hval, hnext_toNat]; omega
            · intro row hrow
              dsimp only [] at hrow ⊢
              rcases Array.mem_push.mp hrow with hm | rfl
              · have := h.live row hm; rw [hnext_toNat]; omega
              · rw [hval, hnext_toNat]; omega
            · intro row hrow
              dsimp only [] at hrow ⊢
              have := h.global row hrow; rw [hnext_toNat]; omega
            · intro row hrow
              dsimp only [] at hrow ⊢
              have := h.dead row hrow; rw [hnext_toNat]; omega
            · dsimp only []; rw [hnext_toNat]; exact hroom

end AllocIdSupplyReady

/-- **`step_rawPtr_addrOf_preserves_supply`**: whenever `_d = &raw (const|mut) _t`
promotes an immediate local `_t` and steps to `(m', .ok ())` with
`nextAllocId.toNat + 1 < 2 ^ 32`, `m'.machine.memory` retains `AllocIdSupplyReady`
with `nextAllocId` incremented by `1`, enabling arbitrarily many chained `&raw`
promotions across distinct locals without re-establishing high-water bounds by hand. -/
theorem step_rawPtr_addrOf_preserves_supply
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hroom : m.machine.memory.nextAllocId.toNat + 1 < 2 ^ 32)
    (hsrc : m.machine.memory.sourceAllocIdWorldActive = true →
      m.machine.memory.sourceAllocIdNext + 1 ≠ 0)
    (hm_step : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true)) :
    (AllocIdSupplyReady m'.machine.memory ∧
      m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId + 1 ∧
      m'.machine.memory.sourceAllocIdWorldActive = m.machine.memory.sourceAllocIdWorldActive) ∧
    (∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, k ≠ targetIdx → IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_tgt⟩ := himm tf hframes
  obtain ⟨_, mls_d, _, hlt_d, _, hmls_d, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRelLM3_1 body m.machine allocMap s.frame tfa :=
    hfr.cache_local_layout hdecl_dst hlt_d
  obtain ⟨_, mls_t, _, hlt_t, _, hmls_t, hmls_t_eq, hloc_t⟩ := hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.cachedLayout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hkind : translateRawPtrKind mutability ≠ .FakeForPtrMetadata := by
    cases mutability <;> decide
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.RawPtr (translateRawPtrKind mutability) ⟨targetIdx, #[]⟩) ⟨dstIdx, #[]⟩) m := rfl
  have hlt_tb : targetIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_t
  have hval_tb : (tfb.locals[targetIdx]'hlt_tb).value = mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  cases hloc_t with
  | rawPtr _ _ _ _ _ _ hty_raw _ =>
    exfalso
    rcases htgt_ty with h | h | ⟨_, h⟩ | ⟨_, h⟩ <;> rw [h] at hty_raw <;> cases hty_raw
  | base hloc_t_b =>
    cases hloc_t_b with
    | indirect _ mp _ _ _ _ =>
      exact absurd rfl (himm_tgt.cache_layout hlt_d _ _ hmls_t mp)
    | dead _ _ =>
      have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
        (m := { m with stack := ⟨#[tfb]⟩ }) rfl hlt_tb hval_tb
        (translateTy targetDecl.ty body.layouts)
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
        rw [hm_stmt]
        unfold Miri.Interpreter.runRvalue
        rw [evalRvalueIntoPlace_rawPtr_force_error hdst_eval htgt_eval hforce]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        at hm_step
      cases hm_step
    | immediate _ imm _ _ hval =>
      have hlay_tb : (tfb.locals[targetIdx]'hlt_tb).layout =
          some (translateTy targetDecl.ty body.layouts) := by
        simp [tfb, cacheFrameLocalLayout]
      obtain ⟨hsized, allocation, htry⟩ := htgt_ty.layout_ok (layouts := body.layouts)
      obtain ⟨_, hshape0⟩ :=
        StackScalarAllocShape.of_tryNew (none : Option Miri.TreeBorrows.BorrowTree) htry
      obtain ⟨mem', hres⟩ := hsupply.reserve_eq
      let freshId : Miri.Memory.AllocId := ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
      obtain ⟨alloc', hfill⟩ :
          ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
            ((imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
              ∃ sc, imm = .scalar sc ∧
                Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                  (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc
                  (allocation.withExtra none) = .ok () alloc') := by
        rcases hval with ⟨_, rfl⟩ | ⟨_, _, himmRel⟩
        · exact ⟨allocation.withExtra none, Or.inl ⟨rfl, rfl⟩⟩
        · obtain ⟨sc, msc, _, rfl, hrel, hsz, _, _⟩ := himmRel.of_primitive_scalar htgt_ty
          obtain ⟨alloc₃, hw₃, _, _, -⟩ :=
            StackScalarAllocShape.writeScalar_readScalar hrel (hsz ▸ hshape0)
          exact ⟨alloc₃, Or.inr ⟨_, rfl, hw₃⟩⟩
      have hforce₀ := forceAllocation_promote_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hdecl_tgt
        hlt_tb hlay_tb hval_tb hsized htry hres hfill
      have hforce : annealForceAllocation body.localDecls body.layouts
          ⟨.local 0 targetIdx none tfa.localsIdentity, translateTy targetDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .ok (stackAllocPlace freshId)
            { stack := ⟨#[{ tfb with
                locals := tfb.locals.set targetIdx
                  { tfb.locals[targetIdx]'hlt_tb with
                    value := .live (.indirect (stackAllocPlace freshId)) } hlt_tb }]⟩
              machine := stackAllocMachine m.machine mem' freshId alloc' } := by
        unfold annealForceAllocation
        erw [hforce₀]
      have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval htgt_eval hforce
        (stackAllocPlace_toRef freshId)
      let tfc : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
        { tfb with
          locals := tfb.locals.set targetIdx
            { tfb.locals[targetIdx]'hlt_tb with
              value := .live (.indirect (stackAllocPlace freshId)) } hlt_tb }
      have hdc_eq : tfc.locals[dstIdx]? =
          some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
        simp only [tfc, tfb, tfa, cacheFrameLocalLayout]
        rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_ne _ (Ne.symm hne),
          Array.getElem?_set_self, hmls_d_eq]
      obtain ⟨hlt_dc, -⟩ := Array.getElem?_eq_some_iff.mp hdc_eq
      have hlive_mach :
          ∀ oldImm, mls_d.value = .live (.immediate oldImm) →
            m'.machine = stackAllocMachine m.machine mem' freshId alloc' ∧
            (∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
              ∀ k, k ≠ targetIdx → IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k) := by
        intro oldImm hmd_imm
        have hdc_imm : tfc.locals[dstIdx]? =
            some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
          rw [hdc_eq]; rcases mls_d with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
        have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
              .concrete freshId Miri.Memory.BorTag.one⟩))
          (m := ⟨⟨#[tfc]⟩, stackAllocMachine m.machine mem' freshId alloc'⟩)
          (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
            m =
            ({ (⟨⟨#[tfc]⟩, stackAllocMachine m.machine mem' freshId alloc'⟩ : AnnealStepState) with
                stack := ⟨#[{ tfc with
                  locals := tfc.locals.set dstIdx
                    { tfc.locals[dstIdx]'hlt_dc with
                      value := .live (.immediate (.scalar
                        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr freshId),
                            .concrete freshId Miri.Memory.BorTag.one⟩))) }
                    hlt_dc }]⟩ },
              .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        have hloc_c : tfc.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfr.location_eq
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
          hloc_c] at hm_step
        injection hm_step with hm_eq _
        subst hm_eq
        refine ⟨rfl, fun tf₀ tf' htf₀ htf' k hk_ne hk mls' hmls' mp hmp => ?_⟩
        rw [hframes] at htf₀
        injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
        injection htf' with h₁; injection h₁ with h₁'; subst h₁'
        dsimp only [] at hmls'
        rw [Array.getElem?_set] at hmls'
        by_cases hdk : dstIdx = k
        · subst hdk
          simp only [↓reduceIte, Option.some.injEq] at hmls'
          rw [← hmls'] at hmp
          cases hmp
        · simp only [hdk, ↓reduceIte, tfc] at hmls'
          rw [Array.getElem?_set_ne _ (Ne.symm hk_ne)] at hmls'
          have hk_b : IsImmediateFrameLocal tfb k :=
            (hk.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout hlt_t
              (translateTy targetDecl.ty body.layouts)
          exact hk_b mls' hmls' mp hmp
      obtain ⟨hmach_eq, himm_pres⟩ :
          m'.machine = stackAllocMachine m.machine mem' freshId alloc' ∧
          (∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
            ∀ k, k ≠ targetIdx → IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k) := by
        cases hloc_d with
        | rawPtr _ _ _ _ _ _ _ _ => exact hlive_mach _ rfl
        | base hloc_d_b =>
          cases hloc_d_b with
          | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst _ hmls_d mp)
          | dead _ _ =>
            have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
            have hm_err : Miri.Interpreter.Step.evalStatement
                (annealStepHooks body.localDecls body.layouts) ()
                (translateStmt
                  ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
                (⟨⟨#[tfc]⟩, stackAllocMachine m.machine mem' freshId alloc'⟩,
                  .error (.undefinedBehavior "write to dead local")) := by
              rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
              rw [hrv, annealWriteImmediate_dead
                (m := ⟨⟨#[tfc]⟩, stackAllocMachine m.machine mem' freshId alloc'⟩) rfl hget_dc]
            rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
              at hm_step
            cases hm_step
          | immediate _ oldImm _ _ _ => exact hlive_mach oldImm rfl
      refine ⟨?_, himm_pres⟩
      rw [hmach_eq]
      exact hsupply.of_stackAllocMachine hroom hsrc hres alloc'

/-- `annealForceAllocation` on an already memory-backed local (`Operand.indirect mp`)
is a pure no-op returning `mp` without reserving a fresh allocation id or
mutating machine memory. -/
theorem annealForceAllocation_indirect_eq
    {ld : List LocalDecl} {ly : LayoutTable} {m : AnnealStepState}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {idx : Nat} (hlt : idx < tf.locals.size)
    {mp : Miri.Interpreter.MemPlace AnnealProv}
    (hind : (tf.locals[idx]'hlt).value = .live (.indirect mp))
    (lay : Miri.Interpreter.LocalLayout) :
    annealForceAllocation ld ly ⟨.local 0 idx none tf.localsIdentity, lay⟩ m =
      .ok mp m := by
  have hgo : tf.getLocalOperand idx = .ok (.indirect mp) := by
    unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
      Miri.Interpreter.LocalState.access
    simp [hlt, hind, bind, Except.bind, pure, Except.pure, Except.mapError]
  unfold annealForceAllocation Miri.Interpreter.forceAllocation
  simp only [Miri.Interpreter.requireCurrent_eq,
    Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
    bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes, bne_self_eq_false,
    Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure, annealPlaceHooks_getFrame_eq hframes,
    hgo, Miri.Interpreter.stackLift_ok]

/-- **`step_rawPtr_addrOf_indirect_lm3_1_simulation`**: re-borrowing an already
address-taken local (`_d = &raw (const|mut) _t` where `e₀ ∈ allocMap` has
`e₀.localIdx = _t`). If `_t` is dead, both machines report UB; if `_t` is live,
`forceAllocation` reuses `e₀.allocId` without touching `reserveAllocId` (so no
`AllocIdSupplyReady` premise is needed), Anneal pushes a fresh borrow tag
`nextTag`, and `allocMap` extends by `(nextTag, _t, e₀.allocId, perm)`. -/
theorem step_rawPtr_addrOf_indirect_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
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
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = targetIdx) :
    StepRelLM3_1 body m
      (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx s.memory.nextTag
        e₀.allocId :: allocMap)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc,
    hdisj⟩ := id hstate
  have himm_d := himm_dst tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRelLM3_1 body m.machine allocMap s.frame tfa :=
    hfr.cache_local_layout hdecl_dst hlt_d
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_t, mls_t, _, hlt_t, hslot_t, _, hmls_t_eq, hloc_t⟩ :=
    hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.cachedLayout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
    hstate_a.cache_layout rfl hdecl_tgt hlt_t
  have hkind : translateRawPtrKind mutability ≠ .FakeForPtrMetadata := by
    cases mutability <;> decide
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.RawPtr (translateRawPtrKind mutability) ⟨targetIdx, #[]⟩) ⟨dstIdx, #[]⟩) m := rfl
  have hlt_tb : targetIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_t
  have hval_tb : (tfb.locals[targetIdx]'hlt_tb).value = mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  by_cases ht_dead : slot_t = .dead
  · subst ht_dead
    have hmls_t_dead : mls_t.value = .dead := by
      cases hloc_t with
      | base hb =>
        cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hne_d _ => exact absurd rfl hne_d
    have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only
      rw [evalRvalue_rawPtr_dead_eq s body.localDecls body.layouts mutability targetIdx hslot_t]
    have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl hlt_tb (hval_tb.trans hmls_t_dead)
      (translateTy targetDecl.ty body.layouts)
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [evalRvalueIntoPlace_rawPtr_force_error hdst_eval htgt_eval hforce]
    rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · obtain ⟨tfb', hfb, -, -, hfrb, -, -, -, -, -, halloc_b, hdisj_b⟩ := hstate_b
    injection hfb with hfb₁
    injection hfb₁ with hfb₂
    subst hfb₂
    obtain ⟨⟨lay_t, hlay_t⟩, _, _⟩ :=
      (halloc_b.local_alloc_sync tfb rfl e₀ he₀).1 slot_t (he₀_loc ▸ hslot_t) ht_dead
    rw [he₀_loc] at hlay_t
    have hval_tb_ind :
        (tfb.locals[targetIdx]'hlt_tb).value = .live (.indirect (stackAllocPlace e₀.allocId)) := by
      have h := Array.getElem?_eq_getElem hlt_tb
      rw [hlay_t] at h
      exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h).symm
    have hforce : annealForceAllocation body.localDecls body.layouts
        ⟨.local 0 targetIdx none tfa.localsIdentity, translateTy targetDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok (stackAllocPlace e₀.allocId) { m with stack := ⟨#[tfb]⟩ } :=
      annealForceAllocation_indirect_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hlt_tb
        hval_tb_ind (translateTy targetDecl.ty body.layouts)
    have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval htgt_eval hforce
      (stackAllocPlace_toRef e₀.allocId)
    have hdb_eq : tfb.locals[dstIdx]? =
        some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
      simp only [tfb, tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_self, hmls_d_eq]
    obtain ⟨hlt_db, -⟩ := Array.getElem?_eq_some_iff.mp hdb_eq
    have hlive_dst_step :
        ∀ oldImm, mls_d.value = .live (.immediate oldImm) → slot_d ≠ .dead →
          StepRelLM3_1 body m
            (rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx
              s.memory.nextTag e₀.allocId :: allocMap)
            (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
              body.localDecls body.layouts)
            (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
      intro oldImm hmls_d_imm hslot_d_ne
      have hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx :=
        hstate.immediate_not_in_allocMap hframes hslot_d hslot_d_ne himm_d
      have hdb_imm : tfb.locals[dstIdx]? =
          some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
        rw [hdb_eq]; rcases mls_d with ⟨v0, l0⟩; dsimp only at hmls_d_imm; subst hmls_d_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
            .concrete e₀.allocId Miri.Memory.BorTag.one⟩))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar
                    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
                        .concrete e₀.allocId Miri.Memory.BorTag.one⟩))) }
                hlt_db }]⟩ },
            .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      have hloc_b : tfb.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := hfrb.location_eq
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hloc_b]
      let newEntry := rawPtrAllocMapEntry body.localDecls body.layouts mutability targetIdx
        s.memory.nextTag e₀.allocId
      have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
          body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s
              (s.frame.locals.set dstIdx
                (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
              { s.memory with
                borrows := newEntry.toBorrowEntry :: s.memory.borrows
                nextTag := s.memory.nextTag + 1 }) := by
        unfold evalStmt; dsimp only
        rw [evalRvalue_rawPtr_live_eq s body.localDecls body.layouts mutability targetIdx slot_t
          hslot_t ht_dead]
        dsimp only; rw [hslot_d]
        have hbeq : Nat.beq targetIdx dstIdx = false := by
          cases h : Nat.beq targetIdx dstIdx
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true h).symm hne
        have hinv_tail := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
        cases slot_d with
        | dead => exact absurd rfl hslot_d_ne
        | uninit =>
          simp only [set?_eq_some_set hlt_af_d, hprot, invalidateConflictingBorrows_cons,
            updateBorrowPerm, hbeq, newEntry, rawPtrAllocMapEntry,
            AllocMapEntry.toBorrowEntry, hinv_tail]
        | init _ =>
          simp only [set?_eq_some_set hlt_af_d, hprot, invalidateConflictingBorrows_cons,
            updateBorrowPerm, hbeq, newEntry, rawPtrAllocMapEntry,
            AllocMapEntry.toBorrowEntry, hinv_tail]
      rw [ha]
      apply StepRelLM3_1.step
      have h32_e0 := (halloc_b.base_addr_valid e₀ he₀).1
      have hptr := PtrRel.of_stackAllocPlace
        (allocMap := newEntry :: allocMap) (e := newEntry)
        (List.Mem.head allocMap) h32_e0
      have hdb' : tfb.locals[dstIdx]'hlt_db =
          ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ :=
        Option.some.inj ((Array.getElem?_eq_getElem hlt_db).symm.trans hdb_imm)
      have hnew : LocalRelLM3_1 m.machine (newEntry :: allocMap) dstDecl body.layouts
          (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
          { tfb.locals[dstIdx]'hlt_db with
            value := .live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
                  .concrete e₀.allocId Miri.Memory.BorTag.one⟩))) } := by
        rw [hdb']
        exact .rawPtr _ _ _ mutability pointeeKind (fun l hl => (Option.some.inj hl).symm)
          hdst_ty hptr
      have hfrd := (hfrb.mono_cons newEntry).update_local hdecl_dst _ _ hnew
      have hnodup_new : ((newEntry :: allocMap).map AllocMapEntry.tag).Nodup := by
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, halloc_b.tags_nodup⟩
        intro hmem
        obtain ⟨e, he, htag_eq⟩ := List.mem_map.mp hmem
        have hlt_tag := (halloc_b.borrow_sync e he).1
        dsimp only [newEntry, rawPtrAllocMapEntry] at htag_eq
        omega
      refine .mk _ rfl hretCont hretPlace hfrd.advance hcal hstack hprot hcaller
        (by simp [advanceStmt, hbor, newEntry]) ?_ ?_
      · refine ⟨hnodup_new, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro e₁ h₁ e₂ h₂ hloc_eq
          rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
            rcases List.mem_cons.mp h₂ with rfl | hm₂
          · rfl
          · exact halloc_b.local_to_alloc_unique e₀ he₀ e₂ hm₂ (he₀_loc.trans hloc_eq)
          · exact halloc_b.local_to_alloc_unique e₁ hm₁ e₀ he₀ (hloc_eq.trans he₀_loc.symm)
          · exact halloc_b.local_to_alloc_unique e₁ hm₁ e₂ hm₂ hloc_eq
        · intro e₁ h₁ e₂ h₂ hid_eq
          rcases List.mem_cons.mp h₁ with rfl | hm₁ <;>
            rcases List.mem_cons.mp h₂ with rfl | hm₂
          · rfl
          · exact he₀_loc.symm.trans (halloc_b.alloc_to_local_injective e₀ he₀ e₂ hm₂ hid_eq)
          · exact (halloc_b.alloc_to_local_injective e₁ hm₁ e₀ he₀ hid_eq).trans he₀_loc
          · exact halloc_b.alloc_to_local_injective e₁ hm₁ e₂ hm₂ hid_eq
        · intro e he
          rcases List.mem_cons.mp he with rfl | hm
          · exact ⟨targetDecl, hdecl_tgt, htgt_ty⟩
          · exact halloc_b.target_decl e hm
        · intro e he
          rcases List.mem_cons.mp he with rfl | hm
          · exact halloc_b.base_addr_valid e₀ he₀
          · exact halloc_b.base_addr_valid e hm
        · intro e he
          have hlook_all := lookupBorrow_map_toBorrowEntry_of_nodup hnodup_new he
          rcases List.mem_cons.mp he with rfl | hm
          · exact ⟨Nat.lt_succ_self _,
              by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
          · exact ⟨Nat.lt_trans (halloc_b.borrow_sync e hm).1 (Nat.lt_succ_self _),
              by simpa [advanceStmt, hbor, AllocMapEntry.toBorrowEntry] using hlook_all⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | hm
          · exact halloc_b.live_key_unique e₀ he₀
          · exact halloc_b.live_key_unique e hm
        · intro topFrame htop e he
          injection htop with h₁
          injection h₁ with h₂
          subst h₂
          have he_mem_or : ∃ e_orig ∈ allocMap,
              e.localIdx = e_orig.localIdx ∧ e.allocId = e_orig.allocId := by
            rcases List.mem_cons.mp he with rfl | hm
            · exact ⟨e₀, he₀, he₀_loc.symm, rfl⟩
            · exact ⟨e, hm, rfl, rfl⟩
          obtain ⟨e_orig, he_orig, heloc, heaid⟩ := he_mem_or
          rw [heloc, heaid]
          have hne_d : dstIdx ≠ e_orig.localIdx := Ne.symm (hnot_dst e_orig he_orig)
          obtain ⟨hlive_e, hdead_e⟩ := halloc_b.local_alloc_sync tfb rfl e_orig he_orig
          have hslot_after :
              get? (advanceStmt s
                (s.frame.locals.set dstIdx
                  (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)))
                { s.memory with
                  borrows := newEntry.toBorrowEntry :: s.memory.borrows
                  nextTag := s.memory.nextTag + 1 }).frame.locals e_orig.localIdx =
              get? s.frame.locals e_orig.localIdx := by
            dsimp only [advanceStmt]
            rw [get?_eq_getElem?, List.getElem?_set_ne hne_d, ← get?_eq_getElem?]
          refine ⟨fun slot hslot hne_dead => ?_, fun hdead => ?_⟩
          · rw [hslot_after] at hslot
            obtain ⟨⟨lay_e, hlay_e⟩, hsc_e, hshape_e⟩ := hlive_e slot hslot hne_dead
            refine ⟨⟨lay_e, ?_⟩, hsc_e, hshape_e⟩
            show (tfb.locals.set dstIdx _ hlt_db)[e_orig.localIdx]? = _
            rw [Array.getElem?_set_ne _ hne_d]
            exact hlay_e
          · rw [hslot_after] at hdead
            exact hdead_e hdead
      · apply MemoryAllocDisjoint.mono_immediate hdisj_b
        intro k
        by_cases hk : k = dstIdx
        · subst hk
          right
          refine ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
                .concrete e₀.allocId Miri.Memory.BorTag.one⟩),
            some (translateTy dstDecl.ty body.layouts), ?_⟩
          show (tfb.locals.set k _ hlt_db)[k]? = _
          rw [Array.getElem?_set_self, hdb']
        · left
          show (tfb.locals.set dstIdx _ hlt_db)[k]? = _
          rw [Array.getElem?_set_ne _ (Ne.symm hk)]
    cases hloc_d with
    | rawPtr _ _ _ _ _ _ _ _ => exact hlive_dst_step _ rfl (by simp)
    | base hloc_d_b =>
      cases hloc_d_b with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d _ hmls_d mp)
      | dead _ _ =>
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_eq
        have ha : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only
          rw [evalRvalue_rawPtr_live_eq s body.localDecls body.layouts mutability targetIdx slot_t
            hslot_t ht_dead]
          dsimp only; rw [hslot_d]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
            m =
            ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [hrv, annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ }) rfl hget_db]
        rw [ha, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
        exact .ub _ _
      | immediate _ oldImm _ _ hvald =>
        have hslot_d_ne : slot_d ≠ .dead := by
          rcases hvald with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp
        exact hlive_dst_step oldImm rfl hslot_d_ne

/-- On a successful re-borrow `_d = &raw (const|mut) _t` of an already-promoted
local (`e₀.localIdx = _t`), `m'.machine = m.machine` (neither `nextAllocId` nor
`addresses` changes) and every local `k` that was immediate in `m` remains
immediate in `m'`. -/
theorem step_rawPtr_addrOf_indirect_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (hne : dstIdx ≠ targetIdx)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx)
    {e₀ : AllocMapEntry} (he₀ : e₀ ∈ allocMap) (he₀_loc : e₀.localIdx = targetIdx)
    (hm_step : Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
      (m', .ok true)) :
    m'.machine = m.machine ∧
    (∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  obtain ⟨_, mls_d, _, hlt_d, _, hmls_d, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRelLM3_1 body m.machine allocMap s.frame tfa :=
    hfr.cache_local_layout hdecl_dst hlt_d
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_t, mls_t, _, hlt_t, hslot_t, _, hmls_t_eq, hloc_t⟩ := hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.cachedLayout_eq
  have htgt_eval := annealEvalPlace_unprojected (m := { m with stack := ⟨#[tfa]⟩ }) rfl hlt_t
    hdecl_tgt hcache_t
  let tfb := cacheFrameLocalLayout tfa targetIdx hlt_t (translateTy targetDecl.ty body.layouts)
  have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
    hstate_a.cache_layout rfl hdecl_tgt hlt_t
  have hlt_tb : targetIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_t
  have hkind : translateRawPtrKind mutability ≠ .FakeForPtrMetadata := by
    cases mutability <;> decide
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.RawPtr (translateRawPtrKind mutability) ⟨targetIdx, #[]⟩) ⟨dstIdx, #[]⟩) m := rfl
  by_cases ht_dead : slot_t = .dead
  · subst ht_dead
    have hm_t_dead : mls_t.value = .dead := by
      cases hloc_t with
      | base hb => cases hb with
        | dead _ _ => rfl
        | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
        | indirect _ _ _ _ hnd _ => exact absurd rfl hnd
    have hval_tb : (tfb.locals[targetIdx]'hlt_tb).value = .dead := by
      simp [tfb, cacheFrameLocalLayout, hmls_t_eq, hm_t_dead]
    have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl hlt_tb hval_tb
      (translateTy targetDecl.ty body.layouts)
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [evalRvalueIntoPlace_rawPtr_force_error hdst_eval htgt_eval hforce]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
      at hm_step
    cases hm_step
  · obtain ⟨tfb', hfb, -, -, hfrb, -, -, -, -, -, halloc_b, _⟩ := hstate_b
    injection hfb with hfb₁; injection hfb₁ with hfb₂; subst hfb₂
    obtain ⟨⟨lay_t, hlay_t⟩, _, _⟩ :=
      (halloc_b.local_alloc_sync tfb rfl e₀ he₀).1 slot_t (he₀_loc ▸ hslot_t) ht_dead
    rw [he₀_loc] at hlay_t
    have hval_tb_ind :
        (tfb.locals[targetIdx]'hlt_tb).value = .live (.indirect (stackAllocPlace e₀.allocId)) := by
      have h := Array.getElem?_eq_getElem hlt_tb
      rw [hlay_t] at h
      exact congrArg Miri.Interpreter.LocalState.value (Option.some.inj h).symm
    have hforce := annealForceAllocation_indirect_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl hlt_tb hval_tb_ind
      (translateTy targetDecl.ty body.layouts)
    have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval htgt_eval hforce
      (stackAllocPlace_toRef e₀.allocId)
    have hdb_eq : tfb.locals[dstIdx]? =
        some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
      simp only [tfb, tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_self, hmls_d_eq]
    obtain ⟨hlt_db, -⟩ := Array.getElem?_eq_some_iff.mp hdb_eq
    have hlive_d : ∀ oldImm, mls_d.value = .live (.immediate oldImm) →
        m'.machine = m.machine ∧
        (∀ tf₀ tf', m.stack.frames = #[tf₀] → m'.stack.frames = #[tf'] →
          ∀ k, IsImmediateFrameLocal tf₀ k → IsImmediateFrameLocal tf' k) := by
      intro oldImm hmd_imm
      have hdb_imm : tfb.locals[dstIdx]? =
          some ⟨.live (.immediate oldImm), some (translateTy dstDecl.ty body.layouts)⟩ := by
        rw [hdb_eq]; rcases mls_d with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
            .concrete e₀.allocId Miri.Memory.BorTag.one⟩))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar
                    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e₀.allocId),
                        .concrete e₀.allocId Miri.Memory.BorTag.one⟩))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfrb.location_eq] at hm_step
      injection hm_step with hm_eq _
      subst hm_eq
      refine ⟨rfl, fun tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp => ?_⟩
      rw [hframes] at htf₀
      injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
      injection htf' with h₁; injection h₁ with h₁'; subst h₁'
      dsimp only [] at hmls'
      rw [Array.getElem?_set] at hmls'
      by_cases hdk : dstIdx = k
      · subst hdk
        simp only [↓reduceIte, Option.some.injEq] at hmls'
        rw [← hmls'] at hmp
        cases hmp
      · simp only [hdk, ↓reduceIte] at hmls'
        exact ((hk.cache_layout hlt_d _).cache_layout hlt_t _) mls' hmls' mp hmp
    cases hloc_d with
    | rawPtr _ _ _ _ _ _ _ _ => exact hlive_d _ rfl
    | base hb => cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d _ hmls_d mp)
      | dead _ _ =>
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_eq
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
            m =
            ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [hrv, annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ }) rfl hget_db]
        rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
          at hm_step
        cases hm_step
      | immediate _ oldImm _ _ _ => exact hlive_d oldImm rfl

/-- `annealWriteImmediate` to a memory-backed local (`Operand.indirect mplace`)
delegates directly to `annealWriteMemoryPlace`. -/
theorem annealWriteImmediate_indirect
    {m : AnnealStepState}
    {topFrame : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {dstIdx : Nat} {val : Miri.Interpreter.Immediate AnnealProv}
    {mplace : Miri.Interpreter.MemPlace AnnealProv}
    {lay : Option Miri.Interpreter.LocalLayout}
    {dstLay : Miri.Interpreter.LocalLayout}
    {id0 : Miri.Interpreter.LocalsIdentity}
    (hframes : m.stack.frames = #[topFrame])
    (hget : topFrame.getLocal dstIdx = .ok ⟨.live (.indirect mplace), lay⟩) :
    annealWriteImmediate val ⟨.local 0 dstIdx none id0, dstLay⟩ m =
      annealWriteMemoryPlace val mplace dstLay m := by
  have hgop := frame_getLocalOperand_live topFrame hget
  with_unfolding_all
    unfold annealWriteImmediate
    simp only [get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind,
      stack_currentFrame?_singleton m.stack topFrame hframes, hframes, hgop]
    rfl

/-- **`step_nop_lm3_1_simulation`**: `StatementKind.nop` steps in lockstep from
any `StateRelLM3_1`-related state without modifying `allocMap`. -/
theorem step_nop_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.nop, span⟩) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have ha : evalStmt s ⟨.nop, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) := rfl
  have hm : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt ⟨.nop, span⟩) m =
      (m, .ok ()) := rfl
  rw [ha, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm hframes
    hfr.location_eq]
  apply StepRelLM3_1.step
  refine .mk _ rfl hretCont hretPlace hfr.advance hcal hstack hprot hcaller hbor ?_ hdisj
  refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
    halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
  intro tf' htf' e he
  injection htf' with h1
  injection h1 with h2
  subst h2
  exact halloc.local_alloc_sync tf hframes e he

/-- **`step_scalar_use_lm3_1_simulation`**: scalar assignment `_d = .use op`
into an immediate primitive-scalar local `_d` from any `StateRelLM3_1`-related
state (including non-empty `allocMap` with live raw pointers and promoted stack
allocations) steps in lockstep preserving `allocMap` (or reports UB in both
machines if `op` or `_d` is dead/uninitialized). -/
theorem step_scalar_use_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (himm_dst : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, hstack, hprot, hcaller, hbor, _, _⟩ := id hstate
  have himm_d := himm_dst tf hframes
  have hop_tf := hop tf hframes
  have hval_prim : IsPrimScalarTy valTy := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind.trans hk)
    · exact Or.inr (Or.inl (hval_kind.trans hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind.trans hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind.trans hk⟩))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts ⟨dstIdx, .nil⟩ op span m
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval : annealEvalPlace body.localDecls body.layouts (translatePlace ⟨dstIdx, .nil⟩) m =
      .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d
            (translateTy dstDecl.ty body.layouts)]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa : WellTypedScalarOperand body tfa op valTy :=
    hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  rcases evalOperand_scalar_lm3_1_simulation hstate_a rfl hop_tfa hval_prim
      (some (translateTy dstDecl.ty body.layouts)) with
    ⟨m_op, msg_op, hop_ub, hm_op_ub⟩ |
    ⟨sc, msc, tf', hop_ok, hm_op_ok, hstate_tf', himm_sc, hloc_id_tf', htf'_preserve⟩
  · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
        (m_op, .error (.undefinedBehavior msg_op)) := by
      rw [hm_stmt]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]
      dsimp only []
      rw [estate_bind_assoc, EStateM.bind_eq_error hm_op_ub]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · have himm_dst_rel : ImmediateRel dstDecl.ty body.layouts (.scalar sc)
        (.scalar (.fromScalarInt msc)) :=
      himm_sc.of_ty_kind_eq hval_prim hval_kind
    have hfr_tf' := hstate_tf'.frame_rel_singleton rfl
    obtain ⟨_, mls_dc, _, hlt_dc, _, hmls_dc, hmls_dc_eq, hloc_dc⟩ :=
      hfr_tf'.lookup_local hdecl_dst
    have hd_tfa : (tfa.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some mls_d.value := by
      simp [tfa, cacheFrameLocalLayout, Array.getElem?_set_self, hmls_d_eq]
    have hd_Val : mls_dc.value = mls_d.value := by
      have hp := htf'_preserve dstIdx
      rw [hd_tfa, hmls_dc] at hp
      injection hp
    have hnot_ind_d := himm_d mls_d hmls_d
    cases hloc_d with
    | rawPtr _ _ _ _ _ _ hty_raw _ =>
      exfalso
      rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty_raw <;> cases hty_raw
    | base hloc_d_b =>
      cases hloc_d_b with
      | indirect _ mp _ _ _ _ => exact absurd rfl (hnot_ind_d mp)
      | dead _ _ =>
        have hdc_dead : tf'.locals[dstIdx]? = some ⟨.dead, mls_dc.layout⟩ := by
          rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val]
        have hget_dc := frame_getLocal_of_getElem? tf' dstIdx _ hdc_dead
        have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts = MirStepNode.fail .ub := by
          unfold evalStmt; dsimp only []
          rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
          dsimp only []; rw [hslot_d]
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval]
          dsimp only []
          rw [estate_bind_assoc, EStateM.bind_eq_ok hm_op_ok,
            annealWriteImmediate_dead (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
              rfl hget_dc]
        rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
          hm_err]
        exact .ub _ _
      | immediate _ oldImm _ _ hvald =>
        have hsd_ne : slot_d ≠ .dead := by
          rcases hvald with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp
        have hnot_dst : ∀ e ∈ allocMap, e.localIdx ≠ dstIdx :=
          hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_d
        have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
        have hdc_live : tf'.locals[dstIdx]? =
            some ⟨.live (.immediate oldImm), mls_dc.layout⟩ := by
          rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val]
        have hget_dc := frame_getLocal_of_getElem? tf' dstIdx _ hdc_live
        have hw_ok := annealWriteImmediate_live
          (val := .scalar (.fromScalarInt msc))
          (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩) m =
            ({ m with stack := ⟨#[{ tf' with
                locals := tf'.locals.set dstIdx
                  { tf'.locals[dstIdx]'hlt_dc with
                    value := .live (.immediate (.scalar (.fromScalarInt msc))) }
                  hlt_dc }]⟩ },
              .ok ()) := by
          rw [hm_stmt]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval]
          dsimp only []
          rw [estate_bind_assoc, EStateM.bind_eq_ok hm_op_ok, hw_ok]
        rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
          hfr_tf'.location_eq]
        have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
            body.localDecls body.layouts =
            MirStepNode.step
              (advanceStmt s (s.frame.locals.set dstIdx (.init (.scalar sc))) s.memory) := by
          unfold evalStmt; dsimp only []
          rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
          dsimp only []; rw [hslot_d]
          cases slot_d with
          | dead => exact absurd rfl hsd_ne
          | uninit =>
            simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
            congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
          | init _ =>
            simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
            congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
        rw [ha_ok]
        refine .step _ _ ?_
        have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts
            (.init (.scalar sc))
            { tf'.locals[dstIdx]'hlt_dc with
              value := .live (.immediate (.scalar (.fromScalarInt msc))) } := by
          rw [List.map_id]
          exact .base (.immediate (.init (.scalar sc)) (.scalar (.fromScalarInt msc)) _
            (by rw [hmls_dc_eq]; exact hloc_dc.cachedLayout_eq)
            (Or.inr ⟨_, rfl, himm_dst_rel⟩))
        have hval_dc : (tf'.locals[dstIdx]'hlt_dc).value = .live (.immediate oldImm) := by
          rw [hmls_dc_eq, hd_Val]
        have hstep_rel := hstate_tf'.advance_write_immediate_perm_map rfl id
          (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
          hdecl_dst hnot_dst hval_dc hnew_d
          hcal hstack hprot hcaller (by rw [List.map_id]; exact hbor) rfl
        rw [List.map_id] at hstep_rel
        exact hstep_rel

/-- **`step_direct_write_promoted_lm3_1_simulation`**: direct scalar assignment
`_d = .use op` into an address-taken / promoted primitive-scalar local `_d`
(`∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx`) from any `StateRelLM3_1`-related state
steps in lockstep under `Miri.Interpreter.Step.step` (`annealStepHooks`) and
Anneal's `stepMirFn`, overwriting `_d`'s backing stack allocation in `lean-miri`,
invalidating conflicting Tree Borrows permissions in Anneal (`updateAllocMapOnWrite
allocMap dstIdx none`), and reporting UB in both machines if `op` or `_d` is dead. -/
theorem step_direct_write_promoted_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩)
    {dstDecl : LocalDecl} {valTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hval_kind : valTy.kind = dstDecl.ty.kind)
    (hop : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame op valTy)
    (hmem_dst : ∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx) :
    StepRelLM3_1 body m (updateAllocMapOnWrite allocMap dstIdx none)
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨e₀, he₀, he₀_loc⟩ := hmem_dst
  cases he₀_loc
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, hbor, _, _⟩ := id hstate
  have hop_tf := hop tf hframes
  have hval_prim : IsPrimScalarTy valTy := by
    rcases hdst_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
    · exact Or.inl (hval_kind.trans hk)
    · exact Or.inr (Or.inl (hval_kind.trans hk))
    · exact Or.inr (Or.inr (Or.inl ⟨it, hval_kind.trans hk⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨ut, hval_kind.trans hk⟩))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨e₀.localIdx, .nil⟩ op span m
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[e₀.localIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval : annealEvalPlace body.localDecls body.layouts
      (translatePlace ⟨e₀.localIdx, .nil⟩) m =
      .ok ⟨.local 0 e₀.localIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf e₀.localIdx hlt_d
            (translateTy dstDecl.ty body.layouts)]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf e₀.localIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa : WellTypedScalarOperand body tfa op valTy :=
    hop_tf.of_cacheFrameLocalLayout e₀.localIdx hlt_d (translateTy dstDecl.ty body.layouts)
  rcases evalOperand_scalar_lm3_1_simulation hstate_a rfl hop_tfa hval_prim
      (some (translateTy dstDecl.ty body.layouts)) with
    ⟨m_op, msg_op, hop_ub, hm_op_ub⟩ |
    ⟨sc, msc, tf', hop_ok, hm_op_ok, hstate_tf', himm_sc, _, htf'_preserve⟩
  · have ha_ub : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ub]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩) m =
        (m_op, .error (.undefinedBehavior msg_op)) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
      rw [estate_bind_assoc, EStateM.bind_eq_error hm_op_ub]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · obtain ⟨tf₀', hframes_tf', _, _, hfr_tf', _, _, _, _, _, halloc_tf', _⟩ := id hstate_tf'
    injection hframes_tf' with h₁
    injection h₁ with htf'
    subst htf'
    obtain ⟨_, mls_dc, _, _, _, hmls_dc, _, _⟩ := hfr_tf'.lookup_local hdecl_dst
    have hd_tfa : (tfa.locals[e₀.localIdx]?).map Miri.Interpreter.LocalState.value =
        some mls_d.value := by
      simp [tfa, cacheFrameLocalLayout, Array.getElem?_set_self, hmls_d_eq]
    have hd_Val : mls_dc.value = mls_d.value := by
      have hp := htf'_preserve e₀.localIdx
      rw [hd_tfa, hmls_dc] at hp
      injection hp
    by_cases hsd_dead : slot_d = .dead
    · subst hsd_dead
      have hmd_dead : mls_d.value = .dead := by
        cases hloc_d with
        | base hb =>
          cases hb with
          | dead _ _ => rfl
          | immediate _ _ _ _ hv => rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
          | indirect _ _ _ _ hne _ => exact absurd rfl hne
      have hdc_dead : tf'.locals[e₀.localIdx]? = some ⟨.dead, mls_dc.layout⟩ := by
        rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val, hmd_dead]
      have hget_dc := frame_getLocal_of_getElem? tf' e₀.localIdx _ hdc_dead
      have ha_ub : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only []
        rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
        dsimp only []; rw [hslot_d]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩) m =
          ({ m with stack := ⟨#[tf']⟩ }, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        rw [estate_bind_assoc, EStateM.bind_eq_ok hm_op_ok,
          annealWriteImmediate_dead (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
            rfl hget_dc]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · obtain ⟨⟨lay_e, hlay_e⟩, _, hsh_e⟩ :=
        (halloc_tf'.local_alloc_sync tf' rfl e₀ he₀).1 slot_d hslot_d hsd_dead
      obtain ⟨localAlloc, hfind_la, hkind_la, halign_la, hshape_la⟩ := hsh_e dstDecl hdecl_dst
      obtain ⟨hid_lt, _, hbase_e⟩ := halloc_tf'.base_addr_valid e₀ he₀
      obtain ⟨sc', msc', hsc_eq, hmsc_eq, hrel_sc, hsz_sc, hbool_val, hchar_val⟩ :=
        (himm_sc.of_ty_kind_eq hval_prim hval_kind).of_primitive_scalar hdst_prim
      injection hsc_eq with hsc'; subst hsc'
      have hmsc' : msc = msc' := by
        injection hmsc_eq with h1
        unfold Miri.Memory.Scalar.fromScalarInt at h1
        injection h1 with h2
        injection h2 with h3
      subst hmsc'
      have hshape_sc : StackScalarAllocShape (translateSizeBytes sc.sizeBytes)
          localAlloc.allocation := hsz_sc ▸ hshape_la
      obtain ⟨alloc', hw_alloc, halign_alloc', hshape_alloc', hinit_alloc', hread_alloc'⟩ :=
        hshape_sc.writeScalar_readScalar hrel_sc
      have hmsc_sz : msc.size = (translateTy dstDecl.ty body.layouts).layout.size := by
        rw [hrel_sc.size_eq, ← hsz_sc]
      have hw_alloc_lay : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO
            (translateTy dstDecl.ty body.layouts).layout.size)
          (.fromScalarInt msc) localAlloc.allocation = .ok () alloc' := by
        rw [← hmsc_sz]; exact hw_alloc
      have hval_sc : annealValidateScalarForTyId (translateTy dstDecl.ty body.layouts).ty
          (.fromScalarInt msc) = true :=
        annealValidateScalarForTyId_of_scalarRel hdst_prim hrel_sc hbool_val hchar_val
      have hget_dc := frame_getLocal_of_getElem? tf' e₀.localIdx _ hlay_e
      have hw_ind := annealWriteImmediate_indirect
        (val := .scalar (.fromScalarInt msc))
        (m := { m with stack := ⟨#[tf']⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hget_dc
      have hw_m := annealWriteMemoryPlace_zero_offset_scalar_ok hdst_prim hid_lt hbase_e hfind_la
        hshape_la.mutability_eq hshape_la.byteSize_eq hmsc_sz hval_sc hw_alloc_lay
        (borTag := Miri.Memory.BorTag.one) (st := { m with stack := ⟨#[tf']⟩ })
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩) m =
          ({ stack := ⟨#[tf']⟩
             machine := { m.machine with
               memory := { m.machine.memory with
                 live := (m.machine.memory.live.filter (fun x => x.1 != e₀.allocId)).push
                   (e₀.allocId, ⟨localAlloc.kind, alloc'⟩) } } }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; dsimp only []
        rw [estate_bind_assoc, EStateM.bind_eq_ok hm_op_ok, hw_ind, stackAllocPlace, hw_m]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr_tf'.location_eq]
      have ha_ok : evalStmt s ⟨.assign ⟨e₀.localIdx, .nil⟩ (.use op), span⟩
          body.localDecls body.layouts =
          MirStepNode.step
            (advanceStmt s (s.frame.locals.set e₀.localIdx (.init (.scalar sc)))
              { s.memory with
                borrows := (updateAllocMapOnWrite allocMap e₀.localIdx none).map
                  AllocMapEntry.toBorrowEntry }) := by
        unfold evalStmt; dsimp only []
        rw [evalRvalue_use_scalarOperand_eq hop_tf, hop_ok]
        dsimp only []; rw [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_dead
        | uninit =>
          simp only [set?_eq_some_set hlt_af_d, hprot, hbor,
            invalidateConflictingBorrows_map_toBorrowEntry]
        | init _ =>
          simp only [set?_eq_some_set hlt_af_d, hprot, hbor,
            invalidateConflictingBorrows_map_toBorrowEntry]
      rw [ha_ok]
      apply StepRelLM3_1.step
      exact hstate_tf'.advance_write_deref_scalar rfl
        (fun x => x.updateOnWrite e₀.localIdx none)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
        he₀ hdecl_dst hdst_prim hslot_d hsd_dead hfind_la hkind_la halign_la
        hrel_sc hsz_sc hbool_val hchar_val halign_alloc' hshape_alloc' hinit_alloc' hread_alloc'

/-- **`step_placeMention_local_lm3_1_simulation`**: `PlaceMention(_x)` on a live
unprojected local `_x` (`get? s.frame.locals loc ≠ some .dead`) steps in
lockstep from any `StateRelLM3_1`-related state, memoizing `_x`'s layout in
`lean-miri` without altering `allocMap` or any local value. -/
theorem step_placeMention_local_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention ⟨loc, .nil⟩, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hlive : get? s.frame.locals loc ≠ some .dead) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨slot, mls, _, hlt_mf, hslot, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hslot_ne : slot ≠ .dead := fun hd => hlive (hslot.trans (congrArg some hd))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have ha : evalStmt s ⟨.placeMention ⟨loc, .nil⟩, span⟩ body.localDecls body.layouts =
      MirStepNode.step (advanceStmt s s.frame.locals) := by
    unfold evalStmt; dsimp only []; rw [hslot]
    cases slot with
    | dead => exact absurd rfl hslot_ne
    | uninit => rfl
    | init _ => rfl
  have hcache : ∀ l, (tf.locals[loc]'hlt_mf).layout = some l →
      l = translateTy decl.ty body.layouts := by
    rw [hmls_eq]; exact hloc.cachedLayout_eq
  have hm := evalStatement_placeMention_eq (span := span) hframes hlt_mf hdecl hcache
  have hstate' := hstate.cache_layout hframes hdecl hlt_mf
  rcases hstate' with
    ⟨tfa, hframes_a, hretCont, hretPlace, hfra, _, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  injection hframes_a with h1; injection h1 with h2; subst tfa
  rw [ha, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfra.location_eq]
  apply StepRelLM3_1.step
  refine .mk _ rfl hretCont hretPlace hfra.advance hcal hstack hprot hcaller hbor ?_ hdisj
  refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
    halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
  intro tf' htf' e he
  injection htf' with h3; injection h3 with h4; subst tf'
  exact halloc.local_alloc_sync _ rfl e he

/-- **`step_placeMention_deref_lm3_1_simulation`**: `PlaceMention(*_p)` on an
immediate raw-pointer local `_p : *(const|mut) T` (with primitive-scalar `T` and
`get? s.frame.locals ptrIdx ≠ some .uninit`) steps in lockstep across
`StateRelLM3_1`:

* when `_p` is `.dead`, both machines report undefined behavior
  (`StepRelLM3_1.ub`);
* when `_p` is `.init` (including null, provenance-less, dangling,
  out-of-bounds, or misaligned raw pointers), both machines step normally
  without reading pointee memory (`let _ = *ptr;` in unsafe Rust). -/
theorem step_placeMention_deref_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hnot_uninit : get? s.frame.locals ptrIdx ≠ some .uninit) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_p := himm_ptr tf hframes
  obtain ⟨slot_p, mls_p, _, hlt_p, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ := hfr.lookup_local hdecl_ptr
  have hnot_ind : ∀ mp, mls_p.value ≠ .live (.indirect mp) := himm_p mls_p hmls_p
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_eq : ∀ pOut stOut,
      annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m = .ok pOut stOut →
      Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩) m = (stOut, .ok ()) := by
    intro pOut stOut hp
    unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
    dsimp only [Miri.Interpreter.runRvalue]
    rw [hp]; rfl
  rcases hloc_p.rawPtr_immediate_cases hptr_ty hnot_ind with
    ⟨rfl, hmp_dead⟩ | ⟨rfl, _⟩ |
    ⟨sc, msc, rfl, hsz8, hrel_sc, hmp_sc⟩ |
    ⟨ptrVal, mptr, rfl, _, hmp_ptr⟩
  · have hmls_dead : tf.locals[ptrIdx]'hlt_p = ⟨.dead, mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_dead; subst hmp_dead; rfl
    have hdead_ev := annealEvalPlace_deref_dead hframes hlt_p hdecl_ptr hmls_dead hcache_p
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩) m =
        ({ m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt_p
            (translateTy ptrDecl.ty body.layouts)]⟩ },
          .error (.undefinedBehavior "read of dead local")) := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
      dsimp only [Miri.Interpreter.runRvalue]; rw [hdead_ev]; rfl
    have ha_err : evalStmt s ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [hslot_p]
    rw [ha_err, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact StepRelLM3_1.ub _ _
  · exact absurd hslot_p hnot_uninit
  · have hmls_sc : tf.locals[ptrIdx]'hlt_p =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_sc; subst hmp_sc; rfl
    have hlive_ev := annealEvalPlace_deref_live hframes hlt_p hdecl_ptr hmls_sc hcache_p
    obtain ⟨mismatch, hder_sc⟩ := annealDerefOperandToMemPlace_scalarInt hdecl_ptr hptr_ty
      hpk_prim hrel_sc hsz8 (translateTy ptrDecl.ty body.layouts)
      { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt_p
          (translateTy ptrDecl.ty body.layouts)]⟩ }
    have hp_ok : annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
        .ok ⟨.memory ⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits), .none,
            mismatch⟩, translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
          { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt_p
              (translateTy ptrDecl.ty body.layouts)]⟩ } := by
      rw [hlive_ev, EStateM.bind_eq_ok hder_sc]; rfl
    have ha_ok : evalStmt s ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s s.frame.locals) := by
      unfold evalStmt; dsimp only []; rw [hslot_p]
    have hstate' := hstate.cache_layout hframes hdecl_ptr hlt_p
    rcases hstate' with
      ⟨tfa, hframes_a, hretCont, hretPlace, hfra, _, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
    injection hframes_a with h1; injection h1 with h2; subst tfa
    rw [ha_ok, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      (hm_eq _ _ hp_ok) rfl hfra.location_eq]
    apply StepRelLM3_1.step
    refine .mk _ rfl hretCont hretPlace hfra.advance hcal hstack hprot hcaller hbor ?_ hdisj
    refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h3; injection h3 with h4; subst tf'
    exact halloc.local_alloc_sync _ rfl e he
  · have hmls_ptr : tf.locals[ptrIdx]'hlt_p =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
    have hlive_ev := annealEvalPlace_deref_live hframes hlt_p hdecl_ptr hmls_ptr hcache_p
    obtain ⟨_, _, _, _, hpow_pk, _⟩ := hpk_prim.size_align_ok body.layouts
    obtain ⟨mismatch, hmis_any⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset _ hpow_pk
    have hder_ptr := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hpk_prim mptr hmis_any
      (translateTy ptrDecl.ty body.layouts)
      { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt_p
          (translateTy ptrDecl.ty body.layouts)]⟩ }
    have hp_ok : annealEvalPlace body.localDecls body.layouts
        (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
        .ok ⟨.memory ⟨mptr.withOptionalProvenance, .none, mismatch⟩,
            translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
          { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt_p
              (translateTy ptrDecl.ty body.layouts)]⟩ } := by
      rw [hlive_ev, EStateM.bind_eq_ok hder_ptr]; rfl
    have ha_ok : evalStmt s ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩
        body.localDecls body.layouts = MirStepNode.step (advanceStmt s s.frame.locals) := by
      unfold evalStmt; dsimp only []; rw [hslot_p]
    have hstate' := hstate.cache_layout hframes hdecl_ptr hlt_p
    rcases hstate' with
      ⟨tfa, hframes_a, hretCont, hretPlace, hfra, _, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
    injection hframes_a with h1; injection h1 with h2; subst tfa
    rw [ha_ok, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt
      (hm_eq _ _ hp_ok) rfl hfra.location_eq]
    apply StepRelLM3_1.step
    refine .mk _ rfl hretCont hretPlace hfra.advance hcal hstack hprot hcaller hbor ?_ hdisj
    refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h3; injection h3 with h4; subst tf'
    exact halloc.local_alloc_sync _ rfl e he

/-- Deinitializing an immediate frame local preserves `IsImmediateFrameLocal`
at every local index `k`. -/
theorem IsImmediateFrameLocal.deinit_local
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {srcIdx : Nat} (hlt : srcIdx < tf.locals.size)
    {k : Nat} (hk : IsImmediateFrameLocal tf k) :
    IsImmediateFrameLocal (deinitFrameLocal tf srcIdx hlt) k := by
  intro mls hmls mp hmp
  simp only [deinitFrameLocal] at hmls
  by_cases hsk : srcIdx = k
  · subst hsk
    rw [Array.getElem?_set_self] at hmls
    injection hmls with hm
    rw [← hm] at hmp
    cases hmp
  · rw [Array.getElem?_set_ne _ hsk] at hmls
    exact hk mls hmls mp hmp

/-- Deinitializing an immediate local preserves `WellTypedScalarOperand`. -/
theorem WellTypedScalarOperand.of_deinitFrameLocal
    {body : CapturedMir}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {op : MirAst.Operand} {ty : Ty}
    (hop : WellTypedScalarOperand body tf op ty)
    (srcIdx : Nat) (hlt : srcIdx < tf.locals.size) :
    WellTypedScalarOperand body (deinitFrameLocal tf srcIdx hlt) op ty := by
  cases hop with
  | constScalar c sc hval hprim hsz hcan hlaysz hbool hchar =>
    exact .constScalar c sc hval hprim hsz hcan hlaysz hbool hchar
  | copyLocal idx decl hdecl hsz_nz himm =>
    exact .copyLocal idx decl hdecl hsz_nz (himm.deinit_local hlt)

/-- Deinitializing a live immediate local `srcIdx` (`Operand.move`)
to `.uninit` / `.live (.immediate .uninit)` preserves `StateRelLM3_1` without
modifying `allocMap` or machine memory. -/
theorem StateRelLM3_1.deinit_immediate_local
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    {srcIdx : Local} {srcDecl : LocalDecl}
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    {slot_s : LocalSlot}
    (hslot_s : get? s.frame.locals srcIdx = some slot_s)
    (hne_dead : slot_s ≠ .dead)
    (himm_src : IsImmediateFrameLocal tf srcIdx)
    (hlt_s : srcIdx < tf.locals.size) :
    StateRelLM3_1 body
      { s with frame := { s.frame with locals := s.frame.locals.set srcIdx .uninit } }
      { m with stack := ⟨#[deinitFrameLocal tf srcIdx hlt_s]⟩ }
      allocMap := by
  have hnot_src : ∀ e ∈ allocMap, e.localIdx ≠ srcIdx :=
    hstate.immediate_not_in_allocMap hframes hslot_s hne_dead himm_src
  rcases hstate with
    ⟨tf₀, hframes₀, hretCont, hretPlace, hfr, hcal, hstack, hprot, hcaller, hbor, halloc, hdisj⟩
  rw [hframes] at hframes₀
  injection hframes₀ with h₁
  injection h₁ with htf
  subst htf
  obtain ⟨_, mls_s, _, _, _, _, hmls_s_eq, hloc_s⟩ := hfr.lookup_local hdecl_src
  have hnew_s : LocalRelLM3_1 m.machine allocMap srcDecl body.layouts .uninit
      { tf.locals[srcIdx]'hlt_s with value := .live (.immediate .uninit) } :=
    .base (.immediate .uninit .uninit (tf.locals[srcIdx]'hlt_s).layout
      (by rw [hmls_s_eq]; exact hloc_s.cachedLayout_eq)
      (Or.inl ⟨rfl, rfl⟩))
  have hfr' := hfr.update_local hdecl_src .uninit (.live (.immediate .uninit)) hnew_s
  refine .mk (deinitFrameLocal tf srcIdx hlt_s) rfl hretCont hretPlace hfr'
    hcal hstack hprot hcaller hbor ?_ ?_
  · refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h₁
    injection h₁ with h₂
    subst h₂
    have hne_s : srcIdx ≠ e.localIdx := Ne.symm (hnot_src e he)
    obtain ⟨hlive_e, hdead_e⟩ := halloc.local_alloc_sync tf hframes e he
    have hget_ne :
        get? (s.frame.locals.set srcIdx .uninit) e.localIdx =
          get? s.frame.locals e.localIdx := by
      rw [get?_eq_getElem?, List.getElem?_set_ne hne_s, ← get?_eq_getElem?]
    refine ⟨fun slot' hslot' hne_d => ?_, fun hdead' => ?_⟩
    · dsimp only [] at hslot'
      rw [hget_ne] at hslot'
      obtain ⟨⟨lay, hlay⟩, hsc, hshape⟩ := hlive_e slot' hslot' hne_d
      refine ⟨⟨lay, ?_⟩, hsc, hshape⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ hne_s]
      exact hlay
    · dsimp only [] at hdead'
      rw [hget_ne] at hdead'
      exact hdead_e hdead'
  · apply MemoryAllocDisjoint.mono_immediate hdisj
    intro k
    by_cases hk : k = srcIdx
    · subst hk
      right
      refine ⟨.uninit, (tf.locals[k]'hlt_s).layout, ?_⟩
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_self]
    · left
      dsimp only [deinitFrameLocal]
      rw [Array.getElem?_set_ne _ (Ne.symm hk)]

/-- Shared post-operand write step into an immediate local `dstIdx` from an
operand-updated `StateRelLM3_1` mid-state `(s_mid, tf_mid)` (such as after
deinitializing a moved source local). -/
private theorem finish_write_immediate_from_mid
    {body : CapturedMir} {s s_mid : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    {tf tf_mid : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (hframes : m.stack.frames = #[tf])
    (hbody : tf.body = translateBody body)
    (hloc : tf.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩)
    (hstate_mid : StateRelLM3_1 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap)
    (hs_frame_eq : s_mid = { s with frame := { s.frame with locals := s_mid.frame.locals } })
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl} {rv : Rvalue} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (himm_dst_mid : IsImmediateFrameLocal tf_mid dstIdx)
    {val : Value} {newImm : Miri.Interpreter.Immediate AnnealProv}
    (hrv_anneal : evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
      .ok val s_mid.frame.locals s.memory)
    (hm_write : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
      Miri.Interpreter.runRvalue
        (annealWriteImmediate newImm
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
        { m with stack := ⟨#[tf_mid]⟩ })
    (hnew_rel : ∀ cachedLay,
      (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
      LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init val)
        ⟨.live (.immediate newImm), cachedLay⟩) :
    StepRelLM3_1 body m allocMap
      (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  have hfr_m := hstate_mid.frame_rel_singleton rfl
  obtain ⟨_, _, _, _, _, hcal_m, hstack_m, hprot_m, hcaller_m, hbor_m, _, _⟩ := id hstate_mid
  obtain ⟨slot_dm, mls_dm, hlt_af_dm, hlt_dm, hslot_dm, hmls_dm, hmls_dm_eq, hloc_dm⟩ :=
    hfr_m.lookup_local hdecl_dst
  have hs_mem : s_mid.memory = s.memory := by rw [hs_frame_eq]
  have hb_eq : s_mid.frame.blockIdx = s.frame.blockIdx := by rw [hs_frame_eq]
  have hsi_eq : s_mid.frame.stmtIdx = s.frame.stmtIdx := by rw [hs_frame_eq]
  have hd_dead_helper : slot_dm = .dead → mls_dm.value = .dead →
      StepRelLM3_1 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
    intro hsd_dead hmd_dead
    have hdm_dead : tf_mid.locals[dstIdx]? = some ⟨.dead, mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_dead
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.fail .ub := by
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm, hsd_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[tf_mid]⟩ }, .error (.undefinedBehavior "write to dead local")) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue
      rw [annealWriteImmediate_dead (m := { m with stack := ⟨#[tf_mid]⟩ })
        (id0 := tf.localsIdentity) rfl hget_dm]
    rw [ha_ub, miri_step_at_statement_error _ hframes hbody hloc hbb hstmt hm_err]
    exact .ub _ _
  have hd_live_helper : ∀ oldImm, mls_dm.value = .live (.immediate oldImm) →
      slot_dm ≠ .dead →
      StepRelLM3_1 body m allocMap
        (evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
    intro oldImm hmd_imm hsd_ne
    have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
      hstate_mid.immediate_not_in_allocMap rfl hslot_dm hsd_ne himm_dst_mid
    have hbor_s : s.memory.borrows = allocMap.map AllocMapEntry.toBorrowEntry := by
      rw [← hs_mem]; exact hbor_m
    have hprot_s : s.memory.activeProtectors = .nil := by
      rw [← hs_mem]; exact hprot_m
    have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor_s dstIdx none hnot_dst
    have hdm_live : tf_mid.locals[dstIdx]? =
        some ⟨.live (.immediate oldImm), mls_dm.layout⟩ := by
      rw [hmls_dm]; rcases mls_dm with ⟨v0, l0⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hget_dm := frame_getLocal_of_getElem? tf_mid dstIdx _ hdm_live
    have hw_ok := annealWriteImmediate_live (val := newImm)
      (m := { m with stack := ⟨#[tf_mid]⟩ }) (id0 := tf.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dm hget_dm
    have hm_ok : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩) m =
        ({ m with stack := ⟨#[{ tf_mid with
            locals := tf_mid.locals.set dstIdx
              { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) }
              hlt_dm }]⟩ }, .ok ()) := by
      rw [hm_write]; unfold Miri.Interpreter.runRvalue; rw [hw_ok]
    have hloc_mid : tf_mid.location = .mir ⟨s.frame.blockIdx, s.frame.stmtIdx⟩ := by
      have hl := hfr_m.location_eq
      rw [hb_eq, hsi_eq] at hl
      exact hl
    rw [miri_step_at_statement_ok _ hframes hbody hloc hbb hstmt hm_ok rfl hloc_mid]
    have ha_ok : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ body.localDecls body.layouts =
        MirStepNode.step
          (advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory) := by
      have hadv_eq : advanceStmt s (s_mid.frame.locals.set dstIdx (.init val)) s.memory =
          advanceStmt s_mid (s_mid.frame.locals.set dstIdx (.init val)) s_mid.memory := by
        rw [hs_frame_eq]; rfl
      rw [← hadv_eq]
      unfold evalStmt; dsimp only []; rw [hrv_anneal]; dsimp only []; rw [hslot_dm]
      cases slot_dm with
      | dead => exact absurd rfl hsd_ne
      | uninit =>
        simp only [set?_eq_some_set hlt_af_dm, hprot_s, hbor_inv]
        congr 2; generalize s.memory = mem at hprot_s ⊢
        cases mem; dsimp at hprot_s ⊢; subst hprot_s; rfl
      | init _ =>
        simp only [set?_eq_some_set hlt_af_dm, hprot_s, hbor_inv]
        congr 2; generalize s.memory = mem at hprot_s ⊢
        cases mem; dsimp at hprot_s ⊢; subst hprot_s; rfl
    rw [ha_ok]
    refine .step _ _ ?_
    have hnew_d : LocalRelLM3_1 m.machine (allocMap.map id) dstDecl body.layouts (.init val)
        { tf_mid.locals[dstIdx]'hlt_dm with value := .live (.immediate newImm) } := by
      rw [List.map_id]
      exact hnew_rel (tf_mid.locals[dstIdx]'hlt_dm).layout
        (by rw [hmls_dm_eq]; exact hloc_dm.cachedLayout_eq)
    have hstep_rel := hstate_mid.advance_write_immediate_perm_map rfl id
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
      hdecl_dst hnot_dst (by rw [hmls_dm_eq]; exact hmd_imm) hnew_d
      hcal_m hstack_m hprot_m hcaller_m (by rw [List.map_id]; exact hbor_m) rfl
    rw [List.map_id, hb_eq, hsi_eq] at hstep_rel
    exact hstep_rel
  cases hloc_dm with
  | rawPtr _ _ _ _ _ _ _ _ => exact hd_live_helper _ rfl (by simp)
  | base hb =>
    cases hb with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst_mid _ hmls_dm mp)
    | dead _ _ => exact hd_dead_helper rfl rfl
    | immediate _ oldImm _ _ hvd =>
      exact hd_live_helper oldImm rfl (by rcases hvd with ⟨rfl, _⟩ | ⟨_, rfl, _⟩ <;> simp)

/-- **`step_rawPtr_use_lm3_1_simulation`**: direct copy or move assignment
`_d = .use (opKind ⟨srcIdx, .nil⟩)` (`opKind ∈ {.copy, .move}`) between
immediate raw-pointer locals (`srcDecl.ty.kind = .rawPtr srcMut pointeeKind`,
`dstDecl.ty.kind = .rawPtr dstMut pointeeKind`). Covers `.dead`/`.uninit` UB,
provenance-less integer-scalar pointers (e.g. `0 as *const T`), and `PtrRel`
provenance-tracked pointers, including self-assignment `dstIdx = srcIdx` and
moving out of `_s` (leaving `_s` uninitialized in both machines). -/
theorem step_rawPtr_use_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩)
    {dstDecl srcDecl : LocalDecl} {srcMut dstMut : Mutability} {pointeeKind : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_src⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (opKind ⟨srcIdx, .nil⟩) span m
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_copy : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  have htr_move : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, hlt_af_s, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx :=
    himm_src.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx :=
    himm_dst.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
    himm_d_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have himm_s_tfb : IsImmediateFrameLocal tfb srcIdx :=
    himm_s_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_sa
  rcases hloc_s.rawPtr_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨hss_dead, hms_dead⟩ | ⟨hss_un, hms_un⟩ |
    ⟨sc_s, msc_s, hss_sc, hsz8, hrel_sc, hms_sc⟩ |
    ⟨ptrVal, mptr, hss_ptr, hptrRel, hms_ptr⟩
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_dead; subst hms_dead; rfl
    rcases hopKind with rfl | rfl
    · have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_un; subst hms_un; rfl
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_s))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_sc; subst hms_sc; rfl
    have hnew_sc : ∀ cachedLay,
        (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
        LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init (.scalar sc_s))
          ⟨.live (.immediate (.scalar (.fromScalarInt msc_s))), cachedLay⟩ := by
      intro cachedLay hc
      refine .base (.immediate (.init (.scalar sc_s)) (.scalar (.fromScalarInt msc_s))
        cachedLay hc (Or.inr ⟨.scalar sc_s, rfl, .scalar sc_s msc_s hrel_sc ?_ ?_ ?_⟩))
      · unfold translateTy; rw [hdst_ty, hsz8]; rfl
      · intro hb; rw [hdst_ty] at hb; cases hb
      · intro hc'; rw [hdst_ty] at hc'; cases hc'
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hrv_a : evalRvalue s.frame.locals (.use (.copy ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts = .ok (.scalar sc_s) s.frame.locals s.memory := by
        unfold evalRvalue evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss_sc]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc_s))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_b rfl
        hbb hstmt hdecl_dst himm_d_tfb hrv_a hm_w hnew_sc
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s
        (by rw [hss_sc]; simp) himm_s_tfb hlt_sb
      have hrv_a : evalRvalue s.frame.locals (.use (.move ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts =
          .ok (.scalar sc_s) (s.frame.locals.set srcIdx .uninit) s.memory := by
        unfold evalRvalue evalOperand; dsimp only []
        rw [hslot_s, hss_sc, set?_eq_some_set hlt_af_s]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc_s))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_mid rfl
        hbb hstmt hdecl_dst (himm_d_tfb.deinit_local hlt_sb) hrv_a hm_w hnew_sc
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_ptr; subst hms_ptr; rfl
    have hnew_ptr : ∀ cachedLay,
        (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
        LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init (.ptr ptrVal 8))
          ⟨.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))), cachedLay⟩ :=
      fun cachedLay hc => .rawPtr ptrVal mptr cachedLay dstMut pointeeKind hc hdst_ty hptrRel
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hrv_a : evalRvalue s.frame.locals (.use (.copy ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts = .ok (.ptr ptrVal 8) s.frame.locals s.memory := by
        unfold evalRvalue evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss_ptr]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate
              (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_b rfl
        hbb hstmt hdecl_dst himm_d_tfb hrv_a hm_w hnew_ptr
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s
        (by rw [hss_ptr]; simp) himm_s_tfb hlt_sb
      have hrv_a : evalRvalue s.frame.locals (.use (.move ⟨srcIdx, .nil⟩)) s.memory
          body.localDecls body.layouts =
          .ok (.ptr ptrVal 8) (s.frame.locals.set srcIdx .uninit) s.memory := by
        unfold evalRvalue evalOperand; dsimp only []
        rw [hslot_s, hss_ptr, set?_eq_some_set hlt_af_s]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.move ⟨srcIdx, .nil⟩)), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate
              (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval]; rw [EStateM.bind_eq_ok hsrc_ok]; rfl
      exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_mid rfl
        hbb hstmt hdecl_dst (himm_d_tfb.deinit_local hlt_sb) hrv_a hm_w hnew_ptr

/-- **`step_cast_ptrToPtr_move_simulation`**: move-operand `CastKind.PtrToPtr`
(`_d = move _s as *(const|mut) V`) between thin raw-pointer locals,
deinitializing `_s` in both machines before writing the casted pointer into
`_d`. -/
theorem step_cast_ptrToPtr_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl}
    {srcMut dstMut castMut : Mutability} {srcPointee dstPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hno_int : ∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_src⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_cast_ptrToPtr_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (.move ⟨srcIdx, .nil⟩) castTy span m
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, hlt_af_s, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx :=
    himm_src.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx :=
    himm_dst.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
    himm_d_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have himm_s_tfb : IsImmediateFrameLocal tfb srcIdx :=
    himm_s_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_src : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  rcases hloc_s.rawPtr_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨hss_dead, hms_dead⟩ | ⟨hss_un, hms_un⟩ |
    ⟨sc_s, _, hss_sc, _, _, _⟩ |
    ⟨ptrVal, mptr, hss_ptr, hptrRel, hms_ptr⟩
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_dead; subst hms_dead; rfl
    have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_un; subst hms_un; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_un]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        miri_cast_dispatch_ptrToPtr_eq body.layouts srcMut dstMut castMut srcPointee dstPointee
          srcDecl.ty dstDecl.ty castTy hsrc_ty hdst_ty hcast_ty hsrc_thin]
      rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · exact absurd (hslot_s.trans (congrArg some hss_sc)) (hno_int sc_s)
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_ptr; subst hms_ptr; rfl
    have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
    let tf_mid := deinitFrameLocal tfb srcIdx hlt_sb
    have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s
      (by rw [hss_ptr]; simp) himm_s_tfb hlt_sb
    have hrv_a : evalRvalue s.frame.locals (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.ptr ptrVal 8) (s.frame.locals.set srcIdx .uninit) s.memory := by
      unfold evalRvalue evalOperand; dsimp only []
      rw [hslot_s, hss_ptr, set?_eq_some_set hlt_af_s]
    have hcast_ok := miri_cast_ptrToPtr_annealCastHooks_eq body.layouts
      { m with stack := ⟨#[tf_mid]⟩ } srcMut dstMut srcPointee dstPointee srcDecl.ty dstDecl.ty
      hsrc_ty hdst_ty hsrc_thin hdst_thin mptr
    have hread_src : annealReadImmediate
        ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf_mid]⟩ } =
        .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
          translateTy srcDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf_mid]⟩ } := rfl
    have hm_w : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (annealWriteImmediate
            (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
            ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
          { m with stack := ⟨#[tf_mid]⟩ } := by
      rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
        miri_cast_dispatch_ptrToPtr_eq body.layouts srcMut dstMut castMut srcPointee dstPointee
          srcDecl.ty dstDecl.ty castTy hsrc_ty hdst_ty hcast_ty hsrc_thin,
        EStateM.bind_eq_ok hread_src, EStateM.bind_eq_ok hcast_ok]
    exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_mid rfl
      hbb hstmt hdecl_dst (himm_d_tfb.deinit_local hlt_sb) hrv_a hm_w
      (fun cachedLay hc => .rawPtr ptrVal mptr cachedLay dstMut dstPointee hc hdst_ty hptrRel)

/-- **`step_binOp_offset_move_simulation`**: move-operand `BinOp.Offset`
(`_d = Offset(move _p, rhsOp)`) on byte-sized raw pointers (`*const u8`,
`*mut u8`, `*const i8`, `*mut i8`), deinitializing `_p` before evaluating
`rhsOp` (matching both machines' left-to-right operand evaluation order, even
when `rhsOp` reads `_p` or `_d = _p`). -/
theorem step_binOp_offset_move_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : LocalDecl} {ptrMut dstMut : Mutability} {pointeeKind : RigidTy}
    {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hinbounds : ∀ ptrVal sc e tgtDecl,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      evalOperand (s.frame.locals.set ptrIdx .uninit) rhsOp s.memory.borrows s.memory.globals
        body.layouts s.memory.callerLocals =
        .ok (.scalar sc) (s.frame.locals.set ptrIdx .uninit) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? body.localDecls e.localIdx = some tgtDecl →
      sc.bits = 0 ∨
        (get? s.frame.locals e.localIdx ≠ some .dead ∧
          ptrVal.offsetBytes + sc.bits ≤
            (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨himm_dst, himm_ptr⟩ := himm tf hframes
  have hop_tf := hop_rhs tf hframes
  have hrhs_prim : IsPrimScalarTy rhsTy := by
    rcases hrhs_ty with hk | hk
    · exact Or.inr (Or.inr (Or.inr ⟨.usize, hk⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨.isize, hk⟩))
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt := evalStatement_assign_binOp_offset_eq body.localDecls body.layouts
    ⟨dstIdx, .nil⟩ (.move ⟨ptrIdx, .nil⟩) rhsOp span m
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hop_tfa := hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  obtain ⟨slot_p, mls_p, hlt_af_p, hlt_pa, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  have himm_p_tfa : IsImmediateFrameLocal tfa ptrIdx :=
    himm_ptr.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx :=
    himm_dst.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
  have hop_tfb := hop_tfa.of_cacheFrameLocalLayout ptrIdx hlt_pa
    (translateTy ptrDecl.ty body.layouts)
  have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
    himm_d_tfa.cache_layout hlt_pa (translateTy ptrDecl.ty body.layouts)
  have himm_p_tfb : IsImmediateFrameLocal tfb ptrIdx :=
    himm_p_tfa.cache_layout hlt_pa (translateTy ptrDecl.ty body.layouts)
  have hlt_pb : ptrIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_pa
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_lhs : translateOperand (.move ⟨ptrIdx, .nil⟩) = .Move ⟨ptrIdx, #[]⟩ := rfl
  have hlay_eq : translateTy ptrDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
    unfold translateTy encodeTyId; rw [hptr_ty, hdst_ty]
  rcases hloc_p.rawPtr_immediate_cases hptr_ty (himm_p_tfa mls_p hmls_p) with
    ⟨hsp_dead, hmp_dead⟩ | ⟨hsp_un, hmp_un⟩ |
    ⟨sc_p, _, hsp_sc, _, _, _⟩ |
    ⟨ptrVal, mptr, hsp_ptr, hptrRel, hmp_ptr⟩
  · have hmls_p' : tfa.locals[ptrIdx]'hlt_pa = ⟨.dead, mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_dead; subst hmp_dead; rfl
    have hlhs_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_p, hsp_dead]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
      rw [hm_stmt, htr_dst, htr_lhs]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hlhs_err]
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · have hmls_p' : tfa.locals[ptrIdx]'hlt_pa = ⟨.live (.immediate .uninit), mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_un; subst hmp_un; rfl
    have hlhs_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
    have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
        (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩
        body.localDecls body.layouts = MirStepNode.fail .ub := by
      unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_p, hsp_un]
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt
          ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
        ({ m with stack := ⟨#[deinitFrameLocal tfb ptrIdx hlt_pb]⟩ },
          .error (.undefinedBehavior "read of uninitialized local")) := by
      rw [hm_stmt, htr_dst, htr_lhs]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok]; rfl
    rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err]
    exact .ub _ _
  · exact absurd (hslot_p.trans (congrArg some hsp_sc)) (hno_int sc_p)
  · have hmls_p' : tfa.locals[ptrIdx]'hlt_pa =
        ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
          mls_p.layout⟩ := by
      rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
    have hlhs_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
      (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
    let tf_mid := deinitFrameLocal tfb ptrIdx hlt_pb
    let s_mid : MachineState :=
      { s with frame := { s.frame with locals := s.frame.locals.set ptrIdx .uninit } }
    have hstate_mid : StateRelLM3_1 body s_mid { m with stack := ⟨#[tf_mid]⟩ } allocMap :=
      hstate_b.deinit_immediate_local rfl hdecl_ptr hslot_p (by rw [hsp_ptr]; simp)
        himm_p_tfb hlt_pb
    have hop_mid : WellTypedScalarOperand body tf_mid rhsOp rhsTy :=
      hop_tfb.of_deinitFrameLocal ptrIdx hlt_pb
    have himm_d_mid : IsImmediateFrameLocal tf_mid dstIdx := himm_d_tfb.deinit_local hlt_pb
    have hread_lhs : annealReadImmediate
        ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
          translateTy ptrDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf_mid]⟩ } =
        .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
          translateTy ptrDecl.ty body.layouts⟩
        { m with stack := ⟨#[tf_mid]⟩ } := rfl
    have hsp_full : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) :=
      hslot_p.trans (congrArg some hsp_ptr)
    have hrv_move_eq : evalRvalue s.frame.locals
        (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp) s.memory body.localDecls body.layouts =
        match evalOperand s_mid.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
            s.memory.callerLocals with
        | .ok (.scalar sc) locals' =>
          .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8) locals' s.memory
        | .ok _ _ => .unsupported
        | .ub => .ub
        | .unsupported => .unsupported := by
      cases hop_tf <;>
      · unfold evalRvalue
        have hlhs_a : evalOperand s.frame.locals (.move ⟨ptrIdx, .nil⟩) s.memory.borrows
            s.memory.globals body.layouts s.memory.callerLocals =
            .ok (.ptr ptrVal 8) s_mid.frame.locals := by
          unfold evalOperand; dsimp only []; rw [hsp_full, set?_eq_some_set hlt_af_p]
        dsimp only []; rw [hlhs_a]; dsimp only []
        cases hr : evalOperand s_mid.frame.locals _ s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals with
        | ub => rfl
        | unsupported => rfl
        | ok v locs' => cases v <;> rfl
    rcases evalOperand_scalar_lm3_1_simulation hstate_mid rfl hop_mid hrhs_prim none with
      ⟨m_rhs, msg_rhs, hrhs_ub, hm_rhs_ub⟩ |
      ⟨sc, msc, tfc, hrhs_ok, hm_rhs_ok, hstate_c, hrel_imm, _, htfc_preserve⟩
    · have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
          (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt; dsimp only []; rw [hrv_move_eq]; exact hrhs_ub ▸ rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt
            ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
          (m_rhs, .error (.undefinedBehavior msg_rhs)) := by
        rw [hm_stmt, htr_dst, htr_lhs]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
          EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_error hm_rhs_ub]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have hsc_rel : ScalarRel sc msc ∧ sc.sizeBytes = 8 := by
        cases hrel_imm with
        | scalar _ _ hrel hsz _ _ =>
          have hlay_rhs : (translateTy rhsTy body.layouts).layout.size =
              Miri.ABI.Size.ofBytes 8 := by
            rcases hrhs_ty with hk | hk <;> (unfold translateTy; rw [hk]; rfl)
          rw [hlay_rhs] at hsz
          have hb : (8 : UInt64) = UInt64.ofNat sc.sizeBytes := congrArg Miri.ABI.Size.bytes hsz
          have hcan := hrel.validBytes
          have hsz8 : sc.sizeBytes = 8 := by
            rcases hcan with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb ⊢ <;>
              first | rfl | cases hb
          exact ⟨hrel, hsz8⟩
      obtain ⟨allocId, borTag, hprov_eq, hid_lt, hoff_lt, hmptr_off, e, he_mem, he_tag, he_aid⟩ :=
        hptrRel
      subst he_aid
      obtain ⟨tgtDecl, htgt_decl, htgt_prim⟩ := halloc.target_decl e he_mem
      have hsc_cases := hinbounds ptrVal sc e tgtDecl hsp_full hrhs_ok he_mem he_tag htgt_decl
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
            some (.concrete e.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
        subst hprov_eq hmptr_off; rfl
      have hptr_step : sc.bits < 2 ^ 32 ∧
          ptrVal.offsetBytes + sc.bits < 2 ^ 32 ∧
          Miri.Interpreter.ptrOffsetInbounds annealPointerArithmetic
            mptr.withOptionalProvenance (Int64.ofInt (sc.bits : Int))
            (annealResolvePtr m.machine) (annealLookupAlloc m.machine) =
            .ok ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes + sc.bits)),
              some (.concrete e.allocId borTag)⟩ := by
        rcases hsc_cases with hbits0 | ⟨hlive_e, hinb_e⟩
        · refine ⟨by omega, by omega, ?_⟩
          rw [hmptr_opt, hbits0]
          simpa [Nat.add_zero] using
            ptrOffsetInbounds_zero_ok m.machine
              ⟨Miri.ABI.Size.ofBytes
                (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
                some (.concrete e.allocId borTag)⟩
        · obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local htgt_decl
          have ht_ne_dead : slot_t ≠ .dead := fun hd => hlive_e (hslot_t.trans (congrArg some hd))
          obtain ⟨_, _, hsh_t⟩ :=
            (halloc.local_alloc_sync tf hframes e he_mem).1 slot_t hslot_t ht_ne_dead
          obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_t tgtDecl htgt_decl
          obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e he_mem
          have htgt_le16 : (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat ≤ 16 := by
            rcases htgt_prim with hk | hk | ⟨it, hk⟩ | ⟨ut, hk⟩
            · simp only [translateTy, hk]; decide
            · simp only [translateTy, hk]; decide
            · cases it <;> (simp only [translateTy, hk]; decide)
            · cases ut <;> (simp only [translateTy, hk]; decide)
          have hsz_nat : localAlloc.allocation.byteSize.bytes.toNat ≤ 16 := by
            rw [hshape_la.byteSize_eq]; exact htgt_le16
          have hinb_la : ptrVal.offsetBytes + sc.bits ≤
              localAlloc.allocation.byteSize.bytes.toNat := by
            rw [hshape_la.byteSize_eq]; exact hinb_e
          have hbits_lt : sc.bits < 2 ^ 32 := by omega
          have hsum_lt : ptrVal.offsetBytes + sc.bits < 2 ^ 32 := by omega
          refine ⟨hbits_lt, hsum_lt, ?_⟩
          rw [hmptr_opt]
          exact ptrOffsetInbounds_live_inbounds_ok e.allocId borTag ptrVal.offsetBytes sc.bits
            localAlloc hid_lt hoff_lt hbits_lt hbase hfind_la hinb_la
      obtain ⟨hbits_lt, hsum_lt, hpoff_ok⟩ := hptr_step
      let mptr' : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes
          (annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes + sc.bits)),
          .concrete e.allocId borTag⟩
      have hptrRel' : PtrRel allocMap
          { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } mptr' :=
        .mk e.allocId borTag rfl hid_lt hsum_lt rfl ⟨e, he_mem, he_tag, rfl⟩
      have hbin_ok : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
          ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            translateTy ptrDecl.ty body.layouts⟩
          ⟨.scalar (.fromScalarInt msc), translateTy rhsTy body.layouts⟩
          { m with stack := ⟨#[tfc]⟩ } =
          .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr'),
            translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tfc]⟩ } := by
        rw [scalarOps_binary_offset_byte_eq body.localDecls body.layouts hptr_ty hpt hrhs_ty,
          annealPointerBinary_byte_eq body.layouts hptr_ty hpt hrhs_ty hsc_rel.1 hsc_rel.2
            hbits_lt mptr { m with stack := ⟨#[tfc]⟩ },
          hpoff_ok]
        rfl
      have hassert_ok : assertRvalueLayoutPub (translateTy ptrDecl.ty body.layouts)
          (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfc]⟩ } =
          .ok () { m with stack := ⟨#[tfc]⟩ } := by
        unfold assertRvalueLayoutPub; simp [hlay_eq, pure, EStateM.pure]
      have hrv_a : evalRvalue s.frame.locals
          (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp) s.memory body.localDecls body.layouts =
          .ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8)
            s_mid.frame.locals s.memory := by
        rw [hrv_move_eq]; exact hrhs_ok ▸ rfl
      have himm_d_tfc : IsImmediateFrameLocal tfc dstIdx := by
        intro mls_c hmls_c mp hmp
        have hp_c := htfc_preserve dstIdx
        rw [hmls_c] at hp_c
        dsimp only [Option.map] at hp_c
        cases hdm : tf_mid.locals[dstIdx]? with
        | none => rw [hdm] at hp_c; cases hp_c
        | some mls_m =>
          rw [hdm] at hp_c
          injection hp_c with hv_eq
          exact himm_d_mid mls_m hdm mp (hv_eq.symm.trans hmp)
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt
            ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate
              (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr'))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tfc]⟩ } := by
        rw [hm_stmt, htr_dst, htr_lhs]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
          EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_ok hm_rhs_ok,
          EStateM.bind_eq_ok hbin_ok, EStateM.bind_eq_ok hassert_ok]
      exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_c rfl
        hbb hstmt hdecl_dst himm_d_tfc hrv_a hm_w
        (fun cachedLay hc => .rawPtr _ mptr' cachedLay dstMut pointeeKind hc hdst_ty hptrRel')

/-- **`step_cast_expose_provenance_scalar_simulation`**: provenance-exposing
pointer-to-integer cast `_d = (opKind ⟨srcIdx, .nil⟩) as usize`
(`CastKind.PointerExposeProvenance`, `opKind ∈ {.copy, .move}`) on thin
raw-pointer locals that do **not** hold a concrete `PtrRel` provenance tag
(i.e. `.dead` UB, `.uninit` UB, or provenance-less integer-scalar pointers such
as `0 as *const T`). Because `Pointer.withoutProvenance` carries
`.provenance = none`, `Cast.pointerExposeProvenance` skips `exposeProvenance`
and converts the 8-byte address cleanly to `usize` in lockstep with Anneal's
`stepMirFn`. -/
theorem step_cast_expose_provenance_scalar_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local}
    {opKind : Place → MirAst.Operand} {castTy : Ty} {span : String}
    (hopKind : opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .pointerExposeProvenance (opKind ⟨srcIdx, .nil⟩) castTy), span⟩)
    {dstDecl srcDecl : LocalDecl} {srcMut : Mutability} {srcPointee : RigidTy}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_ty : dstDecl.ty.kind = .uint .usize)
    (hcast_ty : castTy.kind = .uint .usize)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hno_ptr : ∀ ptrVal, get? s.frame.locals srcIdx ≠ some (.init (.ptr ptrVal 8))) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_src⟩ := himm tf hframes
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  have hm_stmt : ∀ op : MirAst.Operand,
      Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.cast .pointerExposeProvenance op castTy), span⟩)
        m =
      Miri.Interpreter.runRvalue
        (do
          let destPlace ← annealEvalPlace body.localDecls body.layouts
            (translatePlace ⟨dstIdx, .nil⟩)
          let src ← annealEvalOperand body.localDecls body.layouts (translateOperand op) none
          Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16 src
            .PointerExposeProvenance (encodeTyId castTy) destPlace) m := by
    intro op
    unfold Miri.Interpreter.Step.evalStatement translateStmt
    dsimp only [translateStmtKind, translateRvalue, translateCastKind, annealStepHooks]
    apply runRvalue_eq_of_eq
    unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
    dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, pure, EStateM.pure, bind, EStateM.bind]
  have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
  have htr_copy : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
  have htr_move : translateOperand (.move ⟨srcIdx, .nil⟩) = .Move ⟨srcIdx, #[]⟩ := rfl
  obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  obtain ⟨slot_s, mls_s, hlt_af_s, hlt_sa, hslot_s, hmls_s, hmls_s_eq, hloc_s⟩ :=
    hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
  have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
    hloc_s.cachedLayout_eq
  have himm_s_tfa : IsImmediateFrameLocal tfa srcIdx :=
    himm_src.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  have himm_d_tfa : IsImmediateFrameLocal tfa dstIdx :=
    himm_dst.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
  let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
  have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
  have himm_d_tfb : IsImmediateFrameLocal tfb dstIdx :=
    himm_d_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have himm_s_tfb : IsImmediateFrameLocal tfb srcIdx :=
    himm_s_tfa.cache_layout hlt_sa (translateTy srcDecl.ty body.layouts)
  have hlt_sb : srcIdx < tfb.locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt_sa
  have hsrc_enc : (translateTy srcDecl.ty body.layouts).ty = encodeRawPtrTyId srcPointee := by
    unfold translateTy encodeTyId; rw [hsrc_ty]
  have hsrc_lay : (translateTy srcDecl.ty body.layouts).layout = pointerLayoutData false := by
    unfold translateTy; rw [hsrc_ty]
  obtain ⟨pInfo, hpInfo⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId srcPointee hsrc_thin
  have hdst_enc : (translateTy dstDecl.ty body.layouts).ty = 25 := by
    unfold translateTy encodeTyId; rw [hdst_ty]
  have hdst_lay : (translateTy dstDecl.ty body.layouts).layout = scalarLayoutData 8 false := by
    unfold translateTy; rw [hdst_ty]; rfl
  have hcast_enc : encodeTyId castTy = 25 := by unfold encodeTyId; rw [hcast_ty]
  have husize_info : castTypeInfoOfEncodedTyId 25 = .ok (.integer .usize) := rfl
  have hcast_dispatch : ∀ srcOp destVal,
      Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16
        ⟨srcOp, translateTy srcDecl.ty body.layouts⟩ .PointerExposeProvenance (encodeTyId castTy)
        ⟨destVal, translateTy dstDecl.ty body.layouts⟩ =
      (do
        let value ← annealReadImmediate ⟨srcOp, translateTy srcDecl.ty body.layouts⟩
        let result ← Miri.Interpreter.Cast.pointerExposeProvenance (annealCastHooks body.layouts) ()
          value (translateTy dstDecl.ty body.layouts)
        annealWriteImmediate result.imm ⟨destVal, translateTy dstDecl.ty body.layouts⟩) := by
    intro srcOp destVal
    funext st
    unfold Miri.Interpreter.Cast.cast annealCastHooks
    simp only [hsrc_enc, hdst_enc, hcast_enc, hsrc_lay, pointerLayoutData, hpInfo, beq_self_eq_true,
      ↓reduceIte, Bool.false_eq_true, bind, EStateM.bind, pure, EStateM.pure]
  rcases hloc_s.rawPtr_immediate_cases hsrc_ty (himm_s_tfa mls_s hmls_s) with
    ⟨hss_dead, hms_dead⟩ | ⟨hss_un, hms_un⟩ |
    ⟨sc_s, msc_s, hss_sc, hsz8, hrel_sc, hms_sc⟩ |
    ⟨ptrVal, _, hss_ptr, _, _⟩
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.dead, mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_dead; subst hms_dead; rfl
    rcases hopKind with rfl | rfl
    · have hsrc_err := annealEvalOperand_copy_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have hsrc_err := annealEvalOperand_move_dead (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .pointerExposeProvenance (.move ⟨srcIdx, .nil⟩) castTy), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_dead]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_error hsrc_err]
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa = ⟨.live (.immediate .uninit), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_un; subst hms_un; rfl
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_dispatch]
        rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have ha_ub : evalStmt s ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .pointerExposeProvenance (.move ⟨srcIdx, .nil⟩) castTy), span⟩
          body.localDecls body.layouts = MirStepNode.fail .ub := by
        unfold evalStmt evalRvalue evalOperand; dsimp only []; rw [hslot_s, hss_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_dispatch]
        rfl
      rw [ha_ub, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt
        hm_err]
      exact .ub _ _
  · have hmls_s' : tfa.locals[srcIdx]'hlt_sa =
        ⟨.live (.immediate (.scalar (.fromScalarInt msc_s))), mls_s.layout⟩ := by
      rw [hmls_s_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_sc; subst hms_sc; rfl
    have hsz8_raw : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨msc_conv, htrunc_conv, hrel_conv⟩ :=
      truncateFromUInt_translateSizeBytes_raw hsz8_raw
        (BitVec.ofNat 128 (BitVec.ofNat 128 sc_s.bits).toNat)
    have hbits_conv_eq :
        (BitVec.ofNat 128 (BitVec.ofNat 128 sc_s.bits).toNat).toNat % 2 ^ (8 * 8) = sc_s.bits := by
      have hcan := hrel_sc.canonical
      rw [hsz8, scalarModulus_eq_two_pow] at hcan
      have hbv1 := bitVec_ofNat_toNat_of_valid hsz8_raw
        (by rw [scalarModulus_eq_two_pow]; exact hcan)
      rw [hbv1, hbv1]
      exact Nat.mod_eq_of_lt hcan
    have hrel_out : ScalarRel ⟨sc_s.bits, 8⟩ msc_conv := hbits_conv_eq ▸ hrel_conv
    have htoUInt_s : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_s).toUInt
        (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc_s.bits) := by
      have hsz_eq : translateSizeBytes sc_s.sizeBytes = Miri.ABI.Size.ofBytes 8 := by
        rw [hsz8]; decide
      have hzero8 : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := by decide
      have hts : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_s).toScalarInt =
          .ok msc_s := rfl
      have htb : msc_s.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc_s.bits) := by
        rw [← hsz_eq]; exact hrel_sc.toBits_eq
      unfold Miri.Memory.Scalar.toUInt Miri.Memory.Scalar.toBits
      simp only [hzero8, Bool.false_eq_true, ↓reduceIte, hts, htb,
        Except.mapError, bind, Except.bind]
    have hpep_ok : ∀ st : AnnealStepState,
        Miri.Interpreter.Cast.pointerExposeProvenance (annealCastHooks body.layouts) ()
          ⟨.scalar (.fromScalarInt msc_s), translateTy srcDecl.ty body.layouts⟩
          (translateTy dstDecl.ty body.layouts) st =
        .ok ⟨.scalar (.fromScalarInt msc_conv), translateTy dstDecl.ty body.layouts⟩ st := by
      intro st
      have hint_cast : Miri.Interpreter.IntegerCast.cast
          (.integer ⟨Miri.ABI.Size.ofBytes 16, .u128⟩)
          (.ofUInt128 (BitVec.ofNat 128 sc_s.bits))
          (.integer ⟨Miri.ABI.Size.ofBytes 8, .usize⟩) = .ok msc_conv := by
        have hsz_eq8 : Miri.ABI.Size.ofBytes 8 = translateSizeBytes 8 := by decide
        rw [hsz_eq8]
        with_unfolding_all
          change ((Miri.Memory.ScalarInt.truncateFromUInt
              (BitVec.ofNat 128 (BitVec.ofNat 128 sc_s.bits).toNat) (translateSizeBytes 8)
              |>.mapError Miri.Interpreter.IntegerCastError.scalar).bind
              fun (result, _) => Except.ok result) = _
          rw [htrunc_conv]
          rfl
      have hintLike : Miri.Interpreter.Cast.intLikeValue (annealCastHooks body.layouts) ()
          (.fromScalarInt msc_s) (translateTy srcDecl.ty body.layouts) st =
          .ok (BitVec.ofNat 128 sc_s.bits, false) st := by
        with_unfolding_all
          unfold Miri.Interpreter.Cast.intLikeValue annealCastHooks
          simp only [hsrc_enc, hsrc_lay, pointerLayoutData, hpInfo,
            Miri.ABI.BackendRepr.isSigned, Miri.ABI.Scalar.isSigned, htoUInt_s,
            Except.mapError, bind, EStateM.bind, pure, EStateM.pure]
          rfl
      have hti_s : (annealCastHooks body.layouts).typeInfo ()
          (translateTy srcDecl.ty body.layouts).ty = pure (.rawPointer pInfo) := by
        unfold annealCastHooks; simp only [hsrc_enc, hpInfo]
      have hti_d : (annealCastHooks body.layouts).typeInfo ()
          (translateTy dstDecl.ty body.layouts).ty = pure (.integer .usize) := by
        unfold annealCastHooks; simp only [hdst_enc, husize_info]
      have hsz_d : (translateTy dstDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
        rw [hdst_lay]; rfl
      have hcast_int : Miri.Interpreter.Cast.castFromIntLike (annealCastHooks body.layouts) ()
          (.fromScalarInt msc_s) (translateTy srcDecl.ty body.layouts)
          (translateTy dstDecl.ty body.layouts) st =
          .ok ⟨.scalar (.fromScalarInt msc_conv), translateTy dstDecl.ty body.layouts⟩ st := by
        unfold Miri.Interpreter.Cast.castFromIntLike
        rw [EStateM.bind_eq_ok hintLike]
        simp only [hti_d, hsz_d, hint_cast, Except.mapError, pure_bind]
        rfl
      have htoPtr_t : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_s).toPointer
          (annealCastHooks body.layouts).target =
          .ok (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc_s.bits)) :=
        scalar_fromScalarInt_toPointer_eq hrel_sc hsz8
      have hpep_eq : Miri.Interpreter.Cast.pointerExposeProvenance (annealCastHooks body.layouts) ()
          ⟨.scalar (.fromScalarInt msc_s), translateTy srcDecl.ty body.layouts⟩
          (translateTy dstDecl.ty body.layouts) st =
          Miri.Interpreter.Cast.castFromIntLike (annealCastHooks body.layouts) ()
            (.fromScalarInt msc_s) (translateTy srcDecl.ty body.layouts)
            (translateTy dstDecl.ty body.layouts) st := by
        unfold Miri.Interpreter.Cast.pointerExposeProvenance
        simp only [hti_s, hti_d, pure_bind]
        refine Eq.trans (EStateM.bind_eq_ok (s' := st) (a := .fromScalarInt msc_s)
          (by with_unfolding_all rfl)) ?_
        rw [htoPtr_t]
        with_unfolding_all rfl
      rw [hpep_eq]
      exact hcast_int
    have hread_s : ∀ st : AnnealStepState,
        annealReadImmediate
          ⟨.immediate (.scalar (.fromScalarInt msc_s)), translateTy srcDecl.ty body.layouts⟩ st =
        .ok ⟨.scalar (.fromScalarInt msc_s), translateTy srcDecl.ty body.layouts⟩ st :=
      fun _ => rfl
    have hnew_usize : ∀ cachedLay,
        (∀ l, cachedLay = some l → l = translateTy dstDecl.ty body.layouts) →
        LocalRelLM3_1 m.machine allocMap dstDecl body.layouts (.init (.scalar ⟨sc_s.bits, 8⟩))
          ⟨.live (.immediate (.scalar (.fromScalarInt msc_conv))), cachedLay⟩ := by
      intro cachedLay hc
      refine .base (.immediate (.init (.scalar ⟨sc_s.bits, 8⟩)) (.scalar (.fromScalarInt msc_conv))
        cachedLay hc (Or.inr ⟨.scalar ⟨sc_s.bits, 8⟩, rfl, .scalar _ msc_conv hrel_out ?_ ?_ ?_⟩))
      · unfold translateTy; rw [hdst_ty]; rfl
      · intro hb; rw [hdst_ty] at hb; cases hb
      · intro hc'; rw [hdst_ty] at hc'; cases hc'
    rcases hopKind with rfl | rfl
    · have hsrc_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hrv_a : evalRvalue s.frame.locals
          (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts = .ok (.scalar ⟨sc_s.bits, 8⟩) s.frame.locals s.memory := by
        unfold evalRvalue evalOperand readProjectedValue; dsimp only []; rw [hslot_s, hss_sc]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc_conv))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_copy]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_dispatch,
          EStateM.bind_eq_ok (hread_s _), EStateM.bind_eq_ok (hpep_ok _)]
      exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_b rfl
        hbb hstmt hdecl_dst himm_d_tfb hrv_a hm_w hnew_usize
    · have hsrc_ok := annealEvalOperand_move_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := none) rfl hlt_sa hdecl_src hmls_s' hcache_s
      have hstate_mid := hstate_b.deinit_immediate_local rfl hdecl_src hslot_s
        (by rw [hss_sc]; simp) himm_s_tfb hlt_sb
      have hrv_a : evalRvalue s.frame.locals
          (.cast .pointerExposeProvenance (.move ⟨srcIdx, .nil⟩) castTy) s.memory
          body.localDecls body.layouts =
          .ok (.scalar ⟨sc_s.bits, 8⟩) (s.frame.locals.set srcIdx .uninit) s.memory := by
        unfold evalRvalue evalOperand; dsimp only []
        rw [hslot_s, hss_sc, set?_eq_some_set hlt_af_s]
      have hm_w : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.move ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          Miri.Interpreter.runRvalue
            (annealWriteImmediate (.scalar (.fromScalarInt msc_conv))
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩)
            { m with stack := ⟨#[deinitFrameLocal tfb srcIdx hlt_sb]⟩ } := by
        rw [hm_stmt, htr_dst, htr_move]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok, hcast_dispatch,
          EStateM.bind_eq_ok (hread_s _), EStateM.bind_eq_ok (hpep_ok _)]
      exact finish_write_immediate_from_mid hframes hfr.body_eq hfr.location_eq hstate_mid rfl
        hbb hstmt hdecl_dst (himm_d_tfb.deinit_local hlt_sb) hrv_a hm_w hnew_usize
  · exact absurd (hslot_s.trans (congrArg some hss_ptr)) (hno_ptr ptrVal)

/-! ## 11. Composed `StateRelLM3_1` Statement Simulation (`step_stmt_lm3_1_state_simulation`) -/

/-- Statement forms covered by `step_stmt_lm3_1_state_simulation` across
arbitrary `StateRelLM3_1 body s m allocMap` states (including states with live
raw pointers and memory-backed locals):
* `nop`: `StatementKind.nop`
* `storageLive`: `StorageLive(loc)` (for non-address-taken `loc`)
* `storageDead`: `StorageDead(loc)` (`loc ≠ 0`, freeing any backing allocation)
* `scalarUse`: `_d = .use op` into an immediate primitive-scalar local `_d`
* `directWritePromoted`: `_d = .use op` into an address-taken / promoted
  primitive-scalar local `_d` (invalidating conflicting Tree Borrows tags)
* `rawPtrAddrOf`: `_d = &raw (const|mut) _t` (promoting immediate `_t` to a
  stack allocation)
* `rawPtrReborrow`: `_d = &raw (const|mut) _t` on an already-promoted local `_t`
  (reusing `_t`'s stack `AllocId` and minting a fresh Anneal borrow tag)
* `derefRead`: `_d = (copy|move) *_p`
* `derefWrite`: `*_p = .use op`
* `castPtrToPtr`: `_d = copy _s as *(const|mut) V` (`CastKind.PtrToPtr` on thin
  pointers)
* `binOpOffset`: `_d = Offset(copy _p, rhsOp)` (in-bounds / zero-offset)
* `placeMentionLocal`: `PlaceMention(_x)` on a live local
* `placeMentionDeref`: `PlaceMention(*_p)` on an initialized pointer local
* `rawPtrUse`: `_d = (copy|move) _s` between immediate raw-pointer locals
* `castPtrToPtrMove`: `_d = move _s as *(const|mut) V` (`CastKind.PtrToPtr` on
  thin pointers)
* `binOpOffsetMove`: `_d = Offset(move _p, rhsOp)` (in-bounds / zero-offset)
* `castExposeProvenanceScalar`: `_d = (copy|move) _s as usize`
  (`CastKind.PointerExposeProvenance`) on provenance-less raw-pointer locals.

Despite its name, this predicate is not a static typing judgment: besides types,
its constructors carry state-side conditions on `(s, m, allocMap)` (pointer
offset `0`, non-disabled permissions, in-bounds or zero `Offset` counts,
`u8`/`i8` pointees for `Offset`, thin pointees for `PtrToPtr`, unmapped
`StorageLive` targets). These conditions exclude the states where Anneal's
trusted semantics and `lean-miri` diverge (`step_deref_oob_divergence`,
`step_deref_misaligned_divergence`, `step_deref_invalid_bool_divergence`,
`step_binOp_offset_oob_dangling_miri_ub`, `step_binOp_offset_stride_divergence`,
`step_binOp_offset_neg_isize_divergence`, and the `WitLM3_1` divergence
witnesses). -/
inductive WellTypedLM3_1StateStmt
    (body : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Statement → Prop where
  | nop (span : String) :
      WellTypedLM3_1StateStmt body s m allocMap ⟨.nop, span⟩
  | storageLive (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      (∀ e ∈ allocMap, e.localIdx ≠ loc) →
      WellTypedLM3_1StateStmt body s m allocMap ⟨.storageLive loc, span⟩
  | storageDead (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      loc ≠ 0 →
      WellTypedLM3_1StateStmt body s m allocMap ⟨.storageDead loc, span⟩
  | scalarUse
      (dstIdx : Local) (op : MirAst.Operand) (dstDecl : LocalDecl) (valTy : Ty) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      IsPrimScalarTy dstDecl.ty →
      valTy.kind = dstDecl.ty.kind →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame op valTy) →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
  | directWritePromoted
      (dstIdx : Local) (op : MirAst.Operand) (dstDecl : LocalDecl) (valTy : Ty) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      IsPrimScalarTy dstDecl.ty →
      valTy.kind = dstDecl.ty.kind →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame op valTy) →
      (∃ e₀ ∈ allocMap, e₀.localIdx = dstIdx) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use op), span⟩
  | rawPtrAddrOf
      (dstIdx targetIdx : Local) (mutability : Mutability) (pointeeKind : RigidTy)
      (dstDecl targetDecl : LocalDecl) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls targetIdx = some targetDecl →
      dstDecl.ty.kind = .rawPtr mutability pointeeKind →
      IsPrimScalarTy targetDecl.ty →
      dstIdx ≠ targetIdx →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧
          IsImmediateFrameLocal topFrame targetIdx) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
  | rawPtrReborrow
      (dstIdx targetIdx : Local) (mutability : Mutability) (pointeeKind : RigidTy)
      (dstDecl targetDecl : LocalDecl) (e₀ : AllocMapEntry) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls targetIdx = some targetDecl →
      dstDecl.ty.kind = .rawPtr mutability pointeeKind →
      IsPrimScalarTy targetDecl.ty →
      dstIdx ≠ targetIdx →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame dstIdx) →
      e₀ ∈ allocMap →
      e₀.localIdx = targetIdx →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
  | derefRead
      (dstIdx ptrIdx : Local) (opKind : Place → MirAst.Operand)
      (dstDecl ptrDecl : LocalDecl) (mutability : Mutability) (span : String) :
      (opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move) →
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls ptrIdx = some ptrDecl →
      ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind →
      IsPrimScalarTy dstDecl.ty →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx) →
      (∀ ptrVal, get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
        ∀ e ∈ allocMap, e.tag = ptrVal.tag →
          get? s.frame.locals e.localIdx ≠ some .dead →
            ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧
            (∀ decl, get? body.localDecls e.localIdx = some decl →
              decl.ty.kind = dstDecl.ty.kind)) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨ptrIdx, .cons .deref .nil⟩)), span⟩
  | derefWrite
      (ptrIdx : Local) (op : MirAst.Operand) (ptrDecl : LocalDecl)
      (mutability : Mutability) (pointeeKind : RigidTy) (valTy : Ty) (span : String) :
      get? body.localDecls ptrIdx = some ptrDecl →
      ptrDecl.ty.kind = .rawPtr mutability pointeeKind →
      IsPrimScalarTy valTy →
      valTy.kind = pointeeKind →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame op valTy) →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx) →
      (∀ ptrVal e tgtDecl,
        get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
        e ∈ allocMap → e.tag = ptrVal.tag →
        get? body.localDecls e.localIdx = some tgtDecl →
        get? s.frame.locals e.localIdx ≠ some .dead →
        ptrVal.offsetBytes = 0 ∧ (e.perm = .active ∨ e.perm = .reserved) ∧
          tgtDecl.ty.kind = pointeeKind) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use op), span⟩
  | castPtrToPtr
      (dstIdx srcIdx : Local) (castTy : Ty) (dstDecl srcDecl : LocalDecl)
      (srcMut dstMut castMut : Mutability) (srcPointee dstPointee : RigidTy)
      (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcIdx = some srcDecl →
      srcDecl.ty.kind = .rawPtr srcMut srcPointee →
      dstDecl.ty.kind = .rawPtr dstMut dstPointee →
      castTy.kind = .rawPtr castMut dstPointee →
      isThinRawPtrPointee srcPointee = true →
      isThinRawPtrPointee dstPointee = true →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) →
      (∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc))) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩
  | binOpOffset
      (dstIdx ptrIdx : Local) (rhsOp : MirAst.Operand)
      (dstDecl ptrDecl : LocalDecl) (ptrMut dstMut : Mutability)
      (pointeeKind : RigidTy) (rhsTy : Ty) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls ptrIdx = some ptrDecl →
      ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind →
      dstDecl.ty.kind = .rawPtr dstMut pointeeKind →
      (pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8) →
      (rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize) →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame rhsOp rhsTy) →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx) →
      (∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc))) →
      (∀ ptrVal sc e tgtDecl,
        get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
        evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
          s.memory.callerLocals = .ok (.scalar sc) s.frame.locals →
        e ∈ allocMap → e.tag = ptrVal.tag →
        get? body.localDecls e.localIdx = some tgtDecl →
        sc.bits = 0 ∨
          (get? s.frame.locals e.localIdx ≠ some .dead ∧
            ptrVal.offsetBytes + sc.bits ≤
              (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩
  | placeMentionLocal
      (loc : Local) (decl : LocalDecl) (span : String) :
      get? body.localDecls loc = some decl →
      get? s.frame.locals loc ≠ some .dead →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.placeMention ⟨loc, .nil⟩, span⟩
  | placeMentionDeref
      (ptrIdx : Local) (ptrDecl : LocalDecl)
      (mutability : Mutability) (pointeeKind : RigidTy) (span : String) :
      get? body.localDecls ptrIdx = some ptrDecl →
      ptrDecl.ty.kind = .rawPtr mutability pointeeKind →
      IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 } →
      (∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx) →
      get? s.frame.locals ptrIdx ≠ some .uninit →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩
  | rawPtrUse
      (dstIdx srcIdx : Local) (opKind : Place → MirAst.Operand)
      (dstDecl srcDecl : LocalDecl) (srcMut dstMut : Mutability)
      (pointeeKind : RigidTy) (span : String) :
      (opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move) →
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcIdx = some srcDecl →
      srcDecl.ty.kind = .rawPtr srcMut pointeeKind →
      dstDecl.ty.kind = .rawPtr dstMut pointeeKind →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (opKind ⟨srcIdx, .nil⟩)), span⟩
  | castPtrToPtrMove
      (dstIdx srcIdx : Local) (castTy : Ty) (dstDecl srcDecl : LocalDecl)
      (srcMut dstMut castMut : Mutability) (srcPointee dstPointee : RigidTy)
      (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcIdx = some srcDecl →
      srcDecl.ty.kind = .rawPtr srcMut srcPointee →
      dstDecl.ty.kind = .rawPtr dstMut dstPointee →
      castTy.kind = .rawPtr castMut dstPointee →
      isThinRawPtrPointee srcPointee = true →
      isThinRawPtrPointee dstPointee = true →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) →
      (∀ sc, get? s.frame.locals srcIdx ≠ some (.init (.scalar sc))) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.move ⟨srcIdx, .nil⟩) castTy), span⟩
  | binOpOffsetMove
      (dstIdx ptrIdx : Local) (rhsOp : MirAst.Operand)
      (dstDecl ptrDecl : LocalDecl) (ptrMut dstMut : Mutability)
      (pointeeKind : RigidTy) (rhsTy : Ty) (span : String) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls ptrIdx = some ptrDecl →
      ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind →
      dstDecl.ty.kind = .rawPtr dstMut pointeeKind →
      (pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8) →
      (rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize) →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        WellTypedScalarOperand body topFrame rhsOp rhsTy) →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx) →
      (∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc))) →
      (∀ ptrVal sc e tgtDecl,
        get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
        evalOperand (s.frame.locals.set ptrIdx .uninit) rhsOp s.memory.borrows s.memory.globals
          body.layouts s.memory.callerLocals =
          .ok (.scalar sc) (s.frame.locals.set ptrIdx .uninit) →
        e ∈ allocMap → e.tag = ptrVal.tag →
        get? body.localDecls e.localIdx = some tgtDecl →
        sc.bits = 0 ∨
          (get? s.frame.locals e.localIdx ≠ some .dead ∧
            ptrVal.offsetBytes + sc.bits ≤
              (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat)) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.move ⟨ptrIdx, .nil⟩) rhsOp), span⟩
  | castExposeProvenanceScalar
      (dstIdx srcIdx : Local) (opKind : Place → MirAst.Operand) (castTy : Ty)
      (dstDecl srcDecl : LocalDecl) (srcMut : Mutability) (srcPointee : RigidTy)
      (span : String) :
      (opKind = MirAst.Operand.copy ∨ opKind = MirAst.Operand.move) →
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls srcIdx = some srcDecl →
      srcDecl.ty.kind = .rawPtr srcMut srcPointee →
      isThinRawPtrPointee srcPointee = true →
      dstDecl.ty.kind = .uint .usize →
      castTy.kind = .uint .usize →
      (∀ topFrame, m.stack.frames = #[topFrame] →
        IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx) →
      (∀ ptrVal, get? s.frame.locals srcIdx ≠ some (.init (.ptr ptrVal 8))) →
      WellTypedLM3_1StateStmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .pointerExposeProvenance (opKind ⟨srcIdx, .nil⟩) castTy), span⟩

/-- **`step_stmt_lm3_1_state_simulation` (`LM-3.1` Composed `StateRelLM3_1` Step)**:
every statement satisfying `WellTypedLM3_1StateStmt body s m allocMap` at the
current location of a `StateRelLM3_1`-related state steps in lockstep under
`Miri.Interpreter.Step.step` (`annealStepHooks`) and Anneal's `stepMirFn`,
landing in `StateRelLM3_1`-related post-states under an updated `allocMap'`
(or reporting undefined behavior in both machines). -/
theorem step_stmt_lm3_1_state_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hwt : WellTypedLM3_1StateStmt body s m allocMap stmt)
    (hsupply : AllocIdSupplyReady m.machine.memory) :
    ∃ allocMap' : List AllocMapEntry,
      StepRelLM3_1 body m allocMap'
        (stepMirFn body s)
        (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  cases hwt with
  | nop span =>
    exact ⟨allocMap, step_nop_lm3_1_simulation hstate hphase hbb hstmt⟩
  | storageLive loc decl span hdecl hne0 =>
    exact ⟨allocMap, step_storageLive_lm3_1_simulation hstate hphase hbb hstmt hdecl hne0⟩
  | storageDead loc decl span hdecl hne0 =>
    exact ⟨allocMap, step_storageDead_lm3_1_simulation hstate hphase hbb hstmt hdecl hne0⟩
  | scalarUse dstIdx op dstDecl valTy span hdecl_dst hdst_prim hval_kind hop himm_dst =>
    exact ⟨allocMap, step_scalar_use_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst
      hdst_prim hval_kind hop himm_dst⟩
  | directWritePromoted dstIdx op dstDecl valTy span hdecl_dst hdst_prim hval_kind hop hmem_dst =>
    exact ⟨_, step_direct_write_promoted_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst
      hdst_prim hval_kind hop hmem_dst⟩
  | rawPtrAddrOf dstIdx targetIdx mutability pointeeKind dstDecl targetDecl span
      hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm =>
    exact ⟨_, step_rawPtr_addrOf_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst hdecl_tgt
      hdst_ty htgt_ty hne himm hsupply⟩
  | rawPtrReborrow dstIdx targetIdx mutability pointeeKind dstDecl targetDecl e₀ span
      hdecl_dst hdecl_tgt hdst_ty htgt_ty hne himm_dst he₀ he₀_loc =>
    exact ⟨_, step_rawPtr_addrOf_indirect_lm3_1_simulation hstate hphase hbb hstmt hdecl_dst
      hdecl_tgt hdst_ty htgt_ty hne himm_dst he₀ he₀_loc⟩
  | derefRead dstIdx ptrIdx opKind dstDecl ptrDecl mutability span
      hopKind hdecl_dst hdecl_ptr hptr_ty hdst_prim himm hlive =>
    exact step_deref_read_simulation hstate hphase hopKind hbb hstmt hdecl_dst hdecl_ptr
      hptr_ty hdst_prim himm hlive
  | derefWrite ptrIdx op ptrDecl mutability pointeeKind valTy span
      hdecl_ptr hptr_ty hval_prim hval_kind hop himm_ptr hlive =>
    exact step_deref_write_simulation hstate hphase hbb hstmt hdecl_ptr hptr_ty
      hval_prim hval_kind hop himm_ptr hlive
  | castPtrToPtr dstIdx srcIdx castTy dstDecl srcDecl srcMut dstMut castMut
      srcPointee dstPointee span hdecl_dst hdecl_src hsrc_ty hdst_ty hcast_ty
      hsrc_thin hdst_thin himm hno_int =>
    exact ⟨allocMap, step_cast_ptrToPtr_simulation hstate hphase hbb hstmt hdecl_dst hdecl_src
      hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hno_int⟩
  | binOpOffset dstIdx ptrIdx rhsOp dstDecl ptrDecl ptrMut dstMut pointeeKind rhsTy span
      hdecl_dst hdecl_ptr hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hno_int hinb =>
    exact ⟨allocMap, step_binOp_offset_simulation hstate hphase hbb hstmt hdecl_dst hdecl_ptr
      hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hno_int hinb⟩
  | placeMentionLocal loc decl span hdecl hlive =>
    exact ⟨allocMap, step_placeMention_local_lm3_1_simulation hstate hphase hbb hstmt hdecl hlive⟩
  | placeMentionDeref ptrIdx ptrDecl mutability pointeeKind span
      hdecl_ptr hptr_ty hpk_prim himm_ptr hnot_uninit =>
    exact ⟨allocMap, step_placeMention_deref_lm3_1_simulation hstate hphase hbb hstmt
      hdecl_ptr hptr_ty hpk_prim himm_ptr hnot_uninit⟩
  | rawPtrUse dstIdx srcIdx opKind dstDecl srcDecl srcMut dstMut pointeeKind span
      hopKind hdecl_dst hdecl_src hsrc_ty hdst_ty himm =>
    exact ⟨allocMap, step_rawPtr_use_lm3_1_simulation hstate hphase hopKind hbb hstmt
      hdecl_dst hdecl_src hsrc_ty hdst_ty himm⟩
  | castPtrToPtrMove dstIdx srcIdx castTy dstDecl srcDecl srcMut dstMut castMut
      srcPointee dstPointee span hdecl_dst hdecl_src hsrc_ty hdst_ty hcast_ty
      hsrc_thin hdst_thin himm hno_int =>
    exact ⟨allocMap, step_cast_ptrToPtr_move_simulation hstate hphase hbb hstmt hdecl_dst
      hdecl_src hsrc_ty hdst_ty hcast_ty hsrc_thin hdst_thin himm hno_int⟩
  | binOpOffsetMove dstIdx ptrIdx rhsOp dstDecl ptrDecl ptrMut dstMut pointeeKind rhsTy span
      hdecl_dst hdecl_ptr hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hno_int hinb =>
    exact ⟨allocMap, step_binOp_offset_move_simulation hstate hphase hbb hstmt hdecl_dst
      hdecl_ptr hptr_ty hdst_ty hpt hrhs_ty hop_rhs himm hno_int hinb⟩
  | castExposeProvenanceScalar dstIdx srcIdx opKind castTy dstDecl srcDecl srcMut srcPointee
      span hopKind hdecl_dst hdecl_src hsrc_ty hsrc_thin hdst_ty hcast_ty himm hno_ptr =>
    exact ⟨allocMap, step_cast_expose_provenance_scalar_simulation hstate hphase hopKind
      hbb hstmt hdecl_dst hdecl_src hsrc_ty hsrc_thin hdst_ty hcast_ty himm hno_ptr⟩

/-! ## 12. Real-Step Divergence Characterizations (`LM-3.1`) -/

/-- **`step_deref_misaligned_divergence`**: in `StateRelLM3_1`-related states
where `_d = copy *_p` reads an in-bounds live allocation at an address that fails
`Size.isAligned` for the pointee's ABI alignment (e.g. `offsetBytes = 1` on a
`u64` / `*const u32` pointer), Anneal's `stepMirFn` steps normally (ignoring
`offsetBytes` and alignment to return the target local's scalar), whereas
`lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) reports
`StepError.undefinedBehavior` (`step_deref_misaligned_miri_ub`). -/
theorem step_deref_misaligned_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    {localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hfind_la : m.machine.memory.live.find? (fun x => x.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hinbounds : ptrVal.offsetBytes + (translateTy dstDecl.ty body.layouts).layout.size.bytes.toNat ≤
      localAlloc.allocation.byteSize.bytes.toNat)
    (hmis : (Miri.ABI.Size.ofBytes
        (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes)).isAligned
      (translateTy dstDecl.ty body.layouts).layout.align.abi = .ok false)
    (hperm : e.perm ≠ .disabled)
    {sc : MirAst.ScalarInt}
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m' msg,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior msg)) := by
  refine ⟨?_, step_deref_misaligned_miri_ub hstate (opKind := MirAst.Operand.copy) (Or.inl rfl)
    hbb hstmt hdecl_dst hdecl_ptr hdst_prim hptr_ty himm_ptr hslot_p he htag hfind_la hinbounds
    hmis⟩
  obtain ⟨_, _, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  have hlookup := (halloc.borrow_sync e he).2
  rw [htag] at hlookup
  obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
  have hread : evalOperand s.frame.locals (.copy ⟨ptrIdx, .cons .deref .nil⟩)
      s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
      .ok (.scalar sc) s.frame.locals := by
    unfold evalOperand; dsimp only []; rw [hslot_p]; dsimp only []; rw [hlookup]; dsimp only []
    cases hp : e.perm with
    | disabled => exact absurd hp hperm
    | _ => simp only [htarget]; rfl
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  unfold evalStmt evalRvalue; dsimp only []; rw [hread]; dsimp only []
  have hset := set?_eq_some_set hlt_af_d (LocalSlot.init (.scalar sc))
  have hget_set : get? (s.frame.locals.set dstIdx (.init (.scalar sc))) dstIdx =
      some (.init (.scalar sc)) := by
    rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
  cases hb : s.memory.borrows with
  | nil =>
    simp only [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
  | cons b₁ rest =>
    cases rest with
    | nil =>
      simp only [hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | cons b₂ rest' =>
      simp only [hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩

/-- **`step_deref_invalid_bool_divergence`**: in `StateRelLM3_1`-related states
where `_p : *(const|mut) bool` at `offsetBytes = 0` points to a 1-byte `u8`/`i8`
stack local holding `sc` with `2 ≤ sc.bits` (e.g. `2_u8` cast via `PtrToPtr` to
`*const bool`), executing `_d = copy *_p` diverges:
1. Anneal's `stepMirFn` takes a normal step storing `.init (.scalar sc)` in `_d`
   without checking `bool` bit-pattern validity (`0 | 1`); while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) rejects the
   invalid `bool` bit pattern with `StepError.undefinedBehavior "reading invalid value"`. -/
theorem step_deref_invalid_bool_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl tgtDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_bool : dstDecl.ty.kind = .bool)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_byte : tgtDecl.ty.kind = .uint .u8 ∨ tgtDecl.ty.kind = .int .i8)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinvalid : 2 ≤ sc.bits)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) := by
  have hdst_prim : IsPrimScalarTy dstDecl.ty := Or.inl hdst_bool
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hread : evalOperand s.frame.locals (.copy ⟨ptrIdx, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only []; rw [hslot_p]; dsimp only []; rw [hlookup]; dsimp only []
      cases hp : e.perm with
      | disabled => exact absurd hp hperm
      | _ => simp only [htarget]; rfl
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []; rw [hread]; dsimp only []
    have hset := set?_eq_some_set hlt_af_d (LocalSlot.init (.scalar sc))
    have hget_set : get? (s.frame.locals.set dstIdx (.init (.scalar sc))) dstIdx =
        some (.init (.scalar sc)) := by
      rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
    cases hb : s.memory.borrows with
    | nil =>
      simp only [hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | cons b₁ rest =>
      cases rest with
      | nil =>
        simp only [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_ne
        | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
        | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | cons b₂ rest' =>
        simp only [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_ne
        | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
        | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
  · have himm_p := himm_ptr tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (.copy ⟨ptrIdx, .cons .deref .nil⟩) span m
    obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
      hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hfra.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
    have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
      hstate_a.cache_layout rfl hdecl_ptr hlt_pa
    obtain ⟨tfb', hframes_b, _, _, hfrb, _, _, _, _, _, halloc_b, _⟩ := id hstate_b
    injection hframes_b with hfb₁; injection hfb₁ with hfb₂; subst hfb₂
    have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
        translateTy dstDecl.ty body.layouts := hdst_prim.translateTy_layoutIdx body.layouts
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e' he'
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      have hop_ptr := annealEvalOperand_deref_live (opKind := MirAst.Operand.copy) (Or.inl rfl)
        (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      have hmptr_zero : mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId) := by
        rw [hmptr_off, hoff0, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
      obtain ⟨_, _, _, _, hpow_dst, _⟩ := hdst_prim.size_align_ok body.layouts
      have hmis0 : annealOffsetMisalignment mptr.offset
          (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok none := by
        rw [hlay0_eq, hmptr_zero]
        exact annealOffsetMisalignment_stackBase_eq_none e'.allocId _ hpow_dst
      have hder_ok := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hdst_prim mptr hmis0
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      rw [hlay0_eq] at hder_ok
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
            some (.concrete e'.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_zero ⊢
        subst hprov_eq hmptr_zero; rfl
      rw [hmptr_opt] at hder_ok
      obtain ⟨slot_t, mls_t, _, _, hslot_t, hmls_t, _, hloc_t⟩ := hfrb.lookup_local hdecl_tgt
      have hst_eq : slot_t = .init (.scalar sc) := Option.some.inj (hslot_t.symm.trans htarget)
      subst hst_eq
      obtain ⟨⟨lay_t, hlay_t⟩, _, hsh_fn⟩ :=
        (halloc_b.local_alloc_sync tfb rfl e' he').1 _ hslot_t (by simp)
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_fn tgtDecl hdecl_tgt
      have hmls_t_eq : mls_t = ⟨.live (.indirect (stackAllocPlace e'.allocId)), lay_t⟩ :=
        Option.some.inj (hmls_t.symm.trans hlay_t)
      have hsz_tgt_1 : (translateTy tgtDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 1 := by
        rcases htgt_byte with hk | hk <;> (unfold translateTy; rw [hk]; rfl)
      have hsz_dst_1 : (translateTy dstDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 1 := by
        unfold translateTy; rw [hdst_bool]; rfl
      have hty_dst_1 : (translateTy dstDecl.ty body.layouts).ty = 1 := by
        unfold translateTy encodeTyId; rw [hdst_bool]
      obtain ⟨_, hsc_spec⟩ := hloc_t.indirect_stackAllocPlace_spec hmls_t_eq hbase hfind_la
        (halloc_b.live_key_unique e' he') (by rw [hsz_tgt_1]; decide)
      obtain ⟨hsz_sc, _, _, msc, hrel_sc, hread_sc⟩ := hsc_spec sc rfl
      rw [hsz_tgt_1, ← hsz_dst_1] at hread_sc
      have hread_m := annealReadMemoryPlace_zero_offset_eq hdst_prim hid_lt hbase hfind_la
        (hshape_la.byteSize_eq.trans (hsz_tgt_1.trans hsz_dst_1.symm))
        (borTag := borTag) (st := { m with stack := ⟨#[tfb]⟩ })
      rw [hread_sc, hty_dst_1] at hread_m
      dsimp only [] at hread_m
      have hval_false : annealValidateScalarForTyId 1 (.fromScalarInt msc) = false := by
        have hsz1 : sc.sizeBytes = 1 := by
          rw [hsz_tgt_1] at hsz_sc
          have hb : (1 : UInt64) = UInt64.ofNat sc.sizeBytes := congrArg Miri.ABI.Size.bytes hsz_sc
          rcases hrel_sc.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb ⊢ <;>
            first | rfl | cases hb
        have hlt256 : sc.bits < 256 := by
          have hc := hrel_sc.canonical; rw [hsz1] at hc; simpa [scalarModulus] using hc
        have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
            .ok msc := rfl
        unfold annealValidateScalarForTyId
        rw [hsi]; dsimp only []
        rw [hrel_sc.size_eq, hrel_sc.data_eq, hsz1]
        have hsz_b : (translateSizeBytes 1 == Miri.ABI.Size.ofBytes 1) = true := rfl
        have hbv_nat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hsz_b, Bool.true_and, hbv_nat]
        change (sc.bits == 0 || sc.bits == 1) = false
        rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
        exact ⟨by omega, by omega⟩
      simp only [hval_false, Bool.false_eq_true, ↓reduceIte] at hread_m
      have hop_ok : annealEvalOperand body.localDecls body.layouts
          (translateOperand (.copy ⟨ptrIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
              some (.concrete e'.allocId borTag)⟩, .none, none⟩,
            translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = { localId := dstIdx, projection := #[] } := rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
          m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "reading invalid value")) := by
        rw [hm_stmt, htr_dst]
        unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
        dsimp only [annealReadImmediate]
        rw [EStateM.bind_eq_error hread_m]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

private theorem checkedBounds_neg_inbounds
    (target : Miri.Memory.PointerArithmetic)
    (id : Miri.Memory.AllocId)
    (allocationSize offset : Miri.ABI.Size)
    (delta : Int)
    (msg : Miri.Memory.CheckInAllocMsg)
    (hlo : -(2 ^ 63 : Int) ≤ delta)
    (hneg : delta < 0)
    (hlo_off : (-delta).toNat ≤ offset.bytes.toNat)
    (hhi_off : offset.bytes.toNat ≤ allocationSize.bytes.toNat) :
    Miri.Memory.checkedBounds target id allocationSize offset delta msg = .ok () := by
  have hhi : delta < 2 ^ 63 := by omega
  have hfits : fitsI64Pub delta = true := fitsI64Pub_eq_true_of_bounds hlo hhi
  change (do
    if !fitsI64Pub delta then
      throw (Miri.Memory.AccessError.signedSizeOutsideI64 delta)
    let offsetNat := offset.bytes.toNat
    let allocationNat := allocationSize.bytes.toNat
    let inBounds := if delta >= 0 then
        offsetNat + delta.toNat ≤ allocationNat
      else
        let amount := (-delta).toNat
        amount ≤ offsetNat && offsetNat ≤ allocationNat
    if !inBounds then
      let signedOffset ←
        (target.signExtendToTargetIsize offset.bytes).mapError
          Miri.Memory.AccessError.pointerArithmetic
      throw (Miri.Memory.AccessError.pointerOutOfBounds id allocationSize
        signedOffset.toInt delta msg)) = .ok ()
  have hnot_ge : ¬ (delta ≥ 0) := by omega
  simp only [hfits, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hnot_ge,
    hlo_off, hhi_off, decide_true, Bool.and_self, pure, Except.pure]

private theorem ptrOffsetInbounds_neg_var_live_ok
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes negBytes : Nat) (delta64 : Int64)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hpos : 0 < negBytes)
    (hneg_lt : negBytes < 2 ^ 32)
    (hdelta_int : delta64.toInt = -(negBytes : Int))
    (hdelta_u64 : UInt64.ofNat negBytes + delta64.toUInt64 = 0)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hlo_off : negBytes ≤ offsetBytes)
    (hhi_off : offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      delta64
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .ok ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat (offsetBytes - negBytes)),
        some (.concrete allocId borTag)⟩ := by
  unfold Miri.Interpreter.ptrOffsetInbounds Miri.Memory.checkPtrAccessSigned
  rw [hdelta_int]
  have h63 : negBytes < 9223372036854775808 := Nat.lt_trans hneg_lt (by decide)
  have hlo : -(2 ^ 63 : Int) ≤ -(negBytes : Int) := by
    have hlt : (negBytes : Int) < (9223372036854775808 : Int) := Int.ofNat_lt.mpr h63
    have h263 : (2 ^ 63 : Int) = 9223372036854775808 := by decide
    omega
  have hhi : -(negBytes : Int) < 2 ^ 63 := by
    have h263 : (0 : Int) < 2 ^ 63 := by decide
    omega
  have hne0 : -(negBytes : Int) ≠ 0 := by omega
  have hres := PtrRel.resolvePtr_concrete_eq allocId borTag offsetBytes hid hoff hbase (-(negBytes : Int))
  have hlook : annealLookupAlloc mach allocId =
      .ok { size := localAlloc.allocation.byteSize
            align := localAlloc.allocation.align
            kind := .liveData
            mutability := localAlloc.allocation.mutability } := by
    unfold annealLookupAlloc; rw [hlive]
  rw [checkAndDerefPtr_nonzero_lookup_ok _ _ _ _ _ _ _ _ _ _ _ _ hlo hhi hne0 hres hlook]
  have hoff_lt64 : offsetBytes < 2 ^ 64 :=
    Nat.lt_trans hoff (Nat.pow_lt_pow_right (by decide) (by decide))
  have hoff_bytes :
      (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes)).bytes.toNat = offsetBytes :=
    UInt64.toNat_ofNat_of_lt hoff_lt64
  have hcb := checkedBounds_neg_inbounds annealPointerArithmetic allocId
    localAlloc.allocation.byteSize (Miri.ABI.Size.ofBytes (UInt64.ofNat offsetBytes))
    (-(negBytes : Int)) .inboundsPointerArithmetic hlo (by omega)
    (by rw [hoff_bytes, Int.neg_neg, Int.toNat_natCast]; exact hlo_off)
    (by rw [hoff_bytes]; exact hhi_off)
  rw [hcb]
  simp only [Except.mapError, bind, Except.bind, pure, Except.pure,
    Miri.Memory.Pointer.wrappingSignedOffset, wrappingOffset_annealPointerArithmetic_eq,
    Miri.ABI.Size.ofBytes]
  have hoff_split :
      UInt64.ofNat offsetBytes = UInt64.ofNat (offsetBytes - negBytes) + UInt64.ofNat negBytes := by
    have heq : offsetBytes = (offsetBytes - negBytes) + negBytes := by omega
    conv => lhs; rw [heq]
    exact UInt64.ofNat_add (offsetBytes - negBytes) negBytes
  rw [hoff_split, ← UInt64.add_assoc, UInt64.add_assoc _ (UInt64.ofNat negBytes) _,
    hdelta_u64, UInt64.add_zero]

/-- In-bounds `-1`-byte `Miri.Interpreter.ptrOffsetInbounds` (`1 ≤ offsetBytes ≤ alloc.byteSize`)
on a live stack allocation succeeds and steps the pointer backward to
`annealStackBaseAddr allocId + UInt64.ofNat (offsetBytes - 1)`. -/
theorem ptrOffsetInbounds_neg_one_live_ok
    {mach : AnnealMachine}
    (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
    (offsetBytes : Nat)
    (localAlloc :
      Miri.Memory.LocalAllocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)
        Miri.Memory.MiriMemoryKind)
    (hid : allocId.value.toNat < 2 ^ 32)
    (hoff : offsetBytes < 2 ^ 32)
    (hbase : mach.lookupBaseAddr allocId = some (annealStackBaseAddr allocId))
    (hlive : mach.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc))
    (hlo_off : 1 ≤ offsetBytes)
    (hhi_off : offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat) :
    Miri.Interpreter.ptrOffsetInbounds
      annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat offsetBytes),
        some (.concrete allocId borTag)⟩
      (-1 : Int64)
      (annealResolvePtr mach)
      (annealLookupAlloc mach) =
      .ok ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId + UInt64.ofNat (offsetBytes - 1)),
        some (.concrete allocId borTag)⟩ := by
  have hi64 : (-1 : Int64).toInt = -((1 : Nat) : Int) := by
    rw [Int64.toInt_neg, Int64.toInt_one]
    exact Int.bmod_eq_of_le (by decide) (by decide)
  have hu64 : UInt64.ofNat 1 + (-1 : Int64).toUInt64 = 0 := by
    rw [Int64.toUInt64_neg]
    exact UInt64.add_right_neg 1
  exact ptrOffsetInbounds_neg_var_live_ok allocId borTag offsetBytes 1 (-1 : Int64) localAlloc
    hid hoff (by decide) (by decide) hi64 hu64 hbase hlive hlo_off hhi_off

private theorem mulWithOverflow_one_usize_stride_eight_eq
    {rightInt : Miri.Memory.ScalarInt}
    (hrel : ScalarRel ⟨1, 8⟩ rightInt) :
    ∃ scaledInt : Miri.Memory.ScalarInt,
      Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨rightInt, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
        ⟨Miri.Memory.ScalarInt.ofUInt64 8, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
        .ok (.withOverflow scaledInt false) ∧
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) scaledInt).toTargetIsize
        annealPointerArithmetic.pointerSize =
        .ok (Int64.ofInt 8) := by
  have hrel8 : ScalarRel ⟨8, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 8) :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  have hbin : Miri.Interpreter.IntegerOps.binary .MulWithOverflow
      ⟨rightInt, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩
      ⟨Miri.Memory.ScalarInt.ofUInt64 8, ⟨Miri.ABI.Size.ofBytes 8, .usize⟩⟩ =
      arithmeticInt .MulWithOverflow 1 8 ⟨translateSizeBytes 8, .usize⟩ := by
    have hb := integerOps_binary_sameType_eq hrel hrel8 rfl .usize .MulWithOverflow rfl
    exact hb
  have hv8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨scaledInt, lossy, htr, hrel_s, hovf⟩ := truncateInt_spec hv8 .usize 8
  have hmod : ((8 : Int) % (2 : Int) ^ (8 * 8)).toNat = 8 := by decide
  rw [hmod] at hrel_s
  have hcan_rep : canRepresentInt Miri.MIR.IntegerKind.usize.signed 8 8 = true := by decide
  rw [hcan_rep, Bool.not_true] at hovf
  have harith : arithmeticInt .MulWithOverflow 1 8
      ⟨translateSizeBytes 8, .usize⟩ = .ok (.withOverflow scaledInt false) := by
    rw [arithmeticInt_nonDivRem_eq .MulWithOverflow 1 8 8 .usize rfl rfl]
    simp only [Int.one_mul, htr, scalarResultInt, hovf, Miri.MIR.BinOp.isUnchecked,
      Miri.MIR.BinOp.isOverflowing, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
  refine ⟨scaledInt, ?_, ?_⟩
  · rw [hbin]; exact harith
  · have hp_sz : annealPointerArithmetic.pointerSize = Miri.ABI.Size.ofBytes 8 := rfl
    have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) scaledInt).toScalarInt =
        .ok scaledInt := rfl
    have hbz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
    have hsz8 : Miri.ABI.Size.ofBytes 8 =
        translateSizeBytes (⟨8, 8⟩ : MirAst.ScalarInt).sizeBytes := rfl
    have htb : scaledInt.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 8) := by
      rw [hsz8]; exact hrel_s.toBits_eq
    have hse : (Miri.ABI.Size.ofBytes 8).signExtend (BitVec.ofNat 128 8) = .ok (8 : Int) := by
      rw [hsz8, size_signExtend_translateSizeBytes hv8]
      have hbv := bitVec_ofNat_toNat_of_valid hv8 hrel_s.canonical
      rw [hbv]; decide
    unfold Miri.Memory.Scalar.toTargetIsize Miri.Memory.Scalar.toInt Miri.Memory.Scalar.toBits
    simp only [hp_sz, hbz, Bool.false_eq_true, ↓reduceIte, hsi, htb, hse,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    rfl

private theorem mulWithOverflow_neg_one_isize_stride_one_eq
    {rightInt : Miri.Memory.ScalarInt}
    (hrel : ScalarRel ⟨2 ^ 64 - 1, 8⟩ rightInt) :
    ∃ scaledInt : Miri.Memory.ScalarInt,
      Miri.Interpreter.IntegerOps.binary .MulWithOverflow
        ⟨rightInt, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩
        ⟨Miri.Memory.ScalarInt.ofUInt64 1, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩ =
        .ok (.withOverflow scaledInt false) ∧
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) scaledInt).toTargetIsize
        annealPointerArithmetic.pointerSize =
        .ok (-1 : Int64) := by
  have hrel1 : ScalarRel ⟨1, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 1) :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  have hbin : Miri.Interpreter.IntegerOps.binary .MulWithOverflow
      ⟨rightInt, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩
      ⟨Miri.Memory.ScalarInt.ofUInt64 1, ⟨Miri.ABI.Size.ofBytes 8, .isize⟩⟩ =
      arithmeticInt .MulWithOverflow (-1) 1 ⟨translateSizeBytes 8, .isize⟩ := by
    have hb := integerOps_binary_sameType_eq hrel hrel1 rfl .isize .MulWithOverflow rfl
    have hdec_l : decodeBitsInt Miri.MIR.IntegerKind.isize.signed 8 (2 ^ 64 - 1) = -1 := by decide
    have hdec_r : decodeBitsInt Miri.MIR.IntegerKind.isize.signed 8 1 = 1 := rfl
    dsimp only [] at hb
    rw [hdec_l, hdec_r] at hb
    exact hb
  have hv8 : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨scaledInt, lossy, htr, hrel_s, hovf⟩ := truncateInt_spec hv8 .isize (-1)
  have hmod : (((-1 : Int) % (2 : Int) ^ (8 * 8)).toNat) = 2 ^ 64 - 1 := by decide
  rw [hmod] at hrel_s
  have hcan_rep : canRepresentInt Miri.MIR.IntegerKind.isize.signed 8 (-1) = true := by decide
  rw [hcan_rep, Bool.not_true] at hovf
  have harith : arithmeticInt .MulWithOverflow (-1) 1
      ⟨translateSizeBytes 8, .isize⟩ = .ok (.withOverflow scaledInt false) := by
    rw [arithmeticInt_nonDivRem_eq .MulWithOverflow (-1) 1 8 .isize rfl rfl]
    simp only [Int.mul_one, htr, scalarResultInt, hovf, Miri.MIR.BinOp.isUnchecked,
      Miri.MIR.BinOp.isOverflowing, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
      bind, Except.bind, pure, Except.pure]
  refine ⟨scaledInt, ?_, ?_⟩
  · rw [hbin]; exact harith
  · have hp_sz : annealPointerArithmetic.pointerSize = Miri.ABI.Size.ofBytes 8 := rfl
    have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) scaledInt).toScalarInt =
        .ok scaledInt := rfl
    have hbz : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := rfl
    have hsz8 : Miri.ABI.Size.ofBytes 8 =
        translateSizeBytes (⟨2 ^ 64 - 1, 8⟩ : MirAst.ScalarInt).sizeBytes := rfl
    have htb : scaledInt.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 (2 ^ 64 - 1)) := by
      rw [hsz8]; exact hrel_s.toBits_eq
    have hse : (Miri.ABI.Size.ofBytes 8).signExtend (BitVec.ofNat 128 (2 ^ 64 - 1)) =
        .ok (-1 : Int) := by
      rw [hsz8, size_signExtend_translateSizeBytes hv8]
      have hbv := bitVec_ofNat_toNat_of_valid hv8 hrel_s.canonical
      rw [hbv]; decide
    unfold Miri.Memory.Scalar.toTargetIsize Miri.Memory.Scalar.toInt Miri.Memory.Scalar.toBits
    simp only [hp_sz, hbz, Bool.false_eq_true, ↓reduceIte, hsi, htb, hse,
      Except.mapError, bind, Except.bind, pure, Except.pure]
    rfl

private theorem step_binOp_offset_divergent_ok
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl : LocalDecl}
    {ptrMut dstMut : Mutability} {pointeeKind : RigidTy} {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hrhs_prim : IsPrimScalarTy rhsTy)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {sc : MirAst.ScalarInt}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (nextPtr : Miri.Memory.Pointer AnnealProv → Miri.Memory.Pointer AnnealProv)
    (hbin : ∀ mptr msc tfc,
      PtrRel allocMap ptrVal mptr →
      ScalarRel sc msc →
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks body.localDecls body.layouts)
        () .Offset
        ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
          translateTy ptrDecl.ty body.layouts⟩
        ⟨.scalar (.fromScalarInt msc), translateTy rhsTy body.layouts⟩
        { m with stack := ⟨#[tfc]⟩ } =
        .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout (nextPtr mptr)),
          translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tfc]⟩ }) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits } 8)))
          s.memory) ∧
    ∃ m' tf' mptr,
      PtrRel allocMap ptrVal mptr ∧
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout (nextPtr mptr))))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, hbor, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_ptr⟩ := himm tf hframes
  have hop_tf := hop_rhs tf hframes
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
  have hnot_dst : ∀ d ∈ allocMap, d.localIdx ≠ dstIdx :=
    hstate.immediate_not_in_allocMap hframes hslot_d hsd_ne himm_dst
  have hbor_inv := invalidateConflictingBorrows_eq_of_not_mem hbor dstIdx none hnot_dst
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; dsimp only []
    rw [evalRvalue_binOp_offset_scalarOperand_eq hop_tf s.frame.locals s.memory
      ptrIdx ptrVal hptr_slot, hrhs_eval]
    dsimp only []; rw [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit =>
      simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
    | init _ =>
      simp only [set?_eq_some_set hlt_af_d, hprot, hbor_inv]
      congr 2; generalize s.memory = mem at hprot ⊢; cases mem; dsimp at hprot ⊢; subst hprot; rfl
  · have hm_stmt := evalStatement_assign_binOp_offset_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (.copy ⟨ptrIdx, .nil⟩) rhsOp span m
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval : annealEvalPlace body.localDecls body.layouts (translatePlace ⟨dstIdx, .nil⟩) m =
        .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[cacheFrameLocalLayout tf dstIdx hlt_d
              (translateTy dstDecl.ty body.layouts)]⟩ } :=
      annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
      hstate.cache_layout hframes hdecl_dst hlt_d
    have hop_tfa := hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ :=
      hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_p_tfa : IsImmediateFrameLocal tfa ptrIdx :=
      himm_ptr.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)
    let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
    have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
      hstate_a.cache_layout rfl hdecl_ptr hlt_pa
    have hop_tfb := hop_tfa.of_cacheFrameLocalLayout ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_p.symm.trans hptr_slot)
    rcases hloc_p.rawPtr_immediate_cases hptr_ty (himm_p_tfa mls_p hmls_p) with
      ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, _, h1, _, _, _⟩ | ⟨ptrVal', mptr, hsp_ptr, hptrRel, hmp_ptr⟩
    · rw [hsp_eq] at h1; cases h1
    · rw [hsp_eq] at h1; cases h1
    · rw [hsp_eq] at h1; cases h1
    · rw [hsp_eq] at hsp_ptr
      injection hsp_ptr with hp1; injection hp1 with hpv_eq; subst hpv_eq
      have hmls_p' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      have hlhs_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_p' hcache_p
      have hread_lhs : annealReadImmediate
          ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
            translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } =
          .ok ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            translateTy ptrDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := rfl
      rcases evalOperand_scalar_lm3_1_simulation hstate_b rfl hop_tfb hrhs_prim none with
        ⟨_, _, hrhs_ub, _⟩ |
        ⟨sc', msc, tfc, hrhs_ok, hm_rhs_ok, hstate_c, hrel_imm, hloc_id_c, htfc_preserve⟩
      · rw [hrhs_eval] at hrhs_ub; cases hrhs_ub
      · rw [hrhs_eval] at hrhs_ok
        injection hrhs_ok with hv_eq _; injection hv_eq with hsc_eq; subst hsc_eq
        have hrel_sc : ScalarRel sc msc := by cases hrel_imm with | scalar _ _ hr _ _ _ => exact hr
        have hbin_ok := hbin mptr msc tfc hptrRel hrel_sc
        have hlay_eq : translateTy ptrDecl.ty body.layouts = translateTy dstDecl.ty body.layouts := by
          unfold translateTy encodeTyId; rw [hptr_ty, hdst_ty]
        have hassert_ok : assertRvalueLayoutPub (translateTy ptrDecl.ty body.layouts)
            (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfc]⟩ } =
            .ok () { m with stack := ⟨#[tfc]⟩ } := by
          unfold assertRvalueLayoutPub; simp [hlay_eq, pure, EStateM.pure]
        have hfr_c := hstate_c.frame_rel_singleton rfl
        obtain ⟨_, mls_dc, _, hlt_dc, _, hmls_dc, _, _⟩ := hfr_c.lookup_local hdecl_dst
        have hd_tfb : (tfb.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
            some mls_d.value := by
          simp only [tfb, tfa, cacheFrameLocalLayout]
          by_cases hpd : ptrIdx = dstIdx
          · subst hpd; simp [Array.getElem?_set_self, Array.getElem_set_self, hmls_d_eq]
          · rw [Array.getElem?_set_ne _ hpd, Array.getElem?_set_self]; simp [hmls_d_eq]
        have hd_Val : mls_dc.value = mls_d.value := by
          have hp_c := htfc_preserve dstIdx; rw [hd_tfb, hmls_dc] at hp_c; injection hp_c
        obtain ⟨oldImm, hmd_imm⟩ : ∃ oldImm, mls_d.value = .live (.immediate oldImm) := by
          rcases hloc_d.rawPtr_immediate_cases hdst_ty (himm_dst mls_d hmls_d) with
            ⟨hsd_dead, _⟩ | ⟨_, hm⟩ | ⟨_, _, _, _, _, hm⟩ | ⟨_, _, _, _, hm⟩
          · exact absurd hsd_dead hsd_ne
          · exact ⟨_, hm⟩
          · exact ⟨_, hm⟩
          · exact ⟨_, hm⟩
        have hdc_live : tfc.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_dc.layout⟩ := by
          rw [hmls_dc]; rcases mls_dc with ⟨vd, ld⟩; dsimp only at hd_Val; rw [hd_Val, hmd_imm]
        have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_live
        have hw_ok := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout (nextPtr mptr)))
          (m := { m with stack := ⟨#[tfc]⟩ }) (id0 := tfc.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
        have hloc_id_tf : tfc.localsIdentity = tf.localsIdentity := hloc_id_c
        rw [hloc_id_tf] at hw_ok
        have htr_lhs : translateOperand (.copy ⟨ptrIdx, .nil⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt
              ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
            ({ m with stack := ⟨#[{ tfc with
                locals := tfc.locals.set dstIdx
                  { tfc.locals[dstIdx]'hlt_dc with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout (nextPtr mptr)))) }
                  hlt_dc }]⟩ }, .ok ()) := by
          rw [hm_stmt, htr_lhs]
          unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
            EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_ok hm_rhs_ok,
            EStateM.bind_eq_ok hbin_ok, EStateM.bind_eq_ok hassert_ok]
          dsimp only []
          rw [hw_ok]
          simp only [hloc_id_tf]
        have hstep_m := miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt
          hm_ok rfl hfr_c.location_eq
        refine ⟨_, _, mptr, hptrRel, hstep_m, rfl, ?_⟩
        simp [Array.getElem?_set_self]

/-- **`step_binOp_offset_stride_divergence`**: for a non-byte pointee type
(`*(const|mut) u64`, stride `8` bytes) at `offsetBytes = 0` targeting a live
8-byte `u64` local `e.localIdx`, executing `_d = Offset(copy _p, rhsOp)` with
`rhsOp` evaluating to `1_usize` (`⟨1, 8⟩`) diverges in the byte offset written
to `_d`:
1. Anneal's `stepMirFn` stores `.ptr { ptrVal with offsetBytes := 1 } 8`
   (adding the unscaled element count `1` directly to `offsetBytes`); while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) multiplies
   `1` by `sizeof::<u64>() = 8` and stores a pointer at byte offset
   `annealStackBaseAddr e.allocId + 8` (one-past-the-end of the 8-byte `u64`
   allocation). -/
theorem step_binOp_offset_stride_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl tgtDecl : LocalDecl}
    {ptrMut dstMut : Mutability} {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut (.uint .u64))
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut (.uint .u64))
    (hrhs_ty : rhsTy.kind = .uint .usize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar ⟨1, 8⟩) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he_mem : e ∈ allocMap)
    (he_tag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_ty : tgtDecl.ty.kind = .uint .u64)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx (.init (.ptr { ptrVal with offsetBytes := 1 } 8)))
          s.memory) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + 8),
              .concrete e.allocId borTag⟩)))) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
  have ht_ne : slot_t ≠ .dead := fun hd => htgt_live (hslot_t.trans (congrArg some hd))
  obtain ⟨_, _, hsh_fn⟩ := (halloc.local_alloc_sync tf hframes e he_mem).1 slot_t hslot_t ht_ne
  obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_fn tgtDecl hdecl_tgt
  obtain ⟨hid_lt, _, hbase⟩ := halloc.base_addr_valid e he_mem
  have hsz_tgt_8 : localAlloc.allocation.byteSize.bytes.toNat = 8 := by
    rw [hshape_la.byteSize_eq]; unfold translateTy; rw [htgt_ty]; rfl
  have hrhs_prim : IsPrimScalarTy rhsTy := Or.inr (Or.inr (Or.inr ⟨.usize, hrhs_ty⟩))
  let nextPtr : Miri.Memory.Pointer AnnealProv → Miri.Memory.Pointer AnnealProv :=
    fun mptr => ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId + 8), mptr.provenance⟩
  have hdiv := step_binOp_offset_divergent_ok hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hrhs_prim hop_rhs himm hptr_slot hrhs_eval hdst_live nextPtr
    (fun mptr msc tfc hptrRel hrel_sc => by
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, e', he'_mem, he'_tag, rfl⟩ := hptrRel
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he'_mem he_mem (he'_tag.trans he_tag.symm)
      subst he_eq
      obtain ⟨scaledInt, hmul, htisize⟩ := mulWithOverflow_one_usize_stride_eight_eq hrel_sc
      have hp_tr : translateTy ptrDecl.ty body.layouts =
          { ty := 73, layout := pointerLayoutData false } := by
        unfold translateTy encodeTyId; rw [hptr_ty]; rfl
      have hr_tr : translateTy rhsTy body.layouts =
          { ty := 25, layout := scalarLayoutData 8 false } := by
        unfold translateTy encodeTyId; rw [hrhs_ty]; rfl
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat 0),
            some (.concrete e'.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
        rw [hoff0] at hmptr_off; subst hprov_eq hmptr_off; rfl
      have hpoff := ptrOffsetInbounds_live_inbounds_ok e'.allocId borTag 0 8 localAlloc
        hid_lt (by decide) (by decide) hbase hfind_la (by omega)
      have htb : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 1) := by
        have hsz : Miri.ABI.Size.ofBytes 8 =
            translateSizeBytes (⟨1, 8⟩ : MirAst.ScalarInt).sizeBytes := rfl
        rw [hsz]; exact hrel_sc.toBits_eq
      have hbin_eq : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
          ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            { ty := 73, layout := pointerLayoutData false }⟩
          ⟨.scalar (.fromScalarInt msc),
            { ty := 25, layout := scalarLayoutData 8 false }⟩
          { m with stack := ⟨#[tfc]⟩ } =
          annealPointerBinary body.layouts .Offset
            ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
              { ty := 73, layout := pointerLayoutData false }⟩
            ⟨.scalar (.fromScalarInt msc),
              { ty := 25, layout := scalarLayoutData 8 false }⟩
            { m with stack := ⟨#[tfc]⟩ } := by
        have hf := congrFun (scalarOps_binary_def
          (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
          ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            { ty := 73, layout := pointerLayoutData false }⟩
          ⟨.scalar (.fromScalarInt msc),
            { ty := 25, layout := scalarLayoutData 8 false }⟩) { m with stack := ⟨#[tfc]⟩ }
        rw [hf]; unfold annealScalarOpsHooks
        simp only [classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
      rw [hp_tr, hr_tr, hbin_eq]
      unfold annealPointerBinary
      have hpt_lay : layoutOfEncodedTyId 23 body.layouts =
          { ty := 23, layout := scalarLayoutData 8 false } := rfl
      have hisSized : (!(({ ty := 23, layout := scalarLayoutData 8 false } :
          Miri.Interpreter.LocalLayout).layout.isSized &&
          decide (({ ty := 23, layout := scalarLayoutData 8 false } :
            Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
      have hfrom8 : Miri.Memory.Scalar.fromInt (Prov := AnnealProv) 8 (Miri.ABI.Size.ofBytes 8) =
          .ok (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 8)) := rfl
      have hsz8 : (scalarLayoutData 8 false).size = Miri.ABI.Size.ofBytes 8 := rfl
      have hsz_pt : Int.ofNat (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
      have hisSigned : (scalarLayoutData 8 false).backendRepr.isSigned = .ok false := rfl
      have hlt0_false : decide ((Int64.ofInt 8).toInt < 0) = false := rfl
      simp only [show (Miri.MIR.BinOp.Offset != .Offset) = false from rfl, Bool.false_eq_true,
        ↓reduceIte, show (Miri.Interpreter.Immediate.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)).toScalar =
          .ok (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) from rfl,
        scalar_fromPointer_toPointer_eq mptr, rawPtrPointeeEncodedTyId?, hpt_lay,
        hisSized, classifyEncodedTyId,
        show (Miri.Interpreter.Immediate.scalar
          (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc)).toScalar =
          .ok (.fromScalarInt msc) from rfl,
        show (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
          .ok msc from rfl]
      simp only [hsz8, hsz_pt, htb, hfrom8,
        show (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv)
          (Miri.Memory.ScalarInt.ofUInt64 8)).toScalarInt =
          .ok (Miri.Memory.ScalarInt.ofUInt64 8) from rfl,
        hmul, htisize, hisSigned, hlt0_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
        hmptr_opt]
      have h8 : Int64.ofInt ((8 : Nat) : Int) = Int64.ofInt 8 := rfl
      rw [h8] at hpoff
      rw [hpoff]
      dsimp only [nextPtr, Miri.Memory.Scalar.fromMaybePointer]
      rw [hprov_eq]; rfl)
  rw [hoff0, Nat.zero_add] at hdiv
  obtain ⟨ha, m', tf', mptr, hptrRel, hm, hfr', hval'⟩ := hdiv
  obtain ⟨_, borTag, hprov_eq, _, _, _, e', he'_mem, he'_tag, rfl⟩ := hptrRel
  have he_eq : e' = e :=
    allocMap_mem_tag_injective halloc.tags_nodup he'_mem he_mem (he'_tag.trans he_tag.symm)
  subst he_eq
  refine ⟨ha, m', tf', borTag, hm, hfr', ?_⟩
  simpa [nextPtr, hprov_eq] using hval'

/-- **`step_binOp_offset_neg_isize_divergence`**: for a byte pointer
`*(const|mut) u8` at `1 ≤ ptrVal.offsetBytes ≤ allocSize` targeting a live
stack local `e.localIdx`, executing `_d = Offset(copy _p, rhsOp)` with `rhsOp`
evaluating to `-1_isize` (`⟨2 ^ 64 - 1, 8⟩`) diverges in the direction of
pointer arithmetic:
1. Anneal's `stepMirFn` treats `sc.bits = 2 ^ 64 - 1` as an unsigned `Nat` and
   stores `.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + (2 ^ 64 - 1) } 8`; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) sign-extends
   `-1_isize` to `-1 : Int64` and steps the pointer backward in-bounds to
   `annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes - 1)`. -/
theorem step_binOp_offset_neg_isize_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    {dstDecl ptrDecl tgtDecl : LocalDecl}
    {ptrMut dstMut : Mutability} {rhsTy : Ty}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut (.uint .u8))
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut (.uint .u8))
    (hrhs_ty : rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hptr_slot : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar ⟨2 ^ 64 - 1, 8⟩) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (he_mem : e ∈ allocMap)
    (he_tag : e.tag = ptrVal.tag)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead)
    (hlo_off : 1 ≤ ptrVal.offsetBytes)
    (hhi_off : ptrVal.offsetBytes ≤
      (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat) :
    stepMirFn body s =
      MirStepNode.step
        (advanceStmt s
          (s.frame.locals.set dstIdx
            (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + (2 ^ 64 - 1) } 8)))
          s.memory) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes - 1)),
              .concrete e.allocId borTag⟩)))) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, halloc, _⟩ := id hstate
  obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
  have ht_ne : slot_t ≠ .dead := fun hd => htgt_live (hslot_t.trans (congrArg some hd))
  obtain ⟨_, _, hsh_fn⟩ := (halloc.local_alloc_sync tf hframes e he_mem).1 slot_t hslot_t ht_ne
  obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_fn tgtDecl hdecl_tgt
  obtain ⟨hid_lt, _, hbase⟩ := halloc.base_addr_valid e he_mem
  have hhi_la : ptrVal.offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat := by
    rw [hshape_la.byteSize_eq]; exact hhi_off
  have hrhs_prim : IsPrimScalarTy rhsTy := Or.inr (Or.inr (Or.inl ⟨.isize, hrhs_ty⟩))
  let nextPtr : Miri.Memory.Pointer AnnealProv → Miri.Memory.Pointer AnnealProv :=
    fun mptr =>
      ⟨Miri.ABI.Size.ofBytes
        (annealStackBaseAddr e.allocId + UInt64.ofNat (ptrVal.offsetBytes - 1)),
        mptr.provenance⟩
  have hdiv := step_binOp_offset_divergent_ok hstate hphase hbb hstmt hdecl_dst hdecl_ptr
    hptr_ty hdst_ty hrhs_prim hop_rhs himm hptr_slot hrhs_eval hdst_live nextPtr
    (fun mptr msc tfc hptrRel hrel_sc => by
      obtain ⟨_, borTag, hprov_eq, _, hoff_lt, hmptr_off, e', he'_mem, he'_tag, rfl⟩ := hptrRel
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he'_mem he_mem (he'_tag.trans he_tag.symm)
      subst he_eq
      obtain ⟨scaledInt, hmul, htisize⟩ := mulWithOverflow_neg_one_isize_stride_one_eq hrel_sc
      have hp_tr : translateTy ptrDecl.ty body.layouts =
          { ty := 70, layout := pointerLayoutData false } := by
        unfold translateTy encodeTyId; rw [hptr_ty]; rfl
      have hr_tr : translateTy rhsTy body.layouts =
          { ty := 15, layout := scalarLayoutData 8 true } := by
        unfold translateTy encodeTyId; rw [hrhs_ty]; rfl
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
            some (.concrete e'.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_off ⊢
        subst hprov_eq hmptr_off; rfl
      have hpoff := ptrOffsetInbounds_neg_one_live_ok e'.allocId borTag ptrVal.offsetBytes
        localAlloc hid_lt hoff_lt hbase hfind_la hlo_off hhi_la
      have htb : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 (2 ^ 64 - 1)) := by
        have hsz : Miri.ABI.Size.ofBytes 8 =
            translateSizeBytes (⟨2 ^ 64 - 1, 8⟩ : MirAst.ScalarInt).sizeBytes := rfl
        rw [hsz]; exact hrel_sc.toBits_eq
      have hbin_eq : Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
          ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            { ty := 70, layout := pointerLayoutData false }⟩
          ⟨.scalar (.fromScalarInt msc),
            { ty := 15, layout := scalarLayoutData 8 true }⟩
          { m with stack := ⟨#[tfc]⟩ } =
          annealPointerBinary body.layouts .Offset
            ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
              { ty := 70, layout := pointerLayoutData false }⟩
            ⟨.scalar (.fromScalarInt msc),
              { ty := 15, layout := scalarLayoutData 8 true }⟩
            { m with stack := ⟨#[tfc]⟩ } := by
        have hf := congrFun (scalarOps_binary_def
          (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
          ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
            { ty := 70, layout := pointerLayoutData false }⟩
          ⟨.scalar (.fromScalarInt msc),
            { ty := 15, layout := scalarLayoutData 8 true }⟩) { m with stack := ⟨#[tfc]⟩ }
        rw [hf]; unfold annealScalarOpsHooks
        simp only [classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
      rw [hp_tr, hr_tr, hbin_eq]
      unfold annealPointerBinary
      have hpt_lay : layoutOfEncodedTyId 20 body.layouts =
          { ty := 20, layout := scalarLayoutData 1 false } := rfl
      have hisSized : (!(({ ty := 20, layout := scalarLayoutData 1 false } :
          Miri.Interpreter.LocalLayout).layout.isSized &&
          decide (({ ty := 20, layout := scalarLayoutData 1 false } :
            Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
      have hfrom1 : Miri.Memory.Scalar.fromInt (Prov := AnnealProv) 1 (Miri.ABI.Size.ofBytes 8) =
          .ok (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 1)) := rfl
      have hsz8 : (scalarLayoutData 8 true).size = Miri.ABI.Size.ofBytes 8 := rfl
      have hsz_pt : Int.ofNat (scalarLayoutData 1 false).size.bytes.toNat = 1 := rfl
      have hisSigned : (scalarLayoutData 8 true).backendRepr.isSigned = .ok true := rfl
      simp only [show (Miri.MIR.BinOp.Offset != .Offset) = false from rfl, Bool.false_eq_true,
        ↓reduceIte, show (Miri.Interpreter.Immediate.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)).toScalar =
          .ok (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) from rfl,
        scalar_fromPointer_toPointer_eq mptr, rawPtrPointeeEncodedTyId?, hpt_lay,
        hisSized, classifyEncodedTyId,
        show (Miri.Interpreter.Immediate.scalar
          (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc)).toScalar =
          .ok (.fromScalarInt msc) from rfl,
        show (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
          .ok msc from rfl]
      simp only [hsz8, hsz_pt, htb, hfrom1,
        show (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv)
          (Miri.Memory.ScalarInt.ofUInt64 1)).toScalarInt =
          .ok (Miri.Memory.ScalarInt.ofUInt64 1) from rfl,
        hmul, htisize, hisSigned, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
        hmptr_opt, hpoff]
      dsimp only [nextPtr, Miri.Memory.Scalar.fromMaybePointer]
      rw [hprov_eq]; rfl)
  obtain ⟨ha, m', tf', mptr, hptrRel, hm, hfr', hval'⟩ := hdiv
  obtain ⟨_, borTag, hprov_eq, _, _, _, e', he'_mem, he'_tag, rfl⟩ := hptrRel
  have he_eq : e' = e :=
    allocMap_mem_tag_injective halloc.tags_nodup he'_mem he_mem (he'_tag.trans he_tag.symm)
  subst he_eq
  refine ⟨ha, m', tf', borTag, hm, hfr', ?_⟩
  simpa [nextPtr, hprov_eq] using hval'

/-! ## 13. Extended `LM-3.1` Casts, Validity, `PlaceMention(*_p)`,
`&raw (*_p)` & Terminators -/

/-- **`evalCast_ptrToPtr_annealCastHooks_simulation`**: leaf-level `PtrToPtr`
cast correspondence directly against the production `annealCastHooks` (as wired
into `annealStepHooks`), requiring thin raw-pointer pointees
(`isThinRawPtrPointee` for both source and destination, `TyId = 60..82`) while
rejecting non-thin raw pointers (`TyId = 40`,
`castTypeInfoOfEncodedTyId_nonThin_err`). -/
theorem evalCast_ptrToPtr_annealCastHooks_simulation
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
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (hsrc_slot : get? locals srcLoc = some (.init (.ptr ptrVal 8)))
    (hptr_rel : PtrRel allocMap ptrVal mptr) :
    evalRvalue locals (.cast .ptrToPtr (.copy ⟨srcLoc, .nil⟩) dstTy) mem localDecls layouts =
      .ok (.ptr ptrVal 8) locals mem ∧
    Miri.Interpreter.Cast.ptrToPtr
      (annealCastHooks layouts)
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
   miri_cast_ptrToPtr_annealCastHooks_eq layouts m srcMut dstMut srcPointee dstPointee srcTy dstTy
     hsrcTy hdstTy hsrc_thin hdst_thin mptr,
   .rawPtr dstMut dstPointee ptrVal mptr hdstTy hptr_rel⟩

/-- Safe references (`&T` / `&mut T`) resolve to `none` in
`lookupDerefPointeeLayout`, failing closed instead of routing `&T`/`&mut T`
dereferences through `PointerPlaceMachine.fromImmediate` (which omits
`PointerPlaceMachine.dereference`'s eager non-null, bounds, and alignment
checks). -/
theorem lookupDerefPointeeLayout_ref_eq_none
    {localDecls : List LocalDecl} {layouts : LayoutTable}
    {refIdx : Local} {refDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy}
    (hdecl : get? localDecls refIdx = some refDecl)
    (hty : refDecl.ty.kind = .ref mutability pointeeKind)
    (ptrLay : Miri.Interpreter.LocalLayout) :
    lookupDerefPointeeLayout localDecls layouts refIdx ptrLay = none := by
  unfold lookupDerefPointeeLayout
  rw [hdecl]
  dsimp only []
  rw [hty]

/-- **`lookupDerefPointeeLayout_decl_eq_encoded` (Representation Coherence)**:
with `derefPointeeKindHasExactLayout` covering every thin pointee type whose
`encodeRawPtrTyId` tag (`60..79`) uniquely identifies its layout (including ZST
`fnDef` items at tag `60`), `lookupDerefPointeeLayout` on any local's translated
`LocalLayout` returns the exact same result whether `localDecls` is populated or
empty (`.nil`). -/
theorem lookupDerefPointeeLayout_decl_eq_encoded
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (localId : Local) (decl : LocalDecl)
    (hdecl : get? localDecls localId = some decl) :
    lookupDerefPointeeLayout localDecls layouts localId (translateTy decl.ty layouts) =
      lookupDerefPointeeLayout .nil layouts localId (translateTy decl.ty layouts) := by
  have hnil : get? ([] : List LocalDecl) localId = none := by cases localId <;> rfl
  have hraw_gt100 : ∀ idx : Nat, rawPtrPointeeEncodedTyId? (100 + idx) = none := by
    intro idx
    unfold rawPtrPointeeEncodedTyId? Miri.MIR.TyId
    split <;> first | rfl | omega
  rcases decl with ⟨_, ⟨kind, layoutIdx⟩, _⟩
  unfold lookupDerefPointeeLayout
  rw [hdecl, hnil]
  dsimp only []
  cases kind with
  | rawPtr _ pk =>
    cases pk with
    | bool | char | never => rfl
    | int it => cases it <;> rfl
    | uint ut => cases ut <;> rfl
    | float ft => cases ft <;> rfl
    | tuple elems => cases elems <;> rfl
    | fnDef _ _ => rfl
    | rawPtr _ _ | ref _ _ | fnPtr _ _ _ _ => rfl
    | _ => rfl
  | bool | char | never => rfl
  | int it => cases it <;> rfl
  | uint ut => cases ut <;> rfl
  | float ft => cases ft <;> rfl
  | ref _ _ | fnPtr _ _ _ _ | fnDef _ _ => rfl
  | tuple elems =>
    cases elems with
    | nil => rfl
    | cons _ _ =>
      change none = (rawPtrPointeeEncodedTyId? (100 + layoutIdx)).map (layoutOfEncodedTyId · layouts)
      rw [hraw_gt100]; rfl
  | _ =>
    change none = (rawPtrPointeeEncodedTyId? (100 + layoutIdx)).map (layoutOfEncodedTyId · layouts)
    rw [hraw_gt100]; rfl

/-- Uninhabited `!` (`tyId = 50`) rejects every scalar in
`annealValidateScalarForTyId`. -/
theorem annealValidateScalarForTyId_never_false
    (sc : Miri.Memory.Scalar AnnealProv) :
    annealValidateScalarForTyId 50 sc = false := rfl

/-- Non-null pointer encodings (`tyId = 41` `&T`/`&mut T` and `tyId = 42`
`fnPtr`, `pointerLayoutData true`) reject null 0-address scalars in
`annealValidateScalarForTyId`. -/
theorem annealValidateScalarForTyId_nonNullPtr_null_false
    (tyId : Miri.MIR.TyId) (hty : tyId = 41 ∨ tyId = 42) :
    annealValidateScalarForTyId tyId
      (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 0)) = false := by
  have hrel0 : ScalarRel ⟨0, 8⟩ (Miri.Memory.ScalarInt.ofUInt64 0) :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  have hptr0 := scalar_fromScalarInt_toPointer_eq hrel0 rfl
  rcases hty with rfl | rfl <;>
    (unfold annealValidateScalarForTyId; rw [hptr0]; rfl)

/-- **`step_deref_invalid_char_divergence`**: in `StateRelLM3_1`-related states
where `_p : *(const|mut) char` at `offsetBytes = 0` points to a 4-byte
`u32`/`i32` stack local holding `sc` with `isValidCharCode sc.bits = false`
(e.g. a UTF-16 surrogate `0xD800` or `0x110000` cast via `PtrToPtr` to
`*const char`), executing `_d = copy *_p` diverges:

1. Anneal's `stepMirFn` takes a normal step storing `.init (.scalar sc)` in `_d`
   without checking Unicode scalar-value validity; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) rejects the
   invalid `char` bit pattern with
   `StepError.undefinedBehavior "reading invalid value"`. -/
theorem step_deref_invalid_char_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
    {dstDecl ptrDecl tgtDecl : LocalDecl} {mutability : Mutability}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hdst_char : dstDecl.ty.kind = .char)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability dstDecl.ty.kind)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {sc : MirAst.ScalarInt}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm ≠ .disabled)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_word : tgtDecl.ty.kind = .uint .u32 ∨ tgtDecl.ty.kind = .int .i32)
    (htarget : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hinvalid : isValidCharCode sc.bits = false)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx = some (.init (.scalar sc))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "reading invalid value")) := by
  have hdst_prim : IsPrimScalarTy dstDecl.ty := Or.inr (Or.inl hdst_char)
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hread : evalOperand s.frame.locals (.copy ⟨ptrIdx, .cons .deref .nil⟩)
        s.memory.borrows s.memory.globals body.layouts s.memory.callerLocals =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand; dsimp only []; rw [hslot_p]; dsimp only []; rw [hlookup]; dsimp only []
      cases hp : e.perm with
      | disabled => exact absurd hp hperm
      | _ => simp only [htarget]; rfl
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []; rw [hread]; dsimp only []
    have hset := set?_eq_some_set hlt_af_d (LocalSlot.init (.scalar sc))
    have hget_set : get? (s.frame.locals.set dstIdx (.init (.scalar sc))) dstIdx =
        some (.init (.scalar sc)) := by
      rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
    cases hb : s.memory.borrows with
    | nil =>
      simp only [hslot_d]
      cases slot_d with
      | dead => exact absurd rfl hsd_ne
      | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | cons b₁ rest =>
      cases rest with
      | nil =>
        simp only [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_ne
        | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
        | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
      | cons b₂ rest' =>
        simp only [hslot_d]
        cases slot_d with
        | dead => exact absurd rfl hsd_ne
        | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
        | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
  · have himm_p := himm_ptr tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (.copy ⟨ptrIdx, .cons .deref .nil⟩) span m
    obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
      hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hfra.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
    have hstate_b : StateRelLM3_1 body s { m with stack := ⟨#[tfb]⟩ } allocMap :=
      hstate_a.cache_layout rfl hdecl_ptr hlt_pa
    obtain ⟨tfb', hframes_b, _, _, hfrb, _, _, _, _, _, halloc_b, _⟩ := id hstate_b
    injection hframes_b with hfb₁; injection hfb₁ with hfb₂; subst hfb₂
    have hlay0_eq : translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts =
        translateTy dstDecl.ty body.layouts := hdst_prim.translateTy_layoutIdx body.layouts
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e' he'
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      have hop_ptr := annealEvalOperand_deref_live (opKind := MirAst.Operand.copy) (Or.inl rfl)
        (known := some (translateTy dstDecl.ty body.layouts)) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      have hmptr_zero : mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId) := by
        rw [hmptr_off, hoff0, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
      obtain ⟨_, _, _, _, hpow_dst, _⟩ := hdst_prim.size_align_ok body.layouts
      have hmis0 : annealOffsetMisalignment mptr.offset
          (translateTy { kind := dstDecl.ty.kind, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok none := by
        rw [hlay0_eq, hmptr_zero]
        exact annealOffsetMisalignment_stackBase_eq_none e'.allocId _ hpow_dst
      have hder_ok := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hdst_prim mptr hmis0
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      rw [hlay0_eq] at hder_ok
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
            some (.concrete e'.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_zero ⊢
        subst hprov_eq hmptr_zero; rfl
      rw [hmptr_opt] at hder_ok
      obtain ⟨slot_t, mls_t, _, _, hslot_t, hmls_t, _, hloc_t⟩ := hfrb.lookup_local hdecl_tgt
      have hst_eq : slot_t = .init (.scalar sc) := Option.some.inj (hslot_t.symm.trans htarget)
      subst hst_eq
      obtain ⟨⟨lay_t, hlay_t⟩, _, hsh_fn⟩ :=
        (halloc_b.local_alloc_sync tfb rfl e' he').1 _ hslot_t (by simp)
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_fn tgtDecl hdecl_tgt
      have hmls_t_eq : mls_t = ⟨.live (.indirect (stackAllocPlace e'.allocId)), lay_t⟩ :=
        Option.some.inj (hmls_t.symm.trans hlay_t)
      have hsz_tgt_4 : (translateTy tgtDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 4 := by
        rcases htgt_word with hk | hk <;> (unfold translateTy; rw [hk]; rfl)
      have hsz_dst_4 : (translateTy dstDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 4 := by
        unfold translateTy; rw [hdst_char]; rfl
      have hty_dst_2 : (translateTy dstDecl.ty body.layouts).ty = 2 := by
        unfold translateTy encodeTyId; rw [hdst_char]
      obtain ⟨_, hsc_spec⟩ := hloc_t.indirect_stackAllocPlace_spec hmls_t_eq hbase hfind_la
        (halloc_b.live_key_unique e' he') (by rw [hsz_tgt_4]; decide)
      obtain ⟨hsz_sc, _, _, msc, hrel_sc, hread_sc⟩ := hsc_spec sc rfl
      rw [hsz_tgt_4, ← hsz_dst_4] at hread_sc
      have hread_m := annealReadMemoryPlace_zero_offset_eq hdst_prim hid_lt hbase hfind_la
        (hshape_la.byteSize_eq.trans (hsz_tgt_4.trans hsz_dst_4.symm))
        (borTag := borTag) (st := { m with stack := ⟨#[tfb]⟩ })
      rw [hread_sc, hty_dst_2] at hread_m
      dsimp only [] at hread_m
      have hval_false : annealValidateScalarForTyId 2 (.fromScalarInt msc) = false := by
        have hsz4 : sc.sizeBytes = 4 := by
          rw [hsz_tgt_4] at hsz_sc
          have hb : (4 : UInt64) = UInt64.ofNat sc.sizeBytes := congrArg Miri.ABI.Size.bytes hsz_sc
          rcases hrel_sc.validBytes with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb ⊢ <;>
            first | rfl | cases hb
        have hlt128 : sc.bits < 2 ^ 128 := by
          have hc := hrel_sc.canonical; rw [hsz4] at hc
          have hm4 : scalarModulus 4 = 2 ^ 32 := rfl
          omega
        have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
            .ok msc := rfl
        have h2 : (2 : Miri.MIR.TyId) = (translateTy { kind := .char, layoutIdx := 0 } body.layouts).ty := rfl
        have hsz_c : (translateSizeBytes 4 == Miri.ABI.Size.ofBytes 4) = true := rfl
        have hbv_nat : (BitVec.ofNat 128 sc.bits).toNat = sc.bits := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt128]
        simp only [annealValidateScalarForTyId, hsi, hrel_sc.size_eq, hrel_sc.data_eq, hsz4,
          hsz_c, Bool.true_and, hbv_nat, hinvalid]
      simp only [hval_false, Bool.false_eq_true, ↓reduceIte] at hread_m
      have hop_ok : annealEvalOperand body.localDecls body.layouts
          (translateOperand (.copy ⟨ptrIdx, .cons .deref .nil⟩))
          (some (translateTy dstDecl.ty body.layouts)) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.indirect ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
              some (.concrete e'.allocId borTag)⟩, .none, none⟩,
            translateTy dstDecl.ty body.layouts⟩ { m with stack := ⟨#[tfb]⟩ } := by
        rw [hop_ptr, EStateM.bind_eq_ok hder_ok]; rfl
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = { localId := dstIdx, projection := #[] } := rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrIdx, .cons .deref .nil⟩)), span⟩)
          m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "reading invalid value")) := by
        rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_ok]
        dsimp only [annealReadImmediate]
        rw [EStateM.bind_eq_error hread_m]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_deref_write_invalid_bool_divergence`**: in `StateRelLM3_1`-related
states where `_p : *mut bool` at `offsetBytes = 0` (`e.perm = .active` or
`e.perm = .reserved`) points to a live 1-byte stack local (`bool`, `u8`, or
`i8`) and `c` is a 1-byte `bool` constant with `2 ≤ b < 256`, executing
`*_p = const c` diverges:

1. Anneal's `stepMirFn` writes `.init (.scalar ⟨b, 1⟩)` into `e.localIdx`
   without checking `bool` bit-pattern validity; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) rejects the
   invalid `bool` bit pattern with
   `StepError.undefinedBehavior "writing invalid value"`. -/
theorem step_deref_write_invalid_bool_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {c : ConstOperand} {b : Nat} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩)
    {ptrDecl tgtDecl : LocalDecl}
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr .mut .bool)
    (hc_val : c.val = .scalar (.int ⟨b, 1⟩))
    (hc_ty : c.ty.kind = .bool)
    (hb_lo : 2 ≤ b) (hb_hi : b < 256)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    {ptrVal : ProvenancePtr} {e : AllocMapEntry}
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (hoff0 : ptrVal.offsetBytes = 0)
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active ∨ e.perm = .reserved)
    (hdecl_tgt : get? body.localDecls e.localIdx = some tgtDecl)
    (htgt_1 : tgtDecl.ty.kind = .bool ∨ tgtDecl.ty.kind = .uint .u8 ∨ tgtDecl.ty.kind = .int .i8)
    (htgt_live : get? s.frame.locals e.localIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals e.localIdx = some (.init (.scalar ⟨b, 1⟩))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "writing invalid value")) := by
  have hbool_prim : IsPrimScalarTy { kind := .bool, layoutIdx := 0 } := Or.inl rfl
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    obtain ⟨slot_t, _, hlt_af_t, _, hslot_t, _, _, _⟩ := hfr.lookup_local hdecl_tgt
    have hst_ne : slot_t ≠ .dead := fun hd => htgt_live (hslot_t.trans (congrArg some hd))
    have hc_op : ∀ bor, evalOperand s.frame.locals (.constant c) bor s.memory.globals
        body.layouts s.memory.callerLocals = .ok (.scalar ⟨b, 1⟩) s.frame.locals := by
      intro bor; unfold evalOperand; dsimp only []; rw [hc_val]; rfl
    have hset_t := set?_eq_some_set hlt_af_t (LocalSlot.init (.scalar ⟨b, 1⟩))
    have hget_set : get? (s.frame.locals.set e.localIdx (.init (.scalar ⟨b, 1⟩))) e.localIdx =
        some (.init (.scalar ⟨b, 1⟩)) := by
      rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_t]
    have hw_anneal : evalPlaceWrite s.frame.locals s.memory.borrows ⟨ptrIdx, .cons .deref .nil⟩
        (.scalar ⟨b, 1⟩) s.memory.activeProtectors =
        .ok (s.frame.locals.set e.localIdx (.init (.scalar ⟨b, 1⟩))) := by
      unfold evalPlaceWrite writePlaceValue; rw [hprot]; dsimp only []
      rw [hslot_p]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
      rcases hperm with hp | hp <;> rw [hp] <;> dsimp only [] <;> rw [hslot_t] <;>
        (cases slot_t with
          | dead => exact absurd rfl hst_ne
          | uninit => simp only [hset_t]
          | init _ => simp only [hset_t])
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hrv_c : evalRvalue s.frame.locals (.use (.constant c)) s.memory body.localDecls
        body.layouts = .ok (.scalar ⟨b, 1⟩) s.frame.locals s.memory := by
      unfold evalRvalue
      cases s.memory.borrows with
      | nil => dsimp only []; rw [hc_op]
      | cons b₁ rest =>
        cases rest with
        | nil => dsimp only []; rw [hc_op]
        | cons b₂ rest' => dsimp only []; rw [hc_op]
    unfold evalStmt; dsimp only []; rw [hrv_c]; dsimp only []; rw [hw_anneal]
    exact ⟨_, rfl, hget_set⟩
  · have himm_p := himm_ptr tf hframes
    have hm_stmt := evalStatement_assign_use_eq body.localDecls body.layouts
      ⟨ptrIdx, .cons .deref .nil⟩ (.constant c) span m
    obtain ⟨slot_p, mls_p, _, hlt_p, hslot_p', hmls_p, hmls_p_eq, hloc_p⟩ :=
      hfr.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_p' : ∀ mp, mls_p.value ≠ .live (.indirect mp) := himm_p mls_p hmls_p
    let tfa := cacheFrameLocalLayout tf ptrIdx hlt_p (translateTy ptrDecl.ty body.layouts)
    have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
      hstate.cache_layout hframes hdecl_ptr hlt_p
    obtain ⟨tfa', hframes_a, _, _, hfra, _, _, _, _, _, halloc_a, _⟩ := id hstate_a
    injection hframes_a with hfa₁; injection hfa₁ with hfa₂; subst hfa₂
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_p'.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_p' with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, borTag, hprov_eq, hid_lt, _, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      obtain ⟨_, _, hbase⟩ := halloc.base_addr_valid e' he'
      have hmls_p' : tf.locals[ptrIdx]'hlt_p =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      have hdst_live := annealEvalPlace_deref_live hframes hlt_p hdecl_ptr hmls_p' hcache_p
      have hmptr_zero : mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId) := by
        rw [hmptr_off, hoff0, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero]
      obtain ⟨_, _, _, _, hpow_b, _⟩ := hbool_prim.size_align_ok body.layouts
      have hmis0 : annealOffsetMisalignment mptr.offset
          (translateTy { kind := .bool, layoutIdx := 0 } body.layouts).layout.align.abi =
          .ok none := by
        rw [hmptr_zero]; exact annealOffsetMisalignment_stackBase_eq_none e'.allocId _ hpow_b
      have hder_ok := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hbool_prim mptr hmis0
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfa]⟩ }
      have hmptr_opt : mptr.withOptionalProvenance =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
            some (.concrete e'.allocId borTag)⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only [Miri.Memory.Pointer.withOptionalProvenance] at hprov_eq hmptr_zero ⊢
        subst hprov_eq hmptr_zero; rfl
      rw [hmptr_opt] at hder_ok
      have hdst_ok : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) m =
          .ok ⟨.memory ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
              some (.concrete e'.allocId borTag)⟩, .none, none⟩,
            translateTy { kind := .bool, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfa]⟩ } := by
        rw [hdst_live, EStateM.bind_eq_ok hder_ok]; rfl
      have hsz_b1 : ValidScalarBytes ({ bits := b, sizeBytes := 1 } : MirAst.ScalarInt).sizeBytes :=
        Or.inl rfl
      have hcan_b : ({ bits := b, sizeBytes := 1 } : MirAst.ScalarInt).bits <
          scalarModulus ({ bits := b, sizeBytes := 1 } : MirAst.ScalarInt).sizeBytes := by
        simpa [scalarModulus] using hb_hi
      obtain ⟨msc, htry_b, hrel_b⟩ := tryFromUInt_of_valid_canonical hsz_b1 hcan_b
      have hc_prim : IsPrimScalarTy c.ty := Or.inl hc_ty
      have hop_c : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
          (some (translateTy { kind := .bool, layoutIdx := 0 } body.layouts))
          { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
            translateTy c.ty body.layouts⟩ { m with stack := ⟨#[tfa]⟩ } := by
        with_unfolding_all
          unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
          dsimp only
          rw [hc_val]
          simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
            EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
            stack_currentFrame?_singleton _ tfa rfl, Option.isNone_some,
            Bool.false_eq_true, ↓reduceIte, htry_b, hc_prim.layoutOfEncoded]
      obtain ⟨slot_t, _, _, _, hslot_t, _, _, _⟩ := hfra.lookup_local hdecl_tgt
      have hst_ne : slot_t ≠ .dead := fun hd => htgt_live (hslot_t.trans (congrArg some hd))
      obtain ⟨_, _, hsh_fn⟩ := (halloc_a.local_alloc_sync tfa rfl e' he').1 slot_t hslot_t hst_ne
      obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh_fn tgtDecl hdecl_tgt
      have hsz_tgt_1 : (translateTy tgtDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 1 := by
        rcases htgt_1 with hk | hk | hk <;> (unfold translateTy; rw [hk]; rfl)
      obtain ⟨hsz_bool, hgt0_bool, hlt63_bool, _, _, _⟩ := hbool_prim.size_align_ok body.layouts
      have hinb_0 : 0 + (translateTy { kind := .bool, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat ≤
          localAlloc.allocation.byteSize.bytes.toNat := by
        rw [Nat.zero_add, hshape_la.byteSize_eq, hsz_tgt_1]; exact Nat.le_refl _
      have hchk_ok := checkAndDerefPtr_live_inbounds_ok e'.allocId borTag 0
        (translateTy { kind := .bool, layoutIdx := 0 } body.layouts).layout.size.bytes.toNat
        localAlloc .memoryAccess hid_lt (by show 0 < 2 ^ 32; decide) hbase hfind_la
        (Int.ofNat_lt.mp hgt0_bool) hlt63_bool hinb_0
      have hoff0_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
      rw [hoff0_sz, show UInt64.ofNat 0 = 0 from rfl, UInt64.add_zero] at hchk_ok
      have hval_false : annealValidateScalarForTyId 1 (.fromScalarInt msc) = false := by
        have hsi : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
            .ok msc := rfl
        unfold annealValidateScalarForTyId
        rw [hsi]; dsimp only []
        rw [hrel_b.size_eq, hrel_b.data_eq]
        have hsz_b : (translateSizeBytes 1 == Miri.ABI.Size.ofBytes 1) = true := rfl
        have hbv_nat : (BitVec.ofNat 128 b).toNat = b := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [hsz_b, Bool.true_and, hbv_nat]
        change (b == 0 || b == 1) = false
        rw [Bool.or_eq_false_iff, beq_eq_false_iff_ne, beq_eq_false_iff_ne]
        exact ⟨by omega, by omega⟩
      have hw_err : annealWriteMemoryPlace (.scalar (.fromScalarInt msc))
          ⟨⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId),
              some (.concrete e'.allocId borTag)⟩, .none, none⟩
          (translateTy { kind := .bool, layoutIdx := 0 } body.layouts)
          { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "writing invalid value") { m with stack := ⟨#[tfa]⟩ } := by
        unfold annealWriteMemoryPlace
        have hty1 : (translateTy { kind := .bool, layoutIdx := 0 } body.layouts).ty = 1 := rfl
        have hmut_ok : (localAlloc.allocation.mutability != Miri.Memory.Mutability.Mut) = false := by
          rw [hshape_la.mutability_eq]; rfl
        have hsc_sz : ((Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).size !=
            (translateTy { kind := .bool, layoutIdx := 0 } body.layouts).layout.size) = false := by
          rw [Miri.Memory.Scalar.fromScalarInt_size, hrel_b.size_eq]; rfl
        dsimp only []
        rw [hsz_bool]; dsimp only []
        rw [hchk_ok]; dsimp only []
        rw [hmut_ok]; simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hfind_la, hsc_sz]; dsimp only [Bool.false_eq_true, ↓reduceIte]
        rw [hty1, hval_false]; rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨ptrIdx, .cons .deref .nil⟩ (.use (.constant c)), span⟩) m =
          ({ m with stack := ⟨#[tfa]⟩ }, .error (.undefinedBehavior "writing invalid value")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_ok, EStateM.bind_eq_ok hop_c]
        dsimp only [annealReadImmediate, pure, EStateM.pure, bind, EStateM.bind]
        rw [annealWriteImmediate_memory_eq rfl, hw_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_placeMention_deref_uninit_divergence`**: when an immediate
raw-pointer local `_p : *(const|mut) T` (`T` primitive scalar) is `.uninit`
(`StorageLive(_p)` before `_p` is initialized), `PlaceMention(*_p)`
(`let _ = *_p;`) diverges:

1. Anneal's `stepMirFn` checks only `get? s.frame.locals ptrIdx ≠ some .dead`
   and steps normally without reading `_p`; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) reads `_p` to
   evaluate the place `*_p` and raises
   `StepError.undefinedBehavior "read of uninitialized local"`. -/
theorem step_placeMention_deref_uninit_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {ptrIdx : Local} {ptrDecl : LocalDecl}
    {mutability : Mutability} {pointeeKind : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr mutability pointeeKind)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (huninit : get? s.frame.locals ptrIdx = some .uninit) :
    stepMirFn body s = MirStepNode.step (advanceStmt s s.frame.locals) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "read of uninitialized local")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  have himm_p := himm_ptr tf hframes
  obtain ⟨slot_p, mls_p, _, hlt_p, hslot_p, hmls_p, hmls_p_eq, hloc_p⟩ := hfr.lookup_local hdecl_ptr
  have hnot_ind : ∀ mp, mls_p.value ≠ .live (.indirect mp) := himm_p mls_p hmls_p
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  have hsp_eq : slot_p = .uninit := Option.some.inj (hslot_p.symm.trans huninit)
  subst hsp_eq
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt; dsimp only []; rw [huninit]
  · rcases hloc_p.rawPtr_immediate_cases hptr_ty hnot_ind with
      ⟨h, _⟩ | ⟨_, hmp_un⟩ | ⟨_, _, h, _⟩ | ⟨_, _, h, _⟩
    · cases h
    · have hmls_un : tf.locals[ptrIdx]'hlt_p = ⟨.live (.immediate .uninit), mls_p.layout⟩ := by
        rw [hmls_p_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_un; subst hmp_un; rfl
      have hlive_ev := annealEvalPlace_deref_live hframes hlt_p hdecl_ptr hmls_un hcache_p
      have hder_un := annealDerefOperandToMemPlace_uninit (ly := body.layouts) hdecl_ptr hptr_ty
        hpk_prim (translateTy ptrDecl.ty body.layouts)
        { m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt_p
            (translateTy ptrDecl.ty body.layouts)]⟩ }
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.placeMention ⟨ptrIdx, .cons .deref .nil⟩, span⟩) m =
          ({ m with stack := ⟨#[cacheFrameLocalLayout tf ptrIdx hlt_p
              (translateTy ptrDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind annealStepHooks
        dsimp only [Miri.Interpreter.runRvalue]
        rw [hlive_ev, EStateM.bind_eq_error hder_un]; rfl
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩
    · cases h
    · cases h

/-- `annealForceAllocation` on an already-dereferenced `.memory mp` place is a
pure no-op (returning `mp` without touching `AnnealStepState`). -/
theorem annealForceAllocation_memory_eq
    (ld : List LocalDecl) (ly : LayoutTable)
    (mp : Miri.Interpreter.MemPlace AnnealProv)
    (lay : Miri.Interpreter.LocalLayout)
    (m : AnnealStepState) :
    annealForceAllocation ld ly ⟨.memory mp, lay⟩ m = .ok mp m := rfl

/-- `MemPlace.toRef` on a provenance-less address
`Pointer.withoutProvenance addr` succeeds at `annealTargetDataLayout` (64-bit),
wrapping `addr` into an 8-byte `Miri.Memory.ScalarInt` related by
`ScalarRel ⟨addr.toNat, 8⟩`. -/
theorem memPlace_toRef_withoutProvenance
    (addr : UInt64) (mismatch : Option Miri.Memory.Misalignment) :
    ∃ msc_ref : Miri.Memory.ScalarInt,
      ScalarRel ⟨addr.toNat, 8⟩ msc_ref ∧
      (⟨Miri.Memory.Pointer.withoutProvenance addr, .none, mismatch⟩ :
        Miri.Interpreter.MemPlace AnnealProv).toRef annealTargetDataLayout =
        .ok (.scalar (.fromScalarInt msc_ref)) := by
  have hsz8 :
      ValidScalarBytes ({ bits := addr.toNat, sizeBytes := 8 } : MirAst.ScalarInt).sizeBytes :=
    Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have hcan8 :
      ({ bits := addr.toNat, sizeBytes := 8 } : MirAst.ScalarInt).bits <
        scalarModulus ({ bits := addr.toNat, sizeBytes := 8 } : MirAst.ScalarInt).sizeBytes := by
    simpa [scalarModulus] using addr.toNat_lt
  obtain ⟨msc_ref, htry_ref, hrel_ref⟩ := tryFromUInt_of_valid_canonical hsz8 hcan8
  refine ⟨msc_ref, hrel_ref, ?_⟩
  have hmp : Miri.Memory.Scalar.fromMaybePointer (Prov := AnnealProv) annealTargetDataLayout
      (Miri.Memory.Pointer.withoutProvenance addr) = .ok (.fromScalarInt msc_ref) := by
    have htry_ref' : Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 addr.toNat)
        (translateSizeBytes 8) = .ok (some msc_ref) := htry_ref
    with_unfolding_all
      change (Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 addr.toNat)
          (translateSizeBytes 8) |>.mapError Miri.Memory.ScalarError.scalarInt).bind
          (fun scalar =>
            match scalar with
            | some scalar => Except.ok (Miri.Memory.Scalar.fromScalarInt scalar)
            | none => Except.error (.pointerOffsetDoesNotFit
                (Miri.ABI.Size.ofBytes addr) (translateSizeBytes 8))) = _
      rw [htry_ref']
      rfl
  unfold Miri.Interpreter.MemPlace.toRef Miri.Interpreter.Immediate.newPointerWithMeta
  rw [hmp]
  rfl

/-- **`step_rawPtr_deref_null_divergence` (RFC 2582 Place-to-Pointer False
UB)**: in `StateRelLM3_1`-related states where `_p : *(const|mut) T` (`T`
primitive scalar) holds a provenance-less 8-byte integer scalar `sc` (such as a
null raw pointer `0 as *const T`), executing `_d = &raw (const|mut) (*_p)`
diverges:

1. Anneal's `stepMirFn` (`Places.lean:2708, 2743`) requires `_p` to hold a
   `Value.ptr` and falsely reports `MirStepNode.fail .ub`.
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) evaluates
   `*_p` as a `MemPlace` without reading pointee memory
   (`annealForceAllocation_memory_eq`) and steps normally via `MemPlace.toRef`,
   storing an 8-byte integer scalar `msc_ref` (`ScalarRel sc msc_ref`) into `_d`
   (matching RFC 2582 `&raw const (*ptr::null::<T>())`). -/
theorem step_rawPtr_deref_null_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {sc : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc))) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' msc_ref,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc_ref ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_ref)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []; rw [hslot_p]
  · obtain ⟨himm_d, himm_p⟩ := himm tf hframes
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hfra.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    have hsp_eq : slot_p = .init (.scalar sc) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨sc', msc, hsc_eq, hsz8, hrel_sc, hmp_sc⟩ | ⟨_, _, h, _⟩
    · cases h
    · cases h
    · injection hsc_eq with hv; injection hv with hsc'; subst hsc'
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_sc; subst hmp_sc; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      obtain ⟨mismatch, hder_sc⟩ := annealDerefOperandToMemPlace_scalarInt hdecl_ptr hptr_ty
        hpk_prim hrel_sc hsz8 (translateTy ptrDecl.ty body.layouts)
        { m with stack := ⟨#[tfb]⟩ }
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits), .none,
              mismatch⟩, translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_sc]; rfl
      have hkind : translateRawPtrKind rawMut ≠ .FakeForPtrMetadata := by
        cases rawMut <;> decide
      obtain ⟨msc_ref, hrel_addr, href⟩ :=
        memPlace_toRef_withoutProvenance (UInt64.ofNat sc.bits) mismatch
      have hsc_eq_addr : (⟨(UInt64.ofNat sc.bits).toNat, 8⟩ : MirAst.ScalarInt) = sc := by
        have hcan := hrel_sc.canonical
        rw [hsz8, scalarModulus_eq_two_pow] at hcan
        have htonat : (UInt64.ofNat sc.bits).toNat = sc.bits :=
          Nat.mod_eq_of_lt hcan
        cases sc with | mk bits sz =>
          dsimp only at hsz8 htonat
          rw [htonat, hsz8]
      rw [hsc_eq_addr] at hrel_addr
      have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) href
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      subst hsdb_eq
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_pa _) mls_db hmls_db
      obtain ⟨oldImm, hmdb_imm⟩ : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
        rcases hloc_db.rawPtr_immediate_cases hdst_ty himm_db with
          ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
        · exact absurd rfl hsd_ne
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
        rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmdb_imm; subst hmdb_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hw := annealWriteImmediate_live
        (val := .scalar (.fromScalarInt msc_ref))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
              (.RawPtr (translateRawPtrKind rawMut) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
              ⟨dstIdx, #[]⟩) m := rfl
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar (.fromScalarInt msc_ref))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      refine ⟨_, _, msc_ref, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_ok rfl hfrb.location_eq, rfl, hrel_addr, ?_⟩
      simp [Array.getElem?_set_self]
    · cases h

/-- **`step_rawPtr_deref_nonzero_offset_divergence` (Offset-Reset Reborrow
Bug)**: in `StateRelLM3_1`-related states where `_p : *(const|mut) T` (`T`
primitive scalar) holds a `PtrRel` pointer `ptrVal` at `ptrVal.offsetBytes > 0`
(`e.perm = .active`), executing `_d = &raw (const|mut) (*_p)` diverges in the
resulting pointer offset:

1. Anneal's `stepMirFn` (`Places.lean:2741`) stores
   `.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8` in `_d`,
   **silently resetting `offsetBytes` to `0`** (dropping `ptrVal.offsetBytes`);
   while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) preserves the
   exact byte offset
   `annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes` via
   `MemPlace.toRef`. -/
theorem step_rawPtr_deref_nonzero_offset_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .active) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              .concrete e.allocId borTag⟩)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hne_d_p : slot_d ≠ .dead := hsd_ne
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hrv_ok : ∃ mem₁, evalRvalue s.frame.locals
        (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
        .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
        mem₁.activeProtectors = .nil := by
      unfold evalRvalue; dsimp only []
      rw [hslot_p]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
      rw [hperm]; cases rawMut <;> exact ⟨_, rfl, hprot⟩
    obtain ⟨mem₁, hrv, hprot₁⟩ := hrv_ok
    have hset := set?_eq_some_set hlt_af_d
      (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
    have hget_set : get? (s.frame.locals.set dstIdx
        (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
        some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
      rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
    unfold evalStmt; dsimp only []; rw [hrv]; dsimp only []; rw [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit => simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
    | init _ => simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
  · obtain ⟨himm_d, himm_p⟩ := himm tf hframes
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hfra.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      obtain ⟨_, _, _, _, hpow_pk, _⟩ := hpk_prim.size_align_ok body.layouts
      obtain ⟨mismatch, hmis_any⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset _ hpow_pk
      have hder_ptr := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hpk_prim mptr hmis_any
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨mptr.withOptionalProvenance, .none, mismatch⟩,
              translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_ptr]; rfl
      have hkind : translateRawPtrKind rawMut ≠ .FakeForPtrMetadata := by
        cases rawMut <;> decide
      have hmptr_eq : mptr =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
            .concrete e'.allocId borTag⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rfl
      have href : (⟨mptr.withOptionalProvenance, .none, mismatch⟩ :
            Miri.Interpreter.MemPlace AnnealProv).toRef annealTargetDataLayout =
          .ok (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) := by
        rw [hmptr_eq]; rfl
      have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) href
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      subst hsdb_eq
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_pa _) mls_db hmls_db
      obtain ⟨oldImm, hmdb_imm⟩ : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
        rcases hloc_db.rawPtr_immediate_cases hdst_ty himm_db with
          ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
        · exact absurd rfl hsd_ne
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
        rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmdb_imm; subst hmdb_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
              (.RawPtr (translateRawPtrKind rawMut) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
              ⟨dstIdx, #[]⟩) m := rfl
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar
                    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      refine ⟨_, _, borTag, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_ok rfl hfrb.location_eq, rfl, ?_⟩
      rw [hmptr_eq]
      simp [Array.getElem?_set_self]

/-- **`step_cast_expose_provenance_ptr_unsupported`**: in `StateRelLM3_1`
states where `_p` holds a thin raw pointer (`isThinRawPtrPointee`) with concrete
provenance (`PtrRel`), `_d = copy _p as usize (PointerExposeProvenance)`
diverges by design:

1. Anneal's `stepMirFn` steps storing the synthetic integer
   `⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩`.
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) fails closed
   with `StepError.unsupported "exposeProvenance in cast"` rather than
   fabricating Anneal's non-canonical `65536`-stride formula. -/
theorem step_cast_expose_provenance_ptr_unsupported
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty}
    {dstDecl srcDecl : LocalDecl} {srcMut : Mutability} {srcPointee : RigidTy}
    {ptrVal : ProvenancePtr} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_ty : dstDecl.ty.kind = .uint .usize)
    (hcast_ty : castTy.kind = .uint .usize)
    (himm_src : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame srcIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.ptr ptrVal 8))) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported "exposeProvenance in cast")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, _, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hrv : evalRvalue s.frame.locals
        (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩) s.frame.locals s.memory := by
      unfold evalRvalue evalOperand; dsimp only []; rw [hslot_s]; rfl
    have hset := set?_eq_some_set hlt_af_d
      (LocalSlot.init (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩))
    have hget_set : get? (s.frame.locals.set dstIdx
        (.init (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩))) dstIdx =
        some (.init (.scalar ⟨ptrVal.allocId * 65536 + ptrVal.offsetBytes, 8⟩)) := by
      rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
    unfold evalStmt; dsimp only []; rw [hrv]; dsimp only []; rw [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
  · have himm_s := himm_src tf hframes
    obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_sa, hmls_sa, hmls_sa_eq, hloc_s⟩ :=
      hfra.lookup_local hdecl_src
    have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
      hloc_s.cachedLayout_eq
    have himm_sa : ∀ mp, mls_s.value ≠ .live (.indirect mp) :=
      himm_s.cache_layout hlt_d _ mls_s hmls_sa
    have hss_eq : slot_s = .init (.ptr ptrVal 8) := Option.some.inj (hslot_sa.symm.trans hslot_s)
    subst hss_eq
    rcases hloc_s.rawPtr_immediate_cases hsrc_ty himm_sa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, mptr, -, -, hmp_ptr⟩
    · cases h
    · cases h
    · cases h
    · have hmls_sa' : tfa.locals[srcIdx]'hlt_sa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_s.layout⟩ := by
        rw [hmls_sa_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      have hop_s := annealEvalOperand_copy_live (known := none) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_sa hdecl_src hmls_sa' hcache_s
      let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
      have hsrc_enc : (translateTy srcDecl.ty body.layouts).ty = encodeRawPtrTyId srcPointee := by
        unfold translateTy encodeTyId; rw [hsrc_ty]
      have hsrc_lay : (translateTy srcDecl.ty body.layouts).layout = pointerLayoutData false := by
        unfold translateTy; rw [hsrc_ty]
      obtain ⟨pInfo, hpInfo⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId srcPointee hsrc_thin
      have hdst_enc : (translateTy dstDecl.ty body.layouts).ty = 25 := by
        unfold translateTy encodeTyId; rw [hdst_ty]
      have hcast_enc : encodeTyId castTy = 25 := by unfold encodeTyId; rw [hcast_ty]
      have hcast_err : Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16
          ⟨.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)),
            translateTy srcDecl.ty body.layouts⟩
          .PointerExposeProvenance (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .error (.unsupported "exposeProvenance in cast") { m with stack := ⟨#[tfb]⟩ } := by
        have husize_info : castTypeInfoOfEncodedTyId 25 = .ok (.integer .usize) := rfl
        with_unfolding_all
          unfold Miri.Interpreter.Cast.cast Miri.Interpreter.Cast.pointerExposeProvenance
            annealCastHooks annealReadImmediate
          simp only [hsrc_enc, hsrc_lay, pointerLayoutData, hpInfo, hdst_enc, hcast_enc,
            husize_info, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, Except.mapError,
            bind, EStateM.bind, pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw]
          rfl
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          Miri.Interpreter.runRvalue
            (do
              let destPlace ← annealEvalPlace body.localDecls body.layouts
                (translatePlace ⟨dstIdx, .nil⟩)
              let src ← annealEvalOperand body.localDecls body.layouts
                (translateOperand (.copy ⟨srcIdx, .nil⟩)) none
              Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16 src
                .PointerExposeProvenance (encodeTyId castTy) destPlace) m := by
        unfold Miri.Interpreter.Step.evalStatement translateStmt
        dsimp only [translateStmtKind, translateRvalue, translateCastKind, annealStepHooks]
        apply runRvalue_eq_of_eq
        unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
        dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, pure, EStateM.pure, bind,
          EStateM.bind]
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = { localId := dstIdx, projection := #[] } := rfl
      have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.cast .pointerExposeProvenance (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ }, .error (.unsupported "exposeProvenance in cast")) := by
        rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_s]
        dsimp only []
        rw [hcast_err]
      exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_cast_with_exposed_provenance_divergence` (Forged-Provenance Bug)**:
in `StateRelLM3_1`-related states, executing `_d = const c as *(const|mut) T`
(`CastKind.PointerWithExposedProvenance`) on a `usize` integer constant `c`
(`c.val = .scalar (.int ⟨bits, 8⟩)`, `bits < 2 ^ 64`) diverges:

1. Anneal's `stepMirFn` (`Places.lean:2818-2825`) unconditionally fabricates
   live pointer provenance
   `{ allocId := bits / 65536, offsetBytes := bits % 65536 }` in `_d` without
   checking whether any pointer was ever exposed, allowing
   `65536_usize as *const T` to forge tag `1` for an unexposed local.
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) fails closed
   with `StepError.unsupported "pointerFromExposedAddress in cast"`. -/
theorem step_cast_with_exposed_provenance_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx : Local} {c : ConstOperand} {castTy : Ty}
    {dstDecl : LocalDecl} {dstMut castMut : Mutability} {dstPointee : RigidTy}
    {bits : Nat} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩
        (.cast .pointerWithExposedProvenance (.constant c) castTy), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (hc_ty : c.ty.kind = .uint .usize)
    (hc_val : c.val = .scalar (.int ⟨bits, 8⟩))
    (hbits_lt : bits < 2 ^ 64)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead) :
    (∃ s', stepMirFn body s = .step s' ∧
      get? s'.frame.locals dstIdx =
        some (.init (.ptr { allocId := bits / 65536, offsetBytes := bits % 65536 } 8))) ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.unsupported "pointerFromExposedAddress in cast")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, _, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · obtain ⟨slot_d, _, hlt_af_d, _, hslot_d, _, _, _⟩ := hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hrv : evalRvalue s.frame.locals
        (.cast .pointerWithExposedProvenance (.constant c) castTy) s.memory
        body.localDecls body.layouts =
        .ok (.ptr { allocId := bits / 65536, offsetBytes := bits % 65536 } 8)
          s.frame.locals s.memory := by
      unfold evalRvalue evalOperand; dsimp only []; rw [hc_val]; rfl
    have hset := set?_eq_some_set hlt_af_d
      (LocalSlot.init (.ptr { allocId := bits / 65536, offsetBytes := bits % 65536 } 8))
    have hget_set : get? (s.frame.locals.set dstIdx
        (.init (.ptr { allocId := bits / 65536, offsetBytes := bits % 65536 } 8))) dstIdx =
        some (.init (.ptr { allocId := bits / 65536, offsetBytes := bits % 65536 } 8)) := by
      rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
    unfold evalStmt; dsimp only []; rw [hrv]; dsimp only []; rw [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hsd_ne
    | uninit => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
    | init _ => simp only [hset, hprot]; exact ⟨_, rfl, hget_set⟩
  · obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hsz8 : ValidScalarBytes ({ bits := bits, sizeBytes := 8 } : MirAst.ScalarInt).sizeBytes :=
      Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    have hcan8 : ({ bits := bits, sizeBytes := 8 } : MirAst.ScalarInt).bits <
        scalarModulus ({ bits := bits, sizeBytes := 8 } : MirAst.ScalarInt).sizeBytes := by
      simpa [scalarModulus] using hbits_lt
    obtain ⟨msc, htry_c, hrel_c⟩ := tryFromUInt_of_valid_canonical hsz8 hcan8
    have hc_prim : IsPrimScalarTy c.ty := Or.inr (Or.inr (Or.inr ⟨.usize, hc_ty⟩))
    have hop_c : annealEvalOperand body.localDecls body.layouts (translateOperand (.constant c))
        none { m with stack := ⟨#[tfa]⟩ } =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc)),
          translateTy c.ty body.layouts⟩ { m with stack := ⟨#[tfa]⟩ } := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only
        rw [hc_val]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton _ tfa rfl, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry_c, hc_prim.layoutOfEncoded]
    have hc_lay_eq : translateTy c.ty body.layouts =
        translateTy { kind := .uint .usize, layoutIdx := 0 } emptyLayoutTable := by
      unfold translateTy encodeTyId; rw [hc_ty]
    have hdst_enc : (translateTy dstDecl.ty body.layouts).ty = encodeRawPtrTyId dstPointee := by
      unfold translateTy encodeTyId; rw [hdst_ty]
    have hcast_enc : encodeTyId castTy = encodeRawPtrTyId dstPointee := by
      unfold encodeTyId; rw [hcast_ty]
    obtain ⟨pInfo, hpInfo⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId dstPointee hdst_thin
    have hsz8_raw : ValidScalarBytes 8 := Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    obtain ⟨msc_conv, htrunc_conv, hrel_conv⟩ :=
      truncateFromUInt_translateSizeBytes_raw hsz8_raw
        (BitVec.ofNat 128 (BitVec.ofNat 128 bits).toNat)
    let bits_conv := (BitVec.ofNat 128 (BitVec.ofNat 128 bits).toNat).toNat % 2 ^ (8 * 8)
    have hsz_eq : translateSizeBytes 8 = Miri.ABI.Size.ofBytes 8 := by decide
    have hzero8 : ((Miri.ABI.Size.ofBytes 8).bytes == 0) = false := by decide
    have htoUInt_c : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toUInt
        (translateSizeBytes 8) = .ok (BitVec.ofNat 128 bits) := by
      have hts : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc).toScalarInt =
          .ok msc := rfl
      have htb : msc.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 bits) := by
        rw [← hsz_eq]; exact hrel_c.toBits_eq
      rw [hsz_eq]
      unfold Miri.Memory.Scalar.toUInt Miri.Memory.Scalar.toBits
      simp only [hzero8, Bool.false_eq_true, ↓reduceIte, hts, htb,
        Except.mapError, bind, Except.bind]
    have htoUInt_conv : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_conv).toUInt
        (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 bits_conv) := by
      have hts : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_conv).toScalarInt =
          .ok msc_conv := rfl
      have htb : msc_conv.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 bits_conv) := by
        rw [← hsz_eq]; exact hrel_conv.toBits_eq
      unfold Miri.Memory.Scalar.toUInt Miri.Memory.Scalar.toBits
      simp only [hzero8, Bool.false_eq_true, ↓reduceIte, hts, htb,
        Except.mapError, bind, Except.bind]
    have htoUsize_conv : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_conv).toTargetUsize
        (Miri.ABI.Size.ofBytes 8) = .ok (UInt64.ofNat bits_conv) := by
      have hcan_conv : bits_conv < scalarModulus 8 := by
        rw [scalarModulus_eq_two_pow]; exact Nat.mod_lt _ (by decide)
      have hbv_lt : (BitVec.ofNat 128 bits_conv).toNat = bits_conv :=
        bitVec_ofNat_toNat_of_valid hsz8_raw hcan_conv
      have hnot_gt : ¬(bits_conv > 18446744073709551615) := by
        have hlt64 : bits_conv < 2 ^ 64 := Nat.mod_lt _ (by decide)
        omega
      unfold Miri.Memory.Scalar.toTargetUsize
      rw [htoUInt_conv]
      change (if (BitVec.ofNat 128 bits_conv).toNat > 18446744073709551615 then
          Except.error (Miri.Memory.ScalarError.integerConversionOverflow _)
        else
          Except.ok (UInt64.ofNat (BitVec.ofNat 128 bits_conv).toNat)) = _
      rw [hbv_lt]
      simp only [hnot_gt, ↓reduceIte]
    have hcast_err : Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16
        ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy c.ty body.layouts⟩
        .PointerWithExposedProvenance (encodeTyId castTy)
        ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } =
        .error (.unsupported "pointerFromExposedAddress in cast") { m with stack := ⟨#[tfa]⟩ } := by
      let usizeLay := translateTy { kind := .uint .usize, layoutIdx := 0 } emptyLayoutTable
      let st_a : AnnealStepState := { m with stack := ⟨#[tfa]⟩ }
      have husize_enc : usizeLay.ty = 25 := rfl
      have husize_lay : usizeLay.layout = scalarLayoutData 8 false := rfl
      have husize_info : castTypeInfoOfEncodedTyId 25 = .ok (.integer .usize) := rfl
      have hti_usize : (annealCastHooks body.layouts).typeInfo () usizeLay.ty =
          pure (.integer .usize) := rfl
      have hti_dst : (annealCastHooks body.layouts).typeInfo ()
          (translateTy dstDecl.ty body.layouts).ty = pure (.rawPointer pInfo) := by
        unfold annealCastHooks
        simp only [hdst_enc, hpInfo]
      have htarget_hk : Miri.ABI.Size.fromBits (annealCastHooks body.layouts).target.pointerWidth.bits =
          Miri.ABI.Size.ofBytes 8 := by dsimp only [annealCastHooks]; decide
      have henf : (annealCastHooks body.layouts).enforceValidity () usizeLay = pure true := rfl
      have hread_m : (annealCastHooks body.layouts).readImmediate ()
          ⟨.immediate (.scalar (.fromScalarInt msc)), usizeLay⟩ =
          pure ⟨.scalar (.fromScalarInt msc), usizeLay⟩ := rfl
      have hdl : (annealCastHooks body.layouts).destLayout
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩ =
          translateTy dstDecl.ty body.layouts := rfl
      have hintLike : Miri.Interpreter.Cast.intLikeValue (annealCastHooks body.layouts) ()
          (.fromScalarInt msc) usizeLay st_a =
          .ok (BitVec.ofNat 128 bits, false) st_a := by
        with_unfolding_all
          unfold Miri.Interpreter.Cast.intLikeValue annealCastHooks
          simp only [husize_enc, husize_lay, husize_info, scalarLayoutData,
            Miri.ABI.BackendRepr.isSigned, Miri.ABI.Scalar.isSigned,
            Miri.MIR.IntegerKind.signed, htoUInt_c, Except.mapError,
            Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure]
          rfl
      have hint_cast : Miri.Interpreter.IntegerCast.cast
          (.integer ⟨Miri.ABI.Size.ofBytes 16, .u128⟩)
          (.ofUInt128 (BitVec.ofNat 128 bits))
          (.integer ⟨translateSizeBytes 8, .usize⟩) = .ok msc_conv := by
        with_unfolding_all
          change ((Miri.Memory.ScalarInt.truncateFromUInt
              (BitVec.ofNat 128 (BitVec.ofNat 128 bits).toNat) (translateSizeBytes 8)
              |>.mapError Miri.Interpreter.IntegerCastError.scalar).bind
              fun (result, _) => Except.ok result) = _
          rw [htrunc_conv]
          rfl
      have hcast_int : Miri.Interpreter.Cast.castFromIntLike (annealCastHooks body.layouts) ()
          (.fromScalarInt msc) usizeLay usizeLay st_a =
          .ok ⟨.scalar (.fromScalarInt msc_conv), usizeLay⟩ st_a := by
        unfold Miri.Interpreter.Cast.castFromIntLike
        rw [EStateM.bind_eq_ok hintLike]
        with_unfolding_all
          simp only [hti_usize, husize_lay, scalarLayoutData, hint_cast,
            Except.mapError, bind, EStateM.bind, pure, EStateM.pure]
          rfl
      have hpwep : Miri.Interpreter.Cast.pointerWithExposedProvenance
          (annealCastHooks body.layouts) ()
          ⟨.scalar (.fromScalarInt msc), usizeLay⟩
          (translateTy dstDecl.ty body.layouts) st_a =
          .error (.unsupported "pointerFromExposedAddress in cast") st_a := by
        unfold Miri.Interpreter.Cast.pointerWithExposedProvenance
        rw [hti_usize, pure_bind]
        dsimp only []
        rw [hti_dst, pure_bind]
        dsimp only []
        with_unfolding_all
          erw [EStateM.bind_eq_ok (a := Miri.Memory.Scalar.fromScalarInt msc) (s' := st_a) rfl]
          erw [EStateM.bind_eq_ok (a := usizeLay) (s' := st_a) rfl]
          erw [EStateM.bind_eq_ok hcast_int]
          erw [EStateM.bind_eq_ok (a := Miri.Memory.Scalar.fromScalarInt msc_conv) (s' := st_a) rfl]
          erw [EStateM.bind_eq_ok (a := UInt64.ofNat bits_conv) (s' := st_a)
            (by rw [htarget_hk, htoUsize_conv]; rfl)]
          rfl
      rw [hc_lay_eq]
      change Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16
          ⟨.immediate (.scalar (.fromScalarInt msc)), usizeLay⟩
          .PointerWithExposedProvenance (encodeTyId castTy)
          ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩ st_a = _
      unfold Miri.Interpreter.Cast.cast
      simp only [hdl, hdst_enc, hcast_enc, henf, hti_usize, hread_m, beq_self_eq_true,
        Bool.false_eq_true, ↓reduceIte, pure_bind]
      with_unfolding_all
        change
          (do
            let result ← Miri.Interpreter.Cast.pointerWithExposedProvenance
              (annealCastHooks body.layouts) ()
              ⟨.scalar (.fromScalarInt msc), usizeLay⟩
              (translateTy dstDecl.ty body.layouts)
            (annealCastHooks body.layouts).writeImmediate () result.imm
              ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩) st_a = _
      rw [EStateM.bind_eq_error hpwep]
    have hm_stmt : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .pointerWithExposedProvenance (.constant c) castTy), span⟩) m =
        Miri.Interpreter.runRvalue
          (do
            let destPlace ← annealEvalPlace body.localDecls body.layouts
              (translatePlace ⟨dstIdx, .nil⟩)
            let src ← annealEvalOperand body.localDecls body.layouts
              (translateOperand (.constant c)) none
            Miri.Interpreter.Cast.cast (annealCastHooks body.layouts) () 16 src
              .PointerWithExposedProvenance (encodeTyId castTy) destPlace) m := by
      unfold Miri.Interpreter.Step.evalStatement translateStmt
      dsimp only [translateStmtKind, translateRvalue, translateCastKind, annealStepHooks]
      apply runRvalue_eq_of_eq
      unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
      dsimp only [Miri.Interpreter.RvalueHooks.evalOperandAt, pure, EStateM.pure, bind,
        EStateM.bind]
    have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = { localId := dstIdx, projection := #[] } := rfl
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
          (.cast .pointerWithExposedProvenance (.constant c) castTy), span⟩) m =
        ({ m with stack := ⟨#[tfa]⟩ }, .error (.unsupported "pointerFromExposedAddress in cast")) := by
      rw [hm_stmt, htr_dst]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hop_c, hcast_err]
    exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err⟩

/-- **`step_cast_ptrToPtr_scalar_divergence`**: in `StateRelLM3_1` states
where `_s : *(const|mut) T` (`isThinRawPtrPointee`) holds a provenance-less
8-byte integer scalar `.init (.scalar sc)` (such as `0 as *const T`) and
`_d : *(const|mut) V` (`isThinRawPtrPointee`) is a live immediate local,
executing `_d = copy _s as *(const|mut) V` (`CastKind.PtrToPtr`) diverges:

1. Anneal's `stepMirFn` (`Places.lean:2798`) only matches `.ptr` and wide
   `.aggregate` pointers in `CastKind.PtrToPtr`, rejecting `.scalar sc` with
   `MirStepNode.unsupported`; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) steps cleanly
   via `Cast.ptrToPtr` (`8 == 8`), storing the provenance-less pointer scalar
   `.fromScalarInt msc` (`ScalarRel sc msc`) in `_d`. -/
theorem step_cast_ptrToPtr_scalar_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx srcIdx : Local} {castTy : Ty}
    {dstDecl srcDecl : LocalDecl}
    {srcMut dstMut castMut : Mutability} {srcPointee dstPointee : RigidTy}
    {sc : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_src : get? body.localDecls srcIdx = some srcDecl)
    (hsrc_ty : srcDecl.ty.kind = .rawPtr srcMut srcPointee)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hcast_ty : castTy.kind = .rawPtr castMut dstPointee)
    (hsrc_thin : isThinRawPtrPointee srcPointee = true)
    (hdst_thin : isThinRawPtrPointee dstPointee = true)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame srcIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_s : get? s.frame.locals srcIdx = some (.init (.scalar sc))) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' msc,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue evalOperand readProjectedValue
    dsimp only []
    rw [hslot_s]
  · obtain ⟨himm_d, himm_s⟩ := himm tf hframes
    have hm_stmt := evalStatement_assign_cast_ptrToPtr_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (.copy ⟨srcIdx, .nil⟩) castTy span m
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    obtain ⟨slot_s, mls_s, _, hlt_sa, hslot_sa, hmls_sa, hmls_sa_eq, hloc_s⟩ :=
      hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_src
    have hcache_s : ∀ l, mls_s.layout = some l → l = translateTy srcDecl.ty body.layouts :=
      hloc_s.cachedLayout_eq
    have himm_sa : ∀ mp, mls_s.value ≠ .live (.indirect mp) :=
      himm_s.cache_layout hlt_d _ mls_s hmls_sa
    have hss_eq : slot_s = .init (.scalar sc) := Option.some.inj (hslot_sa.symm.trans hslot_s)
    subst hss_eq
    rcases hloc_s.rawPtr_immediate_cases hsrc_ty himm_sa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨sc', msc, hsc_eq, _, hrel_sc, hms_sc⟩ | ⟨_, _, h, _⟩
    · cases h
    · cases h
    · injection hsc_eq with hv; injection hv with hsc'; subst hsc'
      have hmls_sa' : tfa.locals[srcIdx]'hlt_sa =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc))), mls_s.layout⟩ := by
        rw [hmls_sa_eq]; rcases mls_s with ⟨v0, l0⟩; dsimp only at hms_sc; subst hms_sc; rfl
      have hsrc_ok := annealEvalOperand_copy_live (known := none) (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_sa hdecl_src hmls_sa' hcache_s
      let tfb := cacheFrameLocalLayout tfa srcIdx hlt_sa (translateTy srcDecl.ty body.layouts)
      have hstate_b := hstate_a.cache_layout rfl hdecl_src hlt_sa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      subst hsdb_eq
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_sa _) mls_db hmls_db
      obtain ⟨oldImm, hmdb_imm⟩ : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
        rcases hloc_db.rawPtr_immediate_cases hdst_ty himm_db with
          ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
        · exact absurd rfl hsd_ne
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
        rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmdb_imm; subst hmdb_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hcast_sc : Miri.Interpreter.Cast.ptrToPtr (annealCastHooks body.layouts) ()
          ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
          (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ } =
          .ok ⟨.scalar (.fromScalarInt msc), translateTy dstDecl.ty body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        have hsrc_enc : (translateTy srcDecl.ty body.layouts).ty = encodeRawPtrTyId srcPointee := by
          unfold translateTy encodeTyId; rw [hsrc_ty]
        have hdst_enc : (translateTy dstDecl.ty body.layouts).ty = encodeRawPtrTyId dstPointee := by
          unfold translateTy encodeTyId; rw [hdst_ty]
        have hsrc_sz : (translateTy srcDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
          unfold translateTy; rw [hsrc_ty]; rfl
        have hdst_sz : (translateTy dstDecl.ty body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 := by
          unfold translateTy; rw [hdst_ty]; rfl
        obtain ⟨i₁, hi₁⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId srcPointee hsrc_thin
        obtain ⟨i₂, hi₂⟩ := castTypeInfoOfEncodedTyId_encodeRawPtrTyId dstPointee hdst_thin
        unfold Miri.Interpreter.Cast.ptrToPtr annealCastHooks
        simp only [hsrc_enc, hdst_enc, hsrc_sz, hdst_sz, hi₁, hi₂,
          bind, EStateM.bind, pure, EStateM.pure]
        rfl
      have hread_src : annealReadImmediate
          ⟨.immediate (.scalar (.fromScalarInt msc)), translateTy srcDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .ok ⟨.scalar (.fromScalarInt msc), translateTy srcDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } := rfl
      have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
      have htr_src : translateOperand (.copy ⟨srcIdx, .nil⟩) = .Copy ⟨srcIdx, #[]⟩ := rfl
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt
            ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar (.fromScalarInt msc))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt, htr_dst, htr_src]; unfold Miri.Interpreter.runRvalue
        rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hsrc_ok,
          miri_cast_dispatch_ptrToPtr_eq body.layouts srcMut dstMut castMut srcPointee dstPointee
            srcDecl.ty dstDecl.ty castTy hsrc_ty hdst_ty hcast_ty hsrc_thin,
          EStateM.bind_eq_ok hread_src, EStateM.bind_eq_ok hcast_sc, hw_ok]
      refine ⟨_, _, msc, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_ok rfl hfrb.location_eq, rfl, hrel_sc, ?_⟩
      simp [Array.getElem?_set_self]
    · cases h

private theorem scalarOps_binary_offset_scalarInt_byte_eq
    (ld : List LocalDecl) (ly : LayoutTable)
    {ptrTy rhsTy : Ty} {mutability : Mutability} {pointeeKind : RigidTy}
    (hptr_ty : ptrTy.kind = .rawPtr mutability pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    {sc_p : MirAst.ScalarInt} {msc_p : Miri.Memory.ScalarInt}
    (hrel_p : ScalarRel sc_p msc_p) (hsz_p : sc_p.sizeBytes = 8)
    {sc_r : MirAst.ScalarInt} {msc_r : Miri.Memory.ScalarInt}
    (hrel_r : ScalarRel sc_r msc_r) (hsz_r : sc_r.sizeBytes = 8) (hbits_r : sc_r.bits < 2 ^ 32)
    (st : AnnealStepState) :
    Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Offset
      ⟨.scalar (.fromScalarInt msc_p), translateTy ptrTy ly⟩
      ⟨.scalar (.fromScalarInt msc_r), translateTy rhsTy ly⟩ st =
      match Miri.Interpreter.ptrOffsetInbounds annealPointerArithmetic
          (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc_p.bits))
          (Int64.ofInt (sc_r.bits : Int))
          (annealResolvePtr st.machine) (annealLookupAlloc st.machine) with
      | .error (.access _) => .error (.undefinedBehavior "pointer Offset out of bounds") st
      | .error (.pointer _) => .error (.invalidProgram "pointer Offset arithmetic error") st
      | .ok nextPtr =>
        match Miri.Memory.Scalar.fromMaybePointer annealTargetDataLayout nextPtr with
        | .error err => .error (Miri.Interpreter.ScalarOps.scalarError err) st
        | .ok result => .ok ⟨.scalar result, translateTy ptrTy ly⟩ st := by
  have hptr_enc : (translateTy ptrTy ly).ty = encodeRawPtrTyId pointeeKind := by
    unfold translateTy encodeTyId; rw [hptr_ty]
  have hdispatch :
      Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () .Offset
        ⟨.scalar (.fromScalarInt msc_p), translateTy ptrTy ly⟩
        ⟨.scalar (.fromScalarInt msc_r), translateTy rhsTy ly⟩ st =
      annealPointerBinary ly .Offset
        ⟨.scalar (.fromScalarInt msc_p), translateTy ptrTy ly⟩
        ⟨.scalar (.fromScalarInt msc_r), translateTy rhsTy ly⟩ st := by
    rw [scalarOps_binary_def]
    unfold annealScalarOpsHooks
    rcases hpt with hpt | hpt <;> rcases hrhs_ty with hrhs | hrhs
    · have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
      have hr : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
      simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
    · have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
      have hr : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
      simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
    · have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
      have hr : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
      simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
    · have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
      have hr : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
      simp only [hp, hr, classifyEncodedTyId, bind, EStateM.bind, pure, EStateM.pure]
  rw [hdispatch]
  have htb : msc_r.toBits (Miri.ABI.Size.ofBytes 8) = .ok (BitVec.ofNat 128 sc_r.bits) := by
    have hsz : Miri.ABI.Size.ofBytes 8 = translateSizeBytes sc_r.sizeBytes := by rw [hsz_r]; rfl
    rw [hsz]; exact hrel_r.toBits_eq
  have hfrom1 : Miri.Memory.Scalar.fromInt (Prov := AnnealProv) 1 (Miri.ABI.Size.ofBytes 8) =
      .ok (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 1)) := rfl
  have htoInt64 : (Int64.ofInt (sc_r.bits : Int)).toInt < 0 ↔ False := by
    rw [int64_toInt_ofInt_of_lt_u32 sc_r.bits hbits_r]
    exact ⟨fun h => by omega, False.elim⟩
  have hlt0_false : decide ((Int64.ofInt (sc_r.bits : Int)).toInt < 0) = false :=
    decide_eq_false htoInt64.mp
  unfold annealPointerBinary
  have hop_ne : (Miri.MIR.BinOp.Offset != .Offset) = false := rfl
  have htoSc_l : (Miri.Interpreter.Immediate.scalar
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_p)).toScalar =
      .ok (.fromScalarInt msc_p) := rfl
  have htoSc_r : (Miri.Interpreter.Immediate.scalar
      (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_r)).toScalar =
      .ok (.fromScalarInt msc_r) := rfl
  have htoSi_r : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_r).toScalarInt =
      .ok msc_r := rfl
  have htoSi_1 : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv)
      (Miri.Memory.ScalarInt.ofUInt64 1)).toScalarInt =
      .ok (Miri.Memory.ScalarInt.ofUInt64 1) := rfl
  have htoPtr_l : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) msc_p).toPointer
      annealTargetDataLayout = .ok (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc_p.bits)) :=
    scalar_fromScalarInt_toPointer_eq hrel_p hsz_p
  rcases hpt with hpt | hpt <;> rcases hrhs_ty with hrhs | hrhs
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel_r hsz_r hbits_r .usize (Or.inl rfl)
    have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 false := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 20 ly =
        { ty := 20, layout := scalarLayoutData 1 false } := rfl
    have hisSized : (!(({ ty := 20, layout := scalarLayoutData 1 false } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 20, layout := scalarLayoutData 1 false } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 false).backendRepr.isSigned = .ok false := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l, htoPtr_l,
      hp, rawPtrPointeeEncodedTyId?, hpt_lay, hisSized, hr_ty, hr_lay, classifyEncodedTyId,
      htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 false).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 false).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel_r hsz_r hbits_r .isize (Or.inr rfl)
    have hp : (translateTy ptrTy ly).ty = 70 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 true := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 20 ly =
        { ty := 20, layout := scalarLayoutData 1 false } := rfl
    have hisSized : (!(({ ty := 20, layout := scalarLayoutData 1 false } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 20, layout := scalarLayoutData 1 false } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 true).backendRepr.isSigned = .ok true := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l, htoPtr_l,
      hp, rawPtrPointeeEncodedTyId?, hpt_lay, hisSized, hr_ty, hr_lay, classifyEncodedTyId,
      htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 true).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 false).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel_r hsz_r hbits_r .usize (Or.inl rfl)
    have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 25 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 false := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 10 ly =
        { ty := 10, layout := scalarLayoutData 1 true } := rfl
    have hisSized : (!(({ ty := 10, layout := scalarLayoutData 1 true } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 10, layout := scalarLayoutData 1 true } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 false).backendRepr.isSigned = .ok false := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l, htoPtr_l,
      hp, rawPtrPointeeEncodedTyId?, hpt_lay, hisSized, hr_ty, hr_lay, classifyEncodedTyId,
      htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 false).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 true).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  · obtain ⟨scaledInt, hmul, htisize⟩ :=
      mulWithOverflow_stride_one_eq hrel_r hsz_r hbits_r .isize (Or.inr rfl)
    have hp : (translateTy ptrTy ly).ty = 63 := by rw [hptr_enc, hpt]; rfl
    have hr_ty : (translateTy rhsTy ly).ty = 15 := by unfold translateTy encodeTyId; rw [hrhs]
    have hr_lay : (translateTy rhsTy ly).layout = scalarLayoutData 8 true := by
      unfold translateTy; rw [hrhs]; rfl
    have hpt_lay : layoutOfEncodedTyId 10 ly =
        { ty := 10, layout := scalarLayoutData 1 true } := rfl
    have hisSized : (!(({ ty := 10, layout := scalarLayoutData 1 true } :
        Miri.Interpreter.LocalLayout).layout.isSized &&
        decide (({ ty := 10, layout := scalarLayoutData 1 true } :
          Miri.Interpreter.LocalLayout).layout.size.bytes.toNat < 2 ^ 63))) = false := by decide
    have hisSigned : (scalarLayoutData 8 true).backendRepr.isSigned = .ok true := rfl
    simp only [hop_ne, Bool.false_eq_true, ↓reduceIte, htoSc_l, htoPtr_l,
      hp, rawPtrPointeeEncodedTyId?, hpt_lay, hisSized, hr_ty, hr_lay, classifyEncodedTyId,
      htoSc_r, htoSi_r]
    have hsz8 : (scalarLayoutData 8 true).size = Miri.ABI.Size.ofBytes 8 := rfl
    have hsz1 : Int.ofNat (scalarLayoutData 1 true).size.bytes.toNat = 1 := rfl
    simp only [hsz8, hsz1, htb, hfrom1, htoSi_1, hmul, htisize, hisSigned, hlt0_false,
      Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- **`step_binOp_offset_scalar_zero_divergence`**: in `StateRelLM3_1`-related
states where `_p : *(const|mut) (u8|i8)` holds a provenance-less integer scalar
`.init (.scalar sc)` (such as `0 as *const u8`), `rhsOp` evaluates to `0`
(`sc_rhs.bits = 0`), and `_d` is live immediate, executing
`_d = Offset(copy _p, rhsOp)` diverges:

1. Anneal's `stepMirFn` rejects `Offset` on `.scalar` pointers with
   `MirStepNode.unsupported`; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) succeeds via
   `ptrOffsetInbounds_zero_ok` (matching Rust `ptr::offset(_, 0)` semantics on
   null/integer pointers), storing `.fromScalarInt msc_out`
   (`ScalarRel sc msc_out`) in `_d`. -/
theorem step_binOp_offset_scalar_zero_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand}
    {dstDecl ptrDecl : LocalDecl} {ptrMut dstMut : Mutability}
    {pointeeKind : RigidTy} {rhsTy : Ty} {sc sc_rhs : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc_rhs) s.frame.locals)
    (hrhs_zero : sc_rhs.bits = 0) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m' tf' msc_out,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      ScalarRel sc msc_out ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt msc_out)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hlhs : evalOperand s.frame.locals (.copy ⟨ptrIdx, .nil⟩) s.memory.borrows
        s.memory.globals body.layouts s.memory.callerLocals =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_p]
    unfold evalStmt evalRvalue; dsimp only []
    rw [hlhs]; dsimp only []; rw [hrhs_eval]; dsimp only []; unfold evalScalarBinOp
    cases sc.sizeBytes.beq 0 <;> cases sc.sizeBytes.beq sc_rhs.sizeBytes <;> rfl
  · obtain ⟨himm_d, himm_p⟩ := himm tf hframes
    have hop_tf := hop_rhs tf hframes
    have hrhs_prim : IsPrimScalarTy rhsTy := by
      rcases hrhs_ty with hk | hk
      · exact Or.inr (Or.inr (Or.inr ⟨.usize, hk⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨.isize, hk⟩))
    have hm_stmt := evalStatement_assign_binOp_offset_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (.copy ⟨ptrIdx, .nil⟩) rhsOp span m
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hop_tfa := hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d
      (translateTy dstDecl.ty body.layouts)
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    have hsp_eq : slot_p = .init (.scalar sc) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨sc', msc_p, hsc_eq, hsz8_p, hrel_p, hmp_sc⟩ | ⟨_, _, h, _⟩
    · cases h
    · cases h
    · injection hsc_eq with hv; injection hv with hsc'; subst hsc'
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc_p))), mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_sc; subst hmp_sc; rfl
      have hlhs_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_pa'
        hcache_p
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hop_tfb := hop_tfa.of_cacheFrameLocalLayout ptrIdx hlt_pa
        (translateTy ptrDecl.ty body.layouts)
      have hread_lhs : annealReadImmediate
          ⟨.immediate (.scalar (.fromScalarInt msc_p)), translateTy ptrDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .ok ⟨.scalar (.fromScalarInt msc_p), translateTy ptrDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } := rfl
      rcases evalOperand_scalar_lm3_1_simulation hstate_b rfl hop_tfb hrhs_prim none with
        ⟨_, _, hrhs_ub, _⟩ |
        ⟨sc_r', msc_r, tfc, hrhs_ok, hm_rhs_ok, hstate_c, hrel_imm, _, htfc_preserve⟩
      · rw [hrhs_eval] at hrhs_ub; cases hrhs_ub
      · rw [hrhs_eval] at hrhs_ok
        injection hrhs_ok with hv_r _; injection hv_r with hsc_r_eq; subst hsc_r_eq
        have hsc_rel : ScalarRel sc_rhs msc_r ∧ sc_rhs.sizeBytes = 8 := by
          cases hrel_imm with
          | scalar _ _ hrel hsz _ _ =>
            have hlay_rhs : (translateTy rhsTy body.layouts).layout.size =
                Miri.ABI.Size.ofBytes 8 := by
              rcases hrhs_ty with hk | hk <;> (unfold translateTy; rw [hk]; rfl)
            rw [hlay_rhs] at hsz
            have hb : (8 : UInt64) = UInt64.ofNat sc_rhs.sizeBytes :=
              congrArg Miri.ABI.Size.bytes hsz
            have hcan := hrel.validBytes
            have hsz8 : sc_rhs.sizeBytes = 8 := by
              rcases hcan with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb ⊢ <;>
                first | rfl | cases hb
            exact ⟨hrel, hsz8⟩
        obtain ⟨msc_out, hrel_addr, href⟩ :=
          memPlace_toRef_withoutProvenance (UInt64.ofNat sc.bits) none
        have hsc_eq_addr : (⟨(UInt64.ofNat sc.bits).toNat, 8⟩ : MirAst.ScalarInt) = sc := by
          have hcan := hrel_p.canonical
          rw [hsz8_p, scalarModulus_eq_two_pow] at hcan
          have hu : (UInt64.ofNat sc.bits).toNat = sc.bits := by
            rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hcan
          rcases sc with ⟨b, sz⟩
          dsimp only at hu hsz8_p
          rw [hu, hsz8_p]
        rw [hsc_eq_addr] at hrel_addr
        have hfrom_mp : Miri.Memory.Scalar.fromMaybePointer (Prov := AnnealProv)
            annealTargetDataLayout (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) =
            .ok (.fromScalarInt msc_out) := by
          unfold Miri.Interpreter.MemPlace.toRef Miri.Interpreter.Immediate.newPointerWithMeta at href
          dsimp only [Except.map, bind, Except.bind] at href
          cases hfm : Miri.Memory.Scalar.fromMaybePointer (Prov := AnnealProv)
              annealTargetDataLayout (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) with
          | error e => rw [hfm] at href; cases href
          | ok v =>
            rw [hfm] at href
            injection href with hi
            injection hi with hv_eq
            rw [hv_eq]
        have hpoff0 : Miri.Interpreter.ptrOffsetInbounds annealPointerArithmetic
            (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits))
            (Int64.ofInt (sc_rhs.bits : Int))
            (annealResolvePtr m.machine) (annealLookupAlloc m.machine) =
            .ok (Miri.Memory.Pointer.withoutProvenance (UInt64.ofNat sc.bits)) := by
          rw [hrhs_zero]; exact ptrOffsetInbounds_zero_ok m.machine _
        have hbin_ok : Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
            ⟨.scalar (.fromScalarInt msc_p), translateTy ptrDecl.ty body.layouts⟩
            ⟨.scalar (.fromScalarInt msc_r), translateTy rhsTy body.layouts⟩
            { m with stack := ⟨#[tfc]⟩ } =
            .ok ⟨.scalar (.fromScalarInt msc_out), translateTy ptrDecl.ty body.layouts⟩
              { m with stack := ⟨#[tfc]⟩ } := by
          rw [scalarOps_binary_offset_scalarInt_byte_eq body.localDecls body.layouts hptr_ty hpt
            hrhs_ty hrel_p hsz8_p hsc_rel.1 hsc_rel.2 (by omega), hpoff0]
          dsimp only []
          rw [hfrom_mp]
        have hlay_eq : translateTy ptrDecl.ty body.layouts =
            translateTy dstDecl.ty body.layouts := by
          unfold translateTy encodeTyId; rw [hptr_ty, hdst_ty]
        have hassert_ok : assertRvalueLayoutPub (translateTy ptrDecl.ty body.layouts)
            (translateTy dstDecl.ty body.layouts) { m with stack := ⟨#[tfc]⟩ } =
            .ok () { m with stack := ⟨#[tfc]⟩ } := by
          unfold assertRvalueLayoutPub; simp [hlay_eq, pure, EStateM.pure]
        have hfr_c := hstate_c.frame_rel_singleton rfl
        obtain ⟨slot_dc, mls_dc, _, hlt_dc, hslot_dc, hmls_dc, _, hloc_dc⟩ :=
          hfr_c.lookup_local hdecl_dst
        have hsdc_eq : slot_dc = slot_d := Option.some.inj (hslot_dc.symm.trans hslot_d)
        subst hsdc_eq
        have himm_db := (himm_d.cache_layout hlt_d (translateTy dstDecl.ty body.layouts)).cache_layout
          hlt_pa (translateTy ptrDecl.ty body.layouts)
        have himm_dc : ∀ mp, mls_dc.value ≠ .live (.indirect mp) := by
          intro mp hmp
          have hp_c := htfc_preserve dstIdx
          rw [hmls_dc] at hp_c
          dsimp only [Option.map] at hp_c
          cases hdb : tfb.locals[dstIdx]? with
          | none => rw [hdb] at hp_c; cases hp_c
          | some mls_b =>
            rw [hdb] at hp_c
            injection hp_c with hv_eq
            exact himm_db mls_b hdb mp (hv_eq.symm.trans hmp)
        obtain ⟨oldImm, hmdc_imm⟩ : ∃ oldImm, mls_dc.value = .live (.immediate oldImm) := by
          rcases hloc_dc.rawPtr_immediate_cases hdst_ty himm_dc with
            ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
          · exact absurd rfl hsd_ne
          · exact ⟨_, h⟩
          · exact ⟨_, h⟩
          · exact ⟨_, h⟩
        have hdc_live : tfc.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_dc.layout⟩ := by
          rw [hmls_dc]; rcases mls_dc with ⟨v0, l0⟩; dsimp only at hmdc_imm; subst hmdc_imm; rfl
        have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_live
        have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc_out))
          (m := { m with stack := ⟨#[tfc]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_dc hget_dc
        have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
        have htr_lhs : translateOperand (.copy ⟨ptrIdx, .nil⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt
              ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
            ({ m with stack := ⟨#[{ tfc with
                locals := tfc.locals.set dstIdx
                  { tfc.locals[dstIdx]'hlt_dc with
                    value := .live (.immediate (.scalar (.fromScalarInt msc_out))) }
                  hlt_dc }]⟩ }, .ok ()) := by
          rw [hm_stmt, htr_dst, htr_lhs]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
            EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_ok hm_rhs_ok,
            EStateM.bind_eq_ok hbin_ok, EStateM.bind_eq_ok hassert_ok, hw_ok]
        refine ⟨_, _, msc_out, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq
          hbb hstmt hm_ok rfl hfr_c.location_eq, rfl, hrel_addr, ?_⟩
        simp [Array.getElem?_set_self]
    · cases h

/-- **`step_binOp_offset_scalar_nonzero_divergence`**: in `StateRelLM3_1`
states where `_p : *(const|mut) (u8|i8)` holds a provenance-less integer scalar
`.init (.scalar sc)` (such as `0 as *const u8`) and `rhsOp` evaluates to a
non-zero offset `sc_rhs` (`0 < sc_rhs.bits < 2 ^ 32`), executing
`_d = Offset(copy _p, rhsOp)` diverges:

1. Anneal's `stepMirFn` fails with `MirStepNode.unsupported`; while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) reports
   `StepError.undefinedBehavior "pointer Offset out of bounds"` via
   `ptrOffsetInbounds_withoutProvenance_err`. -/
theorem step_binOp_offset_scalar_nonzero_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local} {rhsOp : MirAst.Operand}
    {dstDecl ptrDecl : LocalDecl} {ptrMut : Mutability}
    {pointeeKind : RigidTy} {rhsTy : Ty} {sc sc_rhs : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hpt : pointeeKind = .uint .u8 ∨ pointeeKind = .int .i8)
    (hrhs_ty : rhsTy.kind = .uint .usize ∨ rhsTy.kind = .int .isize)
    (hop_rhs : ∀ topFrame, m.stack.frames = #[topFrame] →
      WellTypedScalarOperand body topFrame rhsOp rhsTy)
    (himm_ptr : ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame ptrIdx)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.scalar sc)))
    (hrhs_eval : evalOperand s.frame.locals rhsOp s.memory.borrows s.memory.globals body.layouts
      s.memory.callerLocals = .ok (.scalar sc_rhs) s.frame.locals)
    (hrhs_pos : 0 < sc_rhs.bits)
    (hrhs_lt : sc_rhs.bits < 2 ^ 32) :
    stepMirFn body s = MirStepNode.unsupported ∧
    ∃ m',
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .error (.undefinedBehavior "pointer Offset out of bounds")) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, _, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    have hlhs : evalOperand s.frame.locals (.copy ⟨ptrIdx, .nil⟩) s.memory.borrows
        s.memory.globals body.layouts s.memory.callerLocals =
        .ok (.scalar sc) s.frame.locals := by
      unfold evalOperand readProjectedValue; dsimp only []; rw [hslot_p]
    unfold evalStmt evalRvalue; dsimp only []
    rw [hlhs]; dsimp only []; rw [hrhs_eval]; dsimp only []; unfold evalScalarBinOp
    cases sc.sizeBytes.beq 0 <;> cases sc.sizeBytes.beq sc_rhs.sizeBytes <;> rfl
  · have himm_p := himm_ptr tf hframes
    have hop_tf := hop_rhs tf hframes
    have hrhs_prim : IsPrimScalarTy rhsTy := by
      rcases hrhs_ty with hk | hk
      · exact Or.inr (Or.inr (Or.inr ⟨.usize, hk⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨.isize, hk⟩))
    have hm_stmt := evalStatement_assign_binOp_offset_eq body.localDecls body.layouts
      ⟨dstIdx, .nil⟩ (.copy ⟨ptrIdx, .nil⟩) rhsOp span m
    obtain ⟨_, mls_d, _, hlt_d, _, _, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hop_tfa := hop_tf.of_cacheFrameLocalLayout dstIdx hlt_d
      (translateTy dstDecl.ty body.layouts)
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hstate_a.frame_rel_singleton rfl |>.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    have hsp_eq : slot_p = .init (.scalar sc) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨sc', msc_p, hsc_eq, hsz8_p, hrel_p, hmp_sc⟩ | ⟨_, _, h, _⟩
    · cases h
    · cases h
    · injection hsc_eq with hv; injection hv with hsc'; subst hsc'
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (.fromScalarInt msc_p))), mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_sc; subst hmp_sc; rfl
      have hlhs_ok := annealEvalOperand_copy_live (m := { m with stack := ⟨#[tfa]⟩ })
        (known := some (translateTy dstDecl.ty body.layouts)) rfl hlt_pa hdecl_ptr hmls_pa'
        hcache_p
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hop_tfb := hop_tfa.of_cacheFrameLocalLayout ptrIdx hlt_pa
        (translateTy ptrDecl.ty body.layouts)
      have hread_lhs : annealReadImmediate
          ⟨.immediate (.scalar (.fromScalarInt msc_p)), translateTy ptrDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } =
          .ok ⟨.scalar (.fromScalarInt msc_p), translateTy ptrDecl.ty body.layouts⟩
          { m with stack := ⟨#[tfb]⟩ } := rfl
      rcases evalOperand_scalar_lm3_1_simulation hstate_b rfl hop_tfb hrhs_prim none with
        ⟨_, _, hrhs_ub, _⟩ |
        ⟨sc_r', msc_r, tfc, hrhs_ok, hm_rhs_ok, _, hrel_imm, _, _⟩
      · rw [hrhs_eval] at hrhs_ub; cases hrhs_ub
      · rw [hrhs_eval] at hrhs_ok
        injection hrhs_ok with hv_r _; injection hv_r with hsc_r_eq; subst hsc_r_eq
        have hsc_rel : ScalarRel sc_rhs msc_r ∧ sc_rhs.sizeBytes = 8 := by
          cases hrel_imm with
          | scalar _ _ hrel hsz _ _ =>
            have hlay_rhs : (translateTy rhsTy body.layouts).layout.size =
                Miri.ABI.Size.ofBytes 8 := by
              rcases hrhs_ty with hk | hk <;> (unfold translateTy; rw [hk]; rfl)
            rw [hlay_rhs] at hsz
            have hb : (8 : UInt64) = UInt64.ofNat sc_rhs.sizeBytes :=
              congrArg Miri.ABI.Size.bytes hsz
            have hcan := hrel.validBytes
            have hsz8 : sc_rhs.sizeBytes = 8 := by
              rcases hcan with h1 | h1 | h1 | h1 | h1 <;> rw [h1] at hb ⊢ <;>
                first | rfl | cases hb
            exact ⟨hrel, hsz8⟩
        have hpoff_err := ptrOffsetInbounds_withoutProvenance_err m.machine
          (UInt64.ofNat sc.bits) sc_rhs.bits hrhs_pos hrhs_lt
        have hbin_err : Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks body.localDecls body.layouts) () .Offset
            ⟨.scalar (.fromScalarInt msc_p), translateTy ptrDecl.ty body.layouts⟩
            ⟨.scalar (.fromScalarInt msc_r), translateTy rhsTy body.layouts⟩
            { m with stack := ⟨#[tfc]⟩ } =
            .error (.undefinedBehavior "pointer Offset out of bounds")
              { m with stack := ⟨#[tfc]⟩ } := by
          rw [scalarOps_binary_offset_scalarInt_byte_eq body.localDecls body.layouts hptr_ty hpt
            hrhs_ty hrel_p hsz8_p hsc_rel.1 hsc_rel.2 hrhs_lt, hpoff_err]
        have htr_dst : translatePlace ⟨dstIdx, .nil⟩ = ⟨dstIdx, #[]⟩ := rfl
        have htr_lhs : translateOperand (.copy ⟨ptrIdx, .nil⟩) = .Copy ⟨ptrIdx, #[]⟩ := rfl
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt
              ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhsOp), span⟩) m =
            ({ m with stack := ⟨#[tfc]⟩ },
              .error (.undefinedBehavior "pointer Offset out of bounds")) := by
          rw [hm_stmt, htr_dst, htr_lhs]; unfold Miri.Interpreter.runRvalue
          rw [EStateM.bind_eq_ok hdst_eval, EStateM.bind_eq_ok hlhs_ok,
            EStateM.bind_eq_ok hread_lhs, estate_bind_assoc, EStateM.bind_eq_ok hm_rhs_ok,
            EStateM.bind_eq_error hbin_err]
        exact ⟨_, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
          hbb hstmt hm_err⟩
    · cases h

/-- **`step_rawPtr_deref_perm_divergence` (Spurious Tree Borrows Access on
`&raw (*_p)`)**: in `StateRelLM3_1`-related states where `_p : *(const|mut) T`
(`T` primitive scalar) holds `.init (.ptr ptrVal 8)` (`e ∈ allocMap`,
`e.tag = ptrVal.tag`), `_d` is live immediate, and `e.perm = .disabled` or
`e.perm = .frozen ∧ rawMut = .mut`, executing `_d = &raw rawMut (*_p)` diverges:

1. Anneal's `stepMirFn` (`Places.lean:2711-2713`) rejects `.disabled` parents
   and mutable raw reborrows of `.frozen` parents with `MirStepNode.fail .ub`;
   while
2. `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) steps cleanly
   via `MemPlace.toRef`, because `&raw (*_p)` in Rust / Miri
   (`core::ptr::addr_of!` / `addr_of_mut!`) is pure pointer re-tagging /
   passthrough with **zero** memory or Tree Borrows access. -/
theorem step_rawPtr_deref_perm_divergence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy}
    {ptrVal : ProvenancePtr} {e : AllocMapEntry} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (hslot_p : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)))
    (he : e ∈ allocMap) (htag : e.tag = ptrVal.tag)
    (hperm : e.perm = .disabled ∨ (e.perm = .frozen ∧ rawMut = .mut)) :
    stepMirFn body s = MirStepNode.fail .ub ∧
    ∃ m' tf' borTag,
      Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
        (m', .ok true) ∧
      m'.stack.frames = #[tf'] ∧
      (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes
              (annealStackBaseAddr e.allocId + UInt64.ofNat ptrVal.offsetBytes),
              .concrete e.allocId borTag⟩)))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, _, _, _, halloc, _⟩ := id hstate
  refine ⟨?_, ?_⟩
  · have hlookup := (halloc.borrow_sync e he).2
    rw [htag] at hlookup
    rw [stepMirFn_eq_of_not_other body s hcal hphase]
    simp only [hbb, hstmt]
    unfold evalStmt evalRvalue; dsimp only []
    rw [hslot_p]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
    rcases hperm with hp | ⟨hp, hm⟩
    · rw [hp]
    · rw [hp, hm]
  · obtain ⟨himm_d, himm_p⟩ := himm tf hframes
    obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
      hfr.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
        l = translateTy dstDecl.ty body.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
    let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
    have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
    have hfra := hstate_a.frame_rel_singleton rfl
    obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
      hfra.lookup_local hdecl_ptr
    have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
      hloc_p.cachedLayout_eq
    have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
      himm_p.cache_layout hlt_d _ mls_p hmls_pa
    have hsp_eq : slot_p = .init (.ptr ptrVal 8) := Option.some.inj (hslot_pa.symm.trans hslot_p)
    subst hsp_eq
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨h, _⟩ | ⟨h, _⟩ | ⟨_, _, h, _⟩ | ⟨ptrVal', mptr, hp_eq, hptrRel, hmp_ptr⟩
    · cases h
    · cases h
    · cases h
    · injection hp_eq with hv_eq; injection hv_eq with hpv_eq _; subst hpv_eq
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, ⟨e', he', htag', rfl⟩⟩ := hptrRel
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      obtain ⟨_, _, _, _, hpow_pk, _⟩ := hpk_prim.size_align_ok body.layouts
      obtain ⟨mismatch, hmis_any⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset _ hpow_pk
      have hder_ptr := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hpk_prim mptr hmis_any
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨mptr.withOptionalProvenance, .none, mismatch⟩,
              translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_ptr]; rfl
      have hkind : translateRawPtrKind rawMut ≠ .FakeForPtrMetadata := by
        cases rawMut <;> decide
      have hmptr_eq : mptr =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e'.allocId + UInt64.ofNat ptrVal.offsetBytes),
            .concrete e'.allocId borTag⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off; rfl
      have href : (⟨mptr.withOptionalProvenance, .none, mismatch⟩ :
            Miri.Interpreter.MemPlace AnnealProv).toRef annealTargetDataLayout =
          .ok (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) := by
        rw [hmptr_eq]; rfl
      have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) href
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      subst hsdb_eq
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_pa _) mls_db hmls_db
      obtain ⟨oldImm, hmdb_imm⟩ : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
        rcases hloc_db.rawPtr_immediate_cases hdst_ty himm_db with
          ⟨rfl, _⟩ | ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ | ⟨_, _, _, _, h⟩
        · exact absurd rfl hsd_ne
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
        · exact ⟨_, h⟩
      have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
        rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmdb_imm; subst hmdb_imm; rfl
      have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
      have hw := annealWriteImmediate_live
        (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
        (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
        (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
      have hm_stmt : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          Miri.Interpreter.runRvalue
            (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
              (.RawPtr (translateRawPtrKind rawMut) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
              ⟨dstIdx, #[]⟩) m := rfl
      have hm_ok : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[{ tfb with
              locals := tfb.locals.set dstIdx
                { tfb.locals[dstIdx]'hlt_db with
                  value := .live (.immediate (.scalar
                    (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                hlt_db }]⟩ }, .ok ()) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
      refine ⟨_, _, borTag, miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_ok rfl hfrb.location_eq, rfl, ?_⟩
      rw [hmptr_eq]
      simp [Array.getElem?_set_self]

/-- **`step_rawPtr_deref_zero_offset_correspondence`**: positive real-step
correspondence for `_d = &raw rawMut (*_p)` when `_p : *(const|mut) T` (`T`
primitive scalar, not holding a provenance-less integer scalar) has
`ptrVal.offsetBytes = 0`, `e.perm ≠ .disabled`, and
`¬(e.perm = .frozen ∧ rawMut = .mut)`:

1. **Exact UB equivalence**: `stepMirFn body s = .fail .ub` iff `lean-miri`'s
   `Step.step` (`annealStepHooks`) fails with `StepError.undefinedBehavior`
   (covering `_p` `.dead`, `_p` `.uninit`, and `_d` `.dead`); and
2. **Normal-step correspondence without pointee access**: when `_p` holds
   `.init (.ptr ptrVal 8)` and `_d` is live, BOTH machines step cleanly
   (even if `e.localIdx` is `.uninit` or `.dead`) and write an offset-`0`
   pointer targeting `e.localIdx` / `e.allocId` into `_d`. -/
theorem step_rawPtr_deref_zero_offset_correspondence
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData} {dstIdx ptrIdx : Local}
    {dstDecl ptrDecl : LocalDecl}
    {rawMut ptrMut dstMut : Mutability} {pointeeKind dstPointee : RigidTy} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_ptr : get? body.localDecls ptrIdx = some ptrDecl)
    (hptr_ty : ptrDecl.ty.kind = .rawPtr ptrMut pointeeKind)
    (hdst_ty : dstDecl.ty.kind = .rawPtr dstMut dstPointee)
    (hpk_prim : IsPrimScalarTy { kind := pointeeKind, layoutIdx := 0 })
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame ptrIdx)
    (hno_int : ∀ sc, get? s.frame.locals ptrIdx ≠ some (.init (.scalar sc)))
    (hzero_perm : ∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      ptrVal.offsetBytes = 0 ∧ e.perm ≠ .disabled ∧ ¬(e.perm = .frozen ∧ rawMut = .mut)) :
    ((stepMirFn body s = MirStepNode.fail .ub) ↔
      ∃ m' msg,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .error (.undefinedBehavior msg))) ∧
    (∀ ptrVal e,
      get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) →
      e ∈ allocMap → e.tag = ptrVal.tag →
      get? s.frame.locals dstIdx ≠ some .dead →
      (∃ s', stepMirFn body s = .step s' ∧
        get? s'.frame.locals dstIdx =
          some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
      ∃ m' tf' borTag,
        Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
          (m', .ok true) ∧
        m'.stack.frames = #[tf'] ∧
        (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar
            (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
              ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                .concrete e.allocId borTag⟩))))) := by
  obtain ⟨tf, hframes, _, _, hfr, hcal, _, hprot, _, _, halloc, _⟩ := id hstate
  obtain ⟨himm_d, himm_p⟩ := himm tf hframes
  obtain ⟨slot_d, mls_d, hlt_af_d, hlt_d, hslot_d, _, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a := hstate.cache_layout hframes hdecl_dst hlt_d
  have hfra := hstate_a.frame_rel_singleton rfl
  obtain ⟨slot_p, mls_p, _, hlt_pa, hslot_pa, hmls_pa, hmls_pa_eq, hloc_p⟩ :=
    hfra.lookup_local hdecl_ptr
  have hcache_p : ∀ l, mls_p.layout = some l → l = translateTy ptrDecl.ty body.layouts :=
    hloc_p.cachedLayout_eq
  have himm_pa : ∀ mp, mls_p.value ≠ .live (.indirect mp) :=
    himm_p.cache_layout hlt_d _ mls_p hmls_pa
  have hm_stmt : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
        (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
      Miri.Interpreter.runRvalue
        (Miri.Interpreter.evalRvalueIntoPlace (annealRvalueHooks body.localDecls body.layouts) ()
          (.RawPtr (translateRawPtrKind rawMut) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
          ⟨dstIdx, #[]⟩) m := rfl
  have hkind : translateRawPtrKind rawMut ≠ .FakeForPtrMetadata := by
    cases rawMut <;> decide
  have hmain :
      (stepMirFn body s = MirStepNode.fail .ub ∧
        ∃ m' msg,
          Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
            (m', .error (.undefinedBehavior msg))) ∨
      (∃ ptrVal e,
        get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) ∧
        e ∈ allocMap ∧ e.tag = ptrVal.tag ∧
        get? s.frame.locals dstIdx ≠ some .dead ∧
        (∃ s', stepMirFn body s = .step s' ∧
          get? s'.frame.locals dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) ∧
        ∃ m' tf' borTag,
          Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m =
            (m', .ok true) ∧
          m'.stack.frames = #[tf'] ∧
          (tf'.locals[dstIdx]?).map Miri.Interpreter.LocalState.value =
            some (.live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
                ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
                  .concrete e.allocId borTag⟩))))) := by
    rcases hloc_p.rawPtr_immediate_cases hptr_ty himm_pa with
      ⟨hsp_dead, hmp_dead⟩ | ⟨hsp_un, hmp_un⟩ |
      ⟨sc_p, _, hsp_sc, _, _, _⟩ | ⟨ptrVal, mptr, hsp_ptr, hptrRel, hmp_ptr⟩
    · left
      have ha : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue; dsimp only []; rw [hslot_pa, hsp_dead]
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa = ⟨.dead, mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_dead; subst hmp_dead; rfl
      have hsrc_dead := annealEvalPlace_deref_dead (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[cacheFrameLocalLayout tfa ptrIdx hlt_pa
              (translateTy ptrDecl.ty body.layouts)]⟩ },
            .error (.undefinedBehavior "read of dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.RawPtr (translateRawPtrKind rawMut) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior "read of dead local")
              { m with stack := ⟨#[cacheFrameLocalLayout tfa ptrIdx hlt_pa
                  (translateTy ptrDecl.ty body.layouts)]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, EStateM.pure, tfa, hdst_eval, hsrc_dead]
        rw [hrv_err]
      exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩
    · left
      have ha : stepMirFn body s = MirStepNode.fail .ub := by
        rw [stepMirFn_eq_of_not_other body s hcal hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue; dsimp only []; rw [hslot_pa, hsp_un]
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa = ⟨.live (.immediate .uninit), mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_un; subst hmp_un; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      have hder_un := annealDerefOperandToMemPlace_uninit (ly := body.layouts)
        hdecl_ptr hptr_ty hpk_prim (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      have hsrc_un : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .error (.undefinedBehavior "read of uninitialized local")
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_error hder_un]
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
            (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
          ({ m with stack := ⟨#[tfb]⟩ },
            .error (.undefinedBehavior "read of uninitialized local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        have hrv_err : Miri.Interpreter.evalRvalueIntoPlace
            (annealRvalueHooks body.localDecls body.layouts) ()
            (.RawPtr (translateRawPtrKind rawMut) (translatePlace ⟨ptrIdx, .cons .deref .nil⟩))
            ⟨dstIdx, #[]⟩ m =
            .error (.undefinedBehavior "read of uninitialized local")
              { m with stack := ⟨#[tfb]⟩ } := by
          unfold Miri.Interpreter.evalRvalueIntoPlace annealRvalueHooks
          simp only [bind, EStateM.bind, pure, EStateM.pure, tfa, hdst_eval, hsrc_un]
        rw [hrv_err]
      exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
        hbb hstmt hm_err⟩
    · exact absurd (hslot_pa.trans (congrArg some hsp_sc)) (hno_int sc_p)
    · have hsp_full : get? s.frame.locals ptrIdx = some (.init (.ptr ptrVal 8)) :=
        hslot_pa.trans (congrArg some hsp_ptr)
      obtain ⟨_, borTag, hprov_eq, _, _, hmptr_off, ⟨e, he, htag, rfl⟩⟩ := hptrRel
      obtain ⟨hoff0, hne_dis, hnot_fmut⟩ := hzero_perm ptrVal e hsp_full he htag
      have hlookup := (halloc.borrow_sync e he).2
      rw [htag] at hlookup
      have hrv_a_ok : ∃ mem₁, evalRvalue s.frame.locals
          (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil := by
        unfold evalRvalue; dsimp only []
        rw [hsp_full]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
        cases hp : e.perm <;> cases hm : rawMut
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact absurd ⟨hp, hm⟩ hnot_fmut
        · exact absurd hp hne_dis
        · exact absurd hp hne_dis
      obtain ⟨mem₁, hrv_a, hprot₁⟩ := hrv_a_ok
      have hmls_pa' : tfa.locals[ptrIdx]'hlt_pa =
          ⟨.live (.immediate (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))),
            mls_p.layout⟩ := by
        rw [hmls_pa_eq]; rcases mls_p with ⟨v0, l0⟩; dsimp only at hmp_ptr; subst hmp_ptr; rfl
      let tfb := cacheFrameLocalLayout tfa ptrIdx hlt_pa (translateTy ptrDecl.ty body.layouts)
      have hsrc_live := annealEvalPlace_deref_live (m := { m with stack := ⟨#[tfa]⟩ })
        rfl hlt_pa hdecl_ptr hmls_pa' hcache_p
      obtain ⟨_, _, _, _, hpow_pk, _⟩ := hpk_prim.size_align_ok body.layouts
      obtain ⟨mismatch, hmis_any⟩ := annealOffsetMisalignment_ok_of_pow2 mptr.offset _ hpow_pk
      have hder_ptr := annealDerefOperandToMemPlace_pointer hdecl_ptr hptr_ty hpk_prim mptr hmis_any
        (translateTy ptrDecl.ty body.layouts) { m with stack := ⟨#[tfb]⟩ }
      have hsrc_eval : annealEvalPlace body.localDecls body.layouts
          (translatePlace ⟨ptrIdx, .cons .deref .nil⟩) { m with stack := ⟨#[tfa]⟩ } =
          .ok ⟨.memory ⟨mptr.withOptionalProvenance, .none, mismatch⟩,
              translateTy { kind := pointeeKind, layoutIdx := 0 } body.layouts⟩
            { m with stack := ⟨#[tfb]⟩ } := by
        rw [hsrc_live, EStateM.bind_eq_ok hder_ptr]; rfl
      have hmptr_eq : mptr =
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId), .concrete e.allocId borTag⟩ := by
        rcases mptr with ⟨off, prov⟩
        dsimp only at hprov_eq hmptr_off; subst hprov_eq hmptr_off
        rw [hoff0]
        simp
      have href : (⟨mptr.withOptionalProvenance, .none, mismatch⟩ :
            Miri.Interpreter.MemPlace AnnealProv).toRef annealTargetDataLayout =
          .ok (.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)) := by
        rw [hmptr_eq]; rfl
      have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval hsrc_eval
        (annealForceAllocation_memory_eq _ _ _ _ _) href
      have hstate_b := hstate_a.cache_layout rfl hdecl_ptr hlt_pa
      have hfrb := hstate_b.frame_rel_singleton rfl
      obtain ⟨slot_db, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ :=
        hfrb.lookup_local hdecl_dst
      have hsdb_eq : slot_db = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      subst hsdb_eq
      have himm_db : ∀ mp, mls_db.value ≠ .live (.indirect mp) :=
        ((himm_d.cache_layout hlt_d _).cache_layout hlt_pa _) mls_db hmls_db
      rcases hloc_db.rawPtr_immediate_cases hdst_ty himm_db with
        ⟨hsd_dead, hmd_dead⟩ | ⟨hsd_un, hmd_un⟩ |
        ⟨_, msc_d, hsd_sc, _, _, hmd_sc⟩ | ⟨_, mptr_d, hsd_ptr, _, hmd_ptr⟩
      · left
        have ha : stepMirFn body s = MirStepNode.fail .ub := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_dead]
        have hdb_dead : tfb.locals[dstIdx]? = some ⟨.dead, mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_dead; subst hmd_dead; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_dead
        have hm_err : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[tfb]⟩ },
              .error (.undefinedBehavior "write to dead local")) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
          rw [hrv, annealWriteImmediate_dead (m := { m with stack := ⟨#[tfb]⟩ })
            (id0 := tf.localsIdentity) rfl hget_db]
        exact ⟨ha, _, _, miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq
          hbb hstmt hm_err⟩
      · right
        have hlive_d : get? s.frame.locals dstIdx ≠ some .dead := by
          rw [hslot_d, hsd_un]; simp
        have hset := set?_eq_some_set hlt_af_d
          (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
        have hget_set : get? (s.frame.locals.set dstIdx
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
        have ha_step : ∃ s', stepMirFn body s = .step s' ∧
            get? s'.frame.locals dstIdx =
              some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_un]
          simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
        have hdb_imm : tfb.locals[dstIdx]? = some ⟨.live (.immediate .uninit), mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_un; subst hmd_un; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[{ tfb with
                locals := tfb.locals.set dstIdx
                  { tfb.locals[dstIdx]'hlt_db with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                  hlt_db }]⟩ }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        refine ⟨ptrVal, e, hsp_full, he, htag, hlive_d, ha_step, _, _, borTag,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfrb.location_eq, rfl, ?_⟩
        rw [hmptr_eq]; simp [Array.getElem?_set_self]
      · right
        have hlive_d : get? s.frame.locals dstIdx ≠ some .dead := by
          rw [hslot_d, hsd_sc]; simp
        have hset := set?_eq_some_set hlt_af_d
          (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
        have hget_set : get? (s.frame.locals.set dstIdx
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
        have ha_step : ∃ s', stepMirFn body s = .step s' ∧
            get? s'.frame.locals dstIdx =
              some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_sc]
          simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
        have hdb_imm : tfb.locals[dstIdx]? =
            some ⟨.live (.immediate (.scalar (.fromScalarInt msc_d))), mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_sc; subst hmd_sc; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[{ tfb with
                locals := tfb.locals.set dstIdx
                  { tfb.locals[dstIdx]'hlt_db with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                  hlt_db }]⟩ }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        refine ⟨ptrVal, e, hsp_full, he, htag, hlive_d, ha_step, _, _, borTag,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfrb.location_eq, rfl, ?_⟩
        rw [hmptr_eq]; simp [Array.getElem?_set_self]
      · right
        have hlive_d : get? s.frame.locals dstIdx ≠ some .dead := by
          rw [hslot_d, hsd_ptr]; simp
        have hset := set?_eq_some_set hlt_af_d
          (LocalSlot.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))
        have hget_set : get? (s.frame.locals.set dstIdx
            (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8))) dstIdx =
            some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [get?_eq_getElem?, List.getElem?_set_self hlt_af_d]
        have ha_step : ∃ s', stepMirFn body s = .step s' ∧
            get? s'.frame.locals dstIdx =
              some (.init (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)) := by
          rw [stepMirFn_eq_of_not_other body s hcal hphase]
          simp only [hbb, hstmt]
          unfold evalStmt; dsimp only []; rw [hrv_a]; dsimp only []; rw [hslot_d, hsd_ptr]
          simp only [hset, hprot₁]; exact ⟨_, rfl, hget_set⟩
        have hdb_imm : tfb.locals[dstIdx]? =
            some ⟨.live (.immediate (.scalar
              (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr_d))),
              mls_db.layout⟩ := by
          rw [hmls_db]; rcases mls_db with ⟨v0, l0⟩; dsimp only at hmd_ptr; subst hmd_ptr; rfl
        have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_imm
        have hw := annealWriteImmediate_live
          (val := .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))
          (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tf.localsIdentity)
          (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
        have hm_ok : Miri.Interpreter.Step.evalStatement
            (annealStepHooks body.localDecls body.layouts) ()
            (translateStmt ⟨.assign ⟨dstIdx, .nil⟩
              (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩), span⟩) m =
            ({ m with stack := ⟨#[{ tfb with
                locals := tfb.locals.set dstIdx
                  { tfb.locals[dstIdx]'hlt_db with
                    value := .live (.immediate (.scalar
                      (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr))) }
                  hlt_db }]⟩ }, .ok ()) := by
          rw [hm_stmt]; unfold Miri.Interpreter.runRvalue; rw [hrv, hw]
        refine ⟨ptrVal, e, hsp_full, he, htag, hlive_d, ha_step, _, _, borTag,
          miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
            hfrb.location_eq, rfl, ?_⟩
        rw [hmptr_eq]; simp [Array.getElem?_set_self]
  refine ⟨?_, ?_⟩
  · rcases hmain with ⟨ha_ub, hm_ub⟩ | ⟨_, _, _, _, _, _, ⟨_, ha_ok, _⟩, ⟨_, _, _, hm_ok, _⟩⟩
    · exact ⟨fun _ => hm_ub, fun _ => ha_ub⟩
    · refine ⟨fun h => ?_, fun ⟨_, _, h⟩ => ?_⟩
      · rw [ha_ok] at h; cases h
      · rw [hm_ok] at h; cases h
  · intro ptrVal e hsp he htag hlive
    rcases hmain with ⟨ha_ub, _⟩ | ⟨ptrVal', e', hsp', he', htag', _, ha_step, hm_step⟩
    · exfalso
      obtain ⟨_, hne_dis, hnot_fmut⟩ := hzero_perm ptrVal e hsp he htag
      have hlookup := (halloc.borrow_sync e he).2
      rw [htag] at hlookup
      have hrv_ok' : ∃ mem₁, evalRvalue s.frame.locals
          (.rawPtr rawMut ⟨ptrIdx, .cons .deref .nil⟩) s.memory body.localDecls body.layouts =
          .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8) s.frame.locals mem₁ ∧
          mem₁.activeProtectors = .nil := by
        clear ha_ub
        unfold evalRvalue; dsimp only []
        rw [hsp]; dsimp only []; rw [hlookup]; dsimp only [AllocMapEntry.toBorrowEntry]
        cases hp : e.perm <;> cases hm : rawMut
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact ⟨_, rfl, hprot⟩
        · exact absurd ⟨hp, hm⟩ hnot_fmut
        · exact absurd hp hne_dis
        · exact absurd hp hne_dis
      obtain ⟨mem₁, hrv₁, hprot₁⟩ := hrv_ok'
      rw [stepMirFn_eq_of_not_other body s hcal hphase] at ha_ub
      simp only [hbb, hstmt] at ha_ub
      unfold evalStmt at ha_ub
      dsimp only [] at ha_ub
      rw [hrv₁] at ha_ub
      dsimp only [] at ha_ub
      rw [hslot_d] at ha_ub
      cases slot_d with
      | dead => exact hlive hslot_d
      | uninit => simp only [set?_eq_some_set hlt_af_d, hprot₁] at ha_ub; cases ha_ub
      | init _ => simp only [set?_eq_some_set hlt_af_d, hprot₁] at ha_ub; cases ha_ub
    · have hp_eq : ptrVal' = ptrVal := by
        have hv := Option.some.inj (hsp'.symm.trans hsp)
        injection hv with hv'
        injection hv'
      subst hp_eq
      have he_eq : e' = e :=
        allocMap_mem_tag_injective halloc.tags_nodup he' he (htag'.trans htag.symm)
      subst he_eq
      exact ⟨ha_step, hm_step⟩

/-- **`step_terminator_goto_return_lm3_1_simulation`**: root-frame basic-block
terminators `Goto`, `Return` (for any non-zero-sized non-`.rawPtr` immediate
`_0`, such as primitive scalars and scalar pairs, even when `allocMap` has
active or freed stack allocations and borrow entries), and `Unreachable` step
in lockstep across `StateRelLM3_1` under `stepMirFn` and
`Miri.Interpreter.Step.step` (`annealStepHooks`). -/
theorem step_terminator_goto_return_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hphase : ∀ p, body.phase ≠ .other p)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    (hstmt_len : s.frame.stmtIdx = length bb.statements)
    (hcleanup : bb.isCleanup = false)
    (hterm :
      (∃ target, bb.terminator.kind = .goto target) ∨
      (bb.terminator.kind = .return_ ∧
        ∃ decl0,
          get? body.localDecls 0 = some decl0 ∧
          (∀ mutability pk, decl0.ty.kind ≠ .rawPtr mutability pk) ∧
          (translateTy decl0.ty body.layouts).layout.size ≠ Miri.ABI.Size.ZERO ∧
          ∀ topFrame, m.stack.frames = #[topFrame] → IsImmediateFrameLocal topFrame 0) ∨
      bb.terminator.kind = .unreachable) :
    StepRelLM3_1 body m allocMap
      (stepMirFn body s)
      (Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m) := by
  rcases hstate with
    ⟨topFrame, hframes, hretCont, ⟨retLay, hretPlace⟩, hframe,
      hcal, hstack, hprot, hcaller, hbor, halloc, hd_tf⟩
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  have hbeq_len : (s.frame.stmtIdx == length bb.statements) = true := by
    simp [hstmt_len]
  simp only [hbb, hstmt_none, hbeq_len, ↓reduceIte]
  rw [miri_step_at_terminator hframes hframe.body_eq hframe.location_eq hbb hstmt_none]
  rcases hterm with ⟨target, hgoto⟩ | ⟨hret, decl0, hdecl0, hno_ptr, hsz0, himm0⟩ | hunreach
  · unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
      Miri.Interpreter.ControlFlow.goToBlock
      Miri.Interpreter.ControlFlow.setLocation
    rw [hgoto, stack_currentFrame?_singleton m.stack topFrame hframes, hframes]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    apply StepRelLM3_1.step
    refine StateRelLM3_1.mk
      { topFrame with location := .mir ⟨target, 0⟩ }
      rfl hretCont ⟨retLay, hretPlace⟩
      ⟨hframe.body_eq, rfl, hframe.af_locals_len, hframe.mf_locals_size, hframe.locals_rel⟩
      hcal hstack hprot hcaller hbor ?_ hd_tf
    refine ⟨halloc.tags_nodup, halloc.local_to_alloc_unique, halloc.alloc_to_local_injective,
      halloc.target_decl, halloc.base_addr_valid, halloc.borrow_sync, halloc.live_key_unique, ?_⟩
    intro tf' htf' e he
    injection htf' with h1; injection h1 with h2; subst tf'
    exact halloc.local_alloc_sync topFrame hframes e he
  · obtain ⟨slot0, mls0, _, _, hslot0, hmls0, _, hloc0⟩ := hframe.lookup_local hdecl0
    have hget0 := frame_getLocal_of_getElem? topFrame 0 mls0 hmls0
    have himm0' := himm0 topFrame hframes mls0 hmls0
    unfold evalTerminator translateTerminator
      Miri.Interpreter.ControlFlow.evalTerminator
    rw [hret, hstack, annealTerminatorHooks_toControlHooks, hslot0]
    dsimp only [translateTerminatorKind, Id.run, Pure.pure]
    cases hloc0 with
    | rawPtr _ _ _ mutability pk _ hty _ =>
      exact False.elim (hno_ptr mutability pk hty)
    | base hbase0 =>
      cases hbase0 with
      | dead cachedLayout _ =>
        rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
          hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_dead hframes hget0)]
        exact StepRelLM3_1.ub _ _
      | indirect _ mp _ _ _ _ =>
        exact False.elim (himm0' mp rfl)
      | immediate _ imm cachedLayout _ hval =>
        rcases hval with ⟨rfl, rfl⟩ | ⟨retVal, rfl, himmRel⟩
        · rw [returnFromCurrentFrame_of_error annealControlHooks hframes hframe.body_eq
            hframe.location_eq hbb hcleanup (annealControlHooks_returnOperand_uninit hframes hget0)]
          exact StepRelLM3_1.ub _ _
        · cases himmRel with
          | unit hzero =>
            exact False.elim (hsz0 hzero)
          | scalar sc msc hsc hsz_sc hbool_sc hchar_sc =>
            have hop0 := annealControlHooks_returnOperand_scalar hframes hget0
            rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
              hframe.location_eq hbb hcleanup hretCont hop0
              (annealControlHooks_popFrame_singleton hframes)
              (annealControlHooks_copyReturn_empty _ hretPlace)
              (annealControlHooks_cleanupFrame_eq false topFrame _)]
            exact StepRelLM3_1.retRoot decl0 _ _ s.memory _ hdecl0 hop0
              (.scalar sc msc hsc hsz_sc hbool_sc hchar_sc) rfl
          | scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair =>
            have hop0 := annealControlHooks_returnOperand_scalarPair hframes hget0
            rw [returnFromCurrentFrame_of_ok annealControlHooks hframes hframe.body_eq
              hframe.location_eq hbb hcleanup hretCont hop0
              (annealControlHooks_popFrame_singleton hframes)
              (annealControlHooks_copyReturn_empty _ hretPlace)
              (annealControlHooks_cleanupFrame_eq false topFrame _)]
            exact StepRelLM3_1.retRoot decl0 _ _ s.memory _ hdecl0 hop0
              (.scalarPair sc₁ sc₂ msc₁ msc₂ hsc₁ hsc₂ hagg hpair) rfl
  · unfold evalTerminator translateTerminator Miri.Interpreter.ControlFlow.evalTerminator
    rw [hunreach]
    dsimp only [translateTerminatorKind, Except.map, Id.run]
    exact StepRelLM3_1.ub _ _

end LeanMiriSpec.Correspondence
