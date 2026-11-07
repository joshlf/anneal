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

Correspondence theorems between Anneal's `Trusted.Rustc.V2026_06_01.MirSemantics`
and `lean-miri` for the raw-pointer fragment (`LM-3.1`):

1. **`Rvalue.RawPtr` (`&raw const p` / `&raw mut p`) and `.immediate → .indirect`
   Coalescing (`evalRvalue_rawPtr_addrOf_simulation`)**:
   Taking the address of a live local promotes an immediate local to a memory-backed
   stack allocation (`Miri.Interpreter.forceAllocation` via
   `forceAllocation_preserves_StateRel`), records the `(tag, localIdx, allocId, perm)`
   correspondence in `AllocMapRel`, and produces `PtrRel`-related raw pointers at
   offset `0` (while a dead target local raises UB in both semantics).
2. **`PlaceElem.Deref` (`*ptr`) Reads, Writes, and UB (`evalProjection_deref_simulation`)**:
   Dereferencing a pointer (`_d = copy *_p`, `_d = move *_p`, and `*_p = rv`)
   succeeds in lockstep when the pointer is live, in-bounds, and aligned, and
   triggers UB in both semantics on:
   - dangling / dead allocations after `StorageDead` (`deadAllocation`),
   - out-of-bounds offsets (`pointerOutOfBounds`),
   - misaligned accesses (`Size.isAligned = .ok false`), and
   - null / provenance-less integer pointers (`danglingIntegerPointer`).
3. **`BinOp.Offset` (`inbounds` vs. `wrapping`) (`evalBinOp_offset_inbounds_simulation`)**:
   In-bounds pointer offset (`Miri.Interpreter.ptrOffsetInbounds`) succeeds if and
   only if the pointer has valid provenance and `[offsetBytes, offsetBytes + deltaBytes]`
   lies within `[0, alloc.byteSize]` without address-space wraparound (including
   zero-offset / ZST edge cases), preserving `PtrRel` with Anneal's `.binaryOp .offset`
   and raising UB when out-of-bounds, dangling, or provenance-less; wrapping offset
   (`Pointer.wrappingSignedOffset`) computes the modular address without bounds or
   liveness checks.
4. **`CastKind.PtrToPtr` and Pointer/Integer Exposure Casts (`evalCast_ptrToPtr_simulation`)**:
   Raw pointer casts (`CastKind.PtrToPtr` via `Miri.Interpreter.Cast.ptrToPtr`)
   preserve `PtrRel` and pointer provenance across `*const T` / `*mut U`, and
   `PointerExposeProvenance` / `PointerWithExposedProvenance` round-trip pointer
   values in both semantics.
5. **Composed `LM-3.1` Statement Simulation (`step_stmt_lm3_1_simulation`)**:
   Combines the `LM-3.1` statement forms into a unified step theorem.
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

/-- Monotonicity of `ImmediateRelLM3_1` when extending `allocMap` with a fresh entry
whose tag was not previously mapped. -/
theorem of_cons_fresh
    {allocMap : List AllocMapEntry} {e : AllocMapEntry}
    {ty : Ty} {layouts : LayoutTable}
    {v : Value} {imm : Miri.Interpreter.Immediate AnnealProv}
    (hfresh : ∀ p : ProvenancePtr, v = .ptr p 8 → e.tag ≠ p.tag)
    (h : ImmediateRelLM3_1 allocMap ty layouts v imm) :
    ImmediateRelLM3_1 (e :: allocMap) ty layouts v imm := by
  cases h with
  | of_immediateRel himm => exact .of_immediateRel himm
  | rawPtr mutability pointeeKind p mptr hty hptr =>
    refine .rawPtr mutability pointeeKind p mptr hty ?_
    cases hptr with
    | mk allocId borTag hprov hid hoff haddr htarget =>
      refine .mk allocId borTag hprov hid hoff haddr ?_
      rcases htarget with ⟨e', he', htag, halloc⟩ | ⟨hnone, halloc⟩
      · exact Or.inl ⟨e', List.mem_cons_of_mem e he', htag, halloc⟩
      · right
        refine ⟨?_, halloc⟩
        unfold lookupAllocMapByTag
        have hne : Nat.beq e.tag p.tag = false := by
          cases hbeq : Nat.beq e.tag p.tag
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hbeq) (hfresh p rfl)
        rw [hne]
        exact hnone

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

/-- `CastHooks` extended for `LM-3.1` with raw pointer type classification
(`castTypeInfoOfEncodedTyIdLM3_1`) and provenance exposure hooks. -/
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
      | .error err => throw err
    exposeProvenance := fun _ _ => pure ()
    pointerFromExposedAddress := fun _ addr =>
      let allocIdVal := addr >>> 32
      if h : allocIdVal = 0 then
        pure (Miri.Memory.Pointer.withoutProvenance addr)
      else
        pure ⟨Miri.ABI.Size.ofBytes addr,
          some (.concrete ⟨allocIdVal, h⟩ Miri.Memory.BorTag.one)⟩ }

/-- Evaluate `Rvalue.RawPtr` (`&raw const local` / `&raw mut local`) in `lean-miri`:
resolves the local place via `annealEvalPlace`, materializes its stack allocation
if currently immediate via `Miri.Interpreter.forceAllocation`, and returns the
resulting pointer immediate `Scalar.fromPointer annealTargetDataLayout mplace.mplace.ptr`. -/
def evalRawPtrAddrOfMiri
    (localDecls : List LocalDecl) (layouts : LayoutTable)
    (targetIdx : Miri.MIR.LocalId) (ptrTy : Ty) :
    Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.RvalueImmTy AnnealProv) := do
  let place ← annealEvalPlace localDecls layouts { localId := targetIdx, projection := #[] }
  let mplace ← Miri.Interpreter.forceAllocation (annealPlaceHooks localDecls layouts) () place
  let someProv ← match mplace.mplace.ptr.provenance with
    | some prov => pure prov
    | none => throw (.invalidProgram "forceAllocation returned provenance-less stack pointer")
  let ptr : Miri.Memory.Pointer AnnealProv := ⟨mplace.mplace.ptr.offset, someProv⟩
  return ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout ptr),
    translateTy ptrTy layouts⟩

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

/-- **`evalRvalue_rawPtr_addrOf_simulation` (`LM-3.1` Deliverable 1)**:
Simulation of `Rvalue.RawPtr` (`&raw const _target` / `&raw mut _target`) between
Anneal's `MirSemantics.evalRvalue` and `lean-miri`'s `evalRawPtrAddrOfMiri`
(which invokes `Miri.Interpreter.forceAllocation` via `forceAllocation_preserves_StateRel`):

1. **Coalescing & Address-Of on Live Locals**: When `targetIdx` is live (including
   when it is `.immediate` in `lean-miri` and promoted to `.indirect (stackAllocPlace allocId)`
   by `forceAllocation`), `forceAllocation` preserves `StateRel`, the target local
   in `m'` is memory-backed at `mplace.mplace` with concrete provenance `(allocId, .one)`
   at base address `annealStackBaseAddr allocId`, Anneal's `evalRvalue` returns
   `.ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)`, and the two
   resulting pointers are related by `PtrRel` and `ImmediateRelLM3_1` under the
   extended `allocMap' := ⟨s.memory.nextTag, targetIdx, allocId, perm⟩ :: allocMap`!
2. **Dead-Local UB Agreement**: When `targetIdx` is `.dead`, Anneal's `evalRvalue`
   returns `.ub` and `lean-miri`'s `evalRawPtrAddrOfMiri` fails (never returning `.ok`). -/
theorem evalRvalue_rawPtr_addrOf_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    (allocMap : List AllocMapEntry)
    (hstate : StateRel body s m)
    (mutability : Mutability) (pointeeKind : RigidTy) (ptrTy : Ty)
    (hptrTy : ptrTy.kind = .rawPtr mutability pointeeKind)
    {targetIdx : Local} {targetDecl : LocalDecl}
    (hdecl : get? body.localDecls targetIdx = some targetDecl) :
    (get? s.frame.locals targetIdx = some .dead →
      evalRvalue s.frame.locals (.rawPtr mutability ⟨targetIdx, .nil⟩)
        s.memory body.localDecls body.layouts = .ub ∧
      ∀ imm m', evalRawPtrAddrOfMiri body.localDecls body.layouts targetIdx ptrTy m ≠ .ok imm m') ∧
    (∀ imm m' allocId,
      evalRawPtrAddrOfMiri body.localDecls body.layouts targetIdx ptrTy m = .ok imm m' →
      (∃ mptr, imm.imm = .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) ∧
        mptr.provenance = .concrete allocId Miri.Memory.BorTag.one ∧
        mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId)) →
      allocId.value.toNat < 2 ^ 32 →
      let perm : TreeBorrowPerm := rawPtrPerm body.localDecls body.layouts mutability targetIdx
      let entry : AllocMapEntry :=
        { tag := s.memory.nextTag
          localIdx := targetIdx
          allocId := allocId
          perm := perm }
      let bEntry : BorrowEntry :=
        { tag := s.memory.nextTag
          targetLocal := targetIdx
          targetProjection := .nil
          perm := perm }
      StateRel body s m' ∧
      evalRvalue s.frame.locals (.rawPtr mutability ⟨targetIdx, .nil⟩)
        s.memory body.localDecls body.layouts =
        .ok (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)
          s.frame.locals
          { s.memory with
            borrows := .cons bEntry s.memory.borrows
            nextTag := s.memory.nextTag + 1 } ∧
      ImmediateRelLM3_1 (entry :: allocMap) ptrTy body.layouts
        (.ptr { allocId := s.memory.nextTag, offsetBytes := 0 } 8)
        imm.imm) := by
  constructor
  · intro hdead
    refine ⟨evalRvalue_rawPtr_dead_eq s body.localDecls body.layouts mutability targetIdx hdead, ?_⟩
    intro imm m' hok
    rcases hstate with ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _⟩
    obtain ⟨slot, mls, _, hlt_mf, hslot, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    rw [hdead] at hslot
    injection hslot with hslot
    subst hslot
    cases hloc with
    | dead c hc =>
      have hc' : ∀ l, (tf.locals[targetIdx]'hlt_mf).layout = some l →
          l = translateTy targetDecl.ty body.layouts := by
        rw [hmls_eq]; exact hc
      unfold evalRawPtrAddrOfMiri at hok
      dsimp only [bind] at hok
      rw [EStateM.bind_apply_ok (annealEvalPlace_unprojected hframes hlt_mf hdecl hc')] at hok
      unfold Miri.Interpreter.forceAllocation at hok
      have hcf_frames :
          ({ m with stack := ⟨#[cacheFrameLocalLayout tf targetIdx hlt_mf
              (translateTy targetDecl.ty body.layouts)]⟩ } : AnnealStepState).stack.frames =
            #[cacheFrameLocalLayout tf targetIdx hlt_mf
              (translateTy targetDecl.ty body.layouts)] := rfl
      simp only [Miri.Interpreter.requireCurrent_eq,
        Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
        bind, EStateM.bind,
        annealPlaceHooks_frameIndex_eq hcf_frames, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte, pure, EStateM.pure, annealPlaceHooks_getFrame_eq hcf_frames] at hok
      have hgo_dead :
          (cacheFrameLocalLayout tf targetIdx hlt_mf
            (translateTy targetDecl.ty body.layouts)).getLocalOperand targetIdx =
            .error (.localExpectedLive targetIdx) := by
        unfold Miri.Interpreter.Frame.getLocalOperand Miri.Interpreter.Frame.getLocal
          Miri.Interpreter.LocalState.access
        have hlt' : targetIdx < (cacheFrameLocalLayout tf targetIdx hlt_mf
            (translateTy targetDecl.ty body.layouts)).locals.size := by
          rw [cacheFrameLocalLayout_size]; exact hlt_mf
        have hval_dead : ((cacheFrameLocalLayout tf targetIdx hlt_mf
            (translateTy targetDecl.ty body.layouts)).locals[targetIdx]'hlt').value = .dead := by
          simp [cacheFrameLocalLayout, hmls_eq]
        simp [hlt', hval_dead, Except.mapError]
      rw [hgo_dead] at hok
      cases hok
    | immediate _ _ _ _ hv =>
      rcases hv with ⟨h, _⟩ | ⟨_, h, _⟩ <;> cases h
    | indirect _ _ _ _ hne _ =>
      exact absurd rfl hne
  · intro imm m' allocId hok ⟨mptr, himm, hprov, haddr⟩ hid_lt
    unfold evalRawPtrAddrOfMiri at hok
    dsimp only [bind] at hok
    rcases id hstate with ⟨tf, hframes, hretCont, hretPlace, hfr, hcal, hstack, hbor, hprot, hcaller, hdisj⟩
    obtain ⟨slot, mls, _, hlt_mf, hslot, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
    have hc : ∀ l, (tf.locals[targetIdx]'hlt_mf).layout = some l →
        l = translateTy targetDecl.ty body.layouts := by
      rw [hmls_eq]; exact hloc.layout_eq
    rw [EStateM.bind_apply_ok (annealEvalPlace_unprojected hframes hlt_mf hdecl hc)] at hok
    have hstate₁ : StateRel body s
        { m with stack := ⟨#[cacheFrameLocalLayout tf targetIdx hlt_mf
            (translateTy targetDecl.ty body.layouts)]⟩ } := by
      refine StateRel.mk _ rfl hretCont hretPlace (hfr.cache_local_layout hdecl hlt_mf)
        hcal hstack hbor hprot hcaller ?_
      intro i j mp_i mp_j lay_i lay_j hij hi hj
      unfold cacheFrameLocalLayout at hi hj
      have hval_eq : ∀ (k : Nat) mp lay,
          (tf.locals.set targetIdx
            { tf.locals[targetIdx]'hlt_mf with
              layout := some (translateTy targetDecl.ty body.layouts) } hlt_mf)[k]? =
            some ({ value := .live (.indirect mp), layout := lay } :
              Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) →
          ∃ lay', tf.locals[k]? =
            some ({ value := .live (.indirect mp), layout := lay' } :
              Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout) := by
        intro k mp lay hk
        rw [Array.getElem?_set] at hk
        by_cases htk : targetIdx = k
        · subst htk
          simp only [↓reduceIte, Option.some.injEq] at hk
          injection hk with hval_k _
          exact ⟨(tf.locals[targetIdx]'hlt_mf).layout, by
            rw [Array.getElem?_eq_getElem hlt_mf]
            rcases hmk : tf.locals[targetIdx]'hlt_mf with ⟨v, l⟩
            rw [hmk] at hval_k
            subst hval_k
            rfl⟩
        · simp only [htk, ↓reduceIte] at hk
          exact ⟨lay, hk⟩
      obtain ⟨lay_i', hi'⟩ := hval_eq i mp_i lay_i hi
      obtain ⟨lay_j', hj'⟩ := hval_eq j mp_j lay_j hj
      exact hdisj i j mp_i mp_j lay_i' lay_j' hij hi' hj'
    cases hforce : Miri.Interpreter.forceAllocation (annealPlaceHooks body.localDecls body.layouts) ()
        ⟨.local 0 targetIdx none tf.localsIdentity,
          translateTy targetDecl.ty body.layouts⟩
        { m with stack := ⟨#[cacheFrameLocalLayout tf targetIdx hlt_mf
            (translateTy targetDecl.ty body.layouts)]⟩ } with
    | error e s' =>
      rw [EStateM.bind_apply_error hforce] at hok
      cases hok
    | ok mplace m₂ =>
      rw [EStateM.bind_apply_ok hforce] at hok
      obtain ⟨hstate₂, hlocal_ind⟩ := forceAllocation_preserves_StateRel hstate₁ hforce
      cases hprov_mp : mplace.mplace.ptr.provenance with
      | none =>
        simp [hprov_mp, EStateM.bind, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
          at hok
      | some prov =>
        simp only [hprov_mp, EStateM.bind, pure, EStateM.pure] at hok
        injection hok with himm_eq hm₂_eq
        subst hm₂_eq
        obtain ⟨tf', lay', hframes', hloc'⟩ := hlocal_ind 0 targetIdx _ rfl
        rcases id hstate₂ with ⟨tf₂, hframes₂, _, _, hfr₂, _, _, _, _, _, _⟩
        rw [hframes'] at hframes₂
        injection hframes₂ with htf_eq
        injection htf_eq with htf_eq'
        subst htf_eq'
        obtain ⟨slot', mls', _, _, hslot', hmls', _, hloc_rel'⟩ := hfr₂.lookup_local hdecl
        rw [hslot] at hslot'
        injection hslot' with hslot_eq
        subst hslot_eq
        rw [hloc'] at hmls'
        injection hmls' with hmls_eq'
        subst hmls_eq'
        have hlive_slot : slot ≠ .dead := by
          cases hloc_rel' with
          | indirect _ _ _ _ hne _ => exact hne
        refine ⟨hstate₂,
          evalRvalue_rawPtr_live_eq s body.localDecls body.layouts mutability targetIdx slot
            hslot hlive_slot, ?_⟩
        rw [himm]
        refine .rawPtr mutability pointeeKind
          { allocId := s.memory.nextTag, offsetBytes := 0 } mptr hptrTy ?_
        have hzero : (annealStackBaseAddr allocId + UInt64.ofNat 0) =
            annealStackBaseAddr allocId := by simp
        refine .mk allocId Miri.Memory.BorTag.one hprov hid_lt (by show 0 < 2 ^ 32; decide)
          (by rw [haddr, hzero]) ?_
        exact Or.inl ⟨_, List.Mem.head _, rfl, rfl⟩

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
    (_hoff0 : ptrVal.offsetBytes = 0)
    (hmptr : mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
      .concrete e.allocId Miri.Memory.BorTag.one⟩)
    (htarget_slot : get? s.frame.locals e.localIdx = some (.init (.scalar sc)))
    (hfind : m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hsz_alloc : localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8)
    (_hsc : ScalarRel sc msc)
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
    (_hoff0 : ptrVal.offsetBytes = 0)
    (hmptr : mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
      .concrete e.allocId Miri.Memory.BorTag.one⟩)
    (htarget_slot : get? s.frame.locals e.localIdx = some oldSlot)
    (hold_live : oldSlot ≠ .dead)
    (hset : set? s.frame.locals e.localIdx (.init (.scalar sc)) = some locals')
    (hfind : m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
      some (e.allocId, localAlloc))
    (hsz_alloc : localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8)
    (_hsc : ScalarRel sc msc)
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

/-- **`evalProjection_deref_simulation` (`LM-3.1` Deliverable 2)**:
Simulation of `PlaceElem.Deref` (`*ptr`) across reads, writes, and all four UB
categories between Anneal's `MirSemantics` and `lean-miri`:

1. **Deref Read (`_d = copy *_p` / `_d = move *_p`) & Deref Write (`*_p = val`)**:
   When `ptrLoc` holds `.ptr ptrVal 8` related by `PtrRel allocMap ptrVal mptr` at
   `ptrVal.offsetBytes = 0` to an entry `e ∈ allocMap` under `AllocMapRel body s m allocMap`
   whose target local holds an initialized scalar `.init (.scalar sc)` in a
   memory-backed allocation `localAlloc` (`MemPlaceRel`), Anneal's
   `evalOperand (.copy ⟨ptrLoc, [.deref]⟩)` returns `.ok (.scalar sc) s.frame.locals`
   and `lean-miri`'s `evalDerefReadScalarMiri` succeeds with `.ok (.fromScalarInt msc)`
   satisfying `ScalarRel sc msc`. Similarly, when `e.perm = .active`, Anneal's
   `writePlaceValue s.frame.locals s.memory.borrows ⟨ptrLoc, [.deref]⟩ (.scalar newSc)`
   succeeds with `.ok (s.frame.locals.set e.localIdx (.init (.scalar newSc)))`.
2. **Dangling / Use-After-`StorageDead` Deref UB**:
   When `ptrVal` resolves to an allocation `allocId` whose target local is `.dead`
   in Anneal (`get? s.frame.locals entry.targetLocal = some .dead`) and deallocated
   in `lean-miri` (`m.machine.memory.live.find? (fun x => x.1 == allocId) = none`),
   Anneal's `evalOperand (.copy ⟨ptrLoc, [.deref]⟩)` returns `.ub` and `lean-miri`'s
   `evalDerefReadScalarMiri` fails with `.error (.undefinedBehavior _)`.
3. **Out-of-Bounds Deref UB**:
   When `ptrVal` points to an allocation of size `< ptrVal.offsetBytes + 8`,
   Anneal's `evalOperand (.copy ⟨ptrLoc, [.deref]⟩)` returns `.ub` and `lean-miri`'s
   `evalDerefReadScalarMiri` fails with `.error (.undefinedBehavior _)`.
4. **Misaligned & Provenance-less / Null Deref UB**:
   When `ptrVal.offsetBytes % 8 ≠ 0` on an 8-byte aligned type, `evalDerefReadScalarMiri`
   fails with `.error (.undefinedBehavior _)`; when `mptr` has no concrete provenance
   (`Pointer.withoutProvenance addr`), `Miri.Memory.checkAndDerefPtr` fails with
   `.error (.danglingIntegerPointer addr 8 .memoryAccess)`. -/
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
      ptrVal.offsetBytes = 0 →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ →
      get? s.frame.locals e.localIdx = some (.init (.scalar sc)) →
      m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
        some (e.allocId, localAlloc) →
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8 →
      ScalarRel sc msc →
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
      ptrVal.offsetBytes = 0 →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ →
      get? s.frame.locals e.localIdx = some oldSlot →
      oldSlot ≠ .dead →
      set? s.frame.locals e.localIdx (.init (.scalar sc)) = some locals' →
      m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
        some (e.allocId, localAlloc) →
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8 →
      ScalarRel sc msc →
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
Simulation of `BinOp.Offset` (`inbounds` vs. `wrapping`) between Anneal's
`MirSemantics` and `lean-miri`'s `Miri.Interpreter.ptrOffsetInbounds` /
`Miri.Memory.Pointer.wrappingSignedOffset`:

1. **In-Bounds Offset Equivalence (`iff`)**:
   For any pointer `PtrRel allocMap ptrVal mptr` pointing into a live allocation
   `localAlloc` at `ptrVal.offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat`
   and any non-negative offset `deltaBytes < 2^32`, `lean-miri`'s
   `Miri.Interpreter.ptrOffsetInbounds` succeeds if and only if
   `ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat`
   (including the zero-offset / ZST edge case `deltaBytes = 0`).
2. **In-Bounds `PtrRel` Preservation**:
   When `ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat`
   and `ptrVal.offsetBytes + deltaBytes < 2^32`, Anneal's
   `evalRvalue (.binaryOp .offset ...)` produces
   `.ok (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + deltaBytes } 8)` and
   `lean-miri`'s `ptrOffsetInbounds` produces `.ok ⟨mptr'.offset, some mptr'.provenance⟩`
   such that `PtrRel allocMap { ptrVal with offsetBytes := ptrVal.offsetBytes + deltaBytes } mptr'`
   holds!
3. **Out-of-Bounds & Dangling UB vs. Wrapping Offset**:
   When `localAlloc.allocation.byteSize.bytes.toNat < ptrVal.offsetBytes + deltaBytes`,
   `ptrOffsetInbounds` fails with `.error (.access (.pointerOutOfBounds ...))` (while
   `wrappingSignedOffset` succeeds without bounds/liveness checks). -/
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

/-- **`evalCast_ptrToPtr_simulation` (`LM-3.1` Deliverable 4)**:
Simulation of `CastKind.PtrToPtr` (and pointer/integer expose/withExposed casts)
between Anneal's `MirSemantics.evalRvalue` and `lean-miri`'s
`Miri.Interpreter.Cast.ptrToPtr` under `annealCastHooksLM3_1`:

1. **`PtrToPtr` Simulation**: Casting a raw pointer `.ptr ptrVal 8` related by
   `ImmediateRelLM3_1 allocMap srcTy layouts` from `srcTy` (`*const T` or `*mut T`)
   to `dstTy` (`*const U` or `*mut U`) succeeds in both Anneal and `lean-miri`,
   preserving the exact pointer provenance and address and establishing
   `ImmediateRelLM3_1 allocMap dstTy layouts (.ptr ptrVal 8) res.imm`.
2. **Expose / WithExposed Provenance Round-Trip**: Exposing a pointer's provenance
   to an integer and reconstructing a pointer from that exposed integer address
   round-trips `ProvenancePtr` in Anneal (`offsetBytes < 65536`) and reconstructs
   the concrete `Miri.Memory.Pointer` via `(annealCastHooksLM3_1 layouts).pointerFromExposedAddress`. -/
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

/-- Well-typed `LM-3.1` statement forms covered by `step_stmt_lm3_1_simulation`:
- `rawPtrAddrOf`: `_dst = &raw (const|mut) _target`
- `derefRead`: `_dst = copy *_ptr`
- `ptrOffset`: `_dst = Offset(copy _ptr, copy _off)`
- `ptrToPtrCast`: `_dst = copy _src as *const/*mut U (PtrToPtr)` -/
inductive WellTypedLM3_1Stmt (body : CapturedMir) (s : MachineState) (m : AnnealStepState)
    (allocMap : List AllocMapEntry) : Statement → Prop where
  | rawPtrAddrOf
      (dstIdx targetIdx : Local) (mutability : Mutability) (pointeeKind : RigidTy)
      (dstDecl targetDecl : LocalDecl) (span : String)
      (imm : Miri.Interpreter.RvalueImmTy AnnealProv) (m' : AnnealStepState)
      (allocId : Miri.Memory.AllocId) (mptr : Miri.Memory.Pointer AnnealProv) :
      get? body.localDecls dstIdx = some dstDecl →
      get? body.localDecls targetIdx = some targetDecl →
      dstDecl.ty.kind = .rawPtr mutability pointeeKind →
      evalRawPtrAddrOfMiri body.localDecls body.layouts targetIdx dstDecl.ty m = .ok imm m' →
      imm.imm = .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr) →
      mptr.provenance = .concrete allocId Miri.Memory.BorTag.one →
      mptr.offset = Miri.ABI.Size.ofBytes (annealStackBaseAddr allocId) →
      allocId.value.toNat < 2 ^ 32 →
      WellTypedLM3_1Stmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩
  | derefRead
      (dstIdx ptrLoc : Local) (ptrVal : ProvenancePtr)
      (mptr : Miri.Memory.Pointer AnnealProv) (pointeeTy : Ty)
      (e : AllocMapEntry) (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (span : String) :
      AllocMapRel body s m allocMap →
      get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)) →
      (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 8 →
      (translateTy pointeeTy body.layouts).layout.align.abi = Miri.ABI.Align.EIGHT →
      e ∈ allocMap →
      e.tag = ptrVal.tag →
      e.perm ≠ .disabled →
      ptrVal.offsetBytes = 0 →
      mptr = ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr e.allocId),
        .concrete e.allocId Miri.Memory.BorTag.one⟩ →
      get? s.frame.locals e.localIdx = some (.init (.scalar sc)) →
      m.machine.memory.live.find? (fun entry => entry.1 == e.allocId) =
        some (e.allocId, localAlloc) →
      localAlloc.allocation.byteSize = Miri.ABI.Size.ofBytes 8 →
      sc.sizeBytes = 8 →
      ScalarRel sc msc →
      localAlloc.allocation.readScalar annealTargetDataLayout
        (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) false =
        .ok (.fromScalarInt msc) →
      WellTypedLM3_1Stmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.use (.copy ⟨ptrLoc, .cons .deref .nil⟩)), span⟩
  | ptrOffset
      (dstIdx ptrLoc offLoc : Local) (ptrVal : ProvenancePtr)
      (mptr : Miri.Memory.Pointer AnnealProv) (deltaBytes : Nat) (offsetSc : MirAst.ScalarInt)
      (allocId : Miri.Memory.AllocId) (borTag : Miri.Memory.BorTag)
      (localAlloc :
        Miri.Memory.LocalAllocation
          AnnealProv
          (Option Miri.TreeBorrows.BorrowTree)
          Miri.Memory.MiriMemoryKind)
      (span : String) :
      PtrRel allocMap ptrVal mptr →
      mptr.provenance = .concrete allocId borTag →
      m.machine.lookupBaseAddr allocId = some (annealStackBaseAddr allocId) →
      m.machine.memory.live.find? (fun entry => entry.1 == allocId) = some (allocId, localAlloc) →
      ptrVal.offsetBytes ≤ localAlloc.allocation.byteSize.bytes.toNat →
      deltaBytes < 2 ^ 32 →
      ptrVal.offsetBytes + deltaBytes ≤ localAlloc.allocation.byteSize.bytes.toNat →
      ptrVal.offsetBytes + deltaBytes < 2 ^ 32 →
      offsetSc.bits = deltaBytes →
      get? s.frame.locals ptrLoc = some (.init (.ptr ptrVal 8)) →
      get? s.frame.locals offLoc = some (.init (.scalar offsetSc)) →
      WellTypedLM3_1Stmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩
          (.binaryOp .offset (.copy ⟨ptrLoc, .nil⟩) (.copy ⟨offLoc, .nil⟩)), span⟩
  | ptrToPtrCast
      (dstIdx srcLoc : Local) (ptrVal : ProvenancePtr)
      (mptr : Miri.Memory.Pointer AnnealProv)
      (srcMut dstMut : Mutability) (srcPointee dstPointee : RigidTy)
      (srcTy dstTy : Ty) (span : String) :
      srcTy.kind = .rawPtr srcMut srcPointee →
      dstTy.kind = .rawPtr dstMut dstPointee →
      get? s.frame.locals srcLoc = some (.init (.ptr ptrVal 8)) →
      PtrRel allocMap ptrVal mptr →
      WellTypedLM3_1Stmt body s m allocMap
        ⟨.assign ⟨dstIdx, .nil⟩ (.cast .ptrToPtr (.copy ⟨srcLoc, .nil⟩) dstTy), span⟩

/-- **`step_stmt_lm3_1_simulation` (`LM-3.1` Deliverable 5)**:
Composed `LM-3.1` statement-level simulation theorem dispatching across
`WellTypedLM3_1Stmt`:
- `rawPtrAddrOf` (`_dst = &raw (const|mut) _target`),
- `derefRead` (`_dst = copy *_ptr`),
- `ptrOffset` (`_dst = Offset(copy _ptr, copy _off)`), and
- `ptrToPtrCast` (`_dst = copy _src as *const/*mut U`).

In every case, Anneal's Rvalue/Operand evaluator and `lean-miri`'s corresponding
evaluator (`evalRawPtrAddrOfMiri`, `evalDerefReadScalarMiri`,
`Miri.Interpreter.ptrOffsetInbounds`, `Miri.Interpreter.Cast.ptrToPtr`) succeed
in lockstep and produce `ImmediateRelLM3_1`-related values. -/
theorem step_stmt_lm3_1_simulation
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {stmt : Statement}
    (hstate : StateRel body s m)
    (hwt : WellTypedLM3_1Stmt body s m allocMap stmt) :
    ∃ (dstIdx : Local) (rv : Rvalue) (span : String)
      (v : Value) (locals' : List LocalSlot) (mem' : Memory)
      (allocMap' : List AllocMapEntry) (ty : Ty) (imm : Miri.Interpreter.Immediate AnnealProv),
      stmt = ⟨.assign ⟨dstIdx, .nil⟩ rv, span⟩ ∧
      evalRvalue s.frame.locals rv s.memory body.localDecls body.layouts =
        .ok v locals' mem' ∧
      ImmediateRelLM3_1 allocMap' ty body.layouts v imm := by
  cases hwt with
  | rawPtrAddrOf dstIdx targetIdx mutability pointeeKind dstDecl targetDecl span
      imm m' allocId mptr _ htargetDecl hptrTy hok himm hprov haddr hid_lt =>
    have hsim := (evalRvalue_rawPtr_addrOf_simulation allocMap hstate mutability pointeeKind
      dstDecl.ty hptrTy htargetDecl).2 imm m' allocId hok ⟨mptr, himm, hprov, haddr⟩ hid_lt
    obtain ⟨_, heval, hrel⟩ := hsim
    exact ⟨dstIdx, .rawPtr mutability ⟨targetIdx, .nil⟩, span, _, _, _, _, dstDecl.ty, imm.imm,
      rfl, heval, hrel⟩
  | derefRead dstIdx ptrLoc ptrVal mptr pointeeTy e sc msc localAlloc span
      hmap hptr_slot hsz8 halign8 he htag hperm hoff0 hmptr htarget_slot hfind hsz_alloc
      hsc_sz hsc_rel hread_sc =>
    have hderef := (evalProjection_deref_simulation hmap ptrLoc ptrVal mptr
      pointeeTy hptr_slot hsz8 halign8).1 e sc msc localAlloc he htag hperm hoff0 hmptr
      htarget_slot hfind hsz_alloc hsc_rel hread_sc
    obtain ⟨hop, _⟩ := hderef
    rcases id hstate with ⟨_, _, _, _, _, _, _, hbor_nil, _, _, _⟩
    have heval :
        evalRvalue s.frame.locals (.use (.copy ⟨ptrLoc, .cons .deref .nil⟩))
          s.memory body.localDecls body.layouts =
          .ok (.scalar sc) s.frame.locals s.memory := by
      unfold evalRvalue
      dsimp only []
      rw [hop, hbor_nil]
    have hty_bool : pointeeTy.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1) := by
      intro hbool
      have : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 1 := by
        unfold translateTy; rw [hbool]; rfl
      rw [hsz8] at this
      cases this
    have hty_char : pointeeTy.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true := by
      intro hchar
      have : (translateTy pointeeTy body.layouts).layout.size = Miri.ABI.Size.ofBytes 4 := by
        unfold translateTy; rw [hchar]; rfl
      rw [hsz8] at this
      cases this
    have hsz_sc : (translateTy pointeeTy body.layouts).layout.size =
        translateSizeBytes sc.sizeBytes := by
      rw [hsz8, hsc_sz]
      rfl
    exact ⟨dstIdx, .use (.copy ⟨ptrLoc, .cons .deref .nil⟩), span, .scalar sc,
      s.frame.locals, s.memory, allocMap, pointeeTy, .scalar (.fromScalarInt msc),
      rfl, heval, .of_immediateRel (.scalar sc msc hsc_rel hsz_sc hty_bool hty_char)⟩
  | ptrOffset dstIdx ptrLoc offLoc ptrVal mptr deltaBytes offsetSc allocId borTag localAlloc span
      hptr_rel hprov hbase hlive hoff_in hdelta hinbounds hsum_lt hsc_bits hptr_slot hoff_slot =>
    have hoff_sim := (evalBinOp_offset_inbounds_simulation ptrLoc offLoc ptrVal mptr
      deltaBytes offsetSc allocId borTag localAlloc hptr_rel hprov hbase hlive hoff_in
      hdelta hsc_bits hptr_slot hoff_slot).2.1 hinbounds hsum_lt
    obtain ⟨_, _, hptr_rel'⟩ := hoff_sim
    have heval := evalRvalue_binOp_offset_eq s.frame.locals s.memory body.localDecls body.layouts
      ptrLoc offLoc ptrVal offsetSc hptr_slot hoff_slot
    rw [hsc_bits] at heval
    let ptrTy : Ty := { kind := .rawPtr .mut (.int .i64), layoutIdx := 0 }
    exact ⟨dstIdx, .binaryOp .offset (.copy ⟨ptrLoc, .nil⟩) (.copy ⟨offLoc, .nil⟩), span,
      .ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + deltaBytes } 8,
      s.frame.locals, s.memory, allocMap, ptrTy,
      .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
        ⟨Miri.ABI.Size.ofBytes
          (annealStackBaseAddr allocId + UInt64.ofNat (ptrVal.offsetBytes + deltaBytes)),
          .concrete allocId borTag⟩),
      rfl, heval, .rawPtr .mut (.int .i64) _ _ rfl hptr_rel'⟩
  | ptrToPtrCast dstIdx srcLoc ptrVal mptr srcMut dstMut srcPointee dstPointee srcTy dstTy span
      hsrcTy hdstTy hsrc_slot hptr_rel =>
    have hcast := evalCast_ptrToPtr_simulation s.frame.locals s.memory body.localDecls body.layouts
      m srcLoc ptrVal mptr srcMut dstMut srcPointee dstPointee srcTy dstTy hsrcTy hdstTy
      hsrc_slot hptr_rel
    obtain ⟨heval, _, hrel⟩ := hcast
    exact ⟨dstIdx, .cast .ptrToPtr (.copy ⟨srcLoc, .nil⟩) dstTy, span,
      .ptr ptrVal 8, s.frame.locals, s.memory, allocMap, dstTy,
      .scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr),
      rfl, heval, hrel⟩

end LeanMiriSpec.Correspondence
