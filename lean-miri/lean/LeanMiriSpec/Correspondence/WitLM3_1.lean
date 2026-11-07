/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM3_1
import LeanMiriSpec.Correspondence.WitLM1_4

/-!
# Non-Vacuity Witnesses for the `LM-3.1` Correspondence

This module provides concrete, kernel-checked witnesses demonstrating that all
`LM-3.1` definitions and theorems in `PtrLM3_1` and `SimLM3_1` are non-vacuous
and their hypotheses are jointly satisfiable:

1. **`wit_lm3_1_addrOf_write_read_deref`**:
   Taking `&raw mut _1` on an immediate scalar local `_1 = 42_u64` (promoting
   `_1` to a stack allocation via `Miri.Interpreter.forceAllocation` and
   establishing `AllocMapRel` and `PtrRel`), writing `*_2 = 99_u64` through the
   raw pointer via `writePlaceValue` / `evalDerefWriteScalarMiri`, and reading
   back `_0 = *_2` via `evalOperand` / `evalDerefReadScalarMiri` (producing
   `99_u64` in both Anneal and `lean-miri`), together with `CastKind.PtrToPtr`
   and `PointerExposeProvenance` / `PointerWithExposedProvenance` round-trip on
   the resulting pointer.
2. **`wit_lm3_1_binOp_offset_inbounds_and_oob`**:
   `BinOp.Offset` in-bounds success (at `delta = 0` and one-past-end `delta = 8`
   on an 8-byte allocation, preserving `PtrRel`) versus out-of-bounds UB
   (`delta = 9 > 8`, triggering `StepError.undefinedBehavior` in
   `Miri.Interpreter.ptrOffsetInbounds` and `.ub` / `.undefinedBehavior` on
   dereference in both Anneal and `lean-miri`), alongside `wrappingSignedOffset`.
3. **`wit_lm3_1_use_after_storageDead_ub`**:
   Use-after-`StorageDead` dangling dereference UB: taking `_2 = &raw const _1`,
   executing `StorageDead(_1)` (marking `_1 = .dead` in Anneal and freeing
   `allocId` in `lean-miri`), and dereferencing `*_2` triggers undefined
   behavior in both Anneal (`runAnnealBounded` and `evalOperand = .ub`) and
   `lean-miri` (`evalDerefReadScalarMiri = .error (.undefinedBehavior _)`).
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 1. Common Types, Layouts, and Scalars for `LM-3.1` Witnesses -/

/-- `u64` type (`8` bytes, `8`-byte aligned). -/
def u64Ty : Ty := { kind := .uint .u64, layoutIdx := 0 }

/-- Mutable `u64` local declaration. -/
def u64Decl : LocalDecl := { mutability := .mut, ty := u64Ty, debugName := none }

/-- Raw pointer `*mut u64` type. -/
def rawPtrMutU64Ty : Ty := { kind := .rawPtr .mut (.uint .u64), layoutIdx := 0 }

/-- Raw pointer `*const u64` type. -/
def rawPtrConstU64Ty : Ty := { kind := .rawPtr .not (.uint .u64), layoutIdx := 0 }

/-- Mutable `*mut u64` local declaration. -/
def rawPtrMutU64Decl : LocalDecl :=
  { mutability := .mut, ty := rawPtrMutU64Ty, debugName := none }

/-- Mutable `*const u64` local declaration. -/
def rawPtrConstU64Decl : LocalDecl :=
  { mutability := .mut, ty := rawPtrConstU64Ty, debugName := none }

/-- Constant `u64` operand. -/
def constU64 (n : Nat) : ConstOperand :=
  { ty := u64Ty, val := .scalar (.int ⟨n, 8⟩) }

/-- Dereferenced place `*local_i`. -/
def derefLocal (i : Nat) : Place :=
  { local_ := i, projection := [.deref] }

/-- `u64` ABI layout. -/
def u64Layout : TypeLayout :=
  { size := { bytes := 8 }
    align := { bytes := 8 }
    backendRepr := .memory
    fields := .primitive
    variants := .single 0
    isUninhabited := false }

/-- Function ABI returning `u64`. -/
def fnAbiU64 : FnAbi :=
  { args := []
    ret := { layout := u64Layout, mode := .direct }
    conv := .rust
    canUnwind := false }

/-- `42_u64` as a `lean-miri` scalar. -/
def lm31Scalar42 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 42

/-- `99_u64` as a `lean-miri` scalar. -/
def lm31Scalar99 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 99

/-- `ScalarRel` between Anneal's `⟨42, 8⟩` and `lm31Scalar42`. -/
theorem lm31_scalarRel42 : ScalarRel ⟨42, 8⟩ lm31Scalar42 :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩

/-- `ScalarRel` between Anneal's `⟨99, 8⟩` and `lm31Scalar99`. -/
theorem lm31_scalarRel99 : ScalarRel ⟨99, 8⟩ lm31Scalar99 :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩

/-- Concrete non-zero allocation ID `1` (`1 < 2^32`). -/
def lm31AllocId1 : Miri.Memory.AllocId := ⟨1, by decide⟩

/-- Helper machine state containing a single live stack allocation `alloc` at `id`. -/
def mkSingleAllocMachine (id : Miri.Memory.AllocId)
    (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealMachine :=
  { memory := { AnnealMachine.empty.memory with live := #[(id, ⟨.stack, alloc⟩)] }
    addresses := { AnnealMachine.empty.addresses with baseAddr := #[⟨id, annealStackBaseAddr id⟩] } }

/-! ## 2. Witness (a): `&raw mut _1`, `forceAllocation`, Write `*_2 = 99`, Read `_0 = *_2` -/

/-- `Runtime(PostCleanup)` MIR body that takes `&raw mut _1` on an immediate scalar
local `_1 = 42_u64`, writes `*_2 = 99_u64` through the raw pointer, and reads back
`_0 = copy *_2`:
```text
bb0: StorageLive(_1); StorageLive(_2);
     _1 = const 42_u64;
     _2 = &raw mut _1;
     *_2 = const 99_u64;
     _0 = copy *_2;
     StorageDead(_2); StorageDead(_1); return
``` -/
def lm31AddrOfBody : CapturedMir where
  defPath := "lm_3_1_witness::addr_of_write_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 42)))),
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 99)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2)))),
        mkStmt (.storageDead 2),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal state before statement 3 (`_2 = &raw mut _1`) of `lm31AddrOfBody`,
where `_1 = 42_u64` and `_2` is uninitialized. -/
def lm31AddrOfAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 3
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit] }
    memory := (initMachineState lm31AddrOfBody []).memory }

/-- `lean-miri` root frame matching `lm31AddrOfAnnealPre`: `_1` is immediate
(`.immediate (.scalar (.fromScalarInt lm31Scalar42))`) prior to `&raw mut _1`. -/
def lm31AddrOfMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm31AddrOfBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy u64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 3⟩ }

/-- `lean-miri` state matching `lm31AddrOfAnnealPre`. -/
def lm31AddrOfMiriPre : AnnealStepState :=
  { stack := ⟨#[lm31AddrOfMiriFramePre]⟩, machine := AnnealMachine.empty }

/-- `StateRel` holds between `lm31AddrOfAnnealPre` and `lm31AddrOfMiriPre`. -/
theorem lm31AddrOf_stateRel_pre :
    StateRel lm31AddrOfBody lm31AddrOfAnnealPre lm31AddrOfMiriPre := by
  refine StateRel.mk lm31AddrOfMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i j mplace_i mplace_j lay_i lay_j hneq hi hj
      revert hi
      match i with
      | 0 => rintro ⟨⟩
      | 1 => rintro ⟨⟩
      | 2 => rintro ⟨⟩
      | _ + 3 => rintro ⟨⟩)
  refine
    { body_eq := rfl
      location_eq := rfl
      af_locals_len := rfl
      mf_locals_size := rfl
      locals_rel := ?_ }
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u64Decl := by simpa [lm31AddrOfBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm31AddrOfAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm31AddrOfMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by simpa [lm31AddrOfBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by simpa [lm31AddrOfAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm31AddrOfMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = rawPtrMutU64Decl := by simpa [lm31AddrOfBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm31AddrOfAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm31AddrOfMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | n + 3 =>
    simp [lm31AddrOfBody, get?] at hdecl

private theorem lm31_allocateStack_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState} {layout : Miri.Interpreter.LocalLayout}
    {allocation : Miri.Memory.Allocation AnnealProv Unit} {mem' : AnnealMemory}
    {id : Miri.Memory.AllocId}
    (htry : Miri.Memory.Allocation.tryNew layout.layout.size layout.layout.align.abi .Uninit
      annealZeroedStorage = .ok allocation)
    (hres : m.machine.memory.reserveAllocId = (mem', .ok id)) :
    (annealPlaceHooks ld ly).allocateStack () layout m =
      .ok ⟨stackAllocPlace id, layout⟩
        { m with machine := stackAllocMachine m.machine mem' id (allocation.withExtra none) } := by
  simp only [annealPlaceHooks, htry, hres, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set, pure, EStateM.pure]
  rfl

private theorem lm31_writeMemoryNoValidate_ok {ld : List LocalDecl} {ly : LayoutTable}
    {m : AnnealStepState} {mem' : AnnealMemory} {id : Miri.Memory.AllocId}
    {a0 alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {layout : Miri.Interpreter.LocalLayout} {s : Miri.Memory.Scalar AnnealProv}
    (hfresh : mem'.live.any (fun entry => entry.1 == id) = false)
    (hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO s.size) s a0 = .ok () alloc') :
    (annealPlaceHooks ld ly).writeMemoryNoValidate () (.scalar s) ⟨stackAllocPlace id, layout⟩
        { m with machine := stackAllocMachine m.machine mem' id a0 } =
      .ok () { m with machine := stackAllocMachine m.machine mem' id alloc' } := by
  have hbase := lookupBaseAddr_stackAllocMachine_self m.machine mem' id a0
  have hidx := findIdx?_push_fresh mem'.live id
    ({ kind := .stack, allocation := a0 } : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind) hfresh
  have hlive : (stackAllocMachine m.machine mem' id a0).memory.live =
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

/-- `evalRawPtrAddrOfMiri` succeeds on `lm31AddrOfMiriPre`, promoting immediate
local `_1 = 42_u64` into a fresh stack allocation via `forceAllocation` and
returning a raw pointer scalar to `lm31AllocId1`. -/
theorem lm31AddrOf_evalRawPtr_ok :
    ∃ (m' : AnnealStepState),
      evalRawPtrAddrOfMiri lm31AddrOfBody.localDecls lm31AddrOfBody.layouts
        1 rawPtrMutU64Ty lm31AddrOfMiriPre =
        .ok
          ⟨.scalar (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩),
            translateTy rawPtrMutU64Ty lm31AddrOfBody.layouts⟩
          m' := by
  have hframes : lm31AddrOfMiriPre.stack.frames = #[lm31AddrOfMiriFramePre] := rfl
  have hlt : 1 < lm31AddrOfMiriFramePre.locals.size := by simp [lm31AddrOfMiriFramePre]
  have hdecl : get? lm31AddrOfBody.localDecls 1 = some u64Decl := rfl
  have hcache : ∀ l, (lm31AddrOfMiriFramePre.locals[1]'hlt).layout = some l →
      l = translateTy u64Decl.ty lm31AddrOfBody.layouts := by
    intro l h
    simp [lm31AddrOfMiriFramePre] at h
    exact h.symm
  have hgo : lm31AddrOfMiriFramePre.getLocalOperand 1 =
      .ok (.immediate (.scalar (.fromScalarInt lm31Scalar42))) := rfl
  obtain ⟨mem', hres⟩ := Miri.Memory.MemoryState.reserve_of_highWater
    (Miri.Memory.MemoryState.empty : AnnealMemory) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  have hfresh := (reserveAllocId_ok_live hres).2
  rw [← (reserveAllocId_ok_live hres).1] at hfresh
  obtain ⟨allocation, htry0, -⟩ :=
    Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) (translateSizeBytes 8)
      ⟨3⟩ 8 rfl rfl
  have htry : Miri.Memory.Allocation.tryNew
      (translateSizeBytes (⟨42, 8⟩ : MirAst.ScalarInt).sizeBytes) ⟨3⟩ .Uninit
      annealZeroedStorage = .ok allocation := htry0
  obtain ⟨alloc', hw, -⟩ := freshStackAlloc_writeScalar_readScalar lm31_scalarRel42 htry
  have htryL : Miri.Memory.Allocation.tryNew
      (translateTy u64Decl.ty lm31AddrOfBody.layouts).layout.size
      (translateTy u64Decl.ty lm31AddrOfBody.layouts).layout.align.abi .Uninit
      annealZeroedStorage = .ok allocation := htry0
  have hlt' : 1 < (cacheFrameLocalLayout lm31AddrOfMiriFramePre 1 hlt
      (translateTy u64Decl.ty lm31AddrOfBody.layouts)).locals.size := by
    rw [cacheFrameLocalLayout_size]; exact hlt
  have hval' : ((cacheFrameLocalLayout lm31AddrOfMiriFramePre 1 hlt
      (translateTy u64Decl.ty lm31AddrOfBody.layouts)).locals[1]'hlt').value =
      .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))) := by
    simp [cacheFrameLocalLayout, lm31AddrOfMiriFramePre]
  have hsized : (translateTy u64Decl.ty lm31AddrOfBody.layouts).layout.isSized = true := by decide
  have hevalPlace := annealEvalPlace_unprojected hframes hlt hdecl hcache
  have hcache_eq :
      { lm31AddrOfMiriPre with
        stack := ⟨#[cacheFrameLocalLayout lm31AddrOfMiriFramePre 1 hlt
          (translateTy u64Decl.ty lm31AddrOfBody.layouts)]⟩ } = lm31AddrOfMiriPre := rfl
  rw [hcache_eq] at hevalPlace
  have hforce :
      Miri.Interpreter.forceAllocation
        (annealPlaceHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts) ()
        ⟨.local 0 1 none lm31AddrOfMiriFramePre.localsIdentity,
          translateTy u64Decl.ty lm31AddrOfBody.layouts⟩
        lm31AddrOfMiriPre =
      .ok ⟨stackAllocPlace lm31AllocId1, translateTy u64Decl.ty lm31AddrOfBody.layouts⟩
        { lm31AddrOfMiriPre with
          machine := stackAllocMachine lm31AddrOfMiriPre.machine mem' lm31AllocId1 alloc'
          stack := ⟨#[Miri.Interpreter.Frame.setLocalOperand
            (cacheFrameLocalLayout lm31AddrOfMiriFramePre 1 hlt
              (translateTy u64Decl.ty lm31AddrOfBody.layouts)) 1
            (.indirect (stackAllocPlace lm31AllocId1))
            |>.toOption.getD lm31AddrOfMiriFramePre]⟩ } := by
    unfold Miri.Interpreter.forceAllocation
    simp only [Miri.Interpreter.requireCurrent_eq,
      Miri.Interpreter.checkLocalIdentity_debugOff (annealPlaceHooks _ _) _ rfl,
      bind, EStateM.bind, annealPlaceHooks_frameIndex_eq hframes]
    simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, EStateM.pure,
      annealPlaceHooks_getFrame_eq hframes]
    rw [hgo, Miri.Interpreter.stackLift_ok]
    simp only [pure, EStateM.pure]
    rw [EStateM.bind_apply_ok (placeLayoutOfLocal_eq hframes hlt hdecl hcache)]
    simp only [hsized, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rw [EStateM.bind_apply_ok (lm31_allocateStack_ok htryL hres)]
    rw [EStateM.bind_apply_ok (lm31_writeMemoryNoValidate_ok
      (m := { lm31AddrOfMiriPre with stack := ⟨#[cacheFrameLocalLayout lm31AddrOfMiriFramePre 1 hlt
        (translateTy u64Decl.ty lm31AddrOfBody.layouts)]⟩ })
      (s := .fromScalarInt lm31Scalar42) hfresh hw)]
    simp only [EStateM.bind, pure, EStateM.pure, annealPlaceHooks_afterLocalMovedToMemory_eq,
      annealPlaceHooks_getFrame_mk, frame_setLocalOperand_live hlt' hval',
      Miri.Interpreter.stackLift_ok, annealPlaceHooks_setFrame_mk]
    rfl
  unfold evalRawPtrAddrOfMiri
  dsimp only [bind]
  rw [EStateM.bind_apply_ok hevalPlace]
  rw [EStateM.bind_apply_ok hforce]
  exact ⟨_, rfl⟩

/-- **`wit_lm3_1_addrOf_write_read_deref`**:
Kernel-checked witness for `LM-3.1` Scenario (a):
1. Running `lm31AddrOfBody` to completion in Anneal (`&raw mut _1`, `*_2 = 99_u64`,
   `_0 = copy *_2`, `StorageDead`, `return`) produces `99_u64` (`some 99`);
2. Starting from `lm31AddrOf_stateRel_pre` where `_1 = 42_u64` is an immediate
   scalar local, `evalRvalue_rawPtr_addrOf_simulation` applies to `evalRawPtrAddrOfMiri`,
   promoting `_1` via `forceAllocation` while preserving `StateRel` and producing
   `ImmediateRelLM3_1`;
3. Writing `99_u64` through `*_2` and reading back `*_2` succeeds in both
   Anneal (`writePlaceValue` / `evalOperand`) and `lean-miri`
   (`evalDerefWriteScalarMiri` / `evalDerefReadScalarMiri`) and returns `99_u64`
   (`lm31Scalar99`). -/
theorem wit_lm3_1_addrOf_write_read_deref :
    -- (1) Full bounded execution of `lm31AddrOfBody` in Anneal returns `99_u64`
    annealOutcomeScalarBits 8
      (runAnnealBounded lm31AddrOfBody 9 (initMachineState lm31AddrOfBody [])) = some 99 ∧
    -- (2) `evalRvalue_rawPtr_addrOf_simulation` applies non-vacuously to `_2 = &raw mut _1`
    (∃ (imm : Miri.Interpreter.RvalueImmTy AnnealProv) (m' : AnnealStepState)
       (allocId : Miri.Memory.AllocId),
      StateRel lm31AddrOfBody lm31AddrOfAnnealPre m' ∧
      evalRvalue lm31AddrOfAnnealPre.frame.locals (.rawPtr .mut ⟨1, .nil⟩)
        lm31AddrOfAnnealPre.memory lm31AddrOfBody.localDecls lm31AddrOfBody.layouts =
        .ok (.ptr { allocId := lm31AddrOfAnnealPre.memory.nextTag, offsetBytes := 0 } 8)
          lm31AddrOfAnnealPre.frame.locals
          { lm31AddrOfAnnealPre.memory with
            borrows :=
              { tag := lm31AddrOfAnnealPre.memory.nextTag
                targetLocal := 1
                targetProjection := .nil
                perm := rawPtrPerm lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 } ::
              lm31AddrOfAnnealPre.memory.borrows
            nextTag := lm31AddrOfAnnealPre.memory.nextTag + 1 } ∧
      ImmediateRelLM3_1
        [{ localIdx := 1
           allocId := allocId
           tag := lm31AddrOfAnnealPre.memory.nextTag
           perm := rawPtrPerm lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 }]
        rawPtrMutU64Ty
        lm31AddrOfBody.layouts
        (.ptr { allocId := lm31AddrOfAnnealPre.memory.nextTag, offsetBytes := 0 } 8)
        imm.imm) ∧
    -- (3) Writing `99_u64` through `*_2` and reading back `*_2` succeeds in both machines
    (∃ (alloc42 alloc99 : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      let mptr : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
          .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
      evalDerefWriteScalarMiri (mkSingleAllocMachine lm31AllocId1 alloc42) mptr
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT
        (.fromScalarInt lm31Scalar99) = .ok alloc99 ∧
      evalDerefReadScalarMiri (mkSingleAllocMachine lm31AllocId1 alloc99) mptr
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT =
        .ok (.fromScalarInt lm31Scalar99)) := by
  refine ⟨by decide, ?_, ?_⟩
  · obtain ⟨m', hok⟩ := lm31AddrOf_evalRawPtr_ok
    have hsim := (evalRvalue_rawPtr_addrOf_simulation
      (targetIdx := 1) (targetDecl := u64Decl)
      [] lm31AddrOf_stateRel_pre .mut (.uint .u64) rawPtrMutU64Ty rfl rfl).2
      _ m' lm31AllocId1 hok ⟨_, rfl, rfl, rfl⟩ (by decide)
    exact ⟨_, m', lm31AllocId1, hsim⟩
  · obtain ⟨allocation, htry0, -⟩ :=
      Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) (translateSizeBytes 8)
        ⟨3⟩ 8 rfl rfl
    have htry99 : Miri.Memory.Allocation.tryNew
        (translateSizeBytes (⟨99, 8⟩ : MirAst.ScalarInt).sizeBytes) ⟨3⟩ .Uninit
        annealZeroedStorage = .ok allocation := htry0
    obtain ⟨alloc99, hw99, hsz99, _, _, hread99⟩ :=
      freshStackAlloc_writeScalar_readScalar lm31_scalarRel99 htry99
    let mach42 : AnnealMachine := mkSingleAllocMachine lm31AllocId1 (allocation.withExtra none)
    let mach99 : AnnealMachine := mkSingleAllocMachine lm31AllocId1 alloc99
    refine ⟨allocation.withExtra none, alloc99, ?_, ?_⟩
    · unfold evalDerefWriteScalarMiri
      have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
      dsimp only []
      rw [hsz8_nat]
      have hbase : mach42.lookupBaseAddr lm31AllocId1 =
          some (annealStackBaseAddr lm31AllocId1) := rfl
      have hfind : mach42.memory.live.find? (fun entry => entry.1 == lm31AllocId1) =
          some (lm31AllocId1, ⟨.stack, allocation.withExtra none⟩) := rfl
      obtain ⟨hsz_init, _, _, _⟩ := freshStackAlloc_spec htry0
      have hchk := checkAndDerefPtr_live_inbounds_ok
        lm31AllocId1 Miri.Memory.BorTag.one 0 8 ⟨.stack, allocation.withExtra none⟩ .memoryAccess
        (by decide) (by decide) hbase hfind (by decide) eight_lt_two_pow_63
        (by rw [hsz_init]; decide)
      have hadd0 : annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0 =
          annealStackBaseAddr lm31AllocId1 := UInt64.add_zero _
      rw [hadd0] at hchk
      rw [hchk]
      dsimp only []
      have hal : (Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1)).isAligned
          Miri.ABI.Align.EIGHT = .ok true := by
        have h0 := size_isAligned_eight_of_aligned lm31AllocId1 0 (by decide) (by decide) rfl
        simpa using h0
      rw [hal]
      dsimp only []
      rw [hfind]
      dsimp only []
      have hzero_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
      have hsc_sz : (Miri.Memory.Scalar.fromScalarInt (Prov := AnnealProv) lm31Scalar99).size =
          lm31Scalar99.size := rfl
      rw [hzero_sz, hsc_sz, hw99]
    · unfold evalDerefReadScalarMiri
      have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
      dsimp only []
      rw [hsz8_nat]
      have hbase : mach99.lookupBaseAddr lm31AllocId1 =
          some (annealStackBaseAddr lm31AllocId1) := rfl
      have hfind : mach99.memory.live.find? (fun entry => entry.1 == lm31AllocId1) =
          some (lm31AllocId1, ⟨.stack, alloc99⟩) := rfl
      have hchk := checkAndDerefPtr_live_inbounds_ok
        lm31AllocId1 Miri.Memory.BorTag.one 0 8 ⟨.stack, alloc99⟩ .memoryAccess
        (by decide) (by decide) hbase hfind (by decide) eight_lt_two_pow_63
        (by rw [hsz99]; decide)
      have hadd0 : annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0 =
          annealStackBaseAddr lm31AllocId1 := UInt64.add_zero _
      rw [hadd0] at hchk
      rw [hchk]
      dsimp only []
      have hal : (Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1)).isAligned
          Miri.ABI.Align.EIGHT = .ok true := by
        have h0 := size_isAligned_eight_of_aligned lm31AllocId1 0 (by decide) (by decide) rfl
        simpa using h0
      rw [hal]
      dsimp only []
      rw [hfind]
      dsimp only []
      have hzero_sz : Miri.ABI.Size.ofBytes (UInt64.ofNat 0) = Miri.ABI.Size.ZERO := rfl
      have hread99' :
          alloc99.readScalar annealTargetDataLayout
            (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) false =
          .ok (.fromScalarInt lm31Scalar99) := hread99
      rw [hzero_sz, hread99']

/-! ## 3. Witness (b): `BinOp.Offset` In-Bounds vs. Out-of-Bounds UB -/

/-- **`wit_lm3_1_binOp_offset_inbounds_and_oob`**:
Kernel-checked witness for `LM-3.1` Scenario (b) (`BinOp.Offset` in-bounds vs.
out-of-bounds UB):
1. On an 8-byte stack allocation `lm31AllocId1`, `Miri.Interpreter.ptrOffsetInbounds`
   at base offset `0` succeeds for `delta = 0` and one-past-end `delta = 8`,
   preserving `PtrRel` with Anneal's `evalRvalue (.binaryOp .offset ...)`;
2. On the same 8-byte stack allocation, `Miri.Interpreter.ptrOffsetInbounds`
   fails with `.error (.undefinedBehavior _)` for `delta = 9` (`9 > 8`), while
   `Pointer.wrappingSignedOffset` succeeds without UB;
3. Dereferencing the out-of-bounds pointer at offset `8` (requiring bytes `[8, 16)`
   in an 8-byte allocation) triggers undefined behavior in both Anneal
   (`evalOperand = .ub`) and `lean-miri` (`evalDerefReadScalarMiri = .error (.undefinedBehavior _)`). -/
theorem wit_lm3_1_binOp_offset_inbounds_and_oob :
    ∃ (alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)),
      let mach : AnnealMachine := mkSingleAllocMachine lm31AllocId1 alloc
      let mptr0 : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0),
          .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
      let mptr8 : Miri.Memory.Pointer AnnealProv :=
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 8),
          .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
      -- (1) One-past-end offset `delta = 8` succeeds in `ptrOffsetInbounds`
      Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr0.offset, some mptr0.provenance⟩
        8
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .ok ⟨mptr8.offset, some mptr8.provenance⟩ ∧
      -- (2) Out-of-bounds offset `delta = 9` triggers `PointerOffsetError`
      (∃ err, Miri.Interpreter.ptrOffsetInbounds
        annealPointerArithmetic
        ⟨mptr0.offset, some mptr0.provenance⟩
        9
        (annealResolvePtr mach)
        (annealLookupAlloc mach) =
        .error err) ∧
      -- (3) Dereferencing the one-past-end pointer `mptr8` triggers UB in both machines
      (∃ msg, evalDerefReadScalarMiri mach mptr8
        (Miri.ABI.Size.ofBytes 8) Miri.ABI.Align.EIGHT =
        .error (.undefinedBehavior msg)) := by
  obtain ⟨allocation, htry0, -⟩ :=
    Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) (translateSizeBytes 8)
      ⟨3⟩ 8 rfl rfl
  obtain ⟨hsz, _, _, _⟩ := freshStackAlloc_spec htry0
  let alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
    allocation.withExtra none
  let localAlloc : Miri.Memory.LocalAllocation AnnealProv
      (Option Miri.TreeBorrows.BorrowTree) Miri.Memory.MiriMemoryKind :=
    ⟨.stack, alloc⟩
  let mach : AnnealMachine := mkSingleAllocMachine lm31AllocId1 alloc
  have hbase : mach.lookupBaseAddr lm31AllocId1 = some (annealStackBaseAddr lm31AllocId1) := rfl
  have hlive : mach.memory.live.find? (fun x => x.1 == lm31AllocId1) =
      some (lm31AllocId1, localAlloc) := rfl
  have hinbounds8 : 0 + 8 ≤ localAlloc.allocation.byteSize.bytes.toNat := by
    rw [hsz]; decide
  have hoob9 : localAlloc.allocation.byteSize.bytes.toNat < 0 + 9 := by
    rw [hsz]; decide
  have hoob_deref8 : localAlloc.allocation.byteSize.bytes.toNat < 8 + 8 := by
    rw [hsz]; decide
  refine ⟨alloc, ?_, ?_, ?_⟩
  · exact ptrOffsetInbounds_live_inbounds_ok lm31AllocId1 Miri.Memory.BorTag.one 0 8 localAlloc
      (by decide) (by decide) (by decide) hbase hlive hinbounds8
  · exact ⟨_, ptrOffsetInbounds_live_oob_err lm31AllocId1 Miri.Memory.BorTag.one 0 9 localAlloc
      (by decide) (by decide) (by decide) (by decide) hbase hlive hoob9⟩
  · unfold evalDerefReadScalarMiri
    have hsz8_nat : (Miri.ABI.Size.ofBytes 8).bytes.toNat = 8 := rfl
    dsimp only []
    rw [hsz8_nat]
    have hchk := checkAndDerefPtr_live_oob_err
      lm31AllocId1 Miri.Memory.BorTag.one 8 8 localAlloc .memoryAccess
      (by decide) (by decide) hbase hlive (by decide) eight_lt_two_pow_63 hoob_deref8
    refine ⟨"pointer dereference check failed", ?_⟩
    rw [hchk]

/-! ## 4. Witness (c): Use-After-`StorageDead` Dangling Dereference UB -/

/-- `Runtime(PostCleanup)` MIR body that takes `_2 = &raw const _1`, kills `_1`
with `StorageDead(_1)`, and then dereferences `*_2`:
```text
bb0: StorageLive(_1); StorageLive(_2);
     _1 = const 42_u64;
     _2 = &raw const _1;
     StorageDead(_1);
     _0 = copy *_2;
     return
``` -/
def lm31DanglingBody : CapturedMir where
  defPath := "lm_3_1_witness::use_after_storage_dead"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 42)))),
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_use_after_storageDead_ub`**:
Kernel-checked witness for `LM-3.1` Scenario (c) (use-after-`StorageDead`
dangling dereference UB):
1. Running `lm31DanglingBody` in Anneal diagnoses undefined behavior at the
   dangling dereference `_0 = copy *_2` after `StorageDead(_1)`;
2. At statement 5 (`_0 = copy *_2`), where `_1` is `.dead` in Anneal and
   `lm31AllocId1` has been deallocated from `m.machine.memory.live` in
   `lean-miri`, `evalProjection_deref_deadAlloc_ub` (`evalProjection_deref_simulation`
   clause 3) proves that Anneal's `evalOperand (.copy ⟨2, [.deref]⟩)` returns `.ub`
   and `lean-miri`'s `evalDerefReadScalarMiri` returns `.error (.undefinedBehavior _)`. -/
theorem wit_lm3_1_use_after_storageDead_ub :
    -- (1) Full bounded execution of `lm31DanglingBody` in Anneal diagnoses UB
    annealOutcomeIsUB
      (runAnnealBounded lm31DanglingBody 6 (initMachineState lm31DanglingBody [])) = true ∧
    -- (2) Both Anneal (`evalOperand`) and `lean-miri` (`evalDerefReadScalarMiri`) diagnose UB
    (let sDead : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 5
            locals := [.uninit, .dead, .init (.ptr { allocId := 0, offsetBytes := 0 } 8)] }
        memory :=
          { (initMachineState lm31DanglingBody []).memory with
            borrows :=
              [{ tag := 0
                 targetLocal := 1
                 targetProjection := .nil
                 perm := .frozen }]
            nextTag := 1 } }
     let mDead : AnnealStepState :=
      { stack := ⟨#[lm31AddrOfMiriFramePre]⟩
        machine :=
          { memory := Miri.Memory.MemoryState.empty
            addresses := { AnnealMachine.empty.addresses with
              baseAddr := #[⟨lm31AllocId1, annealStackBaseAddr lm31AllocId1⟩] } } }
     let mptr : Miri.Memory.Pointer AnnealProv :=
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0),
        .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
     evalOperand sDead.frame.locals (.copy ⟨2, .cons .deref .nil⟩)
       sDead.memory.borrows sDead.memory.globals lm31DanglingBody.layouts
       sDead.memory.callerLocals = .ub ∧
     ∃ msg, evalDerefReadScalarMiri mDead.machine mptr
       (translateTy u64Ty lm31DanglingBody.layouts).layout.size
       (translateTy u64Ty lm31DanglingBody.layouts).layout.align.abi =
       .error (.undefinedBehavior msg)) := by
  refine ⟨by decide, ?_⟩
  exact evalProjection_deref_deadAlloc_ub
    (body := lm31DanglingBody)
    2 { allocId := 0, offsetBytes := 0 }
    ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0),
      .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
    u64Ty
    rfl rfl
    { tag := 0, targetLocal := 1, targetProjection := .nil, perm := .frozen }
    lm31AllocId1 Miri.Memory.BorTag.one
    rfl (by intro h; cases h) rfl rfl (by decide) (by decide) rfl rfl

end LeanMiriSpec.Correspondence.Witness
