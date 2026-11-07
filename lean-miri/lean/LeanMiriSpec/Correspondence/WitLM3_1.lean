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
# Witnesses for the `LM-3.1` Correspondence

Concrete, kernel-checked instances of the `LM-3.1` correspondence and
divergence theorems:

1. **`wit_lm3_1_rawPtr_step`**: `step_rawPtr_addrOf_simulation` applies to
   `_2 = &raw mut _1` on the immediate scalar `_1 = 42_u64`; both machines take
   the step (`lean-miri` moving `_1` into a stack allocation), and the resulting
   states satisfy `StateRelLM3_1` under a non-empty `allocMap`.
2. **`wit_lm3_1_addrOf_write_read_deref`** and
   **`wit_lm3_1_addrOf_deref_storageDead_real_steps`**: full execution of the
   address-of, dereference-write, dereference-read, and `StorageDead` body
   (`lm31AddrOfBody`), both via the standalone dereference helpers and chained
   step-by-step through `Miri.Interpreter.Step.step` (`annealStepHooks`) and
   `stepMirFn` (`&raw mut _1` -> `*_2 = 99_u64` -> `_0 = copy *_2` ->
   `StorageDead(_2)` -> `StorageDead(_1)`, verifying `_0 = 99_u64` in
   `lean-miri`'s root frame and stack-allocation deallocation on `StorageDead`).
3. **`wit_lm3_1_binOp_offset_inbounds_and_oob`** and
   **`wit_lm3_1_ptrToPtr_and_offset_real_steps`**: `BinOp.Offset` in-bounds
   one-past-end (`delta = 8`) vs. out-of-bounds (`delta = 9`) behavior, both at
   the `ptrOffsetInbounds` helper level and chained end-to-end through
   `Miri.Interpreter.Step.step` (`annealStepHooks`) and `stepMirFn` across
   `_2 = &raw mut _1` -> `_3 = copy _2 as *mut u8` (`CastKind.PtrToPtr`) ->
   `_4 = Offset(copy _3, 8_usize)` (lockstep) -> `_5 = Offset(copy _3, 9_usize)`
   (Anneal steps vs. `lean-miri` `undefinedBehavior`).
4. **`wit_lm3_1_anneal_offset_deref_divergence`** and
   **`wit_lm3_1_deref_oob_and_misaligned_real_steps`**: real-step witnesses
   chained from pointer-free `StateRel` states showing `Miri.Interpreter.Step.step`
   (`annealStepHooks`) rejects both a one-past-end dereference (`offset = 8` on
   an 8-byte allocation via `step_deref_oob_miri_ub`, where Anneal returns `42`)
   and an in-bounds misaligned `u32` dereference (`offset = 2` on an 8-byte
   allocation via `step_deref_misaligned_miri_ub`).
5. **`wit_lm3_1_use_after_storageDead_ub`** and
   **`wit_lm3_1_use_after_storageDead_real_steps`**: use-after-`StorageDead`
   dangling-pointer dereference UB, both at the helper level and chained end-to-end
   through `Miri.Interpreter.Step.step` (`annealStepHooks`) and `stepMirFn` across
   `_2 = &raw const _1` -> `StorageDead(_1)` -> `_0 = copy *_2`, proving both
   machines diagnose UB on the actual `StateRelLM3_1`-related states reached
   after `StorageDead(_1)`.
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

/-- `_1` and `_2` are immediate in `lm31AddrOfMiriPre`. -/
theorem lm31AddrOf_immediate_pre :
    ∀ topFrame, lm31AddrOfMiriPre.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame 2 ∧ IsImmediateFrameLocal topFrame 1 := by
  intro topFrame h
  injection h with h₁
  injection h₁ with h₂
  subst h₂
  refine ⟨?_, ?_⟩ <;> intro mls hmls mp hmp <;>
    simp [lm31AddrOfMiriFramePre] at hmls <;> subst hmls <;> cases hmp

/-- **`wit_lm3_1_rawPtr_step`**: `step_rawPtr_addrOf_simulation` applies to
statement 3 (`_2 = &raw mut _1`) of `lm31AddrOfBody` from the pointer-free
states of `lm31AddrOf_stateRel_pre`, and both machines really take the step:
Anneal's `stepMirFn` steps, `lean-miri`'s `Miri.Interpreter.Step.step` succeeds
(moving `_1` into the fresh allocation `lm31AllocId1`), and the two resulting
states are related by `StateRelLM3_1` under the non-empty `allocMap` entry
`(tag 1, _1, lm31AllocId1, .active)`. `StateRelLM3_1` with a non-empty
`allocMap` is therefore satisfiable. -/
theorem wit_lm3_1_rawPtr_step :
    ∃ (s' : MachineState) (m' : AnnealStepState),
      stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = .step s' ∧
      Miri.Interpreter.Step.step
          (annealStepHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts) ()
          lm31AddrOfMiriPre = (m', .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s' m'
        [rawPtrAllocMapEntry lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 1
          lm31AllocId1] := by
  have hsim := step_rawPtr_addrOf_simulation (body := lm31AddrOfBody)
    (s := lm31AddrOfAnnealPre) (m := lm31AddrOfMiriPre) lm31AddrOf_stateRel_pre
    (by intro p h; cases h) (dstIdx := 2) (targetIdx := 1) (mutability := .mut)
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    lm31AddrOf_immediate_pre AllocIdSupplyReady.empty
  have hstep : (match stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre with
      | .tau (.running _) => true
      | _ => false) = true := by decide
  generalize hA : stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = aRes at hsim hstep
  generalize hres : Miri.Interpreter.Step.step
    (annealStepHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts) ()
    lm31AddrOfMiriPre = res at hsim
  cases hsim with
  | step s' m' hrel =>
    have htag : lm31AddrOfAnnealPre.memory.nextTag = 1 := by decide
    have hid : (⟨lm31AddrOfMiriPre.machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag, hid] at hrel
    exact ⟨s', m', rfl, rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => simp [MirStepNode.retNormal] at hstep
  | ub _ _ => simp [MirStepNode.fail] at hstep

/-- **`wit_lm3_1_addrOf_write_read_deref`**:
Kernel-checked witness for `LM-3.1` Scenario (a):
1. Running `lm31AddrOfBody` to completion in Anneal (`&raw mut _1`, `*_2 = 99_u64`,
   `_0 = copy *_2`, `StorageDead`, `return`) produces `99_u64` (`some 99`);
2. the address-of step `_2 = &raw mut _1` runs in lockstep through
   `Miri.Interpreter.Step.step`, promoting the immediate local `_1` into the
   stack allocation `lm31AllocId1` and reaching `StateRelLM3_1`-related states
   (`wit_lm3_1_rawPtr_step`);
3. on an allocation of that shape (8 bytes at `annealStackBaseAddr lm31AllocId1`),
   `evalDerefWriteScalarMiri` writes `99_u64` through the pointer and
   `evalDerefReadScalarMiri` reads it back.

Item 3 exercises the standalone `evalDerefWriteScalarMiri` and
`evalDerefReadScalarMiri` helpers directly on a single-allocation machine;
`wit_lm3_1_addrOf_deref_storageDead_real_steps` below chains the entire body
through `Miri.Interpreter.Step.step` (`annealStepHooks`) and `stepMirFn`. -/
theorem wit_lm3_1_addrOf_write_read_deref :
    -- (1) Full bounded execution of `lm31AddrOfBody` in Anneal returns `99_u64`
    annealOutcomeScalarBits 8
      (runAnnealBounded lm31AddrOfBody 9 (initMachineState lm31AddrOfBody [])) = some 99 ∧
    -- (2) The address-of step runs in lockstep to `StateRelLM3_1`-related states
    (∃ (s' : MachineState) (m' : AnnealStepState),
      stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = .step s' ∧
      Miri.Interpreter.Step.step
          (annealStepHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts) ()
          lm31AddrOfMiriPre = (m', .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s' m'
        [rawPtrAllocMapEntry lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 1
          lm31AllocId1]) ∧
    -- (3) Writing `99_u64` through the pointer and reading it back
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
  refine ⟨by decide, wit_lm3_1_rawPtr_step, ?_⟩
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

/-- **`wit_lm3_1_binOp_offset_inbounds_and_oob`**: on an 8-byte stack allocation
`lm31AllocId1`, `lean-miri`'s `ptrOffsetInbounds` at base offset `0` accepts the
one-past-end delta `8` and rejects `9`, and `evalDerefReadScalarMiri` rejects an
8-byte read at offset `8`. Anneal's `Offset` omits the bounds check and its
stack-pointer dereference ignores `offsetBytes`; see
`wit_lm3_1_anneal_offset_deref_divergence`,
`wit_lm3_1_ptrToPtr_and_offset_real_steps`, and
`wit_lm3_1_deref_oob_and_misaligned_real_steps` for the real-step witnesses. -/
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

/-! ## 3b. Divergence: Anneal Dereferences a Pointer Offset Past Its Local -/

/-- `usize` type. -/
def usizeTyLM31 : Ty := { kind := .uint .usize, layoutIdx := 0 }

/-- Constant `usize` operand. -/
def constUsizeLM31 (n : Nat) : ConstOperand :=
  { ty := usizeTyLM31, val := .scalar (.int ⟨n, 8⟩) }

/-- `Runtime(PostCleanup)` MIR body that offsets a pointer to `_1` by one
element and dereferences the result:
```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3);
     _1 = const 42_u64;
     _2 = &raw const _1;
     _3 = Offset(copy _2, const 1_usize);
     _0 = copy *_3;
     return
```
In Rust (and in Miri) the dereference is undefined behavior: `_3` points one
`u64` past the end of `_1`. -/
def lm31OffsetDerefBody : CapturedMir where
  defPath := "lm_3_1_witness::offset_deref_past_end"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 42)))),
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.binaryOp .offset (.copy (local_ 2)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_anneal_offset_deref_divergence`**: Anneal's `MirSemantics`
gives `lm31OffsetDerefBody` a defined result, although the program dereferences
a pointer past the end of `_1`:

1. Anneal runs the body to completion and returns `42`: its `Offset` adds the
   unscaled count `1` to `offsetBytes` without a bounds check, and its
   dereference of a tracked stack pointer reads the borrowed local while
   ignoring `offsetBytes`.
2. `lean-miri` rejects the corresponding access: `Offset(_2, 1)` on a `*const u64`
   moves the address by `8` bytes, and `Miri.Memory.checkAndDerefPtr` reports an
   8-byte access at offset `8` of the 8-byte stack allocation of `_1` as out of
   bounds.

So `LM-3.1` cannot prove "out-of-bounds offsets are undefined behavior in both
semantics" as long as Anneal's trusted semantics keeps this behavior. -/
theorem wit_lm3_1_anneal_offset_deref_divergence :
    annealOutcomeScalarBits 8
      (runAnnealBounded lm31OffsetDerefBody 10 (initMachineState lm31OffsetDerefBody [])) =
      some 42 ∧
    ∃ alloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
      alloc.byteSize = Miri.ABI.Size.ofBytes 8 ∧
      ∃ err, Miri.Memory.checkAndDerefPtr annealPointerArithmetic
        ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 8),
          some (.concrete lm31AllocId1 Miri.Memory.BorTag.one)⟩
        ((8 : Nat) : Int) .memoryAccess
        (annealResolvePtr (mkSingleAllocMachine lm31AllocId1 alloc))
        (annealLookupAlloc (mkSingleAllocMachine lm31AllocId1 alloc)) = .error err := by
  refine ⟨by decide, ?_⟩
  obtain ⟨allocation, htry0, -⟩ :=
    Miri.Memory.Allocation.tryNew_replicate_full (P := AnnealProv) (translateSizeBytes 8)
      ⟨3⟩ 8 rfl rfl
  obtain ⟨hsz, _, _, _⟩ := freshStackAlloc_spec htry0
  refine ⟨allocation.withExtra none, hsz, _,
    checkAndDerefPtr_live_oob_err lm31AllocId1 Miri.Memory.BorTag.one 8 8
      ⟨.stack, allocation.withExtra none⟩ .memoryAccess (by decide) (by decide) rfl rfl
      (by decide) eight_lt_two_pow_63 (by rw [hsz]; decide)⟩

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

/-- **`wit_lm3_1_use_after_storageDead_ub`**: use-after-`StorageDead`
dereference.

1. Running `lm31DanglingBody` in Anneal reports undefined behavior at
   `_0 = copy *_2` after `StorageDead(_1)`.
2. In the Anneal state at that statement (`_1` dead, `_2` holding the raw
   pointer with tag `1`), `evalOperand (.copy ⟨2, [.deref]⟩)` is `.ub`, and on a
   `lean-miri` machine whose allocation `lm31AllocId1` has been freed,
   `evalDerefReadScalarMiri` reports undefined behavior
   (`evalProjection_deref_deadAlloc_ub`). See
   `wit_lm3_1_use_after_storageDead_real_steps` below for the end-to-end
   `Miri.Interpreter.Step.step` (`annealStepHooks`) and `stepMirFn` chain on
   `lm31DanglingBody` through `StorageDead(_1)` and `_0 = copy *_2`. -/
theorem wit_lm3_1_use_after_storageDead_ub :
    -- (1) Full bounded execution of `lm31DanglingBody` in Anneal diagnoses UB
    annealOutcomeIsUB
      (runAnnealBounded lm31DanglingBody 6 (initMachineState lm31DanglingBody [])) = true ∧
    -- (2) Both Anneal (`evalOperand`) and `lean-miri` (`evalDerefReadScalarMiri`) diagnose UB
    (let sDead : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 5
            locals := [.uninit, .dead, .init (.ptr { allocId := 1, offsetBytes := 0 } 8)] }
        memory :=
          { (initMachineState lm31DanglingBody []).memory with
            borrows :=
              [{ tag := 1
                 targetLocal := 1
                 targetProjection := .nil
                 perm := .frozen }]
            nextTag := 2 } }
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
    2 { allocId := 1, offsetBytes := 0 }
    ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0),
      .concrete lm31AllocId1 Miri.Memory.BorTag.one⟩
    u64Ty
    rfl rfl
    { tag := 1, targetLocal := 1, targetProjection := .nil, perm := .frozen }
    lm31AllocId1 Miri.Memory.BorTag.one
    rfl (by intro h; cases h) rfl rfl (by decide) (by decide) rfl rfl

/-! ## 5. End-to-End Real-Interpreter (`Miri.Interpreter.Step.step`) Witnesses -/

/-- `RvalueM` actions that preserve `machine.addresses`, singleton-stack structure,
`location`, and `IsImmediateFrameLocal` for every local `k`. -/
private def RvaluePreservesAllImm {α : Type}
    (act : Miri.Interpreter.RvalueM AnnealStepState α) : Prop :=
  ∀ m a m', act m = .ok a m' →
    m'.machine.addresses = m.machine.addresses ∧
    ∀ tf, m.stack.frames = #[tf] →
      ∃ tf', m'.stack.frames = #[tf'] ∧
        tf'.location = tf.location ∧
        ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k

private theorem rvaluePreservesAllImm_pure {α : Type} (x : α) :
    RvaluePreservesAllImm (pure x) := by
  intro m a m' h
  cases h
  exact ⟨rfl, fun tf htf => ⟨tf, htf, rfl, fun _ hk => hk⟩⟩

private theorem rvaluePreservesAllImm_throw {α : Type} (err : Miri.Interpreter.StepError) :
    RvaluePreservesAllImm (throw err : Miri.Interpreter.RvalueM AnnealStepState α) := by
  intro _ _ _ h
  cases h

private theorem rvaluePreservesAllImm_bind {α β : Type}
    {f : Miri.Interpreter.RvalueM AnnealStepState α}
    {g : α → Miri.Interpreter.RvalueM AnnealStepState β}
    (hf : RvaluePreservesAllImm f) (hg : ∀ x, RvaluePreservesAllImm (g x)) :
    RvaluePreservesAllImm (f >>= g) := by
  intro m b m' h
  change EStateM.bind f g m = .ok b m' at h
  unfold EStateM.bind at h
  cases hfm : f m with
  | error _ _ => rw [hfm] at h; cases h
  | ok x m₁ =>
    rw [hfm] at h
    obtain ⟨haddr₁, hstk₁⟩ := hf m x m₁ hfm
    obtain ⟨haddr₂, hstk₂⟩ := hg x m₁ b m' h
    refine ⟨haddr₂.trans haddr₁, fun tf htf => ?_⟩
    obtain ⟨tf₁, htf₁, hloc₁, himm₁⟩ := hstk₁ tf htf
    obtain ⟨tf₂, htf₂, hloc₂, himm₂⟩ := hstk₂ tf₁ htf₁
    exact ⟨tf₂, htf₂, hloc₂.trans hloc₁, fun k hk => himm₂ k (himm₁ k hk)⟩

private theorem rvaluePreservesAllImm_of_eq {α : Type}
    {act : Miri.Interpreter.RvalueM AnnealStepState α}
    (heq : ∀ m a m', act m = .ok a m' →
      m'.machine.addresses = m.machine.addresses ∧ m'.stack = m.stack) :
    RvaluePreservesAllImm act := by
  intro m a m' h
  obtain ⟨ha, hs⟩ := heq m a m' h
  exact ⟨ha, fun tf htf => ⟨tf, (congrArg Miri.Interpreter.Stack.frames hs).trans htf,
    rfl, fun _ hk => hk⟩⟩

private theorem annealReadImmediate_eq {op : Miri.Interpreter.OpTy AnnealProv}
    {m m' : AnnealStepState} {a : Miri.Interpreter.RvalueImmTy AnnealProv}
    (h : annealReadImmediate op m = .ok a m') :
    m'.machine.addresses = m.machine.addresses ∧ m'.stack = m.stack := by
  rcases op with ⟨opv, lay⟩
  unfold annealReadImmediate at h
  cases opv with
  | immediate imm =>
    cases imm <;> (
      dsimp only [pure, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
        EStateM.throw] at h
      cases h <;> exact ⟨rfl, rfl⟩)
  | indirect mp =>
    unfold annealReadMemoryPlace at h
    dsimp only [] at h
    repeat (first | (cases h <;> exact ⟨rfl, rfl⟩) | split at h)

private theorem rvaluePreservesAllImm_throw_bind {α β} (err : Miri.Interpreter.StepError)
    (g : α → Miri.Interpreter.RvalueM AnnealStepState β) :
    RvaluePreservesAllImm (throw err >>= g) :=
  rvaluePreservesAllImm_of_eq (fun _ _ _ h => nomatch h)

private theorem rvaluePreservesAllImm_pure_bind {α β} (x : α)
    {g : α → Miri.Interpreter.RvalueM AnnealStepState β}
    (hg : RvaluePreservesAllImm (g x)) :
    RvaluePreservesAllImm (pure x >>= g) := by
  intro m b m' h
  exact hg m b m' h

private theorem annealReadImmediate_preserves (op : Miri.Interpreter.OpTy AnnealProv) :
    RvaluePreservesAllImm (annealReadImmediate op) :=
  rvaluePreservesAllImm_of_eq (fun _ _ _ => annealReadImmediate_eq)

private theorem annealDerefOperandToMemPlace_preserves
    (ld : List LocalDecl) (ly : LayoutTable)
    (loc : Miri.MIR.LocalId) (op : Miri.Interpreter.Operand AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm (annealDerefOperandToMemPlace ld ly loc op lay) := by
  unfold annealDerefOperandToMemPlace
  cases lookupDerefPointeeLayout ld ly loc lay with
  | none => exact rvaluePreservesAllImm_throw _
  | some pointeeLay =>
    dsimp only []
    refine rvaluePreservesAllImm_bind (annealReadImmediate_preserves _) (fun ptrImm => ?_)
    cases ptrImm.imm.toScalar with
    | error _ => exact rvaluePreservesAllImm_throw_bind _ _
    | ok s =>
      apply rvaluePreservesAllImm_pure_bind
      cases s.toPointer annealTargetDataLayout with
      | error _ => exact rvaluePreservesAllImm_throw_bind _ _
      | ok p =>
        apply rvaluePreservesAllImm_pure_bind
        cases annealOffsetMisalignment p.offset pointeeLay.layout.align.abi with
        | error _ => exact rvaluePreservesAllImm_throw_bind _ _
        | ok m =>
          apply rvaluePreservesAllImm_pure_bind
          exact rvaluePreservesAllImm_pure _

private theorem annealWriteMemoryPlace_preserves
    (val : Miri.Interpreter.Immediate AnnealProv)
    (mp : Miri.Interpreter.MemPlace AnnealProv) (lay : Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm (annealWriteMemoryPlace val mp lay) := by
  apply rvaluePreservesAllImm_of_eq
  intro m a m' h
  unfold annealWriteMemoryPlace at h
  dsimp only [] at h
  repeat (first | (cases h <;> exact ⟨rfl, rfl⟩) | split at h)

private theorem annealPointerBinary_preserves
    (ly : LayoutTable) (bop : Miri.MIR.BinOp)
    (lv rv : Miri.Interpreter.RvalueImmTy AnnealProv) :
    RvaluePreservesAllImm (annealPointerBinary ly bop lv rv) := by
  apply rvaluePreservesAllImm_of_eq
  intro m a m' h
  unfold annealPointerBinary at h
  dsimp only [] at h
  repeat (first | (cases h <;> exact ⟨rfl, rfl⟩) | split at h)

private theorem assertRvalueLayoutPub_preserves
    (l₁ l₂ : Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm (assertRvalueLayoutPub l₁ l₂) := by
  apply rvaluePreservesAllImm_of_eq
  intro m a m' h
  unfold assertRvalueLayoutPub at h
  split at h <;> cases h <;> exact ⟨rfl, rfl⟩

private theorem castTypeInfoOfEncodedTyId_cases (tyId : Miri.MIR.TyId) :
    ∀ info, castTypeInfoOfEncodedTyId tyId = .ok info →
      info = .boolean ∨ info = .character ∨
        (∃ k, info = .integer k) ∨ (∃ p, info = .rawPointer p) := by
  unfold castTypeInfoOfEncodedTyId
  split <;> intro info h <;> cases h <;>
    first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl rfl)
    | exact Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨_, rfl⟩))

private theorem cast_ptrToPtr_preserves
    (ly : LayoutTable) (src : Miri.Interpreter.RvalueImmTy AnnealProv)
    (target : Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm
      (Miri.Interpreter.Cast.ptrToPtr (annealCastHooks ly) () src target) := by
  unfold Miri.Interpreter.Cast.ptrToPtr
  change RvaluePreservesAllImm
    ((match castTypeInfoOfEncodedTyId src.layout.ty with
      | .ok info => pure info
      | .error err => throw err) >>= _)
  cases hs : castTypeInfoOfEncodedTyId src.layout.ty with
  | error err => exact rvaluePreservesAllImm_throw_bind err _
  | ok sourceKind =>
    apply rvaluePreservesAllImm_pure_bind
    rcases castTypeInfoOfEncodedTyId_cases src.layout.ty sourceKind hs with
      rfl | rfl | ⟨k, rfl⟩ | ⟨p, rfl⟩
    · with_unfolding_all exact rvaluePreservesAllImm_throw_bind _ _
    · with_unfolding_all exact rvaluePreservesAllImm_throw_bind _ _
    · with_unfolding_all exact rvaluePreservesAllImm_throw_bind _ _
    · dsimp only []
      split
      · with_unfolding_all exact rvaluePreservesAllImm_throw_bind _ _
      · change RvaluePreservesAllImm
          ((match castTypeInfoOfEncodedTyId target.ty with
            | .ok info => pure info
            | .error err => throw err) >>= _)
        cases ht : castTypeInfoOfEncodedTyId target.ty with
        | error err => exact rvaluePreservesAllImm_throw_bind err _
        | ok tinfo =>
          apply rvaluePreservesAllImm_pure_bind
          rcases castTypeInfoOfEncodedTyId_cases target.ty tinfo ht with
            rfl | rfl | ⟨tk, rfl⟩ | ⟨tp, rfl⟩
          · with_unfolding_all exact rvaluePreservesAllImm_throw _
          · with_unfolding_all exact rvaluePreservesAllImm_throw _
          · with_unfolding_all exact rvaluePreservesAllImm_throw _
          · dsimp only []
            split
            · exact rvaluePreservesAllImm_pure _
            · refine rvaluePreservesAllImm_bind ?_ (fun pairSize => ?_)
              · cases ((Miri.ABI.Size.fromBits
                    (annealCastHooks ly).target.pointerWidth.bits).mul 2
                    |>.mapError fun e =>
                      Miri.Interpreter.StepError.invalidProgram (toString e)) with
                | ok ps => with_unfolding_all exact rvaluePreservesAllImm_pure ps
                | error err => with_unfolding_all exact rvaluePreservesAllImm_throw err
              · split
                · with_unfolding_all exact rvaluePreservesAllImm_throw_bind _ _
                · cases src.imm with
                  | scalarPair data _ => exact rvaluePreservesAllImm_pure _
                  | scalar _ => with_unfolding_all exact rvaluePreservesAllImm_throw _
                  | uninit => exact rvaluePreservesAllImm_throw _

private theorem getOrCacheLocalLayout_preserves
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Miri.MIR.LocalId} {computed lay : Miri.Interpreter.LocalLayout}
    (h : tf.getOrCacheLocalLayout loc computed = .ok (tf', lay)) :
    tf'.location = tf.location ∧
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  unfold Miri.Interpreter.Frame.getOrCacheLocalLayout Miri.Interpreter.Frame.getLocal at h
  by_cases hlt : loc < tf.locals.size
  · simp only [hlt, ↓reduceDIte, bind, Except.bind, pure, Except.pure] at h
    cases hc : (tf.locals[loc]'hlt).layout with
    | some cached =>
      rw [hc] at h
      injection h with hp
      injection hp with htf _
      subst htf
      exact ⟨rfl, fun _ hk => hk⟩
    | none =>
      rw [hc] at h
      injection h with hp
      injection hp with htf _
      have htf' : tf' = cacheFrameLocalLayout tf loc hlt computed := htf.symm
      subst htf'
      exact ⟨rfl, fun _ hk => hk.cache_layout hlt computed⟩
  · simp [hlt, bind, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h

private theorem replaceLocalValue_immediate_preserves
    {tf tf' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    {loc : Miri.MIR.LocalId} {imm : Miri.Interpreter.Immediate AnnealProv}
    (h : tf.replaceLocalValue loc (.live (.immediate imm)) = .ok tf') :
    tf'.location = tf.location ∧
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  unfold Miri.Interpreter.Frame.replaceLocalValue at h
  by_cases hlt : loc < tf.locals.size
  · simp only [hlt, ↓reduceDIte, pure, Except.pure] at h
    injection h with htf
    subst htf
    refine ⟨rfl, fun k hk mls hmls mp hmp => ?_⟩
    dsimp only [] at hmls
    rw [Array.getElem?_set] at hmls
    by_cases heq : loc = k
    · subst heq
      simp only [↓reduceIte, Option.some.injEq] at hmls
      rw [← hmls] at hmp
      cases hmp
    · simp only [heq, ↓reduceIte] at hmls
      exact hk mls hmls mp hmp
  · simp [hlt, throw, throwThe, MonadExceptOf.throw] at h

private theorem annealResolveAndCacheLocalLayout_preserves
    (ld : List LocalDecl) (ly : LayoutTable)
    (loc : Miri.MIR.LocalId) (known : Option Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm (annealResolveAndCacheLocalLayout ld ly loc known) := by
  intro m a m' h
  refine ⟨?_, fun tf htf => ?_⟩
  · unfold annealResolveAndCacheLocalLayout at h
    dsimp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      EStateM.set, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    cases hcf : m.stack.currentFrame? with
    | none => rw [hcf] at h; cases h
    | some frame =>
      rw [hcf] at h
      dsimp only [] at h
      cases hgl : frame.getLocal loc with
      | error _ => rw [hgl] at h; dsimp only [EStateM.bind, EStateM.throw] at h; cases h
      | ok ls =>
        rw [hgl] at h
        dsimp only [EStateM.bind, EStateM.pure] at h
        cases hopt : (ls.layout <|> lookupLocalDeclLayout ld ly loc <|> known) with
        | none =>
          rw [hopt] at h
          dsimp only [] at h
          cases hty : frame.body.locals[loc]? with
          | none => rw [hty] at h; dsimp only [EStateM.bind, EStateM.throw] at h; cases h
          | some tyId =>
            rw [hty] at h
            dsimp only [EStateM.bind, EStateM.pure] at h
            cases hgor : frame.getOrCacheLocalLayout loc (layoutOfEncodedTyId tyId ly) with
            | error _ => rw [hgor] at h; cases h
            | ok fl =>
              rw [hgor] at h
              rcases fl with ⟨frame', lay'⟩
              by_cases hsz : m.stack.frames.size - 1 < m.stack.frames.size <;>
                simp only [hsz, ↓reduceDIte, EStateM.bind, EStateM.set,
                  EStateM.pure, EStateM.throw] at h <;>
                cases h <;> rfl
        | some comp =>
          rw [hopt] at h
          dsimp only [EStateM.bind, EStateM.pure] at h
          cases hgor : frame.getOrCacheLocalLayout loc comp with
          | error _ => rw [hgor] at h; cases h
          | ok fl =>
            rw [hgor] at h
            rcases fl with ⟨frame', lay'⟩
            by_cases hsz : m.stack.frames.size - 1 < m.stack.frames.size <;>
              simp only [hsz, ↓reduceDIte, EStateM.bind, EStateM.set,
                EStateM.pure, EStateM.throw] at h <;>
              cases h <;> rfl
  · have hcf : m.stack.currentFrame? = some tf :=
      stack_currentFrame?_singleton m.stack tf htf
    unfold annealResolveAndCacheLocalLayout at h
    dsimp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      EStateM.set, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    rw [hcf] at h
    dsimp only [] at h
    cases hgl : tf.getLocal loc with
    | error _ => rw [hgl] at h; cases h
    | ok ls =>
      rw [hgl] at h
      dsimp only [EStateM.bind, EStateM.pure] at h
      cases hopt : (ls.layout <|> lookupLocalDeclLayout ld ly loc <|> known) with
      | none =>
        rw [hopt] at h
        dsimp only [] at h
        cases hty : tf.body.locals[loc]? with
        | none => rw [hty] at h; cases h
        | some tyId =>
          rw [hty] at h
          dsimp only [EStateM.bind, EStateM.pure] at h
          cases hgor : tf.getOrCacheLocalLayout loc (layoutOfEncodedTyId tyId ly) with
          | error _ => rw [hgor] at h; cases h
          | ok fl =>
            rw [hgor] at h
            rcases fl with ⟨tf', lay'⟩
            obtain ⟨hloc, himm⟩ := getOrCacheLocalLayout_preserves hgor
            simp only [htf] at h
            cases h
            exact ⟨tf', rfl, hloc, himm⟩
      | some comp =>
        rw [hopt] at h
        dsimp only [EStateM.bind, EStateM.pure] at h
        cases hgor : tf.getOrCacheLocalLayout loc comp with
        | error _ => rw [hgor] at h; cases h
        | ok fl =>
          rw [hgor] at h
          rcases fl with ⟨tf', lay'⟩
          obtain ⟨hloc, himm⟩ := getOrCacheLocalLayout_preserves hgor
          simp only [htf] at h
          cases h
          exact ⟨tf', rfl, hloc, himm⟩

private theorem annealEvalPlace_preserves
    (ld : List LocalDecl) (ly : LayoutTable) (place : Miri.MIR.Place) :
    RvaluePreservesAllImm (annealEvalPlace ld ly place) := by
  intro m a m' h
  unfold annealEvalPlace at h
  by_cases hemp : (!place.projection.isEmpty) = true
  · simp only [hemp, ↓reduceIte] at h
    cases hproj : place.projection.toList with
    | nil =>
      rw [hproj] at h
      cases h
    | cons p0 ps =>
      cases p0 with
      | Deref =>
        cases ps with
        | nil =>
          rw [hproj] at h
          dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
            EStateM.bind, pure, Pure.pure, EStateM.pure,
            throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
          by_cases hnone : m.stack.currentFrame?.isNone = true
          · simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h
            cases h
          · have hnf : m.stack.currentFrame?.isNone = false := Bool.eq_false_iff.mpr hnone
            simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
            refine (rvaluePreservesAllImm_bind
              (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
              (fun fl => ?_)) m a m' h
            cases fl.1.getLocalOperand place.localId with
            | ok op =>
              exact rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure op) (fun op' =>
                rvaluePreservesAllImm_bind
                  (annealDerefOperandToMemPlace_preserves ld ly place.localId op' fl.2)
                  (fun _ => rvaluePreservesAllImm_pure _))
            | error e =>
              cases e <;> (intro _ _ _ herr; cases herr)
        | cons _ _ => rw [hproj] at h; cases h
      | _ => rw [hproj] at h; cases h
  · have hemp' : (!place.projection.isEmpty) = false := Bool.eq_false_iff.mpr hemp
    simp only [hemp', Bool.false_eq_true, ↓reduceIte] at h
    dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    by_cases hnone : m.stack.currentFrame?.isNone = true
    · simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h
      cases h
    · have hnf : m.stack.currentFrame?.isNone = false := Bool.eq_false_iff.mpr hnone
      simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
      exact (rvaluePreservesAllImm_bind
        (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
        (fun _ => rvaluePreservesAllImm_pure _)) m a m' h

private theorem annealEvalOperand_nonMove_preserves
    (ld : List LocalDecl) (ly : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout)
    (hnm : ∀ p, op ≠ .Move p) :
    RvaluePreservesAllImm (annealEvalOperand ld ly op known) := by
  intro m a m' h
  unfold annealEvalOperand at h
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  by_cases hnone : m.stack.currentFrame?.isNone = true
  · simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h
    cases h
  · have hnf : m.stack.currentFrame?.isNone = false := Bool.eq_false_iff.mpr hnone
    simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
    cases op with
    | Move place => exact absurd rfl (hnm place)
    | Constant c =>
      dsimp only [] at h
      cases hc : evalMirConstImmediate ly c with
      | ok imm =>
        rw [hc] at h; cases h
        exact ⟨rfl, fun tf htf => ⟨tf, htf, rfl, fun _ hk => hk⟩⟩
      | error _ => rw [hc] at h; cases h
    | RuntimeChecks _ =>
      dsimp only [] at h; cases h
    | Copy place =>
      dsimp only [] at h
      refine (rvaluePreservesAllImm_bind
        (annealResolveAndCacheLocalLayout_preserves ld ly place.localId known)
        (fun fl => ?_)) m a m' h
      cases fl.1.getLocalOperand place.localId with
      | error e => cases e <;> (intro _ _ _ herr; cases herr)
      | ok opv =>
        refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure opv) (fun operand => ?_)
        cases place.projection.toList with
        | nil => exact rvaluePreservesAllImm_pure _
        | cons p0 ps =>
          cases p0 with
          | Deref =>
            cases ps with
            | nil =>
              exact rvaluePreservesAllImm_bind
                (annealDerefOperandToMemPlace_preserves ld ly place.localId operand fl.2)
                (fun _ => rvaluePreservesAllImm_pure _)
            | cons _ _ => exact rvaluePreservesAllImm_throw _
          | Field _ _ =>
            cases ps with
            | nil =>
              cases operand with
              | immediate imm =>
                cases imm with
                | scalarPair _ _ => exact rvaluePreservesAllImm_pure _
                | _ => exact rvaluePreservesAllImm_throw _
              | indirect _ => exact rvaluePreservesAllImm_throw _
            | cons _ _ => exact rvaluePreservesAllImm_throw _
          | _ => exact rvaluePreservesAllImm_throw _

private theorem annealWriteImmediate_preserves
    (val : Miri.Interpreter.Immediate AnnealProv)
    (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    RvaluePreservesAllImm (annealWriteImmediate val dest) := by
  intro m a m' h
  rcases dest with ⟨dref, dlay⟩
  cases dref with
  | memory mp =>
    refine ⟨?_, fun tf htf => ?_⟩
    · unfold annealWriteImmediate at h
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      cases hcf : m.stack.currentFrame? with
      | none => rw [hcf] at h; cases h
      | some _ =>
        rw [hcf] at h
        exact (annealWriteMemoryPlace_preserves val mp dlay m a m' h).1
    · have hcf : m.stack.currentFrame? = some tf := stack_currentFrame?_singleton m.stack tf htf
      unfold annealWriteImmediate at h
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      rw [hcf] at h
      exact (annealWriteMemoryPlace_preserves val mp dlay m a m' h).2 tf htf
  | «local» frameIdx localId proj id0 =>
    cases proj with
    | some _ =>
      unfold annealWriteImmediate at h
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      cases hcf : m.stack.currentFrame? <;> rw [hcf] at h <;> cases h
    | none =>
      refine ⟨?_, fun tf htf => ?_⟩
      · unfold annealWriteImmediate at h
        dsimp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
          EStateM.set, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
        cases hcf : m.stack.currentFrame? with
        | none => rw [hcf] at h; cases h
        | some frame =>
          rw [hcf] at h
          dsimp only [] at h
          by_cases hfi : (frameIdx != m.stack.frames.size - 1) = true
          · simp only [hfi, ↓reduceIte] at h; cases h
          · have hfif : (frameIdx != m.stack.frames.size - 1) = false :=
              Bool.eq_false_iff.mpr hfi
            simp only [hfif, Bool.false_eq_true, ↓reduceIte] at h
            cases hlo : frame.getLocalOperand localId with
            | error e => rw [hlo] at h; cases e <;> cases h
            | ok lop =>
              rw [hlo] at h
              cases lop with
              | indirect mp =>
                exact (annealWriteMemoryPlace_preserves val mp dlay m a m' h).1
              | immediate _ =>
                dsimp only [] at h
                cases hrep : frame.replaceLocalValue localId (.live (.immediate val)) with
                | error _ => rw [hrep] at h; dsimp only [EStateM.bind, EStateM.throw] at h; cases h
                | ok f' =>
                  rw [hrep] at h
                  dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.set,
                    EStateM.throw] at h
                  split at h <;> cases h <;> rfl
      · have hcf : m.stack.currentFrame? = some tf :=
          stack_currentFrame?_singleton m.stack tf htf
        unfold annealWriteImmediate at h
        dsimp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
          EStateM.set, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
          throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
        rw [hcf] at h
        simp only [htf] at h
        by_cases hfi : (frameIdx != #[tf].size - 1) = true
        · simp only [hfi, ↓reduceIte] at h; cases h
        · have hfif : (frameIdx != #[tf].size - 1) = false := Bool.eq_false_iff.mpr hfi
          simp only [hfif, Bool.false_eq_true, ↓reduceIte] at h
          cases hlo : tf.getLocalOperand localId with
          | error e => rw [hlo] at h; cases e <;> cases h
          | ok lop =>
            rw [hlo] at h
            cases lop with
            | indirect mp =>
              exact (annealWriteMemoryPlace_preserves val mp dlay m a m' h).2 tf htf
            | immediate _ =>
              dsimp only [] at h
              cases hrep : tf.replaceLocalValue localId (.live (.immediate val)) with
              | error _ => rw [hrep] at h; dsimp only [EStateM.bind, EStateM.throw] at h; cases h
              | ok tf' =>
                rw [hrep] at h
                obtain ⟨hloc, himm⟩ := replaceLocalValue_immediate_preserves hrep
                dsimp only [EStateM.bind, EStateM.pure, EStateM.get, EStateM.set,
                  EStateM.throw] at h
                cases h
                exact ⟨tf', rfl, hloc, himm⟩

private theorem liftScalarResult_preserves {α} (r : Except Miri.Interpreter.StepError α) :
    RvaluePreservesAllImm (liftScalarResult r) := by
  cases r with
  | ok v => exact rvaluePreservesAllImm_pure v
  | error e => exact rvaluePreservesAllImm_throw e

private theorem scalarOpsToScalar_preserves (v : Miri.Interpreter.RvalueImmTy AnnealProv) :
    RvaluePreservesAllImm (scalarOpsToScalar v) :=
  liftScalarResult_preserves _

private theorem scalarOpsToInteger_preserves (v : Miri.Interpreter.RvalueImmTy AnnealProv)
    (k : Miri.MIR.IntegerKind) :
    RvaluePreservesAllImm (scalarOpsToInteger v k) := by
  unfold scalarOpsToInteger
  exact rvaluePreservesAllImm_bind (scalarOpsToScalar_preserves v) (fun _ =>
    rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun _ =>
      rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun _ =>
        rvaluePreservesAllImm_pure _)))

private theorem scalarOpsAssertSameType_preserves
    (l r : Miri.Interpreter.RvalueImmTy AnnealProv) :
    RvaluePreservesAllImm (scalarOpsAssertSameType l r) := by
  unfold scalarOpsAssertSameType
  split <;> first | exact rvaluePreservesAllImm_pure _ | exact rvaluePreservesAllImm_throw _

private theorem scalarOpsFinish_preserves
    (ld : List LocalDecl) (ly : LayoutTable) (lay : Miri.ABI.TyAndLayout Miri.MIR.TyId)
    (res : Miri.Interpreter.IntegerResult) :
    RvaluePreservesAllImm (scalarOpsFinish (annealScalarOpsHooks ld ly) () lay res) := by
  cases res with
  | scalar _ => exact rvaluePreservesAllImm_pure _
  | withOverflow _ _ =>
    exact rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure _) (fun _ =>
      rvaluePreservesAllImm_pure _)
  | boolean _ =>
    exact rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure _) (fun _ =>
      rvaluePreservesAllImm_pure _)
  | ordering _ =>
    exact rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure _) (fun _ =>
      rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun _ =>
        rvaluePreservesAllImm_pure _))

private theorem scalarOpsClassify_preserves
    (ld : List LocalDecl) (ly : LayoutTable) (ty : Miri.MIR.TyId) :
    RvaluePreservesAllImm ((annealScalarOpsHooks ld ly).classify () ty) := by
  unfold annealScalarOpsHooks; dsimp only []
  cases classifyEncodedTyId ty with
  | ok c => exact rvaluePreservesAllImm_pure c
  | error e => exact rvaluePreservesAllImm_throw e

private theorem scalarOps_binary_preserves
    (ld : List LocalDecl) (ly : LayoutTable) (bop : Miri.MIR.BinOp)
    (lv rv : Miri.Interpreter.RvalueImmTy AnnealProv) :
    RvaluePreservesAllImm
      (Miri.Interpreter.ScalarOps.binary (annealScalarOpsHooks ld ly) () bop lv rv) := by
  rw [scalarOps_binary_def]
  refine rvaluePreservesAllImm_bind (scalarOpsClassify_preserves ld ly lv.layout.ty) (fun cls => ?_)
  cases cls with
  | character =>
    exact rvaluePreservesAllImm_bind (scalarOpsAssertSameType_preserves lv rv) (fun _ =>
      rvaluePreservesAllImm_bind (scalarOpsToScalar_preserves lv) (fun _ =>
        rvaluePreservesAllImm_bind (scalarOpsToScalar_preserves rv) (fun _ =>
          rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun _ =>
            rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun _ =>
              rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun res =>
                scalarOpsFinish_preserves ld ly lv.layout res))))))
  | boolean =>
    exact rvaluePreservesAllImm_bind (scalarOpsAssertSameType_preserves lv rv) (fun _ =>
      rvaluePreservesAllImm_bind (scalarOpsToScalar_preserves lv) (fun _ =>
        rvaluePreservesAllImm_bind (scalarOpsToScalar_preserves rv) (fun _ =>
          rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun _ =>
            rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun _ =>
              rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun res =>
                scalarOpsFinish_preserves ld ly lv.layout res))))))
  | floating =>
    exact rvaluePreservesAllImm_bind (scalarOpsAssertSameType_preserves lv rv) (fun _ =>
      rvaluePreservesAllImm_throw _)
  | integer kind =>
    refine rvaluePreservesAllImm_bind (scalarOpsClassify_preserves ld ly rv.layout.ty)
      (fun rcls => ?_)
    cases rcls with
    | integer rightKind =>
      refine rvaluePreservesAllImm_bind (scalarOpsToInteger_preserves lv kind) (fun _ => ?_)
      refine rvaluePreservesAllImm_bind (scalarOpsToInteger_preserves rv rightKind) (fun _ => ?_)
      dsimp only []
      split
      · exact rvaluePreservesAllImm_bind (scalarOpsAssertSameType_preserves lv rv) (fun _ =>
          rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun res =>
            scalarOpsFinish_preserves ld ly lv.layout res))
      · first
        | exact rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure ()) (fun _ =>
            rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun res =>
              scalarOpsFinish_preserves ld ly lv.layout res))
        | exact rvaluePreservesAllImm_bind (liftScalarResult_preserves _) (fun res =>
            scalarOpsFinish_preserves ld ly lv.layout res)
    | _ => exact rvaluePreservesAllImm_throw _
  | pointer | functionPointer =>
    refine rvaluePreservesAllImm_bind (scalarOpsClassify_preserves ld ly rv.layout.ty)
      (fun rhs => ?_)
    cases rhs <;> first
      | exact annealPointerBinary_preserves ly bop lv rv
      | exact rvaluePreservesAllImm_throw _

private theorem cast_dispatch_ptrToPtr_preserves
    (ly : LayoutTable) (src : Miri.Interpreter.OpTy AnnealProv)
    (castTyId : Miri.MIR.TyId) (dest : Miri.Interpreter.RuntimePlace AnnealProv) :
    RvaluePreservesAllImm
      (Miri.Interpreter.Cast.cast (annealCastHooks ly) () 16 src .PtrToPtr castTyId dest) := by
  have hbody : ∀ target, RvaluePreservesAllImm
      (do
        let value ← (annealCastHooks ly).readImmediate () src
        let result ← Miri.Interpreter.Cast.ptrToPtr (annealCastHooks ly) () value target
        (annealCastHooks ly).writeImmediate () result.imm dest) :=
    fun target =>
      rvaluePreservesAllImm_bind (annealReadImmediate_preserves src) (fun value =>
        rvaluePreservesAllImm_bind (cast_ptrToPtr_preserves ly value target) (fun result =>
          annealWriteImmediate_preserves result.imm dest))
  unfold Miri.Interpreter.Cast.cast
  dsimp only []
  split <;>
  · apply rvaluePreservesAllImm_pure_bind
    split
    · contradiction
    · apply rvaluePreservesAllImm_pure_bind
      split
      · change RvaluePreservesAllImm
          ((match castTypeInfoOfEncodedTyId src.layout.ty with
            | .ok info => pure info
            | .error err => throw err) >>= _)
        cases hs : castTypeInfoOfEncodedTyId src.layout.ty with
        | error err => exact rvaluePreservesAllImm_throw_bind err _
        | ok info =>
          apply rvaluePreservesAllImm_pure_bind
          rcases castTypeInfoOfEncodedTyId_cases src.layout.ty info hs with
            rfl | rfl | ⟨k, rfl⟩ | ⟨p, rfl⟩
          · exact hbody _
          · exact hbody _
          · exact hbody _
          · dsimp only []
            split
            · exact rvaluePreservesAllImm_throw_bind _ _
            · exact hbody _
      · contradiction

private theorem step_preserves_of_rvalue
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {stmt : Statement}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    {act : Miri.Interpreter.RvalueM AnnealStepState Unit}
    (heval : Miri.Interpreter.Step.evalStatement
      (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
      Miri.Interpreter.runRvalue act m)
    (hpres : RvaluePreservesAllImm act)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  cases hact : act m with
  | error err m_ev =>
    have herr : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        (m_ev, .error err) := by
      rw [heval]; unfold Miri.Interpreter.runRvalue; rw [hact]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt herr] at hstep
    cases hstep
  | ok u m_ev =>
    cases u
    obtain ⟨haddr, hstk⟩ := hpres m () m_ev hact
    obtain ⟨tf_ev, htf_ev, hloc_ev, himm_ev⟩ := hstk tf hframes
    have hok : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) () (translateStmt stmt) m =
        (m_ev, .ok ()) := by
      rw [heval]; unfold Miri.Interpreter.runRvalue; rw [hact]
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hok htf_ev
      (hloc_ev.trans hfr.location_eq)] at hstep
    injection hstep with hm' _
    subst hm'
    refine ⟨haddr, fun tf₀ tf' htf₀ htf' k hk => ?_⟩
    rw [hframes] at htf₀
    injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
    injection htf' with h₁; injection h₁ with h₁'; subst h₁'
    exact himm_ev k hk

private theorem step_assign_use_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {op : MirAst.Operand} {span : String}
    (hnm : ∀ p, translateOperand op ≠ .Move p)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign dst (.use op), span⟩)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_of_rvalue hstate hbb hstmt
    (evalStatement_assign_use_eq body.localDecls body.layouts dst op span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_nonMove_preserves body.localDecls body.layouts
          (translateOperand op) (some dp.layout) hnm)
        (fun opTy => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves opTy)
          (fun imm => annealWriteImmediate_preserves imm.imm dp))))
    hstep

private theorem step_assign_cast_ptrToPtr_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {srcIdx : Local} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign dst (.cast .ptrToPtr (.copy ⟨srcIdx, .nil⟩) castTy), span⟩)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_of_rvalue hstate hbb hstmt
    (evalStatement_assign_cast_ptrToPtr_eq body.localDecls body.layouts dst
      (.copy ⟨srcIdx, .nil⟩) castTy span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_nonMove_preserves body.localDecls body.layouts
          (translateOperand (.copy ⟨srcIdx, .nil⟩)) none (by rintro _ ⟨⟩))
        (fun src => cast_dispatch_ptrToPtr_preserves body.layouts src (encodeTyId castTy) dp)))
    hstep

private theorem step_assign_binOp_offset_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {ptrIdx : Local} {rhs : MirAst.Operand} {span : String}
    (hnm : ∀ p, translateOperand rhs ≠ .Move p)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign dst (.binaryOp .offset (.copy ⟨ptrIdx, .nil⟩) rhs), span⟩)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_of_rvalue hstate hbb hstmt
    (evalStatement_assign_binOp_offset_eq body.localDecls body.layouts dst
      (.copy ⟨ptrIdx, .nil⟩) rhs span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_nonMove_preserves body.localDecls body.layouts
          (translateOperand (.copy ⟨ptrIdx, .nil⟩)) (some dp.layout) (by rintro _ ⟨⟩))
        (fun lOp => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves lOp)
          (fun lv => rvaluePreservesAllImm_bind
            (annealEvalOperand_nonMove_preserves body.localDecls body.layouts
              (translateOperand rhs) none hnm)
            (fun rOp => rvaluePreservesAllImm_bind
              (annealReadImmediate_preserves rOp)
              (fun rv => rvaluePreservesAllImm_bind
                (scalarOps_binary_preserves body.localDecls body.layouts .Offset lv rv)
                (fun res => rvaluePreservesAllImm_bind
                  (assertRvalueLayoutPub_preserves res.layout dp.layout)
                  (fun _ => annealWriteImmediate_preserves res.imm dp))))))))
    hstep

private theorem step_storageDead_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageDead loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (hne0 : loc ≠ 0)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, _, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
    rw [hmls_eq]; exact hloc.allocLive
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageDead loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .dead } hlt_mf }]⟩
         machine := { m.machine with
            memory := deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value } },
        .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    exact annealStepHooks_storageDead_any_eq hframes hlt_mf hne0 hlive
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hstep
  injection hstep with hm' _
  subst hm'
  refine ⟨rfl, fun tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp => ?_⟩
  rw [hframes] at htf₀
  injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
  injection htf' with h₁; injection h₁ with h₁'; subst h₁'
  dsimp only [] at hmls'
  rw [Array.getElem?_set] at hmls'
  by_cases heq : loc = k
  · subst heq
    simp only [↓reduceIte, Option.some.injEq] at hmls'
    rw [← hmls'] at hmp
    cases hmp
  · simp only [heq, ↓reduceIte] at hmls'
    exact hk mls' hmls' mp hmp

/-- On a successful `_d = &raw (const|mut) _t` step from a pointer-free `StateRel`
state, `addresses.baseAddr` prepends `lm31AllocId1` (when `nextAllocId = 1`), and
every local `k ≠ _t` that was immediate in `m` remains immediate in `m'`. -/
private theorem step_rawPtr_addrOf_preserves_ne
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    (hstate : StateRel body s m)
    {bb : BasicBlockData} {dstIdx targetIdx : Local} {mutability : Mutability} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩)
    {dstDecl targetDecl : LocalDecl}
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hdecl_tgt : get? body.localDecls targetIdx = some targetDecl)
    (htgt_ty : IsPrimScalarTy targetDecl.ty)
    (hne : dstIdx ≠ targetIdx)
    (himm : ∀ topFrame, m.stack.frames = #[topFrame] →
      IsImmediateFrameLocal topFrame dstIdx ∧ IsImmediateFrameLocal topFrame targetIdx)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses.baseAddr =
      #[⟨⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩,
        annealStackBaseAddr ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩⟩] ++
        m.machine.addresses.baseAddr ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, k ≠ targetIdx → IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨himm_dst, himm_tgt⟩ := himm tf hframes
  obtain ⟨_, mls_d, _, hlt_d, _, hmls_d, hmls_d_eq, hloc_d⟩ := hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.layout_eq
  have hdst_eval := annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hfra : FrameRel body m.machine s.frame tfa := hfr.cache_local_layout hdecl_dst hlt_d
  obtain ⟨_, mls_t, _, hlt_t, _, hmls_t, hmls_t_eq, hloc_t⟩ := hfra.lookup_local hdecl_tgt
  have hcache_t : ∀ l, (tfa.locals[targetIdx]'hlt_t).layout = some l →
      l = translateTy targetDecl.ty body.layouts := by
    rw [hmls_t_eq]; exact hloc_t.layout_eq
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
  have hval_tb : (tfb.locals[targetIdx]'(by rw [cacheFrameLocalLayout_size]; exact hlt_t)).value =
      mls_t.value := by
    simp [tfb, cacheFrameLocalLayout, hmls_t_eq]
  cases hloc_t with
  | indirect _ mp _ _ _ _ =>
    exact absurd rfl (himm_tgt.cache_layout hlt_d _ _ hmls_t mp)
  | dead _ _ =>
    have hforce := annealForceAllocation_dead_eq (ld := body.localDecls) (ly := body.layouts)
      (m := { m with stack := ⟨#[tfb]⟩ }) rfl
      (by rw [cacheFrameLocalLayout_size]; exact hlt_t) hval_tb
      (translateTy targetDecl.ty body.layouts)
    have hm_err : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
        ({ m with stack := ⟨#[tfb]⟩ }, .error (.undefinedBehavior "address of dead local")) := by
      rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
      rw [evalRvalueIntoPlace_rawPtr_force_error hdst_eval htgt_eval hforce]
    rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
    cases hstep
  | immediate _ imm _ _ hval =>
    have hlt_tb : targetIdx < tfb.locals.size := by rw [cacheFrameLocalLayout_size]; exact hlt_t
    have hlay_tb : (tfb.locals[targetIdx]'hlt_tb).layout =
        some (translateTy targetDecl.ty body.layouts) := by simp [tfb, cacheFrameLocalLayout]
    obtain ⟨hsized, allocation, htry⟩ := htgt_ty.layout_ok (layouts := body.layouts)
    obtain ⟨_, hshape0⟩ :=
      StackScalarAllocShape.of_tryNew (none : Option Miri.TreeBorrows.BorrowTree) htry
    obtain ⟨mem', hres⟩ := hsupply.reserve_eq
    obtain ⟨alloc', hfill⟩ :
        ∃ alloc' : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree),
          (imm = .uninit ∧ alloc' = allocation.withExtra none) ∨
            ∃ sc, imm = .scalar sc ∧
              Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                (Miri.Memory.allocRange Miri.ABI.Size.ZERO sc.size) sc
                (allocation.withExtra none) = .ok () alloc' := by
      rcases hval with ⟨_, rfl⟩ | ⟨v, _, himmRel⟩
      · exact ⟨_, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨sc, msc, _, rfl, hrel, hsz, _, _⟩ := himmRel.of_primitive_scalar htgt_ty
        obtain ⟨alloc'', hw, -⟩ := StackScalarAllocShape.writeScalar_readScalar hrel (hsz ▸ hshape0)
        exact ⟨alloc'', Or.inr ⟨_, rfl, hw⟩⟩
    have hforce₀ := forceAllocation_promote_eq (m := { m with stack := ⟨#[tfb]⟩ }) rfl hdecl_tgt
      hlt_tb hlay_tb hval_tb hsized htry hres hfill
    let freshId : Miri.Memory.AllocId := ⟨m.machine.memory.nextAllocId, hsupply.nonzero⟩
    have hforce : annealForceAllocation body.localDecls body.layouts
        ⟨.local 0 targetIdx none tfa.localsIdentity, translateTy targetDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfb]⟩ } =
        .ok (stackAllocPlace freshId)
          { stack := ⟨#[{ tfb with
              locals := tfb.locals.set targetIdx
                { tfb.locals[targetIdx]'hlt_tb with
                  value := .live (.indirect (stackAllocPlace freshId)) }
                hlt_tb }]⟩
            machine := stackAllocMachine m.machine mem' freshId alloc' } := by
      unfold annealForceAllocation; erw [hforce₀]
    have hrv := evalRvalueIntoPlace_rawPtr_ok hkind hdst_eval htgt_eval hforce
      (stackAllocPlace_toRef freshId)
    let tfc : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
      { tfb with
        locals := tfb.locals.set targetIdx
          { tfb.locals[targetIdx]'hlt_tb with
            value := .live (.indirect (stackAllocPlace freshId)) }
          hlt_tb }
    let machc := stackAllocMachine m.machine mem' freshId alloc'
    have hdc_eq : tfc.locals[dstIdx]? =
        some { mls_d with layout := some (translateTy dstDecl.ty body.layouts) } := by
      simp only [tfc, tfb, tfa, cacheFrameLocalLayout]
      rw [Array.getElem?_set_ne _ (Ne.symm hne), Array.getElem?_set_ne _ (Ne.symm hne),
        Array.getElem?_set_self, hmls_d_eq]
    obtain ⟨hlt_dc, -⟩ := Array.getElem?_eq_some_iff.mp hdc_eq
    have hget_dc := frame_getLocal_of_getElem? tfc dstIdx _ hdc_eq
    cases hloc_d with
    | indirect _ mp _ _ _ _ => exact absurd rfl (himm_dst _ hmls_d mp)
    | dead _ _ =>
      have hm_err : Miri.Interpreter.Step.evalStatement
          (annealStepHooks body.localDecls body.layouts) ()
          (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.rawPtr mutability ⟨targetIdx, .nil⟩), span⟩) m =
          (⟨⟨#[tfc]⟩, machc⟩, .error (.undefinedBehavior "write to dead local")) := by
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [hrv, annealWriteImmediate_dead (m := ⟨⟨#[tfc]⟩, machc⟩) (id0 := tf.localsIdentity)
          rfl hget_dc]
      rw [miri_step_at_statement_error _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_err] at hstep
      cases hstep
    | immediate _ oldImm _ _ _ =>
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
        rw [hm_stmt]; unfold Miri.Interpreter.runRvalue
        rw [hrv, hw]
      rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ok rfl
        hfr.location_eq] at hstep
      injection hstep with hm' _
      subst hm'
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

/-- Construct a concrete intra-frame `MachineState` in block `0` at `stmtIdx`
with `locals`, `borrows`, and `nextTag`, avoiding nested `stepMirFn` match terms
so `stepMirFn body s = .step s'` reduces by `rfl` in constant time. -/
private def mkWitState (body : CapturedMir) (stmtIdx : Nat) (locals : List LocalSlot)
    (borrows : List BorrowEntry) (nextTag : Nat) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := stmtIdx, locals := locals }
    memory := { (initMachineState body []).memory with
                  borrows := borrows, nextTag := nextTag } }

private theorem stepRelLM3_1_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap := by
  cases hsim with
  | step s₁ m' hrel =>
    injection ha with htau
    injection htau with hs
    subst hs
    exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub _ _ => cases ha

private theorem stepRelLM3_1_of_anneal_ub
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    (hsim : StepRelLM3_1 body m allocMap aRes mRes)
    (ha : aRes = .fail .ub) :
    ∃ m' msg, mRes = (m', .error (.undefinedBehavior msg)) := by
  cases hsim with
  | step _ _ _ => cases ha
  | retRoot _ _ _ _ _ _ _ _ _ => cases ha
  | ub m' msg => exact ⟨m', msg, rfl⟩

private theorem scalarInt_eq_of_scalarRel
    {sc : MirAst.ScalarInt} {msc₁ msc₂ : Miri.Memory.ScalarInt}
    (h₁ : ScalarRel sc msc₁) (h₂ : ScalarRel sc msc₂) : msc₁ = msc₂ := by
  rcases msc₁ with ⟨d₁, sz₁⟩
  rcases msc₂ with ⟨d₂, sz₂⟩
  have hd : d₁ = d₂ := h₁.data_eq.trans h₂.data_eq.symm
  have hsz : sz₁ = sz₂ := h₁.size_eq.trans h₂.size_eq.symm
  subst hd hsz
  rfl

private theorem constU64_wellTyped (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hcan : n < scalarModulus 8) :
    WellTypedScalarOperand body tf (.constant (constU64 n)) u64Ty :=
  .constScalar (constU64 n) ⟨n, 8⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hcan rfl (fun h => nomatch h) (fun h => nomatch h)

private theorem constUsize_wellTyped (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hcan : n < scalarModulus 8) :
    WellTypedScalarOperand body tf (.constant (constUsizeLM31 n)) usizeTyLM31 :=
  .constScalar (constUsizeLM31 n) ⟨n, 8⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hcan rfl (fun h => nomatch h) (fun h => nomatch h)

private theorem lm31AddrOf_all_immediate_pre :
    ∀ tf, lm31AddrOfMiriPre.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 => simp [lm31AddrOfMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 3 => simp [lm31AddrOfMiriFramePre] at hmls

private theorem ptrVal_of_some_init {p q : ProvenancePtr}
    (h : some (LocalSlot.init (.ptr p 8)) = some (LocalSlot.init (.ptr q 8))) : q = p := by
  injection h with h₁; injection h₁ with h₂; injection h₂ with h₃ _; exact h₃.symm

private theorem slot_ptr_ne_scalar {p : ProvenancePtr} {sz : Nat} {sc : MirAst.ScalarInt} :
    some (LocalSlot.init (.ptr p sz)) ≠ some (LocalSlot.init (.scalar sc)) := by
  intro h; injection h with h₁; injection h₁ with h₂; cases h₂

/-- **`wit_lm3_1_addrOf_deref_storageDead_real_steps`**:
End-to-end 5-step execution of `lm31AddrOfBody` through BOTH Anneal's `stepMirFn`
and `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`):
1. `_2 = &raw mut _1`: promotes `_1 = 42_u64` into fresh stack allocation
   `lm31AllocId1`;
2. `*_2 = const 99_u64`: writes `99_u64` through `_2` into `lm31AllocId1`;
3. `_0 = copy *_2`: reads `99_u64` back through `_2` into `_0` (storing
   `.live (.immediate (.scalar (.fromScalarInt lm31Scalar99)))` in `lean-miri`'s
   root frame and `.init (.scalar ⟨99, 8⟩)` in Anneal's frame);
4. `StorageDead(_2)`: kills the pointer local `_2`;
5. `StorageDead(_1)`: deallocates `lm31AllocId1` from `lean-miri`'s live memory
   (`m₅.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none`), with
   all 5 post-states related by `StateRelLM3_1`. -/
theorem wit_lm3_1_addrOf_deref_storageDead_real_steps :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (allocMap₂ allocMap₃ : List AllocMapEntry),
      let hooks := annealStepHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts
      stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31AddrOfMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₁ m₁
        [rawPtrAllocMapEntry lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 1
          lm31AllocId1] ∧
      stepMirFn lm31AddrOfBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₂ m₂ allocMap₂ ∧
      stepMirFn lm31AddrOfBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₃ m₃ allocMap₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      (∀ tf₃, m₃.stack.frames = #[tf₃] →
        (tf₃.locals[0]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99))))) ∧
      stepMirFn lm31AddrOfBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₄ m₄ allocMap₃ ∧
      stepMirFn lm31AddrOfBody s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₅ m₅ allocMap₃ ∧
      m₅.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none := by
  have hphase : ∀ p, lm31AddrOfBody.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let borMut := [rawPtrBorrowEntry lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 1]
  -- Step 1: `_2 = &raw mut _1`
  let s₁ := mkWitState lm31AddrOfBody 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0] borMut 2
  have hs₁ : stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = .step s₁ := rfl
  obtain ⟨s₁', m₁, hs₁', hm₁, hrel₁⟩ := wit_lm3_1_rawPtr_step
  have hs₁_eq : s₁' = s₁ := by
    rw [hs₁] at hs₁'; injection hs₁' with h; injection h with h'; exact h'.symm
  subst hs₁_eq
  obtain ⟨haddr₁, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne lm31AddrOf_stateRel_pre
    rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    lm31AddrOf_immediate_pre AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step lm31AddrOfMiriFramePre tf₁ rfl htf₁ k hne (lm31AddrOf_all_immediate_pre _ rfl k)
  -- Step 2: `*_2 = const 99_u64`
  let s₂ := mkWitState lm31AddrOfBody 5 [.uninit, .init (.scalar ⟨99, 8⟩), .init ptr0] borMut 2
  have hs₂ : stepMirFn lm31AddrOfBody s₁ = .step s₂ := rfl
  obtain ⟨allocMap₂, hsim₂⟩ := step_deref_write_simulation hrel₁ hphase rfl rfl
    rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (valTy := u64Ty) rfl
    (fun tf₁ _ => constU64_wellTyped lm31AddrOfBody tf₁ 99 (by decide))
    (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
    (fun ptrVal e tgtDecl hp he _ htgt _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = u64Decl := Option.some.inj htgt.symm
        subst hp' hd
        exact ⟨rfl, Or.inl rfl, rfl⟩)
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
  obtain ⟨haddr₂, himm₂_step⟩ := step_assign_use_preserves hrel₁ (by rintro _ ⟨⟩)
    rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `_0 = copy *_2`
  let s₃ := mkWitState lm31AddrOfBody 6
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr0] borMut 2
  have hs₃ : stepMirFn lm31AddrOfBody s₂ = .step s₃ := rfl
  obtain ⟨allocMap₃, hsim₃⟩ := step_deref_read_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
    rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 0 (by decide), himm₂ tf₂ htf₂ 2 (by decide)⟩)
    (fun ptrVal hp e he _ _ => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
      obtain ⟨_, _, _, _, _, _, _, _, _, hbor_eq₂, _, _⟩ := id hrel₂
      have hbor₂ : s₂.memory.borrows =
          [{ tag := 1, targetLocal := 1, targetProjection := .nil, perm := .active }] := rfl
      have hmem_b : e.toBorrowEntry ∈ s₂.memory.borrows := by
        rw [hbor_eq₂]; exact List.mem_map_of_mem he
      rw [hbor₂] at hmem_b
      have hb_eq := List.mem_singleton.mp hmem_b
      have heloc : e.localIdx = 1 := congrArg BorrowEntry.targetLocal hb_eq
      have heperm : e.perm = .active := congrArg BorrowEntry.perm hb_eq
      subst hp'
      refine ⟨rfl, by rw [heperm]; rintro ⟨⟩, fun decl hdecl => ?_⟩
      rw [heloc] at hdecl
      have h0 : get? lm31AddrOfBody.localDecls 1 = some u64Decl := rfl
      rw [h0] at hdecl
      injection hdecl with hd; subst hd; rfl)
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  obtain ⟨haddr₃, himm₃_step⟩ := step_assign_use_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  have hret99 : ∀ tf₃, m₃.stack.frames = #[tf₃] →
      (tf₃.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99)))) := by
    intro tf₃ htf₃
    obtain ⟨tf₃', htf₃', _, _, hfr₃, _, _, _, _, _, _, _⟩ := id hrel₃
    rw [htf₃'] at htf₃; injection htf₃ with htf_eq; injection htf_eq with htf_eq'; subst htf_eq'
    obtain ⟨slot₀, mls₀, _, _, hslot₀, hmls₀, _, hloc₀⟩ :=
      hfr₃.lookup_local (idx := 0) (decl := u64Decl) rfl
    have hs₀_eq : slot₀ = .init (.scalar ⟨99, 8⟩) := by
      have h0 : get? s₃.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) := rfl
      rw [h0] at hslot₀; exact Option.some.inj hslot₀.symm
    subst hs₀_eq
    rw [hmls₀]
    cases hloc₀ with
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm₃ tf₃' htf₃' 0 (by decide) _ hmls₀ mp)
      | immediate _ imm _ _ hv =>
        rcases hv with ⟨h, _⟩ | ⟨v, hv_eq, himmRel⟩
        · cases h
        · injection hv_eq with hveq; subst hveq
          cases himmRel with
          | scalar _ msc hsc _ _ _ =>
            have hmsc : msc = lm31Scalar99 := scalarInt_eq_of_scalarRel hsc lm31_scalarRel99
            subst hmsc; rfl
  -- Step 4: `StorageDead(_2)`
  let s₄ := mkWitState lm31AddrOfBody 7
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩), .dead] borMut 2
  have hs₄ : stepMirFn lm31AddrOfBody s₃ = .step s₄ := rfl
  have hsim₄ := step_storageDead_lm3_1_simulation hrel₃ hphase rfl rfl
    (decl := rawPtrMutU64Decl) rfl (by decide)
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step hsim₄ hs₄
  obtain ⟨haddr₄, _⟩ := step_storageDead_preserves hrel₃ rfl rfl
    (decl := rawPtrMutU64Decl) rfl (by decide) hm₄
  -- Step 5: `StorageDead(_1)`
  let s₅ := mkWitState lm31AddrOfBody 8 [.init (.scalar ⟨99, 8⟩), .dead, .dead] borMut 2
  have hs₅ : stepMirFn lm31AddrOfBody s₄ = .step s₅ := rfl
  have hsim₅ := step_storageDead_lm3_1_simulation hrel₄ hphase rfl rfl
    (decl := u64Decl) rfl (by decide)
  obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step hsim₅ hs₅
  obtain ⟨haddr₅, _⟩ := step_storageDead_preserves hrel₄ rfl rfl
    (decl := u64Decl) rfl (by decide) hm₅
  have hdealloc : m₅.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none := by
    obtain ⟨tf₅, htf₅, _, _, _, _, _, _, _, hbor_eq₅, halloc_rel₅, _⟩ := id hrel₅
    have hbor₅ : s₅.memory.borrows =
        [{ tag := 1, targetLocal := 1, targetProjection := .nil, perm := .active }] := rfl
    cases halloc₃ : allocMap₃ with
    | nil =>
      rw [hbor₅, halloc₃] at hbor_eq₅; cases hbor_eq₅
    | cons e₃ rest =>
      rw [hbor₅, halloc₃] at hbor_eq₅
      injection hbor_eq₅ with he₃ _
      have heloc : e₃.localIdx = 1 := (congrArg BorrowEntry.targetLocal he₃).symm
      have hdead₁ : get? s₅.frame.locals e₃.localIdx = some .dead := by
        rw [heloc]; rfl
      have hfind_none := (halloc_rel₅.local_alloc_sync tf₅ htf₅ e₃
        (halloc₃ ▸ List.Mem.head _)).2 hdead₁
      obtain ⟨_, _, hbase₅⟩ := halloc_rel₅.base_addr_valid e₃ (halloc₃ ▸ List.Mem.head _)
      have hbase_arr : m₅.machine.addresses.baseAddr =
          #[⟨lm31AllocId1, annealStackBaseAddr lm31AllocId1⟩] := by
        have ha : m₅.machine.addresses = m₁.machine.addresses :=
          haddr₅.trans (haddr₄.trans (haddr₃.trans haddr₂))
        rw [congrArg (fun a => a.baseAddr) ha, haddr₁]
        rfl
      unfold AnnealMachine.lookupBaseAddr at hbase₅
      rw [hbase_arr] at hbase₅
      have he_id : e₃.allocId = lm31AllocId1 := by
        by_cases heq : e₃.allocId = lm31AllocId1
        · exact heq
        · have hbeqf : (lm31AllocId1 == e₃.allocId) = false :=
            beq_false_of_ne (Ne.symm heq)
          rw [← Array.find?_toList] at hbase₅
          simp [hbeqf] at hbase₅
      rw [← he_id]
      exact hfind_none
  exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, allocMap₂, allocMap₃,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, rfl, hret99,
    hs₄, hm₄, hrel₄, hs₅, hm₅, hrel₅, hdealloc⟩

/-- Pre-state in Anneal before statement 3 (`_2 = &raw const _1`) of
`lm31DanglingBody`. -/
def lm31DanglingAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 3
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit] }
    memory := (initMachineState lm31DanglingBody []).memory }

/-- Pre-state in `lean-miri` matching `lm31DanglingAnnealPre`. -/
def lm31DanglingMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { lm31AddrOfMiriFramePre with body := translateBody lm31DanglingBody }

/-- Full `AnnealStepState` matching `lm31DanglingAnnealPre`. -/
def lm31DanglingMiriPre : AnnealStepState :=
  { stack := ⟨#[lm31DanglingMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem lm31Dangling_stateRel_pre :
    StateRel lm31DanglingBody lm31DanglingAnnealPre lm31DanglingMiriPre := by
  refine StateRel.mk lm31DanglingMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = u64Decl := by simpa [lm31DanglingBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm31DanglingAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm31DanglingMiriFramePre, lm31AddrOfMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by simpa [lm31DanglingBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [lm31DanglingAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm31DanglingMiriFramePre, lm31AddrOfMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = rawPtrConstU64Decl := by simpa [lm31DanglingBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm31DanglingAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm31DanglingMiriFramePre, lm31AddrOfMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 3 => simp [lm31DanglingBody, get?] at hdecl

private theorem lm31Dangling_all_immediate_pre :
    ∀ tf, lm31DanglingMiriPre.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 =>
    simp [lm31DanglingMiriFramePre, lm31AddrOfMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 3 => simp [lm31DanglingMiriFramePre, lm31AddrOfMiriFramePre] at hmls

/-- **`wit_lm3_1_use_after_storageDead_real_steps`**:
End-to-end 3-step execution of `lm31DanglingBody` through `Miri.Interpreter.Step.step`
(`annealStepHooks`) and `stepMirFn` from `lm31Dangling_stateRel_pre`:
1. `_2 = &raw const _1` promotes `_1` into `lm31AllocId1` in lockstep;
2. `StorageDead(_1)` marks `_1` `.dead` in Anneal and frees `lm31AllocId1` in
   `lean-miri` (`m₂.machine.memory.live.find? ... = none`), maintaining
   `StateRelLM3_1`;
3. `_0 = copy *_2` diagnoses dangling-pointer undefined behavior in BOTH
   `stepMirFn` (`.fail .ub`) and `Miri.Interpreter.Step.step`
   (`.error (.undefinedBehavior msg)`). -/
theorem wit_lm3_1_use_after_storageDead_real_steps :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks lm31DanglingBody.localDecls lm31DanglingBody.layouts
      let entry := rawPtrAllocMapEntry lm31DanglingBody.localDecls lm31DanglingBody.layouts
        .not 1 1 lm31AllocId1
      stepMirFn lm31DanglingBody lm31DanglingAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31DanglingMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 lm31DanglingBody s₁ m₁ [entry] ∧
      stepMirFn lm31DanglingBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31DanglingBody s₂ m₂ [entry] ∧
      m₂.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none ∧
      stepMirFn lm31DanglingBody s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg)) := by
  have hphase : ∀ p, lm31DanglingBody.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, lm31DanglingMiriPre.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨lm31Dangling_all_immediate_pre tf htf 2, lm31Dangling_all_immediate_pre tf htf 1⟩
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let borConst := [rawPtrBorrowEntry lm31DanglingBody.localDecls lm31DanglingBody.layouts .not 1 1]
  -- Step 1: `_2 = &raw const _1`
  let s₁ := mkWitState lm31DanglingBody 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0] borConst 2
  have hs₁ : stepMirFn lm31DanglingBody lm31DanglingAnnealPre = .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation lm31Dangling_stateRel_pre hphase
    rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    himm₀ AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step hsim₁ hs₁
  have htag₀ : lm31DanglingAnnealPre.memory.nextTag = 1 := rfl
  have hid₀ : (⟨lm31DanglingMiriPre.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne lm31Dangling_stateRel_pre
    rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step lm31DanglingMiriFramePre tf₁ rfl htf₁ k hne (lm31Dangling_all_immediate_pre _ rfl k)
  -- Step 2: `StorageDead(_1)`
  let s₂ := mkWitState lm31DanglingBody 5 [.uninit, .dead, .init ptr0] borConst 2
  have hs₂ : stepMirFn lm31DanglingBody s₁ = .step s₂ := rfl
  have hsim₂ := step_storageDead_lm3_1_simulation hrel₁ hphase rfl rfl
    (decl := u64Decl) rfl (by decide)
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
  obtain ⟨_, himm₂_step⟩ := step_storageDead_preserves hrel₁ rfl rfl
    (decl := u64Decl) rfl (by decide) hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  have hdealloc₂ : m₂.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none := by
    obtain ⟨tf₂, htf₂, _, _, _, _, _, _, _, _, halloc₂, _⟩ := id hrel₂
    exact (halloc₂.local_alloc_sync tf₂ htf₂ _ (.head _)).2 rfl
  -- Step 3: `_0 = copy *_2` -> UB in both!
  have hs₃_ub : stepMirFn lm31DanglingBody s₂ = .fail .ub := rfl
  obtain ⟨_, hsim₃⟩ := step_deref_read_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
    rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 0 (by decide), himm₂ tf₂ htf₂ 2 (by decide)⟩)
    (fun _ _ e he _ hnot_dead => by
      cases he with
      | tail _ h => cases h
      | head _ => exact absurd rfl hnot_dead)
  obtain ⟨m₃, msg, hm₃⟩ := stepRelLM3_1_of_anneal_ub hsim₃ hs₃_ub
  exact ⟨s₁, s₂, m₁, m₂, m₃, msg, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hdealloc₂, hs₃_ub, hm₃⟩

/-- Raw pointer `*mut u8` type. -/
def rawPtrMutU8Ty : Ty := { kind := .rawPtr .mut (.uint .u8), layoutIdx := 0 }

/-- Raw pointer `*const u8` type. -/
def rawPtrConstU8Ty : Ty := { kind := .rawPtr .not (.uint .u8), layoutIdx := 0 }

/-- Raw pointer `*const u32` type. -/
def rawPtrConstU32Ty : Ty := { kind := .rawPtr .not (.uint .u32), layoutIdx := 0 }

/-- `u32` type (`4` bytes, `4`-byte aligned). -/
def u32TyLM31 : Ty := { kind := .uint .u32, layoutIdx := 0 }

def rawPtrMutU8Decl : LocalDecl := { mutability := .mut, ty := rawPtrMutU8Ty, debugName := none }
def rawPtrConstU8Decl : LocalDecl := { mutability := .mut, ty := rawPtrConstU8Ty, debugName := none }
def rawPtrConstU32Decl : LocalDecl :=
  { mutability := .mut, ty := rawPtrConstU32Ty, debugName := none }
def u32DeclLM31 : LocalDecl := { mutability := .mut, ty := u32TyLM31, debugName := none }

/-- `Runtime(PostCleanup)` MIR body exercising `&raw mut _1`, `CastKind.PtrToPtr`
(`*mut u64 -> *mut u8`), in-bounds one-past-end `BinOp.Offset(..., 8_usize)`, and
out-of-bounds `BinOp.Offset(..., 9_usize)`:
```text
bb0: _2 = &raw mut _1;
     _3 = copy _2 as *mut u8 (PtrToPtr);
     _4 = Offset(copy _3, const 8_usize);
     _5 = Offset(copy _3, const 9_usize);
     return
``` -/
def lm31PtrCastOffsetBody : CapturedMir where
  defPath := "lm_3_1_witness::ptr_to_ptr_and_offset"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU8Decl, rawPtrMutU8Decl,
    rawPtrMutU8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 4)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 8)))),
        mkStmt (.assign (local_ 5)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 9))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Generic 6-local pre-state in Anneal (`stmtIdx = 0`, `_1 = 42_u64`, all other
locals `.uninit`). -/
def mkSixLocalAnnealPre (body : CapturedMir) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState body []).memory }

/-- Generic 6-local root frame in `lean-miri` (`stmtIdx = 0`, `_1 = 42_u64`
immediate, all other locals `.uninit` immediate). -/
def mkSixLocalMiriFramePre (body : CapturedMir) (retTy : Ty) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy retTy) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def mkSixLocalMiriPre (body : CapturedMir) (retTy : Ty) : AnnealStepState :=
  { stack := ⟨#[mkSixLocalMiriFramePre body retTy]⟩, machine := AnnealMachine.empty }

private theorem mkSixLocal_all_immediate (body : CapturedMir) (retTy : Ty) :
    ∀ tf, (mkSixLocalMiriPre body retTy).stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 =>
    simp [mkSixLocalMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 6 => simp [mkSixLocalMiriFramePre] at hmls

private theorem mkSixLocal_stateRel
    (body : CapturedMir) (retTy : Ty) (d₀ d₂ d₃ d₄ d₅ : LocalDecl)
    (hdecls : body.localDecls = [d₀, u64Decl, d₂, d₃, d₄, d₅])
    (hlay : body.layouts = emptyLayoutTable) :
    StateRel body (mkSixLocalAnnealPre body) (mkSixLocalMiriPre body retTy) := by
  refine StateRel.mk (mkSixLocalMiriFramePre body retTy) rfl rfl ⟨translateTy retTy, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => rintro ⟨⟩)
  refine ⟨rfl, rfl, by simp [mkSixLocalAnnealPre, hdecls], by simp [mkSixLocalMiriFramePre, hdecls],
    ?_⟩
  intro i decl slot mls hdecl hslot hmls
  rw [hdecls] at hdecl
  match i with
  | 0 | 2 | 3 | 4 | 5 =>
    have hs : slot = .uninit := by simpa [mkSixLocalAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkSixLocalMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by simpa [get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [mkSixLocalAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [mkSixLocalMiriFramePre] using hmls.symm
    subst hd hs hm
    rw [hlay]
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 6 => simp [get?] at hdecl

/-- **`wit_lm3_1_ptrToPtr_and_offset_real_steps`**:
End-to-end 4-step execution of `lm31PtrCastOffsetBody` through
`Miri.Interpreter.Step.step` (`annealStepHooks`) and `stepMirFn`:
1. `_2 = &raw mut _1`: promotes `_1` to `lm31AllocId1` in lockstep;
2. `_3 = copy _2 as *mut u8`: executes `CastKind.PtrToPtr` in lockstep via
   `step_cast_ptrToPtr_simulation`;
3. `_4 = Offset(copy _3, const 8_usize)`: executes one-past-end `BinOp.Offset` in
   lockstep via `step_binOp_offset_simulation`, storing `offsetBytes = 8` in `_4`;
4. `_5 = Offset(copy _3, const 9_usize)`: Anneal's `stepMirFn` steps while
   `lean-miri`'s `Miri.Interpreter.Step.step` raises `.error (.undefinedBehavior msg)`
   via `step_binOp_offset_oob_dangling_miri_ub`. -/
theorem wit_lm3_1_ptrToPtr_and_offset_real_steps :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState) (msg : String),
      let hooks := annealStepHooks lm31PtrCastOffsetBody.localDecls lm31PtrCastOffsetBody.layouts
      let entry := rawPtrAllocMapEntry lm31PtrCastOffsetBody.localDecls
        lm31PtrCastOffsetBody.layouts .mut 1 1 lm31AllocId1
      stepMirFn lm31PtrCastOffsetBody (mkSixLocalAnnealPre lm31PtrCastOffsetBody) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre lm31PtrCastOffsetBody u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 lm31PtrCastOffsetBody s₁ m₁ [entry] ∧
      stepMirFn lm31PtrCastOffsetBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31PtrCastOffsetBody s₂ m₂ [entry] ∧
      stepMirFn lm31PtrCastOffsetBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 lm31PtrCastOffsetBody s₃ m₃ [entry] ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn lm31PtrCastOffsetBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior msg)) := by
  have hrel₀ : StateRel lm31PtrCastOffsetBody (mkSixLocalAnnealPre lm31PtrCastOffsetBody)
      (mkSixLocalMiriPre lm31PtrCastOffsetBody u64Ty) :=
    mkSixLocal_stateRel lm31PtrCastOffsetBody u64Ty u64Decl rawPtrMutU64Decl rawPtrMutU8Decl
      rawPtrMutU8Decl rawPtrMutU8Decl rfl rfl
  have hphase : ∀ p, lm31PtrCastOffsetBody.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (mkSixLocalMiriPre lm31PtrCastOffsetBody u64Ty).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  let bor := [rawPtrBorrowEntry lm31PtrCastOffsetBody.localDecls
    lm31PtrCastOffsetBody.layouts .mut 1 1]
  -- Step 1: `_2 = &raw mut _1`
  let s₁ := mkWitState lm31PtrCastOffsetBody 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn lm31PtrCastOffsetBody (mkSixLocalAnnealPre lm31PtrCastOffsetBody) =
      .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step hsim₁ hs₁
  have htag₀ : (mkSixLocalAnnealPre lm31PtrCastOffsetBody).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalMiriPre lm31PtrCastOffsetBody u64Ty).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
  -- Step 2: `_3 = copy _2 as *mut u8`
  let s₂ := mkWitState lm31PtrCastOffsetBody 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn lm31PtrCastOffsetBody s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar)
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
  obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `_4 = Offset(copy _3, const 8_usize)` (one-past-end inbounds!)
  let s₃ := mkWitState lm31PtrCastOffsetBody 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr8, .uninit] bor 2
  have hs₃ : stepMirFn lm31PtrCastOffsetBody s₂ = .step s₃ := rfl
  have hsim₃ := step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
    (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
    (fun tf₂ _ => constUsize_wellTyped lm31PtrCastOffsetBody tf₂ 8 (by decide))
    (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar)
    (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
      have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
      have hsc' : sc = ⟨8, 8⟩ := by
        change evalOperand s₂.frame.locals (.constant (constUsizeLM31 8)) _ _ _ _ = _ at hsc
        injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
      cases he with
      | tail _ h => cases h
      | head _ =>
        have hd : tgtDecl = u64Decl := Option.some.inj htgt.symm
        subst hp' hsc' hd
        exact Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  obtain ⟨_, himm₃_step⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4: `_5 = Offset(copy _3, const 9_usize)` (Anneal steps vs. `lean-miri` UB!)
  obtain ⟨hs₄, m₄, msg, hm₄⟩ := step_binOp_offset_oob_dangling_miri_ub hrel₃ hphase rfl rfl
    (dstDecl := rawPtrMutU8Decl) (ptrDecl := rawPtrMutU8Decl) (tgtDecl := u64Decl)
    rfl rfl rfl (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
    (fun tf₃ _ => constUsize_wellTyped lm31PtrCastOffsetBody tf₃ 9 (by decide))
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 3 (by decide)⟩)
    (ptrVal := { allocId := 1, offsetBytes := 0 }) (sc := ⟨9, 8⟩)
    rfl rfl (by rintro ⟨⟩) (.head _) rfl rfl (by decide) (by decide) (Or.inr (by decide))
  exact ⟨s₁, s₂, s₃, _, m₁, m₂, m₃, m₄, msg,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, rfl, hs₄, hm₄⟩

/-- `Runtime(PostCleanup)` MIR body that offsets a pointer to `_1` by `8` bytes
(one past the end of `_1`), casts back to `*const u64`, and dereferences `*_5`. -/
def lm31DerefOobRealBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_oob_real"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrConstU8Decl, rawPtrConstU8Decl,
    rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstU8Ty)),
        mkStmt (.assign (local_ 4)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 8)))),
        mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrConstU64Ty)),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 5))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body that offsets a pointer to `_1 : u64` by `2`
bytes (strictly in-bounds for a `4`-byte `u32` read: `2 + 4 = 6 ≤ 8`, but
misaligned for `Align = 4`), casts to `*const u32`, and dereferences `*_5`. -/
def lm31DerefMisalignedRealBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_misaligned_real"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32DeclLM31, u64Decl, rawPtrConstU64Decl, rawPtrConstU8Decl, rawPtrConstU8Decl,
    rawPtrConstU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstU8Ty)),
        mkStmt (.assign (local_ 4)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 2)))),
        mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrConstU32Ty)),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 5))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_oob_and_misaligned_real_steps`**:
Real-step (`Miri.Interpreter.Step.step` under `annealStepHooks`) witnesses from
pointer-free `StateRel` states exercising BOTH out-of-bounds dereference UB
(`step_deref_oob_miri_ub`) and in-bounds misaligned dereference UB
(`step_deref_misaligned_miri_ub`):
1. On `lm31DerefOobRealBody` (`&raw const _1` -> `as *const u8` -> `Offset(_, 8)`
   -> `as *const u64` -> `_0 = copy *_5`), the first 4 steps execute in lockstep
   to `StateRelLM3_1`-related states; at step 5 (`_0 = copy *_5`), Anneal's
   `stepMirFn` steps with `_0 = 42_u64` while `Miri.Interpreter.Step.step` raises
   `StepError.undefinedBehavior` (`8 < 8 + 8`).
2. On `lm31DerefMisalignedRealBody` (`&raw const _1` -> `as *const u8` ->
   `Offset(_, 2)` -> `as *const u32` -> `_0 = copy *_5`), the first 4 steps
   execute in lockstep to `StateRelLM3_1`-related states where `*_5` is strictly
   in-bounds (`2 + 4 = 6 ≤ 8`); at step 5 (`_0 = copy *_5`),
   `Miri.Interpreter.Step.step` raises `StepError.undefinedBehavior` due to
   4-byte misalignment at byte offset `2`. -/
theorem wit_lm3_1_deref_oob_and_misaligned_real_steps :
    -- (1) Real-step one-past-end OOB dereference (`offset = 8` on 8-byte `_1`)
    (∃ (s₄ s₅ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefOobRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      stepMirFn b s₄ = .step s₅ ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) ∧
    -- (2) Real-step in-bounds misaligned `u32` dereference (`offset = 2`, `2 + 4 ≤ 8`)
    (∃ (s₄ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefMisalignedRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  refine ⟨?_, ?_⟩
  · -- Part (1): `lm31DerefOobRealBody`
    have hrel₀ : StateRel lm31DerefOobRealBody (mkSixLocalAnnealPre lm31DerefOobRealBody)
        (mkSixLocalMiriPre lm31DerefOobRealBody u64Ty) :=
      mkSixLocal_stateRel lm31DerefOobRealBody u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU8Decl
        rawPtrConstU8Decl rawPtrConstU64Decl rfl rfl
    have hphase : ∀ p, lm31DerefOobRealBody.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, (mkSixLocalMiriPre lm31DerefOobRealBody u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry lm31DerefOobRealBody.localDecls
      lm31DerefOobRealBody.layouts .not 1 1]
    let s₁ := mkWitState lm31DerefOobRealBody 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn lm31DerefOobRealBody (mkSixLocalAnnealPre lm31DerefOobRealBody) =
        .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalAnnealPre lm31DerefOobRealBody).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalMiriPre lm31DerefOobRealBody u64Ty).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    let s₂ := mkWitState lm31DerefOobRealBody 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn lm31DerefOobRealBody s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    let s₃ := mkWitState lm31DerefOobRealBody 3
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr8, .uninit] bor 2
    have hs₃ : stepMirFn lm31DerefOobRealBody s₂ = .step s₃ := rfl
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
      (step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
        (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
        (fun tf₂ _ => constUsize_wellTyped lm31DerefOobRealBody tf₂ 8 (by decide))
        (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
        (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
          have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
          have hsc' : sc = ⟨8, 8⟩ := by
            change evalOperand s₂.frame.locals (.constant (constUsizeLM31 8)) _ _ _ _ = _ at hsc
            injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
          cases he with
          | tail _ h => cases h
          | head _ =>
            have hd : tgtDecl = u64Decl := Option.some.inj htgt.symm
            subst hp' hsc' hd; exact Or.inr ⟨by rintro ⟨⟩, by decide⟩)) hs₃
    obtain ⟨_, himm₃_step⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
      rfl rfl hm₃
    have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
      intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
    let s₄ := mkWitState lm31DerefOobRealBody 4
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr8, .init ptr8] bor 2
    have hs₄ : stepMirFn lm31DerefOobRealBody s₃ = .step s₄ := rfl
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₄
    obtain ⟨_, himm₄_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
    have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
      intro tf₄ htf₄ k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
      exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
    obtain ⟨tf₄, htf₄, _, _, _, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
    obtain ⟨_, _, hsh₄⟩ :=
      (halloc₄.local_alloc_sync tf₄ htf₄ _ (.head _)).1 (.init (.scalar ⟨42, 8⟩)) rfl nofun
    obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh₄ u64Decl rfl
    have hoob : localAlloc.allocation.byteSize.bytes.toNat <
        8 + (translateTy u64Decl.ty lm31DerefOobRealBody.layouts).layout.size.bytes.toNat := by
      rw [hshape_la.byteSize_eq]; decide
    obtain ⟨m₅, msg, hm₅⟩ := step_deref_oob_miri_ub hrel₄ (Or.inl rfl) rfl rfl
      (dstDecl := u64Decl) (ptrDecl := rawPtrConstU64Decl) rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf htf => himm₄ tf htf 5 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 8 })
      rfl (.head _) rfl hfind_la hoob
    let s₅ := mkWitState lm31DerefOobRealBody 5
      [.init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0,
        .init ptr8, .init ptr8] bor 2
    have hs₅ : stepMirFn lm31DerefOobRealBody s₄ = .step s₅ := rfl
    exact ⟨s₄, s₅, m₄, m₅, msg, hrel₄, rfl, hs₅, rfl, hm₅⟩
  · -- Part (2): `lm31DerefMisalignedRealBody`
    have hrel₀ : StateRel lm31DerefMisalignedRealBody
        (mkSixLocalAnnealPre lm31DerefMisalignedRealBody)
        (mkSixLocalMiriPre lm31DerefMisalignedRealBody u32TyLM31) :=
      mkSixLocal_stateRel lm31DerefMisalignedRealBody u32TyLM31 u32DeclLM31 rawPtrConstU64Decl
        rawPtrConstU8Decl rawPtrConstU8Decl rawPtrConstU32Decl rfl rfl
    have hphase : ∀ p, lm31DerefMisalignedRealBody.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf,
        (mkSixLocalMiriPre lm31DerefMisalignedRealBody u32TyLM31).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry lm31DerefMisalignedRealBody.localDecls
      lm31DerefMisalignedRealBody.layouts .not 1 1]
    let s₁ := mkWitState lm31DerefMisalignedRealBody 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn lm31DerefMisalignedRealBody
        (mkSixLocalAnnealPre lm31DerefMisalignedRealBody) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalAnnealPre lm31DerefMisalignedRealBody).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalMiriPre lm31DerefMisalignedRealBody u32TyLM31).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    let s₂ := mkWitState lm31DerefMisalignedRealBody 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn lm31DerefMisalignedRealBody s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    let s₃ := mkWitState lm31DerefMisalignedRealBody 3
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .uninit] bor 2
    have hs₃ : stepMirFn lm31DerefMisalignedRealBody s₂ = .step s₃ := rfl
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
      (step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
        (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
        (fun tf₂ _ => constUsize_wellTyped lm31DerefMisalignedRealBody tf₂ 2 (by decide))
        (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
        (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
          have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
          have hsc' : sc = ⟨2, 8⟩ := by
            change evalOperand s₂.frame.locals (.constant (constUsizeLM31 2)) _ _ _ _ = _ at hsc
            injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
          cases he with
          | tail _ h => cases h
          | head _ =>
            have hd : tgtDecl = u64Decl := Option.some.inj htgt.symm
            subst hp' hsc' hd; exact Or.inr ⟨by rintro ⟨⟩, by decide⟩)) hs₃
    obtain ⟨_, himm₃_step⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
      rfl rfl hm₃
    have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
      intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
    let s₄ := mkWitState lm31DerefMisalignedRealBody 4
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .init ptr2] bor 2
    have hs₄ : stepMirFn lm31DerefMisalignedRealBody s₃ = .step s₄ := rfl
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₄
    obtain ⟨_, himm₄_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
    have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
      intro tf₄ htf₄ k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
      exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
    obtain ⟨tf₄, htf₄, _, _, _, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
    obtain ⟨_, _, hsh₄⟩ :=
      (halloc₄.local_alloc_sync tf₄ htf₄ _ (.head _)).1 (.init (.scalar ⟨42, 8⟩)) rfl nofun
    obtain ⟨localAlloc, hfind_la, _, _, hshape_la⟩ := hsh₄ u64Decl rfl
    have hinb : 2 +
        (translateTy u32DeclLM31.ty lm31DerefMisalignedRealBody.layouts).layout.size.bytes.toNat ≤
        localAlloc.allocation.byteSize.bytes.toNat := by
      rw [hshape_la.byteSize_eq]; decide
    obtain ⟨m₅, msg, hm₅⟩ := step_deref_misaligned_miri_ub hrel₄ (Or.inl rfl) rfl rfl
      (dstDecl := u32DeclLM31) (ptrDecl := rawPtrConstU32Decl) rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
      (fun tf htf => himm₄ tf htf 5 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 2 })
      rfl (.head _) rfl hfind_la hinb (by decide)
    exact ⟨s₄, m₄, m₅, msg, hrel₄, rfl, rfl, hm₅⟩

end LeanMiriSpec.Correspondence.Witness
