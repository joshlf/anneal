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
   an 8-byte allocation via `step_deref_oob_divergence`, where Anneal steps with
   `42_u64`) and an in-bounds misaligned `u32` dereference (`offset = 2` on an
   8-byte allocation via `step_deref_misaligned_divergence`, where Anneal also
   steps with `42_u64`).
5. **`wit_lm3_1_use_after_storageDead_ub`** and
   **`wit_lm3_1_use_after_storageDead_real_steps`**: use-after-`StorageDead`
   dangling-pointer dereference UB, both at the helper level and chained end-to-end
   through `Miri.Interpreter.Step.step` (`annealStepHooks`) and `stepMirFn` across
   `_2 = &raw const _1` -> `StorageDead(_1)` -> `_0 = copy *_2`, proving both
   machines diagnose UB on the actual `StateRelLM3_1`-related states reached
   after `StorageDead(_1)`.
6. **`wit_lm3_1_two_promotions_reborrow_and_direct_write_real_steps`**,
   **`wit_lm3_1_invalid_bool_cast_deref_real_steps`**, and
   **`wit_lm3_1_offset_stride_and_neg_isize_real_steps`**: multi-allocation
   real-step execution (`&raw mut _1` + `&raw mut _2` + re-borrow `&raw const _1`
   + direct scalar overwrite `_1 = 77_u64` + explicit-`allocMap'` dereference
   read `_0 = copy *_4`), invalid-`bool` (`2_u8 as *const bool`) dereference
   validity UB divergence, and non-byte stride (`*const u64` + `1_usize`) and
   signed negative `isize` (`-1_isize`) `BinOp.Offset` real-step divergences.
7. **`wit_lm3_1_end_to_end_return_real_steps`**,
   **`wit_lm3_1_rawPtr_deref_null_and_offset_real_steps`**,
   **`wit_lm3_1_anneal_forged_provenance_real_steps`**, and
   **`wit_lm3_1_invalid_char_write_bool_and_placeMention_real_steps`**: full
   6-step execution of `lm31AddrOfBody` through `TerminatorKind.return_`
   popping `lean-miri`'s root frame with `99_u64`; RFC 2582 `&raw const (*_p)`
   divergences on null (`0 as *const u64`) and non-zero offset (`+ 1`);
   `PointerExposeProvenance` fail-closed vs. `PointerWithExposedProvenance`
   (`65536_usize as *const u64`) forged-provenance read of an unexposed local;
   and invalid `char` surrogate read (`0xD800_u32`), invalid `bool` dereference
   write (`2`), and `PlaceMention(*_p)` correspondence vs. `.uninit` divergence.
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

/-! ## 3c. Divergence: Anneal Accesses a Revived Local Through a Stale Pointer -/

/-- `Runtime(PostCleanup)` MIR body that writes and reads through a raw pointer
after its pointee's storage has ended and restarted:
```text
bb0: StorageLive(_1); StorageLive(_2);
     _1 = const 42_u64;
     _2 = &raw mut _1;
     StorageDead(_1);
     StorageLive(_1);
     *_2 = const 7_u64;
     _0 = copy *_2;
     return
```
In Rust (and in Miri), `StorageDead(_1)` ends the allocation that `_2` points
into, so `*_2 = 7` uses a dangling pointer. -/
def lm31ReviveBody : CapturedMir where
  defPath := "lm_3_1_witness::write_through_pointer_into_revived_local"
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
        mkStmt (.storageDead 1),
        mkStmt (.storageLive 1),
        mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 7)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_anneal_storage_revive_divergence`**: Anneal's `MirSemantics`
gives `lm31ReviveBody` a defined result, although the program writes through a
dangling pointer:

1. Anneal runs the body to completion and returns `7`: `StorageDead` and
   `StorageLive` only reset `_1`'s slot and leave `_2`'s borrow entry in place,
   so the write and the read through `_2` reach the revived `_1`.
2. `lean-miri` rejects the access: once `StorageDead(_1)` has freed `_1`'s stack
   allocation (`annealLocalStorageHooks.deallocateStack` keeps only its cached
   base address), `checkAndDerefPtr` reports the access through `_2` as an
   access to a dead allocation.

`AllocMapRel.local_alloc_sync` therefore cannot be kept across `StorageLive` of
a local that a pointer still targets; such states fall outside `StateRelLM3_1`. -/
theorem wit_lm3_1_anneal_storage_revive_divergence :
    annealOutcomeScalarBits 8
      (runAnnealBounded lm31ReviveBody 10 (initMachineState lm31ReviveBody [])) = some 7 ∧
    Miri.Memory.checkAndDerefPtr annealPointerArithmetic
      ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0),
        some (.concrete lm31AllocId1 Miri.Memory.BorTag.one)⟩
      ((8 : Nat) : Int) .memoryAccess
      (annealResolvePtr { AnnealMachine.empty with
        addresses := { AnnealMachine.empty.addresses with
          baseAddr := #[⟨lm31AllocId1, annealStackBaseAddr lm31AllocId1⟩] } })
      (annealLookupAlloc { AnnealMachine.empty with
        addresses := { AnnealMachine.empty.addresses with
          baseAddr := #[⟨lm31AllocId1, annealStackBaseAddr lm31AllocId1⟩] } }) =
      .error (.allocationLookup (.deadAllocation lm31AllocId1)) :=
  ⟨by decide,
    checkAndDerefPtr_deadAlloc_err lm31AllocId1 Miri.Memory.BorTag.one 0 ((8 : Nat) : Int)
      .memoryAccess (by decide) (by decide) rfl rfl (by decide) eight_lt_two_pow_63⟩

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
def RvaluePreservesAllImm {α : Type}
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

theorem step_preserves_of_rvalue
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

theorem step_assign_use_preserves
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

theorem step_assign_cast_ptrToPtr_preserves
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

theorem step_assign_binOp_offset_preserves
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

private theorem evalStatement_placeMention_any_eq
    (ld : List LocalDecl) (ly : LayoutTable) (p : Place) (span : String)
    (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks ld ly) ()
      (translateStmt ⟨.placeMention p, span⟩) m =
    Miri.Interpreter.runRvalue
      (annealEvalPlace ld ly (translatePlace p) >>= fun _ => pure ()) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt translateStmtKind
    annealStepHooks Miri.Interpreter.runRvalue
  dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure]
  cases annealEvalPlace ld ly (translatePlace p) m <;> rfl

theorem step_placeMention_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {p : Place} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.placeMention p, span⟩)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_of_rvalue hstate hbb hstmt
    (evalStatement_placeMention_any_eq body.localDecls body.layouts p span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace p))
      (fun _ => rvaluePreservesAllImm_pure ()))
    hstep

theorem step_storageDead_preserves
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
theorem step_rawPtr_addrOf_preserves_ne
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
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
    (∃ (s₄ s₅ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefMisalignedRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₄ = .step s₅ ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩)) ∧
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
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
      (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
      (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
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
    obtain ⟨⟨s₅, hs₅, hget₅⟩, m₅, msg, hm₅⟩ :=
      step_deref_misaligned_divergence hrel₄ hphase rfl rfl
        (dstDecl := u32DeclLM31) (ptrDecl := rawPtrConstU32Decl) rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
        (fun tf htf => himm₄ tf htf 5 (by decide))
        (ptrVal := { allocId := 1, offsetBytes := 2 })
        rfl (.head _) rfl hfind_la hinb (by decide) (by rintro ⟨⟩) rfl (by rintro ⟨⟩)
    exact ⟨s₄, s₅, m₄, m₅, msg, hrel₄, rfl, rfl, hs₅, hget₅, hm₅⟩

/-! ## 6. Divergence: Anneal Dereferences Through a Narrowing Pointer Cast -/

/-- `Runtime(PostCleanup)` MIR body that reads a `u64` local through a
`*const u32`:
```text
bb0: StorageLive(_1); StorageLive(_2); StorageLive(_3);
     _1 = const 4294967301_u64;          // 2^32 + 5
     _2 = &raw const _1;
     _3 = copy _2 as *const u32 (PtrToPtr);
     _0 = copy *_3;                      // _0 : u32
     return
```
In Rust (and in Miri) `*_3` reads the four low-order bytes of `_1` on this
little-endian target, so the function returns `5_u32`. -/
def lm31TypePunBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_through_narrowing_cast"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32DeclLM31, u64Decl, rawPtrConstU64Decl, rawPtrConstU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.storageLive 2),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 4294967301)))),
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstU32Ty)),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_anneal_deref_type_pun_divergence`**: Anneal's `MirSemantics`
returns the 8-byte scalar `4294967301` from `lm31TypePunBody`, whose return
place has type `u32`: its dereference of a tracked stack pointer returns the
borrowed local's whole value regardless of the pointee type of the pointer
(`*const u32`). No `u32` holds `4294967301`; Rust and Miri return `5_u32`. -/
theorem wit_lm3_1_anneal_deref_type_pun_divergence :
    annealOutcomeScalarBits 8
      (runAnnealBounded lm31TypePunBody 10 (initMachineState lm31TypePunBody [])) =
      some 4294967301 := by
  decide

/-! ## 7. Multi-Promotion, Re-Borrow, Direct Write, Invalid `bool`, Stride & Negative `isize` Real-Step Witnesses -/

/-- Concrete non-zero allocation ID `2` (`2 < 2^32`). -/
def lm31AllocId2 : Miri.Memory.AllocId := ⟨2, by decide⟩

/-- `77_u64` as a `lean-miri` scalar. -/
def lm31Scalar77 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 77

/-- `Runtime(PostCleanup)` MIR body exercising two distinct stack promotions
(`&raw mut _1`, `&raw mut _2`), re-borrowing an already-promoted local
(`&raw const _1`), direct scalar overwrite of a promoted local (`_1 = 77_u64`),
and reading the unaffected second allocation (`_0 = copy *_4`):
```text
bb0: _3 = &raw mut _1;
     _4 = &raw mut _2;
     _5 = &raw const _1;
     _1 = const 77_u64;
     _0 = copy *_4;
     return
``` -/
def lm31TwoPromotionsBody : CapturedMir where
  defPath := "lm_3_1_witness::two_promotions_reborrow_and_direct_write"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl, rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 3) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 4) (.rawPtr .mut (local_ 2))),
        mkStmt (.assign (local_ 5) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 77)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 4))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal pre-state for `lm31TwoPromotionsBody`: `_1 = 42_u64`, `_2 = 99_u64`. -/
def lm31TwoPromotionsAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩),
          .uninit, .uninit, .uninit] }
    memory := (initMachineState lm31TwoPromotionsBody []).memory }

/-- `lean-miri` root frame matching `lm31TwoPromotionsAnnealPre`. -/
def lm31TwoPromotionsMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm31TwoPromotionsBody
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
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar99))),
        layout := some (translateTy u64Ty) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri` pre-state matching `lm31TwoPromotionsAnnealPre`. -/
def lm31TwoPromotionsMiriPre : AnnealStepState :=
  { stack := ⟨#[lm31TwoPromotionsMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem lm31TwoPromotions_stateRel_pre :
    StateRel lm31TwoPromotionsBody lm31TwoPromotionsAnnealPre lm31TwoPromotionsMiriPre := by
  refine StateRel.mk lm31TwoPromotionsMiriFramePre rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 3 | 4 | 5 =>
    have hs : slot = .uninit := by simpa [lm31TwoPromotionsAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm31TwoPromotionsMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by simpa [lm31TwoPromotionsBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [lm31TwoPromotionsAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm31TwoPromotionsMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 2 =>
    have hd : decl = u64Decl := by simpa [lm31TwoPromotionsBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨99, 8⟩) := by
      simpa [lm31TwoPromotionsAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar99))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm31TwoPromotionsMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel99 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 6 => simp [lm31TwoPromotionsBody, get?] at hdecl

private theorem lm31TwoPromotions_all_immediate_pre :
    ∀ tf, lm31TwoPromotionsMiriPre.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 =>
    simp [lm31TwoPromotionsMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 6 => simp [lm31TwoPromotionsMiriFramePre] at hmls

/-- **`wit_lm3_1_two_promotions_reborrow_and_direct_write_real_steps`**:
End-to-end 5-step execution of `lm31TwoPromotionsBody` through BOTH Anneal's
`stepMirFn` and `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`)
with explicit computable `allocMap` tables at every checkpoint:
1. `_3 = &raw mut _1`: promotes `_1 = 42_u64` to `lm31AllocId1` (`nextAllocId = 2`);
2. `_4 = &raw mut _2`: promotes `_2 = 99_u64` to `lm31AllocId2` (`nextAllocId = 3`,
   via `step_rawPtr_addrOf_preserves_supply` + `step_rawPtr_addrOf_lm3_1_simulation`);
3. `_5 = &raw const _1`: re-borrows already-promoted `_1` reusing `lm31AllocId1`
   without reserving a new allocation (`m₃.machine.memory.nextAllocId = 3`, via
   `step_rawPtr_addrOf_indirect_lm3_1_simulation`);
4. `_1 = const 77_u64`: overwrites promoted `_1` directly via
   `step_direct_write_promoted_lm3_1_simulation`, disabling `_1`'s borrows (`e₁`, `e₃`)
   while leaving `_2`'s borrow `e₂` active;
5. `_0 = copy *_4`: reads `99_u64` from `_2`'s `lm31AllocId2` into `_0` in both
   machines via `step_deref_read_simulation_explicit`. -/
theorem wit_lm3_1_two_promotions_reborrow_and_direct_write_real_steps :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState),
      let b := lm31TwoPromotionsBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
      let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 lm31AllocId2
      let e₃ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 3 lm31AllocId1
      let map₄ := updateAllocMapOnWrite [e₃, e₂, e₁] 1 none
      stepMirFn b lm31TwoPromotionsAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31TwoPromotionsMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [e₁] ∧
      m₁.machine.memory.nextAllocId = 2 ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [e₂, e₁] ∧
      m₂.machine.memory.nextAllocId = 3 ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [e₃, e₂, e₁] ∧
      m₃.machine.memory.nextAllocId = 3 ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ map₄ ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ (derefReadNextAllocMap s₄.frame.locals map₄ 4) ∧
      get? s₅.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) ∧
      (∀ tf₅, m₅.stack.frames = #[tf₅] →
        (tf₅.locals[0]?).map Miri.Interpreter.LocalState.value =
          some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99))))) := by
  let b := lm31TwoPromotionsBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 2, offsetBytes := 0 } 8
  let ptr3 := Value.ptr { allocId := 3, offsetBytes := 0 } 8
  let e₁ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
  let e₂ := rawPtrAllocMapEntry b.localDecls b.layouts .mut 2 2 lm31AllocId2
  let e₃ := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 3 lm31AllocId1
  have himm₀ : ∀ tf, lm31TwoPromotionsMiriPre.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 3 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf =>
      ⟨lm31TwoPromotions_all_immediate_pre tf htf 3, lm31TwoPromotions_all_immediate_pre tf htf 1⟩
  -- Step 1: `_3 = &raw mut _1`
  let s₁ := mkWitState b 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .uninit, .uninit]
    [e₁.toBorrowEntry] 2
  have hs₁ : stepMirFn b lm31TwoPromotionsAnnealPre = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation lm31TwoPromotions_stateRel_pre hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
  have htag₀ : lm31TwoPromotionsAnnealPre.memory.nextTag = 1 := rfl
  have hid₀ : (⟨lm31TwoPromotionsMiriPre.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨⟨hsupply₁, hnext₁, hsrc₁⟩, himm₁_step⟩ :=
    step_rawPtr_addrOf_preserves_supply lm31TwoPromotions_stateRel_pre.toLM3_1
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
  have hnext₁_eq : m₁.machine.memory.nextAllocId = 2 := hnext₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (lm31TwoPromotions_all_immediate_pre _ rfl k)
  -- Step 2: `_4 = &raw mut _2`
  let s₂ := mkWitState b 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2, .uninit]
    [e₂.toBorrowEntry, e₁.toBorrowEntry] 3
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  have himm₁_pair : ∀ tf₁, m₁.stack.frames = #[tf₁] →
      IsImmediateFrameLocal tf₁ 4 ∧ IsImmediateFrameLocal tf₁ 2 :=
    fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 4 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_lm3_1_simulation hrel₁ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁) hs₂
  have htag₁ : s₁.memory.nextTag = 2 := rfl
  have hid₁ : (⟨m₁.machine.memory.nextAllocId, hsupply₁.nonzero⟩ : Miri.Memory.AllocId) =
      lm31AllocId2 := by
    generalize hsupply₁.nonzero = nz
    revert nz
    rw [hnext₁_eq]
    intro _
    rfl
  rw [htag₁, hid₁] at hrel₂
  obtain ⟨⟨_, hnext₂, _⟩, himm₂_step⟩ :=
    step_rawPtr_addrOf_preserves_supply hrel₁ rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₁_pair hsupply₁
      (by rw [hnext₁_eq]; decide)
      (by rw [hsrc₁]; intro h; cases h) hm₂
  have hnext₂_eq : m₂.machine.memory.nextAllocId = 3 := by rw [hnext₂, hnext₁_eq]; rfl
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hk₁ hk₂
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k hk₂ (himm₁ tf₁ htf₁ k hk₁)
  -- Step 3: `_5 = &raw const _1` (re-borrow of already-promoted `_1`)
  let s₃ := mkWitState b 3
    [.uninit, .init (.scalar ⟨42, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2, .init ptr3]
    [e₃.toBorrowEntry, e₂.toBorrowEntry, e₁.toBorrowEntry] 4
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_indirect_lm3_1_simulation hrel₂ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 5 (by decide) (by decide))
      (.tail _ (.head _)) rfl) hs₃
  obtain ⟨hmach₃, himm₃_step⟩ := step_rawPtr_addrOf_indirect_preserves hrel₂ rfl rfl rfl rfl
    (by decide) (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 5 (by decide) (by decide))
    (.tail _ (.head _)) rfl hm₃
  have hnext₃_eq : m₃.machine.memory.nextAllocId = 3 := by
    rw [congrArg (fun mc => mc.memory.nextAllocId) hmach₃, hnext₂_eq]
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hk₁ hk₂
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hk₁ hk₂)
  -- Step 4: `_1 = const 77_u64` (direct scalar write to promoted `_1`)
  let map₄ := updateAllocMapOnWrite [e₃, e₂, e₁] 1 none
  let s₄ := mkWitState b 4
    [.uninit, .init (.scalar ⟨77, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr1, .init ptr2, .init ptr3]
    (map₄.map AllocMapEntry.toBorrowEntry) 4
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_direct_write_promoted_lm3_1_simulation hrel₃ hphase rfl rfl
      (dstDecl := u64Decl) (valTy := u64Ty) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf₃ _ => constU64_wellTyped b tf₃ 77 (by decide))
      ⟨e₃, .head _, rfl⟩) hs₄
  obtain ⟨_, himm₄_step⟩ := step_assign_use_preserves hrel₃ (by rintro _ ⟨⟩) rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] →
      ∀ k, k ≠ 1 → k ≠ 2 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hk₁ hk₂
    obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hk₁ hk₂)
  -- Step 5: `_0 = copy *_4` (explicit-`allocMap'` dereference read of `_2`)
  let s₅ := mkWitState b 5
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨77, 8⟩), .init (.scalar ⟨99, 8⟩),
      .init ptr1, .init ptr2, .init ptr3]
    (map₄.map AllocMapEntry.toBorrowEntry) 4
  have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
  obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step
    (step_deref_read_simulation_explicit hrel₄ hphase (Or.inl rfl) rfl rfl
      rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      (fun tf₄ htf₄ =>
        ⟨himm₄ tf₄ htf₄ 0 (by decide) (by decide), himm₄ tf₄ htf₄ 4 (by decide) (by decide)⟩)
      (fun ptrVal hp e he htag _ => by
        have hp' : ptrVal = { allocId := 2, offsetBytes := 0 } := ptrVal_of_some_init hp
        subst hp'
        rcases List.mem_cons.mp he with rfl | he'
        · cases htag
        · rcases List.mem_cons.mp he' with rfl | he''
          · refine ⟨rfl, by rintro ⟨⟩, fun decl hdecl => ?_⟩
            have h2 : get? b.localDecls 2 = some u64Decl := rfl
            rw [show (e₂.updateOnWrite 1 none).localIdx = 2 from rfl, h2] at hdecl
            injection hdecl with hd; subst hd; rfl
          · rcases List.mem_cons.mp he'' with rfl | hnil
            · cases htag
            · cases hnil)) hs₅
  obtain ⟨_, himm₅_step⟩ := step_assign_use_preserves hrel₄ (by rintro _ ⟨⟩) rfl rfl hm₅
  have himm₅_0 : ∀ tf₅, m₅.stack.frames = #[tf₅] → IsImmediateFrameLocal tf₅ 0 := by
    intro tf₅ htf₅
    obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
    exact himm₅_step tf₄ tf₅ htf₄ htf₅ 0 (himm₄ tf₄ htf₄ 0 (by decide) (by decide))
  have hret99 : ∀ tf₅, m₅.stack.frames = #[tf₅] →
      (tf₅.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar99)))) := by
    intro tf₅ htf₅
    obtain ⟨tf₅', htf₅', _, _, hfr₅, _, _, _, _, _, _, _⟩ := id hrel₅
    rw [htf₅'] at htf₅; injection htf₅ with htf_eq; injection htf_eq with htf_eq'; subst htf_eq'
    obtain ⟨slot₀, mls₀, _, _, hslot₀, hmls₀, _, hloc₀⟩ :=
      hfr₅.lookup_local (idx := 0) (decl := u64Decl) rfl
    have hs₀_eq : slot₀ = .init (.scalar ⟨99, 8⟩) := by
      have h0 : get? s₅.frame.locals 0 = some (.init (.scalar ⟨99, 8⟩)) := rfl
      rw [h0] at hslot₀; exact Option.some.inj hslot₀.symm
    subst hs₀_eq
    rw [hmls₀]
    cases hloc₀ with
    | base hb =>
      cases hb with
      | indirect _ mp _ _ _ _ => exact absurd rfl (himm₅_0 tf₅' htf₅' _ hmls₀ mp)
      | immediate _ imm _ _ hv =>
        rcases hv with ⟨h, _⟩ | ⟨v, hv_eq, himmRel⟩
        · cases h
        · injection hv_eq with hveq; subst hveq
          cases himmRel with
          | scalar _ msc hsc _ _ _ =>
            have hmsc : msc = lm31Scalar99 := scalarInt_eq_of_scalarRel hsc lm31_scalarRel99
            subst hmsc; rfl
  exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅,
    hs₁, hm₁, hrel₁, hnext₁_eq,
    hs₂, hm₂, hrel₂, hnext₂_eq,
    hs₃, hm₃, hrel₃, hnext₃_eq,
    hs₄, hm₄, hrel₄,
    hs₅, hm₅, hrel₅, rfl, hret99⟩

/-- `bool`, `u8`, `*const bool`, and `isize` types and declarations for real-step
divergence witnesses. -/
def boolTyLM31 : Ty := { kind := .bool, layoutIdx := 0 }
def u8TyLM31 : Ty := { kind := .uint .u8, layoutIdx := 0 }
def rawPtrConstBoolTy : Ty := { kind := .rawPtr .not .bool, layoutIdx := 0 }
def isizeTyLM31 : Ty := { kind := .int .isize, layoutIdx := 0 }

def boolDeclLM31 : LocalDecl := { mutability := .mut, ty := boolTyLM31, debugName := none }
def u8DeclLM31 : LocalDecl := { mutability := .mut, ty := u8TyLM31, debugName := none }
def rawPtrConstBoolDecl : LocalDecl :=
  { mutability := .mut, ty := rawPtrConstBoolTy, debugName := none }

/-- `2_u8` as a 1-byte `lean-miri` scalar. -/
def lm31Scalar2U8 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt8 2

theorem lm31_scalarRel2U8 : ScalarRel ⟨2, 1⟩ lm31Scalar2U8 :=
  ⟨Or.inl rfl, by decide, rfl, rfl⟩

/-- `Runtime(PostCleanup)` MIR body casting `&raw const _1` (`_1 = 2_u8`) to
`*const bool` and dereferencing `*_3`:
```text
bb0: _2 = &raw const _1;
     _3 = copy _2 as *const bool (PtrToPtr);
     _0 = copy *_3;
     return
``` -/
def lm31InvalidBoolDerefBody : CapturedMir where
  defPath := "lm_3_1_witness::invalid_bool_cast_deref"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDeclLM31, u8DeclLM31, rawPtrConstU8Decl, rawPtrConstBoolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstBoolTy)),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

def lm31InvalidBoolAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨2, 1⟩), .uninit, .uninit] }
    memory := (initMachineState lm31InvalidBoolDerefBody []).memory }

def lm31InvalidBoolMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm31InvalidBoolDerefBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy boolTyLM31) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar2U8))),
        layout := some (translateTy u8TyLM31) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def lm31InvalidBoolMiriPre : AnnealStepState :=
  { stack := ⟨#[lm31InvalidBoolMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem lm31InvalidBool_stateRel_pre :
    StateRel lm31InvalidBoolDerefBody lm31InvalidBoolAnnealPre lm31InvalidBoolMiriPre := by
  refine StateRel.mk lm31InvalidBoolMiriFramePre rfl rfl ⟨translateTy boolTyLM31, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [lm31InvalidBoolAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm31InvalidBoolMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u8DeclLM31 := by simpa [lm31InvalidBoolDerefBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨2, 1⟩) := by
      simpa [lm31InvalidBoolAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar2U8))),
          layout := some (translateTy u8TyLM31) } := by
      simpa [lm31InvalidBoolMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u8TyLM31)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel2U8 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | _ + 4 => simp [lm31InvalidBoolDerefBody, get?] at hdecl

private theorem lm31InvalidBool_all_immediate_pre :
    ∀ tf, lm31InvalidBoolMiriPre.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 =>
    simp [lm31InvalidBoolMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 4 => simp [lm31InvalidBoolMiriFramePre] at hmls

/-- **`wit_lm3_1_invalid_bool_cast_deref_real_steps`**:
End-to-end 3-step execution of `lm31InvalidBoolDerefBody` from pointer-free
`StateRel` states (`_1 = 2_u8`):
1. `_2 = &raw const _1` promotes `_1` into `lm31AllocId1` in lockstep;
2. `_3 = copy _2 as *const bool` casts the pointer in lockstep via
   `step_cast_ptrToPtr_simulation`;
3. `_0 = copy *_3` diverges (`step_deref_invalid_bool_divergence`): Anneal's
   `stepMirFn` steps storing `.init (.scalar ⟨2, 1⟩)` in `_0 : bool`, whereas
   `lean-miri`'s `Miri.Interpreter.Step.step` (`annealStepHooks`) rejects the
   invalid `bool` bit pattern with `StepError.undefinedBehavior "reading invalid value"`. -/
theorem wit_lm3_1_invalid_bool_cast_deref_real_steps :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := lm31InvalidBoolDerefBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      stepMirFn b lm31InvalidBoolAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31InvalidBoolMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨2, 1⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "reading invalid value")) := by
  let b := lm31InvalidBoolDerefBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, lm31InvalidBoolMiriPre.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf =>
      ⟨lm31InvalidBool_all_immediate_pre tf htf 2, lm31InvalidBool_all_immediate_pre tf htf 1⟩
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨2, 1⟩), .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn b lm31InvalidBoolAnnealPre = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation lm31InvalidBool_stateRel_pre hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
  have htag₀ : lm31InvalidBoolAnnealPre.memory.nextTag = 1 := rfl
  have hid₀ : (⟨lm31InvalidBoolMiriPre.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne lm31InvalidBool_stateRel_pre
    rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide)
    himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (lm31InvalidBool_all_immediate_pre _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨2, 1⟩), .init ptr0, .init ptr0] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨⟨s₃, hs₃, hget₃⟩, m₃, hm₃⟩ := step_deref_invalid_bool_divergence hrel₂ hphase rfl rfl
    (dstDecl := boolDeclLM31) (ptrDecl := rawPtrConstBoolDecl) (tgtDecl := u8DeclLM31)
    rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide))
    (ptrVal := { allocId := 1, offsetBytes := 0 })
    rfl rfl (.head _) rfl (by rintro ⟨⟩) rfl (Or.inl rfl) rfl (by decide) (by rintro ⟨⟩)
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hget₃, hm₃⟩

/-- Constant `-1_isize` (`2^64 - 1` in two's complement 64-bit bits). -/
def constNegOneIsizeLM31 : ConstOperand :=
  { ty := isizeTyLM31, val := .scalar (.int ⟨2 ^ 64 - 1, 8⟩) }

private theorem constNegOneIsize_wellTyped (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit) :
    WellTypedScalarOperand body tf (.constant constNegOneIsizeLM31) isizeTyLM31 :=
  .constScalar constNegOneIsizeLM31 ⟨2 ^ 64 - 1, 8⟩ rfl
    (Or.inr (Or.inr (Or.inl ⟨.isize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
    (fun h => nomatch h) (fun h => nomatch h)

/-- `Runtime(PostCleanup)` MIR body offsetting a `*const u64` pointer by `1_usize`
(exercising `sizeof::<u64>() = 8` stride scaling vs. Anneal's unscaled `+ 1`). -/
def lm31StrideOffsetRealBody : CapturedMir where
  defPath := "lm_3_1_witness::stride_offset_real"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl, u64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.binaryOp .offset (.copy (local_ 2)) (.constant (constUsizeLM31 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body offsetting a `*const u8` pointer forward by
`2_usize` and then backward by `-1_isize` (exercising signed two's-complement
backward `ptrOffsetInbounds` vs. Anneal's unsigned `2 + (2^64 - 1)`). -/
def lm31NegIsizeOffsetRealBody : CapturedMir where
  defPath := "lm_3_1_witness::neg_isize_offset_real"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrConstU8Decl, rawPtrConstU8Decl,
    rawPtrConstU8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstU8Ty)),
        mkStmt (.assign (local_ 4)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 2)))),
        mkStmt (.assign (local_ 5)
          (.binaryOp .offset (.copy (local_ 4)) (.constant constNegOneIsizeLM31)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_offset_stride_and_neg_isize_real_steps`**:
Real-step (`Miri.Interpreter.Step.step` under `annealStepHooks` vs. `stepMirFn`)
witnesses from pointer-free `StateRel` states exercising BOTH `BinOp.Offset`
pointer-arithmetic divergences:
1. **Non-byte stride (`*const u64` + `1_usize`)**: after `_2 = &raw const _1` on
   `_1 : u64`, `_3 = Offset(copy _2, const 1_usize)` stores `offsetBytes = 1` in
   Anneal (`s₂`), whereas `lean-miri` scales by `sizeof::<u64>() = 8` and stores
   the one-past-end pointer `annealStackBaseAddr lm31AllocId1 + 8` (`m₂`).
2. **Signed negative `isize` (`-1_isize`)**: after `&raw const _1` ->
   `as *const u8` -> `Offset(_, 2_usize)` in lockstep (`offsetBytes = 2`),
   `_5 = Offset(copy _4, const (-1_isize))` stores `offsetBytes = 2 + (2^64 - 1)`
   in Anneal (`s₄`), whereas `lean-miri` sign-extends `-1_isize` and steps
   backward in-bounds to `annealStackBaseAddr lm31AllocId1 + 1` (`m₄`). -/
theorem wit_lm3_1_offset_stride_and_neg_isize_real_steps :
    -- (1) `*const u64` + `1_usize` stride divergence (`1` vs. `+ 8`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31StrideOffsetRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + 8),
              .concrete lm31AllocId1 borTag⟩))))) ∧
    -- (2) `*const u8` at offset `2` + `(-1_isize)` signed delta divergence (`2 + (2^64 - 1)` vs. `+ 1`)
    (∃ (s₃ s₄ : MachineState) (m₃ m₄ : AnnealStepState)
      (tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31NegIsizeOffsetRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₃ m₃
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₃ = .step s₄ ∧
      get? s₄.frame.locals 5 =
        some (.init (.ptr { allocId := 1, offsetBytes := 2 + (2 ^ 64 - 1) } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      m₄.stack.frames = #[tf₄] ∧
      (tf₄.locals[5]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + 1),
              .concrete lm31AllocId1 borTag⟩))))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  refine ⟨?_, ?_⟩
  · -- Part (1): `lm31StrideOffsetRealBody`
    let b := lm31StrideOffsetRealBody
    have hrel₀ : StateRel b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) :=
      mkSixLocal_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        u64Decl u64Decl rfl rfl
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, (mkSixLocalMiriPre b u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalAnnealPre b).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalMiriPre b u64Ty).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    obtain ⟨hs₂, m₂, tf₂, borTag, hm₂, htf₂, hval₂⟩ :=
      step_binOp_offset_stride_divergence hrel₁ hphase rfl rfl
        (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl rfl
        (fun tf₁ _ => constUsize_wellTyped b tf₁ 1 (by decide))
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 })
        rfl rfl rfl (by rintro ⟨⟩) (.head _) rfl rfl rfl (by rintro ⟨⟩)
    exact ⟨s₁, _, m₁, m₂, tf₂, borTag, hs₁, hm₁, hrel₁, hs₂, rfl, hm₂, htf₂, hval₂⟩
  · -- Part (2): `lm31NegIsizeOffsetRealBody`
    let b := lm31NegIsizeOffsetRealBody
    have hrel₀ : StateRel b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) :=
      mkSixLocal_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU8Decl
        rawPtrConstU8Decl rawPtrConstU8Decl rfl rfl
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, (mkSixLocalMiriPre b u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalAnnealPre b).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalMiriPre b u64Ty).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    let s₂ := mkWitState b 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    let s₃ := mkWitState b 3
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
      (step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
        (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
        (fun tf₂ _ => constUsize_wellTyped b tf₂ 2 (by decide))
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
    obtain ⟨hs₄, m₄, tf₄, borTag, hm₄, htf₄, hval₄⟩ :=
      step_binOp_offset_neg_isize_divergence hrel₃ hphase rfl rfl
        (dstDecl := rawPtrConstU8Decl) (ptrDecl := rawPtrConstU8Decl) (tgtDecl := u64Decl)
        (rhsTy := isizeTyLM31) rfl rfl rfl rfl rfl
        (fun tf₃ _ => constNegOneIsize_wellTyped b tf₃)
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 2 })
        rfl rfl (by rintro ⟨⟩) (.head _) rfl rfl (by rintro ⟨⟩) (by decide) (by decide)
    exact ⟨s₃, _, m₃, m₄, tf₄, borTag, hrel₃, rfl, rfl, hs₄, rfl, hm₄, htf₄, hval₄⟩

/-! ## 7. Complete Return, `&raw (*_p)`, Forged Provenance &
Validity/PlaceMention Witnesses -/

/-- **`wit_lm3_1_end_to_end_return_real_steps`**:
Complete 6-step execution of `lm31AddrOfBody` from initial pointer-free
`StateRel` through `&raw mut _1`, `*_2 = 99_u64`, `_0 = copy *_2`,
`StorageDead(_2)`, `StorageDead(_1)` (freeing `lm31AllocId1`), and
`TerminatorKind.return_` (`step_terminator_goto_return_lm3_1_simulation`),
popping `lean-miri`'s root frame (`{ m₅ with stack := ⟨#[]⟩ }`) in lockstep with
Anneal's `MirStepNode.retNormal (.scalar ⟨99, 8⟩) s₅.memory` and reading back
`lm31Scalar99` via `annealControlHooks.returnOperand`. -/
theorem wit_lm3_1_end_to_end_return_real_steps :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (allocMap₂ allocMap₃ : List AllocMapEntry),
      let hooks := annealStepHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts
      stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31AddrOfMiriPre = (m₁, .ok true) ∧
      stepMirFn lm31AddrOfBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₂ m₂ allocMap₂ ∧
      stepMirFn lm31AddrOfBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn lm31AddrOfBody s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      stepMirFn lm31AddrOfBody s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₅ m₅ allocMap₃ ∧
      m₅.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none ∧
      stepMirFn lm31AddrOfBody s₅ = .retNormal (.scalar ⟨99, 8⟩) s₅.memory ∧
      Miri.Interpreter.Step.step hooks () m₅ = ({ m₅ with stack := ⟨#[]⟩ }, .ok true) ∧
      Miri.Interpreter.Step.step hooks () { m₅ with stack := ⟨#[]⟩ } =
        ({ m₅ with stack := ⟨#[]⟩ }, .ok false) ∧
      annealControlHooks.returnOperand () m₅ =
        (m₅, .ok (.immediate (.scalar (.fromScalarInt lm31Scalar99)))) := by
  obtain ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, allocMap₂, allocMap₃,
    hs₁, hm₁, _, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, _, hret99₃,
    hs₄, hm₄, hrel₄, hs₅, hm₅, hrel₅, hdealloc⟩ :=
    wit_lm3_1_addrOf_deref_storageDead_real_steps
  have hphase : ∀ p, lm31AddrOfBody.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let borMut := [rawPtrBorrowEntry lm31AddrOfBody.localDecls lm31AddrOfBody.layouts .mut 1 1]
  let s₁_v := mkWitState lm31AddrOfBody 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0] borMut 2
  let s₂_v := mkWitState lm31AddrOfBody 5 [.uninit, .init (.scalar ⟨99, 8⟩), .init ptr0] borMut 2
  let s₃_v := mkWitState lm31AddrOfBody 6
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩), .init ptr0] borMut 2
  let s₄_v := mkWitState lm31AddrOfBody 7
    [.init (.scalar ⟨99, 8⟩), .init (.scalar ⟨99, 8⟩), .dead] borMut 2
  let s₅_v := mkWitState lm31AddrOfBody 8 [.init (.scalar ⟨99, 8⟩), .dead, .dead] borMut 2
  have hs₁_def : s₁ = s₁_v := by
    have h : stepMirFn lm31AddrOfBody lm31AddrOfAnnealPre = .step s₁_v := rfl
    rw [h] at hs₁; injection hs₁ with ht; injection ht with heq; exact heq.symm
  subst hs₁_def
  have hs₂_def : s₂ = s₂_v := by
    have h : stepMirFn lm31AddrOfBody s₁_v = .step s₂_v := rfl
    rw [h] at hs₂; injection hs₂ with ht; injection ht with heq; exact heq.symm
  subst hs₂_def
  have hs₃_def : s₃ = s₃_v := by
    have h : stepMirFn lm31AddrOfBody s₂_v = .step s₃_v := rfl
    rw [h] at hs₃; injection hs₃ with ht; injection ht with heq; exact heq.symm
  subst hs₃_def
  have hs₄_def : s₄ = s₄_v := by
    have h : stepMirFn lm31AddrOfBody s₃_v = .step s₄_v := rfl
    rw [h] at hs₄; injection hs₄ with ht; injection ht with heq; exact heq.symm
  subst hs₄_def
  have hs₅_def : s₅ = s₅_v := by
    have h : stepMirFn lm31AddrOfBody s₄_v = .step s₅_v := rfl
    rw [h] at hs₅; injection hs₅ with ht; injection ht with heq; exact heq.symm
  subst hs₅_def
  have himm₃_0 : ∀ tf₃, m₃.stack.frames = #[tf₃] → IsImmediateFrameLocal tf₃ 0 := by
    intro tf₃ htf₃ mls hmls mp hmp
    have hr := hret99₃ tf₃ htf₃
    rw [hmls] at hr; simp only [Option.map, Option.some.injEq] at hr
    rw [hr] at hmp; cases hmp
  obtain ⟨_, himm₄_step⟩ := step_storageDead_preserves hrel₃ rfl rfl
    (decl := rawPtrMutU64Decl) rfl (by decide) hm₄
  have himm₄_0 : ∀ tf₄, m₄.stack.frames = #[tf₄] → IsImmediateFrameLocal tf₄ 0 := by
    intro tf₄ htf₄; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ 0 (himm₃_0 tf₃ htf₃)
  obtain ⟨_, himm₅_step⟩ := step_storageDead_preserves hrel₄ rfl rfl
    (decl := u64Decl) rfl (by decide) hm₅
  have himm₅_0 : ∀ tf₅, m₅.stack.frames = #[tf₅] → IsImmediateFrameLocal tf₅ 0 := by
    intro tf₅ htf₅; obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
    exact himm₅_step tf₄ tf₅ htf₄ htf₅ 0 (himm₄_0 tf₄ htf₄)
  have hsim₆ := step_terminator_goto_return_lm3_1_simulation hrel₅ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, u64Decl, rfl, (by rintro _ _ ⟨⟩), (by decide), himm₅_0⟩))
  have ha₆ : stepMirFn lm31AddrOfBody s₅_v = .retNormal (.scalar ⟨99, 8⟩) s₅_v.memory := rfl
  rw [ha₆] at hsim₆
  generalize hm_res : Miri.Interpreter.Step.step
      (annealStepHooks lm31AddrOfBody.localDecls lm31AddrOfBody.layouts) () m₅ = mRes at hsim₆
  cases hsim₆ with
  | retRoot decl₀ _ imm₀ _ m' hdecl₀ hop₀ himmRel₀ hm₆ =>
    subst hm₆
    have hd₀ : decl₀ = u64Decl := Option.some.inj hdecl₀.symm
    subst hd₀
    cases himmRel₀ with
    | scalar _ msc hsc _ _ _ =>
      have hmsc : msc = lm31Scalar99 := scalarInt_eq_of_scalarRel hsc lm31_scalarRel99
      subst hmsc
      exact ⟨_, _, _, _, _, m₁, m₂, m₃, m₄, m₅, allocMap₂, allocMap₃,
        hs₁, hm₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hs₄, hm₄, hs₅, hm₅, hrel₅,
        hdealloc, ha₆, hm_res, rfl, hop₀⟩

/-- Parameterized 4-local Anneal pre-state (`_1` initialized to scalar `sc`,
locals `0, 2, 3` `.uninit`). -/
def mkFourLocalScalarAnnealPre (body : CapturedMir) (sc : MirAst.ScalarInt) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar sc), .uninit, .uninit] }
    memory := (initMachineState body []).memory }

/-- Parameterized 4-local `lean-miri` root frame matching
`mkFourLocalScalarAnnealPre`. -/
def mkFourLocalScalarMiriFramePre (body : CapturedMir) (retTy local1Ty : Ty)
    (msc : Miri.Memory.ScalarInt) :
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
      { value := .live (.immediate (.scalar (.fromScalarInt msc))),
        layout := some (translateTy local1Ty) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- Parameterized 4-local `lean-miri` step state matching
`mkFourLocalScalarAnnealPre`. -/
def mkFourLocalScalarMiriPre (body : CapturedMir) (retTy local1Ty : Ty)
    (msc : Miri.Memory.ScalarInt) : AnnealStepState :=
  { stack := ⟨#[mkFourLocalScalarMiriFramePre body retTy local1Ty msc]⟩
    machine := AnnealMachine.empty }

private theorem mkFourLocalScalar_all_immediate (body : CapturedMir) (retTy local1Ty : Ty)
    (msc : Miri.Memory.ScalarInt) :
    ∀ tf, (mkFourLocalScalarMiriPre body retTy local1Ty msc).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 =>
    simp [mkFourLocalScalarMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 4 => simp [mkFourLocalScalarMiriFramePre] at hmls

private theorem mkFourLocalScalar_stateRel
    (body : CapturedMir) (retTy : Ty) (d₀ d₁ d₂ d₃ : LocalDecl)
    (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
    (hdecls : body.localDecls = [d₀, d₁, d₂, d₃])
    (hlay : body.layouts = emptyLayoutTable)
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy d₁.ty emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes)
    (hnot_bool : d₁.ty.kind ≠ .bool)
    (hnot_char : d₁.ty.kind ≠ .char) :
    StateRel body (mkFourLocalScalarAnnealPre body sc)
      (mkFourLocalScalarMiriPre body retTy d₁.ty msc) := by
  refine StateRel.mk (mkFourLocalScalarMiriFramePre body retTy d₁.ty msc) rfl rfl
    ⟨translateTy retTy, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, by simp [mkFourLocalScalarAnnealPre, hdecls],
    by simp [mkFourLocalScalarMiriFramePre, hdecls], ?_⟩
  intro i decl slot mls hdecl hslot hmls
  rw [hdecls] at hdecl
  match i with
  | 0 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [mkFourLocalScalarAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkFourLocalScalarMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = d₁ := by simpa [get?] using hdecl.symm
    have hs : slot = .init (.scalar sc) := by
      simpa [mkFourLocalScalarAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt msc))),
          layout := some (translateTy d₁.ty) } := by
      simpa [mkFourLocalScalarMiriFramePre] using hmls.symm
    subst hs hm
    rw [hd, hlay]
    exact .immediate _ _ (some (translateTy d₁.ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ hrel hsz
        (fun h => absurd h hnot_bool) (fun h => absurd h hnot_char)⟩)
  | _ + 4 => simp [get?] at hdecl

/-- `0_u64` (`0 as *const u64` null address) as a `lean-miri` scalar. -/
def lm31Scalar0U64 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 0

theorem lm31_scalarRel0U64 : ScalarRel ⟨0, 8⟩ lm31Scalar0U64 :=
  ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩

/-- `Runtime(PostCleanup)` MIR body executing `_2 = &raw const (*_1)` where `_1`
holds null (`0 as *const u64`). -/
def lm31RawPtrDerefNullBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_deref_null"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl, u64Decl]
  basicBlocks := [
    { statements := [mkStmt (.assign (local_ 2) (.rawPtr .not (derefLocal 1)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `_2 = &raw mut _1`,
`_3 = copy _2 as *mut u8`, `_4 = Offset(copy _3, 1_usize)`, and
`_5 = &raw const (*_4)` (place-to-pointer reborrow at byte offset `1`). -/
def lm31RawPtrDerefOffsetBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_deref_offset"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU8Decl,
    rawPtrMutU8Decl, rawPtrConstU8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 4)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 5) (.rawPtr .not (derefLocal 4)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_rawPtr_deref_null_and_offset_real_steps`**:
Concrete real-step witnesses exercising BOTH RFC 2582 `&raw (const|mut) (*_p)`
place-to-pointer divergences:

1. **Null place-to-pointer (`&raw const (*ptr::null::<u64>())`)**: on a
   `StateRelLM3_1` state where `_1 : *const u64` holds `Value.scalar ⟨0, 8⟩`,
   `_2 = &raw const (*_1)` falsely raises `MirStepNode.fail .ub` in Anneal while
   `lean-miri` steps normally storing `lm31Scalar0U64` (`0`) in `_2`
   (`step_rawPtr_deref_null_divergence`).
2. **Non-zero byte offset reset (`&raw const (*_4)` at `offsetBytes = 1`)**:
   after `_2 = &raw mut _1` -> `_3 = copy _2 as *mut u8` ->
   `_4 = Offset(copy _3, 1_usize)` in lockstep (`offsetBytes = 1`),
   `_5 = &raw const (*_4)` resets `_5` to `offsetBytes = 0` in Anneal (`s₄`),
   whereas `lean-miri` preserves `annealStackBaseAddr lm31AllocId1 + 1` (`m₄`,
   `step_rawPtr_deref_nonzero_offset_divergence`). -/
theorem wit_lm3_1_rawPtr_deref_null_and_offset_real_steps :
    -- (1) `&raw const (*_1)` on null `0 as *const u64`
    (∃ (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31RawPtrDerefNullBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (2) `&raw const (*_4)` at `offsetBytes = 1`
    (∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
      (tf₄ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31RawPtrDerefOffsetBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₃ m₃
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1] ∧
      s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 2, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      m₄.stack.frames = #[tf₄] ∧
      (tf₄.locals[5]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + 1),
              .concrete lm31AllocId1 borTag⟩))))) := by
  refine ⟨?_, ?_⟩
  · -- Part (1): `lm31RawPtrDerefNullBody`
    let b := lm31RawPtrDerefNullBody
    have hrel₀ : StateRelLM3_1 b (mkFourLocalScalarAnnealPre b ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    obtain ⟨ha_ub, m₁, tf₁, msc_ref, hm₁, htf₁, hrel_ref, hval₁⟩ :=
      step_rawPtr_deref_null_divergence hrel₀ hphase rfl rfl
        (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (by rintro ⟨⟩) rfl
    have hmsc_eq : msc_ref = lm31Scalar0U64 :=
      scalarInt_eq_of_scalarRel hrel_ref lm31_scalarRel0U64
    subst hmsc_eq
    exact ⟨m₁, tf₁, hrel₀, ha_ub, hm₁, htf₁, hval₁⟩
  · -- Part (2): `lm31RawPtrDerefOffsetBody`
    let b := lm31RawPtrDerefOffsetBody
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr1 := Value.ptr { allocId := 1, offsetBytes := 1 } 8
    have hrel₀ : StateRel b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) :=
      mkSixLocal_stateRel b u64Ty u64Decl rawPtrMutU64Decl rawPtrMutU8Decl
        rawPtrMutU8Decl rawPtrConstU8Decl rfl rfl
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, (mkSixLocalMiriPre b u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalAnnealPre b).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalMiriPre b u64Ty).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    let s₂ := mkWitState b 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    let s₃ := mkWitState b 3
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr1, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
      (step_binOp_offset_simulation hrel₂ hphase rfl rfl rfl rfl rfl rfl
        (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
        (fun tf₂ _ => constUsize_wellTyped b tf₂ 1 (by decide))
        (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
        (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
          have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
          have hsc' : sc = ⟨1, 8⟩ := by
            change evalOperand s₂.frame.locals (.constant (constUsizeLM31 1)) _ _ _ _ = _ at hsc
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
    obtain ⟨⟨s₄, hs₄, hget₄⟩, m₄, tf₄, borTag, hm₄, htf₄, hval₄⟩ :=
      step_rawPtr_deref_nonzero_offset_divergence hrel₃ hphase rfl rfl
        (dstDecl := rawPtrConstU8Decl) (ptrDecl := rawPtrMutU8Decl)
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩)))
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
        (by rintro ⟨⟩) (ptrVal := { allocId := 1, offsetBytes := 1 }) rfl
        (.head _) rfl rfl
    exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, tf₄, borTag,
      hrel₃, rfl, rfl, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hget₄, hm₄, htf₄, hval₄⟩

/-- Mutable `usize` local declaration. -/
def usizeDeclLM31 : LocalDecl := { mutability := .mut, ty := usizeTyLM31, debugName := none }

/-- `Runtime(PostCleanup)` MIR body taking `_2 = &raw const _1` (WITHOUT ever
exposing `_2`), forging tag `1` via `_4 = const 65536_usize as *const u64`
(`PointerWithExposedProvenance`), and reading `_0 = copy *_4` in Anneal:
```text
bb0: _2 = &raw const _1;
     _4 = const 65536_usize as *const u64 (PointerWithExposedProvenance);
     _0 = copy *_4;
     return
``` -/
def lm31ForgedProvenanceBody : CapturedMir where
  defPath := "lm_3_1_witness::forged_provenance"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, usizeDeclLM31,
    rawPtrConstU64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 4)
          (.cast .pointerWithExposedProvenance (.constant (constUsizeLM31 65536))
            rawPtrConstU64Ty)),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 4))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body taking `_2 = &raw const _1` and executing
`_3 = copy _2 as usize` (`PointerExposeProvenance`). -/
def lm31ExposeProvenanceBody : CapturedMir where
  defPath := "lm_3_1_witness::expose_provenance"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, usizeDeclLM31, u64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.cast .pointerExposeProvenance (.copy (local_ 2)) usizeTyLM31))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_anneal_forged_provenance_real_steps`**:
Concrete real-step witnesses exercising BOTH pointer-integer exposure casts:

1. **Forged provenance (`PointerWithExposedProvenance`,
   `lm31ForgedProvenanceBody`)**:
   after `_2 = &raw const _1` (`_1 = 42_u64`, tag `1`, NEVER exposing `_2`),
   `_4 = const 65536_usize as *const u64` diverges
   (`step_cast_with_exposed_provenance_divergence`): `lean-miri` fails closed
   with `.error (.unsupported "pointerFromExposedAddress in cast")`, whereas
   Anneal fabricates `{ allocId := 1, offsetBytes := 0 }` in `_4` and then steps
   `_0 = copy *_4` to read `42_u64` out of unexposed `_1`!
2. **Pointer exposure (`PointerExposeProvenance`, `lm31ExposeProvenanceBody`)**:
   after `_2 = &raw const _1` in lockstep, `_3 = copy _2 as usize` stores
   `⟨65536, 8⟩` in Anneal while `lean-miri` fails closed with
   `.error (.unsupported "exposeProvenance in cast")`
   (`step_cast_expose_provenance_ptr_unsupported`). -/
theorem wit_lm3_1_anneal_forged_provenance_real_steps :
    -- (1) `PointerWithExposedProvenance` forges tag `1` and reads `42_u64`
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm31ForgedProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.unsupported "pointerFromExposedAddress in cast")) ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨42, 8⟩))) ∧
    -- (2) `PointerExposeProvenance`: `65536` in Anneal vs. `.unsupported`
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm31ExposeProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.scalar ⟨65536, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.unsupported "exposeProvenance in cast"))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  refine ⟨?_, ?_⟩
  · -- Part (1): `lm31ForgedProvenanceBody`
    let b := lm31ForgedProvenanceBody
    have hrel₀ : StateRel b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) :=
      mkSixLocal_stateRel b u64Ty u64Decl rawPtrConstU64Decl usizeDeclLM31
        rawPtrConstU64Decl u64Decl rfl rfl
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, (mkSixLocalMiriPre b u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalAnnealPre b).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalMiriPre b u64Ty).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨⟨s₂, hs₂, hget₂⟩, m₂, hm₂⟩ :=
      step_cast_with_exposed_provenance_divergence hrel₁ hphase rfl rfl
        (dstDecl := rawPtrConstU64Decl) rfl rfl rfl rfl rfl rfl (by decide) (by rintro ⟨⟩)
    let s₂_def := mkWitState b 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .init ptr0, .uninit] bor 2
    have hs₂_eq : s₂ = s₂_def := by
      have h : stepMirFn b s₁ = .step s₂_def := rfl
      rw [h] at hs₂; injection hs₂ with ht; injection ht with heq; exact heq.symm
    subst hs₂_eq
    let s₃ := mkWitState b 3
      [.init (.scalar ⟨42, 8⟩), .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .init ptr0, .uninit]
      bor 2
    have hs₃ : stepMirFn b s₂_def = .step s₃ := rfl
    exact ⟨s₁, s₂_def, s₃, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hget₂, hm₂, hs₃, rfl⟩
  · -- Part (2): `lm31ExposeProvenanceBody`
    let b := lm31ExposeProvenanceBody
    have hrel₀ : StateRel b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) :=
      mkSixLocal_stateRel b u64Ty u64Decl rawPtrConstU64Decl usizeDeclLM31
        u64Decl u64Decl rfl rfl
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, (mkSixLocalMiriPre b u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalAnnealPre b).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalMiriPre b u64Ty).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    obtain ⟨⟨s₂, hs₂, hget₂⟩, m₂, hm₂⟩ :=
      step_cast_expose_provenance_ptr_unsupported hrel₁ hphase rfl rfl
        (dstDecl := usizeDeclLM31) (srcDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
        (by rintro ⟨⟩) (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl
    exact ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hget₂, hm₂⟩

/-- `char`, `*const char`, `*mut bool`, `*mut u8`, and scalar helpers for
validity and `PlaceMention(*_p)` real-step witnesses. -/
def charTyLM31 : Ty := { kind := .char, layoutIdx := 0 }
def rawPtrConstCharTy : Ty := { kind := .rawPtr .not .char, layoutIdx := 0 }
def rawPtrMutBoolTy : Ty := { kind := .rawPtr .mut .bool, layoutIdx := 0 }

def charDeclLM31 : LocalDecl := { mutability := .mut, ty := charTyLM31, debugName := none }
def rawPtrConstCharDecl : LocalDecl :=
  { mutability := .mut, ty := rawPtrConstCharTy, debugName := none }
def rawPtrMutBoolDecl : LocalDecl :=
  { mutability := .mut, ty := rawPtrMutBoolTy, debugName := none }

/-- UTF-16 surrogate `0xD800_u32` (`55296`), an invalid Rust `char` bit
pattern. -/
def lm31ScalarSurrogateU32 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt32 0xD800

theorem lm31_scalarRelSurrogateU32 : ScalarRel ⟨0xD800, 4⟩ lm31ScalarSurrogateU32 :=
  ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩

/-- `0_u8` as a 1-byte `lean-miri` scalar. -/
def lm31Scalar0U8 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt8 0

theorem lm31_scalarRel0U8 : ScalarRel ⟨0, 1⟩ lm31Scalar0U8 :=
  ⟨Or.inl rfl, by decide, rfl, rfl⟩

/-- Invalid 1-byte `bool` constant with bit pattern `2`. -/
def constInvalidBool2LM31 : ConstOperand :=
  { ty := boolTyLM31, val := .scalar (.int ⟨2, 1⟩) }

/-- `Runtime(PostCleanup)` MIR body casting `&raw const _1` (`_1 = 0xD800_u32`)
to `*const char` and dereferencing `*_3`. -/
def lm31InvalidCharDerefBody : CapturedMir where
  defPath := "lm_3_1_witness::invalid_char_cast_deref"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [charDeclLM31, u32DeclLM31, rawPtrConstU32Decl, rawPtrConstCharDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstCharTy)),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body casting `&raw mut _1` (`_1 = 0_u8`) to
`*mut bool` and writing `*_3 = const (2 : bool)`. -/
def lm31WriteInvalidBoolBody : CapturedMir where
  defPath := "lm_3_1_witness::write_invalid_bool"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u8DeclLM31, u8DeclLM31, rawPtrMutU8Decl, rawPtrMutBoolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutBoolTy)),
        mkStmt (.assign (derefLocal 3) (.use (.constant constInvalidBool2LM31)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `PlaceMention(*_1)` on
`_1 : *const u64` (initialized to null `0 as *const u64`), followed by
`PlaceMention(*_2)` on an uninitialized `_2 : *const u64`. -/
def lm31PlaceMentionDerefBody : CapturedMir where
  defPath := "lm_3_1_witness::place_mention_deref"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.placeMention (derefLocal 1)),
        mkStmt (.placeMention (derefLocal 2))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_invalid_char_write_bool_and_placeMention_real_steps`**:
Concrete real-step witnesses exercising invalid-`char` dereference read UB,
invalid-`bool` dereference write UB, and `PlaceMention(*_p)` correspondence vs.
`.uninit` divergence:

1. **Invalid `char` surrogate read (`0xD800_u32 as *const char`)**: after
   `_2 = &raw const _1` and `_3 = copy _2 as *const char` in lockstep,
   `_0 = copy *_3` stores `⟨0xD800, 4⟩` in Anneal while `lean-miri` rejects it
   with `StepError.undefinedBehavior "reading invalid value"`
   (`step_deref_invalid_char_divergence`).
2. **Invalid `bool` dereference write (`*_3 = const (2 : bool)`)**: after
   `_2 = &raw mut _1` and `_3 = copy _2 as *mut bool` in lockstep,
   `*_3 = const (2 : bool)` writes `⟨2, 1⟩` into `_1` in Anneal while
   `lean-miri` rejects it with `StepError.undefinedBehavior "writing invalid value"`
   (`step_deref_write_invalid_bool_divergence`).
3. **`PlaceMention(*_p)` lockstep on null vs. `.uninit` divergence**: on
   `lm31PlaceMentionDerefBody`, Step 1 (`PlaceMention(*_1)` on null
   `0 as *const u64`) steps in lockstep to `StateRelLM3_1`-related states
   (`step_placeMention_deref_lm3_1_simulation`), and Step 2 (`PlaceMention(*_2)`
   on `.uninit` `_2`) diverges (`step_placeMention_deref_uninit_divergence`):
   Anneal steps without reading `_2`, whereas `lean-miri` raises
   `StepError.undefinedBehavior "read of uninitialized local"`. -/
theorem wit_lm3_1_invalid_char_write_bool_and_placeMention_real_steps :
    -- (1) Invalid `char` surrogate read (`0xD800_u32`)
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := lm31InvalidCharDerefBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0xD800, 4⟩
      let m₀ := mkFourLocalScalarMiriPre b charTyLM31 u32TyLM31 lm31ScalarSurrogateU32
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 0 = some (.init (.scalar ⟨0xD800, 4⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "reading invalid value"))) ∧
    -- (2) Invalid `bool` dereference write (`2`)
    (∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := lm31WriteInvalidBoolBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 1⟩
      let m₀ := mkFourLocalScalarMiriPre b u8TyLM31 u8TyLM31 lm31Scalar0U8
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1] ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 1 = some (.init (.scalar ⟨2, 1⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "writing invalid value"))) ∧
    -- (3) `PlaceMention(*_1)` lockstep -> `PlaceMention(*_2)` divergence
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm31PlaceMentionDerefBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.undefinedBehavior "read of uninitialized local"))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  refine ⟨?_, ?_, ?_⟩
  · -- Part (1): `lm31InvalidCharDerefBody`
    let b := lm31InvalidCharDerefBody
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨0xD800, 4⟩)
        (mkFourLocalScalarMiriPre b charTyLM31 u32TyLM31 lm31ScalarSurrogateU32) :=
      mkFourLocalScalar_stateRel b charTyLM31 charDeclLM31 u32DeclLM31
        rawPtrConstU32Decl rawPtrConstCharDecl ⟨0xD800, 4⟩ lm31ScalarSurrogateU32
        rfl rfl lm31_scalarRelSurrogateU32 rfl (by rintro ⟨⟩) (by rintro ⟨⟩)
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf,
        (mkFourLocalScalarMiriPre b charTyLM31 u32TyLM31 lm31ScalarSurrogateU32).stack.frames =
          #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf =>
        ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
         mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0xD800, 4⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨0xD800, 4⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨0xD800, 4⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b charTyLM31 u32TyLM31
        lm31ScalarSurrogateU32).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨0xD800, 4⟩), .init ptr0, .init ptr0] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨⟨s₃, hs₃, hget₃⟩, m₃, hm₃⟩ := step_deref_invalid_char_divergence hrel₂ hphase rfl rfl
      (dstDecl := charDeclLM31) (ptrDecl := rawPtrConstCharDecl) (tgtDecl := u32DeclLM31)
      rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 0 })
      rfl rfl (.head _) rfl (by rintro ⟨⟩) rfl (Or.inl rfl) rfl (by decide) (by rintro ⟨⟩)
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, hs₃, hget₃, hm₃⟩
  · -- Part (2): `lm31WriteInvalidBoolBody`
    let b := lm31WriteInvalidBoolBody
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨0, 1⟩)
        (mkFourLocalScalarMiriPre b u8TyLM31 u8TyLM31 lm31Scalar0U8) :=
      mkFourLocalScalar_stateRel b u8TyLM31 u8DeclLM31 u8DeclLM31
        rawPtrMutU8Decl rawPtrMutBoolDecl ⟨0, 1⟩ lm31Scalar0U8
        rfl rfl lm31_scalarRel0U8 rfl (by rintro ⟨⟩) (by rintro ⟨⟩)
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf,
        (mkFourLocalScalarMiriPre b u8TyLM31 u8TyLM31 lm31Scalar0U8).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf =>
        ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
         mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0, 1⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨0, 1⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨0, 1⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b u8TyLM31 u8TyLM31
        lm31Scalar0U8).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨0, 1⟩), .init ptr0, .init ptr0] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨⟨s₃, hs₃, hget₃⟩, m₃, hm₃⟩ := step_deref_write_invalid_bool_divergence hrel₂ hphase
      rfl rfl (ptrDecl := rawPtrMutBoolDecl) (tgtDecl := u8DeclLM31)
      rfl rfl rfl rfl (by decide) (by decide)
      (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 0 })
      rfl rfl (.head _) rfl (Or.inl rfl) rfl (Or.inr (Or.inl rfl)) (by rintro ⟨⟩)
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, hs₃, hget₃, hm₃⟩
  · -- Part (3): `lm31PlaceMentionDerefBody`
    let b := lm31PlaceMentionDerefBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0, 8⟩), .uninit, .uninit] [] 1
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_placeMention_deref_lm3_1_simulation hrel₀ hphase rfl rfl
        (ptrDecl := rawPtrConstU64Decl) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf htf => mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1)
        (by rintro ⟨⟩)) hs₁
    obtain ⟨_, himm₁_step⟩ := step_placeMention_preserves hrel₀ rfl rfl hm₁
    have himm₁_2 : ∀ tf₁, m₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 2 := by
      intro tf₁ htf₁
      exact himm₁_step _ tf₁ rfl htf₁ 2 (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl 2)
    obtain ⟨hs₂, m₂, hm₂⟩ := step_placeMention_deref_uninit_divergence hrel₁ hphase rfl rfl
      (ptrDecl := rawPtrConstU64Decl) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      himm₁_2 rfl
    exact ⟨s₁, _, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

end LeanMiriSpec.Correspondence.Witness
