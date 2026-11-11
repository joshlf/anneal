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
   (undefined behavior in both machines).
4. **`wit_lm3_1_anneal_offset_deref_simulation`** and
   **`wit_lm3_1_deref_oob_and_misaligned_real_steps`**: real-step witnesses
   chained from pointer-free `StateRel` states showing that BOTH Anneal's
   `stepMirFn` (`MirStepNode.fail .ub`) and `Miri.Interpreter.Step.step`
   (`annealStepHooks`) reject a one-past-end dereference (`offset = 8` on an
   8-byte allocation, `step_deref_oob_simulation`) and an in-bounds misaligned
   `u32` dereference (`offset = 2` on an 8-byte allocation,
   `step_deref_misaligned_simulation`).
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
   validity UB in both machines, and non-byte stride (`*const u64` + `1_usize`)
   and signed negative `isize` (`-1_isize`) `BinOp.Offset` real-step lockstep
   (`+ 8` and `+ 1` in both machines).
7. **`wit_lm3_1_end_to_end_return_real_steps`**,
   **`wit_lm3_1_rawPtr_deref_null_and_offset_real_steps`**,
   **`wit_lm3_1_anneal_forged_provenance_real_steps`**, and
   **`wit_lm3_1_invalid_char_write_bool_and_placeMention_real_steps`**: full
   6-step execution of `lm31AddrOfBody` through `TerminatorKind.return_`
   popping `lean-miri`'s root frame with `99_u64`; RFC 2582 `&raw const (*_p)`
   correspondences on null (`0 as *const u64`) and non-zero offset (`+ 1`);
   `PointerExposeProvenance` and unexposed `PointerWithExposedProvenance`
   (`65536_usize as *const u64`) fail-closed divergences (Anneal no longer
   forges provenance, so `*_4` faults); and invalid `char` surrogate read
   (`0xD800_u32`), invalid `bool` dereference write (`2`), and
   `PlaceMention(*_p)` on null and `.uninit` pointers in lockstep.
8. **`wit_lm3_1_rawPtr_use_move_and_expose_scalar_real_steps`**,
   **`wit_lm3_1_null_ptrToPtr_and_offset_correspondences_real_steps`**, and
   **`wit_lm3_1_rawPtr_deref_zero_and_perm_correspondence_real_steps`**: 6-step
   move/copy raw-pointer chain (`&raw mut _1` -> `_3 = copy _2` ->
   `_4 = move _2 as *mut u8` -> `_5 = Offset(move _4, 8_usize)` ->
   `_2 = move _3` -> UB on `copy *_3` of moved-from `_3`) plus lockstep
   `PointerExposeProvenance` on provenance-less `.copy` (`0`) and `.move`
   (`42`); provenance-less `PtrToPtr` and `BinOp.Offset` (`0_usize`:
   corresponding results; `1_usize`: UB in both machines); and RFC 2582
   `&raw mut (*_2)` zero-offset and frozen-parent correspondences.
9. **`wit_lm3_1_branch_offset_zero_and_return_rawPtr_real_steps`**,
   **`wit_lm3_1_rawPtr_cmp_and_ptrMetadata_real_steps`**, and
   **`wit_lm3_1_cmp_symm_move_ub_and_unified_step_real_steps`**: multi-block
   execution from pointer-free `StateRel` through `&raw mut _1`, `*_2 = 99_u64`,
   `_0 = Offset(move _2, 0_usize)` on `*mut u64` (`stride = 8`), `Assert`,
   `SwitchInt` (`MirObs.event 1`), and root-frame `Return` of `_0 : *mut u64`
   (`PtrRel` return correspondence); provenance-less vs. tracked raw-pointer
   `Eq` comparison (`(.ptr, .ptr)` and symmetric `(.scalar, .ptr)`: both
   machines step, results unrelated), use-after-move pointer comparison UB
   (`Eq(move _2, copy _2)` via `step_rawPtr_cmp_ub_lm3_1_simulation` and unified
   `step_mir_lm3_1_state_simulation`), move-operand provenance-less `PtrToPtr`
   and `Offset` (`0_usize`: corresponding results; `1_usize`: UB in both
   machines), and `UnOp.PtrMetadata` UB (`.uninit` pointer) vs. thin-pointer
   correspondence.
10. **`wit_lm3_1_deref_write_oob_real_steps`**,
    **`wit_lm3_1_storage_revive_read_ub_real_steps`**,
    **`wit_lm3_1_deref_type_pun_offset4_and_write_real_steps`**,
    **`wit_lm3_1_deref_read_narrower_partial_oob_real_steps`**,
    **`wit_lm3_1_deref_write_misaligned_real_steps`**,
    **`wit_lm3_1_deref_write_invalid_char_real_steps`**,
    **`wit_lm3_1_raw_overwritten_bool_and_char_real_steps`**,
    **`wit_lm3_1_deref_read_narrower_invalid_char_real_steps`**,
    **`wit_lm3_1_binOp_offset_neg_stride_and_oob_real_steps`**,
    **`wit_lm3_1_binOp_offset_usize_wrap_divergence_real_steps`**,
    **`wit_lm3_1_deref_write_invalid_bool_offset5_and_usize_oob_real_steps`**,
    **`wit_lm3_1_composed_step_mir_deref_ub_real_steps`**,
    **`wit_lm3_1_binOp_offset_disabled_live_real_steps`**, and
    **`wit_lm3_1_raw_subbyte_write_and_composed_oob_misaligned_real_steps`**: real-step
    witnesses for the generalized `D1`..`D6` theorems (out-of-bounds and
    misaligned dereference writes, stale reads after `StorageDead` +
    `StorageLive` revival, narrower / type-punned reads and writes at byte
    offsets `0` and `4`, partial-overlap and invalid-`char` narrower reads,
    invalid `bool` write at odd byte offset `5` of `u64`, invalid `char` writes,
    full-width and sub-byte `move` raw `u8`/`u32` overwrites of `bool`/`char`
    locals, non-byte negative `isize` strides, negative `isize` and
    `usize ≥ 2^63` OOB underflow UB, and end-to-end composed
    `step_mir_lm3_1_state_simulation` UB traces across invalid `bool`/`char`,
    partial-overlap OOB write, and `AllocId`-free misaligned read/write), the
    unsigned `usize` wrap-around `Offset` divergence (Anneal steps backward,
    `lean-miri` raises `"PointerArithOverflow"`), and the disabled-tag `Offset`
    boundary (after a direct write disables a live raw-pointer tag, `+1_usize`
    and `-1_isize` offsets fault in Anneal while `lean-miri` steps and
    `usize::MAX` is UB in both; after `StorageDead`, a zero-count offset of the
    dangling pointer at `offsetBytes = 8` faults in Anneal while `lean-miri`
    steps).
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
8-byte read at offset `8`. On the Stage-1 repaired semantics Anneal's `Offset`
checks allocation bounds and its typed stack-pointer dereference checks
`offsetBytes`, so both machines reject these accesses; see
`wit_lm3_1_anneal_offset_deref_simulation`,
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

/-! ## 3b. Agreement: Both Machines Reject a Dereference of a Pointer Offset Past Its Local -/

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

/-! ## 3c. Agreement: Both Machines Reject a Stale-Pointer Access to a Revived Local -/

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

/-- Machine-level invariant preserved by `RvalueM` evaluation: `addresses` is
unchanged and `AllocIdSupplyReady` (together with `nextAllocId` and
`sourceAllocIdWorldActive`) is preserved across any in-place live-allocation
write-backs. -/
structure MachineAddrSupplyEq (mc' mc : AnnealMachine) : Prop where
  addresses_eq : mc'.addresses = mc.addresses
  supply_pres :
    AllocIdSupplyReady mc.memory →
      AllocIdSupplyReady mc'.memory ∧
        mc'.memory.nextAllocId = mc.memory.nextAllocId ∧
        mc'.memory.sourceAllocIdWorldActive = mc.memory.sourceAllocIdWorldActive

theorem MachineAddrSupplyEq.refl (mc : AnnealMachine) : MachineAddrSupplyEq mc mc :=
  ⟨rfl, fun h => ⟨h, rfl, rfl⟩⟩

theorem MachineAddrSupplyEq.trans {a b c : AnnealMachine}
    (h1 : MachineAddrSupplyEq a b) (h2 : MachineAddrSupplyEq b c) :
    MachineAddrSupplyEq a c :=
  ⟨h1.addresses_eq.trans h2.addresses_eq, fun hs =>
    let ⟨hs1, hn1, hw1⟩ := h2.supply_pres hs
    let ⟨hs2, hn2, hw2⟩ := h1.supply_pres hs1
    ⟨hs2, hn2.trans hn1, hw2.trans hw1⟩⟩

/-- `RvalueM` actions that preserve `MachineAddrSupplyEq`, singleton-stack structure,
`location`, and `IsImmediateFrameLocal` for every local `k`. -/
def RvaluePreservesAllImm {α : Type}
    (act : Miri.Interpreter.RvalueM AnnealStepState α) : Prop :=
  ∀ m a m', act m = .ok a m' →
    MachineAddrSupplyEq m'.machine m.machine ∧
    ∀ tf, m.stack.frames = #[tf] →
      ∃ tf', m'.stack.frames = #[tf'] ∧
        tf'.location = tf.location ∧
        ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k

private theorem rvaluePreservesAllImm_pure {α : Type} (x : α) :
    RvaluePreservesAllImm (pure x) := by
  intro m a m' h
  cases h
  exact ⟨.refl _, fun tf htf => ⟨tf, htf, rfl, fun _ hk => hk⟩⟩

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
      m'.machine = m.machine ∧ m'.stack = m.stack) :
    RvaluePreservesAllImm act := by
  intro m a m' h
  obtain ⟨hmc, hs⟩ := heq m a m' h
  exact ⟨hmc ▸ .refl _, fun tf htf => ⟨tf, (congrArg Miri.Interpreter.Stack.frames hs).trans htf,
    rfl, fun _ hk => hk⟩⟩

private theorem annealReadImmediate_eq {op : Miri.Interpreter.OpTy AnnealProv}
    {m m' : AnnealStepState} {a : Miri.Interpreter.RvalueImmTy AnnealProv}
    (h : annealReadImmediate op m = .ok a m') :
    m'.machine = m.machine ∧ m'.stack = m.stack := by
  rcases op with ⟨opv, lay⟩
  unfold annealReadImmediate at h
  cases opv with
  | immediate imm =>
    cases imm <;> (
      dsimp only [pure, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw,
        EStateM.throw] at h
      cases h <;> exact ⟨rfl, rfl⟩)
  | indirect mp =>
    cases hf : lay.layout.fields with
    | Array stride count =>
      rw [hf] at h
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        pure, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
      cases hp : mp.ptr.provenance.bind Miri.Memory.Provenance.getAllocId with
      | none => rw [hp] at h; cases h
      | some allocId =>
        rw [hp] at h; dsimp only [] at h
        cases hb : m.machine.lookupBaseAddr allocId with
        | none => rw [hb] at h; cases h
        | some baseAddr =>
          rw [hb] at h; dsimp only [] at h
          cases hl : m.machine.memory.live.find? (fun (k, _) => k == allocId) with
          | none => rw [hl] at h; cases h
          | some entry =>
            rcases entry with ⟨_, localAlloc⟩
            rw [hl] at h; dsimp only [] at h
            by_cases hty : (lay.ty == arraySliceMetaTyId) = true
            · simp only [hty, ↓reduceIte] at h
              cases hi : localAlloc.allocation.initializationMask.isRangeInitialized
                  (Miri.Memory.allocRange (Miri.ABI.Size.ofBytes (mp.ptr.offset.bytes - baseAddr))
                    lay.layout.size) with
              | error _ => rw [hi] at h; cases h
              | ok res =>
                cases res with
                | error _ => rw [hi] at h; cases h
                | ok u =>
                  cases u
                  rw [hi] at h; dsimp only [] at h
                  cases hc : (Miri.Memory.ScalarInt.tryFromUInt (BitVec.ofNat 128 count.toNat)
                      (Miri.ABI.Size.ofBytes 8)).toOption.join with
                  | none => rw [hc] at h; cases h
                  | some countSc =>
                    rw [hc] at h; dsimp only [] at h
                    cases hpr : mp.ptr.provenance with
                    | none => rw [hpr] at h; cases h
                    | some prov =>
                      rw [hpr] at h; cases h; exact ⟨rfl, rfl⟩
            · simp only [Bool.eq_false_iff.mpr hty, Bool.false_eq_true, ↓reduceIte] at h
              cases h
    | _ =>
      rw [hf] at h
      dsimp only [] at h
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

private theorem annealDerefSafeRefToMemPlace_preserves
    (ld : List LocalDecl) (ly : LayoutTable)
    (loc : Miri.MIR.LocalId) (op : Miri.Interpreter.Operand AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm (annealDerefSafeRefToMemPlace ld ly loc op lay) := by
  unfold annealDerefSafeRefToMemPlace
  cases lookupRefDerefPointeeLayout ld ly loc with
  | none => exact rvaluePreservesAllImm_throw _
  | some pointeeLay =>
    dsimp only []
    refine rvaluePreservesAllImm_bind (annealReadImmediate_preserves _) (fun ptrImm => ?_)
    apply rvaluePreservesAllImm_of_eq
    intro m a m' h
    dsimp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get] at h
    cases hc : annealSafeRefDerefCheck m.machine ptrImm.imm pointeeLay with
    | ok mp =>
      rw [hc] at h
      cases h
      exact ⟨rfl, rfl⟩
    | error e =>
      rw [hc] at h
      cases h

private theorem annealDerefOperandToMemPlace_preserves
    (ld : List LocalDecl) (ly : LayoutTable)
    (loc : Miri.MIR.LocalId) (op : Miri.Interpreter.Operand AnnealProv)
    (lay : Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm (annealDerefOperandToMemPlace ld ly loc op lay) := by
  unfold annealDerefOperandToMemPlace
  cases lookupDerefPointeeLayout ld ly loc lay with
  | none => exact annealDerefSafeRefToMemPlace_preserves ld ly loc op lay
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
  intro m a m' h
  unfold annealWriteMemoryPlace at h
  dsimp only [] at h
  cases hs : Miri.Memory.sizeAsI64 lay.layout.size with
  | error _ => rw [hs] at h; cases h
  | ok signedSize =>
    rw [hs] at h; dsimp only [] at h
    cases hc : Miri.Memory.checkAndDerefPtr annealPointerArithmetic mp.ptr signedSize
        .memoryAccess (annealResolvePtrWrapping m.machine) (annealLookupAlloc m.machine) with
    | error _ => rw [hc] at h; cases h
    | ok checked =>
      rw [hc] at h; dsimp only [] at h
      cases checked with
      | none =>
        cases hm : mp.misaligned with
        | some _ => rw [hm] at h; cases h
        | none =>
          rw [hm] at h
          cases val with
          | uninit =>
            cases h
            exact ⟨.refl _, fun tf htf => ⟨tf, htf, rfl, fun _ hk => hk⟩⟩
          | scalar _ | scalarPair _ _ => cases h
      | some access =>
        dsimp only [] at h
        split at h
        · cases h
        · cases hm : mp.misaligned with
          | some _ => rw [hm] at h; cases h
          | none =>
            rw [hm] at h; dsimp only [] at h
            cases hf : m.machine.memory.live.find? (fun entry => entry.1 == access.pointer.allocId) with
            | none => rw [hf] at h; cases h
            | some row =>
              rcases row with ⟨rk, localAlloc⟩
              have hbeq := Array.find?_some hf
              have hrk : rk = access.pointer.allocId := beq_iff_eq.mp hbeq
              subst rk
              rw [hf] at h; dsimp only [] at h
              cases val with
              | uninit =>
                dsimp only [] at h
                cases hw : Miri.Memory.Allocation.writeUninit
                    (Miri.Memory.allocRange access.pointer.offset lay.layout.size)
                    (Miri.ABI.Size.ofBytes 8) localAlloc.allocation with
                | error _ _ => rw [hw] at h; cases h
                | ok u alloc' =>
                  cases u; rw [hw] at h; dsimp only [] at h
                  cases hset : m.machine.memory.setLiveAllocation access.pointer.allocId alloc' with
                  | error _ => rw [hset] at h; cases h
                  | ok nextMem =>
                    rw [hset] at h; cases h
                    exact ⟨⟨rfl, fun hsup => hsup.of_setLiveAllocation hf hset⟩,
                      fun tf htf => ⟨tf, htf, rfl, fun _ hk => hk⟩⟩
              | scalar sc =>
                dsimp only [] at h
                split at h; · cases h
                split at h; · cases h
                cases hw : Miri.Memory.Allocation.writeScalar annealTargetDataLayout
                    (Miri.Memory.allocRange access.pointer.offset lay.layout.size) sc
                    localAlloc.allocation with
                | error e _ => rw [hw] at h; cases e <;> cases h
                | ok u alloc' =>
                  cases u; rw [hw] at h; dsimp only [] at h
                  cases hset : m.machine.memory.setLiveAllocation access.pointer.allocId alloc' with
                  | error _ => rw [hset] at h; cases h
                  | ok nextMem =>
                    rw [hset] at h; cases h
                    exact ⟨⟨rfl, fun hsup => hsup.of_setLiveAllocation hf hset⟩,
                      fun tf htf => ⟨tf, htf, rfl, fun _ hk => hk⟩⟩
              | scalarPair _ _ => cases h

private theorem annealPointerBinary_preserves
    (ly : LayoutTable) (bop : Miri.MIR.BinOp)
    (lv rv : Miri.Interpreter.RvalueImmTy AnnealProv) :
    RvaluePreservesAllImm (annealPointerBinary ly bop lv rv) := by
  apply rvaluePreservesAllImm_of_eq
  intro m a m' h
  unfold annealPointerBinary at h
  cases bop with
  | Eq | Ne | Lt | Le | Gt | Ge =>
    rcases lv with ⟨limm, llay⟩
    rcases rv with ⟨rimm, rlay⟩
    dsimp only [Miri.Interpreter.ExecutionScalar.pointerBinary, annealExecutionScalarLeaves,
      bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    split at h
    · cases limm with
      | uninit => cases h
      | scalar la =>
        dsimp only [] at h
        cases hla : la.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) with
        | error _ => rw [hla] at h; with_unfolding_all cases h
        | ok _ =>
          rw [hla] at h
          cases rimm with
          | uninit => with_unfolding_all cases h
          | scalar ra =>
            dsimp only [] at h
            cases hra : ra.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
              rw [hra] at h <;> with_unfolding_all (cases h <;> exact ⟨rfl, rfl⟩)
          | scalarPair ra rb =>
            dsimp only [] at h
            cases hra : ra.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
              cases hrb : rb.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
              rw [hra, hrb] at h <;> with_unfolding_all (cases h <;> exact ⟨rfl, rfl⟩)
      | scalarPair la lb =>
        dsimp only [] at h
        cases hla : la.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
          cases hlb : lb.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
          rw [hla, hlb] at h
        · with_unfolding_all cases h
        · with_unfolding_all cases h
        · with_unfolding_all cases h
        · cases rimm with
          | uninit => with_unfolding_all cases h
          | scalar ra =>
            dsimp only [] at h
            cases hra : ra.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
              rw [hra] at h <;> with_unfolding_all (cases h <;> exact ⟨rfl, rfl⟩)
          | scalarPair ra rb =>
            dsimp only [] at h
            cases hra : ra.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
              cases hrb : rb.toBits (Miri.ABI.Size.fromBits annealTargetDataLayout.pointerWidth.bits) <;>
              rw [hra, hrb] at h <;> with_unfolding_all (cases h <;> exact ⟨rfl, rfl⟩)
    · cases h
  | _ =>
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
                cases h <;> exact .refl _
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
              cases h <;> exact .refl _
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

private theorem annealEvalPlace_fallback_inner_preserves
    (ly : LayoutTable) (localId : Miri.MIR.LocalId)
    (projs : List Miri.MIR.ProjectionElem)
    (fl : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit ×
      Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm
      (match fl.1.getLocalOperand localId with
      | .error (.localExpectedLive _) =>
          throw (.undefinedBehavior "projected write to dead local")
      | .error e =>
          throw (.stack e)
      | .ok (.immediate .uninit) =>
          throw (.undefinedBehavior "projected write to uninitialized local")
      | .ok (.immediate _) =>
          throw (.unsupported "projected destination place on immediate local")
      | .ok (.indirect mp) => do
          let st ← get
          match annealCheckIndirectInitialized st.machine mp fl.2.layout.size with
          | .error err => throw err
          | .ok () =>
              match annealProjectList (annealProjectionCx fl.1 ly st.machine)
                  ⟨.indirect mp, fl.2⟩ projs with
              | .ok ⟨.indirect elemMp, elemLayout⟩ =>
                  pure (⟨.memory elemMp, elemLayout⟩ : Miri.Interpreter.RuntimePlace AnnealProv)
              | .ok ⟨.immediate _, _⟩ =>
                  throw (.unsupported "projected place resolved to immediate")
              | .error projErr =>
                  throw (annealLiftProjectionError projErr)) := by
  cases fl.1.getLocalOperand localId with
  | error e => cases e <;> exact rvaluePreservesAllImm_throw _
  | ok lop =>
    cases lop with
    | immediate imm => cases imm <;> exact rvaluePreservesAllImm_throw _
    | indirect mp =>
      apply rvaluePreservesAllImm_of_eq
      intro st _ st' h'
      dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
        pure, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h'
      cases hc : annealCheckIndirectInitialized st.machine mp fl.2.layout.size with
      | error _ => rw [hc] at h'; cases h'
      | ok u =>
        cases u
        rw [hc] at h'
        dsimp only [EStateM.bind, EStateM.get, EStateM.pure, EStateM.throw] at h'
        cases hp : annealProjectList (annealProjectionCx fl.1 ly st.machine)
            ⟨.indirect mp, fl.2⟩ projs with
        | error _ => rw [hp] at h'; cases h'
        | ok opTy =>
          rcases opTy with ⟨opv, elay⟩
          cases opv with
          | immediate _ => rw [hp] at h'; cases h'
          | indirect _ => rw [hp] at h'; cases h'; exact ⟨rfl, rfl⟩

private theorem annealEvalOperand_proj_tail_eq
    (frame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable)
    (operand : Miri.Interpreter.Operand AnnealProv)
    (layout : Miri.Interpreter.LocalLayout)
    (projs : List Miri.MIR.ProjectionElem)
    {m m' : AnnealStepState} {a : Miri.Interpreter.OpTy AnnealProv}
    (h : ((match operand with
      | .immediate .uninit =>
          throw (Miri.Interpreter.StepError.undefinedBehavior "projected read of uninitialized local")
      | .indirect mp => do
          let st ← get
          match annealCheckIndirectInitialized st.machine mp layout.layout.size with
          | .error err => throw err
          | .ok () =>
              match annealProjectList
                  (annealProjectionCx frame' layouts st.machine)
                  ⟨.indirect mp, layout⟩ projs with
              | .ok projected => pure projected
              | .error projErr => throw (annealLiftProjectionError projErr)
      | _ => throw (Miri.Interpreter.StepError.unsupported "projected operand in scalar rvalue")) :
        Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv))
      m = .ok a m') :
    m' = m := by
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    pure, Pure.pure, EStateM.pure, throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  cases operand with
  | immediate imm =>
    cases imm <;> cases h
  | indirect mp =>
    dsimp only [EStateM.bind, EStateM.get, EStateM.pure, EStateM.throw] at h
    cases hc : annealCheckIndirectInitialized m.machine mp layout.layout.size with
    | error _ => rw [hc] at h; cases h
    | ok u =>
      cases u
      rw [hc] at h
      dsimp only [EStateM.bind, EStateM.get, EStateM.pure, EStateM.throw] at h
      cases hp : annealProjectList (annealProjectionCx frame' layouts m.machine)
          ⟨.indirect mp, layout⟩ projs with
      | error _ => rw [hp] at h; cases h
      | ok _ => rw [hp] at h; cases h; rfl

private theorem annealEvalOperand_proj_tail_preserves
    (frame' : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (layouts : LayoutTable)
    (operand : Miri.Interpreter.Operand AnnealProv)
    (layout : Miri.Interpreter.LocalLayout)
    (projs : List Miri.MIR.ProjectionElem) :
    RvaluePreservesAllImm
      (match operand with
      | .immediate .uninit =>
          throw (Miri.Interpreter.StepError.undefinedBehavior "projected read of uninitialized local")
      | .indirect mp => do
          let st ← get
          match annealCheckIndirectInitialized st.machine mp layout.layout.size with
          | .error err => throw err
          | .ok () =>
              match annealProjectList
                  (annealProjectionCx frame' layouts st.machine)
                  ⟨.indirect mp, layout⟩ projs with
              | .ok projected => pure projected
              | .error projErr => throw (annealLiftProjectionError projErr)
      | _ => throw (Miri.Interpreter.StepError.unsupported "projected operand in scalar rvalue")) :=
  rvaluePreservesAllImm_of_eq fun _ _ _ h' => by
    cases annealEvalOperand_proj_tail_eq frame' layouts operand layout projs h'
    exact ⟨rfl, rfl⟩

private theorem annealEvalProjection_eq
    (layouts : LayoutTable)
    (base : Miri.Interpreter.OpTy AnnealProv) :
    ∀ (projs : List Miri.MIR.ProjectionElem) {m a m'},
      annealEvalProjection layouts base projs m = .ok a m' → m' = m
  | [], _, _, _, h => by cases h; rfl
  | elem :: rest, m, a, m', h => by
    unfold annealEvalProjection at h
    dsimp only [bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    let hintTy := match elem with | .Field _ ft => some ft | _ => none
    change (match Miri.Interpreter.project (annealStructProjectionCx layouts hintTy) base elem with
      | .ok opTy => (EStateM.pure opTy).bind fun next => annealEvalProjection layouts next rest
      | .error err => (EStateM.throw (annealLiftProjectionError err)).bind fun next =>
          annealEvalProjection layouts next rest) m = .ok a m' at h
    cases hp : Miri.Interpreter.project (annealStructProjectionCx layouts hintTy) base elem with
    | error _ => rw [hp] at h; cases h
    | ok next =>
      rw [hp] at h
      exact annealEvalProjection_eq layouts next rest h

private theorem annealEvalProjection_preserves
    (layouts : LayoutTable)
    (base : Miri.Interpreter.OpTy AnnealProv)
    (projs : List Miri.MIR.ProjectionElem) :
    RvaluePreservesAllImm (annealEvalProjection layouts base projs) :=
  rvaluePreservesAllImm_of_eq fun _ _ _ h' => by
    cases annealEvalProjection_eq layouts base projs h'
    exact ⟨rfl, rfl⟩

private theorem annealEvalProjectedPlace_preserves
    (ld : List LocalDecl) (ly : LayoutTable) (place : Miri.MIR.Place) :
    RvaluePreservesAllImm (annealEvalProjectedPlace ld ly place) := by
  intro m a m' h
  unfold annealEvalProjectedPlace at h
  dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
    EStateM.bind, pure, Pure.pure, EStateM.pure,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
  by_cases hnone : m.stack.currentFrame?.isNone = true
  · simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h; cases h
  · have hnf : m.stack.currentFrame?.isNone = false := Bool.eq_false_iff.mpr hnone
    simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
    refine (rvaluePreservesAllImm_bind
      (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
      (fun fl => ?_)) m a m' h
    cases annealProjectPlaceList ly
        ⟨.local (m.stack.frames.size - 1) place.localId none fl.1.localsIdentity, fl.2⟩
        place.projection.toList with
    | ok p => exact rvaluePreservesAllImm_pure p
    | error err => exact rvaluePreservesAllImm_throw err

private theorem annealEvalPlace_preserves
    (ld : List LocalDecl) (ly : LayoutTable) (place : Miri.MIR.Place) :
    RvaluePreservesAllImm (annealEvalPlace ld ly place) := by
  intro m a m' h
  unfold annealEvalPlace at h
  by_cases hemp : (!place.projection.isEmpty) = true
  · simp only [hemp, ↓reduceIte] at h
    dsimp only [get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind,
      EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    by_cases hnone : m.stack.currentFrame?.isNone = true
    · rcases hlist : place.projection.toList with _ | ⟨p0, ps⟩
      · rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
        simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h; cases h
      · cases p0 with
        | Deref =>
          cases ps <;>
            (rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h;
             simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h; cases h)
        | Field _ _ | Downcast _ _ =>
          rw [hlist] at h
          exact annealEvalProjectedPlace_preserves ld ly place m a m' h
        | _ =>
          rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
          simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h; cases h
    · have hnf : m.stack.currentFrame?.isNone = false := Bool.eq_false_iff.mpr hnone
      rcases hlist : place.projection.toList with _ | ⟨p0, ps⟩
      · rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
        simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
        exact (rvaluePreservesAllImm_bind
          (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
          (annealEvalPlace_fallback_inner_preserves ly place.localId [])) m a m' h
      · cases p0 with
        | Deref =>
          cases ps with
          | nil =>
            rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
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
          | cons p1 ps' =>
            rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
            simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
            exact (rvaluePreservesAllImm_bind
              (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
              (annealEvalPlace_fallback_inner_preserves ly place.localId
                (.Deref :: p1 :: ps'))) m a m' h
        | Field idx ft =>
          rw [hlist] at h
          exact annealEvalProjectedPlace_preserves ld ly place m a m' h
        | Index idx =>
          rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
          simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
          exact (rvaluePreservesAllImm_bind
            (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
            (annealEvalPlace_fallback_inner_preserves ly place.localId (.Index idx :: ps))) m a m' h
        | ConstantIndex offset minLength fromEnd =>
          rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
          simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
          exact (rvaluePreservesAllImm_bind
            (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
            (annealEvalPlace_fallback_inner_preserves ly place.localId
              (.ConstantIndex offset minLength fromEnd :: ps))) m a m' h
        | Subslice fromIdx toIdx fromEnd =>
          rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
          simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
          exact (rvaluePreservesAllImm_bind
            (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
            (annealEvalPlace_fallback_inner_preserves ly place.localId
              (.Subslice fromIdx toIdx fromEnd :: ps))) m a m' h
        | Downcast name v =>
          rw [hlist] at h
          exact annealEvalProjectedPlace_preserves ld ly place m a m' h
        | OpaqueCast ty =>
          rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
          simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
          exact (rvaluePreservesAllImm_bind
            (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
            (annealEvalPlace_fallback_inner_preserves ly place.localId
              (.OpaqueCast ty :: ps))) m a m' h
        | UnwrapUnsafeBinder ty =>
          rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
          simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
          exact (rvaluePreservesAllImm_bind
            (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
            (annealEvalPlace_fallback_inner_preserves ly place.localId
              (.UnwrapUnsafeBinder ty :: ps))) m a m' h
        | PhantomDeref =>
          rw [hlist] at h; dsimp only [EStateM.bind, EStateM.get] at h
          simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
          exact (rvaluePreservesAllImm_bind
            (annealResolveAndCacheLocalLayout_preserves ld ly place.localId none)
            (annealEvalPlace_fallback_inner_preserves ly place.localId
              (.PhantomDeref :: ps))) m a m' h
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
        exact ⟨.refl _, fun tf htf => ⟨tf, htf, rfl, fun _ hk => hk⟩⟩
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
        rcases hlist : place.projection.toList with _ | ⟨p0, ps⟩
        · exact rvaluePreservesAllImm_pure _
        · cases p0 with
          | Deref =>
            cases ps with
            | nil =>
              exact rvaluePreservesAllImm_bind
                (annealDerefOperandToMemPlace_preserves ld ly place.localId operand fl.2)
                (fun _ => rvaluePreservesAllImm_pure _)
            | cons p1 ps' =>
              exact annealEvalOperand_proj_tail_preserves fl.1 ly operand fl.2 (.Deref :: p1 :: ps')
          | Field idx ft =>
            cases ps with
            | nil =>
              cases operand with
              | immediate imm =>
                cases imm with
                | scalarPair _ _ =>
                  by_cases h0 : (idx == 0) = true
                  · simp only [h0, ↓reduceIte]
                    exact rvaluePreservesAllImm_pure _
                  · have h0f : (idx == 0) = false := Bool.eq_false_iff.mpr h0
                    simp only [h0f, Bool.false_eq_true, ↓reduceIte]
                    by_cases h1 : (idx == 1) = true
                    · simp only [h1, ↓reduceIte]
                      exact rvaluePreservesAllImm_pure _
                    · have h1f : (idx == 1) = false := Bool.eq_false_iff.mpr h1
                      simp only [h1f, Bool.false_eq_true, ↓reduceIte]
                      exact annealEvalProjection_preserves ly _ _
                | _ => exact annealEvalProjection_preserves ly _ _
              | indirect _ => exact annealEvalProjection_preserves ly _ _
            | cons p1 ps' =>
              exact annealEvalProjection_preserves ly ⟨operand, fl.2⟩
                (.Field idx ft :: p1 :: ps')
          | Index idx =>
            exact annealEvalOperand_proj_tail_preserves fl.1 ly operand fl.2 (.Index idx :: ps)
          | ConstantIndex offset minLength fromEnd =>
            exact annealEvalOperand_proj_tail_preserves fl.1 ly operand fl.2
              (.ConstantIndex offset minLength fromEnd :: ps)
          | Subslice fromIdx toIdx fromEnd =>
            exact annealEvalOperand_proj_tail_preserves fl.1 ly operand fl.2
              (.Subslice fromIdx toIdx fromEnd :: ps)
          | Downcast name v =>
            exact annealEvalProjection_preserves ly ⟨operand, fl.2⟩
              (.Downcast name v :: ps)
          | OpaqueCast ty =>
            exact annealEvalOperand_proj_tail_preserves fl.1 ly operand fl.2
              (.OpaqueCast ty :: ps)
          | UnwrapUnsafeBinder ty =>
            exact annealEvalOperand_proj_tail_preserves fl.1 ly operand fl.2
              (.UnwrapUnsafeBinder ty :: ps)
          | PhantomDeref =>
            exact annealEvalOperand_proj_tail_preserves fl.1 ly operand fl.2
              (.PhantomDeref :: ps)

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
                  split at h <;> cases h <;> exact .refl _
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
    refine ⟨haddr.addresses_eq, fun tf₀ tf' htf₀ htf' k hk => ?_⟩
    rw [hframes] at htf₀
    injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
    injection htf' with h₁; injection h₁ with h₁'; subst h₁'
    exact himm_ev k hk

theorem step_preserves_supply_of_rvalue
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
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    (AllocIdSupplyReady m'.machine.memory ∧
      m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId ∧
      m'.machine.memory.sourceAllocIdWorldActive = m.machine.memory.sourceAllocIdWorldActive) ∧
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
    refine ⟨haddr.supply_pres hsupply, fun tf₀ tf' htf₀ htf' k hk => ?_⟩
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

private theorem annealResolveAndCacheLocalLayout_ok
    {ld : List LocalDecl} {ly : LayoutTable}
    {loc : Miri.MIR.LocalId} {known : Option Miri.Interpreter.LocalLayout}
    {m m₁ : AnnealStepState}
    {fl : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit ×
      Miri.Interpreter.LocalLayout}
    (h : annealResolveAndCacheLocalLayout ld ly loc known m = .ok fl m₁) :
    MachineAddrSupplyEq m₁.machine m.machine ∧
      ∀ tf, m.stack.frames = #[tf] →
        m₁.stack.frames = #[fl.1] ∧
        fl.1.location = tf.location ∧
        ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal fl.1 k := by
  refine ⟨(annealResolveAndCacheLocalLayout_preserves ld ly loc known m fl m₁ h).1,
    fun tf htf => ?_⟩
  have hcf : m.stack.currentFrame? = some tf :=
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
        | ok fl' =>
          rw [hgor] at h
          rcases fl' with ⟨tf', lay'⟩
          obtain ⟨hloc, himm⟩ := getOrCacheLocalLayout_preserves hgor
          simp only [htf] at h
          cases h
          exact ⟨rfl, hloc, himm⟩
    | some comp =>
      rw [hopt] at h
      dsimp only [EStateM.bind, EStateM.pure] at h
      cases hgor : tf.getOrCacheLocalLayout loc comp with
      | error _ => rw [hgor] at h; cases h
      | ok fl' =>
        rw [hgor] at h
        rcases fl' with ⟨tf', lay'⟩
        obtain ⟨hloc, himm⟩ := getOrCacheLocalLayout_preserves hgor
        simp only [htf] at h
        cases h
        exact ⟨rfl, hloc, himm⟩

private theorem annealEvalOperand_any_preserves
    (ld : List LocalDecl) (ly : LayoutTable)
    (op : Miri.MIR.Operand) (known : Option Miri.Interpreter.LocalLayout) :
    RvaluePreservesAllImm (annealEvalOperand ld ly op known) := by
  cases op with
  | Copy p =>
    exact annealEvalOperand_nonMove_preserves ld ly (.Copy p) known (by rintro _ ⟨⟩)
  | Constant c =>
    exact annealEvalOperand_nonMove_preserves ld ly (.Constant c) known (by rintro _ ⟨⟩)
  | RuntimeChecks r =>
    exact annealEvalOperand_nonMove_preserves ld ly (.RuntimeChecks r) known (by rintro _ ⟨⟩)
  | Move place =>
    intro m a m' h
    unfold annealEvalOperand at h
    dsimp only [get, getThe, MonadStateOf.get, EStateM.get, set, MonadStateOf.set,
      EStateM.set, bind, Bind.bind, EStateM.bind, pure, Pure.pure, EStateM.pure,
      throw, throwThe, MonadExceptOf.throw, EStateM.throw] at h
    by_cases hnone : m.stack.currentFrame?.isNone = true
    · simp only [hnone, ↓reduceIte, EStateM.bind, EStateM.throw] at h
      cases h
    · have hnf : m.stack.currentFrame?.isNone = false := Bool.eq_false_iff.mpr hnone
      simp only [hnf, Bool.false_eq_true, ↓reduceIte] at h
      dsimp only [EStateM.bind] at h
      cases hres : annealResolveAndCacheLocalLayout ld ly place.localId known m with
      | error _ _ => rw [hres] at h; cases h
      | ok fl m₁ =>
        rw [hres] at h
        dsimp only [] at h
        obtain ⟨haddr₁, hstk₁⟩ := annealResolveAndCacheLocalLayout_ok hres
        cases hglo : fl.1.getLocalOperand place.localId with
        | error e =>
          rw [hglo] at h
          cases e <;> (dsimp only [EStateM.bind, EStateM.throw] at h; cases h)
        | ok operand =>
          rw [hglo] at h
          dsimp only [EStateM.bind, EStateM.pure] at h
          have hproj_other : ∀ projs,
              ((match operand with
                | .immediate .uninit =>
                    throw (Miri.Interpreter.StepError.undefinedBehavior "projected read of uninitialized local")
                | .indirect mp => do
                    let st ← get
                    match annealCheckIndirectInitialized st.machine mp fl.2.layout.size with
                    | .error err => throw err
                    | .ok () =>
                        match annealProjectList
                            (annealProjectionCx fl.1 ly st.machine)
                            ⟨.indirect mp, fl.2⟩ projs with
                        | .ok projected => pure projected
                        | .error projErr => throw (annealLiftProjectionError projErr)
                | _ => throw (Miri.Interpreter.StepError.unsupported "projected operand in scalar rvalue")) :
                  Miri.Interpreter.RvalueM AnnealStepState (Miri.Interpreter.OpTy AnnealProv))
                m₁ = .ok a m' →
              MachineAddrSupplyEq m'.machine m.machine ∧
              (∀ tf, m.stack.frames = #[tf] →
                ∃ tf', m'.stack.frames = #[tf'] ∧
                  tf'.location = tf.location ∧
                  (∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k)) := by
            intro projs h'
            cases annealEvalOperand_proj_tail_eq fl.1 ly operand fl.2 projs h'
            refine ⟨haddr₁, fun tf htf => ?_⟩
            obtain ⟨hm₁_stk, hloc₁, himm₁⟩ := hstk₁ tf htf
            exact ⟨fl.1, hm₁_stk, hloc₁, himm₁⟩
          have hproj_eval : ∀ projs,
              annealEvalProjection ly ⟨operand, fl.2⟩ projs m₁ = .ok a m' →
              MachineAddrSupplyEq m'.machine m.machine ∧
              (∀ tf, m.stack.frames = #[tf] →
                ∃ tf', m'.stack.frames = #[tf'] ∧
                  tf'.location = tf.location ∧
                  (∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k)) := by
            intro projs h'
            cases annealEvalProjection_eq ly ⟨operand, fl.2⟩ projs h'
            refine ⟨haddr₁, fun tf htf => ?_⟩
            obtain ⟨hm₁_stk, hloc₁, himm₁⟩ := hstk₁ tf htf
            exact ⟨fl.1, hm₁_stk, hloc₁, himm₁⟩
          rcases hlist : place.projection.toList with _ | ⟨p0, ps⟩
          · rw [hlist] at h
            dsimp only [EStateM.bind, EStateM.get, EStateM.set, EStateM.pure, EStateM.throw] at h
            cases hrpl : fl.1.replaceLocalValue place.localId (.live (.immediate .uninit)) with
            | error _ => rw [hrpl] at h; cases h
            | ok frame'' =>
              rw [hrpl] at h
              dsimp only [EStateM.bind, EStateM.get, EStateM.set, EStateM.pure, EStateM.throw] at h
              obtain ⟨hloc₂, himm₂⟩ := replaceLocalValue_immediate_preserves hrpl
              split at h
              · dsimp only [EStateM.bind, EStateM.set, EStateM.pure] at h
                cases h
                refine ⟨haddr₁, fun tf htf => ?_⟩
                obtain ⟨hm₁_stk, hloc₁, himm₁⟩ := hstk₁ tf htf
                exact ⟨frame'', by simp [hm₁_stk], hloc₂.trans hloc₁,
                  fun k hk => himm₂ k (himm₁ k hk)⟩
              · dsimp only [EStateM.throw] at h
                cases h
          · cases p0 with
            | Deref =>
              cases ps with
              | nil =>
                rw [hlist] at h
                have htail := rvaluePreservesAllImm_bind
                  (annealDerefOperandToMemPlace_preserves ld ly place.localId operand fl.2)
                  (fun _ => rvaluePreservesAllImm_pure _) m₁ a m' h
                refine ⟨htail.1.trans haddr₁, fun tf htf => ?_⟩
                obtain ⟨hm₁_stk, hloc₁, himm₁⟩ := hstk₁ tf htf
                obtain ⟨tf', htf', hloc₂, himm₂⟩ := htail.2 fl.1 hm₁_stk
                exact ⟨tf', htf', hloc₂.trans hloc₁, fun k hk => himm₂ k (himm₁ k hk)⟩
              | cons p1 ps' =>
                rw [hlist] at h; exact hproj_other (.Deref :: p1 :: ps') h
            | Field idx ft =>
              cases ps with
              | nil =>
                rw [hlist] at h
                cases operand with
                | immediate imm =>
                  cases imm with
                  | scalarPair _ _ =>
                    by_cases h0 : (idx == 0) = true
                    · simp only [h0, ↓reduceIte, EStateM.pure] at h
                      cases h
                      refine ⟨haddr₁, fun tf htf => ?_⟩
                      obtain ⟨hm₁_stk, hloc₁, himm₁⟩ := hstk₁ tf htf
                      exact ⟨fl.1, hm₁_stk, hloc₁, himm₁⟩
                    · have h0f : (idx == 0) = false := Bool.eq_false_iff.mpr h0
                      simp only [h0f, Bool.false_eq_true, ↓reduceIte] at h
                      by_cases h1 : (idx == 1) = true
                      · simp only [h1, ↓reduceIte, EStateM.pure] at h
                        cases h
                        refine ⟨haddr₁, fun tf htf => ?_⟩
                        obtain ⟨hm₁_stk, hloc₁, himm₁⟩ := hstk₁ tf htf
                        exact ⟨fl.1, hm₁_stk, hloc₁, himm₁⟩
                      · have h1f : (idx == 1) = false := Bool.eq_false_iff.mpr h1
                        simp only [h1f, Bool.false_eq_true, ↓reduceIte] at h
                        exact hproj_eval [.Field idx ft] h
                  | _ => exact hproj_eval [.Field idx ft] h
                | indirect _ => exact hproj_eval [.Field idx ft] h
              | cons p1 ps' =>
                rw [hlist] at h; exact hproj_eval (.Field idx ft :: p1 :: ps') h
            | Index idx =>
              rw [hlist] at h; exact hproj_other (.Index idx :: ps) h
            | ConstantIndex offset minLength fromEnd =>
              rw [hlist] at h; exact hproj_other (.ConstantIndex offset minLength fromEnd :: ps) h
            | Subslice fromIdx toIdx fromEnd =>
              rw [hlist] at h; exact hproj_other (.Subslice fromIdx toIdx fromEnd :: ps) h
            | Downcast name v =>
              rw [hlist] at h; exact hproj_eval (.Downcast name v :: ps) h
            | OpaqueCast ty =>
              rw [hlist] at h; exact hproj_other (.OpaqueCast ty :: ps) h
            | UnwrapUnsafeBinder ty =>
              rw [hlist] at h; exact hproj_other (.UnwrapUnsafeBinder ty :: ps) h
            | PhantomDeref =>
              rw [hlist] at h; exact hproj_other (.PhantomDeref :: ps) h

private theorem step_assign_use_any_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {op : MirAst.Operand} {span : String}
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
        (annealEvalOperand_any_preserves body.localDecls body.layouts
          (translateOperand op) (some dp.layout))
        (fun opTy => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves opTy)
          (fun imm => annealWriteImmediate_preserves imm.imm dp))))
    hstep

private theorem step_assign_cast_ptrToPtr_any_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {op : MirAst.Operand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign dst (.cast .ptrToPtr op castTy), span⟩)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_of_rvalue hstate hbb hstmt
    (evalStatement_assign_cast_ptrToPtr_eq body.localDecls body.layouts dst op castTy span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_any_preserves body.localDecls body.layouts
          (translateOperand op) none)
        (fun src => cast_dispatch_ptrToPtr_preserves body.layouts src (encodeTyId castTy) dp)))
    hstep

private theorem step_assign_binOp_offset_any_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {lhs rhs : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign dst (.binaryOp .offset lhs rhs), span⟩)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine.addresses = m.machine.addresses ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_of_rvalue hstate hbb hstmt
    (evalStatement_assign_binOp_offset_eq body.localDecls body.layouts dst lhs rhs span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_any_preserves body.localDecls body.layouts
          (translateOperand lhs) (some dp.layout))
        (fun lOp => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves lOp)
          (fun lv => rvaluePreservesAllImm_bind
            (annealEvalOperand_any_preserves body.localDecls body.layouts
              (translateOperand rhs) none)
            (fun rOp => rvaluePreservesAllImm_bind
              (annealReadImmediate_preserves rOp)
              (fun rv => rvaluePreservesAllImm_bind
                (scalarOps_binary_preserves body.localDecls body.layouts .Offset lv rv)
                (fun res => rvaluePreservesAllImm_bind
                  (assertRvalueLayoutPub_preserves res.layout dp.layout)
                  (fun _ => annealWriteImmediate_preserves res.imm dp))))))))
    hstep

/-- `AllocIdSupplyReady` + `IsImmediateFrameLocal` preservation across any
`dst = .use op` statement (supporting `.copy`, `.move`, and `.constant` operands
and both immediate and memory-backed destination places). -/
theorem step_assign_use_preserves_supply
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {op : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.assign dst (.use op), span⟩)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    (AllocIdSupplyReady m'.machine.memory ∧
      m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId ∧
      m'.machine.memory.sourceAllocIdWorldActive = m.machine.memory.sourceAllocIdWorldActive) ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_supply_of_rvalue hstate hbb hstmt
    (evalStatement_assign_use_eq body.localDecls body.layouts dst op span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_any_preserves body.localDecls body.layouts
          (translateOperand op) (some dp.layout))
        (fun opTy => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves opTy)
          (fun imm => annealWriteImmediate_preserves imm.imm dp))))
    hsupply hstep

/-- `AllocIdSupplyReady` + `IsImmediateFrameLocal` preservation across any
`dst = op as *(const|mut) T` (`CastKind.PtrToPtr`) statement (supporting both
`.copy` and `.move` operands). -/
theorem step_assign_cast_ptrToPtr_preserves_supply
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {op : MirAst.Operand} {castTy : Ty} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign dst (.cast .ptrToPtr op castTy), span⟩)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    (AllocIdSupplyReady m'.machine.memory ∧
      m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId ∧
      m'.machine.memory.sourceAllocIdWorldActive = m.machine.memory.sourceAllocIdWorldActive) ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_supply_of_rvalue hstate hbb hstmt
    (evalStatement_assign_cast_ptrToPtr_eq body.localDecls body.layouts dst op castTy span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_any_preserves body.localDecls body.layouts
          (translateOperand op) none)
        (fun src => cast_dispatch_ptrToPtr_preserves body.layouts src (encodeTyId castTy) dp)))
    hsupply hstep

/-- `AllocIdSupplyReady` + `IsImmediateFrameLocal` preservation across any
`dst = Offset(lhs, rhs)` statement (supporting both `.copy` and `.move` operands). -/
theorem step_assign_binOp_offset_preserves_supply
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {lhs rhs : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign dst (.binaryOp .offset lhs rhs), span⟩)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    (AllocIdSupplyReady m'.machine.memory ∧
      m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId ∧
      m'.machine.memory.sourceAllocIdWorldActive = m.machine.memory.sourceAllocIdWorldActive) ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_supply_of_rvalue hstate hbb hstmt
    (evalStatement_assign_binOp_offset_eq body.localDecls body.layouts dst lhs rhs span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_any_preserves body.localDecls body.layouts
          (translateOperand lhs) (some dp.layout))
        (fun lOp => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves lOp)
          (fun lv => rvaluePreservesAllImm_bind
            (annealEvalOperand_any_preserves body.localDecls body.layouts
              (translateOperand rhs) none)
            (fun rOp => rvaluePreservesAllImm_bind
              (annealReadImmediate_preserves rOp)
              (fun rv => rvaluePreservesAllImm_bind
                (scalarOps_binary_preserves body.localDecls body.layouts .Offset lv rv)
                (fun res => rvaluePreservesAllImm_bind
                  (assertRvalueLayoutPub_preserves res.layout dp.layout)
                  (fun _ => annealWriteImmediate_preserves res.imm dp))))))))
    hsupply hstep

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

private instance (s : LocalSlot) : Decidable (s = .dead) :=
  match s with
  | .dead => isTrue rfl
  | .uninit => isFalse nofun
  | .init _ => isFalse nofun

private theorem stepMirFn_binOp_offset_const_eq
    {body : CapturedMir} {s s' : MachineState}
    {bb : BasicBlockData} {dstIdx : Local}
    {op_lhs : MirAst.Operand} {c : ConstOperand} {span : String}
    {ptrVal : ProvenancePtr} {sc : MirAst.ScalarInt} {stride : Nat}
    (e : AllocMapEntry) (tgtDecl : LocalDecl) {slot_t slot_d : LocalSlot}
    {locals_mid : List LocalSlot}
    (hphase : ∀ p, body.phase ≠ .other p)
    (htgt_prim : IsPrimScalarTy tgtDecl.ty)
    (hcal : s.memory.activeCallee = none := by rfl)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb := by rfl)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp .offset op_lhs (.constant c)), span⟩ := by rfl)
    (hop_lhs : evalOperand s.frame.locals op_lhs s.memory.borrows
      s.memory.globals body.layouts s.memory.callerLocals body.localDecls =
      .ok (.ptr ptrVal 8) locals_mid := by rfl)
    (hc : c.val = .scalar (.int sc) := by rfl)
    (hsz8 : sc.sizeBytes = 8 := by rfl)
    (hbor : lookupBorrow s.memory.borrows ptrVal.tag = some e.toBorrowEntry := by rfl)
    (hstride : pointeeElemByteStride body.localDecls body.layouts op_lhs =
      some stride := by rfl)
    (htgt_decl : get? body.localDecls e.localIdx = some tgtDecl := by rfl)
    (hslot_t : get? locals_mid e.localIdx = some slot_t := by rfl)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl)
    (hslot_d : get? locals_mid dstIdx = some slot_d := by rfl)
    (hset_d : set? locals_mid dstIdx
      (.init (.ptr { ptrVal with offsetBytes := ptrVal.offsetBytes + sc.bits * stride } 8)) =
      some s'.frame.locals := by rfl)
    (hprot : s.memory.activeProtectors = .nil := by rfl)
    (hs' : advanceStmt s s'.frame.locals
      { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstIdx none
        activeProtectors := .nil } = s' := by rfl)
    (hperm : e.perm ≠ .disabled := by rintro ⟨⟩)
    (hstride_le : stride ≤ 16 := by decide)
    (hbits_lt : sc.bits < 2 ^ 32 := by decide)
    (hoff_lt : ptrVal.offsetBytes < 2 ^ 32 := by decide)
    (hinb : (sc.bits = 0 ∧ ptrVal.offsetBytes = 0) ∨
      (slot_t ≠ .dead ∧
        ptrVal.offsetBytes + sc.bits * stride ≤
          (translateTy tgtDecl.ty body.layouts).layout.size.bytes.toNat) := by
      exact Or.inr ⟨by decide, by decide⟩)
    (hd_ne : slot_d ≠ .dead := by decide) :
    stepMirFn body s = .step s' := by
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  unfold evalStmt evalRvalue
  dsimp only []
  rw [hop_lhs]
  dsimp only []
  have hop_rhs : evalOperand locals_mid (.constant c) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.scalar sc) locals_mid := by
    unfold evalOperand evalConstValue; dsimp only []; rw [hc]
  rw [hop_rhs]
  dsimp only []
  rw [evalPtrOffsetBinOp_allocMap_ok hbor hperm hstride hstride_le htgt_decl htgt_prim hslot_t
    hsz8 hbits_lt hoff_lt hptr8 hinb]
  dsimp only []
  rw [hslot_d]
  cases slot_d with
  | dead => exact absurd rfl hd_ne
  | uninit => simp only [hset_d, hprot, hs']
  | init _ => simp only [hset_d, hprot, hs']

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
      StateRelLM3_1 lm31AddrOfBody s₄ m₄ (disableAllocMapLocal allocMap₃ 2) ∧
      stepMirFn lm31AddrOfBody s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 lm31AddrOfBody s₅ m₅
        (disableAllocMapLocal (disableAllocMapLocal allocMap₃ 2) 1) ∧
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
  let s₅ := mkWitState lm31AddrOfBody 8 [.init (.scalar ⟨99, 8⟩), .dead, .dead]
    (disableLocalBorrows borMut 1) 2
  have hs₅ : stepMirFn lm31AddrOfBody s₄ = .step s₅ := rfl
  have hsim₅ := step_storageDead_lm3_1_simulation hrel₄ hphase rfl rfl
    (decl := u64Decl) rfl (by decide)
  obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step hsim₅ hs₅
  obtain ⟨haddr₅, _⟩ := step_storageDead_preserves hrel₄ rfl rfl
    (decl := u64Decl) rfl (by decide) hm₅
  have hdealloc : m₅.machine.memory.live.find? (fun x => x.1 == lm31AllocId1) = none := by
    obtain ⟨tf₅, htf₅, _, _, _, _, _, _, _, hbor_eq₅, halloc_rel₅, _⟩ := id hrel₅
    have hbor₅ : s₅.memory.borrows =
        [{ tag := 1, targetLocal := 1, targetProjection := .nil, perm := .disabled }] := rfl
    let allocMap₅ := disableAllocMapLocal (disableAllocMapLocal allocMap₃ 2) 1
    change s₅.memory.borrows = allocMap₅.map AllocMapEntry.toBorrowEntry at hbor_eq₅
    cases halloc₅ : allocMap₅ with
    | nil =>
      rw [hbor₅, halloc₅] at hbor_eq₅; cases hbor_eq₅
    | cons e₅ rest =>
      rw [hbor₅, halloc₅] at hbor_eq₅
      injection hbor_eq₅ with he₅ _
      have heloc : e₅.localIdx = 1 := (congrArg BorrowEntry.targetLocal he₅).symm
      have hdead₁ : get? s₅.frame.locals e₅.localIdx = some .dead := by
        rw [heloc]; rfl
      have hmem₅ : e₅ ∈ disableAllocMapLocal (disableAllocMapLocal allocMap₃ 2) 1 := by
        change e₅ ∈ allocMap₅
        rw [halloc₅]
        exact .head _
      have hfind_none := (halloc_rel₅.local_alloc_sync tf₅ htf₅ e₅ hmem₅).2 hdead₁
      obtain ⟨_, _, hbase₅⟩ := halloc_rel₅.base_addr_valid e₅ hmem₅
      have hbase_arr : m₅.machine.addresses.baseAddr =
          #[⟨lm31AllocId1, annealStackBaseAddr lm31AllocId1⟩] := by
        have ha : m₅.machine.addresses = m₁.machine.addresses :=
          haddr₅.trans (haddr₄.trans (haddr₃.trans haddr₂))
        rw [congrArg (fun a => a.baseAddr) ha, haddr₁]
        rfl
      unfold AnnealMachine.lookupBaseAddr at hbase₅
      rw [hbase_arr] at hbase₅
      have he_id : e₅.allocId = lm31AllocId1 := by
        by_cases heq : e₅.allocId = lm31AllocId1
        · exact heq
        · have hbeqf : (lm31AllocId1 == e₅.allocId) = false :=
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
      StateRelLM3_1 lm31DanglingBody s₂ m₂ (disableAllocMapLocal [entry] 1) ∧
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
  let s₂ := mkWitState lm31DanglingBody 5 [.uninit, .dead, .init ptr0]
    (disableLocalBorrows borConst 1) 2
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
4. `_5 = Offset(copy _3, const 9_usize)`: BOTH machines raise undefined
   behavior: Anneal's `stepMirFn` rejects the out-of-bounds offset
   (`MirStepNode.fail .ub`) and `lean-miri`'s `Miri.Interpreter.Step.step`
   raises `.error (.undefinedBehavior msg)` via
   `step_binOp_offset_oob_dangling_miri_ub`. -/
theorem wit_lm3_1_ptrToPtr_and_offset_real_steps :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState) (msg : String),
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
      stepMirFn lm31PtrCastOffsetBody s₃ = .fail .ub ∧
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
  have hs₃ : stepMirFn lm31PtrCastOffsetBody s₂ = .step s₃ :=
    stepMirFn_binOp_offset_const_eq
      (rawPtrAllocMapEntry lm31PtrCastOffsetBody.localDecls lm31PtrCastOffsetBody.layouts
        .mut 1 1 lm31AllocId1)
      u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
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
        exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  obtain ⟨_, himm₃_step⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
    rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4: `_5 = Offset(copy _3, const 9_usize)` (UB in both!)
  obtain ⟨hs₄, m₄, msg, hm₄⟩ := step_binOp_offset_oob_dangling_miri_ub hrel₃ hphase rfl rfl
    (dstDecl := rawPtrMutU8Decl) (ptrDecl := rawPtrMutU8Decl) (tgtDecl := u64Decl)
    rfl rfl rfl (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
    (fun tf₃ _ => constUsize_wellTyped lm31PtrCastOffsetBody tf₃ 9 (by decide))
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 3 (by decide)⟩)
    (ptrVal := { allocId := 1, offsetBytes := 0 }) (sc := ⟨9, 8⟩)
    rfl rfl (by rintro ⟨⟩) (.head _) rfl rfl (by decide) (by decide) (Or.inr (by decide))
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, msg,
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
(`step_deref_oob_simulation`) and in-bounds misaligned dereference UB
(`step_deref_misaligned_simulation`):
1. On `lm31DerefOobRealBody` (`&raw const _1` -> `as *const u8` -> `Offset(_, 8)`
   -> `as *const u64` -> `_0 = copy *_5`), the first 4 steps execute in lockstep
   to `StateRelLM3_1`-related states; at step 5 (`_0 = copy *_5`), BOTH Anneal's
   `stepMirFn` (`MirStepNode.fail .ub`) and `Miri.Interpreter.Step.step`
   (`StepError.undefinedBehavior`) reject the read (`8 < 8 + 8`).
2. On `lm31DerefMisalignedRealBody` (`&raw const _1` -> `as *const u8` ->
   `Offset(_, 2)` -> `as *const u32` -> `_0 = copy *_5`), the first 4 steps
   execute in lockstep to `StateRelLM3_1`-related states where `*_5` is strictly
   in-bounds (`2 + 4 = 6 ≤ 8`); at step 5 (`_0 = copy *_5`), BOTH Anneal's
   `stepMirFn` (`MirStepNode.fail .ub`) and `Miri.Interpreter.Step.step`
   (`StepError.undefinedBehavior`) reject the 4-byte misaligned read at byte
   offset `2`. -/
theorem wit_lm3_1_deref_oob_and_misaligned_real_steps :
    -- (1) Real-step one-past-end OOB dereference (`offset = 8` on 8-byte `_1`)
    (∃ (s₄ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefOobRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      stepMirFn b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) ∧
    -- (2) Real-step in-bounds misaligned `u32` dereference (`offset = 2`, `2 + 4 ≤ 8`)
    (∃ (s₄ : MachineState) (m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefMisalignedRealBody
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₄ m₄
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      s₄.frame.stmtIdx = 4 ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₄ = .fail .ub ∧
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
    have hs₃ : stepMirFn lm31DerefOobRealBody s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry lm31DerefOobRealBody.localDecls lm31DerefOobRealBody.layouts
          .not 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
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
            subst hp' hsc' hd; exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)) hs₃
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
    have hs₅ : stepMirFn lm31DerefOobRealBody s₄ = .fail .ub := rfl
    exact ⟨s₄, m₄, m₅, msg, hrel₄, rfl, hs₅, hm₅⟩
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
    have hs₃ : stepMirFn lm31DerefMisalignedRealBody s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry lm31DerefMisalignedRealBody.localDecls
          lm31DerefMisalignedRealBody.layouts .not 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
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
            subst hp' hsc' hd; exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)) hs₃
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
    obtain ⟨m₅, msg, hm₅⟩ :=
      step_deref_misaligned_miri_ub hrel₄ (Or.inl rfl) rfl rfl
        (dstDecl := u32DeclLM31) (ptrDecl := rawPtrConstU32Decl) rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
        (fun tf htf => himm₄ tf htf 5 (by decide))
        (ptrVal := { allocId := 1, offsetBytes := 2 })
        rfl (.head _) rfl hfind_la hinb (by decide)
    have hs₅ : stepMirFn lm31DerefMisalignedRealBody s₄ = .fail .ub := rfl
    exact ⟨s₄, m₄, m₅, msg, hrel₄, rfl, rfl, hs₅, hm₅⟩

/-! ## 6. Agreement: Narrowing Pointer-Cast Dereferences Read the Pointee Type -/

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
3. `_0 = copy *_3` raises undefined behavior in BOTH machines
   (`step_deref_invalid_bool_simulation`): Anneal's `stepMirFn` rejects the
   invalid `bool` bit pattern (`MirStepNode.fail .ub`) and `lean-miri`'s
   `Miri.Interpreter.Step.step` (`annealStepHooks`) reports
   `StepError.undefinedBehavior`. -/
theorem wit_lm3_1_invalid_bool_cast_deref_real_steps :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let b := lm31InvalidBoolDerefBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      stepMirFn b lm31InvalidBoolAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31InvalidBoolMiriPre = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior msg)) := by
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
  obtain ⟨hsim₃, hs₃⟩ := step_deref_invalid_bool_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
    (dstDecl := boolDeclLM31) (ptrDecl := rawPtrConstBoolDecl) (tgtDecl := u8DeclLM31)
    rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide))
    (ptrVal := { allocId := 1, offsetBytes := 0 })
    rfl rfl (.head _) rfl rfl (Or.inl rfl) rfl (by decide)
  obtain ⟨m₃, msg, hm₃⟩ := stepRelLM3_1_of_anneal_ub hsim₃ hs₃
  exact ⟨s₁, s₂, m₁, m₂, m₃, msg, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃⟩

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
    -- (1) `*const u64` + `1_usize` stride simulation (`+ 8` in both)
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
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + 8),
              .concrete lm31AllocId1 borTag⟩))))) ∧
    -- (2) `*const u8` at offset `2` + `(-1_isize)` signed delta simulation (`+ 1` in both)
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
        some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
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
    obtain ⟨_, hs₂, m₂, tf₂, borTag, hm₂, htf₂, hval₂⟩ :=
      step_binOp_offset_stride_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
        (fun tf₁ _ => .of_wt (constUsize_wellTyped b tf₁ 1 (by decide)))
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
        rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
        (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
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
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
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
            subst hp' hsc' hd; exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)) hs₃
    obtain ⟨_, himm₃_step⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
      rfl rfl hm₃
    have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
      intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
    obtain ⟨_, hs₄, m₄, tf₄, borTag, hm₄, htf₄, hval₄⟩ :=
      step_binOp_offset_neg_isize_simulation hrel₃ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrConstU8Decl) (ptrDecl := rawPtrConstU8Decl) (tgtDecl := u64Decl)
        (rhsTy := isizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) rfl
        (fun tf₃ _ => .of_wt (constNegOneIsize_wellTyped b tf₃))
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 2 }) (countMag := 1)
        rfl rfl (by decide) (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl (by rintro ⟨⟩)
        (by decide) (by decide)
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
  let s₅_v := mkWitState lm31AddrOfBody 8 [.init (.scalar ⟨99, 8⟩), .dead, .dead]
    (disableLocalBorrows borMut 1) 2
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
      exact ⟨_, _, _, _, _, m₁, m₂, m₃, m₄, m₅, allocMap₂,
        disableAllocMapLocal (disableAllocMapLocal allocMap₃ 2) 1,
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
Concrete real-step witnesses for BOTH RFC 2582 `&raw (const|mut) (*_p)`
place-to-pointer correspondences:

1. **Null place-to-pointer (`&raw const (*ptr::null::<u64>())`)**: on a
   `StateRelLM3_1` state where `_1 : *const u64` holds `Value.scalar ⟨0, 8⟩`,
   `_2 = &raw const (*_1)` steps in Anneal storing `⟨0, 8⟩` in `_2` and in
   `lean-miri` storing `lm31Scalar0U64` (`0`) in `_2`
   (`step_rawPtr_deref_null_correspondence`).
2. **Non-zero byte offset (`&raw const (*_4)` at `offsetBytes = 1`)**: after
   `_2 = &raw mut _1` -> `_3 = copy _2 as *mut u8` ->
   `_4 = Offset(copy _3, 1_usize)` in lockstep (`offsetBytes = 1`),
   `_5 = &raw const (*_4)` preserves `offsetBytes = 1` in Anneal (`s₄`) and
   `annealStackBaseAddr lm31AllocId1 + 1` in `lean-miri` (`m₄`,
   `step_rawPtr_deref_nonzero_offset_correspondence`). -/
theorem wit_lm3_1_rawPtr_deref_null_and_offset_real_steps :
    -- (1) `&raw const (*_1)` on null `0 as *const u64`
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31RawPtrDerefNullBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
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
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8)) ∧
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
    obtain ⟨⟨s₁, hs₁, hget₁⟩, m₁, tf₁, msc_ref, hm₁, htf₁, hrel_ref, hval₁⟩ :=
      step_rawPtr_deref_null_correspondence hrel₀ hphase rfl rfl
        (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (by rintro ⟨⟩) rfl
    have hmsc_eq : msc_ref = lm31Scalar0U64 :=
      scalarInt_eq_of_scalarRel hrel_ref lm31_scalarRel0U64
    subst hmsc_eq
    exact ⟨s₁, m₁, tf₁, hrel₀, hs₁, hget₁, hm₁, htf₁, hval₁⟩
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
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
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
            subst hp' hsc' hd; exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)) hs₃
    obtain ⟨_, himm₃_step⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩)
      rfl rfl hm₃
    have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
      intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
    obtain ⟨⟨s₄, hs₄, hget₄⟩, m₄, tf₄, borTag, hm₄, htf₄, hval₄⟩ :=
      step_rawPtr_deref_nonzero_offset_correspondence hrel₃ hphase rfl rfl
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

1. **Unexposed `PointerWithExposedProvenance` (`lm31ForgedProvenanceBody`)**:
   after `_2 = &raw const _1` (`_1 = 42_u64`, tag `1`, NEVER exposing `_2`),
   `_4 = const 65536_usize as *const u64` diverges
   (`step_cast_with_exposed_provenance_divergence`): `lean-miri` fails closed
   with `.error (.unsupported "pointerFromExposedAddress in cast")`, whereas
   Anneal keeps the unexposed address as the provenance-less scalar
   `⟨65536, 8⟩` in `_4`, so the subsequent `_0 = copy *_4` faults with
   `MirStepNode.fail .ub` instead of reading `_1`.
2. **Pointer exposure (`PointerExposeProvenance`, `lm31ExposeProvenanceBody`)**:
   after `_2 = &raw const _1` in lockstep, `_3 = copy _2 as usize` stores an
   integer address `⟨addrBits, 8⟩` in Anneal while `lean-miri` fails closed with
   `.error (.unsupported "exposeProvenance in cast")`
   (`step_cast_expose_provenance_ptr_unsupported`). -/
theorem wit_lm3_1_anneal_forged_provenance_real_steps :
    -- (1) `PointerWithExposedProvenance` keeps unexposed `65536` scalar and faults on `*_4`
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm31ForgedProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 4 = some (.init (.scalar ⟨65536, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₁ =
        (m₂, .error (.unsupported "pointerFromExposedAddress in cast")) ∧
      stepMirFn b s₂ = .fail .ub) ∧
    -- (2) `PointerExposeProvenance`: exposes address in Anneal vs. `.unsupported`
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState) (addrBits : Nat),
      let b := lm31ExposeProvenanceBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.scalar ⟨addrBits, 8⟩)) ∧
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
        (dstDecl := rawPtrConstU64Decl) rfl rfl rfl rfl rfl rfl (by decide) (by rintro ⟨⟩) rfl rfl
    let s₂_def := mkWitState b 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .init (.scalar ⟨65536, 8⟩), .uninit]
      bor 2
    have hs₂_eq : s₂ = s₂_def := by
      have h : stepMirFn b s₁ = .step s₂_def := by
        let bb₀ : BasicBlockData :=
          { statements := [
              mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
              mkStmt (.assign (local_ 4)
                (.cast .pointerWithExposedProvenance (.constant (constUsizeLM31 65536))
                  rawPtrConstU64Ty)),
              mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 4))))],
            terminator := mkTerm .return_, isCleanup := false }
        have hbb : get? b.basicBlocks s₁.frame.blockIdx = some bb₀ := rfl
        have hstmt : get? bb₀.statements s₁.frame.stmtIdx =
            some (mkStmt (.assign (local_ 4)
              (.cast .pointerWithExposedProvenance (.constant (constUsizeLM31 65536))
                rawPtrConstU64Ty))) := rfl
        rw [stepMirFn_eq_of_not_other b s₁ rfl hphase]
        simp only [hbb, hstmt]
        unfold evalStmt evalRvalue evalPointerWithExposedProvenance
        dsimp only [b, lm31ForgedProvenanceBody, s₁, mkWitState, initMachineState, mkStmt, local_,
          isBadWithExposedTargetTy, isThinRawPtrTy, rawPtrConstU64Ty,
          isExposeIntSourceTy, layoutPointerBytes, emptyLayoutTable, operandTy,
          constUsizeLM31, usizeTyLM31, evalOperand, evalConstValue, Nat.beq,
          operandIsSigned, tyIsSigned, wrapScalarBits, scalarModulus, Bool.not_true]
        have hrec : recoverExposedPtrValue?
            [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit]
            bor [] [] []
            [u64Decl, u64Decl, rawPtrConstU64Decl, usizeDeclLM31, rawPtrConstU64Decl, u64Decl]
            emptyLayoutTable 8 65536 =
            some (.scalar ⟨65536, 8⟩) := by
          unfold recoverExposedPtrValue? findBestExposedStackBorrow
          rw [show Nat.div 65536 65536 = 1 by decide]
          rfl
        rw [hrec]
        rfl
      rw [h] at hs₂; injection hs₂ with ht; injection ht with heq; exact heq.symm
    subst hs₂_eq
    have hs₃ : stepMirFn b s₂_def = .fail .ub := rfl
    exact ⟨s₁, s₂_def, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hget₂, hm₂, hs₃⟩
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
    obtain ⟨⟨s₂, addrBits, hs₂, hget₂⟩, m₂, hm₂⟩ :=
      step_cast_expose_provenance_ptr_unsupported hrel₁ hphase rfl rfl
        (dstDecl := usizeDeclLM31) (srcDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => himm₁ tf₁ htf₁ 2 (by decide))
        (by rintro ⟨⟩) (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl
    exact ⟨s₁, s₂, m₁, m₂, addrBits, hs₁, hm₁, hrel₁, hs₂, hget₂, hm₂⟩

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
invalid-`bool` dereference write UB, and `PlaceMention(*_p)` on null and
`.uninit` pointers, all in lockstep:

1. **Invalid `char` surrogate read (`0xD800_u32 as *const char`)**: after
   `_2 = &raw const _1` and `_3 = copy _2 as *const char` in lockstep,
   `_0 = copy *_3` raises undefined behavior in BOTH Anneal
   (`MirStepNode.fail .ub`) and `lean-miri`
   (`StepError.undefinedBehavior "reading invalid value"`,
   `step_deref_invalid_char_simulation`).
2. **Invalid `bool` dereference write (`*_3 = const (2 : bool)`)**: after
   `_2 = &raw mut _1` and `_3 = copy _2 as *mut bool` in lockstep,
   `*_3 = const (2 : bool)` raises undefined behavior in BOTH Anneal
   (`MirStepNode.fail .ub`) and `lean-miri`
   (`StepError.undefinedBehavior "writing invalid value"`,
   `step_deref_write_invalid_bool_simulation`).
3. **`PlaceMention(*_p)` on null and `.uninit` pointers**: on
   `lm31PlaceMentionDerefBody`, Step 1 (`PlaceMention(*_1)` on null
   `0 as *const u64`) steps in lockstep to `StateRelLM3_1`-related states
   (`step_placeMention_deref_lm3_1_simulation`), and Step 2 (`PlaceMention(*_2)`
   on `.uninit` `_2`) raises undefined behavior in BOTH Anneal
   (`MirStepNode.fail .ub`) and `lean-miri`
   (`StepError.undefinedBehavior "read of uninitialized local"`,
   `step_placeMention_deref_uninit_simulation`). -/
theorem wit_lm3_1_invalid_char_write_bool_and_placeMention_real_steps :
    -- (1) Invalid `char` surrogate read (`0xD800_u32`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
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
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "reading invalid value"))) ∧
    -- (2) Invalid `bool` dereference write (`2`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
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
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "writing invalid value"))) ∧
    -- (3) `PlaceMention(*_1)` lockstep -> `PlaceMention(*_2)` UB
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState),
      let b := lm31PlaceMentionDerefBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      stepMirFn b s₁ = .fail .ub ∧
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
    obtain ⟨_, hs₃, m₃, hm₃⟩ := step_deref_invalid_char_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := charDeclLM31) (ptrDecl := rawPtrConstCharDecl) (tgtDecl := u32DeclLM31)
      rfl rfl rfl rfl (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 0 })
      rfl rfl (.head _) rfl rfl (Or.inl rfl) rfl (by decide)
    exact ⟨s₁, s₂, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, hs₃, hm₃⟩
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
    obtain ⟨_, hs₃, m₃, hm₃⟩ := step_deref_write_invalid_bool_simulation hrel₂ hphase
      rfl rfl (ptrDecl := rawPtrMutBoolDecl) (tgtDecl := u8DeclLM31)
      rfl rfl rfl rfl (by decide) (by decide)
      (fun tf₂ htf₂ => himm₂ tf₂ htf₂ 3 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 0 })
      rfl (.head _) rfl (Or.inl rfl) rfl (by decide) (by rintro ⟨⟩)
    exact ⟨s₁, s₂, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, hs₃, hm₃⟩
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
        (fun tf htf => mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1)) hs₁
    obtain ⟨_, himm₁_step⟩ := step_placeMention_preserves hrel₀ rfl rfl hm₁
    have himm₁_2 : ∀ tf₁, m₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 2 := by
      intro tf₁ htf₁
      exact himm₁_step _ tf₁ rfl htf₁ 2 (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl 2)
    obtain ⟨_, hs₂, m₂, hm₂⟩ := step_placeMention_deref_uninit_simulation hrel₁ hphase rfl rfl
      (ptrDecl := rawPtrConstU64Decl) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      himm₁_2 rfl
    exact ⟨s₁, m₁, m₂, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

/-! ## 8. Move-Operand Raw-Pointer Chaining, Provenance-Less Cast/Offset,
and RFC 2582 Zero-Offset vs. Permission Witnesses -/

/-- `Runtime(PostCleanup)` MIR body chaining `_2 = &raw mut _1`,
`_3 = copy _2`, `_4 = move _2 as *mut u8`, `_5 = Offset(move _4, 8_usize)`,
`_2 = move _3`, and `_0 = copy *_3` (UB on moved-from `_3`):
```text
bb0: _2 = &raw mut _1;
     _3 = copy _2;
     _4 = move _2 as *mut u8 (PtrToPtr);
     _5 = Offset(move _4, const 8_usize);
     _2 = move _3;
     _0 = copy *_3;
     return
``` -/
def lm31RawPtrUseMoveBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_use_move_chain"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl,
    rawPtrMutU8Decl, rawPtrMutU8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.use (.copy (local_ 2)))),
        mkStmt (.assign (local_ 4) (.cast .ptrToPtr (.move (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 5)
          (.binaryOp .offset (.move (local_ 4)) (.constant (constUsizeLM31 8)))),
        mkStmt (.assign (local_ 2) (.use (.move (local_ 3)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 3))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `_2 = copy _1 as usize`
(`CastKind.PointerExposeProvenance`) on provenance-less `_1 : *const u64`. -/
def lm31ExposeScalarCopyBody : CapturedMir where
  defPath := "lm_3_1_witness::expose_scalar_copy"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, usizeDeclLM31, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.cast .pointerExposeProvenance (.copy (local_ 1)) usizeTyLM31))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `_2 = move _1 as usize`
(`CastKind.PointerExposeProvenance`) on provenance-less `_1 : *const u64`. -/
def lm31ExposeScalarMoveBody : CapturedMir where
  defPath := "lm_3_1_witness::expose_scalar_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, usizeDeclLM31, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.cast .pointerExposeProvenance (.move (local_ 1)) usizeTyLM31))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_rawPtr_use_move_and_expose_scalar_real_steps`**:
Concrete real-step witnesses exercising raw-pointer `.copy`/`.move` assignment,
`.move` `PtrToPtr` cast, `.move` `BinOp.Offset`, and provenance-less
`PointerExposeProvenance`:

1. **6-step move/copy raw-pointer chain (`lm31RawPtrUseMoveBody`)**:
   `_2 = &raw mut _1` -> `_3 = copy _2` (`step_rawPtr_use_lm3_1_simulation`) ->
   `_4 = move _2 as *mut u8` (`step_cast_ptrToPtr_move_simulation`,
   deinitializing `_2`) -> `_5 = Offset(move _4, const 8_usize)`
   (`step_binOp_offset_move_simulation`, storing `offsetBytes = 8` in `_5` and
   deinitializing `_4`) -> `_2 = move _3` (`step_rawPtr_use_lm3_1_simulation`,
   restoring `{ allocId := 1, offsetBytes := 0 }` into `_2` and deinitializing
   `_3`) -> `_0 = copy *_3` (`step_deref_read_simulation`, diagnosing UB in
   both machines because `_3` was moved from).
2. **Provenance-less `PointerExposeProvenance` (`lm31ExposeScalarCopyBody`,
   `lm31ExposeScalarMoveBody`)**:
   `step_cast_expose_provenance_scalar_simulation` steps in lockstep to
   `StateRelLM3_1`-related states on both `.copy` (`0 as *const u64 -> 0_usize`)
   and `.move` (`42 as *const u64 -> 42_usize`, deinitializing `_1`). -/
theorem wit_lm3_1_rawPtr_use_move_and_expose_scalar_real_steps :
    -- (1) 6-step move/copy raw-pointer chain ending in moved-from deref UB
    (∃ (s₁ s₂ s₃ s₄ s₅ : MachineState)
      (m₁ m₂ m₃ m₄ m₅ m₆ : AnnealStepState) (msg : String),
      let b := lm31RawPtrUseMoveBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      get? s₃.frame.locals 2 = some .uninit ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ [entry] ∧
      get? s₅.frame.locals 3 = some .uninit ∧
      get? s₅.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      stepMirFn b s₅ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .error (.undefinedBehavior msg))) ∧
    -- (2) Provenance-less `PointerExposeProvenance` on `.copy` and `.move`
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState),
      let bc := lm31ExposeScalarCopyBody
      let bm := lm31ExposeScalarMoveBody
      let hc := annealStepHooks bc.localDecls bc.layouts
      let hm := annealStepHooks bm.localDecls bm.layouts
      stepMirFn bc (mkFourLocalScalarAnnealPre bc ⟨0, 8⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hc ()
        (mkFourLocalScalarMiriPre bc u64Ty rawPtrConstU64Ty lm31Scalar0U64) = (m₁, .ok true) ∧
      StateRelLM3_1 bc s₁ m₁ [] ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      stepMirFn bm (mkFourLocalScalarAnnealPre bm ⟨42, 8⟩) = .step s₂ ∧
      Miri.Interpreter.Step.step hm ()
        (mkFourLocalScalarMiriPre bm u64Ty rawPtrConstU64Ty lm31Scalar42) = (m₂, .ok true) ∧
      StateRelLM3_1 bm s₂ m₂ [] ∧
      get? s₂.frame.locals 1 = some .uninit ∧
      get? s₂.frame.locals 2 = some (.init (.scalar ⟨42, 8⟩))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  refine ⟨?_, ?_⟩
  · -- Part (1): `lm31RawPtrUseMoveBody`
    let b := lm31RawPtrUseMoveBody
    have hrel₀ : StateRel b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) :=
      mkSixLocal_stateRel b u64Ty u64Decl rawPtrMutU64Decl rawPtrMutU64Decl
        rawPtrMutU8Decl rawPtrMutU8Decl rfl rfl
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
      (step_rawPtr_use_lm3_1_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (srcDecl := rawPtrMutU64Decl) rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)) hs₂
    obtain ⟨_, himm₂_step⟩ := step_assign_use_any_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    let s₃ := mkWitState b 3
      [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .init ptr0, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_move_simulation hrel₂ hphase rfl rfl
        (dstDecl := rawPtrMutU8Decl) (srcDecl := rawPtrMutU64Decl) rfl rfl rfl rfl rfl rfl rfl
        (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₃
    obtain ⟨_, himm₃_step⟩ := step_assign_cast_ptrToPtr_any_preserves hrel₂ rfl rfl hm₃
    have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
      intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
    let s₄ := mkWitState b 4
      [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr0, .uninit, .init ptr8] bor 2
    have hs₄ : stepMirFn b s₃ = .step s₄ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
      (step_binOp_offset_move_simulation hrel₃ hphase rfl rfl
        (dstDecl := rawPtrMutU8Decl) (ptrDecl := rawPtrMutU8Decl) rfl rfl rfl rfl
        (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
        (fun tf₃ _ => constUsize_wellTyped b tf₃ 8 (by decide))
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
        (fun ptrVal sc e tgtDecl hp hsc he _ htgt => by
          have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
          have hsc' : sc = ⟨8, 8⟩ := by
            change evalOperand (s₃.frame.locals.set 4 .uninit)
              (.constant (constUsizeLM31 8)) _ _ _ _ = _ at hsc
            injection hsc with hv _; injection hv with hsc_eq; exact hsc_eq.symm
          cases he with
          | tail _ h => cases h
          | head _ =>
            have hd : tgtDecl = u64Decl := Option.some.inj htgt.symm
            subst hp' hsc' hd; exact ⟨by rintro ⟨⟩, Or.inr ⟨by rintro ⟨⟩, by decide⟩⟩)) hs₄
    obtain ⟨_, himm₄_step⟩ := step_assign_binOp_offset_any_preserves hrel₃ rfl rfl hm₄
    have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
      intro tf₄ htf₄ k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
      exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
    let s₅ := mkWitState b 5
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .init ptr8] bor 2
    have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
    obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_use_lm3_1_simulation hrel₄ hphase (Or.inr rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (srcDecl := rawPtrMutU64Decl) rfl rfl rfl rfl
        (fun tf₄ htf₄ => ⟨himm₄ tf₄ htf₄ 2 (by decide), himm₄ tf₄ htf₄ 3 (by decide)⟩)) hs₅
    obtain ⟨_, himm₅_step⟩ := step_assign_use_any_preserves hrel₄ rfl rfl hm₅
    have himm₅ : ∀ tf₅, m₅.stack.frames = #[tf₅] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₅ k := by
      intro tf₅ htf₅ k hne; obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
      exact himm₅_step tf₄ tf₅ htf₄ htf₅ k (himm₄ tf₄ htf₄ k hne)
    have hs₆_ub : stepMirFn b s₅ = .fail .ub := rfl
    obtain ⟨_, hsim₆⟩ := step_deref_read_simulation hrel₅ hphase (Or.inl rfl) rfl rfl
      (dstDecl := u64Decl) (ptrDecl := rawPtrMutU64Decl) rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      (fun tf₅ htf₅ => ⟨himm₅ tf₅ htf₅ 0 (by decide), himm₅ tf₅ htf₅ 3 (by decide)⟩)
      (fun _ hp => nomatch hp)
    obtain ⟨m₆, msg, hm₆⟩ := stepRelLM3_1_of_anneal_ub hsim₆ hs₆_ub
    exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, m₆, msg,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, rfl, hs₄, hm₄, rfl,
      hs₅, hm₅, hrel₅, rfl, rfl, hs₆_ub, hm₆⟩
  · -- Part (2): `lm31ExposeScalarCopyBody` & `lm31ExposeScalarMoveBody`
    let bc := lm31ExposeScalarCopyBody
    let bm := lm31ExposeScalarMoveBody
    have hrel_c₀ : StateRelLM3_1 bc (mkFourLocalScalarAnnealPre bc ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bc u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bc u64Ty u64Decl rawPtrConstU64Decl usizeDeclLM31
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hrel_m₀ : StateRelLM3_1 bm (mkFourLocalScalarAnnealPre bm ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre bm u64Ty rawPtrConstU64Ty lm31Scalar42) [] :=
      (mkFourLocalScalar_stateRel bm u64Ty u64Decl rawPtrConstU64Decl usizeDeclLM31
        u64Decl ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    let s₁ := mkWitState bc 1
      [.uninit, .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨0, 8⟩), .uninit] [] 1
    have hs₁ : stepMirFn bc (mkFourLocalScalarAnnealPre bc ⟨0, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_expose_provenance_scalar_simulation hrel_c₀ (fun _ h => nomatch h)
        (Or.inl rfl) rfl rfl (dstDecl := usizeDeclLM31) (srcDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl rfl rfl
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (fun _ => by rintro ⟨⟩)) hs₁
    let s₂ := mkWitState bm 1 [.uninit, .uninit, .init (.scalar ⟨42, 8⟩), .uninit] [] 1
    have hs₂ : stepMirFn bm (mkFourLocalScalarAnnealPre bm ⟨42, 8⟩) = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_expose_provenance_scalar_simulation hrel_m₀ (fun _ h => nomatch h)
        (Or.inr rfl) rfl rfl (dstDecl := usizeDeclLM31) (srcDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl rfl rfl
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (fun _ => by rintro ⟨⟩)) hs₂
    exact ⟨s₁, s₂, m₁, m₂, hs₁, hm₁, hrel₁, rfl, hs₂, hm₂, hrel₂, rfl, rfl⟩

/-- `Runtime(PostCleanup)` MIR body executing `_2 = copy _1 as *const u8`
(`CastKind.PtrToPtr`) where `_1 : *const u64` holds null (`0 as *const u64`). -/
def lm31NullPtrToPtrBody : CapturedMir where
  defPath := "lm_3_1_witness::null_ptr_to_ptr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, rawPtrConstU8Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.cast .ptrToPtr (.copy (local_ 1)) rawPtrConstU8Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing
`_2 = Offset(copy _1, const 0_usize)` where `_1 : *const u8` holds null
(`0 as *const u8`). -/
def lm31NullOffsetZeroBody : CapturedMir where
  defPath := "lm_3_1_witness::null_offset_zero"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU8Decl, rawPtrConstU8Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.binaryOp .offset (.copy (local_ 1)) (.constant (constUsizeLM31 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing
`_2 = Offset(copy _1, const 1_usize)` where `_1 : *const u8` holds null
(`0 as *const u8`). -/
def lm31NullOffsetOneBody : CapturedMir where
  defPath := "lm_3_1_witness::null_offset_one"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU8Decl, rawPtrConstU8Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.binaryOp .offset (.copy (local_ 1)) (.constant (constUsizeLM31 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_null_ptrToPtr_and_offset_correspondences_real_steps`**:
Concrete real-step witnesses for the three provenance-less raw-pointer cases
that Stage-1 brought into agreement
(`step_cast_ptrToPtr_scalar_correspondence`,
`step_binOp_offset_scalar_zero_correspondence`, and
`step_binOp_offset_scalar_nonzero_simulation`):

1. **`0 as *const u64 -> *const u8` (`PtrToPtr`)**: BOTH machines step, Anneal
   storing `⟨0, 8⟩` and `lean-miri` storing `lm31Scalar0U64` (`0`) in `_2`.
2. **`Offset(0 as *const u8, 0_usize)`**: BOTH machines step, Anneal storing
   `⟨0, 8⟩` and `lean-miri` storing `lm31Scalar0U64` (`0`) in `_2`.
3. **`Offset(0 as *const u8, 1_usize)`**: BOTH machines raise undefined
   behavior (Anneal `MirStepNode.fail .ub`; `lean-miri`
   `StepError.undefinedBehavior "pointer Offset out of bounds"`). -/
theorem wit_lm3_1_null_ptrToPtr_and_offset_correspondences_real_steps :
    -- (1) `PtrToPtr` on null `0 as *const u64`
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31NullPtrToPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (2) `Offset(0 as *const u8, 0_usize)`
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31NullOffsetZeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (3) `Offset(0 as *const u8, 1_usize)`
    (∃ (m₁ : AnnealStepState),
      let b := lm31NullOffsetOneBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      StateRelLM3_1 b s₀ m₀ [] ∧
      stepMirFn b s₀ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₀ =
        (m₁, .error (.undefinedBehavior "pointer Offset out of bounds"))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- Part (1): `lm31NullPtrToPtrBody`
    let b := lm31NullPtrToPtrBody
    have hrel₀ : StateRelLM3_1 b (mkFourLocalScalarAnnealPre b ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU8Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    obtain ⟨⟨s₁, hs₁, hget₁⟩, m₁, tf₁, msc, hm₁, htf₁, hrel_msc, hval₁⟩ :=
      step_cast_ptrToPtr_scalar_correspondence hrel₀ (fun _ h => nomatch h) rfl rfl
        (dstDecl := rawPtrConstU8Decl) (srcDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (by rintro ⟨⟩) rfl
    have hmsc_eq : msc = lm31Scalar0U64 := scalarInt_eq_of_scalarRel hrel_msc lm31_scalarRel0U64
    subst hmsc_eq
    exact ⟨s₁, m₁, tf₁, hrel₀, hs₁, hget₁, hm₁, htf₁, hval₁⟩
  · -- Part (2): `lm31NullOffsetZeroBody`
    let b := lm31NullOffsetZeroBody
    have hrel₀ : StateRelLM3_1 b (mkFourLocalScalarAnnealPre b ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU8Decl rawPtrConstU8Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    obtain ⟨⟨s₁, hs₁, hget₁⟩, m₁, tf₁, msc, hm₁, htf₁, hrel_msc, hval₁⟩ :=
      step_binOp_offset_scalar_zero_correspondence hrel₀ (fun _ h => nomatch h) rfl rfl
        (dstDecl := rawPtrConstU8Decl) (ptrDecl := rawPtrConstU8Decl)
        rfl rfl rfl rfl (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
        (fun tf _ => constUsize_wellTyped b tf 0 (by decide))
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (by rintro ⟨⟩) rfl (sc_rhs := ⟨0, 8⟩) rfl rfl
    have hmsc_eq : msc = lm31Scalar0U64 := scalarInt_eq_of_scalarRel hrel_msc lm31_scalarRel0U64
    subst hmsc_eq
    exact ⟨s₁, m₁, tf₁, hrel₀, hs₁, hget₁, hm₁, htf₁, hval₁⟩
  · -- Part (3): `lm31NullOffsetOneBody`
    let b := lm31NullOffsetOneBody
    have hrel₀ : StateRelLM3_1 b (mkFourLocalScalarAnnealPre b ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU8Decl rawPtrConstU8Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    obtain ⟨_, ha_ub, m₁, hm₁⟩ :=
      step_binOp_offset_scalar_nonzero_simulation hrel₀ (fun _ h => nomatch h) rfl rfl
        (dstDecl := rawPtrConstU8Decl) (ptrDecl := rawPtrConstU8Decl)
        rfl rfl rfl (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
        (fun tf _ => constUsize_wellTyped b tf 1 (by decide))
        (fun tf htf => mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1)
        rfl (sc_rhs := ⟨1, 8⟩) rfl (by decide) (by decide)
    exact ⟨m₁, hrel₀, ha_ub, hm₁⟩

/-- `Runtime(PostCleanup)` MIR body taking `_2 = &raw mut _1`
(`e.perm = .active`, `offsetBytes = 0`) and reborrowing `_3 = &raw mut (*_2)`. -/
def lm31RawPtrDerefZeroBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_deref_zero"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.rawPtr .mut (derefLocal 2)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body taking `_2 = &raw const _1`
(`e.perm = .frozen`) and forming `_3 = &raw mut (*_2)`. -/
def lm31RawPtrDerefFrozenMutBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_deref_frozen_mut"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.rawPtr .mut (derefLocal 2)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_rawPtr_deref_zero_and_perm_correspondence_real_steps`**:
Concrete real-step witnesses for RFC 2582 `&raw mut (*_2)` zero-offset
correspondence (`step_rawPtr_deref_zero_offset_correspondence`) and for
`&raw mut (*_2)` over a frozen parent
(`step_rawPtr_deref_perm_correspondence`):

1. **Zero-offset active reborrow (`lm31RawPtrDerefZeroBody`)**: after
   `_2 = &raw mut _1` (`_1 = 42_u64`), `_3 = &raw mut (*_2)` steps cleanly in
   both Anneal and `lean-miri` (storing `annealStackBaseAddr lm31AllocId1` in
   `_3`).
2. **Mutable raw reborrow of frozen parent (`lm31RawPtrDerefFrozenMutBody`)**:
   after `_2 = &raw const _1` (`e.perm = .frozen`), `_3 = &raw mut (*_2)` steps
   cleanly in BOTH machines without a Tree Borrows access: Anneal stores
   `{ allocId := 1, offsetBytes := 0 }` in `_3` (no longer raising spurious UB)
   and `lean-miri` stores `annealStackBaseAddr lm31AllocId1` in `_3`. -/
theorem wit_lm3_1_rawPtr_deref_zero_and_perm_correspondence_real_steps :
    -- (1) Zero-offset correspondence on `&raw mut (*_2)` (`e.perm = .active`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31RawPtrDerefZeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩))))) ∧
    -- (2) `&raw mut (*_2)` (`e.perm = .frozen`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (borTag : Miri.Memory.BorTag),
      let b := lm31RawPtrDerefFrozenMutBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
            ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1),
              .concrete lm31AllocId1 borTag⟩))))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  refine ⟨?_, ?_⟩
  · -- Part (1): `lm31RawPtrDerefZeroBody`
    let b := lm31RawPtrDerefZeroBody
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl
        rawPtrMutU64Decl ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf,
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf =>
        ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
         mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty
        lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    have hcorr := step_rawPtr_deref_zero_offset_correspondence hrel₁ hphase rfl rfl
      (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl)
      rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)
      (fun ptrVal e hp he _ => by
        have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
        cases he with
        | tail _ h => cases h
        | head _ =>
          subst hp'
          exact ⟨rfl, by rintro ⟨⟩, fun ⟨h, _⟩ => nomatch h⟩)
    obtain ⟨⟨s₂, hs₂, hget₂⟩, m₂, tf₂, borTag, hm₂, htf₂, hval₂⟩ :=
      hcorr.2 { allocId := 1, offsetBytes := 0 } _ rfl (.head _) rfl (by rintro ⟨⟩)
    exact ⟨s₁, s₂, m₁, m₂, tf₂, borTag, hs₁, hm₁, hrel₁, hs₂, hget₂, hm₂, htf₂, hval₂⟩
  · -- Part (2): `lm31RawPtrDerefFrozenMutBody`
    let b := lm31RawPtrDerefFrozenMutBody
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrConstU64Decl
        rawPtrMutU64Decl ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf,
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf =>
        ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
         mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty
        lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    obtain ⟨⟨s₂, hs₂, hget₂⟩, m₂, tf₂, borTag, hm₂, htf₂, hval₂⟩ :=
      step_rawPtr_deref_perm_correspondence hrel₁ hphase rfl rfl
        (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (by rintro ⟨⟩) (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl
        (.head _) rfl (Or.inr ⟨rfl, rfl⟩)
    have haddr_eq : annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0 =
        annealStackBaseAddr lm31AllocId1 := by simp
    change (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
      some (.live (.immediate (.scalar
        (Miri.Memory.Scalar.fromPointer annealTargetDataLayout
          ⟨Miri.ABI.Size.ofBytes (annealStackBaseAddr lm31AllocId1 + UInt64.ofNat 0),
            .concrete lm31AllocId1 borTag⟩)))) at hval₂
    rw [haddr_eq] at hval₂
    exact ⟨s₁, s₂, m₁, m₂, tf₂, borTag, hs₁, hm₁, hrel₁, hs₂, hget₂, hm₂, htf₂, hval₂⟩

/-! ## 9. Multi-Block `Offset(..., 0)` + `Assert`/`SwitchInt`/`Return(*mut T)`,
Raw-Pointer Comparisons, and `UnOp.PtrMetadata` Real-Step Witnesses -/

/-- `()` unit type and mutable local declaration for `PtrMetadata` witnesses. -/
def unitTyLM31 : Ty := { kind := .tuple .nil, layoutIdx := 0 }
def unitDeclLM31 : LocalDecl := { mutability := .mut, ty := unitTyLM31, debugName := none }

/-- `true` as a 1-byte `lean-miri` boolean scalar. -/
def lm31ScalarTrue : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofBool true

theorem lm31_scalarRelTrue : ScalarRel ⟨1, 1⟩ lm31ScalarTrue :=
  ⟨Or.inl rfl, by decide, rfl, rfl⟩

/-- Construct a concrete intra-frame `MachineState` at `(blockIdx, stmtIdx)`. -/
private def mkWitBlockState (body : CapturedMir) (blockIdx stmtIdx : Nat)
    (locals : List LocalSlot) (borrows : List BorrowEntry) (nextTag : Nat) :
    MachineState :=
  { frame := { blockIdx := blockIdx, stmtIdx := stmtIdx, locals := locals }
    memory := { (initMachineState body []).memory with
                  borrows := borrows, nextTag := nextTag } }

private theorem stepObsRelLM3_1_of_anneal_emitStep
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {obs : MirObs} {s' : MachineState}
    (hsim : StepObsRelLM3_1 body m allocMap aRes mRes)
    (ha : aRes = .emitStep obs s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap := by
  cases hsim with
  | emitStep obs₁ _ m' hrel =>
    cases obs <;> cases obs₁
    · injection ha with htau; injection htau with hs; subst hs; exact ⟨m', rfl, hrel⟩
    · cases ha
    · cases ha
    · injection ha with _ hfn
      have hrun := congrFun hfn ()
      injection hrun with hs
      subst hs
      exact ⟨m', rfl, hrel⟩
  | retRoot _ _ _ _ _ _ _ _ _ => cases obs <;> cases ha
  | ub _ _ => cases obs <;> cases ha

private theorem step_terminator_assert_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    {cond : MirAst.Operand} {expected : Bool} {target : BasicBlockIdx}
    (hterm : bb.terminator.kind = .assert cond expected target .unreachable)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf₀, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none] at hstep
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .Assert (translateOperand cond) expected
          (.BoundsCheck (translateOperand cond) (translateOperand cond))
          target .Unreachable } := by
    unfold translateTerminator; rw [hterm]; rfl
  rw [hm_term] at hstep
  let act : Miri.Interpreter.RvalueM AnnealStepState Bool := do
    let opTy ← annealEvalOperand body.localDecls body.layouts (translateOperand cond) none
    let imm ← annealReadImmediate opTy
    let sc ← match imm.imm.toScalar with
      | .ok sc => pure sc
      | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
    match sc.toBool with
    | .ok b => return b
    | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
  have hpres : RvaluePreservesAllImm act :=
    rvaluePreservesAllImm_bind
      (annealEvalOperand_any_preserves body.localDecls body.layouts (translateOperand cond) none)
      (fun opTy => rvaluePreservesAllImm_bind (annealReadImmediate_preserves opTy)
        (fun imm => by
          dsimp only []
          cases imm.imm.toScalar with
          | error e =>
            refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_throw _) (fun sc' => ?_)
            cases sc'.toBool with
            | ok b => exact rvaluePreservesAllImm_pure b
            | error e' => exact rvaluePreservesAllImm_throw _
          | ok sc =>
            refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure sc) (fun sc' => ?_)
            cases sc'.toBool with
            | ok b => exact rvaluePreservesAllImm_pure b
            | error e => exact rvaluePreservesAllImm_throw _))
  dsimp only [Miri.Interpreter.ControlFlow.evalTerminator, annealStepHooks] at hstep
  cases hact : act m with
  | error err m_ev =>
    have hread' : (annealTerminatorHooks body.localDecls body.layouts).8 ()
        (translateOperand cond) m = (m_ev, .error err) := by
      change Miri.Interpreter.runRvalue act m = _
      unfold Miri.Interpreter.runRvalue; rw [hact]
    simp only [hread', Except.map] at hstep
    cases hstep
  | ok b m_ev =>
    obtain ⟨_, hstk⟩ := hpres m b m_ev hact
    obtain ⟨tf_ev, htf_ev, _, himm_ev⟩ := hstk tf₀ hframes
    have hread' : (annealTerminatorHooks body.localDecls body.layouts).8 ()
        (translateOperand cond) m = (m_ev, .ok b) := by
      change Miri.Interpreter.runRvalue act m = _
      unfold Miri.Interpreter.runRvalue; rw [hact]
    simp only [hread'] at hstep
    dsimp only [Id.run, bind, Except.bind, pure, Except.pure,
      Miri.Interpreter.TerminatorHooks.ignoreOptionalOverflowChecks,
      Miri.Interpreter.ControlFlow.isOptionalOverflowCheck] at hstep
    by_cases h_eq : (expected == b) = true
    · simp only [Bool.and_false, Bool.false_or, h_eq, ↓reduceIte] at hstep
      unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation at hstep
      rw [stack_currentFrame?_singleton _ tf_ev htf_ev] at hstep
      dsimp only [Except.map] at hstep
      injection hstep with hm'_eq _
      subst hm'_eq
      rw [htf_ev]
      intro tf₁ tf₂ h₁ h₂ k hk
      rw [hframes] at h₁
      injection h₁ with h₁'; injection h₁' with h₁''; subst h₁''
      dsimp only [Array.pop, Array.push] at h₂
      injection h₂ with h₂'; injection h₂' with h₂''; subst h₂''
      exact himm_ev k hk
    · have h_false : (expected == b) = false := Bool.eq_false_iff.mpr h_eq
      simp only [Bool.and_false, Bool.false_or, h_false, Bool.false_eq_true, ↓reduceIte,
        annealTerminatorHooks, Except.map] at hstep
      cases hstep

private theorem step_terminator_switchInt_one_preserves
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt_none : get? bb.statements s.frame.stmtIdx = none)
    {discr : MirAst.Operand} {v₀ b₀ oth : Nat}
    (hterm : bb.terminator.kind = .switchInt discr { branches := [(v₀, b₀)], otherwise := oth })
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    ∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k := by
  obtain ⟨tf₀, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  rw [miri_step_at_terminator hframes hfr.body_eq hfr.location_eq hbb hstmt_none] at hstep
  have hm_term : translateTerminator bb.terminator =
      { sourceInfo := defaultSourceInfo,
        kind := .SwitchInt (translateOperand discr)
          (translateSwitchTargets { branches := [(v₀, b₀)], otherwise := oth }) } := by
    unfold translateTerminator; rw [hterm]; rfl
  rw [hm_term] at hstep
  let actDisc : Miri.Interpreter.RvalueM AnnealStepState
      (Miri.Interpreter.RvalueImmTy AnnealProv) := do
    let opTy ← annealEvalOperand body.localDecls body.layouts (translateOperand discr) none
    annealReadImmediate opTy
  have hpresDisc : RvaluePreservesAllImm actDisc :=
    rvaluePreservesAllImm_bind
      (annealEvalOperand_any_preserves body.localDecls body.layouts (translateOperand discr) none)
      (fun opTy => annealReadImmediate_preserves opTy)
  dsimp only [annealStepHooks] at hstep
  unfold Miri.Interpreter.ControlFlow.evalTerminator at hstep
  dsimp only [] at hstep
  have hdisc_def : (annealTerminatorHooks body.localDecls body.layouts).evalDiscriminant ()
      (translateOperand discr) m = Miri.Interpreter.runRvalue actDisc m := rfl
  simp only [hdisc_def] at hstep
  cases hact : actDisc m with
  | error err m_ev =>
    unfold Miri.Interpreter.runRvalue at hstep
    simp only [hact, Except.map] at hstep
    cases hstep
  | ok val m_ev =>
    obtain ⟨_, hstk₁⟩ := hpresDisc m val m_ev hact
    obtain ⟨tf_ev, htf_ev, _, himm_ev⟩ := hstk₁ tf₀ hframes
    unfold Miri.Interpreter.runRvalue at hstep
    simp only [hact] at hstep
    dsimp only [Id.run] at hstep
    rw [translateSwitchTargets_cases] at hstep
    simp only [List.map, List.forIn_toArray, List.forIn_cons, List.forIn_nil, pure_bind] at hstep
    let actCmp : Miri.Interpreter.RvalueM AnnealStepState Bool := do
      let caseScalar ←
        match Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 v₀) val.layout.layout.size with
        | .ok sc => pure sc
        | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
      let result ←
        Miri.Interpreter.ScalarOps.binary
          (annealScalarOpsHooks body.localDecls body.layouts) () .Eq
          val ⟨.scalar caseScalar, val.layout⟩
      let resScalar ←
        match result.imm.toScalar with
        | .ok sc => pure sc
        | .error err => throw (Miri.Interpreter.ScalarOps.immediateError err)
      match resScalar.toBool with
      | .ok b => return b
      | .error err => throw (Miri.Interpreter.ScalarOps.scalarError err)
    have hpresCmp : RvaluePreservesAllImm actCmp := by
      dsimp only [actCmp]
      cases Miri.Memory.Scalar.fromUInt (BitVec.ofNat 128 v₀) val.layout.layout.size with
      | error e =>
        refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_throw _) (fun csc' =>
          rvaluePreservesAllImm_bind
            (scalarOps_binary_preserves body.localDecls body.layouts .Eq val ⟨.scalar csc', val.layout⟩)
            (fun result => ?_))
        cases result.imm.toScalar with
        | error e' =>
          refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_throw _) (fun rsc' => ?_)
          cases rsc'.toBool with
          | ok b => exact rvaluePreservesAllImm_pure b
          | error e'' => exact rvaluePreservesAllImm_throw _
        | ok rsc =>
          refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure rsc) (fun rsc' => ?_)
          cases rsc'.toBool with
          | ok b => exact rvaluePreservesAllImm_pure b
          | error e' => exact rvaluePreservesAllImm_throw _
      | ok csc =>
        refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure csc) (fun csc' =>
          rvaluePreservesAllImm_bind
            (scalarOps_binary_preserves body.localDecls body.layouts .Eq val ⟨.scalar csc', val.layout⟩)
            (fun result => ?_))
        cases result.imm.toScalar with
        | error e =>
          refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_throw _) (fun rsc' => ?_)
          cases rsc'.toBool with
          | ok b => exact rvaluePreservesAllImm_pure b
          | error e' => exact rvaluePreservesAllImm_throw _
        | ok rsc =>
          refine rvaluePreservesAllImm_bind (rvaluePreservesAllImm_pure rsc) (fun rsc' => ?_)
          cases rsc'.toBool with
          | ok b => exact rvaluePreservesAllImm_pure b
          | error e => exact rvaluePreservesAllImm_throw _
    have hcmp_def : (annealTerminatorHooks body.localDecls body.layouts).compareSwitchCase ()
        val v₀ m_ev = Miri.Interpreter.runRvalue actCmp m_ev := rfl
    simp only [hcmp_def] at hstep
    cases hcmp : actCmp m_ev with
    | error err m_c =>
      unfold Miri.Interpreter.runRvalue at hstep
      simp only [hcmp, Except.map] at hstep
      cases hstep
    | ok b m_c =>
      obtain ⟨_, hstk₂⟩ := hpresCmp m_ev b m_c hcmp
      obtain ⟨tf_c, htf_c, _, himm_c⟩ := hstk₂ tf_ev htf_ev
      unfold Miri.Interpreter.runRvalue at hstep
      simp only [hcmp] at hstep
      cases b <;>
        (dsimp only [bind, pure, Id.run] at hstep;
         unfold Miri.Interpreter.ControlFlow.goToBlock Miri.Interpreter.ControlFlow.setLocation
           at hstep;
         rw [stack_currentFrame?_singleton _ tf_c htf_c] at hstep;
         dsimp only [Except.map] at hstep;
         injection hstep with hm'_eq _;
         subst hm'_eq;
         rw [htf_c];
         intro tf₁ tf₂ h₁ h₂ k hk;
         rw [hframes] at h₁;
         injection h₁ with h₁'; injection h₁' with h₁''; subst h₁'';
         dsimp only [Array.pop, Array.push] at h₂;
         injection h₂ with h₂'; injection h₂' with h₂''; subst h₂'';
         exact himm_c k (himm_ev k hk))

/-- Multi-block `Runtime(PostCleanup)` MIR body returning `*mut u64`:
```text
bb0: _2 = &raw mut _1;
     *_2 = const 99_u64;
     _0 = Offset(move _2, const 0_usize);
     assert(copy _3 == true) -> bb1;
bb1: switchInt(copy _3) -> [1: bb2, otherwise: bb0];
bb2: return;
``` -/
def lm31BranchOffsetReturnPtrBody : CapturedMir where
  defPath := "lm_3_1_witness::branch_offset_zero_return_ptr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [rawPtrMutU64Decl, u64Decl, rawPtrMutU64Decl, boolDeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (derefLocal 2) (.use (.constant (constU64 99)))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .offset (.move (local_ 2)) (.constant (constUsizeLM31 0))))],
      terminator := mkTerm (.assert (.copy (local_ 3)) true 1 .unreachable),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm (.switchInt (.copy (local_ 3))
        { branches := [(1, 2)], otherwise := 0 }),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Anneal pre-state for `lm31BranchOffsetReturnPtrBody` (`_1 = 42_u64`,
`_3 = true`, `_0` and `_2` `.uninit`). -/
def lm31BranchOffsetReturnPtrAnnealPre : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := 0
        locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init (.scalar ⟨1, 1⟩)] }
    memory := (initMachineState lm31BranchOffsetReturnPtrBody []).memory }

/-- `lean-miri` root frame matching `lm31BranchOffsetReturnPtrAnnealPre`. -/
def lm31BranchOffsetReturnPtrMiriFramePre :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm31BranchOffsetReturnPtrBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy rawPtrMutU64Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
        layout := some (translateTy u64Ty) },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate (.scalar (.fromScalarInt lm31ScalarTrue))),
        layout := some (translateTy boolTyLM31) }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- `lean-miri` step state matching `lm31BranchOffsetReturnPtrAnnealPre`. -/
def lm31BranchOffsetReturnPtrMiriPre : AnnealStepState :=
  { stack := ⟨#[lm31BranchOffsetReturnPtrMiriFramePre]⟩, machine := AnnealMachine.empty }

theorem lm31BranchOffsetReturnPtr_stateRel_pre :
    StateRel lm31BranchOffsetReturnPtrBody
      lm31BranchOffsetReturnPtrAnnealPre lm31BranchOffsetReturnPtrMiriPre := by
  refine StateRel.mk lm31BranchOffsetReturnPtrMiriFramePre rfl rfl
    ⟨translateTy rawPtrMutU64Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 =>
    have hs : slot = .uninit := by
      simpa [lm31BranchOffsetReturnPtrAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm31BranchOffsetReturnPtrMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = u64Decl := by
      simpa [lm31BranchOffsetReturnPtrBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨42, 8⟩) := by
      simpa [lm31BranchOffsetReturnPtrAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42))),
          layout := some (translateTy u64Ty) } := by
      simpa [lm31BranchOffsetReturnPtrMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
  | 3 =>
    have hd : decl = boolDeclLM31 := by
      simpa [lm31BranchOffsetReturnPtrBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨1, 1⟩) := by
      simpa [lm31BranchOffsetReturnPtrAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm31ScalarTrue))),
          layout := some (translateTy boolTyLM31) } := by
      simpa [lm31BranchOffsetReturnPtrMiriFramePre] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ (some (translateTy boolTyLM31)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRelTrue rfl
        (fun _ => ⟨rfl, Or.inr rfl⟩) (fun h => nomatch h)⟩)
  | _ + 4 => simp [lm31BranchOffsetReturnPtrBody, get?] at hdecl

private theorem lm31BranchOffsetReturnPtr_all_immediate_pre :
    ∀ tf, lm31BranchOffsetReturnPtrMiriPre.stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 =>
    simp [lm31BranchOffsetReturnPtrMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 4 => simp [lm31BranchOffsetReturnPtrMiriFramePre] at hmls

/-- **`wit_lm3_1_branch_offset_zero_and_return_rawPtr_real_steps`**:
Complete 6-step multi-block execution of `lm31BranchOffsetReturnPtrBody` from
pointer-free `StateRel` (`_1 = 42_u64`, `_3 = true`) across `stepMirFn` and
`Miri.Interpreter.Step.step` (`annealStepHooks`):
1. `bb0[0]`: `_2 = &raw mut _1` promotes `_1` into `lm31AllocId1`
   (`step_rawPtr_addrOf_simulation`);
2. `bb0[1]`: `*_2 = const 99_u64` writes `99_u64` through `_2`
   (`step_deref_write_simulation`);
3. `bb0[2]`: `_0 = Offset(move _2, const 0_usize)` offsets `_2 : *mut u64`
   (`stride = 8`) by `0` with destructive `move _2`
   (`step_binOp_offset_zero_any_stride_lm3_1_simulation`);
4. `bb0` terminator: `Assert(copy _3 == true -> bb1, unreachable)` jumps to
   `bb1` (`step_terminator_assert_lm3_1_simulation`);
5. `bb1` terminator: `SwitchInt(copy _3 : [1 -> bb2, otherwise -> bb0])` emits
   `MirObs.event 1` in Anneal and jumps to `bb2`
   (`step_terminator_switchInt_lm3_1_simulation`);
6. `bb2` terminator: `Return` of `_0 : *mut u64` pops `lean-miri`'s root frame
   in lockstep with Anneal's `.retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8)`,
   extracting `mptr` with `PtrRel allocMap₂ { allocId := 1, offsetBytes := 0 } mptr`
   via `step_terminator_return_rawPtr_lm3_1_simulation` and
   `StepObsRelLM3_1.retNormal_rel`. -/
theorem wit_lm3_1_branch_offset_zero_and_return_rawPtr_real_steps :
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState)
      (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (allocMap₂ : List AllocMapEntry)
      (mptr : Miri.Memory.Pointer AnnealProv),
      let b := lm31BranchOffsetReturnPtrBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b lm31BranchOffsetReturnPtrAnnealPre = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () lm31BranchOffsetReturnPtrMiriPre = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      get? s₃.frame.locals 2 = some .uninit ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      s₄.frame.blockIdx = 1 ∧
      stepMirFn b s₄ = .emitStep (.event 1) s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      s₅.frame.blockIdx = 2 ∧
      StateRelLM3_1 b s₅ m₅ allocMap₂ ∧
      stepMirFn b s₅ =
        .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₅.memory ∧
      Miri.Interpreter.Step.step hooks () m₅ = ({ m₅ with stack := ⟨#[]⟩ }, .ok true) ∧
      annealControlHooks.returnOperand () m₅ =
        (m₅, .ok (.immediate (.scalar
          (Miri.Memory.Scalar.fromPointer annealTargetDataLayout mptr)))) ∧
      PtrRel allocMap₂ { allocId := 1, offsetBytes := 0 } mptr := by
  let b := lm31BranchOffsetReturnPtrBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  have himm₀ : ∀ tf, lm31BranchOffsetReturnPtrMiriPre.stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf =>
      ⟨lm31BranchOffsetReturnPtr_all_immediate_pre tf htf 2,
       lm31BranchOffsetReturnPtr_all_immediate_pre tf htf 1⟩
  -- Step 1 (`bb0[0]`): `_2 = &raw mut _1`
  let s₁ := mkWitBlockState b 0 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init (.scalar ⟨1, 1⟩)] bor 2
  have hs₁ : stepMirFn b lm31BranchOffsetReturnPtrAnnealPre = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation lm31BranchOffsetReturnPtr_stateRel_pre hphase
      rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
      AllocIdSupplyReady.empty) hs₁
  have htag₀ : lm31BranchOffsetReturnPtrAnnealPre.memory.nextTag = 1 := rfl
  have hid₀ : (⟨lm31BranchOffsetReturnPtrMiriPre.machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne
    lm31BranchOffsetReturnPtr_stateRel_pre rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (lm31BranchOffsetReturnPtr_all_immediate_pre _ rfl k)
  -- Step 2 (`bb0[1]`): `*_2 = const 99_u64`
  let s₂ := mkWitBlockState b 0 2
    [.uninit, .init (.scalar ⟨99, 8⟩), .init ptr0, .init (.scalar ⟨1, 1⟩)] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨allocMap₂, hsim₂⟩ := step_deref_write_simulation hrel₁ hphase rfl rfl
    rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (valTy := u64Ty) rfl
    (fun tf₁ _ => constU64_wellTyped b tf₁ 99 (by decide))
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
  obtain ⟨_, himm₂_step⟩ := step_assign_use_preserves hrel₁ (by rintro _ ⟨⟩) rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3 (`bb0[2]`): `_0 = Offset(move _2, const 0_usize)` (`stride = 8`)
  let s₃ := mkWitBlockState b 0 3
    [.init ptr0, .init (.scalar ⟨99, 8⟩), .uninit, .init (.scalar ⟨1, 1⟩)] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ :=
    stepMirFn_binOp_offset_const_eq
      (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
      u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (hinb := Or.inl ⟨rfl, rfl⟩)
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
    (step_binOp_offset_zero_any_stride_lm3_1_simulation hrel₂ hphase (Or.inr rfl) rfl rfl
      (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (rhsTy := usizeTyLM31)
      rfl rfl rfl rfl rfl (Or.inl rfl)
      (fun tf₂ _ => constUsize_wellTyped b tf₂ 0 (by decide))
      (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 0 (by decide), himm₂ tf₂ htf₂ 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)
      (fun locals_mid sc _ _ ha_r => by
        change evalOperand locals_mid (.constant (constUsizeLM31 0)) _ _ _ _ = _ at ha_r
        injection ha_r with hv _; injection hv with hsc; rw [← hsc])
      (fun ptrVal e _ hp he _ _ => by
        have hp' : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hp
        obtain ⟨_, _, _, _, _, _, _, _, _, hbor_eq₂, _, _⟩ := id hrel₂
        have hbor₂ : s₂.memory.borrows =
            [{ tag := 1, targetLocal := 1, targetProjection := .nil, perm := .active }] := rfl
        have hmem_b : e.toBorrowEntry ∈ s₂.memory.borrows := by
          rw [hbor_eq₂]; exact List.mem_map_of_mem he
        rw [hbor₂] at hmem_b
        have hb_eq := List.mem_singleton.mp hmem_b
        have heperm : e.perm = .active := congrArg BorrowEntry.perm hb_eq
        subst hp'
        exact ⟨by rw [heperm]; rintro ⟨⟩, Or.inl rfl⟩)
      ⟨8, by decide, rfl⟩) hs₃
  obtain ⟨_, himm₃_step⟩ := step_assign_binOp_offset_any_preserves hrel₂ rfl rfl hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4 (`bb0` terminator): `Assert(copy _3 == true -> bb1, unreachable)`
  let s₄ := mkWitBlockState b 1 0
    [.init ptr0, .init (.scalar ⟨99, 8⟩), .uninit, .init (.scalar ⟨1, 1⟩)] bor 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_terminator_assert_lm3_1_simulation hrel₃ hphase rfl rfl rfl rfl
      (condTy := boolTyLM31) rfl
      (fun tf₃ htf₃ => .copyLocal 3 boolDeclLM31 rfl (by decide)
        (himm₃ tf₃ htf₃ 3 (by decide)))) hs₄
  have himm₄_step := step_terminator_assert_preserves hrel₃ rfl rfl rfl hm₄
  have himm₄ : ∀ tf₄, m₄.stack.frames = #[tf₄] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₄ k := by
    intro tf₄ htf₄ k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm₄_step tf₃ tf₄ htf₃ htf₄ k (himm₃ tf₃ htf₃ k hne)
  -- Step 5 (`bb1`): `SwitchInt(copy _3 : [1 -> bb2, otherwise -> bb0])`
  let s₅ := mkWitBlockState b 2 0
    [.init ptr0, .init (.scalar ⟨99, 8⟩), .uninit, .init (.scalar ⟨1, 1⟩)] bor 2
  have hs₅ : stepMirFn b s₄ = .emitStep (.event 1) s₅ := rfl
  obtain ⟨m₅, hm₅, hrel₅⟩ := stepObsRelLM3_1_of_anneal_emitStep
    (step_terminator_switchInt_lm3_1_simulation hrel₄ hphase rfl rfl rfl rfl
      (ty := boolTyLM31) (Or.inl rfl)
      (fun tf₄ htf₄ => .copyLocal 3 boolDeclLM31 rfl (by decide)
        (himm₄ tf₄ htf₄ 3 (by decide)))
      (fun v blk hmem => by
        simp only [List.mem_singleton, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩
        exact ⟨by decide, fun _ => Or.inr rfl⟩)) hs₅
  have himm₅_step := step_terminator_switchInt_one_preserves hrel₄ rfl rfl rfl hm₅
  have himm₅_0 : ∀ tf₅, m₅.stack.frames = #[tf₅] → IsImmediateFrameLocal tf₅ 0 := by
    intro tf₅ htf₅; obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
    exact himm₅_step tf₄ tf₅ htf₄ htf₅ 0 (himm₄ tf₄ htf₄ 0 (by decide))
  -- Step 6 (`bb2` terminator): `Return` of `_0 : *mut u64`
  have hsim₆ := step_terminator_return_rawPtr_lm3_1_simulation hrel₅ hphase
    rfl rfl rfl rfl rfl (decl0 := rawPtrMutU64Decl) rfl rfl himm₅_0
  have hs₆ : stepMirFn b s₅ =
      .retNormal (.ptr { allocId := 1, offsetBytes := 0 } 8) s₅.memory := rfl
  rw [hs₆] at hsim₆
  obtain ⟨decl₀, imm₀, hdecl₀, hop₀, himmRel₀, hm₆⟩ := StepObsRelLM3_1.retNormal_rel hsim₆
  have hd₀ : decl₀ = rawPtrMutU64Decl := Option.some.inj hdecl₀.symm
  subst hd₀
  cases himmRel₀ with
  | of_immediateRel hbase => cases hbase
  | rawPtr _ _ _ mptr _ hptrRel =>
    exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, allocMap₂, mptr,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, rfl, hs₄, hm₄, rfl, hs₅, hm₅, rfl, hrel₅,
      hs₆, hm₆, hop₀, hptrRel⟩

/-- `Runtime(PostCleanup)` MIR body comparing provenance-less `_1 : *const u64`
with itself via `BinOp.Eq` (`_2 = Eq(copy _1, copy _1)`). -/
def lm31RawPtrCmpScalarBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_cmp_scalar"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, boolDeclLM31, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.binaryOp .eq (.copy (local_ 1)) (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body taking `_2 = &raw const _1` and comparing
the tracked raw pointer `_2` with itself (`_3 = Eq(copy _2, copy _2)`). -/
def lm31RawPtrCmpPtrBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_cmp_ptr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, boolDeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.binaryOp .eq (.copy (local_ 2)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `_2 = move _1 as *const u8`
(`CastKind.PtrToPtr` with destructive `move _1`) on null `_1 = 0 as *const u64`. -/
def lm31MoveNullPtrToPtrBody : CapturedMir where
  defPath := "lm_3_1_witness::move_null_ptr_to_ptr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, rawPtrConstU8Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.cast .ptrToPtr (.move (local_ 1)) rawPtrConstU8Ty))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing
`_2 = Offset(move _1, const 0_usize)` on null `_1 = 0 as *const u64`
(`stride = 8`). -/
def lm31MoveNullOffsetZeroBody : CapturedMir where
  defPath := "lm_3_1_witness::move_null_offset_zero"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.binaryOp .offset (.move (local_ 1)) (.constant (constUsizeLM31 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `_3 = PtrMetadata(copy _2)` on
`.uninit` `_2 : *const u64` (lockstep UB). -/
def lm31PtrMetadataUninitBody : CapturedMir where
  defPath := "lm_3_1_witness::ptr_metadata_uninit"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl, unitDeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 3) (.unaryOp .ptrMetadata (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `_3 = PtrMetadata(copy _1)` on
initialized `_1 = 0 as *const u64` (Anneal `.unsupported` vs. `lean-miri` `()`
write). -/
def lm31PtrMetadataThinBody : CapturedMir where
  defPath := "lm_3_1_witness::ptr_metadata_thin"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl, unitDeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 3) (.unaryOp .ptrMetadata (.copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_rawPtr_cmp_and_ptrMetadata_real_steps`**:
Concrete real-step witnesses exercising raw-pointer relational comparisons,
move-operand provenance-less `PtrToPtr`/`Offset(..., 0)`, and
`UnOp.PtrMetadata`:
1. **`step_rawPtr_cmp_scalar_lm3_1_simulation`**: `_2 = Eq(copy _1, copy _1)` on
   null `_1 = 0 as *const u64` steps in lockstep to `_2 = true` across
   `StateRelLM3_1`.
2. **`step_rawPtr_cmp_ptr_divergence`**: after `_2 = &raw const _1` (`_1 = 42`),
   `_3 = Eq(copy _2, copy _2)` steps in BOTH machines (Anneal storing
   `boolToScalar aRes`, `lean-miri` storing `.fromScalarInt (.ofBool b)`).
3. **`step_cast_ptrToPtr_move_scalar_correspondence`**:
   `_2 = move _1 as *const u8` on `_1 = 0 as *const u64` steps in BOTH machines,
   storing `⟨0, 8⟩` (Anneal) and `lm31Scalar0U64` (`lean-miri`) in `_2`.
4. **`step_binOp_offset_move_scalar_zero_correspondence`**:
   `_2 = Offset(move _1, const 0_usize)` on `_1 = 0 as *const u64` (`stride = 8`)
   steps in BOTH machines, storing `⟨0, 8⟩` (Anneal) and `lm31Scalar0U64`
   (`lean-miri`) in `_2`.
5. **`step_unaryOp_ptrMetadata_thin_rawPtr_ub_simulation` and
   `step_unaryOp_ptrMetadata_thin_rawPtr_correspondence`**:
   `_3 = PtrMetadata(copy _2)` on `.uninit` `_2` raises UB in lockstep, and
   `_3 = PtrMetadata(copy _1)` on initialized `_1 = 0 as *const u64` steps in
   BOTH machines (Anneal storing `.init .unit`, `lean-miri` writing the `()` ZST
   immediate `.uninit` into `_3`). -/
theorem wit_lm3_1_rawPtr_cmp_and_ptrMetadata_real_steps :
    -- (1) Provenance-less `Eq(copy _1, copy _1)` lockstep simulation
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState),
      let b := lm31RawPtrCmpScalarBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨1, 1⟩))) ∧
    -- (2) Tracked raw-pointer `Eq(copy _2, copy _2)` divergence
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (aRes eqRes : Bool),
      let b := lm31RawPtrCmpPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 3 = some (.init (.scalar (boolToScalar aRes))) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool eqRes)))))) ∧
    -- (3) Move-operand provenance-less `PtrToPtr` divergence
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31MoveNullPtrToPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (4) Move-operand null `Offset(..., 0)` divergence (`stride = 8`)
    (∃ (s₁ : MachineState) (m₁ : AnnealStepState)
      (tf₁ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let b := lm31MoveNullOffsetZeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      get? s₁.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      m₁.stack.frames = #[tf₁] ∧
      (tf₁.locals[2]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt lm31Scalar0U64))))) ∧
    -- (5) `PtrMetadata` UB simulation on `.uninit` vs. thin-pointer divergence
    (∃ (st' : MachineState) (m_ub m_ok : AnnealStepState) (msg : String)
      (tf_ok : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit),
      let bu := lm31PtrMetadataUninitBody
      let bt := lm31PtrMetadataThinBody
      let su := mkFourLocalScalarAnnealPre bu ⟨0, 8⟩
      let mu := mkFourLocalScalarMiriPre bu u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let st := mkFourLocalScalarAnnealPre bt ⟨0, 8⟩
      let mt := mkFourLocalScalarMiriPre bt u64Ty rawPtrConstU64Ty lm31Scalar0U64
      stepMirFn bu su = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks bu.localDecls bu.layouts) () mu =
        (m_ub, .error (.undefinedBehavior msg)) ∧
      stepMirFn bt st = .step st' ∧
      get? st'.frame.locals 3 = some (.init .unit) ∧
      Miri.Interpreter.Step.step (annealStepHooks bt.localDecls bt.layouts) () mt =
        (m_ok, .ok true) ∧
      m_ok.stack.frames = #[tf_ok] ∧
      (tf_ok.locals[3]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate .uninit))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Part (1): `lm31RawPtrCmpScalarBody`
    let b := lm31RawPtrCmpScalarBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU64Decl boolDeclLM31 u64Decl
        ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨1, 1⟩), .uninit] [] 1
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_cmp_scalar_lm3_1_simulation hrel₀ (fun _ h => nomatch h)
        (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) rfl rfl
        (dstDecl := boolDeclLM31) (lhsDecl := rawPtrConstU64Decl)
        (rhsDecl := rawPtrConstU64Decl) rfl rfl rfl rfl rfl rfl
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (fun _ => slot_ptr_ne_scalar.symm) (fun _ => slot_ptr_ne_scalar.symm)) hs₁
    exact ⟨s₁, m₁, hs₁, hm₁, hrel₁, rfl⟩
  · -- Part (2): `lm31RawPtrCmpPtrBody`
    let b := lm31RawPtrCmpPtrBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
    have hrel₀ : StateRel b s₀ m₀ :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrConstU64Decl boolDeclLM31
        ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (by rintro ⟨⟩) (by rintro ⟨⟩)
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, m₀.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf =>
        ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
         mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : s₀.memory.nextTag = 1 := rfl
    have hid₀ : (⟨m₀.machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    obtain ⟨⟨s₂, aRes, hs₂, hget₂⟩, m₂, tf₂, eqRes, hm₂, htf₂, hval₂⟩ :=
      step_rawPtr_cmp_ptr_divergence hrel₁ hphase (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
        rfl rfl (dstDecl := boolDeclLM31) (lhsDecl := rawPtrConstU64Decl)
        (rhsDecl := rawPtrConstU64Decl) rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ =>
          ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide),
           himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (by rintro ⟨⟩) (ptrVal₁ := { allocId := 1, offsetBytes := 0 }) rfl
        ⟨by rintro ⟨⟩, by rintro ⟨⟩⟩ (fun h => absurd (congrFun h ⟨0, .nil⟩) (by nofun))
    exact ⟨s₁, s₂, m₁, m₂, tf₂, aRes, eqRes, hs₁, hm₁, hs₂, hget₂, hm₂, htf₂, hval₂⟩
  · -- Part (3): `lm31MoveNullPtrToPtrBody`
    let b := lm31MoveNullPtrToPtrBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU8Decl u64Decl
        ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    obtain ⟨⟨s₁, hs₁, hget₁⟩, m₁, tf₁, msc, hm₁, htf₁, hsc, hval₁⟩ :=
      step_cast_ptrToPtr_move_scalar_correspondence hrel₀ (fun _ h => nomatch h) rfl rfl
        (dstDecl := rawPtrConstU8Decl) (srcDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (by rintro ⟨⟩) (sc := ⟨0, 8⟩) rfl
    have hmsc : msc = lm31Scalar0U64 := scalarInt_eq_of_scalarRel hsc lm31_scalarRel0U64
    subst hmsc
    exact ⟨s₁, m₁, tf₁, hs₁, hget₁, hm₁, htf₁, hval₁⟩
  · -- Part (4): `lm31MoveNullOffsetZeroBody`
    let b := lm31MoveNullOffsetZeroBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl u64Decl
        ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    obtain ⟨⟨s₁, hs₁, hget₁⟩, m₁, tf₁, msc_out, hm₁, htf₁, hsc_out, hval₁⟩ :=
      step_binOp_offset_move_scalar_zero_correspondence hrel₀ (fun _ h => nomatch h) rfl rfl
        (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (rhsTy := usizeTyLM31)
        (sc_p := ⟨0, 8⟩) (sc_r := ⟨0, 8⟩)
        (locals_r := s₀.frame.locals.set 1 .uninit)
        rfl rfl rfl rfl rfl (Or.inl rfl)
        (fun tf _ => constUsize_wellTyped b tf 0 (by decide))
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (by rintro ⟨⟩) rfl rfl rfl
    have hmsc : msc_out = lm31Scalar0U64 := scalarInt_eq_of_scalarRel hsc_out lm31_scalarRel0U64
    subst hmsc
    exact ⟨s₁, m₁, tf₁, hs₁, hget₁, hm₁, htf₁, hval₁⟩
  · -- Part (5): `lm31PtrMetadataUninitBody` and `lm31PtrMetadataThinBody`
    let bu := lm31PtrMetadataUninitBody
    let su := mkFourLocalScalarAnnealPre bu ⟨0, 8⟩
    let mu := mkFourLocalScalarMiriPre bu u64Ty rawPtrConstU64Ty lm31Scalar0U64
    have hrelu : StateRelLM3_1 bu su mu [] :=
      (mkFourLocalScalar_stateRel bu u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        unitDeclLM31 ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hsu : stepMirFn bu su = .fail .ub := rfl
    obtain ⟨m_ub, msg, hm_ub⟩ := stepRelLM3_1_of_anneal_ub
      (step_unaryOp_ptrMetadata_thin_rawPtr_ub_simulation hrelu (fun _ h => nomatch h)
        (Or.inl rfl) rfl rfl (dstDecl := unitDeclLM31) (ptrDecl := rawPtrConstU64Decl)
        rfl rfl rfl (fun tf htf => mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2)
        (Or.inr rfl)) hsu
    let bt := lm31PtrMetadataThinBody
    let st := mkFourLocalScalarAnnealPre bt ⟨0, 8⟩
    let mt := mkFourLocalScalarMiriPre bt u64Ty rawPtrConstU64Ty lm31Scalar0U64
    have hrelt : StateRelLM3_1 bt st mt [] :=
      (mkFourLocalScalar_stateRel bt u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        unitDeclLM31 ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    obtain ⟨⟨st', hst, hget_st⟩, m_ok, tf_ok, hm_ok, htf_ok, hval_ok⟩ :=
      step_unaryOp_ptrMetadata_thin_rawPtr_correspondence hrelt (fun _ h => nomatch h)
        (Or.inl rfl) rfl rfl (dstDecl := unitDeclLM31) (ptrDecl := rawPtrConstU64Decl)
        rfl rfl rfl rfl rfl
        (fun tf htf =>
          ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 3,
           mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        (by rintro ⟨⟩) ⟨by rintro ⟨⟩, by rintro ⟨⟩⟩
    exact ⟨st', m_ub, m_ok, msg, tf_ok, hsu, hm_ub, hst, hget_st, hm_ok, htf_ok, hval_ok⟩

/-- `Runtime(PostCleanup)` MIR body taking `_2 = &raw const _3` and comparing
null `_1 : *const u64` (`0 as *const u64` on the LHS) with the tracked raw
pointer `_2 : *const u64` (on the RHS) via `_0 = Eq(copy _1, copy _2)`. -/
def lm31RawPtrCmpScalarPtrBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_cmp_scalar_ptr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDeclLM31, rawPtrConstU64Decl, rawPtrConstU64Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 3))),
        mkStmt (.assign (local_ 0)
          (.binaryOp .eq (.copy (local_ 1)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body taking `_2 = &raw const _1` and executing a
use-after-move relational comparison `_3 = Eq(move _2, copy _2)` on the tracked
raw pointer `_2`. -/
def lm31RawPtrCmpMoveUbBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_cmp_move_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, boolDeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.binaryOp .eq (.move (local_ 2)) (.copy (local_ 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing
`_2 = Offset(move _1, const 1_usize)` on null `_1 = 0 as *const u8` (non-zero
offset on provenance-less pointer with destructive `move _1`). -/
def lm31MoveNullOffsetNonzeroBody : CapturedMir where
  defPath := "lm_3_1_witness::move_null_offset_nonzero"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, rawPtrConstU8Decl, rawPtrConstU8Decl, u64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2)
          (.binaryOp .offset (.move (local_ 1)) (.constant (constUsizeLM31 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_cmp_symm_move_ub_and_unified_step_real_steps`**:
Concrete real-step witnesses exercising:
1. **`step_rawPtr_cmp_scalar_ptr_divergence`**: on `lm31RawPtrCmpScalarPtrBody`,
   after `_2 = &raw const _3`, comparing null `_1 = 0 as *const u64` on the LHS
   with tracked `_2` on the RHS (`_0 = Eq(copy _1, copy _2)`) steps in BOTH
   machines (Anneal storing `boolToScalar aRes`, `lean-miri` storing
   `.fromScalarInt (.ofBool eqRes)` in `_0`).
2. **`step_rawPtr_cmp_ub_lm3_1_simulation` and `step_mir_lm3_1_state_simulation`
   (`WellTypedLM3_1StateStmt.rawPtrCmpUb`)**: on `lm31RawPtrCmpMoveUbBody`, after
   `_2 = &raw const _1`, the use-after-move comparison `_3 = Eq(move _2, copy _2)`
   on the tracked pointer `_2` raises UB in lockstep (`StepObsRelLM3_1.ub`) in
   both Anneal (`MirStepNode.fail .ub`) and `lean-miri`
   (`StepError.undefinedBehavior`).
3. **`step_binOp_offset_move_scalar_nonzero_simulation`**: on
   `lm31MoveNullOffsetNonzeroBody`, `_2 = Offset(move _1, const 1_usize)` on
   null `_1 = 0 as *const u8` raises UB in BOTH machines (Anneal
   `MirStepNode.fail .ub`; `lean-miri` deinitializes `_1` and reports
   `StepError.undefinedBehavior "pointer Offset out of bounds"`). -/
theorem wit_lm3_1_cmp_symm_move_ub_and_unified_step_real_steps :
    -- (1) Symmetric `(.scalar, .ptr)` pointer comparison divergence (`null() == p`)
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState)
      (tf₂ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
      (aRes eqRes : Bool),
      let b := lm31RawPtrCmpScalarPtrBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b boolTyLM31 rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      get? s₂.frame.locals 0 = some (.init (.scalar (boolToScalar aRes))) ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      m₂.stack.frames = #[tf₂] ∧
      (tf₂.locals[0]?).map Miri.Interpreter.LocalState.value =
        some (.live (.immediate (.scalar (.fromScalarInt (.ofBool eqRes)))))) ∧
    -- (2) Tracked-pointer use-after-move `Eq(move _2, copy _2)` lockstep UB via
    --     unified `step_mir_lm3_1_state_simulation`
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := lm31RawPtrCmpMoveUbBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg))) ∧
    -- (3) Move-operand non-zero `Offset(move _1, const 1_usize)` on null pointer
    (∃ (m₁ : AnnealStepState),
      let b := lm31MoveNullOffsetNonzeroBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₀ =
        (m₁, .error (.undefinedBehavior "pointer Offset out of bounds"))) := by
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  refine ⟨?_, ?_, ?_⟩
  · -- Part (1): `lm31RawPtrCmpScalarPtrBody`
    let b := lm31RawPtrCmpScalarPtrBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b boolTyLM31 rawPtrConstU64Ty lm31Scalar0U64
    have hrel₀ : StateRel b s₀ m₀ :=
      mkFourLocalScalar_stateRel b boolTyLM31 boolDeclLM31 rawPtrConstU64Decl
        rawPtrConstU64Decl u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, m₀.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 3 :=
      fun tf htf =>
        ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
         mkFourLocalScalar_all_immediate _ _ _ _ tf htf 3⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 3 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : s₀.memory.nextTag = 1 := rfl
    have hid₀ : (⟨m₀.machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 3 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    obtain ⟨⟨s₂, aRes, hs₂, hget₂⟩, m₂, tf₂, eqRes, hm₂, htf₂, hval₂⟩ :=
      step_rawPtr_cmp_scalar_ptr_divergence hrel₁ hphase (Or.inl rfl) (Or.inl rfl) (Or.inl rfl)
        rfl rfl (dstDecl := boolDeclLM31) (lhsDecl := rawPtrConstU64Decl)
        (rhsDecl := rawPtrConstU64Decl) rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ =>
          ⟨himm₁ tf₁ htf₁ 0 (by decide), himm₁ tf₁ htf₁ 1 (by decide),
           himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (by rintro ⟨⟩) (sc₁ := ⟨0, 8⟩) (ptrVal₂ := { allocId := 1, offsetBytes := 0 }) rfl rfl
    exact ⟨s₁, s₂, m₁, m₂, tf₂, aRes, eqRes, hs₁, hm₁, hs₂, hget₂, hm₂, htf₂, hval₂⟩
  · -- Part (2): `lm31RawPtrCmpMoveUbBody` via `step_mir_lm3_1_state_simulation`
    let b := lm31RawPtrCmpMoveUbBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨42, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
    have hrel₀ : StateRel b s₀ m₀ :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrConstU64Decl boolDeclLM31
        ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (by rintro ⟨⟩) (by rintro ⟨⟩)
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, m₀.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf =>
        ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
         mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty) hs₁
    have htag₀ : s₀.memory.nextTag = 1 := rfl
    have hid₀ : (⟨m₀.machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm₁_step⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀.toLM3_1
        rfl rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
        AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm₁_step _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁
        [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1]
        (mkStmt (.assign (local_ 3) (.binaryOp .eq (.move (local_ 2)) (.copy (local_ 2))))) := by
      exact .rawPtrCmpUb 3 2 2 MirAst.Operand.move MirAst.Operand.copy .eq
        boolDeclLM31 rawPtrConstU64Decl rawPtrConstU64Decl .not .not (.uint .u64) (.uint .u64) _
        (Or.inr rfl) (Or.inl rfl) (Or.inl rfl) rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ =>
          ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide),
           himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (Or.inr (Or.inr ⟨rfl, rfl⟩))
    obtain ⟨_, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    have hs₂ : stepMirFn b s₁ = .fail .ub := rfl
    obtain ⟨msg, hm₂_err⟩ := (StepObsRelLM3_1.ub_iff hsim₂).mp hs₂
    exact ⟨s₁, m₁, (Miri.Interpreter.Step.step
        (annealStepHooks b.localDecls b.layouts) () m₁).1,
      msg, hs₁, hm₁, hs₂, Prod.ext rfl hm₂_err⟩
  · -- Part (3): `lm31MoveNullOffsetNonzeroBody`
    let b := lm31MoveNullOffsetNonzeroBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU8Ty lm31Scalar0U64
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU8Decl rawPtrConstU8Decl u64Decl
        ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    obtain ⟨_, hs₁, m₁, hm₁⟩ :=
      step_binOp_offset_move_scalar_nonzero_simulation hrel₀ (fun _ h => nomatch h) rfl rfl
        (dstDecl := rawPtrConstU8Decl) (ptrDecl := rawPtrConstU8Decl) (rhsTy := usizeTyLM31)
        (sc_p := ⟨0, 8⟩) (sc_r := ⟨1, 8⟩)
        (locals_r := s₀.frame.locals.set 1 .uninit)
        rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
        (fun tf _ => constUsize_wellTyped b tf 1 (by decide))
        (fun tf htf => mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1)
        rfl rfl (by decide) (by decide)
    exact ⟨m₁, hs₁, hm₁⟩

/-- `Runtime(PostCleanup)` MIR body exercising `step_binOp_offset_disabled_divergence`:
1. `_2 = &raw mut _1`;
2. `_3 = copy _2 as *mut u8`;
3. `StorageDead(_1)` (disables the borrow entry for `_1` in Anneal and frees
   `lm31AllocId1` in `lean-miri`);
4. `_4 = Offset(copy _3, const 0_usize)`: zero-byte `BinOp.Offset` on a disabled
   raw pointer faults with `MirStepNode.fail .ub` in Anneal while `lean-miri`'s
   `ptrOffsetInbounds` short-circuits at `delta == 0` and steps cleanly. -/
def lm31OffsetDisabledBody : CapturedMir where
  defPath := "lm_3_1_witness::offset_disabled_zero"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU8Decl, rawPtrMutU8Decl,
    rawPtrMutU8Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 4)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_binOp_offset_disabled_divergence`**:
Concrete end-to-end non-vacuity witness for `step_binOp_offset_disabled_divergence`
starting from pointer-free `StateRel`:
1. `_2 = &raw mut _1` promotes `_1` to `lm31AllocId1` in lockstep;
2. `_3 = copy _2 as *mut u8` casts to `*mut u8` in lockstep;
3. `StorageDead(_1)` transitions `entry` to `{ entry with perm := .disabled }` in
   lockstep;
4. `_4 = Offset(copy _3, const 0_usize)` faults with `MirStepNode.fail .ub` in
   Anneal (`stepMirFn`) while `lean-miri` (`Miri.Interpreter.Step.step`) steps to
   `(m₄, .ok true)`. -/
theorem wit_lm3_1_binOp_offset_disabled_divergence :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let hooks := annealStepHooks lm31OffsetDisabledBody.localDecls lm31OffsetDisabledBody.layouts
      let entry := rawPtrAllocMapEntry lm31OffsetDisabledBody.localDecls
        lm31OffsetDisabledBody.layouts .mut 1 1 lm31AllocId1
      stepMirFn lm31OffsetDisabledBody (mkSixLocalAnnealPre lm31OffsetDisabledBody) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre lm31OffsetDisabledBody u64Ty) =
        (m₁, .ok true) ∧
      StateRelLM3_1 lm31OffsetDisabledBody s₁ m₁ [entry] ∧
      stepMirFn lm31OffsetDisabledBody s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 lm31OffsetDisabledBody s₂ m₂ [entry] ∧
      stepMirFn lm31OffsetDisabledBody s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 lm31OffsetDisabledBody s₃ m₃ [{ entry with perm := .disabled }] ∧
      stepMirFn lm31OffsetDisabledBody s₃ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) := by
  have hrel₀ : StateRel lm31OffsetDisabledBody (mkSixLocalAnnealPre lm31OffsetDisabledBody)
      (mkSixLocalMiriPre lm31OffsetDisabledBody u64Ty) :=
    mkSixLocal_stateRel lm31OffsetDisabledBody u64Ty u64Decl rawPtrMutU64Decl rawPtrMutU8Decl
      rawPtrMutU8Decl rawPtrMutU8Decl rfl rfl
  have hphase : ∀ p, lm31OffsetDisabledBody.phase ≠ .other p := fun _ h => nomatch h
  have himm₀ : ∀ tf, (mkSixLocalMiriPre lm31OffsetDisabledBody u64Ty).stack.frames = #[tf] →
      IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
    fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let entry := rawPtrAllocMapEntry lm31OffsetDisabledBody.localDecls
    lm31OffsetDisabledBody.layouts .mut 1 1 lm31AllocId1
  let bor := [rawPtrBorrowEntry lm31OffsetDisabledBody.localDecls
    lm31OffsetDisabledBody.layouts .mut 1 1]
  -- Step 1: `_2 = &raw mut _1`
  let s₁ := mkWitState lm31OffsetDisabledBody 1
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn lm31OffsetDisabledBody (mkSixLocalAnnealPre lm31OffsetDisabledBody) =
      .step s₁ := rfl
  have hsim₁ := step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step hsim₁ hs₁
  have htag₀ : (mkSixLocalAnnealPre lm31OffsetDisabledBody).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalMiriPre lm31OffsetDisabledBody u64Ty).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm₁_step⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀ AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
    fun tf₁ htf₁ k hne =>
      himm₁_step _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
  -- Step 2: `_3 = copy _2 as *mut u8`
  let s₂ := mkWitState lm31OffsetDisabledBody 2
    [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn lm31OffsetDisabledBody s₁ = .step s₂ := rfl
  have hsim₂ := step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
    (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar)
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
  obtain ⟨_, himm₂_step⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
    intro tf₂ htf₂ k hne
    obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm₂_step tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
  -- Step 3: `StorageDead(_1)`
  let s₃ := mkWitState lm31OffsetDisabledBody 3
    [.uninit, .dead, .init ptr0, .init ptr0, .uninit, .uninit]
    (disableLocalBorrows bor 1) 2
  have hs₃ : stepMirFn lm31OffsetDisabledBody s₂ = .step s₃ := rfl
  have hsim₃ := step_storageDead_lm3_1_simulation hrel₂ hphase rfl rfl
    (decl := u64Decl) rfl (by decide)
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  obtain ⟨_, himm₃_step⟩ := step_storageDead_preserves hrel₂ rfl rfl
    (decl := u64Decl) rfl (by decide) hm₃
  have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
    intro tf₃ htf₃ k hne
    obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm₃_step tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
  -- Step 4: `_4 = Offset(copy _3, const 0_usize)` -> UB in Anneal, `.ok true` in Miri
  obtain ⟨hs₄, m₄, hm₄⟩ := step_binOp_offset_disabled_divergence hrel₃ hphase rfl rfl
    (dstDecl := rawPtrMutU8Decl) (ptrDecl := rawPtrMutU8Decl)
    rfl rfl rfl rfl (Or.inl rfl) (rhsTy := usizeTyLM31) (Or.inl rfl)
    (fun tf₃ _ => constUsize_wellTyped lm31OffsetDisabledBody tf₃ 0 (by decide))
    (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 4 (by decide), himm₃ tf₃ htf₃ 3 (by decide)⟩)
    (fun _ => slot_ptr_ne_scalar)
    (ptrVal := { allocId := 1, offsetBytes := 0 }) (sc := ⟨0, 8⟩)
    (e := { entry with perm := .disabled }) (tgtDecl := u64Decl)
    rfl rfl (.head _) rfl rfl rfl (Or.inl ⟨rfl, rfl⟩) (by rintro ⟨⟩) rfl
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, hs₃, hm₃, hrel₃, hs₄, hm₄⟩

/-! ## 8. Episode 2 (`D1..D6`) Upgraded Real-Step Simulations & Read/Write/Offset Witnesses -/

/-- Entry `lean-miri` frame matching `initMachineState body []` (`argCount = 0`):
local `0` is `.live (.immediate .uninit)` and non-return locals `1 .. n` are `.dead`. -/
def mkZeroArgEntryMiriFrame (body : CapturedMir) (retTy : Ty) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy retTy) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := (
      { value := .live (.immediate .uninit), layout := none } ::
      (body.localDecls.drop 1).map (fun _ =>
        ({ value := .dead, layout := none } :
          Miri.Interpreter.LocalState AnnealProv Miri.Interpreter.LocalLayout))).toArray
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

/-- Entry `AnnealStepState` matching `initMachineState body []` (`argCount = 0`). -/
def mkZeroArgEntryMiri (body : CapturedMir) (retTy : Ty) : AnnealStepState :=
  { stack := ⟨#[mkZeroArgEntryMiriFrame body retTy]⟩, machine := AnnealMachine.empty }

private theorem mkZeroArgEntry_all_immediate (body : CapturedMir) (retTy : Ty)
    (hmax : body.localDecls.length ≤ 6) :
    ∀ tf, (mkZeroArgEntryMiri body retTy).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  rcases body with ⟨_, _, _, _, lds, _, _, _, _, _⟩
  dsimp only [mkZeroArgEntryMiriFrame] at hmls hmax
  rcases lds with _ | ⟨d0, _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, _ | ⟨d4, _ | ⟨d5, rest⟩⟩⟩⟩⟩⟩
  · cases k <;> simp at hmls; subst hmls; cases hmp
  · cases k with | zero => simp at hmls; subst hmls; cases hmp | succ k => simp at hmls
  · match k with | 0 | 1 => simp at hmls; subst hmls; cases hmp | _ + 2 => simp at hmls
  · match k with | 0 | 1 | 2 => simp at hmls; subst hmls; cases hmp | _ + 3 => simp at hmls
  · match k with | 0 | 1 | 2 | 3 => simp at hmls; subst hmls; cases hmp | _ + 4 => simp at hmls
  · match k with | 0 | 1 | 2 | 3 | 4 => simp at hmls; subst hmls; cases hmp | _ + 5 => simp at hmls
  · cases rest with
    | nil =>
      match k with
      | 0 | 1 | 2 | 3 | 4 | 5 => simp at hmls; subst hmls; cases hmp
      | _ + 6 => simp at hmls
    | cons _ _ => simp at hmax

private theorem mkZeroArgEntry_stateRel3 (body : CapturedMir) (d₀ d₁ d₂ : LocalDecl)
    (hdecls : body.localDecls = [d₀, d₁, d₂]) :
    StateRel body (initMachineState body []) (mkZeroArgEntryMiri body d₀.ty) := by
  refine StateRel.mk (mkZeroArgEntryMiriFrame body d₀.ty) rfl rfl ⟨translateTy d₀.ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; rw [mkZeroArgEntryMiriFrame, hdecls];
        match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)
  have hf_loc : (initMachineState body []).frame.locals = [.uninit, .dead, .dead] := by
    unfold initMachineState; dsimp only []; rw [hdecls]; rfl
  refine ⟨rfl, rfl, by rw [hf_loc, hdecls]; rfl, by simp [mkZeroArgEntryMiriFrame, hdecls], ?_⟩
  intro i decl slot mls hdecl hslot hmls
  rw [hf_loc] at hslot; rw [hdecls] at hdecl
  have hmls' : ((mkZeroArgEntryMiriFrame body d₀.ty).locals)[i]? = some mls := hmls
  simp only [mkZeroArgEntryMiriFrame, hdecls] at hmls'
  match i with
  | 0 =>
    have hs : slot = .uninit := by simpa [get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by simpa using hmls'.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 | 2 =>
    have hs : slot = .dead := by simpa [get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by simpa using hmls'.symm
    subst hs hm
    exact .dead none (fun _ h => nomatch h)
  | _ + 3 => simp [get?] at hdecl

private theorem mkZeroArgEntry_stateRel4 (body : CapturedMir) (d₀ d₁ d₂ d₃ : LocalDecl)
    (hdecls : body.localDecls = [d₀, d₁, d₂, d₃]) :
    StateRel body (initMachineState body []) (mkZeroArgEntryMiri body d₀.ty) := by
  refine StateRel.mk (mkZeroArgEntryMiriFrame body d₀.ty) rfl rfl ⟨translateTy d₀.ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; rw [mkZeroArgEntryMiriFrame, hdecls];
        match i with | 0 | 1 | 2 | 3 | _ + 4 => rintro ⟨⟩)
  have hf_loc : (initMachineState body []).frame.locals = [.uninit, .dead, .dead, .dead] := by
    unfold initMachineState; dsimp only []; rw [hdecls]; rfl
  refine ⟨rfl, rfl, by rw [hf_loc, hdecls]; rfl, by simp [mkZeroArgEntryMiriFrame, hdecls], ?_⟩
  intro i decl slot mls hdecl hslot hmls
  rw [hf_loc] at hslot; rw [hdecls] at hdecl
  have hmls' : ((mkZeroArgEntryMiriFrame body d₀.ty).locals)[i]? = some mls := hmls
  simp only [mkZeroArgEntryMiriFrame, hdecls] at hmls'
  match i with
  | 0 =>
    have hs : slot = .uninit := by simpa [get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by simpa using hmls'.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 | 2 | 3 =>
    have hs : slot = .dead := by simpa [get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by simpa using hmls'.symm
    subst hs hm
    exact .dead none (fun _ h => nomatch h)
  | _ + 4 => simp [get?] at hdecl

private theorem step_storageLive_preserves_machine
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {loc : Local} {decl : LocalDecl} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some ⟨.storageLive loc, span⟩)
    (hdecl : get? body.localDecls loc = some decl)
    (himm_loc : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf loc)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine = m.machine ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨_, mls, _, hlt_mf, _, hmls, hmls_eq, hloc⟩ := hfr.lookup_local hdecl
  have hnot_ind := himm_loc tf hframes mls hmls
  have hdealloc_eq : deallocLocalMemory m.machine.memory (tf.locals[loc]'hlt_mf).value =
      m.machine.memory := by
    rw [hmls_eq]
    cases hv : mls.value with
    | dead => rfl
    | live op =>
      cases op with
      | immediate _ => rfl
      | indirect mp => exact absurd hv (hnot_ind mp)
  have hty : ∃ ty, tf.body.locals[loc]? = some ty := by
    rw [hfr.body_eq, translateBody_locals_getElem? body loc, hdecl]
    exact ⟨_, rfl⟩
  have hm : Miri.Interpreter.Step.evalStatement (annealStepHooks body.localDecls body.layouts) ()
      (translateStmt ⟨.storageLive loc, span⟩) m =
      ({ stack := ⟨#[{ tf with
            locals := tf.locals.set loc
              { tf.locals[loc]'hlt_mf with value := .live (.immediate .uninit) } hlt_mf }]⟩
         machine := { m.machine with memory := m.machine.memory } }, .ok ()) := by
    simp only [Miri.Interpreter.Step.evalStatement, translateStmt, translateStmtKind]
    have hlive : LocalAllocLive m.machine.memory (tf.locals[loc]'hlt_mf).value := by
      rw [hmls_eq]; exact hloc.allocLive
    have hsl := annealStepHooks_storageLive_any_eq
      (localDecls := body.localDecls) (layouts := body.layouts) hframes hlt_mf hty hlive
    rw [hdealloc_eq] at hsl
    exact hsl
  rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm rfl
    hfr.location_eq] at hstep
  injection hstep with hm' _; subst hm'
  refine ⟨rfl, fun tf₀ tf' htf₀ htf' k hk mls' hmls' mp hmp => ?_⟩
  rw [hframes] at htf₀; injection htf₀ with h₀; injection h₀ with h₀'; subst h₀'
  injection htf' with h₁; injection h₁ with h₁'; subst h₁'
  dsimp only [] at hmls'
  rw [Array.getElem?_set] at hmls'
  by_cases heq : loc = k
  · subst heq; simp only [↓reduceIte, Option.some.injEq] at hmls'; rw [← hmls'] at hmp; cases hmp
  · simp only [heq, ↓reduceIte] at hmls'; exact hk mls' hmls' mp hmp

private theorem step_const_assign_preserves_machine
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dstIdx : Local} {dstDecl : LocalDecl}
    {c : ConstOperand} {sc : MirAst.ScalarInt} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.use (.constant c)), span⟩)
    (hdecl_dst : get? body.localDecls dstIdx = some dstDecl)
    (hc_ok : evalOperand s.frame.locals (.constant c) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals = .ok (.scalar sc) s.frame.locals)
    (hdst_live : get? s.frame.locals dstIdx ≠ some .dead)
    (himm_dst : ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf dstIdx)
    (hop : ∀ tf, m.stack.frames = #[tf] →
      WellTypedScalarOperand body tf (.constant c) dstDecl.ty)
    (hdst_prim : IsPrimScalarTy dstDecl.ty)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    m'.machine = m.machine ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) := by
  obtain ⟨tf, hframes, _, _, hfr, _, _, _, _, _, _, _⟩ := id hstate
  obtain ⟨slot_d, mls_d, _, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
    hfr.lookup_local hdecl_dst
  have hcache_d : ∀ l, (tf.locals[dstIdx]'hlt_d).layout = some l →
      l = translateTy dstDecl.ty body.layouts := by
    rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
  let tfa := cacheFrameLocalLayout tf dstIdx hlt_d (translateTy dstDecl.ty body.layouts)
  have hstate_a : StateRelLM3_1 body s { m with stack := ⟨#[tfa]⟩ } allocMap :=
    hstate.cache_layout hframes hdecl_dst hlt_d
  have hdst_eval : annealEvalPlace body.localDecls body.layouts ⟨dstIdx, #[]⟩ m =
      .ok ⟨.local 0 dstIdx none tf.localsIdentity, translateTy dstDecl.ty body.layouts⟩
        { m with stack := ⟨#[tfa]⟩ } :=
    annealEvalPlace_unprojected hframes hlt_d hdecl_dst hcache_d
  have hop_a := (hop tf hframes).of_cacheFrameLocalLayout dstIdx hlt_d
    (translateTy dstDecl.ty body.layouts)
  rcases evalOperand_scalar_lm3_1_simulation hstate_a rfl hop_a hdst_prim
      (some (translateTy dstDecl.ty body.layouts)) with
    ⟨_, _, ha_ub, _⟩ | ⟨_, msc, tfb, _, hm_op, hstate_b, _, hid_b, hpres_b⟩
  · rw [hc_ok] at ha_ub; cases ha_ub
  · have himm_db : IsImmediateFrameLocal tfb dstIdx := by
      intro mls' hmls' mp hmp
      have hv := hpres_b dstIdx; rw [hmls'] at hv
      cases h₁ : tfa.locals[dstIdx]? with
      | none => rw [h₁] at hv; cases hv
      | some mls₁ =>
        rw [h₁] at hv; dsimp only [Option.map] at hv; injection hv with hv'
        exact (himm_dst tf hframes).cache_layout hlt_d _ mls₁ h₁ mp (hv'.symm.trans hmp)
    have hfr_b := hstate_b.frame_rel_singleton rfl
    obtain ⟨_, mls_db, _, hlt_db, hslot_db, hmls_db, _, hloc_db⟩ := hfr_b.lookup_local hdecl_dst
    have hsd_ne : slot_d ≠ .dead := fun hd => hdst_live (hslot_d.trans (congrArg some hd))
    have himm_db_v := himm_db mls_db hmls_db
    obtain ⟨oldImm, hmd_imm⟩ : ∃ oldImm, mls_db.value = .live (.immediate oldImm) := by
      have hs_eq : _ = slot_d := Option.some.inj (hslot_db.symm.trans hslot_d)
      cases hloc_db with
      | rawPtr _ _ _ _ _ _ hty _ =>
        exfalso; rcases hdst_prim with hk | hk | ⟨_, hk⟩ | ⟨_, hk⟩ <;> rw [hk] at hty <;> cases hty
      | base hb =>
        cases hb with
        | dead _ _ => exact absurd hs_eq.symm hsd_ne
        | indirect _ mp _ _ _ _ => exact absurd rfl (himm_db_v mp)
        | immediate _ imm _ _ _ => exact ⟨imm, rfl⟩
    have hdb_live : tfb.locals[dstIdx]? = some ⟨.live (.immediate oldImm), mls_db.layout⟩ := by
      rw [hmls_db]; rcases mls_db with ⟨vd, ld⟩; dsimp only at hmd_imm; rw [hmd_imm]
    have hget_db := frame_getLocal_of_getElem? tfb dstIdx _ hdb_live
    have hid_tfa : tfa.localsIdentity = tf.localsIdentity := rfl
    have hid_tf : tfb.localsIdentity = tf.localsIdentity := hid_b.trans hid_tfa
    have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc))
      (m := { m with stack := ⟨#[tfb]⟩ }) (id0 := tfb.localsIdentity)
      (dstLay := translateTy dstDecl.ty body.layouts) rfl hlt_db hget_db
    rw [hid_tf] at hw_ok
    have h1_arr : ([] : List Miri.MIR.ProjectionElem).toArray = #[] := rfl
    have hm_ev : Miri.Interpreter.Step.evalStatement
        (annealStepHooks body.localDecls body.layouts) ()
        (translateStmt ⟨.assign ⟨dstIdx, .nil⟩ (.use (.constant c)), span⟩) m =
        ({ m with stack := ⟨#[{ tfb with
            locals := tfb.locals.set dstIdx
              { tfb.locals[dstIdx]'hlt_db with value := .live (.immediate (.scalar (.fromScalarInt msc))) }
              hlt_db }]⟩ }, .ok ()) := by
      rw [evalStatement_assign_use_eq]
      dsimp only [translatePlace, List.map]; rw [h1_arr]
      unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_eval]
      dsimp only []
      have hassoc : ∀ {ε σ α β γ} (ma : EStateM ε σ α) (mb : α → EStateM ε σ β)
          (mc : β → EStateM ε σ γ), (ma >>= fun x => mb x >>= mc) = ((ma >>= mb) >>= mc) :=
        fun ma mb mc => funext (EStateM.bind_assoc_apply ma mb mc)
      rw [hassoc, EStateM.bind_eq_ok hm_op]
      dsimp only []; rw [hw_ok]; simp only [hid_tf]
    rw [miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ev rfl
      hfr_b.location_eq] at hstep
    injection hstep with hm' _; subst hm'
    refine ⟨rfl, fun tf₀ tf' htf₀ htf' k hk => ?_⟩
    have himm_ev := (step_assign_use_preserves hstate (fun _ => by nofun) hbb hstmt
      (miri_step_at_statement_ok _ hframes hfr.body_eq hfr.location_eq hbb hstmt hm_ev rfl
        hfr_b.location_eq)).2
    exact himm_ev tf₀ tf' htf₀ htf' k hk

/-! ### 8.1 D1 Real-Step Witnesses (`wit_lm3_1_anneal_offset_deref_simulation` & OOB Deref Write) -/

/-- **`wit_lm3_1_anneal_offset_deref_simulation` (`LM-3.1` D1 Real-Step Upgrade)**:
Complete 7-step end-to-end real-step `StateRelLM3_1` execution of `lm31OffsetDerefBody`
from initial entry state `initMachineState lm31OffsetDerefBody []` and
`mkZeroArgEntryMiri lm31OffsetDerefBody u64Ty`:
1–3. `StorageLive(_1); StorageLive(_2); StorageLive(_3)` step in lockstep;
4. `_1 = const 42_u64` steps in lockstep;
5. `_2 = &raw const _1` promotes `_1` to `lm31AllocId1` in lockstep;
6. `_3 = Offset(copy _2, const 1_usize)` scales by `sizeof::<u64>() = 8` to
   `offsetBytes = 8` in lockstep (`step_binOp_offset_stride_simulation`);
7. `_0 = copy *_3` raises OOB UB in BOTH `stepMirFn` (`.fail .ub`) and
   `Miri.Interpreter.Step.step` (`.error (.undefinedBehavior msg)`) via
   `step_deref_oob_simulation`. -/
theorem wit_lm3_1_anneal_offset_deref_simulation :
    ∃ (s₁ s₂ s₃ s₄ s₅ s₆ : MachineState) (m₁ m₂ m₃ m₄ m₅ m₆ m₇ : AnnealStepState)
      (msg : String),
      let b := lm31OffsetDerefBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      stepMirFn b (initMachineState b []) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkZeroArgEntryMiri b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [] ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ [entry] ∧
      stepMirFn b s₅ = .step s₆ ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM3_1 b s₆ m₆ [entry] ∧
      get? s₆.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn b s₆ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₆ = (m₇, .error (.undefinedBehavior msg)) := by
  let b := lm31OffsetDerefBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ : StateRelLM3_1 b (initMachineState b []) (mkZeroArgEntryMiri b u64Ty) [] :=
    (mkZeroArgEntry_stateRel4 b u64Decl u64Decl rawPtrConstU64Decl rawPtrConstU64Decl rfl).toLM3_1
  have himm₀ := mkZeroArgEntry_all_immediate b u64Ty (by decide)
  let s₁ := mkWitState b 1 [.uninit, .uninit, .dead, .dead] [] 1
  have hs₁ : stepMirFn b (initMachineState b []) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₀ hphase rfl rfl (decl := u64Decl) rfl (fun _ h => nomatch h)) hs₁
  obtain ⟨hmach₁, himm_s₁⟩ := step_storageLive_preserves_machine hrel₀ rfl rfl (decl := u64Decl) rfl
    (fun tf htf => himm₀ tf htf 1) hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₀, htf₀, _⟩ := id hrel₀; exact himm_s₁ tf₀ tf htf₀ htf k (himm₀ tf₀ htf₀ k)
  let s₂ := mkWitState b 2 [.uninit, .uninit, .uninit, .dead] [] 1
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₁ hphase rfl rfl (decl := rawPtrConstU64Decl) rfl (fun _ h => nomatch h)) hs₂
  obtain ⟨hmach₂, himm_s₂⟩ := step_storageLive_preserves_machine hrel₁ rfl rfl
    (decl := rawPtrConstU64Decl) rfl (fun tf htf => himm₁ tf htf 2) hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k)
  let s₃ := mkWitState b 3 [.uninit, .uninit, .uninit, .uninit] [] 1
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₂ hphase rfl rfl (decl := rawPtrConstU64Decl) rfl (fun _ h => nomatch h)) hs₃
  obtain ⟨hmach₃, himm_s₃⟩ := step_storageLive_preserves_machine hrel₂ rfl rfl
    (decl := rawPtrConstU64Decl) rfl (fun tf htf => himm₂ tf htf 3) hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k)
  let s₄ := mkWitState b 4 [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .uninit] [] 1
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_scalar_use_lm3_1_simulation hrel₃ hphase rfl rfl (dstDecl := u64Decl) (valTy := u64Ty)
      rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf _ => constU64_wellTyped b tf 42 (by decide)) (fun tf htf => himm₃ tf htf 1)) hs₄
  obtain ⟨hmach₄, himm_s₄⟩ := step_const_assign_preserves_machine hrel₃ rfl rfl
    (dstDecl := u64Decl) rfl rfl (by rintro ⟨⟩) (fun tf htf => himm₃ tf htf 1)
    (fun tf _ => constU64_wellTyped b tf 42 (by decide))
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) hm₄
  have himm₄ : ∀ tf, m₄.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃; exact himm_s₄ tf₃ tf htf₃ htf k (himm₃ tf₃ htf₃ k)
  have hmach₄_empty : m₄.machine = AnnealMachine.empty :=
    hmach₄.trans (hmach₃.trans (hmach₂.trans hmach₁))
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
  let s₅ := mkWitState b 5 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
  have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
  have hsup₄ : AllocIdSupplyReady m₄.machine.memory := by rw [hmach₄_empty]; exact AllocIdSupplyReady.empty
  obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_lm3_1_simulation hrel₄ hphase rfl rfl
      (dstDecl := rawPtrConstU64Decl) (targetDecl := u64Decl) rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₄ tf htf 2, himm₄ tf htf 1⟩) hsup₄) hs₅
  have hna4 : m₄.machine.memory.nextAllocId = 1 := by rw [hmach₄_empty]; rfl
  have hid₄ : (⟨m₄.machine.memory.nextAllocId, hsup₄.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := by
    show ({ value := m₄.machine.memory.nextAllocId, nonzero := _ } : Miri.Memory.AllocId) = ⟨1, by decide⟩
    simp only [hna4]
  have htag₄ : s₄.memory.nextTag = 1 := rfl
  rw [htag₄, hid₄] at hrel₅
  obtain ⟨_, himm_s₅⟩ := step_rawPtr_addrOf_preserves_ne hrel₄.toStateRel rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₄ tf htf 2, himm₄ tf htf 1⟩) hsup₄ hm₅
  have himm₅ : ∀ tf, m₅.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₄, htf₄, _⟩ := id hrel₄; exact himm_s₅ tf₄ tf htf₄ htf k hne (himm₄ tf₄ htf₄ k)
  obtain ⟨hsim₆, hs₆_eq, m₆, _, _, hm₆, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₅ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
      (fun tf htf => ⟨himm₅ tf htf 3 (by decide), himm₅ tf htf 2 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₆ := mkWitState b 6 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr8] bor 2
  have hs₆ : stepMirFn b s₅ = .step s₆ := hs₆_eq
  obtain ⟨m₆', hm₆_eq, hrel₆⟩ := stepRelLM3_1_of_anneal_step hsim₆ hs₆
  have hm₆_inj : m₆' = m₆ := (Prod.mk.inj (hm₆_eq.symm.trans hm₆)).1; subst m₆'
  obtain ⟨_, himm_s₆⟩ := step_assign_binOp_offset_preserves hrel₅ (by rintro _ ⟨⟩) rfl rfl hm₆
  have himm₆ : ∀ tf, m₆.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₅, htf₅, _⟩ := id hrel₅; exact himm_s₆ tf₅ tf htf₅ htf k (himm₅ tf₅ htf₅ k hne)
  obtain ⟨tf₆, htf₆, _, _, _, _, _, _, _, _, halloc₆, _⟩ := id hrel₆
  obtain ⟨_, _, hsh₆⟩ := (halloc₆.local_alloc_sync tf₆ htf₆ _ (.head _)).1
    (.init (.scalar ⟨42, 8⟩)) rfl (by rintro ⟨⟩)
  obtain ⟨la₆, hfind₆, _, _, hshape₆⟩ := hsh₆ u64Decl rfl
  obtain ⟨hsim₇, hs₇⟩ := step_deref_oob_simulation hrel₆ hphase (Or.inl rfl) rfl rfl
    (dstDecl := u64Decl) (ptrDecl := rawPtrConstU64Decl)
    rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (fun tf htf => himm₆ tf htf 3 (by decide))
    (ptrVal := { allocId := 1, offsetBytes := 8 }) rfl (.head _) rfl hfind₆
    (by rw [hshape₆.byteSize_eq]; decide)
  obtain ⟨m₇, msg, hm₇⟩ := stepRelLM3_1_of_anneal_ub hsim₇ hs₇
  exact ⟨s₁, s₂, s₃, s₄, s₅, s₆, m₁, m₂, m₃, m₄, m₅, m₆, m₇, msg,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrel₄, hs₅, hm₅, hrel₅,
    hs₆, hm₆, hrel₆, rfl, hs₇, hm₇⟩

/-- `Runtime(PostCleanup)` MIR body exercising an out-of-bounds dereference **write**
(`_2 = &raw mut _1; _3 = Offset(move _2, const 1_usize); *_3 = const 99_u64`),
also exercising `Operand.move` on the `BinOp.Offset` pointer operand. -/
def lm31DerefWriteOobBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_write_oob_real"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.binaryOp .offset (.move (local_ 2)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (derefLocal 3) (.use (.constant (constU64 99))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_write_oob_real_steps` (`LM-3.1` D1 Out-of-Bounds Deref Write Real Steps)**:
End-to-end 3-step execution of `lm31DerefWriteOobBody` from `StateRel`:
1. `_2 = &raw mut _1` promotes `_1` (`42_u64`) to `lm31AllocId1` in lockstep;
2. `_3 = Offset(move _2, const 1_usize)` scales by `8` bytes (`offsetBytes = 8`)
   and deinitializes moved `_2` in lockstep (`step_binOp_offset_stride_simulation`
   with `opKind = .move`);
3. `*_3 = const 99_u64` raises OOB UB (`8 < 8 + 8`) in BOTH `stepMirFn` (`.fail .ub`)
   and `Miri.Interpreter.Step.step` (`.error (.undefinedBehavior msg)`) via
   `step_deref_write_oob_simulation`. -/
theorem wit_lm3_1_deref_write_oob_real_steps :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msg : String),
      let b := lm31DerefWriteOobBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
      stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 2 = some .uninit ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg)) := by
  let b := lm31DerefWriteOobBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
      (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
    mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl rawPtrMutU64Decl
      ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
  have himm₀ := mkFourLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  obtain ⟨hsim₂, hs₂_eq, m₂, tf₂, _, hm₂, htf₂, hval₂⟩ :=
    step_binOp_offset_stride_simulation hrel₁ hphase (Or.inr rfl) rfl rfl
      (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .uninit, .init ptr8] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := hs₂_eq
  obtain ⟨m₂', hm₂_eq, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
  have hm₂_inj : m₂' = m₂ := (Prod.mk.inj (hm₂_eq.symm.trans hm₂)).1; subst m₂'
  have himm₂_3 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 := by
    intro tf htf mls hmls mp hmp
    rw [htf₂] at htf; injection htf with h1; injection h1 with h2; subst h2
    rw [hmls] at hval₂; injection hval₂ with hv; rw [hv] at hmp; cases hmp
  obtain ⟨tf₂', htf₂', _, _, _, _, _, _, _, _, halloc₂, _⟩ := id hrel₂
  obtain ⟨_, _, hsh₂⟩ := (halloc₂.local_alloc_sync tf₂' htf₂' _ (.head _)).1
    (.init (.scalar ⟨42, 8⟩)) rfl (by rintro ⟨⟩)
  obtain ⟨la₂, hfind₂, _, _, hshape₂⟩ := hsh₂ u64Decl rfl
  obtain ⟨hsim₃, hs₃⟩ := step_deref_write_oob_simulation hrel₂ hphase rfl rfl
    (ptrDecl := rawPtrMutU64Decl) (valTy := u64Ty) rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (fun tf _ => .of_wt (constU64_wellTyped b tf 99 (by decide)))
    himm₂_3 (ptrVal := { allocId := 1, offsetBytes := 8 }) rfl (.head _) rfl hfind₂
    (by rw [hshape₂.byteSize_eq]; decide)
  obtain ⟨m₃, msg, hm₃⟩ := stepRelLM3_1_of_anneal_ub hsim₃ hs₃
  exact ⟨s₁, s₂, m₁, m₂, m₃, msg, hs₁, hm₁, hrel₁, hs₂, hm₂, hrel₂, rfl, rfl, hs₃, hm₃⟩

/-! ### 8.2 D2 Real-Step Witnesses (`wit_lm3_1_anneal_storage_revive_simulation` & Stale Revival Read) -/

/-- **`wit_lm3_1_anneal_storage_revive_simulation` (`LM-3.1` D2 Real-Step Upgrade)**:
Complete 7-step end-to-end real-step execution of `lm31ReviveBody` from initial
entry state `initMachineState lm31ReviveBody []` and
`mkZeroArgEntryMiri lm31ReviveBody u64Ty`:
1–2. `StorageLive(_1); StorageLive(_2)` step in lockstep;
3. `_1 = const 42_u64` steps in lockstep;
4. `_2 = &raw mut _1` promotes `_1` to `lm31AllocId1` in lockstep;
5. `StorageDead(_1)` marks `_1` `.dead`, disables `_2`'s borrow tag, and frees
   `lm31AllocId1` in `lean-miri`;
6. `StorageLive(_1)` revives `_1` as `.uninit` in lockstep while keeping `_2`'s
   tag `.disabled` and `lm31AllocId1` absent from `m₆.machine.memory.live`;
7. `*_2 = const 7_u64` raises UAF UB in BOTH `stepMirFn` (`.fail .ub`) and
   `Miri.Interpreter.Step.step` (`.error (.undefinedBehavior msg)`) via
   `step_storageDead_storageLive_deref_ub_simulation`. -/
theorem wit_lm3_1_anneal_storage_revive_simulation :
    ∃ (s₁ s₂ s₃ s₄ s₅ s₆ : MachineState) (m₁ m₂ m₃ m₄ m₅ m₆ m₇ : AnnealStepState)
      (msg : String),
      let b := lm31ReviveBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
      stepMirFn b (initMachineState b []) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkZeroArgEntryMiri b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [] ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      stepMirFn b s₅ = .step s₆ ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
      StepRelLM3_1 b m₆ (disableAllocMapLocal [entry] 1)
        (stepMirFn b s₆) (Miri.Interpreter.Step.step hooks () m₆) ∧
      stepMirFn b s₆ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₆ = (m₇, .error (.undefinedBehavior msg)) := by
  let b := lm31ReviveBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ : StateRelLM3_1 b (initMachineState b []) (mkZeroArgEntryMiri b u64Ty) [] :=
    (mkZeroArgEntry_stateRel3 b u64Decl u64Decl rawPtrMutU64Decl rfl).toLM3_1
  have himm₀ := mkZeroArgEntry_all_immediate b u64Ty (by decide)
  let s₁ := mkWitState b 1 [.uninit, .uninit, .dead] [] 1
  have hs₁ : stepMirFn b (initMachineState b []) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₀ hphase rfl rfl (decl := u64Decl) rfl (fun _ h => nomatch h)) hs₁
  obtain ⟨hmach₁, himm_s₁⟩ := step_storageLive_preserves_machine hrel₀ rfl rfl (decl := u64Decl) rfl
    (fun tf htf => himm₀ tf htf 1) hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₀, htf₀, _⟩ := id hrel₀; exact himm_s₁ tf₀ tf htf₀ htf k (himm₀ tf₀ htf₀ k)
  let s₂ := mkWitState b 2 [.uninit, .uninit, .uninit] [] 1
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₁ hphase rfl rfl (decl := rawPtrMutU64Decl) rfl (fun _ h => nomatch h)) hs₂
  obtain ⟨hmach₂, himm_s₂⟩ := step_storageLive_preserves_machine hrel₁ rfl rfl
    (decl := rawPtrMutU64Decl) rfl (fun tf htf => himm₁ tf htf 2) hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k)
  let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨42, 8⟩), .uninit] [] 1
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
    (step_scalar_use_lm3_1_simulation hrel₂ hphase rfl rfl (dstDecl := u64Decl) (valTy := u64Ty)
      rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf _ => constU64_wellTyped b tf 42 (by decide)) (fun tf htf => himm₂ tf htf 1)) hs₃
  obtain ⟨hmach₃, himm_s₃⟩ := step_const_assign_preserves_machine hrel₂ rfl rfl
    (dstDecl := u64Decl) rfl rfl (by rintro ⟨⟩) (fun tf htf => himm₂ tf htf 1)
    (fun tf _ => constU64_wellTyped b tf 42 (by decide))
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k)
  have hmach₃_empty : m₃.machine = AnnealMachine.empty := hmach₃.trans (hmach₂.trans hmach₁)
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₄ := mkWitState b 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0] bor 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  have hsup₃ : AllocIdSupplyReady m₃.machine.memory := by rw [hmach₃_empty]; exact AllocIdSupplyReady.empty
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_lm3_1_simulation hrel₃ hphase rfl rfl
      (dstDecl := rawPtrMutU64Decl) (targetDecl := u64Decl) rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₃ tf htf 2, himm₃ tf htf 1⟩) hsup₃) hs₄
  have hna3 : m₃.machine.memory.nextAllocId = 1 := by rw [hmach₃_empty]; rfl
  have hid₃ : (⟨m₃.machine.memory.nextAllocId, hsup₃.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := by
    show ({ value := m₃.machine.memory.nextAllocId, nonzero := _ } : Miri.Memory.AllocId) = ⟨1, by decide⟩
    simp only [hna3]
  have htag₃ : s₃.memory.nextTag = 1 := rfl
  rw [htag₃, hid₃] at hrel₄
  obtain ⟨_, himm_s₄⟩ := step_rawPtr_addrOf_preserves_ne hrel₃.toStateRel rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₃ tf htf 2, himm₃ tf htf 1⟩) hsup₃ hm₄
  have himm₄_2 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf htf; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃; exact himm_s₄ tf₃ tf htf₃ htf 2 (by decide) (himm₃ tf₃ htf₃ 2)
  obtain ⟨s₅, m₅, s₆, m₆, hs₅, hm₅, hs₆, hm₆, hsim₇, hs₇⟩ :=
    step_storageDead_storageLive_deref_ub_simulation hrel₄ hphase rfl
      (loc := 1) (ptrIdx := 2) (locDecl := u64Decl) (ptrDecl := rawPtrMutU64Decl)
      rfl (by decide) (by decide) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
      himm₄_2 (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl (.head _) rfl rfl
      rfl rfl (Or.inr (Or.inl ⟨constU64 7, ⟨7, 8⟩, rfl, rfl,
        Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl⟩))
  obtain ⟨m₇, msg, hm₇⟩ := stepRelLM3_1_of_anneal_ub hsim₇ hs₇
  exact ⟨s₁, s₂, s₃, s₄, s₅, s₆, m₁, m₂, m₃, m₄, m₅, m₆, m₇, msg,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hrel₃, hs₄, hm₄, hrel₄,
    hs₅, hm₅, hs₆, hm₆, hsim₇, hs₇, hm₇⟩

/-- `Runtime(PostCleanup)` MIR body exercising stale dereference **read**
(`_0 = move *_2`) after `StorageDead(_1); StorageLive(_1); _1 = const 7_u64`
(re-initializing the revived local before reading through the stale pointer). -/
def lm31ReviveReadAfterReinitBody : CapturedMir where
  defPath := "lm_3_1_witness::read_through_pointer_into_reinitialized_revived_local"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.storageDead 1),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 7)))),
        mkStmt (.assign (local_ 0) (.use (.move (derefLocal 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_storage_revive_read_ub_real_steps` (`LM-3.1` D2 Stale Deref Read After Revival & Re-Init)**:
Complete 5-step real-step execution of `lm31ReviveReadAfterReinitBody` from `StateRel`:
1. `_2 = &raw const _1` promotes `_1` (`42_u64`) to `lm31AllocId1`;
2. `StorageDead(_1)` retires `_1`'s allocation and disables `_2`'s tag;
3. `StorageLive(_1)` revives `_1` as `.uninit` (`StateRelLM3_1Revived`);
4. `_1 = const 7_u64` re-initializes the revived local `_1` to `7_u64` in lockstep
   (`step_const_assign_revived_lm3_1_simulation`), keeping `_2`'s old `lm31AllocId1`
   deallocated;
5. `_0 = move *_2` raises UAF UB in BOTH `stepMirFn` (`.fail .ub`) and
   `Miri.Interpreter.Step.step` (`.error (.undefinedBehavior msg)`) via
   `step_deref_revived_local_ub_simulation` (with `opKind = .move`). -/
theorem wit_lm3_1_storage_revive_read_ub_real_steps :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31ReviveReadAfterReinitBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      let s₀ : MachineState :=
        { frame := { blockIdx := 0, stmtIdx := 0,
                     locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit] }
          memory := (initMachineState b []).memory }
      let m₀ : AnnealStepState :=
        { stack := ⟨#[{ lm31AddrOfMiriFramePre with body := translateBody b, location := .mir ⟨0, 0⟩ }]⟩
          machine := AnnealMachine.empty }
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1Revived b s₄ m₄ [] (disableAllocMapLocal [entry] 1) ∧
      get? s₄.frame.locals 1 = some (.init (.scalar ⟨7, 8⟩)) ∧
      stepMirFn b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg)) := by
  let b := lm31ReviveReadAfterReinitBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let s₀ : MachineState :=
    { frame := { blockIdx := 0, stmtIdx := 0,
                 locals := [.uninit, .init (.scalar ⟨42, 8⟩), .uninit] }
      memory := (initMachineState b []).memory }
  let mf₀ : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
    { lm31AddrOfMiriFramePre with body := translateBody b, location := .mir ⟨0, 0⟩ }
  let m₀ : AnnealStepState := { stack := ⟨#[mf₀]⟩, machine := AnnealMachine.empty }
  have hrel₀ : StateRel b s₀ m₀ := by
    refine StateRel.mk mf₀ rfl rfl ⟨translateTy u64Ty, rfl⟩ ?_ rfl rfl rfl rfl rfl
      (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | 2 | _ + 3 => rintro ⟨⟩)
    refine ⟨rfl, rfl, rfl, rfl, ?_⟩
    intro i decl slot mls hdecl hslot hmls
    match i with
    | 0 | 2 =>
      have hs : slot = .uninit := by simpa [s₀, get?] using hslot.symm
      have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
        simpa [mf₀, lm31AddrOfMiriFramePre] using hmls.symm
      subst hs hm; exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
    | 1 =>
      have hd : decl = u64Decl := by simpa [b, lm31ReviveReadAfterReinitBody, get?] using hdecl.symm
      have hs : slot = .init (.scalar ⟨42, 8⟩) := by simpa [s₀, get?] using hslot.symm
      have hm : mls =
          { value := .live (.immediate (.scalar (.fromScalarInt lm31Scalar42)))
            layout := some (translateTy u64Ty) } := by
        simpa [mf₀, lm31AddrOfMiriFramePre] using hmls.symm
      subst hd hs hm
      exact .immediate _ _ (some (translateTy u64Ty)) (fun _ h => Option.some.inj h.symm)
        (Or.inr ⟨_, rfl, .scalar _ _ lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)⟩)
    | _ + 3 => simp [b, lm31ReviveReadAfterReinitBody, get?] at hdecl
  have himm₀ : ∀ tf, m₀.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf h k mls hmls mp hmp
    injection h with h₁; injection h₁ with h₂; subst h₂
    match k with
    | 0 | 1 | 2 => simp [mf₀, lm31AddrOfMiriFramePre] at hmls; subst hmls; cases hmp
    | _ + 3 => simp [mf₀, lm31AddrOfMiriFramePre] at hmls
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0] bor 2
  have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : s₀.memory.nextTag = 1 := rfl
  have hid₀ : (⟨m₀.machine.memory.nextAllocId, AllocIdSupplyReady.empty.nonzero⟩ :
      Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁_2 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
    fun tf htf => himm_s₁ _ tf rfl htf 2 (by decide) (himm₀ _ rfl 2)
  let s₂ := mkWitState b 2 [.uninit, .dead, .init ptr0] (disableLocalBorrows bor 1) 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_storageDead_lm3_1_simulation hrel₁ hphase rfl rfl (decl := u64Decl) rfl (by decide)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_storageDead_preserves hrel₁ rfl rfl (decl := u64Decl) rfl (by decide) hm₂
  have himm₂_2 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf htf; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf 2 (himm₁_2 tf₁ htf₁)
  have hrev₂ : StateRelLM3_1Revived b s₂ m₂ [] (disableAllocMapLocal
      [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] 1) := by
    refine hrel₂.retireDeadLocal 1 rfl (fun e he _ => ?_)
    have he' := List.mem_singleton.mp he; subst he'; rfl
  obtain ⟨s₃, m₃, hs₃_eq, hs₃, hm₃, himm_s₃, hrev₃⟩ :=
    step_storageLive_revived_lm3_1_simulation hrev₂ hphase rfl rfl (decl := u64Decl) rfl
      (fun _ h => nomatch h)
  have himm₃_2 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 :=
    himm_s₃ 2 (by decide) himm₂_2
  have himm₃_1 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 1 := by
    rcases hrev₂ with ⟨tf₂, hframes₂, _, _, hfr₂, _, _, _, _, _, _, _, _, _, _⟩
    obtain ⟨_, mls₂, _, hlt_mf₂, _, _, hmls_eq₂, hloc₂⟩ := hfr₂.lookup_local (idx := 1) (decl := u64Decl) rfl
    have hty₂ : ∃ ty, tf₂.body.locals[1]? = some ty := by
      rw [hfr₂.body_eq, translateBody_locals_getElem? b 1]; exact ⟨_, rfl⟩
    have hlive₂ : LocalAllocLive m₂.machine.memory (tf₂.locals[1]'hlt_mf₂).value := by
      rw [hmls_eq₂]; exact hloc₂.allocLive
    have hm_ev₂ : Miri.Interpreter.Step.evalStatement (annealStepHooks b.localDecls b.layouts) ()
        (translateStmt ⟨.storageLive 1, ""⟩) m₂ =
        ({ stack := ⟨#[{ tf₂ with
              locals := tf₂.locals.set 1
                { tf₂.locals[1]'hlt_mf₂ with value := .live (.immediate .uninit) } hlt_mf₂ }]⟩
           machine := { m₂.machine with
              memory := deallocLocalMemory m₂.machine.memory (tf₂.locals[1]'hlt_mf₂).value } },
          .ok ()) :=
      annealStepHooks_storageLive_any_eq (localDecls := b.localDecls) (layouts := b.layouts)
        hframes₂ hlt_mf₂ hty₂ hlive₂
    rw [miri_step_at_statement_ok _ hframes₂ hfr₂.body_eq hfr₂.location_eq rfl rfl hm_ev₂ rfl
      hfr₂.location_eq] at hm₃
    injection hm₃ with hm₃_eq _; subst hm₃_eq
    intro tf htf mls hmls mp hmp
    injection htf with h₁; injection h₁ with h₂; subst h₂
    dsimp only [] at hmls; rw [Array.getElem?_set_self] at hmls
    injection hmls with hmls'; rw [← hmls'] at hmp; cases hmp
  have hs₃_blk : s₃.frame.blockIdx = 0 := by rw [hs₃_eq]; rfl
  have hs₃_idx : s₃.frame.stmtIdx = 3 := by rw [hs₃_eq]; rfl
  have hs₃_l1 : get? s₃.frame.locals 1 = some .uninit := by rw [hs₃_eq]; rfl
  obtain ⟨s₄, m₄, hs₄_eq, hs₄, hm₄, hrev₄⟩ :=
    step_const_assign_revived_lm3_1_simulation hrev₃ hphase
      (by rw [hs₃_blk]; rfl) (by rw [hs₃_idx]; rfl)
      (dstDecl := u64Decl) (sc := ⟨7, 8⟩) rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl rfl
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide) rfl
      (fun h => by cases h) (fun h => by cases h) himm₃_1
      (by rw [hs₃_l1]; intro h; cases h) (fun _ h => nomatch h)
  have himm₄_2 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    rcases hrev₃ with ⟨tf₃, hframes₃, _, _, hfr₃, _, _, _, _, _, _, _, _, _, _⟩
    obtain ⟨slot_d, mls₃, _, hlt_d, hslot_d, hmls_d, hmls_d_eq, hloc_d⟩ :=
      hfr₃.lookup_local (idx := 1) (decl := u64Decl) rfl
    have hcache_d : ∀ l, (tf₃.locals[1]'hlt_d).layout = some l → l = translateTy u64Decl.ty b.layouts := by
      rw [hmls_d_eq]; exact hloc_d.cachedLayout_eq
    have hdst_ev := annealEvalPlace_unprojected (body := b) (dstIdx := 1) (dstDecl := u64Decl)
      hframes₃ hlt_d rfl hcache_d
    let tfa := cacheFrameLocalLayout tf₃ 1 hlt_d (translateTy u64Decl.ty b.layouts)
    obtain ⟨msc7, htry7, _⟩ := tryFromUInt_of_valid_canonical (sc := ⟨7, 8⟩)
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) (by decide)
    have hop_c : annealEvalOperand b.localDecls b.layouts (translateOperand (.constant (constU64 7)))
        (some (translateTy u64Decl.ty b.layouts)) { m₃ with stack := ⟨#[tfa]⟩ } =
        .ok ⟨.immediate (.scalar (.fromScalarInt msc7)), translateTy (constU64 7).ty b.layouts⟩
          { m₃ with stack := ⟨#[tfa]⟩ } := by
      with_unfolding_all
        unfold translateOperand translateConstOperand annealEvalOperand evalMirConstImmediate
        dsimp only [constU64]
        simp only [translateConstValue, translateConstScalar, get, getThe, MonadStateOf.get,
          EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure,
          stack_currentFrame?_singleton _ tfa rfl, Option.isNone_some,
          Bool.false_eq_true, ↓reduceIte, htry7]
        rfl
    have himm_d' := himm₃_1 tf₃ hframes₃ mls₃ hmls_d
    obtain ⟨oldImm, hmd_imm⟩ : ∃ oldImm, mls₃.value = .live (.immediate oldImm) := by
      have hs_u : slot_d = LocalSlot.uninit := Option.some.inj (hslot_d.symm.trans hs₃_l1)
      cases hloc_d with
      | rawPtr _ _ _ _ _ _ hty _ => cases hty
      | base hb =>
        cases hb with
        | dead _ _ => cases hs_u
        | indirect _ mp _ _ _ _ => exact absurd rfl (himm_d' mp)
        | immediate _ imm _ _ _ => exact ⟨imm, rfl⟩
    have hlt_da : 1 < tfa.locals.size := by simp [tfa, cacheFrameLocalLayout, hlt_d]
    have hd_tfa : tfa.locals[1]? =
        some ⟨.live (.immediate oldImm), some (translateTy u64Decl.ty b.layouts)⟩ := by
      simp only [tfa, cacheFrameLocalLayout, Array.getElem?_set_self, hmls_d_eq]
      rcases mls₃ with ⟨vd, ld⟩; dsimp only at hmd_imm; subst hmd_imm; rfl
    have hw_ok := annealWriteImmediate_live (val := .scalar (.fromScalarInt msc7))
      (m := { m₃ with stack := ⟨#[tfa]⟩ }) (id0 := tf₃.localsIdentity)
      (dstLay := translateTy u64Decl.ty b.layouts) rfl hlt_da (frame_getLocal_of_getElem? tfa 1 _ hd_tfa)
    have hm_ev₃ : Miri.Interpreter.Step.evalStatement (annealStepHooks b.localDecls b.layouts) ()
        (translateStmt (mkStmt (.assign (local_ 1) (.use (.constant (constU64 7)))))) m₃ =
        ({ m₃ with stack := ⟨#[{ tfa with
            locals := tfa.locals.set 1
              { tfa.locals[1]'hlt_da with value := .live (.immediate (.scalar (.fromScalarInt msc7))) }
              hlt_da }]⟩ }, .ok ()) := by
      have htr_dst : translatePlace (local_ 1) = ⟨1, #[]⟩ := rfl
      dsimp only [mkStmt]; rw [evalStatement_assign_use_eq, htr_dst]; unfold Miri.Interpreter.runRvalue
      rw [EStateM.bind_eq_ok hdst_ev, EStateM.bind_eq_ok hop_c]
      dsimp only [annealReadImmediate, Pure.pure, EStateM.pure, Bind.bind, EStateM.bind]; rw [hw_ok]
    have hloc_a : tfa.location = .mir ⟨s₃.frame.blockIdx, s₃.frame.stmtIdx⟩ := hfr₃.location_eq
    rw [miri_step_at_statement_ok _ hframes₃ hfr₃.body_eq hfr₃.location_eq
      (by rw [hs₃_blk]; rfl) (by rw [hs₃_idx]; rfl) hm_ev₃ rfl hloc_a] at hm₄
    injection hm₄ with hm₄_eq _; subst hm₄_eq
    intro tf htf mls hmls mp hmp
    injection htf with h₁; injection h₁ with h₂; subst h₂
    dsimp only [] at hmls; rw [Array.getElem?_set_ne _ (by decide : 1 ≠ 2)] at hmls
    dsimp only [tfa, cacheFrameLocalLayout] at hmls; rw [Array.getElem?_set_ne _ (by decide : 1 ≠ 2)] at hmls
    exact himm₃_2 tf₃ hframes₃ mls hmls mp hmp
  have hs₄_blk : s₄.frame.blockIdx = 0 := by rw [hs₄_eq, hs₃_eq]; rfl
  have hs₄_idx : s₄.frame.stmtIdx = 4 := by rw [hs₄_eq, hs₃_eq]; rfl
  have hs₄_l2 : get? s₄.frame.locals 2 = some (.init ptr0) := by rw [hs₄_eq, hs₃_eq]; rfl
  have hs₄_l1 : get? s₄.frame.locals 1 = some (.init (.scalar ⟨7, 8⟩)) := by rw [hs₄_eq, hs₃_eq]; rfl
  obtain ⟨hsim₅, hs₅⟩ := step_deref_revived_local_ub_simulation hrev₄ hphase
    (by rw [hs₄_blk]; rfl) (ptrIdx := 2) (ptrDecl := rawPtrConstU64Decl) rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₄_2
    (ptrVal := { allocId := 1, offsetBytes := 0 }) hs₄_l2 (.head _) (fun h => nomatch h) rfl
    (Or.inl ⟨0, u64Decl, MirAst.Operand.move, Or.inr rfl, rfl, rfl, by rw [hs₄_idx]; rfl⟩)
  obtain ⟨m₅, msg, hm₅⟩ := stepRelLM3_1_of_anneal_ub hsim₅ hs₅
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, m₅, msg,
    hs₁, hm₁, hrel₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrev₄, hs₄_l1, hs₅, hm₅⟩

/-! ### 8.3 D3 Real-Step Witnesses (`wit_lm3_1_anneal_deref_type_pun_simulation`, Offset-4 Read/Write & Partial OOB) -/

/-- **`wit_lm3_1_anneal_deref_type_pun_simulation` (`LM-3.1` D3 Real-Step Upgrade)**:
Complete 8-step lockstep execution of `lm31TypePunBody` from `initMachineState lm31TypePunBody []`
and `mkZeroArgEntryMiri lm31TypePunBody u32TyLM31`:
1..3. `StorageLive(1..3)` (`step_storageLive_lm3_1_simulation`);
4. `_1 = const 4294967301_u64` (`2^32 + 5`, `step_scalar_use_lm3_1_simulation`);
5. `_2 = &raw const _1` (`step_rawPtr_addrOf_lm3_1_simulation`);
6. `_3 = copy _2 as *const u32` (`step_cast_ptrToPtr_simulation`);
7. `_0 = copy *_3` (`step_deref_read_narrower_simulation`, extracting the 4 low-order
   little-endian bytes `5_u32`);
8. `return` (`step_terminator_goto_return_lm3_1_simulation`), returning
   `.retNormal (.scalar ⟨5, 4⟩)` in Anneal and `Miri.Memory.ScalarInt.ofUInt32 5`
   via `annealControlHooks.returnOperand` in `lean-miri`! -/
theorem wit_lm3_1_anneal_deref_type_pun_simulation :
    ∃ (s₁ s₂ s₃ s₄ s₅ s₆ s₇ : MachineState)
      (m₁ m₂ m₃ m₄ m₅ m₆ m₇ : AnnealStepState),
      let b := lm31TypePunBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      let s₀ := initMachineState b []
      let m₀ := mkZeroArgEntryMiri b u32TyLM31
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [] ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ [entry] ∧
      stepMirFn b s₅ = .step s₆ ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM3_1 b s₆ m₆ [entry] ∧
      stepMirFn b s₆ = .step s₇ ∧
      Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok true) ∧
      StateRelLM3_1 b s₇ m₇ (derefReadNextAllocMap s₆.frame.locals [entry] 3) ∧
      stepMirFn b s₇ = .retNormal (.scalar ⟨5, 4⟩) s₇.memory ∧
      Miri.Interpreter.Step.step hooks () m₇ = ({ m₇ with stack := ⟨#[]⟩ }, .ok true) ∧
      annealControlHooks.returnOperand () m₇ =
        (m₇, .ok (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 5))))) := by
  let b := lm31TypePunBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let s₀ := initMachineState b []
  let m₀ := mkZeroArgEntryMiri b u32TyLM31
  have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
    (mkZeroArgEntry_stateRel4 b u32DeclLM31 u64Decl rawPtrConstU64Decl rawPtrConstU32Decl rfl).toLM3_1
  have himm₀ := mkZeroArgEntry_all_immediate b u32TyLM31 (by decide)
  let s₁ := mkWitState b 1 [.uninit, .uninit, .dead, .dead] [] 1
  have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₀ hphase rfl rfl (decl := u64Decl) rfl (fun _ h => nomatch h)) hs₁
  obtain ⟨hmach₁, himm_s₁⟩ := step_storageLive_preserves_machine hrel₀ rfl rfl (decl := u64Decl) rfl
    (fun tf htf => himm₀ tf htf 1) hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₀, htf₀, _⟩ := id hrel₀; exact himm_s₁ tf₀ tf htf₀ htf k (himm₀ tf₀ htf₀ k)
  let s₂ := mkWitState b 2 [.uninit, .uninit, .uninit, .dead] [] 1
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₁ hphase rfl rfl (decl := rawPtrConstU64Decl) rfl (fun _ h => nomatch h)) hs₂
  obtain ⟨hmach₂, himm_s₂⟩ := step_storageLive_preserves_machine hrel₁ rfl rfl (decl := rawPtrConstU64Decl) rfl
    (fun tf htf => himm₁ tf htf 2) hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k)
  let s₃ := mkWitState b 3 [.uninit, .uninit, .uninit, .uninit] [] 1
  have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
  obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
    (step_storageLive_lm3_1_simulation hrel₂ hphase rfl rfl (decl := rawPtrConstU32Decl) rfl (fun _ h => nomatch h)) hs₃
  obtain ⟨hmach₃, himm_s₃⟩ := step_storageLive_preserves_machine hrel₂ rfl rfl (decl := rawPtrConstU32Decl) rfl
    (fun tf htf => himm₂ tf htf 3) hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k)
  let scVal : MirAst.ScalarInt := ⟨4294967301, 8⟩
  let s₄ := mkWitState b 4 [.uninit, .init (.scalar scVal), .uninit, .uninit] [] 1
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_scalar_use_lm3_1_simulation hrel₃ hphase rfl rfl (dstDecl := u64Decl) (valTy := u64Ty)
      rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf _ => constU64_wellTyped b tf 4294967301 (by decide)) (fun tf htf => himm₃ tf htf 1)) hs₄
  obtain ⟨hmach₄, himm_s₄⟩ := step_const_assign_preserves_machine hrel₃ rfl rfl (dstDecl := u64Decl) rfl
    rfl (by rintro ⟨⟩) (fun tf htf => himm₃ tf htf 1)
    (fun tf _ => constU64_wellTyped b tf 4294967301 (by decide))
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) hm₄
  have himm₄ : ∀ tf, m₄.stack.frames = #[tf] → ∀ k, IsImmediateFrameLocal tf k := by
    intro tf htf k; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃; exact himm_s₄ tf₃ tf htf₃ htf k (himm₃ tf₃ htf₃ k)
  have hmach₄_empty : m₄.machine = AnnealMachine.empty :=
    hmach₄.trans (hmach₃.trans (hmach₂.trans hmach₁))
  have hsup₄ : AllocIdSupplyReady m₄.machine.memory := by rw [hmach₄_empty]; exact AllocIdSupplyReady.empty
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
  let s₅ := mkWitState b 5 [.uninit, .init (.scalar scVal), .init ptr0, .uninit] bor 2
  have hs₅ : stepMirFn b s₄ = .step s₅ := rfl
  obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_lm3_1_simulation hrel₄ hphase rfl rfl
      (dstDecl := rawPtrConstU64Decl) (targetDecl := u64Decl) rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₄ tf htf 2, himm₄ tf htf 1⟩) hsup₄) hs₅
  have hna4 : m₄.machine.memory.nextAllocId = 1 := by rw [hmach₄_empty]; rfl
  have hid₄ : (⟨m₄.machine.memory.nextAllocId, hsup₄.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := by
    show ({ value := m₄.machine.memory.nextAllocId, nonzero := _ } : Miri.Memory.AllocId) = ⟨1, by decide⟩
    simp only [hna4]
  have htag₄ : s₄.memory.nextTag = 1 := rfl
  rw [htag₄, hid₄] at hrel₅
  obtain ⟨_, himm_s₅⟩ := step_rawPtr_addrOf_preserves_ne hrel₄.toStateRel rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₄ tf htf 2, himm₄ tf htf 1⟩) hsup₄ hm₅
  have himm₅ : ∀ tf, m₅.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₄, htf₄, _⟩ := id hrel₄; exact himm_s₅ tf₄ tf htf₄ htf k hne (himm₄ tf₄ htf₄ k)
  let s₆ := mkWitState b 6 [.uninit, .init (.scalar scVal), .init ptr0, .init ptr0] bor 2
  have hs₆ : stepMirFn b s₅ = .step s₆ := rfl
  obtain ⟨m₆, hm₆, hrel₆⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₅ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₅ tf htf 3 (by decide), himm₅ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₆
  obtain ⟨_, himm_s₆⟩ := step_assign_cast_ptrToPtr_preserves hrel₅ rfl rfl hm₆
  have himm₆ : ∀ tf, m₆.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₅, htf₅, _⟩ := id hrel₅; exact himm_s₆ tf₅ tf htf₅ htf k (himm₅ tf₅ htf₅ k hne)
  obtain ⟨hsim₇, hs₇_fn⟩ := step_deref_read_narrower_simulation hrel₆ hphase (Or.inl rfl) rfl rfl
    (dstDecl := u32DeclLM31) (ptrDecl := rawPtrConstU32Decl) (tgtDecl := u64Decl) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩)))
    (fun tf htf => ⟨himm₆ tf htf 0 (by decide), himm₆ tf htf 3 (by decide)⟩)
    (ptrVal := { allocId := 1, offsetBytes := 0 }) (oldSc := scVal)
    rfl (.head _) rfl (by rintro ⟨⟩) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (by decide) (by decide) (fun h => by cases h) (fun h => by cases h)
  have hs₇ := hs₇_fn (by rintro ⟨⟩)
  dsimp only [] at hs₇
  have hacc7 : (translateTy u32DeclLM31.ty b.layouts).layout.size.bytes.toNat = 4 := rfl
  have hbits7 : scVal.bits / 2 ^ (8 * ({ allocId := 1, offsetBytes := 0 } : ProvenancePtr).offsetBytes) %
      scalarModulus 4 = 5 := by decide
  rw [hacc7, hbits7] at hs₇
  let s₇ := advanceStmt s₆ (s₆.frame.locals.set 0 (.init (.scalar ⟨5, 4⟩)))
    ({ s₆.memory with borrows := (List.map AllocMapEntry.toBorrowEntry
        (derefReadNextAllocMap s₆.frame.locals
          [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] 3)) })
  have hs₇_eq : stepMirFn b s₆ = .step s₇ := hs₇
  obtain ⟨m₇, hm₇, hrel₇⟩ := stepRelLM3_1_of_anneal_step hsim₇ hs₇_eq
  obtain ⟨_, himm_s₇⟩ := step_assign_use_preserves hrel₆ (by rintro _ ⟨⟩) rfl rfl hm₇
  have himm₇_0 : ∀ tf, m₇.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 := by
    intro tf htf; obtain ⟨tf₆, htf₆, _⟩ := id hrel₆; exact himm_s₇ tf₆ tf htf₆ htf 0 (himm₆ tf₆ htf₆ 0 (by decide))
  have hsim₈ := step_terminator_goto_return_lm3_1_simulation hrel₇ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, u32DeclLM31, rfl, (by rintro _ _ ⟨⟩), (by decide), himm₇_0⟩))
  have ha₈ : stepMirFn b s₇ = .retNormal (.scalar ⟨5, 4⟩) s₇.memory := rfl
  rw [ha₈] at hsim₈
  generalize hm_res : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₇ = mRes at hsim₈
  cases hsim₈ with
  | retRoot decl₀ _ imm₀ _ m' hdecl₀ hop₀ himmRel₀ hm₈ =>
    subst hm₈
    have hd₀ : decl₀ = u32DeclLM31 := Option.some.inj hdecl₀.symm; subst hd₀
    cases himmRel₀ with
    | scalar _ msc hsc _ _ _ =>
      have hrel5 : ScalarRel ⟨5, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 5) :=
        ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
      have hmsc : msc = Miri.Memory.ScalarInt.ofUInt32 5 := scalarInt_eq_of_scalarRel hsc hrel5
      subst hmsc
      exact ⟨s₁, s₂, s₃, s₄, s₅, s₆, s₇, m₁, m₂, m₃, m₄, m₅, m₆, m₇,
        hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrel₄,
        hs₅, hm₅, hrel₅, hs₆, hm₆, hrel₆, hs₇_eq, hm₇, hrel₇, ha₈, hm_res, hop₀⟩

/-- `*mut u32` type & local decl + `u32` constant constructor for Episode 2 witnesses. -/
def rawPtrMutU32Ty : Ty := { kind := .rawPtr .mut (.uint .u32), layoutIdx := 0 }
def rawPtrMutU32Decl : LocalDecl := { mutability := .mut, ty := rawPtrMutU32Ty, debugName := none }
def constU32LM31 (n : Nat) : ConstOperand :=
  { ty := u32TyLM31, val := .scalar (.int ⟨n, 4⟩) }

private theorem constU32_wellTyped (body : CapturedMir)
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < scalarModulus 4) :
    WellTypedScalarOperand body tf (.constant (constU32LM31 n)) u32TyLM31 :=
  .constScalar (constU32LM31 n) ⟨n, 4⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩)))
    (Or.inr (Or.inr (Or.inl rfl))) hn rfl (fun h => nomatch h) (fun h => nomatch h)

/-- Parameterized 6-local Anneal pre-state (`_1` initialized to scalar `sc`,
locals `0, 2, 3, 4, 5` `.uninit`). -/
def mkSixLocalScalarAnnealPre (body : CapturedMir) (sc : MirAst.ScalarInt) : MachineState :=
  { frame :=
      { blockIdx := 0, stmtIdx := 0
        locals := [.uninit, .init (.scalar sc), .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState body []).memory }

/-- Parameterized 6-local `lean-miri` root frame matching `mkSixLocalScalarAnnealPre`. -/
def mkSixLocalScalarMiriFramePre (body : CapturedMir) (retTy local1Ty : Ty)
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
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def mkSixLocalScalarMiriPre (body : CapturedMir) (retTy local1Ty : Ty)
    (msc : Miri.Memory.ScalarInt) : AnnealStepState :=
  { stack := ⟨#[mkSixLocalScalarMiriFramePre body retTy local1Ty msc]⟩
    machine := AnnealMachine.empty }

private theorem mkSixLocalScalar_all_immediate (body : CapturedMir) (retTy local1Ty : Ty)
    (msc : Miri.Memory.ScalarInt) :
    ∀ tf, (mkSixLocalScalarMiriPre body retTy local1Ty msc).stack.frames = #[tf] →
      ∀ k, IsImmediateFrameLocal tf k := by
  intro tf h k mls hmls mp hmp
  injection h with h₁; injection h₁ with h₂; subst h₂
  match k with
  | 0 | 1 | 2 | 3 | 4 | 5 => simp [mkSixLocalScalarMiriFramePre] at hmls; subst hmls; cases hmp
  | _ + 6 => simp [mkSixLocalScalarMiriFramePre] at hmls

private theorem mkSixLocalScalar_stateRel
    (body : CapturedMir) (retTy : Ty) (d₀ d₁ d₂ d₃ d₄ d₅ : LocalDecl)
    (sc : MirAst.ScalarInt) (msc : Miri.Memory.ScalarInt)
    (hdecls : body.localDecls = [d₀, d₁, d₂, d₃, d₄, d₅])
    (hlay : body.layouts = emptyLayoutTable)
    (hrel : ScalarRel sc msc)
    (hsz : (translateTy d₁.ty emptyLayoutTable).layout.size = translateSizeBytes sc.sizeBytes)
    (hbool : d₁.ty.kind = .bool → sc.sizeBytes = 1 ∧ (sc.bits = 0 ∨ sc.bits = 1))
    (hchar : d₁.ty.kind = .char → sc.sizeBytes = 4 ∧ isValidCharCode sc.bits = true) :
    StateRel body (mkSixLocalScalarAnnealPre body sc)
      (mkSixLocalScalarMiriPre body retTy d₁.ty msc) := by
  refine StateRel.mk (mkSixLocalScalarMiriFramePre body retTy d₁.ty msc) rfl rfl
    ⟨translateTy retTy, rfl⟩ ?_ rfl rfl rfl rfl rfl
    (by intro i _ _ _ _ _ _ hi _; revert hi; match i with | 0 | 1 | 2 | 3 | 4 | 5 | _ + 6 => rintro ⟨⟩)
  refine ⟨rfl, rfl, by simp [mkSixLocalScalarAnnealPre, hdecls],
    by simp [mkSixLocalScalarMiriFramePre, hdecls], ?_⟩
  intro i decl slot mls hdecl hslot hmls
  rw [hdecls] at hdecl
  match i with
  | 0 | 2 | 3 | 4 | 5 =>
    have hs : slot = .uninit := by simpa [mkSixLocalScalarAnnealPre, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [mkSixLocalScalarMiriFramePre] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = d₁ := by simpa [get?] using hdecl.symm
    have hs : slot = .init (.scalar sc) := by simpa [mkSixLocalScalarAnnealPre, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt msc))),
          layout := some (translateTy d₁.ty) } := by
      simpa [mkSixLocalScalarMiriFramePre] using hmls.symm
    subst decl slot mls; rw [hlay]
    exact .immediate _ _ (some (translateTy d₁.ty)) (fun _ h => Option.some.inj h.symm)
      (Or.inr ⟨_, rfl, .scalar _ _ hrel hsz hbool hchar⟩)
  | _ + 6 => simp [get?] at hdecl

/-- `Runtime(PostCleanup)` MIR body exercising aligned non-zero offset `4` narrower
read (`_5 = copy *_4` -> `1_u32`), narrower deref **write** (`*_4 = const 9_u32`
splicing `9_u32` into the upper 4 bytes of `_1 : u64`), full-width `u64` deref
read (`_0 = copy *_2` -> `38654705669_u64 = 9 * 2^32 + 5`), and `return`. -/
def lm31TypePunOffset4AndWriteBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_type_pun_offset4_read_and_write"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU32Decl, rawPtrMutU32Decl, u32DeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU32Ty)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 5) (.use (.copy (derefLocal 4)))),
        mkStmt (.assign (derefLocal 4) (.use (.constant (constU32LM31 9)))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_type_pun_offset4_and_write_real_steps` (`LM-3.1` D3 Aligned Offset-4 Read & Narrower Write)**:
Complete 7-step lockstep execution of `lm31TypePunOffset4AndWriteBody` from `StateRel`:
extracts high word `1_u32` at aligned offset `4`, splices `9_u32` into bytes `[4, 8)`
producing `38654705669_u64` (`9 * 2^32 + 5`), reads back `38654705669_u64`, and returns
in lockstep across BOTH machines. -/
theorem wit_lm3_1_deref_type_pun_offset4_and_write_real_steps :
    ∃ (s₁ s₂ s₃ s₄ s₅ s₆ : MachineState) (m₁ m₂ m₃ m₄ m₅ m₆ : AnnealStepState)
      (allocMap₄ allocMap₅ allocMap₆ : List AllocMapEntry),
      let b := lm31TypePunOffset4AndWriteBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
      let s₀ := mkSixLocalScalarAnnealPre b ⟨4294967301, 8⟩
      let m₀ := mkSixLocalScalarMiriPre b u64Ty u64Ty (Miri.Memory.ScalarInt.ofUInt64 4294967301)
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [entry] ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ allocMap₄ ∧
      get? s₄.frame.locals 5 = some (.init (.scalar ⟨1, 4⟩)) ∧
      stepMirFn b s₄ = .step s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      StateRelLM3_1 b s₅ m₅ allocMap₅ ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨38654705669, 8⟩)) ∧
      stepMirFn b s₅ = .step s₆ ∧
      Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
      StateRelLM3_1 b s₆ m₆ allocMap₆ ∧
      stepMirFn b s₆ = .retNormal (.scalar ⟨38654705669, 8⟩) s₆.memory ∧
      Miri.Interpreter.Step.step hooks () m₆ = ({ m₆ with stack := ⟨#[]⟩ }, .ok true) ∧
      annealControlHooks.returnOperand () m₆ =
        (m₆, .ok (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt64 38654705669))))) := by
  let b := lm31TypePunOffset4AndWriteBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let scInit : MirAst.ScalarInt := ⟨4294967301, 8⟩
  let mscInit := Miri.Memory.ScalarInt.ofUInt64 4294967301
  have hscRel : ScalarRel scInit mscInit := ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b scInit)
      (mkSixLocalScalarMiriPre b u64Ty u64Ty mscInit) :=
    mkSixLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl rawPtrMutU32Decl
      rawPtrMutU32Decl u32DeclLM31 scInit mscInit rfl rfl hscRel rfl (fun h => nomatch h) (fun h => nomatch h)
  have himm₀ := mkSixLocalScalar_all_immediate b u64Ty u64Ty mscInit
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr4 := Value.ptr { allocId := 1, offsetBytes := 4 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar scInit), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b scInit) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkSixLocalScalarAnnealPre b scInit).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalScalarMiriPre b u64Ty u64Ty mscInit).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrMutU32Decl) (ptrDecl := rawPtrMutU32Decl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
      (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₃ := mkWitState b 3 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4, .uninit] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
  obtain ⟨m₃', hm₃_eq, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
  obtain ⟨_, himm_s₃⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
  obtain ⟨hsim₄, hs₄_fn⟩ := step_deref_read_narrower_simulation hrel₃ hphase (Or.inl rfl) rfl rfl
    (dstDecl := u32DeclLM31) (ptrDecl := rawPtrMutU32Decl) (tgtDecl := u64Decl) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩)))
    (fun tf htf => ⟨himm₃ tf htf 5 (by decide), himm₃ tf htf 4 (by decide)⟩)
    (ptrVal := { allocId := 1, offsetBytes := 4 }) (oldSc := scInit)
    rfl (.head _) rfl (by rintro ⟨⟩) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (by decide) (by decide) (fun h => by cases h) (fun h => by cases h)
  have hs₄ := hs₄_fn (by rintro ⟨⟩); dsimp only [] at hs₄
  have hacc4 : (translateTy u32DeclLM31.ty b.layouts).layout.size.bytes.toNat = 4 := rfl
  have hbits4 : scInit.bits / 2 ^ (8 * ({ allocId := 1, offsetBytes := 4 } : ProvenancePtr).offsetBytes) %
      scalarModulus 4 = 1 := by decide
  rw [hacc4, hbits4] at hs₄
  let map₄ := derefReadNextAllocMap s₃.frame.locals [rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1] 4
  let s₄ := advanceStmt s₃ (s₃.frame.locals.set 5 (.init (.scalar ⟨1, 4⟩)))
    ({ s₃.memory with borrows := List.map AllocMapEntry.toBorrowEntry map₄ })
  have hs₄_eq : stepMirFn b s₃ = .step s₄ := hs₄
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step hsim₄ hs₄_eq
  obtain ⟨_, himm_s₄⟩ := step_assign_use_preserves hrel₃ (by rintro _ ⟨⟩) rfl rfl hm₄
  have himm₄ : ∀ tf, m₄.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃; exact himm_s₄ tf₃ tf htf₃ htf k (himm₃ tf₃ htf₃ k hne)
  have hsim₅ := step_deref_write_narrower_simulation hrel₄ hphase rfl rfl
    (ptrDecl := rawPtrMutU32Decl) (tgtDecl := u64Decl) (valTy := u32TyLM31)
    rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
    (fun tf _ => .of_wt (constU32_wellTyped b tf 9 (by decide)))
    (fun tf htf => himm₄ tf htf 4 (by decide))
    (ptrVal := { allocId := 1, offsetBytes := 4 }) (oldSc := scInit)
    rfl (.head _) rfl (Or.inl rfl) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (by decide) (by decide) ⟨(fun h => by cases h), (fun h => by cases h)⟩
  let map₅ := derefWriteNextAllocMap s₄.frame.locals map₄ 4
  let scMerged : MirAst.ScalarInt := ⟨38654705669, 8⟩
  let s₅ := advanceStmt s₄ (s₄.frame.locals.set 1 (.init (.scalar scMerged)))
    ({ s₄.memory with borrows := List.map AllocMapEntry.toBorrowEntry map₅ })
  have hsp : spliceScalarSlice? scInit 4 ⟨9, 4⟩ = some scMerged := by
    refine (spliceScalarSlice?_eq_of_inbounds scInit ⟨9, 4⟩ 4
      (by decide) (by decide) (by decide)).1.trans ?_
    exact congrArg (fun bits => some ({ bits := bits, sizeBytes := 8 } : MirAst.ScalarInt))
      (by decide)
  have hs₅ : stepMirFn b s₄ = .step s₅ := by
    have hbb₄ : get? b.basicBlocks s₄.frame.blockIdx = some {
        statements := [
          mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
          mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU32Ty)),
          mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1)))),
          mkStmt (.assign (local_ 5) (.use (.copy (derefLocal 4)))),
          mkStmt (.assign (derefLocal 4) (.use (.constant (constU32LM31 9)))),
          mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))],
        terminator := mkTerm .return_, isCleanup := false } := rfl
    have hst₄ : get? [
          mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
          mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU32Ty)),
          mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1)))),
          mkStmt (.assign (local_ 5) (.use (.copy (derefLocal 4)))),
          mkStmt (.assign (derefLocal 4) (.use (.constant (constU32LM31 9)))),
          mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 2))))] s₄.frame.stmtIdx =
        some (mkStmt (.assign (derefLocal 4) (.use (.constant (constU32LM31 9))))) := rfl
    have hloc₄ : s₄.frame.locals =
        [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4,
          .init (.scalar ⟨1, 4⟩)] := rfl
    have hbor₄ : s₄.memory.borrows = bor := rfl
    have hprot₄ : s₄.memory.activeProtectors = .nil := rfl
    have hwrite₅ :
        writePlaceValue
          [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4,
            .init (.scalar ⟨1, 4⟩)]
          bor (derefLocal 4) (.scalar ⟨9, 4⟩) b.localDecls b.layouts =
        .ok [.uninit, .init (.scalar scMerged), .init ptr0, .init ptr0, .init ptr4,
          .init (.scalar ⟨1, 4⟩)] := by
      have hderef_eq :
          writePlaceValue
            [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4,
              .init (.scalar ⟨1, 4⟩)]
            bor (derefLocal 4) (.scalar ⟨9, 4⟩) b.localDecls b.layouts =
          writeStackThinPtrTypedDeref
            [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4,
              .init (.scalar ⟨1, 4⟩)]
            [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4,
              .init (.scalar ⟨1, 4⟩)]
            (rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1)
            { allocId := 1, offsetBytes := 4 }
            .nil (.scalar ⟨9, 4⟩) b.localDecls b.layouts
            (some u32TyLM31) (some u32TyLM31) := rfl
      rw [hderef_eq]
      unfold writeStackThinPtrTypedDeref
      have halign_ok :
          Bool.and
            (checkDerefAlign b.localDecls b.layouts
              (some (resolveTyWithLocalDecls b.localDecls b.layouts u32TyLM31)) 4)
            (Bool.and
              (checkTargetPlaceAlign b.localDecls b.layouts
                (some (resolveTyWithLocalDecls b.localDecls b.layouts u32TyLM31))
                (rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1)
                { allocId := 1, offsetBytes := 4 }
                (some (.scalar scInit)))
              (validateValueForTy? b.layouts
                (some (resolveTyWithLocalDecls b.localDecls b.layouts u32TyLM31))
                (.scalar ⟨9, 4⟩))) = true := rfl
      have hget1 :
          get? ([.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4,
            .init (.scalar ⟨1, 4⟩)] : List LocalSlot) 1 =
            some (.init (.scalar scInit)) := rfl
      have hrp :
          readProjectedForLocal
            [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4,
              .init (.scalar ⟨1, 4⟩)]
            b.localDecls b.layouts 1 (.scalar scInit) .nil = .ok (.scalar scInit) := rfl
      dsimp only [rawPtrBorrowEntry] at halign_ok
      dsimp only [stripTransparentProjections, rawPtrBorrowEntry]
      rw [hget1]; dsimp only []
      rw [halign_ok]; dsimp only [b, lm31TypePunOffset4AndWriteBody] at hrp ⊢
      rw [hrp]; dsimp only []
      rw [hsp]; rfl
    rw [stepMirFn_eq_of_not_other b s₄ rfl hphase]
    simp only [hbb₄, hst₄]
    unfold evalStmt evalRvalue evalOperand evalPlaceWrite
    dsimp only [mkStmt, constU32LM31, evalConstValue]
    rw [hprot₄, hloc₄, hbor₄, hwrite₅]
    rfl
  obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step hsim₅ hs₅
  obtain ⟨_, himm_s₅⟩ := step_assign_use_preserves hrel₄ (by rintro _ ⟨⟩) rfl rfl hm₅
  have himm₅ : ∀ tf, m₅.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₄, htf₄, _⟩ := id hrel₄; exact himm_s₅ tf₄ tf htf₄ htf k (himm₄ tf₄ htf₄ k hne)
  obtain ⟨hsim₆, hs₆_fn⟩ := step_deref_read_narrower_simulation hrel₅ hphase (Or.inl rfl) rfl rfl
    (dstDecl := u64Decl) (ptrDecl := rawPtrMutU64Decl) (tgtDecl := u64Decl) rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    (fun tf htf => ⟨himm₅ tf htf 0 (by decide), himm₅ tf htf 2 (by decide)⟩)
    (ptrVal := { allocId := 1, offsetBytes := 0 }) (oldSc := scMerged)
    rfl (.head _) rfl (by rintro ⟨⟩) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
    (by decide) (by decide) (fun h => by cases h) (fun h => by cases h)
  have hs₆ := hs₆_fn (by rintro ⟨⟩); dsimp only [] at hs₆
  have hacc6 : (translateTy u64Decl.ty b.layouts).layout.size.bytes.toNat = 8 := rfl
  have hbits6 : scMerged.bits / 2 ^ (8 * ({ allocId := 1, offsetBytes := 0 } : ProvenancePtr).offsetBytes) %
      scalarModulus 8 = 38654705669 := by decide
  rw [hacc6, hbits6] at hs₆
  let map₆ := derefReadNextAllocMap s₅.frame.locals map₅ 2
  let s₆ := advanceStmt s₅ (s₅.frame.locals.set 0 (.init (.scalar scMerged)))
    ({ s₅.memory with borrows := List.map AllocMapEntry.toBorrowEntry map₆ })
  have hs₆_eq : stepMirFn b s₅ = .step s₆ := hs₆
  obtain ⟨m₆, hm₆, hrel₆⟩ := stepRelLM3_1_of_anneal_step hsim₆ hs₆_eq
  obtain ⟨_, himm_s₆⟩ := step_assign_use_preserves hrel₅ (by rintro _ ⟨⟩) rfl rfl hm₆
  have himm₆_0 : ∀ tf, m₆.stack.frames = #[tf] → IsImmediateFrameLocal tf 0 := by
    intro tf htf; obtain ⟨tf₅, htf₅, _⟩ := id hrel₅; exact himm_s₆ tf₅ tf htf₅ htf 0 (himm₅ tf₅ htf₅ 0 (by decide))
  have hsim₇ := step_terminator_goto_return_lm3_1_simulation hrel₆ hphase rfl rfl rfl rfl
    (Or.inr (Or.inl ⟨rfl, u64Decl, rfl, (by rintro _ _ ⟨⟩), (by decide), himm₆_0⟩))
  have ha₇ : stepMirFn b s₆ = .retNormal (.scalar scMerged) s₆.memory := rfl
  rw [ha₇] at hsim₇
  generalize hm_res : Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₆ = mRes at hsim₇
  cases hsim₇ with
  | retRoot decl₀ _ imm₀ _ m' hdecl₀ hop₀ himmRel₀ hm₇ =>
    subst hm₇
    have hd₀ : decl₀ = u64Decl := Option.some.inj hdecl₀.symm; subst hd₀
    cases himmRel₀ with
    | scalar _ msc hsc _ _ _ =>
      have hrelM : ScalarRel scMerged (Miri.Memory.ScalarInt.ofUInt64 38654705669) :=
        ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
      have hmsc : msc = Miri.Memory.ScalarInt.ofUInt64 38654705669 := scalarInt_eq_of_scalarRel hsc hrelM
      subst hmsc
      exact ⟨s₁, s₂, s₃, s₄, s₅, s₆, m₁, m₂, m₃, m₄, m₅, m₆, map₄, map₅, map₆,
        hs₁, hm₁, hrel₁, hs₂, hm₂, hs₃, hm₃, hs₄_eq, hm₄, hrel₄, rfl,
        hs₅, hm₅, hrel₅, rfl, hs₆_eq, hm₆, hrel₆, ha₇, hm_res, hop₀⟩

/-- `Runtime(PostCleanup)` MIR body exercising partial-overlap OOB narrower read
(`*const u32` at byte offset `6` of an 8-byte `u64`, `6 + 4 = 10 > 8`, with `opKind = .move`). -/
def lm31TypePunPartialOobBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_read_narrower_partial_oob"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32DeclLM31, u64Decl, rawPtrConstU64Decl, rawPtrConstU8Decl, rawPtrConstU8Decl, rawPtrConstU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstU8Ty)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 6)))),
        mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrConstU32Ty)),
        mkStmt (.assign (local_ 0) (.use (.move (derefLocal 5))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_read_narrower_partial_oob_real_steps` (`LM-3.1` D3 Partial-Overlap OOB Read UB)**:
5-step real-step execution of `lm31TypePunPartialOobBody` from `StateRel`:
offsets `*const u8` to byte `6` of `_1 : u64`, casts to `*const u32`, and fails with
`.ub` in BOTH `stepMirFn` and `Miri.Interpreter.Step.step` (`6 + 4 = 10 > 8`) via
`step_deref_read_narrower_partial_oob_simulation` (with `opKind = .move`). -/
theorem wit_lm3_1_deref_read_narrower_partial_oob_real_steps :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31TypePunPartialOobBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u32TyLM31) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 6 } 8)) ∧
      stepMirFn b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg)) := by
  let b := lm31TypePunPartialOobBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ := mkSixLocal_stateRel b u32TyLM31 u32DeclLM31 rawPtrConstU64Decl
    rawPtrConstU8Decl rawPtrConstU8Decl rawPtrConstU32Decl rfl rfl
  have himm₀ := mkSixLocal_all_immediate b u32TyLM31
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr6 := Value.ptr { allocId := 1, offsetBytes := 6 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkSixLocalAnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalMiriPre b u32TyLM31).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrConstU8Decl) (ptrDecl := rawPtrConstU8Decl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 6 (by decide)))
      (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 6)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr6, .uninit] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
  obtain ⟨m₃', hm₃_eq, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
  obtain ⟨_, himm_s₃⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
  let s₄ := mkWitState b 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr6, .init ptr6] bor 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₃ tf htf 5 (by decide), himm₃ tf htf 4 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₄
  obtain ⟨_, himm_s₄⟩ := step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄_5 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 5 := by
    intro tf htf; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃; exact himm_s₄ tf₃ tf htf₃ htf 5 (himm₃ tf₃ htf₃ 5 (by decide))
  obtain ⟨hsim₅, hs₅⟩ := step_deref_read_narrower_partial_oob_simulation hrel₄ hphase (Or.inr rfl)
    rfl rfl (dstDecl := u32DeclLM31) (ptrDecl := rawPtrConstU32Decl) (tgtDecl := u64Decl)
    rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl himm₄_5
    (ptrVal := { allocId := 1, offsetBytes := 6 }) rfl (.head _) rfl rfl (by rintro ⟨⟩) (by decide)
  obtain ⟨m₅, msg, hm₅⟩ := stepRelLM3_1_of_anneal_ub hsim₅ hs₅
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, m₅, msg,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrel₄, rfl, hs₅, hm₅⟩

/-! ### 8.4 D4 Real-Step Witness (`wit_lm3_1_deref_write_misaligned_real_steps`) -/

/-- `Runtime(PostCleanup)` MIR body exercising misaligned dereference **write**
(`_2 = &raw mut _1; _3 = copy _2 as *mut u8; _4 = Offset(copy _3, const 2_usize);
_5 = copy _4 as *mut u32; *_5 = const 7_u32`). -/
def lm31DerefWriteMisalignedBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_write_misaligned_real"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU8Decl, rawPtrMutU8Decl, rawPtrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 2)))),
        mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrMutU32Ty)),
        mkStmt (.assign (derefLocal 5) (.use (.constant (constU32LM31 7))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_write_misaligned_real_steps` (`LM-3.1` D4 Misaligned Deref Write UB)**:
5-step real-step execution of `lm31DerefWriteMisalignedBody` from `StateRel`:
at byte offset `2` inside 8-byte `_1 : u64` (`2 + 4 = 6 ≤ 8`, misaligned for `Align = 4`),
`*_5 = const 7_u32` fails with `.ub` in BOTH `stepMirFn` and `Miri.Interpreter.Step.step`
via `step_deref_write_misaligned_simulation`. -/
theorem wit_lm3_1_deref_write_misaligned_real_steps :
    ∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState) (msg : String),
      let b := lm31DerefWriteMisalignedBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ [entry] ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 2 } 8)) ∧
      stepMirFn b s₄ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg)) := by
  let b := lm31DerefWriteMisalignedBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ := mkSixLocal_stateRel b u64Ty u64Decl rawPtrMutU64Decl
    rawPtrMutU8Decl rawPtrMutU8Decl rawPtrMutU32Decl rfl rfl
  have himm₀ := mkSixLocal_all_immediate b u64Ty
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkSixLocalAnnealPre b).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalMiriPre b u64Ty).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrMutU8Decl) (ptrDecl := rawPtrMutU8Decl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 2 (by decide)))
      (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 2)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .uninit] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
  obtain ⟨m₃', hm₃_eq, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
  obtain ⟨_, himm_s₃⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
  let s₄ := mkWitState b 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .init ptr2] bor 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₃ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₃ tf htf 5 (by decide), himm₃ tf htf 4 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₄
  obtain ⟨_, himm_s₄⟩ := step_assign_cast_ptrToPtr_preserves hrel₃ rfl rfl hm₄
  have himm₄_5 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 5 := by
    intro tf htf; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃; exact himm_s₄ tf₃ tf htf₃ htf 5 (himm₃ tf₃ htf₃ 5 (by decide))
  obtain ⟨tf₄, htf₄, _, _, _, _, _, _, _, _, halloc₄, _⟩ := id hrel₄
  obtain ⟨_, _, hsh₄⟩ := (halloc₄.local_alloc_sync tf₄ htf₄ _ (.head _)).1
    (.init (.scalar ⟨42, 8⟩)) rfl (by rintro ⟨⟩)
  obtain ⟨la₄, hfind₄, _, _, hshape₄⟩ := hsh₄ u64Decl rfl
  obtain ⟨hsim₅, hs₅⟩ := step_deref_write_misaligned_simulation hrel₄ hphase rfl rfl
    (ptrDecl := rawPtrMutU32Decl) (valTy := u32TyLM31)
    rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
    (fun tf _ => .of_wt (constU32_wellTyped b tf 7 (by decide)))
    himm₄_5 (ptrVal := { allocId := 1, offsetBytes := 2 }) rfl (.head _) rfl hfind₄
    (by rw [hshape₄.byteSize_eq]; decide) (by decide)
  obtain ⟨m₅, msg, hm₅⟩ := stepRelLM3_1_of_anneal_ub hsim₅ hs₅
  exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, m₅, msg,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrel₄, rfl, hs₅, hm₅⟩

/-! ### 8.5 D5 Real-Step Witnesses (Invalid `char` Deref Write & Raw-Overwritten `bool`/`char` Audit) -/

def rawPtrMutCharTy : Ty := { kind := .rawPtr .mut .char, layoutIdx := 0 }
def rawPtrMutCharDecl : LocalDecl := { mutability := .mut, ty := rawPtrMutCharTy, debugName := none }
def constInvalidCharD800LM31 : ConstOperand :=
  { ty := charTyLM31, val := .scalar (.int ⟨0xD800, 4⟩) }
def constU8LM31 (n : Nat) : ConstOperand :=
  { ty := u8TyLM31, val := .scalar (.int ⟨n, 1⟩) }

/-- `Runtime(PostCleanup)` MIR body writing invalid UTF-16 surrogate `0xD800` through `*mut char`. -/
def lm31DerefWriteInvalidCharBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_write_invalid_char_surrogate"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32DeclLM31, u32DeclLM31, rawPtrMutU32Decl, rawPtrMutCharDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutCharTy)),
        mkStmt (.assign (derefLocal 3) (.use (.constant constInvalidCharD800LM31)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_write_invalid_char_real_steps` (`LM-3.1` D5 Invalid `char` Deref Write UB)**:
3-step real-step execution of `lm31DerefWriteInvalidCharBody` from `StateRel`:
`*_3 = const (0xD800 : char)` fails with `.ub` in Anneal and
`.error (.undefinedBehavior "writing invalid value")` in `lean-miri` via
`step_deref_write_invalid_char_simulation`. -/
theorem wit_lm3_1_deref_write_invalid_char_real_steps :
    ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      let b := lm31DerefWriteInvalidCharBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
      stepMirFn b (mkFourLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkFourLocalScalarMiriPre b u32TyLM31 u32TyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      StepRelLM3_1 b m₂ [entry] (stepMirFn b s₂) (Miri.Interpreter.Step.step hooks () m₂) ∧
      stepMirFn b s₂ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "writing invalid value")) := by
  let b := lm31DerefWriteInvalidCharBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let msc41 := Miri.Memory.ScalarInt.ofUInt32 0x41
  have hrel41 : ScalarRel ⟨0x41, 4⟩ msc41 := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨0x41, 4⟩)
      (mkFourLocalScalarMiriPre b u32TyLM31 u32TyLM31 msc41) :=
    mkFourLocalScalar_stateRel b u32TyLM31 u32DeclLM31 u32DeclLM31 rawPtrMutU32Decl rawPtrMutCharDecl
      ⟨0x41, 4⟩ msc41 rfl rfl hrel41 rfl (fun h => nomatch h) (fun h => nomatch h)
  have himm₀ := mkFourLocalScalar_all_immediate b u32TyLM31 u32TyLM31 msc41
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkFourLocalScalarAnnealPre b ⟨0x41, 4⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkFourLocalScalarMiriPre b u32TyLM31 u32TyLM31 msc41).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .init ptr0] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂_3 : ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf 3 := by
    intro tf htf; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf 3 (himm₁ tf₁ htf₁ 3 (by decide))
  obtain ⟨hsim₃, hs₃, m₃, hm₃⟩ := step_deref_write_invalid_char_simulation hrel₂ hphase rfl rfl
    (ptrDecl := rawPtrMutCharDecl) (tgtDecl := u32DeclLM31) rfl rfl rfl rfl (by decide) (by decide)
    himm₂_3 (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl (.head _) rfl (Or.inl rfl)
    rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (by decide) (by decide) (by rintro ⟨⟩)
  exact ⟨s₁, s₂, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, hsim₃, hs₃, hm₃⟩

/-- Parameterized `Runtime(PostCleanup)` MIR body for the D5 raw-overwrite `bool` audit:
promotes `_1 : bool` (`false`), casts to `*mut u8`, writes `2_u8` (`*_3 = const 2_u8`),
and then either dereferences `move *_2` (`useDeref = true`) or directly copies `copy _1`
(`useDeref = false`). -/
def lm31RawOverwriteBoolBody (useDeref : Bool) : CapturedMir where
  defPath := if useDeref then "lm_3_1_witness::raw_overwrite_bool_deref"
             else "lm_3_1_witness::raw_overwrite_bool_direct_copy"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [boolDeclLM31, boolDeclLM31, rawPtrMutBoolDecl, rawPtrMutU8Decl, u8DeclLM31, u8DeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (derefLocal 3) (.use (.constant (constU8LM31 2)))),
        mkStmt (.assign (local_ 0)
          (.use (if useDeref then .move (derefLocal 2) else .copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- Parameterized `Runtime(PostCleanup)` MIR body for the D5 raw-overwrite `char` audit:
promotes `_1 : char` (`'A'`), casts to `*mut u32`, writes surrogate `0xD800_u32`,
and then either dereferences `copy *_2` (`useDeref = true`), directly copies `copy _1`
(`useDeref = false, useMove = false`), or directly moves `move _1`
(`useDeref = false, useMove = true`). -/
def lm31RawOverwriteCharBody (useDeref : Bool) (useMove : Bool := false) : CapturedMir where
  defPath := if useDeref then "lm_3_1_witness::raw_overwrite_char_deref"
             else if useMove then "lm_3_1_witness::raw_overwrite_char_direct_move"
             else "lm_3_1_witness::raw_overwrite_char_direct_copy"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [charDeclLM31, charDeclLM31, rawPtrMutCharDecl, rawPtrMutU32Decl, u32DeclLM31, u32DeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU32Ty)),
        mkStmt (.assign (derefLocal 3) (.use (.constant (constU32LM31 0xD800)))),
        mkStmt (.assign (local_ 0)
          (.use (if useDeref then .copy (derefLocal 2)
                 else if useMove then .move (local_ 1)
                 else .copy (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

private theorem rawOverwriteBool_reach_state (useDeref : Bool) :
    let b := lm31RawOverwriteBoolBody useDeref
    let hooks := annealStepHooks b.localDecls b.layouts
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msc_raw : Miri.Memory.ScalarInt),
      stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0, 1⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkSixLocalScalarMiriPre b boolTyLM31 boolTyLM31 (Miri.Memory.ScalarInt.ofUInt8 0)) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      s₃.frame.blockIdx = 0 ∧ s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 0 = some .uninit ∧
      get? s₃.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      (∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 2) ∧
      RawOverwrittenScalarState b s₃ m₃ (updateAllocMapOnWrite [entry] 1 (some 1)) 1 lm31AllocId1 ⟨2, 1⟩ msc_raw := by
  let b := lm31RawOverwriteBoolBody useDeref
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let msc0 := Miri.Memory.ScalarInt.ofUInt8 0
  have hrel_sc : ScalarRel ⟨0, 1⟩ msc0 := ⟨Or.inl rfl, by decide, rfl, rfl⟩
  have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b ⟨0, 1⟩)
      (mkSixLocalScalarMiriPre b boolTyLM31 boolTyLM31 msc0) :=
    mkSixLocalScalar_stateRel b boolTyLM31 boolDeclLM31 boolDeclLM31 rawPtrMutBoolDecl
      rawPtrMutU8Decl u8DeclLM31 u8DeclLM31 ⟨0, 1⟩ msc0 rfl rfl hrel_sc rfl
      (fun _ => ⟨rfl, Or.inl rfl⟩) (fun h => nomatch h)
  have himm₀ := mkSixLocalScalar_all_immediate b boolTyLM31 boolTyLM31 msc0
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0, 1⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0, 1⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inl rfl) (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkSixLocalScalarAnnealPre b ⟨0, 1⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalScalarMiriPre b boolTyLM31 boolTyLM31 msc0).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inl rfl) (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨0, 1⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨s₃, m₃, msc_raw, hs₃_eq, hs₃, hm₃, hraw₃⟩ :=
    step_deref_raw_write_into_bool_or_char_correspondence hrel₂ hphase rfl rfl
      (ptrDecl := rawPtrMutU8Decl) (tgtDecl := boolDeclLM31) (rawKind := .uint .u8)
      (rawSc := ⟨2, 1⟩) rfl rfl rfl rfl rfl
      (Or.inl ⟨rfl, Or.inl rfl, rfl, by decide⟩)
      (fun tf htf => himm₂ tf htf 3 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl rfl (.head _) rfl (Or.inl rfl) (by rintro ⟨⟩)
  obtain ⟨_, himm_s₃⟩ := step_assign_use_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃_2 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf htf; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf 2 (himm₂ tf₂ htf₂ 2 (by decide))
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, msc_raw, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃,
    by rw [hs₃_eq]; rfl, by rw [hs₃_eq]; rfl, by rw [hs₃_eq]; rfl, by rw [hs₃_eq]; rfl, himm₃_2, hraw₃⟩

private theorem rawOverwriteChar_reach_state (useDeref : Bool) (useMove : Bool := false) :
    let b := lm31RawOverwriteCharBody useDeref useMove
    let hooks := annealStepHooks b.localDecls b.layouts
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState) (msc_raw : Miri.Memory.ScalarInt),
      stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      s₃.frame.blockIdx = 0 ∧ s₃.frame.stmtIdx = 3 ∧
      get? s₃.frame.locals 0 = some .uninit ∧
      get? s₃.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      (∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 2) ∧
      RawOverwrittenScalarState b s₃ m₃ (updateAllocMapOnWrite [entry] 1 (some 1)) 1 lm31AllocId1 ⟨0xD800, 4⟩ msc_raw := by
  let b := lm31RawOverwriteCharBody useDeref useMove
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let mscA := Miri.Memory.ScalarInt.ofUInt32 0x41
  have hrel_sc : ScalarRel ⟨0x41, 4⟩ mscA := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩)
      (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 mscA) :=
    mkSixLocalScalar_stateRel b charTyLM31 charDeclLM31 charDeclLM31 rawPtrMutCharDecl
      rawPtrMutU32Decl u32DeclLM31 u32DeclLM31 ⟨0x41, 4⟩ mscA rfl rfl hrel_sc rfl
      (fun h => nomatch h) (fun _ => ⟨rfl, by decide⟩)
  have himm₀ := mkSixLocalScalar_all_immediate b charTyLM31 charTyLM31 mscA
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inl rfl)) (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 mscA).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inl rfl)) (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨s₃, m₃, msc_raw, hs₃_eq, hs₃, hm₃, hraw₃⟩ :=
    step_deref_raw_write_into_bool_or_char_correspondence hrel₂ hphase rfl rfl
      (ptrDecl := rawPtrMutU32Decl) (tgtDecl := charDeclLM31) (rawKind := .uint .u32)
      (rawSc := ⟨0xD800, 4⟩) rfl rfl rfl rfl rfl
      (Or.inr ⟨rfl, Or.inl rfl, rfl, by decide⟩)
      (fun tf htf => himm₂ tf htf 3 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 0 }) rfl rfl (.head _) rfl (Or.inl rfl) (by rintro ⟨⟩)
  obtain ⟨_, himm_s₃⟩ := step_assign_use_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃_2 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf htf; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf 2 (himm₂ tf₂ htf₂ 2 (by decide))
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, msc_raw, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃,
    by rw [hs₃_eq]; rfl, by rw [hs₃_eq]; rfl, by rw [hs₃_eq]; rfl, by rw [hs₃_eq]; rfl, himm₃_2, hraw₃⟩

/-- **`wit_lm3_1_raw_overwritten_bool_and_char_real_steps` (`LM-3.1` D5 Multi-Step Raw-Overwrite Audit)**:
End-to-end 4-step real-step execution auditing BOTH `bool` (`*mut u8 -> 2_u8`) and
`char` (`*mut u32 -> 0xD800_u32`):
1. `bool` + `move *_2` (`lm31RawOverwriteBoolBody true`): UB in BOTH machines;
2. `bool` + `copy _1` (`lm31RawOverwriteBoolBody false`): UB (`"reading invalid value"`) in BOTH machines;
3. `char` + `copy *_2` (`lm31RawOverwriteCharBody true`): UB in BOTH machines;
4. `char` + `copy _1` (`lm31RawOverwriteCharBody false false`): documented `validateLoadedValue` boundary
   (`stepMirFn` steps while `lean-miri` reports `"reading invalid value"`);
5. `char` + `move _1` (`lm31RawOverwriteCharBody false true`): documented `validateLoadedValue` boundary
   for `.move` (`stepMirFn` steps and deinitializes `_1` while `lean-miri` reports `"reading invalid value"`). -/
theorem wit_lm3_1_raw_overwritten_bool_and_char_real_steps :
    (-- (1) `bool` + `move *_2` -> UB in both
     let b := lm31RawOverwriteBoolBody true
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ m₁ m₂ m₃ m₄ msg,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0, 1⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b boolTyLM31 boolTyLM31 (Miri.Memory.ScalarInt.ofUInt8 0)) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior msg))) ∧
    (-- (2) `bool` + `copy _1` -> UB ("reading invalid value") in both
     let b := lm31RawOverwriteBoolBody false
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ m₁ m₂ m₃ m₄,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0, 1⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b boolTyLM31 boolTyLM31 (Miri.Memory.ScalarInt.ofUInt8 0)) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior "reading invalid value"))) ∧
    (-- (3) `char` + `copy *_2` -> UB in both
     let b := lm31RawOverwriteCharBody true
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ m₁ m₂ m₃ m₄ msg,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior msg))) ∧
    (-- (4) `char` + `copy _1` -> documented `validateLoadedValue` direct-copy boundary
     let b := lm31RawOverwriteCharBody false false
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ s₄ m₁ m₂ m₃ m₄,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .step s₄ ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior "reading invalid value"))) ∧
    (-- (5) `char` + `move _1` -> documented `validateLoadedValue` direct-move boundary
     let b := lm31RawOverwriteCharBody false true
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ s₄ m₁ m₂ m₃ m₄,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .step s₄ ∧
       get? s₄.frame.locals 1 = some .uninit ∧
       get? s₄.frame.locals 0 = some (.init (.scalar ⟨0xD800, 4⟩)) ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior "reading invalid value"))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, _, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hblk, hidx, _, hl2, himm₂, hraw⟩ :=
      rawOverwriteBool_reach_state true
    obtain ⟨hsim₄, hs₄⟩ := step_raw_overwritten_deref_invalid_bool_or_char_simulation hraw
      (fun _ h => nomatch h) (Or.inr rfl) (by rw [hblk]; rfl) (by rw [hidx]; rfl)
      (dstDecl := boolDeclLM31) (ptrDecl := rawPtrMutBoolDecl) (tgtDecl := boolDeclLM31)
      rfl rfl rfl rfl (by decide) (by decide) himm₂ hl2 rfl (.head _) rfl rfl rfl
      (Or.inl ⟨rfl, rfl, rfl, by decide, by decide⟩)
    obtain ⟨m₄, msg, hm₄⟩ := stepRelLM3_1_of_anneal_ub hsim₄ hs₄
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, msg, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄⟩
  · obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, _, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hblk, hidx, _, _, _, hraw⟩ :=
      rawOverwriteBool_reach_state false
    obtain ⟨_, hs₄, m₄, hm₄⟩ := step_raw_overwritten_direct_copy_invalid_bool_simulation hraw
      (fun _ h => nomatch h) (Or.inl rfl) (by rw [hblk]; rfl) (by rw [hidx]; rfl)
      (dstDecl := boolDeclLM31) (locDecl := boolDeclLM31) rfl rfl rfl rfl (by decide) rfl (by decide) (by decide)
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄⟩
  · obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, _, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hblk, hidx, _, hl2, himm₂, hraw⟩ :=
      rawOverwriteChar_reach_state true
    obtain ⟨hsim₄, hs₄⟩ := step_raw_overwritten_deref_invalid_bool_or_char_simulation hraw
      (fun _ h => nomatch h) (Or.inl rfl) (by rw [hblk]; rfl) (by rw [hidx]; rfl)
      (dstDecl := charDeclLM31) (ptrDecl := rawPtrMutCharDecl) (tgtDecl := charDeclLM31)
      rfl rfl rfl rfl (by decide) (by decide) himm₂ hl2 rfl (.head _) rfl rfl rfl
      (Or.inr ⟨rfl, rfl, rfl, by decide, by decide⟩)
    obtain ⟨m₄, msg, hm₄⟩ := stepRelLM3_1_of_anneal_ub hsim₄ hs₄
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, msg, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄⟩
  · obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, _, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hblk, hidx, hl0, _, _, hraw⟩ :=
      rawOverwriteChar_reach_state false false
    obtain ⟨hs₄, m₄, hm₄⟩ := step_raw_overwritten_direct_copy_invalid_char_divergence hraw
      (fun _ h => nomatch h) (Or.inl rfl) (by rw [hblk]; rfl) (by rw [hidx]; rfl)
      (dstDecl := charDeclLM31) (locDecl := charDeclLM31) rfl rfl rfl rfl (by decide)
      (by rw [hl0]; rintro ⟨⟩) rfl (by decide) (by decide)
    exact ⟨s₁, s₂, s₃, _, m₁, m₂, m₃, m₄, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄⟩
  · obtain ⟨s₁, s₂, s₃, m₁, m₂, m₃, _, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hblk, hidx, hl0, _, _, hraw⟩ :=
      rawOverwriteChar_reach_state false true
    have hlen₃ : s₃.frame.locals.length = 6 := by
      rcases hraw with ⟨_, _, _, _, haf_len, _⟩; exact haf_len
    obtain ⟨hs₄, m₄, hm₄⟩ := step_raw_overwritten_direct_copy_invalid_char_divergence hraw
      (fun _ h => nomatch h) (Or.inr rfl) (by rw [hblk]; rfl) (by rw [hidx]; rfl)
      (dstDecl := charDeclLM31) (locDecl := charDeclLM31) rfl rfl rfl rfl (by decide)
      (by rw [hl0]; rintro ⟨⟩) rfl (by decide) (by decide)
    refine ⟨s₁, s₂, s₃, _, m₁, m₂, m₃, m₄, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, ?_, ?_, hm₄⟩
    · dsimp only [advanceStmt, offsetAfterLhsLocals]
      rw [get?_eq_getElem?, List.getElem?_set_ne (by decide),
        List.getElem?_set_self (by omega)]
    · dsimp only [advanceStmt, offsetAfterLhsLocals]
      rw [get?_eq_getElem?, List.getElem?_set_self (by simp [hlen₃])]

/-- `Runtime(PostCleanup)` MIR body exercising narrower / offset invalid `char` deref read
(`*const char` at byte offset `4` of `_1 : u64` holding `0x0000D800_00000041 = 237494511599681`,
with `Operand.move`). -/
def lm31NarrowerInvalidCharReadBody : CapturedMir where
  defPath := "lm_3_1_witness::deref_read_narrower_invalid_char_offset4"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [charDeclLM31, u64Decl, rawPtrConstU64Decl, rawPtrConstCharDecl, rawPtrConstCharDecl, rawPtrConstCharDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstCharTy)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 0) (.use (.move (derefLocal 4))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_read_narrower_invalid_char_real_steps` (`LM-3.1` D3 × D5 Narrower Offset Invalid `char` Read UB)**:
4-step real-step execution of `lm31NarrowerInvalidCharReadBody` from `StateRel`:
promotes `_1 : u64` (`0x0000D800_00000041`), casts `*const u64 -> *const char`,
offsets by `+1_usize` (`offsetBytes = 4`), and fails on `_0 = move *_4` with `.ub`
in Anneal and `"reading invalid value"` in `lean-miri` via
`step_deref_read_narrower_invalid_bool_or_char_simulation`! -/
theorem wit_lm3_1_deref_read_narrower_invalid_char_real_steps :
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
      let b := lm31NarrowerInvalidCharReadBody
      let hooks := annealStepHooks b.localDecls b.layouts
      let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
      stepMirFn b (mkSixLocalScalarAnnealPre b ⟨237494511599681, 8⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkSixLocalScalarMiriPre b charTyLM31 u64Ty (Miri.Memory.ScalarInt.ofUInt64 237494511599681)) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      StateRelLM3_1 b s₃ m₃ [entry] ∧
      get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 4 } 8)) ∧
      StepRelLM3_1 b m₃ [entry] (stepMirFn b s₃) (Miri.Interpreter.Step.step hooks () m₃) ∧
      stepMirFn b s₃ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₃ =
        (m₄, .error (.undefinedBehavior "reading invalid value")) := by
  let b := lm31NarrowerInvalidCharReadBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let scInit : MirAst.ScalarInt := ⟨237494511599681, 8⟩
  let mscInit := Miri.Memory.ScalarInt.ofUInt64 237494511599681
  have hscRel : ScalarRel scInit mscInit := ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
  have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b scInit)
      (mkSixLocalScalarMiriPre b charTyLM31 u64Ty mscInit) :=
    mkSixLocalScalar_stateRel b charTyLM31 charDeclLM31 u64Decl rawPtrConstU64Decl
      rawPtrConstCharDecl rawPtrConstCharDecl rawPtrConstCharDecl scInit mscInit rfl rfl hscRel rfl
      (fun h => nomatch h) (fun h => nomatch h)
  have himm₀ := mkSixLocalScalar_all_immediate b charTyLM31 u64Ty mscInit
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr4 := Value.ptr { allocId := 1, offsetBytes := 4 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar scInit), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b scInit) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkSixLocalScalarAnnealPre b scInit).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalScalarMiriPre b charTyLM31 u64Ty mscInit).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrConstCharDecl) (ptrDecl := rawPtrConstCharDecl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inl rfl)) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
      (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₃ := mkWitState b 3 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4, .uninit] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
  obtain ⟨m₃', hm₃_eq, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
  obtain ⟨_, himm_s₃⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃_4 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 4 := by
    intro tf htf; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf 4 (himm₂ tf₂ htf₂ 4 (by decide))
  obtain ⟨hsim₄, hs₄, m₄, hm₄⟩ :=
    step_deref_read_narrower_invalid_bool_or_char_simulation hrel₃ hphase (Or.inr rfl)
      rfl rfl (dstDecl := charDeclLM31) (ptrDecl := rawPtrConstCharDecl) (tgtDecl := u64Decl)
      rfl rfl rfl himm₃_4 (ptrVal := { allocId := 1, offsetBytes := 4 }) (oldSc := scInit)
      rfl (.head _) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩)
  exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hrel₃, rfl, hsim₄, hs₄, hm₄⟩

/-! ### 8.6 D6 Real-Step Witnesses (Non-Byte Negative `isize` Stride & Negative OOB Underflow UB) -/

/-- `Runtime(PostCleanup)` MIR body exercising non-byte (`*const u32`, stride `4`)
negative `.isize` offset with `Operand.move` (`Offset(move _4, const -1_isize)`
from `offsetBytes = 8` back to `offsetBytes = 4`, reading `1_u32`). -/
def lm31OffsetNegStrideBody : CapturedMir where
  defPath := "lm_3_1_witness::binop_offset_neg_isize_u32_stride"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32DeclLM31, u64Decl, rawPtrConstU64Decl, rawPtrConstU32Decl, rawPtrConstU32Decl, rawPtrConstU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstU32Ty)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 2)))),
        mkStmt (.assign (local_ 5) (.binaryOp .offset (.move (local_ 4)) (.constant constNegOneIsizeLM31))),
        mkStmt (.assign (local_ 0) (.use (.copy (derefLocal 5))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body exercising negative `.isize` underflow OOB UB
(`Offset(copy _2, const -1_isize)` at `offsetBytes = 0` on `*const u64`). -/
def lm31OffsetNegOobBody : CapturedMir where
  defPath := "lm_3_1_witness::binop_offset_neg_isize_oob_ub"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (.constant constNegOneIsizeLM31)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_binOp_offset_neg_stride_and_oob_real_steps` (`LM-3.1` D6 Non-Byte Negative Stride & Negative OOB UB)**:
1. `lm31OffsetNegStrideBody`: advances `*const u32` by `+2_usize` (`offsetBytes = 8`),
   steps backward `-1_isize` with `opKind = .move` (`step_binOp_offset_neg_isize_simulation`,
   stride `4`, landing at `offsetBytes = 4` and deinitializing `_4`), and reads `1_u32`
   in lockstep!
2. `lm31OffsetNegOobBody`: `Offset(copy _2, const -1_isize)` at `offsetBytes = 0` on
   `*const u64` fails with `.ub` in BOTH `stepMirFn` and `Miri.Interpreter.Step.step`
   via `step_binOp_offset_neg_oob_ub_simulation`! -/
theorem wit_lm3_1_binOp_offset_neg_stride_and_oob_real_steps :
    (let b := lm31OffsetNegStrideBody
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ s₄ s₅ m₁ m₂ m₃ m₄ m₅ map₅,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨4294967301, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b u32TyLM31 u64Ty (Miri.Memory.ScalarInt.ofUInt64 4294967301)) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .step s₄ ∧ Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
       get? s₄.frame.locals 4 = some .uninit ∧
       get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 4 } 8)) ∧
       stepMirFn b s₄ = .step s₅ ∧ Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
       StateRelLM3_1 b s₅ m₅ map₅ ∧
       get? s₅.frame.locals 0 = some (.init (.scalar ⟨1, 4⟩))) ∧
    (let b := lm31OffsetNegOobBody
     let hooks := annealStepHooks b.localDecls b.layouts
     let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
     ∃ s₁ m₁ m₂ msg,
       stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       StateRelLM3_1 b s₁ m₁ [entry] ∧
       stepMirFn b s₁ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg))) := by
  refine ⟨?_, ?_⟩
  · let b := lm31OffsetNegStrideBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let scInit : MirAst.ScalarInt := ⟨4294967301, 8⟩
    let mscInit := Miri.Memory.ScalarInt.ofUInt64 4294967301
    have hscRel : ScalarRel scInit mscInit := ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b scInit)
        (mkSixLocalScalarMiriPre b u32TyLM31 u64Ty mscInit) :=
      mkSixLocalScalar_stateRel b u32TyLM31 u32DeclLM31 u64Decl rawPtrConstU64Decl
        rawPtrConstU32Decl rawPtrConstU32Decl rawPtrConstU32Decl scInit mscInit rfl rfl hscRel rfl
        (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkSixLocalScalar_all_immediate b u32TyLM31 u64Ty mscInit
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
    let ptr4 := Value.ptr { allocId := 1, offsetBytes := 4 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar scInit), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b scInit) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalScalarAnnealPre b scInit).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalScalarMiriPre b u32TyLM31 u64Ty mscInit).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
      step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrConstU32Decl) (ptrDecl := rawPtrConstU32Decl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 2 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 2)
        rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
        (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
    let s₃ := mkWitState b 3 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr8, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
    obtain ⟨m₃', hm₃_eq, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
    have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
    obtain ⟨_, himm_s₃⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
    have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂; exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
    obtain ⟨hsim₄, hs₄_eq, m₄, _, _, hm₄, _, _⟩ :=
      step_binOp_offset_neg_isize_simulation hrel₃ hphase (Or.inr rfl) rfl rfl
        (dstDecl := rawPtrConstU32Decl) (ptrDecl := rawPtrConstU32Decl) (tgtDecl := u64Decl)
        (rhsTy := isizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
        (fun tf _ => .of_wt (constNegOneIsize_wellTyped b tf))
        (fun tf htf => ⟨himm₃ tf htf 5 (by decide), himm₃ tf htf 4 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 8 }) (countMag := 1)
        rfl rfl (by decide) (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl (by rintro ⟨⟩)
        (by decide) (by decide)
    let s₄ := mkWitState b 4 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .uninit, .init ptr4] bor 2
    have hs₄ : stepMirFn b s₃ = .step s₄ := hs₄_eq
    obtain ⟨m₄', hm₄_eq, hrel₄⟩ := stepRelLM3_1_of_anneal_step hsim₄ hs₄
    have hm₄_inj : m₄' = m₄ := (Prod.mk.inj (hm₄_eq.symm.trans hm₄)).1; subst m₄'
    obtain ⟨_, himm_s₄⟩ := step_assign_binOp_offset_any_preserves hrel₃ rfl rfl hm₄
    have himm₄ : ∀ tf, m₄.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃; exact himm_s₄ tf₃ tf htf₃ htf k (himm₃ tf₃ htf₃ k hne)
    obtain ⟨hsim₅, hs₅_fn⟩ := step_deref_read_narrower_simulation hrel₄ hphase (Or.inl rfl) rfl rfl
      (dstDecl := u32DeclLM31) (ptrDecl := rawPtrConstU32Decl) (tgtDecl := u64Decl) rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩)))
      (fun tf htf => ⟨himm₄ tf htf 0 (by decide), himm₄ tf htf 5 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 4 }) (oldSc := scInit)
      rfl (.head _) rfl (by rintro ⟨⟩) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (by decide) (by decide) (fun h => by cases h) (fun h => by cases h)
    have hs₅ := hs₅_fn (by rintro ⟨⟩); dsimp only [] at hs₅
    have hacc5 : (translateTy u32DeclLM31.ty b.layouts).layout.size.bytes.toNat = 4 := rfl
    have hbits5 : scInit.bits / 2 ^ (8 * ({ allocId := 1, offsetBytes := 4 } : ProvenancePtr).offsetBytes) %
        scalarModulus 4 = 1 := by decide
    rw [hacc5, hbits5] at hs₅
    let map₅ := derefReadNextAllocMap s₄.frame.locals [rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1] 5
    let s₅ := advanceStmt s₄ (s₄.frame.locals.set 0 (.init (.scalar ⟨1, 4⟩)))
      ({ s₄.memory with borrows := List.map AllocMapEntry.toBorrowEntry map₅ })
    have hs₅_eq : stepMirFn b s₄ = .step s₅ := hs₅
    obtain ⟨m₅, hm₅, hrel₅⟩ := stepRelLM3_1_of_anneal_step hsim₅ hs₅_eq
    exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, map₅,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, rfl, rfl, hs₅_eq, hm₅, hrel₅, rfl⟩
  · let b := lm31OffsetNegOobBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkFourLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    obtain ⟨_, hs₂, m₂, msg, hm₂⟩ :=
      step_binOp_offset_neg_oob_ub_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (rhsTy := isizeTyLM31)
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inr rfl)
        (fun tf _ => .of_wt (constNegOneIsize_wellTyped b tf))
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
        (by
          intro ptrVal sc locals_rhs e tgtDecl hptr hsc _ _ _
          have hp : ptrVal = { allocId := 1, offsetBytes := 0 } :=
            ptrVal_of_some_init hptr
          have hs : sc = ⟨2 ^ 64 - 1, 8⟩ := by
            dsimp [evalOperand, constNegOneIsizeLM31] at hsc
            injection hsc with h1 _
            injection h1 with h2
            exact h2.symm
          subst hp hs
          exact Or.inl ⟨by decide, Or.inr (Or.inl (by decide))⟩)
    exact ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

/-! ### 8.7 D6 Real-Step Witness (Unsigned `usize` Wrap-Around `Offset` Divergence) -/

/-- `Runtime(PostCleanup)` MIR body exercising the unsigned `usize` wrap-around `Offset`
divergence: `_3 = Offset(copy _2, const 1_usize)` advances `*const u64` to the
one-past-the-end `offsetBytes = 8` of `_1 : u64`, then
`_2 = Offset(copy _3, const 18446744073709551615_usize)` (`usize::MAX`). -/
def lm31OffsetUsizeWrapBody : CapturedMir where
  defPath := "lm_3_1_witness::binop_offset_usize_wrap_divergence"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 2)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 18446744073709551615))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_binOp_offset_usize_wrap_divergence_real_steps` (`LM-3.1` D6 Unsigned `usize`
Wrap-Around `Offset` Divergence)**: 3-step real-step execution of `lm31OffsetUsizeWrapBody`
from `StateRel`: `_2 = &raw const _1` and `_3 = Offset(copy _2, const 1_usize)` step in
lockstep (`step_binOp_offset_stride_simulation`, landing at the one-past-the-end
`offsetBytes = 8`), then `_2 = Offset(copy _3, const usize::MAX)` makes Anneal's `stepMirFn`
step *backward* to `offsetBytes = 0` while `lean-miri` raises `"PointerArithOverflow"`
(`step_binOp_offset_usize_wrap_divergence`). -/
theorem wit_lm3_1_binOp_offset_usize_wrap_divergence_real_steps :
    let b := lm31OffsetUsizeWrapBody
    let hooks := annealStepHooks b.localDecls b.layouts
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
    ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
      stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ [entry] ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
      stepMirFn b s₂ = .step s₃ ∧
      get? s₃.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      Miri.Interpreter.Step.step hooks () m₂ =
        (m₃, .error (.undefinedBehavior "PointerArithOverflow")) := by
  let b := lm31OffsetUsizeWrapBody
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
      (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
    mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
      ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
  have himm₀ := mkFourLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
  have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
    (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  obtain ⟨hsim₂, hs₂_eq, m₂, _, _, hm₂, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr8] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := hs₂_eq
  obtain ⟨m₂', hm₂_eq, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
  have hm₂_inj : m₂' = m₂ := (Prod.mk.inj (hm₂_eq.symm.trans hm₂)).1; subst m₂'
  obtain ⟨_, himm_s₂⟩ := step_assign_binOp_offset_preserves hrel₁ (by rintro _ ⟨⟩) rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hs₃, m₃, hm₃⟩ :=
    step_binOp_offset_usize_wrap_divergence hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (tgtDecl := u64Decl)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 18446744073709551615 (by decide)))
      (fun tf htf => ⟨himm₂ tf htf 2 (by decide), himm₂ tf htf 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 8 }) (countMag := 1)
      rfl rfl (by decide) (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl (by rintro ⟨⟩)
      (by decide) (by decide)
  exact ⟨s₁, s₂, _, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, rfl, hs₃, rfl, hm₃⟩

/-! ### 8.8 Generalized Invalid-`bool` Non-Zero Offset Write, `usize ≥ 2^63` OOB `Offset`, & Composed `step_mir_lm3_1_state_simulation` UB Witnesses -/

/-- `Runtime(PostCleanup)` MIR body writing an invalid `bool` (`2`) through `*mut bool`
at odd byte offset `5` inside `_1 : u64`:
`_2 = &raw mut _1; _3 = copy _2 as *mut bool; _4 = Offset(copy _3, const 5_usize); *_4 = const (2 : bool)`. -/
def lm31DerefWriteInvalidBoolOffset5Body : CapturedMir where
  defPath := "lm_3_1_witness::deref_write_invalid_bool_offset5"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutBoolDecl, rawPtrMutBoolDecl, rawPtrMutBoolDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutBoolTy)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 5)))),
        mkStmt (.assign (derefLocal 4) (.use (.constant constInvalidBool2LM31)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body executing `_3 = Offset(copy _2, const usize::MAX)`
at `offsetBytes = 0` of `_1 : u64` (unsigned `usize ≥ 2^63` whose negative wrap-around
underflows `offsetBytes = 0`, raising UB in BOTH machines). -/
def lm31OffsetUsizeMaxAtZeroOobBody : CapturedMir where
  defPath := "lm_3_1_witness::binop_offset_usize_max_at_zero_oob"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrConstU64Decl, rawPtrConstU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1))),
        mkStmt (.assign (local_ 3)
          (.binaryOp .offset (.copy (local_ 2)) (.constant (constUsizeLM31 18446744073709551615))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_deref_write_invalid_bool_offset5_and_usize_oob_real_steps`**:
1. **Generalized `step_deref_write_invalid_bool_simulation` at odd byte offset `5` of `u64`**:
   promotes `_1 : u64` (`42`), casts `*mut u64 -> *mut bool`, offsets by `+5_usize`
   (`offsetBytes = 5`), and faults in lockstep on `*_4 = const (2 : bool)`
   (`stepMirFn = .fail .ub`, Miri `"writing invalid value"`).
2. **Generalized `step_binOp_offset_neg_oob_ub_simulation` on `usize ≥ 2^63` OOB**:
   promotes `_1 : u64` (`42`) to `offsetBytes = 0` and faults in lockstep on
   `Offset(copy _2, const usize::MAX)` (`stepMirFn = .fail .ub`, Miri `.undefinedBehavior msg`). -/
theorem wit_lm3_1_deref_write_invalid_bool_offset5_and_usize_oob_real_steps :
    (let b := lm31DerefWriteInvalidBoolOffset5Body
     let hooks := annealStepHooks b.localDecls b.layouts
     let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
     ∃ s₁ s₂ s₃ m₁ m₂ m₃ m₄,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧
       Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       StateRelLM3_1 b s₃ m₃ [entry] ∧
       get? s₃.frame.locals 4 = some (.init (.ptr { allocId := 1, offsetBytes := 5 } 8)) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ =
         (m₄, .error (.undefinedBehavior "writing invalid value"))) ∧
    (let b := lm31OffsetUsizeMaxAtZeroOobBody
     let hooks := annealStepHooks b.localDecls b.layouts
     let entry := rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1
     ∃ s₁ m₁ m₂ msg,
       stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       StateRelLM3_1 b s₁ m₁ [entry] ∧
       stepMirFn b s₁ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₁ =
         (m₂, .error (.undefinedBehavior msg))) := by
  refine ⟨?_, ?_⟩
  · let b := lm31DerefWriteInvalidBoolOffset5Body
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkSixLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl
        rawPtrMutBoolDecl rawPtrMutBoolDecl rawPtrMutBoolDecl ⟨42, 8⟩ lm31Scalar42
        rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkSixLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr5 := Value.ptr { allocId := 1, offsetBytes := 5 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)) hs₂
    obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁; exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
      step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrMutBoolDecl) (ptrDecl := rawPtrMutBoolDecl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl
        (Or.inl rfl) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 5 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 5)
        rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
        (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
    let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr5, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
    obtain ⟨m₃', hm₃_eq, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
    have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
    obtain ⟨_, himm_s₃⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
    have himm₃_4 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 4 := by
      intro tf htf; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf htf₂ htf 4 (himm₂ tf₂ htf₂ 4 (by decide))
    obtain ⟨_, hs₄, m₄, hm₄⟩ :=
      step_deref_write_invalid_bool_simulation hrel₃ hphase rfl rfl
        (ptrDecl := rawPtrMutBoolDecl) (tgtDecl := u64Decl)
        rfl rfl rfl rfl (by decide) (by decide) himm₃_4
        (ptrVal := { allocId := 1, offsetBytes := 5 })
        rfl (.head _) rfl (Or.inl rfl) rfl (by decide) (by rintro ⟨⟩)
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hrel₃, rfl, hs₄, hm₄⟩
  · let b := lm31OffsetUsizeMaxAtZeroOobBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkFourLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    obtain ⟨_, hs₂, m₂, msg, hm₂⟩ :=
      step_binOp_offset_neg_oob_ub_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrConstU64Decl) (ptrDecl := rawPtrConstU64Decl) (rhsTy := usizeTyLM31)
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 18446744073709551615 (by decide)))
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
        (by
          intro ptrVal sc locals_rhs e tgtDecl hptr hsc _ _ _
          have hp : ptrVal = { allocId := 1, offsetBytes := 0 } := ptrVal_of_some_init hptr
          have hs : sc = ⟨18446744073709551615, 8⟩ := by
            dsimp [evalOperand, constUsizeLM31] at hsc
            injection hsc with h1 _; injection h1 with h2; exact h2.symm
          subst hp hs
          exact Or.inl ⟨by decide, Or.inr (Or.inl (by decide))⟩)
    exact ⟨s₁, m₁, m₂, msg, hs₁, hm₁, hrel₁, hs₂, hm₂⟩

private theorem stepObsRelLM3_1_of_anneal_step
    {body : CapturedMir} {m : AnnealStepState} {allocMap : List AllocMapEntry}
    {aRes : MirStepNode} {mRes : Miri.Interpreter.StepResult AnnealStepState Bool}
    {s' : MachineState}
    (hsim : StepObsRelLM3_1 body m allocMap aRes mRes)
    (ha : aRes = .step s') :
    ∃ m', mRes = (m', .ok true) ∧ StateRelLM3_1 body s' m' allocMap :=
  stepObsRelLM3_1_of_anneal_emitStep (obs := .silent) (s' := s') hsim ha

private theorem allocMap_singleton_of_stateRel
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry} {be : BorrowEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    (hbor : s.memory.borrows = [be]) :
    ∃ e ∈ allocMap, e.tag = be.tag ∧ e.localIdx = be.targetLocal ∧ e.perm = be.perm := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hbor_eq, _, _⟩ := id hstate
  rw [hbor] at hbor_eq
  cases allocMap with
  | nil => cases hbor_eq
  | cons e rest =>
    injection hbor_eq with he _
    exact ⟨e, .head _, (congrArg BorrowEntry.tag he).symm,
      (congrArg BorrowEntry.targetLocal he).symm,
      (congrArg BorrowEntry.perm he).symm⟩

/-- **`wit_lm3_1_composed_step_mir_deref_ub_real_steps` (`LM-3.1` Composed
`step_mir_lm3_1_state_simulation` Multi-Step UB Traces)**:
End-to-end 4-step executions where **every step** from entry (`stmtIdx = 0, 1, 2, 3`)
is stepped exclusively through the unified composed theorem `step_mir_lm3_1_state_simulation`
(`WellTypedLM3_1StateStmt.rawPtrAddrOf` -> `.castPtrToPtr` -> `.binOpOffsetStride` ->
`.derefWriteInvalidBoolUb` / `.derefReadNarrowerInvalidUb`), threading `AllocIdSupplyReady`
across `addrOf`, `PtrToPtr` cast, and `BinOp.Offset` via `step_rawPtr_addrOf_preserves_supply`,
`step_assign_cast_ptrToPtr_preserves_supply`, and `step_assign_binOp_offset_preserves_supply`:
1. `lm31DerefWriteInvalidBoolOffset5Body`: `*_4 = const (2 : bool)` at odd byte offset `5`
   of `_1 : u64` (`WellTypedLM3_1StateStmt.derefWriteInvalidBoolUb`).
2. `lm31NarrowerInvalidCharReadBody`: `_0 = move *_4` reading surrogate `0xD800` at byte
   offset `4` of `_1 : u64` (`WellTypedLM3_1StateStmt.derefReadNarrowerInvalidUb`). -/
theorem wit_lm3_1_composed_step_mir_deref_ub_real_steps :
    (let b := lm31DerefWriteInvalidBoolOffset5Body
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ m₁ m₂ m₃ m₄ map₄ msg,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧
       Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       AllocIdSupplyReady m₃.machine.memory ∧
       StepObsRelLM3_1 b m₃ map₄ (stepMirFn b s₃) (Miri.Interpreter.Step.step hooks () m₃) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior msg))) ∧
    (let b := lm31NarrowerInvalidCharReadBody
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ m₁ m₂ m₃ m₄ map₄ msg,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨237494511599681, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b charTyLM31 u64Ty (Miri.Memory.ScalarInt.ofUInt64 237494511599681)) =
         (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧
       Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       AllocIdSupplyReady m₃.machine.memory ∧
       StepObsRelLM3_1 b m₃ map₄ (stepMirFn b s₃) (Miri.Interpreter.Step.step hooks () m₃) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .error (.undefinedBehavior msg))) := by
  refine ⟨?_, ?_⟩
  · let b := lm31DerefWriteInvalidBoolOffset5Body
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let s₀ := mkSixLocalScalarAnnealPre b ⟨42, 8⟩
    let m₀ := mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkSixLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl
        rawPtrMutBoolDecl rawPtrMutBoolDecl rawPtrMutBoolDecl ⟨42, 8⟩ lm31Scalar42
        rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)).toLM3_1
    have himm₀ := mkSixLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    have himm01 : ∀ tf, m₀.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr5 := Value.ptr { allocId := 1, offsetBytes := 5 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    have hwt₀ : WellTypedLM3_1StateStmt b s₀ m₀ []
        (mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .mut (.uint .u64) rawPtrMutU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
    obtain ⟨map₁, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm_s₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
        AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ map₁
        (mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutBoolTy))) :=
      .castPtrToPtr 3 2 rawPtrMutBoolTy rawPtrMutBoolDecl rawPtrMutU64Decl
        .mut .mut .mut (.uint .u64) .bool _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₂, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_1_of_anneal_step hsim₂ hs₂
    obtain ⟨⟨hsupply₂, _, _⟩, himm_s₂⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₁ rfl rfl hsupply₁ hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨e₂, he₂, htag₂, hloc₂, hperm₂⟩ := allocMap_singleton_of_stateRel hrel₂ rfl
    have hwt₂ : WellTypedLM3_1StateStmt b s₂ m₂ map₂
        (mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 5))))) :=
      .binOpOffsetStride 4 3 MirAst.Operand.copy (.constant (constUsizeLM31 5))
        rawPtrMutBoolDecl rawPtrMutBoolDecl u64Decl .mut .mut .bool usizeTyLM31
        { allocId := 1, offsetBytes := 0 } 5 s₂.frame.locals e₂ _
        (Or.inl rfl) rfl rfl rfl rfl (Or.inl rfl) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 5 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
        rfl rfl (by rintro ⟨⟩) he₂ htag₂ (by rw [hperm₂]; rintro ⟨⟩) (by rw [hloc₂]; rfl)
        (Or.inr ⟨by rw [hloc₂]; rintro ⟨⟩, by decide⟩)
    obtain ⟨map₃, hsim₃⟩ := step_mir_lm3_1_state_simulation hrel₂ hphase rfl
      (Or.inl ⟨_, rfl, hwt₂⟩) hsupply₂
    let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr5, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepObsRelLM3_1_of_anneal_step hsim₃ hs₃
    obtain ⟨⟨hsupply₃, _, _⟩, himm_s₃⟩ :=
      step_assign_binOp_offset_preserves_supply hrel₂ rfl rfl hsupply₂ hm₃
    have himm₃_4 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 4 := by
      intro tf htf; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf htf₂ htf 4 (himm₂ tf₂ htf₂ 4 (by decide))
    obtain ⟨e₃, he₃, htag₃, hloc₃, hperm₃⟩ := allocMap_singleton_of_stateRel hrel₃ rfl
    have hwt₃ : WellTypedLM3_1StateStmt b s₃ m₃ map₃
        (mkStmt (.assign (derefLocal 4) (.use (.constant constInvalidBool2LM31)))) :=
      .derefWriteInvalidBoolUb 4 constInvalidBool2LM31 2 rawPtrMutBoolDecl u64Decl .mut
        { allocId := 1, offsetBytes := 5 } e₃ _
        rfl rfl rfl rfl (by decide) (by decide) himm₃_4 rfl he₃ htag₃ (Or.inl hperm₃)
        (by rw [hloc₃]; rfl) (by decide) (by rw [hloc₃]; rintro ⟨⟩)
    obtain ⟨map₄, hsim₄⟩ := step_mir_lm3_1_state_simulation hrel₃ hphase rfl
      (Or.inl ⟨_, rfl, hwt₃⟩) hsupply₃
    obtain ⟨_, hs₄, _⟩ :=
      step_deref_write_invalid_bool_simulation hrel₃ hphase rfl rfl
        (ptrDecl := rawPtrMutBoolDecl) (tgtDecl := u64Decl)
        rfl rfl rfl rfl (by decide) (by decide) himm₃_4
        (ptrVal := { allocId := 1, offsetBytes := 5 })
        rfl he₃ htag₃ (Or.inl hperm₃) (by rw [hloc₃]; rfl) (by decide) (by rw [hloc₃]; rintro ⟨⟩)
    obtain ⟨msg, hm₄_err⟩ := (StepObsRelLM3_1.ub_iff hsim₄).mp hs₄
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, _, map₄, msg,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hsupply₃, hsim₄, hs₄, Prod.ext rfl hm₄_err⟩
  · let b := lm31NarrowerInvalidCharReadBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let scInit : MirAst.ScalarInt := ⟨237494511599681, 8⟩
    let mscInit := Miri.Memory.ScalarInt.ofUInt64 237494511599681
    have hscRel : ScalarRel scInit mscInit :=
      ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    let s₀ := mkSixLocalScalarAnnealPre b scInit
    let m₀ := mkSixLocalScalarMiriPre b charTyLM31 u64Ty mscInit
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkSixLocalScalar_stateRel b charTyLM31 charDeclLM31 u64Decl rawPtrConstU64Decl
        rawPtrConstCharDecl rawPtrConstCharDecl rawPtrConstCharDecl scInit mscInit
        rfl rfl hscRel rfl (fun h => nomatch h) (fun h => nomatch h)).toLM3_1
    have himm₀ := mkSixLocalScalar_all_immediate b charTyLM31 u64Ty mscInit
    have himm01 : ∀ tf, m₀.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr4 := Value.ptr { allocId := 1, offsetBytes := 4 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1]
    have hwt₀ : WellTypedLM3_1StateStmt b s₀ m₀ []
        (mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .not (.uint .u64) rawPtrConstU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
    obtain ⟨map₁, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar scInit), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm_s₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
        AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ map₁
        (mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrConstCharTy))) :=
      .castPtrToPtr 3 2 rawPtrConstCharTy rawPtrConstCharDecl rawPtrConstU64Decl
        .not .not .not (.uint .u64) .char _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₂, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_1_of_anneal_step hsim₂ hs₂
    obtain ⟨⟨hsupply₂, _, _⟩, himm_s₂⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₁ rfl rfl hsupply₁ hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨e₂, he₂, htag₂, hloc₂, hperm₂⟩ := allocMap_singleton_of_stateRel hrel₂ rfl
    have hwt₂ : WellTypedLM3_1StateStmt b s₂ m₂ map₂
        (mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1))))) :=
      .binOpOffsetStride 4 3 MirAst.Operand.copy (.constant (constUsizeLM31 1))
        rawPtrConstCharDecl rawPtrConstCharDecl u64Decl .not .not .char usizeTyLM31
        { allocId := 1, offsetBytes := 0 } 1 s₂.frame.locals e₂ _
        (Or.inl rfl) rfl rfl rfl rfl (Or.inr (Or.inl rfl)) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
        rfl rfl (by rintro ⟨⟩) he₂ htag₂ (by rw [hperm₂]; rintro ⟨⟩) (by rw [hloc₂]; rfl)
        (Or.inr ⟨by rw [hloc₂]; rintro ⟨⟩, by decide⟩)
    obtain ⟨map₃, hsim₃⟩ := step_mir_lm3_1_state_simulation hrel₂ hphase rfl
      (Or.inl ⟨_, rfl, hwt₂⟩) hsupply₂
    let s₃ := mkWitState b 3 [.uninit, .init (.scalar scInit), .init ptr0, .init ptr0, .init ptr4, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .not 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepObsRelLM3_1_of_anneal_step hsim₃ hs₃
    obtain ⟨⟨hsupply₃, _, _⟩, himm_s₃⟩ :=
      step_assign_binOp_offset_preserves_supply hrel₂ rfl rfl hsupply₂ hm₃
    have himm₃_4 : ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf 4 := by
      intro tf htf; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf htf₂ htf 4 (himm₂ tf₂ htf₂ 4 (by decide))
    obtain ⟨e₃, he₃, htag₃, hloc₃, _⟩ := allocMap_singleton_of_stateRel hrel₃ rfl
    have hwt₃ : WellTypedLM3_1StateStmt b s₃ m₃ map₃
        (mkStmt (.assign (local_ 0) (.use (.move (derefLocal 4))))) :=
      .derefReadNarrowerInvalidUb 0 4 MirAst.Operand.move charDeclLM31 rawPtrConstCharDecl u64Decl .not
        { allocId := 1, offsetBytes := 4 } e₃ scInit _
        (Or.inr rfl) rfl rfl rfl himm₃_4 rfl he₃ htag₃ (by rw [hloc₃]; rfl)
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by rw [hloc₃]; rfl)
        (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩)
    obtain ⟨map₄, hsim₄⟩ := step_mir_lm3_1_state_simulation hrel₃ hphase rfl
      (Or.inl ⟨_, rfl, hwt₃⟩) hsupply₃
    obtain ⟨_, hs₄, _⟩ :=
      step_deref_read_narrower_invalid_bool_or_char_simulation hrel₃ hphase (Or.inr rfl)
        rfl rfl (dstDecl := charDeclLM31) (ptrDecl := rawPtrConstCharDecl) (tgtDecl := u64Decl)
        rfl rfl rfl himm₃_4 (ptrVal := { allocId := 1, offsetBytes := 4 }) (oldSc := scInit)
        rfl he₃ htag₃ (by rw [hloc₃]; rfl) (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (by rw [hloc₃]; rfl) (by decide) (by decide) (Or.inr ⟨rfl, by decide⟩)
    obtain ⟨msg, hm₄_err⟩ := (StepObsRelLM3_1.ub_iff hsim₄).mp hs₄
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, _, map₄, msg,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hsupply₃, hsim₄, hs₄, Prod.ext rfl hm₄_err⟩

/-! ### 8.9 D6 Disabled-Tag `Offset` Witnesses (Live Stride, Negative `isize`, `usize::MAX`, Dead-Local Zero Count) -/

/-- `Runtime(PostCleanup)` MIR body disabling a live raw-pointer tag with a direct write and
then offsetting it: `_2 = &raw mut _1; _1 = const 7_u64; _3 = Offset(move _2, const 1_usize)`
(stride `8`, one-past-the-end `offsetBytes = 8` of the live `_1 : u64`). -/
def lm31OffsetDisabledLiveBody : CapturedMir where
  defPath := "lm_3_1_witness::offset_disabled_live_stride"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 7)))),
        mkStmt (.assign (local_ 3) (.binaryOp .offset (.move (local_ 2)) (.constant (constUsizeLM31 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body disabling a live raw-pointer tag at `offsetBytes = 8` and
stepping it backward: `_2 = &raw mut _1; _3 = Offset(copy _2, const 1_usize); _1 = const 7_u64;
_4 = Offset(move _3, const -1_isize)`. -/
def lm31OffsetDisabledNegBody : CapturedMir where
  defPath := "lm_3_1_witness::offset_disabled_live_neg_isize"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl,
    rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 7)))),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.move (local_ 3)) (.constant constNegOneIsizeLM31)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body disabling a live raw-pointer tag and offsetting it by
`usize::MAX`: `_2 = &raw mut _1; _1 = const 7_u64; _3 = Offset(copy _2, const usize::MAX)`. -/
def lm31OffsetDisabledUsizeMaxBody : CapturedMir where
  defPath := "lm_3_1_witness::offset_disabled_usize_max"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 1) (.use (.constant (constU64 7)))),
        mkStmt (.assign (local_ 3)
          (.binaryOp .offset (.copy (local_ 2)) (.constant (constUsizeLM31 18446744073709551615))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body offsetting a dangling raw pointer into a dead local by a
zero count at a non-zero offset: `_2 = &raw mut _1; _3 = Offset(copy _2, const 1_usize);
StorageDead(_1); _4 = Offset(copy _3, const 0_usize)` (`offsetBytes = 8`). -/
def lm31OffsetDisabledDeadZeroBody : CapturedMir where
  defPath := "lm_3_1_witness::offset_disabled_dead_zero_at_8"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl, rawPtrMutU64Decl,
    rawPtrMutU64Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.binaryOp .offset (.copy (local_ 2)) (.constant (constUsizeLM31 1)))),
        mkStmt (.storageDead 1),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 0))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_binOp_offset_disabled_live_real_steps` (`LM-3.1` D6 Disabled-Tag `Offset`
Boundary)**: real-step executions from `StateRel` in which `_2`'s raw-pointer tag is disabled in
lockstep, in parts 1–3 by a direct write `_1 = const 7_u64` to the promoted `_1`
(`step_direct_write_promoted_lm3_1_simulation`, `updateAllocMapOnWrite`) while `_1` stays live,
and in part 4 by `StorageDead(_1)` (`step_storageDead_lm3_1_simulation`):
1. `lm31OffsetDisabledLiveBody`: `Offset(move _2, const 1_usize)` (stride `8`) faults with
   `.ub` in Anneal while `lean-miri` steps to `offsetBytes = 8`
   (`step_binOp_offset_disabled_stride_divergence`).
2. `lm31OffsetDisabledNegBody`: after `Offset(copy _2, const 1_usize)` reaches
   `offsetBytes = 8` in lockstep, the direct write disables the tag and
   `Offset(move _3, const -1_isize)` faults with `.ub` in Anneal while `lean-miri` steps back to
   `offsetBytes = 0` (`step_binOp_offset_disabled_neg_isize_divergence`).
3. `lm31OffsetDisabledUsizeMaxBody`: `Offset(copy _2, const usize::MAX)` raises UB in BOTH
   machines (Anneal `.ub`, `lean-miri` `"PointerArithOverflow"`;
   `step_binOp_offset_usize_wrap_disabled_ub_simulation`).
4. `lm31OffsetDisabledDeadZeroBody`: after `Offset(copy _2, const 1_usize)` reaches
   `offsetBytes = 8` and `StorageDead(_1)` disables the tag and frees the allocation in lockstep,
   the zero-count `Offset(copy _3, const 0_usize)` of the dangling pointer faults with `.ub` in
   Anneal while `lean-miri` steps (`step_binOp_offset_disabled_stride_divergence`, zero-count
   case at a non-zero offset). -/
theorem wit_lm3_1_binOp_offset_disabled_live_real_steps :
    (let b := lm31OffsetDisabledLiveBody
     let hooks := annealStepHooks b.localDecls b.layouts
     let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
     ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
       stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       StateRelLM3_1 b s₂ m₂ (updateAllocMapOnWrite [entry] 1 none) ∧
       (entry.updateOnWrite 1 none).perm = .disabled ∧
       get? s₂.frame.locals 1 = some (.init (.scalar ⟨7, 8⟩)) ∧
       stepMirFn b s₂ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true)) ∧
    (let b := lm31OffsetDisabledNegBody
     let hooks := annealStepHooks b.localDecls b.layouts
     let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
     ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧
       Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       StateRelLM3_1 b s₃ m₃ (updateAllocMapOnWrite [entry] 1 none) ∧
       get? s₃.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true)) ∧
    (let b := lm31OffsetDisabledUsizeMaxBody
     let hooks := annealStepHooks b.localDecls b.layouts
     let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
     ∃ (s₁ s₂ : MachineState) (m₁ m₂ m₃ : AnnealStepState),
       stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       StateRelLM3_1 b s₂ m₂ (updateAllocMapOnWrite [entry] 1 none) ∧
       StepRelLM3_1 b m₂ (updateAllocMapOnWrite [entry] 1 none)
         (stepMirFn b s₂) (Miri.Interpreter.Step.step hooks () m₂) ∧
       stepMirFn b s₂ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₂ =
         (m₃, .error (.undefinedBehavior "PointerArithOverflow"))) ∧
    (let b := lm31OffsetDisabledDeadZeroBody
     let hooks := annealStepHooks b.localDecls b.layouts
     let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
     ∃ (s₁ s₂ s₃ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState),
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧
       Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧
       Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       StateRelLM3_1 b s₃ m₃ (disableAllocMapLocal [entry] 1) ∧
       get? s₃.frame.locals 1 = some .dead ∧
       get? s₃.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 8 } 8)) ∧
       stepMirFn b s₃ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · let b := lm31OffsetDisabledLiveBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl rawPtrMutU64Decl
        ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkFourLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    let map₂ := updateAllocMapOnWrite [entry] 1 none
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨7, 8⟩), .init ptr0, .uninit]
      (map₂.map AllocMapEntry.toBorrowEntry) 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_direct_write_promoted_lm3_1_simulation hrel₁ hphase rfl rfl
        (dstDecl := u64Decl) (valTy := u64Ty) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
        (fun tf _ => constU64_wellTyped b tf 7 (by decide)) ⟨entry, .head _, rfl⟩) hs₂
    obtain ⟨_, himm_s₂⟩ := step_assign_use_preserves hrel₁ (by rintro _ ⟨⟩) rfl rfl hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨hs₃, m₃, hm₃⟩ :=
      step_binOp_offset_disabled_stride_divergence hrel₂ hphase (Or.inr rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 3 (by decide), himm₂ tf htf 2 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
        rfl rfl (by rintro ⟨⟩) (.head _) rfl rfl rfl
        (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
    exact ⟨s₁, s₂, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, rfl, rfl, hs₃, hm₃⟩
  · let b := lm31OffsetDisabledNegBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkSixLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl
        rawPtrMutU64Decl rawPtrMutU64Decl rawPtrMutU64Decl ⟨42, 8⟩ lm31Scalar42
        rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkSixLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    obtain ⟨hsim₂, hs₂_eq, m₂, _, _, hm₂, _, _⟩ :=
      step_binOp_offset_stride_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
        rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
        (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr8, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := hs₂_eq
    obtain ⟨m₂', hm₂_eq, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
    have hm₂_inj : m₂' = m₂ := (Prod.mk.inj (hm₂_eq.symm.trans hm₂)).1; subst m₂'
    obtain ⟨_, himm_s₂⟩ := step_assign_binOp_offset_preserves hrel₁ (by rintro _ ⟨⟩) rfl rfl hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    let map₃ := updateAllocMapOnWrite [entry] 1 none
    let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨7, 8⟩), .init ptr0, .init ptr8, .uninit, .uninit]
      (map₃.map AllocMapEntry.toBorrowEntry) 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
      (step_direct_write_promoted_lm3_1_simulation hrel₂ hphase rfl rfl
        (dstDecl := u64Decl) (valTy := u64Ty) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
        (fun tf _ => constU64_wellTyped b tf 7 (by decide)) ⟨entry, .head _, rfl⟩) hs₃
    obtain ⟨_, himm_s₃⟩ := step_assign_use_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
    have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
    obtain ⟨hs₄, m₄, hm₄⟩ :=
      step_binOp_offset_disabled_neg_isize_divergence hrel₃ hphase (Or.inr rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (tgtDecl := u64Decl)
        (rhsTy := isizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
        (fun tf _ => .of_wt (constNegOneIsize_wellTyped b tf))
        (fun tf htf => ⟨himm₃ tf htf 4 (by decide), himm₃ tf htf 3 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 8 }) (countMag := 1)
        rfl rfl (by decide) (by rintro ⟨⟩) (.head _) rfl rfl rfl (by rintro ⟨⟩)
        (by decide) (by decide)
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hrel₃, rfl, hs₄, hm₄⟩
  · let b := lm31OffsetDisabledUsizeMaxBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hrel₀ : StateRel b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl rawPtrMutU64Decl
        ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkFourLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit] bor 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkFourLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    let map₂ := updateAllocMapOnWrite [entry] 1 none
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨7, 8⟩), .init ptr0, .uninit]
      (map₂.map AllocMapEntry.toBorrowEntry) 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
      (step_direct_write_promoted_lm3_1_simulation hrel₁ hphase rfl rfl
        (dstDecl := u64Decl) (valTy := u64Ty) rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
        (fun tf _ => constU64_wellTyped b tf 7 (by decide)) ⟨entry, .head _, rfl⟩) hs₂
    obtain ⟨_, himm_s₂⟩ := step_assign_use_preserves hrel₁ (by rintro _ ⟨⟩) rfl rfl hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨hsim₃, hs₃, m₃, hm₃⟩ :=
      step_binOp_offset_usize_wrap_disabled_ub_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (rhsTy := usizeTyLM31)
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) rfl
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 18446744073709551615 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 3 (by decide), himm₂ tf htf 2 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 })
        rfl rfl (by decide) (.head _) rfl rfl
    exact ⟨s₁, s₂, m₁, m₂, m₃, hs₁, hm₁, hs₂, hm₂, hrel₂, hsim₃, hs₃, hm₃⟩
  · let b := lm31OffsetDisabledDeadZeroBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) :=
      mkSixLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl
        rawPtrMutU64Decl rawPtrMutU64Decl rawPtrMutU64Decl ⟨42, 8⟩ lm31Scalar42
        rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)
    have himm₀ := mkSixLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr8 := Value.ptr { allocId := 1, offsetBytes := 8 } 8
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
      (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
        (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty) hs₁
    have htag₀ : (mkSixLocalScalarAnnealPre b ⟨42, 8⟩).memory.nextTag = 1 := rfl
    have hid₀ : (⟨(mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).machine.memory.nextAllocId,
        AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
    rw [htag₀, hid₀] at hrel₁
    obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide)
      (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩) AllocIdSupplyReady.empty hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    obtain ⟨hsim₂, hs₂_eq, m₂, _, _, hm₂, _, _⟩ :=
      step_binOp_offset_stride_simulation hrel₁ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
        rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
        (Or.inr ⟨by rintro ⟨⟩, by decide⟩)
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr8, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := hs₂_eq
    obtain ⟨m₂', hm₂_eq, hrel₂⟩ := stepRelLM3_1_of_anneal_step hsim₂ hs₂
    have hm₂_inj : m₂' = m₂ := (Prod.mk.inj (hm₂_eq.symm.trans hm₂)).1; subst m₂'
    obtain ⟨_, himm_s₂⟩ := step_assign_binOp_offset_preserves hrel₁ (by rintro _ ⟨⟩) rfl rfl hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    let s₃ := mkWitState b 3 [.uninit, .dead, .init ptr0, .init ptr8, .uninit, .uninit]
      (disableLocalBorrows bor 1) 2
    have hs₃ : stepMirFn b s₂ = .step s₃ := rfl
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepRelLM3_1_of_anneal_step
      (step_storageDead_lm3_1_simulation hrel₂ hphase rfl rfl (decl := u64Decl) rfl (by decide)) hs₃
    obtain ⟨_, himm_s₃⟩ := step_storageDead_preserves hrel₂ rfl rfl
      (decl := u64Decl) rfl (by decide) hm₃
    have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
    obtain ⟨hs₄, m₄, hm₄⟩ :=
      step_binOp_offset_disabled_stride_divergence hrel₃ hphase (Or.inl rfl) rfl rfl
        (dstDecl := rawPtrMutU64Decl) (ptrDecl := rawPtrMutU64Decl) (tgtDecl := u64Decl)
        (rhsTy := usizeTyLM31) rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 0 (by decide)))
        (fun tf htf => ⟨himm₃ tf htf 4 (by decide), himm₃ tf htf 3 (by decide)⟩)
        (ptrVal := { allocId := 1, offsetBytes := 8 }) (count := 0)
        rfl rfl (by rintro ⟨⟩) (.head _) rfl rfl rfl (Or.inl rfl)
    exact ⟨s₁, s₂, s₃, m₁, m₂, m₃, m₄, hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hrel₃, rfl, rfl, hs₄, hm₄⟩

/-! ### 8.10 Sub-Byte `move` Raw Overwrite into `char` & Composed `AllocId`-Free OOB / Misaligned UB Witnesses -/

/-- `Runtime(PostCleanup)` MIR body splicing `0xD8_u8` via `Operand.move` into byte `1`
of promoted `_1 : char` (`'A' = 0x00000041 -> 0x0000D841`), then reading either via
`copy *_2` (`useDeref = true`, lockstep UB) or `move _1` (`useDeref = false`,
documented `validateLoadedValue` direct-`char` load boundary). -/
def lm31RawSubbyteMoveOverwriteCharBody (useDeref : Bool) : CapturedMir where
  defPath := if useDeref then "lm_3_1_witness::raw_subbyte_move_overwrite_char_deref"
             else "lm_3_1_witness::raw_subbyte_move_overwrite_char_direct_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [charDeclLM31, charDeclLM31, rawPtrMutCharDecl, rawPtrMutU8Decl, rawPtrMutU8Decl,
    u8DeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 5) (.use (.constant (constU8LM31 0xD8)))),
        mkStmt (.assign (derefLocal 4) (.use (.move (local_ 5)))),
        mkStmt (.assign (local_ 0)
          (.use (if useDeref then .copy (derefLocal 2) else .move (local_ 1))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body exercising 5-step composed `step_mir_lm3_1_state_simulation`
into `WellTypedLM3_1StateStmt.derefWriteNarrowerPartialOobUb` (`*mut u32` write at byte offset `6`
of `_1 : u64`). -/
def lm31ComposedPartialOobWriteBody : CapturedMir where
  defPath := "lm_3_1_witness::composed_partial_oob_write_offset6"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU8Decl, rawPtrMutU8Decl,
    rawPtrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 6)))),
        mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrMutU32Ty)),
        mkStmt (.assign (derefLocal 5) (.use (.constant (constU32LM31 7))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- `Runtime(PostCleanup)` MIR body exercising 5-step composed `step_mir_lm3_1_state_simulation`
into `WellTypedLM3_1StateStmt.derefReadMisalignedOffsetUb` (`isWrite = false`) and
`WellTypedLM3_1StateStmt.derefWriteMisalignedOffsetUb` (`isWrite = true`) at byte offset `2`
of `_1 : u64`. -/
def lm31ComposedMisalignedOffsetBody (isWrite : Bool) : CapturedMir where
  defPath := if isWrite then "lm_3_1_witness::composed_misaligned_offset2_write"
             else "lm_3_1_witness::composed_misaligned_offset2_read"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u32DeclLM31, u64Decl, rawPtrMutU64Decl, rawPtrMutU8Decl, rawPtrMutU8Decl,
    rawPtrMutU32Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 2)))),
        mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrMutU32Ty)),
        if isWrite then mkStmt (.assign (derefLocal 5) (.use (.constant (constU32LM31 7))))
        else mkStmt (.assign (local_ 0) (.use (.move (derefLocal 5))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

private theorem rawSubbyteMoveOverwriteChar_reach_state (useDeref : Bool) :
    let b := lm31RawSubbyteMoveOverwriteCharBody useDeref
    let hooks := annealStepHooks b.localDecls b.layouts
    let entry := rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1
    ∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (msc_merged : Miri.Memory.ScalarInt),
      stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks ()
        (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧ Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      stepMirFn b s₄ = .step s₅ ∧ Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      s₅.frame.blockIdx = 0 ∧ s₅.frame.stmtIdx = 5 ∧
      s₅.frame.locals.length = 6 ∧
      get? s₅.frame.locals 0 = some .uninit ∧
      get? s₅.frame.locals 1 = some (.init (.scalar ⟨0xD841, 4⟩)) ∧
      get? s₅.frame.locals 2 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8)) ∧
      get? s₅.frame.locals 5 = some .uninit ∧
      (∀ tf, m₅.stack.frames = #[tf] → IsImmediateFrameLocal tf 2) ∧
      RawOverwrittenScalarState b s₅ m₅ (updateAllocMapOnWrite [entry] 1 (some 1))
        1 lm31AllocId1 ⟨0xD841, 4⟩ msc_merged := by
  let b := lm31RawSubbyteMoveOverwriteCharBody useDeref
  have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
  let msc41 := Miri.Memory.ScalarInt.ofUInt32 0x41
  have hrel_sc : ScalarRel ⟨0x41, 4⟩ msc41 := ⟨Or.inr (Or.inr (Or.inl rfl)), by decide, rfl, rfl⟩
  have hrel₀ : StateRel b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩)
      (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 msc41) :=
    mkSixLocalScalar_stateRel b charTyLM31 charDeclLM31 charDeclLM31 rawPtrMutCharDecl
      rawPtrMutU8Decl rawPtrMutU8Decl u8DeclLM31 ⟨0x41, 4⟩ msc41 rfl rfl hrel_sc rfl
      (fun h => nomatch h) (fun _ => ⟨rfl, by decide⟩)
  have himm₀ := mkSixLocalScalar_all_immediate b charTyLM31 charTyLM31 msc41
  let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
  let ptr1 := Value.ptr { allocId := 1, offsetBytes := 1 } 8
  let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
  let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
  have hs₁ : stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ := rfl
  obtain ⟨m₁, hm₁, hrel₁⟩ := stepRelLM3_1_of_anneal_step
    (step_rawPtr_addrOf_simulation hrel₀ hphase rfl rfl rfl rfl rfl
      (Or.inr (Or.inl rfl)) (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩)
      AllocIdSupplyReady.empty) hs₁
  have htag₀ : (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩).memory.nextTag = 1 := rfl
  have hid₀ : (⟨(mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 msc41).machine.memory.nextAllocId,
      AllocIdSupplyReady.empty.nonzero⟩ : Miri.Memory.AllocId) = lm31AllocId1 := rfl
  rw [htag₀, hid₀] at hrel₁
  obtain ⟨_, himm_s₁⟩ := step_rawPtr_addrOf_preserves_ne hrel₀ rfl rfl rfl rfl
    (Or.inr (Or.inl rfl)) (by decide) (fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩)
    AllocIdSupplyReady.empty hm₁
  have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
    fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
  let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
  have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
  obtain ⟨m₂, hm₂, hrel₂⟩ := stepRelLM3_1_of_anneal_step
    (step_cast_ptrToPtr_simulation hrel₁ hphase rfl rfl rfl rfl rfl rfl rfl rfl rfl
      (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
      (fun _ => slot_ptr_ne_scalar)) hs₂
  obtain ⟨_, himm_s₂⟩ := step_assign_cast_ptrToPtr_preserves hrel₁ rfl rfl hm₂
  have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
    exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
  obtain ⟨hsim₃, hs₃_eq, m₃, _, _, hm₃, _, _⟩ :=
    step_binOp_offset_stride_simulation hrel₂ hphase (Or.inl rfl) rfl rfl
      (dstDecl := rawPtrMutU8Decl) (ptrDecl := rawPtrMutU8Decl) (tgtDecl := charDeclLM31)
      (rhsTy := usizeTyLM31) rfl rfl rfl rfl
      (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
      (fun tf _ => .of_wt (constUsize_wellTyped b tf 1 (by decide)))
      (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
      (ptrVal := { allocId := 1, offsetBytes := 0 }) (count := 1)
      rfl rfl (by rintro ⟨⟩) (.head _) rfl (by rintro ⟨⟩) rfl
      (Or.inr ⟨by rintro ⟨⟩, by change 0 + 1 * 1 ≤ 4; decide⟩)
  let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .init ptr0, .init ptr1, .uninit] bor 2
  have hs₃ : stepMirFn b s₂ = .step s₃ := hs₃_eq
  obtain ⟨m₃', hm₃_eq, hrel₃⟩ := stepRelLM3_1_of_anneal_step hsim₃ hs₃
  have hm₃_inj : m₃' = m₃ := (Prod.mk.inj (hm₃_eq.symm.trans hm₃)).1; subst m₃'
  obtain ⟨_, himm_s₃⟩ := step_assign_binOp_offset_preserves hrel₂ (by rintro _ ⟨⟩) rfl rfl hm₃
  have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
    exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
  let s₄ := mkWitState b 4 [.uninit, .init (.scalar ⟨0x41, 4⟩), .init ptr0, .init ptr0, .init ptr1,
    .init (.scalar ⟨0xD8, 1⟩)] bor 2
  have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
  obtain ⟨m₄, hm₄, hrel₄⟩ := stepRelLM3_1_of_anneal_step
    (step_scalar_use_lm3_1_simulation hrel₃ hphase rfl rfl (dstDecl := u8DeclLM31)
      (valTy := u8TyLM31) rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) rfl
      (fun tf _ => .constScalar (constU8LM31 0xD8) ⟨0xD8, 1⟩ rfl
        (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl) (by decide) rfl
        (fun h => nomatch h) (fun h => nomatch h))
      (fun tf htf => himm₃ tf htf 5 (by decide))) hs₄
  obtain ⟨_, himm_s₄⟩ := step_assign_use_preserves hrel₃ (by rintro _ ⟨⟩) rfl rfl hm₄
  have himm₄ : ∀ tf, m₄.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
    intro tf htf k hne; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
    exact himm_s₄ tf₃ tf htf₃ htf k (himm₃ tf₃ htf₃ k hne)
  obtain ⟨s₅, m₅, msc_merged, hs₅_eq, hs₅, hm₅, hraw₅⟩ :=
    step_deref_raw_subrange_write_into_bool_or_char_correspondence hrel₄ hphase rfl rfl
      (ptrDecl := rawPtrMutU8Decl) (tgtDecl := charDeclLM31) (valTy := u8TyLM31)
      rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) rfl
      (fun tf htf => .moveLocal 5 u8DeclLM31 rfl
        (by change Miri.ABI.Size.ofBytes 1 ≠ Miri.ABI.Size.ZERO; decide)
        (himm₄ tf htf 5 (by decide)))
      (fun tf htf => himm₄ tf htf 4 (by decide))
      (ptrVal := { allocId := 1, offsetBytes := 1 }) (oldSc := ⟨0x41, 4⟩)
      (wSc := ⟨0xD8, 1⟩) (mergedSc := ⟨0xD841, 4⟩)
      rfl rfl (.head _) rfl (Or.inl rfl) rfl (Or.inr (Or.inl rfl)) rfl
      (by change 1 + 1 ≤ 4; decide) (by change 1 % 1 = 0; decide) rfl
  obtain ⟨_, himm_s₅⟩ := step_preserves_of_rvalue hrel₄ rfl rfl
    (evalStatement_assign_use_eq b.localDecls b.layouts (derefLocal 4) (.move (local_ 5)) _ m₄)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves b.localDecls b.layouts (translatePlace (derefLocal 4)))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_any_preserves b.localDecls b.layouts
          (translateOperand (.move (local_ 5))) (some dp.layout))
        (fun opTy => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves opTy)
          (fun imm => annealWriteImmediate_preserves imm.imm dp))))
    hm₅
  have himm₅_2 : ∀ tf, m₅.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf htf; obtain ⟨tf₄, htf₄, _⟩ := id hrel₄
    exact himm_s₅ tf₄ tf htf₄ htf 2 (himm₄ tf₄ htf₄ 2 (by decide))
  exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, msc_merged,
    hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hs₅, hm₅,
    by rw [hs₅_eq]; rfl, by rw [hs₅_eq]; rfl, by rw [hs₅_eq]; rfl,
    by rw [hs₅_eq]; rfl, by rw [hs₅_eq]; rfl, by rw [hs₅_eq]; rfl,
    by rw [hs₅_eq]; rfl, himm₅_2, hraw₅⟩

/-- **`wit_lm3_1_raw_subbyte_write_and_composed_oob_misaligned_real_steps`**:
1. **Sub-byte `move` raw overwrite of `char` (`lm31RawSubbyteMoveOverwriteCharBody`)**:
   splicing `0xD8_u8` via `*_4 = move _5` at byte offset `1` of promoted `_1 : char`
   (`'A' = 0x41 -> 0xD841`) steps in lockstep into `RawOverwrittenScalarState`
   (`step_deref_raw_subrange_write_into_bool_or_char_correspondence`, leaving `_5 = .uninit`),
   after which (1a) `copy *_2` raises UB in BOTH machines
   (`step_raw_overwritten_deref_invalid_bool_or_char_simulation`) while (1b) `move _1`
   steps in Anneal (`_1 = .uninit`, `_0 = 0xD841`) and raises `"reading invalid value"` in
   `lean-miri` (`step_raw_overwritten_direct_copy_invalid_char_divergence`).
2. **5-step composed `step_mir_lm3_1_state_simulation` partial-overlap OOB write UB**:
   `lm31ComposedPartialOobWriteBody` (`*mut u32` write at byte offset `6` of `_1 : u64`)
   driven end-to-end through `step_mir_lm3_1_state_simulation` via
   `WellTypedLM3_1StateStmt.derefWriteNarrowerPartialOobUb` (without an explicit `localAlloc`).
3. **5-step composed `step_mir_lm3_1_state_simulation` `AllocId`-free misaligned read & write UB**:
   `lm31ComposedMisalignedOffsetBody false` (`move *_5` at byte offset `2` of `_1 : u64`) and
   `lm31ComposedMisalignedOffsetBody true` (`*_5 = const 7_u32` at byte offset `2` of `_1 : u64`)
   driven end-to-end through `step_mir_lm3_1_state_simulation` via
   `WellTypedLM3_1StateStmt.derefReadMisalignedOffsetUb` and
   `WellTypedLM3_1StateStmt.derefWriteMisalignedOffsetUb` (proved from `2 % 4 ≠ 0` without
   referencing `e.allocId` or `localAlloc`). -/
theorem wit_lm3_1_raw_subbyte_write_and_composed_oob_misaligned_real_steps :
    (let b := lm31RawSubbyteMoveOverwriteCharBody true
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ s₄ s₅ m₁ m₂ m₃ m₄ m₅ m₆ msg,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) =
         (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .step s₄ ∧ Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
       stepMirFn b s₄ = .step s₅ ∧ Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
       get? s₅.frame.locals 5 = some .uninit ∧
       get? s₅.frame.locals 1 = some (.init (.scalar ⟨0xD841, 4⟩)) ∧
       stepMirFn b s₅ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₅ = (m₆, .error (.undefinedBehavior msg))) ∧
    (let b := lm31RawSubbyteMoveOverwriteCharBody false
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ s₄ s₅ s₆ m₁ m₂ m₃ m₄ m₅ m₆,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨0x41, 4⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b charTyLM31 charTyLM31 (Miri.Memory.ScalarInt.ofUInt32 0x41)) =
         (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .step s₄ ∧ Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
       stepMirFn b s₄ = .step s₅ ∧ Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
       stepMirFn b s₅ = .step s₆ ∧
       get? s₆.frame.locals 1 = some .uninit ∧
       get? s₆.frame.locals 0 = some (.init (.scalar ⟨0xD841, 4⟩)) ∧
       Miri.Interpreter.Step.step hooks () m₅ =
         (m₆, .error (.undefinedBehavior "reading invalid value"))) ∧
    (let b := lm31ComposedPartialOobWriteBody
     let hooks := annealStepHooks b.localDecls b.layouts
     ∃ s₁ s₂ s₃ s₄ m₁ m₂ m₃ m₄ m₅ map₅ msg,
       stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
       Miri.Interpreter.Step.step hooks ()
         (mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) = (m₁, .ok true) ∧
       stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
       stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
       stepMirFn b s₃ = .step s₄ ∧ Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
       StepObsRelLM3_1 b m₄ map₅ (stepMirFn b s₄) (Miri.Interpreter.Step.step hooks () m₄) ∧
       stepMirFn b s₄ = .fail .ub ∧
       Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) ∧
    (∀ isWrite : Bool,
      let b := lm31ComposedMisalignedOffsetBody isWrite
      let hooks := annealStepHooks b.localDecls b.layouts
      ∃ s₁ s₂ s₃ s₄ m₁ m₂ m₃ m₄ m₅ map₅ msg,
        stepMirFn b (mkSixLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
        Miri.Interpreter.Step.step hooks ()
          (mkSixLocalScalarMiriPre b u32TyLM31 u64Ty lm31Scalar42) = (m₁, .ok true) ∧
        stepMirFn b s₁ = .step s₂ ∧ Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        stepMirFn b s₂ = .step s₃ ∧ Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        stepMirFn b s₃ = .step s₄ ∧ Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        StepObsRelLM3_1 b m₄ map₅ (stepMirFn b s₄) (Miri.Interpreter.Step.step hooks () m₄) ∧
        stepMirFn b s₄ = .fail .ub ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .error (.undefinedBehavior msg))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, _,
        hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hs₅, hm₅,
        hblk, hidx, _, _, hl1, hl2, hl5, himm₅, hraw₅⟩ :=
      rawSubbyteMoveOverwriteChar_reach_state true
    obtain ⟨hsim₆, hs₆⟩ := step_raw_overwritten_deref_invalid_bool_or_char_simulation hraw₅
      (fun _ h => nomatch h) (Or.inl rfl) (by rw [hblk]; rfl) (by rw [hidx]; rfl)
      (dstDecl := charDeclLM31) (ptrDecl := rawPtrMutCharDecl) (tgtDecl := charDeclLM31)
      rfl rfl rfl rfl (by decide) (by decide) himm₅ hl2 rfl (.head _) rfl rfl rfl
      (Or.inr ⟨rfl, rfl, rfl, by decide, by decide⟩)
    obtain ⟨m₆, msg, hm₆⟩ := stepRelLM3_1_of_anneal_ub hsim₆ hs₆
    exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, m₆, msg,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hs₅, hm₅, hl5, hl1, hs₆, hm₆⟩
  · obtain ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, _,
        hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hs₅, hm₅,
        hblk, hidx, hlen₅, hl0, _, _, _, _, hraw₅⟩ :=
      rawSubbyteMoveOverwriteChar_reach_state false
    obtain ⟨hs₆, m₆, hm₆⟩ := step_raw_overwritten_direct_copy_invalid_char_divergence hraw₅
      (fun _ h => nomatch h) (Or.inr rfl) (by rw [hblk]; rfl) (by rw [hidx]; rfl)
      (dstDecl := charDeclLM31) (locDecl := charDeclLM31) rfl rfl rfl rfl (by decide)
      (by rw [hl0]; rintro ⟨⟩) rfl (by decide) (by decide)
    refine ⟨s₁, s₂, s₃, s₄, s₅, _, m₁, m₂, m₃, m₄, m₅, m₆,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hs₅, hm₅, hs₆, ?_, ?_, hm₆⟩
    · dsimp only [advanceStmt, offsetAfterLhsLocals]
      rw [get?_eq_getElem?, List.getElem?_set_ne (by decide), List.getElem?_set_self (by omega)]
    · dsimp only [advanceStmt, offsetAfterLhsLocals]
      rw [get?_eq_getElem?, List.getElem?_set_self (by simp [hlen₅])]
  · let b := lm31ComposedPartialOobWriteBody
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let s₀ := mkSixLocalScalarAnnealPre b ⟨42, 8⟩
    let m₀ := mkSixLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkSixLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrMutU64Decl
        rawPtrMutU8Decl rawPtrMutU8Decl rawPtrMutU32Decl ⟨42, 8⟩ lm31Scalar42
        rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)).toLM3_1
    have himm₀ := mkSixLocalScalar_all_immediate b u64Ty u64Ty lm31Scalar42
    have himm01 : ∀ tf, m₀.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr6 := Value.ptr { allocId := 1, offsetBytes := 6 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    have hwt₀ : WellTypedLM3_1StateStmt b s₀ m₀ []
        (mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .mut (.uint .u64) rawPtrMutU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
    obtain ⟨map₁, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm_s₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
        AllocIdSupplyReady.empty (by decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ map₁
        (mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty))) :=
      .castPtrToPtr 3 2 rawPtrMutU8Ty rawPtrMutU8Decl rawPtrMutU64Decl
        .mut .mut .mut (.uint .u64) (.uint .u8) _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₂, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_1_of_anneal_step hsim₂ hs₂
    obtain ⟨⟨hsupply₂, _, _⟩, himm_s₂⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₁ rfl rfl hsupply₁ hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨e₂, he₂, htag₂, hloc₂, hperm₂⟩ := allocMap_singleton_of_stateRel hrel₂ rfl
    have hwt₂ : WellTypedLM3_1StateStmt b s₂ m₂ map₂
        (mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 6))))) :=
      .binOpOffsetStride 4 3 MirAst.Operand.copy (.constant (constUsizeLM31 6))
        rawPtrMutU8Decl rawPtrMutU8Decl u64Decl .mut .mut (.uint .u8) usizeTyLM31
        { allocId := 1, offsetBytes := 0 } 6 s₂.frame.locals e₂ _
        (Or.inl rfl) rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 6 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
        rfl rfl (by rintro ⟨⟩) he₂ htag₂ (by rw [hperm₂]; rintro ⟨⟩) (by rw [hloc₂]; rfl)
        (Or.inr ⟨by rw [hloc₂]; rintro ⟨⟩, by decide⟩)
    obtain ⟨map₃, hsim₃⟩ := step_mir_lm3_1_state_simulation hrel₂ hphase rfl
      (Or.inl ⟨_, rfl, hwt₂⟩) hsupply₂
    let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr6, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepObsRelLM3_1_of_anneal_step hsim₃ hs₃
    obtain ⟨⟨hsupply₃, _, _⟩, himm_s₃⟩ :=
      step_assign_binOp_offset_preserves_supply hrel₂ rfl rfl hsupply₂ hm₃
    have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
    have hwt₃ : WellTypedLM3_1StateStmt b s₃ m₃ map₃
        (mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrMutU32Ty))) :=
      .castPtrToPtr 5 4 rawPtrMutU32Ty rawPtrMutU32Decl rawPtrMutU8Decl
        .mut .mut .mut (.uint .u8) (.uint .u32) _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₃ tf htf 5 (by decide), himm₃ tf htf 4 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₄, hsim₄⟩ := step_mir_lm3_1_state_simulation hrel₃ hphase rfl
      (Or.inl ⟨_, rfl, hwt₃⟩) hsupply₃
    let s₄ := mkWitState b 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr6, .init ptr6] bor 2
    have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepObsRelLM3_1_of_anneal_step hsim₄ hs₄
    obtain ⟨⟨hsupply₄, _, _⟩, himm_s₄⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₃ rfl rfl hsupply₃ hm₄
    have himm₄_5 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 5 := by
      intro tf htf; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
      exact himm_s₄ tf₃ tf htf₃ htf 5 (himm₃ tf₃ htf₃ 5 (by decide))
    obtain ⟨e₄, he₄, htag₄, hloc₄, _⟩ := allocMap_singleton_of_stateRel hrel₄ rfl
    have hwt₄ : WellTypedLM3_1StateStmt b s₄ m₄ map₄
        (mkStmt (.assign (derefLocal 5) (.use (.constant (constU32LM31 7))))) :=
      .derefWriteNarrowerPartialOobUb 5 (.constant (constU32LM31 7))
        rawPtrMutU32Decl u64Decl .mut (.uint .u32) u32TyLM31
        { allocId := 1, offsetBytes := 6 } e₄ _
        rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
        (fun tf _ => .of_wt (constU32_wellTyped b tf 7 (by decide)))
        himm₄_5 rfl he₄ htag₄ (by rw [hloc₄]; rfl) (by rw [hloc₄]; rintro ⟨⟩) (by decide)
    obtain ⟨map₅, hsim₅⟩ := step_mir_lm3_1_state_simulation hrel₄ hphase rfl
      (Or.inl ⟨_, rfl, hwt₄⟩) hsupply₄
    obtain ⟨_, hs₅⟩ := step_deref_write_narrower_partial_oob_simulation hrel₄ hphase rfl rfl
      (ptrDecl := rawPtrMutU32Decl) (tgtDecl := u64Decl) (valTy := u32TyLM31)
      rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
      (fun tf _ => .of_wt (constU32_wellTyped b tf 7 (by decide)))
      himm₄_5 rfl he₄ htag₄ (by rw [hloc₄]; rfl) (by rw [hloc₄]; rintro ⟨⟩) (by decide)
    obtain ⟨msg, hm₅_err⟩ := (StepObsRelLM3_1.ub_iff hsim₅).mp hs₅
    exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, _, map₅, msg,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hsim₅, hs₅, Prod.ext rfl hm₅_err⟩
  · intro isWrite
    let b := lm31ComposedMisalignedOffsetBody isWrite
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    let s₀ := mkSixLocalScalarAnnealPre b ⟨42, 8⟩
    let m₀ := mkSixLocalScalarMiriPre b u32TyLM31 u64Ty lm31Scalar42
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkSixLocalScalar_stateRel b u32TyLM31 u32DeclLM31 u64Decl rawPtrMutU64Decl
        rawPtrMutU8Decl rawPtrMutU8Decl rawPtrMutU32Decl ⟨42, 8⟩ lm31Scalar42
        rfl rfl lm31_scalarRel42 rfl (fun h => nomatch h) (fun h => nomatch h)).toLM3_1
    have himm₀ := mkSixLocalScalar_all_immediate b u32TyLM31 u64Ty lm31Scalar42
    have himm01 : ∀ tf, m₀.stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨himm₀ tf htf 2, himm₀ tf htf 1⟩
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr2 := Value.ptr { allocId := 1, offsetBytes := 2 } 8
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    have hwt₀ : WellTypedLM3_1StateStmt b s₀ m₀ []
        (mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .mut (.uint .u64) rawPtrMutU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
    obtain ⟨map₁, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm_s₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
        AllocIdSupplyReady.empty (by change 1 + 1 < 2 ^ 32; decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf, m₁.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k :=
      fun tf htf k hne => himm_s₁ _ tf rfl htf k hne (himm₀ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ map₁
        (mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty))) :=
      .castPtrToPtr 3 2 rawPtrMutU8Ty rawPtrMutU8Decl rawPtrMutU64Decl
        .mut .mut .mut (.uint .u64) (.uint .u8) _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₁ tf htf 3 (by decide), himm₁ tf htf 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₂, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_1_of_anneal_step hsim₂ hs₂
    obtain ⟨⟨hsupply₂, _, _⟩, himm_s₂⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₁ rfl rfl hsupply₁ hm₂
    have himm₂ : ∀ tf, m₂.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf htf₁ htf k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨e₂, he₂, htag₂, hloc₂, hperm₂⟩ := allocMap_singleton_of_stateRel hrel₂ rfl
    have hwt₂ : WellTypedLM3_1StateStmt b s₂ m₂ map₂
        (mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 2))))) :=
      .binOpOffsetStride 4 3 MirAst.Operand.copy (.constant (constUsizeLM31 2))
        rawPtrMutU8Decl rawPtrMutU8Decl u64Decl .mut .mut (.uint .u8) usizeTyLM31
        { allocId := 1, offsetBytes := 0 } 2 s₂.frame.locals e₂ _
        (Or.inl rfl) rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
        (fun tf _ => .of_wt (constUsize_wellTyped b tf 2 (by decide)))
        (fun tf htf => ⟨himm₂ tf htf 4 (by decide), himm₂ tf htf 3 (by decide)⟩)
        rfl rfl (by rintro ⟨⟩) he₂ htag₂ (by rw [hperm₂]; rintro ⟨⟩) (by rw [hloc₂]; rfl)
        (Or.inr ⟨by rw [hloc₂]; rintro ⟨⟩, by change 0 + 2 * 1 ≤ 8; decide⟩)
    obtain ⟨map₃, hsim₃⟩ := step_mir_lm3_1_state_simulation hrel₂ hphase rfl
      (Or.inl ⟨_, rfl, hwt₂⟩) hsupply₂
    let s₃ := mkWitState b 3 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (hinb := Or.inr ⟨by rintro ⟨⟩, by change 0 + 2 * 1 ≤ 8; decide⟩)
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepObsRelLM3_1_of_anneal_step hsim₃ hs₃
    obtain ⟨⟨hsupply₃, _, _⟩, himm_s₃⟩ :=
      step_assign_binOp_offset_preserves_supply hrel₂ rfl rfl hsupply₂ hm₃
    have himm₃ : ∀ tf, m₃.stack.frames = #[tf] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf k := by
      intro tf htf k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf htf₂ htf k (himm₂ tf₂ htf₂ k hne)
    have hwt₃ : WellTypedLM3_1StateStmt b s₃ m₃ map₃
        (mkStmt (.assign (local_ 5) (.cast .ptrToPtr (.copy (local_ 4)) rawPtrMutU32Ty))) :=
      .castPtrToPtr 5 4 rawPtrMutU32Ty rawPtrMutU32Decl rawPtrMutU8Decl
        .mut .mut .mut (.uint .u8) (.uint .u32) _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨himm₃ tf htf 5 (by decide), himm₃ tf htf 4 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₄, hsim₄⟩ := step_mir_lm3_1_state_simulation hrel₃ hphase rfl
      (Or.inl ⟨_, rfl, hwt₃⟩) hsupply₃
    let s₄ := mkWitState b 4 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr2, .init ptr2] bor 2
    have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepObsRelLM3_1_of_anneal_step hsim₄ hs₄
    obtain ⟨⟨hsupply₄, _, _⟩, himm_s₄⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₃ rfl rfl hsupply₃ hm₄
    have himm₄_5 : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 5 := by
      intro tf htf; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
      exact himm_s₄ tf₃ tf htf₃ htf 5 (himm₃ tf₃ htf₃ 5 (by decide))
    obtain ⟨e₄, he₄, htag₄, hloc₄, _⟩ := allocMap_singleton_of_stateRel hrel₄ rfl
    cases isWrite
    · have hwt₄ : WellTypedLM3_1StateStmt b s₄ m₄ map₄
          (mkStmt (.assign (local_ 0) (.use (.move (derefLocal 5))))) :=
        .derefReadMisalignedOffsetUb 0 5 MirAst.Operand.move
          u32DeclLM31 rawPtrMutU32Decl u64Decl .mut
          { allocId := 1, offsetBytes := 2 } e₄ _
          (Or.inr rfl) rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
          himm₄_5 rfl he₄ htag₄ (by rw [hloc₄]; rfl) (by rw [hloc₄]; rintro ⟨⟩)
          (by decide) (by decide)
      obtain ⟨map₅, hsim₅⟩ := step_mir_lm3_1_state_simulation hrel₄ hphase rfl
        (Or.inl ⟨_, rfl, hwt₄⟩) hsupply₄
      obtain ⟨_, hs₅⟩ := step_deref_read_misaligned_offset_simulation hrel₄ hphase (Or.inr rfl)
        rfl rfl (dstDecl := u32DeclLM31) (ptrDecl := rawPtrMutU32Decl) (tgtDecl := u64Decl)
        rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
        himm₄_5 rfl he₄ htag₄ (by rw [hloc₄]; rfl) (by rw [hloc₄]; rintro ⟨⟩)
        (by decide) (by decide)
      obtain ⟨msg, hm₅_err⟩ := (StepObsRelLM3_1.ub_iff hsim₅).mp hs₅
      exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, _, map₅, msg,
        hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hsim₅, hs₅, Prod.ext rfl hm₅_err⟩
    · have hwt₄ : WellTypedLM3_1StateStmt b s₄ m₄ map₄
          (mkStmt (.assign (derefLocal 5) (.use (.constant (constU32LM31 7))))) :=
        .derefWriteMisalignedOffsetUb 5 (.constant (constU32LM31 7))
          rawPtrMutU32Decl u64Decl .mut (.uint .u32) u32TyLM31
          { allocId := 1, offsetBytes := 2 } e₄ _
          rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
          (fun tf _ => .of_wt (constU32_wellTyped b tf 7 (by decide)))
          himm₄_5 rfl he₄ htag₄ (by rw [hloc₄]; rfl) (by rw [hloc₄]; rintro ⟨⟩)
          (by decide) (by decide)
      obtain ⟨map₅, hsim₅⟩ := step_mir_lm3_1_state_simulation hrel₄ hphase rfl
        (Or.inl ⟨_, rfl, hwt₄⟩) hsupply₄
      obtain ⟨_, hs₅⟩ := step_deref_write_misaligned_offset_simulation hrel₄ hphase rfl rfl
        (ptrDecl := rawPtrMutU32Decl) (tgtDecl := u64Decl) (valTy := u32TyLM31)
        rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u32, rfl⟩))) rfl
        (fun tf _ => .of_wt (constU32_wellTyped b tf 7 (by decide)))
        himm₄_5 rfl he₄ htag₄ (by rw [hloc₄]; rfl) (by rw [hloc₄]; rintro ⟨⟩)
        (by decide) (by decide)
      obtain ⟨msg, hm₅_err⟩ := (StepObsRelLM3_1.ub_iff hsim₅).mp hs₅
      exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, _, map₅, msg,
        hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hsim₅, hs₅, Prod.ext rfl hm₅_err⟩

/-! ## 15. `D7..D12` Unified `step_mir_lm3_1_state_simulation` Real-Step Witnesses -/

private theorem evalStatement_assign_binaryOp_eq
    (ld : List LocalDecl) (ly : LayoutTable)
    (dst : Place) (bop : MirAst.BinOp) (lhs rhs : MirAst.Operand)
    (span : String) (m : AnnealStepState) :
    Miri.Interpreter.Step.evalStatement (annealStepHooks ld ly) ()
      (translateStmt ⟨.assign dst (.binaryOp bop lhs rhs), span⟩) m =
      Miri.Interpreter.runRvalue
        (do
          let dest ← annealEvalPlace ld ly (translatePlace dst)
          let layout := dest.layout
          let left ← annealEvalOperand ld ly (translateOperand lhs)
            (if (translateBinOp bop).leftHomogeneous then some layout else none)
          let left ← annealReadImmediate left
          let right ← annealEvalOperand ld ly (translateOperand rhs)
            (if (translateBinOp bop).rightHomogeneous then some left.layout else none)
          let right ← annealReadImmediate right
          let result ← Miri.Interpreter.ScalarOps.binary
            (annealScalarOpsHooks ld ly) () (translateBinOp bop) left right
          assertRvalueLayoutPub result.layout layout
          annealWriteImmediate result.imm dest) m := by
  unfold Miri.Interpreter.Step.evalStatement translateStmt
  dsimp only [translateStmtKind, translateRvalue, annealStepHooks]
  apply runRvalue_eq_of_eq
  rw [evalRvalueIntoPlace_binaryOp_def]
  rfl

theorem step_assign_binaryOp_preserves_supply
    {body : CapturedMir} {s : MachineState} {m m' : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hstate : StateRelLM3_1 body s m allocMap)
    {bb : BasicBlockData} {dst : Place} {bop : MirAst.BinOp}
    {lhs rhs : MirAst.Operand} {span : String}
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign dst (.binaryOp bop lhs rhs), span⟩)
    (hsupply : AllocIdSupplyReady m.machine.memory)
    (hstep : Miri.Interpreter.Step.step
      (annealStepHooks body.localDecls body.layouts) () m = (m', .ok true)) :
    (AllocIdSupplyReady m'.machine.memory ∧
      m'.machine.memory.nextAllocId = m.machine.memory.nextAllocId ∧
      m'.machine.memory.sourceAllocIdWorldActive = m.machine.memory.sourceAllocIdWorldActive) ∧
    (∀ tf tf', m.stack.frames = #[tf] → m'.stack.frames = #[tf'] →
      ∀ k, IsImmediateFrameLocal tf k → IsImmediateFrameLocal tf' k) :=
  step_preserves_supply_of_rvalue hstate hbb hstmt
    (evalStatement_assign_binaryOp_eq body.localDecls body.layouts dst bop lhs rhs span m)
    (rvaluePreservesAllImm_bind
      (annealEvalPlace_preserves body.localDecls body.layouts (translatePlace dst))
      (fun dp => rvaluePreservesAllImm_bind
        (annealEvalOperand_any_preserves body.localDecls body.layouts
          (translateOperand lhs)
          (if (translateBinOp bop).leftHomogeneous then some dp.layout else none))
        (fun lOp => rvaluePreservesAllImm_bind
          (annealReadImmediate_preserves lOp)
          (fun lv => rvaluePreservesAllImm_bind
            (annealEvalOperand_any_preserves body.localDecls body.layouts
              (translateOperand rhs)
              (if (translateBinOp bop).rightHomogeneous then some lv.layout else none))
            (fun rOp => rvaluePreservesAllImm_bind
              (annealReadImmediate_preserves rOp)
              (fun rv => rvaluePreservesAllImm_bind
                (scalarOps_binary_preserves body.localDecls body.layouts (translateBinOp bop) lv rv)
                (fun res => rvaluePreservesAllImm_bind
                  (assertRvalueLayoutPub_preserves res.layout dp.layout)
                  (fun _ => annealWriteImmediate_preserves res.imm dp))))))))
    hsupply hstep

private theorem StateRelLM3_1.of_same_allocs
    {body : CapturedMir} {s : MachineState} {m : AnnealStepState}
    {allocMap : List AllocMapEntry}
    (hrel : StateRelLM3_1 body s m allocMap)
    (hbor : s.memory.borrows = [] := by rfl) :
    StateRelLM3_1 body s m [] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hbor_eq, _, _⟩ := id hrel
  rw [hbor] at hbor_eq
  cases allocMap with
  | nil => exact hrel
  | cons _ _ => cases hbor_eq

private theorem ptrAddress_singleton_eq
    (locals callerLocals : List LocalSlot) (localDecls : List LocalDecl) (layouts : LayoutTable)
    (b : BorrowEntry) (p : ProvenancePtr) (a : Nat)
    (htag : Nat.beq b.tag p.tag = true := by rfl)
    (hproj : b.targetProjection = .nil := by rfl)
    (ha : (1048576 + b.targetLocal) * 65536 + p.offsetBytes = a := by decide) :
    ptrAddress? locals [b] callerLocals localDecls layouts 8 p = some a := by
  have hboff : borrowPlaceByteOffset? locals callerLocals localDecls layouts b = some 0 := by
    unfold borrowPlaceByteOffset?; rw [hproj]; rfl
  have hbase : borrowBaseAddress? locals callerLocals localDecls layouts 8 b =
      some ((1048576 + b.targetLocal) * 65536) := by
    unfold borrowBaseAddress?; rw [hboff]; dsimp only [stackLocalAddrPageBase]
    change some (((1048576 + b.targetLocal) * 65536) + 0) = some ((1048576 + b.targetLocal) * 65536)
    rw [Nat.add_zero]
  unfold ptrAddress? lookupBorrow
  rw [htag]; dsimp only []
  rw [hbase]; dsimp only []
  exact congrArg some ha

private theorem stepMirFn_rawPtr_cmp_copy_eq
    {body : CapturedMir} {s s' : MachineState}
    {bb : BasicBlockData} {dstIdx lhsIdx rhsIdx : Local}
    {bop : MirAst.BinOp} {span : String}
    {v₁ v₂ : Value} {bRes : Bool} {slot_d : LocalSlot}
    (a₁ a₂ : Nat)
    (hphase : ∀ p, body.phase ≠ .other p)
    (hcal : s.memory.activeCallee = none := by rfl)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb := by rfl)
    (hstmt : get? bb.statements s.frame.stmtIdx =
      some ⟨.assign ⟨dstIdx, .nil⟩ (.binaryOp bop (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩)),
        span⟩ := by rfl)
    (hlhs : get? s.frame.locals lhsIdx = some (.init v₁) := by rfl)
    (hrhs : get? s.frame.locals rhsIdx = some (.init v₂) := by rfl)
    (hrel : isPtrRelationalBinOp bop body.localDecls body.layouts
      (.copy ⟨lhsIdx, .nil⟩) (.copy ⟨rhsIdx, .nil⟩) = true := by rfl)
    (hptr8 : layoutPointerBytes body.layouts = 8 := by rfl)
    (ha₁_lt : a₁ < 18446744073709551616 := by decide)
    (ha₂_lt : a₂ < 18446744073709551616 := by decide)
    (hv₁ : (v₁ = .scalar ⟨a₁, 8⟩) ∨
      ∃ p₁, v₁ = .ptr p₁ 8 ∧
        ptrAddress? s.frame.locals s.memory.borrows s.memory.callerLocals
          body.localDecls body.layouts 8 p₁ = some a₁)
    (hv₂ : ∃ p₂, v₂ = .ptr p₂ 8 ∧
      ptrAddress? s.frame.locals s.memory.borrows s.memory.callerLocals
        body.localDecls body.layouts 8 p₂ = some a₂)
    (hcmp : evalScalarBinOp bop ⟨a₁, 8⟩ ⟨a₂, 8⟩ s.frame.locals s.memory false =
      .ok (.scalar (boolToScalar bRes)) s.frame.locals s.memory)
    (hslot_d : get? s.frame.locals dstIdx = some slot_d := by rfl)
    (hd_ne : slot_d ≠ .dead := by decide)
    (hset_d : set? s.frame.locals dstIdx (.init (.scalar (boolToScalar bRes))) =
      some s'.frame.locals := by rfl)
    (hprot : s.memory.activeProtectors = .nil := by rfl)
    (hs' : advanceStmt s s'.frame.locals
      { s.memory with
        borrows := invalidateConflictingBorrows s.memory.borrows dstIdx none
        activeProtectors := .nil } = s' := by rfl) :
    stepMirFn body s = .step s' := by
  have hm8 : scalarModulus 8 = 18446744073709551616 := rfl
  have hbeq8 : (8 : Nat).beq 8 = true := rfl
  have hble₂ : Nat.ble 18446744073709551616 a₂ = false := by
    rw [nat_ble_eq_decide]; exact decide_eq_false (by omega)
  obtain ⟨p₂, rfl, hpa₂⟩ := hv₂
  have hps₂ : ptrAddressScalar? s.frame.locals s.memory.borrows s.memory.callerLocals
      body.localDecls body.layouts 8 p₂ 8 = some ⟨a₂, 8⟩ := by
    unfold ptrAddressScalar?; rw [hpa₂]; dsimp only []
    unfold wrapScalarBits; rw [hm8, hble₂]
  rw [stepMirFn_eq_of_not_other body s hcal hphase]
  simp only [hbb, hstmt]
  unfold evalStmt evalRvalue
  dsimp only []
  have hop₁ : evalOperand s.frame.locals (.copy ⟨lhsIdx, .nil⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok v₁ s.frame.locals := by
    unfold evalOperand readProjectedValue; dsimp only []; rw [hlhs]
  have hop₂ : evalOperand s.frame.locals (.copy ⟨rhsIdx, .nil⟩) s.memory.borrows s.memory.globals
      body.layouts s.memory.callerLocals body.localDecls = .ok (.ptr p₂ 8) s.frame.locals := by
    unfold evalOperand readProjectedValue; dsimp only []; rw [hrhs]
  rw [hop₁]; dsimp only []; rw [hop₂]; dsimp only []
  rw [hrel, hptr8]
  rcases hv₁ with rfl | ⟨p₁, rfl, hpa₁⟩
  · dsimp only [hbeq8]; rw [hps₂]; dsimp only []; rw [hcmp]; dsimp only []
    rw [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hd_ne
    | uninit => simp only [hset_d, hprot, hs']
    | init _ => simp only [hset_d, hprot, hs']
  · have hble₁ : Nat.ble 18446744073709551616 a₁ = false := by
      rw [nat_ble_eq_decide]; exact decide_eq_false (by omega)
    have hps₁ : ptrAddressScalar? s.frame.locals s.memory.borrows s.memory.callerLocals
        body.localDecls body.layouts 8 p₁ 8 = some ⟨a₁, 8⟩ := by
      unfold ptrAddressScalar?; rw [hpa₁]; dsimp only []
      unfold wrapScalarBits; rw [hm8, hble₁]
    dsimp only [hbeq8]; rw [hps₁, hps₂]; dsimp only []; rw [hcmp]; dsimp only []
    rw [hslot_d]
    cases slot_d with
    | dead => exact absurd rfl hd_ne
    | uninit => simp only [hset_d, hprot, hs']
    | init _ => simp only [hset_d, hprot, hs']

/-- **`wit_lm3_1_d7_d11_state_simulation_real_steps`**:
Composed multi-step and single-step witnesses driven through unified
`step_mir_lm3_1_state_simulation` for **`D7..D11`**, each exporting BOTH machines'
real-step equations (`stepMirFn` and `Miri.Interpreter.Step.step`) plus the
post-step relation:
1. **D7 (`rawPtrDeref`, nonzero offset)**: 4-step execution of
   `lm31RawPtrDerefOffsetBody` (`_2 = &raw mut _1` -> `_3 = copy _2 as *mut u8` ->
   `_4 = Offset(copy _3, 1_usize)` -> `_5 = &raw const (*_4)`) preserving
   `StateRelLM3_1` at `offsetBytes = 1`.
2. **D8 (`castPtrToPtrScalar` / `castPtrToPtrMoveScalar`), D10
   (`binOpOffsetScalarZero`, `*const u8` and `*const u64` strides), and D11
   (`unaryOpPtrMetadata`)**: lockstep single steps on `lm31NullPtrToPtrBody`,
   `lm31MoveNullPtrToPtrBody`, `lm31NullOffsetZeroBody`, `lm31MoveNullOffsetZeroBody`,
   and `lm31PtrMetadataThinBody` from their initial states into
   `StateRelLM3_1`-related successors.
3. **D9 (`placeMentionDeref` / `placeMentionDerefUninitUb`)**: 2-step execution of
   `lm31PlaceMentionDerefBody` (`PlaceMention(*_1)` on null succeeds in lockstep,
   then `PlaceMention(*_2)` on uninitialized `_2` is UB in both machines).
4. **D7 (`rawPtrDeref`, `.frozen` parent)**: 2-step execution of
   `lm31RawPtrDerefFrozenMutBody` (`_2 = &raw const _1` -> `_3 = &raw mut (*_2)`)
   preserving `StateRelLM3_1` (raw place-to-pointer reborrows perform no
   permission check in either machine).
5. **D7 (`rawPtrDeref`, null) and D11 (`unaryOpPtrMetadataUb`)**: lockstep
   `_2 = &raw const (*_1)` on null `_1` (`lm31RawPtrDerefNullBody`) into a
   `StateRelLM3_1`-related successor, and lockstep UB of `_3 = PtrMetadata(copy _2)`
   on uninitialized `_2` (`lm31PtrMetadataUninitBody`). -/
theorem wit_lm3_1_d7_d11_state_simulation_real_steps :
    -- (1) D7 4-step `lm31RawPtrDerefOffsetBody` via `step_mir_lm3_1_state_simulation`
    (∃ (s₁ s₂ s₃ s₄ : MachineState) (m₁ m₂ m₃ m₄ : AnnealStepState)
      (map₄ : List AllocMapEntry),
      let b := lm31RawPtrDerefOffsetBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      StateRelLM3_1 b s₄ m₄ map₄ ∧
      get? s₄.frame.locals 5 = some (.init (.ptr { allocId := 1, offsetBytes := 1 } 8))) ∧
    -- (2) D8, D10, D11 lockstep single steps via `step_mir_lm3_1_state_simulation`
    (∃ (s_c s_mc s_o s_mo s_pm : MachineState)
      (m_c m_mc m_o m_mo m_pm : AnnealStepState),
      let bc := lm31NullPtrToPtrBody
      let bmc := lm31MoveNullPtrToPtrBody
      let bo := lm31NullOffsetZeroBody
      let bmo := lm31MoveNullOffsetZeroBody
      let bpm := lm31PtrMetadataThinBody
      stepMirFn bc (mkFourLocalScalarAnnealPre bc ⟨0, 8⟩) = .step s_c ∧
      Miri.Interpreter.Step.step (annealStepHooks bc.localDecls bc.layouts) ()
        (mkFourLocalScalarMiriPre bc u64Ty rawPtrConstU64Ty lm31Scalar0U64) = (m_c, .ok true) ∧
      StateRelLM3_1 bc s_c m_c [] ∧
      stepMirFn bmc (mkFourLocalScalarAnnealPre bmc ⟨0, 8⟩) = .step s_mc ∧
      Miri.Interpreter.Step.step (annealStepHooks bmc.localDecls bmc.layouts) ()
        (mkFourLocalScalarMiriPre bmc u64Ty rawPtrConstU64Ty lm31Scalar0U64) = (m_mc, .ok true) ∧
      StateRelLM3_1 bmc s_mc m_mc [] ∧
      stepMirFn bo (mkFourLocalScalarAnnealPre bo ⟨0, 8⟩) = .step s_o ∧
      Miri.Interpreter.Step.step (annealStepHooks bo.localDecls bo.layouts) ()
        (mkFourLocalScalarMiriPre bo u64Ty rawPtrConstU8Ty lm31Scalar0U64) = (m_o, .ok true) ∧
      StateRelLM3_1 bo s_o m_o [] ∧
      stepMirFn bmo (mkFourLocalScalarAnnealPre bmo ⟨0, 8⟩) = .step s_mo ∧
      Miri.Interpreter.Step.step (annealStepHooks bmo.localDecls bmo.layouts) ()
        (mkFourLocalScalarMiriPre bmo u64Ty rawPtrConstU64Ty lm31Scalar0U64) = (m_mo, .ok true) ∧
      StateRelLM3_1 bmo s_mo m_mo [] ∧
      stepMirFn bpm (mkFourLocalScalarAnnealPre bpm ⟨0, 8⟩) = .step s_pm ∧
      Miri.Interpreter.Step.step (annealStepHooks bpm.localDecls bpm.layouts) ()
        (mkFourLocalScalarMiriPre bpm u64Ty rawPtrConstU64Ty lm31Scalar0U64) = (m_pm, .ok true) ∧
      StateRelLM3_1 bpm s_pm m_pm [] ∧
      get? s_pm.frame.locals 3 = some (.init .unit)) ∧
    -- (3) D9 2-step `lm31PlaceMentionDerefBody` via `step_mir_lm3_1_state_simulation`
    (∃ (s₁ : MachineState) (m₁ m₂ : AnnealStepState) (msg : String),
      let b := lm31PlaceMentionDerefBody
      let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
      let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b s₀ = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () m₀ = (m₁, .ok true) ∧
      StateRelLM3_1 b s₁ m₁ [] ∧
      stepMirFn b s₁ = .fail .ub ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg))) ∧
    -- (4) D7 2-step `lm31RawPtrDerefFrozenMutBody` via `step_mir_lm3_1_state_simulation`
    (∃ (s₁ s₂ : MachineState) (m₁ m₂ : AnnealStepState) (map₂ : List AllocMapEntry),
      let b := lm31RawPtrDerefFrozenMutBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) =
        (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      StateRelLM3_1 b s₂ m₂ map₂ ∧
      get? s₂.frame.locals 3 = some (.init (.ptr { allocId := 1, offsetBytes := 0 } 8))) ∧
    -- (5) D7 null `&raw const (*_1)` and D11 `PtrMetadata` UB via `step_mir_lm3_1_state_simulation`
    (∃ (s_n : MachineState) (m_n m_u : AnnealStepState) (msg : String),
      let bn := lm31RawPtrDerefNullBody
      let bu := lm31PtrMetadataUninitBody
      stepMirFn bn (mkFourLocalScalarAnnealPre bn ⟨0, 8⟩) = .step s_n ∧
      Miri.Interpreter.Step.step (annealStepHooks bn.localDecls bn.layouts) ()
        (mkFourLocalScalarMiriPre bn u64Ty rawPtrConstU64Ty lm31Scalar0U64) = (m_n, .ok true) ∧
      StateRelLM3_1 bn s_n m_n [] ∧
      get? s_n.frame.locals 2 = some (.init (.scalar ⟨0, 8⟩)) ∧
      stepMirFn bu (mkFourLocalScalarAnnealPre bu ⟨0, 8⟩) = .fail .ub ∧
      Miri.Interpreter.Step.step (annealStepHooks bu.localDecls bu.layouts) ()
        (mkFourLocalScalarMiriPre bu u64Ty rawPtrConstU64Ty lm31Scalar0U64) =
        (m_u, .error (.undefinedBehavior msg))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Part (1): D7 4-step `lm31RawPtrDerefOffsetBody`
    let b := lm31RawPtrDerefOffsetBody
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr1 := Value.ptr { allocId := 1, offsetBytes := 1 } 8
    have hrel₀ : StateRelLM3_1 b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) [] :=
      (mkSixLocal_stateRel b u64Ty u64Decl rawPtrMutU64Decl rawPtrMutU8Decl
        rawPtrMutU8Decl rawPtrConstU8Decl rfl rfl).toLM3_1
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm01 : ∀ tf, (mkSixLocalMiriPre b u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    have hwt₀ : WellTypedLM3_1StateStmt b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) []
        (mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .mut (.uint .u64) rawPtrMutU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
    obtain ⟨map₁, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm_s₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
        AllocIdSupplyReady.empty (by change 1 + 1 < 2 ^ 32; decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne => himm_s₁ _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ map₁
        (mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty))) :=
      .castPtrToPtr 3 2 rawPtrMutU8Ty rawPtrMutU8Decl rawPtrMutU64Decl
        .mut .mut .mut (.uint .u64) (.uint .u8) _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₂, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    let s₂ := mkWitState b 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_1_of_anneal_step hsim₂ hs₂
    obtain ⟨⟨hsupply₂, _, _⟩, himm_s₂⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₁ rfl rfl hsupply₁ hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨e₂, he₂, htag₂, hloc₂, hperm₂⟩ := allocMap_singleton_of_stateRel hrel₂ rfl
    have hwt₂ : WellTypedLM3_1StateStmt b s₂ m₂ map₂
        (mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1))))) :=
      .binOpOffsetStride 4 3 MirAst.Operand.copy (.constant (constUsizeLM31 1))
        rawPtrMutU8Decl rawPtrMutU8Decl u64Decl .mut .mut (.uint .u8) usizeTyLM31
        { allocId := 1, offsetBytes := 0 } 1 s₂.frame.locals e₂ _
        (Or.inl rfl) rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
        (fun tf₂ _ => .of_wt (constUsize_wellTyped b tf₂ 1 (by decide)))
        (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
        rfl rfl (by rintro ⟨⟩) he₂ htag₂ (by rw [hperm₂]; rintro ⟨⟩) (by rw [hloc₂]; rfl)
        (Or.inr ⟨by rw [hloc₂]; rintro ⟨⟩, by change 0 + 1 * 1 ≤ 8; decide⟩)
    obtain ⟨map₃, hsim₃⟩ := step_mir_lm3_1_state_simulation hrel₂ hphase rfl
      (Or.inl ⟨_, rfl, hwt₂⟩) hsupply₂
    let s₃ := mkWitState b 3
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr1, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepObsRelLM3_1_of_anneal_step hsim₃ hs₃
    obtain ⟨⟨hsupply₃, _, _⟩, himm_s₃⟩ :=
      step_assign_binOp_offset_preserves_supply hrel₂ rfl rfl hsupply₂ hm₃
    have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
      intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
    have hwt₃ : WellTypedLM3_1StateStmt b s₃ m₃ map₃
        (mkStmt (.assign (local_ 5) (.rawPtr .not (derefLocal 4)))) :=
      .rawPtrDeref 5 4 rawPtrConstU8Decl rawPtrMutU8Decl .not .mut .not (.uint .u8) (.uint .u8) _
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩)))
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
    obtain ⟨map₄, hsim₄⟩ := step_mir_lm3_1_state_simulation hrel₃ hphase rfl
      (Or.inl ⟨_, rfl, hwt₃⟩) hsupply₃
    let s₄ := mkWitState b 4
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr1, .init ptr1] bor 2
    have hs₄ : stepMirFn b s₃ = .step s₄ := rfl
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepObsRelLM3_1_of_anneal_step hsim₄ hs₄
    exact ⟨s₁, s₂, s₃, s₄, m₁, m₂, m₃, m₄, map₄,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, hrel₄, rfl⟩
  · -- Part (2): D8, D10, D11 `StateRelLM3_1` preservation
    let bc := lm31NullPtrToPtrBody
    have hrel_c₀ : StateRelLM3_1 bc (mkFourLocalScalarAnnealPre bc ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bc u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bc u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU8Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hwt_c : WellTypedLM3_1StateStmt bc (mkFourLocalScalarAnnealPre bc ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bc u64Ty rawPtrConstU64Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 2) (.cast .ptrToPtr (.copy (local_ 1)) rawPtrConstU8Ty))) :=
      .castPtrToPtrScalar 2 1 rawPtrConstU8Ty rawPtrConstU8Decl rawPtrConstU64Decl
        .not .not .not (.uint .u64) (.uint .u8) ⟨0, 8⟩ _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
          mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩) rfl
    obtain ⟨_, hsim_c⟩ := step_mir_lm3_1_state_simulation hrel_c₀ (fun _ h => nomatch h) rfl
      (Or.inl ⟨_, rfl, hwt_c⟩) AllocIdSupplyReady.empty
    let s_c := mkWitState bc 1
      [.uninit, .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨0, 8⟩), .uninit] [] 1
    have hs_c : stepMirFn bc (mkFourLocalScalarAnnealPre bc ⟨0, 8⟩) = .step s_c := rfl
    obtain ⟨m_c, hm_c, hrel_c⟩ := stepObsRelLM3_1_of_anneal_step hsim_c hs_c
    have hcr_c := StateRelLM3_1.of_same_allocs hrel_c rfl
    let bmc := lm31MoveNullPtrToPtrBody
    have hrel_mc₀ : StateRelLM3_1 bmc (mkFourLocalScalarAnnealPre bmc ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bmc u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bmc u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU8Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hwt_mc : WellTypedLM3_1StateStmt bmc (mkFourLocalScalarAnnealPre bmc ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bmc u64Ty rawPtrConstU64Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 2) (.cast .ptrToPtr (.move (local_ 1)) rawPtrConstU8Ty))) :=
      .castPtrToPtrMoveScalar 2 1 rawPtrConstU8Ty rawPtrConstU8Decl rawPtrConstU64Decl
        .not .not .not (.uint .u64) (.uint .u8) ⟨0, 8⟩ _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
          mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩) rfl
    obtain ⟨_, hsim_mc⟩ := step_mir_lm3_1_state_simulation hrel_mc₀ (fun _ h => nomatch h) rfl
      (Or.inl ⟨_, rfl, hwt_mc⟩) AllocIdSupplyReady.empty
    let s_mc := mkWitState bmc 1
      [.uninit, .uninit, .init (.scalar ⟨0, 8⟩), .uninit] [] 1
    have hs_mc : stepMirFn bmc (mkFourLocalScalarAnnealPre bmc ⟨0, 8⟩) = .step s_mc := rfl
    obtain ⟨m_mc, hm_mc, hrel_mc⟩ := stepObsRelLM3_1_of_anneal_step hsim_mc hs_mc
    have hcr_mc := StateRelLM3_1.of_same_allocs hrel_mc rfl
    let bo := lm31NullOffsetZeroBody
    have hrel_o₀ : StateRelLM3_1 bo (mkFourLocalScalarAnnealPre bo ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bo u64Ty rawPtrConstU8Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bo u64Ty u64Decl rawPtrConstU8Decl rawPtrConstU8Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hwt_o : WellTypedLM3_1StateStmt bo (mkFourLocalScalarAnnealPre bo ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bo u64Ty rawPtrConstU8Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 2)
          (.binaryOp .offset (.copy (local_ 1)) (.constant (constUsizeLM31 0))))) :=
      .binOpOffsetScalarZero 2 1 MirAst.Operand.copy (.constant (constUsizeLM31 0))
        rawPtrConstU8Decl rawPtrConstU8Decl .not .not (.uint .u8) usizeTyLM31 ⟨0, 8⟩ _
        (Or.inl rfl) rfl rfl rfl rfl rfl (Or.inl rfl)
        (fun tf _ => constUsize_wellTyped bo tf 0 (by decide))
        (fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
          mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        rfl
        (fun l₁ sc_r _ _ _ ha => by
          change evalOperand l₁ (.constant (constUsizeLM31 0)) _ _ _ _ = _ at ha
          injection ha with hv _; injection hv with hsc; rw [← hsc])
        ⟨1, rfl⟩
    obtain ⟨_, hsim_o⟩ := step_mir_lm3_1_state_simulation hrel_o₀ (fun _ h => nomatch h) rfl
      (Or.inl ⟨_, rfl, hwt_o⟩) AllocIdSupplyReady.empty
    let s_o := mkWitState bo 1
      [.uninit, .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨0, 8⟩), .uninit] [] 1
    have hs_o : stepMirFn bo (mkFourLocalScalarAnnealPre bo ⟨0, 8⟩) = .step s_o := rfl
    obtain ⟨m_o, hm_o, hrel_o⟩ := stepObsRelLM3_1_of_anneal_step hsim_o hs_o
    have hcr_o := StateRelLM3_1.of_same_allocs hrel_o rfl
    let bmo := lm31MoveNullOffsetZeroBody
    have hrel_mo₀ : StateRelLM3_1 bmo (mkFourLocalScalarAnnealPre bmo ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bmo u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bmo u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hwt_mo : WellTypedLM3_1StateStmt bmo (mkFourLocalScalarAnnealPre bmo ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bmo u64Ty rawPtrConstU64Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 2)
          (.binaryOp .offset (.move (local_ 1)) (.constant (constUsizeLM31 0))))) :=
      .binOpOffsetScalarZero 2 1 MirAst.Operand.move (.constant (constUsizeLM31 0))
        rawPtrConstU64Decl rawPtrConstU64Decl .not .not (.uint .u64) usizeTyLM31 ⟨0, 8⟩ _
        (Or.inr rfl) rfl rfl rfl rfl rfl (Or.inl rfl)
        (fun tf _ => constUsize_wellTyped bmo tf 0 (by decide))
        (fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
          mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
        rfl
        (fun l₁ sc_r _ _ _ ha => by
          change evalOperand l₁ (.constant (constUsizeLM31 0)) _ _ _ _ = _ at ha
          injection ha with hv _; injection hv with hsc; rw [← hsc])
        ⟨8, rfl⟩
    obtain ⟨_, hsim_mo⟩ := step_mir_lm3_1_state_simulation hrel_mo₀ (fun _ h => nomatch h) rfl
      (Or.inl ⟨_, rfl, hwt_mo⟩) AllocIdSupplyReady.empty
    let s_mo := mkWitState bmo 1
      [.uninit, .uninit, .init (.scalar ⟨0, 8⟩), .uninit] [] 1
    have hs_mo : stepMirFn bmo (mkFourLocalScalarAnnealPre bmo ⟨0, 8⟩) = .step s_mo := rfl
    obtain ⟨m_mo, hm_mo, hrel_mo⟩ := stepObsRelLM3_1_of_anneal_step hsim_mo hs_mo
    have hcr_mo := StateRelLM3_1.of_same_allocs hrel_mo rfl
    let bpm := lm31PtrMetadataThinBody
    have hrel_pm₀ : StateRelLM3_1 bpm (mkFourLocalScalarAnnealPre bpm ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bpm u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bpm u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        unitDeclLM31 ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hwt_pm : WellTypedLM3_1StateStmt bpm (mkFourLocalScalarAnnealPre bpm ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bpm u64Ty rawPtrConstU64Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 3) (.unaryOp .ptrMetadata (.copy (local_ 1))))) :=
      .unaryOpPtrMetadata 3 1 MirAst.Operand.copy unitDeclLM31 rawPtrConstU64Decl
        .not (.uint .u64) _ (Or.inl rfl) rfl rfl rfl rfl rfl
        (fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 3,
          mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
    obtain ⟨_, hsim_pm⟩ := step_mir_lm3_1_state_simulation hrel_pm₀ (fun _ h => nomatch h) rfl
      (Or.inl ⟨_, rfl, hwt_pm⟩) AllocIdSupplyReady.empty
    let s_pm := mkWitState bpm 1
      [.uninit, .init (.scalar ⟨0, 8⟩), .uninit, .init .unit] [] 1
    have hs_pm : stepMirFn bpm (mkFourLocalScalarAnnealPre bpm ⟨0, 8⟩) = .step s_pm := rfl
    obtain ⟨m_pm, hm_pm, hrel_pm⟩ := stepObsRelLM3_1_of_anneal_step hsim_pm hs_pm
    have hcr_pm := StateRelLM3_1.of_same_allocs hrel_pm rfl
    exact ⟨s_c, s_mc, s_o, s_mo, s_pm, m_c, m_mc, m_o, m_mo, m_pm,
      hs_c, hm_c, hcr_c, hs_mc, hm_mc, hcr_mc, hs_o, hm_o, hcr_o, hs_mo, hm_mo, hcr_mo,
      hs_pm, hm_pm, hcr_pm, rfl⟩
  · -- Part (3): D9 2-step `lm31PlaceMentionDerefBody`
    let b := lm31PlaceMentionDerefBody
    let s₀ := mkFourLocalScalarAnnealPre b ⟨0, 8⟩
    let m₀ := mkFourLocalScalarMiriPre b u64Ty rawPtrConstU64Ty lm31Scalar0U64
    have hrel₀ : StateRelLM3_1 b s₀ m₀ [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have hwt₀ : WellTypedLM3_1StateStmt b s₀ m₀ []
        (mkStmt (.placeMention (derefLocal 1))) :=
      .placeMentionDeref 1 rawPtrConstU64Decl .not (.uint .u64) _
        rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf htf => mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1)
    obtain ⟨_, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨0, 8⟩), .uninit, .uninit] [] 1
    have hs₁ : stepMirFn b s₀ = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁_raw⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    have hrel₁ : StateRelLM3_1 b s₁ m₁ [] := StateRelLM3_1.of_same_allocs hrel₁_raw rfl
    obtain ⟨⟨hsupply₁, _, _⟩, himm₁_step⟩ :=
      step_preserves_supply_of_rvalue hrel₀ rfl rfl
        (evalStatement_placeMention_any_eq b.localDecls b.layouts (derefLocal 1) "" m₀)
        (rvaluePreservesAllImm_bind
          (annealEvalPlace_preserves b.localDecls b.layouts (translatePlace (derefLocal 1)))
          (fun _ => rvaluePreservesAllImm_pure ()))
        AllocIdSupplyReady.empty hm₁
    have himm₁_2 : ∀ tf₁, m₁.stack.frames = #[tf₁] → IsImmediateFrameLocal tf₁ 2 :=
      fun tf₁ htf₁ =>
        himm₁_step _ tf₁ rfl htf₁ 2 (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl 2)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ []
        (mkStmt (.placeMention (derefLocal 2))) :=
      .placeMentionDerefUninitUb 2 rawPtrConstU64Decl .not (.uint .u64) _
        rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) himm₁_2 rfl
    obtain ⟨_, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    have hs₂ : stepMirFn b s₁ = .fail .ub := rfl
    obtain ⟨msg, hm₂_err⟩ := (StepObsRelLM3_1.ub_iff hsim₂).mp hs₂
    exact ⟨s₁, m₁, (Miri.Interpreter.Step.step (annealStepHooks b.localDecls b.layouts) () m₁).1,
      msg, hs₁, hm₁, hrel₁, hs₂, Prod.ext rfl hm₂_err⟩
  · -- Part (4): D7 `&raw mut (*_2)` over a `.frozen` parent `_2 = &raw const _1`
    let b := lm31RawPtrDerefFrozenMutBody
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    have hrel₀ : StateRelLM3_1 b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) [] :=
      (mkFourLocalScalar_stateRel b u64Ty u64Decl u64Decl rawPtrConstU64Decl
        rawPtrMutU64Decl ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm₀ : ∀ tf, (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
        mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    have hwt₀ : WellTypedLM3_1StateStmt b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre b u64Ty u64Ty lm31Scalar42) []
        (mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .not (.uint .u64) rawPtrConstU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
    obtain ⟨map₁, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit]
      [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1] 2
    have hs₁ : stepMirFn b (mkFourLocalScalarAnnealPre b ⟨42, 8⟩) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm_s₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm₀
        AllocIdSupplyReady.empty (by change 1 + 1 < 2 ^ 32; decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm_s₁ _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ map₁
        (mkStmt (.assign (local_ 3) (.rawPtr .mut (derefLocal 2)))) :=
      .rawPtrDeref 3 2 rawPtrMutU64Decl rawPtrConstU64Decl .mut .not .mut (.uint .u64) (.uint .u64) _
        rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
    obtain ⟨map₂, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    let s₂ := mkWitState b 2 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0]
      [rawPtrBorrowEntry b.localDecls b.layouts .not 1 1] 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_1_of_anneal_step hsim₂ hs₂
    exact ⟨s₁, s₂, m₁, m₂, map₂, hs₁, hm₁, hs₂, hm₂, hrel₂, rfl⟩
  · -- Part (5): D7 null `&raw const (*_1)` and D11 `PtrMetadata(copy _2)` on uninitialized `_2`
    let bn := lm31RawPtrDerefNullBody
    have hrel_n₀ : StateRelLM3_1 bn (mkFourLocalScalarAnnealPre bn ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bn u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bn u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hwt_n : WellTypedLM3_1StateStmt bn (mkFourLocalScalarAnnealPre bn ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bn u64Ty rawPtrConstU64Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 2) (.rawPtr .not (derefLocal 1)))) :=
      .rawPtrDeref 2 1 rawPtrConstU64Decl rawPtrConstU64Decl .not .not .not (.uint .u64)
        (.uint .u64) _ rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
        (fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
          mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩)
    obtain ⟨_, hsim_n⟩ := step_mir_lm3_1_state_simulation hrel_n₀ (fun _ h => nomatch h) rfl
      (Or.inl ⟨_, rfl, hwt_n⟩) AllocIdSupplyReady.empty
    let s_n := mkWitState bn 1
      [.uninit, .init (.scalar ⟨0, 8⟩), .init (.scalar ⟨0, 8⟩), .uninit] [] 1
    have hs_n : stepMirFn bn (mkFourLocalScalarAnnealPre bn ⟨0, 8⟩) = .step s_n := rfl
    obtain ⟨m_n, hm_n, hrel_n⟩ := stepObsRelLM3_1_of_anneal_step hsim_n hs_n
    have hcr_n := StateRelLM3_1.of_same_allocs hrel_n rfl
    let bu := lm31PtrMetadataUninitBody
    have hrel_u₀ : StateRelLM3_1 bu (mkFourLocalScalarAnnealPre bu ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bu u64Ty rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bu u64Ty u64Decl rawPtrConstU64Decl rawPtrConstU64Decl
        unitDeclLM31 ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hwt_u : WellTypedLM3_1StateStmt bu (mkFourLocalScalarAnnealPre bu ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bu u64Ty rawPtrConstU64Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 3) (.unaryOp .ptrMetadata (.copy (local_ 2))))) :=
      .unaryOpPtrMetadataUb 3 2 MirAst.Operand.copy unitDeclLM31 rawPtrConstU64Decl
        .not (.uint .u64) _ (Or.inl rfl) rfl rfl rfl
        (fun tf htf => mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2) (Or.inr rfl)
    obtain ⟨_, hsim_u⟩ := step_mir_lm3_1_state_simulation hrel_u₀ (fun _ h => nomatch h) rfl
      (Or.inl ⟨_, rfl, hwt_u⟩) AllocIdSupplyReady.empty
    have hs_u : stepMirFn bu (mkFourLocalScalarAnnealPre bu ⟨0, 8⟩) = .fail .ub := rfl
    obtain ⟨msg, hm_u⟩ := (StepObsRelLM3_1.ub_iff hsim_u).mp hs_u
    exact ⟨s_n,  m_n,
      (Miri.Interpreter.Step.step (annealStepHooks bu.localDecls bu.layouts) ()
        (mkFourLocalScalarMiriPre bu u64Ty rawPtrConstU64Ty lm31Scalar0U64)).1,
      msg, hs_n, hm_n, hcr_n, rfl, hs_u, Prod.ext rfl hm_u⟩

/-- Multi-block `Runtime(PostCleanup)` MIR body exercising same-allocation raw-pointer
`Lt` comparison (`_5 = Lt(copy _3, copy _4)`) feeding `SwitchInt(copy _5)` in `bb0`:
```text
bb0: _2 = &raw mut _1;
     _3 = copy _2 as *mut u8;
     _4 = Offset(copy _3, const 1_usize);
     _5 = Lt(copy _3, copy _4);
     switchInt(copy _5) -> [1: bb1, otherwise: bb0];
bb1: return;
``` -/
def lm31RawPtrCmpBranchBody : CapturedMir where
  defPath := "lm_3_1_witness::raw_ptr_cmp_lt_branch"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [u64Decl, u64Decl, rawPtrMutU64Decl, rawPtrMutU8Decl,
    rawPtrMutU8Decl, boolDeclLM31]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1))),
        mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty)),
        mkStmt (.assign (local_ 4)
          (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1)))),
        mkStmt (.assign (local_ 5)
          (.binaryOp .lt (.copy (local_ 3)) (.copy (local_ 4))))],
      terminator := mkTerm (.switchInt (.copy (local_ 5))
        { branches := [(1, 1)], otherwise := 0 }),
      isCleanup := false },
    { statements := [],
      terminator := mkTerm .return_,
      isCleanup := false }]
  fnAbi := fnAbiU64
  layouts := emptyLayoutTable
  allocations := []

/-- **`wit_lm3_1_d12_cmp_branch_state_simulation_real_steps`**:
Composed multi-step witnesses for **`D12`** positive raw-pointer relational
comparison simulation regimes through unified `step_mir_lm3_1_state_simulation`:
1. **5-step same-allocation `Lt` -> `SwitchInt` (`lm31RawPtrCmpBranchBody`)**:
   `_2 = &raw mut _1` -> `_3 = copy _2 as *mut u8` ->
   `_4 = Offset(copy _3, 1_usize)` -> `_5 = Lt(copy _3, copy _4)`
   (`WellTypedLM3_1StateStmt.rawPtrCmpSameAlloc`, storing `true` in `_5` in
   lockstep) -> `SwitchInt(copy _5 : [1 -> bb1, otherwise -> bb0])`
   (`WellTypedLM3_1StateTerminator.switchInt`, emitting `MirObs.event 1` and
   jumping to `bb1` in lockstep with `StateRelLM3_1`).
2. **`WellTypedLM3_1StateStmt.rawPtrCmpCrossLocalEqNe` (degenerate self-comparison
   instance) and null-vs-pointer `.eq` (`WellTypedLM3_1StateStmt.rawPtrCmpNullPtr`)**:
   2-step lockstep executions (both machines' real-step equations exported) of
   `lm31RawPtrCmpPtrBody` (`_3 = Eq(copy _2, copy _2)` -> `true`; both operands are
   the SAME pointer into `_1`, so this exercises the `< 65536`-offset `Eq`/`Ne`
   constructor only on an identical-pointer instance, NOT on pointers into two
   distinct locals) and `lm31RawPtrCmpScalarPtrBody` (`_0 = Eq(copy _1, copy _2)` with
   null `_1` -> `false`) preserving `StateRelLM3_1`. -/
theorem wit_lm3_1_d12_cmp_branch_state_simulation_real_steps :
    -- (1) 5-step same-allocation `Lt` -> `SwitchInt` on `lm31RawPtrCmpBranchBody`
    (∃ (s₁ s₂ s₃ s₄ s₅ : MachineState) (m₁ m₂ m₃ m₄ m₅ : AnnealStepState)
      (map₄ : List AllocMapEntry),
      let b := lm31RawPtrCmpBranchBody
      let hooks := annealStepHooks b.localDecls b.layouts
      stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ ∧
      Miri.Interpreter.Step.step hooks () (mkSixLocalMiriPre b u64Ty) = (m₁, .ok true) ∧
      stepMirFn b s₁ = .step s₂ ∧
      Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
      stepMirFn b s₂ = .step s₃ ∧
      Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
      stepMirFn b s₃ = .step s₄ ∧
      Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
      get? s₄.frame.locals 5 = some (.init (.scalar ⟨1, 1⟩)) ∧
      stepMirFn b s₄ = .emitStep (.event 1) s₅ ∧
      Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
      s₅.frame.blockIdx = 1 ∧
      StateRelLM3_1 b s₅ m₅ map₄) ∧
    -- (2) `rawPtrCmpCrossLocalEqNe` and `rawPtrCmpNullPtr` via `step_mir_lm3_1_state_simulation`
    (∃ (s_eq₁ s_eq₂ s_np₁ s_np₂ : MachineState)
      (m_eq₁ m_eq₂ m_np₁ m_np₂ : AnnealStepState)
      (map_eq map_np : List AllocMapEntry),
      let beq := lm31RawPtrCmpPtrBody
      let bnp := lm31RawPtrCmpScalarPtrBody
      stepMirFn beq (mkFourLocalScalarAnnealPre beq ⟨42, 8⟩) = .step s_eq₁ ∧
      Miri.Interpreter.Step.step (annealStepHooks beq.localDecls beq.layouts) ()
        (mkFourLocalScalarMiriPre beq u64Ty u64Ty lm31Scalar42) = (m_eq₁, .ok true) ∧
      stepMirFn beq s_eq₁ = .step s_eq₂ ∧
      Miri.Interpreter.Step.step (annealStepHooks beq.localDecls beq.layouts) () m_eq₁ =
        (m_eq₂, .ok true) ∧
      get? s_eq₂.frame.locals 3 = some (.init (.scalar ⟨1, 1⟩)) ∧
      StateRelLM3_1 beq s_eq₂ m_eq₂ map_eq ∧
      stepMirFn bnp (mkFourLocalScalarAnnealPre bnp ⟨0, 8⟩) = .step s_np₁ ∧
      Miri.Interpreter.Step.step (annealStepHooks bnp.localDecls bnp.layouts) ()
        (mkFourLocalScalarMiriPre bnp boolTyLM31 rawPtrConstU64Ty lm31Scalar0U64) =
        (m_np₁, .ok true) ∧
      stepMirFn bnp s_np₁ = .step s_np₂ ∧
      Miri.Interpreter.Step.step (annealStepHooks bnp.localDecls bnp.layouts) () m_np₁ =
        (m_np₂, .ok true) ∧
      get? s_np₂.frame.locals 0 = some (.init (.scalar ⟨0, 1⟩)) ∧
      StateRelLM3_1 bnp s_np₂ m_np₂ map_np) := by
  have haid_pos : ∀ (aid : Miri.Memory.AllocId), 0 < aid.value.toNat := by
    intro ⟨v, hnz⟩
    exact Nat.pos_of_ne_zero (fun h => by
      have hv0 : v = 0 := UInt64.toNat_inj.mp h
      rw [hv0] at hnz; exact hnz rfl)
  have hbeq8 : (8 : Nat).beq 8 = true := rfl
  refine ⟨?_, ?_⟩
  · -- Part (1): 5-step same-allocation `Lt` -> `SwitchInt` on `lm31RawPtrCmpBranchBody`
    let b := lm31RawPtrCmpBranchBody
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let ptr1 := Value.ptr { allocId := 1, offsetBytes := 1 } 8
    have hrel₀ : StateRelLM3_1 b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) [] :=
      (mkSixLocal_stateRel b u64Ty u64Decl rawPtrMutU64Decl rawPtrMutU8Decl
        rawPtrMutU8Decl boolDeclLM31 rfl rfl).toLM3_1
    have hphase : ∀ p, b.phase ≠ .other p := fun _ h => nomatch h
    have himm01 : ∀ tf, (mkSixLocalMiriPre b u64Ty).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkSixLocal_all_immediate _ _ tf htf 2, mkSixLocal_all_immediate _ _ tf htf 1⟩
    let bor := [rawPtrBorrowEntry b.localDecls b.layouts .mut 1 1]
    have hwt₀ : WellTypedLM3_1StateStmt b (mkSixLocalAnnealPre b) (mkSixLocalMiriPre b u64Ty) []
        (mkStmt (.assign (local_ 2) (.rawPtr .mut (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .mut (.uint .u64) rawPtrMutU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
    obtain ⟨map₁, hsim₁⟩ := step_mir_lm3_1_state_simulation hrel₀ hphase rfl
      (Or.inl ⟨_, rfl, hwt₀⟩) AllocIdSupplyReady.empty
    let s₁ := mkWitState b 1
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit, .uninit, .uninit] bor 2
    have hs₁ : stepMirFn b (mkSixLocalAnnealPre b) = .step s₁ := rfl
    obtain ⟨m₁, hm₁, hrel₁⟩ := stepObsRelLM3_1_of_anneal_step hsim₁ hs₁
    obtain ⟨⟨hsupply₁, _, _⟩, himm_s₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm01
        AllocIdSupplyReady.empty (by change 1 + 1 < 2 ^ 32; decide) (fun h => nomatch h) hm₁
    have himm₁ : ∀ tf₁, m₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne => himm_s₁ _ tf₁ rfl htf₁ k hne (mkSixLocal_all_immediate _ _ _ rfl k)
    have hwt₁ : WellTypedLM3_1StateStmt b s₁ m₁ map₁
        (mkStmt (.assign (local_ 3) (.cast .ptrToPtr (.copy (local_ 2)) rawPtrMutU8Ty))) :=
      .castPtrToPtr 3 2 rawPtrMutU8Ty rawPtrMutU8Decl rawPtrMutU64Decl
        .mut .mut .mut (.uint .u64) (.uint .u8) _ rfl rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm₁ tf₁ htf₁ 3 (by decide), himm₁ tf₁ htf₁ 2 (by decide)⟩)
        (fun _ => slot_ptr_ne_scalar)
    obtain ⟨map₂, hsim₂⟩ := step_mir_lm3_1_state_simulation hrel₁ hphase rfl
      (Or.inl ⟨_, rfl, hwt₁⟩) hsupply₁
    let s₂ := mkWitState b 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .uninit, .uninit] bor 2
    have hs₂ : stepMirFn b s₁ = .step s₂ := rfl
    obtain ⟨m₂, hm₂, hrel₂⟩ := stepObsRelLM3_1_of_anneal_step hsim₂ hs₂
    obtain ⟨⟨hsupply₂, _, _⟩, himm_s₂⟩ :=
      step_assign_cast_ptrToPtr_preserves_supply hrel₁ rfl rfl hsupply₁ hm₂
    have himm₂ : ∀ tf₂, m₂.stack.frames = #[tf₂] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₂ k := by
      intro tf₂ htf₂ k hne; obtain ⟨tf₁, htf₁, _⟩ := id hrel₁
      exact himm_s₂ tf₁ tf₂ htf₁ htf₂ k (himm₁ tf₁ htf₁ k hne)
    obtain ⟨e₂, he₂, htag₂, hloc₂, hperm₂⟩ := allocMap_singleton_of_stateRel hrel₂ rfl
    have hwt₂ : WellTypedLM3_1StateStmt b s₂ m₂ map₂
        (mkStmt (.assign (local_ 4) (.binaryOp .offset (.copy (local_ 3)) (.constant (constUsizeLM31 1))))) :=
      .binOpOffsetStride 4 3 MirAst.Operand.copy (.constant (constUsizeLM31 1))
        rawPtrMutU8Decl rawPtrMutU8Decl u64Decl .mut .mut (.uint .u8) usizeTyLM31
        { allocId := 1, offsetBytes := 0 } 1 s₂.frame.locals e₂ _
        (Or.inl rfl) rfl rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u8, rfl⟩))) (Or.inl rfl)
        (fun tf₂ _ => .of_wt (constUsize_wellTyped b tf₂ 1 (by decide)))
        (fun tf₂ htf₂ => ⟨himm₂ tf₂ htf₂ 4 (by decide), himm₂ tf₂ htf₂ 3 (by decide)⟩)
        rfl rfl (by rintro ⟨⟩) he₂ htag₂ (by rw [hperm₂]; rintro ⟨⟩) (by rw [hloc₂]; rfl)
        (Or.inr ⟨by rw [hloc₂]; rintro ⟨⟩, by change 0 + 1 * 1 ≤ 8; decide⟩)
    obtain ⟨map₃, hsim₃⟩ := step_mir_lm3_1_state_simulation hrel₂ hphase rfl
      (Or.inl ⟨_, rfl, hwt₂⟩) hsupply₂
    let s₃ := mkWitState b 3
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr1, .uninit] bor 2
    have hs₃ : stepMirFn b s₂ = .step s₃ :=
      stepMirFn_binOp_offset_const_eq
        (rawPtrAllocMapEntry b.localDecls b.layouts .mut 1 1 lm31AllocId1)
        u64Decl hphase (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩)))
    obtain ⟨m₃, hm₃, hrel₃⟩ := stepObsRelLM3_1_of_anneal_step hsim₃ hs₃
    obtain ⟨⟨hsupply₃, _, _⟩, himm_s₃⟩ :=
      step_assign_binOp_offset_preserves_supply hrel₂ rfl rfl hsupply₂ hm₃
    have himm₃ : ∀ tf₃, m₃.stack.frames = #[tf₃] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₃ k := by
      intro tf₃ htf₃ k hne; obtain ⟨tf₂, htf₂, _⟩ := id hrel₂
      exact himm_s₃ tf₂ tf₃ htf₂ htf₃ k (himm₂ tf₂ htf₂ k hne)
    obtain ⟨e₃, he₃, htag₃, hloc₃, _⟩ := allocMap_singleton_of_stateRel hrel₃ rfl
    have hwt₃ : WellTypedLM3_1StateStmt b s₃ m₃ map₃
        (mkStmt (.assign (local_ 5) (.binaryOp .lt (.copy (local_ 3)) (.copy (local_ 4))))) :=
      .rawPtrCmpSameAlloc 5 3 4 MirAst.Operand.copy MirAst.Operand.copy .lt
        boolDeclLM31 rawPtrMutU8Decl rawPtrMutU8Decl .mut .mut (.uint .u8) (.uint .u8)
        { allocId := 1, offsetBytes := 0 } { allocId := 1, offsetBytes := 1 } e₃ e₃ _
        (Or.inl rfl) (Or.inl rfl) (Or.inr (Or.inr (Or.inl rfl))) rfl rfl rfl rfl rfl rfl
        (fun tf₃ htf₃ => ⟨himm₃ tf₃ htf₃ 5 (by decide),
          himm₃ tf₃ htf₃ 3 (by decide), himm₃ tf₃ htf₃ 4 (by decide)⟩)
        rfl rfl he₃ htag₃ he₃ htag₃ rfl (by rw [hloc₃]; decide)
        (fun h => absurd (congrFun h ⟨0, .nil⟩) (by nofun))
    obtain ⟨map₄, hsim₄⟩ := step_mir_lm3_1_state_simulation hrel₃ hphase rfl
      (Or.inl ⟨_, rfl, hwt₃⟩) hsupply₃
    let s₄ := mkWitState b 4
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr1,
       .init (.scalar ⟨1, 1⟩)] bor 2
    have hs₄ : stepMirFn b s₃ = .step s₄ :=
      stepMirFn_rawPtr_cmp_copy_eq (bRes := true) 68719542272 68719542273 hphase
        (hv₁ := Or.inr ⟨_, rfl, ptrAddress_singleton_eq _ _ _ _ _ _ _⟩)
        (hv₂ := ⟨_, rfl, ptrAddress_singleton_eq _ _ _ _ _ _ _⟩)
        (hcmp := by unfold evalScalarBinOp; dsimp only [hbeq8]; congr 3)
    obtain ⟨m₄, hm₄, hrel₄⟩ := stepObsRelLM3_1_of_anneal_step hsim₄ hs₄
    obtain ⟨⟨hsupply₄, _, _⟩, himm_s₄⟩ :=
      step_assign_binaryOp_preserves_supply hrel₃ rfl rfl hsupply₃ hm₄
    have himm₄_5 : ∀ tf₄, m₄.stack.frames = #[tf₄] → IsImmediateFrameLocal tf₄ 5 := by
      intro tf₄ htf₄; obtain ⟨tf₃, htf₃, _⟩ := id hrel₃
      exact himm_s₄ tf₃ tf₄ htf₃ htf₄ 5 (himm₃ tf₃ htf₃ 5 (by decide))
    have hwt₄ : WellTypedLM3_1StateTerminator b m₄ (b.basicBlocks[0]'(by decide)) :=
      .switchInt (.copy (local_ 5)) { branches := [(1, 1)], otherwise := 0 } boolTyLM31
        rfl (Or.inl rfl)
        (fun tf₄ htf₄ => .copyLocal 5 boolDeclLM31 rfl (by decide) (himm₄_5 tf₄ htf₄))
        (fun v blk hmem => by
          simp only [List.mem_singleton, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩
          exact ⟨by decide, fun _ => Or.inr rfl⟩)
    obtain ⟨map₅, hsim₅⟩ := step_mir_lm3_1_state_simulation hrel₄ hphase rfl
      (Or.inr ⟨rfl, rfl, hwt₄⟩) hsupply₄
    let s₅ := mkWitBlockState b 1 0
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init ptr0, .init ptr1,
       .init (.scalar ⟨1, 1⟩)] bor 2
    have hs₅ : stepMirFn b s₄ = .emitStep (.event 1) s₅ := rfl
    obtain ⟨m₅, hm₅, hrel₅⟩ := stepObsRelLM3_1_of_anneal_emitStep hsim₅ hs₅
    exact ⟨s₁, s₂, s₃, s₄, s₅, m₁, m₂, m₃, m₄, m₅, map₅,
      hs₁, hm₁, hs₂, hm₂, hs₃, hm₃, hs₄, hm₄, rfl, hs₅, hm₅, rfl, hrel₅⟩
  · -- Part (2): `rawPtrCmpCrossLocalEqNe` and `rawPtrCmpNullPtr`
    let ptr0 := Value.ptr { allocId := 1, offsetBytes := 0 } 8
    let beq := lm31RawPtrCmpPtrBody
    have hrel_eq₀ : StateRelLM3_1 beq (mkFourLocalScalarAnnealPre beq ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre beq u64Ty u64Ty lm31Scalar42) [] :=
      (mkFourLocalScalar_stateRel beq u64Ty u64Decl u64Decl rawPtrConstU64Decl boolDeclLM31
        ⟨42, 8⟩ lm31Scalar42 rfl rfl lm31_scalarRel42 rfl (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hphase_eq : ∀ p, beq.phase ≠ .other p := fun _ h => nomatch h
    have himm_eq₀ : ∀ tf, (mkFourLocalScalarMiriPre beq u64Ty u64Ty lm31Scalar42).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 1 :=
      fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
        mkFourLocalScalar_all_immediate _ _ _ _ tf htf 1⟩
    have hwt_eq₀ : WellTypedLM3_1StateStmt beq (mkFourLocalScalarAnnealPre beq ⟨42, 8⟩)
        (mkFourLocalScalarMiriPre beq u64Ty u64Ty lm31Scalar42) []
        (mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 1)))) :=
      .rawPtrAddrOf 2 1 .not (.uint .u64) rawPtrConstU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm_eq₀
    obtain ⟨map_eq₁, hsim_eq₁⟩ := step_mir_lm3_1_state_simulation hrel_eq₀ hphase_eq rfl
      (Or.inl ⟨_, rfl, hwt_eq₀⟩) AllocIdSupplyReady.empty
    let s_eq₁ := mkWitState beq 1 [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .uninit]
      [rawPtrBorrowEntry beq.localDecls beq.layouts .not 1 1] 2
    have hs_eq₁ : stepMirFn beq (mkFourLocalScalarAnnealPre beq ⟨42, 8⟩) = .step s_eq₁ := rfl
    obtain ⟨m_eq₁, hm_eq₁, hrel_eq₁⟩ := stepObsRelLM3_1_of_anneal_step hsim_eq₁ hs_eq₁
    obtain ⟨⟨hsupply_eq₁, _, _⟩, himm_seq₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel_eq₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm_eq₀
        AllocIdSupplyReady.empty (by change 1 + 1 < 2 ^ 32; decide) (fun h => nomatch h) hm_eq₁
    have himm_eq₁ : ∀ tf₁, m_eq₁.stack.frames = #[tf₁] → ∀ k, k ≠ 1 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm_seq₁ _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    obtain ⟨e_eq, he_eq, htag_eq, hloc_eq, _⟩ := allocMap_singleton_of_stateRel hrel_eq₁ rfl
    have hwt_eq₁ : WellTypedLM3_1StateStmt beq s_eq₁ m_eq₁ map_eq₁
        (mkStmt (.assign (local_ 3) (.binaryOp .eq (.copy (local_ 2)) (.copy (local_ 2))))) :=
      .rawPtrCmpCrossLocalEqNe 3 2 2 MirAst.Operand.copy MirAst.Operand.copy .eq
        boolDeclLM31 rawPtrConstU64Decl rawPtrConstU64Decl .not .not (.uint .u64) (.uint .u64)
        { allocId := 1, offsetBytes := 0 } { allocId := 1, offsetBytes := 0 } e_eq e_eq _
        (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm_eq₁ tf₁ htf₁ 3 (by decide),
          himm_eq₁ tf₁ htf₁ 2 (by decide), himm_eq₁ tf₁ htf₁ 2 (by decide)⟩)
        rfl rfl he_eq htag_eq (by rw [hloc_eq]; decide) (by decide)
        he_eq htag_eq (by rw [hloc_eq]; decide) (by decide)
        (fun h => absurd (congrFun h ⟨0, .nil⟩) (by nofun))
    obtain ⟨map_eq₂, hsim_eq₂⟩ := step_mir_lm3_1_state_simulation hrel_eq₁ hphase_eq rfl
      (Or.inl ⟨_, rfl, hwt_eq₁⟩) hsupply_eq₁
    let s_eq₂ := mkWitState beq 2
      [.uninit, .init (.scalar ⟨42, 8⟩), .init ptr0, .init (.scalar ⟨1, 1⟩)]
      [rawPtrBorrowEntry beq.localDecls beq.layouts .not 1 1] 2
    have hs_eq₂ : stepMirFn beq s_eq₁ = .step s_eq₂ :=
      stepMirFn_rawPtr_cmp_copy_eq (bRes := true) 68719542272 68719542272 hphase_eq
        (hv₁ := Or.inr ⟨_, rfl, ptrAddress_singleton_eq _ _ _ _ _ _ _⟩)
        (hv₂ := ⟨_, rfl, ptrAddress_singleton_eq _ _ _ _ _ _ _⟩)
        (hcmp := by unfold evalScalarBinOp; dsimp only [hbeq8]; congr 3)
    obtain ⟨m_eq₂, hm_eq₂, hrel_eq₂⟩ := stepObsRelLM3_1_of_anneal_step hsim_eq₂ hs_eq₂
    let bnp := lm31RawPtrCmpScalarPtrBody
    have hrel_np₀ : StateRelLM3_1 bnp (mkFourLocalScalarAnnealPre bnp ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bnp boolTyLM31 rawPtrConstU64Ty lm31Scalar0U64) [] :=
      (mkFourLocalScalar_stateRel bnp boolTyLM31 boolDeclLM31 rawPtrConstU64Decl
        rawPtrConstU64Decl u64Decl ⟨0, 8⟩ lm31Scalar0U64 rfl rfl lm31_scalarRel0U64 rfl
        (by rintro ⟨⟩) (by rintro ⟨⟩)).toLM3_1
    have hphase_np : ∀ p, bnp.phase ≠ .other p := fun _ h => nomatch h
    have himm_np₀ : ∀ tf,
        (mkFourLocalScalarMiriPre bnp boolTyLM31 rawPtrConstU64Ty lm31Scalar0U64).stack.frames = #[tf] →
        IsImmediateFrameLocal tf 2 ∧ IsImmediateFrameLocal tf 3 :=
      fun tf htf => ⟨mkFourLocalScalar_all_immediate _ _ _ _ tf htf 2,
        mkFourLocalScalar_all_immediate _ _ _ _ tf htf 3⟩
    have hwt_np₀ : WellTypedLM3_1StateStmt bnp (mkFourLocalScalarAnnealPre bnp ⟨0, 8⟩)
        (mkFourLocalScalarMiriPre bnp boolTyLM31 rawPtrConstU64Ty lm31Scalar0U64) []
        (mkStmt (.assign (local_ 2) (.rawPtr .not (local_ 3)))) :=
      .rawPtrAddrOf 2 3 .not (.uint .u64) rawPtrConstU64Decl u64Decl _
        rfl rfl rfl (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm_np₀
    obtain ⟨map_np₁, hsim_np₁⟩ := step_mir_lm3_1_state_simulation hrel_np₀ hphase_np rfl
      (Or.inl ⟨_, rfl, hwt_np₀⟩) AllocIdSupplyReady.empty
    let s_np₁ := mkWitState bnp 1 [.uninit, .init (.scalar ⟨0, 8⟩), .init ptr0, .uninit]
      [rawPtrBorrowEntry bnp.localDecls bnp.layouts .not 3 1] 2
    have hs_np₁ : stepMirFn bnp (mkFourLocalScalarAnnealPre bnp ⟨0, 8⟩) = .step s_np₁ := rfl
    obtain ⟨m_np₁, hm_np₁, hrel_np₁⟩ := stepObsRelLM3_1_of_anneal_step hsim_np₁ hs_np₁
    obtain ⟨⟨hsupply_np₁, _, _⟩, himm_snp₁⟩ :=
      step_rawPtr_addrOf_preserves_supply hrel_np₀ rfl rfl rfl rfl rfl
        (Or.inr (Or.inr (Or.inr ⟨.u64, rfl⟩))) (by decide) himm_np₀
        AllocIdSupplyReady.empty (by change 1 + 1 < 2 ^ 32; decide) (fun h => nomatch h) hm_np₁
    have himm_np₁ : ∀ tf₁, m_np₁.stack.frames = #[tf₁] → ∀ k, k ≠ 3 → IsImmediateFrameLocal tf₁ k :=
      fun tf₁ htf₁ k hne =>
        himm_snp₁ _ tf₁ rfl htf₁ k hne (mkFourLocalScalar_all_immediate _ _ _ _ _ rfl k)
    obtain ⟨e_np, he_np, htag_np, hloc_np, _⟩ := allocMap_singleton_of_stateRel hrel_np₁ rfl
    have hwt_np₁ : WellTypedLM3_1StateStmt bnp s_np₁ m_np₁ map_np₁
        (mkStmt (.assign (local_ 0) (.binaryOp .eq (.copy (local_ 1)) (.copy (local_ 2))))) :=
      .rawPtrCmpNullPtr 0 1 2 MirAst.Operand.copy MirAst.Operand.copy .eq
        boolDeclLM31 rawPtrConstU64Decl rawPtrConstU64Decl .not .not (.uint .u64) (.uint .u64)
        ⟨0, 8⟩ { allocId := 1, offsetBytes := 0 } e_np _
        (Or.inl rfl) (Or.inl rfl) (Or.inl rfl) rfl rfl rfl rfl rfl rfl
        (fun tf₁ htf₁ => ⟨himm_np₁ tf₁ htf₁ 0 (by decide),
          himm_np₁ tf₁ htf₁ 1 (by decide), himm_np₁ tf₁ htf₁ 2 (by decide)⟩)
        rfl rfl rfl he_np htag_np (by rw [hloc_np]; decide) (haid_pos e_np.allocId)
    obtain ⟨map_np₂, hsim_np₂⟩ := step_mir_lm3_1_state_simulation hrel_np₁ hphase_np rfl
      (Or.inl ⟨_, rfl, hwt_np₁⟩) hsupply_np₁
    let s_np₂ := mkWitState bnp 2
      [.init (.scalar ⟨0, 1⟩), .init (.scalar ⟨0, 8⟩), .init ptr0, .uninit]
      [rawPtrBorrowEntry bnp.localDecls bnp.layouts .not 3 1] 2
    have hs_np₂ : stepMirFn bnp s_np₁ = .step s_np₂ :=
      stepMirFn_rawPtr_cmp_copy_eq (bRes := false) 0 68719673344 hphase_np
        (hv₁ := Or.inl rfl)
        (hv₂ := ⟨_, rfl, ptrAddress_singleton_eq _ _ _ _ _ _ _⟩)
        (hcmp := by unfold evalScalarBinOp; dsimp only [hbeq8]; congr 3)
    obtain ⟨m_np₂, hm_np₂, hrel_np₂⟩ := stepObsRelLM3_1_of_anneal_step hsim_np₂ hs_np₂
    exact ⟨s_eq₁, s_eq₂, s_np₁, s_np₂, m_eq₁, m_eq₂, m_np₁, m_np₂, map_eq₂, map_np₂,
      hs_eq₁, hm_eq₁, hs_eq₂, hm_eq₂, rfl, hrel_eq₂,
      hs_np₁, hm_np₁, hs_np₂, hm_np₂, rfl, hrel_np₂⟩
end LeanMiriSpec.Correspondence.Witness
