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

Concrete, kernel-checked instances of the `LM-3.1` results:

1. **`wit_lm3_1_rawPtr_step`**: `step_rawPtr_addrOf_simulation` applies to
   `_2 = &raw mut _1` on the immediate scalar `_1 = 42_u64`; both machines take
   the step (`lean-miri` moving `_1` into a stack allocation), and the resulting
   states satisfy `StateRelLM3_1` under a non-empty `allocMap`.
2. **`wit_lm3_1_addrOf_write_read_deref`**: Anneal runs the address-of, write,
   and read-back body to `99_u64`; the address-of step is item 1; and the
   dereference stand-ins write and read `99_u64` on an allocation of the promoted
   shape (a hand-built machine, not the state that item 1 reaches).
3. **`wit_lm3_1_binOp_offset_inbounds_and_oob`**: `lean-miri`'s
   `ptrOffsetInbounds` accepts the one-past-end offset `8` and rejects `9` on an
   8-byte allocation, and the dereference stand-in rejects a read at offset `8`.
   It states no Anneal behavior.
4. **`wit_lm3_1_anneal_offset_deref_divergence`**: Anneal returns `42` from a
   body that dereferences a pointer one element past its local, while
   `lean-miri`'s access check rejects that access: Anneal's trusted semantics is
   more permissive than Miri here.
5. **`wit_lm3_1_use_after_storageDead_ub`**: Anneal reports undefined behavior
   for a dereference after `StorageDead`, and the dereference stand-in does so on
   a hand-built machine whose allocation was freed (its frame is not related to
   the Anneal state).
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

Item 3 exercises the `LM-3.1` dereference stand-ins on a hand-built machine
rather than on the state that item 2 reaches; the interpreter's own `Deref`
place path is not yet wired into `annealStepHooks`. -/
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
8-byte read at offset `8`. These are `lean-miri` facts only: Anneal's `Offset`
never reports undefined behavior, and its dereference of a stack pointer
ignores the offset (`wit_lm3_1_anneal_offset_deref_divergence`). -/
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
   (`evalProjection_deref_deadAlloc_ub`). The `lean-miri` frame here is
   `lm31AddrOfMiriFramePre` and is not related to the Anneal state; relating the
   two states requires stepping both machines through `StorageDead` of an
   address-taken local, which is not yet proved. -/
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

end LeanMiriSpec.Correspondence.Witness
