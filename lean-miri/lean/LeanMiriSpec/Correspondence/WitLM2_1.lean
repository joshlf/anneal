/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import LeanMiriSpec.Correspondence.SimLM2_1
import LeanMiriSpec.Correspondence.Witness

/-!
# Non-Vacuity Witnesses for the `LM-2.1` Correspondence

The `LM-2.1` theorems in `SimLM2_1` (`evalRvalue_aggregate_array_simulation`,
`evalRvalue_repeat_simulation`, `evalRvalue_len_array_simulation`,
`evalProjection_index_simulation`, `evalProjection_constantIndex_simulation`,
`step_assign_array_element_simulation`, and `step_stmt_lm2_1_simulation`) would
hold vacuously if their hypotheses (`StateRel`, `LiveAllocsNodup`,
`WellTypedArrayTy`, `ArraySliceRel`, `CanReserveAllocId`, and
`WellTypedLM2_1Stmt`) could not be satisfied simultaneously.

This module constructs concrete `Runtime(PostCleanup)` MIR states over a
multi-byte stride array `[u16; 3]` (`stride = 2` bytes) backed by a stack
allocation at non-zero virtual base address `0x1000` and non-zero relative byte
offset `relOffset = 4` (`mp.ptr.offset = 0x1004`), alongside `[u16; 0]` for
zero-length `Repeat`, and proves kernel-checked execution agreement for:

1. `Aggregate (.array u16Ty) [0x0102, 0x0304, 0x0506]` (`lm21_aggregate_array_steps`),
2. `Repeat (0x0708_u16) 3` and zero-count `Repeat (0x0708_u16) 0`
   (`lm21_repeat_array_steps`, `lm21_repeat_zero_steps`),
3. `Len(_1)` returning `3_usize` (`lm21_len_array_steps`) and uninitialized
   `Len(_1)` reporting undefined behavior in both machines (`lm21_len_uninit_ub`),
4. `ProjectionElem.index` in-bounds read (`_0 = copy _1[_2]` with `_2 = 1_usize`
   yielding `0x0304_u16`, `lm21_index_read_steps`) and in-bounds element write
   (`_1[_2] = const 0x090A_u16` updating `_1` to `[0x0102, 0x090A, 0x0506]`
   while preserving indices `0` and `2` and `StateRel`, `lm21_index_write_steps`),
5. `ProjectionElem.constantIndex` for both `fromEnd = false`
   (`offset = 2, minLength = 3` reading `0x0506_u16`,
   `lm21_constantIndex_fromStart_steps`) and `fromEnd = true`
   (`offset = 2, minLength = 3` reading `0x0304_u16` at `3 - 2 = 1`, and
   `offset = 1, minLength = 3` writing `0x0B0C_u16` at `3 - 1 = 2`,
   `lm21_constantIndex_fromEnd_read_steps`,
   `lm21_constantIndex_fromEnd_write_steps`),
6. Out-of-bounds `Index` read/write (`_2 = 3_usize` on `[u16; 3]`),
   uninitialized-index `Index` (`_2 = .uninit`), and out-of-bounds
   `ConstantIndex` (`minLength = 4` on `[u16; 3]`), each reporting undefined
   behavior in both machines (`lm21_index_oob_ub`, `lm21_index_write_oob_ub`,
   `lm21_index_uninit_ub`, `lm21_constantIndex_oob_ub`), plus direct
   instantiations of `evalProjection_index_simulation` and
   `evalProjection_constantIndex_simulation`.
-/

namespace LeanMiriSpec.Correspondence.Witness

open Trusted.Sequence
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.Layout
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open LeanMiriSpec.Correspondence

/-! ## 1. Types, Scalars, and `[u16; 3]` Allocation Fixture -/

def lm21U16Ty : Ty := { kind := .uint .u16, layoutIdx := 0 }
def lm21U16Decl : LocalDecl := { mutability := .mut, ty := lm21U16Ty, debugName := none }

def lm21UsizeTy : Ty := { kind := .uint .usize, layoutIdx := 0 }
def lm21UsizeDecl : LocalDecl := { mutability := .mut, ty := lm21UsizeTy, debugName := none }

def lm21U16Arr3Ty : Ty := { kind := .array (.uint .u16) 3, layoutIdx := 0 }
def lm21U16Arr3Decl : LocalDecl := { mutability := .mut, ty := lm21U16Arr3Ty, debugName := none }

def lm21U16Arr0Ty : Ty := { kind := .array (.uint .u16) 0, layoutIdx := 0 }
def lm21U16Arr0Decl : LocalDecl := { mutability := .mut, ty := lm21U16Arr0Ty, debugName := none }

def lm21ConstU16 (n : Nat) : ConstOperand := { ty := lm21U16Ty, val := .scalar (.int ⟨n, 2⟩) }

def lm21U16Layout : TypeLayout :=
  { size := { bytes := 2 }, align := { bytes := 2 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def lm21FnAbi : FnAbi :=
  { args := [], ret := { layout := lm21U16Layout, mode := .direct }, conv := .rust,
    canUnwind := false }

private theorem lm21_elemLayout_eq (c : Nat) :
    arrayElemLayoutOf emptyLayoutTable
      (translateTy { kind := .array (.uint .u16) c, layoutIdx := 0 } emptyLayoutTable)
      (translateTy { kind := .uint .u16, layoutIdx := 0 } emptyLayoutTable).layout.size =
    translateTy { kind := .uint .u16, layoutIdx := 0 } emptyLayoutTable := by
  have hty :
      (translateTy { kind := .array (.uint .u16) c, layoutIdx := 0 } emptyLayoutTable).ty = 1021 :=
    rfl
  unfold arrayElemLayoutOf
  rw [hty]
  have hge : (1021 : Nat) ≥ 1000 := by decide
  have hmod : (1021 - 1000) % 100 = 21 := by decide
  simp only [hge, ↓reduceIte, hmod, layoutOfEncodedTyId]

/-- `[u16; 3]` satisfies `WellTypedArrayTy` under `emptyLayoutTable` (`stride = 2`). -/
theorem lm21_wf_u16Arr3 : WellTypedArrayTy emptyLayoutTable lm21U16Arr3Ty (.uint .u16) 3 :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩)), rfl, rfl, rfl, rfl, rfl,
    lm21_elemLayout_eq 3,
    show 0 < 2 by decide, show 2 ≤ 16 by decide, show 3 * 2 < 2 ^ 32 by decide⟩

/-- `[u16; 0]` satisfies `WellTypedArrayTy` under `emptyLayoutTable`. -/
theorem lm21_wf_u16Arr0 : WellTypedArrayTy emptyLayoutTable lm21U16Arr0Ty (.uint .u16) 0 :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩)), rfl, rfl, rfl, rfl, rfl,
    lm21_elemLayout_eq 0,
    show 0 < 2 by decide, show 2 ≤ 16 by decide, show 0 * 2 < 2 ^ 32 by decide⟩

theorem lm21_isPrim_u16 : IsPrimScalarTy lm21U16Ty :=
  Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩))

/-- `AnnealMachine.empty.memory` can reserve a fresh `AllocId`. -/
theorem lm21_canReserve_empty : CanReserveAllocId AnnealMachine.empty.memory := by
  obtain ⟨mem', hres⟩ := Miri.Memory.MemoryState.reserve_of_highWater
    (Miri.Memory.MemoryState.empty : AnnealMemory) rfl (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
  exact ⟨mem', _, hres⟩

/-- `AnnealMachine.empty` has duplicate-free live `AllocId`s. -/
theorem lm21_nodup_empty : LiveAllocsNodup AnnealMachine.empty :=
  List.Pairwise.nil

/-- Concrete 12-byte stack allocation aligned to 2 bytes (`translateAlignBytes 2`),
holding little-endian `[0x0102_u16, 0x0304_u16, 0x0506_u16]` at relative byte
offsets `4, 6, 8` (`mp.ptr.offset = 0x1004` on `baseAddr = 0x1000`). -/
def lm21ArrAlloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[0, 0, 0, 0, 0x02, 0x01, 0x04, 0x03, 0x06, 0x05, 0, 0]
      (translateAlignBytes 2) .Mut)
    (by decide)).withExtra none

/-- Anneal element list `[0x0102_u16, 0x0304_u16, 0x0506_u16]`. -/
def lm21ArrElems : List Value :=
  [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩, .scalar ⟨0x0506, 2⟩]

/-- `lm21ArrAlloc` satisfies `ArraySliceRel` at `witnessRelOffset` (`4` bytes)
for `[0x0102_u16, 0x0304_u16, 0x0506_u16]`. -/
theorem lm21_arraySliceRel :
    ArraySliceRel (.uint .u16) 3 emptyLayoutTable lm21ArrElems witnessRelOffset lm21ArrAlloc := by
  refine ⟨rfl, by decide, by decide, by decide, by decide,
    show witnessRelOffset.bytes.toNat + 3 * 2 ≤ lm21ArrAlloc.byteSize.bytes.toNat by decide, ?_⟩
  intro idx val hget
  match idx with
  | 0 =>
    have hval : val = .scalar ⟨0x0102, 2⟩ := by simpa [lm21ArrElems, get?] using hget.symm
    subst hval
    refine ⟨⟨0x0102, 2⟩, extractExceptOk (translateScalarInt ⟨0x0102, 2⟩) (by decide), rfl, rfl,
      (fun h => nomatch h), (fun h => nomatch h),
      ⟨Or.inr (Or.inl rfl), by decide, by decide, by decide⟩, ?_⟩
    show lm21ArrAlloc.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange
        (Miri.ABI.Size.ofBytes (witnessRelOffset.bytes + UInt64.ofNat (0 * 2)))
        (Miri.ABI.Size.ofBytes 2)) false = _
    with_unfolding_all rfl
  | 1 =>
    have hval : val = .scalar ⟨0x0304, 2⟩ := by simpa [lm21ArrElems, get?] using hget.symm
    subst hval
    refine ⟨⟨0x0304, 2⟩, extractExceptOk (translateScalarInt ⟨0x0304, 2⟩) (by decide), rfl, rfl,
      (fun h => nomatch h), (fun h => nomatch h),
      ⟨Or.inr (Or.inl rfl), by decide, by decide, by decide⟩, ?_⟩
    show lm21ArrAlloc.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange
        (Miri.ABI.Size.ofBytes (witnessRelOffset.bytes + UInt64.ofNat (1 * 2)))
        (Miri.ABI.Size.ofBytes 2)) false = _
    with_unfolding_all rfl
  | 2 =>
    have hval : val = .scalar ⟨0x0506, 2⟩ := by simpa [lm21ArrElems, get?] using hget.symm
    subst hval
    refine ⟨⟨0x0506, 2⟩, extractExceptOk (translateScalarInt ⟨0x0506, 2⟩) (by decide), rfl, rfl,
      (fun h => nomatch h), (fun h => nomatch h),
      ⟨Or.inr (Or.inl rfl), by decide, by decide, by decide⟩, ?_⟩
    show lm21ArrAlloc.readScalar annealTargetDataLayout
      (Miri.Memory.allocRange
        (Miri.ABI.Size.ofBytes (witnessRelOffset.bytes + UInt64.ofNat (2 * 2)))
        (Miri.ABI.Size.ofBytes 2)) false = _
    with_unfolding_all rfl
  | _ + 3 =>
    simp [lm21ArrElems, get?] at hget

/-- `witnessMemPlace` (`0x1004` = `0x1000 + 4`) satisfies `MemPlaceRel` for
`[0x0102_u16, 0x0304_u16, 0x0506_u16]` in `witnessMachineOf lm21ArrAlloc`. -/
theorem lm21_memPlaceRel :
    MemPlaceRel (witnessMachineOf lm21ArrAlloc) lm21U16Arr3Ty emptyLayoutTable
      (some (.aggregate 0 lm21ArrElems)) witnessMemPlace := by
  refine MemPlaceRel.mk
    witnessAllocId
    witnessTag
    witnessBaseAddr
    witnessRelOffset
    { kind := .stack, allocation := lm21ArrAlloc }
    rfl
    rfl
    rfl
    (List.Mem.head _)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (show witnessMemPlace.ptr.offset.isAligned (translateAlignBytes 2) = .ok true by decide)
    (show witnessRelOffset.bytes.toNat + 6 ≤ lm21ArrAlloc.byteSize.bytes.toNat by decide)
    (fun h _ => nomatch h)
    (fun _ _ _ =>
      show lm21ArrAlloc.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange witnessRelOffset (Miri.ABI.Size.ofBytes 6)) =
        Except.ok (Except.ok ()) by decide)
    (fun _ h => nomatch h)
    ?_
  intro elemKind count elems hkind hval
  have hk : elemKind = .uint .u16 ∧ count = 3 := by
    simpa [lm21U16Arr3Ty] using hkind.symm
  rcases hk with ⟨rfl, rfl⟩
  have he : elems = lm21ArrElems := by
    injection hval with hv
    injection hv with _ hes
    exact hes.symm
  subst he
  exact ⟨rfl, rfl, rfl, lm21_arraySliceRel⟩

/-- `witnessMachineOf lm21ArrAlloc` has duplicate-free live `AllocId`s. -/
theorem lm21_nodup_arr : LiveAllocsNodup (witnessMachineOf lm21ArrAlloc) :=
  List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil

/-! ## 2. Concrete `Runtime(PostCleanup)` MIR Body & Related States -/

/-- `Runtime(PostCleanup)` MIR body exercising every `LM-2.1` statement shape:
- `stmt 0`: `_1 = [const 0x0102_u16, const 0x0304_u16, const 0x0506_u16]`
- `stmt 1`: `_1 = [const 0x0708_u16; 3]`
- `stmt 2`: `_3 = [const 0x0708_u16; 0]`
- `stmt 3`: `_2 = Len(_1)`
- `stmt 4`: `_0 = copy _1[_2]`
- `stmt 5`: `_1[_2] = const 0x090A_u16`
- `stmt 6`: `_0 = copy _1[2 of 3]` (`fromEnd = false`)
- `stmt 7`: `_0 = copy _1[-2 of 3]` (`fromEnd = true`, `3 - 2 = 1`)
- `stmt 8`: `_1[-1 of 3] = const 0x0B0C_u16` (`fromEnd = true`, `3 - 1 = 2`)
- `stmt 9`: `_0 = copy _1[0 of 4]` (`ConstantIndex` OOB `minLength = 4 > 3`) -/
def lm21Body : CapturedMir where
  defPath := "lm_2_1_witness::arrays"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm21U16Decl, lm21U16Arr3Decl, lm21UsizeDecl, lm21U16Arr0Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.constant (lm21ConstU16 0x0102), .constant (lm21ConstU16 0x0304),
           .constant (lm21ConstU16 0x0506)])),
        mkStmt (.assign (local_ 1) (.repeat (.constant (lm21ConstU16 0x0708)) 3)),
        mkStmt (.assign (local_ 3) (.repeat (.constant (lm21ConstU16 0x0708)) 0)),
        mkStmt (.assign (local_ 2) (.len (local_ 1))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.index 2]⟩))),
        mkStmt (.assign ⟨1, [.index 2]⟩ (.use (.constant (lm21ConstU16 0x090A)))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.constantIndex 2 3 false]⟩))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.constantIndex 2 3 true]⟩))),
        mkStmt (.assign ⟨1, [.constantIndex 1 3 true]⟩ (.use (.constant (lm21ConstU16 0x0B0C)))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.constantIndex 0 4 false]⟩)))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

theorem lm21_phase : ∀ p, lm21Body.phase ≠ .other p := by
  intro p h; cases h

/-- Initial Anneal state before statement `k` where all four locals are
uninitialized (`AnnealMachine.empty` side). -/
def lm21InitAnneal (k : Nat) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := k, locals := [.uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm21Body []).memory }

/-- Matching `lean-miri` root frame where all four locals are `.immediate .uninit`. -/
def lm21InitMiriFrame (k : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21Body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm21U16Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, k⟩ }

/-- Matching `lean-miri` state with `AnnealMachine.empty`. -/
def lm21InitMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm21InitMiriFrame k]⟩, machine := AnnealMachine.empty }

theorem lm21_init_stateRel (k : Nat) :
    StateRel lm21Body (lm21InitAnneal k) (lm21InitMiri k) := by
  refine StateRel.mk (lm21InitMiriFrame k) rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 => rintro ⟨⟩
      | _ + 4 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm21U16Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21InitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21InitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 2 =>
    have hd : decl = lm21UsizeDecl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21InitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = lm21U16Arr0Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21InitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21InitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm21Body, get?] at hdecl

private theorem lm21_initFrame_eq {k : Nat}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm21InitMiri k).stack.frames = #[tf]) : tf = lm21InitMiriFrame k := by
  simp only [lm21InitMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at h
  exact h.symm

/-- Anneal state before statement `k` once `_1` holds `[0x0102, 0x0304, 0x0506]`
and `_2` holds `idxSlot`. -/
def lm21ArrAnneal (k : Nat) (idxSlot : LocalSlot) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := k
        locals := [.uninit, .init (.aggregate 0 lm21ArrElems), idxSlot, .uninit] }
    memory := (initMachineState lm21Body []).memory }

/-- Matching `lean-miri` root frame where `_1` is indirect at `witnessMemPlace`
(`0x1004` in `lm21ArrAlloc`) and `_2` holds `.live (.immediate idxImm)`. -/
def lm21ArrMiriFrame (k : Nat) (idxImm : Miri.Interpreter.Immediate AnnealProv) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21Body
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm21U16Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.indirect witnessMemPlace), layout := none },
      { value := .live (.immediate idxImm), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, k⟩ }

/-- Matching `lean-miri` state backed by `witnessMachineOf lm21ArrAlloc`. -/
def lm21ArrMiri (k : Nat) (idxImm : Miri.Interpreter.Immediate AnnealProv) :
    AnnealStepState :=
  { stack := ⟨#[lm21ArrMiriFrame k idxImm]⟩, machine := witnessMachineOf lm21ArrAlloc }

/-- `StateRel` holds for `(lm21ArrAnneal k idxSlot, lm21ArrMiri k idxImm)` whenever
`idxSlot` and `idxImm` correspond for `lm21UsizeTy`. -/
theorem lm21_arr_stateRel (k : Nat) (idxSlot : LocalSlot)
    (idxImm : Miri.Interpreter.Immediate AnnealProv)
    (hidx : (idxSlot = .uninit ∧ idxImm = .uninit) ∨
      ∃ v, idxSlot = .init v ∧ ImmediateRel lm21UsizeTy emptyLayoutTable v idxImm) :
    StateRel lm21Body (lm21ArrAnneal k idxSlot) (lm21ArrMiri k idxImm) := by
  refine StateRel.mk (lm21ArrMiriFrame k idxImm) rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j mp_i mp_j lay_i lay_j hneq hi hj
      match i, j with
      | 0, _ => simp [lm21ArrMiriFrame] at hi
      | 2, _ => simp [lm21ArrMiriFrame] at hi
      | 3, _ => simp [lm21ArrMiriFrame] at hi
      | _ + 4, _ => simp [lm21ArrMiriFrame] at hi
      | 1, 0 => simp [lm21ArrMiriFrame] at hj
      | 1, 1 => exact absurd rfl hneq
      | 1, 2 => simp [lm21ArrMiriFrame] at hj
      | 1, 3 => simp [lm21ArrMiriFrame] at hj
      | 1, _ + 4 => simp [lm21ArrMiriFrame] at hj)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm21U16Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21ArrMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm21ArrElems) := by
      simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm21ArrMiriFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ witnessMemPlace none (fun _ h => nomatch h) nofun lm21_memPlaceRel
  | 2 =>
    have hd : decl = lm21UsizeDecl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = idxSlot := by simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate idxImm), layout := none } := by
      simpa [lm21ArrMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ none (fun _ h => nomatch h) hidx
  | 3 =>
    have hd : decl = lm21U16Arr0Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21ArrMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm21Body, get?] at hdecl

private theorem lm21_arrFrame_eq {k : Nat} {idxImm : Miri.Interpreter.Immediate AnnealProv}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm21ArrMiri k idxImm).stack.frames = #[tf]) : tf = lm21ArrMiriFrame k idxImm := by
  simp only [lm21ArrMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at h
  exact h.symm

def lm21Usize1 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 1
def lm21Usize3 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 3

theorem lm21_idxRel_1 :
    ImmediateRel lm21UsizeTy emptyLayoutTable (.scalar ⟨1, 8⟩)
      (.scalar (.fromScalarInt lm21Usize1)) :=
  .scalar ⟨1, 8⟩ lm21Usize1 ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    rfl (fun h => nomatch h) (fun h => nomatch h)

theorem lm21_idxRel_3 :
    ImmediateRel lm21UsizeTy emptyLayoutTable (.scalar ⟨3, 8⟩)
      (.scalar (.fromScalarInt lm21Usize3)) :=
  .scalar ⟨3, 8⟩ lm21Usize3 ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    rfl (fun h => nomatch h) (fun h => nomatch h)

private theorem lm21_constU16_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 65536) :
    WellTypedScalarOperand lm21Body tf (.constant (lm21ConstU16 n)) lm21U16Ty :=
  .constScalar (lm21ConstU16 n) ⟨n, 2⟩ rfl lm21_isPrim_u16 (Or.inr (Or.inl rfl))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h)

/-! ## 3. `Aggregate` & `Repeat` Construction Witnesses (`stmt 0, 1, 2`) -/

/-- `stmt 0`: `_1 = [const 0x0102_u16, const 0x0304_u16, const 0x0506_u16]`
steps both Anneal and `lean-miri` normally via `step_stmt_lm2_1_simulation`,
initializing `_1` to `lm21ArrElems` and preserving `StateRel`. -/
theorem lm21_aggregate_array_steps :
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 1
            locals := [.uninit, .init (.aggregate 0 lm21ArrElems), .uninit, .uninit] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body (lm21InitAnneal 0) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 0) =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s'
  have hstep : stepMirFn lm21Body (lm21InitAnneal 0) = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation (lm21_init_stateRel 0) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl ?_ ?_ lm21_isPrim_u16 lm21_canReserve_empty
      · intro mls hmls mp hv
        simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv
      · intro op hop
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl
        · exact lm21_constU16_wt _ 0x0102 (by decide)
        · exact lm21_constU16_wt _ 0x0304 (by decide)
        · exact lm21_constU16_wt _ 0x0506 (by decide))
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 0) = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 1`: `_1 = [const 0x0708_u16; 3]` steps both Anneal and `lean-miri`
normally via `step_stmt_lm2_1_simulation`, initializing `_1` to three copies of
`0x0708_u16` and preserving `StateRel`. -/
theorem lm21_repeat_array_steps :
    let repElems : List Value := [.scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩]
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 2
            locals := [.uninit, .init (.aggregate 0 repElems), .uninit, .uninit] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body (lm21InitAnneal 1) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 1) =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro repElems s'
  have hstep : stepMirFn lm21Body (lm21InitAnneal 1) = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation (lm21_init_stateRel 1) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .repeatArray 1 lm21U16Arr3Decl (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 ?_ (lm21_constU16_wt _ 0x0708 (by decide))
        lm21_isPrim_u16 lm21_canReserve_empty
      intro mls hmls mp hv
      simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 1) = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 2`: `_3 = [const 0x0708_u16; 0]` (zero-length `Repeat`) steps both
Anneal and `lean-miri` normally and preserves `StateRel`. -/
theorem lm21_repeat_zero_steps :
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 3
            locals := [.uninit, .uninit, .uninit, .init (.aggregate 0 [])] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body (lm21InitAnneal 2) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 2) =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s'
  have hstep : stepMirFn lm21Body (lm21InitAnneal 2) = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation (lm21_init_stateRel 2) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .repeatArray 3 lm21U16Arr0Decl (.uint .u16) 0 _ _
        rfl lm21_wf_u16Arr0 ?_ (lm21_constU16_wt _ 0x0708 (by decide))
        lm21_isPrim_u16 lm21_canReserve_empty
      intro mls hmls mp hv
      simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 2) = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-! ## 4. `Rvalue.Len` Witness (`stmt 3`, Initialized & Uninitialized UB) -/

/-- `stmt 3`: `_2 = Len(_1)` on initialized `[u16; 3]` writes `3_usize` (`⟨3, 8⟩`)
into `_2` and steps `lean-miri` (`UnaryOp.PtrMetadata`) in `StateRel`. -/
theorem lm21_len_array_steps :
    let s' := lm21ArrAnneal 4 (.init (.scalar ⟨3, 8⟩))
    stepMirFn lm21Body (lm21ArrAnneal 3 .uninit) = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21ArrMiri 3 .uninit) =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s'
  have hstep : stepMirFn lm21Body (lm21ArrAnneal 3 .uninit) = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 3 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .lenArray 2 1 lm21UsizeDecl lm21U16Arr3Decl (.uint .u16) 3 _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩))
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21ArrMiri 3 .uninit) = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 3`: `_2 = Len(_1)` when `_1` is uninitialized reports undefined behavior
in both Anneal and `lean-miri`. -/
theorem lm21_len_uninit_ub :
    stepMirFn lm21Body (lm21InitAnneal 3) = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 3) =
          (m', .error (.undefinedBehavior msg)) := by
  have hstep : stepMirFn lm21Body (lm21InitAnneal 3) = .fail .ub := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation (lm21_init_stateRel 3) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .lenArray 2 1 lm21UsizeDecl lm21U16Arr3Decl (.uint .u16) 3 _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ (Or.inr (Or.inl ⟨rfl, Or.inl (by decide)⟩))
      intro mls hmls mp hv
      simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () (lm21InitMiri 3) = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-! ## 5. Direct `evalProjection_index_simulation` & `evalProjection_constantIndex_simulation` Witnesses -/

/-- Direct non-vacuity witness for `evalProjection_index_simulation` on `[u16; 3]`
at `_2 = 1_usize`: `annealProjectList` advances `0x1004` by `1 * 2 = 2` bytes to
`0x1006`, and `annealReadImmediate` reads `0x0304_u16`. -/
theorem lm21_evalProjection_index_witness :
    ∃ elemVal sc msc,
      get? lm21ArrElems 1 = some elemVal ∧
      elemVal = .scalar ⟨0x0304, 2⟩ ∧
      sc = ⟨0x0304, 2⟩ ∧
      annealProjectList
        (annealProjectionCx (lm21ArrMiriFrame 4 (.scalar (.fromScalarInt lm21Usize1)))
          lm21Body.layouts)
        ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
        [.Index 2] =
        .ok ⟨.indirect
              { witnessMemPlace with
                ptr := { witnessMemPlace.ptr with offset := Miri.ABI.Size.ofBytes 0x1006 }
                metadata := .none },
            translateTy lm21U16Ty lm21Body.layouts⟩ ∧
      ImmediateRel lm21U16Ty lm21Body.layouts (.scalar sc) (.scalar (.fromScalarInt msc)) := by
  have hstate := lm21_arr_stateRel 4 (.init (.scalar ⟨1, 8⟩))
    (.scalar (.fromScalarInt lm21Usize1))
    (Or.inr ⟨.scalar ⟨1, 8⟩, rfl, lm21_idxRel_1⟩)
  have ⟨_, hin, _⟩ := evalProjection_index_simulation hstate rfl lm21_nodup_arr
    (arrLocal := 1) (idxLocal := 2) rfl lm21_wf_u16Arr3 lm21_memPlaceRel rfl rfl
    (fun mls hmls mp hv => by simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  obtain ⟨elemVal, sc, msc, hget, rfl, _, hpl, himm, _⟩ :=
    hin ⟨1, 8⟩ rfl (by decide)
  have hsc : sc = ⟨0x0304, 2⟩ := by
    have h : some (Value.scalar sc) = some (Value.scalar ⟨0x0304, 2⟩) := hget.symm
    injection h with hv; injection hv
  subst hsc
  exact ⟨.scalar ⟨0x0304, 2⟩, ⟨0x0304, 2⟩, msc, hget, rfl, rfl, hpl, himm⟩

/-- Direct non-vacuity witness for `evalProjection_constantIndex_simulation` on
`[u16; 3]` with `fromEnd = true`, `offset = 2`, `minLength = 3` (`3 - 2 = 1`):
`annealProjectList` advances `0x1004` to `0x1006` and reads `0x0304_u16`. -/
theorem lm21_evalProjection_constantIndex_witness :
    ∃ msc,
      annealProjectList
        (annealProjectionCx (lm21ArrMiriFrame 7 .uninit) lm21Body.layouts)
        ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
        [.ConstantIndex 2 3 true] =
        .ok ⟨.indirect
              { witnessMemPlace with
                ptr := { witnessMemPlace.ptr with offset := Miri.ABI.Size.ofBytes 0x1006 }
                metadata := .none },
            translateTy lm21U16Ty lm21Body.layouts⟩ ∧
      ImmediateRel lm21U16Ty lm21Body.layouts (.scalar ⟨0x0304, 2⟩)
        (.scalar (.fromScalarInt msc)) := by
  have hstate := lm21_arr_stateRel 7 .uninit .uninit (Or.inl ⟨rfl, rfl⟩)
  have ⟨hin, _⟩ := evalProjection_constantIndex_simulation hstate rfl lm21_nodup_arr
    (arrLocal := 1) rfl lm21_wf_u16Arr3 lm21_memPlaceRel
    2 3 true (by decide) (by decide) ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩
  obtain ⟨_, sc, msc, hget, rfl, _, hpl, himm, _⟩ := hin (by decide)
  have hsc : sc = ⟨0x0304, 2⟩ := by
    have h : some (Value.scalar sc) = some (Value.scalar ⟨0x0304, 2⟩) := hget.symm
    injection h with hv; injection hv
  subst hsc
  exact ⟨msc, hpl, himm⟩

/-! ## 6. Statement-Level `Index` & `ConstantIndex` Read/Write & UB Witnesses (`stmt 4..9`) -/

/-- `stmt 4`: `_0 = copy _1[_2]` with `_2 = 1_usize` reads `0x0304_u16` into `_0`
and steps both machines in `StateRel`. -/
theorem lm21_index_read_steps :
    let s₀ := lm21ArrAnneal 4 (.init (.scalar ⟨1, 8⟩))
    let m₀ := lm21ArrMiri 4 (.scalar (.fromScalarInt lm21Usize1))
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 5
            locals :=
              [.init (.scalar ⟨0x0304, 2⟩), .init (.aggregate 0 lm21ArrElems),
               .init (.scalar ⟨1, 8⟩), .uninit] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s₀ m₀ s'
  have hstep : stepMirFn lm21Body s₀ = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 4 (.init (.scalar ⟨1, 8⟩)) (.scalar (.fromScalarInt lm21Usize1))
      (Or.inr ⟨.scalar ⟨1, 8⟩, rfl, lm21_idxRel_1⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3 (.index 2) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      · intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv
      · refine .index 2 lm21UsizeDecl rfl rfl ?_
        intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 5`: `_1[_2] = const 0x090A_u16` with `_2 = 1_usize` updates element `1`
to `0x090A_u16` while leaving elements `0` (`0x0102_u16`) and `2` (`0x0506_u16`)
intact, and steps `lean-miri`'s backing byte slice in `StateRel`. -/
theorem lm21_index_write_steps :
    let s₀ := lm21ArrAnneal 5 (.init (.scalar ⟨1, 8⟩))
    let m₀ := lm21ArrMiri 5 (.scalar (.fromScalarInt lm21Usize1))
    let updatedElems : List Value :=
      [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x090A, 2⟩, .scalar ⟨0x0506, 2⟩]
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 6
            locals :=
              [.uninit, .init (.aggregate 0 updatedElems),
               .init (.scalar ⟨1, 8⟩), .uninit] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s₀ m₀ updatedElems s'
  have hstep : stepMirFn lm21Body s₀ = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 5 (.init (.scalar ⟨1, 8⟩)) (.scalar (.fromScalarInt lm21Usize1))
      (Or.inr ⟨.scalar ⟨1, 8⟩, rfl, lm21_idxRel_1⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3 (.index 2)
        (.constant (lm21ConstU16 0x090A)) _
        rfl lm21_wf_u16Arr3 lm21_isPrim_u16 ?_
        (lm21_constU16_wt _ 0x090A (by decide))
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      refine .index 2 lm21UsizeDecl rfl rfl ?_
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 6`: `_0 = copy _1[2 of 3]` (`ConstantIndex`, `fromEnd = false`) reads
`0x0506_u16` at index `2` and steps both machines in `StateRel`. -/
theorem lm21_constantIndex_fromStart_steps :
    let s₀ := lm21ArrAnneal 6 .uninit
    let m₀ := lm21ArrMiri 6 .uninit
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 7
            locals :=
              [.init (.scalar ⟨0x0506, 2⟩), .init (.aggregate 0 lm21ArrElems),
               .uninit, .uninit] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s₀ m₀ s'
  have hstep : stepMirFn lm21Body s₀ = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 6 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.constantIndex 2 3 false) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_
        (.constantIndex 2 3 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 7`: `_0 = copy _1[-2 of 3]` (`ConstantIndex`, `fromEnd = true`) reads
`0x0304_u16` at index `3 - 2 = 1` and steps both machines in `StateRel`. -/
theorem lm21_constantIndex_fromEnd_read_steps :
    let s₀ := lm21ArrAnneal 7 .uninit
    let m₀ := lm21ArrMiri 7 .uninit
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 8
            locals :=
              [.init (.scalar ⟨0x0304, 2⟩), .init (.aggregate 0 lm21ArrElems),
               .uninit, .uninit] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s₀ m₀ s'
  have hstep : stepMirFn lm21Body s₀ = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 7 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.constantIndex 2 3 true) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_
        (.constantIndex 2 3 true (by decide) (by decide)
          ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 8`: `_1[-1 of 3] = const 0x0B0C_u16` (`ConstantIndex`, `fromEnd = true`)
writes `0x0B0C_u16` into index `3 - 1 = 2`, updating `_1` to
`[0x0102_u16, 0x0304_u16, 0x0B0C_u16]` while preserving indices `0` and `1` and
`StateRel`. -/
theorem lm21_constantIndex_fromEnd_write_steps :
    let s₀ := lm21ArrAnneal 8 .uninit
    let m₀ := lm21ArrMiri 8 .uninit
    let updatedElems : List Value :=
      [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩, .scalar ⟨0x0B0C, 2⟩]
    let s' : MachineState :=
      { frame :=
          { blockIdx := 0
            stmtIdx := 9
            locals := [.uninit, .init (.aggregate 0 updatedElems), .uninit, .uninit] }
        memory := (initMachineState lm21Body []).memory }
    stepMirFn lm21Body s₀ = .step s' ∧
      ∃ m', Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .ok true) ∧
        StateRel lm21Body s' m' := by
  intro s₀ m₀ updatedElems s'
  have hstep : stepMirFn lm21Body s₀ = .step s' := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 8 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      exact .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3
        (.constantIndex 1 3 true) (.constant (lm21ConstU16 0x0B0C)) _
        rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.constantIndex 1 3 true (by decide) (by decide)
          ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
        (lm21_constU16_wt _ 0x0B0C (by decide))
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩))))
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 4`: out-of-bounds `Index` read (`_2 = 3_usize` on `[u16; 3]`) reports
undefined behavior in both Anneal and `lean-miri`. -/
theorem lm21_index_oob_ub :
    let s₀ := lm21ArrAnneal 4 (.init (.scalar ⟨3, 8⟩))
    let m₀ := lm21ArrMiri 4 (.scalar (.fromScalarInt lm21Usize3))
    stepMirFn lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) := by
  intro s₀ m₀
  have hstep : stepMirFn lm21Body s₀ = .fail .ub := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 4 (.init (.scalar ⟨3, 8⟩)) (.scalar (.fromScalarInt lm21Usize3))
      (Or.inr ⟨.scalar ⟨3, 8⟩, rfl, lm21_idxRel_3⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3 (.index 2) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      · intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv
      · refine .index 2 lm21UsizeDecl rfl rfl ?_
        intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-- `stmt 5`: out-of-bounds `Index` write (`_2 = 3_usize` on `[u16; 3]`) reports
undefined behavior in both Anneal and `lean-miri`. -/
theorem lm21_index_write_oob_ub :
    let s₀ := lm21ArrAnneal 5 (.init (.scalar ⟨3, 8⟩))
    let m₀ := lm21ArrMiri 5 (.scalar (.fromScalarInt lm21Usize3))
    stepMirFn lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) := by
  intro s₀ m₀
  have hstep : stepMirFn lm21Body s₀ = .fail .ub := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 5 (.init (.scalar ⟨3, 8⟩)) (.scalar (.fromScalarInt lm21Usize3))
      (Or.inr ⟨.scalar ⟨3, 8⟩, rfl, lm21_idxRel_3⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3 (.index 2)
        (.constant (lm21ConstU16 0x090A)) _
        rfl lm21_wf_u16Arr3 lm21_isPrim_u16 ?_
        (lm21_constU16_wt _ 0x090A (by decide))
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      refine .index 2 lm21UsizeDecl rfl rfl ?_
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-- `stmt 4`: reading `_1[_2]` when `_2` is uninitialized reports undefined
behavior in both Anneal and `lean-miri`. -/
theorem lm21_index_uninit_ub :
    let s₀ := lm21ArrAnneal 4 .uninit
    let m₀ := lm21ArrMiri 4 .uninit
    stepMirFn lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) := by
  intro s₀ m₀
  have hstep : stepMirFn lm21Body s₀ = .fail .ub := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 4 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3 (.index 2) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      · intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv
      · refine .index 2 lm21UsizeDecl rfl rfl ?_
        intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-- `stmt 9`: out-of-bounds `ConstantIndex` (`offset = 0, minLength = 4` on
`[u16; 3]`, where `count = 3 < minLength = 4`) reports undefined behavior in both
Anneal and `lean-miri`. -/
theorem lm21_constantIndex_oob_ub :
    let s₀ := lm21ArrAnneal 9 .uninit
    let m₀ := lm21ArrMiri 9 .uninit
    stepMirFn lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) := by
  intro s₀ m₀
  have hstep : stepMirFn lm21Body s₀ = .fail .ub := rfl
  refine ⟨hstep, ?_⟩
  have hsim := step_stmt_lm2_1_simulation
    (lm21_arr_stateRel 9 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.constantIndex 0 4 false) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_
        (.constantIndex 0 4 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

end LeanMiriSpec.Correspondence.Witness
