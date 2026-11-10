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
`step_assign_array_element_simulation`, `step_stmt_lm2_1_array_simulation`, and
`step_stmt_lm2_1_simulation`) would hold vacuously if their hypotheses
(`StateRel`, `LiveAllocsNodup`, `WellTypedArrayTy`, `ArraySliceRel`,
`CanReserveAllocId`, and `WellTypedLM2_1ArrayStmt`) could not be satisfied
simultaneously.

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
   `evalProjection_constantIndex_simulation`, and
7. A chained five-statement run (`lm21_chain_steps`): array construction, two
   `ConstantIndex` writes into the same allocation, a `ConstantIndex` read, and
   `Len`, where every step after the first applies
   `step_stmt_lm2_1_array_simulation` to the previous step's `lean-miri`
   post-state using only the `StateRel`, `LiveAllocsNodup`, and immediacy facts
   that the earlier steps re-established.
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
    show 0 < 2 by decide, show 2 ≤ 16 by decide, show 3 * 2 < 2 ^ 32 by decide, rfl⟩

/-- `[u16; 0]` satisfies `WellTypedArrayTy` under `emptyLayoutTable`. -/
theorem lm21_wf_u16Arr0 : WellTypedArrayTy emptyLayoutTable lm21U16Arr0Ty (.uint .u16) 0 :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩)), rfl, rfl, rfl, rfl, rfl,
    lm21_elemLayout_eq 0,
    show 0 < 2 by decide, show 2 ≤ 16 by decide, show 0 * 2 < 2 ^ 32 by decide, rfl⟩

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
- `stmt 9`: `_0 = copy _1[0 of 4]` (`ConstantIndex` OOB `minLength = 4 > 3`)
- `stmt 10..14`: the chained run `_1 = [0x0102, 0x0304, 0x0506]`,
  `_1[-1 of 3] = const 0x0B0C_u16`, `_1[0 of 3] = const 0x0D0E_u16`,
  `_0 = copy _1[2 of 3]`, `_2 = Len(_1)` (`lm21_chain_steps`) -/
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
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.constantIndex 0 4 false]⟩))),
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.constant (lm21ConstU16 0x0102), .constant (lm21ConstU16 0x0304),
           .constant (lm21ConstU16 0x0506)])),
        mkStmt (.assign ⟨1, [.constantIndex 1 3 true]⟩ (.use (.constant (lm21ConstU16 0x0B0C)))),
        mkStmt (.assign ⟨1, [.constantIndex 0 3 false]⟩ (.use (.constant (lm21ConstU16 0x0D0E)))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.constantIndex 2 3 false]⟩))),
        mkStmt (.assign (local_ 2) (.len (local_ 1)))],
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
    WellTypedLM2_1ScalarOperand lm21Body tf (.constant (lm21ConstU16 n)) lm21U16Ty :=
  .ofScalar (.constScalar (lm21ConstU16 n) ⟨n, 2⟩ rfl lm21_isPrim_u16 (Or.inr (Or.inl rfl))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h))

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
  have hsim := step_stmt_lm2_1_array_simulation (lm21_init_stateRel 0) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inl ⟨?_, lm21_canReserve_empty⟩)) ?_ lm21_isPrim_u16
      · intro mls hmls mp hv
        simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv
      · intro op hop
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl
        · exact lm21_constU16_wt _ 0x0102 (by decide)
        · exact lm21_constU16_wt _ 0x0304 (by decide)
        · exact lm21_constU16_wt _ 0x0506 (by decide))
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation (lm21_init_stateRel 1) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .repeatArray 1 lm21U16Arr3Decl (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 (Or.inr (Or.inl ⟨?_, lm21_canReserve_empty⟩))
        (lm21_constU16_wt _ 0x0708 (by decide)) lm21_isPrim_u16
      intro mls hmls mp hv
      simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation (lm21_init_stateRel 2) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .repeatArray 3 lm21U16Arr0Decl (.uint .u16) 0 _ _
        rfl lm21_wf_u16Arr0 (Or.inr (Or.inl ⟨?_, lm21_canReserve_empty⟩))
        (lm21_constU16_wt _ 0x0708 (by decide)) lm21_isPrim_u16
      intro mls hmls mp hv
      simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
    (lm21_arr_stateRel 3 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .lenArray 2 1 lm21UsizeDecl lm21U16Arr3Decl (.uint .u16) 3 _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩))
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation (lm21_init_stateRel 3) lm21_nodup_empty lm21_phase
    rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .lenArray 2 1 lm21UsizeDecl lm21U16Arr3Decl (.uint .u16) 3 _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ (Or.inr (Or.inl ⟨rfl, Or.inl (by decide)⟩))
      intro mls hmls mp hv
      simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
          lm21Body.layouts (witnessMachineOf lm21ArrAlloc))
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
    (idxLocal := 2) lm21_wf_u16Arr3 lm21_memPlaceRel rfl rfl
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
        (annealProjectionCx (lm21ArrMiriFrame 7 .uninit) lm21Body.layouts
          (witnessMachineOf lm21ArrAlloc))
        ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
        [.ConstantIndex 2 3 true] =
        .ok ⟨.indirect
              { witnessMemPlace with
                ptr := { witnessMemPlace.ptr with offset := Miri.ABI.Size.ofBytes 0x1006 }
                metadata := .none },
            translateTy lm21U16Ty lm21Body.layouts⟩ ∧
      ImmediateRel lm21U16Ty lm21Body.layouts (.scalar ⟨0x0304, 2⟩)
        (.scalar (.fromScalarInt msc)) := by
  have ⟨hin, _⟩ := evalProjection_constantIndex_simulation
    (body := lm21Body) (locals := (lm21ArrAnneal 7 .uninit).frame.locals)
    (m := lm21ArrMiri 7 .uninit) (lm21ArrMiriFrame 7 .uninit) lm21_nodup_arr
    lm21_wf_u16Arr3 lm21_memPlaceRel
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
  have hsim := step_stmt_lm2_1_array_simulation
    (lm21_arr_stateRel 4 (.init (.scalar ⟨1, 8⟩)) (.scalar (.fromScalarInt lm21Usize1))
      (Or.inr ⟨.scalar ⟨1, 8⟩, rfl, lm21_idxRel_1⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3 (.index 2) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      · intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv
      · refine .index 2 lm21UsizeDecl rfl rfl (Or.inl ?_)
        intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
    (lm21_arr_stateRel 5 (.init (.scalar ⟨1, 8⟩)) (.scalar (.fromScalarInt lm21Usize1))
      (Or.inr ⟨.scalar ⟨1, 8⟩, rfl, lm21_idxRel_1⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3 (.index 2)
        (.constant (lm21ConstU16 0x090A)) _
        rfl lm21_wf_u16Arr3 lm21_isPrim_u16 ?_
        (lm21_constU16_wt _ 0x090A (by decide))
        (fun _ h => nomatch h)
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      refine .index 2 lm21UsizeDecl rfl rfl (Or.inl ?_)
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
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
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
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
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
    (lm21_arr_stateRel 8 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      exact .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3
        (.constantIndex 1 3 true) (.constant (lm21ConstU16 0x0B0C)) _
        rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.constantIndex 1 3 true (by decide) (by decide)
          ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
        (lm21_constU16_wt _ 0x0B0C (by decide))
        (fun _ h => nomatch h)
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩))))
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
    (lm21_arr_stateRel 4 (.init (.scalar ⟨3, 8⟩)) (.scalar (.fromScalarInt lm21Usize3))
      (Or.inr ⟨.scalar ⟨3, 8⟩, rfl, lm21_idxRel_3⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3 (.index 2) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      · intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv
      · refine .index 2 lm21UsizeDecl rfl rfl (Or.inl ?_)
        intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
    (lm21_arr_stateRel 5 (.init (.scalar ⟨3, 8⟩)) (.scalar (.fromScalarInt lm21Usize3))
      (Or.inr ⟨.scalar ⟨3, 8⟩, rfl, lm21_idxRel_3⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3 (.index 2)
        (.constant (lm21ConstU16 0x090A)) _
        rfl lm21_wf_u16Arr3 lm21_isPrim_u16 ?_
        (lm21_constU16_wt _ 0x090A (by decide))
        (fun _ h => nomatch h)
        (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      refine .index 2 lm21UsizeDecl rfl rfl (Or.inl ?_)
      intro mls hmls mp hv
      simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
    (lm21_arr_stateRel 4 .uninit .uninit (Or.inl ⟨rfl, rfl⟩))
    lm21_nodup_arr lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_arrFrame_eq htf
      refine .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3 (.index 2) false _
        rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩)))
      · intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv
      · refine .index 2 lm21UsizeDecl rfl rfl (Or.inl ?_)
        intro mls hmls mp hv
        simp [lm21ArrMiriFrame] at hmls; subst hmls; cases hv)
  replace hsim := hsim.1
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
  have hsim := step_stmt_lm2_1_array_simulation
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
  replace hsim := hsim.1
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-! ## 7. Chained Multi-Step Witness (`stmt 10..14`) -/

/-- Every local of `lm21InitMiriFrame k` is immediate. -/
private theorem lm21_initFrame_imm (k j : Nat) : IsImmediateFrameLocal (lm21InitMiriFrame k) j := by
  intro mls hmls mp hv
  match j with
  | 0 | 1 | 2 | 3 =>
    simp [lm21InitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 4 => simp [lm21InitMiriFrame] at hmls

/-- Chained five-statement run from the all-uninitialized state, applying
`step_stmt_lm2_1_array_simulation` to each successive `lean-miri` post-state:
`stmt 10` builds `_1 = [0x0102, 0x0304, 0x0506]` in a fresh allocation, `stmt 11`
writes `_1[-1 of 3] = 0x0B0C` and `stmt 12` writes `_1[0 of 3] = 0x0D0E` into that
allocation, `stmt 13` reads `_0 = copy _1[2 of 3]` (`0x0B0C`), and `stmt 14`
computes `_2 = Len(_1)` (`3`). Each step after the first uses only the
`StateRel`, `LiveAllocsNodup` (`StepPreservesNodup`), and scalar-local immediacy
(`StepPreservesImmediate`) that the preceding steps re-established. -/
theorem lm21_chain_steps :
    let hooks := annealStepHooks lm21Body.localDecls lm21Body.layouts
    let elems₂ : List Value := [.scalar ⟨0x0102, 2⟩, .scalar ⟨0x0304, 2⟩, .scalar ⟨0x0B0C, 2⟩]
    let elems₃ : List Value := [.scalar ⟨0x0D0E, 2⟩, .scalar ⟨0x0304, 2⟩, .scalar ⟨0x0B0C, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState lm21Body []).memory }
    let s₁ := mkState 11 [.uninit, .init (.aggregate 0 lm21ArrElems), .uninit, .uninit]
    let s₂ := mkState 12 [.uninit, .init (.aggregate 0 elems₂), .uninit, .uninit]
    let s₃ := mkState 13 [.uninit, .init (.aggregate 0 elems₃), .uninit, .uninit]
    let s₄ := mkState 14 [.init (.scalar ⟨0x0B0C, 2⟩), .init (.aggregate 0 elems₃), .uninit, .uninit]
    let s₅ := mkState 15
      [.init (.scalar ⟨0x0B0C, 2⟩), .init (.aggregate 0 elems₃), .init (.scalar ⟨3, 8⟩), .uninit]
    stepMirFn lm21Body (lm21InitAnneal 10) = .step s₁ ∧
      stepMirFn lm21Body s₁ = .step s₂ ∧
      stepMirFn lm21Body s₂ = .step s₃ ∧
      stepMirFn lm21Body s₃ = .step s₄ ∧
      stepMirFn lm21Body s₄ = .step s₅ ∧
      ∃ m₁ m₂ m₃ m₄ m₅,
        Miri.Interpreter.Step.step hooks () (lm21InitMiri 10) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        StateRel lm21Body s₅ m₅ ∧
        LiveAllocsNodup m₅.machine := by
  intro hooks elems₂ elems₃ mkState s₁ s₂ s₃ s₄ s₅
  have h₁ : stepMirFn lm21Body (lm21InitAnneal 10) = .step s₁ := rfl
  have h₂ : stepMirFn lm21Body s₁ = .step s₂ := rfl
  have h₃ : stepMirFn lm21Body s₂ = .step s₃ := rfl
  have h₄ : stepMirFn lm21Body s₃ = .step s₄ := rfl
  have h₅ : stepMirFn lm21Body s₄ = .step s₅ := rfl
  refine ⟨h₁, h₂, h₃, h₄, h₅, ?_⟩
  -- `stmt 10`: array construction from the initial state.
  obtain ⟨hsim₁, hnd₁, him₁, -⟩ := step_stmt_lm2_1_array_simulation (lm21_init_stateRel 10)
    lm21_nodup_empty lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_initFrame_eq htf
      refine .aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inl ⟨lm21_initFrame_imm 10 1, lm21_canReserve_empty⟩))
        ?_ lm21_isPrim_u16
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact lm21_constU16_wt _ 0x0102 (by decide)
      · exact lm21_constU16_wt _ 0x0304 (by decide)
      · exact lm21_constU16_wt _ 0x0506 (by decide))
  rw [h₁] at hsim₁
  generalize Miri.Interpreter.Step.step hooks () (lm21InitMiri 10) = r₁ at hsim₁ hnd₁ him₁ ⊢
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
  -- Locals `_0` and `_2` stay immediate: `stmt 10` moves only `_1` into memory.
  have himm₁ : ∀ j, j ≠ 1 → ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf j :=
    fun j hj tf htf => him₁ rfl _ tf rfl htf j (fun h => hj (by injection h with h; exact h.symm))
      (lm21_initFrame_imm 10 j)
  -- `stmt 11`: `ConstantIndex` (`fromEnd = true`) write into the allocation of `stmt 10`.
  obtain ⟨hsim₂, hnd₂, him₂, -⟩ := step_stmt_lm2_1_array_simulation hrel₁ (hnd₁ rfl) lm21_phase
    rfl rfl (fun tf _ =>
      .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3 (.constantIndex 1 3 true)
        (.constant (lm21ConstU16 0x0B0C)) _ rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.constantIndex 1 3 true (by decide) (by decide)
          ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
        (lm21_constU16_wt tf 0x0B0C (by decide))
        (fun _ h => nomatch h)
        (Or.inr (Or.inr ⟨_, rfl⟩))))
  rw [h₂] at hsim₂
  generalize hr₂ : Miri.Interpreter.Step.step hooks () m₁ = r₂ at hsim₂ hnd₂ him₂
  cases hsim₂ with
  | step _ m₂ hrel₂ =>
  have himm₂ : ∀ j, j ≠ 1 → ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj tf htf
    obtain ⟨tf₁, htf₁⟩ : ∃ tf₁, m₁.stack.frames = #[tf₁] := by
      obtain ⟨tf₁, htf₁, _⟩ := hrel₁; exact ⟨tf₁, htf₁⟩
    exact him₂ rfl tf₁ tf htf₁ htf j (fun h => nomatch h) (himm₁ j hj tf₁ htf₁)
  -- `stmt 12`: `ConstantIndex` (`fromEnd = false`) write into the same allocation.
  obtain ⟨hsim₃, hnd₃, him₃, -⟩ := step_stmt_lm2_1_array_simulation hrel₂ (hnd₂ rfl) lm21_phase
    rfl rfl (fun tf _ =>
      .elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3 (.constantIndex 0 3 false)
        (.constant (lm21ConstU16 0x0D0E)) _ rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.constantIndex 0 3 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (lm21_constU16_wt tf 0x0D0E (by decide))
        (fun _ h => nomatch h)
        (Or.inr (Or.inr ⟨_, rfl⟩))))
  rw [h₃] at hsim₃
  generalize hr₃ : Miri.Interpreter.Step.step hooks () m₂ = r₃ at hsim₃ hnd₃ him₃
  cases hsim₃ with
  | step _ m₃ hrel₃ =>
  have himm₃ : ∀ j, j ≠ 1 → ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj tf htf
    obtain ⟨tf₂, htf₂⟩ : ∃ tf₂, m₂.stack.frames = #[tf₂] := by
      obtain ⟨tf₂, htf₂, _⟩ := hrel₂; exact ⟨tf₂, htf₂⟩
    exact him₃ rfl tf₂ tf htf₂ htf j (fun h => nomatch h) (himm₂ j hj tf₂ htf₂)
  -- `stmt 13`: `ConstantIndex` (`fromEnd = false`) read of the element `stmt 11` wrote.
  obtain ⟨hsim₄, hnd₄, him₄, -⟩ := step_stmt_lm2_1_array_simulation hrel₃ (hnd₃ rfl) lm21_phase
    rfl rfl (fun tf htf =>
      .elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.constantIndex 2 3 false) false _ rfl lm21_wf_u16Arr3 rfl rfl
        (himm₃ 0 (by decide) tf htf)
        (.constantIndex 2 3 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (Or.inr (Or.inr ⟨_, rfl⟩))))
  rw [h₄] at hsim₄
  generalize hr₄ : Miri.Interpreter.Step.step hooks () m₃ = r₄ at hsim₄ hnd₄ him₄
  cases hsim₄ with
  | step _ m₄ hrel₄ =>
  have himm₄ : ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf 2 := by
    intro tf htf
    obtain ⟨tf₃, htf₃⟩ : ∃ tf₃, m₃.stack.frames = #[tf₃] := by
      obtain ⟨tf₃, htf₃, _⟩ := hrel₃; exact ⟨tf₃, htf₃⟩
    exact him₄ rfl tf₃ tf htf₃ htf 2 (fun h => nomatch h) (himm₃ 2 (by decide) tf₃ htf₃)
  -- `stmt 14`: `Len(_1)` of the twice-updated array.
  obtain ⟨hsim₅, hnd₅, -, -⟩ := step_stmt_lm2_1_array_simulation hrel₄ (hnd₄ rfl) lm21_phase
    rfl rfl (fun tf htf =>
      .lenArray 2 1 lm21UsizeDecl lm21U16Arr3Decl (.uint .u16) 3 _
        rfl lm21_wf_u16Arr3 rfl rfl (himm₄ tf htf) (Or.inr (Or.inr ⟨_, rfl⟩)))
  rw [h₅] at hsim₅
  generalize hr₅ : Miri.Interpreter.Step.step hooks () m₄ = r₅ at hsim₅ hnd₅
  cases hsim₅ with
  | step _ m₅ hrel₅ =>
  exact ⟨m₁, m₂, m₃, m₄, m₅, rfl, hr₂, hr₃, hr₄, hr₅, hrel₅, hnd₅ rfl⟩

/-! ## 8. Fail-Closed Whole-Array Read & Indirect `usize` Index Local Witnesses -/

/-- Unprojected whole-array immediate reads (`ty ≠ arraySliceMetaTyId`) fail closed
with `StepError.unsupported "whole-array immediate read not supported"`, confirming
that `annealReadImmediate` only synthesizes `(ptr, len)` metadata on the internal
`.UnwrapUnsafeBinder arraySliceMetaTyId` projection emitted by `translateRvalue (.len _)`. -/
theorem lm21_whole_array_read_unsupported :
    annealReadImmediate
      ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
      (lm21ArrMiri 3 .uninit) =
      .error (.unsupported "whole-array immediate read not supported")
        (lm21ArrMiri 3 .uninit) :=
  annealReadImmediate_whole_array_unsupported
    lm21_wf_u16Arr3 lm21_nodup_arr lm21_memPlaceRel

/-- A partial subslice (`_1[1..3]` on `[u16; 3]`) fails closed with
`StepError.unsupported "array subslice in annealProjectionCx"`. -/
theorem lm21_partial_subslice_unsupported :
    (annealProjectList
      (annealProjectionCx (lm21ArrMiriFrame 3 .uninit) lm21Body.layouts
        (witnessMachineOf lm21ArrAlloc))
      ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
      [.Subslice 1 3 false]).mapError annealLiftProjectionError =
      .error (.unsupported "array subslice in annealProjectionCx") :=
  congrArg (Except.mapError annealLiftProjectionError)
    (projectSubslice_array_unsupported
      (mach := witnessMachineOf lm21ArrAlloc) (mp := witnessMemPlace)
      (lm21ArrMiriFrame 3 .uninit) lm21_wf_u16Arr3
      1 3 false (Or.inl ⟨rfl, by decide, by decide⟩))

/-- Whole-array subslices (`[0..3]` with `fromEnd = false` and `[..]` / `Subslice 0 0 true`
with `fromEnd = true` on `[u16; 3]`): `MirSemantics.writeProjectedValue` writes the updated
3-element subslice in place, while the base `annealProjectionCx` (prior to `LM-2.4`'s
`annealSubsliceProjectionCx`) fails closed with
`StepError.unsupported "array subslice in annealProjectionCx"` instead of aliasing
`Rvalue.len`'s internal `.UnwrapUnsafeBinder arraySliceMetaTyId` projection. -/
theorem lm21_whole_subslice_unsupported :
    (∀ v0 v1 v2, writeProjectedValue (lm21ArrAnneal 3 .uninit).frame.locals
      (.aggregate 0 lm21ArrElems) [.subslice 0 3 false] (.aggregate 0 [v0, v1, v2]) =
      .ok (.aggregate 0 [v0, v1, v2])) ∧
    (∀ v0 v1 v2, writeProjectedValue (lm21ArrAnneal 3 .uninit).frame.locals
      (.aggregate 0 lm21ArrElems) [.subslice 0 0 true] (.aggregate 0 [v0, v1, v2]) =
      .ok (.aggregate 0 [v0, v1, v2])) ∧
    (annealProjectList
      (annealProjectionCx (lm21ArrMiriFrame 3 .uninit) lm21Body.layouts
        (witnessMachineOf lm21ArrAlloc))
      ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
      [.Subslice 0 3 false]).mapError annealLiftProjectionError =
      .error (.unsupported "array subslice in annealProjectionCx") ∧
    (annealProjectList
      (annealProjectionCx (lm21ArrMiriFrame 3 .uninit) lm21Body.layouts
        (witnessMachineOf lm21ArrAlloc))
      ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
      [.Subslice 0 0 true]).mapError annealLiftProjectionError =
      .error (.unsupported "array subslice in annealProjectionCx") :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl,
    congrArg (Except.mapError annealLiftProjectionError)
      (projectSubslice_array_unsupported
        (mach := witnessMachineOf lm21ArrAlloc) (mp := witnessMemPlace)
        (lm21ArrMiriFrame 3 .uninit) lm21_wf_u16Arr3
        0 3 false (Or.inl ⟨rfl, by decide, by decide⟩)),
    congrArg (Except.mapError annealLiftProjectionError)
      (projectSubslice_array_unsupported
        (mach := witnessMachineOf lm21ArrAlloc) (mp := witnessMemPlace)
        (lm21ArrMiriFrame 3 .uninit) lm21_wf_u16Arr3
        0 0 true (Or.inr ⟨rfl, by decide⟩))⟩

def lm21IdxAllocId : Miri.Memory.AllocId := ⟨2, by decide⟩
def lm21IdxBaseAddr : UInt64 := 0x2000

/-- Concrete memory-backed `MemPlace` for an indirect `usize` index local `_2`
at virtual address `0x2000` inside `lm21IdxAllocId` (`AllocId = 2`). -/
def lm21IdxMemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes 0x2000, some (.concrete lm21IdxAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

/-- 8-byte stack allocation holding `1_usize` in little-endian (`#[1, 0, 0, 0, 0, 0, 0, 0]`). -/
def lm21IdxInitAlloc1 :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[1, 0, 0, 0, 0, 0, 0, 0] (translateAlignBytes 8) .Mut)
    (by decide)).withExtra none

/-- 8-byte uninitialized stack allocation for `_2 : usize`. -/
def lm21IdxUninitAlloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  match Miri.Memory.Allocation.writeUninit
      (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8))
      (Miri.ABI.Size.ofBytes 8)
      lm21IdxInitAlloc1 with
  | .ok () alloc => alloc
  | .error _ alloc => alloc

/-- Two-allocation `AnnealMachine` simultaneously backing `_1 : [u16; 3]` at
`witnessAllocId` (`1`, `0x1000`) and `_2 : usize` at `lm21IdxAllocId` (`2`, `0x2000`). -/
def lm21TwoAllocMachine
    (idxAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealMachine :=
  { memory :=
      { (Miri.Memory.MemoryState.empty : AnnealMemory) with
        nextAllocId := 3
        live := #[
          (witnessAllocId, { kind := .stack, allocation := lm21ArrAlloc }),
          (lm21IdxAllocId, { kind := .stack, allocation := idxAlloc })] }
    addresses :=
      { provenanceMode := .default
        addressMode := .managed
        generation := none
        baseAddr := #[
          { allocId := witnessAllocId, address := witnessBaseAddr },
          { allocId := lm21IdxAllocId, address := lm21IdxBaseAddr }]
        intToPtrMap := #[
          { address := witnessBaseAddr, allocId := witnessAllocId },
          { address := lm21IdxBaseAddr, allocId := lm21IdxAllocId }] }
    borrowTracker := none }

theorem lm21_nodup_twoAlloc
    (idxAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    LiveAllocsNodup (lm21TwoAllocMachine idxAlloc) :=
  show List.Pairwise (· ≠ ·) [witnessAllocId, lm21IdxAllocId] by decide

def lm21IndIdxMiriFrame (k : Nat) :
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
      { value := .live (.indirect lm21IdxMemPlace), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, k⟩ }

def lm21IndIdxMiri (k : Nat)
    (idxAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    AnnealStepState :=
  { stack := ⟨#[lm21IndIdxMiriFrame k]⟩, machine := lm21TwoAllocMachine idxAlloc }

private theorem lm21_twoAlloc_arr_memPlaceRel
    (idxAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)) :
    MemPlaceRel (lm21TwoAllocMachine idxAlloc) lm21U16Arr3Ty emptyLayoutTable
      (some (.aggregate 0 lm21ArrElems)) witnessMemPlace := by
  refine MemPlaceRel.mk
    witnessAllocId witnessTag witnessBaseAddr witnessRelOffset
    { kind := .stack, allocation := lm21ArrAlloc }
    rfl rfl rfl (List.Mem.head _)
    rfl (by decide) (by decide) (by decide)
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
  have hk : elemKind = .uint .u16 ∧ count = 3 := by simpa [lm21U16Arr3Ty] using hkind.symm
  rcases hk with ⟨rfl, rfl⟩
  have he : elems = lm21ArrElems := by
    injection hval with hv; injection hv with _ hes; exact hes.symm
  subst he
  exact ⟨rfl, rfl, rfl, lm21_arraySliceRel⟩

private theorem lm21_twoAlloc_idx1_memPlaceRel :
    MemPlaceRel (lm21TwoAllocMachine lm21IdxInitAlloc1) lm21UsizeTy emptyLayoutTable
      (some (.scalar ⟨1, 8⟩)) lm21IdxMemPlace := by
  refine MemPlaceRel.mk
    lm21IdxAllocId witnessTag lm21IdxBaseAddr Miri.ABI.Size.ZERO
    { kind := .stack, allocation := lm21IdxInitAlloc1 }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.head _))
    (by decide) (by decide) (by decide) (by decide)
    (show lm21IdxMemPlace.ptr.offset.isAligned (translateAlignBytes 8) = .ok true by decide)
    (show Miri.ABI.Size.ZERO.bytes.toNat + 8 ≤ lm21IdxInitAlloc1.byteSize.bytes.toNat by decide)
    (fun h _ => nomatch h)
    (fun _ _ _ =>
      show lm21IdxInitAlloc1.initializationMask.isRangeInitialized
          (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) =
        Except.ok (Except.ok ()) by decide)
    ?_
    (fun _ _ _ _ h => nomatch h)
  intro sc hval
  have hsc : sc = ⟨1, 8⟩ := by
    injection hval with hv; injection hv with heq; exact heq.symm
  subst hsc
  refine ⟨rfl, (fun h => nomatch h), (fun h => nomatch h), lm21Usize1,
    ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩, ?_⟩
  show lm21IdxInitAlloc1.readScalar annealTargetDataLayout
    (Miri.Memory.allocRange Miri.ABI.Size.ZERO (Miri.ABI.Size.ofBytes 8)) false = _
  with_unfolding_all rfl

private theorem lm21_twoAlloc_idxUninit_memPlaceRel :
    MemPlaceRel (lm21TwoAllocMachine lm21IdxUninitAlloc) lm21UsizeTy emptyLayoutTable
      none lm21IdxMemPlace :=
  MemPlaceRel.mk
    lm21IdxAllocId witnessTag lm21IdxBaseAddr Miri.ABI.Size.ZERO
    { kind := .stack, allocation := lm21IdxUninitAlloc }
    rfl rfl rfl (List.Mem.tail _ (List.Mem.head _))
    (by decide) (by decide) (by decide) (by decide)
    (show lm21IdxMemPlace.ptr.offset.isAligned (translateAlignBytes 8) = .ok true by decide)
    (show Miri.ABI.Size.ZERO.bytes.toNat + 8 ≤ lm21IdxUninitAlloc.byteSize.bytes.toNat by decide)
    (fun _ _ => by decide)
    (fun _ h _ => nomatch h)
    (fun _ h => nomatch h)
    (fun _ _ _ _ h => nomatch h)

private theorem lm21_indIdx_disjoint (k : Nat) :
    MemoryAllocDisjoint (lm21IndIdxMiriFrame k) := by
  intro i j mp_i mp_j lay_i lay_j hneq hi hj
  match i, j with
  | 0, _ => simp [lm21IndIdxMiriFrame] at hi
  | 3, _ => simp [lm21IndIdxMiriFrame] at hi
  | _ + 4, _ => simp [lm21IndIdxMiriFrame] at hi
  | 1, 0 => simp [lm21IndIdxMiriFrame] at hj
  | 1, 1 => exact absurd rfl hneq
  | 1, 2 =>
    have h1 : mp_i = witnessMemPlace := by
      simp [lm21IndIdxMiriFrame] at hi; exact hi.1.symm
    have h2 : mp_j = lm21IdxMemPlace := by
      simp [lm21IndIdxMiriFrame] at hj; exact hj.1.symm
    subst h1 h2; decide
  | 1, 3 => simp [lm21IndIdxMiriFrame] at hj
  | 1, _ + 4 => simp [lm21IndIdxMiriFrame] at hj
  | 2, 0 => simp [lm21IndIdxMiriFrame] at hj
  | 2, 1 =>
    have h1 : mp_i = lm21IdxMemPlace := by
      simp [lm21IndIdxMiriFrame] at hi; exact hi.1.symm
    have h2 : mp_j = witnessMemPlace := by
      simp [lm21IndIdxMiriFrame] at hj; exact hj.1.symm
    subst h1 h2; decide
  | 2, 2 => exact absurd rfl hneq
  | 2, 3 => simp [lm21IndIdxMiriFrame] at hj
  | 2, _ + 4 => simp [lm21IndIdxMiriFrame] at hj

private theorem lm21_indIdx_stateRel (k : Nat) (idxSlot : LocalSlot)
    (idxAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree))
    (hidx_rel : LocalRel (lm21TwoAllocMachine idxAlloc) lm21UsizeDecl emptyLayoutTable
      idxSlot ⟨.live (.indirect lm21IdxMemPlace), none⟩) :
    StateRel lm21Body (lm21ArrAnneal k idxSlot) (lm21IndIdxMiri k idxAlloc) := by
  refine StateRel.mk (lm21IndIdxMiriFrame k) rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl (lm21_indIdx_disjoint k)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm21U16Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21IndIdxMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm21ArrElems) := by
      simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm21IndIdxMiriFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ witnessMemPlace none (fun _ h => nomatch h) nofun
      (lm21_twoAlloc_arr_memPlaceRel idxAlloc)
  | 2 =>
    have hd : decl = lm21UsizeDecl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = idxSlot := by simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect lm21IdxMemPlace), layout := none } := by
      simpa [lm21IndIdxMiriFrame] using hmls.symm
    subst hd hs hm
    exact hidx_rel
  | 3 =>
    have hd : decl = lm21U16Arr0Decl := by simpa [lm21Body, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21ArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21IndIdxMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 4 =>
    simp [lm21Body, get?] at hdecl

private theorem lm21_indIdxFrame_eq {k : Nat}
    {idxAlloc : Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree)}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm21IndIdxMiri k idxAlloc).stack.frames = #[tf]) : tf = lm21IndIdxMiriFrame k := by
  simp only [lm21IndIdxMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at h
  exact h.symm

/-- `stmt 4`: `_0 = copy _1[_2]` when `_2 : usize` is stack-allocated (`.indirect`
in `lm21TwoAllocMachine lm21IdxInitAlloc1` holding `1_usize`) reads `0x0304_u16`
into `_0` and steps both Anneal and `lean-miri` in `StateRel` via
`step_stmt_lm2_1_simulation`. -/
theorem lm21_indirect_index_read_steps :
    let s₀ := lm21ArrAnneal 4 (.init (.scalar ⟨1, 8⟩))
    let m₀ := lm21IndIdxMiri 4 lm21IdxInitAlloc1
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
  have hstate := lm21_indIdx_stateRel 4 (.init (.scalar ⟨1, 8⟩)) lm21IdxInitAlloc1
    (.indirect _ lm21IdxMemPlace none (fun _ h => nomatch h) nofun lm21_twoAlloc_idx1_memPlaceRel)
  have hsim := (step_stmt_lm2_1_simulation hstate (lm21_nodup_twoAlloc lm21IdxInitAlloc1)
    lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_indIdxFrame_eq htf
      refine .arrayStmt (.elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.index 2) false _ rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩))))
      · intro mls hmls mp hv
        simp [lm21IndIdxMiriFrame] at hmls; subst hmls; cases hv
      · exact .index 2 lm21UsizeDecl rfl rfl (Or.inr (Or.inr (Or.inr ⟨⟨1, 8⟩, rfl⟩))))).1
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | step _ m' hrel => exact ⟨m', rfl, hrel⟩

/-- `stmt 4`: `_0 = copy _1[_2]` when `_2 : usize` is stack-allocated (`.indirect`)
but its backing bytes are uninitialized (`lm21IdxUninitAlloc`) reports undefined
behavior in both Anneal and `lean-miri`. -/
theorem lm21_indirect_index_uninit_ub :
    let s₀ := lm21ArrAnneal 4 .uninit
    let m₀ := lm21IndIdxMiri 4 lm21IdxUninitAlloc
    stepMirFn lm21Body s₀ = .fail .ub ∧
      ∃ m' msg, Miri.Interpreter.Step.step
          (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ =
          (m', .error (.undefinedBehavior msg)) := by
  intro s₀ m₀
  have hstep : stepMirFn lm21Body s₀ = .fail .ub := rfl
  refine ⟨hstep, ?_⟩
  have hstate := lm21_indIdx_stateRel 4 .uninit lm21IdxUninitAlloc
    (.indirect _ lm21IdxMemPlace none (fun _ h => nomatch h) nofun
      lm21_twoAlloc_idxUninit_memPlaceRel)
  have hsim := (step_stmt_lm2_1_simulation hstate (lm21_nodup_twoAlloc lm21IdxUninitAlloc)
    lm21_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_indIdxFrame_eq htf
      refine .arrayStmt (.elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.index 2) false _ rfl lm21_wf_u16Arr3 rfl rfl ?_ ?_ (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩))))
      · intro mls hmls mp hv
        simp [lm21IndIdxMiriFrame] at hmls; subst hmls; cases hv
      · exact .index 2 lm21UsizeDecl rfl rfl (Or.inr (Or.inr (Or.inl rfl))))).1
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21Body.localDecls lm21Body.layouts) () m₀ = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-! ## 9. Mixed `LM-1.4` + `LM-2.1` + `LM-1.1` Chained Reassignment Witness -/

def lm21ConstUsize (n : Nat) : ConstOperand :=
  { ty := lm21UsizeTy, val := .scalar (.int ⟨n, 8⟩) }

/-- Seven-statement `Runtime(PostCleanup)` MIR body exercising mixed `LM-1.4`
storage lifecycle (`StorageLive`/`StorageDead`), fresh array construction,
in-place `Repeat` overwrite, in-place `Aggregate` overwrite, `LM-1.1` scalar
`BinaryOp.add`, and dynamic `Index` element read:
- `stmt 0`: `StorageLive(_1)` (`_1` starts `.dead`)
- `stmt 1`: `_1 = [const 0x0102_u16, const 0x0304_u16, const 0x0506_u16]` (fresh allocation)
- `stmt 2`: `_1 = [const 0x0708_u16; 3]` (in-place `Repeat` overwrite of live `.indirect` `_1`)
- `stmt 3`: `_1 = [const 0x090A_u16, const 0x0B0C_u16, const 0x0D0E_u16]` (in-place `Aggregate` overwrite)
- `stmt 4`: `_2 = Add(const 1_usize, const 1_usize)` (`LM-1.1` scalar `BinaryOp` -> `2_usize`)
- `stmt 5`: `_0 = copy _1[_2]` (dynamic `Index` read at `2` -> `0x0D0E_u16`)
- `stmt 6`: `StorageDead(_1)` (`LM-1.4` deallocation of indirect `_1`) -/
def lm21MixedBody : CapturedMir where
  defPath := "lm_2_1_witness::mixed_reassign"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm21U16Decl, lm21U16Arr3Decl, lm21UsizeDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.constant (lm21ConstU16 0x0102), .constant (lm21ConstU16 0x0304),
           .constant (lm21ConstU16 0x0506)])),
        mkStmt (.assign (local_ 1) (.repeat (.constant (lm21ConstU16 0x0708)) 3)),
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.constant (lm21ConstU16 0x090A), .constant (lm21ConstU16 0x0B0C),
           .constant (lm21ConstU16 0x0D0E)])),
        mkStmt (.assign (local_ 2)
          (.binaryOp .add (.constant (lm21ConstUsize 1)) (.constant (lm21ConstUsize 1)))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.index 2]⟩))),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

theorem lm21_mixed_phase : ∀ p, lm21MixedBody.phase ≠ .other p := by
  intro p h; cases h

def lm21MixedInitAnneal : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := 0, locals := [.uninit, .dead, .uninit] }
    memory := (initMachineState lm21MixedBody []).memory }

def lm21MixedInitMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21MixedBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm21U16Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def lm21MixedInitMiri : AnnealStepState :=
  { stack := ⟨#[lm21MixedInitMiriFrame]⟩, machine := AnnealMachine.empty }

theorem lm21_mixed_init_stateRel :
    StateRel lm21MixedBody lm21MixedInitAnneal lm21MixedInitMiri := by
  refine StateRel.mk lm21MixedInitMiriFrame rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 => rintro ⟨⟩
      | _ + 3 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hd : decl = lm21U16Decl := by simpa [lm21MixedBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21MixedInitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21MixedInitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by simpa [lm21MixedBody, get?] using hdecl.symm
    have hs : slot = .dead := by simpa [lm21MixedInitAnneal, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm21MixedInitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .dead none (fun _ h => nomatch h)
  | 2 =>
    have hd : decl = lm21UsizeDecl := by simpa [lm21MixedBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21MixedInitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21MixedInitMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 3 =>
    simp [lm21MixedBody, get?] at hdecl

private theorem lm21_mixedInitFrame_imm (j : Nat) :
    IsImmediateFrameLocal lm21MixedInitMiriFrame j := by
  intro mls hmls mp hv
  match j with
  | 0 | 1 | 2 =>
    simp [lm21MixedInitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 3 => simp [lm21MixedInitMiriFrame] at hmls

private theorem lm21_mixed_constU16_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 65536) :
    WellTypedLM2_1ScalarOperand lm21MixedBody tf (.constant (lm21ConstU16 n)) lm21U16Ty :=
  .ofScalar (.constScalar (lm21ConstU16 n) ⟨n, 2⟩ rfl lm21_isPrim_u16 (Or.inr (Or.inl rfl))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h))

private theorem lm21_mixed_constUsize_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 2 ^ 64) :
    WellTypedScalarOperand lm21MixedBody tf (.constant (lm21ConstUsize n)) lm21UsizeTy :=
  .constScalar (lm21ConstUsize n) ⟨n, 8⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h)

/-- Seven-step end-to-end execution chaining `step_stmt_lm2_1_simulation` across
`LM-1.4` (`StorageLive`, `StorageDead`), `LM-2.1` (fresh `Aggregate`, in-place
`Repeat` overwrite, in-place `Aggregate` overwrite, dynamic `Index` read), and
`LM-1.1` (scalar `BinaryOp.add`), propagating `CanReserveAllocId` across
`StorageLive(1)` purely via `StepPreservesHighWater` + `MemoryHighWater.canReserveAllocId`,
reaching `_0 = 0x0D0E_u16`, `_1 = .dead`, `_2 = 2_usize` in `StateRel` with
`LiveAllocsNodup` and `MemoryHighWater`. -/
theorem lm21_mixed_reassign_chain_steps :
    let hooks := annealStepHooks lm21MixedBody.localDecls lm21MixedBody.layouts
    let repElems : List Value := [.scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩, .scalar ⟨0x0708, 2⟩]
    let newElems : List Value := [.scalar ⟨0x090A, 2⟩, .scalar ⟨0x0B0C, 2⟩, .scalar ⟨0x0D0E, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState lm21MixedBody []).memory }
    let s₁ := mkState 1 [.uninit, .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .init (.aggregate 0 lm21ArrElems), .uninit]
    let s₃ := mkState 3 [.uninit, .init (.aggregate 0 repElems), .uninit]
    let s₄ := mkState 4 [.uninit, .init (.aggregate 0 newElems), .uninit]
    let s₅ := mkState 5 [.uninit, .init (.aggregate 0 newElems), .init (.scalar ⟨2, 8⟩)]
    let s₆ := mkState 6
      [.init (.scalar ⟨0x0D0E, 2⟩), .init (.aggregate 0 newElems), .init (.scalar ⟨2, 8⟩)]
    let s₇ := mkState 7 [.init (.scalar ⟨0x0D0E, 2⟩), .dead, .init (.scalar ⟨2, 8⟩)]
    stepMirFn lm21MixedBody lm21MixedInitAnneal = .step s₁ ∧
      stepMirFn lm21MixedBody s₁ = .step s₂ ∧
      stepMirFn lm21MixedBody s₂ = .step s₃ ∧
      stepMirFn lm21MixedBody s₃ = .step s₄ ∧
      stepMirFn lm21MixedBody s₄ = .step s₅ ∧
      stepMirFn lm21MixedBody s₅ = .step s₆ ∧
      stepMirFn lm21MixedBody s₆ = .step s₇ ∧
      ∃ m₁ m₂ m₃ m₄ m₅ m₆ m₇,
        Miri.Interpreter.Step.step hooks () lm21MixedInitMiri = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok true) ∧
        StateRel lm21MixedBody s₇ m₇ ∧
        LiveAllocsNodup m₇.machine := by
  intro hooks repElems newElems mkState s₁ s₂ s₃ s₄ s₅ s₆ s₇
  have h₁ : stepMirFn lm21MixedBody lm21MixedInitAnneal = .step s₁ := rfl
  have h₂ : stepMirFn lm21MixedBody s₁ = .step s₂ := rfl
  have h₃ : stepMirFn lm21MixedBody s₂ = .step s₃ := rfl
  have h₄ : stepMirFn lm21MixedBody s₃ = .step s₄ := rfl
  have h₅ : stepMirFn lm21MixedBody s₄ = .step s₅ := rfl
  have h₆ : stepMirFn lm21MixedBody s₅ = .step s₆ := rfl
  have h₇ : stepMirFn lm21MixedBody s₆ = .step s₇ := rfl
  refine ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, ?_⟩
  -- `stmt 0`: `LM-1.4` `StorageLive(1)` from `_1 = .dead`.
  have hsl_imm := fun tf' htf' =>
    step_storageLive_establishes_immediate lm21_mixed_init_stateRel
      (loc := 1) (decl := lm21U16Arr3Decl) rfl rfl rfl (tf' := tf') htf'
  obtain ⟨hsim₁, hnd₁, him₁, hhw₁⟩ := step_stmt_lm2_1_simulation lm21_mixed_init_stateRel
    lm21_nodup_empty lm21_mixed_phase rfl rfl
    (fun _ _ => .lm14Stmt (.storageLive 1 lm21U16Arr3Decl _ rfl))
  rw [h₁] at hsim₁
  generalize Miri.Interpreter.Step.step hooks () lm21MixedInitMiri = r₁
    at hsim₁ hnd₁ him₁ hhw₁ hsl_imm ⊢
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
  have himm₁_1 : ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf 1 :=
    fun tf htf => hsl_imm tf htf
  have himm₁_all : ∀ j, ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf j :=
    fun j tf htf => him₁ rfl _ tf rfl htf j (fun h => nomatch h) (lm21_mixedInitFrame_imm j)
  obtain ⟨hw₁, _⟩ := hhw₁ rfl MemoryHighWater.empty (by decide)
  have hcanRes₁ : CanReserveAllocId m₁.machine.memory := hw₁.canReserveAllocId
  -- `stmt 1`: `LM-2.1` fresh `Aggregate` (`_1 = [0x0102, 0x0304, 0x0506]`).
  obtain ⟨hsim₂, hnd₂, him₂, -⟩ := step_stmt_lm2_1_simulation hrel₁ (hnd₁ rfl)
    lm21_mixed_phase rfl rfl (fun tf htf => by
      refine .arrayStmt (.aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inl ⟨himm₁_1 tf htf, hcanRes₁⟩)) ?_ lm21_isPrim_u16)
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact lm21_mixed_constU16_wt tf 0x0102 (by decide)
      · exact lm21_mixed_constU16_wt tf 0x0304 (by decide)
      · exact lm21_mixed_constU16_wt tf 0x0506 (by decide))
  rw [h₂] at hsim₂
  generalize hr₂ : Miri.Interpreter.Step.step hooks () m₁ = r₂ at hsim₂ hnd₂ him₂
  cases hsim₂ with
  | step _ m₂ hrel₂ =>
  have himm₂ : ∀ j, j ≠ 1 → ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj tf htf
    obtain ⟨tf₁, htf₁, _⟩ := hrel₁
    exact him₂ rfl tf₁ tf htf₁ htf j (fun h => hj (by injection h with h; exact h.symm))
      (himm₁_all j tf₁ htf₁)
  -- `stmt 2`: `LM-2.1` in-place `Repeat` overwrite (`_1 = [0x0708; 3]`, reusing `.indirect` `_1`).
  obtain ⟨hsim₃, hnd₃, him₃, -⟩ := step_stmt_lm2_1_simulation hrel₂ (hnd₂ rfl)
    lm21_mixed_phase rfl rfl (fun tf _ =>
      .arrayStmt (.repeatArray 1 lm21U16Arr3Decl (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 (Or.inr (Or.inr ⟨lm21ArrElems, rfl⟩))
        (lm21_mixed_constU16_wt tf 0x0708 (by decide)) lm21_isPrim_u16))
  rw [h₃] at hsim₃
  generalize hr₃ : Miri.Interpreter.Step.step hooks () m₂ = r₃ at hsim₃ hnd₃ him₃
  cases hsim₃ with
  | step _ m₃ hrel₃ =>
  have himm₃ : ∀ j, j ≠ 1 → ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj tf htf
    obtain ⟨tf₂, htf₂, _⟩ := hrel₂
    exact him₃ rfl tf₂ tf htf₂ htf j (fun h => hj (by injection h with h; exact h.symm))
      (himm₂ j hj tf₂ htf₂)
  -- `stmt 3`: `LM-2.1` in-place `Aggregate` overwrite (`_1 = [0x090A, 0x0B0C, 0x0D0E]`).
  obtain ⟨hsim₄, hnd₄, him₄, -⟩ := step_stmt_lm2_1_simulation hrel₃ (hnd₃ rfl)
    lm21_mixed_phase rfl rfl (fun tf _ => by
      refine .arrayStmt (.aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inr ⟨repElems, rfl⟩)) ?_ lm21_isPrim_u16)
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact lm21_mixed_constU16_wt tf 0x090A (by decide)
      · exact lm21_mixed_constU16_wt tf 0x0B0C (by decide)
      · exact lm21_mixed_constU16_wt tf 0x0D0E (by decide))
  rw [h₄] at hsim₄
  generalize hr₄ : Miri.Interpreter.Step.step hooks () m₃ = r₄ at hsim₄ hnd₄ him₄
  cases hsim₄ with
  | step _ m₄ hrel₄ =>
  have himm₄ : ∀ j, j ≠ 1 → ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj tf htf
    obtain ⟨tf₃, htf₃, _⟩ := hrel₃
    exact him₄ rfl tf₃ tf htf₃ htf j (fun h => hj (by injection h with h; exact h.symm))
      (himm₃ j hj tf₃ htf₃)
  -- `stmt 4`: `LM-1.1` scalar `Add` (`_2 = Add(const 1_usize, const 1_usize)` -> `2_usize`).
  have husize_int : IsIntegralTy lm21UsizeTy (translateUintTy .usize) := .uint .usize rfl
  obtain ⟨hsim₅, hnd₅, him₅, -⟩ := step_stmt_lm2_1_simulation hrel₄ (hnd₄ rfl)
    lm21_mixed_phase rfl rfl (fun tf htf =>
      .scalarStmt (.assign _ 2 lm21UsizeDecl _ rfl rfl (himm₄ 2 (by decide) tf htf)
        (.binaryOp .add _ _ lm21UsizeTy lm21UsizeTy lm21UsizeTy
          (lm21_mixed_constUsize_wt tf 1 (by decide))
          (lm21_mixed_constUsize_wt tf 1 (by decide))
          (.intArithOrBitwise .add lm21UsizeTy lm21UsizeTy lm21UsizeTy _
            (Or.inl rfl) husize_int husize_int husize_int))))
  rw [h₅] at hsim₅
  generalize hr₅ : Miri.Interpreter.Step.step hooks () m₄ = r₅ at hsim₅ hnd₅ him₅
  cases hsim₅ with
  | step _ m₅ hrel₅ =>
  have himm₅ : ∀ j, j ≠ 1 → ∀ tf, m₅.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj tf htf
    obtain ⟨tf₄, htf₄, _⟩ := hrel₄
    exact him₅ rfl tf₄ tf htf₄ htf j (fun h => nomatch h) (himm₄ j hj tf₄ htf₄)
  -- `stmt 5`: `LM-2.1` dynamic `Index` read (`_0 = copy _1[_2]` -> `0x0D0E_u16`).
  obtain ⟨hsim₆, hnd₆, -, -⟩ := step_stmt_lm2_1_simulation hrel₅ (hnd₅ rfl)
    lm21_mixed_phase rfl rfl (fun tf htf =>
      .arrayStmt (.elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.index 2) false _ rfl lm21_wf_u16Arr3 rfl rfl
        (himm₅ 0 (by decide) tf htf)
        (.index 2 lm21UsizeDecl rfl rfl (Or.inl (himm₅ 2 (by decide) tf htf)))
        (Or.inr (Or.inr ⟨newElems, rfl⟩)))))
  rw [h₆] at hsim₆
  generalize hr₆ : Miri.Interpreter.Step.step hooks () m₅ = r₆ at hsim₆ hnd₆
  cases hsim₆ with
  | step _ m₆ hrel₆ =>
  -- `stmt 6`: `LM-1.4` `StorageDead(1)` deallocating indirect `_1`.
  obtain ⟨hsim₇, hnd₇, -, -⟩ := step_stmt_lm2_1_simulation hrel₆ (hnd₆ rfl)
    lm21_mixed_phase rfl rfl
    (fun _ _ => .lm14Stmt (.storageDead 1 lm21U16Arr3Decl _ rfl (by decide)))
  rw [h₇] at hsim₇
  generalize hr₇ : Miri.Interpreter.Step.step hooks () m₆ = r₇ at hsim₇ hnd₇
  cases hsim₇ with
  | step _ m₇ hrel₇ =>
  exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, rfl, hr₂, hr₃, hr₄, hr₅, hr₆, hr₇, hrel₇, hnd₇ rfl⟩

/-! ## 10. Multi-Allocation, Reallocation & Destructive `Operand.move` Witnesses -/

def lm21U16Arr2Ty : Ty := { kind := .array (.uint .u16) 2, layoutIdx := 0 }
def lm21U16Arr2Decl : LocalDecl := { mutability := .mut, ty := lm21U16Arr2Ty, debugName := none }

theorem lm21_wf_u16Arr2 : WellTypedArrayTy emptyLayoutTable lm21U16Arr2Ty (.uint .u16) 2 :=
  ⟨rfl, Or.inr (Or.inr (Or.inr ⟨.u16, rfl⟩)), rfl, rfl, rfl, rfl, rfl,
    lm21_elemLayout_eq 2,
    show 0 < 2 by decide, show 2 ≤ 16 by decide, show 2 * 2 < 2 ^ 32 by decide, rfl⟩

/-- MIR body exercising:
- `bb 0` (12 statements): two simultaneous live array allocations (`_1 : [u16; 3]`
  and `_2 : [u16; 2]`), destructive `Operand.move` scalar operands in `Aggregate`
  (`[move _4, copy _5, const 0x7788]`), `Repeat` (`[move _5; 2]`), and `writeElem`
  (`_1[_3] = move _6`), followed by `StorageDead(1); StorageLive(1); _1 = [move _0; 3]`
  reallocation while `_2` remains live, with all three `CanReserveAllocId` obligations
  discharged purely from `StepPreservesHighWater` + `MemoryHighWater.canReserveAllocId`.
- `bb 1` (2 statements): double-move UB (`_1 = [move _4, copy _4, const 0x7788]`)
  reporting undefined behavior in both Anneal and `lean-miri`. -/
def lm21MultiMoveBody : CapturedMir where
  defPath := "lm_2_1_witness::multi_alloc_move"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    lm21U16Decl,      -- `_0 : u16`
    lm21U16Arr3Decl,  -- `_1 : [u16; 3]`
    lm21U16Arr2Decl,  -- `_2 : [u16; 2]`
    lm21UsizeDecl,    -- `_3 : usize`
    lm21U16Decl,      -- `_4 : u16`
    lm21U16Decl,      -- `_5 : u16`
    lm21U16Decl       -- `_6 : u16`
  ]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 4) (.use (.constant (lm21ConstU16 0x1122)))),
        mkStmt (.assign (local_ 5) (.use (.constant (lm21ConstU16 0x3344)))),
        mkStmt (.assign (local_ 6) (.use (.constant (lm21ConstU16 0x5566)))),
        mkStmt (.assign (local_ 3) (.use (.constant (lm21ConstUsize 1)))),
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.move (local_ 4), .copy (local_ 5), .constant (lm21ConstU16 0x7788)])),
        mkStmt (.assign (local_ 2) (.repeat (.move (local_ 5)) 2)),
        mkStmt (.assign ⟨1, [.index 3]⟩ (.use (.move (local_ 6)))),
        mkStmt (.storageDead 1),
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨2, [.constantIndex 1 2 true]⟩))),
        mkStmt (.assign (local_ 1) (.repeat (.move (local_ 0)) 3)),
        mkStmt (.assign (local_ 0) (.use (.move ⟨1, [.index 3]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 4) (.use (.constant (lm21ConstU16 0x1122)))),
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.move (local_ 4), .copy (local_ 4), .constant (lm21ConstU16 0x7788)]))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

theorem lm21_multiMove_phase : ∀ p, lm21MultiMoveBody.phase ≠ .other p := by
  intro p h; cases h

def lm21MultiInitAnneal (bbIdx : Nat) : MachineState :=
  { frame :=
      { blockIdx := bbIdx
        stmtIdx := 0
        locals := [.uninit, .uninit, .uninit, .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm21MultiMoveBody []).memory }

def lm21MultiInitMiriFrame (bbIdx : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21MultiMoveBody
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
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

def lm21MultiInitMiri (bbIdx : Nat) : AnnealStepState :=
  { stack := ⟨#[lm21MultiInitMiriFrame bbIdx]⟩, machine := AnnealMachine.empty }

theorem lm21_multi_init_stateRel (bbIdx : Nat) :
    StateRel lm21MultiMoveBody (lm21MultiInitAnneal bbIdx) (lm21MultiInitMiri bbIdx) := by
  refine StateRel.mk (lm21MultiInitMiriFrame bbIdx) rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rintro ⟨⟩
      | _ + 7 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 =>
    have hs : slot = .uninit := by simpa [lm21MultiInitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21MultiInitMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 7 =>
    simp [lm21MultiMoveBody, get?] at hdecl

private theorem lm21_multiInitFrame_imm (bbIdx j : Nat) :
    IsImmediateFrameLocal (lm21MultiInitMiriFrame bbIdx) j := by
  intro mls hmls mp hv
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 =>
    simp [lm21MultiInitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 7 => simp [lm21MultiInitMiriFrame] at hmls

private theorem lm21_multiInitFrame_eq {bbIdx : Nat}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm21MultiInitMiri bbIdx).stack.frames = #[tf]) :
    tf = lm21MultiInitMiriFrame bbIdx := by
  simp only [lm21MultiInitMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at h
  exact h.symm

private theorem lm21_multi_constU16_scalar_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 65536) :
    WellTypedScalarOperand lm21MultiMoveBody tf (.constant (lm21ConstU16 n)) lm21U16Ty :=
  .constScalar (lm21ConstU16 n) ⟨n, 2⟩ rfl lm21_isPrim_u16 (Or.inr (Or.inl rfl))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h)

private theorem lm21_multi_constUsize_scalar_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 2 ^ 64) :
    WellTypedScalarOperand lm21MultiMoveBody tf (.constant (lm21ConstUsize n)) lm21UsizeTy :=
  .constScalar (lm21ConstUsize n) ⟨n, 8⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h)

/-- Twelve-step execution chaining `step_stmt_lm2_1_simulation` across:
1. two simultaneous live array allocations (`_1 : [u16; 3]` and `_2 : [u16; 2]`),
2. destructive `Operand.move` scalar operands in `Aggregate`, `Repeat`, and `writeElem`
   (deinitializing `_4`, `_5`, and `_6` in lockstep), and
3. `StorageDead(1); StorageLive(1); _1 = [move _0; 3]` reallocation while `_2` stays live,
propagating `MemoryHighWater` across all 12 steps (`nextAllocId ≤ 4`) without ever
unfolding `m_k.machine.memory`. -/
theorem lm21_multi_alloc_move_chain_steps :
    let hooks := annealStepHooks lm21MultiMoveBody.localDecls lm21MultiMoveBody.layouts
    let arr1_init : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x7788, 2⟩]
    let arr2_init : List Value := [.scalar ⟨0x3344, 2⟩, .scalar ⟨0x3344, 2⟩]
    let arr1_upd  : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x5566, 2⟩, .scalar ⟨0x7788, 2⟩]
    let arr1_real : List Value := [.scalar ⟨0x3344, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x3344, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState lm21MultiMoveBody []).memory }
    let s₁ := mkState 1 [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .init (.scalar ⟨0x3344, 2⟩), .uninit]
    let s₃ := mkState 3 [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .init (.scalar ⟨0x3344, 2⟩), .init (.scalar ⟨0x5566, 2⟩)]
    let s₄ := mkState 4 [.uninit, .uninit, .uninit, .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨0x1122, 2⟩), .init (.scalar ⟨0x3344, 2⟩), .init (.scalar ⟨0x5566, 2⟩)]
    let s₅ := mkState 5 [.uninit, .init (.aggregate 0 arr1_init), .uninit, .init (.scalar ⟨1, 8⟩), .uninit, .init (.scalar ⟨0x3344, 2⟩), .init (.scalar ⟨0x5566, 2⟩)]
    let s₆ := mkState 6 [.uninit, .init (.aggregate 0 arr1_init), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .init (.scalar ⟨0x5566, 2⟩)]
    let s₇ := mkState 7 [.uninit, .init (.aggregate 0 arr1_upd), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₈ := mkState 8 [.uninit, .dead, .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₉ := mkState 9 [.uninit, .uninit, .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₁₀ := mkState 10 [.init (.scalar ⟨0x3344, 2⟩), .uninit, .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₁₁ := mkState 11 [.uninit, .init (.aggregate 0 arr1_real), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    let s₁₂ := mkState 12 [.init (.scalar ⟨0x3344, 2⟩), .init (.aggregate 0 arr1_real), .init (.aggregate 0 arr2_init), .init (.scalar ⟨1, 8⟩), .uninit, .uninit, .uninit]
    stepMirFn lm21MultiMoveBody (lm21MultiInitAnneal 0) = .step s₁ ∧
      stepMirFn lm21MultiMoveBody s₁ = .step s₂ ∧
      stepMirFn lm21MultiMoveBody s₂ = .step s₃ ∧
      stepMirFn lm21MultiMoveBody s₃ = .step s₄ ∧
      stepMirFn lm21MultiMoveBody s₄ = .step s₅ ∧
      stepMirFn lm21MultiMoveBody s₅ = .step s₆ ∧
      stepMirFn lm21MultiMoveBody s₆ = .step s₇ ∧
      stepMirFn lm21MultiMoveBody s₇ = .step s₈ ∧
      stepMirFn lm21MultiMoveBody s₈ = .step s₉ ∧
      stepMirFn lm21MultiMoveBody s₉ = .step s₁₀ ∧
      stepMirFn lm21MultiMoveBody s₁₀ = .step s₁₁ ∧
      stepMirFn lm21MultiMoveBody s₁₁ = .step s₁₂ ∧
      ∃ m₁ m₂ m₃ m₄ m₅ m₆ m₇ m₈ m₉ m₁₀ m₁₁ m₁₂,
        Miri.Interpreter.Step.step hooks () (lm21MultiInitMiri 0) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₆ = (m₇, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₇ = (m₈, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₈ = (m₉, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₉ = (m₁₀, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁₀ = (m₁₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁₁ = (m₁₂, .ok true) ∧
        StateRel lm21MultiMoveBody s₁₂ m₁₂ ∧
        LiveAllocsNodup m₁₂.machine ∧
        MemoryHighWater m₁₂.machine.memory ∧
        m₁₂.machine.memory.nextAllocId.toNat ≤ 4 := by
  intro hooks arr1_init arr2_init arr1_upd arr1_real mkState s₁ s₂ s₃ s₄ s₅ s₆ s₇ s₈ s₉ s₁₀ s₁₁ s₁₂
  have h₁ : stepMirFn lm21MultiMoveBody (lm21MultiInitAnneal 0) = .step s₁ := rfl
  have h₂ : stepMirFn lm21MultiMoveBody s₁ = .step s₂ := rfl
  have h₃ : stepMirFn lm21MultiMoveBody s₂ = .step s₃ := rfl
  have h₄ : stepMirFn lm21MultiMoveBody s₃ = .step s₄ := rfl
  have h₅ : stepMirFn lm21MultiMoveBody s₄ = .step s₅ := rfl
  have h₆ : stepMirFn lm21MultiMoveBody s₅ = .step s₆ := rfl
  have h₇ : stepMirFn lm21MultiMoveBody s₆ = .step s₇ := rfl
  have h₈ : stepMirFn lm21MultiMoveBody s₇ = .step s₈ := rfl
  have h₉ : stepMirFn lm21MultiMoveBody s₈ = .step s₉ := rfl
  have h₁₀ : stepMirFn lm21MultiMoveBody s₉ = .step s₁₀ := rfl
  have h₁₁ : stepMirFn lm21MultiMoveBody s₁₀ = .step s₁₁ := rfl
  have h₁₂ : stepMirFn lm21MultiMoveBody s₁₁ = .step s₁₂ := rfl
  refine ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, ?_⟩
  have h0_next : (lm21MultiInitMiri 0).machine.memory.nextAllocId.toNat = 1 := rfl
  -- `stmt 0`: `_4 = const 0x1122_u16`
  obtain ⟨hsim₁, hnd₁, him₁, hhw₁⟩ := step_stmt_lm2_1_simulation (lm21_multi_init_stateRel 0)
    lm21_nodup_empty lm21_multiMove_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_multiInitFrame_eq htf
      exact .scalarStmt (.assign _ 4 lm21U16Decl _ rfl rfl (lm21_multiInitFrame_imm 0 4)
        (.use _ lm21U16Ty (lm21_multi_constU16_scalar_wt _ 0x1122 (by decide)))))
  rw [h₁] at hsim₁
  generalize Miri.Interpreter.Step.step hooks () (lm21MultiInitMiri 0) = r₁
    at hsim₁ hnd₁ him₁ hhw₁ ⊢
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
  have himm₁ : ∀ j, ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf j :=
    fun j tf htf => him₁ rfl _ tf rfl htf j (fun h => nomatch h) (lm21_multiInitFrame_imm 0 j)
  obtain ⟨hw₁, hb₁⟩ := hhw₁ rfl MemoryHighWater.empty (by decide)
  rw [h0_next] at hb₁
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₁
  -- `stmt 1`: `_5 = const 0x3344_u16`
  obtain ⟨hsim₂, hnd₂, him₂, hhw₂⟩ := step_stmt_lm2_1_simulation hrel₁ (hnd₁ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .scalarStmt (.assign _ 5 lm21U16Decl _ rfl rfl (himm₁ 5 tf htf)
        (.use _ lm21U16Ty (lm21_multi_constU16_scalar_wt tf 0x3344 (by decide)))))
  rw [h₂] at hsim₂
  generalize hr₂ : Miri.Interpreter.Step.step hooks () m₁ = r₂ at hsim₂ hnd₂ him₂ hhw₂
  cases hsim₂ with
  | step _ m₂ hrel₂ =>
  have himm₂ : ∀ j, ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j tf htf; obtain ⟨tf₁, htf₁, _⟩ := hrel₁
    exact him₂ rfl tf₁ tf htf₁ htf j (fun h => nomatch h) (himm₁ j tf₁ htf₁)
  obtain ⟨hw₂, hb₂⟩ := hhw₂ rfl hw₁ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₂
  -- `stmt 2`: `_6 = const 0x5566_u16`
  obtain ⟨hsim₃, hnd₃, him₃, hhw₃⟩ := step_stmt_lm2_1_simulation hrel₂ (hnd₂ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .scalarStmt (.assign _ 6 lm21U16Decl _ rfl rfl (himm₂ 6 tf htf)
        (.use _ lm21U16Ty (lm21_multi_constU16_scalar_wt tf 0x5566 (by decide)))))
  rw [h₃] at hsim₃
  generalize hr₃ : Miri.Interpreter.Step.step hooks () m₂ = r₃ at hsim₃ hnd₃ him₃ hhw₃
  cases hsim₃ with
  | step _ m₃ hrel₃ =>
  have himm₃ : ∀ j, ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j tf htf; obtain ⟨tf₂, htf₂, _⟩ := hrel₂
    exact him₃ rfl tf₂ tf htf₂ htf j (fun h => nomatch h) (himm₂ j tf₂ htf₂)
  obtain ⟨hw₃, hb₃⟩ := hhw₃ rfl hw₂ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₃
  -- `stmt 3`: `_3 = const 1_usize`
  obtain ⟨hsim₄, hnd₄, him₄, hhw₄⟩ := step_stmt_lm2_1_simulation hrel₃ (hnd₃ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .scalarStmt (.assign _ 3 lm21UsizeDecl _ rfl rfl (himm₃ 3 tf htf)
        (.use _ lm21UsizeTy (lm21_multi_constUsize_scalar_wt tf 1 (by decide)))))
  rw [h₄] at hsim₄
  generalize hr₄ : Miri.Interpreter.Step.step hooks () m₃ = r₄ at hsim₄ hnd₄ him₄ hhw₄
  cases hsim₄ with
  | step _ m₄ hrel₄ =>
  have himm₄ : ∀ j, ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j tf htf; obtain ⟨tf₃, htf₃, _⟩ := hrel₃
    exact him₄ rfl tf₃ tf htf₃ htf j (fun h => nomatch h) (himm₃ j tf₃ htf₃)
  obtain ⟨hw₄, hb₄⟩ := hhw₄ rfl hw₃ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₄
  -- `stmt 4`: `_1 = [move _4, copy _5, const 0x7788_u16]` (fresh allocation #1 + destructive move `_4`)
  obtain ⟨hsim₅, hnd₅, him₅, hhw₅⟩ := step_stmt_lm2_1_simulation hrel₄ (hnd₄ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf => by
      refine .arrayStmt (.aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inl ⟨himm₄ 1 tf htf, hw₄.canReserveAllocId⟩)) ?_ lm21_isPrim_u16)
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact .moveLocal 4 lm21U16Decl rfl lm21_isPrim_u16 (himm₄ 4 tf htf)
      · exact .ofScalar (.copyLocal 5 lm21U16Decl rfl (by decide) (himm₄ 5 tf htf))
      · exact .ofScalar (lm21_multi_constU16_scalar_wt tf 0x7788 (by decide)))
  rw [h₅] at hsim₅
  generalize hr₅ : Miri.Interpreter.Step.step hooks () m₄ = r₅ at hsim₅ hnd₅ him₅ hhw₅
  cases hsim₅ with
  | step _ m₅ hrel₅ =>
  have himm₅ : ∀ j, j ≠ 1 → ∀ tf, m₅.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj tf htf; obtain ⟨tf₄, htf₄, _⟩ := hrel₄
    exact him₅ rfl tf₄ tf htf₄ htf j (fun h => hj (by injection h with h; exact h.symm))
      (himm₄ j tf₄ htf₄)
  obtain ⟨hw₅, hb₅⟩ := hhw₅ rfl hw₄ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte] at hb₅
  -- `stmt 5`: `_2 = [move _5; 2]` (simultaneous fresh allocation #2 + destructive move `_5`)
  obtain ⟨hsim₆, hnd₆, him₆, hhw₆⟩ := step_stmt_lm2_1_simulation hrel₅ (hnd₅ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .arrayStmt (.repeatArray 2 lm21U16Arr2Decl (.uint .u16) 2 _ _
        rfl lm21_wf_u16Arr2 (Or.inr (Or.inl ⟨himm₅ 2 (by decide) tf htf, hw₅.canReserveAllocId⟩))
        (.moveLocal 5 lm21U16Decl rfl lm21_isPrim_u16 (himm₅ 5 (by decide) tf htf))
        lm21_isPrim_u16))
  rw [h₆] at hsim₆
  generalize hr₆ : Miri.Interpreter.Step.step hooks () m₅ = r₆ at hsim₆ hnd₆ him₆ hhw₆
  cases hsim₆ with
  | step _ m₆ hrel₆ =>
  have himm₆ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₆.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₅, htf₅, _⟩ := hrel₅
    exact him₆ rfl tf₅ tf htf₅ htf j (fun h => hj₂ (by injection h with h; exact h.symm))
      (himm₅ j hj₁ tf₅ htf₅)
  obtain ⟨hw₆, hb₆⟩ := hhw₆ rfl hw₅ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte] at hb₆
  -- `stmt 6`: `_1[_3] = move _6` (dynamic `Index` write with destructive move `_6`)
  obtain ⟨hsim₇, hnd₇, him₇, hhw₇⟩ := step_stmt_lm2_1_simulation hrel₆ (hnd₆ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .arrayStmt (.elemAssign (.writeElem 1 lm21U16Arr3Decl (.uint .u16) 3 (.index 3)
        (.move (local_ 6)) _ rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.index 3 lm21UsizeDecl rfl rfl (Or.inl (himm₆ 3 (by decide) (by decide) tf htf)))
        (.moveLocal 6 lm21U16Decl rfl lm21_isPrim_u16 (himm₆ 6 (by decide) (by decide) tf htf))
        (by intro idxLocal hm; simp [movedScalarLocal?, local_] at hm; subst hm; exact fun h => nomatch h)
        (Or.inr (Or.inr ⟨arr1_init, rfl⟩)))))
  rw [h₇] at hsim₇
  generalize hr₇ : Miri.Interpreter.Step.step hooks () m₆ = r₇ at hsim₇ hnd₇ him₇ hhw₇
  cases hsim₇ with
  | step _ m₇ hrel₇ =>
  have himm₇ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₇.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₆, htf₆, _⟩ := hrel₆
    exact him₇ rfl tf₆ tf htf₆ htf j (fun h => nomatch h) (himm₆ j hj₁ hj₂ tf₆ htf₆)
  obtain ⟨hw₇, hb₇⟩ := hhw₇ rfl hw₆ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₇
  -- `stmt 7`: `StorageDead(1)` (deallocates `_1` while `_2` stays live)
  obtain ⟨hsim₈, hnd₈, him₈, hhw₈⟩ := step_stmt_lm2_1_simulation hrel₇ (hnd₇ rfl)
    lm21_multiMove_phase rfl rfl
    (fun _ _ => .lm14Stmt (.storageDead 1 lm21U16Arr3Decl _ rfl (by decide)))
  rw [h₈] at hsim₈
  generalize hr₈ : Miri.Interpreter.Step.step hooks () m₇ = r₈ at hsim₈ hnd₈ him₈ hhw₈
  cases hsim₈ with
  | step _ m₈ hrel₈ =>
  have himm₈ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₈.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₇, htf₇, _⟩ := hrel₇
    exact him₈ rfl tf₇ tf htf₇ htf j (fun h => nomatch h) (himm₇ j hj₁ hj₂ tf₇ htf₇)
  obtain ⟨hw₈, hb₈⟩ := hhw₈ rfl hw₇ (by
    simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₈
  -- `stmt 8`: `StorageLive(1)` (re-establishes `_1` as `.uninit` immediate)
  have hsl_imm := fun tf' htf' =>
    step_storageLive_establishes_immediate hrel₈
      (loc := 1) (decl := lm21U16Arr3Decl) rfl rfl rfl (tf' := tf') htf'
  obtain ⟨hsim₉, hnd₉, him₉, hhw₉⟩ := step_stmt_lm2_1_simulation hrel₈ (hnd₈ rfl)
    lm21_multiMove_phase rfl rfl
    (fun _ _ => .lm14Stmt (.storageLive 1 lm21U16Arr3Decl _ rfl))
  rw [h₉] at hsim₉
  generalize hr₉ : Miri.Interpreter.Step.step hooks () m₈ = r₉ at hsim₉ hnd₉ him₉ hhw₉ hsl_imm
  cases hsim₉ with
  | step _ m₉ hrel₉ =>
  have himm₉ : ∀ j, j ≠ 2 → ∀ tf, m₉.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₂ tf htf
    by_cases hj₁ : j = 1
    · subst hj₁; exact hsl_imm tf htf
    · obtain ⟨tf₈, htf₈, _⟩ := hrel₈
      exact him₉ rfl tf₈ tf htf₈ htf j (fun h => nomatch h) (himm₈ j hj₁ hj₂ tf₈ htf₈)
  obtain ⟨hw₉, hb₉⟩ := hhw₉ rfl hw₈ (by
    simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₉
  -- `stmt 9`: `_0 = copy _2[-1 of 2]` (reads `0x3344_u16` from still-live `_2`)
  obtain ⟨hsim₁₀, hnd₁₀, him₁₀, hhw₁₀⟩ := step_stmt_lm2_1_simulation hrel₉ (hnd₉ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .arrayStmt (.elemAssign (.readElem 0 2 lm21U16Decl lm21U16Arr2Decl (.uint .u16) 2
        (.constantIndex 1 2 true) false _ rfl lm21_wf_u16Arr2 rfl rfl
        (himm₉ 0 (by decide) tf htf)
        (.constantIndex 1 2 true (by decide) (by decide)
          ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
        (Or.inr (Or.inr ⟨arr2_init, rfl⟩)))))
  rw [h₁₀] at hsim₁₀
  generalize hr₁₀ : Miri.Interpreter.Step.step hooks () m₉ = r₁₀ at hsim₁₀ hnd₁₀ him₁₀ hhw₁₀
  cases hsim₁₀ with
  | step _ m₁₀ hrel₁₀ =>
  have himm₁₀ : ∀ j, j ≠ 2 → ∀ tf, m₁₀.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₂ tf htf; obtain ⟨tf₉, htf₉, _⟩ := hrel₉
    exact him₁₀ rfl tf₉ tf htf₉ htf j (fun h => nomatch h) (himm₉ j hj₂ tf₉ htf₉)
  obtain ⟨hw₁₀, hb₁₀⟩ := hhw₁₀ rfl hw₉ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₁₀
  -- `stmt 10`: `_1 = [move _0; 3]` (reallocation #3 of `_1` + destructive move `_0`)
  obtain ⟨hsim₁₁, hnd₁₁, him₁₁, hhw₁₁⟩ := step_stmt_lm2_1_simulation hrel₁₀ (hnd₁₀ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .arrayStmt (.repeatArray 1 lm21U16Arr3Decl (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 (Or.inr (Or.inl ⟨himm₁₀ 1 (by decide) tf htf, hw₁₀.canReserveAllocId⟩))
        (.moveLocal 0 lm21U16Decl rfl lm21_isPrim_u16 (himm₁₀ 0 (by decide) tf htf))
        lm21_isPrim_u16))
  rw [h₁₁] at hsim₁₁
  generalize hr₁₁ : Miri.Interpreter.Step.step hooks () m₁₀ = r₁₁ at hsim₁₁ hnd₁₁ him₁₁ hhw₁₁
  cases hsim₁₁ with
  | step _ m₁₁ hrel₁₁ =>
  have himm₁₁ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₁₁.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₁₀, htf₁₀, _⟩ := hrel₁₀
    exact him₁₁ rfl tf₁₀ tf htf₁₀ htf j (fun h => hj₁ (by injection h with h; exact h.symm))
      (himm₁₀ j hj₂ tf₁₀ htf₁₀)
  obtain ⟨hw₁₁, hb₁₁⟩ := hhw₁₁ rfl hw₁₀ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte] at hb₁₁
  -- `stmt 11`: `_0 = move _1[_3]` (reads `0x3344_u16` from reallocated `_1`)
  obtain ⟨hsim₁₂, hnd₁₂, -, hhw₁₂⟩ := step_stmt_lm2_1_simulation hrel₁₁ (hnd₁₁ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf =>
      .arrayStmt (.elemAssign (.readElem 0 1 lm21U16Decl lm21U16Arr3Decl (.uint .u16) 3
        (.index 3) true _ rfl lm21_wf_u16Arr3 rfl rfl
        (himm₁₁ 0 (by decide) (by decide) tf htf)
        (.index 3 lm21UsizeDecl rfl rfl (Or.inl (himm₁₁ 3 (by decide) (by decide) tf htf)))
        (Or.inr (Or.inr ⟨arr1_real, rfl⟩)))))
  rw [h₁₂] at hsim₁₂
  generalize hr₁₂ : Miri.Interpreter.Step.step hooks () m₁₁ = r₁₂ at hsim₁₂ hnd₁₂ hhw₁₂
  cases hsim₁₂ with
  | step _ m₁₂ hrel₁₂ =>
  obtain ⟨hw₁₂, hb₁₂⟩ := hhw₁₂ rfl hw₁₁ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₁₂
  exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, m₇, m₈, m₉, m₁₀, m₁₁, m₁₂,
    rfl, hr₂, hr₃, hr₄, hr₅, hr₆, hr₇, hr₈, hr₉, hr₁₀, hr₁₁, hr₁₂,
    hrel₁₂, hnd₁₂ rfl, hw₁₂, by omega⟩

/-- Double-move UB witness (`bb 1`): after initializing `_4 = const 0x1122_u16`,
evaluating `_1 = [move _4, copy _4, const 0x7788_u16]` deinitializes `_4` on the first
operand and hits uninitialized-local UB on the second operand in both Anneal and
`lean-miri`. -/
theorem lm21_aggregate_move_then_copy_ub :
    let hooks := annealStepHooks lm21MultiMoveBody.localDecls lm21MultiMoveBody.layouts
    let s₁ : MachineState :=
      { frame :=
          { blockIdx := 1
            stmtIdx := 1
            locals := [.uninit, .uninit, .uninit, .uninit, .init (.scalar ⟨0x1122, 2⟩), .uninit, .uninit] }
        memory := (initMachineState lm21MultiMoveBody []).memory }
    stepMirFn lm21MultiMoveBody (lm21MultiInitAnneal 1) = .step s₁ ∧
      stepMirFn lm21MultiMoveBody s₁ = .fail .ub ∧
      ∃ m₁ m₂ msg,
        Miri.Interpreter.Step.step hooks () (lm21MultiInitMiri 1) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .error (.undefinedBehavior msg)) := by
  intro hooks s₁
  have h₁ : stepMirFn lm21MultiMoveBody (lm21MultiInitAnneal 1) = .step s₁ := rfl
  have h₂ : stepMirFn lm21MultiMoveBody s₁ = .fail .ub := rfl
  refine ⟨h₁, h₂, ?_⟩
  obtain ⟨hsim₁, hnd₁, him₁, hhw₁⟩ := step_stmt_lm2_1_simulation (lm21_multi_init_stateRel 1)
    lm21_nodup_empty lm21_multiMove_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_multiInitFrame_eq htf
      exact .scalarStmt (.assign _ 4 lm21U16Decl _ rfl rfl (lm21_multiInitFrame_imm 1 4)
        (.use _ lm21U16Ty (lm21_multi_constU16_scalar_wt _ 0x1122 (by decide)))))
  rw [h₁] at hsim₁
  generalize Miri.Interpreter.Step.step hooks () (lm21MultiInitMiri 1) = r₁
    at hsim₁ hnd₁ him₁ hhw₁ ⊢
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
  have himm₁ : ∀ j, ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf j :=
    fun j tf htf => him₁ rfl _ tf rfl htf j (fun h => nomatch h) (lm21_multiInitFrame_imm 1 j)
  obtain ⟨hw₁, _⟩ := hhw₁ rfl MemoryHighWater.empty (by decide)
  obtain ⟨hsim₂, -, -, -⟩ := step_stmt_lm2_1_simulation hrel₁ (hnd₁ rfl)
    lm21_multiMove_phase rfl rfl (fun tf htf => by
      refine .arrayStmt (.aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inl ⟨himm₁ 1 tf htf, hw₁.canReserveAllocId⟩)) ?_ lm21_isPrim_u16)
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact .moveLocal 4 lm21U16Decl rfl lm21_isPrim_u16 (himm₁ 4 tf htf)
      · exact .ofScalar (.copyLocal 4 lm21U16Decl rfl (by decide) (himm₁ 4 tf htf))
      · exact .ofScalar (lm21_multi_constU16_scalar_wt tf 0x7788 (by decide)))
  rw [h₂] at hsim₂
  generalize hr₂ : Miri.Interpreter.Step.step hooks () m₁ = r₂ at hsim₂
  cases hsim₂ with
  | ub m₂ msg =>
    exact ⟨m₁, m₂, msg, rfl, hr₂⟩

/-! ## 11. Uninitialized Indirect `[u16; 0]` UB, Direct Element Copy/Move (`copyElem`), & Malformed `ConstantIndex` Witnesses -/

/-- MIR body exercising:
- `bb 0` (6 statements): intra-array element copy (`_1[2 of 3] = copy _1[0 of 3]`)
  and inter-array element move (`_2[_3] = move _1[-1 of 3]`) via
  `WellTypedArrayElemAssign.copyElem`, followed by readback (`_0 = copy _2[_3]`).
- `bb 1` (3 statements): `copyElem` source-OOB UB (`_2[0 of 2] = copy _1[0 of 4]`)
  when the destination element place is valid and in bounds.
- `bb 2` (2 statements): element read (`_0 = copy _4[_3]`) and element write
  (`_4[0 of 1] = const 0x090A_u16`) on an uninitialized memory-backed zero-length
  array `_4 : [u16; 0]`, where `annealCheckIndirectInitialized` returns `.ok ()`
  because `Size.ZERO` spans `0` bytes yet both machines still agree on UB. -/
def lm21CopyZeroBody : CapturedMir where
  defPath := "lm_2_1_witness::copy_elem_and_zero_arr"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    lm21U16Decl,      -- `_0 : u16`
    lm21U16Arr3Decl,  -- `_1 : [u16; 3]`
    lm21U16Arr2Decl,  -- `_2 : [u16; 2]`
    lm21UsizeDecl,    -- `_3 : usize`
    lm21U16Arr0Decl   -- `_4 : [u16; 0]`
  ]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.constant (lm21ConstU16 0x1122), .constant (lm21ConstU16 0x3344),
           .constant (lm21ConstU16 0x5566)])),
        mkStmt (.assign (local_ 2) (.repeat (.constant (lm21ConstU16 0x7788)) 2)),
        mkStmt (.assign (local_ 3) (.use (.constant (lm21ConstUsize 1)))),
        mkStmt (.assign ⟨1, [.constantIndex 2 3 false]⟩
          (.use (.copy ⟨1, [.constantIndex 0 3 false]⟩))),
        mkStmt (.assign ⟨2, [.index 3]⟩
          (.use (.move ⟨1, [.constantIndex 1 3 true]⟩))),
        mkStmt (.assign (local_ 0) (.use (.copy ⟨2, [.index 3]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21U16Ty)
          [.constant (lm21ConstU16 0x1122), .constant (lm21ConstU16 0x3344),
           .constant (lm21ConstU16 0x5566)])),
        mkStmt (.assign (local_ 2) (.repeat (.constant (lm21ConstU16 0x7788)) 2)),
        mkStmt (.assign ⟨2, [.constantIndex 0 2 false]⟩
          (.use (.copy ⟨1, [.constantIndex 0 4 false]⟩)))],
      terminator := mkTerm .return_, isCleanup := false },
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy ⟨4, [.index 3]⟩))),
        mkStmt (.assign ⟨4, [.constantIndex 0 1 false]⟩
          (.use (.constant (lm21ConstU16 0x090A))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

theorem lm21_copyZero_phase : ∀ p, lm21CopyZeroBody.phase ≠ .other p := by
  intro p h; cases h

def lm21CopyZeroInitAnneal (bbIdx : Nat) : MachineState :=
  { frame :=
      { blockIdx := bbIdx
        stmtIdx := 0
        locals := [.uninit, .uninit, .uninit, .uninit, .uninit] }
    memory := (initMachineState lm21CopyZeroBody []).memory }

def lm21CopyZeroInitMiriFrame (bbIdx : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21CopyZeroBody
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
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨bbIdx, 0⟩ }

def lm21CopyZeroInitMiri (bbIdx : Nat) : AnnealStepState :=
  { stack := ⟨#[lm21CopyZeroInitMiriFrame bbIdx]⟩, machine := AnnealMachine.empty }

theorem lm21_copyZero_init_stateRel (bbIdx : Nat) :
    StateRel lm21CopyZeroBody (lm21CopyZeroInitAnneal bbIdx) (lm21CopyZeroInitMiri bbIdx) := by
  refine StateRel.mk (lm21CopyZeroInitMiriFrame bbIdx) rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 => rintro ⟨⟩
      | _ + 5 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 | 3 | 4 =>
    have hs : slot = .uninit := by simpa [lm21CopyZeroInitAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21CopyZeroInitMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | _ + 5 =>
    simp [lm21CopyZeroBody, get?] at hdecl

private theorem lm21_copyZeroInitFrame_imm (bbIdx j : Nat) :
    IsImmediateFrameLocal (lm21CopyZeroInitMiriFrame bbIdx) j := by
  intro mls hmls mp hv
  match j with
  | 0 | 1 | 2 | 3 | 4 =>
    simp [lm21CopyZeroInitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 5 => simp [lm21CopyZeroInitMiriFrame] at hmls

private theorem lm21_copyZeroInitFrame_eq {bbIdx : Nat}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm21CopyZeroInitMiri bbIdx).stack.frames = #[tf]) :
    tf = lm21CopyZeroInitMiriFrame bbIdx := by
  simp only [lm21CopyZeroInitMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at h
  exact h.symm

private theorem lm21_copyZero_constU16_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 65536) :
    WellTypedLM2_1ScalarOperand lm21CopyZeroBody tf (.constant (lm21ConstU16 n)) lm21U16Ty :=
  .ofScalar (.constScalar (lm21ConstU16 n) ⟨n, 2⟩ rfl lm21_isPrim_u16 (Or.inr (Or.inl rfl))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h))

private theorem lm21_copyZero_constUsize_scalar_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 2 ^ 64) :
    WellTypedScalarOperand lm21CopyZeroBody tf (.constant (lm21ConstUsize n)) lm21UsizeTy :=
  .constScalar (lm21ConstUsize n) ⟨n, 8⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h)

/-- Six-step execution exercising `WellTypedArrayElemAssign.copyElem` for both
intra-array (`_1[2 of 3] = copy _1[0 of 3]`, `dstArr = srcArr = 1`) and
inter-array (`_2[_3] = move _1[-1 of 3]`, `dstArr = 2, srcArr = 1`), followed
by dynamic `Index` readback (`_0 = copy _2[_3]` -> `0x1122_u16`), preserving
`StateRel`, `LiveAllocsNodup`, and `MemoryHighWater` across all 6 steps. -/
theorem lm21_intra_and_inter_array_copyElem_steps :
    let hooks := annealStepHooks lm21CopyZeroBody.localDecls lm21CopyZeroBody.layouts
    let arr1_0 : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x5566, 2⟩]
    let arr2_0 : List Value := [.scalar ⟨0x7788, 2⟩, .scalar ⟨0x7788, 2⟩]
    let arr1_1 : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x1122, 2⟩]
    let arr2_1 : List Value := [.scalar ⟨0x7788, 2⟩, .scalar ⟨0x1122, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 0, stmtIdx := k, locals := locals }
        memory := (initMachineState lm21CopyZeroBody []).memory }
    let s₁ := mkState 1 [.uninit, .init (.aggregate 0 arr1_0), .uninit, .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .init (.aggregate 0 arr1_0), .init (.aggregate 0 arr2_0), .uninit, .uninit]
    let s₃ := mkState 3 [.uninit, .init (.aggregate 0 arr1_0), .init (.aggregate 0 arr2_0), .init (.scalar ⟨1, 8⟩), .uninit]
    let s₄ := mkState 4 [.uninit, .init (.aggregate 0 arr1_1), .init (.aggregate 0 arr2_0), .init (.scalar ⟨1, 8⟩), .uninit]
    let s₅ := mkState 5 [.uninit, .init (.aggregate 0 arr1_1), .init (.aggregate 0 arr2_1), .init (.scalar ⟨1, 8⟩), .uninit]
    let s₆ := mkState 6 [.init (.scalar ⟨0x1122, 2⟩), .init (.aggregate 0 arr1_1), .init (.aggregate 0 arr2_1), .init (.scalar ⟨1, 8⟩), .uninit]
    stepMirFn lm21CopyZeroBody (lm21CopyZeroInitAnneal 0) = .step s₁ ∧
      stepMirFn lm21CopyZeroBody s₁ = .step s₂ ∧
      stepMirFn lm21CopyZeroBody s₂ = .step s₃ ∧
      stepMirFn lm21CopyZeroBody s₃ = .step s₄ ∧
      stepMirFn lm21CopyZeroBody s₄ = .step s₅ ∧
      stepMirFn lm21CopyZeroBody s₅ = .step s₆ ∧
      ∃ m₁ m₂ m₃ m₄ m₅ m₆,
        Miri.Interpreter.Step.step hooks () (lm21CopyZeroInitMiri 0) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₃ = (m₄, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₄ = (m₅, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₅ = (m₆, .ok true) ∧
        StateRel lm21CopyZeroBody s₆ m₆ ∧
        LiveAllocsNodup m₆.machine ∧
        MemoryHighWater m₆.machine.memory := by
  intro hooks arr1_0 arr2_0 arr1_1 arr2_1 mkState s₁ s₂ s₃ s₄ s₅ s₆
  have h₁ : stepMirFn lm21CopyZeroBody (lm21CopyZeroInitAnneal 0) = .step s₁ := rfl
  have h₂ : stepMirFn lm21CopyZeroBody s₁ = .step s₂ := rfl
  have h₃ : stepMirFn lm21CopyZeroBody s₂ = .step s₃ := rfl
  have h₄ : stepMirFn lm21CopyZeroBody s₃ = .step s₄ := rfl
  have h₅ : stepMirFn lm21CopyZeroBody s₄ = .step s₅ := rfl
  have h₆ : stepMirFn lm21CopyZeroBody s₅ = .step s₆ := rfl
  refine ⟨h₁, h₂, h₃, h₄, h₅, h₆, ?_⟩
  have h0_next : (lm21CopyZeroInitMiri 0).machine.memory.nextAllocId.toNat = 1 := rfl
  -- `stmt 0`: `_1 = [0x1122, 0x3344, 0x5566]`
  obtain ⟨hsim₁, hnd₁, him₁, hhw₁⟩ := step_stmt_lm2_1_simulation (lm21_copyZero_init_stateRel 0)
    lm21_nodup_empty lm21_copyZero_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_copyZeroInitFrame_eq htf
      refine .arrayStmt (.aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inl ⟨lm21_copyZeroInitFrame_imm 0 1, lm21_canReserve_empty⟩))
        ?_ lm21_isPrim_u16)
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact lm21_copyZero_constU16_wt _ 0x1122 (by decide)
      · exact lm21_copyZero_constU16_wt _ 0x3344 (by decide)
      · exact lm21_copyZero_constU16_wt _ 0x5566 (by decide))
  rw [h₁] at hsim₁
  generalize Miri.Interpreter.Step.step hooks () (lm21CopyZeroInitMiri 0) = r₁
    at hsim₁ hnd₁ him₁ hhw₁ ⊢
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
  have himm₁ : ∀ j, j ≠ 1 → ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf j :=
    fun j hj tf htf => him₁ rfl _ tf rfl htf j (fun h => hj (by injection h with h; exact h.symm))
      (lm21_copyZeroInitFrame_imm 0 j)
  obtain ⟨hw₁, hb₁⟩ := hhw₁ rfl MemoryHighWater.empty (by decide)
  rw [h0_next] at hb₁
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte] at hb₁
  -- `stmt 1`: `_2 = [0x7788; 2]`
  obtain ⟨hsim₂, hnd₂, him₂, hhw₂⟩ := step_stmt_lm2_1_simulation hrel₁ (hnd₁ rfl)
    lm21_copyZero_phase rfl rfl (fun tf htf =>
      .arrayStmt (.repeatArray 2 lm21U16Arr2Decl (.uint .u16) 2 _ _
        rfl lm21_wf_u16Arr2 (Or.inr (Or.inl ⟨himm₁ 2 (by decide) tf htf, hw₁.canReserveAllocId⟩))
        (lm21_copyZero_constU16_wt tf 0x7788 (by decide)) lm21_isPrim_u16))
  rw [h₂] at hsim₂
  generalize hr₂ : Miri.Interpreter.Step.step hooks () m₁ = r₂ at hsim₂ hnd₂ him₂ hhw₂
  cases hsim₂ with
  | step _ m₂ hrel₂ =>
  have himm₂ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₂.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₁, htf₁, _⟩ := hrel₁
    exact him₂ rfl tf₁ tf htf₁ htf j (fun h => hj₂ (by injection h with h; exact h.symm))
      (himm₁ j hj₁ tf₁ htf₁)
  obtain ⟨hw₂, hb₂⟩ := hhw₂ rfl hw₁ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, ↓reduceIte] at hb₂
  -- `stmt 2`: `_3 = const 1_usize`
  obtain ⟨hsim₃, hnd₃, him₃, hhw₃⟩ := step_stmt_lm2_1_simulation hrel₂ (hnd₂ rfl)
    lm21_copyZero_phase rfl rfl (fun tf htf =>
      .scalarStmt (.assign _ 3 lm21UsizeDecl _ rfl rfl (himm₂ 3 (by decide) (by decide) tf htf)
        (.use _ lm21UsizeTy (lm21_copyZero_constUsize_scalar_wt tf 1 (by decide)))))
  rw [h₃] at hsim₃
  generalize hr₃ : Miri.Interpreter.Step.step hooks () m₂ = r₃ at hsim₃ hnd₃ him₃ hhw₃
  cases hsim₃ with
  | step _ m₃ hrel₃ =>
  have himm₃ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₃.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₂, htf₂, _⟩ := hrel₂
    exact him₃ rfl tf₂ tf htf₂ htf j (fun h => nomatch h) (himm₂ j hj₁ hj₂ tf₂ htf₂)
  obtain ⟨hw₃, hb₃⟩ := hhw₃ rfl hw₂ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₃
  -- `stmt 3`: intra-array `_1[2 of 3] = copy _1[0 of 3]` (`copyElem`, `dstArr = srcArr = 1`)
  obtain ⟨hsim₄, hnd₄, him₄, hhw₄⟩ := step_stmt_lm2_1_simulation hrel₃ (hnd₃ rfl)
    lm21_copyZero_phase rfl rfl (fun _ _ =>
      .arrayStmt (.elemAssign (.copyElem 1 1 lm21U16Arr3Decl lm21U16Arr3Decl (.uint .u16) 3 3
        (.constantIndex 2 3 false) (.constantIndex 0 3 false) false _
        rfl lm21_wf_u16Arr3 rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.constantIndex 2 3 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (.constantIndex 0 3 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (Or.inr (Or.inr ⟨arr1_0, rfl⟩))
        (Or.inr (Or.inr ⟨arr1_0, rfl⟩)))))
  rw [h₄] at hsim₄
  generalize hr₄ : Miri.Interpreter.Step.step hooks () m₃ = r₄ at hsim₄ hnd₄ him₄ hhw₄
  cases hsim₄ with
  | step _ m₄ hrel₄ =>
  have himm₄ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₄.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₃, htf₃, _⟩ := hrel₃
    exact him₄ rfl tf₃ tf htf₃ htf j (fun h => nomatch h) (himm₃ j hj₁ hj₂ tf₃ htf₃)
  obtain ⟨hw₄, hb₄⟩ := hhw₄ rfl hw₃ (by
    simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₄
  -- `stmt 4`: inter-array `_2[_3] = move _1[-1 of 3]` (`copyElem`, `dstArr = 2, srcArr = 1`)
  obtain ⟨hsim₅, hnd₅, him₅, hhw₅⟩ := step_stmt_lm2_1_simulation hrel₄ (hnd₄ rfl)
    lm21_copyZero_phase rfl rfl (fun tf htf =>
      .arrayStmt (.elemAssign (.copyElem 2 1 lm21U16Arr2Decl lm21U16Arr3Decl (.uint .u16) 2 3
        (.index 3) (.constantIndex 1 3 true) true _
        rfl lm21_wf_u16Arr2 rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.index 3 lm21UsizeDecl rfl rfl (Or.inl (himm₄ 3 (by decide) (by decide) tf htf)))
        (.constantIndex 1 3 true (by decide) (by decide)
          ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
        (Or.inr (Or.inr ⟨arr2_0, rfl⟩))
        (Or.inr (Or.inr ⟨arr1_1, rfl⟩)))))
  rw [h₅] at hsim₅
  generalize hr₅ : Miri.Interpreter.Step.step hooks () m₄ = r₅ at hsim₅ hnd₅ him₅ hhw₅
  cases hsim₅ with
  | step _ m₅ hrel₅ =>
  have himm₅ : ∀ j, j ≠ 1 → j ≠ 2 → ∀ tf, m₅.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j hj₁ hj₂ tf htf; obtain ⟨tf₄, htf₄, _⟩ := hrel₄
    exact him₅ rfl tf₄ tf htf₄ htf j (fun h => nomatch h) (himm₄ j hj₁ hj₂ tf₄ htf₄)
  obtain ⟨hw₅, hb₅⟩ := hhw₅ rfl hw₄ (by
    simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  simp only [arrayConstructDest?, mkStmt, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb₅
  -- `stmt 5`: `_0 = copy _2[_3]` -> `0x1122_u16`
  obtain ⟨hsim₆, hnd₆, -, hhw₆⟩ := step_stmt_lm2_1_simulation hrel₅ (hnd₅ rfl)
    lm21_copyZero_phase rfl rfl (fun tf htf =>
      .arrayStmt (.elemAssign (.readElem 0 2 lm21U16Decl lm21U16Arr2Decl (.uint .u16) 2
        (.index 3) false _ rfl lm21_wf_u16Arr2 rfl rfl
        (himm₅ 0 (by decide) (by decide) tf htf)
        (.index 3 lm21UsizeDecl rfl rfl (Or.inl (himm₅ 3 (by decide) (by decide) tf htf)))
        (Or.inr (Or.inr ⟨arr2_1, rfl⟩)))))
  rw [h₆] at hsim₆
  generalize hr₆ : Miri.Interpreter.Step.step hooks () m₅ = r₆ at hsim₆ hnd₆ hhw₆
  cases hsim₆ with
  | step _ m₆ hrel₆ =>
  obtain ⟨hw₆, _⟩ := hhw₆ rfl hw₅ (by
    simp only [arrayConstructDest?, mkStmt, local_, Option.isSome, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]; omega)
  exact ⟨m₁, m₂, m₃, m₄, m₅, m₆, rfl, hr₂, hr₃, hr₄, hr₅, hr₆, hrel₆, hnd₆ rfl, hw₆⟩

/-- Source-OOB UB witness for `WellTypedArrayElemAssign.copyElem` (`bb 1`):
after initializing `_1 : [u16; 3]` and `_2 : [u16; 2]`, `_2[0 of 2] = copy _1[0 of 4]`
resolves the in-bounds destination `_2[0 of 2]` and then fails with out-of-bounds UB
on `_1[0 of 4]` in both Anneal and `lean-miri`. -/
theorem lm21_copyElem_src_oob_ub :
    let hooks := annealStepHooks lm21CopyZeroBody.localDecls lm21CopyZeroBody.layouts
    let arr1_0 : List Value := [.scalar ⟨0x1122, 2⟩, .scalar ⟨0x3344, 2⟩, .scalar ⟨0x5566, 2⟩]
    let arr2_0 : List Value := [.scalar ⟨0x7788, 2⟩, .scalar ⟨0x7788, 2⟩]
    let mkState (k : Nat) (locals : List LocalSlot) : MachineState :=
      { frame := { blockIdx := 1, stmtIdx := k, locals := locals }
        memory := (initMachineState lm21CopyZeroBody []).memory }
    let s₁ := mkState 1 [.uninit, .init (.aggregate 0 arr1_0), .uninit, .uninit, .uninit]
    let s₂ := mkState 2 [.uninit, .init (.aggregate 0 arr1_0), .init (.aggregate 0 arr2_0), .uninit, .uninit]
    stepMirFn lm21CopyZeroBody (lm21CopyZeroInitAnneal 1) = .step s₁ ∧
      stepMirFn lm21CopyZeroBody s₁ = .step s₂ ∧
      stepMirFn lm21CopyZeroBody s₂ = .fail .ub ∧
      ∃ m₁ m₂ m₃ msg,
        Miri.Interpreter.Step.step hooks () (lm21CopyZeroInitMiri 1) = (m₁, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₁ = (m₂, .ok true) ∧
        Miri.Interpreter.Step.step hooks () m₂ = (m₃, .error (.undefinedBehavior msg)) := by
  intro hooks arr1_0 arr2_0 mkState s₁ s₂
  have h₁ : stepMirFn lm21CopyZeroBody (lm21CopyZeroInitAnneal 1) = .step s₁ := rfl
  have h₂ : stepMirFn lm21CopyZeroBody s₁ = .step s₂ := rfl
  have h₃ : stepMirFn lm21CopyZeroBody s₂ = .fail .ub := rfl
  refine ⟨h₁, h₂, h₃, ?_⟩
  obtain ⟨hsim₁, hnd₁, him₁, hhw₁⟩ := step_stmt_lm2_1_simulation (lm21_copyZero_init_stateRel 1)
    lm21_nodup_empty lm21_copyZero_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_copyZeroInitFrame_eq htf
      refine .arrayStmt (.aggregateArray 1 lm21U16Arr3Decl lm21U16Ty (.uint .u16) 3 _ _
        rfl lm21_wf_u16Arr3 rfl (Or.inr (Or.inl ⟨lm21_copyZeroInitFrame_imm 1 1, lm21_canReserve_empty⟩))
        ?_ lm21_isPrim_u16)
      intro op hop
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
      rcases hop with rfl | rfl | rfl
      · exact lm21_copyZero_constU16_wt _ 0x1122 (by decide)
      · exact lm21_copyZero_constU16_wt _ 0x3344 (by decide)
      · exact lm21_copyZero_constU16_wt _ 0x5566 (by decide))
  rw [h₁] at hsim₁
  generalize Miri.Interpreter.Step.step hooks () (lm21CopyZeroInitMiri 1) = r₁
    at hsim₁ hnd₁ him₁ hhw₁ ⊢
  cases hsim₁ with
  | step _ m₁ hrel₁ =>
  have himm₁ : ∀ j, j ≠ 1 → ∀ tf, m₁.stack.frames = #[tf] → IsImmediateFrameLocal tf j :=
    fun j hj tf htf => him₁ rfl _ tf rfl htf j (fun h => hj (by injection h with h; exact h.symm))
      (lm21_copyZeroInitFrame_imm 1 j)
  obtain ⟨hw₁, _⟩ := hhw₁ rfl MemoryHighWater.empty (by decide)
  obtain ⟨hsim₂, hnd₂, -, -⟩ := step_stmt_lm2_1_simulation hrel₁ (hnd₁ rfl)
    lm21_copyZero_phase rfl rfl (fun tf htf =>
      .arrayStmt (.repeatArray 2 lm21U16Arr2Decl (.uint .u16) 2 _ _
        rfl lm21_wf_u16Arr2 (Or.inr (Or.inl ⟨himm₁ 2 (by decide) tf htf, hw₁.canReserveAllocId⟩))
        (lm21_copyZero_constU16_wt tf 0x7788 (by decide)) lm21_isPrim_u16))
  rw [h₂] at hsim₂
  generalize hr₂ : Miri.Interpreter.Step.step hooks () m₁ = r₂ at hsim₂ hnd₂
  cases hsim₂ with
  | step _ m₂ hrel₂ =>
  obtain ⟨hsim₃, -, -, -⟩ := step_stmt_lm2_1_simulation hrel₂ (hnd₂ rfl)
    lm21_copyZero_phase rfl rfl (fun _ _ =>
      .arrayStmt (.elemAssign (.copyElem 2 1 lm21U16Arr2Decl lm21U16Arr3Decl (.uint .u16) 2 3
        (.constantIndex 0 2 false) (.constantIndex 0 4 false) false _
        rfl lm21_wf_u16Arr2 rfl lm21_wf_u16Arr3 lm21_isPrim_u16
        (.constantIndex 0 2 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (.constantIndex 0 4 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (Or.inr (Or.inr ⟨arr2_0, rfl⟩))
        (Or.inr (Or.inr ⟨arr1_0, rfl⟩)))))
  rw [h₃] at hsim₃
  generalize hr₃ : Miri.Interpreter.Step.step hooks () m₂ = r₃ at hsim₃
  cases hsim₃ with
  | ub m₃ msg =>
    exact ⟨m₁, m₂, m₃, msg, rfl, hr₂, hr₃⟩

/-- Zero-byte stack allocation backing an uninitialized indirect `_4 : [u16; 0]`. -/
def lm21ZeroArrAlloc :
    Miri.Memory.Allocation AnnealProv (Option Miri.TreeBorrows.BorrowTree) :=
  (extractExceptOk
    (Miri.Memory.Allocation.fromBytes (Prov := AnnealProv)
      #[] (translateAlignBytes 2) .Mut)
    (by decide)).withExtra none

/-- `MemPlace` at `0x1000` (`relOffset = 0`) inside `lm21ZeroArrAlloc`. -/
def lm21ZeroArrMemPlace : Miri.Interpreter.MemPlace AnnealProv :=
  { ptr := ⟨Miri.ABI.Size.ofBytes witnessBaseAddr, some (.concrete witnessAllocId witnessTag)⟩
    metadata := .none
    misaligned := none }

def lm21Usize0 : Miri.Memory.ScalarInt := Miri.Memory.ScalarInt.ofUInt64 0

theorem lm21_idxRel_0 :
    ImmediateRel lm21UsizeTy emptyLayoutTable (.scalar ⟨0, 8⟩)
      (.scalar (.fromScalarInt lm21Usize0)) :=
  .scalar ⟨0, 8⟩ lm21Usize0 ⟨Or.inr (Or.inr (Or.inr (Or.inl rfl))), by decide, rfl, rfl⟩
    rfl (fun h => nomatch h) (fun h => nomatch h)

/-- `lm21ZeroArrMemPlace` satisfies `MemPlaceRel` for uninitialized (`none`)
`[u16; 0]` in `witnessMachineOf lm21ZeroArrAlloc`. -/
theorem lm21_zeroArr_uninit_memPlaceRel :
    MemPlaceRel (witnessMachineOf lm21ZeroArrAlloc) lm21U16Arr0Ty emptyLayoutTable
      none lm21ZeroArrMemPlace :=
  MemPlaceRel.mk
    witnessAllocId witnessTag witnessBaseAddr Miri.ABI.Size.ZERO
    { kind := .stack, allocation := lm21ZeroArrAlloc }
    rfl rfl rfl (List.Mem.head _)
    (by decide) (by decide) (by decide) (by decide)
    (show lm21ZeroArrMemPlace.ptr.offset.isAligned (translateAlignBytes 2) = .ok true by decide)
    (show Miri.ABI.Size.ZERO.bytes.toNat + 0 ≤ lm21ZeroArrAlloc.byteSize.bytes.toNat by decide)
    (fun _ hsz => absurd rfl hsz)
    (fun _ h => nomatch h)
    (fun _ h => nomatch h)
    (fun _ _ _ _ h => nomatch h)

def lm21ZeroArrAnneal (k : Nat) : MachineState :=
  { frame :=
      { blockIdx := 2
        stmtIdx := k
        locals := [.uninit, .uninit, .uninit, .init (.scalar ⟨0, 8⟩), .uninit] }
    memory := (initMachineState lm21CopyZeroBody []).memory }

def lm21ZeroArrMiriFrame (k : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21CopyZeroBody
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
      { value := .live (.immediate (.scalar (.fromScalarInt lm21Usize0))), layout := none },
      { value := .live (.indirect lm21ZeroArrMemPlace), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨2, k⟩ }

def lm21ZeroArrMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm21ZeroArrMiriFrame k]⟩, machine := witnessMachineOf lm21ZeroArrAlloc }

theorem lm21_zeroArr_stateRel (k : Nat) :
    StateRel lm21CopyZeroBody (lm21ZeroArrAnneal k) (lm21ZeroArrMiri k) := by
  refine StateRel.mk (lm21ZeroArrMiriFrame k) rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j mp_i mp_j _ _ hneq hi hj
      match i, j with
      | 0, _ | 1, _ | 2, _ | 3, _ => simp [lm21ZeroArrMiriFrame] at hi
      | _ + 5, _ => simp [lm21ZeroArrMiriFrame] at hi
      | 4, 0 | 4, 1 | 4, 2 | 4, 3 => simp [lm21ZeroArrMiriFrame] at hj
      | 4, 4 => exact absurd rfl hneq
      | 4, _ + 5 => simp [lm21ZeroArrMiriFrame] at hj)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 1 | 2 =>
    have hs : slot = .uninit := by simpa [lm21ZeroArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21ZeroArrMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 3 =>
    have hd : decl = lm21UsizeDecl := by simpa [lm21CopyZeroBody, get?] using hdecl.symm
    have hs : slot = .init (.scalar ⟨0, 8⟩) := by simpa [lm21ZeroArrAnneal, get?] using hslot.symm
    have hm : mls =
        { value := .live (.immediate (.scalar (.fromScalarInt lm21Usize0))), layout := none } := by
      simpa [lm21ZeroArrMiriFrame] using hmls.symm
    subst hd hs hm
    exact .immediate _ _ none (fun _ h => nomatch h) (Or.inr ⟨_, rfl, lm21_idxRel_0⟩)
  | 4 =>
    have hd : decl = lm21U16Arr0Decl := by simpa [lm21CopyZeroBody, get?] using hdecl.symm
    have hs : slot = .uninit := by simpa [lm21ZeroArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect lm21ZeroArrMemPlace), layout := none } := by
      simpa [lm21ZeroArrMiriFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ lm21ZeroArrMemPlace none (fun _ h => nomatch h) nofun
      lm21_zeroArr_uninit_memPlaceRel
  | _ + 5 =>
    simp [lm21CopyZeroBody, get?] at hdecl

private theorem lm21_zeroArrFrame_eq {k : Nat}
    {tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit}
    (h : (lm21ZeroArrMiri k).stack.frames = #[tf]) :
    tf = lm21ZeroArrMiriFrame k := by
  simp only [lm21ZeroArrMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at h
  exact h.symm

/-- Reading `_0 = copy _4[_3]` when `_4 : [u16; 0]` is `.uninit` in Anneal and
memory-backed (`.indirect lm21ZeroArrMemPlace`) in `lean-miri` — even though
`annealCheckIndirectInitialized` returns `.ok ()` on `Size.ZERO` — reports
undefined behavior in both machines via `step_stmt_lm2_1_simulation`. -/
theorem lm21_uninit_indirect_zero_array_read_ub :
    annealCheckIndirectInitialized (witnessMachineOf lm21ZeroArrAlloc) lm21ZeroArrMemPlace
        (translateTy lm21U16Arr0Ty emptyLayoutTable).layout.size = .ok () ∧
      stepMirFn lm21CopyZeroBody (lm21ZeroArrAnneal 0) = .fail .ub ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooks lm21CopyZeroBody.localDecls lm21CopyZeroBody.layouts) ()
          (lm21ZeroArrMiri 0) = (m', .error (.undefinedBehavior msg)) := by
  have hchk :
      annealCheckIndirectInitialized (witnessMachineOf lm21ZeroArrAlloc) lm21ZeroArrMemPlace
        (translateTy lm21U16Arr0Ty emptyLayoutTable).layout.size = .ok () := by decide
  have hstep : stepMirFn lm21CopyZeroBody (lm21ZeroArrAnneal 0) = .fail .ub := rfl
  refine ⟨hchk, hstep, ?_⟩
  have hnd : LiveAllocsNodup (witnessMachineOf lm21ZeroArrAlloc) :=
    List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  obtain ⟨hsim, -, -, -⟩ := step_stmt_lm2_1_simulation (lm21_zeroArr_stateRel 0) hnd
    lm21_copyZero_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_zeroArrFrame_eq htf
      refine .arrayStmt (.elemAssign (.readElem 0 4 lm21U16Decl lm21U16Arr0Decl (.uint .u16) 0
        (.index 3) false _ rfl lm21_wf_u16Arr0 rfl rfl ?_ ?_ (Or.inr (Or.inl rfl))))
      · intro mls hmls mp hv
        simp [lm21ZeroArrMiriFrame] at hmls; subst hmls; cases hv
      · refine .index 3 lm21UsizeDecl rfl rfl (Or.inl ?_)
        intro mls hmls mp hv
        simp [lm21ZeroArrMiriFrame] at hmls; subst hmls; cases hv)
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21CopyZeroBody.localDecls lm21CopyZeroBody.layouts) ()
    (lm21ZeroArrMiri 0) = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-- Writing `_4[0 of 1] = const 0x090A_u16` when `_4 : [u16; 0]` is `.uninit` in
Anneal and memory-backed (`.indirect lm21ZeroArrMemPlace`) in `lean-miri` — even
though `annealCheckIndirectInitialized` returns `.ok ()` on `Size.ZERO` — reports
undefined behavior in both machines via `step_stmt_lm2_1_simulation`. -/
theorem lm21_uninit_indirect_zero_array_write_ub :
    annealCheckIndirectInitialized (witnessMachineOf lm21ZeroArrAlloc) lm21ZeroArrMemPlace
        (translateTy lm21U16Arr0Ty emptyLayoutTable).layout.size = .ok () ∧
      stepMirFn lm21CopyZeroBody (lm21ZeroArrAnneal 1) = .fail .ub ∧
      ∃ m' msg,
        Miri.Interpreter.Step.step
          (annealStepHooks lm21CopyZeroBody.localDecls lm21CopyZeroBody.layouts) ()
          (lm21ZeroArrMiri 1) = (m', .error (.undefinedBehavior msg)) := by
  have hchk :
      annealCheckIndirectInitialized (witnessMachineOf lm21ZeroArrAlloc) lm21ZeroArrMemPlace
        (translateTy lm21U16Arr0Ty emptyLayoutTable).layout.size = .ok () := by decide
  have hstep : stepMirFn lm21CopyZeroBody (lm21ZeroArrAnneal 1) = .fail .ub := rfl
  refine ⟨hchk, hstep, ?_⟩
  have hnd : LiveAllocsNodup (witnessMachineOf lm21ZeroArrAlloc) :=
    List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
  obtain ⟨hsim, -, -, -⟩ := step_stmt_lm2_1_simulation (lm21_zeroArr_stateRel 1) hnd
    lm21_copyZero_phase rfl rfl (fun tf htf => by
      obtain rfl := lm21_zeroArrFrame_eq htf
      exact .arrayStmt (.elemAssign (.writeElem 4 lm21U16Arr0Decl (.uint .u16) 0
        (.constantIndex 0 1 false) (.constant (lm21ConstU16 0x090A)) _
        rfl lm21_wf_u16Arr0 lm21_isPrim_u16
        (.constantIndex 0 1 false (by decide) (by decide)
          ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
        (lm21_copyZero_constU16_wt _ 0x090A (by decide))
        (fun _ h => nomatch h)
        (Or.inr (Or.inl rfl)))))
  rw [hstep] at hsim
  generalize Miri.Interpreter.Step.step
    (annealStepHooks lm21CopyZeroBody.localDecls lm21CopyZeroBody.layouts) ()
    (lm21ZeroArrMiri 1) = r at hsim ⊢
  cases hsim with
  | ub m' msg => exact ⟨m', msg, rfl⟩

/-- Concrete non-vacuity witness for `projectConstantIndex_malformed_invariant` on
`[u16; 3]` (`witnessMemPlace`), confirming fail-closed `ProjectionError.invariant`
rejection across `offset ≥ 2^64`, `minLength ≥ 2^64`, `fromEnd = false` with
`minLength ≤ offset`, and `fromEnd = true` with `offset = 0` or `minLength < offset`. -/
theorem lm21_malformed_constantIndex_invariant :
    let cx := annealProjectionCx (lm21ArrMiriFrame 7 .uninit) lm21Body.layouts
      (witnessMachineOf lm21ArrAlloc)
    let base : Miri.Interpreter.OpTy AnnealProv :=
      ⟨.indirect witnessMemPlace, translateTy lm21U16Arr3Ty lm21Body.layouts⟩
    (∃ msg, annealProjectList cx base [.ConstantIndex (2 ^ 64) 3 false] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 0 (2 ^ 64) false] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 3 3 false] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 0 3 true] =
      .error (.invariant msg)) ∧
    (∃ msg, annealProjectList cx base [.ConstantIndex 4 3 true] =
      .error (.invariant msg)) :=
  ⟨projectConstantIndex_malformed_invariant (lm21ArrMiriFrame 7 .uninit) lm21_wf_u16Arr3
      (2 ^ 64) 3 false (Or.inl (Nat.le_refl _)),
   projectConstantIndex_malformed_invariant (lm21ArrMiriFrame 7 .uninit) lm21_wf_u16Arr3
      0 (2 ^ 64) false (Or.inr (Or.inl (Nat.le_refl _))),
   projectConstantIndex_malformed_invariant (lm21ArrMiriFrame 7 .uninit) lm21_wf_u16Arr3
      3 3 false (Or.inr (Or.inr ⟨by decide, Or.inl ⟨rfl, by decide⟩⟩)),
   projectConstantIndex_malformed_invariant (lm21ArrMiriFrame 7 .uninit) lm21_wf_u16Arr3
      0 3 true (Or.inr (Or.inr ⟨by decide, Or.inr ⟨rfl, Or.inl rfl⟩⟩)),
   projectConstantIndex_malformed_invariant (lm21ArrMiriFrame 7 .uninit) lm21_wf_u16Arr3
      4 3 true (Or.inr (Or.inr ⟨by decide, Or.inr ⟨rfl, Or.inr (by decide)⟩⟩))⟩

/-! ## 12. End-to-End `StepError.invalidProgram` Malformed `ConstantIndex` Witness & Multi-Domain Full-Function `runBounded` Witness -/

/-- Ill-formed `Runtime(PostCleanup)` MIR body exercising both malformed
`ConstantIndex` read (`_0 = copy _1[3 of 3]`, `fromEnd = false` with
`minLength ≤ offset`) and malformed `ConstantIndex` write
(`_1[-0 of 3] = const 0x090A_u16`, `fromEnd = true` with `offset = 0`) on
initialized `_1 : [u16; 3]`. -/
def lm21MalformedConstBody : CapturedMir where
  defPath := "lm_2_1_witness::malformed_const_index"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [lm21U16Decl, lm21U16Arr3Decl, lm21UsizeDecl, lm21U16Arr0Decl]
  basicBlocks := [
    { statements := [
        mkStmt (.assign (local_ 0) (.use (.copy ⟨1, [.constantIndex 3 3 false]⟩))),
        mkStmt (.assign ⟨1, [.constantIndex 0 3 true]⟩
          (.use (.constant (lm21ConstU16 0x090A))))],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21FnAbi
  layouts := emptyLayoutTable
  allocations := []

def lm21MalArrAnneal (k : Nat) : MachineState :=
  { frame :=
      { blockIdx := 0
        stmtIdx := k
        locals := [.uninit, .init (.aggregate 0 lm21ArrElems), .uninit, .uninit] }
    memory := (initMachineState lm21MalformedConstBody []).memory }

def lm21MalArrMiriFrame (k : Nat) :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21MalformedConstBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm21U16Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.indirect witnessMemPlace), layout := none },
      { value := .live (.immediate .uninit), layout := none },
      { value := .live (.immediate .uninit), layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, k⟩ }

def lm21MalArrMiri (k : Nat) : AnnealStepState :=
  { stack := ⟨#[lm21MalArrMiriFrame k]⟩, machine := witnessMachineOf lm21ArrAlloc }

theorem lm21_mal_arr_stateRel (k : Nat) :
    StateRel lm21MalformedConstBody (lm21MalArrAnneal k) (lm21MalArrMiri k) := by
  refine StateRel.mk (lm21MalArrMiriFrame k) rfl rfl ⟨translateTy lm21U16Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i j _ _ _ _ hneq hi hj
      match i, j with
      | 0, _ | 2, _ | 3, _ | _ + 4, _ => simp [lm21MalArrMiriFrame] at hi
      | 1, 0 | 1, 2 | 1, 3 | 1, _ + 4 => simp [lm21MalArrMiriFrame] at hj
      | 1, 1 => exact absurd rfl hneq)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 | 2 | 3 =>
    have hs : slot = .uninit := by simpa [lm21MalArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21MalArrMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 =>
    have hd : decl = lm21U16Arr3Decl := by
      simpa [lm21MalformedConstBody, get?] using hdecl.symm
    have hs : slot = .init (.aggregate 0 lm21ArrElems) := by
      simpa [lm21MalArrAnneal, get?] using hslot.symm
    have hm : mls = { value := .live (.indirect witnessMemPlace), layout := none } := by
      simpa [lm21MalArrMiriFrame] using hmls.symm
    subst hd hs hm
    exact .indirect _ witnessMemPlace none (fun _ h => nomatch h) nofun lm21_memPlaceRel
  | _ + 4 =>
    simp [lm21MalformedConstBody, get?] at hdecl

/-- Concrete statement-level and `runMiriBounded` witness for
`step_assign_malformed_constantIndex_invalidProgram`: both malformed
`ConstantIndex` element reads (`stmt 0`: `offset = 3, minLength = 3, fromEnd = false`)
and malformed `ConstantIndex` element writes (`stmt 1`: `offset = 0, minLength = 3,
fromEnd = true`) halt `Step.step` and `runMiriBounded` with
`StepError.invalidProgram msg` (`RunLoop.reportsUB = false`), never misclassifying
compiler-invariant violations as undefined behavior. -/
theorem lm21_malformed_constantIndex_step_invalidProgram :
    let hooks :=
      annealStepHooks lm21MalformedConstBody.localDecls lm21MalformedConstBody.layouts
    (∃ m' msg,
      Miri.Interpreter.Step.step hooks () (lm21MalArrMiri 0) =
        (m', .error (.invalidProgram msg)) ∧
      runMiriBounded lm21MalformedConstBody 1 (lm21MalArrMiri 0) =
        .error m' (.invalidProgram msg) ∧
      Miri.Interpreter.RunLoop.reportsUB (.invalidProgram msg) = false) ∧
    (∃ m' msg,
      Miri.Interpreter.Step.step hooks () (lm21MalArrMiri 1) =
        (m', .error (.invalidProgram msg)) ∧
      runMiriBounded lm21MalformedConstBody 1 (lm21MalArrMiri 1) =
        .error m' (.invalidProgram msg) ∧
      Miri.Interpreter.RunLoop.reportsUB (.invalidProgram msg) = false) := by
  intro hooks
  constructor
  · obtain ⟨m', msg, hstep, hrep⟩ :=
      step_assign_malformed_constantIndex_invalidProgram
        (arrIdx := 1) (arrDecl := lm21U16Arr3Decl) (elemKind := .uint .u16) (count := 3)
        (lm21_mal_arr_stateRel 0) lm21_nodup_arr rfl rfl rfl lm21_wf_u16Arr3 rfl
        3 3 false (Or.inr (Or.inr ⟨by decide, Or.inl ⟨rfl, by decide⟩⟩))
        (Or.inl ⟨0, lm21U16Decl, false, "lm-1.1-witness", rfl, rfl⟩)
    refine ⟨m', msg, hstep, ?_, hrep⟩
    unfold runMiriBounded
    rw [hstep]
  · obtain ⟨m', msg, hstep, hrep⟩ :=
      step_assign_malformed_constantIndex_invalidProgram
        (arrIdx := 1) (arrDecl := lm21U16Arr3Decl) (elemKind := .uint .u16) (count := 3)
        (lm21_mal_arr_stateRel 1) lm21_nodup_arr rfl rfl rfl lm21_wf_u16Arr3 rfl
        0 3 true (Or.inr (Or.inr ⟨by decide, Or.inr ⟨rfl, Or.inl rfl⟩⟩))
        (Or.inr ⟨.constant (lm21ConstU16 0x090A), "lm-1.1-witness", rfl⟩)
    refine ⟨m', msg, hstep, ?_, hrep⟩
    unfold runMiriBounded
    rw [hstep]

def lm21I32Ty : Ty := { kind := .int .i32, layoutIdx := 0 }
def lm21I32Decl : LocalDecl := { mutability := .mut, ty := lm21I32Ty, debugName := none }

def lm21BoolTy : Ty := { kind := .bool, layoutIdx := 0 }
def lm21BoolDecl : LocalDecl := { mutability := .mut, ty := lm21BoolTy, debugName := none }

def lm21CharTy : Ty := { kind := .char, layoutIdx := 0 }
def lm21CharDecl : LocalDecl := { mutability := .mut, ty := lm21CharTy, debugName := none }

def lm21I32Arr3Ty : Ty := { kind := .array (.int .i32) 3, layoutIdx := 0 }
def lm21I32Arr3Decl : LocalDecl := { mutability := .mut, ty := lm21I32Arr3Ty, debugName := none }

def lm21BoolArr2Ty : Ty := { kind := .array .bool 2, layoutIdx := 0 }
def lm21BoolArr2Decl : LocalDecl := { mutability := .mut, ty := lm21BoolArr2Ty, debugName := none }

def lm21CharArr2Ty : Ty := { kind := .array .char 2, layoutIdx := 0 }
def lm21CharArr2Decl : LocalDecl := { mutability := .mut, ty := lm21CharArr2Ty, debugName := none }

def lm21ConstI32 (bits : Nat) : ConstOperand := { ty := lm21I32Ty, val := .scalar (.int ⟨bits, 4⟩) }
def lm21ConstBool (b : Bool) : ConstOperand :=
  { ty := lm21BoolTy, val := .scalar (.int ⟨if b then 1 else 0, 1⟩) }
def lm21ConstChar (cp : Nat) : ConstOperand := { ty := lm21CharTy, val := .scalar (.int ⟨cp, 4⟩) }

def lm21I32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory, fields := .primitive,
    variants := .single 0, isUninhabited := false }

def lm21I32FnAbi : FnAbi :=
  { args := [], ret := { layout := lm21I32Layout, mode := .direct }, conv := .rust,
    canUnwind := false }

private theorem lm21_i32_elemLayout_eq (c : Nat) :
    arrayElemLayoutOf emptyLayoutTable
      (translateTy { kind := .array (.int .i32) c, layoutIdx := 0 } emptyLayoutTable)
      (translateTy { kind := .int .i32, layoutIdx := 0 } emptyLayoutTable).layout.size =
    translateTy { kind := .int .i32, layoutIdx := 0 } emptyLayoutTable := by
  have hty :
      (translateTy { kind := .array (.int .i32) c, layoutIdx := 0 } emptyLayoutTable).ty = 1012 :=
    rfl
  unfold arrayElemLayoutOf
  rw [hty]
  have hge : (1012 : Nat) ≥ 1000 := by decide
  have hmod : (1012 - 1000) % 100 = 12 := by decide
  simp only [hge, ↓reduceIte, hmod, layoutOfEncodedTyId]

private theorem lm21_bool_elemLayout_eq (c : Nat) :
    arrayElemLayoutOf emptyLayoutTable
      (translateTy { kind := .array .bool c, layoutIdx := 0 } emptyLayoutTable)
      (translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable).layout.size =
    translateTy { kind := .bool, layoutIdx := 0 } emptyLayoutTable := by
  have hty :
      (translateTy { kind := .array .bool c, layoutIdx := 0 } emptyLayoutTable).ty = 1001 :=
    rfl
  unfold arrayElemLayoutOf
  rw [hty]
  have hge : (1001 : Nat) ≥ 1000 := by decide
  have hmod : (1001 - 1000) % 100 = 1 := by decide
  simp only [hge, ↓reduceIte, hmod, layoutOfEncodedTyId]

private theorem lm21_char_elemLayout_eq (c : Nat) :
    arrayElemLayoutOf emptyLayoutTable
      (translateTy { kind := .array .char c, layoutIdx := 0 } emptyLayoutTable)
      (translateTy { kind := .char, layoutIdx := 0 } emptyLayoutTable).layout.size =
    translateTy { kind := .char, layoutIdx := 0 } emptyLayoutTable := by
  have hty :
      (translateTy { kind := .array .char c, layoutIdx := 0 } emptyLayoutTable).ty = 1002 :=
    rfl
  unfold arrayElemLayoutOf
  rw [hty]
  have hge : (1002 : Nat) ≥ 1000 := by decide
  have hmod : (1002 - 1000) % 100 = 2 := by decide
  simp only [hge, ↓reduceIte, hmod, layoutOfEncodedTyId]

/-- `[i32; 3]` satisfies `WellTypedArrayTy` (`stride = 4`, signed `i32` domain). -/
theorem lm21_wf_i32Arr3 : WellTypedArrayTy emptyLayoutTable lm21I32Arr3Ty (.int .i32) 3 :=
  ⟨rfl, Or.inr (Or.inr (Or.inl ⟨.i32, rfl⟩)), rfl, rfl, rfl, rfl, rfl,
    lm21_i32_elemLayout_eq 3,
    show 0 < 4 by decide, show 4 ≤ 16 by decide, show 3 * 4 < 2 ^ 32 by decide, rfl⟩

/-- `[bool; 2]` satisfies `WellTypedArrayTy` (`stride = 1`, `bool` domain). -/
theorem lm21_wf_boolArr2 : WellTypedArrayTy emptyLayoutTable lm21BoolArr2Ty .bool 2 :=
  ⟨rfl, Or.inl rfl, rfl, rfl, rfl, rfl, rfl,
    lm21_bool_elemLayout_eq 2,
    show 0 < 1 by decide, show 1 ≤ 16 by decide, show 2 * 1 < 2 ^ 32 by decide, rfl⟩

/-- `[char; 2]` satisfies `WellTypedArrayTy` (`stride = 4`, Unicode `char` domain). -/
theorem lm21_wf_charArr2 : WellTypedArrayTy emptyLayoutTable lm21CharArr2Ty .char 2 :=
  ⟨rfl, Or.inr (Or.inl rfl), rfl, rfl, rfl, rfl, rfl,
    lm21_char_elemLayout_eq 2,
    show 0 < 4 by decide, show 4 ≤ 16 by decide, show 2 * 4 < 2 ^ 32 by decide, rfl⟩

theorem lm21_isPrim_i32 : IsPrimScalarTy lm21I32Ty :=
  Or.inr (Or.inr (Or.inl ⟨.i32, rfl⟩))

theorem lm21_isPrim_bool : IsPrimScalarTy lm21BoolTy :=
  Or.inl rfl

theorem lm21_isPrim_char : IsPrimScalarTy lm21CharTy :=
  Or.inr (Or.inl rfl)

/-- Complete `Runtime(PostCleanup)` MIR function exercising signed `[i32; 3]`
(including negative two's-complement `i32`s `-10` and `-3`), `[bool; 2]`, and
`[char; 2]` from `initMachineState` through `StorageDead` and `return_`
(`25_i32 + (-3_i32) = 22_i32`):
```text
bb0:
  StorageLive(_1); _1 = [-10_i32, 25_i32, -3_i32];
  StorageLive(_2); _2 = [true; 2]; _2[-1 of 2] = false;
  StorageLive(_3); _3 = ['A'; 2];
  StorageLive(_6); _6 = copy _2[0 of 2];
  StorageLive(_7); _7 = copy _3[1 of 2];
  StorageLive(_4); _4 = const 1_usize;
  StorageLive(_5); _5 = copy _1[_4];
  _0 = move _1[-1 of 3];
  _0 = Add(copy _5, copy _0);
  StorageDead(_3); StorageDead(_2); StorageDead(_1);
  return
``` -/
def lm21FullFnBody : CapturedMir where
  defPath := "lm_2_1_witness::signed_bool_char_fn"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 0
  localDecls := [
    lm21I32Decl, lm21I32Arr3Decl, lm21BoolArr2Decl, lm21CharArr2Decl,
    lm21UsizeDecl, lm21I32Decl, lm21BoolDecl, lm21CharDecl]
  basicBlocks := [
    { statements := [
        mkStmt (.storageLive 1),
        mkStmt (.assign (local_ 1) (.aggregate (.array lm21I32Ty)
          [.constant (lm21ConstI32 0xFFFF_FFF6),
           .constant (lm21ConstI32 25),
           .constant (lm21ConstI32 0xFFFF_FFFD)])),
        mkStmt (.storageLive 2),
        mkStmt (.assign (local_ 2) (.repeat (.constant (lm21ConstBool true)) 2)),
        mkStmt (.assign ⟨2, [.constantIndex 1 2 true]⟩ (.use (.constant (lm21ConstBool false)))),
        mkStmt (.storageLive 3),
        mkStmt (.assign (local_ 3) (.repeat (.constant (lm21ConstChar 0x41)) 2)),
        mkStmt (.storageLive 6),
        mkStmt (.assign (local_ 6) (.use (.copy ⟨2, [.constantIndex 0 2 false]⟩))),
        mkStmt (.storageLive 7),
        mkStmt (.assign (local_ 7) (.use (.copy ⟨3, [.constantIndex 1 2 false]⟩))),
        mkStmt (.storageLive 4),
        mkStmt (.assign (local_ 4) (.use (.constant (lm21ConstUsize 1)))),
        mkStmt (.storageLive 5),
        mkStmt (.assign (local_ 5) (.use (.copy ⟨1, [.index 4]⟩))),
        mkStmt (.assign (local_ 0) (.use (.move ⟨1, [.constantIndex 1 3 true]⟩))),
        mkStmt (.assign (local_ 0) (.binaryOp .add (.copy (local_ 5)) (.copy (local_ 0)))),
        mkStmt (.storageDead 3),
        mkStmt (.storageDead 2),
        mkStmt (.storageDead 1)],
      terminator := mkTerm .return_, isCleanup := false }]
  fnAbi := lm21I32FnAbi
  layouts := emptyLayoutTable
  allocations := []

theorem lm21_fullFn_phase : ∀ p, lm21FullFnBody.phase ≠ .other p := by
  intro p h; cases h

def lm21FullFnInitMiriFrame :
    Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit :=
  { body := translateBody lm21FullFnBody
    bodyIdentity := .ofCanonicalIndex 0
    functionInstance := { kind := .Item 0, args := #[] }
    extra := ()
    returnContinuation := .stop false
    returnPlace := .frameLocal 0 0 none (translateTy lm21I32Ty) (.ofAllocationToken 0)
    localsIdentity := .ofAllocationToken 0
    locals := #[
      { value := .live (.immediate .uninit), layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none },
      { value := .dead, layout := none }]
    vaList := #[]
    trackCallerArg := none
    location := .mir ⟨0, 0⟩ }

def lm21FullFnInitMiri : AnnealStepState :=
  { stack := ⟨#[lm21FullFnInitMiriFrame]⟩, machine := AnnealMachine.empty }

theorem lm21_fullFn_init_stateRel :
    StateRel lm21FullFnBody (initMachineState lm21FullFnBody []) lm21FullFnInitMiri := by
  refine StateRel.mk lm21FullFnInitMiriFrame rfl rfl ⟨translateTy lm21I32Ty, rfl⟩ ?_
    rfl rfl rfl rfl rfl
    (by
      intro i _ _ _ _ _ _ hi _
      revert hi
      match i with
      | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rintro ⟨⟩
      | _ + 8 => rintro ⟨⟩)
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  intro i decl slot mls hdecl hslot hmls
  match i with
  | 0 =>
    have hs : slot = .uninit := by
      simpa [initMachineState, lm21FullFnBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .live (.immediate .uninit), layout := none } := by
      simpa [lm21FullFnInitMiriFrame] using hmls.symm
    subst hs hm
    exact .immediate .uninit .uninit none (fun _ h => nomatch h) (Or.inl ⟨rfl, rfl⟩)
  | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    have hs : slot = .dead := by
      simpa [initMachineState, lm21FullFnBody, initLocalsAux, get?] using hslot.symm
    have hm : mls = { value := .dead, layout := none } := by
      simpa [lm21FullFnInitMiriFrame] using hmls.symm
    subst hs hm
    exact .dead none (fun _ h => nomatch h)
  | _ + 8 =>
    simp [lm21FullFnBody, get?] at hdecl

private theorem lm21_fullFnInitFrame_imm (j : Nat) :
    IsImmediateFrameLocal lm21FullFnInitMiriFrame j := by
  intro mls hmls mp hv
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 =>
    simp [lm21FullFnInitMiriFrame] at hmls; subst hmls; cases hv
  | _ + 8 => simp [lm21FullFnInitMiriFrame] at hmls

private theorem lm21_fullFn_constI32_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (bits : Nat) (hbits : bits < 2 ^ 32) :
    WellTypedLM2_1ScalarOperand lm21FullFnBody tf (.constant (lm21ConstI32 bits)) lm21I32Ty :=
  .ofScalar (.constScalar (lm21ConstI32 bits) ⟨bits, 4⟩ rfl lm21_isPrim_i32
    (Or.inr (Or.inr (Or.inl rfl))) (by simpa [scalarModulus] using hbits) rfl
    (fun h => nomatch h) (fun h => nomatch h))

private theorem lm21_fullFn_constBool_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (b : Bool) :
    WellTypedLM2_1ScalarOperand lm21FullFnBody tf (.constant (lm21ConstBool b)) lm21BoolTy := by
  cases b
  · exact .ofScalar (.constScalar (lm21ConstBool false) ⟨0, 1⟩ rfl lm21_isPrim_bool
      (Or.inl rfl) (by decide) rfl (fun _ => ⟨rfl, Or.inl rfl⟩) (fun h => nomatch h))
  · exact .ofScalar (.constScalar (lm21ConstBool true) ⟨1, 1⟩ rfl lm21_isPrim_bool
      (Or.inl rfl) (by decide) rfl (fun _ => ⟨rfl, Or.inr rfl⟩) (fun h => nomatch h))

private theorem lm21_fullFn_constChar_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (cp : Nat) (hcp : cp < 2 ^ 32) (hchar : isValidCharCode cp = true) :
    WellTypedLM2_1ScalarOperand lm21FullFnBody tf (.constant (lm21ConstChar cp)) lm21CharTy :=
  .ofScalar (.constScalar (lm21ConstChar cp) ⟨cp, 4⟩ rfl lm21_isPrim_char
    (Or.inr (Or.inr (Or.inl rfl))) (by simpa [scalarModulus] using hcp) rfl
    (fun h => nomatch h) (fun _ => ⟨rfl, hchar⟩))

private theorem lm21_fullFn_constUsize_scalar_wt
    (tf : Miri.Interpreter.Frame AnnealProv Miri.Interpreter.LocalLayout Unit)
    (n : Nat) (hn : n < 2 ^ 64) :
    WellTypedScalarOperand lm21FullFnBody tf (.constant (lm21ConstUsize n)) lm21UsizeTy :=
  .constScalar (lm21ConstUsize n) ⟨n, 8⟩ rfl (Or.inr (Or.inr (Or.inr ⟨.usize, rfl⟩)))
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    (by simpa [scalarModulus] using hn) rfl (fun h => nomatch h) (fun h => nomatch h)

private theorem lm21_step_runBounded
    {body : CapturedMir} {bb : BasicBlockData} {stmt : Statement}
    {s s' : MachineState} {m : AnnealStepState} {P Q : Nat → Prop}
    {optDest : Option Nat} {prevBudget nextBudget fuel : Nat}
    (hphase : ∀ p, body.phase ≠ .other p)
    (hbb : get? body.basicBlocks s.frame.blockIdx = some bb)
    (hstmt : get? bb.statements s.frame.stmtIdx = some stmt)
    (hdest : arrayConstructDest? stmt = optDest)
    (hrel : StateRel body s m)
    (hnd : LiveAllocsNodup m.machine)
    (hhw : MemoryHighWater m.machine.memory)
    (hm_next : m.machine.memory.nextAllocId.toNat ≤ prevBudget)
    (hb : prevBudget + (if optDest.isSome then 1 else 0) ≤ nextBudget)
    (hb_lim : nextBudget < 2 ^ 64)
    (hq : ∀ j, Q j → P j ∧ optDest ≠ some j)
    (hp : ∀ j, P j → ∀ tf, m.stack.frames = #[tf] → IsImmediateFrameLocal tf j)
    (hwt : ∀ tf, m.stack.frames = #[tf] → WellTypedLM2_1Stmt body s m tf stmt)
    (ha : stepMirFn body s = .step s') :
    ∃ m',
      runAnnealBounded body (fuel + 1) s = runAnnealBounded body fuel s' ∧
      runMiriBounded body (fuel + 1) m = runMiriBounded body fuel m' ∧
      StateRel body s' m' ∧
      LiveAllocsNodup m'.machine ∧
      MemoryHighWater m'.machine.memory ∧
      m'.machine.memory.nextAllocId.toNat ≤ nextBudget ∧
      (∀ j, Q j → ∀ tf', m'.stack.frames = #[tf'] → IsImmediateFrameLocal tf' j) := by
  obtain ⟨hsim, hnd', him', hhw'⟩ :=
    step_stmt_lm2_1_simulation hrel hnd hphase hbb hstmt hwt
  rw [hdest] at him' hhw'
  rw [ha] at hsim
  generalize hr :
    Miri.Interpreter.Step.step (annealStepHooks body.localDecls body.layouts) () m = r
    at hsim hnd' him' hhw'
  cases hsim with
  | step _ m' hrel' =>
    have ha_run : runAnnealBounded body (fuel + 1) s = runAnnealBounded body fuel s' :=
      runAnnealBounded_emitStep body fuel s s' .silent ha
    have hm_run : runMiriBounded body (fuel + 1) m = runMiriBounded body fuel m' :=
      runMiriBounded_step_of_stateRel fuel hr hrel'
    have hbudget :
        m.machine.memory.nextAllocId.toNat +
          (if optDest.isSome then 1 else 0) < 2 ^ 64 :=
      Nat.lt_of_le_of_lt
        (Nat.le_trans (Nat.add_le_add_right hm_next _) hb)
        hb_lim
    obtain ⟨hw', hb'⟩ := hhw' rfl hhw hbudget
    have hm_next' : m'.machine.memory.nextAllocId.toNat ≤ nextBudget :=
      Nat.le_trans hb' (Nat.le_trans (Nat.add_le_add_right hm_next _) hb)
    refine ⟨m', ha_run, hm_run, hrel', hnd' rfl, hw', hm_next', ?_⟩
    intro j hqj tf' htf'
    obtain ⟨hpj, hne⟩ := hq j hqj
    obtain ⟨tf, htf, _⟩ := hrel
    exact him' rfl tf tf' htf htf' j hne (hp j hpj tf htf)

private def lm21FullFnI32Arr : List Value :=
  [.scalar ⟨0xFFFF_FFF6, 4⟩, .scalar ⟨25, 4⟩, .scalar ⟨0xFFFF_FFFD, 4⟩]
private def lm21FullFnBoolArr0 : List Value := [.scalar ⟨1, 1⟩, .scalar ⟨1, 1⟩]
private def lm21FullFnBoolArr1 : List Value := [.scalar ⟨1, 1⟩, .scalar ⟨0, 1⟩]
private def lm21FullFnCharArr : List Value := [.scalar ⟨0x41, 4⟩, .scalar ⟨0x41, 4⟩]

private def lm21FullFnState (k : Nat) (locs : List LocalSlot) : MachineState :=
  { frame := { blockIdx := 0, stmtIdx := k, locals := locs }
    memory := (initMachineState lm21FullFnBody []).memory }

/-- Full-function fuel-bounded execution witness (`runAnnealBounded` and
`runMiriBounded`) from `initMachineState lm21FullFnBody []` through
`StorageLive`, signed `[i32; 3]` (`[-10_i32, 25_i32, -3_i32]`), `[bool; 2]`,
`[char; 2]`, element reads/writes, `BinaryOp.add` (`25 + (-3) = 22_i32`),
`StorageDead`, and `TerminatorKind.return_`. -/
theorem lm21_signed_bool_char_runBounded_return :
    ∃ mem' m',
      m'.stack.frames = #[] ∧
      runAnnealBounded lm21FullFnBody 21 (initMachineState lm21FullFnBody []) =
        .returned (.scalar ⟨22, 4⟩) mem' ∧
      runMiriBounded lm21FullFnBody 21 lm21FullFnInitMiri =
        .returned m'
          (.ok (.immediate (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 22))))) ∧
      ImmediateRel lm21I32Ty emptyLayoutTable (.scalar ⟨22, 4⟩)
        (.scalar (.fromScalarInt (Miri.Memory.ScalarInt.ofUInt32 22))) := by
  have hlim1 : (1 : Nat) < 2 ^ 64 := by decide
  have hlim2 : (2 : Nat) < 2 ^ 64 := by decide
  have hlim3 : (3 : Nat) < 2 ^ 64 := by decide
  have hlim4 : (4 : Nat) < 2 ^ 64 := by decide
  have himm₀ : ∀ j, True → ∀ tf, lm21FullFnInitMiri.stack.frames = #[tf] → IsImmediateFrameLocal tf j := by
    intro j _ tf htf
    have htf_eq : tf = lm21FullFnInitMiriFrame := by
      simp only [lm21FullFnInitMiri, List.toArray, Array.mk.injEq, List.cons.injEq, and_true] at htf
      exact htf.symm
    subst htf_eq
    exact lm21_fullFnInitFrame_imm j
  -- `stmt 0`: `StorageLive(1)`
  obtain ⟨m₁, ha₁, hm₁, hrel₁, hnd₁, hhw₁, hb₁, himm₁⟩ :=
    lm21_step_runBounded (Q := fun _ => True) (optDest := none) (prevBudget := 1) (nextBudget := 1) (fuel := 20)
      lm21_fullFn_phase rfl rfl rfl lm21_fullFn_init_stateRel lm21_nodup_empty MemoryHighWater.empty
      (by decide) (Nat.le_refl _) hlim1 (fun _ _ => ⟨trivial, nofun⟩) himm₀
      (fun _ _ => .lm14Stmt (.storageLive 1 lm21I32Arr3Decl _ rfl))
      (rfl : stepMirFn lm21FullFnBody (initMachineState lm21FullFnBody []) =
        .step (lm21FullFnState 1 [.uninit, .uninit, .dead, .dead, .dead, .dead, .dead, .dead]))
  clear himm₀
  -- `stmt 1`: `_1 = [-10_i32, 25_i32, -3_i32]`
  obtain ⟨m₂, ha₂, hm₂, hrel₂, hnd₂, hhw₂, hb₂, himm₂⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1) (optDest := some 1) (prevBudget := 1) (nextBudget := 2) (fuel := 19)
      lm21_fullFn_phase rfl rfl rfl hrel₁ hnd₁ hhw₁ hb₁ (Nat.le_refl _) hlim2
      (fun _ hj => ⟨trivial, fun h => hj (Option.some.inj h).symm⟩) himm₁
      (fun tf htf => by
        refine .arrayStmt (.aggregateArray 1 lm21I32Arr3Decl lm21I32Ty (.int .i32) 3 _ _
          rfl lm21_wf_i32Arr3 rfl (Or.inr (Or.inl ⟨himm₁ 1 trivial tf htf, hhw₁.canReserveAllocId⟩))
          ?_ lm21_isPrim_i32)
        intro op hop
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
        rcases hop with rfl | rfl | rfl
        · exact lm21_fullFn_constI32_wt tf 0xFFFF_FFF6 (by decide)
        · exact lm21_fullFn_constI32_wt tf 25 (by decide)
        · exact lm21_fullFn_constI32_wt tf 0xFFFF_FFFD (by decide))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 2 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .dead, .dead, .dead, .dead, .dead, .dead]))
  clear hrel₁ hnd₁ hhw₁ hb₁ himm₁
  -- `stmt 2`: `StorageLive(2)`
  obtain ⟨m₃, ha₃, hm₃, hrel₃, hnd₃, hhw₃, hb₃, himm₃⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1) (optDest := none) (prevBudget := 2) (nextBudget := 2) (fuel := 18)
      lm21_fullFn_phase rfl rfl rfl hrel₂ hnd₂ hhw₂ hb₂ (Nat.le_refl _) hlim2
      (fun _ hj => ⟨hj, nofun⟩) himm₂
      (fun _ _ => .lm14Stmt (.storageLive 2 lm21BoolArr2Decl _ rfl))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 3 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .uninit, .dead, .dead, .dead, .dead, .dead]))
  clear hrel₂ hnd₂ hhw₂ hb₂ himm₂
  -- `stmt 3`: `_2 = [true; 2]`
  obtain ⟨m₄, ha₄, hm₄, hrel₄, hnd₄, hhw₄, hb₄, himm₄⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2) (optDest := some 2) (prevBudget := 2) (nextBudget := 3) (fuel := 17)
      lm21_fullFn_phase rfl rfl rfl hrel₃ hnd₃ hhw₃ hb₃ (Nat.le_refl _) hlim3
      (fun _ ⟨hj₁, hj₂⟩ => ⟨hj₁, fun h => hj₂ (Option.some.inj h).symm⟩) himm₃
      (fun tf htf =>
        .arrayStmt (.repeatArray 2 lm21BoolArr2Decl .bool 2 _ _
          rfl lm21_wf_boolArr2 (Or.inr (Or.inl ⟨himm₃ 2 (by decide) tf htf, hhw₃.canReserveAllocId⟩))
          (lm21_fullFn_constBool_wt tf true) lm21_isPrim_bool))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 4 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr0), .dead, .dead, .dead, .dead, .dead]))
  clear hrel₃ hnd₃ hhw₃ hb₃ himm₃
  -- `stmt 4`: `_2[-1 of 2] = const false`
  obtain ⟨m₅, ha₅, hm₅, hrel₅, hnd₅, hhw₅, hb₅, himm₅⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2) (optDest := none) (prevBudget := 3) (nextBudget := 3) (fuel := 16)
      lm21_fullFn_phase rfl rfl rfl hrel₄ hnd₄ hhw₄ hb₄ (Nat.le_refl _) hlim3
      (fun _ hj => ⟨hj, nofun⟩) himm₄
      (fun tf _ =>
        .arrayStmt (.elemAssign (.writeElem 2 lm21BoolArr2Decl .bool 2
          (.constantIndex 1 2 true) (.constant (lm21ConstBool false)) _
          rfl lm21_wf_boolArr2 lm21_isPrim_bool
          (.constantIndex 1 2 true (by decide) (by decide)
            ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
          (lm21_fullFn_constBool_wt tf false)
          (fun _ h => nomatch h)
          (Or.inr (Or.inr ⟨lm21FullFnBoolArr0, rfl⟩)))))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 5 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .dead, .dead, .dead, .dead, .dead]))
  clear hrel₄ hnd₄ hhw₄ hb₄ himm₄
  -- `stmt 5`: `StorageLive(3)`
  obtain ⟨m₆, ha₆, hm₆, hrel₆, hnd₆, hhw₆, hb₆, himm₆⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2) (optDest := none) (prevBudget := 3) (nextBudget := 3) (fuel := 15)
      lm21_fullFn_phase rfl rfl rfl hrel₅ hnd₅ hhw₅ hb₅ (Nat.le_refl _) hlim3
      (fun _ hj => ⟨hj, nofun⟩) himm₅
      (fun _ _ => .lm14Stmt (.storageLive 3 lm21CharArr2Decl _ rfl))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 6 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .uninit, .dead, .dead, .dead, .dead]))
  clear hrel₅ hnd₅ hhw₅ hb₅ himm₅
  -- `stmt 6`: `_3 = ['A'; 2]`
  obtain ⟨m₇, ha₇, hm₇, hrel₇, hnd₇, hhw₇, hb₇, himm₇⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := some 3) (prevBudget := 3) (nextBudget := 4) (fuel := 14)
      lm21_fullFn_phase rfl rfl rfl hrel₆ hnd₆ hhw₆ hb₆ (Nat.le_refl _) hlim4
      (fun _ ⟨hj₁, hj₂, hj₃⟩ => ⟨⟨hj₁, hj₂⟩, fun h => hj₃ (Option.some.inj h).symm⟩) himm₆
      (fun tf htf =>
        .arrayStmt (.repeatArray 3 lm21CharArr2Decl .char 2 _ _
          rfl lm21_wf_charArr2 (Or.inr (Or.inl ⟨himm₆ 3 ⟨by decide, by decide⟩ tf htf, hhw₆.canReserveAllocId⟩))
          (lm21_fullFn_constChar_wt tf 0x41 (by decide) (by decide)) lm21_isPrim_char))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 7 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .dead, .dead, .dead, .dead]))
  clear hrel₆ hnd₆ hhw₆ hb₆ himm₆
  -- `stmt 7`: `StorageLive(6)`
  obtain ⟨m₈, ha₈, hm₈, hrel₈, hnd₈, hhw₈, hb₈, himm₈⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 13)
      lm21_fullFn_phase rfl rfl rfl hrel₇ hnd₇ hhw₇ hb₇ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₇
      (fun _ _ => .lm14Stmt (.storageLive 6 lm21BoolDecl _ rfl))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 8 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .dead, .dead, .uninit, .dead]))
  clear hrel₇ hnd₇ hhw₇ hb₇ himm₇
  -- `stmt 8`: `_6 = copy _2[0 of 2]`
  obtain ⟨m₉, ha₉, hm₉, hrel₉, hnd₉, hhw₉, hb₉, himm₉⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 12)
      lm21_fullFn_phase rfl rfl rfl hrel₈ hnd₈ hhw₈ hb₈ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₈
      (fun tf htf =>
        .arrayStmt (.elemAssign (.readElem 6 2 lm21BoolDecl lm21BoolArr2Decl .bool 2
          (.constantIndex 0 2 false) false _
          rfl lm21_wf_boolArr2 rfl rfl
          (himm₈ 6 ⟨by decide, by decide, by decide⟩ tf htf)
          (.constantIndex 0 2 false (by decide) (by decide)
            ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
          (Or.inr (Or.inr ⟨lm21FullFnBoolArr1, rfl⟩)))))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 9 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .dead, .dead, .init (.scalar ⟨1, 1⟩), .dead]))
  clear hrel₈ hnd₈ hhw₈ hb₈ himm₈
  -- `stmt 9`: `StorageLive(7)`
  obtain ⟨m₁₀, ha₁₀, hm₁₀, hrel₁₀, hnd₁₀, hhw₁₀, hb₁₀, himm₁₀⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 11)
      lm21_fullFn_phase rfl rfl rfl hrel₉ hnd₉ hhw₉ hb₉ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₉
      (fun _ _ => .lm14Stmt (.storageLive 7 lm21CharDecl _ rfl))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 10 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .dead, .dead, .init (.scalar ⟨1, 1⟩), .uninit]))
  clear hrel₉ hnd₉ hhw₉ hb₉ himm₉
  -- `stmt 10`: `_7 = copy _3[1 of 2]`
  obtain ⟨m₁₁, ha₁₁, hm₁₁, hrel₁₁, hnd₁₁, hhw₁₁, hb₁₁, himm₁₁⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 10)
      lm21_fullFn_phase rfl rfl rfl hrel₁₀ hnd₁₀ hhw₁₀ hb₁₀ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₀
      (fun tf htf =>
        .arrayStmt (.elemAssign (.readElem 7 3 lm21CharDecl lm21CharArr2Decl .char 2
          (.constantIndex 1 2 false) false _
          rfl lm21_wf_charArr2 rfl rfl
          (himm₁₀ 7 ⟨by decide, by decide, by decide⟩ tf htf)
          (.constantIndex 1 2 false (by decide) (by decide)
            ⟨(fun _ => by decide), (fun h => nomatch h)⟩)
          (Or.inr (Or.inr ⟨lm21FullFnCharArr, rfl⟩)))))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 11 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .dead, .dead, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₀ hnd₁₀ hhw₁₀ hb₁₀ himm₁₀
  -- `stmt 11`: `StorageLive(4)`
  obtain ⟨m₁₂, ha₁₂, hm₁₂, hrel₁₂, hnd₁₂, hhw₁₂, hb₁₂, himm₁₂⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 9)
      lm21_fullFn_phase rfl rfl rfl hrel₁₁ hnd₁₁ hhw₁₁ hb₁₁ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₁
      (fun _ _ => .lm14Stmt (.storageLive 4 lm21UsizeDecl _ rfl))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 12 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .uninit, .dead, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₁ hnd₁₁ hhw₁₁ hb₁₁ himm₁₁
  -- `stmt 12`: `_4 = const 1_usize`
  obtain ⟨m₁₃, ha₁₃, hm₁₃, hrel₁₃, hnd₁₃, hhw₁₃, hb₁₃, himm₁₃⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 8)
      lm21_fullFn_phase rfl rfl rfl hrel₁₂ hnd₁₂ hhw₁₂ hb₁₂ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₂
      (fun tf htf =>
        .scalarStmt (.assign _ 4 lm21UsizeDecl _ rfl rfl
          (himm₁₂ 4 ⟨by decide, by decide, by decide⟩ tf htf)
          (.use _ lm21UsizeTy (lm21_fullFn_constUsize_scalar_wt tf 1 (by decide)))))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 13 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .init (.scalar ⟨1, 8⟩), .dead, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₂ hnd₁₂ hhw₁₂ hb₁₂ himm₁₂
  -- `stmt 13`: `StorageLive(5)`
  obtain ⟨m₁₄, ha₁₄, hm₁₄, hrel₁₄, hnd₁₄, hhw₁₄, hb₁₄, himm₁₄⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 7)
      lm21_fullFn_phase rfl rfl rfl hrel₁₃ hnd₁₃ hhw₁₃ hb₁₃ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₃
      (fun _ _ => .lm14Stmt (.storageLive 5 lm21I32Decl _ rfl))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 14 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .init (.scalar ⟨1, 8⟩), .uninit, .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₃ hnd₁₃ hhw₁₃ hb₁₃ himm₁₃
  -- `stmt 14`: `_5 = copy _1[_4]`
  obtain ⟨m₁₅, ha₁₅, hm₁₅, hrel₁₅, hnd₁₅, hhw₁₅, hb₁₅, himm₁₅⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 6)
      lm21_fullFn_phase rfl rfl rfl hrel₁₄ hnd₁₄ hhw₁₄ hb₁₄ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₄
      (fun tf htf =>
        .arrayStmt (.elemAssign (.readElem 5 1 lm21I32Decl lm21I32Arr3Decl (.int .i32) 3
          (.index 4) false _
          rfl lm21_wf_i32Arr3 rfl rfl
          (himm₁₄ 5 ⟨by decide, by decide, by decide⟩ tf htf)
          (.index 4 lm21UsizeDecl rfl rfl
            (Or.inl (himm₁₄ 4 ⟨by decide, by decide, by decide⟩ tf htf)))
          (Or.inr (Or.inr ⟨lm21FullFnI32Arr, rfl⟩)))))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 15 [.uninit, .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨25, 4⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₄ hnd₁₄ hhw₁₄ hb₁₄ himm₁₄
  -- `stmt 15`: `_0 = move _1[-1 of 3]`
  obtain ⟨m₁₆, ha₁₆, hm₁₆, hrel₁₆, hnd₁₆, hhw₁₆, hb₁₆, himm₁₆⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 5)
      lm21_fullFn_phase rfl rfl rfl hrel₁₅ hnd₁₅ hhw₁₅ hb₁₅ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₅
      (fun tf htf =>
        .arrayStmt (.elemAssign (.readElem 0 1 lm21I32Decl lm21I32Arr3Decl (.int .i32) 3
          (.constantIndex 1 3 true) true _
          rfl lm21_wf_i32Arr3 rfl rfl
          (himm₁₅ 0 ⟨by decide, by decide, by decide⟩ tf htf)
          (.constantIndex 1 3 true (by decide) (by decide)
            ⟨(fun h => nomatch h), (fun _ => ⟨by decide, by decide⟩)⟩)
          (Or.inr (Or.inr ⟨lm21FullFnI32Arr, rfl⟩)))))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 16 [.init (.scalar ⟨0xFFFF_FFFD, 4⟩), .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨25, 4⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₅ hnd₁₅ hhw₁₅ hb₁₅ himm₁₅
  -- `stmt 16`: `_0 = Add(copy _5, copy _0)` (`25 + (-3) = 22_i32`)
  obtain ⟨m₁₇, ha₁₇, hm₁₇, hrel₁₇, hnd₁₇, hhw₁₇, hb₁₇, himm₁₇⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 4)
      lm21_fullFn_phase rfl rfl rfl hrel₁₆ hnd₁₆ hhw₁₆ hb₁₆ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₆
      (fun tf htf =>
        .scalarStmt (.assign _ 0 lm21I32Decl _ rfl rfl
          (himm₁₆ 0 ⟨by decide, by decide, by decide⟩ tf htf)
          (.binaryOp .add _ _ lm21I32Ty lm21I32Ty lm21I32Ty
            (.copyLocal 5 lm21I32Decl rfl (by decide) (himm₁₆ 5 ⟨by decide, by decide, by decide⟩ tf htf))
            (.copyLocal 0 lm21I32Decl rfl (by decide) (himm₁₆ 0 ⟨by decide, by decide, by decide⟩ tf htf))
            (.intArithOrBitwise .add lm21I32Ty lm21I32Ty lm21I32Ty (translateIntTy .i32)
              (Or.inl rfl) (.int .i32 rfl) (.int .i32 rfl) (.int .i32 rfl)))))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 17 [.init (.scalar ⟨22, 4⟩), .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .init (.aggregate 0 lm21FullFnCharArr), .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨25, 4⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₆ hnd₁₆ hhw₁₆ hb₁₆ himm₁₆
  -- `stmt 17`: `StorageDead(3)`
  obtain ⟨m₁₈, ha₁₈, hm₁₈, hrel₁₈, hnd₁₈, hhw₁₈, hb₁₈, himm₁₈⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 3)
      lm21_fullFn_phase rfl rfl rfl hrel₁₇ hnd₁₇ hhw₁₇ hb₁₇ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₇
      (fun _ _ => .lm14Stmt (.storageDead 3 lm21CharArr2Decl _ rfl (by decide)))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 18 [.init (.scalar ⟨22, 4⟩), .init (.aggregate 0 lm21FullFnI32Arr), .init (.aggregate 0 lm21FullFnBoolArr1), .dead, .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨25, 4⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₇ hnd₁₇ hhw₁₇ hb₁₇ himm₁₇
  -- `stmt 18`: `StorageDead(2)`
  obtain ⟨m₁₉, ha₁₉, hm₁₉, hrel₁₉, hnd₁₉, hhw₁₉, hb₁₉, himm₁₉⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 2)
      lm21_fullFn_phase rfl rfl rfl hrel₁₈ hnd₁₈ hhw₁₈ hb₁₈ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₈
      (fun _ _ => .lm14Stmt (.storageDead 2 lm21BoolArr2Decl _ rfl (by decide)))
      (rfl : stepMirFn lm21FullFnBody _ =
        .step (lm21FullFnState 19 [.init (.scalar ⟨22, 4⟩), .init (.aggregate 0 lm21FullFnI32Arr), .dead, .dead, .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨25, 4⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]))
  clear hrel₁₈ hnd₁₈ hhw₁₈ hb₁₈ himm₁₈
  -- `stmt 19`: `StorageDead(1)`
  let s₂₀ := lm21FullFnState 20
    [.init (.scalar ⟨22, 4⟩), .dead, .dead, .dead, .init (.scalar ⟨1, 8⟩), .init (.scalar ⟨25, 4⟩), .init (.scalar ⟨1, 1⟩), .init (.scalar ⟨0x41, 4⟩)]
  obtain ⟨m₂₀, ha₂₀, hm₂₀, hrel₂₀, _, _, _, himm₂₀⟩ :=
    lm21_step_runBounded (Q := fun j => j ≠ 1 ∧ j ≠ 2 ∧ j ≠ 3) (optDest := none) (prevBudget := 4) (nextBudget := 4) (fuel := 1)
      lm21_fullFn_phase rfl rfl rfl hrel₁₉ hnd₁₉ hhw₁₉ hb₁₉ (Nat.le_refl _) hlim4
      (fun _ hj => ⟨hj, nofun⟩) himm₁₉
      (fun _ _ => .lm14Stmt (.storageDead 1 lm21I32Arr3Decl _ rfl (by decide)))
      (rfl : stepMirFn lm21FullFnBody _ = .step s₂₀)
  clear hrel₁₉ hnd₁₉ hhw₁₉ hb₁₉ himm₁₉
  -- `terminator` (`stmtIdx = 20`): `return_`
  have ha_ret :
      stepMirFn lm21FullFnBody s₂₀ = .ret (.normal (.scalar ⟨22, 4⟩, s₂₀.memory)) := rfl
  have hsim_ret :=
    step_terminator_goto_return_simulation hrel₂₀ lm21_fullFn_phase rfl rfl rfl rfl
      (Or.inr (Or.inl ⟨rfl, lm21I32Decl, rfl, (by decide),
        fun tf htf => himm₂₀ 0 ⟨by decide, by decide, by decide⟩ tf htf⟩))
  obtain ⟨ha_end, decl0, m_ret, retImm, hdecl0, himmRel, hframes_empty, hm_end⟩ :=
    runBounded_of_stepRel_retRoot 0 ha_ret hsim_ret
  have hdecl0_eq : decl0 = lm21I32Decl := by
    simpa [lm21FullFnBody, get?] using hdecl0.symm
  subst hdecl0_eq
  cases himmRel with
  | scalar _ msc hsc hsz hbool hchar =>
    have hmsc : msc = Miri.Memory.ScalarInt.ofUInt32 22 := by
      have hd := hsc.data_eq
      have hs := hsc.size_eq
      with_unfolding_all
        rcases msc with ⟨rawData, byteSize⟩
        dsimp only [Miri.Memory.ScalarInt.data, Miri.Memory.ScalarInt.size] at hd hs
        subst hd hs
        rfl
    subst hmsc
    refine ⟨s₂₀.memory, m_ret, hframes_empty, ?_, ?_,
      .scalar ⟨22, 4⟩ (Miri.Memory.ScalarInt.ofUInt32 22) hsc hsz hbool hchar⟩
    · rw [ha₁, ha₂, ha₃, ha₄, ha₅, ha₆, ha₇, ha₈, ha₉, ha₁₀, ha₁₁, ha₁₂, ha₁₃, ha₁₄, ha₁₅, ha₁₆, ha₁₇, ha₁₈, ha₁₉, ha₂₀, ha_end]
    · rw [hm₁, hm₂, hm₃, hm₄, hm₅, hm₆, hm₇, hm₈, hm₉, hm₁₀, hm₁₁, hm₁₂, hm₁₃, hm₁₄, hm₁₅, hm₁₆, hm₁₇, hm₁₈, hm₁₉, hm₂₀, hm_end]

end LeanMiriSpec.Correspondence.Witness
