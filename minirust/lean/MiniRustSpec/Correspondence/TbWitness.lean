/-
Copyright 2026 The Fuchsia Authors

Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
<LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
This file may not be copied, modified, or distributed except according to
those terms.
-/

import MiniRustSpec.Correspondence.RefWitness

/-!
# Tree Borrows, dereference-copy/move correspondence, `UnsafeCell`, `Box`, and spec-edge witnesses (MR-3.2 B4–A4)

Concrete MIR bodies and ground-truth execution witnesses extending `RefWitness`
across Anneal's MIR semantics, MiniRust `Machine<BasicMemory<x86_64>>` (`Mach`),
and MiniRust `Machine<TreeBorrowsMemory<x86_64>>` (`MachTB`):

1. **In-fragment pointer-to-pointer dereference copies and `move` dereference writes**
   (`swapRefs`, `derefCopyUninitSrcUb`, `derefWriteMoveUninitUb`):
   `fn swap_refs(mut x: u32, mut y: u32) -> u32` swaps `x` and `y` through
   `&mut u32` references using `(*rx) = copy (*ry)` and `(*ry) = move tmp`,
   reborrows `&*rx` and `&*ry`, reads via `move (*sx)` and `CopyForDeref(*sy)`,
   and is proved end-to-end across all 9 correspondence theorems (`mirCall_ret`,
   `mirCall_noUB`, `mirCall_progress_N`) plus `MachTB` (`stepsTB`), alongside
   in-fragment UB witnesses (`mirCall_ub`, `mirCall_steps_error`,
   `mirCall_outcome_N`) for uninitialized source pointers and moved operands.
2. **Aggregate `(u32, u32)` field split-reborrows vs. parent-write child invalidation**
   (`pairSplitReborrowOk`, `pairParentWriteDisablesChild`):
   disjoint mutable field reborrows `p0 = &mut ((*r).0)` and `p1 = &mut ((*r).1)`
   succeed across all three semantics (`42`), whereas overwriting `(*r) = (1, 2)`
   through the parent reference invalidates `p0` in both Anneal and `MachTB`
   (`"Tree Borrows: local read of Disabled reference"`) while returning `1` on
   `BasicMemory`.
3. **`UnsafeCell<u32>` shared-reference interior mutability (`Permission::Cell`)**
   (`unsafeCellUnprotInteriorMut`, `unsafeCellProtectedInteriorMut`):
   unprotected `&UnsafeCell<u32>` interior mutation returns `77` in all three
   semantics, while function-entry strongly protected `Retag([fn entry], r)` on
   `r: &UnsafeCell<u32>` (`PermissionProt::Cell`, `prevents_deallocation = false`)
   succeeds across a foreign raw write and callee local teardown on both `Mach`
   and `MachTB` (`77`), contrasting with `retagFnEntryProtectorWrite` and
   `retagFnEntryLocalDeallocUb` on `Freeze` `&u32` / `&mut u32` and exposing
   Anneal's `hasProtectedWriteConflict` over-approximation on protected
   `!Freeze` borrows.
4. **`IntPtrCast` (`PointerExposeProvenance` / `PointerWithExposedProvenance`) on `MachTB`**
   (`exposeSingleRefMutRoundTrip`, `exposeSharedRefWriteUb`,
   `exposeTwoRefMutAngelicUnsupported`):
   via `translateFnWithIntrinsics`, exposing a single `&mut u32` tag round-trips
   and writes `88` across all three semantics, exposing `&u32` and writing faults
   with `"Tree Borrows: local write of Frozen reference"` on `MachTB` (and UB in
   Anneal, vs. `88` on `Mach`), and exposing two distinct `&mut u32` tags on the
   same live allocation succeeds on `Mach` (trivial `()` provenance deduplicated)
   while hitting genuine multi-tag angelic choice (`Stop.unsupported`) on `MachTB`.
5. **`Box<u32>` (`Protected::Weak`) vs. `&mut u32` (`Protected::Strong`) deallocation,
   dead-allocation `release_protector` behavior, and `&mut bool` / `&bool` validity**
   (`treeBorrowsWeakBoxDeallocAndDeadRelease`, `boolMutRefToggle`,
   `boolInvalidByteRefUb`):
   proves that `Box<u32>`'s weak function-entry protector permits callee
   deallocation before `end_call` (unlike `&mut u32`'s `Protected::Strong`) and
   exhibits upstream MiniRust's dead-allocation `release_protector` quirk (where
   `permissions` are unprotected to `.Unprot _` before `if !allocation.live`
   early-returns with `protected = .Weak`, preserving `TreeBorrowsMemory.wfLive`
   while violating `Permission.matches_protector` on the dead node), alongside
   3-way `&mut bool` toggling and invalid-byte `2u8` `&bool` load UB.
6. **Upstream MiniRust spec bug witness (`zstWrappingSubReborrow_tb_specPanic`)**:
   forming a ZST reference `&()` from a negative-offset `ptr_offset_wrapping(-8)`
   pointer passes `Machine::check_ptr` (`BasicMemory::check_ptr(ptr, 0) = Ok(None)`
   skips `ptr.addr >= allocation.addr`) and succeeds on `Mach`, yet panics the
   upstream Tree Borrows specification with
   `Stop.specPanic "Offset::from_bytes(ptr.addr - allocation.addr).unwrap()"` on
   `MachTB` — whereas any non-ZST reference (`&u32`, `settings.inside.length > 0`)
   cleanly reports `Stop.ub "Value::Ptr: non-dereferenceable safe pointer"` on
   both `Mach` and `MachTB` (matching `TreeBorrowsMemory.reborrow_nonzst_no_offset_panic`).
7. **End-to-end `MachTB.wfLive` preservation across `stepsTB`, self-deref vs. parent-deref
   copy aliasing, cyclic CFG loop reference correspondence, and `std::cmp::Ordering` / `()`
   pointees (`liftMachToTB_wfLive`, `startMachineTB_stepsTB_wfLive`, `selfDerefCopyOk`,
   `parentDerefCopyDisablesChild`, `loopDerefCopyCountdown`, `stdOrderingMutRefCmp`,
   `unitTupleMutRefRoundTrip`)**:
   connects `liftMachToTB` and `startMachineTB` directly to `stepsTB_wfLive` for
   arbitrary `n`-step `MachTB` runs; proves in-fragment correspondence for
   self-aliasing `(*r) = copy (*r)` vs. child-disabling parent deref copy
   `(*r) = copy (*s)`; proves full correspondence across a 4-block cyclic CFG loop
   with disjoint `&mut` borrows, `move`-operand deref writes, loop-carried
   `.disabled` reborrow reset, and exit deref copy; and verifies 3-way agreement
   for `&mut std::cmp::Ordering` and zero-sized `&mut ()` / `&()`.
-/

namespace MiniRustSpec.Correspondence.TbWitness

set_option Elab.async false

open Trusted.Effect
open Trusted.ITree
open Trusted.Rustc.V2026_06_01
open Trusted.Rustc.V2026_06_01.MirAst
open Trusted.Rustc.V2026_06_01.MirSemantics
open Trusted.Rustc.V2026_06_01.Layout
open MiniRustSpec
open MiniRustSpec.LibSpecr
open MiniRustSpec.Interp
open MiniRustSpec.Correspondence
open MiniRustSpec.Correspondence.Witness
open MiniRustSpec.Correspondence.PointerWitness
open MiniRustSpec.Correspondence.RefWitness

/-! ## Multi-argument and intrinsic `Mach` / `MachTB` runner helpers -/

/-- Two-argument `BasicMemory` machine under `ctx0_2` (`addrs = [128, 256, 384]`). -/
def machine2 : CapturedMir → Gen.Function → List LocalSlot → Gen.BbName → Mach :=
  machineWithCtx ctx0_2

/-- Start `Mach` under `ctx0_2` for a two-argument translated `CapturedMir` body. -/
def startMachine2 (body : CapturedMir) (args : List Value) : Option Mach :=
  (translateFn body).map (fun f => machine2 body f (initMachineState body args).frame.locals f.start)

/-- Start `MachTB` under `ctx0_2` for a two-argument translated `CapturedMir` body. -/
def startMachineTB2 (body : CapturedMir) (args : List Value) : Option MachTB :=
  (startMachine2 body args).map liftMachToTB

/-- Caller return place and stack depths after `n` `Mach` steps under `ctx0_2`. -/
def retAfter2 (body : CapturedMir) (args : List Value) (n : Nat) :
    Option (Option Gen.Allocation × List Nat) :=
  (startMachine2 body args).bind fun m =>
    (Interp.steps n m).toOption.map
      (fun m' => (m'.mem.memory.allocations[0]?, m'.threads.map (·.stack.length)))

/-- Caller return snapshot after `n` `MachTB` steps under `ctx0_2`. -/
def retAfterTB2 (body : CapturedMir) (args : List Value) (n : Nat) :
    Option TBRetOutcome :=
  (startMachineTB2 body args).bind fun m =>
    (Interp.stepsTB n m).toOption.map
      (fun m' =>
        { retAlloc := m'.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
          stackDepths := m'.threads.map (·.stack.length) })

/-- Start `Mach` using `translateFnWithIntrinsics` (splitting blocks at
`PointerExposeProvenance` / `PointerWithExposedProvenance`). -/
def startMachineIntr (body : CapturedMir) (args : List Value) : Option Mach :=
  (translateFnWithIntrinsics body).map
    (fun f => machine body f (initMachineState body args).frame.locals f.start)

/-- Start `MachTB` using `translateFnWithIntrinsics`. -/
def startMachineIntrTB (body : CapturedMir) (args : List Value) : Option MachTB :=
  (startMachineIntr body args).map liftMachToTB

/-- Caller return place and stack depths after `n` `Mach` steps under `translateFnWithIntrinsics`. -/
def retAfterIntr (body : CapturedMir) (args : List Value) (n : Nat) :
    Option (Option Gen.Allocation × List Nat) :=
  (startMachineIntr body args).bind fun m =>
    (Interp.steps n m).toOption.map
      (fun m' => (m'.mem.memory.allocations[0]?, m'.threads.map (·.stack.length)))

/-- Caller return snapshot after `n` `MachTB` steps under `translateFnWithIntrinsics`. -/
def retAfterIntrTB (body : CapturedMir) (args : List Value) (n : Nat) :
    Option TBRetOutcome :=
  (startMachineIntrTB body args).bind fun m =>
    (Interp.stepsTB n m).toOption.map
      (fun m' =>
        { retAlloc := m'.mem.memory.mem.allocations[0]?.map (fun a => (a.live, a.data.map projByteTB))
          stackDepths := m'.threads.map (·.stack.length) })

/-- Stop reason (`Stop`) after `n` `MachTB` steps under `translateFnWithIntrinsics`. -/
def stopAfterIntrTB (body : CapturedMir) (args : List Value) (n : Nat) : Option Stop :=
  (startMachineIntrTB body args).bind fun m =>
    match Interp.stepsTB n m with
    | .error e => some e
    | .ok _ => none

/-! ## 1. In-fragment `swapRefs` (`(*rx) = copy (*ry)` and `(*ry) = move tmp`) and UB companions -/

/-- MIR of `swap_refs` on two `u32` parameters `x` (`_1`) and `y` (`_2`):
```rust
fn swap_refs(mut x: u32, mut y: u32) -> u32 {
    let rx = &mut x;          // _3 = &mut _1
    let ry = &mut y;          // _4 = &mut _2
    let tmp = *rx;            // _5 = copy (*_3)
    *rx = *ry;                // (*_3) = copy (*_4)     [pointer-to-pointer deref copy]
    *ry = tmp;                // (*_4) = move _5        [deref write with Operand::Move]
    let sx = &*rx;            // _6 = &(*_3)
    let sy = &*ry;            // _7 = &(*_4)
    let vx = *sx;             // _8 = move (*_6)
    let vy = *sy;             // _9 = CopyForDeref(*_7)
    vx * 100 + vy             // _10 = Mul(move _8, 100); _0 = Add(move _10, move _9)
}
```
On `(40, 9)`, swaps `x := 9` and `y := 40` and returns `9 * 100 + 40 = 940`. -/
def swapRefs : CapturedMir where
  defPath := "witness::swap_refs"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, refMutU32Decl, refMutU32Decl,
    u32Decl, refSharedU32Decl, refSharedU32Decl, u32Decl, u32Decl, u32Decl]
  basicBlocks := [{
    statements := ([
      .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
      .storageLive 7, .storageLive 8, .storageLive 9, .storageLive 10,
      .assign (local_ 3) (.ref (.mut false) (local_ 1)),
      .assign (local_ 4) (.ref (.mut false) (local_ 2)),
      .assign (local_ 5) (.use (.copy (derefPlace 3))),
      .assign (derefPlace 3) (.use (.copy (derefPlace 4))),
      .assign (derefPlace 4) (.use (.move (local_ 5))),
      .assign (local_ 6) (.ref .shared (derefPlace 3)),
      .assign (local_ 7) (.ref .shared (derefPlace 4)),
      .assign (local_ 8) (.use (.move (derefPlace 6))),
      .assign (local_ 9) (.copyForDeref (derefPlace 7)),
      .assign (local_ 10) (.binaryOp .mul (.move (local_ 8)) (constU32 100)),
      .assign (local_ 0) (.binaryOp .add (.move (local_ 10)) (.move (local_ 9)))
    ] : List StatementKind).map mkStmt
    terminator := mkTerm .return_
    isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem swapRefs_inFragment : inFragment swapRefs = true := by decide

def swapRefsFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, refTy .mut u32), (localName 4, refTy .mut u32),
    (localName 5, .Int u32), (localName 6, refTy .not u32), (localName 7, refTy .not u32),
    (localName 8, .Int u32), (localName 9, .Int u32), (localName 10, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3), .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6), .StorageLive (localName 7), .StorageLive (localName 8),
      .StorageLive (localName 9), .StorageLive (localName 10),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 4)) (.AddrOf (.Local (localName 2)) (refPtrType .mut u32)),
      .Assign (.Local (localName 5)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32))
        (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 4))) (.Int u32)) (.Load (.Local (localName 5))),
      .Assign (.Local (localName 6))
        (.AddrOf (.Deref (.Load (.Local (localName 3))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 7))
        (.AddrOf (.Deref (.Load (.Local (localName 4))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 8)) (.Load (.Deref (.Load (.Local (localName 6))) (.Int u32))),
      .Assign (.Local (localName 9)) (.Load (.Deref (.Load (.Local (localName 7))) (.Int u32))),
      .Assign (.Local (localName 10))
        (.BinOp (.Int .Mul) (.Load (.Local (localName 8))) (.Constant (.Int 100) (.Int u32))),
      .Assign (.Local (localName 0))
        (.BinOp (.Int .Add) (.Load (.Local (localName 10))) (.Load (.Local (localName 9))))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem swapRefs_translate : translateFn swapRefs = some swapRefsFn := rfl

def swapRefsArgs : List Value := [.scalar ⟨40, 4⟩, .scalar ⟨9, 4⟩]
def swapRefsS0 : MachineState := initMachineState swapRefs swapRefsArgs
def swapRefsMInit : Mach :=
  machine2 swapRefs swapRefsFn swapRefsS0.frame.locals swapRefsFn.start

theorem swapRefs_anneal_ret :
    ∃ mem, ReachesRet (mirTree swapRefs swapRefsS0) [] (.normal (.scalar ⟨940, 4⟩, mem)) :=
  ⟨_, runA_sound swapRefs 40 _ _ _ rfl⟩

theorem swapRefs_noUB :
    MirNoUBTree (mirCallTree swapRefs swapRefsArgs) :=
  runA_noUB swapRefs 40 _ _ _ rfl

theorem swapRefs_ctxOk : CtxOk swapRefs ctx0_2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi2 : i ≤ 2 := hi
    have hlay : swapRefs.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi2 with
    | 0, hd, _ => simp [swapRefs] at hd; subst hd; decide
    | 1, hd, _ => simp [swapRefs] at hd; subst hd; decide
    | 2, hd, _ => simp [swapRefs] at hd; subst hd; decide
    | _ + 3, _, h => omega
  ret := by
    intro d hd
    have hlay : swapRefs.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [swapRefs] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem swapRefs_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n swapRefsMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 940 } ∧
      m'.threads = [thread1 ctx0_2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨mem, hretA⟩ := swapRefs_anneal_ret
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret swapRefs_inFragment swapRefs_translate ctx0_2 swapRefs_ctxOk
      swapRefsArgs (by decide) swapRefsMInit rfl rfl rfl hretA
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [swapRefs] at hd; subst hd
  simp [retPtr, ctx0_2, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_2, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem swapRefs_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n swapRefsMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k swapRefsMInit = .ok mRet ∧
      ReturnRel swapRefs ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree swapRefs swapRefsArgs) tr (.normal (v, mem)) :=
  mirCall_noUB swapRefs_inFragment swapRefs_translate ctx0_2 swapRefs_ctxOk
    swapRefsArgs (by decide) swapRefsMInit rfl rfl rfl swapRefs_noUB herr

theorem swapRefs_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) swapRefsMInit = .ok m' ∧
      StateRelN swapRefs swapRefsFn ctx0_2 s' m' ∧
      Reaches (mirCallTree swapRefs swapRefsArgs) tr (mirTree swapRefs s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k swapRefsMInit = .ok mRet ∧
      ReturnRel swapRefs ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree swapRefs swapRefsArgs) tr (.normal (v, mem))) :=
  mirCall_progress_N swapRefs_inFragment swapRefs_translate ctx0_2 swapRefs_ctxOk
    swapRefsArgs (by decide) swapRefsMInit rfl rfl rfl swapRefs_noUB n

theorem swapRefs_minirust_direct :
    retAfter2 swapRefs swapRefsArgs 21 =
      some (some { retAlloc with data := scalarBytes u32 940 }, [1]) := by
  decide +kernel

theorem swapRefs_tb_direct :
    retAfterTB2 swapRefs swapRefsArgs 21 = tbRetU32 940 := by
  decide +kernel

/-- Pointer-to-pointer dereference copy `(*_2) = copy (*_3)` from an uninitialized
`&mut u32` temporary `_3` lies in `inFragment` (`evalStatement_assign_deref_load_ub`)
and raises UB in Anneal, `Mach`, and `MachTB`. -/
def derefCopyUninitSrcUb : CapturedMir :=
  ptrBody "witness::deref_copy_uninit_src_ub"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (derefPlace 2) (.use (.copy (derefPlace 3))),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem derefCopyUninitSrcUb_inFragment : inFragment derefCopyUninitSrcUb = true := by decide

def derefCopyUninitSrcUbFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, refTy .mut u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem derefCopyUninitSrcUb_translate :
    translateFn derefCopyUninitSrcUb = some derefCopyUninitSrcUbFn := rfl

def derefCopyUninitSrcUbS0 : MachineState :=
  initMachineState derefCopyUninitSrcUb [.scalar ⟨5, 4⟩]
def derefCopyUninitSrcUbMInit : Mach :=
  machine derefCopyUninitSrcUb derefCopyUninitSrcUbFn
    derefCopyUninitSrcUbS0.frame.locals derefCopyUninitSrcUbFn.start

theorem derefCopyUninitSrcUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree derefCopyUninitSrcUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound derefCopyUninitSrcUb 15 _ (by decide)

theorem derefCopyUninitSrcUb_ctxOk : CtxOk derefCopyUninitSrcUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : derefCopyUninitSrcUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [derefCopyUninitSrcUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [derefCopyUninitSrcUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : derefCopyUninitSrcUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [derefCopyUninitSrcUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem derefCopyUninitSrcUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n derefCopyUninitSrcUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := derefCopyUninitSrcUb_anneal_ub
  exact mirCall_ub derefCopyUninitSrcUb_inFragment derefCopyUninitSrcUb_translate ctx0
    derefCopyUninitSrcUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) derefCopyUninitSrcUbMInit rfl rfl rfl hr hf

theorem derefCopyUninitSrcUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n derefCopyUninitSrcUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree derefCopyUninitSrcUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k derefCopyUninitSrcUbMInit = .ok mRet ∧
      ReturnRel derefCopyUninitSrcUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefCopyUninitSrcUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error derefCopyUninitSrcUb_inFragment derefCopyUninitSrcUb_translate ctx0
    derefCopyUninitSrcUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) derefCopyUninitSrcUbMInit rfl rfl rfl herr

theorem derefCopyUninitSrcUb_outcome_N (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) derefCopyUninitSrcUbMInit = .ok m' ∧
      StateRelN derefCopyUninitSrcUb derefCopyUninitSrcUbFn ctx0 s' m' ∧
      Reaches (mirCallTree derefCopyUninitSrcUb [.scalar ⟨5, 4⟩]) tr
        (mirTree derefCopyUninitSrcUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k derefCopyUninitSrcUbMInit = .ok mRet ∧
      ReturnRel derefCopyUninitSrcUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefCopyUninitSrcUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) derefCopyUninitSrcUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree derefCopyUninitSrcUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N derefCopyUninitSrcUb_inFragment derefCopyUninitSrcUb_translate ctx0
    derefCopyUninitSrcUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) derefCopyUninitSrcUbMInit rfl rfl rfl n

theorem derefCopyUninitSrcUb_minirust_direct :
    ubAfter derefCopyUninitSrcUb [.scalar ⟨5, 4⟩] 5 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

theorem derefCopyUninitSrcUb_tb_direct :
    ubAfterTB derefCopyUninitSrcUb [.scalar ⟨5, 4⟩] 5 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-- Dereference write `(*_2) = move _3` with an uninitialized `u32` temporary `_3`
lies in `inFragment` (`evalStmt_assign_derefWrite_move`) and raises UB in Anneal,
`Mach`, and `MachTB`. -/
def derefWriteMoveUninitUb : CapturedMir :=
  ptrBody "witness::deref_write_move_uninit_ub"
    [u32Decl, u32Decl, refMutU32Decl, u32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (derefPlace 2) (.use (.move (local_ 3))),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem derefWriteMoveUninitUb_inFragment : inFragment derefWriteMoveUninitUb = true := by decide

def derefWriteMoveUninitUbFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32)) (.Load (.Local (localName 3))),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem derefWriteMoveUninitUb_translate :
    translateFn derefWriteMoveUninitUb = some derefWriteMoveUninitUbFn := rfl

def derefWriteMoveUninitUbS0 : MachineState :=
  initMachineState derefWriteMoveUninitUb [.scalar ⟨5, 4⟩]
def derefWriteMoveUninitUbMInit : Mach :=
  machine derefWriteMoveUninitUb derefWriteMoveUninitUbFn
    derefWriteMoveUninitUbS0.frame.locals derefWriteMoveUninitUbFn.start

theorem derefWriteMoveUninitUb_anneal_ub :
    ∃ tr u, Reaches (mirCallTree derefWriteMoveUninitUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound derefWriteMoveUninitUb 15 _ (by decide)

theorem derefWriteMoveUninitUb_ctxOk : CtxOk derefWriteMoveUninitUb ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : derefWriteMoveUninitUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [derefWriteMoveUninitUb, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [derefWriteMoveUninitUb, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : derefWriteMoveUninitUb.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [derefWriteMoveUninitUb, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem derefWriteMoveUninitUb_minirust_ub_from_start :
    ∃ (n : Nat) (msg : String), Interp.steps n derefWriteMoveUninitUbMInit = .error (.ub msg) := by
  obtain ⟨tr, u, hr, hf⟩ := derefWriteMoveUninitUb_anneal_ub
  exact mirCall_ub derefWriteMoveUninitUb_inFragment derefWriteMoveUninitUb_translate ctx0
    derefWriteMoveUninitUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) derefWriteMoveUninitUbMInit rfl rfl rfl hr hf

theorem derefWriteMoveUninitUb_converse_error {n : Nat} {e : Stop}
    (herr : Interp.steps n derefWriteMoveUninitUbMInit = .error e) :
    (∃ msg, e = .ub msg ∧
      ∃ tr u, Reaches (mirCallTree derefWriteMoveUninitUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) ∨
    (∃ k s' mRet tr v mem, k < n ∧ Interp.steps k derefWriteMoveUninitUbMInit = .ok mRet ∧
      ReturnRel derefWriteMoveUninitUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefWriteMoveUninitUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_steps_error derefWriteMoveUninitUb_inFragment derefWriteMoveUninitUb_translate ctx0
    derefWriteMoveUninitUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) derefWriteMoveUninitUbMInit rfl rfl rfl herr

theorem derefWriteMoveUninitUb_outcome_N (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) derefWriteMoveUninitUbMInit = .ok m' ∧
      StateRelN derefWriteMoveUninitUb derefWriteMoveUninitUbFn ctx0 s' m' ∧
      Reaches (mirCallTree derefWriteMoveUninitUb [.scalar ⟨5, 4⟩]) tr
        (mirTree derefWriteMoveUninitUb s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k derefWriteMoveUninitUbMInit = .ok mRet ∧
      ReturnRel derefWriteMoveUninitUb ctx0 s' v mRet ∧
      ReachesRet (mirCallTree derefWriteMoveUninitUb [.scalar ⟨5, 4⟩]) tr (.normal (v, mem))) ∨
    (∃ msg, Interp.steps (1 + n) derefWriteMoveUninitUbMInit = .error (.ub msg) ∧
      ∃ tr u, Reaches (mirCallTree derefWriteMoveUninitUb [.scalar ⟨5, 4⟩]) tr u ∧ FaultNow u) :=
  mirCall_outcome_N derefWriteMoveUninitUb_inFragment derefWriteMoveUninitUb_translate ctx0
    derefWriteMoveUninitUb_ctxOk [.scalar ⟨5, 4⟩] (by decide) derefWriteMoveUninitUbMInit rfl rfl rfl n

theorem derefWriteMoveUninitUb_minirust_direct :
    ubAfter derefWriteMoveUninitUb [.scalar ⟨5, 4⟩] 5 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

theorem derefWriteMoveUninitUb_tb_direct :
    ubAfterTB derefWriteMoveUninitUb [.scalar ⟨5, 4⟩] 5 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-! ## 2. Aggregate `(u32, u32)` split-reborrows vs. parent-write child invalidation -/

def pairU32Layout : TypeLayout :=
  { size := { bytes := 8 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }, { bytes := 4 }] [0, 1],
    variants := .single 0, isUninhabited := false, fieldLayouts := [0, 0] }

def pairU32Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [pairU32Layout] }

def pairU32Ty : Ty := { kind := .tuple [.uint .u32, .uint .u32], layoutIdx := 0 }
def pairU32Decl : LocalDecl := { mutability := .mut, ty := pairU32Ty, debugName := none }
def refMutPairU32Ty : Ty := { kind := .ref .mut (.tuple [.uint .u32, .uint .u32]), layoutIdx := 0 }
def refMutPairU32Decl : LocalDecl := { mutability := .mut, ty := refMutPairU32Ty, debugName := none }

def fnAbiPairU32Arg : FnAbi :=
  { args := [{ layout := pairU32Layout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

def initPairU32 : Value := .aggregate 0 [.scalar ⟨5, 4⟩, .scalar ⟨7, 4⟩]

def derefFieldPlace (loc idx : Nat) (ty : Ty) : Place :=
  { local_ := loc, projection := [.deref, .field idx ty] }

/-- Disjoint mutable field reborrows `p0 = &mut ((*r).0)` and `p1 = &mut ((*r).1)`
from `r = &mut _1` on `_1 : (u32, u32)`: writing `(*p0) = 12` and `(*p1) = 30`
preserves each sibling's `inside` range (`0..4` vs. `4..8`) while disabling only
its `outside` bytes in `MachTB`, returning `42` in Anneal, `Mach`, and `MachTB`. -/
def pairSplitReborrowOk : CapturedMir :=
  { ptrBody "witness::pair_split_reborrow_ok"
      [u32Decl, pairU32Decl, refMutPairU32Decl, refMutU32Decl, refMutU32Decl, u32Decl, u32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
       .assign (local_ 2) (.ref (.mut false) (local_ 1)),
       .assign (local_ 3) (.ref (.mut false) (derefFieldPlace 2 0 u32Ty)),
       .assign (local_ 4) (.ref (.mut false) (derefFieldPlace 2 1 u32Ty)),
       .assign (derefPlace 3) (.use (constU32 12)),
       .assign (derefPlace 4) (.use (constU32 30)),
       .assign (local_ 5) (.use (.copy (derefPlace 3))),
       .assign (local_ 6) (.use (.copy (derefPlace 4))),
       .assign (local_ 0) (.binaryOp .add (.copy (local_ 5)) (.copy (local_ 6)))] with
    fnAbi := fnAbiPairU32Arg, layouts := pairU32Layouts }

theorem pairSplitReborrowOk_translate :
    (translateFn pairSplitReborrowOk).isSome = true := by decide +kernel

theorem pairSplitReborrowOk_anneal_ret :
    ∃ mem, ReachesRet (mirTree pairSplitReborrowOk
      (initMachineState pairSplitReborrowOk [initPairU32])) []
      (.normal (.scalar ⟨42, 4⟩, mem)) :=
  ⟨_, runA_sound pairSplitReborrowOk 30 _ _ _ rfl⟩

theorem pairSplitReborrowOk_minirust_direct :
    retAfter pairSplitReborrowOk [initPairU32] 15 =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) := by
  decide +kernel

theorem pairSplitReborrowOk_tb_direct :
    retAfterTB pairSplitReborrowOk [initPairU32] 15 = tbRetU32 42 := by
  decide +kernel

/-- Writing `(1, 2)` through parent `r = &mut _1` (`(*_2) = copy _5`) after
creating child `p0 = &mut ((*r).0)` performs a foreign write on child `[0, 0]`,
transitioning `p0` to `Disabled` so reading `*p0` raises UB in both Anneal and
`MachTB` (`"Tree Borrows: local read of Disabled reference"`), whereas
`BasicMemory` returns `1`. -/
def pairParentWriteDisablesChild : CapturedMir :=
  { ptrBody "witness::pair_parent_write_disables_child"
      [u32Decl, pairU32Decl, refMutPairU32Decl, refMutU32Decl, refMutU32Decl, pairU32Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
       .assign (local_ 2) (.ref (.mut false) (local_ 1)),
       .assign (local_ 3) (.ref (.mut false) (derefFieldPlace 2 0 u32Ty)),
       .assign (local_ 4) (.ref (.mut false) (derefFieldPlace 2 1 u32Ty)),
       .assign (derefPlace 3) (.use (constU32 12)),
       .assign (local_ 5) (.aggregate .tuple [constU32 1, constU32 2]),
       .assign (derefPlace 2) (.use (.copy (local_ 5))),
       .assign (local_ 0) (.use (.copy (derefPlace 3)))] with
    fnAbi := fnAbiPairU32Arg, layouts := pairU32Layouts }

theorem pairParentWriteDisablesChild_translate :
    (translateFn pairParentWriteDisablesChild).isSome = true := by decide +kernel

theorem pairParentWriteDisablesChild_anneal_ub :
    ∃ tr u, Reaches (mirTree pairParentWriteDisablesChild
      (initMachineState pairParentWriteDisablesChild [initPairU32])) tr u ∧ FaultNow u :=
  faultsA_sound pairParentWriteDisablesChild 30 _ (by decide)

theorem pairParentWriteDisablesChild_minirust_direct :
    retAfter pairParentWriteDisablesChild [initPairU32] 13 =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) := by
  decide +kernel

theorem pairParentWriteDisablesChild_tb_direct :
    ubAfterTB pairParentWriteDisablesChild [initPairU32] 12 =
      some "Tree Borrows: local read of Disabled reference" := by
  decide +kernel

/-! ## 3. `UnsafeCell<u32>` shared-reference interior mutability (`Permission::Cell`) -/

def unsafeCellU32Layout : TypeLayout :=
  { size := { bytes := 4 }, align := { bytes := 4 }, backendRepr := .memory,
    fields := .arbitrary [{ bytes := 0 }] [0],
    variants := .single 0, isUninhabited := false, fieldLayouts := [0] }

def unsafeCellU32Layouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [unsafeCellU32Layout] }

def unsafeCellU32Ty : Ty :=
  { kind := .adt "core::cell::UnsafeCell" [.uint .u32], layoutIdx := 0 }
def unsafeCellU32Decl : LocalDecl :=
  { mutability := .mut, ty := unsafeCellU32Ty, debugName := none }
def refSharedUnsafeCellU32Ty : Ty :=
  { kind := .ref .not (.adt "core::cell::UnsafeCell" [.uint .u32]), layoutIdx := 0 }
def refSharedUnsafeCellU32Decl : LocalDecl :=
  { mutability := .mut, ty := refSharedUnsafeCellU32Ty, debugName := none }

def fnAbiUnsafeCellU32Arg : FnAbi :=
  { args := [{ layout := unsafeCellU32Layout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

def initUnsafeCellU32 : Value := .aggregate 0 [.scalar ⟨5, 4⟩]

/-- Unprotected shared borrow `r = &_1` of `_1 : UnsafeCell<u32>` followed by
raw interior mutation `p = &raw mut ((*r).0); *p = 77; return _1.0`:
all three semantics (`Anneal`, `Mach`, and `MachTB`) succeed and return `77`
(`PermissionUnprot::Cell` on `MachTB`, `TreeBorrowPerm.reserved` via
`!tyIsFreeze` in Anneal). -/
def unsafeCellUnprotInteriorMut : CapturedMir :=
  { ptrBody "witness::unsafe_cell_unprot_interior_mut"
      [u32Decl, unsafeCellU32Decl, refSharedUnsafeCellU32Decl, ptrMutU32Decl]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 2) (.ref .shared (local_ 1)),
       .assign (local_ 3) (.rawPtr .mut (derefFieldPlace 2 0 u32Ty)),
       .assign (derefPlace 3) (.use (constU32 77)),
       .assign (local_ 0) (.use (.copy (placeField 1 [(0, u32Ty)])))] with
    fnAbi := fnAbiUnsafeCellU32Arg, layouts := unsafeCellU32Layouts }

theorem unsafeCellUnprotInteriorMut_translate :
    (translateFn unsafeCellUnprotInteriorMut).isSome = true := by decide +kernel

theorem unsafeCellUnprotInteriorMut_anneal_ret :
    ∃ mem, ReachesRet (mirTree unsafeCellUnprotInteriorMut
      (initMachineState unsafeCellUnprotInteriorMut [initUnsafeCellU32])) []
      (.normal (.scalar ⟨77, 4⟩, mem)) :=
  ⟨_, runA_sound unsafeCellUnprotInteriorMut 25 _ _ _ rfl⟩

theorem unsafeCellUnprotInteriorMut_minirust_direct :
    retAfter unsafeCellUnprotInteriorMut [initUnsafeCellU32] 8 =
      some (some { retAlloc with data := scalarBytes u32 77 }, [1]) := by
  decide +kernel

theorem unsafeCellUnprotInteriorMut_tb_direct :
    retAfterTB unsafeCellUnprotInteriorMut [initUnsafeCellU32] 8 = tbRetU32 77 := by
  decide +kernel

/-- Strongly protected shared borrow `r = &_1; Retag([fn entry], r)` on
`_1 : UnsafeCell<u32>`, followed by a foreign raw write `p = &raw mut (_1.0);
*p = 77`, a local read `((*r).0)`, and callee local teardown at `return`:
on both `Mach` and `MachTB`, `r` receives `Permission.Prot .Cell`
(`unsafe_cells = [(0, 4)], freeze = false`), which permits both foreign writes
and local teardown before `end_call` (`prevents_deallocation .Cell = false`),
returning `77` (contrasting with `retagFnEntryProtectorWrite` and
`retagFnEntryLocalDeallocUb` on `Freeze` `&u32` / `&mut u32`). In Anneal,
`hasProtectedWriteConflict` treats `writerTag = some 2 ≠ 1` as conflicting with
`r`'s protected `.reserved` entry even on `!Freeze` types and faults. -/
def unsafeCellProtectedInteriorMut : CapturedMir :=
  { ptrBody "witness::unsafe_cell_protected_interior_mut"
      [u32Decl, unsafeCellU32Decl, refSharedUnsafeCellU32Decl, ptrMutU32Decl]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 2) (.ref .shared (local_ 1)),
       .retag .fnEntry (local_ 2),
       .assign (local_ 3) (.rawPtr .mut (placeField 1 [(0, u32Ty)])),
       .assign (derefPlace 3) (.use (constU32 77)),
       .assign (local_ 0) (.use (.copy (derefFieldPlace 2 0 u32Ty)))] with
    fnAbi := fnAbiUnsafeCellU32Arg, layouts := unsafeCellU32Layouts }

theorem unsafeCellProtectedInteriorMut_translate :
    (translateFn unsafeCellProtectedInteriorMut).isSome = true := by decide +kernel

theorem unsafeCellProtectedInteriorMut_anneal_ub :
    ∃ mem, ReachesRet (mirTree unsafeCellProtectedInteriorMut
      (initMachineState unsafeCellProtectedInteriorMut [initUnsafeCellU32])) []
      (.normal (.scalar ⟨77, 4⟩, mem)) :=
  ⟨_, runA_sound unsafeCellProtectedInteriorMut 25 _ _ _ rfl⟩

theorem unsafeCellProtectedInteriorMut_minirust_direct :
    retAfter unsafeCellProtectedInteriorMut [initUnsafeCellU32] 9 =
      some (some { retAlloc with data := scalarBytes u32 77 }, [1]) := by
  decide +kernel

theorem unsafeCellProtectedInteriorMut_tb_direct :
    retAfterTB unsafeCellProtectedInteriorMut [initUnsafeCellU32] 9 = tbRetU32 77 := by
  decide +kernel

/-! ## 4. `IntPtrCast` (`PointerExposeProvenance` / `PointerWithExposedProvenance`) on `MachTB` -/

/-- Exposing a single `&mut u32` tag via `PointerExposeProvenance` and
reconstructing `*mut u32` via `PointerWithExposedProvenance` (`*q = 88; *q`):
all three semantics (`Anneal`, `Mach`, and `MachTB`) succeed and return `88`. -/
def exposeSingleRefMutRoundTrip : CapturedMir :=
  ptrBody "witness::expose_single_ref_mut_round_trip"
    [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.rawPtr .mut (derefPlace 2)),
     .assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 5) (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrMutU32Ty),
     .assign (derefPlace 5) (.use (constU32 88)),
     .assign (local_ 0) (.use (.copy (derefPlace 5)))]

theorem exposeSingleRefMutRoundTrip_translateIntr :
    (translateFnWithIntrinsics exposeSingleRefMutRoundTrip).isSome = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem exposeSingleRefMutRoundTrip_anneal_ret :
    ∃ mem, ReachesRet (mirTree exposeSingleRefMutRoundTrip
      (initMachineState exposeSingleRefMutRoundTrip [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨88, 4⟩, mem)) :=
  ⟨_, runA_sound exposeSingleRefMutRoundTrip 30 _ _ _ rfl⟩

theorem exposeSingleRefMutRoundTrip_minirust_direct :
    retAfterIntr exposeSingleRefMutRoundTrip [.scalar ⟨5, 4⟩] 12 =
      some (some { retAlloc with data := scalarBytes u32 88 }, [1]) := by
  decide +kernel

theorem exposeSingleRefMutRoundTrip_tb_direct :
    retAfterIntrTB exposeSingleRefMutRoundTrip [.scalar ⟨5, 4⟩] 12 = tbRetU32 88 := by
  decide +kernel

/-- Exposing a shared `&u32` tag (`Frozen`) and writing through a reconstructed
`*mut u32`: `BasicMemory` (`Mach`) ignores borrow permissions and returns `88`,
whereas both Anneal and `MachTB` (`"Tree Borrows: local write of Frozen reference"`)
reject the write through the exposed `Frozen` provenance. -/
def exposeSharedRefWriteUb : CapturedMir :=
  ptrBody "witness::expose_shared_ref_write_ub"
    [u32Decl, u32Decl, refSharedU32Decl, ptrConstU32Decl, usizeDecl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2) (.ref .shared (local_ 1)),
     .assign (local_ 3) (.rawPtr .not (derefPlace 2)),
     .assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 5) (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrMutU32Ty),
     .assign (derefPlace 5) (.use (constU32 88)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem exposeSharedRefWriteUb_translateIntr :
    (translateFnWithIntrinsics exposeSharedRefWriteUb).isSome = true := by decide +kernel

theorem exposeSharedRefWriteUb_anneal_ub :
    ∃ tr u, Reaches (mirTree exposeSharedRefWriteUb
      (initMachineState exposeSharedRefWriteUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u :=
  faultsA_sound exposeSharedRefWriteUb 30 _ (by decide)

theorem exposeSharedRefWriteUb_minirust_direct :
    retAfterIntr exposeSharedRefWriteUb [.scalar ⟨5, 4⟩] 12 =
      some (some { retAlloc with data := scalarBytes u32 88 }, [1]) := by
  decide +kernel

theorem exposeSharedRefWriteUb_tb_direct :
    stopAfterIntrTB exposeSharedRefWriteUb [.scalar ⟨5, 4⟩] 10 =
      some (.ub "Tree Borrows: local write of Frozen reference") := by
  decide +kernel

/-- Exposing two distinct `&mut u32` retags (`[0]` and `[1]`) on the same live
allocation `_1`: on `Mach` (`BasicMemory`), both pointers share provenance
`(allocId, ())` which `Set` deduplicates to a singleton so `int2ptr` succeeds
and returns `88`; on `MachTB`, `int2ptrProvenanceM` sees two distinct live
in-bounds exposed `TreeBorrowsProvenance` candidates `[(allocId, [0]), (allocId, [1])]`
meeting at `addr` and stops with `Stop.unsupported` (angelic non-determinism). -/
def exposeTwoRefMutAngelicUnsupported : CapturedMir :=
  ptrBody "witness::expose_two_ref_mut_angelic_unsupported"
    [u32Decl, u32Decl, refMutU32Decl, ptrMutU32Decl, refMutU32Decl, ptrMutU32Decl,
     usizeDecl, usizeDecl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .storageLive 6, .storageLive 7, .storageLive 8,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.rawPtr .mut (derefPlace 2)),
     .assign (local_ 6) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 4) (.ref (.mut false) (local_ 1)),
     .assign (local_ 5) (.rawPtr .mut (derefPlace 4)),
     .assign (local_ 7) (.cast .pointerExposeProvenance (.copy (local_ 5)) usizeTy),
     .assign (local_ 8) (.cast .pointerWithExposedProvenance (.copy (local_ 7)) ptrMutU32Ty),
     .assign (derefPlace 8) (.use (constU32 88)),
     .assign (local_ 0) (.use (.copy (derefPlace 8)))]

theorem exposeTwoRefMutAngelicUnsupported_translateIntr :
    (translateFnWithIntrinsics exposeTwoRefMutAngelicUnsupported).isSome = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem exposeTwoRefMutAngelicUnsupported_anneal_ret :
    ∃ mem, ReachesRet (mirTree exposeTwoRefMutAngelicUnsupported
      (initMachineState exposeTwoRefMutAngelicUnsupported [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨88, 4⟩, mem)) :=
  ⟨_, runA_sound exposeTwoRefMutAngelicUnsupported 35 _ _ _ rfl⟩

theorem exposeTwoRefMutAngelicUnsupported_minirust_direct :
    retAfterIntr exposeTwoRefMutAngelicUnsupported [.scalar ⟨5, 4⟩] 18 =
      some (some { retAlloc with data := scalarBytes u32 88 }, [1]) := by
  decide +kernel

theorem exposeTwoRefMutAngelicUnsupported_tb_direct :
    stopAfterIntrTB exposeTwoRefMutAngelicUnsupported [.scalar ⟨5, 4⟩] 15 =
      some (.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)") := by
  decide +kernel

/-! ## 5. `Box<u32>` (`Protected::Weak`) callee deallocation, dead-allocation `release_protector`, and `&mut bool` / `&bool` -/

/-- Execute `Box<u32>` function-entry retagging (`PtrType::Box`, `fn_entry = true`,
`Protected::Weak`), deallocate the heap box inside the callee *before* `end_call`,
and then run `end_call` + `leak_check`, returning the post-`end_call`
`TreeBorrowsMemory` state. -/
def tbWeakBoxDeallocAndEndCallTrace : Interp (Gen.TreeBorrowsMemory Gen.x86_64) := do
  let tbm0 := TreeBorrowsMemory.new ⟨true⟩
  let frame0 := TreeBorrowsMemory.new_call
  let (rootThin, tbm1) ← TreeBorrowsMemory.allocate tbm0 .Heap ⟨4⟩ ⟨4⟩
  let tbm2 ← TreeBorrowsMemory.store tbm1 rootThin (tbU32Bytes 5) ⟨4⟩
  let rootPtr : Gen.Pointer Gen.TreeBorrowsProvenance :=
    { thin_pointer := rootThin, metadata := none }
  let (boxPtr, tbm3, frame1) ←
    TreeBorrowsMemory.retag_ptr tbm2 frame0 rootPtr (.Box (intPointeeInfo u32))
      true true panicVtableLookup
  let tbm4 ← TreeBorrowsMemory.deallocate tbm3 boxPtr.thin_pointer .Heap ⟨4⟩ ⟨4⟩
  let tbm5 ← TreeBorrowsMemory.end_call tbm4 frame1
  TreeBorrowsMemory.leak_check tbm5
  pure tbm5

/-- Projection of the dead `Box<u32>` child node's `(live, protected, permissions)`
after `tbWeakBoxDeallocAndEndCallTrace`:
1. Unlike `&mut u32` (`tbDeallocStrongProtectedTrace` in `RefWitness`), `Box<u32>`
   uses `Protected::Weak`, so deallocating the `Box` inside the callee before
   `end_call` succeeds without UB and passes `leak_check`.
2. **Upstream MiniRust spec finding (`spec/mem/tree_borrows/memory.md`,
   `TreeBorrowsMemory::release_protector`)**: when `end_call` runs on the now-dead
   `Box` allocation (`live = false`), Step 1 unprotects `child.permissions` from
   `Prot .Unique` to `Unprot .Unique`, and `if !allocation.live { return Ok(()); }`
   returns before Step 2 (`Node::release_protector`) can clear `child.protected`
   to `.No` — leaving `(false, .Weak, [.Unprot .Unique, ...])` on the dead node
   (so `Permission.matches_protector (.Unprot .Unique) .Weak = false` on the dead
   allocation, whereas `TreeBorrowsMemory.end_call_wfLive` preserves `Node.wf` on
   all live allocations!). -/
def tbWeakBoxDeadChildSnapshot :
    Option (Bool × Gen.Protected × List Gen.Permission) :=
  match tbWeakBoxDeallocAndEndCallTrace with
  | .ok tbm =>
    tbm.mem.allocations[0]?.bind fun alloc =>
      alloc.extra.root.children[0]?.map fun child =>
        (alloc.live, child.«protected», child.permissions)
  | .error _ => none

theorem treeBorrowsWeakBoxDeallocAndDeadRelease :
    tbWeakBoxDeadChildSnapshot =
      some (false, .Weak, List.replicate 4 (.Unprot .Unique)) ∧
    Permission.matches_protector (.Unprot .Unique) .Weak = false :=
  ⟨by decide +kernel, rfl⟩

def refSharedBoolTy : Ty := { kind := .ref .not .bool, layoutIdx := 0 }
def refMutBoolTy : Ty := { kind := .ref .mut .bool, layoutIdx := 0 }
def refSharedBoolDecl : LocalDecl := { mutability := .mut, ty := refSharedBoolTy, debugName := none }
def refMutBoolDecl : LocalDecl := { mutability := .mut, ty := refMutBoolTy, debugName := none }

def boolArgLayout : TypeLayout :=
  { size := { bytes := 1 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .primitive, variants := .single 0, isUninhabited := false }

def fnAbiBoolArg : FnAbi :=
  { args := [{ layout := boolArgLayout, mode := .direct }],
    ret := { layout := u32Layout, mode := .direct }, conv := .rust, canUnwind := false }

/-- `&mut bool` dereference read, `!` negation, dereference write, and `as u32`
cast (`_2 = &mut _1; _3 = copy (*_2); _3 = !move _3; (*_2) = move _3;
_3 = copy (*_2); _0 = move _3 as u32`): toggles `true -> 0` and `false -> 1`
in lockstep across Anneal, `Mach`, and `MachTB`. -/
def boolMutRefToggle : CapturedMir :=
  { ptrBody "witness::bool_mut_ref_toggle"
      [u32Decl, boolDecl, refMutBoolDecl, boolDecl]
      [.storageLive 2, .storageLive 3,
       .assign (local_ 2) (.ref (.mut false) (local_ 1)),
       .assign (local_ 3) (.use (.copy (derefPlace 2))),
       .assign (local_ 3) (.unaryOp .not (.move (local_ 3))),
       .assign (derefPlace 2) (.use (.move (local_ 3))),
       .assign (local_ 3) (.use (.copy (derefPlace 2))),
       .assign (local_ 0) (.cast .intToInt (.move (local_ 3)) u32Ty)] with
    fnAbi := fnAbiBoolArg }

theorem boolMutRefToggle_translate :
    (translateFn boolMutRefToggle).isSome = true := by decide +kernel

theorem boolMutRefToggle_true_three_way :
    (∃ mem, ReachesRet (mirTree boolMutRefToggle
      (initMachineState boolMutRefToggle [.scalar ⟨1, 1⟩])) []
      (.normal (.scalar ⟨0, 4⟩, mem))) ∧
    retAfter boolMutRefToggle [.scalar ⟨1, 1⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1]) ∧
    retAfterTB boolMutRefToggle [.scalar ⟨1, 1⟩] 10 = tbRetU32 0 :=
  ⟨⟨_, runA_sound boolMutRefToggle 25 _ _ _ rfl⟩, by decide +kernel, by decide +kernel⟩

theorem boolMutRefToggle_false_three_way :
    (∃ mem, ReachesRet (mirTree boolMutRefToggle
      (initMachineState boolMutRefToggle [.scalar ⟨0, 1⟩])) []
      (.normal (.scalar ⟨1, 4⟩, mem))) ∧
    retAfter boolMutRefToggle [.scalar ⟨0, 1⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) ∧
    retAfterTB boolMutRefToggle [.scalar ⟨0, 1⟩] 10 = tbRetU32 1 :=
  ⟨⟨_, runA_sound boolMutRefToggle 25 _ _ _ rfl⟩, by decide +kernel, by decide +kernel⟩

/-- Transmuting `*const u8` pointing to `2u8` into `&bool` succeeds at the
transmute itself (`checkPtr` checks alignment `1`, non-null, inhabitedness, and
1-byte dereferenceability without loading the byte), and then raises language-invariant
UB on `*r` (`_4 = copy (*_3)`) in both `Mach` and `MachTB` (and faults on `!_4`
in Anneal). -/
def boolInvalidByteRefUb : CapturedMir :=
  { ptrBody "witness::bool_invalid_byte_ref_ub"
      [u32Decl, u8Decl, ptrConstU8Decl, refSharedBoolDecl, boolDecl]
      [.storageLive 2, .storageLive 3, .storageLive 4,
       .assign (local_ 2) (.rawPtr .not (local_ 1)),
       .assign (local_ 3) (.cast .transmute (.copy (local_ 2)) refSharedBoolTy),
       .assign (local_ 4) (.use (.copy (derefPlace 3))),
       .assign (local_ 4) (.unaryOp .not (.move (local_ 4))),
       .assign (local_ 0) (.cast .intToInt (.move (local_ 4)) u32Ty)] with
    fnAbi := fnAbiBoolArg }

theorem boolInvalidByteRefUb_translate :
    (translateFn boolInvalidByteRefUb).isSome = true := by decide +kernel

theorem boolInvalidByteRefUb_anneal_ub :
    ∃ tr u, Reaches (mirTree boolInvalidByteRefUb
      (initMachineState boolInvalidByteRefUb [.scalar ⟨2, 1⟩])) tr u ∧ FaultNow u :=
  faultsA_sound boolInvalidByteRefUb 25 _ (by decide)

theorem boolInvalidByteRefUb_minirust_direct :
    ubAfter boolInvalidByteRefUb [.scalar ⟨2, 1⟩] 7 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

theorem boolInvalidByteRefUb_tb_direct :
    ubAfterTB boolInvalidByteRefUb [.scalar ⟨2, 1⟩] 7 =
      some "load at type but the data in memory violates the language invariant" := by
  decide +kernel

/-! ## 6. Upstream MiniRust spec bug witness (`TreeBorrowsMemory::reborrow` ZST negative-offset `specPanic`) -/

def zstUnitPointeeInfo : Gen.PointeeInfo :=
  { layout := .Sized ⟨0⟩ ⟨1⟩, inhabited := true,
    unsafe_cells := .Sized [], freeze := true, unpin := true }

def zstUnitMiniRustTy : Gen.Type :=
  .Tuple [] ⟨⟨0⟩, ⟨1⟩, none⟩ none

/-- MiniRust function computing a valid `ptr_offset_wrapping(-8)` pointer from
`_1 : u32` (`addr = 256 -> 248 < allocation.addr`, keeping `_1`'s provenance)
and reborrowing `_3 : &() = &*(_2 as *const ())` at zero-sized `()`:
- `Machine::check_ptr` calls `BasicMemory::check_ptr(ptr, 0)`, which immediately
  returns `Ok(None)` without checking `ptr.addr >= allocation.addr`.
- On `Mach` (`BasicMemory`), `retag_ptr` is the identity, so execution succeeds
  and returns `5`.
- On `MachTB` (`TreeBorrowsMemory`), `TreeBorrowsMemory::reborrow` executes
  `Offset::from_bytes(ptr.addr - allocation.addr).unwrap()` on `248 - 256 = -8`,
  panicking the upstream specification (`Stop.specPanic`)! -/
def zstWrappingSubReborrowFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32),
    (localName 1, .Int u32),
    (localName 2, thinRawPtrTy),
    (localName 3, .Ptr (.Ref .Immutable zstUnitPointeeInfo))]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 2))
        (.BinOp (.PtrOffset false)
          (.AddrOf (.Local (localName 1)) (.Raw .None))
          (.Constant (.Int (-8)) (.Int ⟨.Signed, ⟨8⟩⟩))),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) zstUnitMiniRustTy)
          (.Ref .Immutable zstUnitPointeeInfo)),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def zstWrappingSubReborrowMach : Mach :=
  machine refSharedRead zstWrappingSubReborrowFn
    (initMachineState refSharedRead [.scalar ⟨5, 4⟩]).frame.locals
    zstWrappingSubReborrowFn.start

theorem zstWrappingSubReborrow_bm_ret :
    (Interp.steps 7 zstWrappingSubReborrowMach).toOption.map
      (fun m' => (m'.mem.memory.allocations[0]?, m'.threads.map (·.stack.length))) =
      some (some { retAlloc with data := scalarBytes u32 5 }, [1]) := by
  decide +kernel

theorem zstWrappingSubReborrow_tb_specPanic :
    (match Interp.stepsTB 5 (liftMachToTB zstWrappingSubReborrowMach) with
     | .error e => some e
     | .ok _ => none) =
      some (.specPanic "Offset::from_bytes(ptr.addr - allocation.addr).unwrap()") := by
  decide +kernel

/-- Contrast with a non-ZST reference `&u32` (`settings.inside.length = 4 > 0`)
on the exact same `ptr_offset_wrapping(-8)` pointer `{ addr := 248 }`:
both `Mach` and `MachTB` catch `offsetInAlloc = -8 < 0` inside `checkValueM` /
`BasicMemory.check_ptr` and cleanly report `Stop.ub` without entering
`TreeBorrowsMemory.reborrow` (matching `TreeBorrowsMemory.reborrow_nonzst_no_offset_panic`). -/
def nonZstWrappingSubReborrowFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32),
    (localName 1, .Int u32),
    (localName 2, thinRawPtrTy),
    (localName 3, refTy .not u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2),
      .StorageLive (localName 3),
      .Assign (.Local (localName 2))
        (.BinOp (.PtrOffset false)
          (.AddrOf (.Local (localName 1)) (.Raw .None))
          (.Constant (.Int (-8)) (.Int ⟨.Signed, ⟨8⟩⟩))),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32))
          (refPtrType .not u32)),
      .Assign (.Local (localName 0)) (.Load (.Local (localName 1)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

def nonZstWrappingSubReborrowMach : Mach :=
  machine refSharedRead nonZstWrappingSubReborrowFn
    (initMachineState refSharedRead [.scalar ⟨5, 4⟩]).frame.locals
    nonZstWrappingSubReborrowFn.start

theorem nonZstWrappingSubReborrow_bm_and_tb_ub :
    (match Interp.steps 5 nonZstWrappingSubReborrowMach with
     | .error e => some e
     | .ok _ => none) =
      some (.ub "Value::Ptr: non-dereferenceable safe pointer") ∧
    (match Interp.stepsTB 5 (liftMachToTB nonZstWrappingSubReborrowMach) with
     | .error e => some e
     | .ok _ => none) =
      some (.ub "Value::Ptr: non-dereferenceable safe pointer") :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ## 7. End-to-end `MachTB.wfLive` preservation, self-deref vs. parent-deref copy, loop correspondence, and `std::cmp::Ordering` / `()` pointees (MR-3.2 A4) -/

/-- Every allocation produced by `liftAllocTB` has a well-formed unprotected
`.Unique` root node whose `permissions` list matches `(Allocation.size _).bytes`. -/
theorem liftAllocTB_wf (a : Gen.Allocation) :
    Node.wf (Allocation.size (liftAllocTB a)).bytes (liftAllocTB a).extra.root := by
  refine ⟨by simp [liftAllocTB, Allocation.size], fun p hp => ?_, trivial⟩
  rw [List.eq_of_mem_replicate hp]
  rfl

/-- `liftMachToTB` always produces a globally well-formed `TreeBorrowsMemory`
(`TreeBorrowsMemory.wf`). -/
theorem liftMachToTB_wf (m : Mach) :
    TreeBorrowsMemory.wf (liftMachToTB m).mem.memory := by
  intro alloc hm
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hm
  exact liftAllocTB_wf a

/-- `liftMachToTB` always satisfies the machine-level live-allocation borrow-tree
invariant `MachTB.wfLive`. -/
theorem liftMachToTB_wfLive (m : Mach) :
    MachTB.wfLive (liftMachToTB m) :=
  fun alloc hm _ => liftMachToTB_wf m alloc hm

/-- Any `n`-step `MachTB` execution (`Interp.stepsTB`) starting from `liftMachToTB m`
preserves `MachTB.wfLive` across all statement, intrinsic, retag, deallocation,
and call-return protector-release transitions. -/
theorem liftMachToTB_stepsTB_wfLive {n : Nat} {m : Mach} {m' : MachTB}
    (h : Interp.stepsTB n (liftMachToTB m) = .ok m') :
    MachTB.wfLive m' :=
  stepsTB_wfLive (liftMachToTB_wfLive m) h

/-- Any `n`-step `MachTB` execution starting from `startMachineTB body args`
preserves `MachTB.wfLive`. -/
theorem startMachineTB_stepsTB_wfLive {body : CapturedMir} {args : List Value}
    {m0 m' : MachTB} {n : Nat}
    (hstart : startMachineTB body args = some m0)
    (hsteps : Interp.stepsTB n m0 = .ok m') :
    MachTB.wfLive m' := by
  unfold startMachineTB at hstart
  rcases hsm : startMachine body args with _ | m
  · simp [hsm] at hstart
  · simp [hsm] at hstart
    subst hstart
    exact liftMachToTB_stepsTB_wfLive hsteps

/-- UB message after `n` `MachTB` steps under `ctx0_2`, if step `n` raises UB. -/
def ubAfterTB2 (body : CapturedMir) (args : List Value) (n : Nat) : Option String :=
  (startMachineTB2 body args).bind fun m =>
    match Interp.stepsTB n m with
    | .error (.ub msg) => some msg
    | _ => none

/-- Self-aliasing pointer-to-pointer dereference copy `(*r) = copy (*r)` on
`r: &mut u32` (`_2 = &mut _1; (*_2) = copy (*_2); _3 = &(*_2); _0 = copy (*_3)`):
lies in `inFragment` (`stepDerefWrite` preserves `_2` in its own peer set `[2]`),
performs only local `Read`/`Write` accesses on node `[0]` in `MachTB` (keeping
`Unprot .Unique` active), and returns `42` across Anneal, `Mach`, and `MachTB`. -/
def selfDerefCopyOk : CapturedMir :=
  ptrBody "witness::self_deref_copy_ok"
    [u32Decl, u32Decl, refMutU32Decl, refSharedU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (derefPlace 2) (.use (.copy (derefPlace 2))),
     .assign (local_ 3) (.ref .shared (derefPlace 2)),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem selfDerefCopyOk_inFragment : inFragment selfDerefCopyOk = true := by decide

def selfDerefCopyOkFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, refTy .not u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Deref (.Load (.Local (localName 2))) (.Int u32))
        (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem selfDerefCopyOk_translate : translateFn selfDerefCopyOk = some selfDerefCopyOkFn := rfl

def selfDerefCopyOkS0 : MachineState := initMachineState selfDerefCopyOk [.scalar ⟨42, 4⟩]
def selfDerefCopyOkMInit : Mach :=
  machine selfDerefCopyOk selfDerefCopyOkFn selfDerefCopyOkS0.frame.locals selfDerefCopyOkFn.start

theorem selfDerefCopyOk_anneal_ret :
    ∃ mem, ReachesRet (mirTree selfDerefCopyOk selfDerefCopyOkS0) []
      (.normal (.scalar ⟨42, 4⟩, mem)) :=
  ⟨_, runA_sound selfDerefCopyOk 25 _ _ _ rfl⟩

theorem selfDerefCopyOk_noUB :
    MirNoUBTree (mirCallTree selfDerefCopyOk [.scalar ⟨42, 4⟩]) :=
  runA_noUB selfDerefCopyOk 25 _ _ _ rfl

theorem selfDerefCopyOk_ctxOk : CtxOk selfDerefCopyOk ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : selfDerefCopyOk.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [selfDerefCopyOk, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [selfDerefCopyOk, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : selfDerefCopyOk.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [selfDerefCopyOk, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem selfDerefCopyOk_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n selfDerefCopyOkMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨mem, hretA⟩ := selfDerefCopyOk_anneal_ret
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret selfDerefCopyOk_inFragment selfDerefCopyOk_translate ctx0 selfDerefCopyOk_ctxOk
      [.scalar ⟨42, 4⟩] (by decide) selfDerefCopyOkMInit rfl rfl rfl hretA
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [selfDerefCopyOk, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem selfDerefCopyOk_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n selfDerefCopyOkMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k selfDerefCopyOkMInit = .ok mRet ∧
      ReturnRel selfDerefCopyOk ctx0 s' v mRet ∧
      ReachesRet (mirCallTree selfDerefCopyOk [.scalar ⟨42, 4⟩]) tr (.normal (v, mem)) :=
  mirCall_noUB selfDerefCopyOk_inFragment selfDerefCopyOk_translate ctx0 selfDerefCopyOk_ctxOk
    [.scalar ⟨42, 4⟩] (by decide) selfDerefCopyOkMInit rfl rfl rfl selfDerefCopyOk_noUB herr

theorem selfDerefCopyOk_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) selfDerefCopyOkMInit = .ok m' ∧
      StateRelN selfDerefCopyOk selfDerefCopyOkFn ctx0 s' m' ∧
      Reaches (mirCallTree selfDerefCopyOk [.scalar ⟨42, 4⟩]) tr
        (mirTree selfDerefCopyOk s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k selfDerefCopyOkMInit = .ok mRet ∧
      ReturnRel selfDerefCopyOk ctx0 s' v mRet ∧
      ReachesRet (mirCallTree selfDerefCopyOk [.scalar ⟨42, 4⟩]) tr (.normal (v, mem))) :=
  mirCall_progress_N selfDerefCopyOk_inFragment selfDerefCopyOk_translate ctx0
    selfDerefCopyOk_ctxOk [.scalar ⟨42, 4⟩] (by decide) selfDerefCopyOkMInit rfl rfl rfl
    selfDerefCopyOk_noUB n

theorem selfDerefCopyOk_minirust_direct :
    retAfter selfDerefCopyOk [.scalar ⟨42, 4⟩] 8 =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) := by
  decide +kernel

theorem selfDerefCopyOk_tb_direct :
    retAfterTB selfDerefCopyOk [.scalar ⟨42, 4⟩] 8 = tbRetU32 42 := by
  decide +kernel

/-- Contrast with a pointer-to-pointer dereference copy through a parent `&mut u32`
(`_3 = &mut _1; _4 = &mut _2; _5 = &mut (*_3); (*_3) = copy (*_4); _0 = copy (*_5)`):
`ptrAliasingOk` marks child `_5` `.disabled` upon `(*_3) = copy (*_4)` (so
`inFragment = false`), Anneal and `MachTB` both raise UB when reading `*_5`
(`"Tree Borrows: local read of Disabled reference"`), and flat `BasicMemory`
(`Mach`) returns `99`. -/
def parentDerefCopyDisablesChild : CapturedMir where
  defPath := "witness::parent_deref_copy_disables_child"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, refMutU32Decl, refMutU32Decl, refMutU32Decl]
  basicBlocks := [{
    statements := ([
      .storageLive 3, .storageLive 4, .storageLive 5,
      .assign (local_ 3) (.ref (.mut false) (local_ 1)),
      .assign (local_ 4) (.ref (.mut false) (local_ 2)),
      .assign (local_ 5) (.ref (.mut false) (derefPlace 3)),
      .assign (derefPlace 3) (.use (.copy (derefPlace 4))),
      .assign (local_ 0) (.use (.copy (derefPlace 5)))
    ] : List StatementKind).map mkStmt
    terminator := mkTerm .return_
    isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem parentDerefCopyDisablesChild_notInFragment :
    inFragment parentDerefCopyDisablesChild = false := by decide

theorem parentDerefCopyDisablesChild_translate :
    (translateFn parentDerefCopyDisablesChild).isSome = true := by decide +kernel

theorem parentDerefCopyDisablesChild_anneal_ub :
    ∃ tr u, Reaches (mirCallTree parentDerefCopyDisablesChild
      [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩]) tr u ∧ FaultNow u :=
  faultsA_sound parentDerefCopyDisablesChild 25 _ (by decide)

theorem parentDerefCopyDisablesChild_minirust_direct :
    retAfter2 parentDerefCopyDisablesChild [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) := by
  decide +kernel

theorem parentDerefCopyDisablesChild_tb_direct :
    ubAfterTB2 parentDerefCopyDisablesChild [.scalar ⟨10, 4⟩, .scalar ⟨99, 4⟩] 9 =
      some "Tree Borrows: local read of Disabled reference" := by
  decide +kernel

/-- Four-block cyclic CFG loop in `inFragment` (`bb0 -> bb1 <-> bb2, bb1 -> bb3`)
combining disjoint `&mut u32` borrows (`_3 = &mut _1`, `_4 = &mut _2`),
reborrowed `&u32` loop-header reads (`_5 = &(*_3)` — invalidated to `.disabled`
at the end of `bb2` by `(*_3) = move _7` and re-initialized cleanly at the top
of `bb1`), `CopyForDeref(*_4)`, `move`-operand dereference writes, and an exit
pointer-to-pointer dereference copy `(*_3) = copy (*_5)` followed by
`_0 = move (*_3)`. On `(3, 10)`, computes `10 + 3 + 2 + 1 = 16`. -/
def loopDerefCopyCountdown : CapturedMir where
  defPath := "witness::loop_deref_copy_countdown"
  phase := .runtimePostCleanup
  role := .subject
  argCount := 2
  localDecls := [u32Decl, u32Decl, u32Decl, refMutU32Decl, refMutU32Decl,
    refSharedU32Decl, u32Decl, u32Decl]
  basicBlocks := [
    { statements := ([
        .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6, .storageLive 7,
        .assign (local_ 3) (.ref (.mut false) (local_ 1)),
        .assign (local_ 4) (.ref (.mut false) (local_ 2))
      ] : List StatementKind).map mkStmt
      terminator := mkTerm (.goto 1)
      isCleanup := false },
    { statements := ([
        .assign (local_ 5) (.ref .shared (derefPlace 3)),
        .assign (local_ 6) (.use (.copy (derefPlace 5)))
      ] : List StatementKind).map mkStmt
      terminator := mkTerm (.switchInt (.copy (local_ 6)) { branches := [(0, 3)], otherwise := 2 })
      isCleanup := false },
    { statements := ([
        .assign (local_ 7) (.copyForDeref (derefPlace 4)),
        .assign (local_ 7) (.binaryOp .add (.move (local_ 7)) (.copy (local_ 6))),
        .assign (derefPlace 4) (.use (.move (local_ 7))),
        .assign (local_ 7) (.binaryOp .sub (.copy (local_ 6)) (constU32 1)),
        .assign (derefPlace 3) (.use (.move (local_ 7)))
      ] : List StatementKind).map mkStmt
      terminator := mkTerm (.goto 1)
      isCleanup := false },
    { statements := ([
        .assign (local_ 5) (.ref .shared (derefPlace 4)),
        .assign (derefPlace 3) (.use (.copy (derefPlace 5))),
        .assign (local_ 0) (.use (.move (derefPlace 3)))
      ] : List StatementKind).map mkStmt
      terminator := mkTerm .return_
      isCleanup := false }]
  fnAbi := fnAbi 2
  layouts := emptyLayoutTable
  allocations := []

theorem loopDerefCopyCountdown_inFragment :
    inFragment loopDerefCopyCountdown = true := by decide

def loopDerefCopyCountdownFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32), (localName 2, .Int u32),
    (localName 3, refTy .mut u32), (localName 4, refTy .mut u32),
    (localName 5, refTy .not u32), (localName 6, .Int u32), (localName 7, .Int u32)]⟩
  args := [localName 1, localName 2]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 3), .StorageLive (localName 4), .StorageLive (localName 5),
      .StorageLive (localName 6), .StorageLive (localName 7),
      .Assign (.Local (localName 3)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 4)) (.AddrOf (.Local (localName 2)) (refPtrType .mut u32))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 1, ⟨[
      .Assign (.Local (localName 5))
        (.AddrOf (.Deref (.Load (.Local (localName 3))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Local (localName 6)) (.Load (.Deref (.Load (.Local (localName 5))) (.Int u32)))],
      .Switch (.Load (.Local (localName 6))) ⟨[(0, bbName 3)]⟩ (bbName 2), .Regular⟩),
    (bbName 2, ⟨[
      .Assign (.Local (localName 7)) (.Load (.Deref (.Load (.Local (localName 4))) (.Int u32))),
      .Assign (.Local (localName 7))
        (.BinOp (.Int .Add) (.Load (.Local (localName 7))) (.Load (.Local (localName 6)))),
      .Assign (.Deref (.Load (.Local (localName 4))) (.Int u32)) (.Load (.Local (localName 7))),
      .Assign (.Local (localName 7))
        (.BinOp (.Int .Sub) (.Load (.Local (localName 6))) (.Constant (.Int 1) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32)) (.Load (.Local (localName 7)))],
      .Goto (bbName 1), .Regular⟩),
    (bbName 3, ⟨[
      .Assign (.Local (localName 5))
        (.AddrOf (.Deref (.Load (.Local (localName 4))) (.Int u32)) (refPtrType .not u32)),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32))
        (.Load (.Deref (.Load (.Local (localName 5))) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 4, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 4
  implicit_writes := true

theorem loopDerefCopyCountdown_translate :
    translateFn loopDerefCopyCountdown = some loopDerefCopyCountdownFn := rfl

def loopDerefCopyCountdownArgs : List Value := [.scalar ⟨3, 4⟩, .scalar ⟨10, 4⟩]
def loopDerefCopyCountdownS0 : MachineState :=
  initMachineState loopDerefCopyCountdown loopDerefCopyCountdownArgs
def loopDerefCopyCountdownMInit : Mach :=
  machine2 loopDerefCopyCountdown loopDerefCopyCountdownFn
    loopDerefCopyCountdownS0.frame.locals loopDerefCopyCountdownFn.start

def loopDerefCopyCountdownTrace : List (Event MirEffect) :=
  [3, 2, 1, 0].map (fun b => ⟨.inr (.inl (.emit (.event b))), PUnit.unit⟩)

theorem loopDerefCopyCountdown_anneal_ret :
    ∃ mem, ReachesRet (mirTree loopDerefCopyCountdown loopDerefCopyCountdownS0)
      loopDerefCopyCountdownTrace (.normal (.scalar ⟨16, 4⟩, mem)) :=
  ⟨_, runA_sound loopDerefCopyCountdown 80 _ _ _ rfl⟩

theorem loopDerefCopyCountdown_noUB :
    MirNoUBTree (mirCallTree loopDerefCopyCountdown loopDerefCopyCountdownArgs) :=
  runA_noUB loopDerefCopyCountdown 80 _ _ _ rfl

theorem loopDerefCopyCountdown_ctxOk : CtxOk loopDerefCopyCountdown ctx0_2 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi2 : i ≤ 2 := hi
    have hlay : loopDerefCopyCountdown.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi2 with
    | 0, hd, _ => simp [loopDerefCopyCountdown] at hd; subst hd; decide
    | 1, hd, _ => simp [loopDerefCopyCountdown] at hd; subst hd; decide
    | 2, hd, _ => simp [loopDerefCopyCountdown] at hd; subst hd; decide
    | _ + 3, _, h => omega
  ret := by
    intro d hd
    have hlay : loopDerefCopyCountdown.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [loopDerefCopyCountdown] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem loopDerefCopyCountdown_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n loopDerefCopyCountdownMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 16 } ∧
      m'.threads = [thread1 ctx0_2 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨mem, hretA⟩ := loopDerefCopyCountdown_anneal_ret
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret loopDerefCopyCountdown_inFragment loopDerefCopyCountdown_translate ctx0_2
      loopDerefCopyCountdown_ctxOk loopDerefCopyCountdownArgs (by decide)
      loopDerefCopyCountdownMInit rfl rfl rfl hretA
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [loopDerefCopyCountdown] at hd; subst hd
  simp [retPtr, ctx0_2, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0_2, ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem loopDerefCopyCountdown_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n loopDerefCopyCountdownMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k loopDerefCopyCountdownMInit = .ok mRet ∧
      ReturnRel loopDerefCopyCountdown ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree loopDerefCopyCountdown loopDerefCopyCountdownArgs) tr
        (.normal (v, mem)) :=
  mirCall_noUB loopDerefCopyCountdown_inFragment loopDerefCopyCountdown_translate ctx0_2
    loopDerefCopyCountdown_ctxOk loopDerefCopyCountdownArgs (by decide)
    loopDerefCopyCountdownMInit rfl rfl rfl loopDerefCopyCountdown_noUB herr

theorem loopDerefCopyCountdown_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) loopDerefCopyCountdownMInit = .ok m' ∧
      StateRelN loopDerefCopyCountdown loopDerefCopyCountdownFn ctx0_2 s' m' ∧
      Reaches (mirCallTree loopDerefCopyCountdown loopDerefCopyCountdownArgs) tr
        (mirTree loopDerefCopyCountdown s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k loopDerefCopyCountdownMInit = .ok mRet ∧
      ReturnRel loopDerefCopyCountdown ctx0_2 s' v mRet ∧
      ReachesRet (mirCallTree loopDerefCopyCountdown loopDerefCopyCountdownArgs) tr
        (.normal (v, mem))) :=
  mirCall_progress_N loopDerefCopyCountdown_inFragment loopDerefCopyCountdown_translate ctx0_2
    loopDerefCopyCountdown_ctxOk loopDerefCopyCountdownArgs (by decide)
    loopDerefCopyCountdownMInit rfl rfl rfl loopDerefCopyCountdown_noUB n

theorem loopDerefCopyCountdown_minirust_direct :
    retAfter2 loopDerefCopyCountdown loopDerefCopyCountdownArgs 43 =
      some (some { retAlloc with data := scalarBytes u32 16 }, [1]) := by
  decide +kernel

theorem loopDerefCopyCountdown_tb_direct :
    retAfterTB2 loopDerefCopyCountdown loopDerefCopyCountdownArgs 43 = tbRetU32 16 := by
  decide +kernel

def stdOrderingTy : Ty := { kind := .adt "std::cmp::Ordering" [], layoutIdx := 1 }
def refMutStdOrderingTy : Ty := { kind := .ref .mut (.adt "std::cmp::Ordering" []), layoutIdx := 0 }
def refSharedStdOrderingTy : Ty := { kind := .ref .not (.adt "std::cmp::Ordering" []), layoutIdx := 0 }
def stdOrderingDecl : LocalDecl := { mutability := .mut, ty := stdOrderingTy, debugName := none }
def refMutStdOrderingDecl : LocalDecl :=
  { mutability := .mut, ty := refMutStdOrderingTy, debugName := none }
def refSharedStdOrderingDecl : LocalDecl :=
  { mutability := .mut, ty := refSharedStdOrderingTy, debugName := none }

def stdOrderingLayout : TypeLayout :=
  let tagSc : ScalarLayout := .initialized (.int 8 true) { start := 255, end_ := 1 }
  { size := { bytes := 1 }, align := { bytes := 1 },
    backendRepr := .scalar tagSc,
    fields := .arbitrary [] [],
    variants := .multiple tagSc 0 [.arbitrary [] [], .arbitrary [] [], .arbitrary [] []],
    isUninhabited := false }

def stdOrderingLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [i8Layout, stdOrderingLayout] }

/-- `&mut std::cmp::Ordering` and `&std::cmp::Ordering` (using the `"std::cmp::Ordering"`
`defPath` alias alongside `"core::cmp::Ordering"` in `pointeeInfoOfRigidTy` and
`translatePointeeRigidTy`): writes `10.cmp(&x)` through `r: &mut std::cmp::Ordering`,
reborrows `s: &std::cmp::Ordering = &*r`, reads `*s`, transmutes to `u8`, and casts
to `u32` (`5 -> Greater = 1`, `20 -> Less = 255`) across Anneal, `Mach`, and `MachTB`. -/
def stdOrderingMutRefCmp : CapturedMir :=
  { ptrBody "witness::std_ordering_mut_ref_cmp"
      [u32Decl, u32Decl, stdOrderingDecl, refMutStdOrderingDecl,
       stdOrderingDecl, refSharedStdOrderingDecl, u8Decl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
       .assign (local_ 2) (.binaryOp .cmp (.copy (local_ 1)) (constU32 10)),
       .assign (local_ 3) (.ref (.mut false) (local_ 2)),
       .assign (local_ 4) (.binaryOp .cmp (constU32 10) (.copy (local_ 1))),
       .assign (derefPlace 3) (.use (.move (local_ 4))),
       .assign (local_ 5) (.ref .shared (derefPlace 3)),
       .assign (local_ 4) (.use (.copy (derefPlace 5))),
       .assign (local_ 6) (.cast .transmute (.move (local_ 4)) u8Decl.ty),
       .assign (local_ 0) (.cast .intToInt (.move (local_ 6)) u32Ty)] with
    layouts := stdOrderingLayouts }

theorem stdOrderingMutRefCmp_translate :
    (translateFn stdOrderingMutRefCmp).isSome = true := by decide +kernel

set_option maxRecDepth 16384 in
theorem stdOrderingMutRefCmp_five_three_way :
    (∃ mem, ReachesRet (mirTree stdOrderingMutRefCmp
      (initMachineState stdOrderingMutRefCmp [.scalar ⟨5, 4⟩])) []
      (.normal (.scalar ⟨1, 4⟩, mem))) ∧
    retAfter stdOrderingMutRefCmp [.scalar ⟨5, 4⟩] 15 =
      some (some { retAlloc with data := scalarBytes u32 1 }, [1]) ∧
    retAfterTB stdOrderingMutRefCmp [.scalar ⟨5, 4⟩] 15 = tbRetU32 1 :=
  ⟨⟨_, runA_sound stdOrderingMutRefCmp 30 _ _ _ rfl⟩, by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 16384 in
theorem stdOrderingMutRefCmp_twenty_three_way :
    (∃ mem, ReachesRet (mirTree stdOrderingMutRefCmp
      (initMachineState stdOrderingMutRefCmp [.scalar ⟨20, 4⟩])) []
      (.normal (.scalar ⟨255, 4⟩, mem))) ∧
    retAfter stdOrderingMutRefCmp [.scalar ⟨20, 4⟩] 15 =
      some (some { retAlloc with data := scalarBytes u32 255 }, [1]) ∧
    retAfterTB stdOrderingMutRefCmp [.scalar ⟨20, 4⟩] 15 = tbRetU32 255 :=
  ⟨⟨_, runA_sound stdOrderingMutRefCmp 30 _ _ _ rfl⟩, by decide +kernel, by decide +kernel⟩

def unitTupleLayout : TypeLayout :=
  { size := { bytes := 0 }, align := { bytes := 1 }, backendRepr := .memory,
    fields := .arbitrary [] [],
    variants := .single 0, isUninhabited := false, fieldLayouts := [] }

def unitTupleLayouts : LayoutTable :=
  { pointerBits := 64, isLittleEndian := true, entries := [unitTupleLayout] }

def unitTupleTy : Ty := { kind := .tuple [], layoutIdx := 0 }
def refMutUnitTupleTy : Ty := { kind := .ref .mut (.tuple []), layoutIdx := 0 }
def refSharedUnitTupleTy : Ty := { kind := .ref .not (.tuple []), layoutIdx := 0 }
def unitTupleDecl : LocalDecl := { mutability := .mut, ty := unitTupleTy, debugName := none }
def refMutUnitTupleDecl : LocalDecl :=
  { mutability := .mut, ty := refMutUnitTupleTy, debugName := none }
def refSharedUnitTupleDecl : LocalDecl :=
  { mutability := .mut, ty := refSharedUnitTupleTy, debugName := none }

/-- Zero-sized `&mut ()` and `&()` borrow, dereference read, dereference write,
and shared reborrow (`_2 = (); _3 = &mut _2; _4 = copy (*_3); (*_3) = move _4;
_5 = &(*_3); _6 = copy (*_5); _0 = copy _1`) at valid offset `0` of stack local
`_2`: translates cleanly via `pointeeInfoOfRigidTy (.tuple [])` and
`translatePointeeRigidTy (.tuple [])` and returns `42` in Anneal, `Mach`, and
`MachTB` without triggering the negative-offset ZST `specPanic` of Section 6. -/
def unitTupleMutRefRoundTrip : CapturedMir :=
  { ptrBody "witness::unit_tuple_mut_ref_round_trip"
      [u32Decl, u32Decl, unitTupleDecl, refMutUnitTupleDecl,
       unitTupleDecl, refSharedUnitTupleDecl, unitTupleDecl]
      [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5, .storageLive 6,
       .assign (local_ 2) (.aggregate .tuple []),
       .assign (local_ 3) (.ref (.mut false) (local_ 2)),
       .assign (local_ 4) (.use (.copy (derefPlace 3))),
       .assign (derefPlace 3) (.use (.move (local_ 4))),
       .assign (local_ 5) (.ref .shared (derefPlace 3)),
       .assign (local_ 6) (.use (.copy (derefPlace 5))),
       .assign (local_ 0) (.use (.copy (local_ 1)))] with
    layouts := unitTupleLayouts }

theorem unitTupleMutRefRoundTrip_translate :
    (translateFn unitTupleMutRefRoundTrip).isSome = true := by decide +kernel

theorem unitTupleMutRefRoundTrip_three_way :
    (∃ mem, ReachesRet (mirTree unitTupleMutRefRoundTrip
      (initMachineState unitTupleMutRefRoundTrip [.scalar ⟨42, 4⟩])) []
      (.normal (.scalar ⟨42, 4⟩, mem))) ∧
    retAfter unitTupleMutRefRoundTrip [.scalar ⟨42, 4⟩] 14 =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    retAfterTB unitTupleMutRefRoundTrip [.scalar ⟨42, 4⟩] 14 = tbRetU32 42 :=
  ⟨⟨_, runA_sound unitTupleMutRefRoundTrip 30 _ _ _ rfl⟩, by decide +kernel, by decide +kernel⟩

/-! ## 8. MR-3.3 Provenance & `IntPtrCast` (`PointerExposeProvenance` / `PointerWithExposedProvenance`) 3-Way Witnesses -/

/-- Stop reason (`Stop`) after `n` `Mach` steps under `translateFnWithIntrinsics`. -/
def stopAfterIntr (body : CapturedMir) (args : List Value) (n : Nat) : Option Stop :=
  (startMachineIntr body args).bind fun m =>
    match Interp.steps n m with
    | .error e => some e
    | .ok _ => none

/-- `translateFnWithIntrinsics` lowers `exposeTwice` by splitting blocks at both
`PointerExposeProvenance` casts. -/
theorem exposeTwice_translateIntr :
    (translateFnWithIntrinsics exposeTwice).isSome = true := by decide +kernel

theorem exposeSingleRefMutRoundTrip_inFragmentWithIntrinsics :
    inFragmentWithIntrinsics exposeSingleRefMutRoundTrip = true := by decide +kernel

/-- Reconstructing `*mut u32` from the exposed address of a `*const u32` launders
mutability through the integer, which `provCastFlowOk` rejects
(`exposeSourceCompatible`, mirroring `ptrRvalueOk`'s `PtrToPtr` rule). -/
theorem exposeSharedRefWriteUb_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics exposeSharedRefWriteUb = false := by decide +kernel

theorem exposeTwoRefMutAngelicUnsupported_inFragmentWithIntrinsics :
    inFragmentWithIntrinsics exposeTwoRefMutAngelicUnsupported = true := by decide +kernel

/-- Raw-pointer `PointerExposeProvenance` → `usize` → `PointerWithExposedProvenance`
round-trip (`_2 = &raw mut _1; _3 = expose(_2); _4 = with_exposed(_3); (*_4) = 77; _0 = (*_4)`):
lies in `inFragmentWithIntrinsics`, translates via `translateFnWithIntrinsics`, and
returns `77` across Anneal, `Mach`, and `MachTB`. -/
def int2ptrRawRoundTripOk : CapturedMir :=
  ptrBody "witness::int2ptr_raw_round_trip_ok"
    [u32Decl, u32Decl, ptrMutU32Decl, usizeDecl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.rawPtr .mut (local_ 1)),
     .assign (local_ 3) (.cast .pointerExposeProvenance (.copy (local_ 2)) usizeTy),
     .assign (local_ 4) (.cast .pointerWithExposedProvenance (.copy (local_ 3)) ptrMutU32Ty),
     .assign (derefPlace 4) (.use (constU32 77)),
     .assign (local_ 0) (.use (.copy (derefPlace 4)))]

theorem int2ptrRawRoundTripOk_inFragmentWithIntrinsics :
    inFragmentWithIntrinsics int2ptrRawRoundTripOk = true := by decide +kernel

theorem int2ptrRawRoundTripOk_translateIntr :
    (translateFnWithIntrinsics int2ptrRawRoundTripOk).isSome = true := by decide +kernel

theorem int2ptrRawRoundTripOk_minirust_direct :
    retAfterIntr int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 77 }, [1]) := by
  decide +kernel

theorem int2ptrRawRoundTripOk_tb_direct :
    retAfterIntrTB int2ptrRawRoundTripOk [.scalar ⟨5, 4⟩] 10 = tbRetU32 77 := by
  decide +kernel

/-- Constructing a `*const u32` via `PointerWithExposedProvenance` from an integer
address (`256`, the stack address of `_1` under `ctx0`) when `exposed = ∅`:
`IntPtrCast.int2ptr` yields `{ addr := 256, provenance := none }`, and dereferencing
`*_3` raises `Stop.ub "dereferencing pointer without provenance"` on both `Mach`
and `MachTB` (and faults in Anneal because `exposedAllocIds = []` so
`recoverExposedPtrValue?` leaves a provenance-less scalar `256`). -/
def int2ptrUnexposedDerefUb : CapturedMir :=
  ptrBody "witness::int2ptr_unexposed_deref_ub"
    [u32Decl, u32Decl, usizeDecl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.use (constUsize 256)),
     .assign (local_ 3) (.cast .pointerWithExposedProvenance (.copy (local_ 2)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

/-- The forged address `256` is not an exposed-address local, so `provCastFlowOk`
rejects the body (forged integers stay outside the fragment even though Anneal
now recovers no provenance from an unexposed address, see `int2ptrForgedTag`). -/
theorem int2ptrUnexposedDerefUb_notInFragmentWithIntrinsics :
    inFragmentWithIntrinsics int2ptrUnexposedDerefUb = false := by decide +kernel

theorem int2ptrUnexposedDerefUb_translateIntr :
    (translateFnWithIntrinsics int2ptrUnexposedDerefUb).isSome = true := by decide +kernel

theorem int2ptrUnexposedDerefUb_minirust_direct :
    stopAfterIntr int2ptrUnexposedDerefUb [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") := by
  decide +kernel

theorem int2ptrUnexposedDerefUb_tb_direct :
    stopAfterIntrTB int2ptrUnexposedDerefUb [.scalar ⟨5, 4⟩] 6 =
      some (.ub "dereferencing pointer without provenance") := by
  decide +kernel

/-- Exposing pointers to two distinct live stack allocations (`_1` and `_2`) so
`m.intptrcast.exposed` has two elements (`p1 :: p2 :: []`), then calling
`PointerWithExposedProvenance` on an out-of-bounds integer address (`1024`) where
`candidates = []`: both `Mach` and `MachTB` stop with
`Stop.unsupported "int2ptr: no exposed allocation is in-bounds of the address (angelic choice)"`,
and when two live exposed `BasicMemory` allocations `[128..132]` and `[132..136]`
meet at boundary address `132`, `IntPtrCast.int2ptr` stops with
`Stop.unsupported "int2ptr: several exposed allocations meet at the address (angelic choice)"`. -/
def int2ptrMultiAllocBoundaryUnsupported : CapturedMir :=
  ptrBody "witness::int2ptr_multi_alloc_boundary_unsupported"
    [u32Decl, u32Decl, u32Decl, ptrConstU32Decl, ptrConstU32Decl,
     usizeDecl, usizeDecl, usizeDecl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .storageLive 6, .storageLive 7, .storageLive 8,
     .assign (local_ 2) (.use (constU32 9)),
     .assign (local_ 3) (.rawPtr .not (local_ 1)),
     .assign (local_ 4) (.rawPtr .not (local_ 2)),
     .assign (local_ 5) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 6) (.cast .pointerExposeProvenance (.copy (local_ 4)) usizeTy),
     .assign (local_ 7) (.use (constUsize 1024)),
     .assign (local_ 8) (.cast .pointerWithExposedProvenance (.copy (local_ 7)) ptrConstU32Ty),
     .assign (local_ 0) (.use (.copy (derefPlace 8)))]

theorem int2ptrMultiAllocBoundaryUnsupported_translateIntr :
    (translateFnWithIntrinsics int2ptrMultiAllocBoundaryUnsupported).isSome = true := by decide +kernel

theorem int2ptrMultiAllocOutOfBounds_bm :
    let a0 : Gen.Allocation :=
      { data := scalarBytes u32 1, addr := 128, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let a1 : Gen.Allocation :=
      { data := scalarBytes u32 2, addr := 256, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    int2ptrCandidates [a0, a1] ⟨[(⟨0⟩, ()), (⟨1⟩, ())]⟩ 1024 = [] :=
  rfl

theorem int2ptrAdjacentBoundaryMeeting_bm :
    let a0 : Gen.Allocation :=
      { data := scalarBytes u32 1, addr := 128, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    let a1 : Gen.Allocation :=
      { data := scalarBytes u32 2, addr := 132, align := ⟨4⟩, kind := .Stack, live := true, extra := () }
    int2ptrCandidates [a0, a1] ⟨[(⟨0⟩, ()), (⟨1⟩, ())]⟩ 132 = [(⟨0⟩, ()), (⟨1⟩, ())] :=
  rfl

/-- Exposing a pointer to temporary local `_2`, reconstructing `*const u32` via
`PointerWithExposedProvenance` while `_2` is still live, then executing
`StorageDead(_2)` to deallocate `_2` (`a.live = false`) before dereferencing `*_5`:
all three semantics (`Anneal`, `Mach`, and `MachTB`) raise UB
(`"dereferencing pointer to dead allocation"` on `Mach` and `MachTB`). -/
def int2ptrDeadAllocDerefUb : CapturedMir :=
  ptrBody "witness::int2ptr_dead_alloc_deref_ub"
    [u32Decl, u32Decl, u32Decl, ptrConstU32Decl, usizeDecl, ptrConstU32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4, .storageLive 5,
     .assign (local_ 2) (.use (constU32 42)),
     .assign (local_ 3) (.rawPtr .not (local_ 2)),
     .assign (local_ 4) (.cast .pointerExposeProvenance (.copy (local_ 3)) usizeTy),
     .assign (local_ 5) (.cast .pointerWithExposedProvenance (.copy (local_ 4)) ptrConstU32Ty),
     .storageDead 2,
     .assign (local_ 0) (.use (.copy (derefPlace 5)))]

theorem int2ptrDeadAllocDerefUb_translateIntr :
    (translateFnWithIntrinsics int2ptrDeadAllocDerefUb).isSome = true := by decide +kernel

theorem int2ptrDeadAllocDerefUb_minirust_direct :
    stopAfterIntr int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩] 11 =
      some (.ub "dereferencing pointer to dead allocation") := by
  decide +kernel

theorem int2ptrDeadAllocDerefUb_tb_direct :
    stopAfterIntrTB int2ptrDeadAllocDerefUb [.scalar ⟨5, 4⟩] 11 =
      some (.ub "dereferencing pointer to dead allocation") := by
  decide +kernel

/-! ## 9. Unstable (`b076d6a3`) Rebase-Delta Parity & Soundness Witnesses -/

/-- `validateLoadedValue` invalid-`bool` dereference-load UB parity (without any
subsequent `!` or `IntToInt` use of the loaded `bool` local `_4`):
`_2 = &raw const _1; _3 = transmute(_2) -> &bool; _4 = copy (*_3); _0 = 0u32`.
On input `2u8`, Anneal's `validateLoadedValue` rejects `2 ∉ {0, 1}` at the
dereference load `_4 = copy (*_3)` itself, matching `Mach` and `MachTB`. -/
def boolInvalidLoadDirectUb : CapturedMir :=
  { ptrBody "witness::bool_invalid_load_direct_ub"
      [u32Decl, u8Decl, ptrConstU8Decl, refSharedBoolDecl, boolDecl]
      [.storageLive 2, .storageLive 3, .storageLive 4,
       .assign (local_ 2) (.rawPtr .not (local_ 1)),
       .assign (local_ 3) (.cast .transmute (.copy (local_ 2)) refSharedBoolTy),
       .assign (local_ 4) (.use (.copy (derefPlace 3))),
       .assign (local_ 0) (.use (constU32 0))] with
    fnAbi := fnAbiBoolArg }

theorem boolInvalidLoadDirectUb_translate :
    (translateFn boolInvalidLoadDirectUb).isSome = true := by decide +kernel

/-- The `transmute`d `&bool` load is outside `inFragment`, so the parity below is
established by direct evaluation of all three semantics. -/
theorem boolInvalidLoadDirectUb_notInFragment :
    inFragment boolInvalidLoadDirectUb = false := by decide +kernel

theorem boolInvalidLoadDirectUb_three_way_ub :
    (∃ tr u, Reaches (mirTree boolInvalidLoadDirectUb
      (initMachineState boolInvalidLoadDirectUb [.scalar ⟨2, 1⟩])) tr u ∧ FaultNow u) ∧
    ubAfter boolInvalidLoadDirectUb [.scalar ⟨2, 1⟩] 7 =
      some "load at type but the data in memory violates the language invariant" ∧
    ubAfterTB boolInvalidLoadDirectUb [.scalar ⟨2, 1⟩] 7 =
      some "load at type but the data in memory violates the language invariant" :=
  ⟨faultsA_sound boolInvalidLoadDirectUb 20 _ (by decide),
   by decide +kernel, by decide +kernel⟩

/-- Control for `boolInvalidLoadDirectUb_three_way_ub`: on the valid `bool` byte
`1u8` (`true`) the same program is UB-free in Anneal and returns `0` in Anneal,
`Mach`, and `MachTB`, so the three-way UB on `2u8` stems from the loaded value's
validity (Anneal's `validateLoadedValue`, MiniRust's typed-load invariant check),
not from the `&raw const` / `transmute` pointer setup. -/
theorem boolInvalidLoadDirectUb_valid_three_way_ret :
    (∃ mem, ReachesRet (mirTree boolInvalidLoadDirectUb
      (initMachineState boolInvalidLoadDirectUb [.scalar ⟨1, 1⟩])) []
      (.normal (.scalar ⟨0, 4⟩, mem))) ∧
    MirNoUBTree (mirCallTree boolInvalidLoadDirectUb [.scalar ⟨1, 1⟩]) ∧
    retAfter boolInvalidLoadDirectUb [.scalar ⟨1, 1⟩] 9 =
      some (some { retAlloc with data := scalarBytes u32 0 }, [1]) ∧
    retAfterTB boolInvalidLoadDirectUb [.scalar ⟨1, 1⟩] 9 = tbRetU32 0 :=
  ⟨⟨_, runA_sound boolInvalidLoadDirectUb 30 _ _ _ rfl⟩,
   runA_noUB boolInvalidLoadDirectUb 30 _ _ _ rfl,
   by decide +kernel, by decide +kernel⟩

/-- `D2` (`disableLocalBorrows`) tag-disabling correspondence across stack-slot
cycling: `_3 = &raw mut _2` borrows temporary `_2`, then `StorageDead(_2);
StorageLive(_2); _2 = 77` re-initializes `_2`'s slot to `77`, and `_0 = copy (*_3)`
attempts to read through the stale pointer `_3`. Anneal's `disableLocalBorrows`
disables `_3`'s tag at `StorageDead(_2)` so `(*_3)` faults with UB even after `_2`
is live and initialized again, matching `Mach` and `MachTB`. -/
def storageCycleDisablesBorrowUb : CapturedMir :=
  ptrBody "witness::storage_cycle_disables_borrow_ub"
    [u32Decl, u32Decl, u32Decl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.use (constU32 5)),
     .assign (local_ 3) (.rawPtr .mut (local_ 2)),
     .storageDead 2,
     .storageLive 2,
     .assign (local_ 2) (.use (constU32 77)),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem storageCycleDisablesBorrowUb_notInFragment :
    inFragment storageCycleDisablesBorrowUb = false := by decide +kernel

theorem storageCycleDisablesBorrowUb_translate :
    (translateFn storageCycleDisablesBorrowUb).isSome = true := by decide +kernel

theorem storageCycleDisablesBorrowUb_three_way_ub :
    (∃ tr u, Reaches (mirTree storageCycleDisablesBorrowUb
      (initMachineState storageCycleDisablesBorrowUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
    ubAfter storageCycleDisablesBorrowUb [.scalar ⟨5, 4⟩] 9 =
      some "dereferencing pointer to dead allocation" ∧
    ubAfterTB storageCycleDisablesBorrowUb [.scalar ⟨5, 4⟩] 9 =
      some "dereferencing pointer to dead allocation" :=
  ⟨faultsA_sound storageCycleDisablesBorrowUb 25 _ (by decide),
   by decide +kernel, by decide +kernel⟩

/-- Dereference-read Tree Borrows freezing (`freezeDerefReadBorrowsAt`):
`_2 = &mut _1` followed by `(*_2) = 10` leaves `_2` `.active` (`hot = true`) in
both Anneal and `MachTB`, `_3 = &raw const _1` creates a raw pointer without
performing an initial read (keeping `_2` `.active` in both Anneal and `MachTB`),
and the dereference read `_4 = copy (*_3)` freezes `_2` to `.frozen`, so the
subsequent write `(*_2) = 99` raises UB in both Anneal and `MachTB` (while
returning `99` on `BasicMemory`, and rejected by `inFragment` via
`stepForeignRead`). -/
def derefReadFreezesActiveMutUb : CapturedMir :=
  ptrBody "witness::deref_read_freezes_active_mut_ub"
    [u32Decl, u32Decl, refMutU32Decl, ptrConstU32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (derefPlace 2) (.use (constU32 10)),
     .assign (local_ 3) (.rawPtr .not (local_ 1)),
     .assign (local_ 4) (.use (.copy (derefPlace 3))),
     .assign (derefPlace 2) (.use (constU32 99)),
     .assign (local_ 0) (.use (.copy (local_ 1)))]

theorem derefReadFreezesActiveMutUb_notInFragment :
    inFragment derefReadFreezesActiveMutUb = false := by decide +kernel

theorem derefReadFreezesActiveMutUb_translate :
    (translateFn derefReadFreezesActiveMutUb).isSome = true := by decide +kernel

theorem derefReadFreezesActiveMutUb_three_way :
    (∃ tr u, Reaches (mirTree derefReadFreezesActiveMutUb
      (initMachineState derefReadFreezesActiveMutUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
    retAfter derefReadFreezesActiveMutUb [.scalar ⟨5, 4⟩] 11 =
      some (some { retAlloc with data := scalarBytes u32 99 }, [1]) ∧
    ubAfterTB derefReadFreezesActiveMutUb [.scalar ⟨5, 4⟩] 9 =
      some "Tree Borrows: local write of Frozen reference" :=
  ⟨faultsA_sound derefReadFreezesActiveMutUb 25 _ (by decide),
   by decide +kernel, by decide +kernel⟩

/-- In-fragment `.reserved` mutable reference reborrow (`_3 = &mut (*_2)`) across
a foreign parent read (`_4 = copy (*_2)`) followed by child activation write
(`(*_3) = _4 + 37`) and child read (`_0 = copy (*_3)`): because `&mut (*_2)`
starts `.reserved` (`hot = false`), `freezeDerefReadBorrowsAt` and
`stepForeignRead` keep `_3` live across `*_2`, so `inFragment = true` and all
three semantics (`Anneal`, `Mach` via `mirCall_ret` + `mirCall_noUB`, and
`MachTB`) return `42` on `5`. -/
def mutReborrowForeignReadRoundTrip : CapturedMir :=
  ptrBody "witness::mut_reborrow_foreign_read_round_trip"
    [u32Decl, u32Decl, refMutU32Decl, refMutU32Decl, u32Decl]
    [.storageLive 2, .storageLive 3, .storageLive 4,
     .assign (local_ 2) (.ref (.mut false) (local_ 1)),
     .assign (local_ 3) (.ref (.mut false) (derefPlace 2)),
     .assign (local_ 4) (.use (.copy (derefPlace 2))),
     .assign (derefPlace 3) (.binaryOp .add (.copy (local_ 4)) (constU32 37)),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem mutReborrowForeignReadRoundTrip_inFragment :
    inFragment mutReborrowForeignReadRoundTrip = true := by decide +kernel

def mutReborrowForeignReadRoundTripFn : Gen.Function where
  locals := ⟨[
    (localName 0, .Int u32), (localName 1, .Int u32),
    (localName 2, refTy .mut u32), (localName 3, refTy .mut u32),
    (localName 4, .Int u32)]⟩
  args := [localName 1]
  ret := localName 0
  calling_convention := .Rust
  blocks := ⟨[
    (bbName 0, ⟨[
      .StorageLive (localName 2), .StorageLive (localName 3), .StorageLive (localName 4),
      .Assign (.Local (localName 2)) (.AddrOf (.Local (localName 1)) (refPtrType .mut u32)),
      .Assign (.Local (localName 3))
        (.AddrOf (.Deref (.Load (.Local (localName 2))) (.Int u32)) (refPtrType .mut u32)),
      .Assign (.Local (localName 4)) (.Load (.Deref (.Load (.Local (localName 2))) (.Int u32))),
      .Assign (.Deref (.Load (.Local (localName 3))) (.Int u32))
        (.BinOp (.Int .Add) (.Load (.Local (localName 4))) (.Constant (.Int 37) (.Int u32))),
      .Assign (.Local (localName 0)) (.Load (.Deref (.Load (.Local (localName 3))) (.Int u32)))],
      .Return, .Regular⟩),
    (bbName 1, ⟨[], .Goto (bbName 0), .Regular⟩)]⟩
  start := bbName 1
  implicit_writes := true

theorem mutReborrowForeignReadRoundTrip_translate :
    translateFn mutReborrowForeignReadRoundTrip = some mutReborrowForeignReadRoundTripFn := rfl

def mutReborrowForeignReadRoundTripS0 : MachineState :=
  initMachineState mutReborrowForeignReadRoundTrip [.scalar ⟨5, 4⟩]
def mutReborrowForeignReadRoundTripMInit : Mach :=
  machine mutReborrowForeignReadRoundTrip mutReborrowForeignReadRoundTripFn
    mutReborrowForeignReadRoundTripS0.frame.locals mutReborrowForeignReadRoundTripFn.start

theorem mutReborrowForeignReadRoundTrip_ctxOk : CtxOk mutReborrowForeignReadRoundTrip ctx0 where
  baseLow := by unfold BaseLow; decide
  addrs := by
    intro i d hi hd
    have hi1 : i ≤ 1 := hi
    have hlay : mutReborrowForeignReadRoundTrip.layouts = emptyLayoutTable := rfl
    rw [hlay]
    match i, hd, hi1 with
    | 0, hd, _ => simp [mutReborrowForeignReadRoundTrip, ptrBody] at hd; subst hd; decide
    | 1, hd, _ => simp [mutReborrowForeignReadRoundTrip, ptrBody] at hd; subst hd; decide
    | _ + 2, _, h => omega
  ret := by
    intro d hd
    have hlay : mutReborrowForeignReadRoundTrip.layouts = emptyLayoutTable := rfl
    rw [hlay]
    simp [mutReborrowForeignReadRoundTrip, ptrBody] at hd; subst hd
    exact ⟨0, retAlloc, rfl, rfl, rfl, rfl, rfl, by decide⟩

theorem mutReborrowForeignReadRoundTrip_anneal_ret :
    ∃ mem, ReachesRet (mirTree mutReborrowForeignReadRoundTrip mutReborrowForeignReadRoundTripS0) []
      (.normal (.scalar ⟨42, 4⟩, mem)) :=
  ⟨_, runA_sound mutReborrowForeignReadRoundTrip 30 _ _ _ rfl⟩

theorem mutReborrowForeignReadRoundTrip_noUB :
    MirNoUBTree (mirCallTree mutReborrowForeignReadRoundTrip [.scalar ⟨5, 4⟩]) :=
  runA_noUB mutReborrowForeignReadRoundTrip 30 _ _ _ rfl

theorem mutReborrowForeignReadRoundTrip_minirust_ret_from_start :
    ∃ (n : Nat) (m' : Mach), Interp.steps n mutReborrowForeignReadRoundTripMInit = .ok m' ∧
      m'.mem.memory.allocations[0]? = some { retAlloc with data := scalarBytes u32 42 } ∧
      m'.threads = [thread1 ctx0 [{ callerFrame with next_block := bbName 7, next_stmt := 0 }]] := by
  obtain ⟨mem, hretA⟩ := mutReborrowForeignReadRoundTrip_anneal_ret
  obtain ⟨n, s', m', hsteps, hret⟩ :=
    mirCall_ret mutReborrowForeignReadRoundTrip_inFragment
      mutReborrowForeignReadRoundTrip_translate ctx0
      mutReborrowForeignReadRoundTrip_ctxOk [.scalar ⟨5, 4⟩] (by decide)
      mutReborrowForeignReadRoundTripMInit rfl rfl rfl hretA
  obtain ⟨r, a, d, R, hd, _hv, hp, hr, hthr, hallocs, _hR⟩ := hret
  simp [mutReborrowForeignReadRoundTrip, ptrBody] at hd; subst hd
  simp [retPtr, ctx0] at hp
  have hr0 : r = 0 := by omega
  subst hr0
  simp [ctx0] at hr; subst hr
  refine ⟨n, m', hsteps, ?_, hthr⟩
  rw [hallocs]; rfl

theorem mutReborrowForeignReadRoundTrip_minirust_noUB {n : Nat} {e : Stop}
    (herr : Interp.steps n mutReborrowForeignReadRoundTripMInit = .error e) :
    ∃ k s' mRet tr v mem, k < n ∧ Interp.steps k mutReborrowForeignReadRoundTripMInit = .ok mRet ∧
      ReturnRel mutReborrowForeignReadRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree mutReborrowForeignReadRoundTrip [.scalar ⟨5, 4⟩]) tr
        (.normal (v, mem)) :=
  mirCall_noUB mutReborrowForeignReadRoundTrip_inFragment
    mutReborrowForeignReadRoundTrip_translate ctx0
    mutReborrowForeignReadRoundTrip_ctxOk [.scalar ⟨5, 4⟩] (by decide)
    mutReborrowForeignReadRoundTripMInit rfl rfl rfl mutReborrowForeignReadRoundTrip_noUB herr

theorem mutReborrowForeignReadRoundTrip_progress (n : Nat) :
    (∃ s' m' tr, Interp.steps (1 + n) mutReborrowForeignReadRoundTripMInit = .ok m' ∧
      StateRelN mutReborrowForeignReadRoundTrip mutReborrowForeignReadRoundTripFn ctx0 s' m' ∧
      Reaches (mirCallTree mutReborrowForeignReadRoundTrip [.scalar ⟨5, 4⟩]) tr
        (mirTree mutReborrowForeignReadRoundTrip s')) ∨
    (∃ k s' mRet tr v mem, k ≤ 1 + n ∧ Interp.steps k mutReborrowForeignReadRoundTripMInit = .ok mRet ∧
      ReturnRel mutReborrowForeignReadRoundTrip ctx0 s' v mRet ∧
      ReachesRet (mirCallTree mutReborrowForeignReadRoundTrip [.scalar ⟨5, 4⟩]) tr
        (.normal (v, mem))) :=
  mirCall_progress_N mutReborrowForeignReadRoundTrip_inFragment
    mutReborrowForeignReadRoundTrip_translate ctx0
    mutReborrowForeignReadRoundTrip_ctxOk [.scalar ⟨5, 4⟩] (by decide)
    mutReborrowForeignReadRoundTripMInit rfl rfl rfl mutReborrowForeignReadRoundTrip_noUB n

theorem mutReborrowForeignReadRoundTrip_three_way :
    (∃ mem, ReachesRet (mirTree mutReborrowForeignReadRoundTrip mutReborrowForeignReadRoundTripS0) []
      (.normal (.scalar ⟨42, 4⟩, mem))) ∧
    retAfter mutReborrowForeignReadRoundTrip [.scalar ⟨5, 4⟩] 10 =
      some (some { retAlloc with data := scalarBytes u32 42 }, [1]) ∧
    retAfterTB mutReborrowForeignReadRoundTrip [.scalar ⟨5, 4⟩] 10 = tbRetU32 42 :=
  ⟨mutReborrowForeignReadRoundTrip_anneal_ret, by decide +kernel, by decide +kernel⟩

/-- `D2` (`evalStmt_storageLive_disable`) tag-disabling correspondence on repeated
`StorageLive(_2)` *without* a preceding `StorageDead(_2)`: `_2 = 5; _3 = &raw mut _2;
StorageLive(_2); _2 = 77; _0 = copy (*_3)`. MiniRust's `storage_live` first
deallocates the old allocation of `_2` before allocating a fresh one, and Anneal's
`evalStmt` `.storageLive` runs `disableLocalBorrows` so the stale tag in `_3`
faults with UB on `(*_3)` in Anneal, `Mach`, and `MachTB` (whereas without
`StorageLive` tag disabling, `_2 = 77` would re-initialize the slot and Anneal
would silently return `77`). -/
def storageLiveReallocDisablesBorrowUb : CapturedMir :=
  ptrBody "witness::storage_live_realloc_disables_borrow_ub"
    [u32Decl, u32Decl, u32Decl, ptrMutU32Decl]
    [.storageLive 2, .storageLive 3,
     .assign (local_ 2) (.use (constU32 5)),
     .assign (local_ 3) (.rawPtr .mut (local_ 2)),
     .storageLive 2,
     .assign (local_ 2) (.use (constU32 77)),
     .assign (local_ 0) (.use (.copy (derefPlace 3)))]

theorem storageLiveReallocDisablesBorrowUb_notInFragment :
    inFragment storageLiveReallocDisablesBorrowUb = false := by decide +kernel

theorem storageLiveReallocDisablesBorrowUb_translate :
    (translateFn storageLiveReallocDisablesBorrowUb).isSome = true := by decide +kernel

theorem storageLiveReallocDisablesBorrowUb_three_way_ub :
    (∃ tr u, Reaches (mirTree storageLiveReallocDisablesBorrowUb
      (initMachineState storageLiveReallocDisablesBorrowUb [.scalar ⟨5, 4⟩])) tr u ∧ FaultNow u) ∧
    ubAfter storageLiveReallocDisablesBorrowUb [.scalar ⟨5, 4⟩] 8 =
      some "dereferencing pointer to dead allocation" ∧
    ubAfterTB storageLiveReallocDisablesBorrowUb [.scalar ⟨5, 4⟩] 8 =
      some "dereferencing pointer to dead allocation" :=
  ⟨faultsA_sound storageLiveReallocDisablesBorrowUb 25 _ (by decide),
   by decide +kernel, by decide +kernel⟩

end MiniRustSpec.Correspondence.TbWitness
